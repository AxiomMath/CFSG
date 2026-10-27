module

public import CFSG.LocalAnalysis.UniquenessCase.UCKU3b
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamUSylow
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutInnerIndex
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem isCyclic_homC {p a r : ℕ} (hr : r ≤ 1) : IsCyclic (HomC p a r) := by
  interval_cases r
  · exact isCyclic_of_subsingleton
  · exact isCyclic_of_surjective (MulEquiv.piUnique _).symm.toMonoidHom
      (MulEquiv.piUnique _).symm.surjective

theorem three_div_orderOf_le_one {p Q : ℕ} [Fact p.Prime] (hpQ : ¬ p ∣ Q + 1) :
    3 / orderOf (-((Q : ℕ) : ZMod p)) ≤ 1 := by
  have h1 : orderOf (-((Q : ℕ) : ZMod p)) ≠ 1 := by
    intro h
    rw [orderOf_eq_one_iff] at h
    apply hpQ
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, neg_eq_iff_eq_neg.1 h,
      neg_add_cancel]
  rcases Nat.lt_or_ge (orderOf (-((Q : ℕ) : ZMod p))) 2 with h | h
  · interval_cases hk : orderOf (-((Q : ℕ) : ZMod p))
    · simp
    · exact absurd rfl h1
  · exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 (by omega))

theorem isCyclic_sylow_statedPSU3 {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ 2 ^ n + 1)
    (S : Sylow p (StatedProj (StatedSU 3 (2 ^ n) K))) : IsCyclic S := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq : ¬ p ∣ 2 ^ n := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hk := three_div_orderOf_le_one (p := p) hpn
  have hlt : 3 / orderOf (-((2 ^ n : ℕ) : ZMod p)) < p := lt_of_le_of_lt hk hp.one_lt
  have hGU := famU_sylow_GU_homC (L := K) (n := 3) hp2 hK hpq (by norm_num) hlt
  have hfact : (Nat.card (StatedSU 3 (2 ^ n) K)).factorization p =
      (Nat.card (CFSG.Quasithin.StatedGU 3 (2 ^ n) K)).factorization p := by
    rw [famU_card_GU Nat.prime_two hK (by norm_num), Nat.factorization_mul Nat.card_pos.ne'
      (Nat.succ_ne_zero _), Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpn, add_zero]
  have hSU := sylowShape_of_injective
    (Subgroup.inclusion Stroth.WeakClosure.statedSU_le_statedGU)
    (Subgroup.inclusion_injective _) hfact hGU
  have hker : ¬ p ∣ Nat.card (famUProj 3 (2 ^ n) K).ker := by
    rw [famU_card_ker_proj Nat.prime_two hK (by norm_num)]
    exact fun h => hpn (h.trans (Nat.gcd_dvd_right _ _))
  obtain ⟨φ⟩ := sylowShape_of_surjective (famUProj 3 (2 ^ n) K)
    (QuotientGroup.mk'_surjective _) hker hSU S
  haveI := isCyclic_homC (p := p)
    (a := padicValInt p ((-((2 ^ n : ℕ) : ℤ)) ^ orderOf (-((2 ^ n : ℕ) : ZMod p)) - 1)) hk
  exact isCyclic_of_surjective φ.symm.toMonoidHom φ.symm.surjective

theorem card_le_of_isCyclic_of_pow {G : Type*} [Group G] {A : Subgroup G} [Finite A]
    [IsCyclic A] {p : ℕ} (hp : 0 < p) (hA : ∀ x ∈ A, x ^ p = 1) : Nat.card A ≤ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  refine Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one ?_)
  exact Subtype.ext (by simpa using hA g g.2)

theorem card_le_of_sylow_isCyclic {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (hcyc : ∀ S : Sylow p Y, IsCyclic S) {A : Subgroup Y} (hA : IsElemAbelian p A) :
    Nat.card A ≤ p := by
  have hAp : IsPGroup p A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  obtain ⟨S, hS⟩ := hAp.exists_le_sylow
  haveI := hcyc S
  haveI : IsCyclic A := isCyclic_of_surjective (subgroupOfEquivOfLe hS).toMonoidHom
    (subgroupOfEquivOfLe hS).surjective
  exact card_le_of_isCyclic_of_pow (Fact.out : p.Prime).pos hA.2

@[expose] noncomputable def innerEquivQuot (X : Type*) [Group X] :
    (MulAut.conj : X →* MulAut X).range ≃* X ⧸ center X :=
  (QuotientGroup.quotientKerEquivRange (MulAut.conj : X →* MulAut X)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.EvenSporadicStandard.Induction.AutInner.ker_conj_eq_center X))

theorem u3RankOne : U3RankOne := by
  intro X _ _ n hX p hp hp2 hpn R hRinn hRel
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨ψ⟩⟩ :=
    CFSG.SeitzReduction.RankOne.statedClassicalModel_of_lieModel_psu3 hX.2
  let ι : (MulAut.conj : X →* MulAut X).range ≃* StatedProj (StatedSU 3 (2 ^ n) K) :=
    (innerEquivQuot X).trans ψ
  let A : Subgroup (StatedProj (StatedSU 3 (2 ^ n) K)) :=
    (R.subgroupOf (MulAut.conj : X →* MulAut X).range).map ι.toMonoidHom
  have hAel : IsElemAbelian p A :=
    IsElemAbelian.map (IsElemAbelian.subgroupOf (E := R) hRel _) _
  have hAcard : Nat.card A = Nat.card R := by
    rw [Subgroup.card_map_of_injective ι.injective,
      Nat.card_congr (subgroupOfEquivOfLe hRinn).toEquiv]
  rw [← hAcard]
  exact card_le_of_sylow_isCyclic (fun S => isCyclic_sylow_statedPSU3 hK hp hp2 hpn S) hAel

end CFSG.LocalAnalysis.UniquenessCase.UCK
