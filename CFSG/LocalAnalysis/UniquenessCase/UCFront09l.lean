module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.Goldschmidt.Basic
import CFSG.LocalAnalysis.UniquenessCase.UCFront09i
import CFSG.LocalAnalysis.UniquenessCase.UCFront09k
import CFSG.LocalAnalysis.UniquenessCase.UC22P22p
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.GroupTheory.PCore.RelPPrimeCoreMap
import CFSG.Goldschmidt.Steps.GoldTypeBender
import CFSG.Goldschmidt.Steps.Red2Basic
import CFSG.RankThree.PartTwo.Sec4.Census.Item44RankTwoX
import CFSG.RankThree.PartTwo.Sec20.Item20Res3ProofComm
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore
import CFSG.LocalAnalysis.UniquenessCase.UCFront09h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (relPPrimeCore_le coprime_card_relPPrimeCore)
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def E9 (M X : Subgroup G) : Subgroup G :=
  ⁅CFSG.Goldschmidt.Omega1 ⁅pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X, X⁆, X⁆

theorem E9_le (M X : Subgroup G) :
    E9 M X ≤ ⁅pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X, X⁆ :=
  (le_normalizer_iff_commutator_le_left.1 ((normalizer_commutator_ge_right _ _).trans
    (CFSG.Goldschmidt.GoldType.normalizer_le_normalizer_omega1 _))).trans
    (CFSG.Goldschmidt.GoldType.omega1_le _)

end Defs

variable {G : Type} [Group G] [Finite G]

theorem commutator_omega1_ne_bot {X Z D : Subgroup G} (hZ2 : IsPGroup 2 Z)
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hXZ : X ≤ normalizer (Z : Set G))
    (hXC : ¬ X ≤ centralizer (Z : Set G)) (hDX : D ≤ X) (hD : Nat.card D = 3)
    (hgen : ∀ K : Subgroup G, (∀ x ∈ X, D.map (MulAut.conj x).toMonoidHom ≤ K) → X ≤ K) :
    ⁅CFSG.Goldschmidt.Omega1 Z, X⁆ ≠ ⊥ := by
  intro h
  rw [commutator_eq_bot_iff_le_centralizer] at h
  refine hXC (hgen _ fun x hx b hb => ?_)
  have hDx : D.map (MulAut.conj x).toMonoidHom ≤ X := conj_smul_le_of_le hDX ⟨_, hx⟩
  have hb3 : orderOf b ∣ 3 := by
    have h3 := Subgroup.orderOf_dvd_natCard _ hb
    rwa [card_map_of_injective (MulAut.conj x).injective, hD] at h3
  have hcomm := CFSG.RankThree.PartTwo.Sec4.Census.commute_of_odd_of_centralizes_involutions hZ2
    ⟨⟨fun a c => Subtype.ext (hZc _ a.2 _ c.2)⟩⟩ (Odd.of_dvd_nat (by decide) hb3)
    (fun a ha => (hXZ (hDx hb) a).1 ha) fun a ha ha2 => mem_centralizer_iff.1
      (h (CFSG.Goldschmidt.GoldType.mem_omega1 ha (by rw [pow_two]; exact ha2))) b (hDx hb)
  exact mem_centralizer_iff.2 fun a ha => (hcomm a ha).symm

private theorem sq_eq_one_of_mem_omega1 {M X : Subgroup G} (hXM : X ≤ M) :
    ∀ v ∈ CFSG.Goldschmidt.Omega1 ⁅pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X, X⁆,
      v ^ 2 = 1 := by
  have hZc := commutator_zO2_le_centralizer hXM
  have hV := CFSG.Goldschmidt.GoldType.omega1_le
    ⁅pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X, X⁆
  exact CFSG.Goldschmidt.Red2.sq_eq_one_of_mem_closure
    ⟨⟨fun b c => Subtype.ext (mem_centralizer_iff.1 (hZc (hV c.2)) _ (hV b.2))⟩⟩
    (fun t ht => ht.2) rfl

theorem sq_eq_one_of_mem_E9 {M X : Subgroup G} (hXM : X ≤ M) : ∀ a ∈ E9 M X, a ^ 2 = 1 :=
  fun a ha => sq_eq_one_of_mem_omega1 hXM a
    (le_normalizer_iff_commutator_le_left.1 ((normalizer_commutator_ge_right _ _).trans
      (CFSG.Goldschmidt.GoldType.normalizer_le_normalizer_omega1 _)) ha)

theorem E9_ne_bot {M L X : Subgroup G} (hLM : L ≤ M) (hXL : X ≤ L) (hcov : L = X ⊔ pCoreOf 2 L)
    (hA5 : IsAlt (Bar2 L) 5) (hX : Opp 3 X = X)
    (hZ : ⁅pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X, X⁆ ≠ ⊥) : E9 M X ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXM := hXL.trans hLM
  obtain ⟨D, hDX, hD⟩ := exists_card_eq_three hXL hcov hA5
  exact commutator_omega1_ne_bot ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le
      ((commutator_zO2_le hXM).trans (inf_le_left.trans inf_le_left)))
    (fun a ha b hb => mem_centralizer_iff.1 (commutator_zO2_le_centralizer hXM hb) a ha)
    (normalizer_commutator_ge_right _ _) (not_le_centralizer_commutator hXM hX hZ) hDX hD
    fun K hK => le_of_forall_map_conj_le hXL hcov hA5 hX hDX hD hK

theorem commutator_E9_eq {M L X : Subgroup G} (hLM : L ≤ M) (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L) (hA5 : IsAlt (Bar2 L) 5) (hX : Opp 3 X = X) :
    ⁅E9 M X, X⁆ = E9 M X := by
  obtain ⟨D, hDX, hD⟩ := exists_card_eq_three hXL hcov hA5
  have hXV := (normalizer_commutator_ge_right
    (pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X) X).trans
    (CFSG.Goldschmidt.GoldType.normalizer_le_normalizer_omega1 _)
  have hVZ := CFSG.Goldschmidt.GoldType.omega1_le
    ⁅pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X, X⁆
  have hZc := commutator_zO2_le_centralizer (hXL.trans hLM)
  have hDx : ∀ x ∈ X, D.map (MulAut.conj x).toMonoidHom ≤ X :=
    fun x hx => conj_smul_le_of_le hDX ⟨_, hx⟩
  have hXS : X = closure {s | ∃ x ∈ X, s ∈ D.map (MulAut.conj x).toMonoidHom} :=
    le_antisymm (le_of_forall_map_conj_le hXL hcov hA5 hX hDX hD fun x hx s hs =>
      subset_closure ⟨x, hx, hs⟩) ((closure_le _).2 fun s ⟨x, hx, hs⟩ => hDx x hx hs)
  refine le_antisymm (commutator_mono (le_normalizer_iff_commutator_le_left.1 hXV) le_rfl)
    (CFSG.RankThree.PartTwo.Sec20.Res3.commutator_le_commutator_commutator hXS
      (fun s ⟨x, _, hs⟩ => ?_) (fun a ha b hb => mem_centralizer_iff.1 (hZc (hVZ hb)) a (hVZ ha))
      (fun v hv => by rw [← pow_two]; exact sq_eq_one_of_mem_omega1 (hXL.trans hLM) v hv)
      hXV le_rfl)
  have h3 := Subgroup.orderOf_dvd_natCard _ hs
  rw [card_map_of_injective (MulAut.conj x).injective, hD] at h3
  exact orderOf_dvd_iff_pow_eq_one.1 h3

theorem le_normalizer_I9 (H : Subgroup G) : H ≤ normalizer (I9 H : Set G) :=
  CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H

theorem not_dvd_card_I9 (H : Subgroup G) : ¬ 3 ∣ Nat.card (I9 H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (CFSG.RankThree.GroupTheory.SteinbergBM.coprime_card_inSubgroup_pPrimeCore H)

theorem le_normalizer_relPPrimeCore_I9 (p : ℕ) (H : Subgroup G) :
    H ≤ normalizer (relPPrimeCore p (I9 H) : Set G) := by
  intro h hh
  rw [mem_normalizer_iff_map_conj_eq]
  refine eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj h).injective).ge
  have e := relPPrimeCore_map_le_of_injective ((MulAut.conj h : G ≃* G) : G →* G)
    (MulAut.conj h).injective (I9 H) p
  rwa [mem_normalizer_iff_map_conj_eq.1 (le_normalizer_I9 H hh)] at e

theorem not_dvd_card_relPPrimeCore_two_I9 (H : Subgroup G) :
    ¬ 2 ∣ Nat.card (relPPrimeCore 2 (I9 H)) ∧ ¬ 3 ∣ Nat.card (relPPrimeCore 2 (I9 H)) :=
  ⟨(Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 (coprime_card_relPPrimeCore Nat.prime_two _),
    fun h => not_dvd_card_I9 H (h.trans (card_dvd_of_le (relPPrimeCore_le _)))⟩

theorem relPPrimeCore_two_I9_le {M L X H : Subgroup G} (hLM : L ≤ M) (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L) (hA5 : IsAlt (Bar2 L) 5) (hX : Opp 3 X = X)
    (hZ : ⁅pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X, X⁆ ≠ ⊥)
    (hMX : UniqueMax M X)
    (hND : ∀ A : Subgroup G, A ≤ X → Nat.card A = 3 → normalizer (A : Set G) ≤ M)
    (hXH : X ≤ H) : CFSG.Open.relPPrimeCore 2 (I9 H) ≤ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXM : X ≤ M := hXL.trans hLM
  obtain ⟨D, hDX, hD⟩ := exists_card_eq_three hXL hcov hA5
  have hEZ := E9_le M X
  have hEZ0 := hEZ.trans (commutator_zO2_le hXM)
  have hNE : normalizer (E9 M X : Set G) ≤ M :=
    uc22p22p_le_of_uniqueMax hMX ⟨E9 M X, E9_ne_bot hLM hXL hcov hA5 hX hZ,
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le
        (hEZ0.trans (inf_le_left.trans inf_le_left)), rfl⟩ (normalizer_commutator_ge_right _ _)
  obtain ⟨hP2, hP3⟩ := not_dvd_card_relPPrimeCore_two_I9 H
  have hP : Group.IsSolvable ↥(relPPrimeCore 2 (I9 H)) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hP2))
  refine le_of_inf_centralizer_le hP hP2 hP3 (hXH.trans (le_normalizer_relPPrimeCore_I9 2 H))
    (hEZ0.trans inf_le_right) (normalizer_commutator_ge_right _ _) (sq_eq_one_of_mem_E9 hXM)
    (fun a ha b hb => mem_centralizer_iff.1 (commutator_zO2_le_centralizer hXM (hEZ hb)) a
      (hEZ ha)) (commutator_E9_eq hLM hXL hcov hA5 hX).ge hDX hD
    (fun K hK => le_of_forall_map_conj_le hXL hcov hA5 hX hDX hD hK)
    (inf_le_right.trans ((centralizer_le_normalizer _).trans hNE)) fun x hx => ?_
  have hDx : D.map (MulAut.conj x).toMonoidHom ≤ X := conj_smul_le_of_le hDX ⟨_, hx⟩
  exact inf_le_right.trans ((centralizer_le_normalizer _).trans
    (hND _ hDx ((card_map_of_injective (MulAut.conj x).injective).trans hD)))

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
