module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Open

private theorem ggL45NtVacSz_card_le_of_isElemAbelian_of_isCyclic {Y : Type*} [Group Y] [Finite Y]
    {p : ℕ} (hp : p.Prime) {B : Subgroup Y} (hB : IsElemAbelian p B) (hc : IsCyclic B) :
    Nat.card B ≤ p := by
  obtain ⟨g, hg⟩ := hc.exists_generator
  have hord : orderOf g = Nat.card B := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hB.2 g g.2)
  rw [← hord]
  exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)

private theorem ggL45NtVacSz_conj_injective_of_center_eq_bot {R : Type*} [Group R]
    (hR : Subgroup.center R = ⊥) : Function.Injective (MulAut.conj : R →* MulAut R) := by
  rw [injective_iff_map_eq_one]
  intro r hr
  have hc : r ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut R => φ g) hr
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * r = r * g * r⁻¹ * r := by rw [this]
      _ = r * g := by group
  rw [hR] at hc
  exact Subgroup.mem_bot.mp hc

private theorem ggL45NtVacSz_vac
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (F : Set (MulAut (LargeEvenCenterQuot (LargeEvenSzGroup a K)))) :
    GGL45NtVac p (LargeEvenCenterQuot (LargeEvenSzGroup a K))
      (LargeEvenInnSet (LargeEvenCenterQuot (LargeEvenSzGroup a K))) F := by
  right
  rintro ⟨A, hAab, hAcard, hAI⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hcenter : Subgroup.center (suzukiGroup a K) = ⊥ := by
    obtain ⟨-, -, hsimple⟩ := CFSG.LieType.Ree.suzuki_simple (a := a) ha (K := K) hK
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (suzukiGroup a K)) with h | h
    · exact h
    · have hperf := (CFSG.LieType.Ree.suzuki_perfect (a := a) ha (K := K) hK).1
      rw [(commutator_eq_bot_iff_center_eq_top (suzukiGroup a K)).2 h] at hperf
      exact absurd hperf bot_ne_top
  obtain ⟨e1⟩ := nonempty_centerQuot_congr (largeEvenSzGroup_eq a K)
  let e2 : LargeEvenCenterQuot (suzukiGroup a K) ≃* suzukiGroup a K :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  let e3 : suzukiGroup a K ≃* GLASzGroup a K :=
    MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)
  let eR : LargeEvenCenterQuot (LargeEvenSzGroup a K) ≃* GLASzGroup a K :=
    e1.trans (e2.trans e3)
  haveI : Finite (LargeEvenCenterQuot (LargeEvenSzGroup a K)) := by
    haveI : Finite (LargeEvenSzGroup a K) := Subtype.finite
    exact Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  let e12 : LargeEvenCenterQuot (LargeEvenSzGroup a K) ≃* suzukiGroup a K := e1.trans e2
  have hcenterR : Subgroup.center (LargeEvenCenterQuot (LargeEvenSzGroup a K)) = ⊥ := by
    have hle : Subgroup.center (LargeEvenCenterQuot (LargeEvenSzGroup a K)) ≤
        (e12 : LargeEvenCenterQuot (LargeEvenSzGroup a K) →* suzukiGroup a K).ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      have hx' : e12 x ∈ (Subgroup.center (LargeEvenCenterQuot (LargeEvenSzGroup a K))).map
          (e12 : LargeEvenCenterQuot (LargeEvenSzGroup a K) →* suzukiGroup a K) :=
        ⟨x, hx, rfl⟩
      rw [Subgroup.map_center_eq e12, hcenter] at hx'
      exact Subgroup.mem_bot.mp hx'
    have hker : (e12 : LargeEvenCenterQuot (LargeEvenSzGroup a K) →* suzukiGroup a K).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr e12.injective
    rw [hker] at hle
    exact le_bot_iff.mp hle
  have hconj_inj : Function.Injective
      (MulAut.conj : LargeEvenCenterQuot (LargeEvenSzGroup a K) →*
        MulAut (LargeEvenCenterQuot (LargeEvenSzGroup a K))) :=
    ggL45NtVacSz_conj_injective_of_center_eq_bot hcenterR
  have hSylow : ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 →
      ∀ P : Sylow q (LargeEvenCenterQuot (LargeEvenSzGroup a K)), IsCyclic P :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
      a ha hK eR
  let E : Subgroup (LargeEvenCenterQuot (LargeEvenSzGroup a K)) :=
    A.comap (MulAut.conj : LargeEvenCenterQuot (LargeEvenSzGroup a K) →*
        MulAut (LargeEvenCenterQuot (LargeEvenSzGroup a K)))
  have hEab : IsElemAbelian p E := CFSG.Open.IsElemAbelian.comap hAab hconj_inj
  have hAE : Nat.card A = Nat.card E := by
    have hAeq : A = E.map (MulAut.conj : LargeEvenCenterQuot (LargeEvenSzGroup a K) →*
        MulAut (LargeEvenCenterQuot (LargeEvenSzGroup a K))) :=
      (Subgroup.map_comap_eq_self
        (f := (MulAut.conj : LargeEvenCenterQuot (LargeEvenSzGroup a K) →*
          MulAut (LargeEvenCenterQuot (LargeEvenSzGroup a K))))
        (H := A) hAI).symm
    rw [hAeq, Subgroup.card_map_of_injective hconj_inj]
  have hEodd : Odd (Nat.card E) := by
    obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hEab).exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hEcyc : IsCyclic E :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.odd_commutative_subgroup_cyclic
      E hEodd hEab.1 hSylow
  have hEle : Nat.card E ≤ p :=
    ggL45NtVacSz_card_le_of_isElemAbelian_of_isCyclic hp hEab hEcyc
  have hle : p ^ 2 ≤ p := (hAcard.trans_eq hAE).trans hEle
  exact absurd hle (not_le.mpr (by nlinarith [hp.two_le]))

theorem ggL45NtVacOn_twB2 :
    GGL45NtVacOn fun p lab => GGL45FamNonTorsion p lab ∧ lab.tag = .twB2 := by
  intro p hp hp2 lab hlab _hkg hS Q hQ
  obtain ⟨t, l, n⟩ := lab
  have htag : t = .twB2 := hS.2
  subst htag
  obtain ⟨k, hk⟩ := hlab.2.2.1
  have hk' : n = 2 * k + 1 := hk
  have hn3 : 3 ≤ n := hlab.2.2.2
  have hna : 2 * ((n - 1) / 2) + 1 = n := by omega
  have ha : 1 ≤ (n - 1) / 2 := by omega
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  refine ⟨K, i1, i2, hK, hq', ?_⟩
  exact ggL45NtVacSz_vac ha hK hp hp2 _

end CFSG.StandardType
