module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.HardMathSupport.Timmesfeld.Torality.DescentCongruence
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.RankThree.E6.LargePrimeStabilizers
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerBase
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.ThreeA1Group

public noncomputable section

namespace CFSG.GroupTheory

theorem exists_conj_le_of_isPGroup_of_not_dvd_relIndex {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {Y H A : Subgroup G} (hHY : H ≤ Y) (hAY : A ≤ Y)
    (hAp : IsPGroup p A) (hrel : ¬ p ∣ H.relIndex Y) :
    ∃ g ∈ Y, ∀ x ∈ A, g * x * g⁻¹ ∈ H := by
  classical
  have hcard : Nat.card Y = Nat.card H * H.relIndex Y := by
    have h := Subgroup.relIndex_mul_card (H := H) (K := Y)
    rw [inf_eq_left.2 hHY, mul_comm] at h
    exact h.symm
  have hrel0 : H.relIndex Y ≠ 0 := fun h => hrel (h ▸ dvd_zero p)
  have hord : (Nat.card Y).factorization p = (Nat.card H).factorization p := by
    rw [hcard, Nat.factorization_mul Nat.card_pos.ne' hrel0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hrel, add_zero]
  obtain ⟨S₁⟩ : Nonempty (Sylow p ↥H) := inferInstance
  let P₀ : Subgroup ↥Y := (S₁ : Subgroup ↥H).map (Subgroup.inclusion hHY)
  have hP₀ : Nat.card ↥P₀ = p ^ (Nat.card ↥Y).factorization p := by
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hHY),
      Sylow.card_eq_multiplicity, hord]
  let S₀ : Sylow p ↥Y := Sylow.ofCard P₀ hP₀
  have hA'p : IsPGroup p ↥(A.subgroupOf Y) :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAY).symm
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hA'p
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Y P S₀
  refine ⟨(g : G), g.2, ?_⟩
  intro x hxA
  have hxP : (⟨x, hAY hxA⟩ : ↥Y) ∈ P := hP (Subgroup.mem_subgroupOf.2 hxA)
  have h1 : (MulAut.conj g) • (⟨x, hAY hxA⟩ : ↥Y) ∈ (g • P : Sylow p _) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hxP
  rw [hg] at h1
  obtain ⟨s, -, hs⟩ := Subgroup.mem_map.1 (show _ ∈ P₀ from h1)
  have := congrArg (fun z : ↥Y => (z : G)) hs
  simp only [Subgroup.coe_inclusion] at this
  show (g : G) * x * (g : G)⁻¹ ∈ H
  rw [show (g : G) * x * (g : G)⁻¹ = (s : G) from this.symm.trans (by rfl)]
  exact s.2

end CFSG.GroupTheory

namespace CFSG.GroupTheory

theorem not_dvd_relIndex_of_factorization_eq {G : Type*} [Group G] [Finite G]
    {Y H : Subgroup G} (hHY : H ≤ Y) {p : ℕ} [Fact p.Prime]
    (hord : (Nat.card Y).factorization p = (Nat.card H).factorization p) :
    ¬ p ∣ H.relIndex Y := by
  intro hdvd
  have hcard : H.relIndex Y * Nat.card H = Nat.card Y := by
    have h := Subgroup.relIndex_mul_card (H := H) (K := Y)
    rwa [inf_eq_left.2 hHY] at h
  have h0 : H.relIndex Y ≠ 0 := by
    rintro h
    rw [h, zero_mul] at hcard
    exact Nat.card_pos.ne' hcard.symm
  have hfac : (H.relIndex Y * Nat.card H).factorization p =
      (H.relIndex Y).factorization p + (Nat.card H).factorization p := by
    rw [Nat.factorization_mul h0 Nat.card_pos.ne']
    rfl
  rw [← hcard, hfac] at hord
  have hpos : 0 < (H.relIndex Y).factorization p :=
    (Fact.out : p.Prime).factorization_pos_of_dvd h0 hdvd
  omega

end CFSG.GroupTheory

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LocalTwo

theorem exists_conj_le_torusGroup_E6_of_isPGroup {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ∣ Nat.card K - 1)
    {A : Subgroup (ModGL Tag.E6 K)} (hA : A ≤ adjointGroup Tag.E6 K) (hAp : IsPGroup p A) :
    ∃ g ∈ adjointGroup Tag.E6 K, ∀ x ∈ A, g * x * g⁻¹ ∈ torusGroup Tag.E6 K := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL Tag.E6 K) := CFSG.LieType.Chevalley.finite_modGL
  have hle : torusGroup Tag.E6 K ≤ adjointGroup Tag.E6 K :=
    CFSG.RankThree.PartOne.K128.torusGroup_le_adjointGroup'
  have hord : (Nat.card (adjointGroup Tag.E6 K)).factorization p =
      (Nat.card (torusGroup Tag.E6 K)).factorization p := by
    rw [factorization_card_adjointGroup_E_of_dvd_sub_one (Or.inl rfl) hp (by omega) hpq
      (not_dvd_degreesE_E6 hp hp7), factorization_card_torusGroup_E6 (by omega)]
    rfl
  exact CFSG.GroupTheory.exists_conj_le_of_isPGroup_of_not_dvd_relIndex hle hA hAp
    (CFSG.GroupTheory.not_dvd_relIndex_of_factorization_eq hle hord)

end CFSG.StandardType

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem baseChangeGL_mem_torusGroup
    {R S : Type} [Field R] [Field S] (f : R →+* S) {τ : Tag}
    {g : ModGL τ R} (hg : g ∈ torusGroup τ R) : baseChangeGL f g ∈ torusGroup τ S := by
  have hle : torusGroup τ R ≤ (torusGroup τ S).comap (baseChangeGL f) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    show baseChangeGL f (torusElt τ R i t) ∈ torusGroup τ S
    rw [baseChangeGL_torusElt]
    exact torusElt_mem_torusGroup i _
  exact hle hg

end CFSG.LieType.Chevalley

