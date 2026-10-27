module

public import CFSG.Quasithin.EmptyFaithful.S146F3
public import CFSG.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.Quasithin.EmptyFaithful.S14610Q0

public section

namespace CFSG.Quasithin.S152Y

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Basic

omit [Finite G] in
theorem le_normalizer_omegaOneCenterOf_pCoreOf (K : Subgroup G) :
    K ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 K) : Set G) := by
  intro k hk
  have hN : k ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) := le_normalizer_pCoreOf 2 K hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_omegaOneCenterOf_of_normalizer hN hx, fun hx => ?_⟩
  have := conj_mem_omegaOneCenterOf_of_normalizer ((Subgroup.normalizer (pCoreOf 2 K : Set G)).inv_mem hN) hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem wOf1469_le_omegaOneCenterOf (K : Subgroup G) :
    wOf1469 K ≤ omegaOneCenterOf (pCoreOf 2 K) :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_omegaOneCenterOf_pCoreOf K)

omit [Finite G] in
theorem wOf1469_sq {K : Subgroup G} {a : G} (ha : a ∈ wOf1469 K) : a * a = 1 := by
  have := A4.sq_eq_one_of_mem_omegaOneCenterOf (wOf1469_le_omegaOneCenterOf K ha)
  rwa [pow_two] at this

omit [Finite G] in
theorem le_normalizer_wOf1469 (K : Subgroup G) : K ≤ Subgroup.normalizer (wOf1469 K : Set G) :=
  Subgroup.normalizer_commutator_ge_right _ _

omit [Finite G] in
theorem wOf1469_comm_pCore {K : Subgroup G} {k x : G} (hk : k ∈ pCoreOf 2 K) (hx : x ∈ wOf1469 K) :
    k * x * k⁻¹ = x := by
  have h1 : x ∈ centerOf (pCoreOf 2 K) :=
    A4.omegaOneCenterOf_le_centerOf _ (wOf1469_le_omegaOneCenterOf K hx)
  have h2 : x ∈ Subgroup.centralizer (pCoreOf 2 K : Set G) := A4.centerOf_le_centralizer _ h1
  have h3 : k * x = x * k := Subgroup.mem_centralizer_iff.mp h2 k hk
  rw [h3]
  group

theorem pCoreOf_le_pCoreOf_sup {K R : Subgroup G} (hR : R ≤ Subgroup.normalizer (K : Set G)) :
    pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) := by
  have hKR : K ⊔ R ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hR
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
    (fun g hg => normalizer_le_normalizer_pCoreOf 2 K (hKR hg)) (pCoreOf_isPGroup 2 K)

theorem commutator_pCore_le {K R : Subgroup G} (hR : R ≤ Subgroup.normalizer (K : Set G)) :
    ⁅pCoreOf 2 (K ⊔ R), K⁆ ≤ pCoreOf 2 K := by
  have hKR : K ⊔ R ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hR
  have hKP : K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ R) : Set G) := fun k hk =>
    le_normalizer_pCoreOf 2 (K ⊔ R) ((le_sup_left : K ≤ K ⊔ R) hk)
  have hPK : pCoreOf 2 (K ⊔ R) ≤ Subgroup.normalizer (K : Set G) := fun p hp =>
    hKR (pCoreOf_le 2 _ hp)
  have h1 : ⁅pCoreOf 2 (K ⊔ R), K⁆ ≤ pCoreOf 2 (K ⊔ R) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hKP
  have h2 : ⁅pCoreOf 2 (K ⊔ R), K⁆ ≤ K := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hPK
  have h3 : pCoreOf 2 (K ⊔ R) ⊓ K ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf ⟨hKP hk, Subgroup.le_normalizer hk⟩)
      ((pCoreOf_isPGroup 2 (K ⊔ R)).to_le inf_le_left)
  exact (le_inf h1 h2).trans h3

end Basic

section Quot

omit [Finite G] in
theorem exists_mulEquiv_of_isPSL {K : Subgroup G} (h : IsPSL 3 2 1 (OTwoQuot K)) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨e⟩ := isPSL_three_two_iff.mp h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)).trans e⟩

theorem mem_cComp_of_eq_oTwoUpper {I K : Subgroup G} (hK : K = oTwoUpper I)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) : K ∈ cComp I := by
  subst hK
  refine H13.mem_cComp_of_quasisimple_quotient (H13.oTwoUpper_eq_top_of_isPGroup I) hq
    (A4.subnormal_of_normal (oTwoUpper_le I) ?_)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le I)]
  exact le_normalizer_oTwoUpper I

end Quot

end CFSG.Quasithin.S152Y

