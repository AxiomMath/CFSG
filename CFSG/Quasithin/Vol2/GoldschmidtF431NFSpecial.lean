module

public import CFSG.Quasithin.Vol2.GoldschmidtF431NFTI
public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13.F431.NF

open scoped commutatorElement

variable {M : Type*} [Group M]

theorem card_le_card_inf_centralizer_mul [Finite M] {Q Z : Subgroup M} (hZQ : Z ≤ Q)
    (hZc : ∀ z ∈ Z, ∀ y ∈ Q, y * z = z * y) (hQc : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z) {x : M}
    (hx : x ∈ Q) :
    Nat.card Q ≤ Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set M) : Subgroup M) * Nat.card Z := by
  let φ : Q →* Z :=
    { toFun := fun y => ⟨⁅(y : M), x⁆, hQc _ y.2 _ hx⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro y y'
        ext
        have h1 : ⁅(y : M) * y', x⁆ = ((y : M) * ⁅(y' : M), x⁆ * (y : M)⁻¹) * ⁅(y : M), x⁆ := by
          simp only [commutatorElement_def]
          group
        have h2 : (y : M) * ⁅(y' : M), x⁆ * (y : M)⁻¹ = ⁅(y' : M), x⁆ := by
          have := hZc _ (hQc _ y'.2 _ hx) _ y.2
          calc (y : M) * ⁅(y' : M), x⁆ * (y : M)⁻¹ = ⁅(y' : M), x⁆ * (y : M) * (y : M)⁻¹ := by
                rw [this]
            _ = ⁅(y' : M), x⁆ := by group
        have h3 : ⁅(y' : M), x⁆ * ⁅(y : M), x⁆ = ⁅(y : M), x⁆ * ⁅(y' : M), x⁆ :=
          (hZc _ (hQc _ y'.2 _ hx) _ (hZQ (hQc _ y.2 _ hx))).symm
        show ⁅(y : M) * y', x⁆ = ⁅(y : M), x⁆ * ⁅(y' : M), x⁆
        rw [h1, h2, h3] }
  have hker : φ.ker = (Q ⊓ Subgroup.centralizer ({x} : Set M)).subgroupOf Q := by
    ext ⟨y, hy⟩
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      have h' : ⁅y, x⁆ = 1 := congrArg Subtype.val h
      refine ⟨hy, ?_⟩
      simp only [commutatorElement_def] at h'
      calc x * y = 1 * (x * y) := by group
        _ = (y * x * y⁻¹ * x⁻¹) * (x * y) := by rw [h']
        _ = y * x := by group
    · rintro ⟨-, h⟩
      apply Subtype.ext
      show ⁅y, x⁆ = 1
      simp only [commutatorElement_def]
      calc y * x * y⁻¹ * x⁻¹ = (x * y) * y⁻¹ * x⁻¹ := by rw [← h]
        _ = 1 := by group
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hrange : Nat.card φ.range ≤ Nat.card Z := Subgroup.card_le_card_group _
  have hk : Nat.card φ.ker = Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set M) : Subgroup M) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hcard, hk]
  exact Nat.mul_le_mul_left _ hrange

theorem inf_cj_elemAbelian {Q Z : Subgroup M} (hQc : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z)
    (hQs : ∀ x ∈ Q, x * x ∈ Z) {c : M} (hc : Z ⊓ cj c Z = ⊥) :
    (∀ x ∈ Q ⊓ cj c Q, x * x = 1) ∧
      ∀ x ∈ Q ⊓ cj c Q, ∀ y ∈ Q ⊓ cj c Q, x * y = y * x := by
  have key : ∀ t : M, t ∈ Z → t ∈ cj c Z → t = 1 := by
    intro t h1 h2
    have : t ∈ Z ⊓ cj c Z := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rwa [hc, Subgroup.mem_bot] at this
  constructor
  · intro x hx
    obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp hx
    refine key _ (hQs x hxQ) (mem_cj.mpr ?_)
    have h := hQs _ (mem_cj.mp hxc)
    have : c⁻¹ * (x * x) * c = (c⁻¹ * x * c) * (c⁻¹ * x * c) := by group
    rwa [this]
  · intro x hx y hy
    obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hyQ, hyc⟩ := Subgroup.mem_inf.mp hy
    have h1 := key _ (hQc x hxQ y hyQ) (mem_cj.mpr (by
      have h := hQc _ (mem_cj.mp hxc) _ (mem_cj.mp hyc)
      have : c⁻¹ * ⁅x, y⁆ * c = ⁅c⁻¹ * x * c, c⁻¹ * y * c⁆ := by
        simp only [commutatorElement_def]
        group
      rwa [this]))
    simp only [commutatorElement_def] at h1
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h1]; group

theorem card_sup_mul_card_inf [Finite M] {H K : Subgroup M}
    (hHK : H ≤ Subgroup.normalizer (K : Set M)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have h1 : K.relIndex (H ⊔ K) = K.relIndex H := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hHK
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHK
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hHK).toEquiv.symm
  have h2 := Subgroup.relIndex_mul_card (H := K) (K := H ⊔ K)
  have h3 := Subgroup.relIndex_mul_card (H := K) (K := H)
  rw [inf_eq_left.mpr le_sup_right, h1] at h2
  rw [← h2, ← h3, inf_comm]
  ring

theorem sup_eq_of_card_ge [Finite M] {S H K : Subgroup M} (hHS : H ≤ S) (hKS : K ≤ S)
    (hHK : H ≤ Subgroup.normalizer (K : Set M))
    (hcard : Nat.card S * Nat.card ↥(H ⊓ K) ≤ Nat.card H * Nat.card K) : H ⊔ K = S := by
  have h := card_sup_mul_card_inf hHK
  have hpos : 0 < Nat.card ↥(H ⊓ K) := Nat.card_pos
  have hle : Nat.card S ≤ Nat.card ↥(H ⊔ K) := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [h]
    exact hcard
  exact Subgroup.eq_of_le_of_card_ge (sup_le hHS hKS) hle

theorem exists_conj_le_of_isPGroup [Finite M] {C T A : Subgroup M} (hTC : T ≤ C)
    (hT : IsPGroup 2 T) (hTind : ¬ 2 ∣ (T.subgroupOf C).index) (hAC : A ≤ C)
    (hA : IsPGroup 2 A) : ∃ m ∈ C, ∀ a ∈ A, m * a * m⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 (T.subgroupOf C) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
  have hA' : IsPGroup 2 (A.subgroupOf C) := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAC).symm
  let P : Sylow 2 C := hT'.toSylow hTind
  obtain ⟨R, hR⟩ := hA'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C P R
  refine ⟨(g : M)⁻¹, C.inv_mem g.2, fun a ha => ?_⟩
  have haR : (⟨a, hAC ha⟩ : C) ∈ ((g • P : Sylow 2 C) : Subgroup C) := by
    rw [hg]
    exact hR (Subgroup.mem_subgroupOf.mpr ha)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at haR
  have h2 : (g : M)⁻¹ * a * g ∈ T := haR
  simpa using h2

end CFSG.Quasithin.H13.F431.NF
