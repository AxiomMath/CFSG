module

public import CFSG.Quasithin.H13.NQTermInternalModule
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.Quasithin.H13.NQSetup

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open scoped IsMulCommutative

section QTNQ

variable {G : Type} [Group G] [Finite G]

theorem isCComponent_top_of_qtnq {T L M : Subgroup G} (h : QTNQ T L M) :
    CFSG.IsCComponent (⊤ : Subgroup L) := by
  have h1 : L ∈ cComp (L ⊔ T) := h.maximal_local.1.2.1
  have h2 : L ∈ cComp L := cComp_mem_of_le h1 le_rfl le_sup_left
  have h3 := mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp h2)
  rwa [subgroupOf_self] at h3

theorem qtnqU_le_qtnqVc {T L M : Subgroup G} (h : QTNQ T L M) : qtnqU L M ≤ qtnqVc M := by
  obtain ⟨-, hchar, -⟩ := NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have hMVc : M ≤ normalizer (qtnqVc M : Set G) :=
    le_normalizer.trans (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  rw [qtnqU, commutator_le]
  intro v hv l hl
  have hl' : l ∈ normalizer (qtnqVc M : Set G) := hMVc (h.l_le hl)
  have h1 : l * v⁻¹ * l⁻¹ ∈ qtnqVc M :=
    (mem_normalizer_iff.mp hl' v⁻¹).mp ((qtnqVc M).inv_mem hv)
  rw [commutatorElement_def, show v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) by group]
  exact (qtnqVc M).mul_mem hv h1

theorem radical_commute_qtnqVc {T L M : Subgroup G} (h : QTNQ T L M) {l : L}
    (hl : l ∈ CFSG.solvableRadical L) {v : G} (hv : v ∈ qtnqVc M) : (l : G) * v = v * l := by
  have h1 : (l : G) ∈ L ⊓ centralizer (qtnqVc M : Set G) := by
    rw [h.centralizer_eq_radical]
    exact ⟨l, hl, rfl⟩
  exact ((mem_centralizer_iff.mp (mem_inf.mp h1).2) v hv).symm

omit [Finite G] in
theorem normalizer_le_normalizer_of_characteristic {L X : Subgroup G} (hXL : X ≤ L)
    (hXc : (X.subgroupOf L).Characteristic) :
    normalizer (L : Set G) ≤ normalizer (X : Set G) := by
  have := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (X.subgroupOf L)
  rwa [map_subgroupOf_eq_of_le hXL] at this

theorem isSylowOf_inf_of_qtnq {T L M : Subgroup G} (h : QTNQ T L M) (u : G)
    (hQ : IsSylowOf 2 (T ⊓ centralizer {u}) (M ⊓ centralizer {u})) :
    IsSylowOf 2 (T ⊓ centralizer {u} ⊓ L) (L ⊓ centralizer {u}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : M ⊓ centralizer {u} ≤ normalizer ((L ⊓ centralizer {u} : Subgroup G) : Set G) := by
    intro m hm
    obtain ⟨hmM, hmC⟩ := mem_inf.mp hm
    have hmL : m ∈ normalizer (L : Set G) := h.eq_normalizer ▸ hmM
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hxL, hxC⟩ := mem_inf.mp hx
      exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hmL x).mp hxL,
        mul_mem (mul_mem hmC hxC) (inv_mem hmC)⟩
    · intro hx
      obtain ⟨hxL, hxC⟩ := mem_inf.mp hx
      refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hmL x).mpr hxL, ?_⟩
      have := mul_mem (mul_mem (inv_mem hmC) hxC) hmC
      simpa [mul_assoc] using this
  have h1 := hQ.inf_of_le_normalizer (inf_le_inf_right _ h.l_le) hnorm
  convert h1 using 1
  ext x
  simp only [mem_inf]
  tauto

end QTNQ

@[expose] noncomputable def mulAutLinear (p : ℕ) [Fact p.Prime] (V : Type*) [Group V]
    [IsElementaryAbelian p V] : MulAut V →* (Additive V ≃ₗ[ZMod p] Additive V) where
  toFun φ := (MulEquiv.toAdditive φ).toLinearEquiv fun c x =>
    ZMod.map_smul (MulEquiv.toAdditive φ).toAddMonoidHom c x
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

theorem mulAutLinear_apply (p : ℕ) [Fact p.Prime] {V : Type*} [Group V]
    [IsElementaryAbelian p V] (φ : MulAut V) (x : Additive V) :
    mulAutLinear p V φ x = Additive.ofMul (φ x.toMul) := rfl

theorem mulAutLinear_injective (p : ℕ) [Fact p.Prime] (V : Type*) [Group V]
    [IsElementaryAbelian p V] : Function.Injective (mulAutLinear p V) := by
  intro φ ψ hφψ
  ext x
  exact Additive.ofMul.injective (LinearEquiv.congr_fun hφψ (Additive.ofMul x))

theorem finrank_additive_eq_two {p : ℕ} [Fact p.Prime] {V : Type*} [Group V] [Finite V]
    [IsElementaryAbelian p V] (hV : Nat.card V = p ^ 2) :
    Module.finrank (ZMod p) (Additive V) = 2 := by
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : FiniteDimensional (ZMod p) (Additive V) := Module.Finite.of_finite
  have : Fintype (Additive V) := Fintype.ofFinite _
  have h := Module.card_eq_pow_finrank (K := ZMod p) (V := Additive V)
  rw [ZMod.card, ← Nat.card_eq_fintype_card,
    show Nat.card (Additive V) = Nat.card V from rfl, hV] at h
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm

end CFSG.Quasithin.H13.NQSetup
