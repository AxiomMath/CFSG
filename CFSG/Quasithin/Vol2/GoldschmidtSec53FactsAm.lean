module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsGen

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F1

section Equiv

variable {X Y : Type} [Group X] [Group Y]

theorem mem_centerOf_iff_of_equiv {Q A : Subgroup X} {Q' A' : Subgroup Y} (e : ↥Q ≃* ↥Q')
    (hA : A ≤ Q) (hA' : A' ≤ Q') (hmem : ∀ x : ↥Q, (x : X) ∈ A ↔ ((e x : ↥Q') : Y) ∈ A')
    (x : ↥Q) : (x : X) ∈ centerOf A ↔ ((e x : ↥Q') : Y) ∈ centerOf A' := by
  constructor
  · rintro ⟨hxA, hxc⟩
    refine ⟨(hmem x).mp hxA, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨w, hw⟩ := e.surjective ⟨y, hA' hy⟩
    have hwA : (w : X) ∈ A := (hmem w).mpr (by rw [hw]; exact hy)
    have h1 : (w : X) * x = x * w := Subgroup.mem_centralizer_iff.mp hxc w hwA
    have h2 : w * x = x * w := Subtype.ext h1
    have h3 : e w * e x = e x * e w := by rw [← map_mul, ← map_mul, h2]
    rw [hw] at h3
    exact congrArg Subtype.val h3
  · rintro ⟨hxA, hxc⟩
    refine ⟨(hmem x).mpr hxA, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    have haQ : a ∈ Q := hA ha
    have h1 := Subgroup.mem_centralizer_iff.mp hxc ((e ⟨a, haQ⟩ : ↥Q') : Y)
      ((hmem ⟨a, haQ⟩).mp ha)
    have h2 : e (⟨a, haQ⟩ * x) = e (x * ⟨a, haQ⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext h1
    have h3 := e.injective h2
    exact congrArg Subtype.val h3

theorem exists_conj_of_equiv {Q A C : Subgroup X} {Q' A' : Subgroup Y} (e : ↥Q ≃* ↥Q')
    (hC : C ≤ Subgroup.normalizer (A : Set X)) (hQ : Q = A ⊔ C) (hA' : A' ≤ Q')
    (hmem : ∀ x : ↥Q, (x : X) ∈ A ↔ ((e x : ↥Q') : Y) ∈ A') {R : X → Prop} {R' : Y → Prop}
    (hR : ∀ x : ↥Q, R x ↔ R' ((e x : ↥Q') : Y))
    (htrans : ∀ a ∈ centerOf A', R' a → ∀ a' ∈ centerOf A', R' a' → ∃ m ∈ Q', m * a * m⁻¹ = a')
    {z z' : X} (hz : z ∈ centerOf A) (hz' : z' ∈ centerOf A) (hRz : R z) (hRz' : R z') :
    ∃ c ∈ C, c * z * c⁻¹ = z' := by
  have hAQ : A ≤ Q := hQ ▸ le_sup_left
  have hzq : z ∈ Q := hAQ (Subgroup.mem_inf.mp hz).1
  have hzq' : z' ∈ Q := hAQ (Subgroup.mem_inf.mp hz').1
  have ha := (mem_centerOf_iff_of_equiv e hAQ hA' hmem ⟨z, hzq⟩).mp hz
  have ha' := (mem_centerOf_iff_of_equiv e hAQ hA' hmem ⟨z', hzq'⟩).mp hz'
  obtain ⟨m', hm', hmm⟩ := htrans _ ha ((hR ⟨z, hzq⟩).mp hRz) _ ha' ((hR ⟨z', hzq'⟩).mp hRz')
  set m : ↥Q := e.symm ⟨m', hm'⟩ with hm
  have key : m * ⟨z, hzq⟩ * m⁻¹ = ⟨z', hzq'⟩ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, hm, MulEquiv.apply_symm_apply]
    exact Subtype.ext hmm
  exact exists_conj_of_mem_sup hC hz (hQ ▸ m.2) (congrArg Subtype.val key)

theorem ne_one_iff_of_equiv {Q : Subgroup X} {Q' : Subgroup Y} (e : ↥Q ≃* ↥Q') (x : ↥Q) :
    (x : X) ≠ 1 ↔ ((e x : ↥Q') : Y) ≠ 1 := by
  constructor
  · intro hx h
    apply hx
    have : e x = 1 := Subtype.ext (by rw [h]; rfl)
    have h1 := e.injective (this.trans (map_one e).symm)
    rw [h1]
    rfl
  · intro hx h
    apply hx
    have : x = 1 := Subtype.ext (by rw [h]; rfl)
    rw [this, map_one]
    rfl

theorem mem_pCoreOf_iff_of_equiv {A : Subgroup X} {C : Subgroup Y} (e : ↥A ≃* ↥C) (a : ↥A) :
    (a : X) ∈ pCoreOf 2 A ↔ ((e a : ↥C) : Y) ∈ pCoreOf 2 C := by
  unfold pCoreOf
  rw [show (a : X) = A.subtype a from rfl, show ((e a : ↥C) : Y) = C.subtype (e a) from rfl,
    Subgroup.mem_map_iff_mem A.subtype_injective, Subgroup.mem_map_iff_mem C.subtype_injective,
    ← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e]
  exact (Subgroup.mem_map_iff_mem e.injective).symm

end Equiv

end CFSG.Quasithin.H13.Sec53F
