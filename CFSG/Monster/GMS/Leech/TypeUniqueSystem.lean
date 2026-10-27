module

public import CFSG.Monster.GMS.Leech.Forms

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

theorem exists_leechSystem_of_hom
    (h13 : Co1ModuleUniqueness) {G : Type} [Group G] [Finite G]
    {z : G} (h : GMSLeechCentralizer z) (φ : Subgroup.centralizer ({z} : Set G) →* Co1)
    (hφs : Function.Surjective φ)
    (hφk : φ.ker = CFSG.pCore 2 (Subgroup.centralizer ({z} : Set G))) :
    ∃ L : LeechSystem z, L.φ = φ := by
  classical
  revert φ
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  set P : Subgroup C := CFSG.pCore 2 C with hP
  intro φ hφs hφk
  have hext := h.extraspecialData
  have hz2 : orderOf z = 2 := h.1
  have hQ : IsExtraspecialPGroup 2 P := h.2.1
  have hcard : Nat.card P = 2 ^ 25 := h.2.2.1
  have hcent : Subgroup.centralizer (P : Set C) ≤ P := h.2.2.2.2
  obtain ⟨v, hv1, hv2, hv3, hv4⟩ := exists_vec_of_extraspecial P h13 hQ hcard hcent φ hφs hφk
  let ι : P → G := fun x => ((x : C) : G)
  have hι_inj : Function.Injective ι := fun x y hxy => Subtype.ext (Subtype.ext hxy)
  have hmemQ : ∀ g, g ∈ leechQ z ↔ ∃ x : P, ι x = g := by
    intro g
    constructor
    · intro hg
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
  have hcenter : ∀ x : P, x ∈ Subgroup.center P ↔ ι x = 1 ∨ ι x = z := by
    intro x
    rw [← mem_zpowers_iff_of_orderOf_two hz2, ← center_pCore_map_eq_zpowers hz2 hQ hcent]
    constructor
    · intro hx
      exact ⟨(x : C), ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨w, hw, rfl⟩, hy⟩
      have : w = x := hι_inj hy
      rw [← this]
      exact hw
  let vec : G → Fin 24 → ZMod 2 := fun g =>
    if hg : g ∈ leechQ z then v (Classical.choose ((hmemQ g).1 hg)) else 0
  have hvec : ∀ x : P, vec (ι x) = v x := by
    intro x
    have hg : ι x ∈ leechQ z := (hmemQ _).2 ⟨x, rfl⟩
    simp only [vec, hg, ↓reduceDIte]
    congr 1
    exact hι_inj (Classical.choose_spec ((hmemQ _).1 hg))
  refine ⟨⟨φ, hφs, ?_, hext, ?_, vec, ?_, ?_, ?_, ?_⟩, rfl⟩
  · intro c
    rw [← MonoidHom.mem_ker, hφk, hmemQ]
    constructor
    · intro hc
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro ⟨x, hx⟩
      have : (x : C) = c := Subtype.ext hx
      rw [← this]
      exact x.2
  · intro q hq hcomm
    obtain ⟨x, rfl⟩ := (hmemQ q).1 hq
    refine (hcenter x).1 (Subgroup.mem_center_iff.mpr fun y => ?_)
    exact Subtype.ext (Subtype.ext (hcomm (ι y) ((hmemQ _).2 ⟨y, rfl⟩)))
  · intro p hp q hq
    obtain ⟨x, rfl⟩ := (hmemQ p).1 hp
    obtain ⟨y, rfl⟩ := (hmemQ q).1 hq
    have : ι x * ι y = ι (x * y) := rfl
    rw [this, hvec, hvec, hvec, hv1]
  · intro q hq
    obtain ⟨x, rfl⟩ := (hmemQ q).1 hq
    rw [hvec, hv2, hcenter]
  · intro c q hq
    obtain ⟨x, rfl⟩ := (hmemQ q).1 hq
    have : (c : G) * ι x * (c : G)⁻¹ = ι (MulAut.conjNormal c x) := by
      simp [ι, MulAut.conjNormal_apply]
    rw [this, hvec, hv3, hvec]
  · intro w
    obtain ⟨x, hx⟩ := hv4 w
    exact ⟨ι x, (hmemQ _).2 ⟨x, rfl⟩, by rw [hvec, hx]⟩

structure LeechTypeSystem (H : Type) [Group H] where
  φ : H →* Co1
  φ_surj : Function.Surjective φ
  z : H
  vec : H → Fin 24 → ZMod 2
  z_mul_self : z * z = 1
  z_ne_one : z ≠ 1
  z_comm : ∀ c : H, c * z = z * c
  φ_z : φ z = 1
  vec_mul : ∀ p q, φ p = 1 → φ q = 1 → vec (p * q) = vec p + vec q
  vec_eq_zero : ∀ q, φ q = 1 → (vec q = 0 ↔ q = 1 ∨ q = z)
  vec_conj : ∀ c q, φ q = 1 → vec (c * q * c⁻¹) = co1Act (φ c) (vec q)
  vec_surj : ∀ w, ∃ q, φ q = 1 ∧ vec q = w
  mul_self_eq_one_iff : ∀ q, φ q = 1 → (q * q = 1 ↔ CFSG.Sporadic.Co1.Module.q₀ (vec q) = 0)
  mul_self_eq_z_iff : ∀ q, φ q = 1 → (q * q = z ↔ CFSG.Sporadic.Co1.Module.q₀ (vec q) = 1)
  comm_eq_one_iff : ∀ p q, φ p = 1 → φ q = 1 →
    (⁅p, q⁆ = 1 ↔ CFSG.Sporadic.Co1.Module.bil₀ (vec p) (vec q) = 0)
  comm_eq_z_iff : ∀ p q, φ p = 1 → φ q = 1 →
    (⁅p, q⁆ = z ↔ CFSG.Sporadic.Co1.Module.bil₀ (vec p) (vec q) = 1)
  center_eq : ∀ q, φ q = 1 → (∀ p, φ p = 1 → p * q = q * p) → q = 1 ∨ q = z

namespace LeechTypeSystem

variable {H : Type} [Group H] (S : LeechTypeSystem H)

theorem vec_one : S.vec 1 = 0 := (S.vec_eq_zero 1 (map_one S.φ)).2 (Or.inl rfl)

theorem vec_z : S.vec S.z = 0 := (S.vec_eq_zero S.z S.φ_z).2 (Or.inr rfl)

theorem vec_inv {q : H} (hq : S.φ q = 1) : S.vec q⁻¹ = S.vec q := by
  have h := S.vec_mul q q⁻¹ hq (by rw [map_inv, hq, inv_one])
  rw [mul_inv_cancel, S.vec_one] at h
  have h2 : S.vec q + S.vec q = 0 := CFSG.Sporadic.Co1.Module.vec_add_self (S.vec q)
  exact add_left_cancel (h.symm.trans h2.symm)

theorem comm_cases {p q : H} (hp : S.φ p = 1) (hq : S.φ q = 1) : ⁅p, q⁆ = 1 ∨ ⁅p, q⁆ = S.z := by
  rcases CFSG.Sporadic.Co1.Module.zmod2_cases
      (CFSG.Sporadic.Co1.Module.bil₀ (S.vec p) (S.vec q)) with h | h
  · exact Or.inl ((S.comm_eq_one_iff p q hp hq).2 h)
  · exact Or.inr ((S.comm_eq_z_iff p q hp hq).2 h)

end LeechTypeSystem

namespace LeechSystem

variable {G : Type} [Group G] {z : G} (L : LeechSystem z)

@[expose] def toTypeSystem :
    LeechTypeSystem (Subgroup.centralizer ({z} : Set G)) where
  φ := L.φ
  φ_surj := L.φ_surj
  z := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  vec := fun c => L.vec c
  z_mul_self := Subtype.ext L.z_mul_self
  z_ne_one := fun h => L.z_ne_one (congrArg Subtype.val h)
  z_comm := fun c => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2)
  φ_z := (L.φ_ker _).2 L.z_mem
  vec_mul := fun p q hp hq => L.vec_mul p ((L.φ_ker p).1 hp) q ((L.φ_ker q).1 hq)
  vec_eq_zero := fun q hq => by
    rw [L.vec_eq_zero q ((L.φ_ker q).1 hq), Subtype.ext_iff, Subtype.ext_iff]
    rfl
  vec_conj := fun c q hq => L.vec_conj c q ((L.φ_ker q).1 hq)
  vec_surj := fun w => by
    obtain ⟨q, hq, hqw⟩ := L.vec_surj w
    exact ⟨⟨q, L.mem_centralizer hq⟩, (L.φ_ker _).2 hq, hqw⟩
  mul_self_eq_one_iff := fun q hq => by
    rw [← L.mul_self_eq_one_iff ((L.φ_ker q).1 hq), Subtype.ext_iff]
    rfl
  mul_self_eq_z_iff := fun q hq => by
    rw [← L.mul_self_eq_z_iff ((L.φ_ker q).1 hq), Subtype.ext_iff]
    rfl
  comm_eq_one_iff := fun p q hp hq => by
    rw [← L.comm_eq_one_iff ((L.φ_ker p).1 hp) ((L.φ_ker q).1 hq), Subtype.ext_iff]
    rfl
  comm_eq_z_iff := fun p q hp hq => by
    rw [← L.comm_eq_z_iff ((L.φ_ker p).1 hp) ((L.φ_ker q).1 hq), Subtype.ext_iff]
    rfl
  center_eq := fun q hq hcomm => by
    have h := L.center_eq q ((L.φ_ker q).1 hq) fun p hp =>
      congrArg Subtype.val (hcomm ⟨p, L.mem_centralizer hp⟩ ((L.φ_ker _).2 hp))
    rw [Subtype.ext_iff, Subtype.ext_iff]
    exact h

end LeechSystem

end CFSG.Monster.GMS
