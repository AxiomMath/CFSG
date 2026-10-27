module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBDefs

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

structure StdData (G : Type) [Group G] (T L I K : Subgroup G) (m k n j : ℕ) where
  α : ↥K →* GL (Fin n) (ZMod 2)
  β : ↥(uZero I K) →* Multiplicative (Fin j → Fin n → ZMod 2)
  surj : Function.Surjective α
  ker_eq : α.ker = CFSG.pCore 2 ↥K
  bij : Function.Bijective β
  equi : ∀ (x : ↥K) (u v : ↥(uZero I K)), (v : G) = x * u * (x : G)⁻¹ → ∀ i : Fin j,
    Multiplicative.toAdd (β v) i =
      ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
        (Multiplicative.toAdd (β u) i)
  vcoord : ∀ v : ↥(uZero I K), (v : G) ∈ vV T L → ∀ (i : Fin j) (b : Fin n), m ≤ b.val →
    Multiplicative.toAdd (β v) i b = 0
  cover : ∀ x : Fin n → ZMod 2, (∀ b : Fin n, m ≤ b.val → x b = 0) →
    ∃ v : ↥(uZero I K), (v : G) ∈ vV T L ∧ ∃ i : Fin j, Multiplicative.toAdd (β v) i = x
  veq : j = k → ∀ z : ↥(uZero I K),
    (∀ (i : Fin j) (b : Fin n), m ≤ b.val → Multiplicative.toAdd (β z) i b = 0) →
      (z : G) ∈ vV T L


private theorem neg_eq_self_coG {j n : ℕ} (t : Fin j → Fin n → ZMod 2) : -t = t := by
  have h : ∀ c : ZMod 2, -c = c := by decide
  funext i b
  simp only [Pi.neg_apply]
  exact h _

section CoG

variable {G : Type} [Group G] {T L I K : Subgroup G} {m k n j : ℕ}

@[expose] noncomputable def coG (D : StdData G T L I K m k n j) (x : G) :
    Fin j → Fin n → ZMod 2 :=
  open Classical in
  if h : x ∈ uZero I K then Multiplicative.toAdd (D.β ⟨x, h⟩) else 0

theorem coG_of_mem (D : StdData G T L I K m k n j) (z : ↥(uZero I K)) :
    coG D (z : G) = Multiplicative.toAdd (D.β z) := by
  unfold coG
  rw [dif_pos z.2]

theorem coG_one (D : StdData G T L I K m k n j) : coG D 1 = 0 := by
  have h1 : (1 : G) ∈ uZero I K := (uZero I K).one_mem
  have h2 : (⟨1, h1⟩ : ↥(uZero I K)) = 1 := rfl
  unfold coG
  rw [dif_pos h1, h2, map_one, toAdd_one]

theorem coG_mul (D : StdData G T L I K m k n j) {x y : G} (hx : x ∈ uZero I K)
    (hy : y ∈ uZero I K) : coG D (x * y) = coG D x + coG D y := by
  have hxy : x * y ∈ uZero I K := mul_mem hx hy
  have e : (⟨x * y, hxy⟩ : ↥(uZero I K)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  unfold coG
  rw [dif_pos hxy, dif_pos hx, dif_pos hy, e, map_mul, toAdd_mul]

theorem coG_inv (D : StdData G T L I K m k n j) {x : G} (hx : x ∈ uZero I K) :
    coG D x⁻¹ = coG D x := by
  have hxi : x⁻¹ ∈ uZero I K := inv_mem hx
  have e : (⟨x⁻¹, hxi⟩ : ↥(uZero I K)) = (⟨x, hx⟩ : ↥(uZero I K))⁻¹ := rfl
  unfold coG
  rw [dif_pos hxi, dif_pos hx, e, map_inv, toAdd_inv, neg_eq_self_coG]

theorem coG_injOn (D : StdData G T L I K m k n j) {x y : G} (hx : x ∈ uZero I K)
    (hy : y ∈ uZero I K) (h : coG D x = coG D y) : x = y := by
  have h1 : coG D x = Multiplicative.toAdd (D.β ⟨x, hx⟩) := coG_of_mem D ⟨x, hx⟩
  have h2 : coG D y = Multiplicative.toAdd (D.β ⟨y, hy⟩) := coG_of_mem D ⟨y, hy⟩
  rw [h1, h2] at h
  have h3 : D.β ⟨x, hx⟩ = D.β ⟨y, hy⟩ := Multiplicative.toAdd.injective h
  exact congrArg Subtype.val (D.bij.1 h3)

theorem exists_coG_eq (D : StdData G T L I K m k n j) (t : Fin j → Fin n → ZMod 2) :
    ∃ x : G, x ∈ uZero I K ∧ coG D x = t := by
  obtain ⟨z, hz⟩ := D.bij.2 (Multiplicative.ofAdd t)
  refine ⟨(z : G), z.2, ?_⟩
  rw [coG_of_mem D z, hz, toAdd_ofAdd]

theorem coG_conj_K (D : StdData G T L I K m k n j) {x : ↥K} {z : G} (hz : z ∈ uZero I K)
    (hxz : (x : G) * z * (x : G)⁻¹ ∈ uZero I K) (i : Fin j) :
    coG D ((x : G) * z * (x : G)⁻¹) i =
      ((D.α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (coG D z i) := by
  have h1 : coG D ((x : G) * z * (x : G)⁻¹) =
      Multiplicative.toAdd (D.β ⟨(x : G) * z * (x : G)⁻¹, hxz⟩) :=
    coG_of_mem D ⟨(x : G) * z * (x : G)⁻¹, hxz⟩
  have h2 : coG D z = Multiplicative.toAdd (D.β ⟨z, hz⟩) := coG_of_mem D ⟨z, hz⟩
  rw [h1, h2]
  exact D.equi x ⟨z, hz⟩ ⟨(x : G) * z * (x : G)⁻¹, hxz⟩ rfl i

end CoG

end CFSG.Quasithin.H13.Ch4.NSB
