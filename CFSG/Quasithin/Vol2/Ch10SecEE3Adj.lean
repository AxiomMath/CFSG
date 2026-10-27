module

public import CFSG.Quasithin.Vol2.Ch10SecEOver

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

def innerLike (T₁ B : Subgroup G) (hT₁B : T₁ ≤ Subgroup.normalizer (B : Set G)) : Subgroup G where
  carrier := {y | y ∈ T₁ ∧ ∀ b ∈ B, y * b * y⁻¹ * b⁻¹ ∈ pCoreOf 2 B}
  mul_mem' := fun {y z} hy hz => ⟨T₁.mul_mem hy.1 hz.1, fun b hb => by
    have hzb : z * b * z⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hT₁B hz.1) b).mp hb
    have hO : y ∈ Subgroup.normalizer (pCoreOf 2 B : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B (hT₁B hy.1)
    have e : y * z * b * (y * z)⁻¹ * b⁻¹ =
        (y * (z * b * z⁻¹ * b⁻¹) * y⁻¹) * (y * b * y⁻¹ * b⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 B).mul_mem ((Subgroup.mem_normalizer_iff.mp hO _).mp (hz.2 b hb))
      (hy.2 b hb)⟩
  one_mem' := ⟨T₁.one_mem, fun b _ => by simp⟩
  inv_mem' := fun {y} hy => ⟨T₁.inv_mem hy.1, fun b hb => by
    have hb' : y⁻¹ * b * y⁻¹⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hT₁B (T₁.inv_mem hy.1)) b).mp hb
    have h1 := (pCoreOf 2 B).inv_mem (hy.2 _ hb')
    have e : y⁻¹ * b * y⁻¹⁻¹ * b⁻¹ =
        (y * (y⁻¹ * b * y⁻¹⁻¹) * y⁻¹ * (y⁻¹ * b * y⁻¹⁻¹)⁻¹)⁻¹ := by group
    rw [e]
    exact h1⟩

omit [Finite G] in
theorem mem_innerLike {T₁ B : Subgroup G} {hT₁B : T₁ ≤ Subgroup.normalizer (B : Set G)} {y : G} :
    y ∈ innerLike T₁ B hT₁B ↔ y ∈ T₁ ∧ ∀ b ∈ B, y * b * y⁻¹ * b⁻¹ ∈ pCoreOf 2 B :=
  Iff.rfl

omit [Finite G] in
theorem le_normalizer_innerLike {T₁ B : Subgroup G} (hT₁B : T₁ ≤ Subgroup.normalizer (B : Set G)) :
    T₁ ≤ Subgroup.normalizer (innerLike T₁ B hT₁B : Set G) := by
  have key : ∀ s ∈ T₁, ∀ y ∈ innerLike T₁ B hT₁B, s * y * s⁻¹ ∈ innerLike T₁ B hT₁B := by
    intro s hs y hy
    refine ⟨T₁.mul_mem (T₁.mul_mem hs hy.1) (T₁.inv_mem hs), fun b hb => ?_⟩
    have hb' : s⁻¹ * b * s⁻¹⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hT₁B (T₁.inv_mem hs)) b).mp hb
    have hO : s ∈ Subgroup.normalizer (pCoreOf 2 B : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B (hT₁B hs)
    have e : s * y * s⁻¹ * b * (s * y * s⁻¹)⁻¹ * b⁻¹ =
        s * (y * (s⁻¹ * b * s⁻¹⁻¹) * y⁻¹ * (s⁻¹ * b * s⁻¹⁻¹)⁻¹) * s⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hO _).mp (hy.2 _ hb')
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key s hs y, fun h => ?_⟩
  have h1 := key s⁻¹ (T₁.inv_mem hs) _ h
  simpa [mul_assoc] using h1

theorem exists_centralizer_lift {T₁ B U : Subgroup G} (hT₁B : T₁ ≤ Subgroup.normalizer (B : Set G))
    (hT₁ : IsPGroup 2 T₁)
    (hO : pCoreOf 2 (B ⊔ T₁) = U ⊔ (T₁ ⊓ Subgroup.centralizer (B : Set G)))
    (hUN : T₁ ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (U : Set G))
    (hU2 : ∀ u ∈ U, u ^ 2 = 1) {x : G} (hx : x ∈ innerLike T₁ B hT₁B) (hx2 : x ^ 2 = 1)
    (hxU : ∀ u ∈ U, x * u = u * x) :
    ∃ c ∈ T₁ ⊓ Subgroup.centralizer (B : Set G), c ^ 2 = 1 ∧ x * c⁻¹ ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := innerLike T₁ B hT₁B
  have hYT : Y ≤ T₁ := fun y hy => hy.1
  have hBO : B ≤ Subgroup.normalizer (pCoreOf 2 B : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B
  have hT₁O : T₁ ≤ Subgroup.normalizer (pCoreOf 2 B : Set G) :=
    hT₁B.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B)
  have hYN : Y ≤ Subgroup.normalizer (pCoreOf 2 B : Set G) := hYT.trans hT₁O
  set Q := Y ⊔ pCoreOf 2 B
  have hQ2 : IsPGroup 2 ↥Q := IsPGroup.to_sup_of_normal_right' (hT₁.to_le hYT)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B) hYN
  have hQX : Q ≤ B ⊔ T₁ :=
    sup_le (hYT.trans le_sup_right) ((CFSG.LieType.BorelTits.pCoreOf_le 2 B).trans le_sup_left)
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right Y (pCoreOf 2 B) hYN
  have hBQ : ∀ b ∈ B, ∀ q ∈ Q, b * q * b⁻¹ ∈ Q := by
    intro b hb q hq
    have hq' : q ∈ (Y : Set G) * (pCoreOf 2 B : Set G) := by rw [← hcoe]; exact hq
    obtain ⟨y, hy, o, ho, rfl⟩ := Set.mem_mul.mp hq'
    have h1 : b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 B := by
      have h2 := hy.2 b⁻¹ (B.inv_mem hb)
      have h3 := (Subgroup.mem_normalizer_iff.mp (hBO hb) _).mp h2
      have e : b * y * b⁻¹ * y⁻¹ = b * (y * b⁻¹ * y⁻¹ * b⁻¹⁻¹) * b⁻¹ := by group
      rw [e]
      exact h3
    have e : b * (y * o) * b⁻¹ = (b * y * b⁻¹ * y⁻¹) * y * (b * o * b⁻¹) := by group
    rw [e]
    refine Q.mul_mem (Q.mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hy))
      (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hBO hb) o).mp ho))
  have hXN : B ⊔ T₁ ≤ Subgroup.normalizer (Q : Set G) := by
    refine sup_le (fun b hb => ?_) (le_normalizer_sup_of_le (le_normalizer_innerLike hT₁B) hT₁O)
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨hBQ b hb q, fun h => ?_⟩
    have h1 := hBQ b⁻¹ (B.inv_mem hb) _ h
    simpa [mul_assoc] using h1
  have hQO : Q ≤ pCoreOf 2 (B ⊔ T₁) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQX hXN hQ2
  have hxO : x ∈ U ⊔ (T₁ ⊓ Subgroup.centralizer (B : Set G)) :=
    hO ▸ hQO (Subgroup.mem_sup_left hx)
  have hcoe' := Subgroup.coe_mul_of_right_le_normalizer_left U _ hUN
  have hx' : x ∈ (U : Set G) * ((T₁ ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) := by
    rw [← hcoe']; exact hxO
  obtain ⟨u, hu, c, hc, rfl⟩ := Set.mem_mul.mp hx'
  refine ⟨c, hc, ?_, by rw [mul_inv_cancel_right]; exact hu⟩
  have hcu : c = u⁻¹ * (u * c) := by group
  have hxu := hxU u⁻¹ (U.inv_mem hu)
  have hu2 : u⁻¹ * u⁻¹ = 1 := by
    rw [← mul_inv_rev, ← pow_two, hU2 u hu, inv_one]
  rw [pow_two] at hx2 ⊢
  calc c * c = u⁻¹ * ((u * c) * u⁻¹) * (u * c) := by group
    _ = u⁻¹ * (u⁻¹ * (u * c)) * (u * c) := by rw [hxu]
    _ = (u⁻¹ * u⁻¹) * ((u * c) * (u * c)) := by group
    _ = 1 := by rw [hu2, hx2, one_mul]

end CFSG.Quasithin.Vol2.Ch10.SecE
