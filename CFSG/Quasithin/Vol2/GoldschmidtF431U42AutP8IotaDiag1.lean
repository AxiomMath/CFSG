module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Tr

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

theorem braid_of_pow_four {X : Type*} [Group X] {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (h : (a * b) ^ 4 = 1) : a * b * a * b = b * a * b * a := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h2 : (a * b * a * b) * (a * b * a * b) = 1 := by
    have : (a * b) ^ 4 = (a * b * a * b) * (a * b * a * b) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [← this]
    exact h
  have h3 : a * b * a * b = (a * b * a * b)⁻¹ := eq_inv_of_mul_eq_one_left h2
  rw [h3]
  simp [mul_inv_rev, hai, hbi, mul_assoc]

structure AhBN (s t : Ah) (us ut : List Ah) : Prop where
  s1 : s ∈ P1h
  s2 : s * s = 1
  s3 : s ∉ Bh
  t1 : t ∈ P2h
  t2 : t * t = 1
  t3 : t ∉ Bh
  braid : s * t * s * t = t * s * t * s
  us_B : ∀ u ∈ us, u ∈ Bh
  ut_B : ∀ u ∈ ut, u ∈ Bh
  cos1 : ∀ x ∈ P1h, x ∈ Bh ∨ ∃ v ∈ us, ∃ b ∈ Bh, v * x = s * b
  cos2 : ∀ x ∈ P2h, x ∈ Bh ∨ ∃ v ∈ ut, ∃ b ∈ Bh, v * x = t * b
  us_chain : ∀ u ∈ us, t * u * t ∈ Bh ∧ s * (t * u * t) * s ∈ Bh ∧
    t * (s * (t * u * t) * s) * t ∈ Bh
  ut_chain : ∀ u ∈ ut, s * u * s ∈ Bh ∧ t * (s * u * s) * t ∈ Bh ∧
    s * (t * (s * u * s) * t) * s ∈ Bh
  us_len : us.length ≤ 2
  ut_len : ut.length ≤ 4

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G}

@[expose] def gr1 (iso : AutIso M₁ M₂) : ↥P1h →* Ah × G := (P1h.subtype).prod iso.toG1

@[expose] def gr2 (iso : AutIso M₁ M₂) : ↥P2h →* Ah × G := (P2h.subtype).prod iso.toG2

@[expose] def grB (iso : AutIso M₁ M₂) : ↥Bh →* Ah × G :=
  (gr1 iso).comp (Subgroup.inclusion Bh_le_P1h)

theorem gr1_apply (iso : AutIso M₁ M₂) (x : ↥P1h) : gr1 iso x = ((x : Ah), iso.toG1 x) := rfl

theorem gr2_apply (iso : AutIso M₁ M₂) (x : ↥P2h) : gr2 iso x = ((x : Ah), iso.toG2 x) := rfl

theorem gr2_incl (iso : AutIso M₁ M₂) (b : ↥Bh) :
    gr2 iso (Subgroup.inclusion Bh_le_P2h b) = grB iso b := by
  refine Prod.ext rfl ?_
  show iso.toG2 (Subgroup.inclusion Bh_le_P2h b) = iso.toG1 (Subgroup.inclusion Bh_le_P1h b)
  rw [iso.toG2_inclusion, iso.toG1_inclusion]

theorem gr1_injective (iso : AutIso M₁ M₂) : Function.Injective (gr1 iso) := fun _ _ h =>
  Subtype.ext (congrArg Prod.fst h)

theorem grB_injective (iso : AutIso M₁ M₂) : Function.Injective (grB iso) :=
  (gr1_injective iso).comp (Subgroup.inclusion_injective _)

open scoped Classical in
@[expose] noncomputable def grBf (iso : AutIso M₁ M₂) (x : Ah) : Ah × G :=
  if h : x ∈ Bh then grB iso ⟨x, h⟩ else 1

theorem grBf_of_mem (iso : AutIso M₁ M₂) {x : Ah} (h : x ∈ Bh) : grBf iso x = grB iso ⟨x, h⟩ := by
  simp [grBf, h]

theorem gr1_eq_grBf (iso : AutIso M₁ M₂) (y : ↥P1h) (hy : (y : Ah) ∈ Bh) :
    gr1 iso y = grBf iso y := by
  rw [grBf_of_mem iso hy]
  rfl

theorem gr2_eq_grBf (iso : AutIso M₁ M₂) (y : ↥P2h) (hy : (y : Ah) ∈ Bh) :
    gr2 iso y = grBf iso y := by
  rw [grBf_of_mem iso hy, ← gr2_incl iso ⟨y, hy⟩]
  rfl

end CFSG.Quasithin.H13.F431.U42Aut
