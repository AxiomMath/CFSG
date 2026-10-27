module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4G2Rho

public section

namespace CFSG.Quasithin.F6.GoldAmL5

open CFSG.Quasithin.F6.GoldAmL4

structure Tr where
  v : Fin 4 × Fin 4
  g : Fin 2 × Fin 2
deriving DecidableEq, Fintype

namespace Tr

abbrev i (x : Tr) : Fin 4 := x.v.1
abbrev j (x : Tr) : Fin 4 := x.v.2
abbrev e (x : Tr) : Fin 2 := x.g.1
abbrev f (x : Tr) : Fin 2 := x.g.2

@[expose] def act (g : Fin 2 × Fin 2) (v : Fin 4 × Fin 4) : Fin 4 × Fin 4 :=
  if g.1 = 0 then (if g.2 = 0 then v else (-v.1, -v.2))
  else (if g.2 = 0 then (v.2, v.1) else (-v.2, -v.1))

theorem act_add : ∀ (g : Fin 2 × Fin 2) (v w : Fin 4 × Fin 4),
    act g (v + w) = act g v + act g w := by decide +kernel

theorem act_comp : ∀ (g h : Fin 2 × Fin 2) (v : Fin 4 × Fin 4),
    act (g + h) v = act g (act h v) := by decide +kernel

theorem act_zero_left : ∀ v : Fin 4 × Fin 4, act 0 v = v := by decide +kernel

theorem act_zero_right : ∀ g : Fin 2 × Fin 2, act g 0 = 0 := by decide +kernel

instance : Mul Tr := ⟨fun x y => ⟨x.v + act x.g y.v, x.g + y.g⟩⟩
instance : One Tr := ⟨⟨0, 0⟩⟩
instance : Inv Tr := ⟨fun x => ⟨act x.g (-x.v), x.g⟩⟩

theorem mul_def (x y : Tr) : x * y = ⟨x.v + act x.g y.v, x.g + y.g⟩ := rfl
theorem one_def : (1 : Tr) = ⟨0, 0⟩ := rfl
theorem inv_def (x : Tr) : x⁻¹ = ⟨act x.g (-x.v), x.g⟩ := rfl

theorem act_neg : ∀ (g : Fin 2 × Fin 2) (v : Fin 4 × Fin 4), act g (-v) = -act g v := by
  decide +kernel

theorem act_self : ∀ g : Fin 2 × Fin 2, g + g = 0 := by decide +kernel

instance : Group Tr where
  mul_assoc := by
    intro x y z
    simp only [mul_def, act_add, act_comp, add_assoc]
  one_mul := by
    intro x
    simp only [mul_def, one_def, act_zero_left, zero_add]
  mul_one := by
    intro x
    simp only [mul_def, one_def, act_zero_right, add_zero]
  inv_mul_cancel := by
    intro x
    simp only [mul_def, inv_def, one_def]
    rw [← act_add, neg_add_cancel, act_zero_right, act_self]

end Tr

theorem card_Tr : Nat.card Tr = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] def rA : Tr := ⟨(1, 0), (0, 0)⟩
@[expose] def rB : Tr := ⟨(0, 1), (0, 0)⟩
@[expose] def rS : Tr := ⟨(0, 0), (1, 0)⟩
@[expose] def rR : Tr := ⟨(0, 0), (0, 1)⟩

theorem tr_nf : ∀ x : Tr, x = rA ^ x.i.val * rB ^ x.j.val * rS ^ x.e.val * rR ^ x.f.val := by
  decide +kernel

theorem tr_pow8 : ∀ x : Tr, x ^ 8 = 1 := by decide +kernel

theorem rA_pow_four : rA ^ 4 = 1 := by decide +kernel
theorem rB_pow_four : rB ^ 4 = 1 := by decide +kernel
theorem rS_sq : rS * rS = 1 := by decide +kernel
theorem rR_sq : rR * rR = 1 := by decide +kernel
theorem rA_mul_rB : rA * rB = rB * rA := by decide +kernel
theorem rS_rA_rS : rS * rA * rS = rB := by decide +kernel
theorem rR_rA_rR : rR * rA * rR = rA⁻¹ := by decide +kernel
theorem rR_rB_rR : rR * rB * rR = rB⁻¹ := by decide +kernel
theorem rR_rS_rR : rR * rS * rR = rS := by decide +kernel
theorem rA_ne_rB : rA ≠ rB := by decide +kernel
theorem rS_ne_rR : rS ≠ rR := by decide +kernel

section Emb

variable {E : Type*} [Group E] {a b s ρ : E}

@[expose] def toTc (x : Tr) : Tc := ⟨x.i, x.j, x.e⟩

theorem toTc_mul (x y : Tr) :
    toTc (x * y) = toTc x * (if x.f = 0 then toTc y else sigma (toTc y)) := by
  obtain ⟨⟨i, j⟩, ⟨e, f⟩⟩ := x
  obtain ⟨⟨k, l⟩, ⟨g, h⟩⟩ := y
  fin_cases e <;> fin_cases f <;> rfl

theorem toTc_one : toTc (1 : Tr) = 1 := rfl

@[expose] def embR (hT : TRel a b s) (hR : RhoRel a b s ρ) : Tr →* E where
  toFun x := hT.emb (toTc x) * ρ ^ x.f.val
  map_one' := by
    have h0 : (1 : Tr).f = 0 := rfl
    rw [toTc_one, map_one, h0]
    simp
  map_mul' := by
    intro x y
    have hρ : ρ * ρ = 1 := hR.hρ
    have hc : ∀ w : Tc, hT.emb (sigma w) = ρ * hT.emb w * ρ := fun w => (hR.conj_emb hT w).symm
    have key : ∀ fx fy : Fin 2,
        hT.emb (toTc x * (if fx = 0 then toTc y else sigma (toTc y))) * ρ ^ (fx + fy).val =
          hT.emb (toTc x) * ρ ^ fx.val * (hT.emb (toTc y) * ρ ^ fy.val) := by
      intro fx fy
      fin_cases fx <;> fin_cases fy <;> simp [map_mul, hc, mul_assoc, hρ]
    show hT.emb (toTc (x * y)) * ρ ^ (x * y).f.val =
      hT.emb (toTc x) * ρ ^ x.f.val * (hT.emb (toTc y) * ρ ^ y.f.val)
    rw [toTc_mul]
    exact key x.f y.f

variable (hT : TRel a b s) (hR : RhoRel a b s ρ)

theorem embR_apply (x : Tr) : embR hT hR x = hT.emb (toTc x) * ρ ^ x.f.val := rfl

theorem embR_rA : embR hT hR rA = a := by
  rw [embR_apply]
  have : toTc rA = tA := rfl
  rw [this, hT.emb_tA]
  simp [rA]

theorem embR_rB : embR hT hR rB = b := by
  rw [embR_apply]
  have : toTc rB = tB := rfl
  rw [this, hT.emb_tB]
  simp [rB]

theorem embR_rS : embR hT hR rS = s := by
  rw [embR_apply]
  have : toTc rS = tS := rfl
  rw [this, hT.emb_tS]
  simp [rS]

theorem embR_rR : embR hT hR rR = ρ := by
  rw [embR_apply]
  have : toTc rR = 1 := rfl
  rw [this, map_one]
  simp [rR]

theorem embR_range : (embR hT hR).range = Subgroup.closure ({a, b, s, ρ} : Set E) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [embR_apply]
    refine Subgroup.mul_mem _ ?_ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    have h1 : hT.emb (toTc x) ∈ Subgroup.closure ({a, b, s} : Set E) := by
      rw [← hT.emb_range]; exact ⟨_, rfl⟩
    refine Subgroup.closure_mono ?_ h1
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    tauto
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨rA, embR_rA hT hR⟩
    · exact ⟨rB, embR_rB hT hR⟩
    · exact ⟨rS, embR_rS hT hR⟩
    · exact ⟨rR, embR_rR hT hR⟩

theorem embR_injective (hcard : Nat.card (Subgroup.closure ({a, b, s, ρ} : Set E)) = 64) :
    Function.Injective (embR hT hR) := by
  have hsurj : Function.Surjective (embR hT hR).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  have hfin : Finite (embR hT hR).range := Finite.of_surjective _ hsurj
  have hcard' : Nat.card Tr ≤ Nat.card (embR hT hR).range := by
    rw [embR_range, hcard, card_Tr]
  have hbij := hsurj.bijective_of_nat_card_le hcard'
  intro x y hxy
  exact hbij.1 (Subtype.ext hxy)

end Emb

@[expose] def inQ1 (x : Tr) : Prop := x.e = 0
instance (x : Tr) : Decidable (inQ1 x) := by unfold inQ1; infer_instance

@[expose] def inQ2 (x : Tr) : Prop := (x.i.val + x.j.val) % 2 = 0
instance (x : Tr) : Decidable (inQ2 x) := by unfold inQ2; infer_instance

@[expose] def inN (x : Tr) : Prop := x.e = 0 ∧ x.i.val % 2 = 0 ∧ x.j.val % 2 = 0
instance (x : Tr) : Decidable (inN x) := by unfold inN; infer_instance

@[expose] def mkSub (P : Tr → Prop) (hm : ∀ x y, P x → P y → P (x * y)) (h1 : P 1)
    (hi : ∀ x, P x → P x⁻¹) : Subgroup Tr where
  carrier := {x | P x}
  mul_mem' := fun {x y} hx hy => hm x y hx hy
  one_mem' := h1
  inv_mem' := fun {x} hx => hi x hx

@[expose] def Q1r : Subgroup Tr :=
  mkSub inQ1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def Q2r : Subgroup Tr :=
  mkSub inQ2 (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def Nr : Subgroup Tr :=
  mkSub inN (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem mem_Q1r {x : Tr} : x ∈ Q1r ↔ inQ1 x := Iff.rfl
theorem mem_Q2r {x : Tr} : x ∈ Q2r ↔ inQ2 x := Iff.rfl
theorem mem_Nr {x : Tr} : x ∈ Nr ↔ inN x := Iff.rfl

@[expose] def rT0 : Tr := ⟨(1, 0), (0, 1)⟩

theorem Q1_or : ∀ x : Tr, inQ1 x ∨ inQ1 (x * rS⁻¹) := by decide +kernel

theorem Q2_or : ∀ x : Tr, inQ2 x ∨ inQ2 (x * rT0⁻¹) := by decide +kernel

theorem Q2_pow_four : ∀ x : Tr, inQ2 x → x ^ 4 = 1 := by decide +kernel

theorem Q2_normal : ∀ g x : Tr, inQ2 x → inQ2 (g * x * g⁻¹) := by decide +kernel

theorem N_normal : ∀ g x : Tr, inN x → inN (g * x * g⁻¹) := by decide +kernel

theorem N_le_Q1 : ∀ x : Tr, inN x → inQ1 x := by decide +kernel

theorem N_le_Q2 : ∀ x : Tr, inN x → inQ2 x := by decide +kernel

theorem inN_rA_sq : inN (rA * rA) := by decide +kernel

theorem rA_sq_ne_one : rA * rA ≠ 1 := by decide +kernel

@[expose] def zR : Tr := ⟨(2, 2), (0, 0)⟩

theorem zR_central : ∀ x : Tr, zR * x = x * zR := by decide +kernel
theorem zR_mem_Q2 : inQ2 zR := by decide +kernel
theorem zR_ne_one : zR ≠ 1 := by decide +kernel

theorem Q2_center : ∀ w : Tr, inQ2 w → (∀ v : Tr, inQ2 v → w * v = v * w) → w = 1 ∨ w = zR := by
  decide +kernel

@[expose] def actA (x : Tr) : Tr := ⟨(-x.j, x.i - x.j), (0, x.f)⟩

theorem actA_Q1 : ∀ x : Tr, inQ1 (actA x) := by decide +kernel
theorem actA_N : ∀ x : Tr, inN x → inN (actA x) := by decide +kernel
theorem actA_zR : actA zR ≠ zR := by decide +kernel

@[expose] def Rels4 {G : Type*} [Group G] (c p q r : G) : Prop :=
  c ^ 4 = 1 ∧ p * p = 1 ∧ q * q = 1 ∧ r * r = 1 ∧ r * c * r = c⁻¹ ∧ c * p = p * c ∧
    c * q = q * c ∧ r * p = p * r ∧ r * q = q * r ∧ (p * q) ^ 4 = 1 ∧ c * c = (p * q) ^ 2

instance (c p q r : Tr) : Decidable (Rels4 c p q r) := by unfold Rels4; infer_instance

theorem Rels4.map {G H : Type*} [Group G] [Group H] (φ : G →* H) {c p q r : G}
    (h : Rels4 c p q r) : Rels4 (φ c) (φ p) (φ q) (φ r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [map_mul, map_pow, map_inv, map_one] using congrArg φ h1
  · simpa [map_mul, map_pow, map_inv, map_one] using congrArg φ h2
  · simpa [map_mul, map_pow, map_inv, map_one] using congrArg φ h3
  · simpa [map_mul, map_pow, map_inv, map_one] using congrArg φ h4
  · simpa [map_mul, map_pow, map_inv, map_one] using congrArg φ h5
  · simpa [map_mul, map_pow, map_inv, map_one] using congrArg φ h6
  · simpa [map_mul, map_pow, map_inv, map_one] using congrArg φ h7
  · simpa [map_mul, map_pow, map_inv, map_one] using congrArg φ h8
  · simpa [map_mul, map_pow, map_inv, map_one] using congrArg φ h9
  · simpa [map_mul, map_pow, map_inv, map_one] using congrArg φ h10
  · simpa [map_mul, map_pow, map_inv, map_one] using congrArg φ h11

theorem Rels4.of_injective {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) {c p q r : G} (h : Rels4 (φ c) (φ p) (φ q) (φ r)) :
    Rels4 c p q r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply hφ; simpa [map_mul, map_pow, map_inv, map_one] using h1
  · apply hφ; simpa [map_mul, map_pow, map_inv, map_one] using h2
  · apply hφ; simpa [map_mul, map_pow, map_inv, map_one] using h3
  · apply hφ; simpa [map_mul, map_pow, map_inv, map_one] using h4
  · apply hφ; simpa [map_mul, map_pow, map_inv, map_one] using h5
  · apply hφ; simpa [map_mul, map_pow, map_inv, map_one] using h6
  · apply hφ; simpa [map_mul, map_pow, map_inv, map_one] using h7
  · apply hφ; simpa [map_mul, map_pow, map_inv, map_one] using h8
  · apply hφ; simpa [map_mul, map_pow, map_inv, map_one] using h9
  · apply hφ; simpa [map_mul, map_pow, map_inv, map_one] using h10
  · apply hφ; simpa [map_mul, map_pow, map_inv, map_one] using h11

@[expose] def cR : Tr := ⟨(1, 1), (0, 0)⟩
@[expose] def pR : Tr := ⟨(2, 0), (0, 0)⟩

theorem gen_rels : Rels4 cR pR rS rR := by decide +kernel

@[expose] def nfq (w : Tr) : ℕ × ℕ × ℕ × ℕ :=
  (w.j.val, ((w.i.val + 4 - w.j.val) % 4) / 2, w.e.val, w.f.val)

@[expose] def Fq (u : Tr × Tr × Tr × Tr) (w : Tr) : Tr :=
  u.1 ^ (nfq w).1 * u.2.1 ^ (nfq w).2.1 * u.2.2.1 ^ (nfq w).2.2.1 * u.2.2.2 ^ (nfq w).2.2.2

theorem qr_nf : ∀ w : Tr, inQ2 w → w = Fq (cR, pR, rS, rR) w := by decide +kernel

theorem Fq_cR (u : Tr × Tr × Tr × Tr) : Fq u cR = u.1 := by
  have h : nfq cR = (1, 0, 0, 0) := rfl
  simp [Fq, h]

theorem Fq_pR (u : Tr × Tr × Tr × Tr) : Fq u pR = u.2.1 := by
  have h : nfq pR = (0, 1, 0, 0) := rfl
  simp [Fq, h]

theorem Fq_rS (u : Tr × Tr × Tr × Tr) : Fq u rS = u.2.2.1 := by
  have h : nfq rS = (0, 0, 1, 0) := rfl
  simp [Fq, h]

theorem Fq_rR (u : Tr × Tr × Tr × Tr) : Fq u rR = u.2.2.2 := by
  have h : nfq rR = (0, 0, 0, 1) := rfl
  simp [Fq, h]

theorem conj_Fq {E : Type*} [Group E] (φ : Tr →* E) (κ : E →* E) (u : Tr × Tr × Tr × Tr)
    (h1 : κ (φ cR) = φ u.1) (h2 : κ (φ pR) = φ u.2.1) (h3 : κ (φ rS) = φ u.2.2.1)
    (h4 : κ (φ rR) = φ u.2.2.2) (w : Tr) (hw : inQ2 w) : κ (φ w) = φ (Fq u w) := by
  conv_lhs => rw [qr_nf w hw]
  simp only [Fq, map_mul, map_pow, h1, h2, h3, h4]

@[expose] def Cube4 (u : Tr × Tr × Tr × Tr) : Prop :=
  Fq u (Fq u (Fq u cR)) = cR ∧ Fq u (Fq u (Fq u pR)) = pR ∧ Fq u (Fq u (Fq u rS)) = rS ∧
    Fq u (Fq u (Fq u rR)) = rR

instance (u : Tr × Tr × Tr × Tr) : Decidable (Cube4 u) := by unfold Cube4; infer_instance

@[expose] def FPF (u : Tr × Tr × Tr × Tr) : Prop :=
  ∀ g : Tr, inQ2 g → Fq u g = g → g = 1 ∨ g = zR

instance (u : Tr × Tr × Tr × Tr) : Decidable (FPF u) := by unfold FPF; infer_instance

@[expose] def alpha5 : Tr × Tr × Tr × Tr :=
  (⟨(2, 0), (1, 1)⟩, ⟨(1, 3), (0, 1)⟩, ⟨(0, 0), (0, 1)⟩, ⟨(0, 0), (1, 1)⟩)

@[expose] def conjQ (t : Tr) (u : Tr × Tr × Tr × Tr) : Tr × Tr × Tr × Tr :=
  (t * Fq u (t⁻¹ * cR * t) * t⁻¹, t * Fq u (t⁻¹ * pR * t) * t⁻¹,
    t * Fq u (t⁻¹ * rS * t) * t⁻¹, t * Fq u (t⁻¹ * rR * t) * t⁻¹)

theorem alpha5_rels : Rels4 alpha5.1 alpha5.2.1 alpha5.2.2.1 alpha5.2.2.2 := by decide +kernel
theorem alpha5_cube : Cube4 alpha5 := by decide +kernel
theorem alpha5_mem : ∀ w : Tr, inQ2 w → inQ2 (Fq alpha5 w) := by decide +kernel

theorem alpha5_inverted : ∀ w : Tr, inQ2 w →
    Fq alpha5 (rT0 * Fq alpha5 (rT0⁻¹ * w * rT0) * rT0⁻¹) = w := by decide +kernel

set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxHeartbeats 1000000 in
theorem classify_B5_aux :
    ∀ u₁ : Tr, inQ2 u₁ → u₁ ^ 4 = 1 → u₁ * u₁ ≠ 1 → u₁ ≠ cR →
    ∀ u₄ : Tr, inQ2 u₄ → u₄ * u₄ = 1 → u₄ * u₁ * u₄ = u₁⁻¹ → u₄ ≠ rR →
    ∀ u₂ : Tr, inQ2 u₂ → u₂ * u₂ = 1 → u₁ * u₂ = u₂ * u₁ → u₄ * u₂ = u₂ * u₄ → u₂ ≠ pR →
    ∀ u₃ : Tr, inQ2 u₃ → u₃ * u₃ = 1 → u₁ * u₃ = u₃ * u₁ → u₄ * u₃ = u₃ * u₄ →
      (u₂ * u₃) ^ 4 = 1 → u₁ * u₁ = (u₂ * u₃) ^ 2 → u₃ ≠ rS →
      Cube4 (u₁, u₂, u₃, u₄) → FPF (u₁, u₂, u₃, u₄) →
      (∃ t : Tr, conjQ t (u₁, u₂, u₃, u₄) = alpha5) ∨
        (∀ g : Tr, inN g → inN (Fq (u₁, u₂, u₃, u₄) g)) := by
  decide +kernel

theorem classify_B5 (u : Tr × Tr × Tr × Tr) (hq1 : inQ2 u.1) (hq2 : inQ2 u.2.1)
    (hq3 : inQ2 u.2.2.1) (hq4 : inQ2 u.2.2.2) (hr : Rels4 u.1 u.2.1 u.2.2.1 u.2.2.2)
    (hc : Cube4 u) (hf : FPF u) (hsq : u.1 * u.1 ≠ 1) :
    (∃ t : Tr, conjQ t u = alpha5) ∨ (∀ g : Tr, inN g → inN (Fq u g)) := by
  obtain ⟨u₁, u₂, u₃, u₄⟩ := u
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hr
  have hne : ∀ g : Tr, ¬ (g = 1 ∨ g = zR) → inQ2 g → Fq (u₁, u₂, u₃, u₄) g ≠ g :=
    fun g hg hgq he => hg (hf g hgq he)
  have hc1 : u₁ ≠ cR := fun h => by
    have := hne cR (by decide +kernel) (by decide +kernel)
    rw [Fq_cR] at this
    exact this h
  have hc2 : u₂ ≠ pR := fun h => by
    have := hne pR (by decide +kernel) (by decide +kernel)
    rw [Fq_pR] at this
    exact this h
  have hc3 : u₃ ≠ rS := fun h => by
    have := hne rS (by decide +kernel) (by decide +kernel)
    rw [Fq_rS] at this
    exact this h
  have hc4 : u₄ ≠ rR := fun h => by
    have := hne rR (by decide +kernel) (by decide +kernel)
    rw [Fq_rR] at this
    exact this h
  exact classify_B5_aux u₁ hq1 h1 hsq hc1 u₄ hq4 h4 h5 hc4 u₂ hq2 h2 h6 h8 hc2 u₃ hq3 h3 h7 h9
    h10 h11 hc3 hc hf

theorem lin_classify : ∀ a₀ s₀ r₀ : Fin 2,
    (∀ w : Tr, ((w.i.val + w.j.val) * a₀.val + w.e.val * s₀.val + w.f.val * r₀.val) % 2 = 0 →
      w ^ 4 = 1) →
    (a₀ = 0 ∧ s₀ = 1 ∧ r₀ = 0) ∨ (a₀ = 1 ∧ s₀ = 0 ∧ r₀ = 0) := by decide +kernel

theorem eq_Q_of_index_two (N : Subgroup Tr) (hN : N.index = 2) (hexp : ∀ w ∈ N, w ^ 4 = 1) :
    N = Q1r ∨ N = Q2r := by
  classical
  have hmul : ∀ x y : Tr, x * y ∈ N ↔ (x ∈ N ↔ y ∈ N) := fun x y =>
    Subgroup.mul_mem_iff_of_index_two hN
  let bit : Tr → ℕ := fun x => if x ∈ N then 0 else 1
  have hbit : ∀ x, bit x = 0 ∨ bit x = 1 := by
    intro x; by_cases h : x ∈ N <;> simp [bit, h]
  have hbit0 : ∀ x, bit x = 0 ↔ x ∈ N := by
    intro x; by_cases h : x ∈ N <;> simp [bit, h]
  have hmulb : ∀ x y, bit (x * y) = (bit x + bit y) % 2 := by
    intro x y
    by_cases hx : x ∈ N <;> by_cases hy : y ∈ N
    · have : x * y ∈ N := (hmul x y).mpr (iff_of_true hx hy)
      simp [bit, hx, hy, this]
    · have : x * y ∉ N := fun h' => hy (((hmul x y).mp h').mp hx)
      simp [bit, hx, hy, this]
    · have : x * y ∉ N := fun h' => hx (((hmul x y).mp h').mpr hy)
      simp [bit, hx, hy, this]
    · have : x * y ∈ N := (hmul x y).mpr (iff_of_false hx hy)
      simp [bit, hx, hy, this]
  have hone : bit 1 = 0 := (hbit0 1).mpr N.one_mem
  have hpow : ∀ (g : Tr) (n : ℕ), bit (g ^ n) = (n * bit g) % 2 := by
    intro g n
    induction n with
    | zero => rw [pow_zero, hone]; simp
    | succ n ih =>
      rw [pow_succ, hmulb, ih]
      rcases hbit g with h | h <;> rw [h] <;> omega
  have hrB : bit rB = bit rA := by
    have e : rB = rS * rA * rS := rS_rA_rS.symm
    rw [e, hmulb, hmulb]
    rcases hbit rS with h | h <;> rcases hbit rA with h' | h' <;> rw [h, h']
  have hx : ∀ x : Tr, bit x =
      (x.i.val * bit rA + x.j.val * bit rA + x.e.val * bit rS + x.f.val * bit rR) % 2 := by
    intro x
    conv_lhs => rw [tr_nf x]
    rw [hmulb, hmulb, hmulb, hpow, hpow, hpow, hpow, hrB]
    rcases hbit rA with h1 | h1 <;> rcases hbit rS with h2 | h2 <;> rcases hbit rR with h3 | h3 <;>
      rw [h1, h2, h3] <;> omega
  have hlin : ∀ x : Tr, x ∈ N ↔
      ((x.i.val + x.j.val) * bit rA + x.e.val * bit rS + x.f.val * bit rR) % 2 = 0 := by
    intro x
    rw [← hbit0, hx]
    have : x.i.val * bit rA + x.j.val * bit rA + x.e.val * bit rS + x.f.val * bit rR =
        (x.i.val + x.j.val) * bit rA + x.e.val * bit rS + x.f.val * bit rR := by ring
    rw [this]
  have hbits : ∀ b : Tr, bit b < 2 := fun b => by rcases hbit b with h | h <;> omega
  have key := lin_classify ⟨bit rA, hbits rA⟩ ⟨bit rS, hbits rS⟩ ⟨bit rR, hbits rR⟩ (by
    intro w hw
    exact hexp w ((hlin w).mpr hw))
  have hA2 := hbits rA
  have hS2 := hbits rS
  have hR2 := hbits rR
  rcases key with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · left
    have e1 : bit rA = 0 := by simpa [Fin.ext_iff] using h1
    have e2 : bit rS = 1 := by simpa [Fin.ext_iff] using h2
    have e3 : bit rR = 0 := by simpa [Fin.ext_iff] using h3
    ext x
    rw [hlin, e1, e2, e3, mem_Q1r, inQ1]
    have := x.e.isLt
    simp only [Fin.ext_iff, Fin.val_zero]
    omega
  · right
    have e1 : bit rA = 1 := by simpa [Fin.ext_iff] using h1
    have e2 : bit rS = 0 := by simpa [Fin.ext_iff] using h2
    have e3 : bit rR = 0 := by simpa [Fin.ext_iff] using h3
    ext x
    rw [hlin, e1, e2, e3, mem_Q2r, inQ2]
    omega

theorem cR_mem_Q2 : inQ2 cR := by decide +kernel
theorem pR_mem_Q2 : inQ2 pR := by decide +kernel
theorem rS_mem_Q2 : inQ2 rS := by decide +kernel
theorem rR_mem_Q2 : inQ2 rR := by decide +kernel

theorem cR_sq_ne_one : cR * cR ≠ 1 := by decide +kernel

theorem zR_sq : zR * zR = 1 := by decide +kernel

theorem alpha5_zR : Fq alpha5 zR = zR := by decide +kernel

theorem alpha5_one : Fq alpha5 1 = 1 := by decide +kernel

theorem zR_mem_Q1 : inQ1 zR := by decide +kernel

theorem card_Q1r : Nat.card Q1r = 32 := by
  have h : Fintype.card {x : Tr // inQ1 x} = 32 := by decide +kernel
  rw [← h, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.refl _)

end CFSG.Quasithin.F6.GoldAmL5
