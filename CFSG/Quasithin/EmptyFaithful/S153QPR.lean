module

public import CFSG.LieType.SteinbergBRParabolicTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics

public section

namespace CFSG.Quasithin.QP

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.SteinbergBR.BlockPar

section Fix

variable {F : Type} [Field F] {n : ℕ}

@[expose] def fixSub (X : Subgroup (SpecialLinearGroup (Fin n) F)) : Submodule F (Fin n → F) where
  carrier := {v | ∀ x ∈ X, (x : Matrix (Fin n) (Fin n) F) *ᵥ v = v}
  add_mem' {a b} ha hb x hx := by rw [mulVec_add, ha x hx, hb x hx]
  zero_mem' x _ := by rw [mulVec_zero]
  smul_mem' c v hv x hx := by rw [mulVec_smul, hv x hx]

theorem smul_vec_eq (x : SpecialLinearGroup (Fin n) F) (v : Fin n → F) :
    x • v = (x : Matrix (Fin n) (Fin n) F) *ᵥ v :=
  Matrix.smul_eq_mulVec _ _

theorem mulVec_mul_conj (x g : SpecialLinearGroup (Fin n) F) (v : Fin n → F) :
    (x : Matrix (Fin n) (Fin n) F) *ᵥ ((g : Matrix (Fin n) (Fin n) F) *ᵥ v) =
      (g : Matrix (Fin n) (Fin n) F) *ᵥ (((g⁻¹ * x * g : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) *ᵥ v) := by
  have h2 : g * (g⁻¹ * x * g) = x * g := by group
  calc (x : Matrix (Fin n) (Fin n) F) *ᵥ ((g : Matrix (Fin n) (Fin n) F) *ᵥ v)
      = ((x * g : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v := by
        rw [Matrix.SpecialLinearGroup.coe_mul, mulVec_mulVec]
    _ = ((g * (g⁻¹ * x * g) : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v := by
        rw [h2]
    _ = (g : Matrix (Fin n) (Fin n) F) *ᵥ (((g⁻¹ * x * g : SpecialLinearGroup (Fin n) F) :
          Matrix (Fin n) (Fin n) F) *ᵥ v) := by
        rw [Matrix.SpecialLinearGroup.coe_mul, mulVec_mulVec]

theorem mulVec_mem_fixSub {X : Subgroup (SpecialLinearGroup (Fin n) F)}
    {g : SpecialLinearGroup (Fin n) F} (hg : ∀ x ∈ X, g⁻¹ * x * g ∈ X) {v : Fin n → F}
    (hv : v ∈ fixSub X) : (g : Matrix (Fin n) (Fin n) F) *ᵥ v ∈ fixSub X := by
  intro x hx
  rw [mulVec_mul_conj, hv _ (hg x hx)]

theorem eq_one_of_forall_mulVec {M : Matrix (Fin n) (Fin n) F} (h : ∀ v, M *ᵥ v = v) : M = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

variable [CharP F 2]

theorem two_dvd_natCard_of_pos [Finite F] {m : ℕ} (hm : 1 ≤ m) : 2 ∣ Nat.card F ^ m := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨k, -, hk⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hk, ← pow_mul]
  exact dvd_pow_self 2 (Nat.mul_ne_zero k.ne_zero (by omega))

theorem two_dvd_natCard_vec [Finite F] (hn : 1 ≤ n) : 2 ∣ Nat.card (Fin n → F) := by
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card]
  exact two_dvd_natCard_of_pos hn

theorem exists_ne_zero_mem_fixSub [Finite F] (hn : 1 ≤ n) {X : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hX : IsPGroup 2 X) : ∃ v ∈ fixSub X, v ≠ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb, hne⟩ := hX.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := Fin n → F) (two_dvd_natCard_vec hn) (a := 0)
    (fun x => smul_zero (x : SpecialLinearGroup (Fin n) F))
  refine ⟨b, fun x hx => ?_, fun h => hne h.symm⟩
  have := hb ⟨x, hx⟩
  rwa [Subgroup.mk_smul, smul_vec_eq] at this

end Fix

section Quot

variable {F : Type} [Field F] {n : ℕ}

@[expose, instance_reducible] noncomputable def quotAct (X : Subgroup (SpecialLinearGroup (Fin n) F))
    (W : Submodule F (Fin n → F))
    (h : ∀ x ∈ X, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W) :
    MulAction ↥X ((Fin n → F) ⧸ W) where
  smul x q := W.mapQ W (mulVecLin ((x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (fun w hw => h x.1 x.2 w hw) q
  one_smul q := by
    induction q using Submodule.Quotient.induction_on with
    | H a =>
      show Submodule.Quotient.mk ((1 : Matrix (Fin n) (Fin n) F) *ᵥ a) = Submodule.Quotient.mk a
      rw [one_mulVec]
  mul_smul x y q := by
    induction q using Submodule.Quotient.induction_on with
    | H a =>
      show Submodule.Quotient.mk ((((x : SpecialLinearGroup (Fin n) F) *
          (y : SpecialLinearGroup (Fin n) F) : SpecialLinearGroup (Fin n) F) :
            Matrix (Fin n) (Fin n) F) *ᵥ a) = Submodule.Quotient.mk
          (((x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ
            (((y : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ a))
      rw [Matrix.SpecialLinearGroup.coe_mul, mulVec_mulVec]

theorem quotAct_smul_mk {X : Subgroup (SpecialLinearGroup (Fin n) F)} {W : Submodule F (Fin n → F)}
    (h : ∀ x ∈ X, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W) (x : ↥X) (v : Fin n → F) :
    (quotAct X W h).toSMul.smul x (Submodule.Quotient.mk v : (Fin n → F) ⧸ W) =
      Submodule.Quotient.mk (((x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v) :=
  rfl

end Quot

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem two_dvd_natCard_quotient {W : Submodule F (Fin n → F)} (hW : W ≠ ⊤) :
    2 ∣ Nat.card ((Fin n → F) ⧸ W) := by
  have : Fintype F := Fintype.ofFinite F
  have : Fintype ((Fin n → F) ⧸ W) := Fintype.ofFinite _
  have hnt : Nontrivial ((Fin n → F) ⧸ W) := Submodule.Quotient.nontrivial_iff.2 hW
  have hpos : 0 < finrank F ((Fin n → F) ⧸ W) := Module.finrank_pos_iff.2 hnt
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card]
  exact two_dvd_natCard_of_pos hpos

theorem le_radU_of_isPGroup {d : ℕ} (hd : 1 ≤ d) (hdn : d < n)
    {X : Subgroup (SpecialLinearGroup (Fin n) F)} (hX : IsPGroup 2 X)
    (hN : ∀ g ∈ stabilizer (flagSpace n F d), ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    X ≤ radU F (flagSpace n F d) := by
  have hn : 1 ≤ n := by omega
  set W := flagSpace n F d with hW
  have hfin : finrank F W = d := finrank_flagSpace hdn.le
  have hWbot : W ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hfin
    omega
  have hWtop : W ≠ ⊤ := fun h => by
    rw [h, finrank_top, finrank_fin_fun] at hfin
    omega
  have hclass := (subflag_stabilizer_generation (K := F) (n := n) {d}).2.1
  rw [flagStabilizer_singleton] at hclass
  have hinv : ∀ Y : Submodule F (Fin n → F),
      (∀ g ∈ stabilizer W, ∀ v ∈ Y, (g : Matrix (Fin n) (Fin n) F) *ᵥ v ∈ Y) →
        Y = ⊥ ∨ Y = ⊤ ∨ Y = W := by
    intro Y hY
    rcases (hclass Y).1 hY with h | h | ⟨i, hi, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by rw [h, Set.mem_singleton_iff.mp hi]))
  have hconj : ∀ g ∈ stabilizer W, ∀ x ∈ X, g⁻¹ * x * g ∈ X := fun g hg x hx => by
    simpa using hN g⁻¹ (inv_mem hg) x hx
  have hQW : ∀ g ∈ stabilizer W, ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := fun g hg w hw => by
    have h := mem_stabilizer.1 hg
    rw [← h]
    exact ⟨w, hw, rfl⟩
  obtain ⟨v₀, hv₀, hv₀ne⟩ := exists_ne_zero_mem_fixSub hn hX
  rcases hinv (fixSub X) (fun g hg v hv => mulVec_mem_fixSub (hconj g hg) hv) with h | h | h
  · exact absurd (by rw [← Submodule.mem_bot F, ← h]; exact hv₀) hv₀ne
  · intro x hx
    have h1 : (x : Matrix (Fin n) (Fin n) F) = 1 := eq_one_of_forall_mulVec fun v =>
      (h ▸ Submodule.mem_top : v ∈ fixSub X) x hx
    have hx1 : x = 1 := Subtype.ext h1
    rw [hx1]
    exact one_mem _
  · have hWfix : ∀ x ∈ X, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F) *ᵥ w = w := fun x hx w hw =>
      (h ▸ hw : w ∈ fixSub X) x hx
    let Y : Submodule F (Fin n → F) :=
      { carrier := {v | ∀ x ∈ X, (x : Matrix (Fin n) (Fin n) F) *ᵥ v - v ∈ W}
        add_mem' := fun {a b} ha hb x hx => by
          have e : (x : Matrix (Fin n) (Fin n) F) *ᵥ (a + b) - (a + b) =
              ((x : Matrix (Fin n) (Fin n) F) *ᵥ a - a) + ((x : Matrix (Fin n) (Fin n) F) *ᵥ b - b) := by
            rw [mulVec_add]
            abel
          rw [e]
          exact W.add_mem (ha x hx) (hb x hx)
        zero_mem' := fun x _ => by simp
        smul_mem' := fun c v hv x hx => by
          have e : (x : Matrix (Fin n) (Fin n) F) *ᵥ (c • v) - c • v =
              c • ((x : Matrix (Fin n) (Fin n) F) *ᵥ v - v) := by
            rw [mulVec_smul, smul_sub]
          rw [e]
          exact W.smul_mem c (hv x hx) }
    have hYinv : ∀ g ∈ stabilizer W, ∀ v ∈ Y, (g : Matrix (Fin n) (Fin n) F) *ᵥ v ∈ Y := by
      intro g hg v hv x hx
      have h1 : ((g⁻¹ * x * g : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v - v ∈ W :=
        hv _ (hconj g hg x hx)
      have e : (x : Matrix (Fin n) (Fin n) F) *ᵥ ((g : Matrix (Fin n) (Fin n) F) *ᵥ v) -
          (g : Matrix (Fin n) (Fin n) F) *ᵥ v =
          (g : Matrix (Fin n) (Fin n) F) *ᵥ (((g⁻¹ * x * g : SpecialLinearGroup (Fin n) F) :
            Matrix (Fin n) (Fin n) F) *ᵥ v - v) := by
        rw [mulVec_sub, mulVec_mul_conj]
      rw [e]
      exact hQW g hg _ h1
    have hWY : W ≤ Y := fun w hw x hx => by
      rw [hWfix x hx w hw, sub_self]
      exact W.zero_mem
    have hYtop : Y = ⊤ := by
      rcases hinv Y hYinv with h' | h' | h'
      · exact absurd (le_bot_iff.1 (h' ▸ hWY)) hWbot
      · exact h'
      · exfalso
        have hpres : ∀ x ∈ X, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := fun x hx w hw => by
          rw [hWfix x hx w hw]
          exact hw
        let _ : MulAction ↥X ((Fin n → F) ⧸ W) := quotAct X W hpres
        have : Finite ((Fin n → F) ⧸ W) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective W)
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨b, hb, hne⟩ := hX.exists_fixed_point_of_prime_dvd_card_of_fixed_point
          (α := (Fin n → F) ⧸ W) (two_dvd_natCard_quotient hWtop) (a := 0) (fun x => by
            have := quotAct_smul_mk hpres x 0
            rw [mulVec_zero] at this
            exact this)
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W b
        have hvY : v ∈ Y := fun x hx => by
          have h3 : (Submodule.Quotient.mk ((x : Matrix (Fin n) (Fin n) F) *ᵥ v) :
              (Fin n → F) ⧸ W) = Submodule.Quotient.mk v := hb ⟨x, hx⟩
          exact (Submodule.Quotient.eq W).1 h3
        have hvW : v ∉ W := fun hvW => hne ((Submodule.Quotient.mk_eq_zero W).2 hvW).symm
        exact hvW (h' ▸ hvY)
    intro x hx
    refine ⟨fun v => ?_, fun w hw => hWfix x hx w hw⟩
    exact (hYtop ▸ Submodule.mem_top : v ∈ Y) x hx

end Main

end CFSG.Quasithin.QP
