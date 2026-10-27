module

public import CFSG.Quasithin.H13.GoldschmidtI51Sym

public noncomputable section

namespace CFSG.Quasithin.H13.I51

structure PGData (G Ω : Type) [Group G] [MulAction G Ω] where
  Ln : Ω → Ω → Ω → Prop
  swap12 : ∀ {x y z}, Ln x y z → Ln y x z
  swap23 : ∀ {x y z}, Ln x y z → Ln x z y
  smul : ∀ (g : G) {x y z}, Ln x y z → Ln (g • x) (g • y) (g • z)
  third : ∀ {x y}, x ≠ y → ∃ z, Ln x y z
  pl : Set Ω
  pl_closed : ∀ {x y z}, Ln x y z → x ∈ pl → y ∈ pl → z ∈ pl
  pl_meet : ∀ {x y z}, Ln x y z → x ∈ pl ∨ y ∈ pl ∨ z ∈ pl
  pl_ne : ∃ a, a ∉ pl
  trans : MulAction.IsPretransitive G Ω
  faith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1

section Quot

variable {G Ω : Type} [Group G] [MulAction G Ω] (D : PGData G Ω)

@[expose] def Ksub : Submodule (ZMod 2) (Ω →₀ ZMod 2) :=
  Submodule.span (ZMod 2) {u | ∃ x y z, D.Ln x y z ∧
    u = Finsupp.single x 1 + Finsupp.single y 1 + Finsupp.single z 1}

abbrev Wq : Type := (Ω →₀ ZMod 2) ⧸ Ksub D

@[expose] def psi (x : Ω) : Wq D := Submodule.Quotient.mk (Finsupp.single x 1)

@[expose] def fpl : (Ω →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.linearCombination (ZMod 2) (fun x : Ω => by classical exact if x ∈ D.pl then 0 else 1)

theorem fpl_single (x : Ω) (c : ZMod 2) :
    fpl D (Finsupp.single x c) = c * (by classical exact if x ∈ D.pl then 0 else 1) := by
  simp [fpl]

theorem fpl_gen {x y z : Ω} (h : D.Ln x y z) :
    fpl D (Finsupp.single x 1 + Finsupp.single y 1 + Finsupp.single z 1) = 0 := by
  classical
  simp only [map_add, fpl_single, one_mul]
  by_cases hx : x ∈ D.pl <;> by_cases hy : y ∈ D.pl <;> by_cases hz : z ∈ D.pl
  · simp [hx, hy, hz]
  · exact absurd (D.pl_closed h hx hy) hz
  · exact absurd (D.pl_closed (D.swap23 h) hx hz) hy
  · simp only [hx, hy, hz, ite_true, ite_false]; decide
  · exact absurd (D.pl_closed (D.swap23 (D.swap12 h)) hy hz) hx
  · simp only [hx, hy, hz, ite_true, ite_false]; decide
  · simp only [hx, hy, hz, ite_true, ite_false]; decide
  · rcases D.pl_meet h with h1 | h1 | h1 <;> contradiction

theorem Ksub_le_ker : Ksub D ≤ LinearMap.ker (fpl D) := by
  refine Submodule.span_le.2 ?_
  rintro u ⟨x, y, z, h, rfl⟩
  exact fpl_gen D h

theorem wq_add_self (v : Wq D) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

end Quot

section Action

variable {G Ω : Type} [Group G] [MulAction G Ω] (D : PGData G Ω)

theorem permLin_mem_K (g : G) {u : Ω →₀ ZMod 2} (hu : u ∈ Ksub D) : permLin g u ∈ Ksub D := by
  have : Ksub D ≤ (Ksub D).comap (permLin g) := by
    refine Submodule.span_le.2 ?_
    rintro u ⟨x, y, z, hl, rfl⟩
    show permLin g _ ∈ Ksub D
    rw [map_add, map_add, permLin_single, permLin_single, permLin_single]
    exact Submodule.subset_span ⟨g • x, g • y, g • z, D.smul g hl, rfl⟩
  exact this hu

@[expose] def rhoK (g : G) : Wq D →ₗ[ZMod 2] Wq D :=
  Submodule.mapQ (Ksub D) (Ksub D) (permLin g) (fun _ hu => permLin_mem_K D g hu)

theorem rhoK_mk (g : G) (u : Ω →₀ ZMod 2) :
    rhoK D g (Submodule.Quotient.mk u) = Submodule.Quotient.mk (permLin g u) := rfl

theorem rhoK_psi (g : G) (x : Ω) : rhoK D g (psi D x) = psi D (g • x) := by
  rw [psi, rhoK_mk, permLin_single]; rfl

theorem rhoK_mul (g h : G) : rhoK D (g * h) = rhoK D g ∘ₗ rhoK D h := by
  refine LinearMap.ext fun v => ?_
  induction v using Submodule.Quotient.induction_on with
  | _ u => simp only [LinearMap.comp_apply, rhoK_mk, permLin_mul]

theorem rhoK_one : rhoK D (1 : G) = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  induction v using Submodule.Quotient.induction_on with
  | _ u => rw [rhoK_mk, permLin_one]; rfl

theorem psi_ne_zero (x : Ω) : psi D x ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := D.pl_ne
  obtain ⟨g, hg⟩ := D.trans.exists_smul_eq x a
  have h1 : psi D a = 0 := by rw [← hg, ← rhoK_psi, h, map_zero]
  have h2 : Finsupp.single a (1 : ZMod 2) ∈ Ksub D := (Submodule.Quotient.mk_eq_zero _).1 h1
  have h3 := Ksub_le_ker D h2
  rw [LinearMap.mem_ker, fpl_single] at h3
  simp only [ha, ite_false, one_mul] at h3
  exact absurd h3 (by decide)

theorem psi_add_psi {x y : Ω} (hxy : x ≠ y) : ∃ z, psi D x + psi D y = psi D z := by
  obtain ⟨z, hz⟩ := D.third hxy
  refine ⟨z, ?_⟩
  have h : psi D x + psi D y + psi D z = 0 := by
    simp only [psi, ← Submodule.Quotient.mk_add]
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨x, y, z, hz, rfl⟩
  have h2 := wq_add_self D (psi D z)
  rw [add_eq_zero_iff_eq_neg, neg_eq_of_add_eq_zero_right h2] at h
  exact h

theorem psi_injective : Function.Injective (psi D) := by
  intro x y hxy
  by_contra hne
  obtain ⟨z, hz⟩ := psi_add_psi D hne
  rw [hxy, wq_add_self] at hz
  exact psi_ne_zero D z hz.symm

theorem Wq_cases (v : Wq D) : v = 0 ∨ ∃ x, v = psi D x := by
  let S : Submodule (ZMod 2) (Wq D) :=
    { carrier := {v | v = 0 ∨ ∃ x, v = psi D x}
      zero_mem' := Or.inl rfl
      add_mem' := by
        rintro a b (rfl | ⟨x, rfl⟩) (rfl | ⟨y, rfl⟩)
        · left; simp
        · right; exact ⟨y, by simp⟩
        · right; exact ⟨x, by simp⟩
        · by_cases hxy : x = y
          · left; subst hxy; exact wq_add_self D _
          · right
            obtain ⟨z, hz⟩ := psi_add_psi D hxy
            exact ⟨z, hz⟩
      smul_mem' := by
        intro c v hv
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl
        · left; simp
        · simpa using hv }
  have hmem : ∀ x, psi D x ∈ S := fun x => Or.inr ⟨x, rfl⟩
  induction v using Submodule.Quotient.induction_on with
  | _ u =>
    have : (Submodule.Quotient.mk u : Wq D) ∈ S := by
      induction u using Finsupp.induction_linear with
      | zero => exact S.zero_mem
      | add u₁ u₂ h₁ h₂ =>
        rw [Submodule.Quotient.mk_add]; exact S.add_mem h₁ h₂
      | single x a =>
        have : (Submodule.Quotient.mk (Finsupp.single x a) : Wq D) = a • psi D x := by
          rw [psi, ← Submodule.Quotient.mk_smul, Finsupp.smul_single_one]
        rw [this]; exact S.smul_mem a (hmem x)
    exact this

theorem card_Wq [Finite Ω] : Nat.card (Wq D) = Nat.card Ω + 1 := by
  have := Fintype.ofFinite Ω
  let e : Option Ω ≃ Wq D := Equiv.ofBijective (fun o => o.elim 0 (psi D)) ⟨?_, ?_⟩
  · rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_option,
      Nat.card_eq_fintype_card]
  · rintro (_ | x) (_ | y) h
    · rfl
    · exact absurd h.symm (psi_ne_zero D y)
    · exact absurd h (psi_ne_zero D x)
    · exact congrArg some (psi_injective D h)
  · intro v
    rcases Wq_cases D v with rfl | ⟨x, rfl⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some x, rfl⟩

theorem finrank_Wq [Finite Ω] (hΩ : Nat.card Ω = 15) : Module.finrank (ZMod 2) (Wq D) = 4 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Wq D)
  rw [card_Wq, Nat.card_zmod, hΩ] at h
  have h16 : (2 : ℕ) ^ 4 = 15 + 1 := by norm_num
  rw [← h16] at h
  exact (Nat.pow_right_injective (le_refl 2) h).symm

end Action

section Hom

open Matrix

variable {G Ω : Type} [Group G] [MulAction G Ω] (D : PGData G Ω)
  (b : Module.Basis (Fin 4) (ZMod 2) (Wq D))

@[expose] def repMatK (g : G) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  LinearMap.toMatrix b b (rhoK D g)

theorem repMatK_mul (g h : G) : repMatK D b (g * h) = repMatK D b g * repMatK D b h := by
  rw [repMatK, rhoK_mul, repMatK, repMatK, LinearMap.toMatrix_comp b b b]

theorem repMatK_one : repMatK D b (1 : G) = 1 := by
  rw [repMatK, rhoK_one, LinearMap.toMatrix_id]

@[expose] def glHom : G →* GL (Fin 4) (ZMod 2) :=
  MonoidHom.toHomUnits
    { toFun := repMatK D b
      map_one' := repMatK_one D b
      map_mul' := repMatK_mul D b }

theorem glHom_injective : Function.Injective (glHom D b) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : repMatK D b g = 1 := by
    have := congrArg (fun A : GL (Fin 4) (ZMod 2) => (A : Matrix (Fin 4) (Fin 4) (ZMod 2))) hg
    simpa [glHom] using this
  have h2 : rhoK D g = LinearMap.id := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_id]
    exact h1
  have h3 : ∀ x : Ω, g • x = x := by
    intro x
    apply psi_injective D
    rw [← rhoK_psi, h2]; rfl
  exact D.faith g h3

theorem card_GL_four_two : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  norm_num

include D in
theorem exists_mulEquiv_GL [Finite Ω] (hΩ : Nat.card Ω = 15) (hG : 20160 ≤ Nat.card G) :
    Nonempty (G ≃* GL (Fin 4) (ZMod 2)) := by
  have hrank := finrank_Wq D hΩ
  have hfin : Finite (Wq D) := Nat.finite_of_card_ne_zero (by rw [card_Wq D, hΩ]; norm_num)
  let b : Module.Basis (Fin 4) (ZMod 2) (Wq D) := Module.finBasisOfFinrankEq (ZMod 2) (Wq D) hrank
  have hbij : Function.Bijective (glHom D b) :=
    (glHom_injective D b).bijective_of_nat_card_le (by rw [card_GL_four_two]; exact hG)
  exact ⟨MulEquiv.ofBijective (glHom D b) hbij⟩

end Hom

end CFSG.Quasithin.H13.I51
