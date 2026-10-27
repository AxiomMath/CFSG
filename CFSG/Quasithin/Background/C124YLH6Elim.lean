module

public import CFSG.Quasithin.Background.B4Models

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.H6

open Matrix CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

@[expose] def actHom {K : Type} [Field K] {Γ₀ : Subgroup (GL (Fin 3) K)} (γ : ↥Γ₀) :
    Multiplicative (Fin 3 → K) →* Multiplicative (Fin 3 → K) where
  toFun := natAct Γ₀ γ
  map_one' := by simp [natAct]
  map_mul' := fun a b => by simp [natAct, Matrix.mulVec_add]

theorem actHom_apply {K : Type} [Field K] {Γ₀ : Subgroup (GL (Fin 3) K)} (γ : ↥Γ₀)
    (q : Multiplicative (Fin 3 → K)) : actHom γ q = natAct Γ₀ γ q := rfl

theorem actHom_mul {K : Type} [Field K] {Γ₀ : Subgroup (GL (Fin 3) K)} (γ δ : ↥Γ₀)
    (q : Multiplicative (Fin 3 → K)) : actHom (γ * δ) q = actHom γ (actHom δ q) := by
  simp only [actHom_apply, natAct, toAdd_ofAdd]
  congr 1
  rw [Matrix.mulVec_mulVec]
  rfl

theorem card_sq_le_semilinear {Q : Type*} [CommGroup Q] [Finite Q] (ω T : Q →* Q)
    (hinj : Function.Injective ω) (hfp : ∀ q, ω q = q → q = 1)
    (hT : ∀ q, T (ω q) = ω (ω (T q))) :
    Nat.card ↥(MonoidHom.eqLocus T (MonoidHom.id Q)) ^ 2 ≤ Nat.card Q := by
  set F := MonoidHom.eqLocus T (MonoidHom.id Q) with hF
  have hFmem : ∀ q, q ∈ F ↔ T q = q := fun q => Iff.rfl
  let f : ↥F × ↥F → Q := fun p => (p.1 : Q) * ω (p.2 : Q)
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a : Q) * ω (b : Q) = (a' : Q) * ω (b' : Q) := h
    set c : Q := (b' : Q) * (b : Q)⁻¹ with hc
    have hcF : c ∈ F := F.mul_mem b'.2 (F.inv_mem b.2)
    have hωc : ω c = (a : Q) * (a' : Q)⁻¹ := by
      have key : (a : Q) / (a' : Q) = ω (b' : Q) / ω (b : Q) := by
        rw [div_eq_div_iff_mul_eq_mul, h1, mul_comm]
      rw [hc, ← div_eq_mul_inv, map_div, ← key, div_eq_mul_inv]
    have hωcF : ω c ∈ F := hωc ▸ F.mul_mem a.2 (F.inv_mem a'.2)
    have h2 : ω c = ω (ω c) := by
      have e1 := (hFmem _).1 hωcF
      rw [hT, (hFmem _).1 hcF] at e1
      exact e1.symm
    have h3 : c = ω c := hinj h2
    have hc1 : c = 1 := hfp c h3.symm
    have hb : (b : Q) = (b' : Q) := by
      have := hc1
      rw [hc, mul_inv_eq_one] at this
      exact this.symm
    have ha : (a : Q) = (a' : Q) := by
      rw [hb] at h1
      exact mul_right_cancel h1
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  calc Nat.card ↥F ^ 2 = Nat.card (↥F × ↥F) := by rw [Nat.card_prod, pow_two]
    _ ≤ Nat.card Q := Nat.card_le_card_of_injective f hf

theorem four_elems {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) {ω : K} (h1 : ω ≠ 1)
    (h3 : ω ^ 3 = 1) : ∀ a : K, a = 0 ∨ a = 1 ∨ a = ω ∨ a = ω ^ 2 := by
  intro a
  by_contra hne
  push Not at hne
  obtain ⟨ha0, ha1, haω, haω2⟩ := hne
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h] at h3
    norm_num at h3
  have hω2_0 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω0
  have hω2_1 : ω ^ 2 ≠ 1 := by
    intro h
    apply h1
    calc ω = ω * ω ^ 2 := by rw [h, mul_one]
      _ = ω ^ 3 := by ring
      _ = 1 := h3
  have hω2_ω : ω ^ 2 ≠ ω := by
    intro h
    apply h1
    have : ω * ω = ω * 1 := by rw [mul_one, ← pow_two, h]
    exact mul_left_cancel₀ hω0 this
  have hnd : ([0, 1, ω, ω ^ 2, a] : List K).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨zero_ne_one, hω0.symm, hω2_0.symm, ha0.symm⟩, ⟨h1.symm, hω2_1.symm, ha1.symm⟩,
      ⟨hω2_ω.symm, haω.symm⟩, haω2.symm, not_false, List.nodup_nil⟩
  have := Fintype.ofFinite K
  have := hnd.length_le_card
  rw [← Nat.card_eq_fintype_card (α := K)] at this
  simp only [List.length_cons, List.length_nil] at this
  omega

theorem eq_one_of_linear {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) {ω : K}
    (h1 : ω ≠ 1) (h3 : ω ^ 3 = 1) (T : Multiplicative (Fin 3 → K) →* Multiplicative (Fin 3 → K))
    (hcomm : ∀ y : Fin 3 → K, T (Multiplicative.ofAdd (ω • y)) =
      Multiplicative.ofAdd (ω • Multiplicative.toAdd (T (Multiplicative.ofAdd y))))
    (hfix : 32 ≤ Nat.card ↥(MonoidHom.eqLocus T (MonoidHom.id _))) :
    ∀ q, T q = q := by
  have h4 := four_elems hK h1 h3
  let S : Submodule K (Fin 3 → K) :=
    { carrier := {y | T (Multiplicative.ofAdd y) = Multiplicative.ofAdd y}
      add_mem' := fun {a b} ha hb => by
        show T (Multiplicative.ofAdd (a + b)) = Multiplicative.ofAdd (a + b)
        rw [ofAdd_add, map_mul]
        exact congrArg₂ (· * ·) ha hb
      zero_mem' := by
        show T (Multiplicative.ofAdd 0) = Multiplicative.ofAdd 0
        rw [ofAdd_zero, map_one]
      smul_mem' := fun a y hy => by
        have hω : ∀ z ∈ {y : Fin 3 → K | T (Multiplicative.ofAdd y) = Multiplicative.ofAdd y},
            ω • z ∈ {y : Fin 3 → K | T (Multiplicative.ofAdd y) = Multiplicative.ofAdd y} := by
          intro z hz
          show T (Multiplicative.ofAdd (ω • z)) = Multiplicative.ofAdd (ω • z)
          rw [hcomm, show T (Multiplicative.ofAdd z) = Multiplicative.ofAdd z from hz]
          rfl
        rcases h4 a with rfl | rfl | rfl | rfl
        · show T (Multiplicative.ofAdd (0 • y)) = Multiplicative.ofAdd (0 • y)
          rw [zero_smul, ofAdd_zero, map_one]
        · simpa using hy
        · exact hω y hy
        · rw [pow_two, mul_smul]
          exact hω _ (hω y hy) }
  have hS : Nat.card S ≥ 32 := by
    refine le_of_le_of_eq hfix ?_
    exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun q => by
      show T q = q ↔ T (Multiplicative.ofAdd (Multiplicative.toAdd q)) =
        Multiplicative.ofAdd (Multiplicative.toAdd q)
      rfl)
  have hcard := Module.natCard_eq_pow_finrank (K := K) (V := S)
  rw [hK] at hcard
  have hfr : Module.finrank K S = 3 := by
    have hle : Module.finrank K S ≤ 3 := by
      have := Submodule.finrank_le S
      rwa [Module.finrank_fin_fun] at this
    by_contra hne
    have : Module.finrank K S ≤ 2 := by omega
    have : 4 ^ Module.finrank K S ≤ 4 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have htop : S = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hfr, Module.finrank_fin_fun])
  intro q
  have : Multiplicative.toAdd q ∈ S := by rw [htop]; trivial
  exact this

end CFSG.Quasithin.C124.YL.H6
