module

public import CFSG.Quasithin.Background.G64Case1Pre
public import CFSG.Quasithin.Background.B4ModelsWitness

public section

namespace CFSG.Quasithin.G64

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit

section Zorn

variable {F : Type} [Field F]

theorem add_zornMul (x x' y : quasithinZorn F) :
    quasithinZornMul (x + x') y = quasithinZornMul x y + quasithinZornMul x' y := by
  obtain ⟨r, u, v, s⟩ := x
  obtain ⟨r', u', v', s'⟩ := x'
  obtain ⟨t, a, b, z⟩ := y
  simp only [quasithinZornMul, Prod.mk_add_mk, Pi.add_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [add_mul, Finset.sum_add_distrib]
    ring
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · simp only [add_mul, Finset.sum_add_distrib]
    ring

theorem zornMul_add (x y y' : quasithinZorn F) :
    quasithinZornMul x (y + y') = quasithinZornMul x y + quasithinZornMul x y' := by
  obtain ⟨r, u, v, s⟩ := x
  obtain ⟨t, a, b, z⟩ := y
  obtain ⟨t', a', b', z'⟩ := y'
  simp only [quasithinZornMul, Prod.mk_add_mk, Pi.add_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [mul_add, Finset.sum_add_distrib]
    ring
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · simp only [mul_add, Finset.sum_add_distrib]
    ring

theorem smul_zornMul (c : F) (x y : quasithinZorn F) :
    quasithinZornMul (c • x) y = c • quasithinZornMul x y := by
  obtain ⟨r, u, v, s⟩ := x
  obtain ⟨t, a, b, z⟩ := y
  simp only [quasithinZornMul, Prod.smul_mk, Pi.smul_apply, smul_eq_mul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [Finset.mul_sum, mul_add]
    exact congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun _ _ => by ring)
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · simp only [Finset.mul_sum, mul_add]
    exact congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun _ _ => by ring)

theorem zornMul_smul (c : F) (x y : quasithinZorn F) :
    quasithinZornMul x (c • y) = c • quasithinZornMul x y := by
  obtain ⟨r, u, v, s⟩ := x
  obtain ⟨t, a, b, z⟩ := y
  simp only [quasithinZornMul, Prod.smul_mk, Pi.smul_apply, smul_eq_mul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [Finset.mul_sum, mul_add]
    exact congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun _ _ => by ring)
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · simp only [Finset.mul_sum, mul_add]
    exact congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun _ _ => by ring)

theorem zornMul_alt_left (w z : quasithinZorn F) :
    quasithinZornMul w (quasithinZornMul w z) = quasithinZornMul (quasithinZornMul w w) z := by
  obtain ⟨a, u, v, b⟩ := w
  obtain ⟨c, x, y, d⟩ := z
  simp only [quasithinZornMul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp [quasithinCross, Fin.sum_univ_three]
    ring
  · funext i
    fin_cases i <;> simp [quasithinCross, Fin.sum_univ_three] <;> ring
  · funext i
    fin_cases i <;> simp [quasithinCross, Fin.sum_univ_three] <;> ring
  · simp [quasithinCross, Fin.sum_univ_three]
    ring

theorem cayleyPolar_comm (x y : quasithinZorn F) : cayleyPolar x y = cayleyPolar y x := by
  rw [cayleyPolar_eq, cayleyPolar_eq]
  simp only [Fin.sum_univ_three]
  ring

theorem cayleyPolar_add_left (x y z : quasithinZorn F) :
    cayleyPolar (x + y) z = cayleyPolar x z + cayleyPolar y z := by
  simp only [cayleyPolar_eq, Fin.sum_univ_three, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  ring

theorem cayleyPolar_add_right (x y z : quasithinZorn F) :
    cayleyPolar x (y + z) = cayleyPolar x y + cayleyPolar x z := by
  rw [cayleyPolar_comm, cayleyPolar_add_left, cayleyPolar_comm y, cayleyPolar_comm z]

theorem cayleyPolar_smul_left (c : F) (x y : quasithinZorn F) :
    cayleyPolar (c • x) y = c * cayleyPolar x y := by
  simp only [cayleyPolar_eq, Fin.sum_univ_three, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem cayleyPolar_one_left (y : quasithinZorn F) : cayleyPolar zornOne y = cayleyTr y := by
  simp only [cayleyPolar_eq, zornOne, cayleyTr, Pi.zero_apply, zero_mul, mul_zero, add_zero,
    Finset.sum_const_zero, one_mul, mul_one]
  ring

theorem cayleyPolar_self [CharP F 2] (x : quasithinZorn F) : cayleyPolar x x = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [cayleyPolar_eq]
  simp only [Fin.sum_univ_three]
  linear_combination (x.1 * x.2.2.2 + x.2.1 0 * x.2.2.1 0 + x.2.1 1 * x.2.2.1 1 +
    x.2.1 2 * x.2.2.1 2) * h2

theorem cayleyNorm_add (x y : quasithinZorn F) :
    cayleyNorm (x + y) = cayleyNorm x + cayleyNorm y + cayleyPolar x y := by
  rw [cayleyPolar]
  ring

theorem cayleyNorm_smul_one (c : F) : cayleyNorm (c • zornOne : quasithinZorn F) = c * c := by
  simp [cayleyNorm, zornOne]

theorem cayleyTr_zornMul [CharP F 2] {x y : quasithinZorn F} (hx : cayleyTr x = 0)
    (hy : cayleyTr y = 0) : cayleyTr (quasithinZornMul x y) = cayleyPolar x y := by
  have hxs : x.2.2.2 = x.1 := by
    have h := eq_neg_of_add_eq_zero_right hx
    rw [h, CharTwo.neg_eq]
  have hys : y.2.2.2 = y.1 := by
    have h := eq_neg_of_add_eq_zero_right hy
    rw [h, CharTwo.neg_eq]
  rw [cayleyPolar_eq]
  simp only [cayleyTr, quasithinZornMul, hxs, hys, Fin.sum_univ_three]
  ring

theorem zornMul_self_of_tr [CharP F 2] {x : quasithinZorn F} (hx : cayleyTr x = 0) :
    quasithinZornMul x x = cayleyNorm x • zornOne := by
  have hxs : x.2.2.2 = x.1 := by
    have h := eq_neg_of_add_eq_zero_right hx
    rw [h, CharTwo.neg_eq]
  have h0 : x.1 + x.2.2.2 = 0 := hx
  rw [zornMul_self]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp [cayleyNorm, zornOne, hxs]
  · simp [h0, zornOne]
  · simp [h0, zornOne]
  · simp only [cayleyNorm, zornOne, hxs, Prod.smul_snd, smul_eq_mul, mul_one]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem norm_eq_of_isZornAuto [CharP F 2] {g : quasithinZorn F ≃ₗ[F] quasithinZorn F}
    (hg : IsZornAuto g) {x : quasithinZorn F} (hx : cayleyTr x = 0) :
    cayleyNorm (g x) = cayleyNorm x := by
  have hgx : cayleyTr (g x) = 0 := hg.trace_zero hx
  have h1 := hg x x
  rw [zornMul_self_of_tr hx, zornMul_self_of_tr hgx, map_smul, hg.map_one] at h1
  have h2 := congrArg Prod.fst h1
  simp only [zornOne, Prod.smul_fst, smul_eq_mul, mul_one] at h2
  exact h2.symm

theorem polar_eq_of_isZornAuto [CharP F 2] {g : quasithinZorn F ≃ₗ[F] quasithinZorn F}
    (hg : IsZornAuto g) {x y : quasithinZorn F} (hx : cayleyTr x = 0) (hy : cayleyTr y = 0) :
    cayleyPolar (g x) (g y) = cayleyPolar x y := by
  have hxy : cayleyTr (x + y) = 0 := by
    simp only [cayleyTr, Prod.fst_add, Prod.snd_add] at hx hy ⊢
    linear_combination hx + hy
  simp only [cayleyPolar]
  rw [← map_add, norm_eq_of_isZornAuto hg hxy, norm_eq_of_isZornAuto hg hx,
    norm_eq_of_isZornAuto hg hy]

theorem exists_ne_zero_orth_two (p q : Fin 3 → F) :
    ∃ c : Fin 3 → F, c ≠ 0 ∧ ∑ i, c i * p i = 0 ∧ ∑ i, c i * q i = 0 := by
  classical
  set M : Matrix (Fin 3) (Fin 3) F := Matrix.of ![p, q, 0] with hM
  have hdet : M.det = 0 := Matrix.det_eq_zero_of_row_eq_zero 2 fun j => by simp [hM]
  obtain ⟨c, hc, hMc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have h0 := congrFun hMc 0
  have h1 := congrFun hMc 1
  simp only [hM, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply] at h0 h1
  refine ⟨c, hc, ?_, ?_⟩
  · rw [← h0]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · rw [← h1]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem false_of_transvec_zorn [CharP F 2] {g : quasithinZorn F ≃ₗ[F] quasithinZorn F}
    (hg : IsZornAuto g) {x₁ : quasithinZorn F} (hx₁ : cayleyTr x₁ = 0)
    (hw : ¬ ∃ c : F, g x₁ - x₁ = c • zornOne)
    (hall : ∀ x, cayleyTr x = 0 → (∃ c : F, g x - x = c • zornOne) ∨
      ∃ c : F, g x - x = (g x₁ - x₁) + c • zornOne) : False := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  set w := g x₁ - x₁ with hwdef
  have hgx₁ : g x₁ = x₁ + w := by
    rw [hwdef]
    abel
  have hwtr : cayleyTr w = 0 := by
    have h := hg.trace_zero (x := x₁) hx₁
    have h' : x₁.1 + x₁.2.2.2 = 0 := hx₁
    show (g x₁ - x₁).1 + (g x₁ - x₁).2.2.2 = 0
    simp only [Prod.fst_sub, Prod.snd_sub]
    linear_combination h - h'
  have hkey : ∀ y, cayleyTr y = 0 →
      cayleyPolar y w + cayleyPolar (g y - y) x₁ + cayleyPolar (g y - y) w = 0 := by
    intro y hy
    have h1 : cayleyPolar (y + (g y - y)) (x₁ + w) = cayleyPolar y x₁ := by
      rw [show y + (g y - y) = g y by abel, ← hgx₁]
      exact polar_eq_of_isZornAuto hg hy hx₁
    rw [cayleyPolar_add_left, cayleyPolar_add_right, cayleyPolar_add_right] at h1
    linear_combination h1
  have hone : ∀ (c : F) (y : quasithinZorn F), cayleyTr y = 0 →
      cayleyPolar (c • zornOne) y = 0 := by
    intro c y hy
    rw [cayleyPolar_smul_left, cayleyPolar_one_left, hy, mul_zero]
  have hnd : ∃ y, cayleyTr y = 0 ∧ cayleyPolar w y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c, hc⟩ := (cayleyPolar_radical hwtr).1 hcon
    exact hw ⟨c, by rw [hc]; simp [zornOne]⟩
  have hβ : cayleyPolar w x₁ ≠ 0 := by
    intro hB
    obtain ⟨y, hy, hwy⟩ := hnd
    apply hwy
    rw [cayleyPolar_comm]
    have hk := hkey y hy
    rcases hall y hy with ⟨c, hc⟩ | ⟨c, hc⟩
    · rw [hc, hone c x₁ hx₁, hone c w hwtr] at hk
      linear_combination hk
    · rw [hc, cayleyPolar_add_left, cayleyPolar_add_left, hone c x₁ hx₁, hone c w hwtr, hB,
        cayleyPolar_self] at hk
      linear_combination hk
  have hfix : ∀ y, cayleyTr y = 0 → cayleyPolar y w = 0 → g y = y := by
    intro y hy hyw
    rcases hall y hy with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hN := norm_eq_of_isZornAuto hg hy
      have e : g y = y + c • zornOne := by
        rw [← hc]
        abel
      rw [e, cayleyNorm_add, cayleyNorm_smul_one, cayleyPolar_comm, hone c y hy] at hN
      have hc0 : c * c = 0 := by linear_combination hN
      rw [e, mul_self_eq_zero.mp hc0, zero_smul, add_zero]
    · exfalso
      have hk := hkey y hy
      rw [hc, hyw, cayleyPolar_add_left, cayleyPolar_add_left, hone c x₁ hx₁, hone c w hwtr,
        cayleyPolar_self] at hk
      exact hβ (by linear_combination hk)
  have hNw : cayleyNorm w = cayleyPolar w x₁ := by
    have hN := norm_eq_of_isZornAuto hg hx₁
    rw [hgx₁, cayleyNorm_add, cayleyPolar_comm] at hN
    linear_combination hN - cayleyPolar w x₁ * h2
  have hww : quasithinZornMul w w = cayleyPolar w x₁ • zornOne := by
    rw [zornMul_self_of_tr hwtr, hNw]
  obtain ⟨c, hc0, hcw, hcx⟩ := exists_ne_zero_orth_two w.2.2.1 x₁.2.2.1
  set z : quasithinZorn F := (0, c, 0, 0) with hz
  have hztr : cayleyTr z = 0 := by simp [hz, cayleyTr]
  have hzP : ∀ y, cayleyPolar z y = ∑ i, c i * y.2.2.1 i := by
    intro y
    rw [cayleyPolar_eq]
    simp [hz]
  have hzx : cayleyPolar z x₁ = 0 := by rw [hzP]; exact hcx
  have hgz : g z = z := hfix z hztr (by rw [hzP]; exact hcw)
  have hp : cayleyTr (quasithinZornMul x₁ z) = 0 := by
    rw [cayleyTr_zornMul hx₁ hztr, cayleyPolar_comm, hzx]
  have hgp : g (quasithinZornMul x₁ z) - quasithinZornMul x₁ z = quasithinZornMul w z := by
    rw [hg x₁ z, hgz, hgx₁, add_zornMul]
    abel
  have halt : quasithinZornMul w (quasithinZornMul w z) = cayleyPolar w x₁ • z := by
    rw [zornMul_alt_left, hww, smul_zornMul, zornMul_one_left]
  rcases hall _ hp with ⟨d, hd⟩ | ⟨d, hd⟩
  · rw [hgp] at hd
    rw [hd, zornMul_smul, zornMul_one_right] at halt
    have h1 := congrArg (fun t => cayleyPolar t x₁) halt
    simp only [cayleyPolar_smul_left, hzx, mul_zero] at h1
    have hd0 : d = 0 := (mul_eq_zero.mp h1).resolve_right hβ
    rw [hd0, zero_smul] at halt
    have hz0 : z = 0 := (smul_eq_zero.mp halt.symm).resolve_left hβ
    apply hc0
    have := congrArg (fun t => t.2.1) hz0
    simpa [hz] using this
  · rw [hgp] at hd
    rw [hd, zornMul_add, zornMul_smul, zornMul_one_right, hww] at halt
    have h1 := congrArg (fun t => cayleyPolar t x₁) halt
    simp only [cayleyPolar_add_left, cayleyPolar_smul_left, cayleyPolar_one_left, hx₁, hzx,
      mul_zero, zero_add] at h1
    have hd0 : d = 0 := (mul_eq_zero.mp h1).resolve_right hβ
    rw [hd0, zero_smul, add_zero] at halt
    have hz1 : zornOne = z := smul_right_injective _ hβ halt
    have := congrArg Prod.fst hz1
    simp [hz, zornOne] at this

end Zorn

theorem g2NoTransvection : G2NoTransvection := by
  intro F _ _ hF γ h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨m', hm', hmv, hall⟩ := h
  set g : quasithinZorn F ≃ₗ[F] quasithinZorn F := (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F)
    with hg
  set x₁ : quasithinZorn F := Multiplicative.toAdd (m' : Multiplicative (quasithinZorn F))
    with hx₁
  have hact : ∀ x : quasithinZorn F, zornAct (quasithinG2 F) γ (Multiplicative.ofAdd x) *
      (Multiplicative.ofAdd x)⁻¹ = Multiplicative.ofAdd (g x - x) := by
    intro x
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, sub_eq_add_neg]
    rfl
  have hy₁R : Multiplicative.ofAdd (g x₁ - x₁) ∉ zornR F := by
    rw [← hact]
    exact hmv
  have hall' : ∀ x : quasithinZorn F, Multiplicative.ofAdd x ∈ zornO0 F →
      Multiplicative.ofAdd (g x - x) ∈ zornR F ∨
        Multiplicative.ofAdd ((g x - x) - (g x₁ - x₁)) ∈ zornR F := by
    intro x hx
    rcases hall (Multiplicative.ofAdd x) hx with h0 | h0
    · left
      rw [← hact]
      exact h0
    · right
      have e : Multiplicative.ofAdd ((g x - x) - (g x₁ - x₁)) =
          zornAct (quasithinG2 F) γ (Multiplicative.ofAdd x) * (Multiplicative.ofAdd x)⁻¹ *
            (zornAct (quasithinG2 F) γ (Multiplicative.ofAdd x₁) *
              (Multiplicative.ofAdd x₁)⁻¹)⁻¹ := by
        rw [hact, hact]
        apply Multiplicative.toAdd.injective
        rw [toAdd_ofAdd, toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, sub_eq_add_neg]
      rw [e]
      exact h0
  have hsm : ∀ c : F, (c • zornOne : quasithinZorn F) = (c, 0, 0, c) := fun c => by
    simp [zornOne]
  refine false_of_transvec_zorn (mem_quasithinG2_isZornAuto γ.2) (x₁ := x₁) hm' ?_ ?_
  · rintro ⟨c, hc⟩
    exact hy₁R (mem_zornR.2 ⟨c, by rw [toAdd_ofAdd, hc, hsm]⟩)
  · intro x hx
    rcases hall' x (mem_zornO0.2 hx) with h0 | h0
    · obtain ⟨c, hc⟩ := mem_zornR.1 h0
      exact Or.inl ⟨c, by rw [hsm, ← hc, toAdd_ofAdd]⟩
    · obtain ⟨c, hc⟩ := mem_zornR.1 h0
      refine Or.inr ⟨c, ?_⟩
      rw [hsm, ← hc, toAdd_ofAdd]
      abel

end CFSG.Quasithin.G64
