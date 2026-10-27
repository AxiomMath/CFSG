module

public import CFSG.RankThree.PartOne.AUTSL.FourStr
public import CFSG.RankThree.PartOne.KF1514B.Torus4

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.AUTSL.Four

open Matrix CFSG.RankThree.PartOne.KF1514B CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LieType.Universal.Spin

section Iota

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

@[expose] def jfun (b c : K) (v : PV K) : Vt K :=
  (Sum.elim ![v.1 0 0 + v.1 1 0, b * v.1 1 0 + c * v.1 0 1 + c * v.1 1 1, v.2 0]
    ![b * v.1 0 1 + v.1 0 0 + v.1 1 0, v.1 0 1 + v.1 1 1, v.2 1], v.1 2)

@[expose] def ifun (b c : K) (w : Vt K) : PV K :=
  (![![w.1 (Sum.inl 0) + (w.1 (Sum.inl 1) + c * w.1 (Sum.inr 1)) / b,
        (w.1 (Sum.inr 0) + w.1 (Sum.inl 0)) / b],
      ![(w.1 (Sum.inl 1) + c * w.1 (Sum.inr 1)) / b,
        w.1 (Sum.inr 1) + (w.1 (Sum.inr 0) + w.1 (Sum.inl 0)) / b],
      w.2], ![w.1 (Sum.inl 2), w.1 (Sum.inr 2)])

theorem jfun_add (u v : PV K) : jfun b c (u + v) = jfun b c u + jfun b c v := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · rcases i with i | i <;> fin_cases i <;> simp [jfun] <;> ring
  · simp [jfun]

theorem jfun_smul (r : K) (v : PV K) : jfun b c (r • v) = r • jfun b c v := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · rcases i with i | i <;> fin_cases i <;> simp [jfun] <;> ring
  · simp [jfun]

theorem ifun_jfun (v : PV K) : ifun b c (jfun b c v) = v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hb : b ≠ 0 := b_ne_zero (c := c)
  have L1 : (b * v.1 1 0 + c * v.1 0 1 + c * v.1 1 1 + c * (v.1 0 1 + v.1 1 1)) / b =
      v.1 1 0 := by
    rw [div_eq_iff hb]
    linear_combination (c * (v.1 0 1 + v.1 1 1)) * h2
  have L2 : (b * v.1 0 1 + v.1 0 0 + v.1 1 0 + (v.1 0 0 + v.1 1 0)) / b = v.1 0 1 := by
    rw [div_eq_iff hb]
    linear_combination (v.1 0 0 + v.1 1 0) * h2
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · fin_cases i
    · funext j
      fin_cases j
      · simp [ifun, jfun]
        rw [L1]
        linear_combination v.1 1 0 * h2
      · simp [ifun, jfun]
        exact L2
    · funext j
      fin_cases j
      · simp [ifun, jfun]
        exact L1
      · simp [ifun, jfun]
        rw [L2]
        linear_combination v.1 0 1 * h2
    · simp [ifun, jfun]
  · fin_cases i <;> simp [ifun, jfun]

theorem jfun_ifun (w : Vt K) : jfun b c (ifun b c w) = w := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hb : b ≠ 0 := b_ne_zero (c := c)
  have hbP : b * ((w.1 (Sum.inr 0) + w.1 (Sum.inl 0)) / b) =
      w.1 (Sum.inr 0) + w.1 (Sum.inl 0) := mul_div_cancel₀ _ hb
  have hbR : b * ((w.1 (Sum.inl 1) + c * w.1 (Sum.inr 1)) / b) =
      w.1 (Sum.inl 1) + c * w.1 (Sum.inr 1) := mul_div_cancel₀ _ hb
  refine Prod.ext (funext fun i => ?_) ?_
  · rcases i with i | i <;> fin_cases i <;> simp [ifun, jfun]
    · linear_combination ((w.1 (Sum.inl 1) + c * w.1 (Sum.inr 1)) / b) * h2
    · linear_combination hbR + (c * ((w.1 (Sum.inr 0) + w.1 (Sum.inl 0)) / b) +
        c * w.1 (Sum.inr 1)) * h2
    · linear_combination hbP + (w.1 (Sum.inl 0) +
        (w.1 (Sum.inl 1) + c * w.1 (Sum.inr 1)) / b) * h2
    · linear_combination ((w.1 (Sum.inr 0) + w.1 (Sum.inl 0)) / b) * h2
  · simp [ifun, jfun]

@[expose] noncomputable def iotaEquiv (b c : K) [AnisoPair b c] : PV K ≃ₗ[K] Vt K where
  toFun := jfun b c
  map_add' := jfun_add
  map_smul' := jfun_smul
  invFun := ifun b c
  left_inv := ifun_jfun
  right_inv := jfun_ifun

theorem iotaEquiv_apply (v : PV K) : iotaEquiv b c v = jfun b c v := rfl

theorem quadTail_iotaEquiv (v : PV K) :
    quadTail 3 (minusTailForm K b c) (iotaEquiv b c v) = Qp b c v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [iotaEquiv_apply, quadTail_apply, quadPlus_apply]
  simp only [Fin.sum_univ_three, Qp, jfun, minusTailForm_apply]
  simp
  linear_combination (v.1 0 1 * v.1 1 0 * b + c * v.1 0 1 * v.1 1 1 + v.1 0 0 * v.1 1 0) * h2

end Iota

section TorusCompat

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

@[expose] def tvec (g₁ g₂ g₃ : GL (Fin 2) K) : Fin 3 → GL (Fin 2) K := ![g₁ * g₂⁻¹, g₁ * g₂, g₃]

theorem torusHom_jfun (g₁ g₂ g₃ : Tns b c) (v : PV K) :
    torusHom b c (g₁, g₂, g₃) (jfun b c v) =
      jfun b c (diagEquiv (tvec (g₁ : GL (Fin 2) K) g₂ g₃) v) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨z₁, hz₁, h₁⟩ := g₁.2
  obtain ⟨z₂, hz₂, h₂⟩ := g₂.2
  obtain ⟨z₃, hz₃, h₃⟩ := g₃.2
  have hi₂ := Tns_inv_val hz₂ h₂
  rw [torusHom_apply, trEquiv_apply]
  refine Prod.ext (funext fun i => ?_) ?_
  · rcases i with i | i <;> fin_cases i
    · simp [trFun, jfun, Xmat, diagEquiv_apply, tvec, Units.val_mul, h₁, h₂, hi₂, Mmat,
        Matrix.mul_apply, Fin.sum_univ_two, zconj]
      linear_combination (b * (v.1 1 0) * z₁.1 * z₂.2) * h2
    · simp [trFun, jfun, Xmat, diagEquiv_apply, tvec, Units.val_mul, h₁, h₂, hi₂, Mmat,
        Matrix.mul_apply, Fin.sum_univ_two, zconj]
      linear_combination (-b ^ 2 * c * (v.1 1 1) * z₁.2 * z₂.2 + b ^ 2 * (v.1 1 0) * z₁.1 * z₂.2 -
        b * c * (v.1 1 1) * z₁.2 * z₂.1) * h2
    · simp [trFun, jfun, Xmat, diagEquiv_apply, tvec]
    · simp [trFun, jfun, Xmat, diagEquiv_apply, tvec, Units.val_mul, h₁, h₂, hi₂, Mmat,
        Matrix.mul_apply, Fin.sum_univ_two, zconj]
      linear_combination (2 * b ^ 2 * (v.1 1 0) * z₁.2 * z₂.2 + b * c * (v.1 1 1) * z₁.2 * z₂.2 +
        b * (v.1 1 0) * z₁.1 * z₂.2 + b * (v.1 1 0) * z₁.2 * z₂.1) * h2
    · simp [trFun, jfun, Xmat, diagEquiv_apply, tvec, Units.val_mul, h₁, h₂, hi₂, Mmat,
        Matrix.mul_apply, Fin.sum_univ_two, zconj]
      linear_combination (b * (v.1 1 0) * z₁.2 * z₂.2) * h2
    · simp [trFun, jfun, Xmat, diagEquiv_apply, tvec]
  · simp [trFun, jfun, Xmat, diagEquiv_apply, tvec]

end TorusCompat

section Conj

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

variable (b c) in
@[expose] noncomputable def cjEquiv : (Vt K ≃ₗ[K] Vt K) ≃* (PV K ≃ₗ[K] PV K) where
  toFun g := (iotaEquiv b c).trans (g.trans (iotaEquiv b c).symm)
  invFun h := (iotaEquiv b c).symm.trans (h.trans (iotaEquiv b c))
  left_inv g := LinearEquiv.ext fun v => by simp
  right_inv h := LinearEquiv.ext fun v => by simp
  map_mul' g g' := LinearEquiv.ext fun v => by simp

theorem cjEquiv_apply (g : Vt K ≃ₗ[K] Vt K) (v : PV K) :
    cjEquiv b c g v = (iotaEquiv b c).symm (g (iotaEquiv b c v)) := rfl

theorem cjEquiv_torusHom (g₁ g₂ g₃ : Tns b c) :
    cjEquiv b c (torusHom b c (g₁, g₂, g₃)) =
      diagEquiv (tvec (g₁ : GL (Fin 2) K) g₂ g₃) := by
  refine LinearEquiv.ext fun v => ?_
  rw [cjEquiv_apply, iotaEquiv_apply, torusHom_jfun]
  exact (iotaEquiv b c).symm_apply_apply _

theorem cjEquiv_mem_Oq {g : Vt K ≃ₗ[K] Vt K} (hg : g ∈ G0 b c) : cjEquiv b c g ∈ Oq b c := by
  intro v
  have hgo := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1
    (CFSG.LocalAnalysis.ComponentInitial.orthElementaryGroup_le
      (quadTail 3 (minusTailForm K b c)) hg)
  rw [← quadTail_iotaEquiv, ← quadTail_iotaEquiv, cjEquiv_apply, LinearEquiv.apply_symm_apply, hgo]

end Conj

section LineG0

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c] {p : ℕ}

theorem tvec_mem {g₁ g₂ g₃ : GL (Fin 2) K} (h₁ : g₁ ∈ Tp b c p) (h₂ : g₂ ∈ Tp b c p)
    (h₃ : g₃ ∈ Tp b c p) : ∀ x, tvec g₁ g₂ g₃ x ∈ Tp b c p := by
  intro x
  fin_cases x
  · exact mul_mem h₁ (inv_mem h₂)
  · exact mul_mem h₁ h₂
  · exact h₃

theorem conj_conj_inv (h : Vt K ≃ₗ[K] Vt K) (X : Subgroup (Vt K ≃ₗ[K] Vt K)) :
    (X.map (MulAut.conj h).toMonoidHom).map (MulAut.conj h⁻¹).toMonoidHom = X := by
  rw [Subgroup.map_map]
  have : (MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
      MonoidHom.id (Vt K ≃ₗ[K] Vt K) :=
    MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
  rw [this, Subgroup.map_id]

theorem lineStr_G0 (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (hcard : Nat.card ↥(G0 b c) = (Nat.card K) ^ 12 * ((Nat.card K) ^ 4 + 1) *
      (((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 4 - 1) * ((Nat.card K) ^ 6 - 1)))
    {Ē : Subgroup (Vt K ≃ₗ[K] Vt K)} (hĒ : Ē ≤ G0 b c) (hexp : ∀ a ∈ Ē, a ^ p = 1)
    (hcardE : Nat.card Ē = p ^ 3) :
    ∃ lam : Fin 3 → Subgroup (Vt K ≃ₗ[K] Vt K), LineStr p (G0 b c) Ē lam := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h, hh, hle⟩ := exists_conj_le_torusHom hp5 hcard hpq hĒ hexp
  have hEle : Ē.map (MulAut.conj h).toMonoidHom ≤
      (E0 b c p).map (cjEquiv b c).symm.toMonoidHom := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨t, ht⟩ := hle (Subgroup.mem_map_of_mem _ he)
    have hpow : torusHom b c (t ^ p) = 1 := by
      rw [map_pow, ht, ← map_pow, hexp e he, map_one]
    have ht1 : t ^ p = 1 := torusHom_injective (by rw [hpow, map_one])
    obtain ⟨g₁, g₂, g₃⟩ := t
    have hg : ∀ g : Tns b c, g ^ p = 1 → (g : GL (Fin 2) K) ∈ Tp b c p := fun g hg =>
      ⟨g.2, by rw [← Subgroup.coe_pow, hg, Subgroup.coe_one]⟩
    have h1 := hg g₁ (congrArg Prod.fst ht1)
    have h2 := hg g₂ (congrArg (fun z => z.2.1) ht1)
    have h3 := hg g₃ (congrArg (fun z => z.2.2) ht1)
    refine ⟨cjEquiv b c ((MulAut.conj h).toMonoidHom e), ?_, by simp⟩
    rw [← ht, cjEquiv_torusHom]
    exact ⟨fun x => ⟨tvec (g₁ : GL (Fin 2) K) g₂ g₃ x, tvec_mem h1 h2 h3 x⟩, rfl⟩
  have hcard1 : Nat.card ↥(Ē.map (MulAut.conj h).toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hcardE]
  have hcard2 : Nat.card ↥((E0 b c p).map (cjEquiv b c).symm.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective (cjEquiv b c).symm.injective, card_E0 hp hpq]
  have hEeq : Ē.map (MulAut.conj h).toMonoidHom = (E0 b c p).map (cjEquiv b c).symm.toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hEle (by rw [hcard1, hcard2])
  have hG0 : G0 b c ≤ (Oq b c).map (cjEquiv b c).symm.toMonoidHom := by
    intro g hg
    exact ⟨cjEquiv b c g, cjEquiv_mem_Oq hg, by simp⟩
  have hstr := ((lineStr_plane (b := b) (c := c) hp hp5 hpq).map (cjEquiv b c).symm).anti hG0
  have hstr2 := hstr.map (MulAut.conj h⁻¹)
  have hG0' : G0 b c ≤ ((G0 b c).map (MulAut.conj h⁻¹).toMonoidHom) := by
    intro g hg
    refine ⟨h * g * h⁻¹, mul_mem (mul_mem hh hg) (inv_mem hh), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hstr3 := hstr2.anti hG0'
  rw [← hEeq, conj_conj_inv] at hstr3
  exact ⟨_, hstr3⟩

end LineG0

end CFSG.RankThree.PartOne.AUTSL.Four
