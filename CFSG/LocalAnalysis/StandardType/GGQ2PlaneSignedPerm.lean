module

public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalNormalizers

public section

namespace CFSG.StandardType.GGQ2Frame.PlaneRaw

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

private lemma orientEquiv_mul_self (t : ℕ) (e : V t) :
    orientEquiv t e * orientEquiv t e = 1 := by
  ext w k
  simp only [LinearEquiv.mul_apply, orientEquiv, LinearEquiv.piCongrRight_apply]
  split_ifs <;> simp

private lemma orient_coeff_of_ne_zero {x : F} (h : x ≠ 0) :
    (if x = -1 then (-1 : F) else 1) = x := by
  have h3 : ∀ y : F, y = 0 ∨ y = 1 ∨ y = -1 := by decide
  rcases h3 x with h0 | h1 | h1
  · exact absurd h0 h
  · rw [h1]
    decide
  · rw [h1]
    decide

theorem exists_signedPerm_of_mem_signedPermGroup {t : ℕ} {φ : V t ≃ₗ[F] V t}
    (hφ : φ ∈ signedPermGroup t) :
    ∃ (σ : Equiv.Perm (Fin t)) (ε : Fin t → F), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ u i, φ u i = ε i * u (σ.symm i) := by
  refine Subgroup.closure_induction (p := fun x _ => ∃ (σ : Equiv.Perm (Fin t)) (ε : Fin t → F),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ u i, x u i = ε i * u (σ.symm i)) ?_ ?_ ?_ ?_ hφ
  · intro x hx
    rcases hx with ⟨i, j, rfl⟩ | ⟨i, rfl⟩
    · refine ⟨Equiv.swap i j, fun _ => 1, fun _ => Or.inl rfl, ?_⟩
      intro u k
      simp [swapEquiv, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    · refine ⟨1, fun k => if k = i then (-1 : F) else 1, ?_, ?_⟩
      · intro k
        by_cases hk : k = i <;> simp [hk]
      · intro u k
        simp [negEquiv, LinearEquiv.piCongrRight_apply, Equiv.Perm.one_symm]
        split_ifs <;> simp
  · exact ⟨1, fun _ => 1, fun _ => Or.inl rfl, by intro u i; simp [Equiv.Perm.one_symm]⟩
  · rintro x y _ _ ⟨σ, ε, hε, hx⟩ ⟨τ, δ, hδ, hy⟩
    refine ⟨σ * τ, fun i => ε i * δ (σ.symm i), ?_, ?_⟩
    · intro i
      rcases hε i with h | h <;> rcases hδ (σ.symm i) with h' | h' <;> simp [h, h']
    · intro u i
      have hmul : (σ * τ).symm i = τ.symm (σ.symm i) := by
        rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply]
      rw [LinearEquiv.mul_apply, hx, hy, hmul, mul_assoc]
  · rintro x _ ⟨σ, ε, hε, hx⟩
    refine ⟨σ.symm, fun i => ε (σ i), ?_, ?_⟩
    · intro i
      exact hε (σ i)
    · intro u j
      have h := hx (x.symm u) (σ j)
      simp only [LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply] at h
      have hsq : ε (σ j) * ε (σ j) = 1 := by
        rcases hε (σ j) with h' | h' <;> rw [h'] <;> decide
      have hgoal : (σ.symm).symm j = σ j := by simp
      rw [hgoal]
      calc
        x.symm u j = (ε (σ j) * ε (σ j)) * (x.symm u j) := by rw [hsq, one_mul]
        _ = ε (σ j) * (ε (σ j) * (x.symm u j)) := by ring
        _ = ε (σ j) * u (σ j) := by rw [← h]

theorem mem_twistedPermGroupOn_of_mem_signedPermGroup {t : ℕ} {e : V t} {φ : V t ≃ₗ[F] V t}
    (hφ : φ ∈ signedPermGroup t) (he : φ e = e)
    (hoff : ∀ l, e l = 0 → φ (Pi.single l 1) = Pi.single l 1) :
    φ ∈ twistedPermGroupOn t e := by
  obtain ⟨σ, ε, hε, hφform⟩ := exists_signedPerm_of_mem_signedPermGroup hφ
  have hfix : ∀ l, e l = 0 → σ.symm l = l := by
    intro l hl
    have h := congrArg (fun v => v l) (hoff l hl)
    rw [hφform (Pi.single l 1) l] at h
    by_cases hσ : σ.symm l = l
    · exact hσ
    · exfalso
      simp [hσ] at h
  have heps_zero : ∀ l, e l = 0 → ε l = 1 := by
    intro l hl
    have h := congrArg (fun v => v l) (hoff l hl)
    rw [hφform (Pi.single l 1) l] at h
    rw [hfix l hl] at h
    simpa using h
  have hfixσ : ∀ l, e l = 0 → σ l = l := by
    intro l hl
    have h := congrArg σ (hfix l hl)
    simpa using h.symm
  have hsupp_symm : ∀ i, e i ≠ 0 → e (σ.symm i) ≠ 0 := by
    intro i hi hzero
    have h := hfixσ (σ.symm i) hzero
    have hi' : i = σ.symm i := by simpa using h
    exact hi (by rwa [← hi'] at hzero)
  have heps : ∀ i, e i ≠ 0 → ε i = e i * e (σ.symm i) := by
    intro i hi
    have h := congrArg (fun v => v i) he
    rw [hφform e i] at h
    have hne := hsupp_symm i hi
    have h3 : ∀ y : F, y = 0 ∨ y = 1 ∨ y = -1 := by decide
    rcases h3 (e (σ.symm i)) with hv | hv | hv
    · exact absurd hv hne
    · rw [hv, mul_one] at h
      rw [hv, mul_one]
      exact h
    · rw [hv, mul_neg, mul_one] at h
      rw [hv, mul_neg, mul_one]
      simpa using congrArg Neg.neg h
  have hOO : orientEquiv t e * orientEquiv t e = 1 := orientEquiv_mul_self t e
  have hOinv : (orientEquiv t e)⁻¹ = orientEquiv t e :=
    inv_eq_of_mul_eq_one_right hOO
  have hOapply : ∀ (v : V t) (k : Fin t),
      orientEquiv t e v k = (if e k = -1 then (-1 : F) else 1) * v k := by
    intro v k
    simp [orientEquiv, LinearEquiv.piCongrRight_apply]
    split_ifs <;> simp
  have hPapply : ∀ (v : V t) (k : Fin t),
      LinearEquiv.funCongrLeft F F σ.symm v k = v (σ.symm k) := by
    intro v k
    simp [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  have hphiO : φ =
      (orientEquiv t e)⁻¹ * LinearEquiv.funCongrLeft F F σ.symm * orientEquiv t e := by
    apply LinearEquiv.ext
    intro u
    funext i
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hOinv, hOapply, hPapply, hOapply]
    by_cases hi : e i = 0
    · have hσi : σ.symm i = i := hfix i hi
      have hεi : ε i = 1 := heps_zero i hi
      have hci : (if e i = -1 then (-1 : F) else 1) = 1 := by simp [hi]
      have hcs : (if e (σ.symm i) = -1 then (-1 : F) else 1) = 1 := by
        rw [hσi, hi]
        decide
      rw [hci, hcs, one_mul, one_mul]
      simpa [hεi] using hφform u i
    · have hne : e (σ.symm i) ≠ 0 := hsupp_symm i hi
      have hεi : ε i = e i * e (σ.symm i) := heps i hi
      have hci : (if e i = -1 then (-1 : F) else 1) = e i := orient_coeff_of_ne_zero hi
      have hcs : (if e (σ.symm i) = -1 then (-1 : F) else 1) = e (σ.symm i) :=
        orient_coeff_of_ne_zero hne
      rw [hci, hcs, ← mul_assoc, ← hεi]
      exact hφform u i
  have hpres : ∀ x : Fin t, (e (σ x) ≠ 0) ↔ (e x ≠ 0) := by
    intro x
    constructor
    · intro hx hx0
      have h := hfixσ x hx0
      exact hx (by rwa [h])
    · intro hx hx0
      have h := hfixσ (σ x) hx0
      have h' : σ x = x := by
        have := congrArg σ.symm h
        simpa using this
      exact hx (by rwa [h'] at hx0)
  have hfixoff : ∀ x : Fin t, σ x ≠ x → e x ≠ 0 := by
    intro x hx hx0
    exact hx (hfixσ x hx0)
  let Pmap : Equiv.Perm (Fin t) →* (V t ≃ₗ[F] V t) :=
    MonoidHom.mk' (fun τ => LinearEquiv.funCongrLeft F F τ.symm) (by
      intro α β
      ext u i
      simp [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, LinearEquiv.mul_apply,
        Equiv.Perm.mul_def])
  let H : Equiv.Perm {i : Fin t // e i ≠ 0} →* (V t ≃ₗ[F] V t) :=
    (MulAut.conj (orientEquiv t e)).toMonoidHom.comp (Pmap.comp Equiv.Perm.ofSubtype)
  have hHswap : ∀ (a b : {i : Fin t // e i ≠ 0}), a ≠ b →
      H (Equiv.swap a b) = swapTwist t e a b := by
    intro a b hab
    change (MulAut.conj (orientEquiv t e))
      (Pmap (Equiv.Perm.ofSubtype (Equiv.swap a b))) = swapTwist t e ↑a ↑b
    rw [Equiv.Perm.ofSubtype_swap_eq]
    change orientEquiv t e *
      LinearEquiv.funCongrLeft F F (Equiv.symm (Equiv.swap (a : Fin t) (b : Fin t))) *
      (orientEquiv t e)⁻¹ = swapTwist t e (a : Fin t) (b : Fin t)
    rw [Equiv.symm_swap, swapTwist, swapEquiv, hOinv]
  have hrange : H.range ≤ twistedPermGroupOn t e := by
    rw [MonoidHom.range_eq_map, ← Equiv.Perm.closure_isSwap, MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨a, b, hab, rfl⟩ := hτ
    rw [hHswap a b hab]
    exact Subgroup.subset_closure ⟨a, b, a.2, b.2, rfl⟩
  let τ : Equiv.Perm {i : Fin t // e i ≠ 0} := σ.subtypePerm hpres
  have hτ : Equiv.Perm.ofSubtype τ = σ := Equiv.Perm.ofSubtype_subtypePerm hpres hfixoff
  have hHτ : H τ = φ := by
    change (MulAut.conj (orientEquiv t e)) (Pmap (Equiv.Perm.ofSubtype τ)) = φ
    rw [hτ]
    change orientEquiv t e * LinearEquiv.funCongrLeft F F σ.symm * (orientEquiv t e)⁻¹ = φ
    rw [hphiO, hOinv]
  have hmem : H τ ∈ twistedPermGroupOn t e := hrange ⟨τ, rfl⟩
  rwa [hHτ] at hmem

end

end CFSG.StandardType.GGQ2Frame.PlaneRaw
