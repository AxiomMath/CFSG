module

public import CFSG.Quasithin.Background.SmithB51LnSum

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique Matrix Module
open scoped Matrix

theorem transpose_eq_of_graph_invol {n : ℕ} {σ : ↥(StatedSL n (ZMod 2)) ≃* ↥(StatedSL n (ZMod 2))}
    (hσ : ∀ γ, σ (σ γ) = γ) {P : GL (Fin n) (ZMod 2)}
    (hP : ∀ γ, (P : Matrix (Fin n) (Fin n) (ZMod 2)) * mat γ =
      dmat (σ γ) * (P : Matrix (Fin n) (Fin n) (ZMod 2))) :
    (P : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = (P : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  set Pm := (P : Matrix (Fin n) (Fin n) (ZMod 2)) with hPm
  set Pi := ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) with hPi
  have hPPi : Pm * Pi = 1 := by rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : ∀ γ, mat (σ γ) = Pi * dmat γ * Pm := by
    intro γ
    have h := hP (σ γ)
    rw [hσ] at h
    calc mat (σ γ) = Pi * (Pm * mat (σ γ)) := by rw [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
      _ = Pi * dmat γ * Pm := by rw [h, Matrix.mul_assoc]
  have h2 : ∀ γ, dmat (σ γ) = Pmᵀ * (mat γ * Piᵀ) := by
    intro γ
    have hd : dmat γ⁻¹ = (mat γ)ᵀ := by rw [dmat, inv_inv]
    rw [dmat, ← map_inv σ γ, h1, hd, transpose_mul, transpose_mul, transpose_transpose]
  have hT : Piᵀ * Pmᵀ = 1 := by rw [← transpose_mul, hPPi, transpose_one]
  have hZ : ∀ γ, Piᵀ * Pm * mat γ = mat γ * (Piᵀ * Pm) := by
    intro γ
    calc Piᵀ * Pm * mat γ = Piᵀ * (dmat (σ γ) * Pm) := by rw [Matrix.mul_assoc, hP]
      _ = Piᵀ * (Pmᵀ * (mat γ * Piᵀ) * Pm) := by rw [h2]
      _ = (Piᵀ * Pmᵀ) * mat γ * (Piᵀ * Pm) := by simp only [Matrix.mul_assoc]
      _ = mat γ * (Piᵀ * Pm) := by rw [hT, Matrix.one_mul]
  have hz : ofGL (invT P * P) = 1 := by
    apply eq_one_of_forall_commute
    intro γ
    apply mat_injective
    rw [mat_mul, mat_mul, mat_ofGL, Units.val_mul]
    exact hZ γ
  have hZ1 : Piᵀ * Pm = 1 := by
    have h := congrArg mat hz
    rw [mat_ofGL, mat_one, Units.val_mul] at h
    exact h
  calc Pmᵀ = Pmᵀ * (Piᵀ * Pm) := by rw [hZ1, Matrix.mul_one]
    _ = (Pi * Pm)ᵀ * Pm := by rw [← Matrix.mul_assoc, ← transpose_mul]
    _ = Pm := by rw [hPiP, transpose_one, Matrix.one_mul]

section Conj

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {n : ℕ}

theorem conjSL_conjSL_of_mul_self {π : ↥(StatedSL n (ZMod 2)) →* ↥L} (hπ : Function.Bijective π)
    {g : MulAut V} (hgL : ∀ x ∈ L, g * x * g⁻¹ ∈ L) (hgL' : ∀ x ∈ L, g⁻¹ * x * g ∈ L)
    (hg2 : g * g = 1) (γ : ↥(StatedSL n (ZMod 2))) :
    conjSL hπ hgL hgL' (conjSL hπ hgL hgL' γ) = γ := by
  apply hπ.1
  apply Subtype.ext
  rw [conjSL_spec, conjSL_spec]
  calc g * (g * ((π γ : ↥L) : MulAut V) * g⁻¹) * g⁻¹ =
      (g * g) * ((π γ : ↥L) : MulAut V) * (g * g)⁻¹ := by group
    _ = ((π γ : ↥L) : MulAut V) := by rw [hg2, inv_one, one_mul, mul_one]

theorem conjSL_eq_self_of_commute {π : ↥(StatedSL n (ZMod 2)) →* ↥L} (hπ : Function.Bijective π)
    {g : MulAut V} (hgL : ∀ x ∈ L, g * x * g⁻¹ ∈ L) (hgL' : ∀ x ∈ L, g⁻¹ * x * g ∈ L)
    {γ : ↥(StatedSL n (ZMod 2))}
    (hc : g * ((π γ : ↥L) : MulAut V) = ((π γ : ↥L) : MulAut V) * g) :
    conjSL hπ hgL hgL' γ = γ := by
  apply hπ.1
  apply Subtype.ext
  rw [conjSL_spec, hc, mul_inv_cancel_right]

theorem exists_mat_dmat_conjSL {U₁ U₂ : Subgroup V} {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    (hπ : Function.Bijective π) (hn : 1 ≤ n) (h1 : RealM L U₁ ⊥ π mat)
    (h2 : RealM L U₂ ⊥ π dmat) {g : MulAut V} (hgL : ∀ x ∈ L, g * x * g⁻¹ ∈ L)
    (hgL' : ∀ x ∈ L, g⁻¹ * x * g ∈ L) (hg₁ : U₁.map g.toMonoidHom = U₂) :
    ∃ P : GL (Fin n) (ZMod 2), ∀ γ, (P : Matrix (Fin n) (Fin n) (ZMod 2)) * mat γ =
      dmat (conjSL hπ hgL hgL' γ) * (P : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  obtain ⟨-, -, hLU₁, -, β₁, hβ₁s, hβ₁k, hβ₁e⟩ := h1
  obtain ⟨-, -, hLU₂, -, β₂, -, hβ₂k, hβ₂e⟩ := h2
  set σ := conjSL hπ hgL hgL' with hσ
  have hgU : ∀ u ∈ U₁, g u ∈ U₂ := fun u hu => hg₁ ▸ Subgroup.mem_map_of_mem g.toMonoidHom hu
  have hβ₁inj : Function.Injective β₁ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβ₁k u).1 hu))
  set e₁ := MulEquiv.ofBijective β₁ ⟨hβ₁inj, hβ₁s⟩ with he₁
  have he₁β : ∀ u, e₁ u = β₁ u := fun _ => rfl
  let gr : ↥U₁ →* ↥U₂ := (g.toMonoidHom.comp U₁.subtype).codRestrict U₂ (fun u => hgU u u.2)
  have hgr : ∀ u, ((gr u : ↥U₂) : V) = g (u : V) := fun _ => rfl
  let φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) :=
    AddMonoidHom.toMultiplicative.symm (β₂.comp (gr.comp e₁.symm.toMonoidHom))
  have hφ : ∀ x, φ x = Multiplicative.toAdd (β₂ (gr (e₁.symm (Multiplicative.ofAdd x)))) :=
    fun _ => rfl
  have hφ0 : φ ≠ 0 := by
    intro h0
    set x : Fin n → ZMod 2 := Pi.single ⟨0, by omega⟩ 1 with hx
    have hx0 : x ≠ 0 := by
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp [hx] at this
    apply hx0
    have h4 := DFunLike.congr_fun h0 x
    rw [hφ, AddMonoidHom.zero_apply] at h4
    have h5 : β₂ (gr (e₁.symm (Multiplicative.ofAdd x))) = 1 := h4
    have h6 := Subgroup.mem_bot.1 ((hβ₂k _).1 h5)
    rw [hgr] at h6
    have h7 : ((e₁.symm (Multiplicative.ofAdd x) : ↥U₁) : V) = 1 :=
      g.injective (h6.trans (map_one g).symm)
    have h8 : e₁.symm (Multiplicative.ofAdd x) = 1 := Subtype.ext h7
    rw [MulEquiv.symm_apply_eq, map_one] at h8
    exact ofAdd_eq_one.1 h8
  have hint : ∀ γ x, φ (mat γ *ᵥ x) = dmat (σ γ) *ᵥ φ x := by
    intro γ x
    set u := e₁.symm (Multiplicative.ofAdd x) with hu
    have hβu : β₁ u = Multiplicative.ofAdd x := by rw [← he₁β, hu, MulEquiv.apply_symm_apply]
    have hu' : ((π γ : ↥L) : MulAut V) (u : V) ∈ U₁ := hLU₁ (π γ) u u.2
    have h3 : e₁.symm (Multiplicative.ofAdd (mat γ *ᵥ x)) = ⟨_, hu'⟩ := by
      rw [MulEquiv.symm_apply_eq, he₁β]
      apply Multiplicative.toAdd.injective
      rw [hβ₁e γ u hu', hβu, toAdd_ofAdd, toAdd_ofAdd]
    have hgu : ((π (σ γ) : ↥L) : MulAut V) ((gr u : ↥U₂) : V) ∈ U₂ :=
      hLU₂ (π (σ γ)) (gr u) (gr u).2
    rw [hφ, hφ, h3, ← hu, ← hβ₂e (σ γ) (gr u) hgu]
    congr 2
    apply Subtype.ext
    show g (((π γ : ↥L) : MulAut V) (u : V)) = ((π (σ γ) : ↥L) : MulAut V) (g (u : V))
    rw [hσ, conjSL_spec, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have hB : ∀ γ : ↥(StatedSL n (ZMod 2)), ∃ γ', dmat (σ γ') = mat γ := by
    intro γ
    obtain ⟨δ, hδ⟩ := exists_dmat_eq (γ : GL (Fin n) (ZMod 2))
    exact ⟨σ.symm δ, by rw [MulEquiv.apply_symm_apply]; exact hδ⟩
  obtain ⟨P, -, hP⟩ := exists_conj_of_intertwine (A := mat) (B := fun γ => dmat (σ γ)) hφ0 hB hint
  exact ⟨P, hP⟩

end Conj

section SumSit

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {n : ℕ}
  {U₁ U₂ : Subgroup V} {π : ↥(StatedSL n (ZMod 2)) →* ↥L}

omit [Finite V] in
theorem exists_symm_of_swap (hn : n = 4 ∨ n = 5) (hdir : IsIntDirect U₁ U₂ ⊤)
    (h1 : RealM L U₁ ⊥ π mat) (h2 : RealM L U₂ ⊥ π dmat) {g : MulAut V}
    (hgL : ∀ x ∈ L, g * x * g⁻¹ ∈ L) (hgL' : ∀ x ∈ L, g⁻¹ * x * g ∈ L) (hg2 : g * g = 1)
    (hg₁ : U₁.map g.toMonoidHom = U₂) (hg₂ : U₂.map g.toMonoidHom = U₁) :
    ∃ P : GL (Fin n) (ZMod 2), (P : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
        (P : Matrix (Fin n) (Fin n) (ZMod 2)) ∧
      ∀ γ : ↥(StatedSL n (ZMod 2)),
        g * ((π γ : ↥L) : MulAut V) = ((π γ : ↥L) : MulAut V) * g →
          (P : Matrix (Fin n) (Fin n) (ZMod 2)) * mat γ =
            dmat γ * (P : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  let _ := hdir
  let _ := hg₂
  have hπ : Function.Bijective π := ⟨h1.injective (Or.inl rfl), h1.1⟩
  obtain ⟨P, hP⟩ := exists_mat_dmat_conjSL hπ (by omega) h1 h2 hgL hgL' hg₁
  refine ⟨P, transpose_eq_of_graph_invol (conjSL_conjSL_of_mul_self hπ hgL hgL' hg2) hP,
    fun γ hγ => ?_⟩
  rw [hP γ, conjSL_eq_self_of_commute hπ hgL hgL' hγ]

end SumSit

end CFSG.Quasithin.B5.Ln
