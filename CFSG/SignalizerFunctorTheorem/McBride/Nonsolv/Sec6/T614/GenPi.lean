module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T614

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem isDirectProduct_inf_centralizer {S : Set (Subgroup Γ)} {X E : Subgroup Γ}
    (hX : IsDirectProduct S X) (hE : ∀ J ∈ S, E ≤ Subgroup.normalizer (J : Set Γ)) :
    IsDirectProduct {Y | ∃ J ∈ S, Y = J ⊓ Subgroup.centralizer (E : Set Γ)}
      (X ⊓ Subgroup.centralizer (E : Set Γ)) := by
  have hT : ∀ J ∈ S, J ⊓ Subgroup.centralizer (E : Set Γ) ≤ J := fun J _ => inf_le_left
  have h := Near.Thm210.isDirectProduct_image hX
    (fun J => J ⊓ Subgroup.centralizer (E : Set Γ)) hT
  have hsup : sSup {K | ∃ J ∈ S, K = J ⊓ Subgroup.centralizer (E : Set Γ)} =
      X ⊓ Subgroup.centralizer (E : Set Γ) := by
    ext x
    rw [Near.Thm210.mem_sSup_image_iff hX hT, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxX, hcoord⟩
      refine ⟨hxX, hX.mem_of_coord_mem hxX fun J hJ => ?_⟩
      exact (Subgroup.mem_inf.mp (hcoord J hJ)).2
    · rintro ⟨hxX, hxC⟩
      refine ⟨hxX, fun J hJ => Subgroup.mem_inf.mpr ⟨(hX.coord hJ ⟨x, hxX⟩).2, ?_⟩⟩
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hJe : J.map (MulAut.conj e).toMonoidHom = J :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hE J hJ he)
      have hperm : ∀ J' ∈ S, J'.map (MulAut.conj e).toMonoidHom ∈ S := fun J' hJ' => by
        have hJ'e : J'.map (MulAut.conj e).toMonoidHom = J' :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp (hE J' hJ' he)
        rw [hJ'e]
        exact hJ'
      have hxe : e * x * e⁻¹ = x := by
        rw [Subgroup.mem_centralizer_iff.mp hxC e he]
        group
      have h1 := hX.coord_conj hperm hJ hxX
      have h2 := hX.coord_val_congr (hperm J hJ) hJ hJe ⟨e * x * e⁻¹, hX.conj_mem hperm hxX⟩
      have hyy : (⟨e * x * e⁻¹, hX.conj_mem hperm hxX⟩ : X) = ⟨x, hxX⟩ := Subtype.ext hxe
      have h3 := h2.symm.trans h1
      rw [hyy] at h3
      calc e * ((hX.coord hJ ⟨x, hxX⟩ : J) : Γ)
          = e * ((hX.coord hJ ⟨x, hxX⟩ : J) : Γ) * e⁻¹ * e := by group
        _ = ((hX.coord hJ ⟨x, hxX⟩ : J) : Γ) * e := by rw [← h3]
  rw [hsup] at h
  exact h

theorem nonempty_mulEquiv_inf_centralizer {S : Set (Subgroup Γ)} {X B J₀ : Subgroup Γ}
    (hX : IsDirectProduct S X)
    (hperm : ∀ b ∈ B, ∀ J ∈ S, J.map (MulAut.conj b).toMonoidHom ∈ S)
    (hJ₀ : J₀ ∈ S) (htrans : ∀ K ∈ S, ∃ b ∈ B, K = J₀.map (MulAut.conj b).toMonoidHom)
    (hker : B ⊓ Subgroup.normalizer (J₀ : Set Γ) ≤ Subgroup.centralizer (J₀ : Set Γ)) :
    Nonempty (↥(X ⊓ Subgroup.centralizer (B : Set Γ)) ≃* ↥J₀) := by
  let φ : ↥(X ⊓ Subgroup.centralizer (B : Set Γ)) →* ↥J₀ :=
    (hX.coord hJ₀).comp (Subgroup.inclusion inf_le_left)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : (y : Γ) ∈ sSup (S \ {J₀}) :=
      (hX.coord_eq_one_iff hJ₀ ⟨y, (Subgroup.mem_inf.mp y.2).1⟩).mp hy
    have h2 := inf_centralizer_inf_sSup_eq_bot_of_transitive hX hperm hJ₀ htrans
    have h3 : (y : Γ) ∈ X ⊓ Subgroup.centralizer (B : Set Γ) ⊓ sSup (S \ {J₀}) := ⟨y.2, h1⟩
    rw [h2, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hsurj : Function.Surjective φ := by
    intro z
    have hz : (z : Γ) ∈ projIn S J₀ (X ⊓ Subgroup.centralizer (B : Set Γ)) := by
      rw [projIn_centralizer_eq hX hperm hJ₀]
      refine Subgroup.mem_inf.mpr ⟨z.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp (hker hb) z z.2).symm
    obtain ⟨y, hyX, hyz⟩ := (hX.mem_projIn_iff hJ₀).mp hz
    exact ⟨⟨y, hyX⟩, Subtype.ext hyz⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

theorem nonempty_pi_mulEquiv {S : Set (Subgroup Γ)} {X B : Subgroup Γ}
    (hX : IsDirectProduct S X)
    (hperm : ∀ b ∈ B, ∀ J ∈ S, J.map (MulAut.conj b).toMonoidHom ∈ S)
    (htrans : ∀ J ∈ S, ∀ K ∈ S, ∃ b ∈ B, K = J.map (MulAut.conj b).toMonoidHom)
    (hker : ∀ J ∈ S, B ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)) :
    Nonempty ((Fin (Nat.card S) → ↥(X ⊓ Subgroup.centralizer (B : Set Γ))) ≃* ↥X) := by
  have hJ : ∀ J : S, Nonempty (↥(X ⊓ Subgroup.centralizer (B : Set Γ)) ≃* ↥(J : Subgroup Γ)) :=
    fun J => nonempty_mulEquiv_inf_centralizer hX hperm J.2 (htrans J.1 J.2) (hker J.1 J.2)
  have : Finite S := Set.toFinite S
  let σ : S ≃ Fin (Nat.card S) := Finite.equivFin S
  let e₁ : (Fin (Nat.card S) → ↥(X ⊓ Subgroup.centralizer (B : Set Γ))) ≃*
      (S → ↥(X ⊓ Subgroup.centralizer (B : Set Γ))) :=
    { Equiv.arrowCongr σ.symm (Equiv.refl _) with map_mul' := fun f g => rfl }
  let e₂ : (S → ↥(X ⊓ Subgroup.centralizer (B : Set Γ))) ≃*
      ((J : S) → ↥(J : Subgroup Γ)) := MulEquiv.piCongrRight fun J => (hJ J).some
  exact ⟨e₁.trans (e₂.trans hX.equiv)⟩

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T614
