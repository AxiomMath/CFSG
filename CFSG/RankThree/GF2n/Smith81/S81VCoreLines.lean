module

public import CFSG.RankThree.GF2n.Smith81.S81VAmbPts
public import CFSG.RankThree.GF2n.Smith81.S81VGeomFinal
public import CFSG.RankThree.GF2n.Smith81.S81VAmbAdj

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {b : Fin 3 → Fin 6 → F}
  {K : Type} [Field K]

private theorem co2_map_one (W : Submodule F (Fin 6 → F)) : W.map (gLin (1 : SUid σ 6)) = W := by
  have e : gLin (1 : SUid σ 6) = LinearMap.id := LinearMap.ext gLin_one
  rw [e, Submodule.map_id]

theorem hGen_U (hσ : IsUnitaryInvolution σ) (hq : 3 ≤ Nat.card (Fσ σ)) :
    ∃ Pi : Finset (PtU σ), Pi.card ≤ 20 ∧ ∀ Q : PtU σ → Prop, (∀ x ∈ Pi, Q x) →
      (∀ x y z : PtU σ, Q x → Q y → x ≠ y → ColU x y z → Q z) → ∀ x, Q x := by
  classical
  obtain ⟨Pi₀, hcard, -, hgen⟩ := dh5_generated hσ hq
  refine ⟨Pi₀.subtype (IsPt σ), ?_, ?_⟩
  · exact (le_of_eq (Finset.card_subtype _ _)).trans ((Finset.card_filter_le _ _).trans hcard)
  · intro Q hQ hclos
    have key : ∀ W : Submodule F (Fin 6 → F),
        GenPts σ (↑Pi₀ : Set (Submodule F (Fin 6 → F))) W → ∀ hW : IsPt σ W, Q ⟨W, hW⟩ := by
      intro W hG
      induction hG with
      | @base W hmem =>
        intro hW
        exact hQ ⟨W, hW⟩ (Finset.mem_subtype.2 (Finset.mem_coe.1 hmem))
      | @line W₁ W₂ W₃ hG₁ hG₂ hne h₁ h₂ h₃ hd hle ih₁ ih₂ =>
        intro hW₃
        exact hclos ⟨W₁, h₁⟩ ⟨W₂, h₂⟩ ⟨W₃, hW₃⟩ (ih₁ h₁) (ih₂ h₂)
          (fun e => hne (congrArg (fun w : PtU σ => w.1) e)) ⟨hd, hle⟩
    intro x
    exact key x.1 (hgen x.1 x.2) x.2

variable (hσ : IsUnitaryInvolution σ) (hf : Frame σ e3uT0Vec b) (e₀ : K ≃+* Fσ σ) (ψ : K ≃+* K)

include hσ hf

theorem hline_U (x y z : PtU σ) (hcol : ColU x y z) (hxy : x ≠ y) :
    ∃ (g : SUid σ 6) (t : K), ptU g = x ∧ ptU (g * sU hσ.invol hf) = y ∧
      (z = x ∨ z = ptU (g * uK hσ.invol hf (ψ t • n1K σ e₀) * sU hσ.invol hf)) := by
  obtain ⟨g₁, hg₁⟩ := ptU_surjective hσ x
  obtain ⟨g₂, hg₂⟩ := ptU_surjective hσ y
  obtain ⟨h, hh⟩ : ∃ h : SUid σ 6, h = g₁⁻¹ * g₂ := ⟨_, rfl⟩
  have hgh : g₁ * h = g₂ := by rw [hh, mul_inv_cancel_left]
  have hX : x.1 = (W₀ F).map (gLin g₁) := by rw [← hg₁, ptU_val]
  have hY : y.1 = (W₀ F).map (gLin (g₁ * h)) := by rw [← hg₂, ptU_val, hgh]
  have hYY : y.1 = ((W₀ F).map (gLin h)).map (gLin g₁) := by rw [hY, map_map_gLin]
  have hy'pt : IsPt σ ((W₀ F).map (gLin h)) := isPt_map h isPt_W₀
  have hcol' : finrank F ↥(x.1 ⊓ y.1) = 2 ∧ x.1 ⊓ y.1 ≤ z.1 := hcol
  obtain ⟨hfin, hle⟩ := hcol'
  have hfin2 : finrank F ↥(W₀ F ⊓ (W₀ F).map (gLin h)) = 2 := by
    rw [hX, hYY, ← map_gLin_inf, finrank_map_gLin] at hfin
    exact hfin
  obtain ⟨p, hp, hyp⟩ := exists_P_s_of_adjacent hσ hf hy'pt hfin2
  have hp' : p ∈ Pstab σ (W₀ F) := hp
  have hp1 : (W₀ F).map (gLin p) = W₀ F := hp
  have hyp1 : (W₀ F).map (gLin h) = (W₀ F).map (gLin (p * sU hσ.invol hf)) := hyp
  have hgx : ptU (g₁ * p) = x := by rw [ptU_mul_of_mem_Pstab g₁ hp', hg₁]
  have hxg : x.1 = (W₀ F).map (gLin (g₁ * p)) := by rw [← hgx, ptU_val]
  have hgy : ptU (g₁ * p * sU hσ.invol hf) = y := by
    apply Subtype.ext
    rw [ptU_val, mul_assoc g₁ p (sU hσ.invol hf), ← map_map_gLin, ← hyp1, ← hYY]
  have hW0M : (W₀ F).map (gLin (sU hσ.invol hf)) =
      Submodule.span F {b 0, e3uT0Vec (F := F) 1, e3uT0Vec (F := F) 2} :=
    sU_map_Wa hσ.invol hf
  have hline0 : W₀ F ⊓ Submodule.span F {b 0, e3uT0Vec (F := F) 1, e3uT0Vec (F := F) 2} =
      Submodule.span F {e3uT0Vec (F := F) 1, e3uT0Vec (F := F) 2} := by
    have h0 := (isPt_line_point hσ.invol hf (t := (0 : F)) (map_zero σ)).2
    simp only [zero_smul, add_zero] at h0
    exact h0
  have hWM : W₀ F ⊓ (W₀ F).map (gLin (sU hσ.invol hf)) =
      Submodule.span F {e3uT0Vec (F := F) 1, e3uT0Vec (F := F) 2} := by
    rw [hW0M]
    exact hline0
  have hstep0 : W₀ F ⊓ ((W₀ F).map (gLin (sU hσ.invol hf))).map (gLin p) =
      (W₀ F ⊓ (W₀ F).map (gLin (sU hσ.invol hf))).map (gLin p) := by
    rw [map_gLin_inf, hp1]
  have hstep : W₀ F ⊓ (W₀ F).map (gLin (p * sU hσ.invol hf)) =
      (Submodule.span F {e3uT0Vec (F := F) 1, e3uT0Vec (F := F) 2}).map (gLin p) := by
    rw [← map_map_gLin p (sU hσ.invol hf) (W₀ F), hstep0, hWM]
  have hkey : x.1 ⊓ y.1 =
      (Submodule.span F {e3uT0Vec (F := F) 1, e3uT0Vec (F := F) 2}).map (gLin (g₁ * p)) := by
    rw [hX, hYY, ← map_gLin_inf, hyp1, hstep, map_map_gLin]
  have hH0 : Submodule.span F {e3uT0Vec (F := F) 1, e3uT0Vec (F := F) 2} ≤
      z.1.map (gLin (g₁ * p)⁻¹) := by
    rw [hkey] at hle
    have h1 := Submodule.map_mono (f := gLin (g₁ * p)⁻¹) hle
    rw [map_map_gLin, inv_mul_cancel, co2_map_one] at h1
    exact h1
  have hzpt : IsPt σ (z.1.map (gLin (g₁ * p)⁻¹)) := isPt_map (g₁ * p)⁻¹ z.2
  rcases line_through_H₀ hσ.invol hf hzpt hH0 with hWz | ⟨τ, hτ, hτz⟩
  ·
    have hWz' : z.1.map (gLin (g₁ * p)⁻¹) = W₀ F := hWz
    have e1 := congrArg (Submodule.map (gLin (g₁ * p))) hWz'
    rw [map_map_gLin, mul_inv_cancel, co2_map_one] at e1
    refine ⟨g₁ * p, 0, hgx, hgy, Or.inl ?_⟩
    apply Subtype.ext
    rw [hxg]
    exact e1
  ·
    have hτ' : σ τ = τ := hτ
    obtain ⟨t, ht⟩ : ∃ t : K, ψ t = e₀.symm (⟨τ, hτ'⟩ : Fσ σ) :=
      ⟨ψ.symm (e₀.symm (⟨τ, hτ'⟩ : Fσ σ)), ψ.apply_symm_apply _⟩
    have h2 : ((e₀ (ψ t) : Fσ σ) : F) = τ := by
      rw [ht, RingEquiv.apply_symm_apply]
    have hu := uK_map_W₁ e₀ hσ.invol hf (ψ t)
    rw [h2] at hu
    have e2 : z.1.map (gLin (g₁ * p)⁻¹) =
        (W₀ F).map (gLin (uK hσ.invol hf (ψ t • n1K σ e₀) * sU hσ.invol hf)) := by
      rw [hτz, ← hu, ← hW0M, map_map_gLin]
    have e3 : z.1 = (W₀ F).map
        (gLin (g₁ * p * (uK hσ.invol hf (ψ t • n1K σ e₀) * sU hσ.invol hf))) := by
      rw [← map_map_gLin, ← e2, map_map_gLin, mul_inv_cancel, co2_map_one]
    refine ⟨g₁ * p, t, hgx, hgy, Or.inr ?_⟩
    apply Subtype.ext
    rw [ptU_val, mul_assoc (g₁ * p)]
    exact e3

end CFSG.RankThree.GF2n.Smith81.S81V
