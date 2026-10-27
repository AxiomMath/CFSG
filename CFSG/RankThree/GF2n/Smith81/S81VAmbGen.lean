module

public import CFSG.RankThree.GF2n.Smith81.S81VAmbAdj
public import CFSG.RankThree.GF2n.Smith81.S81VAmbConn

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F}

private theorem gu3_map_one (W : Submodule F (Fin 6 → F)) : W.map (gLin (1 : SUid σ 6)) = W := by
  have e : gLin (1 : SUid σ 6) = LinearMap.id := LinearMap.ext (gLin_one)
  rw [e, Submodule.map_id]

theorem Adj_map (g : SUid σ 6) {x y : Submodule F (Fin 6 → F)} (h : Adj σ x y) :
    Adj σ (x.map (gLin g)) (y.map (gLin g)) := by
  obtain ⟨hx, hy, hxy⟩ : IsPt σ x ∧ IsPt σ y ∧ finrank F ↥(x ⊓ y) = 2 := h
  have hinf : finrank F ↥(x.map (gLin g) ⊓ y.map (gLin g)) = 2 := by
    rw [← map_gLin_inf, finrank_map_gLin]
    exact hxy
  exact (⟨isPt_map g hx, isPt_map g hy, hinf⟩ :
    IsPt σ (x.map (gLin g)) ∧ IsPt σ (y.map (gLin g)) ∧
      finrank F ↥(x.map (gLin g) ⊓ y.map (gLin g)) = 2)

variable (hσ : IsUnitaryInvolution σ) (hf : Frame σ a b)

include hσ hf

theorem isPt_Wa : IsPt σ (Wa a) := by
  have hT : IsTotIso σ (Wa a) := by
    intro x hx y hy
    have hyA : ∀ i, herm σ (a i) y = 0 := (mem_Wa_iff hσ.invol hf y).1 hy
    have hx' : x ∈ Submodule.span F (Set.range a) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      exact hyA j
    | zero => simp
    | add u v _ _ hu hv => rw [herm_add_left, hu, hv, add_zero]
    | smul c u _ hu => rw [herm_smul_left, hu, mul_zero]
  have hli0 : LinearIndependent F (fam a b ∘ Sum.inl) :=
    (fam_li hσ.invol hf).comp Sum.inl Sum.inl_injective
  have hli : LinearIndependent F a := hli0
  have hfin : finrank F ↥(Wa a) = 3 := by
    show finrank F ↥(Submodule.span F (Set.range a)) = 3
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  exact (⟨hT, hfin⟩ : IsTotIso σ (Wa a) ∧ finrank F ↥(Wa a) = 3)

theorem closure_eq_top (H : Subgroup (SUid σ 6)) (hP : Pstab σ (Wa a) ≤ H) (hs : sU hσ.invol hf ∈ H) :
    H = ⊤ := by
  obtain ⟨O, hO⟩ : ∃ O : Set (Submodule F (Fin 6 → F)),
      ∀ x : Submodule F (Fin 6 → F), x ∈ O ↔ ∃ h : SUid σ 6, h ∈ H ∧ x = (Wa a).map (gLin h) :=
    ⟨{x | ∃ h : SUid σ 6, h ∈ H ∧ x = (Wa a).map (gLin h)}, fun x => Iff.rfl⟩
  have hO_Adj : ∀ x y : Submodule F (Fin 6 → F), Adj σ x y → x ∈ O → y ∈ O := by
    intro x y hxy hx
    obtain ⟨h, hh, rfl⟩ := (hO x).1 hx
    have hxy' := Adj_map h⁻¹ hxy
    rw [map_map_gLin, inv_mul_cancel, gu3_map_one] at hxy'
    obtain ⟨-, hB, hC⟩ := hxy'
    obtain ⟨p, hp, hyp⟩ := exists_P_s_of_adjacent hσ hf hB hC
    refine (hO y).2 ⟨h * (p * sU hσ.invol hf), H.mul_mem hh (H.mul_mem (hP hp) hs), ?_⟩
    calc y = (y.map (gLin h⁻¹)).map (gLin h) := by rw [map_map_gLin, mul_inv_cancel, gu3_map_one]
      _ = ((Wa a).map (gLin (p * sU hσ.invol hf))).map (gLin h) := by rw [hyp]
      _ = (Wa a).map (gLin (h * (p * sU hσ.invol hf))) := map_map_gLin _ _ _
  have hWa : Wa a ∈ O := (hO _).2 ⟨1, H.one_mem, (gu3_map_one _).symm⟩
  have hchain : ∀ z : Submodule F (Fin 6 → F), Relation.ReflTransGen (Adj σ) (Wa a) z → z ∈ O := by
    intro z hz
    induction hz with
    | refl => exact hWa
    | tail _ hbc ih => exact hO_Adj _ _ hbc ih
  have hO_pt : ∀ y : Submodule F (Fin 6 → F), IsPt σ y → y ∈ O := fun y hy =>
    hchain y (adj_connected hσ (isPt_Wa hσ hf) hy)
  rw [Subgroup.eq_top_iff']
  intro g
  obtain ⟨h, hh, hgh⟩ := (hO _).1 (hO_pt _ (isPt_map g (isPt_Wa hσ hf)))
  have hmem : h⁻¹ * g ∈ Pstab σ (Wa a) := by
    show (Wa a).map (gLin (h⁻¹ * g)) = Wa a
    rw [← map_map_gLin h⁻¹ g (Wa a), hgh, map_map_gLin h⁻¹ h (Wa a), inv_mul_cancel, gu3_map_one]
  have h2 : h * (h⁻¹ * g) ∈ H := H.mul_mem hh (hP hmem)
  rwa [mul_inv_cancel_left] at h2

end CFSG.RankThree.GF2n.Smith81.S81V
