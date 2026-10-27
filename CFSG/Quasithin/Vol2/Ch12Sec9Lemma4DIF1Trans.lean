module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF1Stab

public section

namespace CFSG.Quasithin.H13.C1294

open Module

section Sub

variable {I : Type} [AddCommGroup I] [Module (ZMod 2) I]

abbrev SubsOf (W : Submodule (ZMod 2) I) (j : ℕ) : Type :=
  {U : Submodule (ZMod 2) I // U ≤ W ∧ finrank (ZMod 2) U = j}

noncomputable def subsOfEquiv (W : Submodule (ZMod 2) I) (j : ℕ) :
    SubsOf W j ≃ CFSG.Monster.B.TwoA.SubspaceDim (ZMod 2) W j where
  toFun U := ⟨Submodule.comap W.subtype U.1, by
    rw [(Submodule.comapSubtypeEquivOfLe U.2.1).finrank_eq, U.2.2]⟩
  invFun V := ⟨Submodule.map W.subtype V.1, by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, _, rfl⟩
      exact x.2
    · exact ((Submodule.equivMapOfInjective W.subtype (Submodule.injective_subtype W)
        V.1).finrank_eq).symm.trans V.2⟩
  left_inv U := Subtype.ext (by
    show Submodule.map W.subtype (Submodule.comap W.subtype U.1) = U.1
    rw [Submodule.map_comap_subtype, inf_eq_right.2 U.2.1])
  right_inv V := Subtype.ext (by
    show Submodule.comap W.subtype (Submodule.map W.subtype V.1) = V.1
    exact Submodule.comap_map_eq_of_injective (Submodule.injective_subtype W) V.1)

theorem card_subsOf [FiniteDimensional (ZMod 2) I] (W : Submodule (ZMod 2) I) (j : ℕ)
    (hj : j ≤ finrank (ZMod 2) W) :
    Nat.card (SubsOf W j) = CFSG.Monster.B.TwoA.qBinom 2 (finrank (ZMod 2) W) j := by
  rw [Nat.card_congr (subsOfEquiv W j)]
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  have h := CFSG.Monster.B.TwoA.card_subspaces (K := ZMod 2) (V := W) (j := j) hj
  rw [h]
  rfl

end Sub

section Complement

variable {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [FiniteDimensional (ZMod 2) I]

theorem sup_inf_complement {W C U : Submodule (ZMod 2) I} (hC : IsCompl W C) (hWU : W ≤ U) :
    W ⊔ (U ⊓ C) = U := by
  have h := sup_inf_assoc_of_le (x := W) (y := C) hWU
  rw [hC.sup_eq_top, top_inf_eq, inf_comm C U] at h
  exact h.symm

theorem finrank_super_eq {W C U : Submodule (ZMod 2) I} (hC : IsCompl W C) (hWU : W ≤ U) :
    finrank (ZMod 2) U = finrank (ZMod 2) W + finrank (ZMod 2) ↥(U ⊓ C) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (U ⊓ C)
  have hdisj : W ⊓ (U ⊓ C) = ⊥ := by
    apply eq_bot_iff.2
    calc W ⊓ (U ⊓ C) ≤ W ⊓ C := inf_le_inf_left W inf_le_right
      _ = ⊥ := hC.inf_eq_bot
  rw [sup_inf_complement hC hWU, hdisj, finrank_bot] at h
  omega

noncomputable def superEquiv (W C : Submodule (ZMod 2) I) (hC : IsCompl W C) (j : ℕ)
    (hj : finrank (ZMod 2) W ≤ j) :
    {U : Submodule (ZMod 2) I // W ≤ U ∧ finrank (ZMod 2) U = j} ≃
      CFSG.Monster.B.TwoA.SubspaceDim (ZMod 2) C (j - finrank (ZMod 2) W) where
  toFun U := ⟨Submodule.comap C.subtype (U.1 ⊓ C), by
    have h := finrank_super_eq hC U.2.1
    rw [U.2.2] at h
    have h2 : finrank (ZMod 2) ↥(U.1 ⊓ C) = j - finrank (ZMod 2) W := by omega
    rw [(Submodule.comapSubtypeEquivOfLe (inf_le_right : U.1 ⊓ C ≤ C)).finrank_eq, h2]⟩
  invFun V := ⟨W ⊔ Submodule.map C.subtype V.1, by
    have hD : Submodule.map C.subtype V.1 ≤ C := by
      rintro _ ⟨x, _, rfl⟩
      exact x.2
    have hdisj : W ⊓ Submodule.map C.subtype V.1 = ⊥ := by
      apply eq_bot_iff.2
      calc W ⊓ Submodule.map C.subtype V.1 ≤ W ⊓ C := inf_le_inf_left W hD
        _ = ⊥ := hC.inf_eq_bot
    have h := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.map C.subtype V.1)
    rw [hdisj, finrank_bot, add_zero] at h
    have hmapV : finrank (ZMod 2) ↥(Submodule.map C.subtype V.1) = j - finrank (ZMod 2) W := by
      rw [← (Submodule.equivMapOfInjective C.subtype (Submodule.injective_subtype C) V.1).finrank_eq]
      exact V.2
    refine ⟨le_sup_left, ?_⟩
    rw [h, hmapV]
    omega⟩
  left_inv U := Subtype.ext (by
    show W ⊔ Submodule.map C.subtype (Submodule.comap C.subtype (U.1 ⊓ C)) = U.1
    rw [Submodule.map_comap_subtype, inf_eq_right.2 (inf_le_right : U.1 ⊓ C ≤ C)]
    exact sup_inf_complement hC U.2.1)
  right_inv V := Subtype.ext (by
    show Submodule.comap C.subtype ((W ⊔ Submodule.map C.subtype V.1) ⊓ C) = V.1
    have hD : Submodule.map C.subtype V.1 ≤ C := by
      rintro _ ⟨x, _, rfl⟩
      exact x.2
    have h1 : (W ⊔ Submodule.map C.subtype V.1) ⊓ C = Submodule.map C.subtype V.1 := by
      rw [sup_comm W, sup_inf_assoc_of_le W hD, hC.inf_eq_bot, sup_bot_eq]
    rw [h1]
    exact Submodule.comap_map_eq_of_injective (Submodule.injective_subtype C) V.1)


theorem card_superOf (W C : Submodule (ZMod 2) I) (hC : IsCompl W C) (j : ℕ)
    (hj : finrank (ZMod 2) W ≤ j) (hjI : j ≤ finrank (ZMod 2) I) :
    Nat.card {U : Submodule (ZMod 2) I // W ≤ U ∧ finrank (ZMod 2) U = j} =
      CFSG.Monster.B.TwoA.qBinom 2 (finrank (ZMod 2) C) (j - finrank (ZMod 2) W) := by
  rw [Nat.card_congr (superEquiv W C hC j hj)]
  haveI : Finite C := Module.finite_of_finite (ZMod 2)
  have hC' : finrank (ZMod 2) W + finrank (ZMod 2) C = finrank (ZMod 2) I :=
    Submodule.finrank_add_eq_of_isCompl hC
  have hle : j - finrank (ZMod 2) W ≤ finrank (ZMod 2) C := by
    omega
  have h := CFSG.Monster.B.TwoA.card_subspaces (K := ZMod 2) (V := C)
    (j := j - finrank (ZMod 2) W) hle
  rw [h]
  rfl

section Transitive

theorem exists_stabS_map_sub (W : Submodule (ZMod 2) I) {U U' : Submodule (ZMod 2) I}
    (hU : U ≤ W) (hU' : U' ≤ W) (h : finrank (ZMod 2) U = finrank (ZMod 2) U') :
    ∃ g ∈ stabS W, Submodule.map (g : I →ₗ[ZMod 2] I) U = U' := by
  have hcU : finrank (ZMod 2) ↥(Submodule.comap W.subtype U) =
      finrank (ZMod 2) ↥(Submodule.comap W.subtype U') := by
    rw [(Submodule.comapSubtypeEquivOfLe hU).finrank_eq,
      (Submodule.comapSubtypeEquivOfLe hU').finrank_eq, h]
  obtain ⟨a, ha⟩ := CFSG.Monster.B.TwoA.exists_linearEquiv_map_eq hcU
  obtain ⟨g, hg⟩ := restrictHom_surjective W a
  have hgW : ∀ x : W, (g.1 : I ≃ₗ[ZMod 2] I) (x : I) = ((a x : W) : I) := fun x => by
    have := congrArg (fun f : W ≃ₗ[ZMod 2] W => ((f x : W) : I)) hg
    exact this
  refine ⟨g.1, g.2, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x, hx, rfl⟩
    have hxW : x ∈ W := hU hx
    have hmem : (⟨x, hxW⟩ : W) ∈ Submodule.comap W.subtype U := hx
    have h2 : a ⟨x, hxW⟩ ∈ Submodule.comap W.subtype U' := by
      rw [← ha]
      exact Submodule.mem_map_of_mem hmem
    show (g.1 : I ≃ₗ[ZMod 2] I) x ∈ U'
    rw [hgW ⟨x, hxW⟩]
    exact h2
  · rw [LinearEquiv.finrank_map_eq]
    exact h

theorem exists_stabS_fix_map_super {W C : Submodule (ZMod 2) I} (hC : IsCompl W C)
    {U U' : Submodule (ZMod 2) I} (hU : W ≤ U) (hU' : W ≤ U')
    (h : finrank (ZMod 2) U = finrank (ZMod 2) U') :
    ∃ g : I ≃ₗ[ZMod 2] I, g ∈ stabS W ∧ (∀ w ∈ W, g w = w) ∧
      Submodule.map (g : I →ₗ[ZMod 2] I) U = U' := by
  have hD : finrank (ZMod 2) ↥(U ⊓ C) = finrank (ZMod 2) ↥(U' ⊓ C) := by
    have h1 := finrank_super_eq hC hU
    have h2 := finrank_super_eq hC hU'
    omega
  have hDC : finrank (ZMod 2) ↥(Submodule.comap C.subtype (U ⊓ C)) =
      finrank (ZMod 2) ↥(Submodule.comap C.subtype (U' ⊓ C)) := by
    rw [(Submodule.comapSubtypeEquivOfLe (inf_le_right : U ⊓ C ≤ C)).finrank_eq,
      (Submodule.comapSubtypeEquivOfLe (inf_le_right : U' ⊓ C ≤ C)).finrank_eq, hD]
  obtain ⟨β, hβ⟩ := CFSG.Monster.B.TwoA.exists_linearEquiv_map_eq hDC
  obtain ⟨g, hgW, hgC⟩ := exists_glue hC (LinearEquiv.refl (ZMod 2) W) β
  have hgstab : (g : I ≃ₗ[ZMod 2] I) ∈ stabS W :=
    mem_stabS_of_restrict (LinearEquiv.refl (ZMod 2) W) hgW
  refine ⟨g, hgstab, fun w hw => hgW ⟨w, hw⟩, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨u, hu, rfl⟩
    rw [← sup_inf_complement hC hU] at hu
    obtain ⟨w, hw, d, hd, rfl⟩ := Submodule.mem_sup.1 hu
    have hdC : d ∈ C := (inf_le_right : U ⊓ C ≤ C) hd
    have hdmem : (⟨d, hdC⟩ : C) ∈ Submodule.comap C.subtype (U ⊓ C) := hd
    have hb : β ⟨d, hdC⟩ ∈ Submodule.comap C.subtype (U' ⊓ C) := by
      rw [← hβ]
      exact Submodule.mem_map_of_mem hdmem
    have hbU : ((β ⟨d, hdC⟩ : C) : I) ∈ U' := (inf_le_left : U' ⊓ C ≤ U') hb
    show (g : I ≃ₗ[ZMod 2] I) (w + d) ∈ U'
    rw [map_add, hgW ⟨w, hw⟩, hgC ⟨d, hdC⟩]
    exact U'.add_mem (hU' hw) hbU
  · rw [LinearEquiv.finrank_map_eq]
    exact h

end Transitive

end Complement

end CFSG.Quasithin.H13.C1294
