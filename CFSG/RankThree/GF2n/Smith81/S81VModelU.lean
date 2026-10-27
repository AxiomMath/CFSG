module

public import CFSG.RankThree.GF2n.Smith81.S81VBlockU

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F} {K : Type} [Field K]

@[expose] def HermK (σ : F ≃+* F) (_ : K ≃+* Fσ σ) : Type := ↥(Herm σ)

instance (σ : F ≃+* F) (e₀ : K ≃+* Fσ σ) : AddCommGroup (HermK σ e₀) :=
  inferInstanceAs (AddCommGroup ↥(Herm σ))

noncomputable instance (σ : F ≃+* F) (e₀ : K ≃+* Fσ σ) : Module K (HermK σ e₀) :=
  Module.compHom ↥(Herm σ) (e₀ : K →+* Fσ σ)

@[expose] def HermK.mat {e₀ : K ≃+* Fσ σ} (H : HermK σ e₀) : Matrix (Fin 3) (Fin 3) F :=
  (show ↥(Herm σ) from H).1

@[expose] def HermK.mk (σ : F ≃+* F) (e₀ : K ≃+* Fσ σ) (M : Matrix (Fin 3) (Fin 3) F)
    (h : cT σ M = M) : HermK σ e₀ :=
  show ↥(Herm σ) from ⟨M, h⟩

variable {e₀ : K ≃+* Fσ σ}

theorem HermK.cT_mat (H : HermK σ e₀) : cT σ H.mat = H.mat := (show ↥(Herm σ) from H).2

@[simp] theorem HermK.mat_mk (M : Matrix (Fin 3) (Fin 3) F) (h : cT σ M = M) :
    (HermK.mk σ e₀ M h).mat = M := rfl

theorem HermK.ext {H H' : HermK σ e₀} (h : H.mat = H'.mat) : H = H' :=
  Subtype.ext h

theorem HermK.mat_add (H H' : HermK σ e₀) : (H + H').mat = H.mat + H'.mat := rfl

theorem HermK.mat_zero : (0 : HermK σ e₀).mat = 0 := rfl

theorem HermK.mat_smul (c : K) (H : HermK σ e₀) : (c • H).mat = (e₀ c : F) • H.mat := rfl

instance [Finite F] : Finite (HermK σ e₀) :=
  Finite.of_injective (fun H : HermK σ e₀ => (H.mat : Fin 3 → Fin 3 → F))
    (fun _ _ h => HermK.ext h)

instance [Finite F] : Module.Finite K (HermK σ e₀) := Module.Finite.of_finite

theorem HermK.diag_fixed (H : HermK σ e₀) (i : Fin 3) : σ (H.mat i i) = H.mat i i := by
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i i) H.cT_mat
  simpa only [cT_apply] using h

@[expose] noncomputable def tauK (σ : F ≃+* F) (e₀ : K ≃+* Fσ σ) : HermK σ e₀ →ₗ[K] K where
  toFun H := e₀.symm ⟨H.mat 0 0, H.diag_fixed 0⟩
  map_add' H H' := by
    beta_reduce
    rw [← map_add e₀.symm]
    congr 1
  map_smul' c H := by
    beta_reduce
    apply e₀.injective
    rw [e₀.apply_symm_apply, RingHom.id_apply, smul_eq_mul, map_mul, e₀.apply_symm_apply]
    apply Subtype.ext
    simp [HermK.mat_smul]

theorem tauK_apply (H : HermK σ e₀) : (e₀ (tauK σ e₀ H) : F) = H.mat 0 0 := by
  have h : tauK σ e₀ H = e₀.symm ⟨H.mat 0 0, H.diag_fixed 0⟩ := rfl
  rw [h, RingEquiv.apply_symm_apply]

@[expose] noncomputable def n1K (σ : F ≃+* F) (e₀ : K ≃+* Fσ σ) : HermK σ e₀ :=
  HermK.mk σ e₀ (Matrix.single 0 0 1) <| by
    ext i j
    by_cases h : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h
      simp [cT_apply, Matrix.single_apply]
    · have h1 : ¬ ((0 : Fin 3) = i ∧ (0 : Fin 3) = j) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
      have h2 : ¬ ((0 : Fin 3) = j ∧ (0 : Fin 3) = i) := fun h' => h ⟨h'.2.symm, h'.1.symm⟩
      simp only [cT_apply, Matrix.single_apply, if_neg h1, if_neg h2, map_zero]

theorem n1K_mat : (n1K σ e₀).mat = Matrix.single 0 0 1 := rfl

theorem tauK_n1K : tauK σ e₀ (n1K σ e₀) = 1 := by
  apply e₀.injective
  apply Subtype.ext
  rw [tauK_apply]
  simp [n1K_mat]

variable [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b)

include hσ hf

noncomputable def uK (H : HermK σ e₀) : SUid σ 6 := uU hσ hf H.mat H.cT_mat

theorem uK_add (H H' : HermK σ e₀) : uK hσ hf (H + H') = uK hσ hf H * uK hσ hf H' :=
  uU_add hσ hf H.mat H'.mat H.cT_mat H'.cT_mat (H + H').cT_mat

theorem gm_uK (H : HermK σ e₀) : gm hσ hf (uK hσ hf H) = Matrix.fromBlocks 1 H.mat 0 1 :=
  gm_uU hσ hf _ _

theorem uK_mem_PtStab (H : HermK σ e₀) : uK hσ hf H ∈ PtStab σ (Wa a) :=
  uU_mem_PtStab hσ hf _ _

theorem exists_uK_of_mem_PtStab {g : SUid σ 6} (hg : g ∈ PtStab σ (Wa a)) :
    ∃ H : HermK σ e₀, g = uK hσ hf H := by
  obtain ⟨M, hM, rfl⟩ := (mem_PtStab_iff hσ hf g).1 hg
  exact ⟨HermK.mk σ e₀ M hM, rfl⟩

end CFSG.RankThree.GF2n.Smith81.S81V
