module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveOpm
public import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig
public import CFSG.HardMathSupport.Timmesfeld.DFour.Residual44Jordan

public section

namespace CFSG.RankThree.GF2n.Stroth80

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem finrank_map_mkQ_add_finrank_inf (U W : Submodule K E) :
    Module.finrank K ↥(U.map W.mkQ) + Module.finrank K ↥(U ⊓ W) = Module.finrank K U := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (W.mkQ.comp U.subtype)
  have hrange : LinearMap.range (W.mkQ.comp U.subtype) = U.map W.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker (W.mkQ.comp U.subtype) = Submodule.comap U.subtype W := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hkerdim : Module.finrank K ↥(Submodule.comap U.subtype W) =
      Module.finrank K ↥(U ⊓ W) := by
    rw [← Submodule.map_comap_subtype U W, Submodule.finrank_map_subtype_eq]
  rw [hrange, hker, hkerdim] at hrk
  exact hrk

theorem finrank_range_sup_add_finrank_comap (f : E →ₗ[K] E) (T : Submodule K E) :
    Module.finrank K ↥(LinearMap.range f ⊔ T) + Module.finrank K ↥(T.comap f) =
      Module.finrank K T + Module.finrank K E := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (T.mkQ.comp f)
  have hrange : LinearMap.range (T.mkQ.comp f) = (LinearMap.range f).map T.mkQ := by
    rw [LinearMap.range_comp]
  have hker : LinearMap.ker (T.mkQ.comp f) = T.comap f := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [hrange, hker] at hrk
  have h1 := finrank_map_mkQ_add_finrank_inf (LinearMap.range f) T
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f) T
  omega

private theorem orthogonal_sup_eq (B : LinearMap.BilinForm K E) (U W : Submodule K E) :
    B.orthogonal (U ⊔ W) = B.orthogonal U ⊓ B.orthogonal W := by
  ext x
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_inf]
  constructor
  · intro h
    exact ⟨fun u hu => h u (Submodule.mem_sup_left hu), fun w hw => h w (Submodule.mem_sup_right hw)⟩
  · rintro ⟨hU, hW⟩ n hn
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hn
    rw [map_add, LinearMap.add_apply, hU u hu, hW w hw, add_zero]

theorem finrank_range_inf_orthogonal_add (B : LinearMap.BilinForm K E) (hnd : B.Nondegenerate)
    (hrefl : B.IsRefl) (y : E ≃ₗ[K] E)
    (hker : LinearMap.ker (opm y) = B.orthogonal (LinearMap.range (opm y))) (U : Submodule K E) :
    Module.finrank K ↥(LinearMap.range (opm y) ⊓ B.orthogonal U) +
        Module.finrank K ↥(U.map (opm y)) =
      Module.finrank K ↥(LinearMap.range (opm y)) := by
  have h1 : B.orthogonal (LinearMap.range (opm y) ⊓ B.orthogonal U) =
      LinearMap.ker (opm y) ⊔ U := by
    have e : LinearMap.range (opm y) ⊓ B.orthogonal U =
        B.orthogonal (LinearMap.ker (opm y) ⊔ U) := by
      rw [orthogonal_sup_eq, hker, LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl]
    rw [e, LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl]
  have h2 := LinearMap.BilinForm.finrank_orthogonal hnd
    (LinearMap.range (opm y) ⊓ B.orthogonal U)
  rw [h1] at h2
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (opm y)) U
  have h4 := CFSG.HardMathSupport.Timmesfeld.DFour.finrank_map_add_finrank_inf_ker (opm y) U
  have h5 := LinearMap.finrank_range_add_finrank_ker (opm y)
  have h6 : Module.finrank K ↥(LinearMap.ker (opm y) ⊓ U) =
      Module.finrank K ↥(U ⊓ LinearMap.ker (opm y)) := by rw [inf_comm]
  have h7 := Submodule.finrank_le (LinearMap.range (opm y) ⊓ B.orthogonal U)
  have h8 := Submodule.finrank_le (LinearMap.ker (opm y) ⊔ U)
  omega

theorem even_finrank_sub_of_alt (β : LinearMap.BilinForm K E) (U N : Submodule K E) (hNU : N ≤ U)
    (halt : ∀ u ∈ U, β u u = 0) (hsymm : ∀ u ∈ U, ∀ v ∈ U, β u v = β v u)
    (hN : ∀ v ∈ U, v ∈ N ↔ ∀ u ∈ U, β u v = 0) :
    Even (Module.finrank K U - Module.finrank K N) := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (N.comap U.subtype)
  have hdim := Submodule.finrank_add_eq_of_isCompl hC
  have hNdim : Module.finrank K ↥(N.comap U.subtype) = Module.finrank K N := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_eq_right.mpr hNU]
  let βU : LinearMap.BilinForm K U := β.compl₁₂ U.subtype U.subtype
  let βC : LinearMap.BilinForm K C := βU.compl₁₂ C.subtype C.subtype
  have halt' : βC.IsAlt := fun c => halt _ (c : U).2
  have hsepL : ∀ c : C, (∀ d : C, βC c d = 0) → c = 0 := by
    intro c hc
    have hcN : ((c : U) : E) ∈ N := by
      rw [hN _ (c : U).2]
      intro u hu
      obtain ⟨n, hn, d, hd, hsum⟩ : ∃ n ∈ N.comap U.subtype, ∃ d ∈ C, n + d = ⟨u, hu⟩ := by
        have htop : (⟨u, hu⟩ : U) ∈ N.comap U.subtype ⊔ C := by
          rw [hC.sup_eq_top]
          exact Submodule.mem_top
        obtain ⟨n, hn, d, hd, hnd⟩ := Submodule.mem_sup.mp htop
        exact ⟨n, hn, d, hd, hnd⟩
      have hu' : u = (n : E) + ((d : U) : E) := by
        have := congrArg Subtype.val hsum
        simpa using this.symm
      have hn' : (n : E) ∈ N := Submodule.mem_comap.mp hn
      have h1 : β (n : E) ((c : U) : E) = 0 := by
        rw [hsymm _ n.2 _ (c : U).2]
        exact (hN _ n.2).mp hn' _ (c : U).2
      have h2 : β ((d : U) : E) ((c : U) : E) = 0 := by
        rw [hsymm _ (d : U).2 _ (c : U).2]
        have := hc ⟨d, hd⟩
        simpa [βC, βU] using this
      rw [hu', map_add, LinearMap.add_apply, h1, h2, add_zero]
    have hcC : (c : U) ∈ N.comap U.subtype ⊓ C := ⟨hcN, c.2⟩
    rw [hC.inf_eq_bot, Submodule.mem_bot] at hcC
    exact Subtype.ext hcC
  have hsymmC : ∀ c d : C, βC c d = βC d c := fun c d => hsymm _ (c : U).2 _ (d : U).2
  have hnd' : βC.Nondegenerate :=
    ⟨fun c hc => hsepL c hc, fun c hc => hsepL c fun d => (hsymmC c d).trans (hc d)⟩
  have heven := even_finrank_of_alt_nondegenerate βC halt' hnd'
  have hfin : Module.finrank K U - Module.finrank K N = Module.finrank K C := by omega
  rw [hfin]
  exact heven

end CFSG.RankThree.GF2n.Stroth80
