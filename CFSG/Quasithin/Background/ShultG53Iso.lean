module

public import CFSG.Quasithin.Background.ShultG53Defs

public section

namespace CFSG.Quasithin.ShultG53

variable {X : Type} [Group X]

theorem iso_symm' {M N : Md X} (h : M.Iso N) : N.Iso M := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f.symm, fun g n => ?_⟩
  apply f.injective
  rw [AddEquiv.apply_symm_apply, hf, AddEquiv.apply_symm_apply]

theorem iso_trans' {M N P : Md X} (h₁ : M.Iso N) (h₂ : N.Iso P) : M.Iso P := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  exact ⟨f.trans g, fun x m => by
    show g (f (M.ρ x m)) = P.ρ x (g (f m))
    rw [hf, hg]⟩

theorem isCovering_of_iso_right {W V V' : Md X} (hW : W.IsCovering V) (h : V.Iso V') :
    W.IsCovering V' := by
  obtain ⟨hperf, W₀, f, hcentral, hsurj, hker, hequiv⟩ := hW
  obtain ⟨i, hi⟩ := h
  refine ⟨hperf, W₀, i.toAddMonoidHom.comp f, hcentral, ?_, fun w => ?_, fun g w => ?_⟩
  · exact i.surjective.comp hsurj
  · show i (f w) = 0 ↔ w ∈ W₀
    rw [map_eq_zero_iff i i.injective]
    exact hker w
  · show i (f (W.ρ g w)) = V'.ρ g (i (f w))
    rw [hequiv, hi]

theorem isFiveDimCover_of_iso_right' {U V V' : Md X} (hU : U.IsFiveDimCover V) (h : V.Iso V') :
    U.IsFiveDimCover V' := by
  obtain ⟨⟨hcov, huniv⟩, hcard⟩ := hU
  refine ⟨⟨isCovering_of_iso_right hcov h, fun W hW => ?_⟩, hcard⟩
  exact huniv W (isCovering_of_iso_right hW (iso_symm' h))

end CFSG.Quasithin.ShultG53
