module

public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7Lift
public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7WittPair

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.StandardType.LieKnownR2.ExcPos.ExcU7
open scoped MatrixGroups


private lemma u7tr_map_map_conj {G H : Type*} [Group G] [Group H] {φ : G →* H} {k : G}
    {S : Subgroup G} : (S.map φ).map (MulAut.conj (φ k)).toMonoidHom =
      (S.map (MulAut.conj k).toMonoidHom).map φ :=
  (Subgroup.map_map_conj S φ k).symm

theorem excU7TransportZ_holds :
    ∀ (p₀ : ℕ) (S : LangSetup Tag.E6 GGL p₀) (a : Fin Tag.E6.rank → GGLˣ)
      (i : KernelComponent (rootCharHom a)) (f p : ℕ), ExcSuClass S a i f p →
      ∀ A A' : Subgroup (ModGL Tag.E6 GGL), ExcSwappedZ S a i f A → ExcSwappedZ S a i f A' →
        ∃ h ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
          A.map (MulAut.conj h).toMonoidHom = A' := by
  intro p₀ S a i f p hS A A' hA hA'
  obtain ⟨σQ, ψ, σf, z, hfrob, hψ, hΨ, hz, hequiv, hrange, hfixmap, hperf, hf1, hker, hconj⟩ :=
    excSuClass_frame S a i f p hS
  obtain ⟨T, hT, hsT, hAeq⟩ :=
    excSwappedZ_lift S a i f hfrob hf1 hψ hΨ hz hequiv hker hconj hA
  obtain ⟨T', hT', hsT', hAeq'⟩ :=
    excSwappedZ_lift S a i f hfrob hf1 hψ hΨ hz hequiv hker hconj hA'
  obtain ⟨k, hk, hkT⟩ := exists_fixed_conj_swapped σQ hf1 hfrob hT hT' hsT hsT'
  refine ⟨((MulAut.conj z).toMonoidHom.comp ψ) k, ?_, ?_⟩
  · have hkfix : k ∈ CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 6) σQ) := by
      rw [CFSG.RankThree.Classical2.mem_fixSubgroup, stdUnitaryEquiv_apply]
      exact hk
    rw [← hfixmap]
    exact Subgroup.mem_map.mpr ⟨k, hkfix, rfl⟩
  · have hC : (((T ⊔ T.map (stdUnitary σQ.toRingHom)) ⊓
        (stdUnitary σQ.toRingHom).eqLocus (MonoidHom.id SL(6, GGL))).map
          (MulAut.conj k).toMonoidHom) =
        ((T' ⊔ T'.map (stdUnitary σQ.toRingHom)) ⊓
          (stdUnitary σQ.toRingHom).eqLocus (MonoidHom.id SL(6, GGL))) := by
      rw [map_conj_fixed_sup (stdUnitary σQ.toRingHom) hk T, hkT]
    rw [hAeq, hAeq',
      u7tr_map_map_conj (φ := (MulAut.conj z).toMonoidHom.comp ψ) (k := k), hC]

private lemma u7tr_excSwappedZ_of_excSwapped {p₀ : ℕ} {S : LangSetup Tag.E6 GGL p₀}
    {a : Fin Tag.E6.rank → GGLˣ} {i : KernelComponent (rootCharHom a)} {f : ℕ}
    {A : Subgroup (ModGL Tag.E6 GGL)} (h : ExcSwapped S a i f A) : ExcSwappedZ S a i f A := by
  obtain ⟨hcard, hΓ, α, w, hα, hw, -, hstab, hcomm, hle⟩ := h
  exact ⟨hcard, hΓ, α, w, hα, hw, hstab, hcomm, hle⟩

theorem excU7Transport_holds : ExcU7Transport := by
  intro p₀ S a i f p hS A A' hA hA'
  exact excU7TransportZ_holds p₀ S a i f p hS A A' (u7tr_excSwappedZ_of_excSwapped hA)
    (u7tr_excSwappedZ_of_excSwapped hA')

end CFSG.StandardType.LieKnownR2.ExcPos
