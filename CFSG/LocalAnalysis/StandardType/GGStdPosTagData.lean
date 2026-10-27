module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSL
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRestSpinPlus
public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.LieType.Steinberg.Classical.SpinPlus
public import CFSG.LieType.Steinberg.Minuscule.ChevExtras
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LieType.Steinberg.Adjoint.Borel

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

theorem ggStdPos_bruhatData
    {t : StatedLieTag} {n f : ℕ}
    (hrank : 3 ≤ bnRank t n) (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) :
    (ggU t n f).D.divisible = ∅ ∧
      (∃ (nn : Fin (ggU t n f).D.rank → (ggU t n f).K)
        (H : Fin (ggU t n f).D.rank → Subgroup (ggU t n f).K),
        IsCTGroupDatum (coxeterMatrix (ggU t n f).D.isFiniteType).toCoxeterSystem
            (weylAction (ggU t n f).D.isFiniteType) (ggU t n f).D.roots
            (ggU t n f).D.rootGroup nn H ∧
          SteinbergExtras (ggU t n f).D nn H ∧ BruhatExtras (ggU t n f).D H) ∧
      ∃ (x : (Fin (ggU t n f).D.rank → ℤ) → GaloisField 2 f → (ggU t n f).K)
        (C : (Fin (ggU t n f).D.rank → ℤ) → (Fin (ggU t n f).D.rank → ℤ) → ℕ × ℕ → ℤ)
        (O : CommOrder (Steinberg.RootSystem.ofCartan (ggU t n f).D.isFiniteType
          (ggU t n f).D.divisible)),
        ChevalleyExtras (ggU t n f).D (GaloisField 2 f) x C O := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [bnRank] at hrank; omega⟩
    have hm2 : 2 ≤ m := by simp only [bnRank] at hrank; omega
    obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
      (SpecialLinear.rootDatum m (GaloisField 2 f)).isFiniteType
      (Dv := (SpecialLinear.rootDatum m (GaloisField 2 f)).divisible) rfl
    exact ⟨rfl, ⟨_, _, SpecialLinear.isCTGroupDatum m _, SpecialLinear.steinbergExtras m _,
      GGRootSL.bruhatExtras⟩, _, _, O,
      Steinberg.SL.chevalleyExtras hm2 O _ (Steinberg.SL.commutatorFormula O)⟩
  ·
    have hn3 : 3 ≤ n := by simpa only [bnRank] using hrank
    have hU : ggU .POmegaPlus n f =
        ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
          Spin.plusDatum n (GaloisField 2 f) hn3⟩ := by
      simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
    rw [hU]
    obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
      (Spin.plusDatum n (GaloisField 2 f) hn3).isFiniteType
      (Dv := (Spin.plusDatum n (GaloisField 2 f) hn3).divisible) rfl
    exact ⟨rfl, ⟨_, _, Steinberg.SpinPlus.isCTGroupDatum hn3, Spin.plusDatum_steinbergExtras hn3,
      GGRootSpinPlus.bruhatExtras hn3⟩, _, _, O, Steinberg.SpinPlus.chevalleyExtras hn3 O
      Steinberg.SpinPlus.commC (Steinberg.SpinPlus.commutatorFormula hn3 O)⟩
  ·
    obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
      (Steinberg.Minuscule.e6Datum (GaloisField 2 f)).isFiniteType
      (Dv := (Steinberg.Minuscule.e6Datum (GaloisField 2 f)).divisible) rfl
    exact ⟨rfl, ⟨_, _, Steinberg.Minuscule.e6Datum_isCTGroupDatum _,
      Steinberg.Minuscule.e6Datum_steinbergExtras _, Steinberg.Minuscule.e6Datum_bruhatExtras _⟩,
      _, _, O, Steinberg.Minuscule.e6_chevalleyExtras (GaloisField 2 f) O _
        (Steinberg.Minuscule.e6Data_valid.commutatorFormula_commC (GaloisField 2 f)
          Steinberg.Minuscule.posDef_cartan_E6 _
          (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E6) O)⟩
  ·
    obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
      (Steinberg.Minuscule.e7Datum (GaloisField 2 f)).isFiniteType
      (Dv := (Steinberg.Minuscule.e7Datum (GaloisField 2 f)).divisible) rfl
    exact ⟨rfl, ⟨_, _, Steinberg.Minuscule.e7Datum_isCTGroupDatum _,
      Steinberg.Minuscule.e7Datum_steinbergExtras _, Steinberg.Minuscule.e7Datum_bruhatExtras _⟩,
      _, _, O, Steinberg.Minuscule.e7_chevalleyExtras (GaloisField 2 f) O _
        (Steinberg.Minuscule.e7Data_valid.commutatorFormula_commC (GaloisField 2 f)
          Steinberg.Minuscule.posDef_cartan_E7 _
          (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E7) O)⟩
  ·
    obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
      (Steinberg.Adjoint.e8Datum (GaloisField 2 f)).isFiniteType
      (Dv := (Steinberg.Adjoint.e8Datum (GaloisField 2 f)).divisible) rfl
    exact ⟨rfl, ⟨_, _, Steinberg.Adjoint.e8_isCTGroupDatum _,
      Steinberg.Adjoint.e8_steinbergExtras _, Steinberg.Adjoint.e8_bruhatExtras _⟩, _, _, O,
      Steinberg.Adjoint.e8_chevalleyExtras (GaloisField 2 f) O _
        (Steinberg.Adjoint.commutatorFormula_commC Steinberg.Adjoint.e8Data_valid
          Steinberg.Adjoint.noG2_E8 _ (Steinberg.Adjoint.adjDatum_roots _ (GaloisField 2 f)) O)⟩

end CFSG.StandardType

end
