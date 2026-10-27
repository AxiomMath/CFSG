module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RLargeEig
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RE8Frame
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UData

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar

section LargeFrame

theorem uframe_dataLarge
    (hR : LangFamilyCompFieldSL)
    {X : Type} [Group X] {G₀ B D J : Subgroup X} [Finite B] {f p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) .E8 (2 ^ f))
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) (hBel : IsElemAbelian p B)
    (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2) (hJG : J ≤ G₀)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hcent : B ⊓ Subgroup.centralizer (J : Set X) = D)
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f')
    (htor : UToralAt .E8 p (Nat.card B)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (S₁ : LangSetup .E8 (AlgebraicClosure K) 5) (fr₁ : GGTCUFrame S₁.Γ G₀ B),
      S₁.D.q = 2 ^ f ∧ fr₁.BLang ≤ S₁.D.torus ∧
      (∃ w : WeylGroup .E8, ∀ γ, IsRoot .E8 γ → S₁.ρ γ = w • γ) ∧
      ∃ (a : ↥(fr₁.DLang D) → Fin Tag.E8.rank → (AlgebraicClosure K)ˣ)
        (i : KernelComponent (famCharHom a)),
        (∀ u : ↥(fr₁.DLang D),
          (u : ModGL Tag.E8 (AlgebraicClosure K)) = rootDiagUnit Tag.E8 (a u)) ∧
        (∀ u j, a u j ^ p = 1) ∧
        fr₁.JLang J ≤ rootSpan Tag.E8 (AlgebraicClosure K) (famOrbit S₁.ρ a i) ∧
        2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) ∧
        CFSG.StandardType.GGCompFieldAtSL
          (2 ^ (f * componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i)))
          (fr₁.JLang J) ∧
        Nat.card B ≤ p ^ (2 + Module.finrank ℤ (Submodule.span ℤ
          (componentRoots (famCharHom a) i))) := by
  classical
  obtain ⟨K, instF, instFin, instChar, S, hq, hFr, ⟨fr⟩⟩ :=
    exists_uframe_untw (Or.inr (Or.inr (Or.inr rfl))) hp hp2 hmod hBN hin hfaith hBel hDB hDcard
  obtain ⟨S₁, hq₁, hΦ₁, hw, fr₁, hBT⟩ :=
    exists_torus_uframe_untw (Or.inr (Or.inr (Or.inr rfl))) hp hp2 S fr hBel htor
  have hqq : S₁.D.q = 2 ^ f := hq₁.trans hq
  obtain ⟨Fr, hFr1, hFr2⟩ := hFr
  obtain ⟨w, hn⟩ := hw
  have hρ : ∀ γ, IsRoot .E8 γ → S₁.ρ γ = w • γ := fun γ hγ =>
    S₁.rho_eq_smul_of_frob (Fr := Fr) (fun c => by rw [hq₁]; exact hFr1 c)
      (by rw [hΦ₁]; exact hFr2) hn hγ
  have hDT : fr₁.DLang D ≤ S₁.D.torus := fr₁.DLang_le_BLang.trans hBT
  obtain ⟨a, i, ha, hap, hspan, h2, hfield⟩ :=
    uframe_data_of_frame hR (Or.inr (Or.inr rfl)) hp hp2 fr₁ hqq hBel hDB hJG hJ hF hDT
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite fr₁.BLang := Finite.of_equiv _ (MonoidHom.ofInjective fr₁.toLang_injective).toEquiv
  have hBel₁ : IsElemAbelian p fr₁.BLang := fr₁.isElemAbelian_BLang hBel
  have hD₁B : fr₁.DLang D ≤ fr₁.BLang := fr₁.DLang_le_BLang
  have hC := fr₁.le_DLang_of_commute hJG hJ.2.2.1 hcent
  have hcard := card_le_of_famChar S₁ fr₁.BLang (fr₁.DLang D) (fr₁.JLang J) hBT hBel₁.2 hD₁B a i
    hspan hC
  refine ⟨K, instF, instFin, instChar, S₁, fr₁, hqq, hBT, ⟨w, hρ⟩, a, i, ha, hap, hspan, h2,
    hfield, ?_⟩
  calc Nat.card B = Nat.card fr₁.BLang := fr₁.card_BLang.symm
    _ ≤ Nat.card (fr₁.DLang D) *
        p ^ Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) := hcard
    _ = p ^ (2 + Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i))) := by
      rw [fr₁.card_DLang hDB, hDcard, pow_add]

end LargeFrame

end CFSG.StandardType.TableCRes

end
