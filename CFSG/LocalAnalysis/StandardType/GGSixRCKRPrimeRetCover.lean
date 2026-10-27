module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetPin
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcOrbit
import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.ModelMinuscule

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.Timmesfeld CFSG.LieType.Steinberg.Minuscule
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped MatrixGroups commutatorElement

theorem rckRet_cover
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    {a : Fin τ.rank → GGLˣ} {i : KernelComponent (rootCharHom a)}
    {β : Fin 6 → Fin τ.rank → ℤ} (hβroot : ∀ b, IsRoot τ (β b))
    (hΨβ : componentRoots (rootCharHom a) i = rootsOfFam β Set.univ)
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    {g : ℕ} (hg : 0 < g) {σ : GGL ≃+* GGL} (hfin : Finite ↥(fixSubfield σ))
    (hKcard : Nat.card ↥(fixSubfield σ) = 2 ^ g)
    (f : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) →* ModGL τ GGL)
    (hf1 : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ f.range)
    (hf2 : f.ker ≤ Subgroup.center ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i))
    (hf3 : ⁅componentRootSpan (fixSubfield σ) (rootCharHom a) i,
        componentRootSpan (fixSubfield σ) (rootCharHom a) i⁆ =
        componentRootSpan (fixSubfield σ) (rootCharHom a) i →
      f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i)
    {z : ModGL τ GGL}
    (hfz : ∀ x : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i),
      f x = z * baseChangeGL (fixSubfield σ).subtype (x : ModGL τ ↥(fixSubfield σ)) * z⁻¹) :
    ∃ (e : GaloisField 2 g →+* GGL)
      (φ : (ggU .E6 0 g).K →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)),
      (∀ c, σ (e c) = e c) ∧ (∀ y, σ y = y → ∃ c, e c = y) ∧
      Function.Surjective φ ∧ φ.ker ≤ Subgroup.center (ggU .E6 0 g).K ∧
      (∀ γ' : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ' → ∀ c : GaloisField 2 g,
        ((φ (e6Data_valid.xm (GaloisField 2 g) γ' c) :
          ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) : ModGL τ GGL) =
          z * pinnedX τ GGL (∑ j : Fin 6, γ' j • β j) (e c) * z⁻¹) ∧
      Finite (ggU .E6 0 g).K ∧ Group.IsPerfect (ggU .E6 0 g).K ∧
      CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit (ggU .E6 0 g).K ∧
      Odd (Nat.card (Subgroup.center (ggU .E6 0 g).K)) ∧
      StandardReturnAt (ggU .E6 0 g) g ∧ RCKADEModel (ggU .E6 0 g) g ∧
      f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(fixSubfield σ) := hfin
  have hadm : StatedLieAdmissible .E6 0 2 g := ⟨Nat.prime_two, hg, rfl⟩
  have hrk : 2 ≤ (ggU .E6 0 g).D.rank := by
    show 2 ≤ (e6Datum (GaloisField 2 g)).rank
    show 2 ≤ 6
    norm_num
  haveI hfinM : Finite (ggU .E6 0 g).K :=
    ggU_finite_exc (Or.inr (Or.inl rfl)) ⟨hadm, hrk⟩
  obtain ⟨hcommM, -⟩ := ggU_perfect_lieModel hadm hrk
  have hsplit := CFSG.StandardType.LieOddCover.oddCentralSplit_ggU_pos (t := .E6) (n := 0)
    (f := g) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) hadm
  haveI : Fintype ↥(fixSubfield σ) := Fintype.ofFinite _
  haveI : Fintype (GaloisField 2 g) := Fintype.ofFinite _
  have hcardEq : Fintype.card (GaloisField 2 g) = Fintype.card ↥(fixSubfield σ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKcard,
      GaloisField.card 2 g hg.ne']
  let e0 : GaloisField 2 g ≃+* ↥(fixSubfield σ) := FiniteField.ringEquivOfCardEq hcardEq
  haveI : CharP ↥(fixSubfield σ) 2 :=
    (RingHom.charP_iff (fixSubfield σ).subtype (fixSubfield σ).subtype.injective 2).2 inferInstance
  obtain ⟨Ψc, hΨcpin, hΨcrange, hΨcker⟩ := rckE6_pinCanon hτ hβroot hι e0
  have hC : componentRootSpan (fixSubfield σ) (rootCharHom a) i = Ψc.range := by
    rw [hΨcrange]
    show rootSpan τ ↥(fixSubfield σ) (componentRoots (rootCharHom a) i) = _
    rw [hΨβ]
  have hmem : ∀ x, Ψc x ∈ componentRootSpan (fixSubfield σ) (rootCharHom a) i := fun x => by
    rw [hC]; exact ⟨x, rfl⟩
  let Ψ' : (ggU .E6 0 g).K →* ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
    (show (ggU .E6 0 g).K →* ModGL τ ↥(fixSubfield σ) from Ψc).codRestrict _ hmem
  have hΨ'surj : Function.Surjective Ψ' := by
    rintro ⟨c, hc⟩
    have hc' : c ∈ Ψc.range := hC ▸ hc
    obtain ⟨x, rfl⟩ := hc'
    exact ⟨x, rfl⟩
  have hperfC : ⁅componentRootSpan (fixSubfield σ) (rootCharHom a) i,
      componentRootSpan (fixSubfield σ) (rootCharHom a) i⁆ =
      componentRootSpan (fixSubfield σ) (rootCharHom a) i := by
    apply Subgroup.isPerfect_iff.1
    refine Group.isPerfect_def.2 ?_
    have h1 := congrArg (Subgroup.map Ψ') hcommM
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective Ψ' hΨ'surj] at h1
    rw [commutator_def]
    exact h1
  have hR : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf3 hperfC) hf1
  have hmemR : ∀ x, f (Ψ' x) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := fun x => by
    rw [← hR]; exact ⟨_, rfl⟩
  let φ : (ggU .E6 0 g).K →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (f.comp Ψ').codRestrict _ hmemR
  have hφ : ∀ x, ((φ x : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) : ModGL τ GGL) =
      f (Ψ' x) := fun x => rfl
  refine ⟨(fixSubfield σ).subtype.comp e0.toRingHom, φ, ?_, ?_, ?_, ?_, ?_, hfinM,
    Group.isPerfect_def.2 hcommM, hsplit, ?_, ?_, ?_, hR⟩
  · intro c
    exact (e0 c).2
  · intro y hy
    exact ⟨e0.symm ⟨y, hy⟩, by simp⟩
  · rintro ⟨r, hr⟩
    rw [← hR] at hr
    obtain ⟨c, rfl⟩ := hr
    obtain ⟨x, rfl⟩ := hΨ'surj c
    exact ⟨x, Subtype.ext rfl⟩
  · intro x hx
    have h2 : Ψ' x ∈ Subgroup.center _ := hf2 (show Ψ' x ∈ f.ker from congrArg Subtype.val hx)
    exact rckA4_preimage_center Ψ' hcommM (fun y hy => hΨcker
      (show Ψc y = 1 from congrArg Subtype.val hy)) h2
  · intro γ' hγ' c
    refine (hφ _).trans ?_
    rw [hfz]
    have h1 : ((Ψ' (e6Data_valid.xm (GaloisField 2 g) γ' c) :
        ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i)) : ModGL τ ↥(fixSubfield σ)) =
        pinnedX τ ↥(fixSubfield σ) (∑ j : Fin 6, γ' j • β j) (e0 c) :=
      hΨcpin γ' hγ' c
    rw [h1, baseChangeGL_pinnedX]
    rfl
  · exact (CFSG.GroupTheory.GomiLeviExc.MinusculeModel.isCharTwoModel_e6
      (GaloisField 2 g)).odd_card_center
  · exact Or.inl ⟨.E6, 0, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
      hadm, rfl⟩
  · exact Or.inl ⟨.E6, 0, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hadm, rfl⟩

end CFSG.StandardType.RCKRP

end
