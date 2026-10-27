module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthKSLBase
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

@[expose] def GGKSLClauseA (S : LargeEvenLabel → Prop)
    (Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop) : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S lab →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ 3 = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∃ D : GGKacDatum, Valid lab 3 D ∧
            ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
              ∃ o ∈ D.orbits, LargeEvenInLambda2 o.lab ∧
                GGHasLabel o.lab (J ⧸ Subgroup.center J)

theorem GGK0MainB.toKSLClauseA {Gen : LargeEvenLabel → ℕ → Prop}
    {Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop} (h : GGK0MainB Gen Valid) :
    GGKSLClauseA (fun lab => Gen lab 3) Valid := by
  intro lab hlab hgen Q hQ
  refine largeEvenRawDatum_mono ?_ (h 3 lab hlab hgen Q hQ)
  rintro R _ I F ⟨hq, hP⟩
  refine ⟨hq, fun L' _ _ ψ hψ hker hcomm e he3 hind => ?_⟩
  obtain ⟨D, hV, ha, -⟩ := hP L' ψ hψ hker hcomm e he3 hind
  refine ⟨D, hV, fun J hJ => ?_⟩
  obtain ⟨o, ho, -, -, hΛ, hh⟩ := ha J hJ
  exact ⟨o, ho, hΛ, hh⟩

theorem GGK0ExcB3.toKSLClauseA (h : GGK0ExcB3) :
    GGKSLClauseA (fun lab => GGKacExcPair lab 3) GGKacValid := by
  intro lab hlab hpair Q hQ
  refine largeEvenRawDatum_mono ?_ (h 3 lab hlab hpair Q hQ)
  rintro R _ I F ⟨hq, hP⟩
  refine ⟨hq, fun L' _ _ ψ hψ hker hcomm e he3 hind => ?_⟩
  obtain ⟨D, hV, ha, -⟩ := hP L' ψ hψ hker hcomm e he3 hind
  refine ⟨D, hV, fun J hJ => ?_⟩
  obtain ⟨o, ho, -, -, hΛ, hh⟩ := ha J hJ
  exact ⟨o, ho, hΛ, hh⟩

theorem ggKSL_orbit
    {S : LargeEvenLabel → Prop} {Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop}
    (hA : GGKSLClauseA S Valid) {G : Type} [Group G] [Finite G] {K J : Subgroup G} {x : G}
    (hx3 : orderOf x = 3) (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (hmark : LargeEvenMarking K (fun lab _ _ I _ θ => S lab ∧ lab.n = 1 ∧
      ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = x⁻¹ * l * x) φ))
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({x} : Set G) ⊓ K)) {f : ℕ}
    (hJf : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 2 f) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ S lab ∧ lab.n = 1 ∧
      GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧ ∃ D : GGKacDatum, Valid lab 3 D ∧
        ∃ o ∈ D.orbits, o.lab = ⟨.A, 3, f⟩ ∨ o.lab = ⟨.D, 3, f⟩ := by
  obtain ⟨hK, lab, hlab, hraw⟩ := hmark
  obtain ⟨_, _, _, _, _, _, _, hS, hn, _⟩ := largeEvenRawDatum_exists hraw
  refine ⟨lab, hlab, hS, hn, largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hraw, ?_⟩
  obtain ⟨e, he3, he, hJ', ⟨eJ⟩⟩ := ggKSL_transport hx3 hxN hJ
  obtain ⟨R, _, I, F, ⟨_, _, θ, _, _, φ, hφI, hφ⟩, hP⟩ :=
    largeEvenRawDatum_exists (hA lab hlab hS _ hraw)
  obtain ⟨D, hV, ha⟩ := hP ↥K (TablePThreeKG.proj θ) (ggKSL_proj_surjective θ)
    (ggKSL_ker_proj_le_center θ) hK e he3 ⟨φ, hφI, fun l => hφ l _ (he l)⟩
  obtain ⟨o, ho, hΛo, hhas⟩ := ha _ hJ'
  refine ⟨D, hV, o, ho, ?_⟩
  rcases ggLabelIso_typeA_cases ggLabelRigidInput_holds (by norm_num : 2 ≤ 3) hΛo
      (largeEvenInLambda2_typeA hJf) (ggHasLabel_of_mulEquiv eJ hhas) (ggHasLabel_typeA hJf)
    with h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

end CFSG.StandardType

end
