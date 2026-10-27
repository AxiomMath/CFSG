module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ComponentAttachPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankExclusionFinishPart1

@[expose] public section

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType CFSG.StandardType.ClassicalPosition CFSG.Open
open CFSG.StandardType.LieCore
open CFSG.StandardType.F4ExplicitPos.RankExclusion
open CFSG.StandardType.F4ExplicitPos.LowRankModels
open CFSG.StandardType.F4ExplicitPos.ComponentAttach
open CFSG.StandardType.F4ExplicitPos.CyclicFinish
open CFSG.StandardType.F4ExplicitPos.InnerDirect
open CFSG.StandardType.F4ExplicitPos.CenterProofFast
open CFSG.StandardType.F4ExplicitPos.CubicLiteral
open CFSG.StandardType.F4ExplicitPos.CubicAction
open CFSG.StandardType.F4ExplicitPos.AmbientAction
open CFSG.StandardType.F4ExplicitPos.Quasisimple
open CFSG.StandardType.F4ExplicitPos.CTNative
open scoped Pointwise

namespace CFSG.StandardType.F4ExplicitPos.RankExclusionFinish

theorem rank_exclusion_neighbor_models
    {Ω : Type} [Field Ω] [CharP Ω 2] [IsSepClosed Ω] [IsAlgClosed Ω]
    (halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω)
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {p : ℕ}
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x)
    {e : X} (he : e ∈ D) {K : Subgroup X}
    (hKG : K ≤ G₀)
    (hKcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({e} : Set X)))
    (hJK : J ≤ K) (hKne : K ≠ J)
    (a : Fin Tag.F4.rank → Ωˣ) (i : KernelComponent (rootCharHom a))
    (Θ : B₁ →* ModGL Tag.F4 Ω) (η : G₀ →* ModGL Tag.F4 Ω)
    (hBG : B₁ ≤ Subgroup.normalizer (G₀ : Set X))
    (hηinj : Function.Injective η)
    (hηact : ∀ (b : B₁) (y : G₀),
      η ((G₀.normalizerMonoidHom ⟨b, hBG b.2⟩) y) = Θ b * η y * (Θ b)⁻¹)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (LangD : LangDatum Tag.F4 Ω) (hρ : FrobRootMap LangD ρ)
    (hKorbit : (η.comp (Subgroup.inclusion hKG)).range ≤
      rootSpan Tag.F4 Ω (ratOrbit (fun u => ρ u) (componentRoots (rootCharHom a) i)))
    (hfix : ∀ b : B₁, LangD.step (Θ b) = Θ b)
    (ha : ∀ j, a j ^ p = 1)
    (hadj : ∀ b : B₁, Θ b ∈ adjointGroup Tag.F4 Ω)
    (hcomm : ∀ b : B₁,
      rootDiagUnit Tag.F4 a * Θ b * (rootDiagUnit Tag.F4 a)⁻¹ = Θ b) :
    3 ≤ compRank (componentRoots (rootCharHom a) i) := by
  have hH' := hH
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hBN : B₁ ≤ Subgroup.normalizer (K : Set X) :=
    CFSG.StandardType.F4ExplicitPos.Neighbors.f4_neighbor_normalized_by_B1 hH' he hKG hKcomp hJK
  have hcub : p ^ 3 ≤ Nat.card (conjAction hBN).range :=
    (CubicLiteral.cubic_action_neighbor hH' he hKG hKcomp hJK hKne).2.1
  exact rank_exclusion_actual_theta_models (Ω := Ω) halg a i Θ η hBG hKG hBN hηinj hηact
    ρ LangD hρ hKorbit hfix h5 h6 ha hadj hcomm h9 hcub

theorem hH_range
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {p : ℕ}
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x) : ψ.range = G₀ :=
  hH.1

theorem hH_ker
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {p : ℕ}
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x) :
    ψ.ker ≤ Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) := by
  change ψ.ker ≤ Subgroup.center (ggU .F4 n f).K
  exact hH.2.1

theorem hH_BN
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {p : ℕ}
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x) :
    B₁ ≤ Subgroup.normalizer (G₀ : Set X) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  exact h7

theorem hH_DB
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {p : ℕ}
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x) : D ≤ B₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  exact h11

theorem hH_xD
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {p : ℕ}
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x) : x ∈ D := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  exact h17

theorem hH_prime
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {p : ℕ}
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x) : p.Prime := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  exact h5

theorem hH_ne_two
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {p : ℕ}
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x) : p ≠ 2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  exact h6

theorem hH_elem
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {p : ℕ}
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x) : IsElemAbelian p B₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  exact h9

theorem ThetaF4_mem_adjointGroup
    {K L X : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    [Group X] [Finite X]
    (ψ : adjointGroup Tag.F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    {g0 : ModGL Tag.F4 L} (hg0C : g0 ∈ adjointGroup Tag.F4 L) (b : B1) :
    ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0 b ∈ adjointGroup Tag.F4 L := by
  rw [ThetaF4_apply]
  exact mul_mem (mul_mem (Subgroup.inv_mem _ hg0C)
    (thetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner b).2) hg0C

theorem comm_of_actor
    {X L : Type} [Group X] [Field L] {B1 : Subgroup X} {p : ℕ}
    (Θ : B1 →* ModGL Tag.F4 L) (hBel : IsElemAbelian p B1)
    {a : Fin Tag.F4.rank → Lˣ} {e : B1} (he : Θ e = rootDiagUnit Tag.F4 a) :
    ∀ b : B1, rootDiagUnit Tag.F4 a * Θ b * (rootDiagUnit Tag.F4 a)⁻¹ = Θ b := by
  intro b
  rw [← he]
  have hc : Θ e * Θ b = Θ b * Θ e := by
    simpa using congrArg Θ (hBel.1.is_comm.comm e b)
  calc Θ e * Θ b * (Θ e)⁻¹ = Θ b * Θ e * (Θ e)⁻¹ := by rw [hc]
    _ = Θ b := by group

theorem exists_hKorbit_of_actual_component
    {Ω : Type} [Field Ω] [CharP Ω 2] [IsSepClosed Ω] [IsAlgClosed Ω]
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X}
    [Algebra (GaloisField 2 f) Ω]
    {G0 B1 D : Subgroup X}
    (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 (GaloisField 2 f)))
    (hcenter : Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ Nat.card (GaloisField 2 f))
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 Ω} (hg0C : g0 ∈ adjointGroup Tag.F4 Ω)
    (hg0 : ((frobF4 (K := GaloisField 2 f) (L := Ω) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 Ω) :
      ModGL Tag.F4 Ω) = g0 * canonicalRep (coxeterSystem Tag.F4) Ω w)
    (LangD : LangDatum Tag.F4 Ω)
    (hLangD : LangD = langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap LangD ρ)
    (a : Fin Tag.F4.rank → Ωˣ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : ∀ j, a j ^ p = 1)
    (haD : rootDiagUnit Tag.F4 a ∈ LangD.torus)
    (hDB : D ≤ B1)
    {z : X} (hzD : z ∈ D)
    (hThetaZ : ThetaF4 (L := Ω) ψ G0 B1 hG0 hker hcenter hBN hinner g0
        ⟨z, hDB hzD⟩ = rootDiagUnit Tag.F4 a)
    {K : Subgroup X} (hKG : K ≤ G0)
    (hKcomp : CFSG.Assembly.IsComponentOf K (G0 ⊓ Subgroup.centralizer ({z} : Set X))) :
    ∃ i : KernelComponent (rootCharHom a),
      ((etaF4 (L := Ω) ψ G0 hG0 hker hcenter g0).comp
        (Subgroup.inclusion hKG)).range ≤
      rootSpan Tag.F4 Ω (ratOrbit (fun u => ρ u) (componentRoots (rootCharHom a) i)) := by
  classical
  subst hLangD
  let η := etaF4 (L := Ω) ψ G0 hG0 hker hcenter g0
  have : Finite (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).model := by
    rw [← etaF4_range_model (K := GaloisField 2 f) (L := Ω) ψ G0 hG0 hker hcenter
      Fr hFr w hg0C hg0]
    exact Set.Finite.to_subtype (by
      rw [MonoidHom.coe_range]
      exact Finite.Set.finite_range η)
  have hKbar : CFSG.Assembly.IsComponentOf ((K.subgroupOf G0).map η)
      ((langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0).Γ ⊓
        Subgroup.centralizer ({rootDiagUnit Tag.F4 a} : Set (ModGL Tag.F4 Ω))) :=
    CFSG.StandardType.F4ExplicitPos.ComponentAttach.isComponentOf_eta_single
      (L := Ω) ψ G0 B1 hG0 hker hcenter hBN hinner Fr hFr w hg0C hg0
      D hDB hzD a hThetaZ hKcomp
  obtain ⟨i, hi⟩ := CFSG.StandardType.F4ExplicitPos.CyclicFinish.f4_component_le_rationalRootSpan
    (L := Ω) (langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0)
    ρ hρ hp hp2 a ha haD ((K.subgroupOf G0).map η) hKbar
  refine ⟨i, ?_⟩
  have hrange : (η.comp (Subgroup.inclusion hKG)).range = (K.subgroupOf G0).map η := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  rw [hrange]
  simpa [rationalRoots, ratOrbit] using hi

end CFSG.StandardType.F4ExplicitPos.RankExclusionFinish
end

end
