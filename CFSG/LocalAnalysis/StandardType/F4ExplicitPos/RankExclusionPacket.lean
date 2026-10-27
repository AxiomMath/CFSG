module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OddKernelActual
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankExclusionFinishPart3

@[expose] public section

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.StandardType CFSG.StandardType.ClassicalPosition CFSG.StandardType.LieCore CFSG.Open

open CFSG.StandardType.F4ExplicitPos.RankExclusionFinish

open CFSG.StandardType.F4ExplicitPos.OddKernelActual

open CFSG.StandardType.F4ExplicitPos.ComponentAttach

open CFSG.StandardType.F4ExplicitPos.AmbientAction

open CFSG.StandardType.F4ExplicitPos.InnerDirect

open CFSG.StandardType.F4ExplicitPos.CyclicFinish

open CFSG.StandardType.F4ExplicitPos.CubicLiteral

open CFSG.StandardType.F4ExplicitPos.CubicAction

open CFSG.StandardType.F4ExplicitPos.Quasisimple

open scoped Pointwise

namespace CFSG.StandardType.F4ExplicitPos.RankExclusionPacket

theorem range_le_componentRootSpan_of_ratOrbit
    {Ω : Type} [Field Ω]
    {X : Type} [Group X]
    {G₀ : Subgroup X} {K : Subgroup X}
    (η : G₀ →* ModGL Tag.F4 Ω) (hKG : K ≤ G₀)
    (LangD : LangDatum Tag.F4 Ω) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ))
    (hρ : FrobRootMap LangD ρ)
    (a : Fin Tag.F4.rank → Ωˣ)
    {p : ℕ} (hp : Odd p) (ha : ∀ j, a j ^ p = 1)
    (haD : rootDiagUnit Tag.F4 a ∈ LangD.torus)
    (i : KernelComponent (rootCharHom a))
    (hKorbit : (η.comp (Subgroup.inclusion hKG)).range ≤
      rootSpan Tag.F4 Ω (ratOrbit (fun u => ρ u) (componentRoots (rootCharHom a) i))) :
    (η.comp (Subgroup.inclusion hKG)).range ≤
      rootSpan Tag.F4 Ω (componentRoots (rootCharHom a) i) := by
  have hcollapse := OddKernelActual.f4_cyclic_rationalRoots_eq_of_coord
    LangD ρ hρ a haD hp ha i
  have hKorbit' : (η.comp (Subgroup.inclusion hKG)).range ≤
      rootSpan Tag.F4 Ω (rationalRoots ρ (rootCharHom a) i) := by
    simpa only [rationalRoots, ratOrbit] using hKorbit
  rw [hcollapse] at hKorbit'
  exact hKorbit'

theorem neighbor_kbar_attachment
    {Ω : Type} [Field Ω] [CharP Ω 2] [IsSepClosed Ω] [IsAlgClosed Ω]
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {p : ℕ}
    [Algebra (GaloisField 2 f) Ω]
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x)
    {e : X} (he : e ∈ D) {K : Subgroup X}
    (hKG : K ≤ G₀)
    (hKcomp : CFSG.Assembly.IsComponentOf K
      (Subgroup.centralizer ({e} : Set X)))
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ Nat.card (GaloisField 2 f))
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 Ω} (hg0C : g0 ∈ adjointGroup Tag.F4 Ω)
    (hg0 : ((frobF4 (K := GaloisField 2 f) (L := Ω) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 Ω) :
      ModGL Tag.F4 Ω) = g0 * canonicalRep (coxeterSystem Tag.F4) Ω w)
    (LangD : LangDatum Tag.F4 Ω)
    (hLangD : LangD = langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0)
    (a : Fin Tag.F4.rank → Ωˣ)
    (hThetaE : ThetaF4 (L := Ω) ψ G₀ B₁ (hH_range hH) (hH_ker hH)
        (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) (hH_BN hH)
        (f4_exists_inner_correction_hH hH) g0 ⟨e, hH_DB hH he⟩ = rootDiagUnit Tag.F4 a) :
    CFSG.Assembly.IsComponentOf
      ((K.subgroupOf G₀).map
        (etaF4 (L := Ω) ψ G₀ (hH_range hH) (hH_ker hH)
          (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) g0))
      (LangD.Γ ⊓
        Subgroup.centralizer ({rootDiagUnit Tag.F4 a} : Set (ModGL Tag.F4 Ω))) := by
  have hKcompG : CFSG.Assembly.IsComponentOf K
      (G₀ ⊓ Subgroup.centralizer ({e} : Set X)) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hKcomp
      (le_inf hKG hKcomp.1) inf_le_right
  rw [hLangD]
  exact CFSG.StandardType.F4ExplicitPos.ComponentAttach.isComponentOf_eta_single
    (L := Ω) ψ G₀ B₁ (hH_range hH) (hH_ker hH)
    (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) (hH_BN hH)
    (f4_exists_inner_correction_hH hH) Fr hFr w hg0C hg0 D (hH_DB hH) he a hThetaE hKcompG

theorem exists_selected_neighbor_data
    {Ω : Type} [Field Ω] [CharP Ω 2] [IsSepClosed Ω] [IsAlgClosed Ω]
    (halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω)
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {p : ℕ}
    [Algebra (GaloisField 2 f) Ω]
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x)
    {e : X} (he : e ∈ D) {K : Subgroup X}
    (hKG : K ≤ G₀)
    (hKcomp : CFSG.Assembly.IsComponentOf K
      (Subgroup.centralizer ({e} : Set X)))
    (hJK : J ≤ K) (hKne : K ≠ J)
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ Nat.card (GaloisField 2 f))
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 Ω} (hg0C : g0 ∈ adjointGroup Tag.F4 Ω)
    (hg0 : ((frobF4 (K := GaloisField 2 f) (L := Ω) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 Ω) :
      ModGL Tag.F4 Ω) = g0 * canonicalRep (coxeterSystem Tag.F4) Ω w)
    (LangD : LangDatum Tag.F4 Ω)
    (hLangD : LangD = langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap LangD ρ)
    (a : Fin Tag.F4.rank → Ωˣ) (ha : ∀ j, a j ^ p = 1)
    (hThetaE : ThetaF4 (L := Ω) ψ G₀ B₁ (hH_range hH) (hH_ker hH)
        (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) (hH_BN hH)
        (f4_exists_inner_correction_hH hH) g0 ⟨e, hH_DB hH he⟩ = rootDiagUnit Tag.F4 a)
    (haD : rootDiagUnit Tag.F4 a ∈ LangD.torus)
    (hfix : ∀ b : B₁, LangD.step
      (ThetaF4 (L := Ω) ψ G₀ B₁ (hH_range hH) (hH_ker hH)
        (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) (hH_BN hH)
        (f4_exists_inner_correction_hH hH) g0 b) =
      ThetaF4 (L := Ω) ψ G₀ B₁ (hH_range hH) (hH_ker hH)
        (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) (hH_BN hH)
        (f4_exists_inner_correction_hH hH) g0 b) :
    ∃ i : KernelComponent (rootCharHom a),
      ((etaF4 (L := Ω) ψ G₀ (hH_range hH) (hH_ker hH)
          (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) g0).comp
        (Subgroup.inclusion hKG)).range ≤
        rootSpan Tag.F4 Ω (ratOrbit (fun u => ρ u) (componentRoots (rootCharHom a) i)) ∧
      ((etaF4 (L := Ω) ψ G₀ (hH_range hH) (hH_ker hH)
          (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) g0).comp
        (Subgroup.inclusion hKG)).range ≤
        rootSpan Tag.F4 Ω (componentRoots (rootCharHom a) i) ∧
      CFSG.Assembly.IsComponentOf
        ((K.subgroupOf G₀).map
          (etaF4 (L := Ω) ψ G₀ (hH_range hH) (hH_ker hH)
            (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) g0))
        (LangD.Γ ⊓
          Subgroup.centralizer ({rootDiagUnit Tag.F4 a} : Set (ModGL Tag.F4 Ω))) ∧
      3 ≤ compRank (componentRoots (rootCharHom a) i) := by
  have hH' := hH
  let hcenter := center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)
  let η := etaF4 (L := Ω) ψ G₀ (hH_range hH) (hH_ker hH) hcenter g0
  let Θ := ThetaF4 (L := Ω) ψ G₀ B₁ (hH_range hH) (hH_ker hH) hcenter (hH_BN hH)
    (f4_exists_inner_correction_hH hH) g0
  have hηinj : Function.Injective η :=
    etaF4_injective (L := Ω) ψ G₀ (hH_range hH) (hH_ker hH) hcenter g0
  have hηact : ∀ (b : B₁) (y : G₀),
      η ((G₀.normalizerMonoidHom ⟨b, hH_BN hH b.2⟩) y) = Θ b * η y * (Θ b)⁻¹ :=
    etaF4_action (L := Ω) ψ G₀ B₁ (hH_range hH) (hH_ker hH) hcenter (hH_BN hH)
      (f4_exists_inner_correction_hH hH) g0
  have hKcompG : CFSG.Assembly.IsComponentOf K
      (G₀ ⊓ Subgroup.centralizer ({e} : Set X)) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hKcomp
      (le_inf hKG hKcomp.1) inf_le_right
  obtain ⟨i, hKorbit⟩ := RankExclusionFinish.exists_hKorbit_of_actual_component
    (Ω := Ω) (ψ := ψ) (hH_range hH) (hH_ker hH) hcenter (hH_BN hH)
    (f4_exists_inner_correction_hH hH) (Fr := Fr) hFr w hg0C hg0
    LangD hLangD ρ hρ a (hH_prime hH) (hH_ne_two hH) ha haD (hH_DB hH) he
    hThetaE hKG hKcompG
  have hadj : ∀ b : B₁, Θ b ∈ adjointGroup Tag.F4 Ω :=
    fun b => ThetaF4_mem_adjointGroup (L := Ω) ψ G₀ B₁ (hH_range hH) (hH_ker hH)
      hcenter (hH_BN hH) (f4_exists_inner_correction_hH hH) hg0C b
  have hcomm : ∀ b : B₁,
      rootDiagUnit Tag.F4 a * Θ b * (rootDiagUnit Tag.F4 a)⁻¹ = Θ b :=
    comm_of_actor (L := Ω) Θ (hH_elem hH) hThetaE
  have hrank : 3 ≤ compRank (componentRoots (rootCharHom a) i) :=
    CFSG.StandardType.F4ExplicitPos.RankExclusionFinish.rank_exclusion_neighbor_models
      (Ω := Ω) halg hH' he hKG hKcomp hJK hKne a i Θ η (hH_BN hH) hηinj hηact
      ρ LangD hρ hKorbit hfix ha hadj hcomm
  have hcomponent : (η.comp (Subgroup.inclusion hKG)).range ≤
      rootSpan Tag.F4 Ω (componentRoots (rootCharHom a) i) :=
    range_le_componentRootSpan_of_ratOrbit (η := η) hKG LangD ρ hρ a
      ((hH_prime hH).odd_of_ne_two (hH_ne_two hH)) ha haD i hKorbit
  have hattach : CFSG.Assembly.IsComponentOf ((K.subgroupOf G₀).map η)
      (LangD.Γ ⊓
        Subgroup.centralizer ({rootDiagUnit Tag.F4 a} : Set (ModGL Tag.F4 Ω))) :=
    neighbor_kbar_attachment hH he hKG hKcomp hFr w hg0C hg0 LangD hLangD a hThetaE
  refine ⟨i, hKorbit, ?_, ?_, hrank⟩
  · simpa only [η] using hcomponent
  · simpa only [η] using hattach

theorem neighbor_rank_or_central_selected
    {Ω : Type} [Field Ω] [CharP Ω 2] [IsSepClosed Ω] [IsAlgClosed Ω]
    (halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω)
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {p : ℕ}
    [Algebra (GaloisField 2 f) Ω]
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x)
    {e : X} (he : e ∈ D) {K : Subgroup X}
    (hKG : K ≤ G₀)
    (hKcomp : CFSG.Assembly.IsComponentOf K
      (Subgroup.centralizer ({e} : Set X)))
    (hJK : J ≤ K) (hKne : K ≠ J)
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ Nat.card (GaloisField 2 f))
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 Ω} (hg0C : g0 ∈ adjointGroup Tag.F4 Ω)
    (hg0 : ((frobF4 (K := GaloisField 2 f) (L := Ω) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 Ω) :
      ModGL Tag.F4 Ω) = g0 * canonicalRep (coxeterSystem Tag.F4) Ω w)
    (LangD : LangDatum Tag.F4 Ω)
    (hLangD : LangD = langDatumF4 (K := GaloisField 2 f) (L := Ω) Fr hFr w hg0C hg0)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap LangD ρ)
    (coords : D → Fin Tag.F4.rank → Ωˣ)
    (hcoords : ∀ d : D,
      ThetaF4 (L := Ω) ψ G₀ B₁ (hH_range hH) (hH_ker hH)
        (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) (hH_BN hH)
        (f4_exists_inner_correction_hH hH) g0 ⟨d, hH_DB hH d.2⟩ = rootDiagUnit Tag.F4 (coords d))
    (hcoords_pow : ∀ (d : D) (j : Fin Tag.F4.rank), coords d j ^ p = 1)
    (hcoords_torus : ∀ d : D, rootDiagUnit Tag.F4 (coords d) ∈ LangD.torus)
    (hfix : ∀ b : B₁, LangD.step
      (ThetaF4 (L := Ω) ψ G₀ B₁ (hH_range hH) (hH_ker hH)
        (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) (hH_BN hH)
        (f4_exists_inner_correction_hH hH) g0 b) =
      ThetaF4 (L := Ω) ψ G₀ B₁ (hH_range hH) (hH_ker hH)
        (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) (hH_BN hH)
        (f4_exists_inner_correction_hH hH) g0 b) :
    K = G₀ ∨
      ∃ i : KernelComponent (rootCharHom (coords ⟨e, he⟩)),
        ((etaF4 (L := Ω) ψ G₀ (hH_range hH) (hH_ker hH)
            (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) g0).comp
          (Subgroup.inclusion hKG)).range ≤
          rootSpan Tag.F4 Ω
            (ratOrbit (fun u => ρ u)
              (componentRoots (rootCharHom (coords ⟨e, he⟩)) i)) ∧
        ((etaF4 (L := Ω) ψ G₀ (hH_range hH) (hH_ker hH)
            (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) g0).comp
          (Subgroup.inclusion hKG)).range ≤
          rootSpan Tag.F4 Ω (componentRoots (rootCharHom (coords ⟨e, he⟩)) i) ∧
        3 ≤ compRank (componentRoots (rootCharHom (coords ⟨e, he⟩)) i) ∧
        rootDiagUnit Tag.F4 (coords ⟨e, he⟩) ≠ 1 ∧
        coords ⟨e, he⟩ ≠ 1 := by
  by_cases hTheta : ThetaF4 (L := Ω) ψ G₀ B₁ (hH_range hH) (hH_ker hH)
      (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) (hH_BN hH)
      (f4_exists_inner_correction_hH hH) g0 ⟨e, hH_DB hH he⟩ = 1
  · left
    exact CFSG.StandardType.F4ExplicitPos.RankExclusionFinish.neighbor_eq_G0_of_theta_eq_one
      hH he hTheta hKG hKcomp
  · right
    have hneD : rootDiagUnit Tag.F4 (coords ⟨e, he⟩) ≠ 1 := by
      intro h
      apply hTheta
      rw [hcoords ⟨e, he⟩, h]
    have hne : coords ⟨e, he⟩ ≠ 1 := by
      intro h
      exact hneD (by rw [h, rootDiagUnit_one])
    obtain ⟨i, hKorbit, hcomponent, _hattach, hrank⟩ :=
      exists_selected_neighbor_data (Ω := Ω) halg hH he hKG hKcomp hJK hKne
        (Fr := Fr) hFr w hg0C hg0 LangD hLangD ρ hρ (coords ⟨e, he⟩)
        (hcoords_pow ⟨e, he⟩) (hcoords ⟨e, he⟩) (hcoords_torus ⟨e, he⟩) hfix
    exact ⟨i, hKorbit, hcomponent, hrank, hneD, hne⟩

end CFSG.StandardType.F4ExplicitPos.RankExclusionPacket

end

end
