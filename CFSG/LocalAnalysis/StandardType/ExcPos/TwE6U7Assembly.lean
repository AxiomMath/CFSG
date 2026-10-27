module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Pieces
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Orbit
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Setup
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Swapped
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Dict
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Lift
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePinnedTransfer
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSU
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTwE6

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private lemma lk0xu7h_ggRootSub_map_conj {U G : Type} [Group U] [Group G]
    (D : UniversalRootDatum U) (φ : U →* G) (γ : Fin D.rank → ℤ) (u m : U) {h : G}
    (hm : φ m = h) :
    (ggRootSub D φ γ u).map (MulAut.conj h).toMonoidHom = ggRootSub D φ γ (m * u) := by
  have hcomp : (MulAut.conj h).toMonoidHom.comp (φ.comp (MulAut.conj u).toMonoidHom) =
      φ.comp (MulAut.conj (m * u)).toMonoidHom := by
    ext x
    change h * φ (u * x * u⁻¹) * h⁻¹ = φ ((m * u) * x * (m * u)⁻¹)
    simp only [map_mul, map_inv, ← hm]
    group
  simp only [ggRootSub, Subgroup.map_map, hcomp]

private lemma lk0xu7h_map_subgroupOf_comp_subtype {U X Y : Type} [Group U] [Group X] [Group Y]
    {K G₀ : Subgroup X} (hKG : K ≤ G₀) (ψ' : U →* ↥K) (φ : U →* Y) (η : ↥G₀ →* Y)
    (hφ : ∀ s, η (Subgroup.inclusion hKG (ψ' s)) = φ s) (A : Subgroup U) :
    (((A.map (K.subtype.comp ψ')).subgroupOf G₀).map η) = A.map φ := by
  apply le_antisymm
  · rintro y ⟨a, ha, rfl⟩
    have ha' : (a : X) ∈ A.map (K.subtype.comp ψ') := Subgroup.mem_subgroupOf.mp ha
    obtain ⟨z, hzA, hz⟩ := Subgroup.mem_map.mp ha'
    have haz : a = Subgroup.inclusion hKG (ψ' z) := by
      apply Subtype.ext
      simpa using hz.symm
    rw [haz, hφ z]
    exact Subgroup.mem_map_of_mem φ hzA
  · rintro y ⟨z, hzA, rfl⟩
    refine Subgroup.mem_map.mpr ⟨Subgroup.inclusion hKG (ψ' z), ?_, hφ z⟩
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map_of_mem (K.subtype.comp ψ') hzA

theorem excU7_of_pieces (hC1 : TwE6U7C1) (hC2 : TwE6U7C2) (hDict : ExcNbrDictTwo)
    (hCover : ExcU7Cover) (hTrans : ExcU7Transport) : ExcU7 := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hP R Rm P hRJ hRmJ hpos hb e he he1 K hKG hKc hJK hKJ hodd
    hKG₀ iK hsub hne hspan horb h2
  have hP' := hP
  obtain ⟨hψr, hψk, hLM, hZodd, hp, hp2, hB₁N, hB₁inn, hB₁el, -, hDB, hDcard, -, -, hJ, -, hx,
    hx1, -, -, -, -, -, -, -, -, -, -, -, -, hlast⟩ := hP
  obtain ⟨A, hB₁A, -, -, -, hAC, -⟩ := hlast (Or.inr rfl)
  have hBC : B₁ ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right (Subgroup.centralizer (G₀ : Set X)) hB₁A).trans hAC.le)
  have hKη : (K.subgroupOf G₀).map P.η = rationalComponent P.ρ P.Δ.Γ (P.chiAt e) iK :=
    hDict X n f ψ p G₀ B₁ D J L x hP' R Rm P hRJ hRmJ hpos hb e he he1 K hKG hKc hJK hKJ hodd
      hKG₀ iK hsub hne hspan horb h2
  have hKq : CFSG.Assembly.IsQuasisimple ↥K := hKc.2.2
  have hqs : CFSG.IsQuasisimple ↥(rationalComponent P.ρ P.Δ.Γ (P.chiAt e) iK) := by
    have h := isQuasisimple_map_of_ker_le_center hKG P.η P.ker_η hKq
    rwa [hKη] at h
  have hperfK : Group.IsPerfect ↥K := ⟨hKq.1⟩
  obtain ⟨S, hSD, hSρ, hf2, hcl⟩ :=
    excU7_suClass hC1 hC2 hp hp2 P hb h2 hDB hBC he he1 hsub horb hqs
  obtain ⟨φ, hφr, hφk, hfin, -, hsplit, β, u₀, hβ, hβ2, hA₀⟩ :=
    hCover p S (P.coord e) iK f p hcl
  obtain ⟨i₂, hi₂, hi₂r, -, -, hsub₂, -, -⟩ := excU7_classes hp hp2 P hb h2 he hsub horb
  have hA : ExcSwapped S (P.coord e) iK f ((R.subgroupOf G₀).map P.η) :=
    excU7_swapped P hb hDB S hSD hSρ he hsub hi₂ hi₂r hsub₂
  obtain ⟨h, hh, hconj⟩ := hTrans p S (P.coord e) iK f p hcl
    (ggRootSub (ggU .PSU 6 f).D φ β u₀) ((R.subgroupOf G₀).map P.η) hA₀ hA
  obtain ⟨m, hm⟩ : ∃ m, φ m = h := by
    rw [← hφr] at hh
    exact hh
  have hconj' : (R.subgroupOf G₀).map P.η = ggRootSub (ggU .PSU 6 f).D φ β (m * u₀) := by
    rw [← hconj, lk0xu7h_ggRootSub_map_conj (ggU .PSU 6 f).D φ β u₀ m hm]
  have hodd0 : Odd (Nat.card (Subgroup.center ↥G₀)) :=
    odd_card_center_of_odd_card_centralizer hZodd
  have hΓ : S.Γ = P.Δ.Γ := by
    change S.D.Γ = P.Δ.Γ
    rw [hSD]
  have hrational : rationalComponent S.ρ S.Γ (rootCharHom (P.coord e)) iK =
      rationalComponent P.ρ P.Δ.Γ (P.chiAt e) iK := by
    simp only [hSρ, hΓ, ExcPacket.chiAt]
  have hφ : φ.range = (K.subgroupOf G₀).map P.η :=
    hφr.trans (hrational.trans hKη.symm)
  haveI : Finite (ggU .PSU 6 f).K := hfin
  obtain ⟨ψ', hψ'surj, hψ'⟩ := exists_cover_lift hKG P.η P.ker_η hodd0 hsplit φ hφ hperfK
  let φ'' : (ggU .PSU 6 f).K →* X := K.subtype.comp ψ'
  have hφ''range : φ''.range = K := by
    rw [show φ'' = K.subtype.comp ψ' from rfl, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr hψ'surj, Subgroup.map_top, Subgroup.range_subtype]
  have hφ''ker : φ''.ker ≤ Subgroup.center (ggU .PSU 6 f).K := by
    intro s hs
    have hs1 : ψ' s = 1 := Subtype.ext (by simpa [φ''] using hs)
    exact hφk (by
      rw [MonoidHom.mem_ker]
      calc φ s = P.η (Subgroup.inclusion hKG (ψ' s)) := (hψ' s).symm
        _ = 1 := by rw [hs1]; simp)
  have hR'le : ggRootSub (ggU .PSU 6 f).D φ'' β (m * u₀) ≤ G₀ := by
    rw [CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map]
    exact (Subgroup.map_le_range _ _).trans (hφ''range.le.trans hKG)
  have hR'p : IsPGroup 2 (ggRootSub (ggU .PSU 6 f).D φ'' β (m * u₀)) := by
    rw [CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map]
    exact (CFSG.StandardType.LieKnownR2.Short.rootGroup_isPGroup_PSU hβ (m * u₀) rfl).of_surjective
      (φ''.subgroupMap _) (φ''.subgroupMap_surjective _)
  have hR'map : ((ggRootSub (ggU .PSU 6 f).D φ'' β (m * u₀)).subgroupOf G₀).map P.η =
      ggRootSub (ggU .PSU 6 f).D φ β (m * u₀) := by
    rw [CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map]
    rw [lk0xu7h_map_subgroupOf_comp_subtype hKG ψ' φ P.η hψ'
      (ggRootSub (ggU .PSU 6 f).D (MonoidHom.id _) β (m * u₀))]
    rw [← CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map]
  obtain ⟨β', hβ', -, u', hRdef, -⟩ := hpos
  have hRle : R ≤ G₀ := by
    rw [hRdef, CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map, ← hψr]
    exact Subgroup.map_le_range _ _
  have hRp : IsPGroup 2 R := by
    rw [hRdef, CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map]
    exact (CFSG.StandardType.LieKnownR2.Short.rootGroup_isPGroup_twistedE6 hβ' u' rfl).of_surjective
      (ψ.subgroupMap _) (ψ.subgroupMap_surjective _)
  have hmap : (R.subgroupOf G₀).map P.η =
      ((ggRootSub (ggU .PSU 6 f).D φ'' β (m * u₀)).subgroupOf G₀).map P.η := by
    rw [hconj', hR'map]
  have hReq : R = ggRootSub (ggU .PSU 6 f).D φ'' β (m * u₀) :=
    eq_of_isPGroup_of_map_eq hRle hR'le P.η P.ker_η hodd0 hRp hR'p hmap
  exact ⟨β, hf2, hβ, hβ2, φ'', hφ''range, hφ''ker, m * u₀, hReq⟩

end CFSG.StandardType.LieKnownR2.ExcPos
