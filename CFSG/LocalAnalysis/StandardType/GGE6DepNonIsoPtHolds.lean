module

public import CFSG.LocalAnalysis.StandardType.GGE6IsoFrame
public import CFSG.LocalAnalysis.StandardType.GGE6IsoLayerAdj
public import CFSG.LocalAnalysis.StandardType.GGE6IsoLayerTw
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKGFrameE
public import CFSG.LocalAnalysis.StandardType.GGKGLayersTheta
public import CFSG.LocalAnalysis.StandardType.GGKGTwFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Group
public import CFSG.HardMathSupport.Lang.E6Descent.RankTwistedE6
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCompInner
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Holds
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc3
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcReduction

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three
  CFSG.StandardType.NoOffRest CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.KGL
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three (e6LineChar e6LineFactor
  e6LineFactor_injective e6Line_exists_cube_root_unit)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def NoSingleComp {G : Type*} [Group G] (C : Subgroup G) : Prop :=
  ∀ J : Subgroup G, IsComponentOf J C → ∃ J' : Subgroup G, IsComponentOf J' C ∧ J' ≠ J

private theorem noSingleComp_of_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {C : Subgroup G} (h : NoSingleComp (C.map f)) :
    NoSingleComp C := by
  intro J hJ
  obtain ⟨M, hM, hne⟩ := h _ (isComponentOf_map_of_injective f hf hJ)
  obtain ⟨hM', hmap⟩ := isComponentOf_comap_of_injective f hf hM
  refine ⟨M.comap f, hM', fun heq => hne ?_⟩
  rw [← hmap, heq]

private theorem noSingleComp_of_cover {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') {a : MulAut L'}
    {φ : MulAut R} (hφ : ∀ l, φ (ψ l) = ψ (a l)) (h : NoSingleComp (ggFix φ)) :
    NoSingleComp (ggFix a) := by
  intro J hJ
  have hJJ := SCFourCover.commutator_eq_self_of_isComponentOf hJ
  obtain ⟨M, hM, hne⟩ := h _ ((SCFourCover.isComponentOf_map_iff hψ hker hφ hJJ).1 hJ)
  obtain ⟨J', hJ', hmap⟩ := SCFourCover.exists_isComponentOf_map_eq hψ hker hφ hM
  refine ⟨J', hJ', fun heq => hne ?_⟩
  rw [← hmap, heq]

private theorem ggFix_conj {L' : Type} [Group L'] (m : L') (a : MulAut L') :
    ggFix (MulAut.conj m * a * (MulAut.conj m)⁻¹) =
      (ggFix a).map (MulAut.conj m).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, mem_ggFix, MulEquiv.coe_toMonoidHom, MulAut.mul_apply]
  constructor
  · intro hx
    refine ⟨(MulAut.conj m)⁻¹ x, (MulAut.conj m).injective ?_, MulAut.apply_inv_self _ _ _⟩
    rw [hx, MulAut.apply_inv_self]
  · rintro ⟨y, hy, rfl⟩
    rw [MulAut.inv_apply_self, hy]

private theorem map_ggFix_eq {R G : Type*} [Group R] [Group G] (θ : R →* G)
    (hθ : Function.Injective θ) (φ : MulAut R) (d : G) (hd : ∀ r, θ (φ r) = d * θ r * d⁻¹) :
    (ggFix φ).map θ = θ.range ⊓ Subgroup.centralizer {d} := by
  apply le_antisymm
  · rintro _ ⟨s, hs, rfl⟩
    have h1 : θ s = d * θ s * d⁻¹ := by rw [← hd s, (mem_ggFix.1 hs : φ s = s)]
    have hcomm : θ s * d = d * θ s := by
      calc θ s * d = (d * θ s * d⁻¹) * d := by rw [← h1]
        _ = d * θ s := inv_mul_cancel_right _ _
    exact Subgroup.mem_inf.2
      ⟨MonoidHom.mem_range.2 ⟨s, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
  · intro x hx
    obtain ⟨hr, hc⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hr
    have hcomm : θ s * d = d * θ s := Subgroup.mem_centralizer_singleton_iff.1 hc
    refine Subgroup.mem_map.2 ⟨s, mem_ggFix.2 (hθ ?_), rfl⟩
    rw [hd s, ← hcomm, mul_inv_cancel_right]

private theorem map_ggFix_eq_subgroupOf {R G : Type*} [Group R] [Group G] {C : Subgroup G}
    (e : R ≃* ↥C) (φ : MulAut R) (d : G)
    (hd : ∀ r, ((e (φ r) : ↥C) : G) = d * (e r : G) * d⁻¹) :
    (ggFix φ).map e.toMonoidHom = (Subgroup.centralizer {d}).subgroupOf C := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨r, hr, rfl⟩
    have h1 := hd r
    rw [(mem_ggFix.1 hr : φ r = r)] at h1
    show (e r : G) * d = d * (e r : G)
    calc (e r : G) * d = (d * (e r : G) * d⁻¹) * d := by rw [← h1]
      _ = d * (e r : G) := inv_mul_cancel_right _ _
  · intro hx
    refine ⟨e.symm x, mem_ggFix.2 (e.injective (Subtype.ext ?_)), by simp⟩
    rw [hd, MulEquiv.apply_symm_apply, ← hx, mul_inv_cancel_right]

theorem ggE6DepNonIsoProp_E6
    (K : Type) [Field K] [Finite K] (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (h3 : 3 ∣ 2 ^ n - 1) :
    GGE6DepNonIsoProp (TableBExc.RecipeGroup Tag.E6 K) (TableBExc.RecipeID Tag.E6 K) := by
  intro L' _ _ ψ A hTB hA Φ T w hM a ha
  have hK3 : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3
  obtain ⟨ζ, hζ, hζ1⟩ := e6Line_exists_cube_root_unit hK3
  have hζo : orderOf ζ = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hζ hζ1
  obtain ⟨g, κ, hg, hκinj, hκrange, hconj, hweyl, hsimple⟩ :=
    kgFrameE6_holds K n hn hK h3 ζ hζ hζo L' ψ A hTB hA
  have hF : KGAutFrame A κ := ⟨hA, hκinj, hκrange, hweyl, hsimple⟩
  obtain ⟨m, b, hb, hbκ⟩ := exists_conj_kappa_eq_ggE6IsoBase hF
    ((ggE6IsoPt_iff_of_kgAutFrame (kgAutFrame_of_model hM hA) hF a).1 ha)
  obtain ⟨hψ, hker, -, -, hAI, -, -, -⟩ := hTB
  obtain ⟨φ, -, hφ⟩ := hAI (b : MulAut L') b.2
  have hθ : ∀ r, kgThetaHom g (φ r) = rootDiagUnit Tag.E6 (e6LineChar ζ) * kgThetaHom g r *
      (rootDiagUnit Tag.E6 (e6LineChar ζ))⁻¹ := by
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    have h := kgThetaHom_conj g ψ
      (fun a => rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (κ a)))) hconj b l
    have hbκ' : (Multiplicative.toAdd (κ b) : Fin Tag.E6.rank → ZMod 3) = ggE6IsoBase := hbκ
    rw [hbκ', zetaVec_ggE6IsoBase] at h
    rw [hφ l]
    exact h
  have hmap : (ggFix φ).map (kgThetaHom g) = toralCentralizer Tag.E6 K (e6LineChar ζ) := by
    rw [map_ggFix_eq _ (kgThetaHom_injective g) φ _ hθ, kgThetaHom_range g hg]
    rfl
  have hC : NoSingleComp (toralCentralizer Tag.E6 K (e6LineChar ζ)) := by
    intro J _
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    have hne : e6LineFactor K 0 ≠ e6LineFactor K 1 := fun h => h01 (e6LineFactor_injective hK3 h)
    by_cases h0 : e6LineFactor K 0 = J
    · exact ⟨_, kgAdjNonIso hζ hζ1 1, fun h1 => hne (h0.trans h1.symm)⟩
    · exact ⟨_, kgAdjNonIso hζ hζ1 0, h0⟩
  have hb' : NoSingleComp (ggFix (b : MulAut L')) :=
    noSingleComp_of_cover hψ hker hφ
      (noSingleComp_of_map _ (kgThetaHom_injective g) (by rw [hmap]; exact hC))
  rw [hb, ggFix_conj] at hb'
  exact noSingleComp_of_map _ (MulAut.conj m).injective hb'

theorem ggE6DepNonIsoProp_twE6
    (n : ℕ) (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    GGE6DepNonIsoProp (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  intro L' _ _ ψ A hTB hA Φ T w hM a ha
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hinj : Function.Injective (iterateFrobenius K 2 n) := (iterateFrobenius K 2 n).injective
  let σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  let Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) 2 n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨ζ, hζ, hζo⟩ := CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.exists_cube_root
    (Ω := AlgebraicClosure K)
    (CFSG.HardMathSupport.Lang.E6Descent.three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3)
  have hζ1 : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζo
    exact absurd hζo (by decide)
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  obtain ⟨v, g, κ, t, hF⟩ :=
    ggTwKGFrame_holds n hn h3 K hK σ hσ ε hε Fr hFr ζ hζ hζo L' ψ A hTB hA
  obtain ⟨m, b, hb, hbκ⟩ := exists_conj_kappa_eq_ggE6IsoBase hF.aut
    ((ggE6IsoPt_iff_of_kgAutFrame (kgAutFrame_of_model hM hA) hF.aut a).1 ha)
  obtain ⟨hψ, hker, -, -, hAI, -, -, -⟩ := hTB
  obtain ⟨φ, -, hφ⟩ := hAI (b : MulAut L') b.2
  have hd : ∀ r, ((ε.symm (φ r) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
      t ggE6IsoBase * (ε.symm r : ModGL TwistTag.E6.tag K) * (t ggE6IsoBase)⁻¹ := by
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    rw [hφ l, hF.conj b l, hbκ]
  have ht' : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (t ggE6IsoBase) * g =
      rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ ggE6IsoBase) := by
    rw [(hF.ht ggE6IsoBase).2]
    group
  have hC : NoSingleComp ((Subgroup.centralizer ({t ggE6IsoBase} :
      Set (ModGL TwistTag.E6.tag K))).subgroupOf (twistedE6RootGroup K σ)) :=
    kgTwAdjNonIso n hn h3 K σ hK hσ Fr hFr v hF.hv g hF.hg hF.hgF ζ hζ hζ1 (t ggE6IsoBase)
      (hF.ht ggE6IsoBase).1 ht'
  have hb' : NoSingleComp (ggFix (b : MulAut L')) :=
    noSingleComp_of_cover hψ hker hφ (noSingleComp_of_map _ ε.symm.injective
      (by rw [map_ggFix_eq_subgroupOf ε.symm φ (t ggE6IsoBase) hd]; exact hC))
  rw [hb, ggFix_conj] at hb'
  exact noSingleComp_of_map _ (MulAut.conj m).injective hb'

end CFSG.StandardType.KGL

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggE6DepNonIsoPt_holds :
    GGE6DepNonIsoPt := by
  intro lab hlab hΛ
  rcases hlab with ⟨htag, h3⟩ | ⟨htag, h3⟩
  · have key := largeEvenLabelAll_e6Div_of (P := fun R _ I => GGE6DepNonIsoProp R I) htag hΛ h3
      (fun K _ _ n hn hK h3' => KGL.ggE6DepNonIsoProp_E6 K n hn hK h3')
    exact LargeEvenLabelAll.mono (fun R _ I F h _ _ => h.2) key
  · exact TwE6Delta.labelAll htag
      (Q := fun R _ I => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGE6DepNonIsoProp R I)
      (fun K _ _ hK _ _ => KGL.ggE6DepNonIsoProp_twE6 lab.n hΛ.1 h3 K hK)

end CFSG.StandardType

end
