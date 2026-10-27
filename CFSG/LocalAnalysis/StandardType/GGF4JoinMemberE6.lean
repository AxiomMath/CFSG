module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinF4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExcCore
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
public import CFSG.LocalAnalysis.StandardType.GGLangComponentLabel
public import CFSG.LocalAnalysis.StandardType.GGSelectedModelOfChevalley
public import CFSG.LocalAnalysis.StandardType.GGRankOneModel
public import CFSG.LocalAnalysis.StandardType.GGSelectedRootPair
public import CFSG.LocalAnalysis.StandardType.GGSelectedPOmegaMinusLongField
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExcOrbit
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFam
import CFSG.LocalAnalysis.StandardType.ExcPos.TwistedE6Factors
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusExcOrbit
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcLang
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
import CFSG.Quasithin.Background.SmithC27RTypeGen
import CFSG.LocalAnalysis.StandardType.GGRankOneTorus
import CFSG.LocalAnalysis.StandardType.GGRankOneSl2
import CFSG.LocalAnalysis.StandardType.GGRankOneTagsA
import CFSG.LocalAnalysis.StandardType.GGRankOneTagsE
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLCores
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
import CFSG.ClassicalInvolution.ModelFacts.Families
import CFSG.LieType.Universal.Spin.Roots.TypeD
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTags
import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc

public section

namespace CFSG.StandardType.F4JoinE6

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
  CFSG.LieType.AlgebraicGroups CFSG.StandardType.LieKnownR2.ExcPos CFSG.StandardType.TableCRes
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem _root_.CFSG.StandardType.GuardedLargeEvenLabel.of_labelIso {c lab : LargeEvenLabel}
    (hc : GuardedLargeEvenLabel c) (hi : GGLabelIso c lab) : GuardedLargeEvenLabel lab := by
  obtain ⟨tc, rc, nc⟩ := c
  obtain ⟨tl, rl, nl⟩ := lab
  unfold GuardedLargeEvenLabel at hc ⊢
  unfold GGLabelIso at hi
  simp only [LargeEvenLabel.mk.injEq] at hc hi ⊢
  rcases hi with ⟨rfl, rfl, rfl⟩ | ⟨htc, htl, hr, -⟩ | ⟨⟨rfl, rfl, -⟩, -⟩ | ⟨⟨rfl, rfl, -⟩, -⟩ |
      ⟨⟨rfl, rfl, -⟩, -⟩ | ⟨⟨rfl, rfl, -⟩, -⟩ | ⟨⟨rfl, rfl, -⟩, -⟩ | ⟨-, rfl, rfl, -⟩
  · exact hc
  · subst hr
    rcases htc with rfl | rfl <;> rcases htl with rfl | rfl <;> simp_all
  all_goals simp at hc

theorem componentLabel_guarded {r N m : ℕ} {k : TwistKind} (hADE : N = r * (r + 1) ∨ 4 ≤ r)
    (hg : GuardedLargeEvenLabel (componentLabel r N k m)) :
    4 ≤ r ∧ k ≠ .suN ∧ (k = .exc → r = 6) := by
  cases k with
  | inner =>
    refine ⟨?_, by simp, by simp⟩
    simp only [componentLabel] at hg
    split_ifs at hg with hA hD h6 h7
    · simp [GuardedLargeEvenLabel] at hg
      omega
    · simp [GuardedLargeEvenLabel] at hg
      omega
    · omega
    · omega
    · exact hADE.resolve_left hA
  | suN => simp [componentLabel, GuardedLargeEvenLabel] at hg
  | twoD =>
    simp [componentLabel, GuardedLargeEvenLabel] at hg
    exact ⟨hg, by simp, by simp⟩
  | exc =>
    simp only [componentLabel] at hg
    split_ifs at hg with h6
    · exact ⟨by omega, by simp, fun _ => h6⟩
    · simp [GuardedLargeEvenLabel] at hg

theorem nonempty_quotCenter_mulEquiv_of_map {X H : Type*} [Group X] [Group H] {G₀ L : Subgroup X}
    (η : ↥G₀ →* H) (hker : η.ker ≤ Subgroup.center ↥G₀) (hLG0 : L ≤ G₀)
    (hperf : commutator ↥L = ⊤) {R : Subgroup H} (hL : (L.subgroupOf G₀).map η = R) :
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* ↥R ⧸ Subgroup.center ↥R) := by
  have : Group.IsPerfect ↥L := ⟨hperf⟩
  have hmem : ∀ l : ↥L, η (Subgroup.inclusion hLG0 l) ∈ R := fun l =>
    hL ▸ Subgroup.mem_map.2 ⟨Subgroup.inclusion hLG0 l, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
  let π : ↥L →* ↥R := (η.comp (Subgroup.inclusion hLG0)).codRestrict R hmem
  have hπ : Function.Surjective π := by
    rintro ⟨r, hr⟩
    rw [← hL] at hr
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hr
    exact ⟨⟨g, Subgroup.mem_subgroupOf.1 hg⟩, rfl⟩
  have hπker : π.ker ≤ Subgroup.center ↥L := by
    intro l hl
    have hl' : Subgroup.inclusion hLG0 l ∈ η.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val (MonoidHom.mem_ker.1 hl)
    have hz := hker hl'
    refine Subgroup.mem_center_iff.2 fun l' => Subgroup.inclusion_injective hLG0 ?_
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hz (Subgroup.inclusion hLG0 l')
  exact ⟨CFSG.Quasithin.SmithC27.quotCenterEquivOfSurjective π hπ hπker⟩

section Shape

theorem shape_of_guarded {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7) {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin τ.rank → GGLˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ j, a j ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) {Y : Type} [Group Y]
    (hmark : LargeEvenMarking Y (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab))
    (e : Y ⧸ Subgroup.center Y ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
      4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      twistKindOf S.ρ (componentRoots (rootCharHom a) i) ≠ .suN ∧
      (twistKindOf S.ρ (componentRoots (rootCharHom a) i) = .exc →
        compRank (componentRoots (rootCharHom a) i) = 6) := by
  have hτ3 : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by rcases hτ with rfl | rfl <;> simp
  have hτ4 : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by rcases hτ with rfl | rfl <;> simp
  have hrk : τ.rank ≤ 7 := by rcases hτ with rfl | rfl <;> decide
  obtain ⟨-, c, hc, hraw⟩ := hmark
  have hgc : GuardedLargeEvenLabel c := by
    obtain ⟨R, _, I, F, -, -, -, h⟩ := largeEvenRawDatum_exists hraw
    exact h
  have hhasc : GGHasLabel c (Y ⧸ Subgroup.center Y) :=
    largeEvenRawDatum_mono (fun _ _ _ _ h => by obtain ⟨-, -, θ, -⟩ := h; exact ⟨θ⟩) hraw
  obtain ⟨m, -, hΛ, -, hhas, -⟩ :=
    LangComponentLabel.exists_componentLabel_rationalComponent hτ3 S hp hp2 hT hap i hq
  have hi := ggLabelRigidInput_holds c _ _ hc hΛ hhasc (ggHasLabel_of_mulEquiv e.symm hhas)
  have hne : (componentRoots (rootCharHom a) i).Nonempty := by
    obtain ⟨b, hb⟩ := Quotient.exists_rep i
    exact ⟨b.1, b.2, hb⟩
  have hADE : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1) ∨
      4 ≤ compRank (componentRoots (rootCharHom a) i) := by
    rcases compRank_ncard_ade hτ4 (isRootComponent_componentRoots i) hne with
      h1 | ⟨-, hA⟩ | ⟨h4, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩
    · left
      rw [FieldTwoExc.ncard_eq_two_of_compRank_eq_one hτ4
        (isRootComponent_componentRoots i) h1, h1]
    · exact Or.inl hA
    · exact Or.inr h4
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  obtain ⟨h4, hsu, hexc⟩ := componentLabel_guarded hADE (hgc.of_labelIso hi)
  refine ⟨?_, h4, hsu, hexc⟩
  have hsr := LangRat.componentOrbitLength_mul_compRank_le S hT i
  have hs0 := (outer_componentOrbitLength_spec S hT i).1
  replace hsr := hsr.trans hrk
  by_contra hne1
  have h2 : 2 ≤ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by omega
  have := Nat.mul_le_mul h2 h4
  omega

end Shape

theorem le_of_sup_eq_of_mul_self_eq_one {G : Type*} [Group G] {A A' Z : Subgroup G}
    (hA : ∀ a ∈ A, a * a = 1) (hA' : ∀ a ∈ A', a * a = 1)
    (hZA' : ∀ z ∈ Z, ∀ a ∈ A', z * a = a * z) (hZ : ∀ z ∈ Z, z * z = 1 → z = 1)
    (h : A ⊔ Z = A' ⊔ Z) : A ≤ A' := by
  intro a ha
  have hN : A' ≤ Subgroup.normalizer (Z : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [← hZA' z hz b hb, mul_inv_cancel_right]
      exact hz
    · intro hz
      have hc := hZA' _ hz b hb
      have hzw : z = b * z * b⁻¹ := by
        calc z = b⁻¹ * ((b * z * b⁻¹) * b) := by group
          _ = b⁻¹ * (b * (b * z * b⁻¹)) := by rw [hc]
          _ = b * z * b⁻¹ := by group
      rw [hzw]
      exact hz
  have hmem : a ∈ ((A' ⊔ Z : Subgroup G) : Set G) := by
    rw [SetLike.mem_coe, ← h]
    exact Subgroup.mem_sup_left ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A' Z hN] at hmem
  obtain ⟨b, hb, z, hz, rfl⟩ := Set.mem_mul.1 hmem
  have hzz : z * z = 1 := by
    have hc := hZA' z hz b hb
    calc z * z = b * b * (z * z) := by rw [hA' b hb, one_mul]
      _ = b * z * (b * z) := by
        rw [show b * z * (b * z) = b * (z * b) * z by group, hc]
        group
      _ = 1 := hA _ ha
  rw [hZ z hz hzz, mul_one]
  exact hb

theorem eq_of_sup_eq_of_mul_self_eq_one {G : Type*} [Group G] {A A' Z : Subgroup G}
    (hA : ∀ a ∈ A, a * a = 1) (hA' : ∀ a ∈ A', a * a = 1)
    (hZA : ∀ z ∈ Z, ∀ a ∈ A, z * a = a * z) (hZA' : ∀ z ∈ Z, ∀ a ∈ A', z * a = a * z)
    (hZ : ∀ z ∈ Z, z * z = 1 → z = 1) (h : A ⊔ Z = A' ⊔ Z) : A = A' :=
  le_antisymm (le_of_sup_eq_of_mul_self_eq_one hA hA' hZA' hZ h)
    (le_of_sup_eq_of_mul_self_eq_one hA' hA hZA hZ h.symm)

section Models

open CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.StandardType.RankOneXfer
  CFSG.StandardType.SelectedRoot

theorem _root_.CFSG.StandardType.SelectedRoot.SelectedSL2Model.mul_self_eq_one_of_mem
    {K k : Type*} [Group K] [Field k] [CharP k 2] {D : UniversalRootDatum K}
    {γ : Fin D.rank → ℤ} (model : SelectedSL2Model D k γ) {z : K} (hz : z ∈ D.rootGroup γ) :
    z * z = 1 := by
  rw [← model.upper_eq] at hz
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.1 hz
  obtain ⟨t, rfl⟩ := mem_sl2UpperUniSub_iff.1 hA
  rw [← map_mul, sl2Upper_mul_sl2Upper, CharTwo.add_self_eq_zero]
  convert map_one model.phi
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2Upper]

theorem _root_.CFSG.StandardType.SelectedRoot.SelectedSL2Model.mul_self_eq_one_of_mem_neg
    {K k : Type*} [Group K] [Field k] [CharP k 2] {D : UniversalRootDatum K}
    {γ : Fin D.rank → ℤ} (model : SelectedSL2Model D k γ)
    (hlow : Set.range (fun t : k => model.phi (sl2Lower t)) = (D.rootGroup (-γ) : Set K))
    {z : K} (hz : z ∈ D.rootGroup (-γ)) : z * z = 1 := by
  rw [← SetLike.mem_coe, ← hlow] at hz
  obtain ⟨t, rfl⟩ := hz
  rw [← map_mul]
  convert map_one model.phi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_sl2Lower, CharTwo.add_self_eq_zero]

theorem _root_.CFSG.StandardType.SelectedRoot.SelectedSL2Model.range_eq_sup
    {K k : Type*} [Group K] [Field k] {D : UniversalRootDatum K} {γ : Fin D.rank → ℤ}
    (model : SelectedSL2Model D k γ)
    (hlow : Set.range (fun t : k => model.phi (sl2Lower t)) = (D.rootGroup (-γ) : Set K)) :
    model.phi.range = D.rootGroup γ ⊔ D.rootGroup (-γ) :=
  SelectedSL2Model.ofRootMap_range D γ model.root_mem model.phi model.injective model.upper_eq
    model.diag_mem (fun h hh => by obtain ⟨c, hc⟩ := model.scalar h hh; exact ⟨c, hc⟩) hlow

theorem exists_model_lower_of_rankOneModel {K k : Type} [Group K] [Field k]
    {D : UniversalRootDatum K} (hM : GGRankOneModel D k) (i : Fin D.rank) :
    ∃ model : SelectedSL2Model D k (Pi.single i 1),
      Set.range (fun t : k => model.phi (sl2Lower t)) = (D.rootGroup (-Pi.single i 1) : Set K) := by
  obtain ⟨x, C, O, hE, hlin⟩ := hM
  obtain ⟨phi, hinj, hupper, hlower⟩ := hE.rankOne i
  have hup : (sl2UpperUniSub k).map phi = D.rootGroup (Pi.single i 1) := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨c, rfl⟩ := mem_sl2UpperUniSub_iff.mp ha
      rw [hupper c]
      exact ((hE.param (Pi.single i 1) (single_mem_roots i)).1 _).mpr ⟨c, rfl⟩
    · intro hz
      obtain ⟨c, hc⟩ := ((hE.param (Pi.single i 1) (single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Upper c, mem_sl2UpperUniSub_iff.mpr ⟨c, rfl⟩, (hupper c).trans hc⟩
  have hscalar : ∀ h ∈ ggTorus D, ∃ c : k, ∀ t : k,
      h * phi (sl2Upper t) * h⁻¹ = phi (sl2Upper (c * t)) := by
    intro h hh
    obtain ⟨c, hc⟩ := hlin h hh i
    exact ⟨c, fun t => by simpa only [hupper] using hc t⟩
  refine ⟨SelectedSL2Model.ofRootMap D (Pi.single i 1) (single_mem_roots i) phi hinj hup
    (fun a => map_sl2Diag_mem_ggTorus hE i phi hupper hlower a) hscalar, ?_⟩
  change Set.range (fun t : k => phi (sl2Lower t)) = _
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    show phi (sl2Lower t) ∈ D.rootGroup (-Pi.single i 1)
    rw [hlower t]
    exact ((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 _).mpr ⟨t, rfl⟩
  · intro hz
    obtain ⟨c, hc⟩ := ((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 z).mp hz
    exact ⟨c, (hlower c).trans hc⟩

end Models

section Member

open CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.StandardType.RankOneXfer
  CFSG.StandardType.SelectedRoot

theorem exists_memberModel {τ : Tag} (hτ : τ = .E6) {p₀ : ℕ} {S : LangSetup τ GGL p₀}
    {a : Fin τ.rank → GGLˣ} {i : KernelComponent (rootCharHom a)} {M : LieUniversal} {f : ℕ}
    (hf : 1 ≤ f) (hM : CarrierModel S a i M f)
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hsu : twistKindOf S.ρ (componentRoots (rootCharHom a) i) ≠ .suN)
    (hexc : twistKindOf S.ρ (componentRoots (rootCharHom a) i) = .exc →
      compRank (componentRoots (rootCharHom a) i) = 6)
    (h1 : rootDiagUnit τ a ≠ 1) (h6 : compRank (componentRoots (rootCharHom a) i) ≤ 6) :
    ∃ (t' : StatedLieTag) (n' : ℕ), M = ggU t' n' f ∧ StatedLieAdmissible t' n' 2 f ∧
      2 ≤ (ggU t' n' f).D.rank ∧ ∃ δ ∈ (ggU t' n' f).D.roots, GGLongRoot (ggU t' n' f).D δ ∧
        ∃ model : SelectedSL2Model (ggU t' n' f).D (GaloisField 2 f) δ,
          model.phi.range = ggRootLevi (ggU t' n' f).D δ ∧
          Set.range (fun t : GaloisField 2 f => model.phi (sl2Lower t)) =
            ((ggU t' n' f).D.rootGroup (-δ) : Set (ggU t' n' f).K) := by
  subst hτ
  unfold CarrierModel at hM
  rcases hM with ⟨hr1, -⟩ | ⟨-, hr2, -, rfl⟩ | ⟨hk, -⟩ | ⟨-, hr4, -, rfl⟩ | ⟨hk, rfl⟩ |
    ⟨-, hE⟩ | ⟨hk, -⟩
  · omega
  ·
    have hadm : StatedLieAdmissible .PSL (compRank (componentRoots (rootCharHom a) i) + 1) 2 f :=
      ⟨Nat.prime_two, hf, by omega, fun h => by have := (Prod.mk.inj h).1; omega,
        fun h => by have := (Prod.mk.inj h).1; omega⟩
    have hrank : 3 ≤ bnRank .PSL (compRank (componentRoots (rootCharHom a) i) + 1) := by
      simp only [bnRank]
      omega
    obtain ⟨model, hlow⟩ := exists_model_lower_of_rankOneModel
      (ggRankOneModel_PSL hadm hrank)
      (⟨0, by change 0 < compRank (componentRoots (rootCharHom a) i); omega⟩)
    exact ⟨.PSL, _, rfl, hadm, (show 2 ≤ compRank (componentRoots (rootCharHom a) i) by omega), _,
      model.root_mem, LieKnownR2.PSL.ggLongRoot_of_mem_roots (by omega) model.root_mem, model,
      model.range_eq_sup hlow, hlow⟩
  · exact absurd hk hsu
  ·
    obtain ⟨m, hm⟩ : ∃ m, compRank (componentRoots (rootCharHom a) i) = m + 4 :=
      ⟨_, (Nat.sub_add_cancel hr4).symm⟩
    rw [hm]
    have hn3 : 3 ≤ m + 4 := by omega
    have hadm : StatedLieAdmissible .POmegaPlus (m + 4) 2 f := ⟨Nat.prime_two, hf, by omega⟩
    have hrank : 3 ≤ bnRank .POmegaPlus (m + 4) := by
      simp only [bnRank]
      omega
    obtain ⟨model, hlow⟩ := exists_model_lower_of_rankOneModel
      (ggRankOneModel_POmegaPlus hadm hrank) (⟨0, by change 0 < m + 4; omega⟩)
    have hlong : GGLongRoot (Spin.plusDatum (m + 4) (GaloisField 2 f) hn3)
        (Pi.single (⟨0, by omega⟩ : Fin (m + 4)) 1) :=
      ggLongRoot_of_symmetric (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanD hn3)
        (fun i j => by
          rw [show (Spin.plusDatum (m + 4) (GaloisField 2 f) hn3).cartan =
            Spin.cartanD (m + 4) from rfl, Spin.cartanD_eq]
          exact (CartanMatrix.D_isSymm (m + 4)).apply j i)
        rfl model.root_mem
    exact ⟨.POmegaPlus, m + 4, rfl, hadm, (show 2 ≤ m + 4 by omega), _, model.root_mem, hlong,
      model, model.range_eq_sup hlow, hlow⟩
  ·
    have h4' := FieldTwoExc.four_le_compRank_of_twoD hk
    obtain ⟨δ, hδ, hlong, model, hrange, hlow⟩ :=
      exists_selectedSL2Model_POmegaMinus_long_range (f := f) h4'
    exact ⟨.POmegaMinus, _, rfl, ⟨Nat.prime_two, hf, h4'⟩,
      (show 2 ≤ compRank (componentRoots (rootCharHom a) i) - 1 by omega), δ, hδ, hlong, model,
      hrange, hlow⟩
  ·
    exfalso
    rcases hE with ⟨-, h72, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩
    · exact h1 (rootDiagUnit_eq_one_of_ncard i (by rw [h72]; decide))
    · omega
    · omega
  ·
    exfalso
    rcases FieldTwoExc.exc_cases hk with ⟨-, h72⟩ | ⟨h4'', -⟩
    · exact h1 (rootDiagUnit_eq_one_of_ncard i (by rw [h72]; decide))
    · have := hexc hk
      omega

end Member

section Center

theorem odd_card_center_of_E6 {X : Type} [Group X] {G₀ : Subgroup X} {f : ℕ}
    {ψ : (ggU .E6 0 f).K →* X} (hψ : ψ.range = G₀)
    (hker : ψ.ker ≤ Subgroup.center (ggU .E6 0 f).K) : Odd (Nat.card (Subgroup.center ↥G₀)) := by
  have : Group.IsPerfect (ggU .E6 0 f).K :=
    (FieldTwoExc.isQuasisimple_exc (.inr (.inl rfl)) 0 f).1
  let ψ' : (ggU .E6 0 f).K →* ↥G₀ :=
    ψ.codRestrict G₀ (fun u => hψ ▸ MonoidHom.mem_range.2 ⟨u, rfl⟩)
  have hsurj : Function.Surjective ψ' := by
    rintro ⟨g, hg⟩
    rw [← hψ] at hg
    obtain ⟨u, rfl⟩ := hg
    exact ⟨u, rfl⟩
  have hker' : ψ'.ker ≤ Subgroup.center (ggU .E6 0 f).K := fun u hu => hker (by
    rw [MonoidHom.mem_ker] at hu ⊢
    exact congrArg Subtype.val hu)
  have hmap : Subgroup.center ↥G₀ = (Subgroup.center (ggU .E6 0 f).K).map ψ' := by
    rw [← CFSG.Quasithin.SmithC27.comap_center_eq_of_perfect ψ' hsurj hker',
      Subgroup.map_comap_eq_self_of_surjective hsurj]
  have h3 : Nat.card (Subgroup.center (ggU .E6 0 f).K) ∣ 3 := by
    change Nat.card (Subgroup.center
      ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField 2 f))) ∣ 3
    rw [(CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6
      (k := GaloisField 2 f)).1]
    exact Nat.gcd_dvd_left 3 _
  rw [hmap]
  exact (show Odd 3 by decide).of_dvd_nat ((Subgroup.card_map_dvd _ _).trans h3)

end Center

theorem eq_of_sup_center_eq {G : Type*} [Group G] {G₀ A A' : Subgroup G}
    (hZodd : Odd (Nat.card (Subgroup.center ↥G₀))) (hAG : A ≤ G₀) (hA'G : A' ≤ G₀)
    (hA : ∀ a ∈ A, a * a = 1) (hA' : ∀ a ∈ A', a * a = 1)
    (h : A ⊔ (Subgroup.center ↥G₀).map G₀.subtype = A' ⊔ (Subgroup.center ↥G₀).map G₀.subtype) :
    A = A' := by
  have hZc : ∀ z ∈ (Subgroup.center ↥G₀).map G₀.subtype, ∀ g ∈ G₀, z * g = g * z := by
    rintro _ ⟨z, hz, rfl⟩ g hg
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)).symm
  have hZ2 : ∀ z ∈ (Subgroup.center ↥G₀).map G₀.subtype, z * z = 1 → z = 1 := by
    rintro _ ⟨z, hz, rfl⟩ hzz
    have hz1 : z * z = 1 := Subtype.ext hzz
    have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz1)
    have hodd : Odd (orderOf z) := hZodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hz)
    have ho : orderOf z = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    rw [orderOf_eq_one_iff.1 ho, map_one]
  exact eq_of_sup_eq_of_mul_self_eq_one hA hA' (fun z hz a ha => hZc z hz a (hAG ha))
    (fun z hz a ha => hZc z hz a (hA'G ha)) hZ2 h

section Pairs

open CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.StandardType.RankOneXfer
  CFSG.StandardType.SelectedRoot

theorem mul_self_eq_one_of_mem_ggRootSub {G : Type} [Group G] {t : StatedLieTag} {n f : ℕ}
    (ψ : (ggU t n f).K →* G) (hW : GGHasWeylLift (ggU t n f).D)
    (hM : GGRankOneModel (ggU t n f).D (GaloisField 2 f)) (hdiv : (ggU t n f).D.divisible = ∅)
    {β : Fin (ggU t n f).D.rank → ℤ} (hβ : β ∈ (ggU t n f).D.roots) (k : (ggU t n f).K) :
    ∀ a ∈ ggRootSub (ggU t n f).D ψ β k, a * a = 1 := by
  obtain ⟨ν, hν⟩ := hW
  rcases hβ with ⟨w, i, rfl⟩ | ⟨-, i, hi, -⟩
  swap
  · rw [hdiv] at hi
    exact absurd hi (Set.notMem_empty i)
  have hi : (Pi.single i 1 : Fin (ggU t n f).D.rank → ℤ) ∈ (ggU t n f).D.roots :=
    Or.inl ⟨1, i, by simp⟩
  obtain ⟨model, -⟩ := exists_model_lower_of_rankOneModel hM i
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  rw [← map_rootGroup_conj_weylLift hν w hi] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [← map_mul]
  convert map_one ψ using 2
  calc k * (ν w * z * (ν w)⁻¹) * k⁻¹ * (k * (ν w * z * (ν w)⁻¹) * k⁻¹) =
        k * ν w * (z * z) * (ν w)⁻¹ * k⁻¹ := by group
    _ = 1 := by rw [model.mul_self_eq_one_of_mem hz]; group

end Pairs

section MemberSide

open CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.StandardType.RankOneXfer
  CFSG.StandardType.SelectedRoot

theorem exists_member_rootPair {t : StatedLieTag} (hτ : langTag t = .E6) {G : Type} [Group G]
    [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n f : ℕ} {ψ : (ggU t n f).K →* G}
    {G₀ L : Subgroup G} {x : G} (hψ : ψ.range = G₀) (hZodd : Odd (Nat.card (Subgroup.center ↥G₀)))
    (F : ExcLangFrame t n f p ψ G₀ (Subgroup.zpowers x) (Subgroup.zpowers x) x)
    (hstep : F.RootStep) (hLG0 : L ≤ G₀) (hf : 1 ≤ f)
    (hT : rootDiagUnit (langTag t) (F.coord x) ∈ F.setup.D.torus)
    (hap : ∀ j, F.coord x j ^ p = 1) (h1 : rootDiagUnit (langTag t) (F.coord x) ≠ 1)
    (i : KernelComponent (rootCharHom (F.coord x)))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i))
    (hL : (L.subgroupOf G₀).map F.η =
      rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i)
    (hmark : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab))
    (hexp : ∀ β ∈ (ggU t n f).D.roots, GGLongRoot (ggU t n f).D β → ∀ k : (ggU t n f).K,
      (∀ a ∈ ggRootSub (ggU t n f).D ψ β k, a * a = 1) ∧
        ∀ a ∈ ggRootSub (ggU t n f).D ψ (-β) k, a * a = 1) :
    ∃ S : Subgroup G, MemberSelectedSL2At L S ∧ ∃ β ∈ (ggU t n f).D.roots,
      GGLongRoot (ggU t n f).D β ∧ ∃ k : (ggU t n f).K,
        S = ggRootSub (ggU t n f).D ψ β k ⊔ ggRootSub (ggU t n f).D ψ (-β) k := by
  obtain ⟨eL⟩ := nonempty_quotCenter_mulEquiv_of_map F.η F.ker_η.le hLG0 hmark.1 hL
  obtain ⟨horb, h4, hsu, hexc⟩ := shape_of_guarded (Or.inl hτ) F.setup hp hp2 hT hap i hqs hmark eL
  have hsr := LangRat.componentOrbitLength_mul_compRank_le F.setup hT i
  rw [horb, one_mul] at hsr
  have hr6 : (langTag t).rank = 6 := by
    rw [hτ]
    rfl
  have h6 : compRank (componentRoots (rootCharHom (F.coord x)) i) ≤ 6 := by omega
  obtain ⟨Mu, α, hMod, -, hrange, hker, -, -, hpair⟩ :=
    F.exists_member_of_orbit_one_of_rootStep (Or.inr (Or.inl hτ)) hp hp2 hψ hZodd hmark.1 hstep
      hLG0 hT hap h1 i hqs hL horb
  obtain ⟨t', n', rfl, hadm', hrk', δ, hδ, hδl, model, hmodel, hlow⟩ :=
    exists_memberModel hτ hf hMod h4 hsu hexc h1 h6
  obtain ⟨β', hβ', hlong', k, hk₁, hk₂⟩ := hpair δ hδ hδl
  obtain ⟨hB₁, hB₂⟩ := hexp β' hβ' hlong' k
  have hαG : ∀ γ, ((ggU t' n' f).D.rootGroup γ).map α ≤ G₀ := by
    rintro γ _ ⟨m, -, rfl⟩
    exact hLG0 (hrange ▸ ⟨m, rfl⟩)
  have hψG : ∀ γ u, ggRootSub (ggU t n f).D ψ γ u ≤ G₀ := by
    rintro γ u _ ⟨y, -, rfl⟩
    rw [← hψ]
    exact ⟨y, rfl⟩
  have h₁ := eq_of_sup_center_eq hZodd (hαG δ) (hψG β' k)
    (by rintro _ ⟨m, hm, rfl⟩; rw [← map_mul, model.mul_self_eq_one_of_mem hm, map_one]) hB₁ hk₁
  have h₂ := eq_of_sup_center_eq hZodd (hαG (-δ)) (hψG (-β') k)
    (by rintro _ ⟨m, hm, rfl⟩; rw [← map_mul, model.mul_self_eq_one_of_mem_neg hlow hm, map_one])
    hB₂ hk₂
  refine ⟨_, memberSelectedSL2At_map_ggRootLevi α hadm' hrk' hker hrange model hmodel, β', hβ',
    hlong', k, ?_⟩
  rw [← h₁, ← h₂]
  exact Subgroup.map_sup _ _ _

end MemberSide

section Main

open CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.StandardType.RankOneXfer
  CFSG.StandardType.SelectedRoot

theorem _root_.CFSG.StandardType.ggActualMember_E6_selected
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ}
    (ψ : (ggU .E6 n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .E6 n f).D .E6 n f ψ)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At ψ S := by
  classical
  obtain rfl : n = 0 := hpres.1.1.2.2
  obtain ⟨hp, hp2, -⟩ := (hcfg.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hq : CFSG.Assembly.IsQuasisimple ↥X := isQuasisimple_of_largeEvenMarking hmark
  obtain ⟨z, hz, hzG, hzp, hXC⟩ := ggActualMember_internal_component hcfg horigin hq
  have hXc : CFSG.Assembly.IsComponentOf X (Subgroup.centralizer ({z} : Set G)) := by
    rcases hz with ⟨rfl, rfl⟩ | hNb
    · exact hcfg.1.2.2.2.2.2.2.1.2.2.2.1
    · exact ⟨hNb.1.2.2.2.2.1.1, hNb.1.2.2.2.2.1.2.1, hq⟩
  have hXG0 : X ≤ ggG0 p B x L D J := hXC.1.trans inf_le_left
  have hadm : StatedLieAdmissible .E6 0 2 f := hpres.1.1
  have hf : 1 ≤ f := hadm.2.1
  have ht4 : FieldTwoExc.GGExcFour .E6 := .inr (.inl rfl)
  have hdiag : GGPsiInnerDiag (ggU .E6 0 f).D ψ z :=
    ggPsiInnerDiag_of_mem_range _ (hpres.2.1.1 ▸ hzG)
  by_cases hnc : z ∈ Subgroup.centralizer (ggG0 p B x L D J : Set G)
  ·
    have hXe := FieldTwoExc.eq_ggG0_of_isComponentOf_of_exc_central ht4 ψ hpres hXC hnc
    have hrank : 3 ≤ bnRank .E6 0 := by
      simp only [bnRank]
      omega
    obtain ⟨modelU, -⟩ :=
      exists_model_lower_of_rankOneModel (ggRankOneModel_E6 hadm hrank) (0 : Fin 6)
    refine ⟨(ψ.comp modelU.phi).range, ⟨.E6, 0, f, ψ, hadm, hpres.1.2, hpres.2.1.2,
      hpres.2.1.1.trans hXe.symm, GaloisField 2 f, inferInstance, inferInstance, inferInstance,
      _, modelU, rfl⟩, GaloisField 2 f, inferInstance, inferInstance, inferInstance, _, modelU, 1,
      ?_⟩
    have hconj : ψ.comp (MulAut.conj (1 : (ggU .E6 0 f).K)).toMonoidHom = ψ := by
      ext g
      simp
    rw [hconj]
  obtain ⟨F⟩ := FieldTwoExc.nonempty_excLangFrame_zpowers (Or.inl rfl) hp hp2 hpres hdiag hzp
  have hN : Subgroup.zpowers z ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
    Subgroup.zpowers_le.mpr (FieldTwoExc.ggPsiInnerDiag_mem_normalizer_exc ht4 hpres hdiag)
  obtain ⟨hT, hap, h1, i, hqs, hL⟩ :=
    F.exists_class_of_noncentral (Or.inl rfl) hp hp2 hN hXG0 hXc hnc
  have hrank : 3 ≤ bnRank .E6 0 := by
    simp only [bnRank]
    omega
  have hW : GGHasWeylLift (ggU .E6 0 f).D := (ggTagFacts_of_admissible hadm hrank).2.1
  have hRM : GGRankOneModel (ggU .E6 0 f).D (GaloisField 2 f) := ggRankOneModel_E6 hadm hrank
  obtain ⟨S, hS, β, hβ, -, k, rfl⟩ :=
    exists_member_rootPair rfl hp hp2 hpres.2.1.1 (odd_card_center_of_E6 hpres.2.1.1 hpres.2.1.2)
      F (F.rootStep_of_exc (Or.inl rfl) hpres.2.1.1) hXG0 hf hT hap h1 i hqs hL hmark
      (fun β hβ _ k => ⟨mul_self_eq_one_of_mem_ggRootSub ψ hW hRM rfl hβ k,
        mul_self_eq_one_of_mem_ggRootSub ψ hW hRM rfl
          (CFSG.LieType.Steinberg.OfCartan.neg_mem_roots _ hβ) k⟩)
  exact ⟨_, hS, presentedSelectedSL2At_ggRootSub ψ hW hRM rfl hβ k⟩

end Main

end CFSG.StandardType.F4JoinE6

end
