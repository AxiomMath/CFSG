module

public import CFSG.LocalAnalysis.StandardType.GGRCLinRefl
public import CFSG.LocalAnalysis.StandardType.ZS.Basic
public import CFSG.LocalAnalysis.StandardType.ZS.MarkedWeyl
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE8Split
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA
public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoNorm

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly
open scoped IsMulCommutative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem not_ggIsReflection_of_mem_perfect {G : Type} [Group G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {E : Subgroup G} [Finite E]
    (hE : IsElemAbelian p E) {W : Subgroup (MulAut E)} [Group.IsPerfect W]
    {r : MulAut E} (hrW : r ∈ W) : ¬ GGIsReflection p r := by
  classical
  let := hE.isElementaryAbelian
  let V := Additive E
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let delta : W →* (ZMod p)ˣ :=
    LinearEquiv.det.comp ((ggLin (p := p) (AddEquiv.refl V)).comp W.subtype)
  have : Group.IsPerfect delta.range := Group.IsPerfect.range delta
  have : Subsingleton delta.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  have hdet : LinearEquiv.det (ggLin (p := p) (AddEquiv.refl V) r) = 1 := by
    have he : (⟨delta ⟨r, hrW⟩, ⟨r, hrW⟩, rfl⟩ : delta.range) = 1 :=
      Subsingleton.elim _ _
    exact congrArg Subtype.val he
  intro hr
  have hlin : ZS.IsRefl p (ggLin (p := p) (AddEquiv.refl V) r) :=
    (ggRC_isReflection_iff_linRefl (AddEquiv.refl V) r).mp hr
  have hn := ZS.det_eq_neg_one_of_isRefl hp2 hlin
  have he : (-1 : (ZMod p)ˣ) = 1 := hn.symm.trans hdet
  have he' : (-1 : ZMod p) = 1 := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) he
  have hz : (2 : ZMod p) = 0 := by
    have := congrArg (fun x : ZMod p => x + 1) he'
    calc (2 : ZMod p) = 1 + 1 := by norm_num
      _ = 0 := by simpa only [neg_add_cancel] using this.symm
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
    ((ZMod.natCast_eq_zero_iff 2 p).mp hz))

theorem not_ggIsReflection_of_mem_ggAutomizer_of_perfect_normalizer_image
    {R G H : Type} [Group R] [Group G] [Group H] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (E : Subgroup R) [Finite E]
    (hE : IsElemAbelian p E) (rho : R →* G) (hRho : Function.Injective rho)
    (A : Subgroup G) (hEA : E.map rho = A) (f : R →* H)
    (hf : Function.Injective f)
    [Group.IsPerfect ↥((E.map f).normalizerMonoidHom.range)]
    {r : MulAut A} (hr : r ∈ ggAutomizer rho.range A) :
    ¬ GGIsReflection p r := by
  classical
  let ε : E ≃* A := (E.equivMapOfInjective rho hRho).trans
    (MulEquiv.subgroupCongr hEA)
  let η : E ≃* E.map f := (E.equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr (rfl : E.map f = E.map f))
  have hmap : ggAutomizer rho.range A =
      (ggAutomizer (⊤ : Subgroup R) E).map (MulAut.congr ε).toMonoidHom := by
    rw [MonoidHom.range_eq_map]
    exact F4AutWeyl.ggAutomizer_map_eq hRho (⊤ : Subgroup R) E hEA
  rw [hmap] at hr
  obtain ⟨r₀, hr₀, heq⟩ := hr
  change MulAut.congr ε r₀ = r at heq
  have hη : MulAut.congr η r₀ ∈ ggAutomizer f.range (E.map f) := by
    rw [MonoidHom.range_eq_map,
      F4AutWeyl.ggAutomizer_map_eq hf (⊤ : Subgroup R) E rfl]
    exact ⟨r₀, hr₀, rfl⟩
  obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp hη
  have hrange : MulAut.congr η r₀ ∈ (E.map f).normalizerMonoidHom.range := by
    refine ⟨⟨g, hgN⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
    exact (hg x).symm
  have : Finite (E.map f) := Finite.of_surjective η η.surjective
  have hEf : IsElemAbelian p (E.map f) := TableB.isElemAbelian_map hE f
  intro hrefl
  have hr₀refl : GGIsReflection p r₀ :=
    (F4AutRefl.ggIsReflection_congr_iff ε r₀).mp (by
      simpa only [heq] using hrefl)
  have hηrefl := (F4AutRefl.ggIsReflection_congr_iff η r₀).mpr hr₀refl
  exact not_ggIsReflection_of_mem_perfect hp2 hEf hrange hηrefl

namespace E8WNorm

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.StandardType.TableBExc CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggTorusWNormSC_recipe_E8_five_split {K : Type} [Field K] [Finite K]
    [CharP K 2] (hpq : 5 ∣ Nat.card K - 1) :
    GGTorusWNormSC 5 (RecipeGroup .E8 K) (RecipeID .E8 K) := by

  classical
  let p : ℕ := 5
  have hp : p.Prime := Nat.prime_five
  intro L _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Γ _ _ M C V _ _ ι' φ h α
    hMw hMC hpair hlin hgen s hs
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by decide
  have hIp : GGOutdiagPrime p (RecipeGroup .E8 K) (RecipeID .E8 K) := by
    intro φ hφ _
    obtain ⟨x, rfl⟩ := idImage_subset_inn_E8 K hφ
    exact ⟨x, rfl⟩
  obtain ⟨Λ₀, hΛeq, hΛinj, _, hAΛ, hE, hAcard, hEsc⟩ :=
    TwE6TB.exists_innerModel hp (center_recipeGroup_eq_bot .E8 K) hIp
      (ExcSplitL.ggCenterPrime_recipe_E8 hp hp2) ψ hψ hker hperf hA hAI hsc
  let ε := recipeEquiv .E8 K
  let E := (A.comap Λ₀).map ε.toMonoidHom
  have hEg : IsElemAbelian p E := TableB.isElemAbelian_map hE _
  have hEgs : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    have hg' : ε.symm g ∈ A.comap Λ₀ := by
      apply hEsc
      · intro e he
        apply ε.injective
        rw [map_mul, map_mul, ε.apply_symm_apply]
        exact hg (ε e) (Subgroup.mem_map_of_mem _ he)
      · rw [← map_pow, hgp, map_one]
    exact ⟨ε.symm g, hg', ε.apply_symm_apply g⟩
  let Ω := AlgebraicClosure K
  let ιK : K →+* Ω := algebraMap K Ω
  have : CharP Ω 2 := charP_of_injective_algebraMap ιK.injective _
  let f : RecipeGroup .E8 K →* adjointGroup .E8 Ω :=
    (adjointBaseChangeHom .E8 ιK).comp ε.toMonoidHom
  have hf : Function.Injective f :=
    (adjointBaseChangeHom_injective .E8 ιK).comp ε.injective
  have : Finite (A.comap Λ₀) := Nat.finite_of_card_ne_zero (by
    rw [hAcard]
    exact (Nat.card_pos (α := A)).ne')
  let H := (A.comap Λ₀).map f
  have : Finite H := Finite.of_surjective
    ((A.comap Λ₀).equivMapOfInjective f hf)
    ((A.comap Λ₀).equivMapOfInjective f hf).surjective
  have hH : IsElemAbelian 5 H := TableB.isElemAbelian_map hE f
  have hHcard : 125 ≤ Nat.card H := by
    rw [show Nat.card H = Nat.card (A.comap Λ₀) from
      Subgroup.card_map_of_injective hf, hAcard]
    exact h3
  have hEA₀ : (A.comap Λ₀).map Λ₀ = A := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx
    · intro a ha
      obtain ⟨x, hx⟩ := hAΛ a ha
      exact ⟨x, show Λ₀ x ∈ A by rw [hx]; exact ha, hx⟩
  have hΛr : Λ₀.range = (MulAut.conj : L →* MulAut L).range := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨l, rfl⟩ := hψ x
      exact ⟨l, (hΛeq rfl).symm⟩
    · rintro ⟨l, rfl⟩
      exact ⟨ψ l, hΛeq rfl⟩
  have hTor : ExcFramesHalf.IsToralSubgroup .E8 Ω
      (H.map (adjointGroup .E8 Ω).subtype) := by
    by_contra hNT
    have : Group.IsPerfect H.normalizerMonoidHom.range :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five.universal_nonToral_normalizer_isPerfect
        H hH hNT hHcard
    let i : Γ := Classical.choice (l05nBL_nonempty hMw)
    have hi : φ i ∈ ggAutomizer Λ₀.range A := by
      rw [hΛr, hgen]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    have hno := not_ggIsReflection_of_mem_ggAutomizer_of_perfect_normalizer_image
      hp2 (A.comap Λ₀) hE Λ₀ hΛinj A hEA₀ f hf hi
    have hα : α i (h i) = (2 : ZMod p) := by
      rw [hpair, hMC.1]
      norm_num
    have hrefl : GGIsReflection p (φ i) :=
      (ggRC_isReflection_iff_linRefl ι' (φ i)).mpr
        (ZS.isRefl_of_apply_eq hp2 hα (hlin i))
    exact hno hrefl
  have hmap : H.map (adjointGroup .E8 Ω).subtype =
      E.map ((baseChangeGL ιK).comp (adjointGroup .E8 K).subtype) := by
    dsimp only [H, E]
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [hmap] at hTor
  have hEcard : 125 ≤ Nat.card E := by
    rw [show Nat.card E = Nat.card (A.comap Λ₀) from
      Subgroup.card_map_of_injective ε.injective, hAcard]
    exact h3
  obtain ⟨g, hct⟩ := exists_conj_le_torusPow_five_of_toral hpq E hEg hEcard hTor
  have hg : E.map (MulAut.conj g).toMonoidHom = torusPow .E8 K p :=
    eq_torusPow_of_conj_le_of_selfCent E hEgs g hct
  let c : adjointGroup .E8 K ≃* adjointGroup .E8 K := MulAut.conj g
  let ψ₁ : L →* adjointGroup .E8 K := c.toMonoidHom.comp (ε.toMonoidHom.comp ψ)
  have hψ₁ : Function.Surjective ψ₁ := c.surjective.comp (ε.surjective.comp hψ)
  have hker₁ : ψ₁.ker ≤ Subgroup.center L := by
    intro l hl
    apply hker
    rw [MonoidHom.mem_ker] at hl ⊢
    have h1 : c (ε (ψ l)) = 1 := hl
    rw [c.map_eq_one_iff, ε.map_eq_one_iff] at h1
    exact h1
  let Λ₁ : adjointGroup .E8 K →* MulAut L :=
    Λ₀.comp (ε.symm.toMonoidHom.comp c.symm.toMonoidHom)
  have hΛ₁ : Function.Injective Λ₁ := hΛinj.comp (ε.symm.injective.comp c.symm.injective)
  have hΛ₁ψ : ∀ l, Λ₁ (ψ₁ l) = MulAut.conj l := by
    intro l
    change Λ₀ (ε.symm (c.symm (c (ε (ψ l))))) = MulAut.conj l
    rw [c.symm_apply_apply, ε.symm_apply_apply]
    exact hΛeq rfl
  have hEA : (torusPow .E8 K p).map Λ₁ = A := by
    have hmapc : E.map c.toMonoidHom = torusPow .E8 K p := hg
    rw [← hmapc, Subgroup.map_map]
    have hcomp : Λ₁.comp c.toMonoidHom = Λ₀.comp ε.symm.toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      change Λ₀ (ε.symm (c.symm (c x))) = Λ₀ (ε.symm x)
      rw [c.symm_apply_apply]
    rw [hcomp]
    change ((A.comap Λ₀).map ε.toMonoidHom).map (Λ₀.comp ε.symm.toMonoidHom) = A
    rw [Subgroup.map_map]
    have hcomp' : (Λ₀.comp ε.symm.toMonoidHom).comp ε.toMonoidHom = Λ₀ := by
      refine MonoidHom.ext fun x => ?_
      change Λ₀ (ε.symm (ε x)) = Λ₀ x
      rw [ε.symm_apply_apply]
    rw [hcomp']
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
    · intro a ha
      obtain ⟨x, hx⟩ := hAΛ a ha
      exact ⟨x, show Λ₀ x ∈ A by rw [hx]; exact ha, hx⟩
  obtain ⟨ζ, hζ, ι, hζo, hι, hrange, hact, hnorm⟩ := E8SplitTorus.exists_frame hp hp2 hpq
  have hn : ∀ i, E8SplitTorus.simpleRep (K := K) i ∈
      Subgroup.normalizer ((torusPow .E8 K p) : Set (adjointGroup .E8 K)) := by
    intro i
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    rw [← hrange] at hx ⊢
    obtain ⟨s, rfl⟩ := hx
    exact ⟨_, (hact i (Multiplicative.toAdd s)).symm⟩
  have hAut : ∀ β : MulAut (adjointGroup .E8 K),
      (∀ x, β x ∈ torusPow .E8 K p ↔ x ∈ torusPow .E8 K p) →
      ∃ (c : (ZMod p)ˣ) (u : WeylGroup .E8), ∀ v,
        β (ι (Multiplicative.ofAdd v)) =
          ι (Multiplicative.ofAdd ((c : ZMod p) • torusAct .E8 p u v)) :=
    fun β hβ => ExcFrames.exists_scalar_weyl_of_mulAut_torusPow_E7E8 (Or.inr rfl) hp hζo ι
      hrange hnorm β hβ
  exact ggWNormConcl_of_centralCover_weylFrame ψ₁ hψ₁ hker₁ center_adjointGroup_eq_bot
    Λ₁ hΛ₁ hΛ₁ψ (torusPow .E8 K p) A hEA ι hι hrange (E8SplitTorus.simpleRep (K := K)) hn
    hact hnorm hAut (by decide)
    (ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inr rfl)) hp2) ι' φ h α hgen hs

theorem largeEvenLabelAll_wnorm_E8_five_split {lab : LargeEvenLabel}
    (htag : lab.tag = .E8) (hpq : 5 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC 5 R I := by
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag hpq ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  exact ggTorusWNormSC_recipe_E8_five_split (by rw [hK]; exact hpq)

end E8WNorm

end CFSG.StandardType
