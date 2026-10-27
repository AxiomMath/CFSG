module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviModel
public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviAssemble
public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviStab
public import CFSG.LocalAnalysis.StandardType.GGTBJCoverBstar
public import CFSG.LocalAnalysis.StandardType.GGTBJCoverComp
public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviSplit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

private theorem e6lf_sum_frameCoord {τ : Tag} {p : ℕ} [NeZero p]
    (x : Fin τ.rank → ℤ) (s : Fin τ.rank → ZMod p) :
    ∑ j, (x j : ZMod p) * ExcFrames.frameCoord τ p s j =
      ((CFSG.LieType.Steinberg.Adjoint.iform x (TableBExc.liftMod τ p s) : ℤ) : ZMod p) := by
  simp only [ExcFrames.frameCoord, CFSG.LieType.Steinberg.Adjoint.iform, TableBExc.liftMod,
    Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ZMod.natCast_zmod_val]
  ring

private theorem e6lf_sum_frameCoord_smul
    {τ : Tag} {p : ℕ} [NeZero p] (w : WeylGroup τ)
    (x : Fin τ.rank → ℤ) (s : Fin τ.rank → ZMod p)
    (hs : TableBExc.torusAct τ p w⁻¹ s = s) :
    ∑ j, (((w • x) j : ℤ) : ZMod p) * ExcFrames.frameCoord τ p s j =
      ∑ j, (x j : ZMod p) * ExcFrames.frameCoord τ p s j := by
  rw [e6lf_sum_frameCoord, e6lf_sum_frameCoord]
  set y := TableBExc.liftMod τ p s
  have hy : CFSG.LieType.Steinberg.Adjoint.iform (w • x) y =
      CFSG.LieType.Steinberg.Adjoint.iform x (w⁻¹ • y) := by
    rw [← CFSG.LieType.Chevalley.iform_smul w x (w⁻¹ • y), smul_inv_smul]
  rw [hy]
  have hred : TableBExc.redMod τ p (w⁻¹ • y) = TableBExc.redMod τ p y := by
    rw [show TableBExc.redMod τ p (w⁻¹ • y) = TableBExc.torusAct τ p w⁻¹ s from rfl, hs,
      TableBExc.redMod_liftMod]
  have hcong : ∀ z z' : Fin τ.rank → ℤ,
      TableBExc.redMod τ p z = TableBExc.redMod τ p z' →
      ((CFSG.LieType.Steinberg.Adjoint.iform x z : ℤ) : ZMod p) =
        ((CFSG.LieType.Steinberg.Adjoint.iform x z' : ℤ) : ZMod p) := by
    intro z z' hz
    simp only [CFSG.LieType.Steinberg.Adjoint.iform]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hzj := congrFun hz j
    simp only [TableBExc.redMod] at hzj
    rw [hzj]
  exact hcong _ _ hred

theorem ggTBJE6Levi_of_frame
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [NeZero p]
    {Bs J X : Subgroup G} {g : G} (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ p = 1 → a ∈ Bs)
    (hJX : J ≤ X) (hgBs : g ∈ Bs)
    (hJg : J ≤ Subgroup.centralizer ({g} : Set G))
    (hgX : ∃ l ∈ X, g * l * g⁻¹ ≠ l)
    (hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({g} : Set G)))
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hZp : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {H : Type} [Group H] [Finite H] {E : Subgroup H}
    (ψ : ↥X →* H) (hψs : Function.Surjective ψ) (hψk : ψ.ker ≤ Subgroup.center ↥X)
    (Λ : H →* MulAut ↥X) (hΛi : Function.Injective Λ) (hΛc : ∀ x, Λ (ψ x) = MulAut.conj x)
    (hΛn : ∀ h l, ψ (Λ h l) = h * ψ l * h⁻¹) (hA : (ggGamma X hN).range = E.map Λ)
    (ι₀ : Multiplicative (Fin Tag.E6.rank → ZMod p) →* H) (hι₀ : Function.Injective ι₀)
    (hrange : ι₀.range = E) {m : ℕ} (wt : GGTorusTorWit m 6 ↥X (ggGamma X hN).range)
    (hact : ∀ k s, ψ (wt.n k) * ι₀ (Multiplicative.ofAdd s) * (ψ (wt.n k))⁻¹ =
      ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p (simple .E6 k) s)))
    (hwt : wt.Holds CartanMatrix.E₆ CoxeterMatrix.E₆)
    {F : Type} [Field F] {ζ : Fˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (hClass : ∀ (t : Fin Tag.E6.rank → ZMod p), ι₀ (Multiplicative.ofAdd t) ≠ 1 →
      ∀ (Y : Subgroup H),
        IsComponentOf Y (Subgroup.centralizer ({ι₀ (Multiplicative.ofAdd t)} : Set H)) →
      ∃ i : KernelComponent
          (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E6 p t))),
        (∀ s : Fin Tag.E6.rank → ZMod p,
          (∀ γ ∈ componentRoots
              (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E6 p t))) i,
            ∑ j, (γ j : ZMod p) * ExcFrames.frameCoord .E6 p s j = 0) →
          ι₀ (Multiplicative.ofAdd s) ∈ Subgroup.centralizer (Y : Set H)) ∧
        ∀ c ∈ componentRoots
            (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E6 p t))) i,
          ∃ y ∈ Y, ∀ s, y * ι₀ (Multiplicative.ofAdd s) * y⁻¹ =
            ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p (rootReflection c) s)))
    (bX : ↥Bs) (hbX1 : bX ≠ 1)
    (hbXc : (bX : G) ∈ Subgroup.centralizer (X : Set G))
    (hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  have hp : p.Prime := Fact.out
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have ha' : a ∈ ι₀.range := by rwa [hrange]
    have hb' : b ∈ ι₀.range := by rwa [hrange]
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp ha'
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hb'
    rw [← map_mul, mul_comm s t, map_mul]
  obtain ⟨ε, hεΛ, hεE, hεsurj, hεker, hεX, hεBs, hεinj, hεN1, hεN2, hεconj⟩ :=
    ggCover_bstar (E := E) hBs hSC hN hZp ψ hψs hψk Λ hΛi
      hΛc hΛn hEc hA
  obtain ⟨V, hVadd, hVmod, ιB, φ, h, α, f, κ, hlin, hrefl, hpair, hf, hclos, hκ, hα, hh,
    hTD, hFε⟩ := e6Cover_datum (p := p) hp2 hBs hSC hN hZp ψ ε hεE hεsurj
      hεker hεX hεBs ι₀ hι₀ hrange wt hact hwt
  have hVfin : Finite V := Finite.of_injective
    (fun x : V => Additive.toMul (ιB.symm x))
    (fun x y h => by
      apply ιB.symm.injective
      exact Additive.toMul.injective h)
  have hofAdd_inj : ∀ {s t : Fin Tag.E6.rank → ZMod p},
      Multiplicative.ofAdd s = Multiplicative.ofAdd t → s = t := by
    intro s t h
    simpa using congrArg Multiplicative.toAdd h
  let gB : ↥Bs := ⟨g, hgBs⟩
  have hbXeps : ε bX = 1 := (hεker bX).2 hbXc
  have hgne : ε gB ≠ 1 := by
    intro h1
    obtain ⟨l, hl, hne⟩ := hgX
    exact hne (by
      have hcomm := (Subgroup.mem_centralizer_iff.mp ((hεker gB).1 h1)) l hl
      calc g * l * g⁻¹ = l * g * g⁻¹ := by rw [hcomm]
        _ = l := by group)
  have hbXα : ∀ j, α j (ιB (Additive.ofMul bX)) = 0 := by
    intro j
    have h0 := hα bX 0 (by simp [hbXeps]) j
    simpa using h0
  obtain ⟨t_g, ht_g⟩ := MonoidHom.mem_range.mp (hrange ▸ hεE gB)
  let s_g : Fin Tag.E6.rank → ZMod p := Multiplicative.toAdd t_g
  have hsg : ι₀ (Multiplicative.ofAdd s_g) = ε gB := ht_g
  have htg1 : ι₀ (Multiplicative.ofAdd s_g) ≠ 1 := by rw [hsg]; exact hgne
  have hsg0 : s_g ≠ 0 := by
    intro h0
    apply htg1
    rw [h0]
    exact map_one ι₀
  let a : Fin Tag.E6.rank → Fˣ :=
    TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E6 p s_g)
  have hdet : IsUnit ((Tag.E6.symmetrizedCartan.det : ℤ) : ZMod p) := by
    rw [CFSG.RankThree.E6.symmetrizedCartan_E6, det_cartan_E6]
    exact isUnit_iff_ne_zero.2 (by
      have h : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
      simpa using h)
  have ha : ∀ j, a j ^ p = 1 := by
    intro j
    change (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E6 p s_g) j) ^ p = 1
    rw [TableBExc.E6Three.zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have ha1 : ∃ j, a j ≠ 1 := by
    by_contra hc
    have h1 : ∀ j, a j = 1 := fun j => by
      by_contra hj
      exact hc ⟨j, hj⟩
    have hone : TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E6 p s_g) = 1 := by
      funext j
      exact h1 j
    have hzero : ExcFrames.frameCoord .E6 p s_g = ExcFrames.frameCoord .E6 p 0 := by
      apply TableBExc.E6Three.zetaVec_injective hζo hζ
      rw [ExcFrames.frameCoord_zero, hone]
      funext j
      rw [TableBExc.E6Three.zetaVec_apply]
      simp
    exact hsg0 (ExcFrames.frameCoord_injective hdet hzero)
  have hprim : IsPrimitiveRoot (ζ : F) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hζo)
  let Y : Subgroup H := (J.subgroupOf X).map ψ
  have hYc := ggCover_component (p := p) hBs hgBs hN hZp ψ hψs hψk Λ hΛc hΛn
    (hεΛ gB) hJX hcomp
  have hY : IsComponentOf Y
      (Subgroup.centralizer ({ι₀ (Multiplicative.ofAdd s_g)} : Set H)) := by
    have h1 := hYc.1
    rw [← hsg] at h1
    exact h1
  have hcentJ : ∀ (b : ↥Bs) (c' : H), Λ c' = ggGamma X hN b →
      c' ∈ Subgroup.centralizer (Y : Set H) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := hYc.2
  obtain ⟨i, hCENT, hLow⟩ := hClass s_g htg1 Y hY
  let A : V →ₗ[ZMod p] (Fin Tag.E6.rank → ZMod p) :=
    { toFun := fun w j => α j w
      map_add' := by
        intro x y
        funext j
        simp only [map_add, Pi.add_apply]
      map_smul' := by
        intro c x
        funext j
        simp only [map_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply] }
  have hAframe : ∀ (b : ↥Bs) (s : Fin Tag.E6.rank → ZMod p),
      ι₀ (Multiplicative.ofAdd s) = ε b →
      A (ιB (Additive.ofMul b)) = ExcFrames.frameCoord .E6 p s := by
    intro b s hs
    funext j
    change α j (ιB (Additive.ofMul b)) = ExcFrames.frameCoord .E6 p s j
    rw [hα b s hs j, ExcFrames.frameCoord, CFSG.RankThree.E6.symmetrizedCartan_E6]
  have hA_surj : Function.Surjective A := by
    intro u
    have hfc : Function.Surjective (ExcFrames.frameCoord .E6 p) :=
      Finite.injective_iff_surjective.mp (ExcFrames.frameCoord_injective hdet)
    obtain ⟨s, hs⟩ := hfc u
    obtain ⟨b, hb⟩ := hεsurj (ι₀ (Multiplicative.ofAdd s))
      (by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    exact ⟨ιB (Additive.ofMul b), by rw [hAframe b s hb.symm, hs]⟩
  let Pre : Submodule (ZMod p) V :=
    (ggRootAnn p (componentRoots (rootCharHom a) i)).comap A
  have hPre_mem : ∀ w, w ∈ Pre ↔ ∀ c ∈ componentRoots (rootCharHom a) i,
      ∑ j, (c j : ZMod p) * A w j = 0 := fun w => Iff.rfl
  have hcard_sub : Nat.card {b : ↥Bs // ∀ c ∈ componentRoots (rootCharHom a) i,
        ∑ j, (c j : ZMod p) * A (ιB (Additive.ofMul b)) j = 0} = Nat.card ↥Pre := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv (Additive.ofMul.trans ιB.toEquiv) ?_
    intro b
    exact (hPre_mem _).symm
  let Apre : ↥Pre →+ ↥(ggRootAnn p (componentRoots (rootCharHom a) i)) :=
    { toFun := fun w => ⟨A w.1, w.2⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; apply Subtype.ext; exact map_add A x.1 y.1 }
  have hApre_surj : Function.Surjective Apre := by
    intro t
    obtain ⟨v, hv⟩ := hA_surj t.1
    refine ⟨⟨v, ?_⟩, ?_⟩
    · rw [hPre_mem]
      intro c hc
      have h0 := t.2 c hc
      rw [← hv] at h0
      exact h0
    · apply Subtype.ext
      exact hv
  have hker_card : Nat.card ↥(AddMonoidHom.ker Apre) =
      Nat.card ↥(LinearMap.ker A) := by
    apply Nat.card_congr
    refine ⟨fun w => ⟨w.1.1, ?_⟩, fun v => ⟨⟨v.1, ?_⟩, ?_⟩, ?_, ?_⟩
    · have hw : A w.1.1 = 0 := congrArg Subtype.val (AddMonoidHom.mem_ker.mp w.2)
      exact hw
    · rw [hPre_mem]
      intro c hc
      have hv : A v.1 = 0 := LinearMap.mem_ker.mp v.2
      refine Finset.sum_eq_zero fun j _ => ?_
      have hαj : A v.1 j = 0 := congrFun hv j
      rw [hαj, mul_zero]
    · apply AddMonoidHom.mem_ker.mpr
      exact Subtype.ext (LinearMap.mem_ker.mp v.2)
    · intro w
      ext
      rfl
    · intro v
      ext
      rfl
  have hPre_card : Nat.card ↥(LinearMap.ker A) *
      Nat.card ↥(ggRootAnn p (componentRoots (rootCharHom a) i)) = Nat.card ↥Pre := by
    rw [← hker_card]
    exact AddSubgroup.card_ker_mul_card_of_surjective hApre_surj
  have hbXker : ιB (Additive.ofMul bX) ∈ LinearMap.ker A := by
    rw [LinearMap.mem_ker]
    funext j
    show α j (ιB (Additive.ofMul bX)) = 0
    rw [hbXα j]
  have hbXne : ιB (Additive.ofMul bX) ≠ 0 := by
    intro h0
    apply hbX1
    have h1 : ιB (Additive.ofMul bX) = ιB 0 := by rw [h0, map_zero]
    have h2 : Additive.ofMul bX = 0 := ιB.injective h1
    simpa using congrArg Additive.toMul h2
  have hnt : Nontrivial ↥(LinearMap.ker A) :=
    ⟨⟨⟨ιB (Additive.ofMul bX), hbXker⟩, ⟨0, by simp⟩, by
      intro h
      exact hbXne (congrArg (fun x : ↥(LinearMap.ker A) => (x.1 : V)) h)⟩⟩
  have hone_lt : 1 < Nat.card ↥(LinearMap.ker A) :=
    Finite.one_lt_card_iff_nontrivial.mpr hnt
  have hcardker : Nat.card ↥(LinearMap.ker A) =
      p ^ Module.finrank (ZMod p) ↥(LinearMap.ker A) :=
    (FiniteField.pow_finrank_eq_natCard p ↥(LinearMap.ker A)).symm
  have hdpos : 0 < Module.finrank (ZMod p) ↥(LinearMap.ker A) := by
    by_contra h0
    have h0' : Module.finrank (ZMod p) ↥(LinearMap.ker A) = 0 := by omega
    rw [hcardker, h0', pow_zero] at hone_lt
    omega
  have hp_le : p ≤ Nat.card ↥(LinearMap.ker A) := by
    rw [hcardker]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ Module.finrank (ZMod p) ↥(LinearMap.ker A) :=
          Nat.pow_le_pow_right hp.pos hdpos
  have hcounted_upper : Nat.card {b : ↥Bs // ∀ c ∈ componentRoots (rootCharHom a) i,
        ∑ j, (c j : ZMod p) * A (ιB (Additive.ofMul b)) j = 0} ≤ p ^ 3 := by
    have hmem : ∀ b : {b : ↥Bs // ∀ c ∈ componentRoots (rootCharHom a) i,
        ∑ j, (c j : ZMod p) * A (ιB (Additive.ofMul b)) j = 0},
        (b.1 : G) ∈ Bs ⊓ Subgroup.centralizer (J : Set G) := by
      intro b
      obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp (hrange ▸ hεE b.1)
      let t' : Fin Tag.E6.rank → ZMod p := Multiplicative.toAdd t
      have ht' : ι₀ (Multiplicative.ofAdd t') = ε b.1 := ht
      have hcent : ι₀ (Multiplicative.ofAdd t') ∈
          Subgroup.centralizer (Y : Set H) :=
        hCENT t' (fun γ hγ => by
          have h1 := b.2 γ hγ
          rwa [hAframe b.1 t' ht'] at h1)
      exact ⟨b.1.2, hcentJ b.1 (ε b.1) (hεΛ b.1) (by rwa [← ht'])⟩
    refine le_trans (Nat.card_le_card_of_injective
      (fun b => (⟨(b.1 : G), hmem b⟩ : ↥(Bs ⊓ Subgroup.centralizer (J : Set G)))) ?_) hcardJ
    intro b1 b2 h
    have h' : (b1.1 : G) = (b2.1 : G) := congrArg (fun x : ↥(Bs ⊓ _) => (x : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hann_le : Nat.card ↥(ggRootAnn p (componentRoots (rootCharHom a) i)) ≤ p ^ 2 := by
    have h1 : p * Nat.card ↥(ggRootAnn p (componentRoots (rootCharHom a) i)) ≤ p * p ^ 2 := by
      calc p * Nat.card ↥(ggRootAnn p (componentRoots (rootCharHom a) i))
          ≤ Nat.card ↥Pre := by
            rw [← hPre_card]
            exact Nat.mul_le_mul_right _ hp_le
        _ = Nat.card {b : ↥Bs // ∀ c ∈ componentRoots (rootCharHom a) i,
              ∑ j, (c j : ZMod p) * A (ιB (Additive.ofMul b)) j = 0} := hcard_sub.symm
        _ ≤ p ^ 3 := hcounted_upper
        _ = p * p ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  have hfin_le : Module.finrank (ZMod p) ↥(ggRootAnn p (componentRoots (rootCharHom a) i))
      ≤ 2 := by
    have hcardann : p ^ Module.finrank (ZMod p)
        ↥(ggRootAnn p (componentRoots (rootCharHom a) i)) =
        Nat.card ↥(ggRootAnn p (componentRoots (rootCharHom a) i)) :=
      FiniteField.pow_finrank_eq_natCard p
        ↥(ggRootAnn p (componentRoots (rootCharHom a) i))
    rw [← hcardann] at hann_le
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hann_le
  have h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i) := by
    have h := le_compRank_of_finrank_ggRootAnn (τ := .E6) (p := p)
      (componentRoots (rootCharHom a) i) hfin_le
    have hrank : Tag.E6.rank = 6 := rfl
    omega
  obtain ⟨v₀, S, hS, hΨeq⟩ := e6_class_levi hp hp2 hprim a ha ha1 i h3
  let F : WeylGroup .E6 →* ↥(ggAutomizer X Bs) := f.toMonoidHom.comp κ.toMonoidHom
  let Fw : WeylGroup .E6 →* MulAut ↥Bs := (ggAutomizer X Bs).subtype.comp F
  have hFwdef : ∀ u, Fw u = (f (κ u) : MulAut ↥Bs) := fun u => rfl
  have hlower : ∀ c ∈ componentRoots (rootCharHom a) i,
      Fw (rootReflection c) ∈ ggAutomizer J Bs := by
    intro c hc
    obtain ⟨gY, hgYY, hactc⟩ := hLow c hc
    obtain ⟨jX, hjJsub, rfl⟩ := Subgroup.mem_map.mp hgYY
    have hjJ : (jX : G) ∈ J := Subgroup.mem_subgroupOf.mp hjJsub
    have hmapE : E.map (MulAut.conj (ψ jX)).toMonoidHom = E := by
      apply le_antisymm
      · rintro x ⟨y, hy, rfl⟩
        obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp (hrange.symm ▸ hy)
        let s : Fin Tag.E6.rank → ZMod p := Multiplicative.toAdd t
        have hs : ι₀ (Multiplicative.ofAdd s) = y := ht
        change ψ jX * y * (ψ jX)⁻¹ ∈ E
        rw [← hs, hactc s, ← hrange]
        exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
      · intro x hx
        obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp (hrange.symm ▸ hx)
        let s : Fin Tag.E6.rank → ZMod p := Multiplicative.toAdd t
        have hs : ι₀ (Multiplicative.ofAdd s) = x := ht
        refine Subgroup.mem_map.mpr ⟨ι₀ (Multiplicative.ofAdd
          (TableBExc.torusAct .E6 p (rootReflection c)⁻¹ s)), ?_, ?_⟩
        · rw [← hrange]
          exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
        · rw [← hs]
          change ψ jX * ι₀ (Multiplicative.ofAdd
            (TableBExc.torusAct .E6 p (rootReflection c)⁻¹ s)) * (ψ jX)⁻¹ =
              ι₀ (Multiplicative.ofAdd s)
          rw [hactc, ← TableBExc.torusAct_mul, mul_inv_cancel, TableBExc.torusAct_one]
    have hjN : (jX : G) ∈ Subgroup.normalizer (Bs : Set G) :=
      hεN1 jX ((Subgroup.mem_normalizer_iff_map_conj_eq).2 hmapE)
    let jsub : ↥(J ⊓ Subgroup.normalizer (Bs : Set G)) := ⟨(jX : G), hjJ, hjN⟩
    have htJ : ggTDρB J Bs jsub ∈ ggAutomizer J Bs := by
      rw [← ggTDρB_range]
      exact ⟨jsub, rfl⟩
    let jXinf : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)) := ⟨(jX : G), jX.2, hjN⟩
    have htXD : ggTDρB X Bs jXinf = (f (κ (rootReflection c)) : MulAut ↥Bs) := by
      refine hTD jXinf (rootReflection c) ?_
      intro s
      have h1 : (⟨jXinf, jXinf.2.1⟩ : ↥X) = jX := rfl
      rw [h1]
      exact hactc s
    rw [hFwdef, ← htXD]
    exact htJ
  have hupper : ∀ t ∈ ggAutomizer J Bs,
      t ∈ (Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i)).map Fw := by
    intro t ht
    obtain ⟨j, hjJ, hjN, hφt⟩ := mem_ggAutomizer_iff.mp ht
    have htX : t ∈ ggAutomizer X Bs := mem_ggAutomizer_iff.mpr ⟨j, hJX hjJ, hjN, hφt⟩
    let w : WeylGroup .E6 := κ.symm (f.symm ⟨t, htX⟩)
    have hFwu : Fw w = t := by
      rw [hFwdef]
      change ((f (κ (κ.symm (f.symm ⟨t, htX⟩))) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = t
      simp
    have htfix : ∀ b : ↥Bs, (b : G) ∈ Subgroup.centralizer (J : Set G) → t b = b := by
      intro b hb
      apply Subtype.ext
      rw [hφt b, (Subgroup.mem_centralizer_iff.mp hb) j hjJ]
      group
    have htg : t gB = gB := by
      apply Subtype.ext
      have hcomm := (Subgroup.mem_centralizer_singleton_iff.mp (hJg hjJ))
      calc ((t gB : ↥Bs) : G) = j * (gB : G) * j⁻¹ := hφt gB
        _ = (gB : G) := by
            change j * g * j⁻¹ = g
            rw [hcomm]
            group
    have hws : TableBExc.torusAct .E6 p w s_g = s_g := by
      have h1 := hFε w gB s_g hsg
      rw [← hFwdef, hFwu, htg, ← hsg] at h1
      exact (hofAdd_inj (hι₀ h1)).symm
    have hwinv : TableBExc.torusAct .E6 p w⁻¹ s_g = s_g := by
      have h1 := congrArg (TableBExc.torusAct .E6 p w⁻¹) hws
      rw [← TableBExc.torusAct_mul, inv_mul_cancel, TableBExc.torusAct_one] at h1
      exact h1.symm
    have hwstab : w ∈ rootCharStabilizerSubgroup a := by
      rw [mem_rootCharStabilizerSubgroup]
      intro c
      change rootChar a (w • c) = rootChar a c
      rw [NoOffE8Five.rootChar_zetaVec hζ, NoOffE8Five.rootChar_zetaVec hζ,
        e6lf_sum_frameCoord_smul w c s_g hwinv]
    have hwfix : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
        ∀ j, ((w • c) j : ZMod p) = (c j : ZMod p) := by
      intro c hcK hcΨ
      have horth : ∀ γ ∈ componentRoots (rootCharHom a) i,
          ∑ j, (γ j : ZMod p) *
            ExcFrames.frameCoord .E6 p (TableBExc.redMod .E6 p c) j = 0 := by
        intro γ hγ
        have hc_mem : c ∈ componentRoots (rootCharHom a) ⟦⟨c, hcK⟩⟧ := ⟨hcK, rfl⟩
        have hne : (⟦⟨c, hcK⟩⟧ : KernelComponent (rootCharHom a)) ≠ i := by
          intro heq
          exact hcΨ (by rwa [heq] at hc_mem)
        have hform : CFSG.LieType.Steinberg.Adjoint.iform γ c = 0 :=
          CFSG.LieType.Chevalley.iform_eq_zero_of_mem_componentRoots hne.symm hγ hc_mem
        rw [e6lf_sum_frameCoord]
        have hcong : ((CFSG.LieType.Steinberg.Adjoint.iform γ
            (TableBExc.liftMod .E6 p (TableBExc.redMod .E6 p c)) : ℤ) : ZMod p) =
            ((CFSG.LieType.Steinberg.Adjoint.iform γ c : ℤ) : ZMod p) := by
          simp only [CFSG.LieType.Steinberg.Adjoint.iform]
          push_cast
          refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
          simp [TableBExc.liftMod, TableBExc.redMod]
        rw [hcong, hform, Int.cast_zero]
      have hcent := hCENT (TableBExc.redMod .E6 p c) horth
      obtain ⟨b, hbε⟩ := hεsurj (ι₀ (Multiplicative.ofAdd (TableBExc.redMod .E6 p c)))
        (by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      have hbC : (b : G) ∈ Subgroup.centralizer (J : Set G) :=
        hcentJ b (ε b) (hεΛ b) (by rwa [hbε])
      have h1 := hFε w b (TableBExc.redMod .E6 p c) hbε.symm
      rw [← hFwdef, hFwu, htfix b hbC, hbε] at h1
      have h2 : TableBExc.torusAct .E6 p w (TableBExc.redMod .E6 p c) =
          TableBExc.redMod .E6 p c := (hofAdd_inj (hι₀ h1)).symm
      have h3 : TableBExc.torusAct .E6 p w (TableBExc.redMod .E6 p c) =
          TableBExc.redMod .E6 p (w • c) :=
        TableBExc.redMod_smul_eq w (TableBExc.redMod_liftMod (TableBExc.redMod .E6 p c))
      intro j
      have h4 := congrFun (h3.symm.trans h2) j
      simpa [TableBExc.redMod] using h4
    have hwcl := mem_closure_rootReflection_of_fix_E6 hp hp2 hp3 ha i hwstab hwfix
    exact ⟨w, hwcl, hFwu⟩
  have hJeq : ggAutomizer J Bs =
      (Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i)).map Fw := by
    apply le_antisymm
    · intro t ht
      exact hupper t ht
    · rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨r, ⟨c, hc, rfl⟩, rfl⟩
      exact hlower c hc
  have hset : Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) =
      Subgroup.closure {s : WeylGroup .E6 | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ} := by
    congr 1
    ext s
    simp only [Set.mem_image, Set.mem_setOf_eq]
    exact ⟨fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩, fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩⟩
  have hpar : Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) =
      Subgroup.closure ((fun j : Fin 6 => v₀ * simple .E6 j * v₀⁻¹) '' {j : Fin 6 | j ∉ S}) := by
    rw [hset, hΨeq, closure_rootReflection_smul_parabolicRoots (τ := .E6) v₀]
    rfl
  have hψsimple : ∀ j, Fw (simple .E6 j) = φ j := by
    intro j
    rw [hFwdef, hκ j]
    exact hf j
  let u : CoxeterMatrix.E₆.Group := κ v₀
  have hJ' : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin 6 // j ∉ S} =>
        (f u : MulAut ↥Bs) * φ j.1 * (f u : MulAut ↥Bs)⁻¹) := by
    rw [hJeq, hpar, MonoidHom.map_closure, Set.image_image, Set.image_eq_range]
    congr 1
    ext t
    simp only [Set.mem_range, Subtype.exists]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, by rw [map_mul, map_mul, map_inv, hψsimple j, hFwdef v₀]⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, by rw [map_mul, map_mul, map_inv, hψsimple j, hFwdef v₀]⟩
  exact ggE6LeviDatum_of_conj hp2 hlin hrefl hpair hf hclos u hS hJ'

theorem ggTBJE6Levi_of_coverModel
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [NeZero p]
    {Bs J X : Subgroup G} {g : G} (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ p = 1 → a ∈ Bs)
    (hJX : J ≤ X) (hgBs : g ∈ Bs)
    (hJg : J ≤ Subgroup.centralizer ({g} : Set G))
    (hgX : ∃ l ∈ X, g * l * g⁻¹ ≠ l)
    (hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({g} : Set G)))
    (hM : GGE6CoverModel p Bs X) (bX : ↥Bs) (hbX1 : bX ≠ 1)
    (hbXc : (bX : G) ∈ Subgroup.centralizer (X : Set G))
    (hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  obtain ⟨hN, Fq, hFqF, hFqFin, hFqChar, ψ, Λ, ζ, hζ, ι₀, m, wt, hK4, hψs, hψk, hZp,
    hΛi, hΛc, hΛn, hA, hζo, hι₀, hrange, hcoe, hact, -, hwt⟩ := hM
  let : Field Fq := hFqF
  let : Finite Fq := hFqFin
  let : CharP Fq 2 := hFqChar
  haveI : Finite (ModGL .E6 Fq) := finite_modGL
  haveI : Finite ↥(adjointGroup .E6 Fq) := Subtype.finite
  refine ggTBJE6Levi_of_frame hp2 hp3 hBs hSC hJX hgBs hJg hgX hcomp hN hZp ψ hψs hψk Λ hΛi hΛc
    hΛn hA ι₀ hι₀ hrange wt hact hwt hζ hζo (fun t _ Y hY => ?_) bX hbX1 hbXc hcardJ
  obtain ⟨i, hYspan, hCENT⟩ := e8Split_class hK4 hcoe hY
  exact ⟨i, hCENT, e8Split_lower hcoe i hYspan⟩

theorem ggTBJE6LeviL_of_coverModel
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [NeZero p]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p ≠ 3) (hM : GGE6CoverModel p Bs L) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  have hp : p.Prime := hH.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ p = 1 → a ∈ Bs :=
    hH.1.2.1.2.2.2
  have hS : LargeEvenSStar p B x L := hH.1.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hyB : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hyB
  have hD : D = Subgroup.closure {x, y} := hnb.2.1
  have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  have hgX : ∃ l ∈ L, y * l * y⁻¹ ≠ l := by
    by_contra h
    have hyC : y ∈ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
      by_contra hne
      exact h ⟨l, hl, fun h' => hne (mul_inv_eq_iff_eq_mul.mp h').symm⟩
    have hyx : y ∈ Subgroup.zpowers x := by
      rw [← inf_centralizer_eq_zpowers_of_sstar hp hS]
      exact ⟨hyB, hyC⟩
    have hle : D ≤ Subgroup.zpowers x := by
      rw [hD, Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | rfl
      · exact Subgroup.mem_zpowers _
      · exact hyx
    have h1 : Nat.card D ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
    rw [hDcard, Nat.card_zpowers, orderOf_eq_prime (hBs.2 x hxBs) hx1] at h1
    have : 1 < p := hp.one_lt
    nlinarith
  have hcomp0 : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hH.1.2.2.1.2.2.2.2.2.1
  have hyD : y ∈ D := by
    rw [hD]
    exact Subgroup.subset_closure (by simp)
  have hLC : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyD))
    · intro l hl
      refine ⟨hl.1, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
      have hxl : x * l = l * x := Subgroup.mem_centralizer_iff.mp (hLx hl.1) x rfl
      have hyl : y * l = l * y := Subgroup.mem_centralizer_iff.mp hl.2 y rfl
      rw [hD] at hd
      refine Subgroup.closure_induction (p := fun d _ => d * l = l * d) ?_ ?_ ?_ ?_ hd
      · rintro d (rfl | rfl)
        · exact hxl
        · exact hyl
      · simp
      · intro a b _ _ ha hb
        rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
      · intro a _ ha
        exact (Commute.inv_left ha : Commute a⁻¹ l)
  have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) := hLC ▸ hcomp0
  have hJX : J ≤ L := hcomp.1.trans inf_le_left
  have hJg : J ≤ Subgroup.centralizer ({y} : Set G) := hcomp.1.trans inf_le_right
  have hbXc : (x : G) ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hLx hl) x rfl).symm
  have hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3 :=
    GGConfig.card_bstar_inf_centralizer_J_le hH.1
  have hx1' : (⟨x, hxBs⟩ : ↥Bs) ≠ 1 := by
    intro h
    exact hx1 (congrArg Subtype.val h)
  exact ggTBJE6Levi_of_coverModel hp2 hp3 hBs hSC hJX hyBs hJg hgX hcomp hM
    ⟨x, hxBs⟩ hx1' hbXc hcardJ

theorem ggTBJE6LeviK_of_coverModel
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [NeZero p]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K) (hp3 : p ≠ 3)
    (hM : GGE6CoverModel p Bs K) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ p = 1 → a ∈ Bs :=
    hH.1.2.1.2.2.2
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hyB : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hyB
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hH.1.1.2.2.2.2.2.2.1 hH.1.2.2 hnb hJK
  have hJg : J ≤ Subgroup.centralizer ({x} : Set G) := hcomp.1.trans inf_le_right
  have hgX : ∃ l ∈ K, x * l * x⁻¹ ≠ l := by
    by_contra h
    refine not_mem_centralizer_of_nbr hnb (Subgroup.mem_centralizer_iff.mpr fun l hl => ?_)
    by_contra hne
    exact h ⟨l, hl, fun h' => hne (mul_inv_eq_iff_eq_mul.mp h').symm⟩
  have hbXc : (y : G) ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hnb.1.2.2.2.1 hl) y rfl).symm
  have hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3 :=
    GGConfig.card_bstar_inf_centralizer_J_le hH.1
  have hy1' : (⟨y, hyBs⟩ : ↥Bs) ≠ 1 := by
    intro h
    exact hnb.1.2.2.1 (congrArg Subtype.val h)
  exact ggTBJE6Levi_of_coverModel hp2 hp3 hBs hSC hJK hxBs hJg hgX hcomp hM
    ⟨y, hyBs⟩ hy1' hbXc hcardJ

end CFSG.StandardType

end
