module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviStab
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnModel
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.LocalAnalysis.StandardType.GGTBJCoverComp
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped IsMulCommutative

@[expose] def GGF4LeviFrame (p : ℕ) [NeZero p] {R : Type}
    [Group R] (E : Subgroup R) : Prop :=
  ∃ (Lf : Type) (_ : Field Lf) (ζ : Lfˣ) (hζ : ζ ^ p = 1)
    (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod p) →* R)
    (nk : Fin Tag.F4.rank → R) (m : ℕ)
    (wt : GGTorusTorWit m 4 (R)
      (E.map (MulAut.conj : R →* MulAut (R)))),
    orderOf ζ = p ∧ Function.Injective ι₀ ∧ ι₀.range = E ∧
    (∀ k s, nk k * ι₀ (Multiplicative.ofAdd s) * (nk k)⁻¹ =
      ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p (simple .F4 k) s))) ∧
    (∀ k, wt.n k = nk k) ∧ wt.Holds CartanMatrix.F₄ CoxeterMatrix.F₄ ∧
    ∀ t : Fin Tag.F4.rank → ZMod p, ι₀ (Multiplicative.ofAdd t) ≠ 1 →
      ∀ Y : Subgroup (R), IsComponentOf Y
        (Subgroup.centralizer ({ι₀ (Multiplicative.ofAdd t)} : Set (R))) →
      ∃ i : KernelComponent
          (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 p t))),
        (∀ s : Fin Tag.F4.rank → ZMod p,
          (∀ γ ∈ componentRoots
              (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 p t))) i,
            ∑ j, (γ j : ZMod p) * ExcFrames.frameCoord .F4 p s j = 0) →
          ι₀ (Multiplicative.ofAdd s) ∈ Subgroup.centralizer (Y : Set (R))) ∧
        (∀ (v : WeylGroup .F4) (Sd : Finset (Fin 4)), Sd ∈ f4LeviDel →
          componentRoots
              (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 p t))) i =
            (fun α => v • α) '' parabolicRoots .F4 {j | j ∉ Sd} →
          ∀ c ∈ componentRoots
              (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 p t))) i,
            ∃ y ∈ Y, ∀ s, y * ι₀ (Multiplicative.ofAdd s) * y⁻¹ =
              ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p (rootReflection c) s)))

@[expose] def GGF4LeviModel (p : ℕ) [NeZero p] {G : Type} [Group G]
    (Bs X : Subgroup G) : Prop :=
  ∃ (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (R : Type) (_ : Group R)
    (_ : Subgroup.center R = ⊥) (e : ↥X ≃* R) (E : Subgroup R),
    (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
        E.map (MulAut.conj : R →* MulAut R) ∧
      GGF4LeviFrame p E

private theorem f4lf_frameCoord_eq {p : ℕ} (s : Fin Tag.F4.rank → ZMod p) (j : Fin Tag.F4.rank) :
    ExcFrames.frameCoord .F4 p s j =
      (((![2, 2, 1, 1] : Fin 4 → ℤ) j : ℤ) : ZMod p) *
        ∑ k, ((Tag.cartan .F4 j k : ℤ) : ZMod p) * s k := by
  rw [ExcFrames.frameCoord, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : Tag.symmetrizedCartan .F4 j k = (![2, 2, 1, 1] : Fin 4 → ℤ) j * Tag.cartan .F4 j k := by
    fin_cases j <;> fin_cases k <;> rfl
  rw [h]
  push_cast
  ring

private theorem f4lf_sum_frameCoord {p : ℕ} [NeZero p] (x : Fin Tag.F4.rank → ℤ)
    (s : Fin Tag.F4.rank → ZMod p) :
    ∑ j, (x j : ZMod p) * ExcFrames.frameCoord .F4 p s j =
      ((CFSG.LieType.Steinberg.Adjoint.iform x (TableBExc.liftMod .F4 p s) : ℤ) : ZMod p) := by
  simp only [ExcFrames.frameCoord, CFSG.LieType.Steinberg.Adjoint.iform, TableBExc.liftMod,
    Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ZMod.natCast_zmod_val]
  ring

private theorem f4lf_sum_frameCoord_smul
    {p : ℕ} [NeZero p] (w : WeylGroup .F4) (x : Fin Tag.F4.rank → ℤ)
    (s : Fin Tag.F4.rank → ZMod p) (hs : TableBExc.torusAct .F4 p w⁻¹ s = s) :
    ∑ j, (((w • x) j : ℤ) : ZMod p) * ExcFrames.frameCoord .F4 p s j =
      ∑ j, (x j : ZMod p) * ExcFrames.frameCoord .F4 p s j := by
  rw [f4lf_sum_frameCoord, f4lf_sum_frameCoord]
  set y := TableBExc.liftMod .F4 p s
  have hy : CFSG.LieType.Steinberg.Adjoint.iform (w • x) y =
      CFSG.LieType.Steinberg.Adjoint.iform x (w⁻¹ • y) := by
    rw [← CFSG.LieType.Chevalley.iform_smul w x (w⁻¹ • y), smul_inv_smul]
  rw [hy]
  have hred : TableBExc.redMod .F4 p (w⁻¹ • y) = TableBExc.redMod .F4 p y := by
    rw [show TableBExc.redMod .F4 p (w⁻¹ • y) = TableBExc.torusAct .F4 p w⁻¹ s from rfl, hs,
      TableBExc.redMod_liftMod]
  have hcong : ∀ z z' : Fin Tag.F4.rank → ℤ,
      TableBExc.redMod .F4 p z = TableBExc.redMod .F4 p z' →
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

theorem ggTBJF4Levi_of_cover_frame
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J X : Subgroup G} {g : G} (hp2 : p ≠ 2)
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ p = 1 → a ∈ Bs)
    (hXB : Bs ≤ Subgroup.normalizer (X : Set G))
    (hJX : J ≤ X) (hgBs : g ∈ Bs)
    (hJg : J ≤ Subgroup.centralizer ({g} : Set G))
    (hgX : ∃ l ∈ X, g * l * g⁻¹ ≠ l)
    (hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({g} : Set G)))
    (hZp : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {R : Type} [Group R] (hZR : Subgroup.center R = ⊥)
    (π : ↥X →* R) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥X)
    {E : Subgroup R}
    (hA : (ggGamma X hXB).range = E.map (ReflInner.liftConj π hπ hker))
    [NeZero p] (hF : GGF4LeviFrame p E) (bX : ↥Bs) (hbX1 : bX ≠ 1)
    (hbXc : (bX : G) ∈ Subgroup.centralizer (X : Set G))
    (hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  have hp : p.Prime := Fact.out
  have : Finite R := Finite.of_surjective π hπ
  let Λ : R →* MulAut ↥X := ReflInner.liftConj π hπ hker
  have hΛinj : Function.Injective Λ := ReflInner.liftConj_injective hπ hker hZR
  have hΛc : ∀ x : ↥X, Λ (π x) = MulAut.conj x :=
    fun x => ReflInner.liftConj_eq hπ hker rfl
  have hΛn : ∀ r x, π (Λ r x) = r * π x * r⁻¹ :=
    ReflInner.map_liftConj_apply hπ hker
  obtain ⟨Lf, _, ζ, hζ, ιT, nk, m, wt, hζo, hιTinj, hιTrange, hact, hwn, hwt, hcl⟩ := hF
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp (hιTrange.symm ▸ ha)
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp (hιTrange.symm ▸ hb)
    exact (map_mul ιT u v).symm.trans ((congrArg ιT (mul_comm u v)).trans (map_mul ιT v u))
  obtain ⟨ε, hεconj, hεE, hεsurj, hεker, hεX, hεlift, huniq, hεN1, hεN2, hεeq⟩ :=
    ggCover_bstar hBs hSC hXB hZp π hπ hker Λ hΛinj hΛc hΛn hEc hA
  obtain ⟨θ, hθ⟩ := ggCover_automizer π hπ ε hεE hεsurj hεker hεX hεlift huniq
    hεN1 hεN2 hεeq
  obtain ⟨nX, hnX, fX, hπnX, hfX, hclosX⟩ :=
    ggCover_weyl π hπ hZR ε hεE hεsurj hεN1 hεeq θ hθ wt hwt
  have hactX : ∀ k s, π (nX k) * ιT (Multiplicative.ofAdd s) * (π (nX k))⁻¹ =
      ιT (Multiplicative.ofAdd (TableBExc.torusAct .F4 p (simple .F4 k) s)) := by
    intro k s
    rw [hπnX, hwn]
    exact hact k s
  obtain ⟨V, hVadd, hVmod, ιB, φ, h, α, f, κ, hlin, hrefl, hpair, hf, hclos, hκ, hα, hh, hTD,
    hFε⟩ := f4Levi_datum (p := p) hp2 hBs hZp π ε hεE hεsurj hεker hεX hεlift
      ιT hιTinj hιTrange nX hnX hactX fX hfX hclosX
  have hVfin : Finite V := Finite.of_injective
    (fun x : V => Additive.toMul (ιB.symm x))
    (fun x y h => by
      apply ιB.symm.injective
      exact Additive.toMul.injective h)
  have hofAdd_inj : ∀ {s t : Fin Tag.F4.rank → ZMod p},
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
  obtain ⟨t_g, ht_g⟩ := MonoidHom.mem_range.mp (hιTrange ▸ hεE gB)
  let s_g : Fin Tag.F4.rank → ZMod p := Multiplicative.toAdd t_g
  have hsg : ιT (Multiplicative.ofAdd s_g) = ε gB := ht_g
  have htg1 : ιT (Multiplicative.ofAdd s_g) ≠ 1 := by rw [hsg]; exact hgne
  have hsg0 : s_g ≠ 0 := by
    intro h0
    apply htg1
    rw [h0]
    exact map_one ιT
  let a : Fin Tag.F4.rank → Lfˣ :=
    TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 p s_g)
  have hdet : IsUnit ((Tag.F4.symmetrizedCartan.det : ℤ) : ZMod p) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inl rfl) hp2
  have ha : ∀ j, a j ^ p = 1 := by
    intro j
    change (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 p s_g) j) ^ p = 1
    rw [TableBExc.E6Three.zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have ha1 : ∃ j, a j ≠ 1 := by
    by_contra hc
    have h1 : ∀ j, a j = 1 := fun j => by
      by_contra hj
      exact hc ⟨j, hj⟩
    have hone : TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 p s_g) = 1 := by
      funext j
      exact h1 j
    have hzero : ExcFrames.frameCoord .F4 p s_g = ExcFrames.frameCoord .F4 p 0 := by
      apply TableBExc.E6Three.zetaVec_injective hζo hζ
      rw [ExcFrames.frameCoord_zero, hone]
      funext j
      rw [TableBExc.E6Three.zetaVec_apply]
      simp
    exact hsg0 (ExcFrames.frameCoord_injective hdet hzero)
  have hprim : IsPrimitiveRoot (ζ : Lf) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hζo)
  let Jsub : Subgroup ↥X := J.subgroupOf X
  let Y : Subgroup R := Jsub.map π
  obtain ⟨hY₀, hCENTJ⟩ := ggCover_component hBs hgBs hXB hZp π hπ hker Λ hΛc hΛn
    (hεconj gB) hJX hcomp
  have hY : IsComponentOf Y
      (Subgroup.centralizer ({ιT (Multiplicative.ofAdd s_g)} : Set R)) := by
    change IsComponentOf ((J.subgroupOf X).map π)
      (Subgroup.centralizer ({ιT (Multiplicative.ofAdd s_g)} : Set R))
    rw [hsg]
    exact hY₀
  obtain ⟨i, hCENT, hLow⟩ := hcl s_g htg1 Y hY
  have hlift_cent : ∀ s : Fin Tag.F4.rank → ZMod p,
      ιT (Multiplicative.ofAdd s) ∈ Subgroup.centralizer (Y : Set R) →
      ∃ b : ↥Bs, (b : G) ∈ X ∧ ε b = ιT (Multiplicative.ofAdd s) ∧
        (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    intro s hcent
    obtain ⟨bs, hbsε⟩ := hεsurj (ιT (Multiplicative.ofAdd s))
      (by rw [← hιTrange]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    obtain ⟨x, hxB, hxε⟩ := hεlift bs
    let b : ↥Bs := ⟨(x : G), hxB⟩
    have hbX : (b : G) ∈ X := x.2
    have hbε : ε b = ιT (Multiplicative.ofAdd s) :=
      (hεX b hbX).trans (hxε.trans hbsε)
    refine ⟨b, hbX, hbε, hCENTJ b (ιT (Multiplicative.ofAdd s)) ?_ hcent⟩
    rw [← hbε]
    exact hεconj b
  let dF : Fin Tag.F4.rank → ZMod p := fun j => (((![2, 2, 1, 1] : Fin 4 → ℤ) j : ℤ) : ZMod p)
  let A : V →ₗ[ZMod p] (Fin Tag.F4.rank → ZMod p) :=
    { toFun := fun w j => dF j * α j w
      map_add' := by
        intro x y
        funext j
        simp only [map_add, mul_add, Pi.add_apply]
      map_smul' := by
        intro c x
        funext j
        simp only [map_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply]
        ring }
  have hAframe : ∀ (b : ↥Bs) (s : Fin Tag.F4.rank → ZMod p),
      ιT (Multiplicative.ofAdd s) = ε b →
      A (ιB (Additive.ofMul b)) = ExcFrames.frameCoord .F4 p s := by
    intro b s hs
    funext j
    show dF j * α j (ιB (Additive.ofMul b)) = _
    rw [hα b s hs j, f4lf_frameCoord_eq]
  have hA_surj : Function.Surjective A := by
    intro u
    have hfc : Function.Surjective (ExcFrames.frameCoord .F4 p) :=
      Finite.injective_iff_surjective.mp (ExcFrames.frameCoord_injective hdet)
    obtain ⟨s, hs⟩ := hfc u
    obtain ⟨b, hb⟩ := hεsurj (ιT (Multiplicative.ofAdd s))
      (by rw [← hιTrange]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩)
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
    show dF j * α j (ιB (Additive.ofMul bX)) = 0
    rw [hbXα j, mul_zero]
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
      obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp (hιTrange ▸ hεE b.1)
      let t' : Fin Tag.F4.rank → ZMod p := Multiplicative.toAdd t
      have ht' : ιT (Multiplicative.ofAdd t') = ε b.1 := ht
      have hcent : ιT (Multiplicative.ofAdd t') ∈
          Subgroup.centralizer (Y : Set (R)) :=
        hCENT t' (fun γ hγ => by
          have h1 := b.2 γ hγ
          rwa [hAframe b.1 t' ht'] at h1)
      obtain ⟨ebs, -, hebsε, hebsC⟩ := hlift_cent t' hcent
      have hkeps : ε (b.1 * ebs⁻¹) = 1 := by
        rw [map_mul, map_inv, hebsε, ht', mul_inv_cancel]
      have hkCJ : ((b.1 * ebs⁻¹ : ↥Bs) : G) ∈ Subgroup.centralizer (J : Set G) :=
        Subgroup.centralizer_le hJX ((hεker (b.1 * ebs⁻¹)).1 hkeps)
      have hb_eq : b.1 = ebs * (b.1 * ebs⁻¹) := by
        rw [(isMulCommutative_iff.mp hBs.1) b.1 ebs⁻¹]
        group
      refine ⟨b.1.2, ?_⟩
      rw [show (b.1 : G) = (ebs : G) * ((b.1 * ebs⁻¹ : ↥Bs) : G) from
        congrArg Subtype.val hb_eq]
      exact Subgroup.mul_mem _ hebsC hkCJ
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
  have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by
    have hrank : Tag.F4.rank = 4 := rfl
    have := le_compRank_of_finrank_ggRootAnn (p := p)
      (componentRoots (rootCharHom a) i) (d := 2) hfin_le
    omega
  obtain ⟨v₀, S, hS, hΨeq⟩ := f4_class_levi hp hp2 hprim a ha ha1 i h2
  let F : WeylGroup .F4 →* ↥(ggAutomizer X Bs) := f.toMonoidHom.comp κ.toMonoidHom
  let ψ : WeylGroup .F4 →* MulAut ↥Bs := (ggAutomizer X Bs).subtype.comp F
  have hψ : ∀ u, ψ u = (f (κ u) : MulAut ↥Bs) := fun u => rfl
  have hlower : ∀ c ∈ componentRoots (rootCharHom a) i,
      ψ (rootReflection c) ∈ ggAutomizer J Bs := by
    intro c hc
    obtain ⟨gY, hgYY, hactc⟩ := hLow v₀ S hS hΨeq c hc
    obtain ⟨jX, hjJsub, hje⟩ := Subgroup.mem_map.mp hgYY
    have hjJ : (jX : G) ∈ J := Subgroup.mem_subgroupOf.mp hjJsub
    have hmapE : E.map (MulAut.conj gY).toMonoidHom = E := by
      apply le_antisymm
      · rintro x ⟨y, hy, rfl⟩
        obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp (hιTrange.symm ▸ hy)
        let s : Fin Tag.F4.rank → ZMod p := Multiplicative.toAdd t
        have hs : ιT (Multiplicative.ofAdd s) = y := ht
        change gY * y * gY⁻¹ ∈ E
        rw [← hs, hactc s, ← hιTrange]
        exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
      · intro x hx
        obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp (hιTrange.symm ▸ hx)
        let s : Fin Tag.F4.rank → ZMod p := Multiplicative.toAdd t
        have hs : ιT (Multiplicative.ofAdd s) = x := ht
        refine Subgroup.mem_map.mpr ⟨ιT (Multiplicative.ofAdd
          (TableBExc.torusAct .F4 p (rootReflection c)⁻¹ s)), ?_, ?_⟩
        · rw [← hιTrange]
          exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
        · rw [← hs]
          change gY * ιT (Multiplicative.ofAdd
            (TableBExc.torusAct .F4 p (rootReflection c)⁻¹ s)) * gY⁻¹ =
              ιT (Multiplicative.ofAdd s)
          rw [hactc, ← TableBExc.torusAct_mul, mul_inv_cancel, TableBExc.torusAct_one]
    have hgYN : gY ∈ Subgroup.normalizer (E : Set (R)) :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).2 hmapE
    have hjN : (jX : G) ∈ Subgroup.normalizer (Bs : Set G) :=
      hεN1 jX (hje ▸ hgYN)
    let jsub : ↥(J ⊓ Subgroup.normalizer (Bs : Set G)) := ⟨(jX : G), hjJ, hjN⟩
    have htJ : ggTDρB J Bs jsub ∈ ggAutomizer J Bs := by
      rw [← ggTDρB_range]
      exact ⟨jsub, rfl⟩
    let jXinf : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)) := ⟨(jX : G), jX.2, hjN⟩
    have htXD : ggTDρB X Bs jXinf = (f (κ (rootReflection c)) : MulAut ↥Bs) := by
      refine hTD jXinf (rootReflection c) ?_
      intro s
      have h1 : π ⟨jXinf, jXinf.2.1⟩ = gY := hje
      rw [h1]
      exact hactc s
    rw [hψ, ← htXD]
    exact htJ
  have hupper : ∀ t ∈ ggAutomizer J Bs,
      t ∈ (Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i)).map ψ := by
    intro t ht
    obtain ⟨j, hjJ, hjN, hφt⟩ := mem_ggAutomizer_iff.mp ht
    have htX : t ∈ ggAutomizer X Bs := mem_ggAutomizer_iff.mpr ⟨j, hJX hjJ, hjN, hφt⟩
    let w : WeylGroup .F4 := κ.symm (f.symm ⟨t, htX⟩)
    have hFw : ψ w = t := by
      rw [hψ]
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
    have hws : TableBExc.torusAct .F4 p w s_g = s_g := by
      have h1 := hFε w gB s_g hsg
      rw [← hψ, hFw, htg, ← hsg] at h1
      exact (hofAdd_inj (hιTinj h1)).symm
    have hwinv : TableBExc.torusAct .F4 p w⁻¹ s_g = s_g := by
      have h1 := congrArg (TableBExc.torusAct .F4 p w⁻¹) hws
      rw [← TableBExc.torusAct_mul, inv_mul_cancel, TableBExc.torusAct_one] at h1
      exact h1.symm
    have hwstab : w ∈ rootCharStabilizerSubgroup a := by
      rw [mem_rootCharStabilizerSubgroup]
      intro c
      rw [NoOffE8Five.rootChar_zetaVec hζ, NoOffE8Five.rootChar_zetaVec hζ,
        f4lf_sum_frameCoord_smul w c s_g hwinv]
    have hwfix : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
        ∀ j, ((w • c) j : ZMod p) = (c j : ZMod p) := by
      intro c hcK hcΨ
      have horth : ∀ γ ∈ componentRoots (rootCharHom a) i,
          ∑ j, (γ j : ZMod p) * ExcFrames.frameCoord .F4 p (TableBExc.redMod .F4 p c) j = 0 := by
        intro γ hγ
        have hc_mem : c ∈ componentRoots (rootCharHom a) ⟦⟨c, hcK⟩⟧ := ⟨hcK, rfl⟩
        have hne : (⟦⟨c, hcK⟩⟧ : KernelComponent (rootCharHom a)) ≠ i := by
          intro heq
          exact hcΨ (by rwa [heq] at hc_mem)
        have hform : CFSG.LieType.Steinberg.Adjoint.iform γ c = 0 :=
          CFSG.LieType.Chevalley.iform_eq_zero_of_mem_componentRoots hne.symm hγ hc_mem
        rw [f4lf_sum_frameCoord]
        have hcong : ((CFSG.LieType.Steinberg.Adjoint.iform γ
            (TableBExc.liftMod .F4 p (TableBExc.redMod .F4 p c)) : ℤ) : ZMod p) =
            ((CFSG.LieType.Steinberg.Adjoint.iform γ c : ℤ) : ZMod p) := by
          simp only [CFSG.LieType.Steinberg.Adjoint.iform]
          push_cast
          refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
          simp [TableBExc.liftMod, TableBExc.redMod]
        rw [hcong, hform, Int.cast_zero]
      have hcent := hCENT (TableBExc.redMod .F4 p c) horth
      obtain ⟨ebs, -, hebsε, hebsC⟩ := hlift_cent (TableBExc.redMod .F4 p c) hcent
      have h1 := hFε w ebs (TableBExc.redMod .F4 p c) hebsε.symm
      rw [← hψ, hFw, htfix ebs hebsC, hebsε] at h1
      have h2 : TableBExc.torusAct .F4 p w (TableBExc.redMod .F4 p c) =
          TableBExc.redMod .F4 p c := (hofAdd_inj (hιTinj h1)).symm
      have h3 : TableBExc.torusAct .F4 p w (TableBExc.redMod .F4 p c) =
          TableBExc.redMod .F4 p (w • c) :=
        TableBExc.redMod_smul_eq w (TableBExc.redMod_liftMod (TableBExc.redMod .F4 p c))
      intro j
      have h4 := congrFun (h3.symm.trans h2) j
      simpa [TableBExc.redMod] using h4
    have hwcl := mem_closure_rootReflection_of_fix_F4 hp hp2 ha i hwstab hwfix
    exact ⟨w, hwcl, hFw⟩
  have hJeq : ggAutomizer J Bs =
      (Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i)).map ψ := by
    apply le_antisymm
    · intro t ht
      exact hupper t ht
    · rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨r, ⟨c, hc, rfl⟩, rfl⟩
      exact hlower c hc
  have hset : Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) =
      Subgroup.closure {s : WeylGroup .F4 | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ} := by
    congr 1
    ext s
    simp only [Set.mem_image, Set.mem_setOf_eq]
    exact ⟨fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩, fun ⟨γ, hγ, e⟩ => ⟨γ, hγ, e.symm⟩⟩
  have hpar : Subgroup.closure (rootReflection '' componentRoots (rootCharHom a) i) =
      Subgroup.closure ((fun j : Fin 4 => v₀ * simple .F4 j * v₀⁻¹) '' {j : Fin 4 | j ∉ S}) := by
    rw [hset, hΨeq, closure_rootReflection_smul_parabolicRoots (τ := .F4) v₀]
    rfl
  have hψsimple : ∀ j, ψ (simple .F4 j) = φ j := by
    intro j
    rw [hψ, hκ j]
    exact hf j
  let u : CoxeterMatrix.F₄.Group := κ v₀
  have hJ' : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin 4 // j ∉ S} =>
        (f u : MulAut ↥Bs) * φ j.1 * (f u : MulAut ↥Bs)⁻¹) := by
    rw [hJeq, hpar, MonoidHom.map_closure, Set.image_image, Set.image_eq_range]
    congr 1
    ext t
    simp only [Set.mem_range, Subtype.exists]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, by rw [map_mul, map_mul, map_inv, hψsimple j, hψ v₀]⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, by rw [map_mul, map_mul, map_inv, hψsimple j, hψ v₀]⟩
  exact ggF4LeviDatum_of_conj hp2 hlin hrefl hpair hf hclos u hS hJ'

theorem ggGamma_range_eq_liftConj_of_equiv {G : Type} [Group G] {Bs X : Subgroup G}
    (hXB : Bs ≤ Subgroup.normalizer (X : Set G)) {R : Type} [Group R]
    (hZR : Subgroup.center R = ⊥) (e : ↥X ≃* R) {E : Subgroup R}
    (hA : (ggGamma X hXB).range.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : R →* MulAut (R))) :
    Subgroup.center ↥X = ⊥ ∧ ∃ hker : (e : ↥X →* R).ker ≤ Subgroup.center ↥X,
      (ggGamma X hXB).range = E.map (ReflInner.liftConj e.toMonoidHom e.surjective hker) := by
  have hZ : Subgroup.center ↥X = ⊥ := by
    have hmap : (Subgroup.center ↥X).map (e : ↥X →* R) = ⊥ := by
      rw [Subgroup.map_center_eq, hZR]
    rw [Subgroup.map_eq_bot_iff, MonoidHom.ker_eq_bot (e : ↥X →* R) e.injective] at hmap
    exact le_bot_iff.mp hmap
  have hker : (e : ↥X →* R).ker ≤ Subgroup.center ↥X := by
    rw [MonoidHom.ker_eq_bot (e : ↥X →* R) e.injective]
    exact bot_le
  refine ⟨hZ, hker, ?_⟩
  have hcomp : (MulAut.congr e).toMonoidHom.comp
      (ReflInner.liftConj e.toMonoidHom e.surjective hker) =
      (MulAut.conj : R →* MulAut R) := by
    apply MonoidHom.ext
    intro r
    obtain ⟨x, rfl⟩ := e.surjective r
    rw [MonoidHom.comp_apply, ReflInner.liftConj_eq (ψ := e.toMonoidHom) e.surjective hker
      (show e.toMonoidHom x = e x from rfl)]
    exact congr_conj e x
  apply Subgroup.map_injective (f := (MulAut.congr e).toMonoidHom) (MulAut.congr e).injective
  rw [hA, Subgroup.map_map, hcomp]

theorem ggTBJF4LeviL_of_cover
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hZp : ∀ z ∈ Subgroup.center ↥L, z ^ p = 1 → z = 1)
    {R : Type} [Group R] (hZR : Subgroup.center R = ⊥)
    (π : ↥L →* R) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    {E : Subgroup R} (hA : (ggGamma L hN).range = E.map (ReflInner.liftConj π hπ hker))
    (hF : GGF4LeviFrame p E) :
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
  exact ggTBJF4Levi_of_cover_frame hp2 hBs hSC hN hJX hyBs hJg hgX hcomp hZp hZR π hπ hker hA hF
    ⟨x, hxBs⟩ hx1' hbXc hcardJ

theorem ggTBJF4LeviL_of_model
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hM : GGF4LeviModel p Bs L) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  obtain ⟨hN, R, _, hZR, e, E, hA, hF⟩ := hM
  obtain ⟨hZ, hker, hA'⟩ := ggGamma_range_eq_liftConj_of_equiv hN hZR e hA
  exact ggTBJF4LeviL_of_cover hH hN (fun z hz _ => by rwa [hZ, Subgroup.mem_bot] at hz) hZR
    e.toMonoidHom e.surjective hker hA' hF

theorem ggTBJF4LeviK_of_cover
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hZp : ∀ z ∈ Subgroup.center ↥K, z ^ p = 1 → z = 1)
    {R : Type} [Group R] (hZR : Subgroup.center R = ⊥)
    (π : ↥K →* R) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥K)
    {E : Subgroup R} (hA : (ggGamma K hN).range = E.map (ReflInner.liftConj π hπ hker))
    (hF : GGF4LeviFrame p E) :
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
  exact ggTBJF4Levi_of_cover_frame hp2 hBs hSC hN hJK hxBs hJg hgX hcomp hZp hZR π hπ hker hA hF
    ⟨y, hyBs⟩ hy1' hbXc hcardJ

theorem ggTBJF4LeviK_of_model
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K) (hM : GGF4LeviModel p Bs K) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  obtain ⟨hN, R, _, hZR, e, E, hA, hF⟩ := hM
  obtain ⟨hZ, hker, hA'⟩ := ggGamma_range_eq_liftConj_of_equiv hN hZR e hA
  exact ggTBJF4LeviK_of_cover hH hJK hN (fun z hz _ => by rwa [hZ, Subgroup.mem_bot] at hz) hZR
    e.toMonoidHom e.surjective hker hA' hF

end CFSG.StandardType

end
