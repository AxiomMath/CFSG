module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnComp
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnModel
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviClass
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviStab
public import CFSG.LocalAnalysis.StandardType.GGTBJE8Tag
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LangGlue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriLab

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

private theorem labelIso_rank8 {lab lab' : LargeEvenLabel} (h : GGLabelIso lab lab')
    (ht : lab'.tag = .A ∨ lab'.tag = .twA) (hr : lab'.rank = 8) : lab = lab' := by
  obtain ⟨t, l, m⟩ := lab
  obtain ⟨t', l', m'⟩ := lab'
  dsimp only at ht hr
  subst hr
  unfold GGLabelIso at h
  rcases ht with rfl | rfl <;> rcases h with h | h | h | h | h | h | h | h <;>
    first | exact h | (exfalso; simp_all)

@[expose] def GGE8LeviFrame (p : ℕ) [NeZero p] {Fq : Type}
    [Field Fq] (E : Subgroup (adjointGroup .E8 Fq)) : Prop :=
  ∃ (Lf : Type) (_ : Field Lf) (ζ : Lfˣ) (hζ : ζ ^ p = 1)
    (ι₀ : Multiplicative (Fin Tag.E8.rank → ZMod p) →* adjointGroup .E8 Fq)
    (nk : Fin Tag.E8.rank → adjointGroup .E8 Fq) (m : ℕ)
    (wt : GGTorusTorWit m 8 (adjointGroup .E8 Fq)
      (E.map (MulAut.conj : adjointGroup .E8 Fq →* MulAut (adjointGroup .E8 Fq)))),
    orderOf ζ = p ∧ Function.Injective ι₀ ∧ ι₀.range = E ∧
    (∀ k s, nk k * ι₀ (Multiplicative.ofAdd s) * (nk k)⁻¹ =
      ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E8 p (simple .E8 k) s))) ∧
    (∀ k, wt.n k = nk k) ∧ wt.Holds CartanMatrix.E₈ CoxeterMatrix.E₈ ∧
    ∀ t : Fin Tag.E8.rank → ZMod p, ι₀ (Multiplicative.ofAdd t) ≠ 1 →
      ∀ Y : Subgroup (adjointGroup .E8 Fq), IsComponentOf Y
        (Subgroup.centralizer ({ι₀ (Multiplicative.ofAdd t)} : Set (adjointGroup .E8 Fq))) →
      ∃ i : KernelComponent
          (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E8 p t))),
        (∀ s : Fin Tag.E8.rank → ZMod p,
          (∀ γ ∈ componentRoots
              (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E8 p t))) i,
            ∑ j, (γ j : ZMod p) * ExcFrames.frameCoord .E8 p s j = 0) →
          ι₀ (Multiplicative.ofAdd s) ∈ Subgroup.centralizer (Y : Set (adjointGroup .E8 Fq))) ∧
        (∀ (v : WeylGroup .E8) (Sd : Finset (Fin 8)), Sd ∈ e8LeviDel →
          componentRoots
              (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E8 p t))) i =
            (fun α => v • α) '' parabolicRoots .E8 {j | j ∉ Sd} →
          ∀ c ∈ componentRoots
              (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E8 p t))) i,
            ∃ y ∈ Y, ∀ s, y * ι₀ (Multiplicative.ofAdd s) * y⁻¹ =
              ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E8 p (rootReflection c) s))) ∧
        (p = 3 → ∀ v : WeylGroup .E8,
          componentRoots
              (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E8 p t))) i =
            (fun α => v • α) '' kacE8.rootsOf (e8A8Nodes : Set (Option (Fin Tag.E8.rank))) →
          ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ (lab.tag = .A ∨ lab.tag = .twA) ∧
            lab.rank = 8 ∧ GGHasLabel lab (↥Y ⧸ Subgroup.center ↥Y))

@[expose] def GGE8LeviModel (p : ℕ) [NeZero p] {G : Type} [Group G]
    (Bs X : Subgroup G) : Prop :=
  ∃ (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
    (_ : CharP Fq 2) (e : ↥X ≃* adjointGroup .E8 Fq) (E : Subgroup (adjointGroup .E8 Fq)),
    (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
        E.map (MulAut.conj : adjointGroup .E8 Fq →* MulAut (adjointGroup .E8 Fq)) ∧
      GGE8LeviFrame p E

private theorem ggReflFormula
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : Fin 8 → MulAut ↥Bs} {h : Fin 8 → V} {α : Fin 8 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    {F : WeylGroup .E8 →* ↥(ggAutomizer X Bs)}
    (hF : ∀ i, (F (simple .E8 i) : MulAut ↥Bs) = φ i)
    (hFh : ∀ (u : WeylGroup .E8) (c : Fin Tag.E8.rank → ℤ),
      ggLin (p := p) ι (F u : MulAut ↥Bs) (∑ j, (c j : ZMod p) • h j) =
        ∑ j, ((u • c) j : ZMod p) • h j)
    (hFα : ∀ (u : WeylGroup .E8) (c : Fin Tag.E8.rank → ℤ) (w : V),
      ∑ j, ((u • c) j : ZMod p) * α j (ggLin (p := p) ι (F u : MulAut ↥Bs) w) =
        ∑ j, (c j : ZMod p) * α j w)
    {c : Fin Tag.E8.rank → ℤ} (hc : IsRoot .E8 c) (w : V) :
    ggLin (p := p) ι ((F (rootReflection c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) w =
      w - (∑ j, (c j : ZMod p) * α j w) • ∑ j, (c j : ZMod p) • h j := by
  obtain ⟨u, j, huj⟩ := isRoot_iff_exists_smul_single.1 hc
  have hroot : rootReflection c = u * simple .E8 j * u⁻¹ := rootReflection_eq_conj huj
  have huc : u⁻¹ • c = (Pi.single j 1 : Fin Tag.E8.rank → ℤ) := by
    rw [← huj, ← mul_smul, inv_mul_cancel, one_smul]
  have hHj : (∑ k, ((Pi.single j 1 : Fin Tag.E8.rank → ℤ) k : ZMod p) • h k) = h j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have hFroot : ((F (rootReflection c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
      (F u : MulAut ↥Bs) * (F (simple .E8 j) : MulAut ↥Bs) *
        (F u⁻¹ : MulAut ↥Bs) := by
    rw [hroot]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hcancel : ggLin (p := p) ι (F u : MulAut ↥Bs)
      (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) = w := by
    rw [← LinearEquiv.mul_apply, ← map_mul]
    simp
  have hFuh : ggLin (p := p) ι (F u : MulAut ↥Bs) (h j) =
      ∑ k, (c k : ZMod p) • h k := by
    have h1 := hFh u (Pi.single j 1)
    rw [hHj, huj] at h1
    exact h1
  have hAj : α j (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) =
      ∑ k, (c k : ZMod p) * α k w := by
    have h1 := hFα u⁻¹ c w
    rw [huc] at h1
    have hsingle : (∑ k, ((Pi.single j 1 : Fin Tag.E8.rank → ℤ) k : ZMod p) *
        α k (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w)) =
        α j (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rwa [hsingle] at h1
  calc
    ggLin (p := p) ι ((F (rootReflection c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) w
        = ggLin (p := p) ι (F u : MulAut ↥Bs)
            (ggLin (p := p) ι (F (simple .E8 j) : MulAut ↥Bs)
              (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w)) := by
          rw [hFroot, map_mul, LinearEquiv.mul_apply, map_mul, LinearEquiv.mul_apply]
    _ = ggLin (p := p) ι (F u : MulAut ↥Bs)
            (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w -
              α j (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) • h j) := by
          rw [hF j, hlin j]
    _ = ggLin (p := p) ι (F u : MulAut ↥Bs)
            (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) -
          α j (ggLin (p := p) ι (F u⁻¹ : MulAut ↥Bs) w) •
            ggLin (p := p) ι (F u : MulAut ↥Bs) (h j) := by
          rw [map_sub, map_smul]
    _ = w - (∑ k, (c k : ZMod p) * α k w) • ∑ k, (c k : ZMod p) • h k := by
          rw [hcancel, hAj, hFuh]

theorem ggE8Levi_input_of_frame
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J X : Subgroup G} {g : G} (hp2 : p ≠ 2)
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ p = 1 → a ∈ Bs)
    (hXB : Bs ≤ Subgroup.normalizer (X : Set G))
    (hJX : J ≤ X) (hgBs : g ∈ Bs)
    (hJg : J ≤ Subgroup.centralizer ({g} : Set G))
    (hgX : ∃ l ∈ X, g * l * g⁻¹ ≠ l)
    (hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({g} : Set G)))
    (hZ : Subgroup.center ↥X = ⊥)
    {Fq : Type} [Field Fq] [Finite Fq] [CharP Fq 2]
    (e : ↥X ≃* adjointGroup .E8 Fq) {E : Subgroup (adjointGroup .E8 Fq)}
    (hA : (ggGamma X hXB).range.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : adjointGroup .E8 Fq →* MulAut (adjointGroup .E8 Fq)))
    (hF : GGE8LeviFrame p E) (bX : ↥Bs) (hbX1 : bX ≠ 1)
    (hbXc : (bX : G) ∈ Subgroup.centralizer (X : Set G))
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hnA8 : ¬ ((labJ.tag = .A ∨ labJ.tag = .twA) ∧ labJ.rank = 8))
    (hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Fin 8 → MulAut ↥Bs) (h : Fin 8 → V) (α : Fin 8 → Module.Dual (ZMod p) V)
      (f : CoxeterMatrix.E₈.Group ≃* ↥(ggAutomizer X Bs)),
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p)) ∧
      (∀ i, (f (CoxeterMatrix.E₈.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (∃ b : ↥Bs, b ≠ 1 ∧ ∀ j, α j (ι (Additive.ofMul b)) = 0) ∧
      ∃ (Lf : Type) (_ : Field Lf) (ζ : Lfˣ) (a : Fin Tag.E8.rank → Lfˣ) (g : ↥Bs)
        (i : KernelComponent (rootCharHom a)),
        IsPrimitiveRoot (ζ : Lf) p ∧ (∀ j, a j ^ p = 1) ∧ (∃ j, a j ≠ 1) ∧
        (∀ v : Fin Tag.E8.rank → ℤ, rootCharHom a (Multiplicative.ofAdd v) =
          ζ ^ (∑ j, (v j : ZMod p) * α j (ι (Additive.ofMul g))).val) ∧
        (∀ c ∈ componentRoots (rootCharHom a) i, ∃ t ∈ ggAutomizer J Bs, ∀ w,
          ggLin (p := p) ι t w = w - (∑ j, (c j : ZMod p) * α j w) • ∑ j, (c j : ZMod p) • h j) ∧
        (∀ t ∈ ggAutomizer J Bs, t ∈ ggAutomizer X Bs ∧ t g = g ∧
          ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
            ggLin (p := p) ι t (∑ j, (c j : ZMod p) • h j) = ∑ j, (c j : ZMod p) • h j) ∧
        Nat.card {b : ↥Bs // ∀ c ∈ componentRoots (rootCharHom a) i,
          ∑ j, (c j : ZMod p) * α j (ι (Additive.ofMul b)) = 0} ≤ p ^ 3 ∧
        (p = 3 → ∀ v : WeylGroup .E8, componentRoots (rootCharHom a) i ≠
          (fun c => v • c) '' kacE8.rootsOf (e8A8Nodes : Set (Option (Fin Tag.E8.rank)))) := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨Lf, _, ζ, hζ, ιT, nk, m, wt, hζo, hιTinj, hιTrange, hact, hwn, hwt, hcl⟩ := hF
  obtain ⟨ε, hεconj, hεE, hεsurj, hεker, hεX, hεBs, hεN1, hεN2, hεeq⟩ :=
    e8Enn_bstar hBs hSC hXB e hA
  obtain ⟨V, hVadd, hVmod, ιB, φ, h, α, f, κ, hlin, hrefl, hpair, hf, hclos, hκ, hα, hh, hTD⟩ :=
    e8Enn_datum (p := p) hp2 hBs hSC hXB hZ e hA ε hεE hεsurj hεker hεX hεBs
      ιT hιTinj hιTrange nk hact wt hwn hwt
  have hVfin : Finite V := Finite.of_injective
    (fun x : V => Additive.toMul (ιB.symm x))
    (fun x y h => by
      apply ιB.symm.injective
      exact Additive.toMul.injective h)
  have : Finite V := hVfin
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
    have h1 : ExcFrames.frameCoord .E8 p (0 : Fin Tag.E8.rank → ZMod p) j = 0 := by
      simp [ExcFrames.frameCoord]
    rwa [h1] at h0
  have hX : ∃ b : ↥Bs, b ≠ 1 ∧ ∀ j, α j (ιB (Additive.ofMul b)) = 0 :=
    ⟨bX, hbX1, hbXα⟩
  obtain ⟨t_g, ht_g⟩ := MonoidHom.mem_range.mp (hιTrange ▸ hεE gB)
  let s_g : Fin Tag.E8.rank → ZMod p := Multiplicative.toAdd t_g
  have hsg : ιT (Multiplicative.ofAdd s_g) = ε gB := ht_g
  have htg1 : ιT (Multiplicative.ofAdd s_g) ≠ 1 := by rw [hsg]; exact hgne
  have hsg0 : s_g ≠ 0 := by
    intro h0
    apply htg1
    rw [h0]
    exact map_one ιT
  let a : Fin Tag.E8.rank → Lfˣ :=
    TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E8 p s_g)
  have hdet : IsUnit ((Tag.E8.symmetrizedCartan.det : ℤ) : ZMod p) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inr rfl)) hp2
  have ha : ∀ j, a j ^ p = 1 := by
    intro j
    change (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E8 p s_g) j) ^ p = 1
    rw [TableBExc.E6Three.zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have ha1 : ∃ j, a j ≠ 1 := by
    by_contra h
    have h1 : ∀ j, a j = 1 := fun j => by
      by_contra hj
      exact h ⟨j, hj⟩
    have hone : TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E8 p s_g) = 1 := by
      funext j
      exact h1 j
    have hzero : ExcFrames.frameCoord .E8 p s_g = ExcFrames.frameCoord .E8 p 0 := by
      apply TableBExc.E6Three.zetaVec_injective hζo hζ
      rw [ExcFrames.frameCoord_zero, hone]
      funext j
      rw [TableBExc.E6Three.zetaVec_apply]
      simp
    have hs0 : s_g = 0 := ExcFrames.frameCoord_injective hdet hzero
    exact hsg0 hs0
  have hprim : IsPrimitiveRoot (ζ : Lf) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hζo)
  have hαg : ∀ j, α j (ιB (Additive.ofMul gB)) = ExcFrames.frameCoord .E8 p s_g j :=
    fun j => hα gB s_g hsg j
  have hχ : ∀ v : Fin Tag.E8.rank → ℤ,
      rootCharHom a (Multiplicative.ofAdd v) =
        ζ ^ (∑ j, (v j : ZMod p) * α j (ιB (Additive.ofMul gB))).val := by
    intro v
    change rootChar (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E8 p s_g)) v = _
    rw [NoOffE8Five.rootChar_zetaVec hζ, CFSG.RankThree.CentralCover.zmodPowHom_apply]
    have hsum : (∑ j, (v j : ZMod p) * ExcFrames.frameCoord .E8 p s_g j) =
        ∑ j, (v j : ZMod p) * α j (ιB (Additive.ofMul gB)) :=
      Finset.sum_congr rfl fun j _ => by rw [hαg j]
    rw [hsum]
  have hconjX : ∀ x : ↥X, e (ggGamma X hXB gB x) = ε gB * e x * (ε gB)⁻¹ := by
    intro x
    have h' := congrArg (fun c : MulAut (adjointGroup .E8 Fq) => c (e x)) (hεconj gB)
    rw [MulAut.conj_apply] at h'
    simpa using h'
  let C : Subgroup G := X ⊓ Subgroup.centralizer ({g} : Set G)
  let Csub : Subgroup ↥X := C.subgroupOf X
  let Jsub : Subgroup ↥X := J.subgroupOf X
  have hCeq : C = X ⊓ Subgroup.centralizer ({g} : Set G) := rfl
  have hcompC : IsComponentOf J C := hcomp
  have hcompX : IsComponentOf Jsub Csub := by
    have hle : Jsub ≤ Csub := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hcompC.1 (Subgroup.mem_subgroupOf.mp hx))
    refine ⟨hle, ?_, ?_⟩
    · rw [CFSG.Assembly.IsSubnormal.iff_subgroupOf hle]
      have hsn : (J.subgroupOf C).IsSubnormal :=
        CFSG.Assembly.IsSubnormal.subgroupOf hcompC.2.1
      let φ : ↥Csub →* ↥C :=
        { toFun := fun x => ⟨(x.1 : G), x.1.2, (Subgroup.mem_subgroupOf.mp x.2).2⟩
          map_one' := by ext; rfl
          map_mul' := by intro x y; ext; rfl }
      have hφ : (J.subgroupOf C).comap φ = Jsub.subgroupOf Csub := by
        ext x
        exact Iff.rfl
      rw [← hφ]
      exact Subgroup.IsSubnormal.comap φ hsn
    · exact (CFSG.Assembly.IsQuasisimple.congr
        (Subgroup.subgroupOfEquivOfLe hJX).symm).mp hcompC.2.2
  let Y : Subgroup (adjointGroup .E8 Fq) := Jsub.map (e : ↥X →* adjointGroup .E8 Fq)
  have hmemC : ∀ x : ↥X, e x ∈ Subgroup.centralizer ({ε gB} : Set (adjointGroup .E8 Fq)) ↔
      (x : G) ∈ Subgroup.centralizer ({g} : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hcx
      have hfix : e (ggGamma X hXB gB x) = e x := by
        rw [hconjX x, ← hcx]
        group
      have hgg : ggGamma X hXB gB x = x := e.injective hfix
      have hval : g * (x : G) * g⁻¹ = (x : G) := by
        have := congrArg Subtype.val hgg
        simpa [ggGamma_coe] using this
      calc (x : G) * g = (g * (x : G) * g⁻¹) * g := by rw [hval]
        _ = g * (x : G) := by group
    · intro hxg
      have hgg : ggGamma X hXB gB x = x := by
        apply Subtype.ext
        rw [ggGamma_coe]
        calc g * (x : G) * g⁻¹ = (x : G) * g * g⁻¹ := by rw [hxg.symm]
          _ = (x : G) := by group
      have hconj := hconjX x
      rw [hgg] at hconj
      calc e x * ε gB = (ε gB * e x * (ε gB)⁻¹) * ε gB := by
              conv_lhs => rw [hconj]
        _ = ε gB * e x := by group
  have hmapC : Csub.map (e : ↥X →* adjointGroup .E8 Fq) =
      Subgroup.centralizer ({ε gB} : Set (adjointGroup .E8 Fq)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmemC x).2 (Subgroup.mem_subgroupOf.mp hx).2
    · intro hy
      have hmem : (e.symm y : ↥X) ∈ Csub := by
        refine ⟨(e.symm y).2, ?_⟩
        exact (hmemC (e.symm y)).1 (by simpa using hy)
      exact ⟨e.symm y, hmem, by simp⟩
  have hY : IsComponentOf Y
      (Subgroup.centralizer ({ιT (Multiplicative.ofAdd s_g)} : Set (adjointGroup .E8 Fq))) := by
    have h' := isComponentOf_map_of_injective (e : ↥X →* adjointGroup .E8 Fq) e.injective hcompX
    rw [hmapC] at h'
    rwa [← hsg] at h'
  obtain ⟨i, hCENT, hLow, hA8c⟩ := hcl s_g htg1 Y hY
  let A : V →ₗ[ZMod p] (Fin Tag.E8.rank → ZMod p) :=
    { toFun := fun w j => α j w
      map_add' := by intro x y; funext j; exact map_add (α j) x y
      map_smul' := by intro c x; funext j; exact map_smul (α j) c x }
  have hA_surj : Function.Surjective A := by
    intro u
    have hfc : Function.Surjective (ExcFrames.frameCoord .E8 p) :=
      Finite.injective_iff_surjective.mp (ExcFrames.frameCoord_injective hdet)
    obtain ⟨s, hs⟩ := hfc u
    obtain ⟨b, hb⟩ := hεsurj (ιT (Multiplicative.ofAdd s))
      (by rw [← hιTrange]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    refine ⟨ιB (Additive.ofMul b), ?_⟩
    funext j
    show α j (ιB (Additive.ofMul b)) = u j
    rw [hα b s hb.symm j, hs]
  let Pre : Submodule (ZMod p) V :=
    (ggRootAnn p (componentRoots (rootCharHom a) i)).comap A
  have hPre_mem : ∀ w, w ∈ Pre ↔ ∀ c ∈ componentRoots (rootCharHom a) i,
      ∑ j, (c j : ZMod p) * α j w = 0 := by
    intro w
    exact Iff.rfl
  have hcard_sub : Nat.card {b : ↥Bs // ∀ c ∈ componentRoots (rootCharHom a) i,
        ∑ j, (c j : ZMod p) * α j (ιB (Additive.ofMul b)) = 0} = Nat.card ↥Pre := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv (Additive.ofMul.trans ιB.toEquiv) ?_
    intro b
    show (∀ c ∈ componentRoots (rootCharHom a) i,
        ∑ j, (c j : ZMod p) * α j (ιB (Additive.ofMul b)) = 0) ↔
      ιB (Additive.ofMul b) ∈ Pre
    rw [hPre_mem]
  let Apre : ↥Pre →+ ↥(ggRootAnn p (componentRoots (rootCharHom a) i)) :=
    { toFun := fun w => ⟨A w.1, w.2⟩
      map_zero' := by ext; simp [A]
      map_add' := by intro x y; apply Subtype.ext; funext j; exact congrFun (map_add A x.1 y.1) j }
  have hApre_surj : Function.Surjective Apre := by
    intro t
    obtain ⟨v, hv⟩ := hA_surj t.1
    refine ⟨⟨v, ?_⟩, ?_⟩
    · rw [hPre_mem]
      intro c hc
      have h0 := t.2 c hc
      rw [← hv] at h0
      simpa [A] using h0
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
      have hαj : α j v.1 = 0 := congrFun hv j
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
    exact hbXα j
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
    by_contra h
    have h0 : Module.finrank (ZMod p) ↥(LinearMap.ker A) = 0 := by omega
    rw [hcardker, h0, pow_zero] at hone_lt
    omega
  have hp_le : p ≤ Nat.card ↥(LinearMap.ker A) := by
    rw [hcardker]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ Module.finrank (ZMod p) ↥(LinearMap.ker A) :=
          Nat.pow_le_pow_right hp.pos hdpos
  have hcounted_upper : Nat.card {b : ↥Bs // ∀ c ∈ componentRoots (rootCharHom a) i,
        ∑ j, (c j : ZMod p) * α j (ιB (Additive.ofMul b)) = 0} ≤ p ^ 3 := by
    have hmem : ∀ b : {b : ↥Bs // ∀ c ∈ componentRoots (rootCharHom a) i,
        ∑ j, (c j : ZMod p) * α j (ιB (Additive.ofMul b)) = 0},
        (b.1 : G) ∈ Bs ⊓ Subgroup.centralizer (J : Set G) := by
      intro b
      obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp (hιTrange ▸ hεE b.1)
      let t' : Fin Tag.E8.rank → ZMod p := Multiplicative.toAdd t
      have ht' : ιT (Multiplicative.ofAdd t') = ε b.1 := ht
      have hcent : ιT (Multiplicative.ofAdd t') ∈
          Subgroup.centralizer (Y : Set (adjointGroup .E8 Fq)) :=
        hCENT t' (fun γ hγ => by
          have h1 := b.2 γ hγ
          have h2 : (∑ j, (γ j : ZMod p) * α j (ιB (Additive.ofMul b.1))) =
              ∑ j, (γ j : ZMod p) * ExcFrames.frameCoord .E8 p t' j :=
            Finset.sum_congr rfl fun j _ => by rw [hα b.1 t' ht' j]
          rwa [h2] at h1)
      have hcJ : ((e.symm (ιT (Multiplicative.ofAdd t')) : ↥X) : G) ∈
          Subgroup.centralizer (J : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        let jX : ↥X := ⟨j, hJX hj⟩
        have hjsub : jX ∈ Jsub := hj
        have hYj : e jX ∈ Y := by
          change e jX ∈ Jsub.map (e : ↥X →* adjointGroup .E8 Fq)
          exact Subgroup.mem_map_of_mem e.toMonoidHom hjsub
        have hcomm := (Subgroup.mem_centralizer_iff.mp hcent) (e jX) hYj
        have hXeq : jX * e.symm (ιT (Multiplicative.ofAdd t')) =
            e.symm (ιT (Multiplicative.ofAdd t')) * jX := by
          apply e.injective
          rw [map_mul, map_mul, e.apply_symm_apply]
          exact hcomm
        exact congrArg Subtype.val hXeq
      have hbsmem : ((e.symm (ιT (Multiplicative.ofAdd t')) : ↥X) : G) ∈ Bs := by
        rw [ht']
        exact hεBs b.1
      let ebs : ↥Bs := ⟨((e.symm (ιT (Multiplicative.ofAdd t')) : ↥X) : G), hbsmem⟩
      have hebsC : (ebs : G) ∈ Subgroup.centralizer (J : Set G) := hcJ
      have hebs_eps : ε ebs = ε b.1 := by
        have hebsX : (ebs : G) ∈ X := (e.symm (ιT (Multiplicative.ofAdd t'))).2
        have h1 := hεX ebs hebsX
        rw [h1]
        rw [show (⟨(ebs : G), hebsX⟩ : ↥X) = e.symm (ιT (Multiplicative.ofAdd t')) from rfl,
          e.apply_symm_apply, ht']
      have hkeps : ε (b.1 * ebs⁻¹) = 1 := by
        rw [map_mul, map_inv, hebs_eps, mul_inv_cancel]
      have hkCJ : ((b.1 * ebs⁻¹ : ↥Bs) : G) ∈
          Subgroup.centralizer (J : Set G) :=
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
              ∑ j, (c j : ZMod p) * α j (ιB (Additive.ofMul b)) = 0} := hcard_sub.symm
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
  have h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i) := by
    have hrank : Tag.E8.rank = 8 := rfl
    have := le_compRank_of_finrank_ggRootAnn (p := p)
      (componentRoots (rootCharHom a) i) (d := 2) hfin_le
    omega
  have hclass := e8_class_levi_or_a8 (p := p) hp hp2 hprim a ha ha1 i h6
  have hnoA8 : p = 3 → ∀ v : WeylGroup .E8,
      componentRoots (rootCharHom a) i ≠
        (fun c => v • c) '' kacE8.rootsOf (e8A8Nodes : Set (Option (Fin Tag.E8.rank))) := by
    intro hp3 v hv
    apply hnA8
    obtain ⟨lab8, hΛ8, htag8, hrank8, hA8labY⟩ := hA8c hp3 v hv
    let eJ : ↥J ≃* ↥Jsub := (Subgroup.subgroupOfEquivOfLe hJX).symm
    let eY : ↥Jsub ≃* ↥Y := Subgroup.equivMapOfInjective Jsub
      (e : ↥X →* adjointGroup .E8 Fq) e.injective
    let eJY : ↥J ≃* ↥Y := eJ.trans eY
    have hq : (↥J ⧸ Subgroup.center ↥J) ≃*
        (↥Y ⧸ Subgroup.center ↥Y) :=
      QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥Y) eJY
        (Subgroup.map_center_eq eJY)
    have hA8labJ : GGHasLabel lab8 (↥J ⧸ Subgroup.center ↥J) :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GTri.triGGHasLabel_congr hA8labY hq.symm
    have hiso : GGLabelIso labJ lab8 :=
      hRig labJ lab8 (↥J ⧸ Subgroup.center ↥J) hΛJ hΛ8 hJlab hA8labJ
    rw [labelIso_rank8 hiso htag8 hrank8]
    exact ⟨htag8, hrank8⟩
  refine ⟨V, hVadd, hVmod, ιB, φ, h, α, f, hlin, hrefl, hpair, hf, hclos, hX, ?_⟩
  refine ⟨Lf, inferInstance, ζ, a, gB, i, hprim, ha, ha1, hχ, ?_⟩
  have hlower : ∀ c ∈ componentRoots (rootCharHom a) i, ∃ t ∈ ggAutomizer J Bs, ∀ w,
      ggLin (p := p) ιB t w =
        w - (∑ j, (c j : ZMod p) * α j w) • ∑ j, (c j : ZMod p) • h j := by
    intro c hc
    rcases hclass with ⟨v, Sd, hSd, hΨeq⟩ | ⟨hp3, v, hΨeq⟩
    · obtain ⟨gY, hgYY, hactc⟩ := hLow v Sd hSd hΨeq c hc
      let jX : ↥X := e.symm gY
      have hje : e jX = gY := e.apply_symm_apply gY
      have hjJsub : jX ∈ Jsub := by
        apply (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
        exact hje ▸ hgYY
      have hjJ : (jX : G) ∈ J := Subgroup.mem_subgroupOf.mp hjJsub
      have hmapE : E.map (MulAut.conj gY).toMonoidHom = E := by
        apply le_antisymm
        · rintro x ⟨y, hy, rfl⟩
          obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp (hιTrange.symm ▸ hy)
          let s : Fin Tag.E8.rank → ZMod p := Multiplicative.toAdd t
          have hs : ιT (Multiplicative.ofAdd s) = y := ht
          change gY * y * gY⁻¹ ∈ E
          rw [← hs, hactc s, ← hιTrange]
          exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
        · intro x hx
          obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp (hιTrange.symm ▸ hx)
          let s : Fin Tag.E8.rank → ZMod p := Multiplicative.toAdd t
          have hs : ιT (Multiplicative.ofAdd s) = x := ht
          refine Subgroup.mem_map.mpr ⟨ιT (Multiplicative.ofAdd
            (TableBExc.torusAct .E8 p (rootReflection c)⁻¹ s)), ?_, ?_⟩
          · rw [← hιTrange]
            exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
          · rw [← hs]
            change gY * ιT (Multiplicative.ofAdd
              (TableBExc.torusAct .E8 p (rootReflection c)⁻¹ s)) * gY⁻¹ =
                ιT (Multiplicative.ofAdd s)
            rw [hactc]
            rw [NoOffE8Five.torusAct_mul_inv_apply]
      have hgYN : gY ∈ Subgroup.normalizer (E : Set (adjointGroup .E8 Fq)) :=
        (Subgroup.mem_normalizer_iff_map_conj_eq).2 hmapE
      have hjN : (jX : G) ∈ Subgroup.normalizer (Bs : Set G) :=
        hεN1 jX (hje ▸ hgYN)
      let jsub : ↥(J ⊓ Subgroup.normalizer (Bs : Set G)) := ⟨(jX : G), hjJ, hjN⟩
      let tJ : MulAut ↥Bs := ggTDρB J Bs jsub
      have htJ : tJ ∈ ggAutomizer J Bs := by
        rw [← ggTDρB_range]
        exact ⟨jsub, rfl⟩
      let jXinf : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)) := ⟨(jX : G), jX.2, hjN⟩
      have htXD : ggTDρB X Bs jXinf =
          (f (κ (rootReflection c)) : MulAut ↥Bs) := by
        refine hTD jXinf (rootReflection c) ?_
        intro s
        have h1 : e ⟨jXinf, jXinf.2.1⟩ = gY := hje
        rw [h1]
        exact hactc s
      have ht_eq : tJ = (f (κ (rootReflection c)) : MulAut ↥Bs) := by
        rw [show tJ = ggTDρB X Bs jXinf from rfl, htXD]
      obtain ⟨e0, he0, hlift⟩ := ggTBJE8Levi_weylLift (p := p) ιB hlin hpair hf
      let F : WeylGroup .E8 →* ↥(ggAutomizer X Bs) := f.toMonoidHom.comp e0.toMonoidHom
      have hF : ∀ j, (F (simple .E8 j) : MulAut ↥Bs) = φ j := by
        intro j
        change (f (e0 (simple .E8 j)) : MulAut ↥Bs) = φ j
        rw [he0 j]
        exact hf j
      have hFh : ∀ (u : WeylGroup .E8) (c : Fin Tag.E8.rank → ℤ),
          ggLin (p := p) ιB (F u : MulAut ↥Bs) (∑ j, (c j : ZMod p) • h j) =
            ∑ j, ((u • c) j : ZMod p) • h j :=
        fun u c => (hlift u c 0).1
      have hFα : ∀ (u : WeylGroup .E8) (c : Fin Tag.E8.rank → ℤ) (w : V),
          ∑ j, ((u • c) j : ZMod p) * α j (ggLin (p := p) ιB (F u : MulAut ↥Bs) w) =
            ∑ j, (c j : ZMod p) * α j w :=
        fun u c w => (hlift u c w).2
      have hκe0 : ∀ u : WeylGroup .E8, κ u = e0 u := by
        intro u
        have hgen : Subgroup.closure (Set.range (simple .E8)) = ⊤ := closure_range_simple
        have hu : u ∈ Subgroup.closure (Set.range (simple .E8)) := by rw [hgen]; trivial
        induction hu using Subgroup.closure_induction with
        | mem x hx => obtain ⟨j, rfl⟩ := hx; rw [hκ j, he0 j]
        | one => simp
        | mul x y hx hy ihx ihy => rw [map_mul, map_mul, ihx, ihy]
        | inv x hx ih => rw [map_inv, map_inv, ih]
      have htF : tJ = (F (rootReflection c) : MulAut ↥Bs) := by
        rw [ht_eq]
        change (f (κ (rootReflection c)) : MulAut ↥Bs) =
          (f (e0 (rootReflection c)) : MulAut ↥Bs)
        rw [hκe0]
      refine ⟨tJ, htJ, fun w => ?_⟩
      rw [htF]
      exact ggReflFormula (p := p) ιB hlin hF hFh hFα
        (isRoot_of_mem_componentRoots hc) w
    · exact (hnoA8 hp3 v hΨeq).elim
  have hupper : ∀ t ∈ ggAutomizer J Bs, t ∈ ggAutomizer X Bs ∧ t gB = gB ∧
      ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
        ggLin (p := p) ιB t (∑ j, (c j : ZMod p) • h j) = ∑ j, (c j : ZMod p) • h j := by
    intro t ht
    obtain ⟨j, hjJ, hjN, hφt⟩ := mem_ggAutomizer_iff.mp ht
    have htX : t ∈ ggAutomizer X Bs :=
      mem_ggAutomizer_iff.mpr ⟨j, hJX hjJ, hjN, hφt⟩
    have htg : t gB = gB := by
      apply Subtype.ext
      have hcomm := (Subgroup.mem_centralizer_singleton_iff.mp (hJg hjJ))
      calc ((t gB : ↥Bs) : G) = j * (gB : G) * j⁻¹ := hφt gB
        _ = (gB : G) := by
            change j * g * j⁻¹ = g
            rw [hcomm]
            group
    have horth : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
        ∀ γ ∈ componentRoots (rootCharHom a) i,
          ∑ j, (γ j : ZMod p) * ExcFrames.frameCoord .E8 p (TableBExc.redMod .E8 p c) j = 0 := by
      intro c hcK hcΨ γ hγ
      have hc_mem : c ∈ componentRoots (rootCharHom a) ⟦⟨c, hcK⟩⟧ := ⟨hcK, rfl⟩
      have hne : (⟦⟨c, hcK⟩⟧ : KernelComponent (rootCharHom a)) ≠ i := by
        intro heq
        exact hcΨ (by rwa [heq] at hc_mem)
      have hform : CFSG.LieType.Steinberg.Adjoint.iform γ c = 0 :=
        CFSG.LieType.Chevalley.iform_eq_zero_of_mem_componentRoots hne.symm hγ hc_mem
      have hbf : NoOffRest.bform .E8 p (TableBExc.redMod .E8 p γ)
          (TableBExc.redMod .E8 p c) =
          ∑ j, (γ j : ZMod p) * ExcFrames.frameCoord .E8 p
            (TableBExc.redMod .E8 p c) j := by
        rw [NoOffRest.bform_apply]
        simp only [ExcFrames.frameCoord, TableBExc.redMod, Finset.mul_sum]
        rw [Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [← hbf, NoOffRest.bform_redMod, hform]
      norm_num
    have hthird : ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
        ggLin (p := p) ιB t (∑ j, (c j : ZMod p) • h j) =
          ∑ j, (c j : ZMod p) • h j := by
      intro c hcK hcΨ
      classical
      choose bk hbkι hbkX hbkε using hh
      let bc : ↥Bs := (List.ofFn fun k => bk k ^ ((c k : ZMod p)).val).prod
      have hιbc : ιB (Additive.ofMul bc) = ∑ j, (c j : ZMod p) • h j := by
        have h := ggTD_sum_eq (p := p) ιB bk (fun k => (c k : ZMod p))
        rw [← h]
        exact Finset.sum_congr rfl fun k _ => by rw [hbkι k]
      have hεprod : ∀ l : List ↥Bs, ε l.prod = (l.map ε).prod := by
        intro l
        induction l with
        | nil => simp
        | cons x xs ih => rw [List.prod_cons, map_mul, ih, List.map_cons, List.prod_cons]
      have hsum_single : (∑ k, ((c k : ZMod p)).val •
          (Pi.single k 1 : Fin Tag.E8.rank → ZMod p)) = fun j => (c j : ZMod p) := by
        funext j
        rw [Finset.sum_apply, Finset.sum_eq_single j]
        · rw [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one,
            ZMod.natCast_zmod_val]
        · intro k _ hk
          have h0 : (Pi.single k (1 : ZMod p) : Fin Tag.E8.rank → ZMod p) j = 0 := by
            simp [hk]
          rw [Pi.smul_apply, h0, smul_zero]
        · intro hj
          exact absurd (Finset.mem_univ j) hj
      have hεbc : ε bc = ιT (Multiplicative.ofAdd
          (fun j => (c j : ZMod p))) := by
        let l : List ↥Bs := List.ofFn fun k => bk k ^ ((c k : ZMod p)).val
        let lv : List (Fin Tag.E8.rank → ZMod p) :=
          List.ofFn fun k =>
            ((c k : ZMod p)).val • (Pi.single k 1 : Fin Tag.E8.rank → ZMod p)
        have hbc : bc = l.prod := rfl
        have h1 : ε bc = (l.map ε).prod := by rw [hbc, hεprod]
        have h2 : l.map ε = (lv.map Multiplicative.ofAdd).map (fun v => ιT v) := by
          change List.ofFn (fun k => ε (bk k ^ ((c k : ZMod p)).val)) =
            List.ofFn (fun k => ιT (Multiplicative.ofAdd
              (((c k : ZMod p)).val • (Pi.single k 1 : Fin Tag.E8.rank → ZMod p))))
          apply List.ofFn_inj.mpr
          funext k
          rw [map_pow, hbkε k, ← map_pow, ← ofAdd_nsmul]
        have h3 : ((lv.map Multiplicative.ofAdd).map (fun v => ιT v)).prod =
            ιT (Multiplicative.ofAdd lv.sum) := by
          change ((lv.map Multiplicative.ofAdd).map ιT).prod =
            ιT (Multiplicative.ofAdd lv.sum)
          rw [← map_list_prod]
          exact congrArg ιT (ofAdd_list_prod lv).symm
        rw [h1, h2, h3, List.sum_ofFn]
        rw [hsum_single]
      have hcent : ιT (Multiplicative.ofAdd (TableBExc.redMod .E8 p c)) ∈
          Subgroup.centralizer (Y : Set (adjointGroup .E8 Fq)) :=
        hCENT (TableBExc.redMod .E8 p c) (fun γ hγ => horth c hcK hcΨ γ hγ)
      let sC : Fin Tag.E8.rank → ZMod p := TableBExc.redMod .E8 p c
      have hεbc' : ε bc = ιT (Multiplicative.ofAdd sC) := hεbc
      obtain ⟨bs, hbsε⟩ := hεsurj (ιT (Multiplicative.ofAdd sC))
        (by rw [← hιTrange]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      have hbsmem : ((e.symm (ιT (Multiplicative.ofAdd sC)) : ↥X) : G) ∈ Bs := by
        have h := hεBs bs
        rwa [hbsε] at h
      let ebs : ↥Bs := ⟨((e.symm (ιT (Multiplicative.ofAdd sC)) : ↥X) : G), hbsmem⟩
      have hebsX : (ebs : G) ∈ X := (e.symm (ιT (Multiplicative.ofAdd sC))).2
      have hebsε : ε ebs = ιT (Multiplicative.ofAdd sC) := by
        have h1 := hεX ebs hebsX
        rw [h1]
        rw [show (⟨(ebs : G), hebsX⟩ : ↥X) = e.symm (ιT (Multiplicative.ofAdd sC))
          from rfl, e.apply_symm_apply]
      have hkeps : ε (bc * ebs⁻¹) = 1 := by
        rw [map_mul, map_inv, hεbc', hebsε, mul_inv_cancel]
      have hebsCJ : (ebs : G) ∈ Subgroup.centralizer (J : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro j' hj'
        let jX : ↥X := ⟨j', hJX hj'⟩
        have hjsub : jX ∈ Jsub := hj'
        have hYj : e jX ∈ Y := by
          change e jX ∈ Jsub.map (e : ↥X →* adjointGroup .E8 Fq)
          exact Subgroup.mem_map_of_mem e.toMonoidHom hjsub
        have hcomm := (Subgroup.mem_centralizer_iff.mp hcent) (e jX) hYj
        have hXeq : jX * e.symm (ιT (Multiplicative.ofAdd sC)) =
            e.symm (ιT (Multiplicative.ofAdd sC)) * jX := by
          apply e.injective
          rw [map_mul, map_mul, e.apply_symm_apply]
          exact hcomm
        exact congrArg Subtype.val hXeq
      have hkCJ : ((bc * ebs⁻¹ : ↥Bs) : G) ∈
          Subgroup.centralizer (J : Set G) :=
        Subgroup.centralizer_le hJX ((hεker (bc * ebs⁻¹)).1 hkeps)
      have hbcCJ : (bc : G) ∈ Subgroup.centralizer (J : Set G) := by
        have hbceq : bc = ebs * (bc * ebs⁻¹) := by
          rw [(isMulCommutative_iff.mp hBs.1) bc ebs⁻¹]
          group
        rw [show (bc : G) = (ebs : G) * ((bc * ebs⁻¹ : ↥Bs) : G) from
          congrArg Subtype.val hbceq]
        exact Subgroup.mul_mem _ hebsCJ hkCJ
      rw [show (∑ j, (c j : ZMod p) • h j) = ιB (Additive.ofMul bc) from hιbc.symm]
      rw [ggLin_apply_ofMul]
      apply congrArg ιB
      apply Additive.ofMul.injective
      apply Subtype.ext
      change ((t bc : ↥Bs) : G) = (bc : G)
      rw [hφt bc]
      have hcomm := (Subgroup.mem_centralizer_iff.mp hbcCJ) j hjJ
      rw [hcomm]
      group
    exact ⟨htX, htg, hthird⟩
  exact ⟨hlower, hupper, hcounted_upper, hnoA8⟩

theorem ggE8Levi_input_L_of_frame
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hM : GGE8LeviModel p Bs L)
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hnA8 : ¬ ((labJ.tag = .A ∨ labJ.tag = .twA) ∧ labJ.rank = 8)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Fin 8 → MulAut ↥Bs) (h : Fin 8 → V) (α : Fin 8 → Module.Dual (ZMod p) V)
      (f : CoxeterMatrix.E₈.Group ≃* ↥(ggAutomizer L Bs)),
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p)) ∧
      (∀ i, (f (CoxeterMatrix.E₈.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range φ) ∧
      (∃ b : ↥Bs, b ≠ 1 ∧ ∀ j, α j (ι (Additive.ofMul b)) = 0) ∧
      ∃ (Lf : Type) (_ : Field Lf) (ζ : Lfˣ) (a : Fin Tag.E8.rank → Lfˣ) (g : ↥Bs)
        (i : KernelComponent (rootCharHom a)),
        IsPrimitiveRoot (ζ : Lf) p ∧ (∀ j, a j ^ p = 1) ∧ (∃ j, a j ≠ 1) ∧
        (∀ v : Fin Tag.E8.rank → ℤ, rootCharHom a (Multiplicative.ofAdd v) =
          ζ ^ (∑ j, (v j : ZMod p) * α j (ι (Additive.ofMul g))).val) ∧
        (∀ c ∈ componentRoots (rootCharHom a) i, ∃ t ∈ ggAutomizer J Bs, ∀ w,
          ggLin (p := p) ι t w = w - (∑ j, (c j : ZMod p) * α j w) • ∑ j, (c j : ZMod p) • h j) ∧
        (∀ t ∈ ggAutomizer J Bs, t ∈ ggAutomizer L Bs ∧ t g = g ∧
          ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
            ggLin (p := p) ι t (∑ j, (c j : ZMod p) • h j) = ∑ j, (c j : ZMod p) • h j) ∧
        Nat.card {b : ↥Bs // ∀ c ∈ componentRoots (rootCharHom a) i,
          ∑ j, (c j : ZMod p) * α j (ι (Additive.ofMul b)) = 0} ≤ p ^ 3 ∧
        (p = 3 → ∀ v : WeylGroup .E8, componentRoots (rootCharHom a) i ≠
          (fun c => v • c) '' kacE8.rootsOf (e8A8Nodes : Set (Option (Fin Tag.E8.rank)))) := by
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
  obtain ⟨hN, Fq, hFqF, hFqFin, hFqChar, e, E, hA, hF⟩ := hM
  let : Field Fq := hFqF
  let : Finite Fq := hFqFin
  let : CharP Fq 2 := hFqChar
  have hZ : Subgroup.center ↥L = ⊥ := by
    have hmap : (Subgroup.center ↥L).map (e : ↥L →* adjointGroup .E8 Fq) = ⊥ := by
      rw [Subgroup.map_center_eq, center_adjointGroup_eq_bot]
    rw [Subgroup.map_eq_bot_iff,
      MonoidHom.ker_eq_bot (e : ↥L →* adjointGroup .E8 Fq) e.injective] at hmap
    exact le_bot_iff.mp hmap
  have hbXc : (x : G) ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hLx hl) x rfl).symm
  have hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3 :=
    GGConfig.card_bstar_inf_centralizer_J_le hH.1
  have hx1' : (⟨x, hxBs⟩ : ↥Bs) ≠ 1 := by
    intro h
    exact hx1 (congrArg Subtype.val h)
  exact ggE8Levi_input_of_frame hRig hp2 hBs hSC hN hJX hyBs hJg hgX hcomp hZ e hA hF
    ⟨x, hxBs⟩ hx1' hbXc hΛJ hJlab hnA8 hcardJ

theorem ggE8Levi_input_K_of_frame
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K) (hM : GGE8LeviModel p Bs K)
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hnA8 : ¬ ((labJ.tag = .A ∨ labJ.tag = .twA) ∧ labJ.rank = 8)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Fin 8 → MulAut ↥Bs) (h : Fin 8 → V) (α : Fin 8 → Module.Dual (ZMod p) V)
      (f : CoxeterMatrix.E₈.Group ≃* ↥(ggAutomizer K Bs)),
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p)) ∧
      (∀ i, (f (CoxeterMatrix.E₈.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer K Bs = Subgroup.closure (Set.range φ) ∧
      (∃ b : ↥Bs, b ≠ 1 ∧ ∀ j, α j (ι (Additive.ofMul b)) = 0) ∧
      ∃ (Lf : Type) (_ : Field Lf) (ζ : Lfˣ) (a : Fin Tag.E8.rank → Lfˣ) (g : ↥Bs)
        (i : KernelComponent (rootCharHom a)),
        IsPrimitiveRoot (ζ : Lf) p ∧ (∀ j, a j ^ p = 1) ∧ (∃ j, a j ≠ 1) ∧
        (∀ v : Fin Tag.E8.rank → ℤ, rootCharHom a (Multiplicative.ofAdd v) =
          ζ ^ (∑ j, (v j : ZMod p) * α j (ι (Additive.ofMul g))).val) ∧
        (∀ c ∈ componentRoots (rootCharHom a) i, ∃ t ∈ ggAutomizer J Bs, ∀ w,
          ggLin (p := p) ι t w = w - (∑ j, (c j : ZMod p) * α j w) • ∑ j, (c j : ZMod p) • h j) ∧
        (∀ t ∈ ggAutomizer J Bs, t ∈ ggAutomizer K Bs ∧ t g = g ∧
          ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
            ggLin (p := p) ι t (∑ j, (c j : ZMod p) • h j) = ∑ j, (c j : ZMod p) • h j) ∧
        Nat.card {b : ↥Bs // ∀ c ∈ componentRoots (rootCharHom a) i,
          ∑ j, (c j : ZMod p) * α j (ι (Additive.ofMul b)) = 0} ≤ p ^ 3 ∧
        (p = 3 → ∀ v : WeylGroup .E8, componentRoots (rootCharHom a) i ≠
          (fun c => v • c) '' kacE8.rootsOf (e8A8Nodes : Set (Option (Fin Tag.E8.rank)))) := by
  have hp : p.Prime := hH.1.1.2.2.2.2.2.1.1
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
  obtain ⟨hN, Fq, hFqF, hFqFin, hFqChar, e, E, hA, hF⟩ := hM
  let : Field Fq := hFqF
  let : Finite Fq := hFqFin
  let : CharP Fq 2 := hFqChar
  have hZ : Subgroup.center ↥K = ⊥ := by
    have hmap : (Subgroup.center ↥K).map (e : ↥K →* adjointGroup .E8 Fq) = ⊥ := by
      rw [Subgroup.map_center_eq, center_adjointGroup_eq_bot]
    rw [Subgroup.map_eq_bot_iff,
      MonoidHom.ker_eq_bot (e : ↥K →* adjointGroup .E8 Fq) e.injective] at hmap
    exact le_bot_iff.mp hmap
  have hbXc : (y : G) ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hnb.1.2.2.2.1 hl) y rfl).symm
  have hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3 :=
    GGConfig.card_bstar_inf_centralizer_J_le hH.1
  have hy1' : (⟨y, hyBs⟩ : ↥Bs) ≠ 1 := by
    intro h
    exact hnb.1.2.2.1 (congrArg Subtype.val h)
  exact ggE8Levi_input_of_frame hRig hp2 hBs hSC hN hJK hxBs hJg hgX hcomp hZ e hA hF
    ⟨y, hyBs⟩ hy1' hbXc hΛJ hJlab hnA8 hcardJ

theorem ggE8Levi_hJ
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs X J : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : Fin 8 → MulAut ↥Bs} {h : Fin 8 → V} {α : Fin 8 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    {f : CoxeterMatrix.E₈.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (CoxeterMatrix.E₈.simple i) : MulAut ↥Bs) = φ i)
    {L : Type} [Field L] {ζ : Lˣ} (hζ : IsPrimitiveRoot (ζ : L) p)
    {a : Fin Tag.E8.rank → Lˣ} (g : ↥Bs)
    (hχ : ∀ v : Fin Tag.E8.rank → ℤ, rootCharHom a (Multiplicative.ofAdd v) =
      ζ ^ (∑ j, (v j : ZMod p) * α j (ι (Additive.ofMul g))).val)
    (i : KernelComponent (rootCharHom a))
    (hlow : ∀ c ∈ componentRoots (rootCharHom a) i, ∃ t ∈ ggAutomizer J Bs, ∀ w,
      ggLin (p := p) ι t w = w - (∑ j, (c j : ZMod p) * α j w) • ∑ j, (c j : ZMod p) • h j)
    (hup : ∀ t ∈ ggAutomizer J Bs, t ∈ ggAutomizer X Bs ∧ t g = g ∧
      ∀ c ∈ kernelRoots (rootCharHom a), c ∉ componentRoots (rootCharHom a) i →
        ggLin (p := p) ι t (∑ j, (c j : ZMod p) • h j) = ∑ j, (c j : ZMod p) • h j) :
    ggAutomizer J Bs = Subgroup.closure {t | t ∈ ggAutomizer X Bs ∧
      ∃ c ∈ componentRoots (rootCharHom a) i, ∀ w,
        ggLin (p := p) ι t w = w - (∑ j, (c j : ZMod p) * α j w) • ∑ j, (c j : ZMod p) • h j} := by
  apply le_antisymm
  · intro t ht
    obtain ⟨htX, htg, htΨ⟩ := hup t ht
    exact ggTBJE8Levi_mem_closure_of_fix hp2 ι hlin hpair hf hζ g hχ i htX htg htΨ
  · rw [Subgroup.closure_le]
    rintro t ⟨-, c, hc, hform⟩
    obtain ⟨t', ht', hform'⟩ := hlow c hc
    have heq : t = t' := ggLin_injective (p := p) ι
      (LinearEquiv.ext fun w => by rw [hform, hform'])
    rw [heq]
    exact ht'

theorem ggTBJE8LeviL_of_frame
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hM : GGE8LeviModel p Bs L)
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hnA8 : ¬ ((labJ.tag = .A ∨ labJ.tag = .twA) ∧ labJ.rank = 8)) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨V, _, _, ι, φ, h, α, f, hlin, hrefl, hpair, hf, hclos, hX, Lf, _, ζ, a, g, i, hζ, ha,
    ha1, hχ, hlow, hup, hcount, hA8⟩ :=
    ggE8Levi_input_L_of_frame hRig hH hM hΛJ hJlab hnA8
  exact ggTBJE8Levi_of_class hp2 ι hlin hrefl hpair hf hclos hX hζ ha ha1 i
    (ggE8Levi_hJ hp2 ι hlin hpair hf hζ g hχ i hlow hup) hcount hA8

theorem ggTBJE8LeviK_of_frame
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K) (hM : GGE8LeviModel p Bs K)
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hnA8 : ¬ ((labJ.tag = .A ∨ labJ.tag = .twA) ∧ labJ.rank = 8)) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨V, _, _, ι, φ, h, α, f, hlin, hrefl, hpair, hf, hclos, hX, Lf, _, ζ, a, g, i, hζ, ha,
    ha1, hχ, hlow, hup, hcount, hA8⟩ :=
    ggE8Levi_input_K_of_frame hRig hH hJK hM hΛJ hJlab hnA8
  exact ggTBJE8Levi_of_class hp2 ι hlin hrefl hpair hf hclos hX hζ ha ha1 i
    (ggE8Levi_hJ hp2 ι hlin hpair hf hζ g hχ i hlow hup) hcount hA8

theorem e8Enn_leviFrame
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {n : ℕ} (hq : Nat.card K = 2 ^ n) (hpn : p ∣ 2 ^ n + 1)
    (E : Subgroup (adjointGroup .E8 K)) (hE : IsElemAbelian p E) (hcard : p ^ 7 ≤ Nat.card E)
    (hSC : ∀ g : adjointGroup .E8 K, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) :
    GGE8LeviFrame p E := by
  have hp : p.Prime := Fact.out
  have hpK : p ∣ Nat.card K + 1 := by rw [hq]; exact hpn
  obtain ⟨ζ, hζ, ιT, nk, S, ι, hζo, hιTinj, hιTrange, hact, -, hSq, hιinj, hιrange, hιιT, hT, hρ,
    wt, hwn, hwt⟩ := e8Enn_frame (K := K) hp2 hpK E hE hcard hSC
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst hn0
    norm_num at hpn
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpn)
  have hq2 : S.D.q = 2 ^ n := by rw [hSq, hq]
  have hΛtwA : LargeEvenInLambda2 (⟨.twA, 8, n⟩ : LargeEvenLabel) := by
    refine ⟨hnpos, by norm_num, ?_⟩
    intro h8
    norm_num at h8
  refine ⟨AlgebraicClosure K, inferInstance, ζ, hζ, ιT, nk, _, wt, hζo, hιTinj, hιTrange, hact,
    hwn, hwt, fun t ht Y hY => ?_⟩
  obtain ⟨i, hi, hCENT⟩ := e8Enn_class (K := K) hp2 S ι hιinj hιrange hιιT hT
    (fun γ hγ => Or.inr (hρ γ hγ)) ht hY
  exact ⟨i, hCENT, fun v Sd hSd hΨ =>
    e8Enn_lower (K := K) (p := p) S ι hιinj hιιT hρ hnpos hq2 i hi hSd hΨ,
    fun _ v hΨ => ⟨⟨.twA, 8, n⟩, hΛtwA, Or.inr rfl, rfl,
      e8Enn_a8 (K := K) S ι hιinj hρ hnpos hq2
        (a := TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E8 p t)) (hT t) i hi hΨ⟩⟩

theorem ggE8Enn_leviModel_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hpn : p ∣ 2 ^ n + 1) :
    GGE8LeviModel p Bs L := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, E, hE, hEcard, hEself, hA⟩ :=
    ggE8Enn_model_L hRig hH hΛ hL hpn
  exact ⟨hN, Fq, inferInstance, inferInstance, inferInstance, e, E, hA,
    e8Enn_leviFrame hH.1.1.2.2.2.2.2.1.2.1 hFqcard hpn E hE hEcard hEself⟩

theorem ggE8Enn_leviModel_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hpn : p ∣ 2 ^ n + 1) :
    GGE8LeviModel p Bs K := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, E, hE, hEcard, hEself, hA⟩ :=
    ggE8Enn_model_K hRig hH hΛ hK hpn
  exact ⟨hN, Fq, inferInstance, inferInstance, inferInstance, e, E, hA,
    e8Enn_leviFrame hH.1.1.2.2.2.2.2.1.2.1 hFqcard hpn E hE hEcard hEself⟩

theorem ggTBJE8LeviL_plus
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hpn : p ∣ 2 ^ n + 1) {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hnA8 : ¬ ((labJ.tag = .A ∨ labJ.tag = .twA) ∧ labJ.rank = 8)) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J :=
  ggTBJE8LeviL_of_frame hRig hH (ggE8Enn_leviModel_L hRig hH hΛ hL hpn) hΛJ hJlab hnA8

theorem ggTBJE8LeviK_plus
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hpn : p ∣ 2 ^ n + 1) {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hnA8 : ¬ ((labJ.tag = .A ∨ labJ.tag = .twA) ∧ labJ.rank = 8)) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J :=
  ggTBJE8LeviK_of_frame hRig hH hJK (ggE8Enn_leviModel_K hRig hH hΛ hK hpn) hΛJ hJlab hnA8

end CFSG.StandardType

end
