module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum
public import CFSG.LocalAnalysis.StandardType.GGTBTorTransport
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open scoped IsMulCommutative

private theorem cartanMatrix_E8_transpose : (CartanMatrix.E₈).transpose = CartanMatrix.E₈ := by
  decide +kernel

private theorem cartanMatrix_E8_symm (i j : Fin Tag.E8.rank) :
    CartanMatrix.E₈ i j = CartanMatrix.E₈ j i := by
  conv_lhs => rw [← cartanMatrix_E8_transpose]
  rfl

private theorem cartan_E8_eq : Tag.cartan .E8 = CartanMatrix.E₈ := by
  rw [show Tag.cartan .E8 = Tag.cartanE 8 from rfl, CFSG.LieType.Chevalley.cartanE_eq 8]

private theorem symmetrizedCartan_E8_eq : Tag.symmetrizedCartan .E8 = CartanMatrix.E₈ := by
  rw [show Tag.symmetrizedCartan .E8 = Tag.cartan .E8 from by decide +kernel, cartan_E8_eq]

private theorem frameCoord_single (p : ℕ) (j i : Fin Tag.E8.rank) :
    ExcFrames.frameCoord .E8 p (Pi.single j 1) i = ((CartanMatrix.E₈ i j : ℤ) : ZMod p) := by
  rw [ExcFrames.frameCoord, symmetrizedCartan_E8_eq]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [hbj]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem torusAct_simple_E8 {p : ℕ} [NeZero p] (k : Fin Tag.E8.rank)
    (s : Fin Tag.E8.rank → ZMod p) :
    TableBExc.torusAct .E8 p (simple .E8 k) s =
      s - (ExcFrames.frameCoord .E8 p s k) • Pi.single k 1 := by
  have hsymm : ∀ i j : Fin Tag.E8.rank, Tag.cartan .E8 i j = Tag.cartan .E8 j i := by
    intro i j
    rw [cartan_E8_eq]
    exact cartanMatrix_E8_symm i j
  rw [← TableBExc.torusRefl_eq_torusAct (τ := .E8) (p := p) hsymm k s, TableBExc.torusRefl]
  congr 2
  rw [ExcFrames.frameCoord, symmetrizedCartan_E8_eq, cartan_E8_eq]
  exact Finset.sum_congr rfl fun j _ => by rw [cartanMatrix_E8_symm j k]

private theorem eq_of_mem_X_of_eps_eq {G H : Type} [Group G] [Group H]
    {Bs X : Subgroup G} (hZ : Subgroup.center ↥X = ⊥) (ε : ↥Bs →* H)
    (hker : ∀ b, ε b = 1 ↔ (b : G) ∈ Subgroup.centralizer (X : Set G))
    {b₁ b₂ : ↥Bs} (h₁ : (b₁ : G) ∈ X) (h₂ : (b₂ : G) ∈ X) (he : ε b₁ = ε b₂) : b₁ = b₂ := by
  have hmem : b₁ * b₂⁻¹ = 1 := by
    have hx : (((b₁ * b₂⁻¹ : ↥Bs) : G)) ∈ Subgroup.centralizer (X : Set G) := by
      rw [← hker]
      simp only [map_mul, map_inv, he, mul_inv_cancel]
    have hcenter : (⟨((b₁ * b₂⁻¹ : ↥Bs) : G), X.mul_mem h₁ (X.inv_mem h₂)⟩ : ↥X) ∈
        Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hx) (y : G) y.2
    rw [hZ, Subgroup.mem_bot] at hcenter
    refine Subtype.ext ?_
    simpa using congrArg Subtype.val hcenter
  calc b₁ = b₁ * b₂⁻¹ * b₂ := by group
    _ = b₂ := by rw [hmem]; simp

private theorem sum_single (n : ℕ) {p : ℕ} (c : Fin n → ZMod p) :
    (∑ j, c j • (Pi.single j 1 : Fin n → ZMod p)) = c := by
  funext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    have h0 : (Pi.single b (1 : ZMod p) : Fin n → ZMod p) i = 0 := by
      rw [Pi.single_apply, if_neg (Ne.symm hbi)]
    rw [Pi.smul_apply, h0, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem eps_sum {G H : Type} [Group G] [Group H] {n : ℕ} {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} [CFSG.IsElementaryAbelian p ↥Bs] (ε : ↥Bs →* H)
    {ι₀ : Multiplicative (Fin n → ZMod p) →* H}
    (coordL : Additive ↥Bs →ₗ[ZMod p] (Fin n → ZMod p))
    (hcoord : ∀ v, ι₀ (Multiplicative.ofAdd (coordL v)) = ε (Additive.toMul v))
    (bk : Fin n → ↥Bs) (hbk : ∀ j, coordL (Additive.ofMul (bk j)) = Pi.single j 1)
    (c : Fin n → ZMod p) :
    ε (Additive.toMul (∑ j, c j • (Additive.ofMul (bk j) : Additive ↥Bs))) =
      ι₀ (Multiplicative.ofAdd c) := by
  have h1 : coordL (∑ j, c j • (Additive.ofMul (bk j) : Additive ↥Bs)) = c := by
    rw [map_sum]
    simp only [map_smul, hbk]
    exact sum_single n c
  rw [← hcoord, h1]

private theorem toMul_sum_mem {G : Type} [Group G] {n : ℕ} {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} [CFSG.IsElementaryAbelian p ↥Bs] (bk : Fin n → ↥Bs)
    (hbkX : ∀ k, (bk k : G) ∈ X) (c : Fin n → ZMod p) :
    ((Additive.toMul (∑ j, c j • (Additive.ofMul (bk j) : Additive ↥Bs)) : ↥Bs) : G) ∈ X := by
  have h1 : (∑ j, c j • (Additive.ofMul (bk j) : Additive ↥Bs)) =
      Additive.ofMul ((List.ofFn fun j => (bk j) ^ (c j).val).prod) := by
    simpa using ggTD_sum_eq (E := ↥Bs) (V := Additive ↥Bs) (AddEquiv.refl (Additive ↥Bs)) bk c
  rw [h1]
  simp only [toMul_ofMul]
  rw [SubmonoidClass.coe_list_prod, List.map_ofFn]
  refine Subgroup.list_prod_mem X ?_
  intro y hy
  simp only [List.mem_ofFn] at hy
  obtain ⟨j, rfl⟩ := hy
  exact X.pow_mem (hbkX j) _

private theorem ofMul_eq_sum_of_coord {G H : Type} [Group G] [Group H] {n : ℕ} {p : ℕ}
    [Fact p.Prime] {Bs X : Subgroup G} [CFSG.IsElementaryAbelian p ↥Bs]
    (hZ : Subgroup.center ↥X = ⊥) (ε : ↥Bs →* H)
    (hker : ∀ b, ε b = 1 ↔ (b : G) ∈ Subgroup.centralizer (X : Set G))
    {ι₀ : Multiplicative (Fin n → ZMod p) →* H}
    (coordL : Additive ↥Bs →ₗ[ZMod p] (Fin n → ZMod p))
    (hcoord : ∀ v, ι₀ (Multiplicative.ofAdd (coordL v)) = ε (Additive.toMul v))
    (bk : Fin n → ↥Bs) (hbkX : ∀ k, (bk k : G) ∈ X)
    (hbk : ∀ k, coordL (Additive.ofMul (bk k)) = Pi.single k 1)
    {x : ↥Bs} (hx : (x : G) ∈ X) (c : Fin n → ZMod p)
    (hc : coordL (Additive.ofMul x) = c) :
    Additive.ofMul x = ∑ j, c j • (Additive.ofMul (bk j) : Additive ↥Bs) := by
  have hεx : ε x = ι₀ (Multiplicative.ofAdd c) := by rw [← hc, hcoord, toMul_ofMul]
  have heps : ε (Additive.toMul (∑ j, c j • (Additive.ofMul (bk j) : Additive ↥Bs))) = ε x := by
    rw [eps_sum ε coordL hcoord bk hbk c, hεx]
  have hmem := toMul_sum_mem bk hbkX c
  have hxeq : x = Additive.toMul (∑ j, c j • (Additive.ofMul (bk j) : Additive ↥Bs)) :=
    eq_of_mem_X_of_eps_eq hZ ε hker hx hmem heps.symm
  rw [hxeq]
  simp

private theorem ggAutomizer_apply_of_mem_centralizer {G : Type} [Group G] {Bs X : Subgroup G}
    {b : ↥Bs} (hb : (b : G) ∈ Subgroup.centralizer (X : Set G)) (ψ : MulAut ↥Bs)
    (hψ : ψ ∈ ggAutomizer X Bs) : ψ b = b := by
  have hfix : ∀ ψ ∈ Subgroup.closure (ggInduced X Bs), ψ b = b := by
    intro ψ hψ
    induction hψ using Subgroup.closure_induction with
    | mem ψ hψ =>
        obtain ⟨g, hgX, -, hgψ⟩ := hψ
        apply Subtype.ext
        rw [hgψ b, (Subgroup.mem_centralizer_iff.mp hb) g hgX, mul_inv_cancel_right]
    | one => rfl
    | mul x y hx hy ihx ihy => rw [MulAut.mul_apply, ihy, ihx]
    | inv x hx ih =>
        have h1 : x⁻¹ (x b) = x⁻¹ b := congrArg (fun y => x⁻¹ y) ih
        rw [show x⁻¹ (x b) = b by
          rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]] at h1
        exact h1.symm
  rw [ggAutomizer] at hψ
  exact hfix ψ hψ

private theorem holds_of_eq_subgroup {m N : ℕ} {L' : Type} [Group L']
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {A A' : Subgroup (MulAut L')} (h : A = A') (w : GGTorusTorWit m N L' A')
    (hw : w.Holds C M) : (h.symm ▸ w).Holds C M := by
  cases h
  exact hw

private theorem n_of_eq_subgroup {m N : ℕ} {L' : Type} [Group L']
    {A A' : Subgroup (MulAut L')} (h : A = A') (w : GGTorusTorWit m N L' A') (k : Fin N) :
    (h.symm ▸ w).n k = w.n k := by
  cases h
  rfl

theorem e8Enn_datum
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hZ : Subgroup.center ↥X = ⊥)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : ↥X ≃* adjointGroup .E8 K) {E : Subgroup (adjointGroup .E8 K)}
    (hA : (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)))
    (ε : ↥Bs →* adjointGroup .E8 K)
    (hεE : ∀ b, ε b ∈ E) (hεsurj : ∀ c ∈ E, ∃ b, ε b = c)
    (hεker : ∀ b, ε b = 1 ↔ (b : G) ∈ Subgroup.centralizer (X : Set G))
    (hεX : ∀ (b : ↥Bs) (hb : (b : G) ∈ X), ε b = e ⟨b, hb⟩)
    (hεBs : ∀ b, ((e.symm (ε b) : ↥X) : G) ∈ Bs)
    (ι₀ : Multiplicative (Fin Tag.E8.rank → ZMod p) →* adjointGroup .E8 K)
    (hι₀ : Function.Injective ι₀) (hrange : ι₀.range = E)
    (n : Fin Tag.E8.rank → adjointGroup .E8 K)
    (hact : ∀ k s, n k * ι₀ (Multiplicative.ofAdd s) * (n k)⁻¹ =
      ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E8 p (simple .E8 k) s)))
    {m : ℕ} (wt : GGTorusTorWit m 8 (adjointGroup .E8 K)
      (E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))))
    (hwn : ∀ k, wt.n k = n k) (hw : wt.Holds CartanMatrix.E₈ CoxeterMatrix.E₈) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Fin 8 → MulAut ↥Bs) (h : Fin 8 → V) (α : Fin 8 → Module.Dual (ZMod p) V)
      (f : CoxeterMatrix.E₈.Group ≃* ↥(ggAutomizer X Bs))
      (κ : WeylGroup .E8 ≃* CoxeterMatrix.E₈.Group),
      (∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p)) ∧
      (∀ i, (f (CoxeterMatrix.E₈.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (∀ i, κ (simple .E8 i) = CoxeterMatrix.E₈.simple i) ∧
      (∀ (b : ↥Bs) (s : Fin Tag.E8.rank → ZMod p), ι₀ (Multiplicative.ofAdd s) = ε b →
        ∀ k, α k (ι (Additive.ofMul b)) = ExcFrames.frameCoord .E8 p s k) ∧
      (∀ k, ∃ b : ↥Bs, ι (Additive.ofMul b) = h k ∧ (b : G) ∈ X ∧
        ε b = ι₀ (Multiplicative.ofAdd (Pi.single k 1))) ∧
      ∀ (g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) (v : WeylGroup .E8),
        (∀ s, e ⟨g, g.2.1⟩ * ι₀ (Multiplicative.ofAdd s) * (e ⟨g, g.2.1⟩)⁻¹ =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E8 p v s))) →
        ggTDρB X Bs g = (f (κ v) : MulAut ↥Bs) := by
  classical
  have hEA : CFSG.IsElementaryAbelian p ↥Bs := hBs.isElementaryAbelian
  have hA' : (E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))).map
        (MulAut.congr e.symm).toMonoidHom = (ggGamma X hN).range := by
    rw [← hA, Subgroup.map_map]
    have hcomp : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
        MonoidHom.id (MulAut ↥X) := by
      ext a x
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hcomp, Subgroup.map_id]
  let w'' : GGTorusTorWit m 8 ↥X
      ((E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))).map
        (MulAut.congr e.symm).toMonoidHom) := wt.transport e.symm
  have hw'' : w''.Holds CartanMatrix.E₈ CoxeterMatrix.E₈ := wt.holds_transport e.symm hw
  let w' : GGTorusTorWit m 8 ↥X ((ggGamma X hN).range) := hA' ▸ w''
  have hw' : w'.Holds CartanMatrix.E₈ CoxeterMatrix.E₈ := holds_of_eq_subgroup hA'.symm w'' hw''
  have hwn' : ∀ k, w'.n k = e.symm (n k) := by
    intro k
    have h1 : w'.n k = w''.n k := n_of_eq_subgroup hA'.symm w'' k
    rw [h1, GGTorusTorWit.transport_n, hwn]
  have hAeb : IsElemAbelian p (ggGamma X hN).range := ggTD_elemAb hN hBs
  have hnk : ∀ k, ((w'.n k : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G) := fun k =>
    mem_normalizer_of_ggTorusWeylElt hN hSC (w'.weylElt hw' hAeb k)
  obtain ⟨f, hf⟩ := ggTD_weyl hN hw' hp2 hBs hnk
  have hclos : ggAutomizer X Bs =
      Subgroup.closure (Set.range fun k => ggTDρB X Bs (ggTDnH w' hnk k)) :=
    ggTD_closure hN hw' hp2 hBs hnk
  have hex : ∀ k : Fin Tag.E8.rank, ∃ b : ↥Bs,
      ε b = ι₀ (Multiplicative.ofAdd (Pi.single k 1)) := by
    intro k
    exact hεsurj _ (by rw [← hrange]; exact ⟨_, rfl⟩)
  let b0 : Fin Tag.E8.rank → ↥Bs := fun k => Classical.choose (hex k)
  have hb0 : ∀ k, ε (b0 k) = ι₀ (Multiplicative.ofAdd (Pi.single k 1)) :=
    fun k => Classical.choose_spec (hex k)
  let bk : Fin Tag.E8.rank → ↥Bs := fun k =>
    ⟨((e.symm (ε (b0 k)) : ↥X) : G), hεBs (b0 k)⟩
  have hbkX : ∀ k, (bk k : G) ∈ X := fun k => (e.symm (ε (b0 k))).2
  have hbk_eps : ∀ k, ε (bk k) = ι₀ (Multiplicative.ofAdd (Pi.single k 1)) := by
    intro k
    have hcoe : (⟨bk k, hbkX k⟩ : ↥X) = e.symm (ε (b0 k)) := Subtype.ext rfl
    rw [hεX (bk k) (hbkX k), hcoe, MulEquiv.apply_symm_apply, hb0 k]
  have hexc : ∀ b : ↥Bs, ∃ s : Fin Tag.E8.rank → ZMod p,
      ι₀ (Multiplicative.ofAdd s) = ε b := by
    intro b
    have h : ε b ∈ E := hεE b
    rw [← hrange] at h
    exact h
  let coord : ↥Bs → (Fin Tag.E8.rank → ZMod p) := fun b => Classical.choose (hexc b)
  have hcoord : ∀ b, ι₀ (Multiplicative.ofAdd (coord b)) = ε b :=
    fun b => Classical.choose_spec (hexc b)
  have hofAdd_inj : ∀ {s t : Fin Tag.E8.rank → ZMod p},
      Multiplicative.ofAdd s = Multiplicative.ofAdd t → s = t := by
    intro s t h
    simpa using congrArg Multiplicative.toAdd h
  have hcoord_mul : ∀ b b' : ↥Bs, coord (b * b') = coord b + coord b' := by
    intro b b'
    apply hofAdd_inj
    apply hι₀
    rw [hcoord, map_mul, ← hcoord b, ← hcoord b', ← map_mul, ← ofAdd_add]
  have hcoord_bk : ∀ k, coord (bk k) = Pi.single k 1 := by
    intro k
    apply hofAdd_inj
    apply hι₀
    rw [hcoord, hbk_eps]
  let coordA : Additive ↥Bs →+ (Fin Tag.E8.rank → ZMod p) :=
    AddMonoidHom.mk' (fun v => coord (Additive.toMul v)) (fun v v' => hcoord_mul _ _)
  let coordL : Additive ↥Bs →ₗ[ZMod p] (Fin Tag.E8.rank → ZMod p) := coordA.toZModLinearMap p
  have hcoordL_apply : ∀ v, coordL v = coord (Additive.toMul v) := fun v => rfl
  have hcoordL : ∀ v, ι₀ (Multiplicative.ofAdd (coordL v)) = ε (Additive.toMul v) :=
    fun v => hcoord (Additive.toMul v)
  have hcoordL_bk : ∀ k, coordL (Additive.ofMul (bk k)) = Pi.single k 1 := by
    intro k
    rw [hcoordL_apply, toMul_ofMul]
    exact hcoord_bk k
  let frameRow (k : Fin Tag.E8.rank) : (Fin Tag.E8.rank → ZMod p) →+ ZMod p :=
    AddMonoidHom.mk' (fun s => ExcFrames.frameCoord .E8 p s k) (fun s t => by
      rw [ExcFrames.frameCoord_add]
      rfl)
  let α : Fin Tag.E8.rank → Module.Dual (ZMod p) (Additive ↥Bs) := fun k =>
    ((frameRow k).comp coordA).toZModLinearMap p
  have hα : ∀ (k : Fin Tag.E8.rank) (v : Additive ↥Bs),
      α k v = ExcFrames.frameCoord .E8 p (coord (Additive.toMul v)) k := fun k v => rfl
  let φ : Fin Tag.E8.rank → MulAut ↥Bs := fun k => ggTDρB X Bs (ggTDnH w' hnk k)
  let hh : Fin Tag.E8.rank → Additive ↥Bs := fun k => Additive.ofMul (bk k)
  have happ : ∀ (i : Fin Tag.E8.rank) (b' : ↥Bs), ((φ i b' : ↥Bs) : G) =
      ((e.symm (n i) : ↥X) : G) * b' * (((e.symm (n i) : ↥X) : G))⁻¹ := by
    intro i b'
    have h1 : ((ggTDnH w' hnk i : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) : G) =
        ((e.symm (n i) : ↥X) : G) := by
      simp only [ggTDnH]
      rw [hwn' i]
    show ((ggTDρB X Bs (ggTDnH w' hnk i) b' : ↥Bs) : G) = _
    rw [ggTDρB_apply, h1]
  have hKlin : ∀ (i : Fin Tag.E8.rank) (b : ↥Bs),
      φ i b = b * (bk i ^ (ExcFrames.frameCoord .E8 p (coord b) i).val)⁻¹ := by
    intro i b
    let x : ↥Bs := ⟨((e.symm (ε b) : ↥X) : G), hεBs b⟩
    have hxX : (x : G) ∈ X := (e.symm (ε b)).2
    have hxeps : ε x = ε b := by
      have hcoe : (⟨x, hxX⟩ : ↥X) = e.symm (ε b) := Subtype.ext rfl
      rw [hεX x hxX, hcoe, MulEquiv.apply_symm_apply]
    have hcoords : coord x = coord b := by
      apply hofAdd_inj
      apply hι₀
      rw [hcoord, hcoord, hxeps]
    have hc_mem : ((b * x⁻¹ : ↥Bs) : G) ∈ Subgroup.centralizer (X : Set G) := by
      rw [← hεker]
      rw [map_mul, map_inv, hxeps, mul_inv_cancel]
    have hφxX : ((φ i x : ↥Bs) : G) ∈ X := by
      rw [happ i x]
      exact X.mul_mem (X.mul_mem (e.symm (n i)).2 hxX) (X.inv_mem (e.symm (n i)).2)
    have hxe : (⟨φ i x, hφxX⟩ : ↥X) =
        e.symm (n i) * (⟨x, hxX⟩ : ↥X) * (e.symm (n i))⁻¹ := by
      apply Subtype.ext
      rw [happ i x]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hεφx : ε (φ i x) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E8 p (simple .E8 i) (coord b))) := by
      rw [hεX (φ i x) hφxX, hxe, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
        ← hεX x hxX, hxeps, ← hcoord b]
      exact hact i (coord b)
    have hexp : ι₀ (Multiplicative.ofAdd (Pi.single i 1)) ^
          (ExcFrames.frameCoord .E8 p (coord b) i).val =
        ι₀ (Multiplicative.ofAdd ((ExcFrames.frameCoord .E8 p (coord b) i).val •
          Pi.single i 1)) := by
      rw [ofAdd_nsmul, map_pow]
    have hεy : ε (x * (bk i ^ (ExcFrames.frameCoord .E8 p (coord b) i).val)⁻¹) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E8 p (simple .E8 i) (coord b))) := by
      rw [map_mul, map_inv, map_pow, hxeps, hbk_eps, ← hcoord b, hexp,
        ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val,
        torusAct_simple_E8 i (coord b), sub_eq_add_neg, ofAdd_add, ofAdd_neg, map_mul, map_inv]
    have hφx : φ i x = x * (bk i ^ (ExcFrames.frameCoord .E8 p (coord b) i).val)⁻¹ :=
      eq_of_mem_X_of_eps_eq hZ ε hεker hφxX
        (X.mul_mem hxX (X.inv_mem (X.pow_mem (hbkX i) _))) (hεφx.trans hεy.symm)
    have hφmem : φ i ∈ ggAutomizer X Bs := by
      rw [← ggTDρB_range]
      exact ⟨ggTDnH w' hnk i, rfl⟩
    calc φ i b = φ i ((b * x⁻¹) * x) := by
          congr 1
          group
      _ = φ i (b * x⁻¹) * φ i x := map_mul _ _ _
      _ = (b * x⁻¹) * φ i x := by
            rw [ggAutomizer_apply_of_mem_centralizer hc_mem (φ i) hφmem]
      _ = (b * x⁻¹) * (x * (bk i ^ (ExcFrames.frameCoord .E8 p (coord b) i).val)⁻¹) := by
            rw [hφx]
      _ = b * (bk i ^ (ExcFrames.frameCoord .E8 p (coord b) i).val)⁻¹ := by group
  have hlin : ∀ i v, ggLin (p := p) (AddEquiv.refl (Additive ↥Bs)) (φ i) v =
      v - α i v • hh i := by
    intro i v
    obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, Additive.ofMul b = v := ⟨Additive.toMul v, ofMul_toMul v⟩
    rw [show Additive.ofMul b = AddEquiv.refl (Additive ↥Bs) (Additive.ofMul b) from rfl]
    rw [ggLin_apply_ofMul]
    simp only [AddEquiv.refl_apply]
    rw [hKlin i b, hα]
    dsimp only [hh]
    rw [toMul_ofMul]
    have hsm : (ExcFrames.frameCoord .E8 p (coord b) i) • (Additive.ofMul (bk i) : Additive ↥Bs) =
        Additive.ofMul (bk i ^ (ExcFrames.frameCoord .E8 p (coord b) i).val) := by
      rw [ofMul_pow, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    rw [hsm, ofMul_mul, ofMul_inv]
    abel
  have hpair : ∀ i j, α i (hh j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p) := by
    intro i j
    have h1 : coord (Additive.toMul (Additive.ofMul (bk j))) = Pi.single j 1 := by
      rw [toMul_ofMul]
      exact hcoord_bk j
    dsimp only [hh]
    rw [hα i (Additive.ofMul (bk j)), toMul_ofMul, h1, frameCoord_single]
  have hdiag : ∀ i : Fin Tag.E8.rank, ((CartanMatrix.E₈ i i : ℤ) : ZMod p) = 2 := by
    intro i
    have h : CartanMatrix.E₈ i i = 2 := by fin_cases i <;> rfl
    rw [h]
    norm_num
  have hrefl : ∀ i, GGIsReflection p (φ i) := by
    intro i
    have hfx : α i (hh i) = 2 := (hpair i i).trans (hdiag i)
    have hL : ggLin (p := p) (AddEquiv.refl (Additive ↥Bs)) (φ i) = Module.reflection hfx :=
      ggLin_eq_reflection _ hfx (fun v => hlin i v)
    exact ggIsReflection_of_eq_reflection hp2 _ hfx hL
  obtain ⟨κ, hκ, hκcoord⟩ :=
    ggTBJE8Levi_weylLift (p := p) (AddEquiv.refl (Additive ↥Bs)) hlin hpair hf
  have hframe : ∀ (b : ↥Bs) (s : Fin Tag.E8.rank → ZMod p),
      ι₀ (Multiplicative.ofAdd s) = ε b → ∀ k,
      α k (AddEquiv.refl (Additive ↥Bs) (Additive.ofMul b)) = ExcFrames.frameCoord .E8 p s k := by
    intro b s hs k
    have h1 : coord b = s := by
      apply hofAdd_inj
      apply hι₀
      rw [hcoord, hs]
    rw [hα k (AddEquiv.refl (Additive ↥Bs) (Additive.ofMul b))]
    have h2 : Additive.toMul (AddEquiv.refl (Additive ↥Bs) (Additive.ofMul b)) = b := by simp
    rw [h2, h1]
  have hbx : ∀ k, ∃ b : ↥Bs, AddEquiv.refl (Additive ↥Bs) (Additive.ofMul b) = hh k ∧
      (b : G) ∈ X ∧ ε b = ι₀ (Multiplicative.ofAdd (Pi.single k 1)) :=
    fun k => ⟨bk k, rfl, hbkX k, hbk_eps k⟩
  have haut : ∀ (g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) (v : WeylGroup .E8),
      (∀ s, e ⟨g, g.2.1⟩ * ι₀ (Multiplicative.ofAdd s) * (e ⟨g, g.2.1⟩)⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E8 p v s))) →
      ggTDρB X Bs g = (f (κ v) : MulAut ↥Bs) := by
    intro g v hv
    refine MulEquiv.ext fun b => ?_
    let x : ↥Bs := ⟨((e.symm (ε b) : ↥X) : G), hεBs b⟩
    have hxX : (x : G) ∈ X := (e.symm (ε b)).2
    have hxeps : ε x = ε b := by
      have hcoe : (⟨x, hxX⟩ : ↥X) = e.symm (ε b) := Subtype.ext rfl
      rw [hεX x hxX, hcoe, MulEquiv.apply_symm_apply]
    have hcoords : coord x = coord b := by
      apply hofAdd_inj
      apply hι₀
      rw [hcoord, hcoord, hxeps]
    have hc_mem : ((b * x⁻¹ : ↥Bs) : G) ∈ Subgroup.centralizer (X : Set G) := by
      rw [← hεker]
      rw [map_mul, map_inv, hxeps, mul_inv_cancel]
    have hLxX : ((ggTDρB X Bs g x : ↥Bs) : G) ∈ X := by
      rw [ggTDρB_apply]
      exact X.mul_mem (X.mul_mem g.2.1 hxX) (X.inv_mem g.2.1)
    obtain ⟨u, hu⟩ : ∃ u : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)),
        ggTDρB X Bs u = (f (κ v) : MulAut ↥Bs) := by
      have hmem : (f (κ v) : MulAut ↥Bs) ∈ (ggTDρB X Bs).range := by
        rw [ggTDρB_range]
        exact (f (κ v)).2
      exact hmem
    have hRxX : (((f (κ v) : MulAut ↥Bs) x : ↥Bs) : G) ∈ X := by
      rw [← hu, ggTDρB_apply]
      exact X.mul_mem (X.mul_mem u.2.1 hxX) (X.inv_mem u.2.1)
    have hεL : ε (ggTDρB X Bs g x) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E8 p v (coord b))) := by
      have hxe : (⟨ggTDρB X Bs g x, hLxX⟩ : ↥X) =
          (⟨(g : G), g.2.1⟩ : ↥X) * (⟨x, hxX⟩ : ↥X) * (⟨(g : G), g.2.1⟩ : ↥X)⁻¹ := by
        apply Subtype.ext
        rw [ggTDρB_apply]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hεX _ hLxX, hxe, map_mul, map_mul, map_inv, ← hεX x hxX, hxeps, ← hcoord b]
      exact hv (coord b)
    have hεR : ε ((f (κ v) : MulAut ↥Bs) x) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E8 p v (coord b))) := by
      have hsumx : Additive.ofMul x =
          ∑ j, ((TableBExc.liftMod .E8 p (coord b)) j : ZMod p) • hh j := by
        have hcx : coordL (Additive.ofMul x) =
            fun j => ((TableBExc.liftMod .E8 p (coord b)) j : ZMod p) := by
          rw [hcoordL_apply, toMul_ofMul, hcoords]
          funext j
          simp [TableBExc.liftMod]
        exact ofMul_eq_sum_of_coord hZ ε hεker coordL hcoordL bk hbkX hcoordL_bk hxX
          (fun j => ((TableBExc.liftMod .E8 p (coord b)) j : ZMod p)) hcx
      have hval : Additive.ofMul ((f (κ v) : MulAut ↥Bs) x) =
          ∑ j, ((v • TableBExc.liftMod .E8 p (coord b)) j : ZMod p) • hh j := by
        rw [show Additive.ofMul ((f (κ v) : MulAut ↥Bs) x) =
            AddEquiv.refl (Additive ↥Bs) (Additive.ofMul ((f (κ v) : MulAut ↥Bs) x)) from rfl]
        rw [← ggLin_apply_ofMul (p := p) (AddEquiv.refl (Additive ↥Bs))
          (f (κ v) : MulAut ↥Bs) x, hsumx]
        exact (hκcoord v (TableBExc.liftMod .E8 p (coord b)) (Additive.ofMul x)).1
      have h := congrArg (fun a : Additive ↥Bs => ε (Additive.toMul a)) hval
      rw [eps_sum ε coordL hcoordL bk hcoordL_bk
        (fun j => ((v • TableBExc.liftMod .E8 p (coord b)) j : ZMod p))] at h
      have hred : (fun j => ((v • TableBExc.liftMod .E8 p (coord b)) j : ZMod p)) =
          TableBExc.torusAct .E8 p v (coord b) := rfl
      rw [hred] at h
      simpa [toMul_ofMul] using h
    have hAx : ggTDρB X Bs g x = (f (κ v) : MulAut ↥Bs) x :=
      eq_of_mem_X_of_eps_eq hZ ε hεker hLxX hRxX (hεL.trans hεR.symm)
    have hb_eq : b = (b * x⁻¹) * x := by group
    have hfixL : ggTDρB X Bs g (b * x⁻¹) = b * x⁻¹ := by
      apply Subtype.ext
      rw [ggTDρB_apply, (Subgroup.mem_centralizer_iff.mp hc_mem) (g : G) g.2.1,
        mul_inv_cancel_right]
    have hfixR : (f (κ v) : MulAut ↥Bs) (b * x⁻¹) = b * x⁻¹ :=
      ggAutomizer_apply_of_mem_centralizer hc_mem _ (f (κ v)).2
    calc ggTDρB X Bs g b
        = ggTDρB X Bs g ((b * x⁻¹) * x) := congrArg _ hb_eq
      _ = ggTDρB X Bs g (b * x⁻¹) * ggTDρB X Bs g x := map_mul _ _ _
      _ = (b * x⁻¹) * ((f (κ v) : MulAut ↥Bs) x) := by rw [hfixL, hAx]
      _ = (f (κ v) : MulAut ↥Bs) (b * x⁻¹) * (f (κ v) : MulAut ↥Bs) x := by rw [hfixR]
      _ = (f (κ v) : MulAut ↥Bs) ((b * x⁻¹) * x) :=
            (map_mul (f (κ v) : MulAut ↥Bs) (b * x⁻¹) x).symm
      _ = (f (κ v) : MulAut ↥Bs) b := congrArg _ hb_eq.symm
  exact ⟨Additive ↥Bs, inferInstance, inferInstance, AddEquiv.refl _, φ, hh, α, f, κ,
    hlin, hrefl, hpair, hf, hclos, hκ, hframe, hbx, haut⟩

end CFSG.StandardType

end
