module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviDatum
public import CFSG.LocalAnalysis.StandardType.GGTBE6IndSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

open scoped IsMulCommutative

private theorem e6fr_eq_of_mem_X_of_eps_eq {G H : Type} [Group G] [Group H]
    {p : ℕ} {Bs X : Subgroup G} (hexp : ∀ b : ↥Bs, b ^ p = 1)
    (hZp : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1) (ε : ↥Bs →* H)
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
    have hpow : (⟨((b₁ * b₂⁻¹ : ↥Bs) : G), X.mul_mem h₁ (X.inv_mem h₂)⟩ : ↥X) ^ p = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val (hexp (b₁ * b₂⁻¹))
    have h1 : (⟨((b₁ * b₂⁻¹ : ↥Bs) : G), X.mul_mem h₁ (X.inv_mem h₂)⟩ : ↥X) = 1 :=
      hZp _ hcenter hpow
    refine Subtype.ext ?_
    simpa using congrArg Subtype.val h1
  calc b₁ = b₁ * b₂⁻¹ * b₂ := by group
    _ = b₂ := by rw [hmem]; simp

private theorem e6fr_eps_sum {G H : Type} [Group G] [Group H] {n : ℕ} {p : ℕ} [Fact p.Prime]
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
    exact (pi_eq_sum_univ' c).symm
  rw [← hcoord, h1]

private theorem e6fr_toMul_sum_mem {G : Type} [Group G] {n : ℕ} {p : ℕ} [Fact p.Prime]
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

private theorem e6fr_ofMul_eq_sum_of_coord {G H : Type} [Group G] [Group H] {n : ℕ} {p : ℕ}
    [Fact p.Prime] {Bs X : Subgroup G} [CFSG.IsElementaryAbelian p ↥Bs]
    (hexp : ∀ b : ↥Bs, b ^ p = 1)
    (hZp : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1) (ε : ↥Bs →* H)
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
    rw [e6fr_eps_sum ε coordL hcoord bk hbk c, hεx]
  have hmem := e6fr_toMul_sum_mem bk hbkX c
  have hxeq : x = Additive.toMul (∑ j, c j • (Additive.ofMul (bk j) : Additive ↥Bs)) :=
    e6fr_eq_of_mem_X_of_eps_eq hexp hZp ε hker hx hmem heps.symm
  rw [hxeq]
  simp

private theorem e6fr_ggAutomizer_apply_of_mem_centralizer {G : Type} [Group G]
    {Bs X : Subgroup G} {b : ↥Bs} (hb : (b : G) ∈ Subgroup.centralizer (X : Set G))
    (ψ : MulAut ↥Bs) (hψ : ψ ∈ ggAutomizer X Bs) : ψ b = b := by
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

theorem e6Cover_datum
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hZp : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {H : Type} [Group H] {E : Subgroup H} (ψ : ↥X →* H) (ε : ↥Bs →* H)
    (hεE : ∀ b, ε b ∈ E)
    (hεsurj : ∀ c ∈ E, ∃ b, ε b = c)
    (hεker : ∀ b, ε b = 1 ↔ (b : G) ∈ Subgroup.centralizer (X : Set G))
    (hεX : ∀ (b : ↥Bs) (hb : (b : G) ∈ X), ε b = ψ ⟨b, hb⟩)
    (hεlift : ∀ b, ∃ x : ↥X, (x : G) ∈ Bs ∧ ψ x = ε b)
    (ι₀ : Multiplicative (Fin Tag.E6.rank → ZMod p) →* H)
    (hι₀ : Function.Injective ι₀) (hrange : ι₀.range = E)
    {m : ℕ} (wt : GGTorusTorWit m 6 ↥X (ggGamma X hN).range)
    (hact : ∀ k s, ψ (wt.n k) * ι₀ (Multiplicative.ofAdd s) * (ψ (wt.n k))⁻¹ =
      ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p (simple .E6 k) s)))
    (hw : wt.Holds CartanMatrix.E₆ CoxeterMatrix.E₆) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Fin 6 → MulAut ↥Bs) (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod p) V)
      (f : CoxeterMatrix.E₆.Group ≃* ↥(ggAutomizer X Bs))
      (κ : WeylGroup .E6 ≃* CoxeterMatrix.E₆.Group),
      (∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = ((Tag.cartan .E6 i j : ℤ) : ZMod p)) ∧
      (∀ i, (f (CoxeterMatrix.E₆.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (∀ i, κ (simple .E6 i) = CoxeterMatrix.E₆.simple i) ∧
      (∀ (b : ↥Bs) (s : Fin Tag.E6.rank → ZMod p), ι₀ (Multiplicative.ofAdd s) = ε b →
        ∀ k, α k (ι (Additive.ofMul b)) = ∑ j, ((Tag.cartan .E6 k j : ℤ) : ZMod p) * s j) ∧
      (∀ k, ∃ b : ↥Bs, ι (Additive.ofMul b) = h k ∧ (b : G) ∈ X ∧
        ε b = ι₀ (Multiplicative.ofAdd (Pi.single k 1))) ∧
      (∀ (g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) (v : WeylGroup .E6),
        (∀ s, ψ ⟨g, g.2.1⟩ * ι₀ (Multiplicative.ofAdd s) * (ψ ⟨g, g.2.1⟩)⁻¹ =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p v s))) →
        ggTDρB X Bs g = (f (κ v) : MulAut ↥Bs)) ∧
      ∀ (u : WeylGroup .E6) (b : ↥Bs) (s : Fin Tag.E6.rank → ZMod p),
        ι₀ (Multiplicative.ofAdd s) = ε b →
        ε ((f (κ u) : MulAut ↥Bs) b) =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p u s)) := by
  classical
  haveI hEA : CFSG.IsElementaryAbelian p ↥Bs := hBs.isElementaryAbelian
  have hBspow : ∀ b : ↥Bs, b ^ p = 1 := fun b => by
    apply Subtype.ext
    simpa using hBs.2 (b : G) b.2
  have hAeb : IsElemAbelian p (ggGamma X hN).range := ggTD_elemAb hN hBs
  have hnk : ∀ k, ((wt.n k : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G) := fun k =>
    mem_normalizer_of_ggTorusWeylElt hN hSC (wt.weylElt hw hAeb k)
  obtain ⟨f, hf⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hclos : ggAutomizer X Bs =
      Subgroup.closure (Set.range fun k => ggTDρB X Bs (ggTDnH wt hnk k)) :=
    ggTD_closure hN hw hp2 hBs hnk
  have hex : ∀ k : Fin Tag.E6.rank, ∃ b : ↥Bs,
      ε b = ι₀ (Multiplicative.ofAdd (Pi.single k 1)) := by
    intro k
    exact hεsurj _ (by rw [← hrange]; exact ⟨_, rfl⟩)
  let b0 : Fin Tag.E6.rank → ↥Bs := fun k => Classical.choose (hex k)
  have hb0 : ∀ k, ε (b0 k) = ι₀ (Multiplicative.ofAdd (Pi.single k 1)) :=
    fun k => Classical.choose_spec (hex k)
  let xlift : ↥Bs → ↥X := fun b => Classical.choose (hεlift b)
  have hxliftB : ∀ b, ((xlift b : ↥X) : G) ∈ Bs :=
    fun b => (Classical.choose_spec (hεlift b)).1
  have hxliftψ : ∀ b, ψ (xlift b) = ε b :=
    fun b => (Classical.choose_spec (hεlift b)).2
  let bk : Fin Tag.E6.rank → ↥Bs := fun k =>
    ⟨((xlift (b0 k) : ↥X) : G), hxliftB (b0 k)⟩
  have hbkX : ∀ k, (bk k : G) ∈ X := fun k => (xlift (b0 k)).2
  have hbk_eps : ∀ k, ε (bk k) = ι₀ (Multiplicative.ofAdd (Pi.single k 1)) := by
    intro k
    have hcoe : (⟨bk k, hbkX k⟩ : ↥X) = xlift (b0 k) := Subtype.ext rfl
    rw [hεX (bk k) (hbkX k), hcoe, hxliftψ, hb0 k]
  have hexc : ∀ b : ↥Bs, ∃ s : Fin Tag.E6.rank → ZMod p,
      ι₀ (Multiplicative.ofAdd s) = ε b := by
    intro b
    have h : ε b ∈ E := hεE b
    rw [← hrange] at h
    exact h
  let coord : ↥Bs → (Fin Tag.E6.rank → ZMod p) := fun b => Classical.choose (hexc b)
  have hcoord : ∀ b, ι₀ (Multiplicative.ofAdd (coord b)) = ε b :=
    fun b => Classical.choose_spec (hexc b)
  have hofAdd_inj : ∀ {s t : Fin Tag.E6.rank → ZMod p},
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
  let coordA : Additive ↥Bs →+ (Fin Tag.E6.rank → ZMod p) :=
    AddMonoidHom.mk' (fun v => coord (Additive.toMul v)) (fun v v' => hcoord_mul _ _)
  let coordL : Additive ↥Bs →ₗ[ZMod p] (Fin Tag.E6.rank → ZMod p) := coordA.toZModLinearMap p
  have hcoordL_apply : ∀ v, coordL v = coord (Additive.toMul v) := fun v => rfl
  have hcoordL : ∀ v, ι₀ (Multiplicative.ofAdd (coordL v)) = ε (Additive.toMul v) :=
    fun v => hcoord (Additive.toMul v)
  have hcoordL_bk : ∀ k, coordL (Additive.ofMul (bk k)) = Pi.single k 1 := by
    intro k
    rw [hcoordL_apply, toMul_ofMul]
    exact hcoord_bk k
  let cartanRow (k : Fin Tag.E6.rank) : (Fin Tag.E6.rank → ZMod p) →+ ZMod p :=
    AddMonoidHom.mk' (fun s => ∑ j, ((Tag.cartan .E6 k j : ℤ) : ZMod p) * s j) (fun s t => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
  let α : Fin Tag.E6.rank → Module.Dual (ZMod p) (Additive ↥Bs) := fun k =>
    ((cartanRow k).comp coordA).toZModLinearMap p
  have hα : ∀ (k : Fin Tag.E6.rank) (v : Additive ↥Bs),
      α k v = ∑ j, ((Tag.cartan .E6 k j : ℤ) : ZMod p) * coord (Additive.toMul v) j :=
    fun k v => rfl
  let φ : Fin Tag.E6.rank → MulAut ↥Bs := fun k => ggTDρB X Bs (ggTDnH wt hnk k)
  let hh : Fin Tag.E6.rank → Additive ↥Bs := fun k => Additive.ofMul (bk k)
  have happ : ∀ (i : Fin Tag.E6.rank) (b' : ↥Bs), ((φ i b' : ↥Bs) : G) =
      ((wt.n i : ↥X) : G) * b' * (((wt.n i : ↥X) : G))⁻¹ := by
    intro i b'
    show ((ggTDρB X Bs (ggTDnH wt hnk i) b' : ↥Bs) : G) = _
    rw [ggTDρB_apply]
    rfl
  have hKlin : ∀ (i : Fin Tag.E6.rank) (b : ↥Bs),
      φ i b = b * (bk i ^ (∑ j, ((Tag.cartan .E6 i j : ℤ) : ZMod p) * coord b j).val)⁻¹ := by
    intro i b
    let x : ↥Bs := ⟨((xlift b : ↥X) : G), hxliftB b⟩
    have hxX : (x : G) ∈ X := (xlift b).2
    have hxeps : ε x = ε b := by
      have hcoe : (⟨x, hxX⟩ : ↥X) = xlift b := Subtype.ext rfl
      rw [hεX x hxX, hcoe, hxliftψ]
    have hc_mem : ((b * x⁻¹ : ↥Bs) : G) ∈ Subgroup.centralizer (X : Set G) := by
      rw [← hεker]
      rw [map_mul, map_inv, hxeps, mul_inv_cancel]
    have hφxX : ((φ i x : ↥Bs) : G) ∈ X := by
      rw [happ i x]
      exact X.mul_mem (X.mul_mem (wt.n i).2 hxX) (X.inv_mem (wt.n i).2)
    have hxe : (⟨φ i x, hφxX⟩ : ↥X) =
        wt.n i * (⟨x, hxX⟩ : ↥X) * (wt.n i)⁻¹ := by
      apply Subtype.ext
      rw [happ i x]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hεφx : ε (φ i x) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p (simple .E6 i) (coord b))) := by
      rw [hεX (φ i x) hφxX, hxe, map_mul, map_mul, map_inv, ← hεX x hxX, hxeps,
        ← hcoord b]
      exact hact i (coord b)
    have hspow : ι₀ (Multiplicative.ofAdd (Pi.single i 1)) ^
          (∑ j, ((Tag.cartan .E6 i j : ℤ) : ZMod p) * coord b j).val =
        ι₀ (Multiplicative.ofAdd ((∑ j, ((Tag.cartan .E6 i j : ℤ) : ZMod p) *
          coord b j).val • Pi.single i 1)) := by
      rw [ofAdd_nsmul, map_pow]
    have hεy : ε (x * (bk i ^
          (∑ j, ((Tag.cartan .E6 i j : ℤ) : ZMod p) * coord b j).val)⁻¹) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p (simple .E6 i) (coord b))) := by
      rw [map_mul, map_inv, map_pow, hxeps, hbk_eps, ← hcoord b, hspow,
        ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val,
        ggExcPlus_torusAct_simple_eq .E6 i (coord b), sub_eq_add_neg, ofAdd_add, ofAdd_neg,
        map_mul, map_inv]
    have hφx : φ i x = x * (bk i ^
        (∑ j, ((Tag.cartan .E6 i j : ℤ) : ZMod p) * coord b j).val)⁻¹ :=
      e6fr_eq_of_mem_X_of_eps_eq hBspow hZp ε hεker hφxX
        (X.mul_mem hxX (X.inv_mem (X.pow_mem (hbkX i) _))) (hεφx.trans hεy.symm)
    have hφmem : φ i ∈ ggAutomizer X Bs := by
      rw [← ggTDρB_range]
      exact ⟨ggTDnH wt hnk i, rfl⟩
    calc φ i b = φ i ((b * x⁻¹) * x) := by
          congr 1
          group
      _ = φ i (b * x⁻¹) * φ i x := map_mul _ _ _
      _ = (b * x⁻¹) * φ i x := by
            rw [e6fr_ggAutomizer_apply_of_mem_centralizer hc_mem (φ i) hφmem]
      _ = (b * x⁻¹) * (x * (bk i ^
            (∑ j, ((Tag.cartan .E6 i j : ℤ) : ZMod p) * coord b j).val)⁻¹) := by
            rw [hφx]
      _ = b * (bk i ^ (∑ j, ((Tag.cartan .E6 i j : ℤ) : ZMod p) * coord b j).val)⁻¹ := by
            group
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
    have hsm : (∑ j, ((Tag.cartan .E6 i j : ℤ) : ZMod p) * coord b j) •
        (Additive.ofMul (bk i) : Additive ↥Bs) =
        Additive.ofMul (bk i ^ (∑ j, ((Tag.cartan .E6 i j : ℤ) : ZMod p) * coord b j).val) := by
      rw [ofMul_pow, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    rw [hsm, ofMul_mul, ofMul_inv]
    abel
  have hpair : ∀ i j, α i (hh j) = ((Tag.cartan .E6 i j : ℤ) : ZMod p) := by
    intro i j
    have h1 : coord (Additive.toMul (Additive.ofMul (bk j))) = Pi.single j 1 := by
      rw [toMul_ofMul]
      exact hcoord_bk j
    dsimp only [hh]
    rw [hα i (Additive.ofMul (bk j)), h1]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      simp [hbj]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hdiag : ∀ i : Fin Tag.E6.rank, ((Tag.cartan .E6 i i : ℤ) : ZMod p) = 2 := by
    intro i
    rw [Tag.cartan_self]
    norm_num
  have hrefl : ∀ i, GGIsReflection p (φ i) := by
    intro i
    have hfx : α i (hh i) = 2 := (hpair i i).trans (hdiag i)
    have hL : ggLin (p := p) (AddEquiv.refl (Additive ↥Bs)) (φ i) = Module.reflection hfx :=
      ggLin_eq_reflection _ hfx (fun v => hlin i v)
    exact ggIsReflection_of_eq_reflection hp2 _ hfx hL
  let κ : WeylGroup .E6 ≃* CoxeterMatrix.E₆.Group := ggE6Row_coxeterGroupEquiv.symm
  have hκ : ∀ i, κ (simple .E6 i) = CoxeterMatrix.E₆.simple i := by
    intro i
    show ggE6Row_coxeterGroupEquiv.symm (simple .E6 i) = CoxeterMatrix.E₆.simple i
    rw [← ggE6Row_coxeterGroupEquiv_simple i]
    exact MulEquiv.symm_apply_apply _ _
  let ρ : WeylGroup .E6 →* (Additive ↥Bs ≃ₗ[ZMod p] Additive ↥Bs) :=
    (ggLin (p := p) (AddEquiv.refl (Additive ↥Bs))).comp
      ((ggAutomizer X Bs).subtype.comp (f.toMonoidHom.comp κ.toMonoidHom))
  have hρu : ∀ u, ρ u = ggLin (p := p) (AddEquiv.refl (Additive ↥Bs)) (f (κ u) : MulAut ↥Bs) :=
    fun u => rfl
  have hρ : ∀ (i : Fin Tag.E6.rank) (v : Additive ↥Bs), ρ (simple .E6 i) v =
      v - α i v • hh i := by
    intro i v
    rw [hρu, hκ i]
    have h1 : (f (CoxeterMatrix.E₆.simple i) : MulAut ↥Bs) = φ i := hf i
    rw [h1]
    exact hlin i v
  have hκcoord : ∀ (u : WeylGroup .E6) (c : Fin Tag.E6.rank → ℤ),
      ggLin (p := p) (AddEquiv.refl (Additive ↥Bs)) (f (κ u) : MulAut ↥Bs)
          (∑ j, (c j : ZMod p) • hh j) = ∑ j, ((u • c) j : ZMod p) • hh j := by
    intro u c
    rw [← hρu]
    exact ggWeyl_smul_sum_frame (p := p) hh α hpair ρ hρ u c
  have hframe : ∀ (b : ↥Bs) (s : Fin Tag.E6.rank → ZMod p),
      ι₀ (Multiplicative.ofAdd s) = ε b → ∀ k,
      α k (AddEquiv.refl (Additive ↥Bs) (Additive.ofMul b)) =
        ∑ j, ((Tag.cartan .E6 k j : ℤ) : ZMod p) * s j := by
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
  have hFε : ∀ (u : WeylGroup .E6) (b : ↥Bs) (s : Fin Tag.E6.rank → ZMod p),
      ι₀ (Multiplicative.ofAdd s) = ε b →
      ε ((f (κ u) : MulAut ↥Bs) b) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p u s)) := by
    intro u b s hs
    have hsb : coord b = s := by
      apply hofAdd_inj
      apply hι₀
      rw [hcoord, hs]
    let x : ↥Bs := ⟨((xlift b : ↥X) : G), hxliftB b⟩
    have hxX : (x : G) ∈ X := (xlift b).2
    have hxeps : ε x = ε b := by
      have hcoe : (⟨x, hxX⟩ : ↥X) = xlift b := Subtype.ext rfl
      rw [hεX x hxX, hcoe, hxliftψ]
    have hcoords : coord x = coord b := by
      apply hofAdd_inj
      apply hι₀
      rw [hcoord, hcoord, hxeps]
    have hc_mem : ((b * x⁻¹ : ↥Bs) : G) ∈ Subgroup.centralizer (X : Set G) := by
      rw [← hεker]
      rw [map_mul, map_inv, hxeps, mul_inv_cancel]
    have hsumx : Additive.ofMul x =
        ∑ j, ((TableBExc.liftMod .E6 p (coord b)) j : ZMod p) • hh j := by
      have hcx : coordL (Additive.ofMul x) =
          fun j => ((TableBExc.liftMod .E6 p (coord b)) j : ZMod p) := by
        rw [hcoordL_apply, toMul_ofMul, hcoords]
        funext j
        simp [TableBExc.liftMod]
      exact e6fr_ofMul_eq_sum_of_coord hBspow hZp ε hεker coordL hcoordL bk hbkX hcoordL_bk
        hxX (fun j => ((TableBExc.liftMod .E6 p (coord b)) j : ZMod p)) hcx
    have hval : Additive.ofMul ((f (κ u) : MulAut ↥Bs) x) =
        ∑ j, ((u • TableBExc.liftMod .E6 p (coord b)) j : ZMod p) • hh j := by
      rw [show Additive.ofMul ((f (κ u) : MulAut ↥Bs) x) =
          AddEquiv.refl (Additive ↥Bs) (Additive.ofMul ((f (κ u) : MulAut ↥Bs) x)) from rfl]
      rw [← ggLin_apply_ofMul (p := p) (AddEquiv.refl (Additive ↥Bs))
        (f (κ u) : MulAut ↥Bs) x, hsumx]
      exact hκcoord u (TableBExc.liftMod .E6 p (coord b))
    have hεx : ε ((f (κ u) : MulAut ↥Bs) x) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p u (coord b))) := by
      have h := congrArg (fun a : Additive ↥Bs => ε (Additive.toMul a)) hval
      rw [e6fr_eps_sum ε coordL hcoordL bk hcoordL_bk
        (fun j => ((u • TableBExc.liftMod .E6 p (coord b)) j : ZMod p))] at h
      have hred : (fun j => ((u • TableBExc.liftMod .E6 p (coord b)) j : ZMod p)) =
          TableBExc.torusAct .E6 p u (coord b) := rfl
      rw [hred] at h
      simpa [toMul_ofMul] using h
    have hfixR : (f (κ u) : MulAut ↥Bs) (b * x⁻¹) = b * x⁻¹ :=
      e6fr_ggAutomizer_apply_of_mem_centralizer hc_mem _ (f (κ u)).2
    have hεc : ε (b * x⁻¹) = 1 := by rw [map_mul, map_inv, hxeps, mul_inv_cancel]
    have hb_eq : b = (b * x⁻¹) * x := by group
    calc ε ((f (κ u) : MulAut ↥Bs) b)
        = ε ((f (κ u) : MulAut ↥Bs) ((b * x⁻¹) * x)) := by rw [← hb_eq]
      _ = ε ((f (κ u) : MulAut ↥Bs) (b * x⁻¹)) * ε ((f (κ u) : MulAut ↥Bs) x) := by
          rw [map_mul, map_mul]
      _ = ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p u s)) := by
          rw [hfixR, hεc, one_mul, hεx, hsb]
  have haut : ∀ (g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) (v : WeylGroup .E6),
      (∀ s, ψ ⟨g, g.2.1⟩ * ι₀ (Multiplicative.ofAdd s) * (ψ ⟨g, g.2.1⟩)⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p v s))) →
      ggTDρB X Bs g = (f (κ v) : MulAut ↥Bs) := by
    intro g v hv
    refine MulEquiv.ext fun b => ?_
    let x : ↥Bs := ⟨((xlift b : ↥X) : G), hxliftB b⟩
    have hxX : (x : G) ∈ X := (xlift b).2
    have hxeps : ε x = ε b := by
      have hcoe : (⟨x, hxX⟩ : ↥X) = xlift b := Subtype.ext rfl
      rw [hεX x hxX, hcoe, hxliftψ]
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
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p v (coord b))) := by
      have hxe : (⟨ggTDρB X Bs g x, hLxX⟩ : ↥X) =
          (⟨(g : G), g.2.1⟩ : ↥X) * (⟨x, hxX⟩ : ↥X) * (⟨(g : G), g.2.1⟩ : ↥X)⁻¹ := by
        apply Subtype.ext
        rw [ggTDρB_apply]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hεX _ hLxX, hxe, map_mul, map_mul, map_inv, ← hεX x hxX, hxeps, ← hcoord b]
      exact hv (coord b)
    have hεR : ε ((f (κ v) : MulAut ↥Bs) x) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 p v (coord b))) := by
      have hsumx : Additive.ofMul x =
          ∑ j, ((TableBExc.liftMod .E6 p (coord b)) j : ZMod p) • hh j := by
        have hcx : coordL (Additive.ofMul x) =
            fun j => ((TableBExc.liftMod .E6 p (coord b)) j : ZMod p) := by
          rw [hcoordL_apply, toMul_ofMul, hcoords]
          funext j
          simp [TableBExc.liftMod]
        exact e6fr_ofMul_eq_sum_of_coord hBspow hZp ε hεker coordL hcoordL bk hbkX
          hcoordL_bk hxX (fun j => ((TableBExc.liftMod .E6 p (coord b)) j : ZMod p)) hcx
      have hval : Additive.ofMul ((f (κ v) : MulAut ↥Bs) x) =
          ∑ j, ((v • TableBExc.liftMod .E6 p (coord b)) j : ZMod p) • hh j := by
        rw [show Additive.ofMul ((f (κ v) : MulAut ↥Bs) x) =
            AddEquiv.refl (Additive ↥Bs) (Additive.ofMul ((f (κ v) : MulAut ↥Bs) x)) from rfl]
        rw [← ggLin_apply_ofMul (p := p) (AddEquiv.refl (Additive ↥Bs))
          (f (κ v) : MulAut ↥Bs) x, hsumx]
        exact hκcoord v (TableBExc.liftMod .E6 p (coord b))
      have h := congrArg (fun a : Additive ↥Bs => ε (Additive.toMul a)) hval
      rw [e6fr_eps_sum ε coordL hcoordL bk hcoordL_bk
        (fun j => ((v • TableBExc.liftMod .E6 p (coord b)) j : ZMod p))] at h
      have hred : (fun j => ((v • TableBExc.liftMod .E6 p (coord b)) j : ZMod p)) =
          TableBExc.torusAct .E6 p v (coord b) := rfl
      rw [hred] at h
      simpa [toMul_ofMul] using h
    have hAx : ggTDρB X Bs g x = (f (κ v) : MulAut ↥Bs) x :=
      e6fr_eq_of_mem_X_of_eps_eq hBspow hZp ε hεker hLxX hRxX (hεL.trans hεR.symm)
    have hb_eq : b = (b * x⁻¹) * x := by group
    have hfixL : ggTDρB X Bs g (b * x⁻¹) = b * x⁻¹ := by
      apply Subtype.ext
      rw [ggTDρB_apply, (Subgroup.mem_centralizer_iff.mp hc_mem) (g : G) g.2.1,
        mul_inv_cancel_right]
    have hfixR : (f (κ v) : MulAut ↥Bs) (b * x⁻¹) = b * x⁻¹ :=
      e6fr_ggAutomizer_apply_of_mem_centralizer hc_mem _ (f (κ v)).2
    calc ggTDρB X Bs g b
        = ggTDρB X Bs g ((b * x⁻¹) * x) := congrArg _ hb_eq
      _ = ggTDρB X Bs g (b * x⁻¹) * ggTDρB X Bs g x := map_mul _ _ _
      _ = (b * x⁻¹) * ((f (κ v) : MulAut ↥Bs) x) := by rw [hfixL, hAx]
      _ = (f (κ v) : MulAut ↥Bs) (b * x⁻¹) * (f (κ v) : MulAut ↥Bs) x := by rw [hfixR]
      _ = (f (κ v) : MulAut ↥Bs) ((b * x⁻¹) * x) :=
            (map_mul (f (κ v) : MulAut ↥Bs) (b * x⁻¹) x).symm
      _ = (f (κ v) : MulAut ↥Bs) b := congrArg _ hb_eq.symm
  exact ⟨Additive ↥Bs, inferInstance, inferInstance, AddEquiv.refl _, φ, hh, α, f, κ,
    hlin, hrefl, hpair, hf, hclos, hκ, hframe, hbx, haut, hFε⟩

end CFSG.StandardType

end
