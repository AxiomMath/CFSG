module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviCore
public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJCoverWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesCore
public import CFSG.LocalAnalysis.StandardType.GGTBRowF4CoreAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open scoped IsMulCommutative

theorem ggWeyl_smul_sum_frame
    {τ : Tag} {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin τ.rank → V) (α : Fin τ.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((τ.cartan i j : ℤ) : ZMod p))
    (ρ : WeylGroup τ →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ (i : Fin τ.rank) (v : V), ρ (simple τ i) v = v - α i v • h i) :
    ∀ (w : WeylGroup τ) (x : Fin τ.rank → ℤ),
      ρ w (∑ k, (x k : ZMod p) • h k) = ∑ k, ((w • x) k : ZMod p) • h k := by
  intro w
  induction w using (coxeterSystem τ).simple_induction_left with
  | one => intro x; simp
  | mul_simple_left w i ih =>
    intro x
    rw [map_mul, LinearEquiv.mul_apply, ih x, hρ i, mul_smul, simple_smul]
    have hα : α i (∑ k, ((w • x) k : ZMod p) • h k) =
        ((∑ j, τ.cartan i j * (w • x) j : ℤ) : ZMod p) := by
      rw [map_sum]
      push_cast
      exact Finset.sum_congr rfl fun k _ => by rw [map_smul, hpair, smul_eq_mul, mul_comm]
    rw [hα]
    set c : ℤ := ∑ j, τ.cartan i j * (w • x) j with hc
    have hr : ∀ k, ((reflect τ i (w • x) k : ℤ) : ZMod p) = ((w • x) k : ZMod p) -
        (c : ZMod p) * (((Pi.single i (1 : ℤ) : Fin τ.rank → ℤ) k : ℤ) : ZMod p) := by
      intro k
      simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul, hc]
    simp only [hr, sub_smul, Finset.sum_sub_distrib, mul_smul]
    congr 1
    rw [← Finset.smul_sum, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

theorem f4_torusAct_simple {p : ℕ} [NeZero p] (k : Fin Tag.F4.rank)
    (s : Fin Tag.F4.rank → ZMod p) :
    TableBExc.torusAct .F4 p (simple .F4 k) s =
      s - (∑ j, ((Tag.cartan .F4 k j : ℤ) : ZMod p) * s j) • Pi.single k 1 := by
  rw [TableBExc.torusAct, simple_smul]
  funext i
  simp only [TableBExc.redMod, TableBExc.liftMod, reflect, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  push_cast
  rw [ZMod.natCast_zmod_val]
  congr 2
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ZMod.natCast_zmod_val]
  · by_cases hi : i = k
    · subst hi
      simp
    · simp [hi]

private theorem f4fr_eq_of_mem_X_of_eps_eq {G H : Type} [Group G] [Group H] {p : ℕ}
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
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
      simpa using hBs.2 ((b₁ * b₂⁻¹ : ↥Bs) : G) (b₁ * b₂⁻¹).2
    have hcenter1 := hZp _ hcenter hpow
    refine Subtype.ext ?_
    simpa using congrArg (fun x : ↥X => (x : G)) hcenter1
  calc b₁ = b₁ * b₂⁻¹ * b₂ := by group
    _ = b₂ := by rw [hmem]; simp

private theorem f4fr_sum_single (n : ℕ) {p : ℕ} (c : Fin n → ZMod p) :
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

private theorem f4fr_eps_sum {G H : Type} [Group G] [Group H] {n : ℕ} {p : ℕ} [Fact p.Prime]
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
    exact f4fr_sum_single n c
  rw [← hcoord, h1]

private theorem f4fr_toMul_sum_mem {G : Type} [Group G] {n : ℕ} {p : ℕ} [Fact p.Prime]
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

private theorem f4fr_ofMul_eq_sum_of_coord {G H : Type} [Group G] [Group H] {n : ℕ} {p : ℕ}
    [Fact p.Prime] {Bs X : Subgroup G} [CFSG.IsElementaryAbelian p ↥Bs]
    (hBs : IsElemAbelian p Bs)
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
    rw [f4fr_eps_sum ε coordL hcoord bk hbk c, hεx]
  have hmem := f4fr_toMul_sum_mem bk hbkX c
  have hxeq : x = Additive.toMul (∑ j, c j • (Additive.ofMul (bk j) : Additive ↥Bs)) :=
    f4fr_eq_of_mem_X_of_eps_eq hBs hZp ε hker hx hmem heps.symm
  rw [hxeq]
  simp

private theorem f4fr_ggAutomizer_apply_of_mem_centralizer {G : Type} [Group G]
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

theorem f4Levi_datum
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hZp : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {R : Type} [Group R]
    (ψ : ↥X →* R) {E : Subgroup R}
    (ε : ↥Bs →* R)
    (hεE : ∀ b, ε b ∈ E) (hεsurj : ∀ c ∈ E, ∃ b, ε b = c)
    (hεker : ∀ b, ε b = 1 ↔ (b : G) ∈ Subgroup.centralizer (X : Set G))
    (hεX : ∀ (b : ↥Bs) (hb : (b : G) ∈ X), ε b = ψ ⟨b, hb⟩)
    (hεlift : ∀ b, ∃ x : ↥X, (x : G) ∈ Bs ∧ ψ x = ε b)
    (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod p) →* R)
    (hι₀ : Function.Injective ι₀) (hrange : ι₀.range = E)
    (n : Fin Tag.F4.rank → ↥X)
    (hnk : ∀ k, (n k : G) ∈ Subgroup.normalizer (Bs : Set G))
    (hact : ∀ k s, ψ (n k) * ι₀ (Multiplicative.ofAdd s) * (ψ (n k))⁻¹ =
      ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p (simple .F4 k) s)))
    (f : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer X Bs))
    (hf : ∀ k, (f (CoxeterMatrix.F₄.simple k) : MulAut ↥Bs) = ggConjAut Bs (hnk k))
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range fun k => ggConjAut Bs (hnk k))) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Fin 4 → MulAut ↥Bs) (h : Fin 4 → V) (α : Fin 4 → Module.Dual (ZMod p) V)
      (f : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer X Bs))
      (κ : WeylGroup .F4 ≃* CoxeterMatrix.F₄.Group),
      (∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = ((Tag.cartan .F4 i j : ℤ) : ZMod p)) ∧
      (∀ i, (f (CoxeterMatrix.F₄.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (∀ i, κ (simple .F4 i) = CoxeterMatrix.F₄.simple i) ∧
      (∀ (b : ↥Bs) (s : Fin Tag.F4.rank → ZMod p), ι₀ (Multiplicative.ofAdd s) = ε b →
        ∀ k, α k (ι (Additive.ofMul b)) = ∑ j, ((Tag.cartan .F4 k j : ℤ) : ZMod p) * s j) ∧
      (∀ k, ∃ b : ↥Bs, ι (Additive.ofMul b) = h k ∧ (b : G) ∈ X ∧
        ε b = ι₀ (Multiplicative.ofAdd (Pi.single k 1))) ∧
      (∀ (g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) (v : WeylGroup .F4),
        (∀ s, ψ ⟨g, g.2.1⟩ * ι₀ (Multiplicative.ofAdd s) * (ψ ⟨g, g.2.1⟩)⁻¹ =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p v s))) →
        ggTDρB X Bs g = (f (κ v) : MulAut ↥Bs)) ∧
      ∀ (u : WeylGroup .F4) (b : ↥Bs) (s : Fin Tag.F4.rank → ZMod p),
        ι₀ (Multiplicative.ofAdd s) = ε b →
        ε ((f (κ u) : MulAut ↥Bs) b) =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p u s)) := by
  classical
  have hEA : CFSG.IsElementaryAbelian p ↥Bs := hBs.isElementaryAbelian
  let xlift : ↥Bs → ↥X := fun b => (hεlift b).choose
  have hxliftB : ∀ b, (xlift b : G) ∈ Bs := fun b => (hεlift b).choose_spec.1
  have hxliftψ : ∀ b, ψ (xlift b) = ε b := fun b => (hεlift b).choose_spec.2
  have hex : ∀ k : Fin Tag.F4.rank, ∃ b : ↥Bs,
      ε b = ι₀ (Multiplicative.ofAdd (Pi.single k 1)) := by
    intro k
    exact hεsurj _ (by rw [← hrange]; exact ⟨_, rfl⟩)
  let b0 : Fin Tag.F4.rank → ↥Bs := fun k => Classical.choose (hex k)
  have hb0 : ∀ k, ε (b0 k) = ι₀ (Multiplicative.ofAdd (Pi.single k 1)) :=
    fun k => Classical.choose_spec (hex k)
  let bk : Fin Tag.F4.rank → ↥Bs := fun k =>
    ⟨(xlift (b0 k) : G), hxliftB (b0 k)⟩
  have hbkX : ∀ k, (bk k : G) ∈ X := fun k => (xlift (b0 k)).2
  have hbk_eps : ∀ k, ε (bk k) = ι₀ (Multiplicative.ofAdd (Pi.single k 1)) := by
    intro k
    have hcoe : (⟨bk k, hbkX k⟩ : ↥X) = xlift (b0 k) := Subtype.ext rfl
    rw [hεX (bk k) (hbkX k), hcoe, hxliftψ, hb0 k]
  have hexc : ∀ b : ↥Bs, ∃ s : Fin Tag.F4.rank → ZMod p,
      ι₀ (Multiplicative.ofAdd s) = ε b := by
    intro b
    have h : ε b ∈ E := hεE b
    rw [← hrange] at h
    exact h
  let coord : ↥Bs → (Fin Tag.F4.rank → ZMod p) := fun b => Classical.choose (hexc b)
  have hcoord : ∀ b, ι₀ (Multiplicative.ofAdd (coord b)) = ε b :=
    fun b => Classical.choose_spec (hexc b)
  have hofAdd_inj : ∀ {s t : Fin Tag.F4.rank → ZMod p},
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
  let coordA : Additive ↥Bs →+ (Fin Tag.F4.rank → ZMod p) :=
    AddMonoidHom.mk' (fun v => coord (Additive.toMul v)) (fun v v' => hcoord_mul _ _)
  let coordL : Additive ↥Bs →ₗ[ZMod p] (Fin Tag.F4.rank → ZMod p) := coordA.toZModLinearMap p
  have hcoordL_apply : ∀ v, coordL v = coord (Additive.toMul v) := fun v => rfl
  have hcoordL : ∀ v, ι₀ (Multiplicative.ofAdd (coordL v)) = ε (Additive.toMul v) :=
    fun v => hcoord (Additive.toMul v)
  have hcoordL_bk : ∀ k, coordL (Additive.ofMul (bk k)) = Pi.single k 1 := by
    intro k
    rw [hcoordL_apply, toMul_ofMul]
    exact hcoord_bk k
  let cartanRow (k : Fin Tag.F4.rank) : (Fin Tag.F4.rank → ZMod p) →+ ZMod p :=
    AddMonoidHom.mk' (fun s => ∑ j, ((Tag.cartan .F4 k j : ℤ) : ZMod p) * s j) (fun s t => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
  let α : Fin Tag.F4.rank → Module.Dual (ZMod p) (Additive ↥Bs) := fun k =>
    ((cartanRow k).comp coordA).toZModLinearMap p
  have hα : ∀ (k : Fin Tag.F4.rank) (v : Additive ↥Bs),
      α k v = ∑ j, ((Tag.cartan .F4 k j : ℤ) : ZMod p) * coord (Additive.toMul v) j :=
    fun k v => rfl
  let φ : Fin Tag.F4.rank → MulAut ↥Bs := fun k => ggConjAut Bs (hnk k)
  let hh : Fin Tag.F4.rank → Additive ↥Bs := fun k => Additive.ofMul (bk k)
  have happ : ∀ (i : Fin Tag.F4.rank) (b' : ↥Bs), ((φ i b' : ↥Bs) : G) =
      (n i : G) * b' * (n i : G)⁻¹ := by
    intro i b'
    exact ggConjAut_apply Bs (hnk i) b'
  have hKlin : ∀ (i : Fin Tag.F4.rank) (b : ↥Bs),
      φ i b = b * (bk i ^ (∑ j, ((Tag.cartan .F4 i j : ℤ) : ZMod p) * coord b j).val)⁻¹ := by
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
      exact X.mul_mem (X.mul_mem (n i).2 hxX) (X.inv_mem (n i).2)
    have hxe : (⟨φ i x, hφxX⟩ : ↥X) =
        n i * (⟨x, hxX⟩ : ↥X) * (n i)⁻¹ := by
      apply Subtype.ext
      rw [happ i x]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hεφx : ε (φ i x) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p (simple .F4 i) (coord b))) := by
      rw [hεX (φ i x) hφxX, hxe, map_mul, map_mul, map_inv,
        ← hεX x hxX, hxeps, ← hcoord b]
      exact hact i (coord b)
    have hexp : ι₀ (Multiplicative.ofAdd (Pi.single i 1)) ^
          (∑ j, ((Tag.cartan .F4 i j : ℤ) : ZMod p) * coord b j).val =
        ι₀ (Multiplicative.ofAdd ((∑ j, ((Tag.cartan .F4 i j : ℤ) : ZMod p) * coord b j).val •
          Pi.single i 1)) := by
      rw [ofAdd_nsmul, map_pow]
    have hεy : ε (x * (bk i ^ (∑ j, ((Tag.cartan .F4 i j : ℤ) : ZMod p) * coord b j).val)⁻¹) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p (simple .F4 i) (coord b))) := by
      rw [map_mul, map_inv, map_pow, hxeps, hbk_eps, ← hcoord b, hexp,
        ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val,
        f4_torusAct_simple i (coord b), sub_eq_add_neg, ofAdd_add, ofAdd_neg, map_mul, map_inv]
    have hφx : φ i x = x * (bk i ^ (∑ j, ((Tag.cartan .F4 i j : ℤ) : ZMod p) * coord b j).val)⁻¹ :=
      f4fr_eq_of_mem_X_of_eps_eq hBs hZp ε hεker hφxX
        (X.mul_mem hxX (X.inv_mem (X.pow_mem (hbkX i) _))) (hεφx.trans hεy.symm)
    have hφmem : φ i ∈ ggAutomizer X Bs :=
      ggConjAut_mem_ggAutomizer (n i).2 (hnk i)
    calc φ i b = φ i ((b * x⁻¹) * x) := by
          congr 1
          group
      _ = φ i (b * x⁻¹) * φ i x := map_mul _ _ _
      _ = (b * x⁻¹) * φ i x := by
            rw [f4fr_ggAutomizer_apply_of_mem_centralizer hc_mem (φ i) hφmem]
      _ = (b * x⁻¹) * (x * (bk i ^
            (∑ j, ((Tag.cartan .F4 i j : ℤ) : ZMod p) * coord b j).val)⁻¹) := by
            rw [hφx]
      _ = b * (bk i ^ (∑ j, ((Tag.cartan .F4 i j : ℤ) : ZMod p) * coord b j).val)⁻¹ := by
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
    have hsm : (∑ j, ((Tag.cartan .F4 i j : ℤ) : ZMod p) * coord b j) •
        (Additive.ofMul (bk i) : Additive ↥Bs) =
        Additive.ofMul (bk i ^ (∑ j, ((Tag.cartan .F4 i j : ℤ) : ZMod p) * coord b j).val) := by
      rw [ofMul_pow, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    rw [hsm, ofMul_mul, ofMul_inv]
    abel
  have hpair : ∀ i j, α i (hh j) = ((Tag.cartan .F4 i j : ℤ) : ZMod p) := by
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
  have hdiag : ∀ i : Fin Tag.F4.rank, ((Tag.cartan .F4 i i : ℤ) : ZMod p) = 2 := by
    intro i
    have h : Tag.cartan .F4 i i = 2 := by fin_cases i <;> rfl
    rw [h]
    norm_num
  have hrefl : ∀ i, GGIsReflection p (φ i) := by
    intro i
    have hfx : α i (hh i) = 2 := (hpair i i).trans (hdiag i)
    have hL : ggLin (p := p) (AddEquiv.refl (Additive ↥Bs)) (φ i) = Module.reflection hfx :=
      ggLin_eq_reflection _ hfx (fun v => hlin i v)
    exact ggIsReflection_of_eq_reflection hp2 _ hfx hL
  let κ : WeylGroup .F4 ≃* CoxeterMatrix.F₄.Group := ggF4Row_coxeterGroupEquiv.symm
  have hκ : ∀ i, κ (simple .F4 i) = CoxeterMatrix.F₄.simple i := by
    intro i
    apply ggF4Row_coxeterGroupEquiv.injective
    rw [MulEquiv.apply_symm_apply, ggF4Row_coxeterGroupEquiv_simple]
  let ρ : WeylGroup .F4 →* (Additive ↥Bs ≃ₗ[ZMod p] Additive ↥Bs) :=
    (ggLin (p := p) (AddEquiv.refl (Additive ↥Bs))).comp
      ((ggAutomizer X Bs).subtype.comp (f.toMonoidHom.comp κ.toMonoidHom))
  have hρu : ∀ u, ρ u = ggLin (p := p) (AddEquiv.refl (Additive ↥Bs)) (f (κ u) : MulAut ↥Bs) :=
    fun u => rfl
  have hρ : ∀ (i : Fin Tag.F4.rank) (v : Additive ↥Bs), ρ (simple .F4 i) v = v - α i v • hh i := by
    intro i v
    rw [hρu, hκ i]
    have h1 : (f (CoxeterMatrix.F₄.simple i) : MulAut ↥Bs) = φ i := hf i
    rw [h1]
    exact hlin i v
  have hκcoord : ∀ (u : WeylGroup .F4) (c : Fin Tag.F4.rank → ℤ),
      ggLin (p := p) (AddEquiv.refl (Additive ↥Bs)) (f (κ u) : MulAut ↥Bs)
          (∑ j, (c j : ZMod p) • hh j) = ∑ j, ((u • c) j : ZMod p) • hh j := by
    intro u c
    rw [← hρu]
    exact ggWeyl_smul_sum_frame (p := p) hh α hpair ρ hρ u c
  have hframe : ∀ (b : ↥Bs) (s : Fin Tag.F4.rank → ZMod p),
      ι₀ (Multiplicative.ofAdd s) = ε b → ∀ k,
      α k (AddEquiv.refl (Additive ↥Bs) (Additive.ofMul b)) =
        ∑ j, ((Tag.cartan .F4 k j : ℤ) : ZMod p) * s j := by
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
  have hFε : ∀ (u : WeylGroup .F4) (b : ↥Bs) (s : Fin Tag.F4.rank → ZMod p),
      ι₀ (Multiplicative.ofAdd s) = ε b →
      ε ((f (κ u) : MulAut ↥Bs) b) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p u s)) := by
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
        ∑ j, ((TableBExc.liftMod .F4 p (coord b)) j : ZMod p) • hh j := by
      have hcx : coordL (Additive.ofMul x) =
          fun j => ((TableBExc.liftMod .F4 p (coord b)) j : ZMod p) := by
        rw [hcoordL_apply, toMul_ofMul, hcoords]
        funext j
        simp [TableBExc.liftMod]
      exact f4fr_ofMul_eq_sum_of_coord hBs hZp ε hεker coordL hcoordL bk hbkX hcoordL_bk hxX
        (fun j => ((TableBExc.liftMod .F4 p (coord b)) j : ZMod p)) hcx
    have hval : Additive.ofMul ((f (κ u) : MulAut ↥Bs) x) =
        ∑ j, ((u • TableBExc.liftMod .F4 p (coord b)) j : ZMod p) • hh j := by
      rw [show Additive.ofMul ((f (κ u) : MulAut ↥Bs) x) =
          AddEquiv.refl (Additive ↥Bs) (Additive.ofMul ((f (κ u) : MulAut ↥Bs) x)) from rfl]
      rw [← ggLin_apply_ofMul (p := p) (AddEquiv.refl (Additive ↥Bs))
        (f (κ u) : MulAut ↥Bs) x, hsumx]
      exact hκcoord u (TableBExc.liftMod .F4 p (coord b))
    have hεx : ε ((f (κ u) : MulAut ↥Bs) x) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p u (coord b))) := by
      have h := congrArg (fun a : Additive ↥Bs => ε (Additive.toMul a)) hval
      rw [f4fr_eps_sum ε coordL hcoordL bk hcoordL_bk
        (fun j => ((u • TableBExc.liftMod .F4 p (coord b)) j : ZMod p))] at h
      have hred : (fun j => ((u • TableBExc.liftMod .F4 p (coord b)) j : ZMod p)) =
          TableBExc.torusAct .F4 p u (coord b) := rfl
      rw [hred] at h
      simpa [toMul_ofMul] using h
    have hfixR : (f (κ u) : MulAut ↥Bs) (b * x⁻¹) = b * x⁻¹ :=
      f4fr_ggAutomizer_apply_of_mem_centralizer hc_mem _ (f (κ u)).2
    have hεc : ε (b * x⁻¹) = 1 := by rw [map_mul, map_inv, hxeps, mul_inv_cancel]
    have hb_eq : b = (b * x⁻¹) * x := by group
    calc ε ((f (κ u) : MulAut ↥Bs) b)
        = ε ((f (κ u) : MulAut ↥Bs) ((b * x⁻¹) * x)) := by rw [← hb_eq]
      _ = ε ((f (κ u) : MulAut ↥Bs) (b * x⁻¹)) * ε ((f (κ u) : MulAut ↥Bs) x) := by
          rw [map_mul, map_mul]
      _ = ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p u s)) := by
          rw [hfixR, hεc, one_mul, hεx, hsb]
  have haut : ∀ (g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) (v : WeylGroup .F4),
      (∀ s, ψ ⟨g, g.2.1⟩ * ι₀ (Multiplicative.ofAdd s) * (ψ ⟨g, g.2.1⟩)⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p v s))) →
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
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p v (coord b))) := by
      have hxe : (⟨ggTDρB X Bs g x, hLxX⟩ : ↥X) =
          (⟨(g : G), g.2.1⟩ : ↥X) * (⟨x, hxX⟩ : ↥X) * (⟨(g : G), g.2.1⟩ : ↥X)⁻¹ := by
        apply Subtype.ext
        rw [ggTDρB_apply]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hεX _ hLxX, hxe, map_mul, map_mul, map_inv, ← hεX x hxX, hxeps, ← hcoord b]
      exact hv (coord b)
    have hεR : ε ((f (κ v) : MulAut ↥Bs) x) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p v (coord b))) := by
      have hsumx : Additive.ofMul x =
          ∑ j, ((TableBExc.liftMod .F4 p (coord b)) j : ZMod p) • hh j := by
        have hcx : coordL (Additive.ofMul x) =
            fun j => ((TableBExc.liftMod .F4 p (coord b)) j : ZMod p) := by
          rw [hcoordL_apply, toMul_ofMul, hcoords]
          funext j
          simp [TableBExc.liftMod]
        exact f4fr_ofMul_eq_sum_of_coord hBs hZp ε hεker coordL hcoordL bk hbkX hcoordL_bk hxX
          (fun j => ((TableBExc.liftMod .F4 p (coord b)) j : ZMod p)) hcx
      have hval : Additive.ofMul ((f (κ v) : MulAut ↥Bs) x) =
          ∑ j, ((v • TableBExc.liftMod .F4 p (coord b)) j : ZMod p) • hh j := by
        rw [show Additive.ofMul ((f (κ v) : MulAut ↥Bs) x) =
            AddEquiv.refl (Additive ↥Bs) (Additive.ofMul ((f (κ v) : MulAut ↥Bs) x)) from rfl]
        rw [← ggLin_apply_ofMul (p := p) (AddEquiv.refl (Additive ↥Bs))
          (f (κ v) : MulAut ↥Bs) x, hsumx]
        exact hκcoord v (TableBExc.liftMod .F4 p (coord b))
      have h := congrArg (fun a : Additive ↥Bs => ε (Additive.toMul a)) hval
      rw [f4fr_eps_sum ε coordL hcoordL bk hcoordL_bk
        (fun j => ((v • TableBExc.liftMod .F4 p (coord b)) j : ZMod p))] at h
      have hred : (fun j => ((v • TableBExc.liftMod .F4 p (coord b)) j : ZMod p)) =
          TableBExc.torusAct .F4 p v (coord b) := rfl
      rw [hred] at h
      simpa [toMul_ofMul] using h
    have hAx : ggTDρB X Bs g x = (f (κ v) : MulAut ↥Bs) x :=
      f4fr_eq_of_mem_X_of_eps_eq hBs hZp ε hεker hLxX hRxX (hεL.trans hεR.symm)
    have hb_eq : b = (b * x⁻¹) * x := by group
    have hfixL : ggTDρB X Bs g (b * x⁻¹) = b * x⁻¹ := by
      apply Subtype.ext
      rw [ggTDρB_apply, (Subgroup.mem_centralizer_iff.mp hc_mem) (g : G) g.2.1,
        mul_inv_cancel_right]
    have hfixR : (f (κ v) : MulAut ↥Bs) (b * x⁻¹) = b * x⁻¹ :=
      f4fr_ggAutomizer_apply_of_mem_centralizer hc_mem _ (f (κ v)).2
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
