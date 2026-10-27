module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnModel
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open scoped IsMulCommutative

private theorem eq_one_of_mem_centralizer_of_center_eq_bot {G : Type} [Group G] {X : Subgroup G}
    (hX : Subgroup.center X = ⊥) {z : G} (hzX : z ∈ X)
    (hzC : z ∈ Subgroup.centralizer (X : Set G)) : z = 1 := by
  have hz : (⟨z, hzX⟩ : X) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC (w : G) w.2
  rw [hX, Subgroup.mem_bot] at hz
  simpa using congrArg Subtype.val hz

private theorem eq_of_conj_eq_of_center_eq_bot {G : Type} [Group G] {X : Subgroup G}
    (hX : Subgroup.center X = ⊥) {u v : G} (huX : u ∈ X) (hvX : v ∈ X)
    (h : ∀ y ∈ X, u * y * u⁻¹ = v * y * v⁻¹) : u = v := by
  have huvX : u⁻¹ * v ∈ X := X.mul_mem (X.inv_mem huX) hvX
  have huvC : u⁻¹ * v ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    calc y * (u⁻¹ * v) = u⁻¹ * (u * y * u⁻¹) * v := by group
      _ = u⁻¹ * (v * y * v⁻¹) * v := by rw [h y hy]
      _ = (u⁻¹ * v) * y := by group
  have h1 : u⁻¹ * v = 1 := eq_one_of_mem_centralizer_of_center_eq_bot hX huvX huvC
  calc u = u * 1 := by group
    _ = u * (u⁻¹ * v) := by rw [h1]
    _ = v := by group

private theorem mem_centralizer_of_conj_action {G : Type} [Group G] {X : Subgroup G} {b x : G}
    (h : ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    x⁻¹ * b ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  calc y * (x⁻¹ * b) = x⁻¹ * (x * y * x⁻¹) * b := by group
    _ = x⁻¹ * (b * y * b⁻¹) * b := by rw [← h y hy]
    _ = (x⁻¹ * b) * y := by group

private theorem mem_bstar_of_conj_eq {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hZX : Subgroup.center X = ⊥) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {b x : G} (hb : b ∈ Bs) (hxX : x ∈ X)
    (hact : ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) : x ∈ Bs := by
  have hcomm : x ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    have hb'X : b' ∈ Subgroup.normalizer (X : Set G) := hN hb'
    have hb'xX : b' * x * b'⁻¹ ∈ X :=
      ((Subgroup.mem_normalizer_iff.mp hb'X) x).mp hxX
    have hact' : ∀ y ∈ X, b' * x * b'⁻¹ * y * (b' * x * b'⁻¹)⁻¹ = x * y * x⁻¹ := by
      intro y hy
      have hb'iyX : b'⁻¹ * y * b' ∈ X := by
        simpa using ((Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (X : Set G)).inv_mem hb'X)) y).mp hy
      calc b' * x * b'⁻¹ * y * (b' * x * b'⁻¹)⁻¹
          = b' * (x * (b'⁻¹ * y * b') * x⁻¹) * b'⁻¹ := by group
        _ = b' * (b * (b'⁻¹ * y * b') * b⁻¹) * b'⁻¹ := by rw [hact _ hb'iyX]
        _ = (b' * b * b'⁻¹) * y * (b' * b * b'⁻¹)⁻¹ := by group
        _ = b * y * b⁻¹ := by
              rw [CFSG.Open.IsElemAbelian.comm hBs hb' hb]
              group
        _ = x * y * x⁻¹ := hact y hy
    have hu_eq : b' * x * b'⁻¹ = x :=
      eq_of_conj_eq_of_center_eq_bot hZX hb'xX hxX hact'
    calc b' * x = (b' * x * b'⁻¹) * b' := by group
      _ = x * b' := by rw [hu_eq]
  have hcC : x⁻¹ * b ∈ Subgroup.centralizer (X : Set G) :=
    mem_centralizer_of_conj_action hact
  have hxc : Commute x (x⁻¹ * b) :=
    Subgroup.mem_centralizer_iff.mp hcC x hxX
  have hbp : b ^ p = 1 := hBs.2 b hb
  have hbp' : b ^ p = x ^ p * (x⁻¹ * b) ^ p := by
    rw [← hxc.mul_pow]
    congr 1
    group
  have hxbpC : x ^ p ∈ Subgroup.centralizer (X : Set G) := by
    have hmul : x ^ p * (x⁻¹ * b) ^ p = 1 := by rw [← hbp', hbp]
    rw [mul_eq_one_iff_eq_inv.mp hmul]
    exact (Subgroup.centralizer (X : Set G)).inv_mem
      ((Subgroup.centralizer (X : Set G)).pow_mem hcC p)
  have hxbp1 : x ^ p = 1 :=
    eq_one_of_mem_centralizer_of_center_eq_bot hZX (X.pow_mem hxX p) hxbpC
  exact hSC x hcomm hxbp1

private theorem cartanMatrix_E7_transpose : (CartanMatrix.E₇).transpose = CartanMatrix.E₇ := by
  decide +kernel

private theorem cartanMatrix_E7_symm (i j : Fin Tag.E7.rank) :
    CartanMatrix.E₇ i j = CartanMatrix.E₇ j i := by
  conv_lhs => rw [← cartanMatrix_E7_transpose]
  rfl

private theorem cartan_E7_eq : Tag.cartan .E7 = CartanMatrix.E₇ := by
  rw [show Tag.cartan .E7 = Tag.cartanE 7 from rfl, CFSG.LieType.Chevalley.cartanE_eq 7]

private theorem symmetrizedCartan_E7_eq : Tag.symmetrizedCartan .E7 = CartanMatrix.E₇ := by
  rw [show Tag.symmetrizedCartan .E7 = Tag.cartan .E7 from by decide +kernel, cartan_E7_eq]

private theorem frameCoord_single (p : ℕ) (j i : Fin Tag.E7.rank) :
    ExcFrames.frameCoord .E7 p (Pi.single j 1) i = ((CartanMatrix.E₇ i j : ℤ) : ZMod p) := by
  rw [ExcFrames.frameCoord, symmetrizedCartan_E7_eq]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [hbj]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem torusAct_simple_E7 {p : ℕ} [NeZero p] (k : Fin Tag.E7.rank)
    (s : Fin Tag.E7.rank → ZMod p) :
    TableBExc.torusAct .E7 p (simple .E7 k) s =
      s - (ExcFrames.frameCoord .E7 p s k) • Pi.single k 1 := by
  have hsymm : ∀ i j : Fin Tag.E7.rank, Tag.cartan .E7 i j = Tag.cartan .E7 j i := by
    intro i j
    rw [cartan_E7_eq]
    exact cartanMatrix_E7_symm i j
  rw [← TableBExc.torusRefl_eq_torusAct (τ := .E7) (p := p) hsymm k s, TableBExc.torusRefl]
  congr 2
  rw [ExcFrames.frameCoord, symmetrizedCartan_E7_eq, cartan_E7_eq]
  exact Finset.sum_congr rfl fun j _ => by rw [cartanMatrix_E7_symm j k]

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

theorem e7Levi_adjointModel
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {Fq : Type} [Field Fq] [Finite Fq] (e : ↥X ≃* adjointGroup .E7 Fq)
    (hZX : Subgroup.center X = ⊥)
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {r : ℕ} (hlb : p ^ r ≤ Nat.card (ggGamma X hN).range) :
    ∃ E : Subgroup (adjointGroup .E7 Fq),
      IsElemAbelian p E ∧ p ^ r ≤ Nat.card E ∧
      (∀ g : adjointGroup .E7 Fq, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
      (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
        E.map (MulAut.conj : adjointGroup .E7 Fq →* MulAut (adjointGroup .E7 Fq)) := by
  classical
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup .E7 Fq →* MulAut (adjointGroup .E7 Fq)) :=
    mulAut_conj_injective_adjointGroup
  let E : Subgroup (adjointGroup .E7 Fq) := (Bs.subgroupOf X).map e.toMonoidHom
  have hcongr_conj : ∀ x : ↥X,
      MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
    intro x
    ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hArange : (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : adjointGroup .E7 Fq →* MulAut (adjointGroup .E7 Fq)) := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, rfl⟩ := ha
      obtain ⟨x, hxX, hxact⟩ := hinner b b.2
      have hxBs : x ∈ Bs := mem_bstar_of_conj_eq hBs hSC hZX hN b.2 hxX hxact
      have hxsub : (⟨x, hxX⟩ : ↥X) ∈ Bs.subgroupOf X := hxBs
      have hconj : ggGamma X hN b = MulAut.conj (⟨x, hxX⟩ : ↥X) := by
        ext y
        exact hxact y y.2
      have hmemE : e ⟨x, hxX⟩ ∈ E := Subgroup.mem_map_of_mem e.toMonoidHom hxsub
      have heq : MulAut.conj (e ⟨x, hxX⟩) =
          (MulAut.congr e).toMonoidHom (ggGamma X hN b) := by
        rw [hconj]
        exact (hcongr_conj _).symm
      rw [← heq]
      exact Subgroup.mem_map_of_mem _ hmemE
    · rintro _ ⟨c, hc, rfl⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hc
      change MulAut.conj (e x) ∈ (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom
      have hxBs : (x : G) ∈ Bs := hx
      have hconj : ggGamma X hN ⟨(x : G), hxBs⟩ = MulAut.conj x := by
        ext y
        rfl
      have heq : MulAut.conj (e x) =
          (MulAut.congr e).toMonoidHom (ggGamma X hN ⟨(x : G), hxBs⟩) := by
        rw [hconj]
        exact (hcongr_conj x).symm
      rw [heq]
      exact Subgroup.mem_map_of_mem _ ⟨⟨(x : G), hxBs⟩, rfl⟩
  have hEel : IsElemAbelian p E := (hBs.subgroupOf X).map e.toMonoidHom
  have hcardEq : Nat.card E = Nat.card (ggGamma X hN).range := by
    have h2 : Nat.card ((ggGamma X hN).range.map (MulAut.congr e).toMonoidHom) =
        Nat.card (ggGamma X hN).range :=
      Subgroup.card_map_of_injective (MulAut.congr e).injective
    have h3 : Nat.card (E.map (MulAut.conj :
        adjointGroup .E7 Fq →* MulAut (adjointGroup .E7 Fq))) = Nat.card E :=
      Subgroup.card_map_of_injective hinj
    rw [← h3, ← h2, hArange]
  have hEcard : p ^ r ≤ Nat.card E := by
    rw [hcardEq]
    exact hlb
  have hEsc : ∀ g : adjointGroup .E7 Fq,
      (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E := by
    intro g hgc hgp
    let z : ↥X := e.symm g
    have hzg : e z = g := e.apply_symm_apply g
    have hzC : (z : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨x, hxX, hxact⟩ := hinner b hb
      have hxBs : x ∈ Bs := mem_bstar_of_conj_eq hBs hSC hZX hN hb hxX hxact
      have hEx : e ⟨x, hxX⟩ ∈ E :=
        Subgroup.mem_map_of_mem e.toMonoidHom (show (⟨x, hxX⟩ : ↥X) ∈ Bs.subgroupOf X from hxBs)
      have hzx : z * (⟨x, hxX⟩ : ↥X) = ⟨x, hxX⟩ * z := by
        have h := hgc (e ⟨x, hxX⟩) hEx
        have h' : e.symm (g * e ⟨x, hxX⟩) = e.symm (e ⟨x, hxX⟩ * g) := by rw [h]
        simpa using h'
      have hzx' : (z : G) * x = x * (z : G) := congrArg Subtype.val hzx
      have hcb : x⁻¹ * b ∈ Subgroup.centralizer (X : Set G) :=
        mem_centralizer_of_conj_action hxact
      have hzc : (z : G) * (x⁻¹ * b) = (x⁻¹ * b) * (z : G) :=
        Subgroup.mem_centralizer_iff.mp hcb (z : G) z.2
      have hzxc : (z : G) * (x * (x⁻¹ * b)) = (x * (x⁻¹ * b)) * (z : G) := by
        calc (z : G) * (x * (x⁻¹ * b)) = ((z : G) * x) * (x⁻¹ * b) := by group
          _ = (x * (z : G)) * (x⁻¹ * b) := by rw [hzx']
          _ = x * ((z : G) * (x⁻¹ * b)) := by group
          _ = x * ((x⁻¹ * b) * (z : G)) := by rw [hzc]
          _ = (x * (x⁻¹ * b)) * (z : G) := by group
      have hbEq : (b : G) = x * (x⁻¹ * b) := by group
      rw [hbEq]
      exact hzxc.symm
    have hzpX : z ^ p = 1 := by
      apply e.injective
      rw [map_pow, hzg, hgp, map_one]
    have hzp : (z : G) ^ p = 1 := by
      simpa using congrArg Subtype.val hzpX
    have hzBs : (z : G) ∈ Bs := hSC z hzC hzp
    have hEz : g ∈ E := by
      rw [← hzg]
      exact Subgroup.mem_map_of_mem e.toMonoidHom (show z ∈ Bs.subgroupOf X from hzBs)
    exact hEz
  exact ⟨E, hEel, hEcard, hEsc, hArange⟩

theorem e7Levi_bstar
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) {K : Type} [Field K] [Finite K]
    (e : ↥X ≃* adjointGroup .E7 K) {E : Subgroup (adjointGroup .E7 K)}
    (hA : (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))) :
    ∃ ε : ↥Bs →* adjointGroup .E7 K,
      (∀ b, MulAut.congr e (ggGamma X hN b) = MulAut.conj (ε b)) ∧
      (∀ b, ε b ∈ E) ∧ (∀ c ∈ E, ∃ b, ε b = c) ∧
      (∀ b, ε b = 1 ↔ (b : G) ∈ Subgroup.centralizer (X : Set G)) ∧
      (∀ (b : ↥Bs) (hb : (b : G) ∈ X), ε b = e ⟨b, hb⟩) ∧
      (∀ b, ((e.symm (ε b) : ↥X) : G) ∈ Bs) ∧
      (∀ g : ↥X, e g ∈ Subgroup.normalizer (E : Set (adjointGroup .E7 K)) →
        (g : G) ∈ Subgroup.normalizer (Bs : Set G)) ∧
      (∀ g : ↥X, (g : G) ∈ Subgroup.normalizer (Bs : Set G) →
        e g ∈ Subgroup.normalizer (E : Set (adjointGroup .E7 K))) ∧
      ∀ (g : ↥X) (b : ↥Bs) (hb : (g : G) * b * (g : G)⁻¹ ∈ Bs),
        ε ⟨_, hb⟩ = e g * ε b * (e g)⁻¹ := by
  classical
  have hZ : Subgroup.center (adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot
  have hZX : Subgroup.center X = ⊥ := center_eq_bot_of_mulEquiv e hZ
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) :=
    mulAut_conj_injective_adjointGroup
  have hex : ∀ b : ↥Bs, ∃ c : adjointGroup .E7 K, c ∈ E ∧
      MulAut.congr e (ggGamma X hN b) = MulAut.conj c := by
    intro b
    have hb : MulAut.congr e (ggGamma X hN b) ∈
        E.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) := by
      rw [← hA]
      exact Subgroup.mem_map_of_mem _ ⟨b, rfl⟩
    obtain ⟨c, hcE, hc⟩ := Subgroup.mem_map.mp hb
    exact ⟨c, hcE, hc.symm⟩
  let epsFun : ↥Bs → adjointGroup .E7 K := fun b => (hex b).choose
  have hspec : ∀ b, epsFun b ∈ E ∧
      MulAut.congr e (ggGamma X hN b) = MulAut.conj (epsFun b) := fun b => (hex b).choose_spec
  have huniq : ∀ (b : ↥Bs) (c : adjointGroup .E7 K), c ∈ E →
      MulAut.congr e (ggGamma X hN b) = MulAut.conj c → epsFun b = c := by
    intro b c _ hc
    exact hinj (by rw [← (hspec b).2, hc])
  have hone : epsFun 1 = 1 := by
    refine huniq 1 1 E.one_mem ?_
    simp only [map_one]
  have hmul : ∀ a b : ↥Bs, epsFun (a * b) = epsFun a * epsFun b := by
    intro a b
    refine huniq (a * b) (epsFun a * epsFun b) (E.mul_mem (hspec a).1 (hspec b).1) ?_
    simp only [map_mul, (hspec a).2, (hspec b).2]
  let eps : ↥Bs →* adjointGroup .E7 K :=
    { toFun := epsFun, map_one' := hone, map_mul' := hmul }
  have hspec' : ∀ b, eps b ∈ E ∧
      MulAut.congr e (ggGamma X hN b) = MulAut.conj (eps b) := hspec
  have honto : ∀ c ∈ E, ∃ b : ↥Bs, eps b = c := by
    intro c hcE
    have hcin : MulAut.conj c ∈
        (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom := by
      rw [hA]
      exact Subgroup.mem_map_of_mem _ hcE
    obtain ⟨a, ha, haconj⟩ := Subgroup.mem_map.mp hcin
    obtain ⟨b, hb⟩ := ha
    refine ⟨b, ?_⟩
    apply hinj
    rw [← haconj, ← hb]
    exact ((hspec' b).2).symm
  have hker : ∀ b : ↥Bs, eps b = 1 ↔ (b : G) ∈ Subgroup.centralizer (X : Set G) := by
    intro b
    rw [← ggGamma_eq_one_iff X hN b]
    constructor
    · intro h
      apply (MulAut.congr e).injective
      rw [(hspec' b).2, h, map_one, map_one]
    · intro h
      apply hinj
      rw [← (hspec' b).2, h, map_one, map_one]
  have hact : ∀ (b : ↥Bs) (y : G), y ∈ X →
      (b : G) * y * (b : G)⁻¹ =
        ((e.symm (eps b) : ↥X) : G) * y * ((e.symm (eps b) : ↥X) : G)⁻¹ := by
    intro b y hy
    have hbyX : (b : G) * y * (b : G)⁻¹ ∈ X :=
      ((Subgroup.mem_normalizer_iff.mp (hN b.2)) y).mp hy
    have h1 : e (⟨(b : G) * y * (b : G)⁻¹, hbyX⟩ : ↥X) =
        eps b * e ⟨y, hy⟩ * (eps b)⁻¹ := by
      have h2 : e (ggGamma X hN b ⟨y, hy⟩) =
          (MulAut.congr e (ggGamma X hN b)) (e ⟨y, hy⟩) := by
        simp [MulAut.congr_apply]
      have h3 : (⟨(b : G) * y * (b : G)⁻¹, hbyX⟩ : ↥X) =
          ggGamma X hN b ⟨y, hy⟩ := Subtype.ext rfl
      rw [h3, h2, (hspec' b).2, MulAut.conj_apply]
    have h4 : (⟨(b : G) * y * (b : G)⁻¹, hbyX⟩ : ↥X) =
        e.symm (eps b) * ⟨y, hy⟩ * (e.symm (eps b))⁻¹ := by
      apply e.injective
      rw [h1, map_mul, map_mul, map_inv, e.apply_symm_apply]
    simpa using congrArg Subtype.val h4
  have hinner : ∀ (b : ↥Bs) (hb : (b : G) ∈ X), eps b = e ⟨b, hb⟩ := by
    intro b hb
    have hxb_eq : ((e.symm (eps b) : ↥X) : G) = (b : G) :=
      (eq_of_conj_eq_of_center_eq_bot hZX hb ((e.symm (eps b)).2) (hact b)).symm
    have hsub : e.symm (eps b) = (⟨b, hb⟩ : ↥X) := Subtype.ext hxb_eq
    calc eps b = e (e.symm (eps b)) := (e.apply_symm_apply (eps b)).symm
      _ = e ⟨b, hb⟩ := by rw [hsub]
  have hcentral : ∀ b : ↥Bs,
      ((e.symm (eps b) : ↥X) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    intro b
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    have hbX : ((e.symm (eps b) : ↥X) : G) ∈ X := (e.symm (eps b)).2
    have hb'X : (b' : G) ∈ Subgroup.normalizer (X : Set G) := hN hb'
    have huX : (b' : G) * ((e.symm (eps b) : ↥X) : G) * (b' : G)⁻¹ ∈ X :=
      ((Subgroup.mem_normalizer_iff.mp hb'X) ((e.symm (eps b) : ↥X) : G)).mp hbX
    have hact' : ∀ y ∈ X,
        (b' : G) * ((e.symm (eps b) : ↥X) : G) * (b' : G)⁻¹ * y *
          ((b' : G) * ((e.symm (eps b) : ↥X) : G) * (b' : G)⁻¹)⁻¹ =
        ((e.symm (eps b) : ↥X) : G) * y * ((e.symm (eps b) : ↥X) : G)⁻¹ := by
      intro y hy
      have hb'iyX : (b' : G)⁻¹ * y * (b' : G) ∈ X := by
        simpa using ((Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (X : Set G)).inv_mem hb'X)) y).mp hy
      calc (b' : G) * ((e.symm (eps b) : ↥X) : G) * (b' : G)⁻¹ * y *
            ((b' : G) * ((e.symm (eps b) : ↥X) : G) * (b' : G)⁻¹)⁻¹
          = (b' : G) * (((e.symm (eps b) : ↥X) : G) * ((b' : G)⁻¹ * y * (b' : G)) *
              ((e.symm (eps b) : ↥X) : G)⁻¹) * (b' : G)⁻¹ := by group
        _ = (b' : G) * ((b : G) * ((b' : G)⁻¹ * y * (b' : G)) * (b : G)⁻¹) *
              (b' : G)⁻¹ := by rw [hact b _ hb'iyX]
        _ = ((b' : G) * (b : G) * (b' : G)⁻¹) * y *
              ((b' : G) * (b : G) * (b' : G)⁻¹)⁻¹ := by group
        _ = (b : G) * y * (b : G)⁻¹ := by
            rw [CFSG.Open.IsElemAbelian.comm hBs hb' b.2]
            group
        _ = ((e.symm (eps b) : ↥X) : G) * y * ((e.symm (eps b) : ↥X) : G)⁻¹ :=
            hact b y hy
    have hu_eq : (b' : G) * ((e.symm (eps b) : ↥X) : G) * (b' : G)⁻¹ =
        ((e.symm (eps b) : ↥X) : G) :=
      eq_of_conj_eq_of_center_eq_bot hZX huX hbX hact'
    calc (b' : G) * ((e.symm (eps b) : ↥X) : G)
        = ((b' : G) * ((e.symm (eps b) : ↥X) : G) * (b' : G)⁻¹) * (b' : G) := by group
      _ = ((e.symm (eps b) : ↥X) : G) * (b' : G) := by rw [hu_eq]
  have hmem : ∀ b : ↥Bs, ((e.symm (eps b) : ↥X) : G) ∈ Bs := by
    intro b
    have hbX : ((e.symm (eps b) : ↥X) : G) ∈ X := (e.symm (eps b)).2
    have hcC : ((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G) ∈
        Subgroup.centralizer (X : Set G) :=
      mem_centralizer_of_conj_action (hact b)
    have hxc : Commute ((e.symm (eps b) : ↥X) : G)
        (((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G)) :=
      Subgroup.mem_centralizer_iff.mp hcC ((e.symm (eps b) : ↥X) : G) hbX
    have hbp : (b : G) ^ p = 1 := hBs.2 b b.2
    have hbp' : (b : G) ^ p = ((e.symm (eps b) : ↥X) : G) ^ p *
        (((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G)) ^ p := by
      rw [← hxc.mul_pow]
      congr 1
      group
    have hxbpC : ((e.symm (eps b) : ↥X) : G) ^ p ∈
        Subgroup.centralizer (X : Set G) := by
      have hmul : ((e.symm (eps b) : ↥X) : G) ^ p *
          (((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G)) ^ p = 1 := by
        rw [← hbp', hbp]
      rw [mul_eq_one_iff_eq_inv.mp hmul]
      exact (Subgroup.centralizer (X : Set G)).inv_mem
        ((Subgroup.centralizer (X : Set G)).pow_mem hcC p)
    have hxbp1 : ((e.symm (eps b) : ↥X) : G) ^ p = 1 :=
      eq_one_of_mem_centralizer_of_center_eq_bot hZX (X.pow_mem hbX p) hxbpC
    exact hSC _ (hcentral b) hxbp1
  have hequiv : ∀ (g : ↥X) (b : ↥Bs) (hb : (g : G) * (b : G) * (g : G)⁻¹ ∈ Bs),
      eps ⟨_, hb⟩ = e g * eps b * (e g)⁻¹ := by
    intro g b hb
    apply hinj
    have hgg : ggGamma X hN ⟨_, hb⟩ =
        MulAut.conj g * ggGamma X hN b * MulAut.conj g⁻¹ := by
      ext y
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ggGamma_coe]
      group
    have hconj : MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
      ext y
      obtain ⟨z, rfl⟩ := e.surjective y
      simp [MulAut.congr_apply]
    have hconj' : MulAut.congr e (MulAut.conj g⁻¹) = MulAut.conj ((e g)⁻¹) := by
      ext y
      obtain ⟨z, rfl⟩ := e.surjective y
      simp [MulAut.congr_apply]
    calc MulAut.conj (eps ⟨_, hb⟩)
        = MulAut.congr e (ggGamma X hN ⟨_, hb⟩) := ((hspec' _).2).symm
      _ = MulAut.congr e (MulAut.conj g * ggGamma X hN b * MulAut.conj g⁻¹) := by rw [hgg]
      _ = MulAut.conj (e g) * MulAut.conj (eps b) * MulAut.conj ((e g)⁻¹) := by
            rw [map_mul, map_mul, hconj, (hspec' b).2, hconj']
      _ = MulAut.conj (e g * eps b * (e g)⁻¹) := by
            simp only [map_mul, map_inv]
  have heE : ∀ z : ↥X, e z ∈ E → (z : G) ∈ Bs := by
    intro z hz
    obtain ⟨b, hb⟩ := honto (e z) hz
    have hz' : z = e.symm (eps b) := by
      rw [hb]
      exact (e.symm_apply_apply z).symm
    rw [hz']
    exact hmem b
  have hconj_mem : ∀ (h : ↥X), e h ∈ Subgroup.normalizer (E : Set (adjointGroup .E7 K)) →
      ∀ b : ↥Bs, (h : G) * (b : G) * (h : G)⁻¹ ∈ Bs := by
    intro h hhE b
    have hxbX : ((e.symm (eps b) : ↥X) : G) ∈ X := (e.symm (eps b)).2
    have hhxbX : (h : G) * ((e.symm (eps b) : ↥X) : G) * (h : G)⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem h.2 hxbX) (X.inv_mem h.2)
    have hhxbE : e (⟨(h : G) * ((e.symm (eps b) : ↥X) : G) * (h : G)⁻¹, hhxbX⟩ : ↥X) ∈ E := by
      have h1 : (⟨(h : G) * ((e.symm (eps b) : ↥X) : G) * (h : G)⁻¹, hhxbX⟩ : ↥X) =
          h * e.symm (eps b) * h⁻¹ := Subtype.ext rfl
      rw [h1, map_mul, map_mul, map_inv, e.apply_symm_apply]
      exact ((Subgroup.mem_normalizer_iff.mp hhE) (eps b)).mp ((hspec' b).1)
    have hhxbBs : (h : G) * ((e.symm (eps b) : ↥X) : G) * (h : G)⁻¹ ∈ Bs :=
      heE ⟨_, hhxbX⟩ hhxbE
    have hcC : ((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G) ∈
        Subgroup.centralizer (X : Set G) :=
      mem_centralizer_of_conj_action (hact b)
    have hcBs : ((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G) ∈ Bs :=
      Bs.mul_mem (Bs.inv_mem (hmem b)) b.2
    have hfinal : (h : G) * (b : G) * (h : G)⁻¹ =
        ((h : G) * ((e.symm (eps b) : ↥X) : G) * (h : G)⁻¹) *
          (((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G)) := by
      set c : G := ((e.symm (eps b) : ↥X) : G)⁻¹ * (b : G) with hc
      have hbEq : (b : G) = ((e.symm (eps b) : ↥X) : G) * c := by rw [hc]; group
      have hcComm : (h : G) * c = c * (h : G) := by
        rw [hc]
        exact Subgroup.mem_centralizer_iff.mp hcC (h : G) h.2
      rw [hbEq]
      have hch : (h : G) * c * (h : G)⁻¹ = c := by rw [hcComm]; group
      calc (h : G) * (((e.symm (eps b) : ↥X) : G) * c) * (h : G)⁻¹
          = ((h : G) * ((e.symm (eps b) : ↥X) : G) * (h : G)⁻¹) * ((h : G) * c * (h : G)⁻¹) := by
              group
        _ = ((h : G) * ((e.symm (eps b) : ↥X) : G) * (h : G)⁻¹) * c := by rw [hch]
    rw [hfinal]
    exact Bs.mul_mem hhxbBs hcBs
  have hnorm1 : ∀ g : ↥X, e g ∈ Subgroup.normalizer (E : Set (adjointGroup .E7 K)) →
      (g : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hconj_mem g hg ⟨y, hy⟩
    · intro hy
      have hg' : e (g⁻¹) ∈ Subgroup.normalizer (E : Set (adjointGroup .E7 K)) := by
        rw [map_inv]
        exact (Subgroup.normalizer (E : Set (adjointGroup .E7 K))).inv_mem hg
      have h1 := hconj_mem g⁻¹ hg' ⟨(g : G) * y * (g : G)⁻¹, hy⟩
      have h2 : ((g⁻¹ : ↥X) : G) = (g : G)⁻¹ := rfl
      rw [h2] at h1
      have h3 : (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * ((g : G)⁻¹)⁻¹ = y := by group
      rwa [h3] at h1
  have hfwd : ∀ (h : ↥X), (h : G) ∈ Subgroup.normalizer (Bs : Set G) →
      ∀ c ∈ E, e h * c * (e h)⁻¹ ∈ E := by
    intro h hh c hc
    obtain ⟨b, hb⟩ := honto c hc
    have hbBs : (h : G) * (b : G) * (h : G)⁻¹ ∈ Bs :=
      ((Subgroup.mem_normalizer_iff.mp hh) (b : G)).mp b.2
    rw [← hb, ← hequiv h b hbBs]
    exact (hspec' ⟨_, hbBs⟩).1
  have hnorm2 : ∀ g : ↥X, (g : G) ∈ Subgroup.normalizer (Bs : Set G) →
      e g ∈ Subgroup.normalizer (E : Set (adjointGroup .E7 K)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact hfwd g hg c hc
    · intro hc
      have hg' : ((g⁻¹ : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G) := by
        have := (Subgroup.normalizer (Bs : Set G)).inv_mem hg
        simpa using this
      have h1 := hfwd g⁻¹ hg' ((e g) * c * (e g)⁻¹) hc
      rw [show e (g⁻¹) = (e g)⁻¹ from map_inv e g] at h1
      have h2 : (e g)⁻¹ * ((e g) * c * (e g)⁻¹) * ((e g)⁻¹)⁻¹ = c := by group
      rwa [h2] at h1
  exact ⟨eps, (fun b => (hspec' b).2), (fun b => (hspec' b).1), honto, hker, hinner,
    hmem, hnorm1, hnorm2, hequiv⟩

theorem e7Levi_datum
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hZ : Subgroup.center ↥X = ⊥)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : ↥X ≃* adjointGroup .E7 K) {E : Subgroup (adjointGroup .E7 K)}
    (hA : (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)))
    (ε : ↥Bs →* adjointGroup .E7 K)
    (hεE : ∀ b, ε b ∈ E) (hεsurj : ∀ c ∈ E, ∃ b, ε b = c)
    (hεker : ∀ b, ε b = 1 ↔ (b : G) ∈ Subgroup.centralizer (X : Set G))
    (hεX : ∀ (b : ↥Bs) (hb : (b : G) ∈ X), ε b = e ⟨b, hb⟩)
    (hεBs : ∀ b, ((e.symm (ε b) : ↥X) : G) ∈ Bs)
    (ι₀ : Multiplicative (Fin Tag.E7.rank → ZMod p) →* adjointGroup .E7 K)
    (hι₀ : Function.Injective ι₀) (hrange : ι₀.range = E)
    (n : Fin Tag.E7.rank → adjointGroup .E7 K)
    (hact : ∀ k s, n k * ι₀ (Multiplicative.ofAdd s) * (n k)⁻¹ =
      ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p (simple .E7 k) s)))
    {m : ℕ} (wt : GGTorusTorWit m 7 (adjointGroup .E7 K)
      (E.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))))
    (hwn : ∀ k, wt.n k = n k) (hw : wt.Holds CartanMatrix.E₇ CoxeterMatrix.E₇) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Fin 7 → MulAut ↥Bs) (h : Fin 7 → V) (α : Fin 7 → Module.Dual (ZMod p) V)
      (f : CoxeterMatrix.E₇.Group ≃* ↥(ggAutomizer X Bs))
      (κ : WeylGroup .E7 ≃* CoxeterMatrix.E₇.Group),
      (∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = ((CartanMatrix.E₇ i j : ℤ) : ZMod p)) ∧
      (∀ i, (f (CoxeterMatrix.E₇.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (∀ i, κ (simple .E7 i) = CoxeterMatrix.E₇.simple i) ∧
      (∀ (b : ↥Bs) (s : Fin Tag.E7.rank → ZMod p), ι₀ (Multiplicative.ofAdd s) = ε b →
        ∀ k, α k (ι (Additive.ofMul b)) = ExcFrames.frameCoord .E7 p s k) ∧
      (∀ k, ∃ b : ↥Bs, ι (Additive.ofMul b) = h k ∧ (b : G) ∈ X ∧
        ε b = ι₀ (Multiplicative.ofAdd (Pi.single k 1))) ∧
      ∀ (g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) (v : WeylGroup .E7),
        (∀ s, e ⟨g, g.2.1⟩ * ι₀ (Multiplicative.ofAdd s) * (e ⟨g, g.2.1⟩)⁻¹ =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p v s))) →
        ggTDρB X Bs g = (f (κ v) : MulAut ↥Bs) := by
  classical
  have hEA : CFSG.IsElementaryAbelian p ↥Bs := hBs.isElementaryAbelian
  have hA' : (E.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))).map
        (MulAut.congr e.symm).toMonoidHom = (ggGamma X hN).range := by
    rw [← hA, Subgroup.map_map]
    have hcomp : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
        MonoidHom.id (MulAut ↥X) := by
      ext a x
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hcomp, Subgroup.map_id]
  let w'' : GGTorusTorWit m 7 ↥X
      ((E.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))).map
        (MulAut.congr e.symm).toMonoidHom) := wt.transport e.symm
  have hw'' : w''.Holds CartanMatrix.E₇ CoxeterMatrix.E₇ := wt.holds_transport e.symm hw
  let w' : GGTorusTorWit m 7 ↥X ((ggGamma X hN).range) := hA' ▸ w''
  have hw' : w'.Holds CartanMatrix.E₇ CoxeterMatrix.E₇ := holds_of_eq_subgroup hA'.symm w'' hw''
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
  have hex : ∀ k : Fin Tag.E7.rank, ∃ b : ↥Bs,
      ε b = ι₀ (Multiplicative.ofAdd (Pi.single k 1)) := by
    intro k
    exact hεsurj _ (by rw [← hrange]; exact ⟨_, rfl⟩)
  let b0 : Fin Tag.E7.rank → ↥Bs := fun k => Classical.choose (hex k)
  have hb0 : ∀ k, ε (b0 k) = ι₀ (Multiplicative.ofAdd (Pi.single k 1)) :=
    fun k => Classical.choose_spec (hex k)
  let bk : Fin Tag.E7.rank → ↥Bs := fun k =>
    ⟨((e.symm (ε (b0 k)) : ↥X) : G), hεBs (b0 k)⟩
  have hbkX : ∀ k, (bk k : G) ∈ X := fun k => (e.symm (ε (b0 k))).2
  have hbk_eps : ∀ k, ε (bk k) = ι₀ (Multiplicative.ofAdd (Pi.single k 1)) := by
    intro k
    have hcoe : (⟨bk k, hbkX k⟩ : ↥X) = e.symm (ε (b0 k)) := Subtype.ext rfl
    rw [hεX (bk k) (hbkX k), hcoe, MulEquiv.apply_symm_apply, hb0 k]
  have hexc : ∀ b : ↥Bs, ∃ s : Fin Tag.E7.rank → ZMod p,
      ι₀ (Multiplicative.ofAdd s) = ε b := by
    intro b
    have h : ε b ∈ E := hεE b
    rw [← hrange] at h
    exact h
  let coord : ↥Bs → (Fin Tag.E7.rank → ZMod p) := fun b => Classical.choose (hexc b)
  have hcoord : ∀ b, ι₀ (Multiplicative.ofAdd (coord b)) = ε b :=
    fun b => Classical.choose_spec (hexc b)
  have hofAdd_inj : ∀ {s t : Fin Tag.E7.rank → ZMod p},
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
  let coordA : Additive ↥Bs →+ (Fin Tag.E7.rank → ZMod p) :=
    AddMonoidHom.mk' (fun v => coord (Additive.toMul v)) (fun v v' => hcoord_mul _ _)
  let coordL : Additive ↥Bs →ₗ[ZMod p] (Fin Tag.E7.rank → ZMod p) := coordA.toZModLinearMap p
  have hcoordL_apply : ∀ v, coordL v = coord (Additive.toMul v) := fun v => rfl
  have hcoordL : ∀ v, ι₀ (Multiplicative.ofAdd (coordL v)) = ε (Additive.toMul v) :=
    fun v => hcoord (Additive.toMul v)
  have hcoordL_bk : ∀ k, coordL (Additive.ofMul (bk k)) = Pi.single k 1 := by
    intro k
    rw [hcoordL_apply, toMul_ofMul]
    exact hcoord_bk k
  let frameRow (k : Fin Tag.E7.rank) : (Fin Tag.E7.rank → ZMod p) →+ ZMod p :=
    AddMonoidHom.mk' (fun s => ExcFrames.frameCoord .E7 p s k) (fun s t => by
      rw [ExcFrames.frameCoord_add]
      rfl)
  let α : Fin Tag.E7.rank → Module.Dual (ZMod p) (Additive ↥Bs) := fun k =>
    ((frameRow k).comp coordA).toZModLinearMap p
  have hα : ∀ (k : Fin Tag.E7.rank) (v : Additive ↥Bs),
      α k v = ExcFrames.frameCoord .E7 p (coord (Additive.toMul v)) k := fun k v => rfl
  let φ : Fin Tag.E7.rank → MulAut ↥Bs := fun k => ggTDρB X Bs (ggTDnH w' hnk k)
  let hh : Fin Tag.E7.rank → Additive ↥Bs := fun k => Additive.ofMul (bk k)
  have happ : ∀ (i : Fin Tag.E7.rank) (b' : ↥Bs), ((φ i b' : ↥Bs) : G) =
      ((e.symm (n i) : ↥X) : G) * b' * (((e.symm (n i) : ↥X) : G))⁻¹ := by
    intro i b'
    have h1 : ((ggTDnH w' hnk i : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) : G) =
        ((e.symm (n i) : ↥X) : G) := by
      simp only [ggTDnH]
      rw [hwn' i]
    show ((ggTDρB X Bs (ggTDnH w' hnk i) b' : ↥Bs) : G) = _
    rw [ggTDρB_apply, h1]
  have hKlin : ∀ (i : Fin Tag.E7.rank) (b : ↥Bs),
      φ i b = b * (bk i ^ (ExcFrames.frameCoord .E7 p (coord b) i).val)⁻¹ := by
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
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p (simple .E7 i) (coord b))) := by
      rw [hεX (φ i x) hφxX, hxe, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
        ← hεX x hxX, hxeps, ← hcoord b]
      exact hact i (coord b)
    have hexp : ι₀ (Multiplicative.ofAdd (Pi.single i 1)) ^
          (ExcFrames.frameCoord .E7 p (coord b) i).val =
        ι₀ (Multiplicative.ofAdd ((ExcFrames.frameCoord .E7 p (coord b) i).val •
          Pi.single i 1)) := by
      rw [ofAdd_nsmul, map_pow]
    have hεy : ε (x * (bk i ^ (ExcFrames.frameCoord .E7 p (coord b) i).val)⁻¹) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p (simple .E7 i) (coord b))) := by
      rw [map_mul, map_inv, map_pow, hxeps, hbk_eps, ← hcoord b, hexp,
        ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val,
        torusAct_simple_E7 i (coord b), sub_eq_add_neg, ofAdd_add, ofAdd_neg, map_mul, map_inv]
    have hφx : φ i x = x * (bk i ^ (ExcFrames.frameCoord .E7 p (coord b) i).val)⁻¹ :=
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
      _ = (b * x⁻¹) * (x * (bk i ^ (ExcFrames.frameCoord .E7 p (coord b) i).val)⁻¹) := by
            rw [hφx]
      _ = b * (bk i ^ (ExcFrames.frameCoord .E7 p (coord b) i).val)⁻¹ := by group
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
    have hsm : (ExcFrames.frameCoord .E7 p (coord b) i) • (Additive.ofMul (bk i) : Additive ↥Bs) =
        Additive.ofMul (bk i ^ (ExcFrames.frameCoord .E7 p (coord b) i).val) := by
      rw [ofMul_pow, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    rw [hsm, ofMul_mul, ofMul_inv]
    abel
  have hpair : ∀ i j, α i (hh j) = ((CartanMatrix.E₇ i j : ℤ) : ZMod p) := by
    intro i j
    have h1 : coord (Additive.toMul (Additive.ofMul (bk j))) = Pi.single j 1 := by
      rw [toMul_ofMul]
      exact hcoord_bk j
    dsimp only [hh]
    rw [hα i (Additive.ofMul (bk j)), toMul_ofMul, h1, frameCoord_single]
  have hdiag : ∀ i : Fin Tag.E7.rank, ((CartanMatrix.E₇ i i : ℤ) : ZMod p) = 2 := by
    intro i
    have h : CartanMatrix.E₇ i i = 2 := by fin_cases i <;> rfl
    rw [h]
    norm_num
  have hrefl : ∀ i, GGIsReflection p (φ i) := by
    intro i
    have hfx : α i (hh i) = 2 := (hpair i i).trans (hdiag i)
    have hL : ggLin (p := p) (AddEquiv.refl (Additive ↥Bs)) (φ i) = Module.reflection hfx :=
      ggLin_eq_reflection _ hfx (fun v => hlin i v)
    exact ggIsReflection_of_eq_reflection hp2 _ hfx hL
  obtain ⟨κ, hκ, hκcoord⟩ :=
    ggTBJE7Levi_weylLift (p := p) (AddEquiv.refl (Additive ↥Bs)) hlin hpair hf
  have hframe : ∀ (b : ↥Bs) (s : Fin Tag.E7.rank → ZMod p),
      ι₀ (Multiplicative.ofAdd s) = ε b → ∀ k,
      α k (AddEquiv.refl (Additive ↥Bs) (Additive.ofMul b)) = ExcFrames.frameCoord .E7 p s k := by
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
  have haut : ∀ (g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) (v : WeylGroup .E7),
      (∀ s, e ⟨g, g.2.1⟩ * ι₀ (Multiplicative.ofAdd s) * (e ⟨g, g.2.1⟩)⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p v s))) →
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
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p v (coord b))) := by
      have hxe : (⟨ggTDρB X Bs g x, hLxX⟩ : ↥X) =
          (⟨(g : G), g.2.1⟩ : ↥X) * (⟨x, hxX⟩ : ↥X) * (⟨(g : G), g.2.1⟩ : ↥X)⁻¹ := by
        apply Subtype.ext
        rw [ggTDρB_apply]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hεX _ hLxX, hxe, map_mul, map_mul, map_inv, ← hεX x hxX, hxeps, ← hcoord b]
      exact hv (coord b)
    have hεR : ε ((f (κ v) : MulAut ↥Bs) x) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p v (coord b))) := by
      have hsumx : Additive.ofMul x =
          ∑ j, ((TableBExc.liftMod .E7 p (coord b)) j : ZMod p) • hh j := by
        have hcx : coordL (Additive.ofMul x) =
            fun j => ((TableBExc.liftMod .E7 p (coord b)) j : ZMod p) := by
          rw [hcoordL_apply, toMul_ofMul, hcoords]
          funext j
          simp [TableBExc.liftMod]
        exact ofMul_eq_sum_of_coord hZ ε hεker coordL hcoordL bk hbkX hcoordL_bk hxX
          (fun j => ((TableBExc.liftMod .E7 p (coord b)) j : ZMod p)) hcx
      have hval : Additive.ofMul ((f (κ v) : MulAut ↥Bs) x) =
          ∑ j, ((v • TableBExc.liftMod .E7 p (coord b)) j : ZMod p) • hh j := by
        rw [show Additive.ofMul ((f (κ v) : MulAut ↥Bs) x) =
            AddEquiv.refl (Additive ↥Bs) (Additive.ofMul ((f (κ v) : MulAut ↥Bs) x)) from rfl]
        rw [← ggLin_apply_ofMul (p := p) (AddEquiv.refl (Additive ↥Bs))
          (f (κ v) : MulAut ↥Bs) x, hsumx]
        exact (hκcoord v (TableBExc.liftMod .E7 p (coord b)) (Additive.ofMul x)).1
      have h := congrArg (fun a : Additive ↥Bs => ε (Additive.toMul a)) hval
      rw [eps_sum ε coordL hcoordL bk hcoordL_bk
        (fun j => ((v • TableBExc.liftMod .E7 p (coord b)) j : ZMod p))] at h
      have hred : (fun j => ((v • TableBExc.liftMod .E7 p (coord b)) j : ZMod p)) =
          TableBExc.torusAct .E7 p v (coord b) := rfl
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
