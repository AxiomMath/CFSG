module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinCells
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoPairing
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBMaxToPair
public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteQTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal Module

section Span

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_ggInduced_top_of_le {Bs X : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    (hA : A ≤ ggAutomizer X Bs) {φ : MulAut ↥Bs} (hφ : φ ∈ A) : φ ∈ ggInduced ⊤ Bs := by
  obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp (hA hφ)
  exact ⟨g, Subgroup.mem_top g, hgN, hg⟩

omit [Finite G] in
private theorem mem_ggInduced_top_of_mem_sup {Bs L K : Subgroup G} {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs) : φ ∈ ggInduced ⊤ Bs :=
  mem_ggInduced_top_of_le
    (sup_le (ggAutomizer_mono Bs (le_sup_left : L ≤ L ⊔ K)) (ggAutomizer_mono Bs le_sup_right)) hφ

omit [Finite G] in
private def ggMovesInto (Bs X : Subgroup G) : Subgroup (MulAut ↥Bs) where
  carrier := {φ | ∀ b : ↥Bs, ((φ b : ↥Bs) : G) * (b : G)⁻¹ ∈ X}
  one_mem' := fun b => by simp
  mul_mem' := by
    intro φ ψ hφ hψ b
    have h : ((((φ * ψ) b : ↥Bs)) : G) * (b : G)⁻¹ =
        (((φ (ψ b) : ↥Bs) : G) * ((ψ b : ↥Bs) : G)⁻¹) * (((ψ b : ↥Bs) : G) * (b : G)⁻¹) := by
      rw [MulAut.mul_apply]; group
    rw [h]
    exact X.mul_mem (hφ (ψ b)) (hψ b)
  inv_mem' := by
    intro φ hφ b
    have h : (((φ⁻¹ b : ↥Bs)) : G) * (b : G)⁻¹ =
        (((φ (φ⁻¹ b) : ↥Bs) : G) * ((φ⁻¹ b : ↥Bs) : G)⁻¹)⁻¹ := by
      rw [MulAut.apply_inv_self]; group
    rw [h]
    exact X.inv_mem (hφ (φ⁻¹ b))

omit [Finite G] in
private theorem ggAutomizer_le_ggMovesInto {Bs Y X : Subgroup G}
    (hY : Bs ≤ Subgroup.normalizer (Y : Set G)) (hYX : Y ≤ X) :
    ggAutomizer Y Bs ≤ ggMovesInto Bs X := by
  intro ψ hψ b
  obtain ⟨g, hgY, -, hg⟩ := mem_ggAutomizer_iff.mp hψ
  have hmem : (b : G) * g⁻¹ * (b : G)⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp (hY b.2) g⁻¹).mp (Y.inv_mem hgY)
  have heq : ((ψ b : ↥Bs) : G) * (b : G)⁻¹ = g * ((b : G) * g⁻¹ * (b : G)⁻¹) := by
    rw [hg b]; group
  rw [heq]
  exact hYX (Y.mul_mem hgY hmem)

omit [Finite G] in
theorem mul_inv_mem_sup_of_mem_sup_ggAutomizer {Bs L K : Subgroup G}
    (hL : Bs ≤ Subgroup.normalizer (L : Set G)) (hK : Bs ≤ Subgroup.normalizer (K : Set G))
    {ψ : MulAut ↥Bs} (hψ : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs) (b : ↥Bs) :
    ((ψ b : ↥Bs) : G) * (b : G)⁻¹ ∈ L ⊔ K :=
  sup_le (ggAutomizer_le_ggMovesInto hL le_sup_left) (ggAutomizer_le_ggMovesInto hK le_sup_right)
    hψ b

omit [Finite G] in
theorem mul_inv_mem_of_mem_ggAutomizerJoin {Bs L X : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hL : Bs ≤ Subgroup.normalizer (L : Set G)) (hLX : L ≤ X)
    (h𝒦 : ∀ K ∈ 𝒦, Bs ≤ Subgroup.normalizer (K : Set G) ∧ K ≤ X)
    {ψ : MulAut ↥Bs} (hψ : ψ ∈ ggAutomizerJoin L Bs 𝒦) (b : ↥Bs) :
    ((ψ b : ↥Bs) : G) * (b : G)⁻¹ ∈ X :=
  sup_le (ggAutomizer_le_ggMovesInto hL hLX)
    (iSup₂_le fun K hK => ggAutomizer_le_ggMovesInto (h𝒦 K hK).1 (h𝒦 K hK).2) hψ b

omit [Finite G] in
theorem coroot_mem_of_reflection {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs X : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V) {φ : MulAut ↥Bs}
    (hφ : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) * (b : G)⁻¹ ∈ X) {k : V}
    {a : Module.Dual (ZMod p) V} (h2 : a k = 2) (hrefl : ggLin (p := p) ιV φ = reflection h2) :
    ((Additive.toMul (ιV.symm k) : ↥Bs) : G) ∈ X := by
  have hane : a ≠ 0 := by
    intro h0
    rw [h0] at h2
    exact zmod_two_ne_zero hp2 h2.symm
  have hmem1 : (1 : ZMod p) ∈ LinearMap.range a := by
    rw [Module.Dual.range_eq_top_of_ne_zero hane]
    exact Submodule.mem_top
  obtain ⟨v, hv⟩ := hmem1
  let b : ↥Bs := Additive.toMul (ιV.symm v)
  have hbvec : ιV (Additive.ofMul b) = v := by
    simp [b]
  have hlin : ggLin (p := p) ιV φ v = ιV (Additive.ofMul (φ b)) := by
    rw [← hbvec, ggLin_apply_ofMul]
  have hk : k = ιV (Additive.ofMul (b * (φ b)⁻¹)) := by
    have hmove : k = v - ggLin (p := p) ιV φ v := by
      rw [hrefl, reflection_apply, hv, one_smul]
      abel
    rw [hmove, hlin, ← hbvec, ← map_sub]
    congr 1
    rw [ofMul_mul, ofMul_inv, sub_eq_add_neg]
  have hmem : ((b * (φ b)⁻¹ : ↥Bs) : G) ∈ X := by
    have hcoe : ((b * (φ b)⁻¹ : ↥Bs) : G) = (((φ b : ↥Bs) : G) * (b : G)⁻¹)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hcoe]
    exact X.inv_mem (hφ b)
  rw [hk]
  simpa using hmem

private theorem exists_card_eq_pow {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) : ∃ k : ℕ, Nat.card Bs = p ^ k := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨V, hVadd, hVmod, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  have : Finite V := Finite.of_equiv _ ιV.toEquiv
  let : Fintype V := Fintype.ofFinite V
  exact ⟨finrank (ZMod p) V, by rw [card_eq_of_ggLin ιV, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]⟩

omit [Finite G] in
theorem cartan_rank_le_finrank_span {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι]
    [DecidableEq ι] {C : Matrix ι ι ℤ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (h : ι → V) (α : ι → Module.Dual (ZMod p) V)
    (hP : ∀ i j, α i (h j) = (C i j : ZMod p)) :
    (C.map (Int.castRingHom (ZMod p))).rank ≤
      finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) := by
  have hcomp : (C.map (Int.castRingHom (ZMod p))).mulVecLin =
      (LinearMap.pi α).comp (Fintype.linearCombination (ZMod p) h) := by
    refine LinearMap.ext fun c => funext fun i => ?_
    simp only [Matrix.mulVecLin_apply, LinearMap.comp_apply, Fintype.linearCombination_apply,
      LinearMap.pi_apply, map_sum, map_smul, hP, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.map_apply, eq_intCast]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [Matrix.rank, hcomp, LinearMap.range_comp, Fintype.range_linearCombination]
  exact Submodule.finrank_map_le _ _

theorem le_of_cartan_pairing {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) {A : Subgroup (MulAut ↥Bs)}
    (hstep : ∀ ψ ∈ A, ∀ b : ↥Bs, ((ψ b : ↥Bs) : G) * (b : G)⁻¹ ∈ X)
    {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hpair : ∀ {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V),
      ∃ (e : M.Group ≃* ↥A) (h : ι → V) (α : ι → Module.Dual (ZMod p) V)
        (hα : ∀ i, α i (h i) = 2),
        (∀ i, ggLin (p := p) ιV ((e (M.simple i) : ↥A) : MulAut ↥Bs) = reflection (hα i)) ∧
        ∀ i j, α i (h j) = (C i j : ZMod p))
    (hcard : Nat.card Bs ≤ p ^ (C.map (Int.castRingHom (ZMod p))).rank) :
    Bs ≤ X := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨V, hVadd, hVmod, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  have : Finite V := Finite.of_equiv _ ιV.toEquiv
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨e, h, α, hα, hrefl, hP⟩ := hpair ιV
  let U : AddSubgroup V :=
    { carrier := {v | ((Additive.toMul (ιV.symm v) : ↥Bs) : G) ∈ X}
      zero_mem' := by
        show ((Additive.toMul (ιV.symm (0 : V)) : ↥Bs) : G) ∈ X
        rw [map_zero, toMul_zero]
        exact X.one_mem
      add_mem' := by
        intro v w hv hw
        show ((Additive.toMul (ιV.symm (v + w)) : ↥Bs) : G) ∈ X
        rw [map_add, toMul_add, Subgroup.coe_mul]
        exact X.mul_mem hv hw
      neg_mem' := by
        intro v hv
        show ((Additive.toMul (ιV.symm (-v)) : ↥Bs) : G) ∈ X
        rw [map_neg, toMul_neg, Subgroup.coe_inv]
        exact X.inv_mem hv }
  have hhU : ∀ i, h i ∈ U := fun i =>
    coroot_mem_of_reflection hp2 ιV (hstep _ (e (M.simple i)).2) (hα i) (hrefl i)
  rw [card_eq_of_ggLin ιV, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p),
    ZMod.card] at hcard
  have hfr := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard
  have hspan : Submodule.span (ZMod p) (Set.range h) = ⊤ := by
    have h1 := cartan_rank_le_finrank_span h α hP
    have h2 := Submodule.finrank_le (Submodule.span (ZMod p) (Set.range h))
    exact Submodule.eq_top_of_finrank_eq (by omega)
  have hspan_le : Submodule.span (ZMod p) (Set.range h) ≤
      AddSubgroup.toZModSubmodule (n := p) U := by
    rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    exact (AddSubgroup.mem_toZModSubmodule (n := p) (S := U)).mpr (hhU i)
  have htop : AddSubgroup.toZModSubmodule (n := p) U = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact hspan_le
  intro b hb
  have hbv : ιV (Additive.ofMul (⟨b, hb⟩ : ↥Bs)) ∈ AddSubgroup.toZModSubmodule (n := p) U := by
    rw [htop]
    exact Submodule.mem_top
  have hbU := (AddSubgroup.mem_toZModSubmodule (n := p) (S := U)).mp hbv
  simpa [U] using hbU

theorem rank_eq_card_of_isUnit_det {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι]
    [DecidableEq ι] {C : Matrix ι ι ℤ} (hdet : IsUnit (C.det : ZMod p)) :
    (C.map (Int.castRingHom (ZMod p))).rank = Fintype.card ι := by
  have hunit : IsUnit (C.map (Int.castRingHom (ZMod p))) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]
    exact hdet
  exact Matrix.rank_of_isUnit _ hunit

theorem card_le_pow_rank_of_isUnit_det {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    {C : Matrix ι ι ℤ} (hdet : IsUnit (C.det : ZMod p)) (hW : GGWeylOfType p M A)
    (hfix : ∀ b : ↥Bs, (∀ ψ ∈ A, ψ b = b) → b = 1) :
    Nat.card Bs ≤ p ^ (C.map (Int.castRingHom (ZMod p))).rank := by
  rw [rank_eq_card_of_isUnit_det hdet]
  exact SpJoinRefl.card_le_pow_of_weylOfType hW hfix

theorem pow_rank_le_card_of_cartan_pairing {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) {ι : Type} [Fintype ι] [DecidableEq ι] {C : Matrix ι ι ℤ}
    (hpair : ∀ {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V),
      ∃ (h : ι → V) (α : ι → Module.Dual (ZMod p) V), ∀ i j, α i (h j) = (C i j : ZMod p)) :
    p ^ (C.map (Int.castRingHom (ZMod p))).rank ≤ Nat.card Bs := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨V, hVadd, hVmod, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  have : Finite V := Finite.of_equiv _ ιV.toEquiv
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨h, α, hP⟩ := hpair ιV
  rw [card_eq_of_ggLin ιV, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p),
    ZMod.card]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
    ((cartan_rank_le_finrank_span h α hP).trans (Submodule.finrank_le _))

theorem le_sup_of_weylOfType_of_isUnit_det {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs L K : Subgroup G} (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (hL : Bs ≤ Subgroup.normalizer (L : Set G)) (hK : Bs ≤ Subgroup.normalizer (K : Set G))
    {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) (hno6 : ∀ i j, M i j ≠ 6) (par : ι → ι) (root : ι) (depth : ι → ℕ)
    (hpar : ∀ i j, i ≠ j → (C i j ≠ 0 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) (hdet : IsUnit (C.det : ZMod p))
    (hW : GGWeylOfType p M (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hfix : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ψ b = b) → b = 1) :
    Bs ≤ L ⊔ K :=
  le_of_cartan_pairing hp2 hBs (fun _ hψ b => mul_inv_mem_sup_of_mem_sup_ggAutomizer hL hK hψ b)
    (fun ιV => SecFiveRootRefl.exists_cartan_pairing_of_weylOfType' (p := p) hp2 hNT hC hno6 par
      root depth hpar hdepth hW (fun _ hφ => mem_ggInduced_top_of_mem_sup hφ) ιV)
    (card_le_pow_rank_of_isUnit_det hdet hW hfix)

theorem le_sup_of_weylOfType_E₇ {Bs L K : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) (hL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hK : Bs ≤ Subgroup.normalizer (K : Set G))
    (hW : GGWeylOfType 3 CoxeterMatrix.E₇ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hfix : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ψ b = b) → b = 1) :
    Bs ≤ L ⊔ K := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_sup_of_weylOfType_of_isUnit_det (by norm_num) hBs hNT hL hK ggIntCartan_E₇
    (by intro i j; fin_cases i <;> fin_cases j <;> decide) ![0, 3, 0, 2, 3, 4, 5] 0 ![0, 3, 1, 2, 3, 4, 5] ?_ (by decide) ?_ hW hfix
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  · rw [CartanMatrix.E₇_det]
    exact isUnit_iff_ne_zero.mpr (by rw [Int.cast_ofNat]; exact h2)

theorem le_sup_of_weylOfType_E₈ {Bs L K : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) (hL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hK : Bs ≤ Subgroup.normalizer (K : Set G))
    (hW : GGWeylOfType 3 CoxeterMatrix.E₈ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hfix : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ψ b = b) → b = 1) :
    Bs ≤ L ⊔ K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_sup_of_weylOfType_of_isUnit_det (by norm_num) hBs hNT hL hK ggIntCartan_E₈
    (by intro i j; fin_cases i <;> fin_cases j <;> decide) ![0, 3, 0, 2, 3, 4, 5, 6] 0 ![0, 3, 1, 2, 3, 4, 5, 6] ?_ (by decide) ?_ hW hfix
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  · rw [CartanMatrix.E₈_det, Int.cast_one]
    exact isUnit_one

theorem le_sup_of_weylOfType_F₄ {Bs L K : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) (hL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hK : Bs ≤ Subgroup.normalizer (K : Set G))
    (hW : GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hfix : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ψ b = b) → b = 1) :
    Bs ≤ L ⊔ K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_sup_of_weylOfType_of_isUnit_det (by norm_num) hBs hNT hL hK ggIntCartan_F₄
    (by intro i j; fin_cases i <;> fin_cases j <;> decide) ![0, 0, 1, 2] 0 ![0, 1, 2, 3] ?_ (by decide) ?_ hW hfix
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  · rw [CartanMatrix.F₄_det, Int.cast_one]
    exact isUnit_one

end Span

section Cells

@[expose] def GGSecFiveQTwoInternalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSecFivePhanARow p B Bs x L D J →
      GGSecFiveQTwoCell p B Bs x L D J →
        p = 3 ∧ x ∈ ggG0 p B x L D J ∧ x ^ 3 = 1

@[expose] def GGSecFiveQTwoInternalE6Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region 3 B Bs x L D J → ¬ GGSecFivePhanARow 3 B Bs x L D J →
      GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
      ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
        GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
          Nat.card Bs = 3 ^ 6 → x ∈ L ⊔ K

theorem ggSecFiveQTwoInternalInput_of_e6
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hE6 : GGSecFiveQTwoInternalE6Input) :
    GGSecFiveQTwoInternalInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hT1 hPhA hQ
  have hR := hcfg.1
  have hp : p = 3 := FrameRoute.p_eq_three_of_qTwo hR.1 hQ.1
  subst hp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxB : x ∈ B := hR.1.1.2.2.2.2.2.2.1.2.1
  have hx3 : x ^ 3 = 1 := (hR.1.1.2.2.2.2.2.2.1.1 : LargeEvenIsBmax 3 B).1.2 x hxB
  refine ⟨rfl, ?_, hx3⟩
  have hxBs : x ∈ Bs := hR.1.2.1.1 hxB
  have hBs : IsElemAbelian 3 Bs := hR.1.2.1.2.1
  have hNT : GGNoTransvection 3 Bs := hR.2.2.2.1
  have hLn : Bs ≤ Subgroup.normalizer (L : Set G) := GGDichotomy.le_normalizer_of_innerDiagOn hR.2.2.1.1
  have hpair : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      (GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∨
        GGWeylOfType 3 CoxeterMatrix.E₇ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∨
        GGWeylOfType 3 CoxeterMatrix.E₈ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∨
        GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) →
      x ∈ L ⊔ K := by
    intro y K hN hW
    have hKn : Bs ≤ Subgroup.normalizer (K : Set G) :=
      GGDichotomy.le_normalizer_of_innerDiagOn (hR.2.2.1.2 y K hN)
    have hfix : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ψ b = b) → b = 1 :=
      fun b hb => hR.eq_one_of_fix_pair hTBF hWI hcfg.2.1 hN b hb
    rcases hW with hW | hW | hW | hW
    · have h5 := E6QTwo.three_pow_five_le_card hBs hNT
        (fun _ hφ => mem_ggInduced_top_of_mem_sup hφ) hW
      have h6 := SpJoinRefl.card_le_pow_of_weylOfType hW hfix
      rw [Fintype.card_fin] at h6
      obtain ⟨k, hk⟩ := exists_card_eq_pow hBs
      rw [hk] at h5 h6
      have hk5 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h5
      have hk6 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h6
      obtain rfl | rfl : k = 5 ∨ k = 6 := by omega
      · exact E6QTwo.le_sup_of_weylOfType_E6 hBs hNT hLn hKn hW hk hxBs
      · exact hE6 G B Bs x L D J 𝒦 hcfg hT1 hPhA hQ.1 y K hN hW hk
    · exact le_sup_of_weylOfType_E₇ hBs hNT hLn hKn hW hfix hxBs
    · exact le_sup_of_weylOfType_E₈ hBs hNT hLn hKn hW hfix hxBs
    · exact le_sup_of_weylOfType_F₄ hBs hNT hLn hKn hW hfix hxBs
  have hG0 : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K → L ⊔ K ≤ ggG0 3 B x L D J :=
    fun y K hN => sup_le (le_ggG0_left 3 B x L D J) (le_ggG0_of_ggNbr hN)
  rcases hQ.2 with ⟨y, K, hN, hW⟩ | ⟨y, K, hN, hW⟩ | ⟨y, K, hN, hW⟩ | ⟨y, K, hN, hW⟩
  · exact hG0 y K hN (hpair y K hN (Or.inl hW))
  · exact hG0 y K hN (hpair y K hN (Or.inr (Or.inl hW)))
  · exact hG0 y K hN (hpair y K hN (Or.inr (Or.inr (Or.inl hW))))
  · exact hG0 y K hN (hpair y K hN (Or.inr (Or.inr (Or.inr hW))))

@[expose] def GGSecFiveQTwoKnownSelectedInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
      ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGPresentsG0 (ggG0 3 B x L D J) (ggU t n f).D t n f ψ →
          x ∈ ggG0 3 B x L D J → x ^ 3 = 1 →
            ∃ (t' : StatedLieTag) (n' : ℕ) (ψ' : (ggU t' n' 1).K →* G),
              StatedLieAdmissible t' n' 2 1 ∧ 2 ≤ (ggU t' n' 1).D.rank ∧
                ψ'.ker ≤ Subgroup.center (ggU t' n' 1).K ∧ ψ'.range = L ∧
                ∃ (γ : Fin (ggU t n f).D.rank → ℤ) (δ : Fin (ggU t' n' 1).D.rank → ℤ)
                  (model : SelectedRoot.SelectedSL2Model (ggU t n f).D (GaloisField 2 1) γ)
                  (model' : SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ),
                  ∃ u₀ : (ggU t n f).K,
                    ((ψ.comp (MulAut.conj u₀).toMonoidHom).comp model.phi).range =
                      (ψ'.comp model'.phi).range

theorem ggSecFiveCompatQTwoCellResNInput_of_internal (hI : GGSecFiveQTwoInternalInput)
    (hK : GGSecFiveQTwoKnownSelectedInput) : GGSecFiveCompatQTwoCellResNInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hReg hrow t n f ψ hpres hQ
  obtain ⟨hp, hx, hx3⟩ := hI G p B Bs x L D J 𝒦 hcfg hReg hrow hQ
  subst p
  obtain ⟨t', n', ψ', hadm, hrk, hker, hrange, γ, δ, model, model', u₀, hS⟩ :=
    hK G B Bs x L D J hcfg.1.1 hQ.1 t n f ψ hpres hx hx3
  exact ggSecFiveCompat_of_selectedSL2 (K := L) hpres (Or.inl rfl) hadm hrk hker hrange
    model model' u₀ hS

end Cells

end CFSG.StandardType

end
