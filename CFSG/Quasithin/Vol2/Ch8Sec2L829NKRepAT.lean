module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKRepA
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKRepB
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKRepC
public import Mathlib.RingTheory.Coalgebra.CoassocSimps

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L829NK

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace CFSG.Quasithin.H.SL3Rep Matrix

section Basis

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W] [Module.Finite E W]

theorem nk_basis_of_span (ι : Fin 3 → W) (hspan : ⊤ ≤ Submodule.span E (Set.range ι))
    (h3 : 3 ≤ Module.finrank E W) : ∃ b : Module.Basis (Fin 3) E W, ⇑b = ι := by
  have hle : Module.finrank E W ≤ 3 := by
    calc Module.finrank E W = Module.finrank E (⊤ : Submodule E W) := (finrank_top E W).symm
      _ ≤ Module.finrank E (Submodule.span E (Set.range ι)) := Submodule.finrank_mono hspan
      _ ≤ Fintype.card (Fin 3) := finrank_range_le_card ι
      _ = 3 := Fintype.card_fin 3
  have hcard : Fintype.card (Fin 3) = Module.finrank E W := by
    rw [Fintype.card_fin]; omega
  exact ⟨basisOfTopLeSpanOfCardEqFinrank ι hspan hcard, coe_basisOfTopLeSpanOfCardEqFinrank _ _ _⟩

end Basis

section Natural

variable {E W : Type} [Field E] [Algebra (ZMod 2) E] [AddCommGroup W] [Module E W]
  [Module.Finite E W] [Module (ZMod 2) W] [IsScalarTower (ZMod 2) E W]

theorem nk_span_top {θ : GS →* (W ≃ₗ[E] W)}
    (hirr : ∀ W' : Submodule E W, (∀ g, ∀ w ∈ W', θ g w ∈ W') → W' = ⊥ ∨ W' = ⊤)
    (U : Submodule (ZMod 2) W) (hU : ∀ g, ∀ u ∈ U, θ g u ∈ U) (hUne : U ≠ ⊥) :
    Submodule.span E (U : Set W) = ⊤ := by
  have hinv : ∀ g, ∀ w ∈ Submodule.span E (U : Set W), θ g w ∈ Submodule.span E (U : Set W) := by
    intro g w hw
    induction hw using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hU g x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  rcases hirr _ hinv with h | h
  · exfalso
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
    have : u ∈ Submodule.span E (U : Set W) := Submodule.subset_span hu
    rw [h] at this
    exact hu0 ((Submodule.mem_bot E).mp this)
  · exact h

theorem nk_rep_of_natural {θ : GS →* (W ≃ₗ[E] W)} (h3 : 3 ≤ Module.finrank E W)
    (hirr : ∀ W' : Submodule E W, (∀ g, ∀ w ∈ W', θ g w ∈ W') → W' = ⊥ ∨ W' = ⊤)
    (U : Submodule (ZMod 2) W) (hU : ∀ g, ∀ u ∈ U, θ g u ∈ U) (hUne : U ≠ ⊥)
    (f : U ≃ₗ[ZMod 2] VS) (A : GS → Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hf : ∀ g (u : U), f ⟨θ g u, hU g u u.2⟩ = A g *ᵥ f u)
    (hdet : ∀ g, (A g).det = 1)
    (hsurj : ∀ M : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), ∃ g, A g = M) :
    ∃ b : Module.Basis (Fin 3) E W,
      (∀ g : GS, ∃ M : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        LinearMap.toMatrix b b (θ g : W →ₗ[E] W) =
          (M : Matrix (Fin 3) (Fin 3) (ZMod 2)).map (algebraMap (ZMod 2) E)) ∧
      (∀ M : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), ∃ g : GS,
        LinearMap.toMatrix b b (θ g : W →ₗ[E] W) =
          (M : Matrix (Fin 3) (Fin 3) (ZMod 2)).map (algebraMap (ZMod 2) E)) := by
  classical
  set ι : Fin 3 → W := fun j => ((f.symm (Pi.single j 1) : U) : W) with hι
  have hUι : ∀ x : U, (x : W) = ∑ j, (f x j) • ι j := by
    intro x
    have h1 : f x = ∑ j, (f x j) • (Pi.single j (1 : ZMod 2) : VS) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    have h2 : x = ∑ j, (f x j) • f.symm (Pi.single j 1) := by
      conv_lhs => rw [← f.symm_apply_apply x, h1]
      simp [map_sum, map_smul]
    conv_lhs => rw [h2]
    simp [hι]
  have hspan : ⊤ ≤ Submodule.span E (Set.range ι) := by
    rw [← nk_span_top hirr U hU hUne]
    apply Submodule.span_le.mpr
    intro x hx
    have := hUι ⟨x, hx⟩
    simp only at this
    rw [this]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← algebraMap_smul E (f ⟨x, hx⟩ j) (ι j)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨b, hb⟩ := nk_basis_of_span ι hspan h3
  have hθι : ∀ g j, θ g (ι j) = ∑ i, algebraMap (ZMod 2) E (A g i j) • ι i := by
    intro g j
    have hx := hUι ⟨θ g (ι j), hU g _ (f.symm (Pi.single j 1)).2⟩
    have hfx : f ⟨θ g (ι j), hU g _ (f.symm (Pi.single j 1)).2⟩ = fun i => A g i j := by
      have := hf g (f.symm (Pi.single j 1))
      rw [LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one] at this
      exact this
    simp only at hx
    rw [hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfx, algebraMap_smul]
  have hmat : ∀ g, LinearMap.toMatrix b b (θ g : W →ₗ[E] W) = (A g).map (algebraMap (ZMod 2) E) := by
    intro g
    ext i j
    rw [LinearMap.toMatrix_apply, hb]
    simp only [LinearEquiv.coe_coe, hθι, Matrix.map_apply]
    rw [← hb]
    exact congrFun (b.repr_sum_self (fun i => algebraMap (ZMod 2) E (A g i j))) i
  refine ⟨b, fun g => ⟨⟨A g, hdet g⟩, ?_⟩, fun M => ?_⟩
  · exact hmat g
  · obtain ⟨g, hg⟩ := hsurj M
    exact ⟨g, by rw [hmat g, hg]⟩

end Natural

section Facts

theorem nk_zmod2_unit_eq_one {x : ZMod 2} (hx : IsUnit x) : x = 1 := by
  have h : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases h x with h0 | h1
  · subst h0; exact absurd hx not_isUnit_zero
  · exact h1

theorem nk_det_toMatrix_eq_one (g : GS) :
    (LinearMap.toMatrix' (g : VS →ₗ[ZMod 2] VS)).det = 1 := by
  have h1 : LinearMap.toMatrix' (g : VS →ₗ[ZMod 2] VS) *
      LinearMap.toMatrix' (g.symm : VS →ₗ[ZMod 2] VS) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (g : VS →ₗ[ZMod 2] VS) ∘ₗ (g.symm : VS →ₗ[ZMod 2] VS) = LinearMap.id := by
      ext v; simp
    rw [this, LinearMap.toMatrix'_id]
  exact nk_zmod2_unit_eq_one (Matrix.isUnit_det_of_right_inverse h1)

theorem nk_toMatrix_iota (M : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    LinearMap.toMatrix' ((iota M : GS) : VS →ₗ[ZMod 2] VS) =
      (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  have : ((iota M : GS) : VS →ₗ[ZMod 2] VS) = Matrix.toLin' (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    LinearMap.ext fun v => by rw [LinearEquiv.coe_coe, iota_apply, Matrix.toLin'_apply]
  rw [this, LinearMap.toMatrix'_toLin']

theorem nk_apply_eq_mulVec (g : GS) (v : VS) :
    g v = (LinearMap.toMatrix' (g : VS →ₗ[ZMod 2] VS)) *ᵥ v := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

@[expose] noncomputable def dualCoord : Module.Dual (ZMod 2) VS ≃ₗ[ZMod 2] VS :=
  (Pi.basisFun (ZMod 2) (Fin 3)).dualBasis.equivFun

theorem dualCoord_apply (φ : Module.Dual (ZMod 2) VS) (i : Fin 3) :
    dualCoord φ i = φ (Pi.single i 1) := by
  simp [dualCoord, Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr]

theorem dualCoord_comp (g : GS) (φ : Module.Dual (ZMod 2) VS) :
    dualCoord (φ.comp (g.symm : VS →ₗ[ZMod 2] VS)) =
      (LinearMap.toMatrix' (g.symm : VS →ₗ[ZMod 2] VS))ᵀ *ᵥ dualCoord φ := by
  have hs : ∀ i : Fin 3, (fun j : Fin 3 => if i = j then (1 : ZMod 2) else 0) = Pi.single i 1 := by
    intro i; ext j; simp [Pi.single_apply, eq_comm]
  ext k
  rw [dualCoord_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, nk_apply_eq_mulVec,
    Matrix.mulVec_single_one, LinearMap.pi_apply_eq_sum_univ φ]
  simp [Matrix.mulVec, dotProduct, dualCoord_apply, hs, mul_comm]

end Facts

section Main

theorem nk_ttGS_orderOf : orderOf ttGS = 2 := by
  have hsq : ttSL * ttSL = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show (1 + Matrix.single 0 2 1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      (1 + Matrix.single 0 2 1) = 1
    decide +kernel
  have hne : ttSL ≠ 1 := by
    intro h
    have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) =>
      (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2) h
    revert this
    show ¬ ((1 + Matrix.single 0 2 1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2 =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2)
    decide +kernel
  have h2 : ttGS * ttGS = 1 := by
    rw [ttGS, ← map_mul, hsq, map_one]
  have hne' : ttGS ≠ 1 := fun h => hne (iota.injective (by rw [map_one]; exact h))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact h2) hne'

theorem nk_natCard_le {E W : Type} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [Finite W] (R : Submodule E W) (h : Module.finrank E R ≤ 1) : Nat.card R ≤ Nat.card E := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fintype R := Fintype.ofFinite R
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := E)
    (V := R)]
  calc Fintype.card E ^ Module.finrank E R ≤ Fintype.card E ^ 1 :=
        Nat.pow_le_pow_right Fintype.card_pos h
    _ = Fintype.card E := pow_one _

theorem nk_sl3_transvection_rep {E W : Type} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    (hE : Nat.card E = 2 ∨ Nat.card E = 4)
    [AddCommGroup W] [Module E W] [Module.Finite E W] [Module (ZMod 2) W]
    [IsScalarTower (ZMod 2) E W]
    (θ : GS →* (W ≃ₗ[E] W)) (hinj : Function.Injective θ)
    (hirr : ∀ W' : Submodule E W, (∀ g, ∀ w ∈ W', θ g w ∈ W') → W' = ⊥ ∨ W' = ⊤)
    (htv : ∀ g : GS, orderOf g = 2 →
      Module.finrank E (LinearMap.range ((θ g : W →ₗ[E] W) - LinearMap.id)) ≤ 1) :
    ∃ b : Module.Basis (Fin 3) E W,
      (∀ g : GS, ∃ M : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        LinearMap.toMatrix b b (θ g : W →ₗ[E] W) =
          (M : Matrix (Fin 3) (Fin 3) (ZMod 2)).map (algebraMap (ZMod 2) E)) ∧
      (∀ M : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), ∃ g : GS,
        LinearMap.toMatrix b b (θ g : W →ₗ[E] W) =
          (M : Matrix (Fin 3) (Fin 3) (ZMod 2)).map (algebraMap (ZMod 2) E)) := by
  classical
  haveI : Finite W := Module.finite_of_finite E
  have h3 := nk_three_le_finrank hE θ hinj
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := E) (by omega)
  let ρ : Representation (ZMod 2) GS W :=
    { toFun := fun g => ((θ g : W ≃ₗ[E] W) : W →ₗ[E] W).restrictScalars (ZMod 2)
      map_one' := by ext w; simp
      map_mul' := fun g h => by ext w; simp }
  have hρ : ∀ g w, ρ g w = θ g w := fun g w => rfl
  obtain ⟨U, hU, hUne, hcases⟩ := nk_exists_model_sub ρ
  have hUθ : ∀ g, ∀ u ∈ U, θ g u ∈ U := fun g u hu => hU g u hu
  rcases hcases with ⟨f, hf⟩ | ⟨f, hf⟩ | ⟨f, hf⟩ | ⟨f, hf⟩
  ·
    exfalso
    obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
    have hfix : ∀ g, θ g u₀ = u₀ := by
      intro g
      have h2 : (⟨ρ g u₀, hU g u₀ hu₀⟩ : U) = ⟨u₀, hu₀⟩ := f.injective (hf g ⟨u₀, hu₀⟩)
      exact congrArg Subtype.val h2
    have hinv : ∀ g, ∀ w ∈ Submodule.span E ({u₀} : Set W),
        θ g w ∈ Submodule.span E ({u₀} : Set W) := by
      intro g w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul, hfix g]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self u₀)
    rcases hirr _ hinv with h | h
    · have hmem : u₀ ∈ Submodule.span E ({u₀} : Set W) := Submodule.mem_span_singleton_self u₀
      rw [h] at hmem
      exact hu₀0 ((Submodule.mem_bot E).mp hmem)
    · have heq : Module.finrank E W = 1 := by
        calc Module.finrank E W = Module.finrank E (⊤ : Submodule E W) := (finrank_top E W).symm
          _ = Module.finrank E (Submodule.span E ({u₀} : Set W)) := by rw [h]
          _ = 1 := finrank_span_singleton hu₀0
      omega
  ·
    refine nk_rep_of_natural h3 hirr U hUθ hUne f
      (fun g => LinearMap.toMatrix' (g : VS →ₗ[ZMod 2] VS)) ?_ nk_det_toMatrix_eq_one
      (fun M => ⟨iota M, nk_toMatrix_iota M⟩)
    intro g u
    show f ⟨ρ g u, hU g u u.2⟩ = _
    rw [hf, nk_apply_eq_mulVec]
  ·
    refine nk_rep_of_natural h3 hirr U hUθ hUne (f.trans dualCoord)
      (fun g => (LinearMap.toMatrix' (g.symm : VS →ₗ[ZMod 2] VS))ᵀ) ?_ ?_ ?_
    · intro g u
      show dualCoord (f ⟨ρ g u, hU g u u.2⟩) = _
      rw [hf, dualCoord_comp]
      rfl
    · intro g
      rw [Matrix.det_transpose]
      exact nk_det_toMatrix_eq_one g.symm
    · intro M
      let Mt : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
        ⟨(M : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ, by rw [Matrix.det_transpose]; exact M.2⟩
      refine ⟨(iota Mt).symm, ?_⟩
      show (LinearMap.toMatrix' (((iota Mt).symm.symm : GS) : VS →ₗ[ZMod 2] VS))ᵀ = _
      rw [LinearEquiv.symm_symm, nk_toMatrix_iota Mt]
      exact Matrix.transpose_transpose _
  ·
    exfalso
    have hrk := htv ttGS nk_ttGS_orderOf
    let R := LinearMap.range ((θ ttGS : W →ₗ[E] W) - LinearMap.id)
    let r : U →ₗ[ZMod 2] U := (ρ ttGS).restrict (fun u hu => hU ttGS u hu)
    have hr : ∀ u, ((f (r u) : traceZeroEnd VS) : Module.End (ZMod 2) VS) =
        (ttGS : VS →ₗ[ZMod 2] VS) ∘ₗ ((f u : traceZeroEnd VS) : Module.End (ZMod 2) VS) ∘ₗ
          (ttGS.symm : VS →ₗ[ZMod 2] VS) := fun u => hf ttGS u
    have h32 := nk_adj_fixed_le f r hr
    have hE4 : Nat.card E ≤ 4 := by rcases hE with h | h <;> omega
    have hRcard : Nat.card R ≤ 4 := le_trans (nk_natCard_le R hrk) hE4
    have hrange : Nat.card (LinearMap.range (r - LinearMap.id)) ≤ 4 := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun x : LinearMap.range (r - LinearMap.id) => (⟨((x : U) : W), ?_⟩ : R)) ?_) hRcard
      · obtain ⟨x, hx⟩ := x
        obtain ⟨u, rfl⟩ := hx
        refine ⟨(u : W), ?_⟩
        simp [r, hρ]
      · intro x y hxy
        have h1 := congrArg Subtype.val hxy
        exact Subtype.ext (Subtype.ext h1)
    have h4 := nk_card_le_fixed_mul r 4 hrange
    have hU256 : Nat.card U = 256 := by
      rw [Nat.card_congr f.toEquiv, natCard_eq_two_pow, finrank_traceZeroEnd finrank_V3]
      norm_num
    omega

end Main

end CFSG.Quasithin.H13.L829NK
