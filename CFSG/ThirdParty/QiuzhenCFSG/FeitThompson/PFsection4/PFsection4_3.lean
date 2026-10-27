module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_9
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 4, Theorem (4.3)

This file starts the formal proof of PF (4.3).  The first checkpoint is to
record the basic direct-product decomposition lemmas used in part `(a)`.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section4

universe v
universe u

/-! ## (4.3) -/

/--
Peterfalvi (4.3)(a): `W \ W₂` is a TI-subset of `L` with normalizer `W`, and
the sec3 cyclic-TI hypothesis holds for `W₁, W₂, W`.
-/
@[expose] public def theorem_4_3_a_statement
    {L : Type u} [Group L] [Finite L]
    (W1 W2 W : Subgroup L) : Prop :=
  Section2.IsTISubsetWithNormalizer ((W : Set L) \ (W2 : Set L)) W ∧
    Section3.hypothesis_3_1_statement W1 W2 W

/--
Peterfalvi (4.3)(b): in the notation of sec3, there are pairwise distinct
irreducible characters `Πᵢⱼ` of `L` and signs `δⱼ` such that
`Ind (ωᵢⱼ - ω₀ⱼ) = δⱼ (Πᵢⱼ - Π₀ⱼ)`, and the sec3 Dade isometry sends `ωᵢⱼ` to
`δⱼ Πᵢⱼ`.
-/
@[expose] public def theorem_4_3_b_statement
    {L : Type u} [Group L] [Finite L]
    (W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L)
    (piChar : I → J → Section1.ClassFunction L)
    (deltaSign : J → ℂ)
    (_hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω) : Prop :=
  Section3.theorem_3_2_map_statement W1 W2 W σ ∧
    (∀ j, Section1.IsSign (deltaSign j)) ∧
    (∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j)) ∧
    (∀ p q : I × J, p ≠ q → piChar p.1 p.2 ≠ piChar q.1 q.2) ∧
    (∀ i j,
      Section1.inducedCF W (ω i j - ω i0 j) =
        deltaSign j • (piChar i j - piChar i0 j)) ∧
    ∀ i j, σ (ω i j) = deltaSign j • piChar i j

/--
Peterfalvi (4.3)(c): on `W \ W₂`, the characters `Πᵢⱼ` agree with the
`ωᵢⱼ` up to the sign `δⱼ`, and every other irreducible character of `L`
vanishes there.
-/
@[expose] public def theorem_4_3_c_statement
    {L : Type u} [Group L] [Finite L]
    (W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (piChar : I → J → Section1.ClassFunction L)
    (deltaSign : J → ℂ)
    (ω : I → J → Section1.ClassFunction W) : Prop :=
  (∀ i j x, ∀ hx : x ∈ ((W : Set L) \ (W2 : Set L)),
      piChar i j x = deltaSign j * ω i j ⟨x, hx.1⟩) ∧
    ∀ ψ : Section1.ClassFunction L,
      Section1.IsIrreducibleCharacterOnGroup ψ →
      ψ ∉ Set.range (fun p : I × J => piChar p.1 p.2) →
      Section3.VanishesOn ψ ((W : Set L) \ (W2 : Set L))

/--
Peterfalvi (4.3)(d): every `Πᵢⱼ(1)` is congruent to the sign `δⱼ` modulo
`|W₁|`, expressed by an explicit integral correction term.
-/
@[expose] public def theorem_4_3_d_statement
    {L : Type u} [Group L] [Finite L]
    (W1 : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (piChar : I → J → Section1.ClassFunction L)
    (deltaSign : J → ℂ) : Prop :=
  ∀ i j, ∃ a : ℤ,
    Section1.degree (piChar i j) =
      deltaSign j + ((a : ℂ) * (Nat.card W1 : ℂ))

/--
Peterfalvi Theorem (4.3): under Hypothesis (4.2), one gets the TI-subset
statement for `W \ W₂`, a sec3 Dade-isometry package adapted to `L`, the
value formula on `W \ W₂`, the vanishing of all other irreducibles there, and
the degree congruence modulo `|W₁|`.
-/
@[expose] public def theorem_4_3_statement
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (_h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω) : Prop :=
  theorem_4_3_a_statement W1 W2 W ∧
    ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L,
      ∃ piChar : I → J → Section1.ClassFunction L,
        ∃ deltaSign : J → ℂ,
          theorem_4_3_b_statement W1 W2 W I J i0 j0 ω σ piChar deltaSign hω ∧
            theorem_4_3_c_statement W2 W I J piChar deltaSign ω ∧
            theorem_4_3_d_statement W1 I J piChar deltaSign


private theorem internalSemidirectProduct_mul_unique_pf43
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K)
    {h₁ h₂ k₁ k₂ : G}
    (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H)
    (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (hmul : h₁ * k₁ = h₂ * k₂) :
    h₁ = h₂ ∧ k₁ = k₂ := by
  have hleft_eq_right : h₂⁻¹ * h₁ = k₂ * k₁⁻¹ := by
    calc
      h₂⁻¹ * h₁ = h₂⁻¹ * (h₁ * k₁) * k₁⁻¹ := by
        simp [mul_assoc]
      _ = h₂⁻¹ * (h₂ * k₂) * k₁⁻¹ := by
        rw [hmul]
      _ = k₂ * k₁⁻¹ := by
        simp
  have hmemH : h₂⁻¹ * h₁ ∈ H :=
    H.mul_mem (H.inv_mem hh₂) hh₁
  have hmemK : h₂⁻¹ * h₁ ∈ K := by
    rw [hleft_eq_right]
    exact K.mul_mem hk₂ (K.inv_mem hk₁)
  have hbot : h₂⁻¹ * h₁ ∈ (⊥ : Subgroup G) := by
    have hinf : h₂⁻¹ * h₁ ∈ H ⊓ K :=
      Subgroup.mem_inf.mpr ⟨hmemH, hmemK⟩
    simpa [h.inf_eq_bot] using hinf
  have hh_eq_one : h₂⁻¹ * h₁ = 1 := by
    simpa using hbot
  have hh : h₁ = h₂ := by
    calc
      h₁ = h₂ * (h₂⁻¹ * h₁) := by
        simp
      _ = h₂ := by
        simp [hh_eq_one]
  have hk : k₁ = k₂ := by
    have hmul' := congrArg (fun z : G => h₂⁻¹ * z) hmul
    simpa [hh, mul_assoc] using hmul'
  exact ⟨hh, hk⟩

private theorem internalSemidirectProduct_card_mul_pf43
    {G : Type u} [Group G] [Finite G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K) :
    Nat.card C = Nat.card H * Nat.card K := by
  classical
  let f : H × K → C := fun p =>
    ⟨(p.1 : G) * (p.2 : G),
      C.mul_mem (h.left_le p.1.2) (h.right_le p.2.2)⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
    apply Prod.ext
    · apply Subtype.ext
      exact (internalSemidirectProduct_mul_unique_pf43 h h₁.2 h₂.2 k₁.2 k₂.2
        (Subtype.ext_iff.mp heq)).1
    · apply Subtype.ext
      exact (internalSemidirectProduct_mul_unique_pf43 h h₁.2 h₂.2 k₁.2 k₂.2
        (Subtype.ext_iff.mp heq)).2
  have hf_surj : Function.Surjective f := by
    intro c
    rcases h.mul_surjective (c : G) c.2 with ⟨h₀, hh₀, k₀, hk₀, hc⟩
    refine ⟨(⟨h₀, hh₀⟩, ⟨k₀, hk₀⟩), ?_⟩
    apply Subtype.ext
    exact hc.symm
  have hcard_equiv :
      Nat.card (H × K) = Nat.card C :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  have hprod : Nat.card (H × K) = Nat.card H * Nat.card K := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card]
    exact Fintype.card_prod H K
  rw [← hcard_equiv, hprod]

private noncomputable def internalSemidirectLeftComponent_pf43
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K) (c : C) : H := by
  classical
  let hs := h.mul_surjective (c : G) c.2
  exact ⟨Classical.choose hs, (Classical.choose_spec hs).1⟩

private noncomputable def internalSemidirectRightComponent_pf43
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K) (c : C) : K := by
  classical
  let hs := h.mul_surjective (c : G) c.2
  let hk := (Classical.choose_spec hs).2
  exact ⟨Classical.choose hk, (Classical.choose_spec hk).1⟩

private theorem internalSemidirectLeft_mul_rightComponent_pf43
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K) (c : C) :
    (internalSemidirectLeftComponent_pf43 h c : G) *
        (internalSemidirectRightComponent_pf43 h c : G) = c := by
  classical
  dsimp [internalSemidirectLeftComponent_pf43, internalSemidirectRightComponent_pf43]
  let hs := h.mul_surjective (c : G) c.2
  let hk := (Classical.choose_spec hs).2
  exact (Classical.choose_spec hk).2.symm

private theorem internalSemidirectRightComponent_of_mul_pf43
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K)
    {h₀ k₀ : G} (hh₀ : h₀ ∈ H) (hk₀ : k₀ ∈ K) :
    internalSemidirectRightComponent_pf43 h
        ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩ =
      ⟨k₀, hk₀⟩ := by
  apply Subtype.ext
  have hdec :=
    internalSemidirectLeft_mul_rightComponent_pf43 h
      ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩
  exact
    (internalSemidirectProduct_mul_unique_pf43 h
      (internalSemidirectLeftComponent_pf43 h
        ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩).2
      hh₀
      (internalSemidirectRightComponent_pf43 h
        ⟨h₀ * k₀, C.mul_mem (h.left_le hh₀) (h.right_le hk₀)⟩).2
      hk₀ hdec).2

private noncomputable def internalSemidirectRightProjection_pf43
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalSemidirectProduct C H K) : C →* K where
  toFun := internalSemidirectRightComponent_pf43 h
  map_one' := by
    apply Subtype.ext
    have hdec := internalSemidirectLeft_mul_rightComponent_pf43 h (1 : C)
    exact
      (internalSemidirectProduct_mul_unique_pf43 h
        (internalSemidirectLeftComponent_pf43 h (1 : C)).2 H.one_mem
        (internalSemidirectRightComponent_pf43 h (1 : C)).2 K.one_mem
        (by simpa using hdec)).2
  map_mul' := by
    intro c d
    apply Subtype.ext
    let lc := internalSemidirectLeftComponent_pf43 h c
    let rc := internalSemidirectRightComponent_pf43 h c
    let ld := internalSemidirectLeftComponent_pf43 h d
    let rd := internalSemidirectRightComponent_pf43 h d
    have hdec_c : (lc : G) * (rc : G) = (c : G) :=
      internalSemidirectLeft_mul_rightComponent_pf43 h c
    have hdec_d : (ld : G) * (rd : G) = (d : G) :=
      internalSemidirectLeft_mul_rightComponent_pf43 h d
    have hleft_mem : (lc : G) * Section2.conjBy (rc : G) (ld : G) ∈ H :=
      H.mul_mem lc.2 (h.right_normalizes_left (rc : G) rc.2 (ld : G) ld.2)
    have hright_mem : (rc : G) * (rd : G) ∈ K :=
      K.mul_mem rc.2 rd.2
    have hprod :
        ((lc : G) * Section2.conjBy (rc : G) (ld : G)) * ((rc : G) * (rd : G)) =
          ((c : G) * (d : G)) := by
      calc
        ((lc : G) * Section2.conjBy (rc : G) (ld : G)) * ((rc : G) * (rd : G)) =
            ((lc : G) * (rc : G)) * ((ld : G) * (rd : G)) := by
              simp [Section2.conjBy, mul_assoc]
        _ = (c : G) * (d : G) := by
              rw [hdec_c, hdec_d]
    have hdec_cd :=
      internalSemidirectLeft_mul_rightComponent_pf43 h (c * d)
    exact
      (internalSemidirectProduct_mul_unique_pf43 h
        (internalSemidirectLeftComponent_pf43 h (c * d)).2 hleft_mem
        (internalSemidirectRightComponent_pf43 h (c * d)).2 hright_mem
        (by simpa [hprod] using hdec_cd)).2


private noncomputable def internalDirectProductMulEquiv_pf43
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2) :
    W1 × W2 ≃* W :=
  Section3.internalDirectProductMulEquiv h

private theorem exists_factors_of_mem_of_internalDirectProduct
    {L : Type u} [Group L]
    {W1 W2 W : Subgroup L}
    (hW : Section2.IsInternalDirectProduct W W1 W2)
    {w : L} (hw : w ∈ W) :
    ∃ x ∈ W1, ∃ y ∈ W2, w = x * y :=
  hW.mul_surjective w hw

private theorem left_ne_one_of_mul_mem_wMinusW2
    {L : Type u} [Group L]
    {W1 W2 W : Subgroup L}
    {x y : L}
    (_hx : x ∈ W1) (hy : y ∈ W2)
    (hxy : x * y ∈ ((W : Set L) \ (W2 : Set L))) :
    x ≠ 1 := by
  intro hx1
  have hxyW2 : x * y ∈ W2 := by
    simpa [hx1] using hy
  exact hxy.2 hxyW2

private theorem mul_mem_wMinusW2_of_left_ne_one
    {L : Type u} [Group L]
    {W1 W2 W : Subgroup L}
    (hW : Section2.IsInternalDirectProduct W W1 W2)
    {x y : L}
    (hx : x ∈ W1) (hx1 : x ≠ 1) (hy : y ∈ W2) :
    x * y ∈ ((W : Set L) \ (W2 : Set L)) := by
  constructor
  · exact W.mul_mem (hW.left_le hx) (hW.right_le hy)
  · intro hxyW2
    have hxW2 : x ∈ W2 := by
      have hxyyinv : x * y * y⁻¹ ∈ W2 := by
        exact W2.mul_mem hxyW2 (W2.inv_mem hy)
      simpa [mul_assoc] using hxyyinv
    have hxbot : x ∈ W1 ⊓ W2 := ⟨hx, hxW2⟩
    have hxeq1 : x = 1 := by
      have hxbot' : x ∈ (⊥ : Subgroup L) := by
        simpa [hW.inf_eq_bot] using hxbot
      simpa using hxbot'
    exact hx1 hxeq1

private theorem exists_ne_one_mem_of_natCard_ne_one
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hH : Nat.card H ≠ 1) :
    ∃ x : G, x ∈ H ∧ x ≠ 1 := by
  have hH_ne_bot : H ≠ ⊥ := by
    intro hbot
    apply hH
    simp [hbot]
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hH_ne_bot with ⟨x, hx1⟩
  exact ⟨x, x.2, by simpa using hx1⟩

private theorem mem_elementCentralizer_of_conjBy_eq_self_pf43
    {G : Type u} [Group G] {a g : G}
    (hga : Section2.conjBy g a = a) :
    g ∈ Section2.elementCentralizer a := by
  unfold Section2.elementCentralizer
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  calc
    a * g = Section2.conjBy g a * g := by rw [hga]
    _ = g * a := by simp [Section2.conjBy, mul_assoc]

private theorem w2_le_K_of_hypothesis_4_2
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : hypothesis_4_2_statement K W1 W2 W) :
    W2 ≤ K := by
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, hcard1, _hcyc2, _hcard2,
      hcent, _hW1, _hW2, _hW, _hodd⟩
  rcases exists_ne_one_mem_of_natCard_ne_one W1 hcard1 with ⟨x, hxW1, hx1⟩
  have hcentx : Section2.centralizerIn K x = W2 := by
    exact hcent ⟨x, hxW1⟩ (by
      intro hxsub
      exact hx1 (Subtype.ext_iff.mp hxsub))
  intro z hz
  have hz' : z ∈ Section2.centralizerIn K x := by
    simpa [hcentx] using hz
  exact (Subgroup.mem_inf.mp hz').1

private theorem natCard_W1_coprime_natCard_K_of_hypothesis_4_2
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : hypothesis_4_2_statement K W1 W2 W) :
    Nat.Coprime (Nat.card W1) (Nat.card K) := by
  rcases h42 with ⟨hsemi, hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, _hW2, _hW, _hodd⟩
  rcases hHall with ⟨π, hHall⟩
  have hcard_top : Nat.card (⊤ : Subgroup L) = Nat.card K * Nat.card W1 := by
    simpa using internalSemidirectProduct_card_mul_pf43 hsemi
  have hindex_eq : W1.index = Nat.card K := by
    have hmul₁ : W1.index * Nat.card W1 = Nat.card L := Subgroup.index_mul_card (H := W1)
    have hmul₂ : Nat.card K * Nat.card W1 = Nat.card L := by
      simpa using hcard_top.symm
    exact Nat.mul_right_cancel (Nat.card_pos (α := W1)) (hmul₁.trans hmul₂.symm)
  simpa [hindex_eq] using IsHallSubgroup.card_coprime_index (π := π) (H := W1) hHall

private theorem natCard_W1_coprime_natCard_W2_of_hypothesis_4_2
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : hypothesis_4_2_statement K W1 W2 W) :
    Nat.Coprime (Nat.card W1) (Nat.card W2) := by
  have hcopK := natCard_W1_coprime_natCard_K_of_hypothesis_4_2 h42
  have hW2K := w2_le_K_of_hypothesis_4_2 h42
  exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hW2K) hcopK

private theorem isCyclic_W_of_hypothesis_4_2
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : hypothesis_4_2_statement K W1 W2 W) :
    IsCyclic W := by
  have hcop12 := natCard_W1_coprime_natCard_W2_of_hypothesis_4_2 h42
  rcases h42 with ⟨_hsemi, _hHall, hcyc1, _hcard1, hcyc2, _hcard2,
      _hcent, _hW1, _hW2, hW, _hodd⟩
  let e : W1 × W2 ≃* W := internalDirectProductMulEquiv_pf43 hW
  have hprod : IsCyclic (W1 × W2) := by
    exact (Group.isCyclic_prod_iff).2 ⟨hcyc1, hcyc2, hcop12⟩
  exact e.isCyclic.mp hprod

private theorem conjBy_pow_pf43
    {G : Type u} [Group G] (x y : G) (n : ℕ) :
    Section2.conjBy x (y ^ n) = Section2.conjBy x y ^ n := by
  simp [Section2.conjBy]

private theorem pow_eq_left_factor_of_coprime_natCard
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    (hW : Section2.IsInternalDirectProduct W W1 W2)
    {x y : L} (hx : x ∈ W1) (hy : y ∈ W2)
    (hcop : Nat.Coprime (orderOf x) (Nat.card W2)) :
    ∃ n : ℕ, Nat.card W2 ∣ n ∧ (x * y) ^ n = x := by
  have hcomm : Commute x y := hW.commute x hx y hy
  have hyPow : y ^ Nat.card W2 = 1 := by
    exact Subtype.ext_iff.mp (pow_card_eq_one' (x := ⟨y, hy⟩))
  rcases exists_pow_eq_self_of_coprime (x := x) (n := Nat.card W2) hcop.symm with
    ⟨m, hm⟩
  refine ⟨Nat.card W2 * m, ⟨m, rfl⟩, ?_⟩
  calc
    (x * y) ^ (Nat.card W2 * m) = ((x * y) ^ Nat.card W2) ^ m := by
      rw [pow_mul]
    _ = (x ^ Nat.card W2) ^ m := by
      rw [hcomm.mul_pow, hyPow, mul_one]
    _ = x := hm

private theorem pow_mem_left_of_mem_internalDirectProduct_of_card_dvd
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    (hW : Section2.IsInternalDirectProduct W W1 W2)
    {w : L} (hw : w ∈ W) {n : ℕ} (hn : Nat.card W2 ∣ n) :
    w ^ n ∈ W1 := by
  rcases hW.mul_surjective w hw with ⟨x, hx, y, hy, rfl⟩
  rcases hn with ⟨m, rfl⟩
  have hcomm : Commute x y := hW.commute x hx y hy
  have hyPow : y ^ Nat.card W2 = 1 := by
    exact Subtype.ext_iff.mp (pow_card_eq_one' (x := ⟨y, hy⟩))
  have hwpow : (x * y) ^ (Nat.card W2 * m) = x ^ (Nat.card W2 * m) := by
    calc
      (x * y) ^ (Nat.card W2 * m) = ((x * y) ^ Nat.card W2) ^ m := by
        rw [pow_mul]
      _ = (x ^ Nat.card W2) ^ m := by
        rw [hcomm.mul_pow, hyPow, mul_one]
      _ = x ^ (Nat.card W2 * m) := by
        rw [pow_mul]
  rw [hwpow]
  exact W1.pow_mem hx (Nat.card W2 * m)

private theorem rightProjection_top_eq_self_of_mem_right_pf43
    {L : Type u} [Group L]
    {K W1 : Subgroup L}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) K W1)
    {x : L} (hx : x ∈ W1) :
    internalSemidirectRightProjection_pf43 hsemi ⟨x, by trivial⟩ = ⟨x, hx⟩ := by
  change internalSemidirectRightComponent_pf43 hsemi ⟨x, by trivial⟩ = ⟨x, hx⟩
  simpa only [one_mul] using
    (internalSemidirectRightComponent_of_mul_pf43 hsemi (hh₀ := K.one_mem) (hk₀ := hx))


private theorem rightProjection_top_conj_eq_self_pf43
    {L : Type u} [Group L]
    {K W1 : Subgroup L}
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) K W1)
    (hcyc1 : IsCyclic W1) (g x : L) :
    internalSemidirectRightProjection_pf43 hsemi ⟨Section2.conjBy g x, by trivial⟩ =
      internalSemidirectRightProjection_pf43 hsemi ⟨x, by trivial⟩ := by
  let ρ := internalSemidirectRightProjection_pf43 hsemi
  let gg : (⊤ : Subgroup L) := ⟨g, by trivial⟩
  let xx : (⊤ : Subgroup L) := ⟨x, by trivial⟩
  letI : CommGroup W1 := hcyc1.commGroup
  change ρ (gg * xx * gg⁻¹) = ρ xx
  rw [map_mul, map_mul]
  simp [mul_assoc, gg, xx]

private theorem elementCentralizer_le_W_of_hypothesis_4_2
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    {x : L} (hxW1 : x ∈ W1) (hx1 : x ≠ 1) :
    Section2.elementCentralizer x ≤ W := by
  rcases h42 with ⟨hsemi, _hHall, hcyc1, _hcard1, _hcyc2, _hcard2,
      hcent, _hW1, _hW2, hW, _hodd⟩
  intro g hg
  rcases hsemi.mul_surjective g (by trivial) with ⟨k, hk, u, hu, rfl⟩
  letI : CommGroup W1 := hcyc1.commGroup
  have hux : (u : L) * x = x * u := by
    simpa using mul_comm (⟨u, hu⟩ : W1) (⟨x, hxW1⟩ : W1)
  have hxg : x * (k * u) = (k * u) * x := by
    unfold Section2.elementCentralizer at hg
    rw [Subgroup.mem_centralizer_iff] at hg
    simpa [mul_assoc] using hg x (by simp)
  have hxk' := congrArg (fun z : L => z * u⁻¹) hxg
  have hxk : x * k = k * x := by
    simpa [mul_assoc, hux] using hxk'
  have hkCent : k ∈ Section2.elementCentralizer x := by
    unfold Section2.elementCentralizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact hxk
  have hkW2 : k ∈ W2 := by
    have hkIn : k ∈ Section2.centralizerIn K x :=
      Subgroup.mem_inf.mpr ⟨hk, hkCent⟩
    have hcentx : Section2.centralizerIn K x = W2 := by
      exact hcent ⟨x, hxW1⟩ (by
        intro hxsub
        exact hx1 (Subtype.ext_iff.mp hxsub))
    simpa [hcentx] using hkIn
  exact W.mul_mem (hW.right_le hkW2) (hW.left_le hu)

private theorem mem_W_of_conjBy_mem_wMinusW2
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    {a g : L}
    (ha : a ∈ ((W : Set L) \ (W2 : Set L)))
    (hga : Section2.conjBy g a ∈ ((W : Set L) \ (W2 : Set L))) :
    g ∈ W := by
  have h42' := h42
  have hW2K := w2_le_K_of_hypothesis_4_2 h42
  have hcopW1K := natCard_W1_coprime_natCard_K_of_hypothesis_4_2 h42
  rcases h42 with ⟨hsemi, _hHall, hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, _hW2, hW, _hodd⟩
  rcases exists_factors_of_mem_of_internalDirectProduct hW ha.1 with
    ⟨x, hxW1, y, hyW2, haxy⟩
  have hx1 : x ≠ 1 := left_ne_one_of_mul_mem_wMinusW2 hxW1 hyW2 (by
    simpa [haxy] using ha)
  have hyK : y ∈ K := hW2K hyW2
  have hcopxW2 : Nat.Coprime (orderOf x) (Nat.card W2) := by
    have hcopxK : Nat.Coprime (orderOf x) (Nat.card K) :=
      Nat.Coprime.of_dvd_left (Subgroup.orderOf_dvd_natCard W1 hxW1) hcopW1K
    exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hW2K) hcopxK
  rcases pow_eq_left_factor_of_coprime_natCard hW hxW1 hyW2 hcopxW2 with
    ⟨n, hnDiv, hpow⟩
  have hxpow : a ^ n = x := by
    simpa [haxy] using hpow
  have hxgW1 : Section2.conjBy g x ∈ W1 := by
    have hgaW : Section2.conjBy g a ∈ W := hga.1
    have hxgpow : Section2.conjBy g x = (Section2.conjBy g a) ^ n := by
      calc
        Section2.conjBy g x = Section2.conjBy g (a ^ n) := by rw [hxpow.symm]
        _ = (Section2.conjBy g a) ^ n := by
              simpa using conjBy_pow_pf43 g a n
    rw [hxgpow]
    exact pow_mem_left_of_mem_internalDirectProduct_of_card_dvd hW hgaW hnDiv
  have hrho :
      internalSemidirectRightProjection_pf43 hsemi ⟨Section2.conjBy g x, by trivial⟩ =
        ⟨x, hxW1⟩ := by
    calc
      internalSemidirectRightProjection_pf43 hsemi ⟨Section2.conjBy g x, by trivial⟩ =
          internalSemidirectRightProjection_pf43 hsemi ⟨x, by trivial⟩ :=
            rightProjection_top_conj_eq_self_pf43 hsemi hcyc1 g x
      _ = ⟨x, hxW1⟩ := rightProjection_top_eq_self_of_mem_right_pf43 hsemi hxW1
  have hxgEq : Section2.conjBy g x = x := by
    have hself :=
      rightProjection_top_eq_self_of_mem_right_pf43 hsemi hxgW1
    exact Subtype.ext_iff.mp (hself.symm.trans hrho)
  have hgCent : g ∈ Section2.elementCentralizer x :=
    mem_elementCentralizer_of_conjBy_eq_self_pf43 hxgEq
  exact elementCentralizer_le_W_of_hypothesis_4_2 h42' hxW1 hx1 hgCent

private theorem conjBy_eq_self_of_mem_W
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    (hW : Section2.IsInternalDirectProduct W W1 W2)
    (hcyc1 : IsCyclic W1) (hcyc2 : IsCyclic W2)
    {w z : L} (hw : w ∈ W) (hz : z ∈ W) :
    Section2.conjBy w z = z := by
  rcases hW.mul_surjective w hw with ⟨x, hx, y, hy, hwxy⟩
  rcases hW.mul_surjective z hz with ⟨u, hu, v, hv, hzuv⟩
  letI : CommGroup W1 := hcyc1.commGroup
  letI : CommGroup W2 := hcyc2.commGroup
  have hxu : x * u = u * x := by
    simpa using mul_comm (⟨x, hx⟩ : W1) (⟨u, hu⟩ : W1)
  have hyv : y * v = v * y := by
    simpa using mul_comm (⟨y, hy⟩ : W2) (⟨v, hv⟩ : W2)
  have hyu : y * u = u * y := by
    simpa using (hW.commute u hu y hy).symm
  have hxv : x * v = v * x := by
    exact hW.commute x hx v hv
  have hwz : w * z = z * w := by
    rw [hwxy, hzuv]
    calc
      (x * y) * (u * v) = x * (y * u) * v := by
        simp [mul_assoc]
      _ = x * (u * y) * v := by
        rw [hyu]
      _ = (x * u) * (y * v) := by
        simp [mul_assoc]
      _ = (u * x) * (v * y) := by
        rw [hxu, hyv]
      _ = u * (x * v) * y := by
        simp [mul_assoc]
      _ = u * (v * x) * y := by
        rw [hxv]
      _ = (u * v) * (x * y) := by
        simp [mul_assoc]
  calc
    Section2.conjBy w z = w * z * w⁻¹ := rfl
    _ = z * w * w⁻¹ := by rw [hwz]
    _ = z := by simp

private theorem normalizesSet_wMinusW2_of_mem_W
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    {w : L} (hw : w ∈ W) :
    Section2.normalizesSet ((W : Set L) \ (W2 : Set L)) w := by
  rcases h42 with ⟨_hsemi, _hHall, hcyc1, _hcard1, hcyc2, _hcard2,
      _hcent, _hW1, _hW2, hW, _hodd⟩
  intro g
  constructor
  · intro hconj
    have hgW : g ∈ W := by
      have hgconjW : Section2.conjBy w g ∈ W := hconj.1
      have hgEq : g = w⁻¹ * Section2.conjBy w g * w := by
        simp [Section2.conjBy, mul_assoc]
      rw [hgEq]
      exact W.mul_mem (W.mul_mem (W.inv_mem hw) hgconjW) hw
    have hfix : Section2.conjBy w g = g :=
      conjBy_eq_self_of_mem_W hW hcyc1 hcyc2 hw hgW
    simpa [hfix] using hconj
  · intro hg
    have hfix : Section2.conjBy w g = g :=
      conjBy_eq_self_of_mem_W hW hcyc1 hcyc2 hw hg.1
    simpa [hfix] using hg

private theorem isTISubsetWithNormalizer_wMinusW2_of_hypothesis_4_2
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : hypothesis_4_2_statement K W1 W2 W) :
    Section2.IsTISubsetWithNormalizer ((W : Set L) \ (W2 : Set L)) W := by
  have h42' := h42
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, _hW2, hW, _hodd⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases exists_ne_one_mem_of_natCard_ne_one W1 hcard1 with ⟨x, hxW1, hx1⟩
    refine ⟨x * 1, ?_⟩
    simpa using mul_mem_wMinusW2_of_left_ne_one hW hxW1 hx1 W2.one_mem
  · intro a ha ha1
    exact ha.2 (by simp [ha1])
  · intro g hgInter
    rcases hgInter with ⟨a, haA, haConj⟩
    rcases haConj with ⟨b, hbA, hab⟩
    have hgbA : Section2.conjBy g b ∈ ((W : Set L) \ (W2 : Set L)) := by
      simpa [hab] using haA
    have hgW : g ∈ W := mem_W_of_conjBy_mem_wMinusW2 h42' hbA hgbA
    exact normalizesSet_wMinusW2_of_mem_W h42' hgW
  · apply le_antisymm
    · intro g hgNorm
      rcases exists_ne_one_mem_of_natCard_ne_one W1 hcard1 with ⟨a0, ha0W1, ha01⟩
      let a : L := a0 * 1
      have ha : a ∈ ((W : Set L) \ (W2 : Set L)) := by
        simpa [a] using mul_mem_wMinusW2_of_left_ne_one hW ha0W1 ha01 W2.one_mem
      have hga : Section2.conjBy g a ∈ ((W : Set L) \ (W2 : Set L)) :=
        (hgNorm a).2 ha
      exact mem_W_of_conjBy_mem_wMinusW2 h42' ha hga
    · intro w hw
      exact normalizesSet_wMinusW2_of_mem_W h42' hw

private theorem isTISubsetWithNormalizer_cyclicTISet_of_hypothesis_4_2
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : hypothesis_4_2_statement K W1 W2 W) :
    Section2.IsTISubsetWithNormalizer (Section3.cyclicTISet W1 W2 W) W := by
  have h42' := h42
  rcases h42 with ⟨_hsemi, _hHall, hcyc1, hcard1, hcyc2, hcard2,
      _hcent, _hW1, _hW2, hW, _hodd⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases exists_ne_one_mem_of_natCard_ne_one W1 hcard1 with ⟨x, hxW1, hx1⟩
    rcases exists_ne_one_mem_of_natCard_ne_one W2 hcard2 with ⟨y, hyW2, hy1⟩
    have hxyWm : x * y ∈ ((W : Set L) \ (W2 : Set L)) :=
      mul_mem_wMinusW2_of_left_ne_one hW hxW1 hx1 hyW2
    refine ⟨x * y, ?_⟩
    rw [Section3.cyclicTISet_mem_iff]
    refine ⟨hxyWm.1, ?_, hxyWm.2⟩
    · intro hxyW1
      have hyW1 : y ∈ W1 := by
        have hxyyinv : x * y * x⁻¹ ∈ W1 := by
          exact W1.mul_mem hxyW1 (W1.inv_mem hxW1)
        simpa [mul_assoc, hW.commute x hxW1 y hyW2] using hxyyinv
      have hybot : y ∈ W1 ⊓ W2 := ⟨hyW1, hyW2⟩
      have hyEq1 : y = 1 := by
        have hyBot' : y ∈ (⊥ : Subgroup L) := by
          simpa [hW.inf_eq_bot] using hybot
        simpa using hyBot'
      exact hy1 hyEq1
  · intro a ha ha1
    exact (Section3.cyclicTISet_not_mem_left W1 W2 W ha) (by simp [ha1])
  · intro g hgInter
    rcases hgInter with ⟨a, haA, haConj⟩
    rcases haConj with ⟨b, hbA, hab⟩
    have hbWm : b ∈ ((W : Set L) \ (W2 : Set L)) := by
      exact ⟨Section3.cyclicTISet_subset W1 W2 W hbA, Section3.cyclicTISet_not_mem_right W1 W2 W hbA⟩
    have hgbWm : Section2.conjBy g b ∈ ((W : Set L) \ (W2 : Set L)) := by
      have haWm : a ∈ ((W : Set L) \ (W2 : Set L)) := by
        exact ⟨Section3.cyclicTISet_subset W1 W2 W haA, Section3.cyclicTISet_not_mem_right W1 W2 W haA⟩
      simpa [hab] using haWm
    have hgW : g ∈ W := mem_W_of_conjBy_mem_wMinusW2 h42' hbWm hgbWm
    have hnormWm := normalizesSet_wMinusW2_of_mem_W h42' hgW
    intro x
    constructor
    · intro hx
      have hxcyc := (Section3.cyclicTISet_mem_iff W1 W2 W).mp hx
      have hxWm : x ∈ ((W : Set L) \ (W2 : Set L)) := (hnormWm x).1 ⟨hxcyc.1, hxcyc.2.2⟩
      rw [Section3.cyclicTISet_mem_iff]
      refine ⟨hxWm.1, ?_, hxWm.2⟩
      intro hxW1
      have hxW : x ∈ W := hxWm.1
      have hfix : Section2.conjBy g x = x :=
        conjBy_eq_self_of_mem_W hW hcyc1 hcyc2 hgW hxW
      exact hxcyc.2.1 (by simpa [hfix] using hxW1)
    · intro hx
      have hxWm : x ∈ ((W : Set L) \ (W2 : Set L)) := by
        exact ⟨(Section3.cyclicTISet_subset W1 W2 W hx), Section3.cyclicTISet_not_mem_right W1 W2 W hx⟩
      have hconjWm : Section2.conjBy g x ∈ ((W : Set L) \ (W2 : Set L)) := (hnormWm x).2 hxWm
      rw [Section3.cyclicTISet_mem_iff]
      refine ⟨hconjWm.1, ?_, hconjWm.2⟩
      intro hconjW1
      have hxBack : x ∈ W1 := by
        have hxW : x ∈ W := hxWm.1
        have hfix : Section2.conjBy g x = x :=
          conjBy_eq_self_of_mem_W hW hcyc1 hcyc2 hgW hxW
        simpa [hfix] using hconjW1
      exact (Section3.cyclicTISet_not_mem_left W1 W2 W hx) hxBack
  · apply le_antisymm
    · intro g hgNorm
      rcases exists_ne_one_mem_of_natCard_ne_one W1 hcard1 with ⟨x0, hx0W1, hx01⟩
      rcases exists_ne_one_mem_of_natCard_ne_one W2 hcard2 with ⟨y0, hy0W2, hy01⟩
      let a : L := x0 * y0
      have ha : a ∈ Section3.cyclicTISet W1 W2 W := by
        have hxyWm : x0 * y0 ∈ ((W : Set L) \ (W2 : Set L)) :=
          mul_mem_wMinusW2_of_left_ne_one hW hx0W1 hx01 hy0W2
        rw [Section3.cyclicTISet_mem_iff]
        refine ⟨hxyWm.1, ?_, hxyWm.2⟩
        intro hxyW1
        have hyW1 : y0 ∈ W1 := by
          have hxyyinv : x0 * y0 * x0⁻¹ ∈ W1 := by
            exact W1.mul_mem hxyW1 (W1.inv_mem hx0W1)
          simpa [mul_assoc, hW.commute x0 hx0W1 y0 hy0W2] using hxyyinv
        have hybot : y0 ∈ W1 ⊓ W2 := ⟨hyW1, hy0W2⟩
        have hyEq1 : y0 = 1 := by
          have hyBot' : y0 ∈ (⊥ : Subgroup L) := by
            simpa [hW.inf_eq_bot] using hybot
          simpa using hyBot'
        exact hy01 hyEq1
      have hga : Section2.conjBy g a ∈ Section3.cyclicTISet W1 W2 W :=
        (hgNorm a).2 ha
      have haWm : a ∈ ((W : Set L) \ (W2 : Set L)) := by
        exact ⟨Section3.cyclicTISet_subset W1 W2 W ha, Section3.cyclicTISet_not_mem_right W1 W2 W ha⟩
      have hgaWm : Section2.conjBy g a ∈ ((W : Set L) \ (W2 : Set L)) := by
        exact ⟨Section3.cyclicTISet_subset W1 W2 W hga, Section3.cyclicTISet_not_mem_right W1 W2 W hga⟩
      exact mem_W_of_conjBy_mem_wMinusW2 h42' haWm hgaWm
    · intro w hw
      have hnormWm := normalizesSet_wMinusW2_of_mem_W h42' hw
      intro x
      constructor
      · intro hx
        have hxcyc := (Section3.cyclicTISet_mem_iff W1 W2 W).mp hx
        have hconjWm : Section2.conjBy w x ∈ ((W : Set L) \ (W2 : Set L)) := by
          exact ⟨hxcyc.1, hxcyc.2.2⟩
        have hxWm : x ∈ ((W : Set L) \ (W2 : Set L)) := (hnormWm x).1 hconjWm
        rw [Section3.cyclicTISet_mem_iff]
        refine ⟨hxWm.1, ?_, hxWm.2⟩
        have hxW : x ∈ W := hxWm.1
        have hfix : Section2.conjBy w x = x :=
          conjBy_eq_self_of_mem_W hW hcyc1 hcyc2 hw hxW
        simpa [hfix] using hxcyc.2.1
      · intro hx
        have hxcyc := (Section3.cyclicTISet_mem_iff W1 W2 W).mp hx
        have hxWm : x ∈ ((W : Set L) \ (W2 : Set L)) := by
          exact ⟨hxcyc.1, hxcyc.2.2⟩
        have hconjWm : Section2.conjBy w x ∈ ((W : Set L) \ (W2 : Set L)) := (hnormWm x).2 hxWm
        rw [Section3.cyclicTISet_mem_iff]
        refine ⟨hconjWm.1, ?_, hconjWm.2⟩
        have hxW : x ∈ W := hxWm.1
        have hfix : Section2.conjBy w x = x :=
          conjBy_eq_self_of_mem_W hW hcyc1 hcyc2 hw hxW
        simpa [hfix] using hxcyc.2.1

public theorem theorem_4_3_a
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (h42 : hypothesis_4_2_statement K W1 W2 W) :
    theorem_4_3_a_statement W1 W2 W := by
  have hA := isTISubsetWithNormalizer_wMinusW2_of_hypothesis_4_2 h42
  have hcycW := isCyclic_W_of_hypothesis_4_2 h42
  have hV := isTISubsetWithNormalizer_cyclicTISet_of_hypothesis_4_2 h42
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, hW1, hW2, hW, hodd⟩
  refine ⟨hA, ?_⟩
  change Section3.isCyclicTIHypothesis W1 W2 W
  refine ⟨hW1, hW2, hW, hcycW, hodd, _hcard1, _hcard2, hV⟩

private theorem scalarProduct_sub_left_pf43
    {H : Type*} [Finite H]
    (φ ψ η : Section1.ClassFunction H) :
    Section1.scalarProduct H (φ - ψ) η =
      Section1.scalarProduct H φ η - Section1.scalarProduct H ψ η := by
  calc
    Section1.scalarProduct H (φ - ψ) η =
        Section1.scalarProduct H (φ + (-1 : ℂ) • ψ) η := by
          congr
          ext x
          simp [sub_eq_add_neg]
    _ = Section1.scalarProduct H φ η +
          Section1.scalarProduct H ((-1 : ℂ) • ψ) η := by
          rw [Section1.scalarProduct_add_left]
    _ = Section1.scalarProduct H φ η - Section1.scalarProduct H ψ η := by
          rw [Section1.scalarProduct_smul_left]
          ring

private theorem scalarProduct_add_right_pf43
    {H : Type*} [Finite H] (φ ψ η : Section1.ClassFunction H) :
    Section1.scalarProduct H φ (ψ + η) =
      Section1.scalarProduct H φ ψ + Section1.scalarProduct H φ η := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]

private theorem scalarProduct_smul_right_pf43
    {H : Type*} [Finite H] (z : ℂ) (φ ψ : Section1.ClassFunction H) :
    Section1.scalarProduct H φ (z • ψ) = Section1.scalarProduct H φ ψ * star z := by
  calc
    Section1.scalarProduct H φ (z • ψ)
        = (Nat.card H : ℂ)⁻¹ * ∑ g : H, (φ g * star (ψ g)) * star z := by
            unfold Section1.scalarProduct
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            simp [mul_left_comm, mul_comm]
    _ = (Nat.card H : ℂ)⁻¹ * ((∑ g : H, φ g * star (ψ g)) * star z) := by
          rw [Finset.sum_mul]
    _ = Section1.scalarProduct H φ ψ * star z := by
          simp [Section1.scalarProduct, mul_left_comm, mul_comm]

private theorem scalarProduct_sub_right_pf43
    {H : Type*} [Finite H]
    (φ ψ η : Section1.ClassFunction H) :
    Section1.scalarProduct H φ (ψ - η) =
      Section1.scalarProduct H φ ψ - Section1.scalarProduct H φ η := by
  calc
    Section1.scalarProduct H φ (ψ - η) =
        Section1.scalarProduct H φ (ψ + (-1 : ℂ) • η) := by
          congr
          ext x
          simp [sub_eq_add_neg]
    _ = Section1.scalarProduct H φ ψ +
          Section1.scalarProduct H φ ((-1 : ℂ) • η) := by
          rw [scalarProduct_add_right_pf43]
    _ = Section1.scalarProduct H φ ψ - Section1.scalarProduct H φ η := by
          rw [scalarProduct_smul_right_pf43]
          simp [sub_eq_add_neg]

private theorem scalarProduct_sum_left_pf43
    {H : Type*} [Finite H] {ι : Type*} [Fintype ι]
    (ψ : Section1.ClassFunction H) (d : ι → ℂ) (φ : ι → Section1.ClassFunction H) :
    Section1.scalarProduct H (∑ i, d i • φ i) ψ =
      ∑ i, d i * Section1.scalarProduct H (φ i) ψ := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simp [Section1.scalarProduct]
  | @insert i s hi hs =>
      simp [hi, hs, Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left]

private theorem scalarProduct_sum_right_pf43
    {H : Type*} [Finite H] {ι : Type*} [Fintype ι]
    (φ : Section1.ClassFunction H) (d : ι → ℂ) (ψ : ι → Section1.ClassFunction H) :
    Section1.scalarProduct H φ (∑ i, d i • ψ i) =
      ∑ i, Section1.scalarProduct H φ (ψ i) * star (d i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simp [Section1.scalarProduct]
  | @insert i s hi hs =>
      simp [hi, hs, scalarProduct_add_right_pf43, scalarProduct_smul_right_pf43]

private theorem supportedOn_basis_pf43
    {H J : Type*} [Finite H] [Fintype J]
    {A : Set H} (basis : Module.Basis J ℂ (Section1.classFunctionsOn H A)) (j : J) :
    Section1.supportedOn (basis j : Section1.ClassFunction H) A :=
  (Section1.mem_classFunctionsOn).1 (basis j).2

private theorem scalarProduct_eq_zero_of_support_disjoint_pf43
    {H : Type*} [Finite H]
    {A : Set H} {phi psi : Section1.ClassFunction H}
    (hphi : Section1.supportedOn phi A)
    (hpsi : Section1.supportedOn psi Aᶜ) :
    Section1.scalarProduct H phi psi = 0 := by
  rw [Section1.supportedOn_iff] at hphi hpsi
  have hsum : ∑ g : H, phi g * star (psi g) = 0 := by
    classical
    refine Finset.sum_eq_zero ?_
    intro g hg
    by_cases hgA : g ∈ A
    · have hgAc : g ∉ Aᶜ := by simpa using hgA
      have hzero : psi g = 0 := hpsi g hgAc
      simp [hzero]
    · have hzero : phi g = 0 := hphi g hgA
      simp [hzero]
  rw [Section1.scalarProduct, hsum]
  simp

private theorem basis_test_iff_orthogonalTo_subspace_pf43
    {H J : Type*} [Finite H] [Fintype J]
    {A : Set H} (basis : Module.Basis J ℂ (Section1.classFunctionsOn H A))
    (eta : Section1.ClassFunction H) :
    (∀ j, Section1.scalarProduct H (basis j : Section1.ClassFunction H) eta = 0) ↔
      ∀ phi ∈ Section1.classFunctionsOn H A, Section1.scalarProduct H phi eta = 0 := by
  constructor
  · intro h phi hphi
    let x : Section1.classFunctionsOn H A := ⟨phi, hphi⟩
    let L : Section1.classFunctionsOn H A →ₗ[ℂ] ℂ :=
      { toFun := fun psi => Section1.scalarProduct H (psi : Section1.ClassFunction H) eta
        map_add' := by
          intro psi1 psi2
          exact Section1.scalarProduct_add_left (psi1 : Section1.ClassFunction H)
            (psi2 : Section1.ClassFunction H) eta
        map_smul' := by
          intro z psi
          exact Section1.scalarProduct_smul_left z (psi : Section1.ClassFunction H) eta }
    have hLbasis : ∀ j, L (basis j) = 0 := by
      intro j
      simpa [L] using h j
    change L x = 0
    calc
      L x = L (∑ j, basis.repr x j • basis j) := by rw [basis.sum_repr x]
      _ = ∑ j, L (basis.repr x j • basis j) := by rw [map_sum]
      _ = ∑ j, basis.repr x j • L (basis j) := by simp
      _ = 0 := by simp [hLbasis]
  · intro h j
    exact h (basis j) (by simp)

private def deltaFunction_pf43
    {H : Type*} [DecidableEq H] (a : H) : Section1.ClassFunction H :=
  fun x => if x = a then 1 else 0

private theorem deltaFunction_supportedOn_pf43
    {H : Type*} [Finite H] [DecidableEq H]
    {A : Set H} {a : H} (ha : a ∈ A) :
    Section1.supportedOn (deltaFunction_pf43 a) A := by
  rw [Section1.supportedOn_iff]
  intro g hg
  by_cases hga : g = a
  · exfalso
    apply hg
    simpa [hga] using ha
  · simp [deltaFunction_pf43, hga]

private theorem scalarProduct_delta_left_pf43
    {H : Type*} [Finite H] [DecidableEq H]
    (a : H) (phi : Section1.ClassFunction H) :
    Section1.scalarProduct H (deltaFunction_pf43 a) phi =
      (Nat.card H : ℂ)⁻¹ * star (phi a) := by
  unfold Section1.scalarProduct deltaFunction_pf43
  simp

private noncomputable def leftPairSubtypeEquiv_pf43
    {X Y : Type*} (x0 : X) :
    {p : X × Y // p.1 ≠ x0} ≃ ({x : X // x ≠ x0} × Y) := by
  refine
    { toFun := fun p => (⟨p.1.1, p.2⟩, p.1.2)
      invFun := fun q => ⟨(q.1.1, q.2), q.1.2⟩
      left_inv := by
        intro p
        rfl
      right_inv := by
        intro q
        rfl }

private noncomputable def classFunctionsOnEquivFun_pf43
    {H : Type*} [Group H] (A : Set H) :
    Section1.classFunctionsOn H A ≃ₗ[ℂ] ({x : H // x ∈ A} → ℂ) := by
  classical
  refine
    { toFun := fun φ x => (φ : Section1.ClassFunction H) x.1
      invFun := fun f =>
        ⟨fun x => if hx : x ∈ A then f ⟨x, hx⟩ else 0,
          by
            refine (Section1.mem_classFunctionsOn).2 ?_
            rw [Section1.supportedOn_iff]
            intro x hx
            simp [hx]⟩
      map_add' := by
        intro φ ψ
        ext x
        rfl
      map_smul' := by
        intro c φ
        ext x
        rfl
      left_inv := by
        intro φ
        ext x
        by_cases hx : x ∈ A
        · simp [hx]
        · have hφsupp : Section1.supportedOn (φ : Section1.ClassFunction H) A := by
            exact (Section1.mem_classFunctionsOn).1 φ.2
          rw [Section1.supportedOn_iff] at hφsupp
          simp [hx, hφsupp x hx]
      right_inv := by
        intro f
        ext x
        simp [x.2] }

private theorem classFunctionsOn_finrank_eq_card_pf43
    {H : Type*} [Group H] [Finite H] (A : Set H) :
    Module.finrank ℂ (Section1.classFunctionsOn H A) =
      Nat.card {x : H // x ∈ A} := by
  calc
    Module.finrank ℂ (Section1.classFunctionsOn H A) =
        Module.finrank ℂ ({x : H // x ∈ A} → ℂ) := by
          exact LinearEquiv.finrank_eq (classFunctionsOnEquivFun_pf43 A)
    _ = Nat.card {x : H // x ∈ A} := by
          rw [Nat.card_eq_fintype_card]
          exact Module.finrank_fintype_fun_eq_card (R := ℂ)
            (η := {x : H // x ∈ A})

private noncomputable def subgroupSubtypeEquiv_pf43
    {L : Type u} [Group L] {S T : Subgroup L} (hST : S ≤ T) :
    {x : T // (x : L) ∈ S} ≃ S := by
  refine
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨⟨x, hST x.2⟩, x.2⟩
      left_inv := by
        intro x
        cases x
        rfl
      right_inv := by
        intro x
        rfl }

private theorem wMinusW2_card_pf43
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    (hW : Section2.IsInternalDirectProduct W W1 W2) :
    Nat.card {x : W // (x : L) ∉ W2} =
      (Nat.card W1 - 1) * Nat.card W2 := by
  classical
  have hcardCompl :
      Nat.card {x : W // (x : L) ∉ W2} =
        Nat.card W - Nat.card {x : W // (x : L) ∈ W2} := by
    have hcardCompl' :
        Fintype.card {x : W // (x : L) ∉ W2} =
          Fintype.card W - Fintype.card {x : W // (x : L) ∈ W2} := by
      exact Fintype.card_subtype_compl (p := fun x : W => (x : L) ∈ W2)
    simpa only [Nat.card_eq_fintype_card] using hcardCompl'
  have hcardRight :
      Nat.card {x : W // (x : L) ∈ W2} = Nat.card W2 := by
    simpa [Nat.card_eq_fintype_card] using
      (Fintype.card_congr (subgroupSubtypeEquiv_pf43 hW.right_le))
  have hcardW : Nat.card W = Nat.card W1 * Nat.card W2 := by
    have hcardW' : Fintype.card (W1 × W2) = Fintype.card W := by
      exact Fintype.card_congr (internalDirectProductMulEquiv_pf43 hW).toEquiv
    simpa [Nat.card_eq_fintype_card, Fintype.card_prod] using hcardW'.symm
  have hW1pos : 0 < Nat.card W1 := Nat.card_pos
  calc
    Nat.card {x : W // (x : L) ∉ W2} =
        Nat.card W - Nat.card {x : W // (x : L) ∈ W2} := hcardCompl
    _ = Nat.card W1 * Nat.card W2 - Nat.card W2 := by
          rw [hcardRight, hcardW]
    _ = (Nat.card W1 - 1) * Nat.card W2 := by
          have hW1ge : 1 ≤ Nat.card W1 := Nat.succ_le_of_lt hW1pos
          have hW1split : Nat.card W1 = (Nat.card W1 - 1) + 1 := by
            exact (Nat.sub_add_cancel hW1ge).symm
          rw [hW1split, Nat.add_mul, one_mul]
          exact Nat.add_sub_cancel_right ((Nat.card W1 - 1) * Nat.card W2) (Nat.card W2)

private theorem omega_eq_baseRow_of_mem_W2_pf43
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) {x : W} (hx : (x : L) ∈ W2) :
    ω i j x = ω i0 j x := by
  have hleft : ω i j0 x = 1 := by
    have hker := hω.left_kernel i ⟨x, hx⟩
    simpa [hω.degree_one i j0] using hker
  calc
    ω i j x = ω i j0 x * ω i0 j x := hω.product i j x
    _ = ω i0 j x := by simp [hleft]

private theorem omegaRowDifference_CFOn_wMinusW2_pf43
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) :
    Section2.CFOn W ((W : Set L) \ (W2 : Set L)) (ω i j - ω i0 j) := by
  constructor
  · intro x g
    simp [hω.is_class i j x g, hω.is_class i0 j x g]
  · intro x hx
    have hxW2 : (x : L) ∈ W2 := by
      by_contra hxnot
      exact hx ⟨x.2, hxnot⟩
    have hEq : ω i j x = ω i0 j x :=
      omega_eq_baseRow_of_mem_W2_pf43 hω i j hxW2
    simp [Pi.sub_apply, hEq]

private theorem omegaRowDifference_scalarProduct_omega_pf43
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J)
    {p : I} {q : J} (hp : p ≠ i0) :
    Section1.scalarProduct W (ω i j - ω i0 j) (ω p q) =
      if i = p ∧ j = q then 1 else 0 := by
  have hbase :
      Section1.scalarProduct W (ω i0 j) (ω p q) = 0 := by
    have hneq : (i0, j) ≠ (p, q) := by
      intro hpair
      exact hp (congrArg Prod.fst hpair).symm
    simpa [hneq] using
      Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (i0, j) (p, q)
  have hmain :
      Section1.scalarProduct W (ω i j) (ω p q) =
        if i = p ∧ j = q then 1 else 0 := by
    by_cases hij : (i, j) = (p, q)
    · have hi : i = p := congrArg Prod.fst hij
      have hj : j = q := congrArg Prod.snd hij
      simp [hi, hj] at *
      simpa using
        Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (p, q) (p, q)
    · have hneq : ¬ (i = p ∧ j = q) := by
        intro h
        exact hij (by simp [h.1, h.2])
      simpa [hneq, hij] using
        Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (i, j) (p, q)
  rw [scalarProduct_sub_left_pf43, hbase, sub_zero]
  exact hmain

private theorem omegaRowDifference_linearIndependent_pf43
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    LinearIndependent ℂ
      (fun p : {p : I × J // p.1 ≠ i0} => ω p.1.1 p.1.2 - ω i0 p.1.2) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha p
  have hcoord :
      ∀ q : {q : I × J // q.1 ≠ i0},
        Section1.scalarProduct W
          (ω q.1.1 q.1.2 - ω i0 q.1.2)
          (ω p.1.1 p.1.2) =
            if q = p then 1 else 0 := by
    intro q
    have hraw :
        Section1.scalarProduct W
          (ω q.1.1 q.1.2 - ω i0 q.1.2)
          (ω p.1.1 p.1.2) =
            if q.1.1 = p.1.1 ∧ q.1.2 = p.1.2 then 1 else 0 := by
      simpa using
        (omegaRowDifference_scalarProduct_omega_pf43
          (hω := hω) (i := q.1.1) (j := q.1.2)
          (p := p.1.1) (q := p.1.2) (hp := p.2))
    by_cases hqp : q = p
    · subst hqp
      simpa using hraw
    · have hpair : ¬ (q.1.1 = p.1.1 ∧ q.1.2 = p.1.2) := by
        intro hp'
        exact hqp (Subtype.ext (Prod.ext hp'.1 hp'.2))
      simpa [hpair, hqp] using hraw
  have hinner :
      Section1.scalarProduct W
        (∑ q, a q • (ω q.1.1 q.1.2 - ω i0 q.1.2))
        (ω p.1.1 p.1.2) = 0 := by
    rw [ha]
    simp [Section1.scalarProduct]
  have hcoeff :
      Section1.scalarProduct W
        (∑ q, a q • (ω q.1.1 q.1.2 - ω i0 q.1.2))
        (ω p.1.1 p.1.2) = a p := by
    rw [scalarProduct_sum_left_pf43]
    simp [hcoord]
  exact hcoeff ▸ hinner


private theorem proposition_1_3_a_special_pf43
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} [Finite H] [DecidableEq H]
    {A : Set H}
    {I J : Type*} [Fintype I] [Fintype J]
    (basis : Module.Basis J ℂ (Section1.classFunctionsOn H A))
    (chi : I → Section1.ClassFunction H)
    (ind : Section1.ClassFunction H →ₗ[ℂ] Section1.ClassFunction G)
    (mu : Section1.ClassFunction G)
    (hfrob : ∀ alpha,
      Section1.scalarProduct G (ind alpha) mu =
        Section1.scalarProduct H alpha (Section1.subgroupRestriction H mu))
    (d : I → ℂ) :
    (∀ g ∈ A, Section1.subgroupRestriction H mu g = (∑ i, d i • chi i) g) ↔
      ∀ j,
        ∑ i, Section1.scalarProduct H (basis j : Section1.ClassFunction H) (chi i) * star (d i) =
          Section1.scalarProduct G (ind (basis j : Section1.ClassFunction H)) mu := by
  let rhs : Section1.ClassFunction H := ∑ i, d i • chi i
  let diff : Section1.ClassFunction H := Section1.subgroupRestriction H mu - rhs
  have hsupport :
      (∀ g ∈ A, Section1.subgroupRestriction H mu g = rhs g) ↔
        Section1.supportedOn diff Aᶜ := by
    constructor
    · intro h
      rw [Section1.supportedOn_iff]
      intro g hg
      have hgA : g ∈ A := by simpa using hg
      simpa [diff, rhs, Pi.sub_apply, sub_eq_zero] using h g hgA
    · intro h g hg
      rw [Section1.supportedOn_iff] at h
      have hgc : g ∉ Aᶜ := by simpa using hg
      simpa [diff, rhs, Pi.sub_apply, sub_eq_zero] using h g hgc
  constructor
  · intro hEq j
    have hzero :
        Section1.scalarProduct H (basis j : Section1.ClassFunction H) diff = 0 := by
      exact scalarProduct_eq_zero_of_support_disjoint_pf43
        (supportedOn_basis_pf43 basis j) ((hsupport.mp hEq))
    have hexpand :
        Section1.scalarProduct H (basis j : Section1.ClassFunction H) diff =
          Section1.scalarProduct G (ind (basis j : Section1.ClassFunction H)) mu -
            ∑ i, Section1.scalarProduct H (basis j : Section1.ClassFunction H) (chi i) *
              star (d i) := by
      simp [diff, rhs, hfrob, scalarProduct_sub_right_pf43,
        scalarProduct_sum_right_pf43]
    have hmain :
        Section1.scalarProduct G (ind (basis j : Section1.ClassFunction H)) mu -
          ∑ i, Section1.scalarProduct H (basis j : Section1.ClassFunction H) (chi i) *
            star (d i) = 0 := by
      simpa [hexpand] using hzero
    exact (sub_eq_zero.mp hmain).symm
  · intro hCoeff
    have hBasisZero :
        ∀ j, Section1.scalarProduct H (basis j : Section1.ClassFunction H) diff = 0 := by
      intro j
      have hj := hCoeff j
      have hmain :
          Section1.scalarProduct G (ind (basis j : Section1.ClassFunction H)) mu -
            ∑ i, Section1.scalarProduct H (basis j : Section1.ClassFunction H) (chi i) *
              star (d i) = 0 := by
        exact sub_eq_zero.mpr hj.symm
      simpa [diff, rhs, hfrob, scalarProduct_sub_right_pf43,
        scalarProduct_sum_right_pf43] using hmain
    have hAllZero :
        ∀ phi ∈ Section1.classFunctionsOn H A, Section1.scalarProduct H phi diff = 0 :=
        (basis_test_iff_orthogonalTo_subspace_pf43 basis diff).mp hBasisZero
    have hcard : (Nat.card H : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ : Nat.card H ≠ 0)
    have hSuppCompl : Section1.supportedOn diff Aᶜ := by
      rw [Section1.supportedOn_iff]
      intro a ha
      have haA : a ∈ A := by simpa using ha
      have hdelta :
          Section1.scalarProduct H (deltaFunction_pf43 a) diff = 0 := by
        exact hAllZero (deltaFunction_pf43 a)
          ((Section1.mem_classFunctionsOn).2 (deltaFunction_supportedOn_pf43 haA))
      have hpoint :
          diff a = 0 := by
        rw [scalarProduct_delta_left_pf43] at hdelta
        rcases mul_eq_zero.mp hdelta with hbad | hstar
        · exact (inv_ne_zero hcard hbad).elim
        · exact star_eq_zero.mp hstar
      exact hpoint
    exact (hsupport).2 hSuppCompl

private theorem exists_wMinusW2_basis_pf43
    {L : Type u} [Group L] [Finite L]
    (W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (hW : Section2.IsInternalDirectProduct W W1 W2)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    ∃ basis : Module.Basis {p : I × J // p.1 ≠ i0} ℂ
        (Section1.classFunctionsOn W (fun x : W => (x : L) ∉ W2)),
      ∀ p,
        (basis p : Section1.ClassFunction W) = ω p.1.1 p.1.2 - ω i0 p.1.2 := by
  classical
  let Aw : Set W := fun x => (x : L) ∉ W2
  let row :
      {p : I × J // p.1 ≠ i0} → Section1.ClassFunction W := fun p =>
    ω p.1.1 p.1.2 - ω i0 p.1.2
  have h_li : LinearIndependent ℂ row := by
    simpa [row] using omegaRowDifference_linearIndependent_pf43
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) hω
  have hcard_idx :
      Fintype.card {p : I × J // p.1 ≠ i0} =
        (Nat.card W1 - 1) * Nat.card W2 := by
    have hI : Fintype.card {i : I // i ≠ i0} = Nat.card W1 - 1 := by
      simp [hω.card_left]
    calc
      Fintype.card {p : I × J // p.1 ≠ i0} =
          Fintype.card ({i : I // i ≠ i0} × J) := by
            simpa using
              (Fintype.card_congr (leftPairSubtypeEquiv_pf43 (X := I) (Y := J) i0))
      _ = (Nat.card W1 - 1) * Nat.card W2 := by
            rw [Fintype.card_prod]
            simp [hI, hω.card_right]
  have hcard_A :
      Fintype.card {x : W // x ∈ Aw} =
        (Nat.card W1 - 1) * Nat.card W2 := by
    have hcard_A_nat :
        Nat.card {x : W // x ∈ Aw} =
          (Nat.card W1 - 1) * Nat.card W2 := by
      change Nat.card {x : W // (x : L) ∉ W2} =
          (Nat.card W1 - 1) * Nat.card W2
      exact wMinusW2_card_pf43 (W1 := W1) (W2 := W2) (W := W) hW
    calc
      Fintype.card {x : W // x ∈ Aw} = Nat.card {x : W // x ∈ Aw} := by
        rw [Nat.card_eq_fintype_card]
      _ = (Nat.card W1 - 1) * Nat.card W2 := hcard_A_nat
  have hfinrank_A :
      Module.finrank ℂ (Section1.classFunctionsOn W Aw) =
        Fintype.card {x : W // x ∈ Aw} := by
    calc
      Module.finrank ℂ (Section1.classFunctionsOn W Aw) =
          Nat.card {x : W // x ∈ Aw} :=
            classFunctionsOn_finrank_eq_card_pf43 (A := Aw)
      _ = Fintype.card {x : W // x ∈ Aw} := by
            rw [Nat.card_eq_fintype_card]
  have hcard :
      Fintype.card {p : I × J // p.1 ≠ i0} =
        Module.finrank ℂ (Section1.classFunctionsOn W Aw) := by
    calc
      Fintype.card {p : I × J // p.1 ≠ i0} =
          (Nat.card W1 - 1) * Nat.card W2 := hcard_idx
      _ = Fintype.card {x : W // x ∈ Aw} := by
          symm
          exact hcard_A
      _ = Module.finrank ℂ (Section1.classFunctionsOn W Aw) := by
          symm
          exact hfinrank_A
  let e : {p : I × J // p.1 ≠ i0} → Section1.classFunctionsOn W Aw := fun p =>
    ⟨row p, (Section1.mem_classFunctionsOn).2 <| by
      rw [Section1.supportedOn_iff]
      intro x hx
      have hxW2 : (x : L) ∈ W2 := by
        by_contra hxW2
        apply hx
        change (x : L) ∉ W2
        exact hxW2
      exact
        (omegaRowDifference_CFOn_wMinusW2_pf43
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
          (i0 := i0) (j0 := j0) (ω := ω) hω p.1.1 p.1.2).2 x
          (by simpa using hxW2)⟩
  have h_li_sub : LinearIndependent ℂ e := by
    simpa [e, row] using
      (LinearIndependent.of_comp
        (Submodule.subtype (Section1.classFunctionsOn W Aw))
        (v := e) (hfv := h_li))
  have hspan :
      ⊤ ≤ Submodule.span ℂ (Set.range e) := by
    rw [LinearIndependent.span_eq_top_of_card_eq_finrank' h_li_sub hcard]
  refine ⟨Module.Basis.mk h_li_sub hspan, ?_⟩
  intro p
  rw [Module.Basis.mk_apply]

private theorem star_eq_self_of_sign_pf43
    {ε : ℂ} (hε : Section1.IsSign ε) :
    star ε = ε := by
  rcases hε with rfl | rfl <;> simp

private theorem isClassFunction_of_irreducibleCharacterOnGroup_pf43
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsClassFunction χ := by
  rcases hχ with ⟨n, ρ, _hirr, rfl⟩
  intro x g
  simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x

private noncomputable def equivFinWithBase_pf43
    {α : Type*} [Fintype α] [DecidableEq α] [NeZero (Fintype.card α)] (a0 : α) :
    Fin (Fintype.card α) ≃ α := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  exact (Equiv.swap 0 (e a0)).trans e.symm

private theorem equivFinWithBase_apply_zero_pf43
    {α : Type*} [Fintype α] [DecidableEq α] [NeZero (Fintype.card α)] (a0 : α) :
    equivFinWithBase_pf43 a0 0 = a0 := by
  classical
  unfold equivFinWithBase_pf43
  simp

private theorem positiveNatDegree_of_irreducible_pf43
    {G : Type*} [Group G] [Finite G] {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ n : ℕ, 0 < n ∧ Section1.degree χ = n := by
  rcases hχ with ⟨n, ρ, hρ, rfl⟩
  refine ⟨n, ?_, ?_⟩
  · by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hdeg : Section1.degree ρ.character = 0 := by
      simp [Section1.degree_representation_character ρ, hn0]
    exact Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup
      ρ.character ⟨n, ρ, hρ, rfl⟩ hdeg
  · simp [Section1.degree_representation_character ρ]

private theorem degree_evalCoeff_pf43
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    (μ : ι → Section1.ClassFunction G) (d : ι → Nat)
    (hdeg : ∀ i, Section1.degree (μ i) = d i)
    (v : Section1.CoeffVector ι) :
    Section1.degree (Section1.evalCoeff μ v) =
      (Section1.coeffDegree d v : Int) := by
  classical
  unfold Section1.degree Section1.evalCoeff
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hsum :
      (∑ x : ι, (v x : ℂ) * μ x 1) =
        Finset.sum (Section1.coeffSupport v) (fun x => (v x : ℂ) * μ x 1) := by
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (by
      intro x _hx hnot
      have hv0 : v x = 0 := Section1.coeff_eq_zero_of_not_mem_support v hnot
      simp [hv0])
  rw [hsum]
  simp only [Section1.coeffDegree]
  calc
    Finset.sum (Section1.coeffSupport v) (fun x => (v x : ℂ) * μ x 1)
        = Finset.sum (Section1.coeffSupport v) (fun x => (v x : ℂ) * (d x : ℂ)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hxdeg : μ x 1 = d x := by
              simpa [Section1.degree] using hdeg x
            simp [hxdeg]
    _ = Finset.sum (Section1.coeffSupport v) (fun x => ((v x * (d x : Int) : Int) : ℂ)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp
    _ = (((Section1.coeffSupport v).sum fun x => v x * (d x : Int)) : ℂ) := by
          simp
    _ = (Section1.coeffDegree d v : Int) := by
          simp [Section1.coeffDegree]

private theorem degree_omegaRowDifference_eq_zero_pf43
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) :
    Section1.degree (ω i j - ω i0 j) = 0 := by
  have hij : Section1.degree (ω i j) = 1 := hω.degree_one i j
  have h0j : Section1.degree (ω i0 j) = 1 := hω.degree_one i0 j
  have hij' : ω i j 1 = 1 := by
    simpa [Section1.degree] using hij
  have h0j' : ω i0 j 1 = 1 := by
    simpa [Section1.degree] using h0j
  simp [Section1.degree, hij', h0j']

private theorem degree_inducedCF_omegaRowDifference_eq_zero_pf43
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) :
    Section1.degree (Section1.inducedCF W (ω i j - ω i0 j)) = 0 := by
  rw [Section1.degree_inducedClassFunction]
  simp [degree_omegaRowDifference_eq_zero_pf43 (hω := hω) i j]

private theorem two_le_card_left_pf43
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    2 ≤ Fintype.card I := by
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, _hW2, _hW, _hodd⟩
  have hpos : 0 < Fintype.card I := by
    rw [hω.card_left]
    exact Nat.card_pos
  have hne1 : Fintype.card I ≠ 1 := by
    rw [hω.card_left]
    exact hcard1
  omega

private theorem inducedCF_isometry_on_wMinusW2_pf43
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    {α β : Section1.ClassFunction W}
    (hα : Section2.CFOn W ((W : Set L) \ (W2 : Set L)) α)
    (hβ : Section2.CFOn W ((W : Set L) \ (W2 : Set L)) β) :
    Section1.scalarProduct L (Section1.inducedCF W α) (Section1.inducedCF W β) =
      Section1.scalarProduct W α β := by
  let A : Set L := (W : Set L) \ (W2 : Set L)
  have hA : Section2.IsTISubsetWithNormalizer A W := (theorem_4_3_a K W1 W2 W h42).1
  have hHyp2 : Section2.Hypothesis2 A W (fun _ : L => ⊥) :=
    (Section2.proposition_2_3 A W hA.1).1 hA
  have hAL : ∀ a ∈ A, a ∈ W := hHyp2.subset_L
  have h26 := Section2.theorem_2_6 A W (fun _ : L => ⊥) hHyp2 hAL
  have hαeq :=
    Section3.inducedCF_eq_dadeTransform_trivial A W hHyp2 hAL α hα
  have hβeq :=
    Section3.inducedCF_eq_dadeTransform_trivial A W hHyp2 hAL β hβ
  rw [hαeq, hβeq]
  exact h26.1 α β hα hβ

private theorem inducedCF_virtual_omegaRowDifference_pf43
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) :
    Theory.Character.IsVirtualCharacter (Section1.inducedCF W (ω i j - ω i0 j)) := by
  let A : Set L := (W : Set L) \ (W2 : Set L)
  have hA : Section2.IsTISubsetWithNormalizer A W := (theorem_4_3_a K W1 W2 W h42).1
  have hHyp2 : Section2.Hypothesis2 A W (fun _ : L => ⊥) :=
    (Section2.proposition_2_3 A W hA.1).1 hA
  have hAL : ∀ a ∈ A, a ∈ W := hHyp2.subset_L
  have hCF :
      Section2.CFOn W A (ω i j - ω i0 j) :=
    omegaRowDifference_CFOn_wMinusW2_pf43 (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω i j
  have hvirtOn : Section2.virtualCharacterOn W A (ω i j - ω i0 j) := by
    refine ⟨?_, hCF.2⟩
    exact Section3.isVirtualCharacter_sub
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hω.irreducible i j))
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hω.irreducible i0 j))
  have h26 := Section2.theorem_2_6 A W (fun _ : L => ⊥) hHyp2 hAL
  have hdadeVirt := h26.2 (ω i j - ω i0 j) hvirtOn
  have hindEq :=
    Section3.inducedCF_eq_dadeTransform_trivial A W hHyp2 hAL (ω i j - ω i0 j) hCF
  rw [hindEq]
  exact hdadeVirt

private theorem coeffDot_self_eq_coeffSqNorm_pf43
    {J : Type*} [Fintype J] [DecidableEq J] (v : Section1.CoeffVector J) :
    ((Section1.coeffSqNorm v : Nat) : Int) = Section1.coeffDot v v := by
  simpa using Section1.coeffDot_self_eq_coeffSqNorm v

private theorem evalCoeff_signedBasisDifference_pf43
    {G J : Type*} [Fintype J] [DecidableEq J]
    (mu : J → Section1.ClassFunction G) (eps : Int) (a b : J) :
    Section1.evalCoeff mu (Section1.signedBasisDifference eps a b) =
      Section1.signIntToComplex eps • (mu b - mu a) := by
  simpa using Section1.evalCoeff_signedBasisDifference mu eps a b

private theorem isSign_of_isSignInt_pf43 {eps : Int} (heps : Section1.IsSignInt eps) :
    Section1.IsSign (Section1.signIntToComplex eps) := by
  simpa using Section1.isSign_of_isSignInt heps

private theorem difference_norm_eq_two_of_orthonormal_raw_pf43
    {H I : Type*} [Finite H] [DecidableEq I]
    (chi : I → Section1.ClassFunction H)
    (hOrtho :
      ∀ i j : I, Section1.scalarProduct H (chi i) (chi j) = if i = j then 1 else 0)
    {base i : I} (hib : i ≠ base) :
    Section1.scalarProduct H (chi i - chi base) (chi i - chi base) = 2 := by
  have hii : Section1.scalarProduct H (chi i) (chi i) = 1 := by
    simpa using hOrtho i i
  have hib0 : Section1.scalarProduct H (chi i) (chi base) = 0 := by
    simpa [hib] using hOrtho i base
  have hbi0 : Section1.scalarProduct H (chi base) (chi i) = 0 := by
    simpa [hib.symm] using hOrtho base i
  have hbb : Section1.scalarProduct H (chi base) (chi base) = 1 := by
    simpa using hOrtho base base
  calc
    Section1.scalarProduct H (chi i - chi base) (chi i - chi base)
        = Section1.scalarProduct H (chi i) (chi i - chi base) -
            Section1.scalarProduct H (chi base) (chi i - chi base) := by
              rw [scalarProduct_sub_left_pf43]
    _ = (Section1.scalarProduct H (chi i) (chi i) - Section1.scalarProduct H (chi i) (chi base)) -
          (Section1.scalarProduct H (chi base) (chi i) - Section1.scalarProduct H (chi base) (chi base)) := by
            rw [scalarProduct_sub_right_pf43, scalarProduct_sub_right_pf43]
    _ = 2 := by
          norm_num [hii, hib0, hbi0, hbb]

private theorem difference_scalar_eq_one_of_orthonormal_raw_pf43
    {H I : Type*} [Finite H] [DecidableEq I]
    (chi : I → Section1.ClassFunction H)
    (hOrtho :
      ∀ i j : I, Section1.scalarProduct H (chi i) (chi j) = if i = j then 1 else 0)
    {base i j : I} (hib : i ≠ base) (hjb : j ≠ base) (hij : i ≠ j) :
    Section1.scalarProduct H (chi i - chi base) (chi j - chi base) = 1 := by
  have hij0 : Section1.scalarProduct H (chi i) (chi j) = 0 := by
    simpa [hij] using hOrtho i j
  have hib0 : Section1.scalarProduct H (chi i) (chi base) = 0 := by
    simpa [hib] using hOrtho i base
  have hbj0 : Section1.scalarProduct H (chi base) (chi j) = 0 := by
    simpa [hjb.symm] using hOrtho base j
  have hbb : Section1.scalarProduct H (chi base) (chi base) = 1 := by
    simpa using hOrtho base base
  calc
    Section1.scalarProduct H (chi i - chi base) (chi j - chi base)
        = Section1.scalarProduct H (chi i) (chi j - chi base) -
            Section1.scalarProduct H (chi base) (chi j - chi base) := by
              rw [scalarProduct_sub_left_pf43]
    _ = (Section1.scalarProduct H (chi i) (chi j) - Section1.scalarProduct H (chi i) (chi base)) -
          (Section1.scalarProduct H (chi base) (chi j) - Section1.scalarProduct H (chi base) (chi base)) := by
            rw [scalarProduct_sub_right_pf43, scalarProduct_sub_right_pf43]
    _ = 1 := by
          simp [hij0, hib0, hbj0, hbb]

private theorem exists_character_family_fixed_column_pf43
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (j : J) :
    ∃ eps : ℂ, Section1.IsSign eps ∧
      ∃ piCol : I → Section1.ClassFunction L,
        (∀ i, Section1.IsIrreducibleCharacterOnGroup (piCol i)) ∧
        (∀ i i', i ≠ i' → piCol i ≠ piCol i') ∧
        ∀ i, Section1.inducedCF W (ω i j - ω i0 j) = eps • (piCol i - piCol i0) := by
  classical
  have htwo : 2 ≤ Fintype.card I := two_le_card_left_pf43 (h42 := h42) hω
  have hI_ne_zero : Fintype.card I ≠ 0 := by
    omega
  letI : NeZero (Fintype.card I) := ⟨hI_ne_zero⟩
  let e : Fin (Fintype.card I) ≃ I := equivFinWithBase_pf43 i0
  have he0 : e 0 = i0 := by
    simpa [e] using equivFinWithBase_apply_zero_pf43 (a0 := i0)
  have he0symm : e.symm i0 = 0 := by
    apply e.injective
    simp [he0]
  let omegaCol : Fin (Fintype.card I) → Section1.ClassFunction W := fun t => ω (e t) j
  have hOrthoRaw :
      ∀ a b : Fin (Fintype.card I),
        Section1.scalarProduct W (omegaCol a) (omegaCol b) = if a = b then 1 else 0 := by
    intro a b
    simpa [omegaCol] using
      Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (e a, j) (e b, j)
  rcases Theory.Character.irreducible_characters_form_basis (G := L) with
    ⟨ι, hι, χ, hχ, b, hb⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  have hχfull := hχ
  rcases hχ with ⟨hirr, _hall, hinj⟩
  let muBasis : ι → Section1.ClassFunction L := fun k => Section1.ofConjClassFunction (χ k)
  have hmuIrr : ∀ k, Section1.IsIrreducibleCharacterOnGroup (muBasis k) := by
    intro k
    exact Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hirr k)
  have hmuPairwiseRaw : Pairwise (fun a b : ι => muBasis a ≠ muBasis b) := by
    intro a b hab hEq
    apply hab
    apply hinj
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    have hEval := congrArg (fun φ : Section1.ClassFunction L => φ g) hEq
    simpa [muBasis, Section1.ofConjClassFunction_apply] using hEval
  choose d hpos hdegBasis using
    (fun k => positiveNatDegree_of_irreducible_pf43 (hmuIrr k))
  have hcoeffInt :
      ∀ t : Fin (Fintype.card I), ∀ k : ι,
        ∃ z : ℤ,
          Section1.scalarProduct L
            (Section1.inducedCF W (omegaCol t - omegaCol 0))
            (muBasis k) = (z : ℂ) := by
    intro t k
    have hvirt :
        Theory.Character.IsVirtualCharacter
          (Section1.inducedCF W (omegaCol t - omegaCol 0)) := by
      simpa [omegaCol, he0] using
        inducedCF_virtual_omegaRowDifference_pf43
          (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h42 hω (e t) j
    exact Section3.scalarProduct_isVirtualCharacter_eq_int hvirt
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hmuIrr k))
  let v : Fin (Fintype.card I) → Section1.CoeffVector ι := fun t =>
    if ht0 : t = 0 then
      0
    else
      Section3.irreducibleBasisCoeff
        (Section1.inducedCF W (omegaCol t - omegaCol 0))
        (hcoeffInt t)
  have hzero : v 0 = 0 := by
    simp [v]
  have hT :
      ∀ t : Fin (Fintype.card I),
        Section1.inducedCF W (omegaCol t - omegaCol 0) = Section1.evalCoeff muBasis (v t) := by
    intro t
    by_cases ht0 : t = 0
    · subst ht0
      ext g
      simp [v, omegaCol, he0, Section1.inducedCF, Section1.inducedClassFunction,
        Section1.evalCoeff]
    · simpa [muBasis, v, ht0] using
        (Section3.irreducibleBasis_evalCoeff_coeff hχfull b hb
          (Section1.inducedCF W (omegaCol t - omegaCol 0))
          (Section1.inducedCF_isClassFunction W (omegaCol t - omegaCol 0))
          (hcoeffInt t)).symm
  have hDeg :
      ∀ t : Fin (Fintype.card I), Section1.coeffDegree d (v t) = 0 := by
    intro t
    by_cases ht0 : t = 0
    · subst ht0
      simp [v, Section1.coeffDegree]
    · have hdeg0 :
        Section1.degree (Section1.inducedCF W (omegaCol t - omegaCol 0)) = 0 := by
        simpa [omegaCol, he0] using
          degree_inducedCF_omegaRowDifference_eq_zero_pf43
            (W1 := W1) (W2 := W2) (W := W)
            (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω (e t) j
      have hc : ((Section1.coeffDegree d (v t) : Int) : ℂ) = 0 := by
        calc
          ((Section1.coeffDegree d (v t) : Int) : ℂ) =
              Section1.degree (Section1.evalCoeff muBasis (v t)) := by
                symm
                exact degree_evalCoeff_pf43 muBasis d hdegBasis (v t)
          _ = Section1.degree (Section1.inducedCF W (omegaCol t - omegaCol 0)) := by
                rw [← hT t]
          _ = 0 := hdeg0
      exact_mod_cast hc
  have hCF :
      ∀ t : Fin (Fintype.card I),
        Section2.CFOn W ((W : Set L) \ (W2 : Set L)) (omegaCol t - omegaCol 0) := by
    intro t
    simpa [omegaCol, he0] using
      omegaRowDifference_CFOn_wMinusW2_pf43
        (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω (e t) j
  have hCoeffIso :
      ∀ a b : Fin (Fintype.card I),
        (Section1.coeffDot (v a) (v b) : ℂ) =
          Section1.scalarProduct W (omegaCol a - omegaCol 0) (omegaCol b - omegaCol 0) := by
    intro a b
    calc
      (Section1.coeffDot (v a) (v b) : ℂ) =
          Section1.scalarProduct L
            (Section1.evalCoeff muBasis (v a))
            (Section1.evalCoeff muBasis (v b)) := by
              symm
              simpa [muBasis] using
                Section3.irreducibleBasis_scalarProduct_evalCoeff hχfull (v a) (v b)
      _ = Section1.scalarProduct L
            (Section1.inducedCF W (omegaCol a - omegaCol 0))
            (Section1.inducedCF W (omegaCol b - omegaCol 0)) := by
              rw [← hT a, ← hT b]
      _ = Section1.scalarProduct W
            (omegaCol a - omegaCol 0)
            (omegaCol b - omegaCol 0) := by
              exact inducedCF_isometry_on_wMinusW2_pf43 h42 (hCF a) (hCF b)
  have hNorm :
      ∀ t : Fin (Fintype.card I), t ≠ 0 → Section1.coeffSqNorm (v t) = 2 := by
    intro t ht0
    have hdot : Section1.coeffDot (v t) (v t) = 2 := by
      have hc : ((Section1.coeffDot (v t) (v t) : Int) : ℂ) = 2 := by
        calc
          ((Section1.coeffDot (v t) (v t) : Int) : ℂ) =
              Section1.scalarProduct W (omegaCol t - omegaCol 0) (omegaCol t - omegaCol 0) := hCoeffIso t t
          _ = 2 := difference_norm_eq_two_of_orthonormal_raw_pf43 omegaCol hOrthoRaw ht0
      exact_mod_cast hc
    have hs : ((Section1.coeffSqNorm (v t) : Nat) : Int) = 2 := by
      rw [coeffDot_self_eq_coeffSqNorm_pf43, hdot]
    exact_mod_cast hs
  have hCross :
      ∀ t s : Fin (Fintype.card I), t ≠ 0 → s ≠ 0 → t ≠ s →
        Section1.coeffDot (v t) (v s) = 1 := by
    intro t s ht0 hs0 hts
    have hc : ((Section1.coeffDot (v t) (v s) : Int) : ℂ) = 1 := by
      calc
        ((Section1.coeffDot (v t) (v s) : Int) : ℂ) =
            Section1.scalarProduct W (omegaCol t - omegaCol 0) (omegaCol s - omegaCol 0) := hCoeffIso t s
        _ = 1 := difference_scalar_eq_one_of_orthonormal_raw_pf43 omegaCol hOrthoRaw ht0 hs0 hts
    exact_mod_cast hc
  rcases Section1.proposition_1_4_coeff_lattice htwo d hpos v hzero hDeg hNorm hCross with
    ⟨eps, heps, nu, hnuPairwise, hnu⟩
  let piCol : I → Section1.ClassFunction L := fun i => muBasis (nu (e.symm i))
  refine ⟨Section1.signIntToComplex eps, isSign_of_isSignInt_pf43 heps, piCol, ?_, ?_, ?_⟩
  · intro i
    exact hmuIrr (nu (e.symm i))
  · intro i i' hii
    have hs : e.symm i ≠ e.symm i' := by
      intro hsymm
      apply hii
      simpa using congrArg e hsymm
    have hidx : nu (e.symm i) ≠ nu (e.symm i') := hnuPairwise hs
    exact hmuPairwiseRaw hidx
  · intro i
    calc
      Section1.inducedCF W (ω i j - ω i0 j)
          = Section1.inducedCF W (omegaCol (e.symm i) - omegaCol 0) := by
              simp [omegaCol, he0]
      _ = Section1.evalCoeff muBasis (v (e.symm i)) := hT (e.symm i)
      _ = Section1.evalCoeff muBasis
            (Section1.signedBasisDifference eps (nu 0) (nu (e.symm i))) := by
              rw [hnu (e.symm i)]
      _ = Section1.signIntToComplex eps • (muBasis (nu (e.symm i)) - muBasis (nu 0)) := by
              exact evalCoeff_signedBasisDifference_pf43 muBasis eps (nu 0) (nu (e.symm i))
      _ = Section1.signIntToComplex eps • (piCol i - piCol i0) := by
              simp [piCol, he0symm]

private theorem exists_character_family_columnwise_pf43
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    ∃ deltaSign : J → ℂ, ∃ piChar : I → J → Section1.ClassFunction L,
      (∀ j, Section1.IsSign (deltaSign j)) ∧
      (∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j)) ∧
      (∀ j i i', i ≠ i' → piChar i j ≠ piChar i' j) ∧
      (∀ i j,
        Section1.inducedCF W (ω i j - ω i0 j) =
          deltaSign j • (piChar i j - piChar i0 j)) := by
  classical
  have hcol :
      ∀ j : J,
        ∃ eps : ℂ, Section1.IsSign eps ∧
          ∃ piCol : I → Section1.ClassFunction L,
            (∀ i, Section1.IsIrreducibleCharacterOnGroup (piCol i)) ∧
            (∀ i i', i ≠ i' → piCol i ≠ piCol i') ∧
            ∀ i, Section1.inducedCF W (ω i j - ω i0 j) = eps • (piCol i - piCol i0) := by
    intro j
    exact exists_character_family_fixed_column_pf43 h42 hω j
  let deltaSign : J → ℂ := fun j => Classical.choose (hcol j)
  let piChar : I → J → Section1.ClassFunction L := fun i j =>
    Classical.choose (Classical.choose_spec (hcol j)).2 i
  refine ⟨deltaSign, piChar, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (Classical.choose_spec (hcol j)).1
  · intro i j
    exact (Classical.choose_spec (Classical.choose_spec (hcol j)).2).1 i
  · intro j i i' hii
    exact (Classical.choose_spec (Classical.choose_spec (hcol j)).2).2.1 i i' hii
  · intro i j
    exact (Classical.choose_spec (Classical.choose_spec (hcol j)).2).2.2 i

private noncomputable def uliftRepresentation_pf43
    {G : Type u} [Group G] {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    Representation ℂ G (ULift.{u} V) := by
  let e : V ≃ₗ[ℂ] ULift.{u} V := ULift.moduleEquiv.symm
  refine
    { toFun := fun g => e.conj (ρ g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply, map_mul] }

private theorem uliftRepresentation_pf43_character
    {G : Type u} [Group G] {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (uliftRepresentation_pf43 (G := G) (V := V) ρ).character g = ρ.character g := by
  dsimp [uliftRepresentation_pf43, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := ULift.{u} V) (ρ g) (ULift.moduleEquiv.symm)

private theorem isBookIrreducibleCharacter_of_group_irreducible_pf43
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsBookIrreducibleCharacter χ := by
  rcases hχ with ⟨n, ρ, hirr, hchar⟩
  constructor
  · refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
      uliftRepresentation_pf43 (G := G) (V := Fin n → ℂ) ρ, ?_⟩
    ext g
    simpa [hchar] using
      (uliftRepresentation_pf43_character
        (G := G) (V := Fin n → ℂ) (ρ := ρ) g).symm
  · rw [Section1.IsIrreducibleCharacter]
    have hρclass : Section1.IsClassFunction ρ.character := by
      intro x g
      simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
    have htoeq :
        Section1.toConjClassFunction ρ.character hρclass =
          Theory.Character.characterClassFunction ρ := by
      apply Section1.toConjClassFunction_eq_of_apply
      intro g
      rfl
    calc
      Section1.scalarProduct G χ χ =
          Section1.scalarProduct G ρ.character ρ.character := by rw [hchar]
      _ = Theory.Character.classFunctionInner
          (Section1.toConjClassFunction ρ.character hρclass)
          (Section1.toConjClassFunction ρ.character hρclass) :=
        (Section1.classFunctionInner_toConjClassFunction
          ρ.character ρ.character hρclass hρclass).symm
      _ = Theory.Character.classFunctionInner
          (Theory.Character.characterClassFunction ρ)
          (Theory.Character.characterClassFunction ρ) := by rw [htoeq]
      _ = 1 :=
        (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hirr

private theorem scalarProduct_irreducible_self_pf43
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct G χ χ = 1 := by
  have hbook : Section1.IsBookIrreducibleCharacter χ :=
    isBookIrreducibleCharacter_of_group_irreducible_pf43 hχ
  simpa [Section1.IsIrreducibleCharacter] using hbook.2

private theorem scalarProduct_irreducible_ne_pf43
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hneq : χ ≠ ψ) :
    Section1.scalarProduct G χ ψ = 0 := by
  exact Section1.scalarProduct_isBookIrreducible_ne χ ψ
    (isBookIrreducibleCharacter_of_group_irreducible_pf43 hχ)
    (isBookIrreducibleCharacter_of_group_irreducible_pf43 hψ)
    hneq

private theorem signed_irreducible_of_irreducible_pf43
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section3.IsSignedIrreducibleCharacter χ := by
  exact ⟨1, Or.inl rfl, χ, hχ, by simp⟩

private theorem scalarProduct_sign_smul_zero_iff_pf43
    {G : Type u} [Group G] [Finite G]
    {ε η : ℂ} (hε : Section1.IsSign ε) (hη : Section1.IsSign η)
    (φ ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (ε • φ) (η • ψ) = 0 ↔
      Section1.scalarProduct G φ ψ = 0 := by
  rcases hε with rfl | rfl
  · rcases hη with rfl | rfl
    · simp
    · rw [Section1.scalarProduct_smul_right]
      simp
  · rcases hη with rfl | rfl
    · rw [Section1.scalarProduct_smul_left]
      simp
    · rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
      simp

private theorem degree_sign_smul_zero_iff_pf43
    {G : Type u} [One G]
    {ε : ℂ} (hε : Section1.IsSign ε) (φ : Section1.ClassFunction G) :
    Section1.degree (ε • φ) = 0 ↔ Section1.degree φ = 0 := by
  rcases hε with rfl | rfl <;> simp [Section1.degree]

private theorem exists_other_row_pf43
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    ∃ i : I, i ≠ i0 := by
  have htwo : 2 ≤ Fintype.card I := two_le_card_left_pf43 (h42 := h42) hω
  have hI_ne_zero : Fintype.card I ≠ 0 := by
    omega
  letI : NeZero (Fintype.card I) := ⟨hI_ne_zero⟩
  let e : Fin (Fintype.card I) ≃ I := equivFinWithBase_pf43 i0
  have hlt : 1 < Fintype.card I := by
    omega
  refine ⟨e ⟨1, hlt⟩, ?_⟩
  intro hi
  have h10 : (⟨1, hlt⟩ : Fin (Fintype.card I)) = 0 := by
    apply e.injective
    simp [e, equivFinWithBase_apply_zero_pf43 (a0 := i0), hi]
  have : (1 : ℕ) = 0 := by
    simpa using congrArg Fin.val h10
  omega

private theorem omegaRowDifference_cross_column_scalarProduct_zero_pf43
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i i' : I} {j j' : J} (hj : j ≠ j') :
    Section1.scalarProduct W (ω i j - ω i0 j) (ω i' j' - ω i0 j') = 0 := by
  have hij : Section1.scalarProduct W (ω i j) (ω i' j') = 0 := by
    have hneq : (i, j) ≠ (i', j') := by
      intro h
      exact hj (congrArg Prod.snd h)
    simpa [hneq] using
      Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (i, j) (i', j')
  have hi0j : Section1.scalarProduct W (ω i j) (ω i0 j') = 0 := by
    have hneq : (i, j) ≠ (i0, j') := by
      intro h
      exact hj (congrArg Prod.snd h)
    simpa [hneq] using
      Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (i, j) (i0, j')
  have h0ij : Section1.scalarProduct W (ω i0 j) (ω i' j') = 0 := by
    have hneq : (i0, j) ≠ (i', j') := by
      intro h
      exact hj (congrArg Prod.snd h)
    simpa [hneq] using
      Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (i0, j) (i', j')
  have h0i0j : Section1.scalarProduct W (ω i0 j) (ω i0 j') = 0 := by
    have hneq : (i0, j) ≠ (i0, j') := by
      intro h
      exact hj (congrArg Prod.snd h)
    simpa [hneq] using
      Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (i0, j) (i0, j')
  calc
    Section1.scalarProduct W (ω i j - ω i0 j) (ω i' j' - ω i0 j') =
        Section1.scalarProduct W (ω i j) (ω i' j' - ω i0 j') -
          Section1.scalarProduct W (ω i0 j) (ω i' j' - ω i0 j') := by
            rw [scalarProduct_sub_left_pf43]
    _ = (Section1.scalarProduct W (ω i j) (ω i' j') -
          Section1.scalarProduct W (ω i j) (ω i0 j')) -
        (Section1.scalarProduct W (ω i0 j) (ω i' j') -
          Section1.scalarProduct W (ω i0 j) (ω i0 j')) := by
            rw [scalarProduct_sub_right_pf43, scalarProduct_sub_right_pf43]
    _ = 0 := by
          simp [hij, hi0j, h0ij, h0i0j]

private theorem character_column_difference_cross_zero_pf43
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {deltaSign : J → ℂ}
    {piChar : I → J → Section1.ClassFunction L}
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsign : ∀ j, Section1.IsSign (deltaSign j))
    (hind :
      ∀ i j,
        Section1.inducedCF W (ω i j - ω i0 j) =
          deltaSign j • (piChar i j - piChar i0 j))
    {i i' : I} {j j' : J} (hj : j ≠ j') :
    Section1.scalarProduct L (piChar i j - piChar i0 j) (piChar i' j' - piChar i0 j') = 0 := by
  have hCF1 :
      Section2.CFOn W ((W : Set L) \ (W2 : Set L)) (ω i j - ω i0 j) := by
    exact omegaRowDifference_CFOn_wMinusW2_pf43
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω i j
  have hCF2 :
      Section2.CFOn W ((W : Set L) \ (W2 : Set L)) (ω i' j' - ω i0 j') := by
    exact omegaRowDifference_CFOn_wMinusW2_pf43
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω i' j'
  have hzeroL :
      Section1.scalarProduct L
          (Section1.inducedCF W (ω i j - ω i0 j))
          (Section1.inducedCF W (ω i' j' - ω i0 j')) = 0 := by
    rw [inducedCF_isometry_on_wMinusW2_pf43 h42 hCF1 hCF2]
    exact omegaRowDifference_cross_column_scalarProduct_zero_pf43
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hj
  rw [hind i j, hind i' j'] at hzeroL
  exact (scalarProduct_sign_smul_zero_iff_pf43 (hsign j) (hsign j')
    (piChar i j - piChar i0 j) (piChar i' j' - piChar i0 j')).mp hzeroL

private theorem character_column_difference_degree_zero_pf43
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {deltaSign : J → ℂ}
    {piChar : I → J → Section1.ClassFunction L}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsign : ∀ j, Section1.IsSign (deltaSign j))
    (hind :
      ∀ i j,
        Section1.inducedCF W (ω i j - ω i0 j) =
          deltaSign j • (piChar i j - piChar i0 j))
    (i : I) (j : J) :
    Section1.degree (piChar i j - piChar i0 j) = 0 := by
  have hzero :
      Section1.degree (Section1.inducedCF W (ω i j - ω i0 j)) = 0 := by
    exact degree_inducedCF_omegaRowDifference_eq_zero_pf43
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω i j
  rw [hind i j] at hzero
  exact (degree_sign_smul_zero_iff_pf43 (hsign j) (piChar i j - piChar i0 j)).mp hzero

private theorem pairwiseOrthogonal4_cross_columns_pf43
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {deltaSign : J → ℂ}
    {piChar : I → J → Section1.ClassFunction L}
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsign : ∀ j, Section1.IsSign (deltaSign j))
    (hirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j))
    (hdistinct : ∀ j i i', i ≠ i' → piChar i j ≠ piChar i' j)
    (hind :
      ∀ i j,
        Section1.inducedCF W (ω i j - ω i0 j) =
          deltaSign j • (piChar i j - piChar i0 j))
    {i i' : I} {j j' : J}
    (hi : i ≠ i0) (hi' : i' ≠ i0) (hj : j ≠ j') :
    pairwiseOrthogonal4 (piChar i j) (piChar i0 j) (piChar i' j') (piChar i0 j') := by
  exact proposition_4_1
    (α := piChar i j) (β := piChar i0 j)
    (γ := piChar i' j') (δ := piChar i0 j')
    (u := 1) (v := 1)
    (signed_irreducible_of_irreducible_pf43 (hirr i j))
    (signed_irreducible_of_irreducible_pf43 (hirr i0 j))
    (signed_irreducible_of_irreducible_pf43 (hirr i' j'))
    (signed_irreducible_of_irreducible_pf43 (hirr i0 j'))
    (by norm_num)
    (by norm_num)
    (scalarProduct_irreducible_ne_pf43 (hirr i j) (hirr i0 j) (hdistinct j i i0 hi))
    (scalarProduct_irreducible_ne_pf43 (hirr i' j') (hirr i0 j') (hdistinct j' i' i0 hi'))
    (by
      simpa using character_column_difference_cross_zero_pf43
        (K := K) (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0)
        (ω := ω) (deltaSign := deltaSign) (piChar := piChar)
        h42 hω hsign hind hj)
    (character_column_difference_degree_zero_pf43
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (deltaSign := deltaSign) (piChar := piChar)
      hω hsign hind i j)
    (by
      simpa using character_column_difference_degree_zero_pf43
        (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0)
        (ω := ω) (deltaSign := deltaSign) (piChar := piChar)
        hω hsign hind i' j')

private theorem scalarProduct_cross_columns_zero_pf43
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {deltaSign : J → ℂ}
    {piChar : I → J → Section1.ClassFunction L}
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsign : ∀ j, Section1.IsSign (deltaSign j))
    (hirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j))
    (hdistinct : ∀ j i i', i ≠ i' → piChar i j ≠ piChar i' j)
    (hind :
      ∀ i j,
        Section1.inducedCF W (ω i j - ω i0 j) =
          deltaSign j • (piChar i j - piChar i0 j))
    {i i' : I} {j j' : J} (hj : j ≠ j') :
    Section1.scalarProduct L (piChar i j) (piChar i' j') = 0 := by
  obtain ⟨k, hk⟩ := exists_other_row_pf43
    (K := K) (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h42 hω
  by_cases hi : i = i0
  · subst i
    by_cases hi' : i' = i0
    · subst i'
      rcases pairwiseOrthogonal4_cross_columns_pf43
          (K := K) (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (i0 := i0) (j0 := j0)
          (ω := ω) (deltaSign := deltaSign) (piChar := piChar)
          h42 hω hsign hirr hdistinct hind hk hk hj with
        ⟨_, _, _, _, hβδ, _⟩
      exact hβδ
    · rcases pairwiseOrthogonal4_cross_columns_pf43
          (K := K) (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (i0 := i0) (j0 := j0)
          (ω := ω) (deltaSign := deltaSign) (piChar := piChar)
          h42 hω hsign hirr hdistinct hind hk hi' hj with
        ⟨_, _, _, hβγ, _, _⟩
      exact hβγ
  · by_cases hi' : i' = i0
    · subst i'
      rcases pairwiseOrthogonal4_cross_columns_pf43
          (K := K) (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (i0 := i0) (j0 := j0)
          (ω := ω) (deltaSign := deltaSign) (piChar := piChar)
          h42 hω hsign hirr hdistinct hind hi hk hj with
        ⟨_, _, hαδ, _, _, _⟩
      exact hαδ
    · rcases pairwiseOrthogonal4_cross_columns_pf43
          (K := K) (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (i0 := i0) (j0 := j0)
          (ω := ω) (deltaSign := deltaSign) (piChar := piChar)
          h42 hω hsign hirr hdistinct hind hi hi' hj with
        ⟨_, hαγ, _, _, _, _⟩
      exact hαγ


/-- In a PF `(4.3)(b)`-style table, the induced row-difference formula,
irreducibility, and same-column row distinctness imply cross-column
orthogonality. -/
public theorem theorem_4_3_b_cross_column_scalarProduct_zero_of_induced_row_differences
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (piChar : I → J → Section1.ClassFunction L)
    (deltaSign : J → ℂ)
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsign : ∀ j, Section1.IsSign (deltaSign j))
    (hirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j))
    (hdistinct : ∀ j i i', i ≠ i' → piChar i j ≠ piChar i' j)
    (hind :
      ∀ i j,
        Section1.inducedCF W (ω i j - ω i0 j) =
          deltaSign j • (piChar i j - piChar i0 j))
    {i i' : I} {j j' : J} (hj : j ≠ j') :
    Section1.scalarProduct L (piChar i j) (piChar i' j') = 0 :=
  scalarProduct_cross_columns_zero_pf43
    (K := K) (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (deltaSign := deltaSign) (piChar := piChar)
    h42 hω hsign hirr hdistinct hind hj

/-- In one PF `(4.3)(b)` column, any character family satisfying the induced
row-difference formula has distinct entries in distinct rows. -/
public theorem theorem_4_3_b_same_column_ne_of_induced_row_differences
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (piChar : I → J → Section1.ClassFunction L)
    (deltaSign : J → ℂ)
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (_hsign : ∀ j, Section1.IsSign (deltaSign j))
    (hind :
      ∀ i j,
        Section1.inducedCF W (ω i j - ω i0 j) =
          deltaSign j • (piChar i j - piChar i0 j))
    {i i' : I} {j : J} (hi : i ≠ i') :
    piChar i j ≠ piChar i' j := by
  classical
  intro hEq
  let row : I → Section1.ClassFunction W := fun a => ω a j
  have hOrtho :
      ∀ a b : I,
        Section1.scalarProduct W (row a) (row b) = if a = b then 1 else 0 := by
    intro a b
    simpa [row] using
      Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (a, j) (b, j)
  have hindEq :
      Section1.inducedCF W (ω i j - ω i0 j) =
        Section1.inducedCF W (ω i' j - ω i0 j) := by
    calc
      Section1.inducedCF W (ω i j - ω i0 j) =
          deltaSign j • (piChar i j - piChar i0 j) := hind i j
      _ = deltaSign j • (piChar i' j - piChar i0 j) := by rw [hEq]
      _ = Section1.inducedCF W (ω i' j - ω i0 j) := (hind i' j).symm
  have hCF_i :
      Section2.CFOn W ((W : Set L) \ (W2 : Set L)) (ω i j - ω i0 j) :=
    omegaRowDifference_CFOn_wMinusW2_pf43
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) hω i j
  have hCF_i' :
      Section2.CFOn W ((W : Set L) \ (W2 : Set L)) (ω i' j - ω i0 j) :=
    omegaRowDifference_CFOn_wMinusW2_pf43
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) hω i' j
  have hbaseIndZero :
      Section1.inducedCF W (ω i0 j - ω i0 j) = 0 := by
    have hdiff : (ω i0 j - ω i0 j : Section1.ClassFunction W) = 0 := by
      ext x
      simp
    rw [hdiff]
    ext x
    simp [Section1.inducedCF, Section1.inducedClassFunction]
  by_cases hi0 : i = i0
  · have hi'0 : i' ≠ i0 := by
      intro hi'
      exact hi (hi0.trans hi'.symm)
    have hzero :
        Section1.scalarProduct W (ω i' j - ω i0 j) (ω i' j - ω i0 j) = 0 := by
      calc
        Section1.scalarProduct W (ω i' j - ω i0 j) (ω i' j - ω i0 j) =
            Section1.scalarProduct L
              (Section1.inducedCF W (ω i' j - ω i0 j))
              (Section1.inducedCF W (ω i' j - ω i0 j)) := by
                exact (inducedCF_isometry_on_wMinusW2_pf43 h42 hCF_i' hCF_i').symm
        _ = Section1.scalarProduct L
              (Section1.inducedCF W (ω i j - ω i0 j))
              (Section1.inducedCF W (ω i j - ω i0 j)) := by
                rw [← hindEq]
        _ = Section1.scalarProduct L
              (Section1.inducedCF W (ω i0 j - ω i0 j))
              (Section1.inducedCF W (ω i0 j - ω i0 j)) := by
                simp [hi0]
        _ = 0 := by
              rw [hbaseIndZero]
              simp [Section1.scalarProduct]
    have htwo :
        Section1.scalarProduct W (ω i' j - ω i0 j) (ω i' j - ω i0 j) = 2 := by
      simpa [row] using
        difference_norm_eq_two_of_orthonormal_raw_pf43 row hOrtho hi'0
    have hcontr : (2 : ℂ) = 0 := htwo.symm.trans hzero
    norm_num at hcontr
  · by_cases hi'0 : i' = i0
    · have hzero :
          Section1.scalarProduct W (ω i j - ω i0 j) (ω i j - ω i0 j) = 0 := by
        calc
          Section1.scalarProduct W (ω i j - ω i0 j) (ω i j - ω i0 j) =
              Section1.scalarProduct L
                (Section1.inducedCF W (ω i j - ω i0 j))
                (Section1.inducedCF W (ω i j - ω i0 j)) := by
                  exact (inducedCF_isometry_on_wMinusW2_pf43 h42 hCF_i hCF_i).symm
          _ = Section1.scalarProduct L
                (Section1.inducedCF W (ω i' j - ω i0 j))
                (Section1.inducedCF W (ω i' j - ω i0 j)) := by
                  rw [hindEq]
          _ = Section1.scalarProduct L
                (Section1.inducedCF W (ω i0 j - ω i0 j))
                (Section1.inducedCF W (ω i0 j - ω i0 j)) := by
                  simp [hi'0]
          _ = 0 := by
                rw [hbaseIndZero]
                simp [Section1.scalarProduct]
      have htwo :
          Section1.scalarProduct W (ω i j - ω i0 j) (ω i j - ω i0 j) = 2 := by
        simpa [row] using
          difference_norm_eq_two_of_orthonormal_raw_pf43 row hOrtho hi0
      have hcontr : (2 : ℂ) = 0 := htwo.symm.trans hzero
      norm_num at hcontr
    · have hinner :
          Section1.scalarProduct W (ω i j - ω i0 j) (ω i j - ω i0 j) =
            Section1.scalarProduct W (ω i j - ω i0 j) (ω i' j - ω i0 j) := by
        calc
          Section1.scalarProduct W (ω i j - ω i0 j) (ω i j - ω i0 j) =
              Section1.scalarProduct L
                (Section1.inducedCF W (ω i j - ω i0 j))
                (Section1.inducedCF W (ω i j - ω i0 j)) := by
                  exact (inducedCF_isometry_on_wMinusW2_pf43 h42 hCF_i hCF_i).symm
          _ = Section1.scalarProduct L
                (Section1.inducedCF W (ω i j - ω i0 j))
                (Section1.inducedCF W (ω i' j - ω i0 j)) := by
                  rw [hindEq]
          _ = Section1.scalarProduct W (ω i j - ω i0 j) (ω i' j - ω i0 j) := by
                  exact inducedCF_isometry_on_wMinusW2_pf43 h42 hCF_i hCF_i'
      have htwo :
          Section1.scalarProduct W (ω i j - ω i0 j) (ω i j - ω i0 j) = 2 := by
        simpa [row] using
          difference_norm_eq_two_of_orthonormal_raw_pf43 row hOrtho hi0
      have hone :
          Section1.scalarProduct W (ω i j - ω i0 j) (ω i' j - ω i0 j) = 1 := by
        simpa [row] using
          difference_scalar_eq_one_of_orthonormal_raw_pf43 row hOrtho hi0 hi'0 hi
      have hcontr : (2 : ℂ) = 1 := by
        exact htwo.symm.trans (hinner.trans hone)
      norm_num at hcontr

private theorem pairwiseDistinct_character_table_pf43
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {deltaSign : J → ℂ}
    {piChar : I → J → Section1.ClassFunction L}
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsign : ∀ j, Section1.IsSign (deltaSign j))
    (hirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j))
    (hdistinct : ∀ j i i', i ≠ i' → piChar i j ≠ piChar i' j)
    (hind :
      ∀ i j,
        Section1.inducedCF W (ω i j - ω i0 j) =
          deltaSign j • (piChar i j - piChar i0 j)) :
    ∀ p q : I × J, p ≠ q → piChar p.1 p.2 ≠ piChar q.1 q.2 := by
  intro p q hpq
  by_cases hj : p.2 = q.2
  ·
    have hi : p.1 ≠ q.1 := by
      intro hrow
      apply hpq
      ext <;> simp [hrow, hj]
    simpa [hj] using hdistinct p.2 p.1 q.1 hi
  · intro hEq
    have hzero :
        Section1.scalarProduct L (piChar p.1 p.2) (piChar q.1 q.2) = 0 :=
      scalarProduct_cross_columns_zero_pf43
        (K := K) (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0)
        (ω := ω) (deltaSign := deltaSign) (piChar := piChar)
        h42 hω hsign hirr hdistinct hind hj
    rw [hEq] at hzero
    have hself : Section1.scalarProduct L (piChar q.1 q.2) (piChar q.1 q.2) = 1 :=
      scalarProduct_irreducible_self_pf43 (hirr q.1 q.2)
    have : (1 : ℂ) = 0 := by
      rw [hself] at hzero
      exact hzero
    exact one_ne_zero this

private theorem exists_character_family_global_pf43
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    ∃ deltaSign : J → ℂ, ∃ piChar : I → J → Section1.ClassFunction L,
      (∀ j, Section1.IsSign (deltaSign j)) ∧
      (∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j)) ∧
      (∀ p q : I × J, p ≠ q → piChar p.1 p.2 ≠ piChar q.1 q.2) ∧
      (∀ i j,
        Section1.inducedCF W (ω i j - ω i0 j) =
          deltaSign j • (piChar i j - piChar i0 j)) := by
  rcases exists_character_family_columnwise_pf43
      (K := K) (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h42 hω with
    ⟨deltaSign, piChar, hsign, hirr, hdistinctCol, hind⟩
  refine ⟨deltaSign, piChar, hsign, hirr, ?_, hind⟩
  exact pairwiseDistinct_character_table_pf43
    (K := K) (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (deltaSign := deltaSign) (piChar := piChar)
    h42 hω hsign hirr hdistinctCol hind

private theorem orthonormal_piChar_table_pf43
    {L : Type u} [Group L] [Finite L]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {piChar : I → J → Section1.ClassFunction L}
    (hirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j))
    (hdistinct : ∀ p q : I × J, p ≠ q → piChar p.1 p.2 ≠ piChar q.1 q.2) :
    ∀ p q : I × J,
      Section1.scalarProduct L (piChar p.1 p.2) (piChar q.1 q.2) =
        if p = q then 1 else 0 := by
  intro p q
  by_cases hpq : p = q
  · subst hpq
    simpa using scalarProduct_irreducible_self_pf43 (hirr p.1 p.2)
  · simpa [hpq] using
      scalarProduct_irreducible_ne_pf43
        (hirr p.1 p.2) (hirr q.1 q.2) (hdistinct p q hpq)

private theorem theorem_4_3_c_values_and_vanishing_pf43
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {deltaSign : J → ℂ}
    {piChar : I → J → Section1.ClassFunction L}
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsign : ∀ j, Section1.IsSign (deltaSign j))
    (hirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j))
    (hdistinct : ∀ p q : I × J, p ≠ q → piChar p.1 p.2 ≠ piChar q.1 q.2)
    (hind :
      ∀ i j,
        Section1.inducedCF W (ω i j - ω i0 j) =
          deltaSign j • (piChar i j - piChar i0 j)) :
    theorem_4_3_c_statement W2 W I J piChar deltaSign ω := by
  classical
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, _hW2, hW, _hodd⟩
  let A : Set W := fun x => (x : L) ∉ W2
  rcases exists_wMinusW2_basis_pf43 W1 W2 W I J i0 j0 ω hW hω with
    ⟨basis, hbasis⟩
  have horth :
      ∀ p q : I × J,
        Section1.scalarProduct L (piChar p.1 p.2) (piChar q.1 q.2) =
          if p = q then 1 else 0 := by
    exact orthonormal_piChar_table_pf43 hirr hdistinct
  have h_expand :
      ∀ p : {p : I × J // p.1 ≠ i0},
        Section1.inducedCFLinear W (basis p : Section1.ClassFunction W) =
          ∑ q : I × J,
            Section1.scalarProduct W
              (basis p : Section1.ClassFunction W)
              (deltaSign q.2 • ω q.1 q.2) •
                piChar q.1 q.2 := by
    intro p
    rcases p with ⟨⟨i, j⟩, hi⟩
    have hcoord :
        ∀ q : I × J,
          Section1.scalarProduct W
            (basis ⟨(i, j), hi⟩ : Section1.ClassFunction W)
            (deltaSign q.2 • ω q.1 q.2) =
              if q = (i, j) then deltaSign j
              else if q = (i0, j) then -deltaSign j else 0 := by
      intro q
      rw [hbasis ⟨(i, j), hi⟩, scalarProduct_smul_right_pf43]
      have hstarq : star (deltaSign q.2) = deltaSign q.2 := by
        exact star_eq_self_of_sign_pf43 (hsign q.2)
      by_cases hqij : q = (i, j)
      · subst hqij
        have hval :
            Section1.scalarProduct W (ω i j - ω i0 j) (ω i j) = 1 := by
          simpa using
            (omegaRowDifference_scalarProduct_omega_pf43
              (W1 := W1) (W2 := W2) (W := W)
              (I := I) (J := J) (i0 := i0) (j0 := j0)
              (ω := ω) hω i j (p := i) (q := j) hi)
        simp [hval, hstarq]
      · by_cases hq0j : q = (i0, j)
        · subst hq0j
          have hcross :
              Section1.scalarProduct W (ω i j) (ω i0 j) = 0 := by
            have hneq : (i, j) ≠ (i0, j) := by
              intro h
              exact hi (congrArg Prod.fst h)
            simpa [hneq] using
                Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (i, j) (i0, j)
          have hself :
              Section1.scalarProduct W (ω i0 j) (ω i0 j) = 1 := by
            simpa using
              Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (i0, j) (i0, j)
          rw [scalarProduct_sub_left_pf43]
          simp [hcross, hself, hstarq, hqij]
        · have hpair : ¬ (i = q.1 ∧ j = q.2) := by
            intro hpair
            apply hqij
            exact Prod.ext hpair.1.symm hpair.2.symm
          by_cases hq0 : q.1 = i0
          · have hneq1 : (i, j) ≠ q := by
              intro h
              apply hqij
              simpa using h.symm
            have hneq2 : (i0, j) ≠ q := by
              intro h
              apply hq0j
              simpa using h.symm
            have h1 : Section1.scalarProduct W (ω i j) (ω q.1 q.2) = 0 := by
              simpa [hneq1] using
                Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (i, j) q
            have h2 : Section1.scalarProduct W (ω i0 j) (ω q.1 q.2) = 0 := by
              simpa [hneq2] using
                Section3.isOrthonormalDoubleFamily_apply hω.orthonormal (i0, j) q
            rw [scalarProduct_sub_left_pf43]
            simp [h1, h2, hstarq, hqij, hq0j]
          · have hωcoord :
                Section1.scalarProduct W (ω i j - ω i0 j) (ω q.1 q.2) =
                  if i = q.1 ∧ j = q.2 then 1 else 0 := by
              exact omegaRowDifference_scalarProduct_omega_pf43
                (W1 := W1) (W2 := W2) (W := W)
                (I := I) (J := J) (i0 := i0) (j0 := j0)
                (ω := ω) hω i j (p := q.1) (q := q.2) hq0
            rw [hωcoord]
            simp [hpair, hqij, hq0j]
    calc
      Section1.inducedCFLinear W (basis ⟨(i, j), hi⟩ : Section1.ClassFunction W) =
          Section1.inducedCF W (basis ⟨(i, j), hi⟩ : Section1.ClassFunction W) := by
            rw [Section1.inducedCFLinear_apply]
      _ = Section1.inducedCF W (ω i j - ω i0 j) := by
            rw [hbasis ⟨(i, j), hi⟩]
      _ = deltaSign j • (piChar i j - piChar i0 j) := by
            rw [hind i j]
      _ =
          ∑ q : I × J,
            Section1.scalarProduct W
              (basis ⟨(i, j), hi⟩ : Section1.ClassFunction W)
              (deltaSign q.2 • ω q.1 q.2) •
                piChar q.1 q.2 := by
            have hsum :
                (∑ x : I × J,
                  if x = (i, j) then deltaSign j • piChar x.1 x.2
                  else if x = (i0, j) then -(deltaSign j • piChar x.1 x.2) else 0) =
                  deltaSign j • piChar i j + -(deltaSign j • piChar i0 j) := by
              ext g
              have h1 :
                  (∑ x : I × J,
                    if x = (i, j) then deltaSign j * piChar x.1 x.2 g else 0) =
                      deltaSign j * piChar i j g := by
                simp
              have h2 :
                  (∑ x : I × J,
                    if x = (i0, j) then -(deltaSign j * piChar x.1 x.2 g) else 0) =
                      -(deltaSign j * piChar i0 j g) := by
                simp
              have hsplit :
                  (∑ c : I × J,
                    (if c = (i, j) then deltaSign j • piChar c.1 c.2
                    else if c = (i0, j) then -(deltaSign j • piChar c.1 c.2) else 0) g) =
                    (∑ x : I × J,
                      if x = (i, j) then deltaSign j * piChar x.1 x.2 g else (0 : ℂ)) +
                    ∑ x : I × J,
                      if x = (i0, j) then -(deltaSign j * piChar x.1 x.2 g) else (0 : ℂ) := by
                let f : I × J → ℂ := fun c =>
                  (if c = (i, j) then deltaSign j • piChar c.1 c.2
                    else if c = (i0, j) then -(deltaSign j • piChar c.1 c.2) else 0) g
                let f1 : I × J → ℂ := fun x =>
                  if x = (i, j) then deltaSign j * piChar x.1 x.2 g else 0
                let f2 : I × J → ℂ := fun x =>
                  if x = (i0, j) then -(deltaSign j * piChar x.1 x.2 g) else 0
                have hf : f = fun x => f1 x + f2 x := by
                  funext x
                  by_cases hxij : x = (i, j)
                  · simp [f, f1, f2, hxij, hi]
                  · by_cases hx0j : x = (i0, j)
                    · have hne : i0 ≠ i := by
                        intro hEq
                        apply hxij
                        simpa [hEq] using hx0j
                      simp [f, f1, f2, hx0j, hne]
                    · simp [f, f1, f2, hxij, hx0j]
                calc
                  ∑ c : I × J, f c = ∑ c : I × J, (f1 c + f2 c) := by rw [hf]
                  _ = (∑ c : I × J, f1 c) + ∑ c : I × J, f2 c := by
                        rw [Finset.sum_add_distrib]
              simpa using hsplit.trans (by rw [h1, h2])
            have hsum' :
                (∑ x : I × J,
                  if x = (i, j) then deltaSign j • piChar x.1 x.2
                  else if x = (i0, j) then -(deltaSign j • piChar x.1 x.2) else 0) =
                  deltaSign j • (piChar i j - piChar i0 j) := by
              simpa [sub_eq_add_neg, smul_sub] using hsum
            have hcoordsum :
                (∑ q : I × J,
                  Section1.scalarProduct W
                    (basis ⟨(i, j), hi⟩ : Section1.ClassFunction W)
                    (deltaSign q.2 • ω q.1 q.2) •
                      piChar q.1 q.2) =
                  (∑ x : I × J,
                    if x = (i, j) then deltaSign j • piChar x.1 x.2
                    else if x = (i0, j) then -(deltaSign j • piChar x.1 x.2)
                    else (0 : Section1.ClassFunction L)) := by
              ext g
              simp [hcoord]
            calc
              deltaSign j • (piChar i j - piChar i0 j) =
                  (∑ x : I × J,
                    if x = (i, j) then deltaSign j • piChar x.1 x.2
                    else if x = (i0, j) then -(deltaSign j • piChar x.1 x.2)
                    else (0 : Section1.ClassFunction L)) := hsum'.symm
              _ =
                  ∑ q : I × J,
                    Section1.scalarProduct W
                      (basis ⟨(i, j), hi⟩ : Section1.ClassFunction W)
                      (deltaSign q.2 • ω q.1 q.2) •
                        piChar q.1 q.2 := hcoordsum.symm
  constructor
  · intro i j x hx
    have hchiClass : Section1.IsClassFunction (piChar i j) :=
      isClassFunction_of_irreducibleCharacterOnGroup_pf43 (hirr i j)
    have hfrob_ij :
        ∀ α0,
          Section1.scalarProduct L (Section1.inducedCFLinear W α0) (piChar i j) =
            Section1.scalarProduct W α0 (Section1.subgroupRestriction W (piChar i j)) := by
      intro α0
      rw [Section1.inducedCFLinear_apply]
      exact Section1.scalarProduct_inducedCF_left W α0 (piChar i j) hchiClass
    have hEq :
        ∀ y ∈ A,
          Section1.subgroupRestriction W (piChar i j) y =
            (∑ k : I × J, (if k = (i, j) then (1 : ℂ) else 0) •
              (deltaSign k.2 • ω k.1 k.2)) y := by
      refine (proposition_1_3_a_special_pf43
        (basis := basis)
        (chi := fun k : I × J => deltaSign k.2 • ω k.1 k.2)
        (ind := Section1.inducedCFLinear W)
        (mu := piChar i j)
        (hfrob := hfrob_ij)
        (d := fun k : I × J => if k = (i, j) then (1 : ℂ) else 0)).mpr ?_
      intro j'
      calc
        ∑ k : I × J,
            Section1.scalarProduct W (basis j' : Section1.ClassFunction W)
              (deltaSign k.2 • ω k.1 k.2) *
                star (if k = (i, j) then (1 : ℂ) else 0) =
          ∑ k : I × J,
            Section1.scalarProduct W (basis j' : Section1.ClassFunction W)
              (deltaSign k.2 • ω k.1 k.2) *
                Section1.scalarProduct L (piChar k.1 k.2) (piChar i j) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              by_cases hkq : k = (i, j)
              · have hkk :
                    Section1.scalarProduct L (piChar i j) (piChar i j) = 1 := by
                  simpa using horth (i, j) (i, j)
                simp [hkq, hkk]
              · have hk0 :
                    Section1.scalarProduct L (piChar k.1 k.2) (piChar i j) = 0 := by
                  simpa [hkq] using horth k (i, j)
                simp [hkq, hk0]
        _ = Section1.scalarProduct L
            (∑ k : I × J,
              Section1.scalarProduct W (basis j' : Section1.ClassFunction W)
                (deltaSign k.2 • ω k.1 k.2) •
                  piChar k.1 k.2) (piChar i j) := by
              rw [scalarProduct_sum_left_pf43]
        _ = Section1.scalarProduct L
            (Section1.inducedCFLinear W (basis j' : Section1.ClassFunction W))
            (piChar i j) := by
              rw [h_expand j']
    have hs :
        (∑ k : I × J, (if k = (i, j) then (1 : ℂ) else 0) •
          (deltaSign k.2 • ω k.1 k.2)) = deltaSign j • ω i j := by
      simp
    have hsumval :
        (∑ k : I × J, (if k = (i, j) then (1 : ℂ) else 0) •
          (deltaSign k.2 • ω k.1 k.2)) ⟨x, hx.1⟩ =
            (deltaSign j • ω i j) ⟨x, hx.1⟩ := by
      simpa using congrArg (fun f : Section1.ClassFunction W => f ⟨x, hx.1⟩) hs
    have hres := (hEq ⟨x, hx.1⟩ hx.2).trans hsumval
    simpa [Section1.subgroupRestriction] using hres
  · intro ψ hψ hnot x hx
    have hψclass : Section1.IsClassFunction ψ :=
      isClassFunction_of_irreducibleCharacterOnGroup_pf43 hψ
    have hfrob_ψ :
        ∀ α0,
          Section1.scalarProduct L (Section1.inducedCFLinear W α0) ψ =
            Section1.scalarProduct W α0 (Section1.subgroupRestriction W ψ) := by
      intro α0
      rw [Section1.inducedCFLinear_apply]
      exact Section1.scalarProduct_inducedCF_left W α0 ψ hψclass
    have horth_to_zero :
        ∀ q : I × J, Section1.scalarProduct L (piChar q.1 q.2) ψ = 0 := by
      intro q
      have hneq : piChar q.1 q.2 ≠ ψ := by
        intro hEq
        apply hnot
        exact ⟨q, by simpa using hEq⟩
      exact scalarProduct_irreducible_ne_pf43 (hirr q.1 q.2) hψ hneq
    have hzero :
        ∀ y ∈ A,
          Section1.subgroupRestriction W ψ y =
            (∑ k : I × J, (0 : ℂ) • (deltaSign k.2 • ω k.1 k.2)) y := by
      refine (proposition_1_3_a_special_pf43
        (basis := basis)
        (chi := fun k : I × J => deltaSign k.2 • ω k.1 k.2)
        (ind := Section1.inducedCFLinear W)
        (mu := ψ)
        (hfrob := hfrob_ψ)
        (d := fun _ : I × J => 0)).mpr ?_
      intro j
      calc
        ∑ k : I × J,
            Section1.scalarProduct W (basis j : Section1.ClassFunction W)
              (deltaSign k.2 • ω k.1 k.2) * star (0 : ℂ) = 0 := by
              simp
        _ = Section1.scalarProduct L
            (∑ k : I × J,
              Section1.scalarProduct W (basis j : Section1.ClassFunction W)
                (deltaSign k.2 • ω k.1 k.2) •
                  piChar k.1 k.2) ψ := by
              rw [scalarProduct_sum_left_pf43]
              simp [horth_to_zero]
        _ = Section1.scalarProduct L
            (Section1.inducedCFLinear W (basis j : Section1.ClassFunction W)) ψ := by
              rw [h_expand j]
    have hs0 :
        (∑ k : I × J, (0 : ℂ) • (deltaSign k.2 • ω k.1 k.2)) = 0 := by
      simp
    have hval := hzero ⟨x, hx.1⟩ hx.2
    simpa [Section1.subgroupRestriction, hs0] using hval

/--
Peterfalvi (4.3)(c): on `W \ W₂`, the characters `Πᵢⱼ` agree with the
`ωᵢⱼ` up to the sign `δⱼ`, and every other irreducible character of `L`
vanishes there.
-/
public theorem theorem_4_3_c
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (deltaSign : J → ℂ)
    (piChar : I → J → Section1.ClassFunction L)
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsign : ∀ j, Section1.IsSign (deltaSign j))
    (hirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j))
    (hdistinct : ∀ p q : I × J, p ≠ q → piChar p.1 p.2 ≠ piChar q.1 q.2)
    (hind :
      ∀ i j,
        Section1.inducedCF W (ω i j - ω i0 j) =
          deltaSign j • (piChar i j - piChar i0 j)) :
    theorem_4_3_c_statement W2 W I J piChar deltaSign ω := by
  exact theorem_4_3_c_values_and_vanishing_pf43
    (K := K) (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (deltaSign := deltaSign) (piChar := piChar)
    h42 hω hsign hirr hdistinct hind

private theorem sign_mul_self_eq_one_pf43
    {ε : ℂ} (hε : Section1.IsSign ε) :
    ε * ε = 1 := by
  rcases hε with rfl | rfl <;> norm_num

private theorem sign_smul_sign_smul_eq_self_pf43
    {G : Type*} {φ : Section1.ClassFunction G}
    {ε : ℂ} (hε : Section1.IsSign ε) :
    ε • (ε • φ) = φ := by
  ext g
  change ε * (ε * φ g) = φ g
  calc
    ε * (ε * φ g) = (ε * ε) * φ g := by rw [← mul_assoc]
    _ = φ g := by simp [sign_mul_self_eq_one_pf43 hε]

private theorem isVirtualCharacter_zsmul_pf43
    {G : Type u} [Group G] (n : ℤ) {χ : G → ℂ}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter (n • χ) := by
  classical
  rcases hχ with ⟨r, m, k, ρ, rfl⟩
  refine ⟨r, fun i => n * m i, k, ρ, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations, Finset.mul_sum, mul_assoc]

private theorem isVirtualCharacter_finset_sum_pf43
    {G : Type u} [Group G] {ι : Type*} [Fintype ι]
    (s : Finset ι) (χ : ι → G → ℂ)
    (hχ : ∀ i ∈ s, Theory.Character.IsVirtualCharacter (χ i)) :
    Theory.Character.IsVirtualCharacter (fun g => ∑ i ∈ s, χ i g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, (fun i : Fin 0 => nomatch i), (fun i : Fin 0 => nomatch i),
        (fun i : Fin 0 => nomatch i), ?_⟩
      ext g
      simp [Theory.Character.virtualCharacterOfRepresentations]
  | @insert i s hi hs =>
      have htail :
          Theory.Character.IsVirtualCharacter (fun g => ∑ j ∈ s, χ j g) := by
        exact hs (by
          intro j hj
          exact hχ j (by simp [hj]))
      have hheadTail := Section3.isVirtualCharacter_add (hχ i (by simp)) htail
      convert hheadTail using 1
      ext g
      simp [hi]

private theorem isVirtualCharacter_subgroupRestriction_pf43
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) {χ : Section1.ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter (Section1.subgroupRestriction H χ) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  refine ⟨r, m, n, fun i => (ρ i).comp H.subtype, ?_⟩
  ext h
  simp [Theory.Character.virtualCharacterOfRepresentations, Section1.subgroupRestriction,
    Representation.character]

private theorem isVirtualCharacter_sign_smul_pf43
    {G : Type u} [Group G] {χ : G → ℂ}
    {ε : ℂ} (hε : Section1.IsSign ε)
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter (ε • χ) := by
  rcases hε with rfl | rfl
  · simpa using hχ
  · simpa using Section3.isVirtualCharacter_neg hχ

private theorem isClassFunction_of_signedIrreducible_pf43
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.IsClassFunction χ := by
  rcases hχ with ⟨ε, hε, ψ, hψ, rfl⟩
  exact Section3.isVirtualCharacter_isClassFunction
    (isVirtualCharacter_sign_smul_pf43 hε
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hψ))

private theorem mapsVirtualCharacters_sigmaOfPF35_pf43
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction L}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (χ i j)) :
    Section3.MapsVirtualCharacters (Section3.sigmaOfPF35 ω χ) := by
  intro α hα
  have hint :
      ∀ p : I × J,
        ∃ z : ℤ,
          Section1.scalarProduct W α (ω p.1 p.2) = (z : ℂ) := by
    intro p
    exact Section3.scalarProduct_isVirtualCharacter_eq_int hα
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hω.irreducible p.1 p.2))
  have hterm :
      ∀ p : I × J,
        Theory.Character.IsVirtualCharacter
          (Section1.scalarProduct W α (ω p.1 p.2) • χ p.1 p.2) := by
    intro p
    rcases hint p with ⟨z, hz⟩
    rw [hz]
    have hχvirt : Theory.Character.IsVirtualCharacter (χ p.1 p.2) := by
      rcases hsigned p.1 p.2 with ⟨ε, hε, ψ, hψ, hEq⟩
      rcases hε with rfl | rfl
      · simpa [hEq] using Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hψ
      · simpa [hEq] using Section3.isVirtualCharacter_neg
          (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hψ)
    have hsmul :
        (z : ℂ) • χ p.1 p.2 =
          (z • χ p.1 p.2 : Section1.ClassFunction L) := by
      ext g
      simp [zsmul_eq_mul]
    rw [hsmul]
    exact isVirtualCharacter_zsmul_pf43 z hχvirt
  have hsum :
      Theory.Character.IsVirtualCharacter
        (Section1.weightedFamilySum
          (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
          (fun p : I × J => χ p.1 p.2)) := by
    unfold Section1.weightedFamilySum
    rw [show (@Finset.univ (I × J) (Fintype.ofFinite (I × J))) =
        (Finset.univ : Finset (I × J)) by
      ext p
      simp]
    simpa using
      isVirtualCharacter_finset_sum_pf43
        (G := L)
        (s := (Finset.univ : Finset (I × J)))
        (χ := fun p => Section1.scalarProduct W α (ω p.1 p.2) • χ p.1 p.2)
        (by
          intro p _hp
          exact hterm p)
  simpa [Section3.sigmaOfPF35] using hsum

private theorem sigmaOfPF35_eq_inducedCF_on_CFOn_pf43
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction L}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (_horth : Section3.IsOrthonormalDoubleFamily χ)
    (_hsigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter L)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (Section3.alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter L - χ i j0 - χ i0 j + χ i j)
    (α : Section1.ClassFunction W)
    (hα : Section2.CFOn W (Section3.cyclicTISet W1 W2 W) α) :
    Section3.sigmaOfPF35 ω χ α = Section1.inducedCF W α := by
  classical
  let σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L :=
    Section3.sigmaOfPF35 ω χ
  have hσ_omega : ∀ i j, σ (ω i j) = χ i j := by
    intro i j
    simpa [σ] using Section3.sigmaOfPF35_apply_omega ω χ hω.orthonormal i j
  have hαbasis := Section3.proposition_3_4
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0) (omega := ω) h31 hω
  rcases hαbasis.2.2 α hα with ⟨c, rfl⟩
  have hbase :
      ∀ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
        σ (Section3.alphaIJ W i0 j0 ω p.1.1 p.1.2) =
          Section1.inducedCF W (Section3.alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
    rintro ⟨⟨i, j⟩, hi, hj⟩
    have hσprincipal : σ (Section1.principalCharacter W) = Section1.principalCharacter L := by
      calc
        σ (Section1.principalCharacter W) = σ (ω i0 j0) := by rw [hω.principal]
        _ = χ i0 j0 := hσ_omega i0 j0
        _ = Section1.principalCharacter L := h00
    calc
      σ (Section3.alphaIJ W i0 j0 ω i j) =
          σ (Section1.principalCharacter W) - σ (ω i j0) - σ (ω i0 j) + σ (ω i j) := by
        simp [Section3.alphaIJ, map_sub, map_add]
      _ = Section1.principalCharacter L - χ i j0 - χ i0 j + χ i j := by
        rw [hσprincipal, hσ_omega i j0, hσ_omega i0 j, hσ_omega i j]
      _ = Section1.inducedCF W (Section3.alphaIJ W i0 j0 ω i j) := by
        symm
        exact hInd i j hi hj
  calc
    σ (∑ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
        c p • Section3.alphaIJ W i0 j0 ω p.1.1 p.1.2) =
      ∑ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
        c p • σ (Section3.alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro p hp
          simp
    _ =
      ∑ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
        c p • Section1.inducedCF W (Section3.alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [hbase p]
    _ =
      Section1.inducedCFLinear W
        (∑ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
          c p • Section3.alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro p hp
        exact (map_smul (Section1.inducedCFLinear W) (c p)
          (Section3.alphaIJ W i0 j0 ω p.1.1 p.1.2)).symm
    _ =
      Section1.inducedCF W
        (∑ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
          c p • Section3.alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
        rfl

private theorem theorem_4_3_b_sigma_identification_pf43
    {L : Type u} [Group L] [Finite L]
    (W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (deltaSign : J → ℂ)
    (piChar : I → J → Section1.ClassFunction L)
    (χ : I → J → Section1.ClassFunction L)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsign : ∀ j, Section1.IsSign (deltaSign j))
    (hirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j))
    (hC : theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (horth : Section3.IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter L)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (Section3.alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter L - χ i j0 - χ i0 j + χ i j) :
    ∀ i j, Section3.sigmaOfPF35 ω χ (ω i j) = deltaSign j • piChar i j := by
  intro i j
  have hX :
      Section3.IsSignedIrreducibleCharacter (deltaSign j • piChar i j) := by
    exact ⟨deltaSign j, hsign j, piChar i j, hirr i j, rfl⟩
  have hXV :
      ∀ x : L, ∀ hx : x ∈ Section3.cyclicTISet W1 W2 W,
        (deltaSign j • piChar i j) x =
          ω i j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
    intro x hx
    have hxWm : x ∈ ((W : Set L) \ (W2 : Set L)) := by
      exact ⟨Section3.cyclicTISet_subset W1 W2 W hx,
        Section3.cyclicTISet_not_mem_right W1 W2 W hx⟩
    have hval := hC.1 i j x hxWm
    change deltaSign j * piChar i j x =
      ω i j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩
    calc
      deltaSign j * piChar i j x =
          deltaSign j *
            (deltaSign j * ω i j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩) := by
              rw [hval]
      _ =
          (deltaSign j * deltaSign j) *
            ω i j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
              rw [mul_assoc]
      _ = ω i j ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
        simp [sign_mul_self_eq_one_pf43 (hsign j)]
  exact
    (Section3.proposition_3_9_a_uniqueness_of_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ)
      h31 hω horth hsigned h00 hInd
      (hω.irreducible i j) hX hXV).symm

/--
Peterfalvi (4.3)(b): there are signs `δⱼ`, irreducible characters `Πᵢⱼ`,
and a sec3 Dade isometry `σ` such that the induced row-difference formula and
the image formula `σ(ωᵢⱼ) = δⱼ • Πᵢⱼ` both hold.
-/
public theorem theorem_4_3_b
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L,
      ∃ piChar : I → J → Section1.ClassFunction L,
        ∃ deltaSign : J → ℂ,
          theorem_4_3_b_statement W1 W2 W I J i0 j0 ω σ piChar deltaSign hω := by
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
    (theorem_4_3_a K W1 W2 W h42).2
  rcases exists_character_family_global_pf43
      (K := K) (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) h42 hω with
    ⟨deltaSign, piChar, hsign, hirr, hdistinct, hind⟩
  have hC : theorem_4_3_c_statement W2 W I J piChar deltaSign ω :=
    theorem_4_3_c K W1 W2 W I J i0 j0 ω deltaSign piChar
      h42 hω hsign hirr hdistinct hind
  rcases Section3.proposition_3_9_a_uniqueness
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) h31 hω with
    ⟨χ, horth, _hvirt, hsigned, h00, hInd, _huniq⟩
  let σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L :=
    Section3.sigmaOfPF35 ω χ
  have hSigma : ∀ i j, σ (ω i j) = deltaSign j • piChar i j := by
    intro i j
    simpa [σ] using theorem_4_3_b_sigma_identification_pf43
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (deltaSign := deltaSign) (piChar := piChar) (χ := χ)
      h31 hω hsign hirr hC horth hsigned h00 hInd i j
  have hσmap : Section3.theorem_3_2_map_statement W1 W2 W σ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [σ] using Section3.sigmaOfPF35_isCFLinearIsometry_of_pf35
        (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h31 hω horth hsigned h00 hInd
    · simpa [σ] using mapsVirtualCharacters_sigmaOfPF35_pf43
        (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) hω hsigned
    · intro α hα
      simpa [σ] using sigmaOfPF35_eq_inducedCF_on_CFOn_pf43
        (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h31 hω horth hsigned h00 hInd α hα
    · intro α _hα x g
      change
        Section1.weightedFamilySum
            (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
            (fun p : I × J => χ p.1 p.2) (x * g * x⁻¹) =
          Section1.weightedFamilySum
            (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
            (fun p : I × J => χ p.1 p.2) g
      unfold Section1.weightedFamilySum
      refine Finset.sum_congr rfl ?_
      intro p _hp
      have hχclass : Section1.IsClassFunction (χ p.1 p.2) :=
        isClassFunction_of_signedIrreducible_pf43 (hsigned p.1 p.2)
      simp [hχclass x g]
    · calc
        σ (Section1.principalCharacter W) = σ (ω i0 j0) := by rw [hω.principal]
        _ = χ i0 j0 := by
          simpa [σ] using Section3.sigmaOfPF35_apply_omega ω χ hω.orthonormal i0 j0
        _ = Section1.principalCharacter L := h00
    · simpa [σ] using Section3.sigmaOfPF35_agreesOnCyclicTISet_of_pf35
        (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h31 hω horth hsigned h00 hInd
    · intro ψ hψ hnot
      have hnotPi :
          ψ ∉ Set.range (fun p : I × J => piChar p.1 p.2) := by
        intro hpi
        rcases hpi with ⟨p, rfl⟩
        apply hnot
        have hpreclass :
            Section1.IsClassFunction (deltaSign p.2 • ω p.1 p.2) := by
          intro x g
          simp [hω.is_class p.1 p.2 x g]
        refine ⟨⟨deltaSign p.2 • ω p.1 p.2, hpreclass⟩, ?_⟩
        calc
          σ (deltaSign p.2 • ω p.1 p.2) = deltaSign p.2 • σ (ω p.1 p.2) := by
            rw [map_smul]
          _ = deltaSign p.2 • (deltaSign p.2 • piChar p.1 p.2) := by
            rw [hSigma p.1 p.2]
          _ = piChar p.1 p.2 := sign_smul_sign_smul_eq_self_pf43 (hsign p.2)
      have hvan := hC.2 ψ hψ hnotPi
      intro x hx
      exact hvan x ⟨Section3.cyclicTISet_subset W1 W2 W hx,
        Section3.cyclicTISet_not_mem_right W1 W2 W hx⟩
  refine ⟨σ, piChar, deltaSign, ?_⟩
  exact ⟨hσmap, hsign, hirr, hdistinct, hind, hSigma⟩

/--
Peterfalvi (4.3)(d): every degree `Πᵢⱼ(1)` is congruent to `δⱼ` modulo
`|W₁|`, encoded by an explicit integral correction term.
-/
public theorem theorem_4_3_d
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (deltaSign : J → ℂ)
    (piChar : I → J → Section1.ClassFunction L)
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsign : ∀ j, Section1.IsSign (deltaSign j))
    (hirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j))
    (hC : theorem_4_3_c_statement W2 W I J piChar deltaSign ω) :
    theorem_4_3_d_statement W1 I J piChar deltaSign := by
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, hW1, _hW2, hW, _hodd⟩
  let Hsub : Subgroup W := W1.subgroupOf W
  have hcardSub : Nat.card Hsub = Nat.card W1 := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W1) (K := W) hW1).toEquiv
  intro i j
  let ξ : Section1.ClassFunction Hsub :=
    Section1.subgroupRestriction Hsub (Section1.subgroupRestriction W (piChar i j)) -
      deltaSign j • Section1.subgroupRestriction Hsub (ω i j)
  have hξvirt : Theory.Character.IsVirtualCharacter ξ := by
    have hpiVirt :
        Theory.Character.IsVirtualCharacter
          (Section1.subgroupRestriction Hsub (Section1.subgroupRestriction W (piChar i j))) := by
      exact isVirtualCharacter_subgroupRestriction_pf43 Hsub
        (isVirtualCharacter_subgroupRestriction_pf43 W
          (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hirr i j)))
    have hωVirt :
        Theory.Character.IsVirtualCharacter
          (Section1.subgroupRestriction Hsub (ω i j)) := by
      exact isVirtualCharacter_subgroupRestriction_pf43 Hsub
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hω.irreducible i j))
    exact Section3.isVirtualCharacter_sub hpiVirt
      (isVirtualCharacter_sign_smul_pf43 (hsign j) hωVirt)
  have hξzero :
      ∀ x : Hsub, x ≠ 1 → ξ x = 0 := by
    intro x hx1
    have hx1L : ((x : Hsub) : L) ≠ 1 := by
      intro hxL
      apply hx1
      apply Subtype.ext
      apply Subtype.ext
      exact hxL
    have hxWm : ((x : Hsub) : L) ∈ ((W : Set L) \ (W2 : Set L)) := by
      simpa using
        (mul_mem_wMinusW2_of_left_ne_one hW x.2 hx1L W2.one_mem)
    have hval :
        Section1.subgroupRestriction Hsub (Section1.subgroupRestriction W (piChar i j)) x =
          deltaSign j * Section1.subgroupRestriction Hsub (ω i j) x := by
      simpa [Section1.subgroupRestriction] using hC.1 i j ((x : Hsub) : L) hxWm
    dsimp [ξ]
    rw [hval]
    ring
  have hsp :
      Section1.scalarProduct Hsub ξ (Section1.principalCharacter Hsub) =
        (Nat.card Hsub : ℂ)⁻¹ * ξ 1 := by
    unfold Section1.scalarProduct
    have hsum :
        ∑ g : Hsub, ξ g * star (Section1.principalCharacter Hsub g) = ξ 1 := by
      rw [Finset.sum_eq_single 1]
      · simp [Section1.principalCharacter]
      · intro g hg hg1
        simp [Section1.principalCharacter, hξzero g hg1]
      · intro h1
        exact False.elim (h1 (by simp))
    rw [hsum]
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int hξvirt
      Section3.isVirtualCharacter_principalCharacter with ⟨a, ha⟩
  have hcard_ne : (Nat.card Hsub : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Hsub)).ne'
  have hξ_at_one :
      ξ 1 = (a : ℂ) * (Nat.card Hsub : ℂ) := by
    calc
      ξ 1 = (Nat.card Hsub : ℂ) * ((Nat.card Hsub : ℂ)⁻¹ * ξ 1) := by
        rw [← mul_assoc]
        simp
      _ = (Nat.card Hsub : ℂ) *
          Section1.scalarProduct Hsub ξ (Section1.principalCharacter Hsub) := by
            rw [hsp]
      _ = (a : ℂ) * (Nat.card Hsub : ℂ) := by
        rw [ha]
        ring
  have hξ_formula :
      ξ 1 = Section1.degree (piChar i j) -
        deltaSign j * Section1.degree (ω i j) := by
    dsimp [ξ]
    simp [Section1.degree, Section1.subgroupRestriction]
  have hξ_degree :
      Section1.degree (piChar i j) - deltaSign j =
        (a : ℂ) * (Nat.card Hsub : ℂ) := by
    calc
      Section1.degree (piChar i j) - deltaSign j =
          Section1.degree (piChar i j) - deltaSign j * Section1.degree (ω i j) := by
            rw [hω.degree_one i j]
            ring
      _ = ξ 1 := by
        rw [hξ_formula]
      _ = (a : ℂ) * (Nat.card Hsub : ℂ) := hξ_at_one
  refine ⟨a, ?_⟩
  calc
    Section1.degree (piChar i j) =
        deltaSign j + (Section1.degree (piChar i j) - deltaSign j) := by
          ring
    _ = deltaSign j + (a : ℂ) * (Nat.card Hsub : ℂ) := by
          rw [hξ_degree]
    _ = deltaSign j + (a : ℂ) * (Nat.card W1 : ℂ) := by
          rw [hcardSub]

/--
Peterfalvi Theorem (4.3): under Hypothesis (4.2), one gets the TI-subset
statement for `W \ W₂`, the sec3 Dade-isometry package, the value formula on
`W \ W₂`, and the degree congruence modulo `|W₁|`.
-/
public theorem theorem_4_3
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    theorem_4_3_statement K W1 W2 W I J i0 j0 ω h42 hω := by
  have hA : theorem_4_3_a_statement W1 W2 W := theorem_4_3_a K W1 W2 W h42
  rcases theorem_4_3_b K W1 W2 W I J i0 j0 ω h42 hω with
    ⟨σ, piChar, deltaSign, hB⟩
  rcases hB with ⟨hσmap, hsign, hirr, hdistinct, hind, hSigma⟩
  have hC : theorem_4_3_c_statement W2 W I J piChar deltaSign ω :=
    theorem_4_3_c K W1 W2 W I J i0 j0 ω deltaSign piChar
      h42 hω hsign hirr hdistinct hind
  have hD : theorem_4_3_d_statement W1 I J piChar deltaSign :=
    theorem_4_3_d K W1 W2 W I J i0 j0 ω deltaSign piChar
      h42 hω hsign hirr hC
  refine ⟨hA, σ, piChar, deltaSign, ?_⟩
  exact ⟨⟨hσmap, hsign, hirr, hdistinct, hind, hSigma⟩, hC, hD⟩

end CFSG.Section4
