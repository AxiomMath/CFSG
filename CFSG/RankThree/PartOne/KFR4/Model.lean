module

public import CFSG.RankThree.PartOne.KFR4.DerivedLe
public import CFSG.RankThree.PartOne.KFR4.BlkProps
public import CFSG.RankThree.PartOne.KFR4.B3Refl

public section

namespace CFSG.RankThree.PartOne.KFR4

open QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KFCL
open scoped commutatorElement

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] [Module.Finite K E]
  {p : ℕ} (S : StdData K E p)

noncomputable abbrev TS : Subgroup ↥(Om S.D) := (Tstd S).subgroupOf (Om S.D)

@[expose] noncomputable def cStd : ↥(TS S) ≃* Multiplicative (Vec p) :=
  (Subgroup.subgroupOfEquivOfLe (Tstd_le_Om S)).trans
    (MonoidHom.ofInjective (torHom_injective S)).symm

theorem coe_cStd_symm (a : Vec p) :
    (((cStd S).symm (Multiplicative.ofAdd a) : ↥(TS S)) : ↥(Om S.D)).1 = tor S a := rfl

theorem coe_eq_tor (x : ↥(TS S)) :
    (x : ↥(Om S.D)).1 = tor S (lin (cStd S) x) := by
  have := coe_cStd_symm S (lin (cStd S) x)
  rw [lin, ofAdd_toAdd, MulEquiv.symm_apply_apply] at this
  exact this

omit [Module.Finite K E] in
theorem tor_injective {a b : Fin 3 → ZMod p} (h : tor S a = tor S b) : a = b :=
  Multiplicative.toAdd.injective (torHom_injective S h)

omit [Module.Finite K E] in
theorem tor_mem_Tstd (a : Fin 3 → ZMod p) : tor S a ∈ Tstd S := ⟨Multiplicative.ofAdd a, rfl⟩

theorem mem_hypS_std {ρ : Root} {x : ↥(Om S.D)} :
    x ∈ hypS (cStd S) ρ ↔ (x : Vs K E ≃ₗ[K] Vs K E) ∈ hypA S ρ := by
  rw [mem_hypS]
  constructor
  · rintro ⟨h, h0⟩
    exact ⟨lin (cStd S) ⟨x, h⟩, h0, (coe_eq_tor S ⟨x, h⟩).symm⟩
  · rintro ⟨a, ha, hax⟩
    have hT : x ∈ TS S := by
      show (x : Vs K E ≃ₗ[K] Vs K E) ∈ Tstd S
      rw [← hax]
      exact tor_mem_Tstd S a
    refine ⟨hT, ?_⟩
    have h1 := coe_eq_tor S ⟨x, hT⟩
    have h2 : a = lin (cStd S) ⟨x, hT⟩ := tor_injective S (hax.trans h1)
    rw [← h2]
    exact ha

theorem block_simple_sub (ρ : Root) (N : Subgroup ↥(Om S.D))
    (hN : N ≤ (Block S.D ρ).subgroupOf (Om S.D))
    (hnorm : (N.subgroupOf ((Block S.D ρ).subgroupOf (Om S.D))).Normal) :
    N = ⊥ ∨ N = (Block S.D ρ).subgroupOf (Om S.D) := by
  have hB : Block S.D ρ ≤ Om S.D := block_le_Om S ρ
  have hN' : N.map (Om S.D).subtype ≤ Block S.D ρ := by
    rintro _ ⟨n, hn, rfl⟩
    exact hN hn
  have hnorm' : ((N.map (Om S.D).subtype).subgroupOf (Block S.D ρ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hN']
    rintro _ g ⟨n, hn, rfl⟩ hg
    have := (Subgroup.normal_subgroupOf_iff hN).1 hnorm n ⟨g, hB hg⟩ hn hg
    exact ⟨⟨g, hB hg⟩ * n * ⟨g, hB hg⟩⁻¹, this, rfl⟩
  rcases block_simple_std S ρ _ hN' hnorm' with h | h
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Om S.D).subtype_injective).1 h
  · right
    apply Subgroup.map_injective (Om S.D).subtype_injective
    rw [h, Subgroup.map_subgroupOf_eq_of_le hB]

theorem block_perfect_sub (ρ : Root) :
    ⁅(Block S.D ρ).subgroupOf (Om S.D), (Block S.D ρ).subgroupOf (Om S.D)⁆ =
      (Block S.D ρ).subgroupOf (Om S.D) :=
  commutator_subgroupOf_eq' (block_le_Om S ρ) (block_perfect_std S ρ)

theorem block_cent_sub (ρ : Root) :
    (Block S.D ρ).subgroupOf (Om S.D) ≤ Subgroup.centralizer (hypS (cStd S) ρ : Set ↥(Om S.D)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨a, ha, hay⟩ := (mem_hypS_std S).1 hy
  apply Subtype.ext
  show (y : Vs K E ≃ₗ[K] Vs K E) * (x : Vs K E ≃ₗ[K] Vs K E) =
    (x : Vs K E ≃ₗ[K] Vs K E) * (y : Vs K E ≃ₗ[K] Vs K E)
  rw [← hay]
  exact (block_cent_std S ρ a ha _ hx).symm

theorem block_T_sub (ρ : Root) (x : ↥(TS S)) :
    (x : ↥(Om S.D)) ∈ (Block S.D ρ).subgroupOf (Om S.D) ↔ x ∈ lineT (cStd S) ρ := by
  rw [mem_lineT]
  show (x : ↥(Om S.D)).1 ∈ Block S.D ρ ↔ _
  rw [coe_eq_tor S x, block_T_std S ρ]

theorem derived_le_sub (S₀ : Subgroup ↥(Om S.D)) (hS₀ : S₀ ≤ TS S)
    (hshape : S₀.relIndex (TS S) = p ∨
      ∃ e : ↥(Om S.D), e ∈ TS S ∧ e ≠ 1 ∧ S₀ = Subgroup.zpowers e) :
    ⁅Subgroup.centralizer (S₀ : Set ↥(Om S.D)), Subgroup.centralizer (S₀ : Set ↥(Om S.D))⁆ ≤
      ⨆ i : {i : Root // S₀ ≤ hypS (cStd S) i}, (Block S.D i.1).subgroupOf (Om S.D) := by
  have hB : ∀ ρ, Block S.D ρ ≤ Om S.D := block_le_Om S
  have hRT : S₀.map (Om S.D).subtype ≤ Tstd S := by
    rintro _ ⟨n, hn, rfl⟩
    exact hS₀ hn
  have hT : (TS S).map (Om S.D).subtype = Tstd S := Subgroup.map_subgroupOf_eq_of_le (Tstd_le_Om S)
  have hshape' : (S₀.map (Om S.D).subtype).relIndex (Tstd S) = p ∨
      ∃ e, e ∈ Tstd S ∧ e ≠ 1 ∧ S₀.map (Om S.D).subtype = Subgroup.zpowers e := by
    rcases hshape with h | ⟨e, heT, he1, rfl⟩
    · left
      rw [← hT, Subgroup.relIndex_map_map_of_injective S₀ (TS S) (Om S.D).subtype_injective]
      exact h
    · right
      refine ⟨(e : Vs K E ≃ₗ[K] Vs K E), hRT ⟨e, Subgroup.mem_zpowers e, rfl⟩, ?_, ?_⟩
      · intro h1
        exact he1 (Subtype.ext h1)
      · rw [MonoidHom.map_zpowers]
        rfl
  have hamb := derived_le_std S _ hRT hshape'
  apply (Subgroup.map_le_map_iff_of_injective (Om S.D).subtype_injective).1
  rw [Subgroup.map_commutator, Subgroup.map_iSup]
  have hC : (Subgroup.centralizer (S₀ : Set ↥(Om S.D))).map (Om S.D).subtype ≤
      Subgroup.centralizer ((S₀.map (Om S.D).subtype : Subgroup _) : Set (Vs K E ≃ₗ[K] Vs K E)) ⊓
        Om S.D := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Subgroup.mem_centralizer_iff.2 ?_, x.2⟩
    rintro _ ⟨n, hn, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hx n hn
    exact congrArg Subtype.val this
  refine (Subgroup.commutator_mono hC hC).trans (hamb.trans (iSup_le fun ρ => ?_))
  refine le_iSup_of_le ⟨ρ.1, ?_⟩ ?_
  · intro n hn
    exact (mem_hypS_std S).2 (ρ.2 ⟨n, hn, rfl⟩)
  · rw [Subgroup.map_subgroupOf_eq_of_le (hB ρ.1)]

theorem realize_sub (σ : Root) :
    ∃ w ∈ Subgroup.normalizer ((TS S : Subgroup ↥(Om S.D)) : Set ↥(Om S.D)),
      ∀ x : ↥(TS S), w * x * w⁻¹ = ((reflT (cStd S) σ x : ↥(TS S)) : ↥(Om S.D)) := by
  obtain ⟨w, hw, hwa⟩ := exists_weyl S σ
  have hval : ∀ x : ↥(TS S), (⟨w, hw⟩ * (x : ↥(Om S.D)) * ⟨w, hw⟩⁻¹ : ↥(Om S.D)).1 =
      tor S (reflLin p σ (lin (cStd S) x)) := by
    intro x
    show w * (x : ↥(Om S.D)).1 * w⁻¹ = _
    rw [coe_eq_tor S x, hwa]
  have hrefl : ∀ x : ↥(TS S), ((reflT (cStd S) σ x : ↥(TS S)) : ↥(Om S.D)).1 =
      tor S (reflLin p σ (lin (cStd S) x)) := by
    intro x
    rw [coe_eq_tor S (reflT (cStd S) σ x), lin_reflT]
  refine ⟨⟨w, hw⟩, ?_, fun x => Subtype.ext ((hval x).trans (hrefl x).symm)⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 : (⟨w, hw⟩ * y * ⟨w, hw⟩⁻¹ : ↥(Om S.D)) =
        ((reflT (cStd S) σ ⟨y, hy⟩ : ↥(TS S)) : ↥(Om S.D)) :=
      Subtype.ext ((hval ⟨y, hy⟩).trans (hrefl ⟨y, hy⟩).symm)
    rw [h1]
    exact (reflT (cStd S) σ ⟨y, hy⟩).2
  · intro hy
    have hy' : (⟨w, hw⟩ * y * ⟨w, hw⟩⁻¹ : ↥(Om S.D)) ∈ TS S := hy
    have hyy : w * y.1 * w⁻¹ = tor S (lin (cStd S) ⟨_, hy'⟩) :=
      coe_eq_tor S ⟨_, hy'⟩
    show y.1 ∈ Tstd S
    have h2 : y.1 = tor S (reflLin p σ (lin (cStd S) ⟨_, hy'⟩)) := by
      have h3 := hwa (reflLin p σ (lin (cStd S) ⟨_, hy'⟩))
      rw [reflLin_reflLin] at h3
      exact (mul_left_cancel (mul_right_cancel (h3.trans hyy.symm))).symm
    rw [h2]
    exact tor_mem_Tstd S _

@[expose] noncomputable def stdB3Data : B3Data p (TS S) where
  c := cStd S
  block ρ := (Block S.D ρ).subgroupOf (Om S.D)
  block_simple := block_simple_sub S
  block_perfect := block_perfect_sub S
  block_cent := block_cent_sub S
  block_T := block_T_sub S
  derived_le := derived_le_sub S
  realize := realize_sub S

end CFSG.RankThree.PartOne.KFR4
