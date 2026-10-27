module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWittFlags
public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Classical.MinusEight

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

instance commutator_self_subgroupOf_normal {G : Type*} [Group G] (H : Subgroup G) :
    (⁅H, H⁆.subgroupOf H).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_left H H)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

private theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem scalars_eq_bot : scalars (ZMod 2) V = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨c, hc⟩ := mem_scalars.1 hg
  rw [Subgroup.mem_bot]
  refine LinearEquiv.ext fun v => ?_
  rcases zmod_two_cases c with rfl | rfl
  · have h0 : ∀ w : V, w = 0 := fun w => by
      have := hc (g⁻¹ w)
      rwa [LinearEquiv.apply_inv_apply', zero_smul] at this
    rw [h0 (g v), h0 ((1 : V ≃ₗ[ZMod 2] V) v)]
  · rw [hc v, one_smul]
    rfl

theorem finrank_tailSpace_eq_two [FiniteDimensional (ZMod 2) V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : finrank (ZMod 2) V = 8) {P : ℕ → HypPair Q}
    (hP : ∀ i j, i < 3 → j < 3 → i ≠ j → (P i).Orth (P j)) :
    finrank (ZMod 2) (tailSpace P 3) = 2 := by
  let P' : Fin 3 → HypPair Q := fun i => P i
  have hP' : ∀ i j : Fin 3, i ≠ j → (P' i).Orth (P' j) := fun i j hij =>
    hP i j i.2 j.2 fun h => hij (Fin.ext h)
  have heq : tailSpace P 3 = OrthogonalTail.pairsPerp P' := by
    ext x
    rw [mem_tailSpace, OrthogonalTail.mem_pairsPerp]
    constructor
    · intro hx i
      exact HypPair.mem_perp.2 (hx i i.2)
    · intro hx i hi
      exact HypPair.mem_perp.1 (hx ⟨i, hi⟩)
  have := OrthogonalTail.finrank_pairsPerp hP' hQ
  rw [← heq, hV] at this
  omega

theorem derived_nontrivial_isSimpleGroup (hQ : (polarBilin Q).Nondegenerate)
    (hV : finrank (ZMod 2) V = 8) {P : ℕ → HypPair Q}
    (hP : ∀ i j, i < 3 → j < 3 → i ≠ j → (P i).Orth (P j))
    (hA : ∀ x ∈ tailSpace P 3, Q x = 0 → x = 0) :
    Nontrivial ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      IsSimpleGroup ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨hnt, hs⟩ := orthogonal_char_two_projective_derived_simple hQ hP le_rfl hA
    (Or.inr (finrank_tailSpace_eq_two hQ hV hP))
  have hbot : (scalars (ZMod 2) V).subgroupOf ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ = ⊥ := by
    rw [scalars_eq_bot, Subgroup.bot_subgroupOf]
  let e := QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)
  exact ⟨e.toEquiv.nontrivial, e.isSimpleGroup⟩

theorem sq_mem_derived (hQ : (polarBilin Q).Nondegenerate) (hV : finrank (ZMod 2) V = 8)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    g ^ 2 ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_pos (by omega)
  have hgen : TauCeti.QuadraticMap.orthogonalGroup Q = Subgroup.closure (Set.range (reflect Q)) :=
    orthogonalGroup_eq_closure_reflect hQ (by omega) (Or.inl (by omega))
  have hle : Subgroup.closure (Set.range (reflect Q)) ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hgen.ge
  have hg' : g ∈ Subgroup.closure (Set.range (reflect Q)) := hgen ▸ hg
  clear hg
  induction hg' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [pow_two, reflect_mul_self]
    exact one_mem _
  | one =>
    rw [one_pow]
    exact one_mem _
  | mul x y hx hy ihx ihy =>
    have hsq : (x * y) ^ 2 = x ^ 2 * ⁅x⁻¹, y⁆ * y ^ 2 := by
      rw [pow_two, pow_two, pow_two, commutatorElement_def]
      group
    rw [hsq]
    exact mul_mem (mul_mem ihx (Subgroup.commutator_mem_commutator (inv_mem (hle hx)) (hle hy)))
      ihy
  | inv x hx ihx =>
    rw [inv_pow]
    exact inv_mem ihx

theorem exponent_quotient_dvd_two (hQ : (polarBilin Q).Nondegenerate)
    (hV : finrank (ZMod 2) V = 8) :
    Monoid.exponent (↥(TauCeti.QuadraticMap.orthogonalGroup Q) ⧸
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆.subgroupOf
          (TauCeti.QuadraticMap.orthogonalGroup Q)) ∣ 2 := by
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun q => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.coe_pow]
  exact sq_mem_derived hQ hV g.2

private theorem exists_eq_span_singleton_of_finrank_eq_one {W : Submodule (ZMod 2) V}
    (hW : finrank (ZMod 2) W = 1) : ∃ v : V, v ≠ 0 ∧ W = Submodule.span (ZMod 2) {v} := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 hW
  refine ⟨v, fun h => hv0 (Subtype.ext h), le_antisymm (fun w hw => ?_) ?_⟩
  · obtain ⟨c, hc⟩ := hv ⟨w, hw⟩
    exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hc⟩
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 v.2

private theorem map_span_eq_of_forall_mem [FiniteDimensional (ZMod 2) V] (g : V ≃ₗ[ZMod 2] V)
    {S : Set V} (h : ∀ s ∈ S, g s ∈ Submodule.span (ZMod 2) S) :
    (Submodule.span (ZMod 2) S).map (g : V →ₗ[ZMod 2] V) = Submodule.span (ZMod 2) S :=
  Submodule.eq_of_le_of_finrank_eq ((Submodule.map_span_le _ _ _).2 h)
    (LinearEquiv.finrank_map_eq g _)

private theorem image_lt_one {α : Type*} (v : Fin 3 → α) :
    v '' {j : Fin 3 | (j : ℕ) < 1} = {v 0} := by
  have : {j : Fin 3 | (j : ℕ) < 1} = {0} := by
    ext j
    fin_cases j <;> simp
  rw [this, Set.image_singleton]

private theorem image_lt_two {α : Type*} (v : Fin 3 → α) :
    v '' {j : Fin 3 | (j : ℕ) < 2} = {v 0, v 1} := by
  have : {j : Fin 3 | (j : ℕ) < 2} = {0, 1} := by
    ext j
    fin_cases j <;> simp
  rw [this, Set.image_pair]

private theorem image_lt_three {α : Type*} (v : Fin 3 → α) :
    v '' {j : Fin 3 | (j : ℕ) < 3} = {v 0, v 1, v 2} := by
  have : {j : Fin 3 | (j : ℕ) < 3} = {0, 1, 2} := by
    ext j
    fin_cases j <;> simp
  rw [this, Set.image_insert_eq, Set.image_pair]

private theorem flag_swap_of_frame [FiniteDimensional (ZMod 2) V] {e f : Fin 3 → V}
    (hef : ∀ i j, polar Q (e i) (f j) = if i = j then 1 else 0)
    (hee : ∀ i j, polar Q (e i) (e j) = 0) (hu : Q (e 0) = 0) :
    ∃ L L' : Submodule (ZMod 2) V, L ≠ L' ∧
      {M : Submodule (ZMod 2) V | finrank (ZMod 2) M = 1 ∧
        M ≤ Submodule.span (ZMod 2) {e 0, e 1} ∧ M ≠ Submodule.span (ZMod 2) {e 0}} = {L, L'} ∧
      ∃ g ∈ elementaryGroup Q,
        (Submodule.span (ZMod 2) {e 0}).map (g : V →ₗ[ZMod 2] V) =
          Submodule.span (ZMod 2) {e 0} ∧
        (Submodule.span (ZMod 2) {e 0, e 1}).map (g : V →ₗ[ZMod 2] V) =
          Submodule.span (ZMod 2) {e 0, e 1} ∧
        (Submodule.span (ZMod 2) {e 0, e 1, e 2}).map (g : V →ₗ[ZMod 2] V) =
          Submodule.span (ZMod 2) {e 0, e 1, e 2} ∧
        L.map (g : V →ₗ[ZMod 2] V) = L' ∧ L'.map (g : V →ₗ[ZMod 2] V) = L := by
  have hw : polar Q (e 0) (f 1) = 0 := by rw [hef]; rfl
  obtain ⟨g, hg⟩ : ∃ g, g = eichler Q (e 0) (f 1) := ⟨_, rfl⟩
  have hg0 : g (e 0) = e 0 := by rw [hg]; exact eichler_apply_self _ _
  have hg2 : g (e 2) = e 2 := by
    rw [hg]
    exact eichler_apply_of_polar_eq_zero (hee 2 0) (by rw [hef]; rfl)
  have hg1 : g (e 1) = e 1 + e 0 := by
    rw [hg, eichler_apply hu hw, hee 1 0, hef 1 1]
    simp only [↓reduceIte, zero_smul, add_zero, mul_zero, one_smul]
    rw [sub_eq_add_neg, ZModModule.neg_eq_self]
  have hg01 : g (e 0 + e 1) = e 1 := by
    rw [map_add, hg0, hg1, add_comm (e 1), ← add_assoc, ZModModule.add_self, zero_add]
  have he1 : e 1 ≠ 0 := by
    intro h0
    have := hef 1 1
    rw [h0, polar_zero_left] at this
    simp at this
  have h01 : e 0 + e 1 ≠ 0 := by
    intro h0
    have := congrArg (fun x => polar Q x (f 0)) h0
    simp only [polar_add_left, hef, polar_zero_left] at this
    simp at this
  refine ⟨Submodule.span (ZMod 2) {e 1}, Submodule.span (ZMod 2) {e 0 + e 1}, ?_, ?_,
    ⟨g, hg ▸ eichler_mem_elementaryGroup Q _ _, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro hL
    have hmem : e 0 + e 1 ∈ Submodule.span (ZMod 2) {e 1} :=
      hL ▸ Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    have := congrArg (fun x => polar Q x (f 0)) hc
    simp only [polar_smul_left, polar_add_left, hef] at this
    simp at this
  · ext M
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hM1, hME, hMne⟩
      obtain ⟨m, hm0, rfl⟩ := exists_eq_span_singleton_of_finrank_eq_one hM1
      have hm : m ∈ Submodule.span (ZMod 2) {e 0, e 1} :=
        hME (Submodule.mem_span_singleton_self m)
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hm
      rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
      · simp at hm0
      · left
        simp
      · exact absurd (by simp) hMne
      · right
        simp
    · rintro (rfl | rfl)
      · refine ⟨finrank_span_singleton he1, ?_, ?_⟩
        · rw [Submodule.span_singleton_le_iff_mem]
          exact Submodule.subset_span (by simp)
        · intro hL
          have hmem : e 1 ∈ Submodule.span (ZMod 2) {e 0} :=
            hL ▸ Submodule.mem_span_singleton_self _
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
          have := congrArg (fun x => polar Q x (f 1)) hc
          simp only [polar_smul_left, hef] at this
          simp at this
      · refine ⟨finrank_span_singleton h01, ?_, ?_⟩
        · rw [Submodule.span_singleton_le_iff_mem]
          exact Submodule.add_mem _ (Submodule.subset_span (by simp))
            (Submodule.subset_span (by simp))
        · intro hL
          have hmem : e 0 + e 1 ∈ Submodule.span (ZMod 2) {e 0} :=
            hL ▸ Submodule.mem_span_singleton_self _
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
          have := congrArg (fun x => polar Q x (f 1)) hc
          simp only [polar_smul_left, polar_add_left, hef] at this
          simp at this
  · rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, hg0]
  · refine map_span_eq_of_forall_mem g fun s hs => ?_
    rcases hs with rfl | rfl
    · rw [hg0]
      exact Submodule.subset_span (by simp)
    · rw [hg1]
      exact Submodule.add_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  · refine map_span_eq_of_forall_mem g fun s hs => ?_
    rcases hs with rfl | rfl | rfl
    · rw [hg0]
      exact Submodule.subset_span (by simp)
    · rw [hg1]
      exact Submodule.add_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    · rw [hg2]
      exact Submodule.subset_span (by simp)
  · rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, hg1, add_comm]
  · rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, hg01]

theorem flag_swap_elementary [FiniteDimensional (ZMod 2) V] (hQ : (polarBilin Q).Nondegenerate)
    {E₁ E₂ E₃ : Submodule (ZMod 2) V} (h12 : E₁ < E₂) (h23 : E₂ < E₃)
    (h1 : finrank (ZMod 2) E₁ = 1) (h2 : finrank (ZMod 2) E₂ = 2) (h3 : finrank (ZMod 2) E₃ = 3)
    (hE₃ : ∀ x ∈ E₃, Q x = 0) :
    ∃ L L' : Submodule (ZMod 2) V, L ≠ L' ∧
      {M : Submodule (ZMod 2) V | finrank (ZMod 2) M = 1 ∧ M ≤ E₂ ∧ M ≠ E₁} = {L, L'} ∧
      ∃ g ∈ elementaryGroup Q, E₁.map (g : V →ₗ[ZMod 2] V) = E₁ ∧
        E₂.map (g : V →ₗ[ZMod 2] V) = E₂ ∧ E₃.map (g : V →ₗ[ZMod 2] V) = E₃ ∧
        L.map (g : V →ₗ[ZMod 2] V) = L' ∧ L'.map (g : V →ₗ[ZMod 2] V) = L := by
  let W : ℕ → Submodule (ZMod 2) V := fun
    | 0 => ⊥
    | 1 => E₁
    | 2 => E₂
    | _ => E₃
  obtain ⟨P, -, hPo, hPW⟩ := OrthogonalTail.exists_hypPairs_of_flag_of_le 3 ⊤
    (polarNondegOn_top hQ) E₃ le_top hE₃ (by omega) 3 le_rfl W le_top
    (fun i hi => by
      interval_cases i
      · exact finrank_bot (ZMod 2) V
      · exact h1
      · exact h2
      · exact h3)
    (fun i hi => by
      interval_cases i
      · exact bot_le
      · exact h12.le
      · exact h23.le)
    hE₃
  obtain ⟨hef, -, hee, -⟩ := OrthogonalTail.polar_pairs hPo
  have hE1 : E₁ = Submodule.span (ZMod 2) {(P 0).e} := by
    have := hPW 1 (by omega)
    rwa [image_lt_one] at this
  have hE2 : E₂ = Submodule.span (ZMod 2) {(P 0).e, (P 1).e} := by
    have := hPW 2 (by omega)
    rwa [image_lt_two] at this
  have hE3 : E₃ = Submodule.span (ZMod 2) {(P 0).e, (P 1).e, (P 2).e} := by
    have := hPW 3 le_rfl
    rwa [image_lt_three] at this
  rw [hE1, hE2, hE3]
  exact flag_swap_of_frame (e := fun j => (P j).e) (f := fun j => (P j).f) hef hee (P 0).Q_e

theorem minus_eight_derived_flag_action (hQ : (polarBilin Q).Nondegenerate)
    (hV : finrank (ZMod 2) V = 8) {P : ℕ → HypPair Q}
    (hP : ∀ i j, i < 3 → j < 3 → i ≠ j → (P i).Orth (P j))
    (hA : ∀ x ∈ tailSpace P 3, Q x = 0 → x = 0) :
    (Nontrivial ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      IsSimpleGroup ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆) ∧
    Monoid.exponent (↥(TauCeti.QuadraticMap.orthogonalGroup Q) ⧸
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆.subgroupOf
          (TauCeti.QuadraticMap.orthogonalGroup Q)) ∣ 2 ∧
    ∀ E₁ E₂ E₃ : Submodule (ZMod 2) V, E₁ < E₂ → E₂ < E₃ → finrank (ZMod 2) E₁ = 1 →
      finrank (ZMod 2) E₂ = 2 → finrank (ZMod 2) E₃ = 3 → (∀ x ∈ E₃, Q x = 0) →
      ∃ L L' : Submodule (ZMod 2) V, L ≠ L' ∧
        {M : Submodule (ZMod 2) V | finrank (ZMod 2) M = 1 ∧ M ≤ E₂ ∧ M ≠ E₁} = {L, L'} ∧
        ∃ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
          E₁.map (g : V →ₗ[ZMod 2] V) = E₁ ∧ E₂.map (g : V →ₗ[ZMod 2] V) = E₂ ∧
          E₃.map (g : V →ₗ[ZMod 2] V) = E₃ ∧ L.map (g : V →ₗ[ZMod 2] V) = L' ∧
          L'.map (g : V →ₗ[ZMod 2] V) = L := by
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_pos (by omega)
  have hD := orthogonal_char_two_derived_elementary hQ hP le_rfl hA
    (Or.inr (finrank_tailSpace_eq_two hQ hV hP))
  refine ⟨derived_nontrivial_isSimpleGroup hQ hV hP hA, exponent_quotient_dvd_two hQ hV,
    fun E₁ E₂ E₃ h12 h23 h1 h2 h3 hE₃ => ?_⟩
  obtain ⟨L, L', hne, hset, g, hg, hg1, hg2, hg3, hgL, hgL'⟩ :=
    flag_swap_elementary hQ h12 h23 h1 h2 h3 hE₃
  refine ⟨L, L', hne, hset, g, ?_, hg1, hg2, hg3, hgL, hgL'⟩
  rw [hD]
  exact hg

section Model

open CFSG.LieType.Universal.Spin

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {Q₀ : QuadraticForm (ZMod 2) W}

private theorem polar_isometryEquiv (φ : Q.IsometryEquiv Q₀) (x y : V) :
    polar Q x y = polar Q₀ (φ x) (φ y) := by
  rw [polar, polar, ← map_add, φ.map_app, φ.map_app, φ.map_app]

private def pullPair (φ : Q.IsometryEquiv Q₀) (P : HypPair Q₀) : HypPair Q where
  e := φ.symm P.e
  f := φ.symm P.f
  Q_e := by rw [← φ.map_app, φ.apply_symm_apply, P.Q_e]
  Q_f := by rw [← φ.map_app, φ.apply_symm_apply, P.Q_f]
  polar_ef := by
    rw [polar_isometryEquiv φ, φ.apply_symm_apply, φ.apply_symm_apply, P.polar_ef]

private theorem polar_pullPair_e (φ : Q.IsometryEquiv Q₀) (P : HypPair Q₀) (x : V) :
    polar Q (pullPair φ P).e x = polar Q₀ P.e (φ x) := by
  rw [polar_isometryEquiv φ]
  exact congrArg (fun y => polar Q₀ y (φ x)) (φ.apply_symm_apply P.e)

private theorem polar_pullPair_f (φ : Q.IsometryEquiv Q₀) (P : HypPair Q₀) (x : V) :
    polar Q (pullPair φ P).f x = polar Q₀ P.f (φ x) := by
  rw [polar_isometryEquiv φ]
  exact congrArg (fun y => polar Q₀ y (φ x)) (φ.apply_symm_apply P.f)

private theorem pullPair_orth (φ : Q.IsometryEquiv Q₀) {P P' : HypPair Q₀} (h : P.Orth P') :
    (pullPair φ P).Orth (pullPair φ P') where
  ee := by
    rw [polar_pullPair_e]
    exact (congrArg (polar Q₀ P.e) (φ.apply_symm_apply P'.e)).trans h.ee
  ef := by
    rw [polar_pullPair_e]
    exact (congrArg (polar Q₀ P.e) (φ.apply_symm_apply P'.f)).trans h.ef
  fe := by
    rw [polar_pullPair_f]
    exact (congrArg (polar Q₀ P.f) (φ.apply_symm_apply P'.e)).trans h.fe
  ff := by
    rw [polar_pullPair_f]
    exact (congrArg (polar Q₀ P.f) (φ.apply_symm_apply P'.f)).trans h.ff

theorem minus_eight_derived_flag_action_of_equivalent
    (hQ : Q.Equivalent (quadMinus 4 (ZMod 2) 1 1)) :
    (Nontrivial ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      IsSimpleGroup ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆) ∧
    Monoid.exponent (↥(TauCeti.QuadraticMap.orthogonalGroup Q) ⧸
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆.subgroupOf
          (TauCeti.QuadraticMap.orthogonalGroup Q)) ∣ 2 ∧
    ∀ E₁ E₂ E₃ : Submodule (ZMod 2) V, E₁ < E₂ → E₂ < E₃ → finrank (ZMod 2) E₁ = 1 →
      finrank (ZMod 2) E₂ = 2 → finrank (ZMod 2) E₃ = 3 → (∀ x ∈ E₃, Q x = 0) →
      ∃ L L' : Submodule (ZMod 2) V, L ≠ L' ∧
        {M : Submodule (ZMod 2) V | finrank (ZMod 2) M = 1 ∧ M ≤ E₂ ∧ M ≠ E₁} = {L, L'} ∧
        ∃ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
          E₁.map (g : V →ₗ[ZMod 2] V) = E₁ ∧ E₂.map (g : V →ₗ[ZMod 2] V) = E₂ ∧
          E₃.map (g : V →ₗ[ZMod 2] V) = E₃ ∧ L.map (g : V →ₗ[ZMod 2] V) = L' ∧
          L'.map (g : V →ₗ[ZMod 2] V) = L := by
  obtain ⟨φ⟩ := hQ
  have hn : 0 < 4 - 1 := by norm_num
  have hnd₀ : (polarBilin (quadMinus 4 (ZMod 2) 1 1)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus 4 (ZMod 2) (by decide)
  have hnd : (polarBilin Q).Nondegenerate := by
    refine nondegenerate_polarBilin_of_forall fun v hv => ?_
    have h0 : φ v = 0 := eq_zero_of_polar_eq_zero hnd₀ fun w => by
      rw [← φ.apply_symm_apply w, ← polar_isometryEquiv φ]
      exact hv _
    simpa using congrArg φ.symm h0
  have hV : finrank (ZMod 2) V = 8 := by
    rw [LinearEquiv.finrank_eq φ.toLinearEquiv, Module.finrank_fintype_fun_eq_card]
    simp
  let P : ℕ → HypPair Q := fun i => pullPair φ (minusFamily (ZMod 2) 1 1 hn i)
  have hP : ∀ i j, i < 3 → j < 3 → i ≠ j → (P i).Orth (P j) := fun i j hi hj hij =>
    pullPair_orth φ (minusFamily_orth hn i j hi hj hij)
  have hA : ∀ x ∈ tailSpace P 3, Q x = 0 → x = 0 := by
    intro x hx hQx
    have hx' : φ x ∈ tailSpace (minusFamily (ZMod 2) 1 1 hn) (4 - 1) := by
      rw [mem_tailSpace] at hx ⊢
      intro i hi
      have := hx i hi
      rwa [polar_pullPair_e, polar_pullPair_f] at this
    have h0 := eq_zero_of_mem_tailSpace_minusFamily (by decide) hn hx'
      (by rw [φ.map_app]; exact hQx)
    simpa using congrArg φ.symm h0
  exact minus_eight_derived_flag_action hnd hV hP hA

end Model

end CFSG.Monster.B.Classical.MinusEight
