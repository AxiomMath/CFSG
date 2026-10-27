module

public import CFSG.OddTranspositions.PartThree.Twelve.SixComponent
import CFSG.OddTranspositions.PartThree.Twelve.Five
import CFSG.OddTranspositions.PartFour.SpLineCount
import CFSG.OddTranspositions.PartFour.Fourteen.ShapeTransport
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpNormal
import CFSG.RankThree.PartOne.KC.SymplecticFullRankTwo
import CFSG.RankThree.PartOne.CTP.SeitzSpClosure
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.Timmesfeld.Connectivity
open CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.Open CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
  CFSG.LocalAnalysis.WeakClosure81

section VectorCount

variable {k : ℕ} {F : Type} [Field F] [Fintype F]

omit [Fintype F] in
theorem natCard_eq_natCard_ker_mul {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] (L : V →ₗ[F] W) (hL : Function.Surjective L) :
    Nat.card V = Nat.card (LinearMap.ker L) * Nat.card W := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker L),
    Nat.card_congr (L.quotKerEquivOfSurjective hL).toEquiv]

omit [Field F] [Fintype F] in
theorem natCard_vec [Finite F] : Nat.card (Fin k ⊕ Fin k → F) = Nat.card F ^ (2 * k) := by
  rw [Nat.card_fun, Nat.card_sum, Nat.card_fin, two_mul]

omit [Fintype F] in
theorem spForm_swap (u v : Fin k ⊕ Fin k → F) : spForm k F v u = - spForm k F u v :=
  (LinearMap.IsAlt.neg (B := spForm k F) spForm_isAlt u v).symm

omit [Fintype F] in
theorem spForm_self (u : Fin k ⊕ Fin k → F) : spForm k F u u = 0 :=
  spForm_isAlt u

omit [Fintype F] in
theorem exists_spForm_ne_zero {u : Fin k ⊕ Fin k → F} (hu : u ≠ 0) :
    ∃ v, spForm k F v u ≠ 0 := by
  by_contra h
  push Not at h
  exact hu (spForm_nondegenerate.2 u h)

theorem ncard_spForm_eq_zero (hk : 1 ≤ k) {u : Fin k ⊕ Fin k → F} (hu : u ≠ 0) :
    {v | spForm k F v u = 0}.ncard = Nat.card F ^ (2 * k - 1) := by
  classical
  set φ : (Fin k ⊕ Fin k → F) →ₗ[F] F := (spForm k F).flip u with hφdef
  have hφ : ∀ v, φ v = spForm k F v u := fun v => rfl
  obtain ⟨v₀, hv₀⟩ := exists_spForm_ne_zero hu
  have hsurj : Function.Surjective φ := fun c => ⟨(c / spForm k F v₀ u) • v₀, by
    rw [map_smul, hφ, smul_eq_mul, div_mul_cancel₀ _ hv₀]⟩
  have h1 := natCard_eq_natCard_ker_mul φ hsurj
  rw [natCard_vec] at h1
  have hset : {v | spForm k F v u = 0} = (LinearMap.ker φ : Set (Fin k ⊕ Fin k → F)) := by
    ext v
    simp [hφ]
  rw [hset, ← Nat.card_coe_set_eq]
  have hq : 0 < Nat.card F := Nat.card_pos
  have h2 : Nat.card F ^ (2 * k) = Nat.card F ^ (2 * k - 1) * Nat.card F := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_right hq h1).symm

theorem ncard_spForm_eq_zero_and_eq_zero (hk : 1 ≤ k) {u w : Fin k ⊕ Fin k → F}
    (huw : spForm k F u w ≠ 0) :
    {v | spForm k F v u = 0 ∧ spForm k F v w = 0}.ncard = Nat.card F ^ (2 * k - 2) := by
  classical
  set L : (Fin k ⊕ Fin k → F) →ₗ[F] F × F :=
    ((spForm k F).flip u).prod ((spForm k F).flip w) with hLdef
  have hL : ∀ v, L v = (spForm k F v u, spForm k F v w) := fun v => rfl
  have hwu : spForm k F w u ≠ 0 := by
    rw [spForm_swap]
    exact neg_ne_zero.mpr huw
  have hsurj : Function.Surjective L := by
    rintro ⟨a, b⟩
    refine ⟨(b / spForm k F u w) • u + (a / spForm k F w u) • w, ?_⟩
    rw [hL, Prod.mk.injEq]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      spForm_self, mul_zero, zero_add, add_zero]
    exact ⟨div_mul_cancel₀ _ hwu, div_mul_cancel₀ _ huw⟩
  have h1 := natCard_eq_natCard_ker_mul L hsurj
  rw [natCard_vec, Nat.card_prod] at h1
  have hset : {v | spForm k F v u = 0 ∧ spForm k F v w = 0} =
      (LinearMap.ker L : Set (Fin k ⊕ Fin k → F)) := by
    ext v
    simp [hL]
  rw [hset, ← Nat.card_coe_set_eq]
  have hq : 0 < Nat.card F * Nat.card F := Nat.mul_pos Nat.card_pos Nat.card_pos
  have h2 : Nat.card F ^ (2 * k) = Nat.card F ^ (2 * k - 2) * (Nat.card F * Nat.card F) := by
    rw [← pow_two, ← pow_add]
    congr 1
    omega
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_right hq h1).symm

theorem ncard_spForm_eq_zero_and_ne_zero (hk : 1 ≤ k) {u w : Fin k ⊕ Fin k → F}
    (huw : spForm k F u w ≠ 0) :
    {v | spForm k F v u = 0 ∧ spForm k F v w ≠ 0}.ncard =
      Nat.card F ^ (2 * k - 1) - Nat.card F ^ (2 * k - 2) := by
  have hu : u ≠ 0 := by
    rintro rfl
    exact huw (by simp)
  have hset : {v | spForm k F v u = 0 ∧ spForm k F v w ≠ 0} =
      {v | spForm k F v u = 0} \ {v | spForm k F v u = 0 ∧ spForm k F v w = 0} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_diff, not_and]
    tauto
  rw [hset, Set.ncard_diff (fun v hv => hv.1) (Set.toFinite _), ncard_spForm_eq_zero hk hu,
    ncard_spForm_eq_zero_and_eq_zero hk huw]

omit [Fintype F] in
theorem exists_eq_smul_add_smul_of_forall_spForm {u w v : Fin k ⊕ Fin k → F}
    (h : ∀ z, spForm k F z u = 0 → spForm k F z w = 0 → spForm k F z v = 0) :
    ∃ α β : F, v = α • u + β • w := by
  have hrefl : (spForm k F).IsRefl := LinearMap.IsAlt.isRefl (B := spForm k F) spForm_isAlt
  set N : Submodule F (Fin k ⊕ Fin k → F) := Submodule.span F (Set.range ![u, w]) with hN
  have hv : v ∈ (spForm k F).orthogonal ((spForm k F).orthogonal N) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro z hz
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hz
    have hzu : spForm k F u z = 0 := hz u (Submodule.subset_span ⟨0, rfl⟩)
    have hzw : spForm k F w z = 0 := hz w (Submodule.subset_span ⟨1, rfl⟩)
    exact h z (hrefl _ _ hzu) (hrefl _ _ hzw)
  rw [LinearMap.BilinForm.orthogonal_orthogonal spForm_nondegenerate hrefl] at hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hv
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  rfl

theorem ncard_smul_add_smul_le (u w : Fin k ⊕ Fin k → F) :
    {v | ∃ α β : F, β ≠ 0 ∧ v = α • u + β • w}.ncard ≤ Nat.card F * (Nat.card F - 1) := by
  classical
  have hset : {v | ∃ α β : F, β ≠ 0 ∧ v = α • u + β • w} =
      (fun p : F × F => p.1 • u + p.2 • w) '' (Set.univ ×ˢ {β | β ≠ 0}) := by
    ext v
    constructor
    · rintro ⟨α, β, hβ, rfl⟩
      exact ⟨(α, β), ⟨trivial, hβ⟩, rfl⟩
    · rintro ⟨⟨α, β⟩, ⟨-, hβ⟩, rfl⟩
      exact ⟨α, β, hβ, rfl⟩
  rw [hset]
  refine (Set.ncard_image_le (Set.toFinite _)).trans (le_of_eq ?_)
  rw [Set.ncard_prod, Set.ncard_univ]
  congr 1
  have : {β : F | β ≠ 0} = Set.univ \ {0} := by
    ext x
    simp
  rw [this, Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]

omit [Fintype F] in
theorem ncard_setOf_ne_zero : {a : F | a ≠ 0}.ncard = Nat.card F - 1 := by
  have : {a : F | a ≠ 0} = Set.univ \ {0} := by
    ext x
    simp
  rw [this, Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]

omit [Fintype F] in
theorem injOn_smul_of_nonproportional {A : Set (Fin k ⊕ Fin k → F)} (hA0 : ∀ x ∈ A, x ≠ 0)
    (hAp : ∀ x ∈ A, ∀ x' ∈ A, ∀ a : F, x' = a • x → x' = x) :
    Set.InjOn (fun p : (Fin k ⊕ Fin k → F) × F => p.2 • p.1) (A ×ˢ {a | a ≠ 0}) := by
  rintro ⟨x, a⟩ ⟨hx, ha⟩ ⟨x', a'⟩ ⟨hx', ha'⟩ h
  have h' : a • x = a' • x' := h
  have h1 : x' = (a'⁻¹ * a) • x := by
    rw [mul_smul, h', smul_smul, inv_mul_cancel₀ ha', one_smul]
  have hxx : x' = x := hAp x hx x' hx' _ h1
  subst hxx
  have : a = a' := smul_left_injective F (hA0 _ hx) h'
  rw [this]

theorem ncard_le_of_vectorConfig (hk : 1 ≤ k)
    {A C : Set (Fin k ⊕ Fin k → F)} {va : Fin k ⊕ Fin k → F}
    (hA0 : ∀ x ∈ A, x ≠ 0) (hC0 : ∀ c ∈ C, c ≠ 0)
    (hAp : ∀ x ∈ A, ∀ x' ∈ A, ∀ a : F, x' = a • x → x' = x)
    (hCp : ∀ c ∈ C, ∀ c' ∈ C, ∀ a : F, c' = a • c → c' = c)
    (hAva : ∀ x ∈ A, spForm k F x va = 0)
    (hAC : ∀ x ∈ A, ∀ c ∈ C, spForm k F x c ≠ 0)
    (hCva : ∀ c ∈ C, spForm k F c va ≠ 0)
    (hAcard : A.ncard = Nat.card F ^ (2 * k - 2)) :
    C.ncard ≤ Nat.card F := by
  classical
  rcases C.eq_empty_or_nonempty with hCe | ⟨vb, hvb⟩
  · rw [hCe, Set.ncard_empty]
    exact Nat.zero_le _
  have hq : 1 < Nat.card F := Finite.one_lt_card
  set I := (fun p : (Fin k ⊕ Fin k → F) × F => p.2 • p.1) '' (A ×ˢ {a | a ≠ 0}) with hI
  have hIcard : I.ncard = Nat.card F ^ (2 * k - 2) * (Nat.card F - 1) := by
    rw [hI, (injOn_smul_of_nonproportional hA0 hAp).ncard_image, Set.ncard_prod,
      hAcard, ncard_setOf_ne_zero]
  have hIP : ∀ c ∈ C, I = {v | spForm k F v va = 0 ∧ spForm k F v c ≠ 0} := by
    intro c hc
    have hsub : I ⊆ {v | spForm k F v va = 0 ∧ spForm k F v c ≠ 0} := by
      rintro _ ⟨⟨x, a⟩, ⟨hx, ha⟩, rfl⟩
      simp only [Set.mem_setOf_eq, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact ⟨by rw [hAva x hx, mul_zero], mul_ne_zero ha (hAC x hx c hc)⟩
    have hvac : spForm k F va c ≠ 0 := by
      rw [spForm_swap]
      exact neg_ne_zero.mpr (hCva c hc)
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [ncard_spForm_eq_zero_and_ne_zero hk hvac, hIcard]
    have h1 : Nat.card F ^ (2 * k - 1) = Nat.card F ^ (2 * k - 2) * Nat.card F := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h1, Nat.mul_sub_one]
  have hspan : C ⊆ {v | ∃ α β : F, β ≠ 0 ∧ v = α • va + β • vb} := by
    intro c hc
    have hPeq : {v | spForm k F v va = 0 ∧ spForm k F v c ≠ 0} =
        {v | spForm k F v va = 0 ∧ spForm k F v vb ≠ 0} := (hIP c hc).symm.trans (hIP vb hvb)
    obtain ⟨α, β, hαβ⟩ := exists_eq_smul_add_smul_of_forall_spForm (u := va) (w := vb) (v := c)
      fun z hza hzb => by
        by_contra hzc
        have hz : z ∈ {v | spForm k F v va = 0 ∧ spForm k F v c ≠ 0} := ⟨hza, hzc⟩
        rw [hPeq] at hz
        exact hz.2 hzb
    refine ⟨α, β, fun hβ => hCva c hc ?_, hαβ⟩
    rw [hαβ, hβ, zero_smul, add_zero, map_smul, LinearMap.smul_apply, spForm_self, smul_zero]
  set J := (fun p : (Fin k ⊕ Fin k → F) × F => p.2 • p.1) '' (C ×ˢ {a | a ≠ 0}) with hJ
  have hJsub : J ⊆ {v | ∃ α β : F, β ≠ 0 ∧ v = α • va + β • vb} := by
    rintro _ ⟨⟨c, a⟩, ⟨hc, ha⟩, rfl⟩
    obtain ⟨α, β, hβ, hcαβ⟩ := hspan hc
    refine ⟨a * α, a * β, mul_ne_zero ha hβ, ?_⟩
    have hcαβ' : c = α • va + β • vb := hcαβ
    show a • c = _
    rw [hcαβ', smul_add, smul_smul, smul_smul]
  have h1 : C.ncard * (Nat.card F - 1) ≤ Nat.card F * (Nat.card F - 1) := by
    calc C.ncard * (Nat.card F - 1) = J.ncard := by
          rw [hJ, (injOn_smul_of_nonproportional hC0 hCp).ncard_image,
            Set.ncard_prod, ncard_setOf_ne_zero]
      _ ≤ _ := (Set.ncard_le_ncard hJsub (Set.toFinite _)).trans (ncard_smul_add_smul_le va vb)
  exact Nat.le_of_mul_le_mul_right h1 (by omega)

omit [Fintype F] in
theorem eq_of_spTransvection_eq [CharP F 2] {v w : Fin k ⊕ Fin k → F} {c : F} (hc : c ≠ 0)
    (hw : w ≠ 0) (h : spTransvection v c = spTransvection w c) : v = w := by
  by_cases hprop : ∃ a : F, v = a • w
  · obtain ⟨a, rfl⟩ := hprop
    rw [spTransvection_smul_eq] at h
    obtain ⟨z, hz⟩ := exists_spForm_ne_zero hw
    have h2 := congrArg (fun g => spEnd g z) h
    simp only [spEnd_spTransvection] at h2
    have h3 : a * a * c * spForm k F z w = c * spForm k F z w :=
      smul_left_injective F hw (add_left_cancel h2)
    have h4 : a * a = 1 := by
      have h5 := mul_right_cancel₀ hz h3
      exact mul_right_cancel₀ hc (by rw [one_mul]; exact h5)
    have h5 : (a + 1) * (a + 1) = 0 := by
      have h2' : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination h4 + (a + 1) * h2'
    have h6 : a = 1 := by
      have h7 := mul_self_eq_zero.mp h5
      calc a = a + (1 + 1) := by rw [CharTwo.add_self_eq_zero, add_zero]
        _ = (a + 1) + 1 := by ring
        _ = 1 := by rw [h7, zero_add]
    rw [h6, one_smul]
  · push Not at hprop
    obtain ⟨x, hxw, hxv⟩ := exists_spForm_eq_zero_ne_zero hw hprop
    have h1 : Commute (spTransvection x c) (spTransvection w c) :=
      (commute_spTransvection_iff hc hc).mpr hxw
    rw [← h] at h1
    exact absurd ((commute_spTransvection_iff hc hc).mp h1) hxv

omit [Fintype F] in
theorem commute_spTransvection_one_iff [CharP F 2] {g : ↥(StatedSp k F)}
    {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) :
    Commute g (spTransvection a 1) ↔ spEnd g a = a := by
  constructor
  · intro h
    have h1 : spTransvection (spEnd g a) 1 = spTransvection a 1 := by
      rw [← CFSG.RankThree.PartOne.CTP.spTransvection_conj g a 1, h.eq]
      group
    exact eq_of_spTransvection_eq one_ne_zero ha h1
  · intro h
    exact (CFSG.RankThree.PartOne.CTP.commute_spTransvection h 1).symm

end VectorCount

theorem exists_vectorModel {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (h : IsSymplecticTransvection X m f s) :
    ∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (τ : (Fin k ⊕ Fin k → F) → X),
      m = 2 * k ∧ Nat.card F = 2 ^ f ∧
      (∀ v, v ≠ 0 → τ v ∈ E) ∧ (∀ t ∈ E, ∃ v, v ≠ 0 ∧ τ v = t) ∧
      (∀ v w, v ≠ 0 → w ≠ 0 → τ v = τ w → v = w) ∧
      (∀ v w, v ≠ 0 → w ≠ 0 → (Commute (τ v) (τ w) ↔ spForm k F v w = 0)) := by
  classical
  obtain ⟨k, hmk, F, _, _, hF, e, hrank⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hF
  set ψ : X →* StatedSp k F := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
    with hψdef
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : QuotientGroup.mk' (Subgroup.center X) a = QuotientGroup.mk' (Subgroup.center X) b :=
      e.injective hab
    rw [QuotientGroup.mk'_eq_mk'] at h1
    obtain ⟨z, hz, hzb⟩ := h1
    rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, mul_one] at hzb
    exact hzb
  have hψsurj : Function.Surjective ψ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨u, c, hu, hc, hψs⟩ := borel86_spn_eq_spTransvection hrank
  change ψ s = spTransvection u c at hψs
  have hEs : ∀ x, x ∈ E ↔ IsConj s x := by
    obtain ⟨d₀, rfl⟩ := hcls
    intro x
    exact ⟨fun hx => (isConj_comm.mp hs).trans hx, fun hx => (show IsConj d₀ s from hs).trans hx⟩
  have hconj : ∀ v, v ≠ 0 → ∃ y ∈ E, ψ y = spTransvection v c := by
    intro v hv
    obtain ⟨g, hg⟩ := exists_spEnd_eq hu hv
    obtain ⟨g', hg'⟩ := hψsurj g
    refine ⟨g' * s * g'⁻¹, (hEs _).mpr (isConj_iff.mpr ⟨g', rfl⟩), ?_⟩
    rw [map_mul, map_mul, map_inv, hg', hψs, conj_spTransvection, hg]
  have hEtr : ∀ x ∈ E, ∃ v, v ≠ 0 ∧ ψ x = spTransvection v c := by
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp ((hEs x).mp hx)
    refine ⟨spEnd (ψ g) u, fun h0 => hu ?_, ?_⟩
    · rw [← spEnd_spEnd_inv_apply (ψ g)⁻¹ u, inv_inv, h0, map_zero]
    · rw [map_mul, map_mul, map_inv, hψs, conj_spTransvection]
  let τ : (Fin k ⊕ Fin k → F) → X := fun v => Function.surjInv hψsurj (spTransvection v c)
  have hτ : ∀ v, ψ (τ v) = spTransvection v c := fun v => Function.surjInv_eq hψsurj _
  refine ⟨k, F, inferInstance, inferInstance, τ, hmk, hF, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨y, hy, hψy⟩ := hconj v hv
    rwa [show τ v = y from hψinj (by rw [hτ, hψy])]
  · intro t ht
    obtain ⟨v, hv, hψt⟩ := hEtr t ht
    exact ⟨v, hv, hψinj (by rw [hτ, hψt])⟩
  · intro v w _ hw h
    have h1 : spTransvection v c = spTransvection w c := by rw [← hτ, ← hτ, h]
    exact eq_of_spTransvection_eq hc hw h1
  · intro v w _ _
    have hcomm : Commute (τ v) (τ w) ↔ Commute (ψ (τ v)) (ψ (τ w)) :=
      ⟨fun h => h.map ψ, fun h => hψinj (by rw [map_mul, map_mul]; exact h.eq)⟩
    rw [hcomm, hτ, hτ, commute_spTransvection_iff hc hc]

theorem ncard_class_of_isSymplecticTransvection {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (h : IsSymplecticTransvection X m f s) : E.ncard = 2 ^ (f * m) - 1 := by
  classical
  obtain ⟨k, F, _, _, τ, hmk, hF, hτE, hτs, hτi, -⟩ := exists_vectorModel hcls hZ hs h
  have hE : E = τ '' {v | v ≠ 0} := by
    ext t
    constructor
    · intro ht
      obtain ⟨v, hv, rfl⟩ := hτs t ht
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact hτE v hv
  have hinj : Set.InjOn τ {v | v ≠ 0} := fun v hv w hw h => hτi v w hv hw h
  have h0 : {v : Fin k ⊕ Fin k → F | v ≠ 0} = Set.univ \ {0} := by
    ext v
    simp
  rw [hE, hinj.ncard_image, h0, Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
    natCard_vec, hF, hmk, ← pow_mul]

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem ncard_gammaAt_pivot (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y) :
    (gammaAt D x y hC.d).ncard = 2 ^ (f * (n - 2)) - 1 := by
  classical
  obtain ⟨K, ι, hZK, ⟨d₀, hcls⟩, hSpK, hinj, -, -, ⟨b₀, hb₀⟩⟩ :=
    exists_localModel hC hMZ hα hs hn hSp hx hy hxy
  have hb₀E : ι b₀ hb₀ ∈ {k : K | ∃ b, ∃ hb : b ∈ gammaAt D x y hC.d, ι b hb = k} :=
    ⟨b₀, hb₀, rfl⟩
  rw [← ncard_class_of_isSymplecticTransvection ⟨d₀, hcls⟩ hZK hb₀E (hSpK b₀ hb₀)]
  exact Set.ncard_congr (fun b hb => ι b hb) (fun b hb => ⟨b, hb, rfl⟩)
    (fun b c hb hc h => hinj b hb c hc h) (fun k ⟨b, hb, hk⟩ => ⟨b, hb, hk⟩)

theorem ncard_gammaAt_of_mem (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {v x y : G} (hv : v ∈ D) (hx : x ∈ commSet D v) (hy : y ∈ commSet D v)
    (hxy : ¬ Commute x y) : (gammaAt D x y v).ncard = 2 ^ (f * (n - 2)) - 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hv)
  set φ := MulAut.conj g with hφdef
  have hφD : ∀ z, φ z ∈ D ↔ z ∈ D := by
    intro z
    rw [MulAut.conj_apply]
    refine ⟨fun h => ?_, fun h => hC.setup.conj_mem g h⟩
    have := hC.setup.conj_mem g⁻¹ h
    simpa [mul_assoc] using this
  have hd : g * hC.d * g⁻¹ = φ hC.d := (MulAut.conj_apply g hC.d).symm
  have hx' : φ.symm x ∈ commSet D hC.d := by
    rw [← mem_commSet_map_iff φ hφD, MulEquiv.apply_symm_apply, ← hd]
    exact hx
  have hy' : φ.symm y ∈ commSet D hC.d := by
    rw [← mem_commSet_map_iff φ hφD, MulEquiv.apply_symm_apply, ← hd]
    exact hy
  have hxy' : ¬ Commute (φ.symm x) (φ.symm y) := fun h =>
    hxy (by simpa using (commute_map_iff φ).mpr h)
  have himg : gammaAt D x y (g * hC.d * g⁻¹) = φ '' gammaAt D (φ.symm x) (φ.symm y) hC.d := by
    ext z
    obtain ⟨z, rfl⟩ := φ.surjective z
    rw [φ.injective.mem_set_image, hd, ← mem_gammaAt_map_iff φ hφD (x := φ.symm x)
      (y := φ.symm y) (v := hC.d) (z := z), MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rw [himg, Set.ncard_image_of_injective _ φ.injective,
    ncard_gammaAt_pivot hC hMZ hα hs hn hSp hx' hy' hxy']

omit [Finite G] in
theorem not_commute_of_not_reach {x y a b z₁ z₂ : G}
    (hab : ¬ Reach (commSet D x ∩ commSet D y) a b) (hz₁ : z₁ ∈ compSet D x y a)
    (hz₂ : z₂ ∈ compSet D x y b) : ¬ Commute z₁ z₂ := by
  intro h
  have h1 : z₂ ∈ compSet D x y a := mem_compSet_of_commute hz₁ hz₂.1 h
  exact hab (reach_trans h1.2 (reach_symm hz₂.2))

omit [Finite G] in
theorem eq_of_closedTwin_compSet {x y d : G}
    (hZ : ∀ v ∈ compSet D x y d, ∀ b ∈ gammaAt D x y v, ∃ c ∈ gammaAt D x y v, ¬ Commute b c)
    {a b : G} (ha : a ∈ compSet D x y d) (hb : b ∈ compSet D x y d) (hab : Commute a b)
    (htw : ∀ c ∈ compSet D x y d, Commute c a ↔ Commute c b) : a = b := by
  have h := noClosedTwins_inClosure_compSet hZ ⟨a, Subgroup.subset_closure ha⟩ ha
    ⟨b, Subgroup.subset_closure hb⟩ hb (Subtype.ext hab.eq) fun c hc =>
      ⟨fun h => Subtype.ext ((htw _ hc).mp (congrArg Subtype.val h.eq)),
        fun h => Subtype.ext ((htw _ hc).mpr (congrArg Subtype.val h.eq))⟩
  exact congrArg Subtype.val h

theorem exists_vec_commSet (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ}
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s) :
    ∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (vec : G → (Fin k ⊕ Fin k → F)),
      n = 2 * k ∧ Nat.card F = 2 ^ f ∧
      (∀ z ∈ commSet D hC.d, vec z ≠ 0) ∧
      (∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d, vec z = vec z' → z = z') ∧
      (∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d,
        (Commute z z' ↔ spForm k F (vec z) (vec z') = 0)) := by
  classical
  have hZ := center_Hbar_eq_bot hC
  obtain ⟨k, F, _, _, τ, hnk, hF, -, hτs, hτi, hτc⟩ :=
    exists_vectorModel (imageClass_isClass hC) hZ hs hSp
  have hne := (subset_rootBlock_and_ne_of_isSymplecticTransvection (imageClass_isClass hC) hZ hs
    hSp).2
  have hinj := injOn_mk_DstarH_of_rootBlock_ne hC hMZ hs hne
  have hmem : ∀ z (hz : z ∈ commSet D hC.d),
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha) ∈ imageClass hC :=
    fun z hz => ⟨_, mem_DstarH_of_mem_commSet hC hα hz, rfl⟩
  let vec : G → (Fin k ⊕ Fin k → F) := fun z =>
    if hz : z ∈ commSet D hC.d then Classical.choose (hτs _ (hmem z hz)) else 0
  have hvec : ∀ z (hz : z ∈ commSet D hC.d), vec z ≠ 0 ∧
      τ (vec z) = QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha) := by
    intro z hz
    simp only [vec, dif_pos hz]
    exact Classical.choose_spec (hτs _ (hmem z hz))
  refine ⟨k, F, inferInstance, inferInstance, vec, hnk, hF, fun z hz => (hvec z hz).1, ?_, ?_⟩
  · intro z hz z' hz' h
    have h1 := (hvec z hz).2
    rw [h, (hvec z' hz').2] at h1
    exact congrArg Subtype.val (hinj (mem_DstarH_of_mem_commSet hC hα hz)
      (mem_DstarH_of_mem_commSet hC hα hz') h1.symm)
  · intro z hz z' hz'
    rw [commute_iff_commute_mk hC hMZ hα hz hz', ← (hvec z hz).2, ← (hvec z' hz').2,
      hτc _ _ (hvec z hz).1 (hvec z' hz').1]

theorem not_disconnected_commSet_pivot (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {w : G} (hw : w ∈ D) (hdw : ¬ Commute hC.d w) :
    ¬ Disconnected (commSet D hC.d ∩ commSet D w) := by
  classical
  rintro ⟨a, ha, b, hb, hab⟩
  have hdmem : ∀ v ∈ commSet D hC.d ∩ commSet D w, hC.d ∈ commSet D v ∧ w ∈ commSet D v :=
    fun v hv => ⟨⟨hC.hd, hv.1.2.1.symm, fun h => hv.1.2.2 h.symm⟩,
      ⟨hw, hv.2.2.1.symm, fun h => hv.2.2.2 h.symm⟩⟩
  have hloc : ∀ v ∈ commSet D hC.d ∩ commSet D w, LocalPivot D hC.d w v := fun v hv =>
    localPivot_of_mem hC hMZ hα hs hn hf hSp hv.1.1 (hdmem v hv).1 (hdmem v hv).2 hdw
  have hcnt : ∀ v ∈ commSet D hC.d ∩ commSet D w,
      (insert v (gammaAt D hC.d w v)).ncard = 2 ^ (f * (n - 2)) := by
    intro v hv
    have hnot : v ∉ gammaAt D hC.d w v := fun h => h.2.2.2 rfl
    rw [Set.ncard_insert_of_notMem hnot (Set.toFinite _),
      ncard_gammaAt_of_mem hC hMZ hα hs hn hSp hv.1.1 (hdmem v hv).1 (hdmem v hv).2 hdw]
    have : 1 ≤ 2 ^ (f * (n - 2)) := Nat.one_le_two_pow
    omega
  have hsub : ∀ e ∈ commSet D hC.d ∩ commSet D w,
      insert e (gammaAt D hC.d w e) ⊆ compSet D hC.d w e := by
    intro e he z hz
    rcases hz with rfl | hz
    · exact mem_compSet_self he
    · exact gammaAt_subset_compSet (mem_compSet_self he) hz
  have htw : ∀ e ∈ commSet D hC.d ∩ commSet D w, ∀ z ∈ compSet D hC.d w e,
      ∀ z' ∈ compSet D hC.d w e, Commute z z' →
        (∀ c ∈ compSet D hC.d w e, Commute c z ↔ Commute c z') → z = z' :=
    fun e _ z hz z' hz' hc htw' => eq_of_closedTwin_compSet
      (fun v hv => (hloc v (compSet_subset _ _ _ _ hv)).2.2.2.1) hz hz' hc htw'
  obtain ⟨k, F, _, _, vec, hnk, hF, hv0, hvinj, hvc⟩ := exists_vec_commSet hC hMZ hα hs hSp
  have hΓd : ∀ e ∈ commSet D hC.d ∩ commSet D w, compSet D hC.d w e ⊆ commSet D hC.d :=
    fun e _ z hz => hz.1.1
  have hprop : ∀ e ∈ commSet D hC.d ∩ commSet D w, ∀ z ∈ compSet D hC.d w e,
      ∀ z' ∈ compSet D hC.d w e, ∀ c : F, vec z' = c • vec z → vec z' = vec z := by
    intro e he z hz z' hz' c hc
    have hzd := hΓd e he hz
    have hzd' := hΓd e he hz'
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hv0 z' hzd' (by rw [hc, zero_smul])
    refine congrArg vec (htw e he z hz z' hz' ?_ fun t ht => ?_).symm
    · rw [hvc z hzd z' hzd', hc, map_smul, smul_eq_mul, spForm_self, mul_zero]
    · rw [hvc t (hΓd e he ht) z hzd, hvc t (hΓd e he ht) z' hzd', hc, map_smul, smul_eq_mul,
        mul_eq_zero, or_iff_right hc0]
  have hk : 2 ≤ k := by omega
  have hle := ncard_le_of_vectorConfig (k := k) (F := F) (by omega)
    (A := vec '' insert a (gammaAt D hC.d w a)) (C := vec '' compSet D hC.d w b) (va := vec a)
    (by rintro _ ⟨z, hz, rfl⟩; exact hv0 z (hΓd a ha (hsub a ha hz)))
    (by rintro _ ⟨z, hz, rfl⟩; exact hv0 z (hΓd b hb hz))
    (by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩ c hc
      exact hprop a ha z (hsub a ha hz) z' (hsub a ha hz') c hc)
    (by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩ c hc
      exact hprop b hb z hz z' hz' c hc)
    (by
      rintro _ ⟨z, hz, rfl⟩
      rcases hz with rfl | hz
      · exact spForm_self _
      · exact (hvc z hz.1.1 a ha.1 ).mp hz.2.2.1)
    (by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
      exact fun h => not_commute_of_not_reach hab (hsub a ha hz) hz'
        ((hvc z (hΓd a ha (hsub a ha hz)) z' (hΓd b hb hz')).mpr h))
    (by
      rintro _ ⟨z, hz, rfl⟩
      exact fun h => not_commute_of_not_reach hab (mem_compSet_self ha) hz
        ((hvc z (hΓd b hb hz) a ha.1).mpr h).symm)
    (by
      rw [Set.InjOn.ncard_image (fun z hz z' hz' h => hvinj z (hΓd a ha (hsub a ha hz)) z'
        (hΓd a ha (hsub a ha hz')) h), hcnt a ha, hF, ← pow_mul, hnk])
  have hge : 2 ^ (f * (n - 2)) ≤ (vec '' compSet D hC.d w b).ncard := by
    rw [Set.InjOn.ncard_image (fun z hz z' hz' h => hvinj z (hΓd b hb hz) z' (hΓd b hb hz') h),
      ← hcnt b hb]
    exact Set.ncard_le_ncard (hsub b hb) (Set.toFinite _)
  rw [hF] at hle
  have h1 : 2 ^ f < 2 ^ (f * (n - 2)) := by
    apply Nat.pow_lt_pow_right (by norm_num)
    have : f * 2 ≤ f * (n - 2) := Nat.mul_le_mul_left f (by omega)
    omega
  omega

omit [Finite G] in
theorem reach_map_of_mapsTo {E E' : Set G} (φ : G →* G) (hφ : ∀ z ∈ E, φ z ∈ E') {a b : G}
    (h : Reach E a b) : Reach E' (φ a) (φ b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih ⟨hφ _ hbc.1, hφ _ hbc.2.1, hbc.2.2.map φ⟩

theorem not_disconnected_commSet_inter (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y) :
    ¬ Disconnected (commSet D x ∩ commSet D y) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hx.1)
  set φ := MulAut.conj g with hφdef
  have hφD : ∀ z, φ z ∈ D ↔ z ∈ D := by
    intro z
    rw [MulAut.conj_apply]
    refine ⟨fun h => ?_, fun h => hC.setup.conj_mem g h⟩
    have := hC.setup.conj_mem g⁻¹ h
    simpa [mul_assoc] using this
  have hφd : φ hC.d = x := by rw [MulAut.conj_apply, hg]
  have hy' : φ.symm y ∈ D := (hφD _).mp (by rw [MulEquiv.apply_symm_apply]; exact hy.1)
  have hdy' : ¬ Commute hC.d (φ.symm y) := fun h =>
    hxy (by simpa [hφd] using (commute_map_iff φ).mpr h)
  have hconn := not_disconnected_commSet_pivot hC hMZ hα hs hn hf hSp hy' hdy'
  have hmem : ∀ z, z ∈ commSet D x ∩ commSet D y ↔
      φ.symm z ∈ commSet D hC.d ∩ commSet D (φ.symm y) := by
    intro z
    rw [Set.mem_inter_iff, Set.mem_inter_iff, ← mem_commSet_map_iff φ hφD (a := hC.d),
      ← mem_commSet_map_iff φ hφD (a := φ.symm y), MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, hφd]
  rintro ⟨a, ha, b, hb, hab⟩
  apply hconn
  refine ⟨φ.symm a, (hmem a).mp ha, φ.symm b, (hmem b).mp hb, fun h => hab ?_⟩
  have := reach_map_of_mapsTo φ.toMonoidHom (E' := commSet D x ∩ commSet D y) (fun z hz => by
    rw [hmem]
    simpa using hz) h
  simpa using this

end CFSG.OddTranspositions.PartThree

end
