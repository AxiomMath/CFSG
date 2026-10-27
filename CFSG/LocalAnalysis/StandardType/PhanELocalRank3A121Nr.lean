module

public import CFSG.LocalAnalysis.StandardType.PhanELocalClsT
public import CFSG.LocalAnalysis.StandardType.PhanELocalSigma

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] def W2 : Submodule K (Fin 4 → K) := Vtail ⊓ Vsub 4 3

@[expose] noncomputable def NRvec (w : Fin 4 → K) : Prop :=
  w ≠ 0 ∧ Submodule.span K {w} ⊓ sgS K f 4 (Submodule.span K {w}) = ⊥

@[expose] def dirVec (ω : K) : Fin 4 → K := ![0, 1, ω, 0]

private theorem plh_mem_Vsub_three_iff (v : Fin 4 → K) : v ∈ Vsub 4 3 ↔ v 3 = 0 := by
  constructor
  · intro hv
    exact hv 3 le_rfl
  · intro hv j hj
    have hj3 : j = 3 := Fin.ext (by omega)
    subst hj3
    exact hv

private theorem plh_sgv_ne_zero {w : Fin 4 → K} (hw : w ≠ 0) : sgv K f 4 w ≠ 0 := by
  intro h
  apply hw
  funext i
  exact (sg K f).map_eq_zero_iff.mp (by simpa [sgv_apply] using congrFun h i)

private theorem plh_mem_span_sgv_iff (hK : Nat.card K = (2 ^ f) ^ 2) {w : Fin 4 → K}
    (hw : w ∈ (W2 : Submodule K (Fin 4 → K))) (hwn : w ≠ 0) :
    sgv K f 4 w ∈ Submodule.span K {w} ↔ w 1 * sg K f (w 2) = w 2 * sg K f (w 1) := by
  rw [W2, Submodule.mem_inf] at hw
  obtain ⟨hw0', hw3'⟩ := hw
  have hw0 : w 0 = 0 := by simpa [Vtail] using hw0'
  have hw3 : w 3 = 0 := (plh_mem_Vsub_three_iff w).mp hw3'
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have h1 : sg K f (w 1) = c * w 1 := by
      simpa [sgv_apply, smul_eq_mul] using (congrFun hc 1).symm
    have h2 : sg K f (w 2) = c * w 2 := by
      simpa [sgv_apply, smul_eq_mul] using (congrFun hc 2).symm
    rw [h2, h1]
    ring
  · intro h
    by_cases h1 : w 1 = 0
    · have h2 : w 2 ≠ 0 := by
        intro h2
        apply hwn
        funext i
        fin_cases i <;> simp [hw0, hw3, h1, h2]
      refine ⟨sg K f (w 2) / w 2, ?_⟩
      funext i
      fin_cases i
      · simp [sgv_apply, hw0]
      · simp [sgv_apply, h1]
      · rw [sgv_apply]
        show sg K f (w 2) / w 2 * w 2 = sg K f (w 2)
        exact div_mul_cancel₀ _ h2
      · simp [sgv_apply, hw3]
    · have hh : sg K f (w 1) / w 1 * w 2 = sg K f (w 2) := by
        rw [div_mul_eq_mul_div, mul_comm (sg K f (w 1)) (w 2), ← h]
        field_simp
      refine ⟨sg K f (w 1) / w 1, ?_⟩
      funext i
      fin_cases i
      · simp [sgv_apply, hw0]
      · rw [sgv_apply]
        show sg K f (w 1) / w 1 * w 1 = sg K f (w 1)
        exact div_mul_cancel₀ _ h1
      · simpa [sgv_apply] using hh
      · simp [sgv_apply, hw3]

theorem mem_W2_iff (w : Fin 4 → K) : w ∈ (W2 : Submodule K (Fin 4 → K)) ↔ w 0 = 0 ∧ w 3 = 0 := by
  rw [W2, Submodule.mem_inf]
  constructor
  · rintro ⟨h0, h3⟩
    exact ⟨by simpa [Vtail] using h0, (plh_mem_Vsub_three_iff w).mp h3⟩
  · rintro ⟨h0, h3⟩
    exact ⟨by simpa [Vtail] using h0, (plh_mem_Vsub_three_iff w).mpr h3⟩

theorem nrvec_iff (hK : Nat.card K = (2 ^ f) ^ 2) {w : Fin 4 → K}
    (hw : w ∈ (W2 : Submodule K (Fin 4 → K))) :
    NRvec f w ↔ w ≠ 0 ∧ w 1 * sg K f (w 2) ≠ w 2 * sg K f (w 1) := by
  rw [NRvec, sgS_span_singleton hK]
  constructor
  · rintro ⟨hwn, hdisj⟩
    refine ⟨hwn, ?_⟩
    intro heq
    have hmem : sgv K f 4 w ∈ Submodule.span K {w} :=
      (plh_mem_span_sgv_iff f hK hw hwn).mpr heq
    have hne : sgv K f 4 w ≠ 0 := plh_sgv_ne_zero f hwn
    have hbot : sgv K f 4 w ∈ (⊥ : Submodule K (Fin 4 → K)) := by
      rw [← hdisj]
      exact ⟨hmem, Submodule.mem_span_singleton_self _⟩
    exact hne ((Submodule.mem_bot _).mp hbot)
  · rintro ⟨hwn, hne⟩
    refine ⟨hwn, ?_⟩
    have hne' : sgv K f 4 w ≠ 0 := plh_sgv_ne_zero f hwn
    rw [← disjoint_iff, Submodule.disjoint_span_singleton' hne']
    intro hmem
    exact hne ((plh_mem_span_sgv_iff f hK hw hwn).mp hmem)

theorem nrvec_dirVec (hK : Nat.card K = (2 ^ f) ^ 2) {ω : K} (h : sg K f ω ≠ ω) :
    NRvec f (dirVec ω) ∧ dirVec ω ∈ (W2 : Submodule K (Fin 4 → K)) := by
  have hmem : dirVec ω ∈ (W2 : Submodule K (Fin 4 → K)) := by
    rw [mem_W2_iff]
    constructor <;> simp [dirVec]
  refine ⟨?_, hmem⟩
  rw [nrvec_iff f hK hmem]
  constructor
  · intro h0
    have := congrFun h0 1
    simp [dirVec] at this
  · simpa [dirVec, map_one] using h

private theorem plh_ne_iff_add_ne_zero {x y : K} : x ≠ y ↔ x + y ≠ 0 := by
  constructor
  · intro h h0
    exact h (CharTwo.add_eq_zero.mp h0)
  · intro h hxy
    exact h (by rw [hxy, CharTwo.add_self_eq_zero])

private theorem plh_nrvec_iff_det (hK : Nat.card K = (2 ^ f) ^ 2) {v : Fin 4 → K}
    (hv : v ∈ (W2 : Submodule K (Fin 4 → K))) :
    NRvec f v ↔ v ≠ 0 ∧ v 1 * sg K f (v 2) + v 2 * sg K f (v 1) ≠ 0 := by
  rw [nrvec_iff f hK hv]
  constructor
  · rintro ⟨hvn, hne⟩
    exact ⟨hvn, plh_ne_iff_add_ne_zero.mp hne⟩
  · rintro ⟨hvn, h0⟩
    exact ⟨hvn, plh_ne_iff_add_ne_zero.mpr h0⟩

private theorem plh_det_eq_zero_of_not_nrvec (hK : Nat.card K = (2 ^ f) ^ 2) {v : Fin 4 → K}
    (hv : v ∈ (W2 : Submodule K (Fin 4 → K))) (h : ¬ NRvec f v) :
    v 1 * sg K f (v 2) + v 2 * sg K f (v 1) = 0 := by
  have h' := (plh_nrvec_iff_det f hK hv).not.mp h
  rcases not_and_or.mp h' with h0 | h0
  · rw [not_not] at h0
    subst h0
    simp
  · exact not_not.mp h0

private theorem plh_det_expand (hK : Nat.card K = (2 ^ f) ^ 2) {w δ : Fin 4 → K} (β : K) :
    (w 1 + β * δ 1) * sg K f (w 2 + β * δ 2) +
        (w 2 + β * δ 2) * sg K f (w 1 + β * δ 1) =
      (δ 1 * sg K f (δ 2) + δ 2 * sg K f (δ 1)) * (β * sg K f β) +
        (w 1 * sg K f (δ 2) + w 2 * sg K f (δ 1)) * sg K f β +
        sg K f (w 1 * sg K f (δ 2) + w 2 * sg K f (δ 1)) * β +
        (w 1 * sg K f (w 2) + w 2 * sg K f (w 1)) := by
  simp only [map_add, map_mul, sg_sg hK]
  ring

private theorem plh_herm_iff (hK : Nat.card K = (2 ^ f) ^ 2) {A B C : K}
    (hA : A ≠ 0) (hAf : sg K f A = A) (β : K) :
    A * (β * sg K f β) + B * sg K f β + sg K f B * β + C = 0 ↔
      (A * β + B) * sg K f (A * β + B) = A * C + B * sg K f B := by
  have hkey : (A * β + B) * sg K f (A * β + B) =
      A * (A * (β * sg K f β) + B * sg K f β + sg K f B * β + C) +
        (A * C + B * sg K f B) := by
    simp only [map_add, map_mul, hAf]
    ring_nf
    simp [CharTwo.two_eq_zero, CharTwo.two_nsmul]
  constructor
  · intro h
    rw [hkey, h, mul_zero, zero_add]
  · intro h
    have h2 : A * (A * (β * sg K f β) + B * sg K f β + sg K f B * β + C) +
        (A * C + B * sg K f B) = 0 + (A * C + B * sg K f B) := by
      rw [zero_add, ← hkey, h]
    have h3 : A * (A * (β * sg K f β) + B * sg K f β + sg K f B * β + C) = 0 :=
      add_right_cancel h2
    exact (mul_eq_zero.mp h3).resolve_left hA

private theorem plh_card_hermitian_le (hK : Nat.card K = (2 ^ f) ^ 2) {A B C : K}
    (hA : A ≠ 0) (hAf : sg K f A = A) :
    Nat.card {β : K // A * (β * sg K f β) + B * sg K f β + sg K f B * β + C = 0} ≤
      2 ^ f + 1 := by
  classical
  haveI := Fintype.ofFinite K
  have hpow : ∀ u : K, u * sg K f u = u ^ (2 ^ f + 1) := by
    intro u
    have hσ : sg K f u = u ^ 2 ^ f :=
      CFSG.LieType.BorelTits.unitaryInvolution_apply K 2 f u
    rw [hσ, pow_succ']
  have hmaps : ∀ β : K, A * (β * sg K f β) + B * sg K f β + sg K f B * β + C = 0 →
      (A * β + B) ∈ Polynomial.nthRootsFinset (2 ^ f + 1) (A * C + B * sg K f B) := by
    intro β hβ
    rw [Polynomial.mem_nthRootsFinset (by positivity), ← hpow]
    exact (plh_herm_iff f hK hA hAf β).mp hβ
  set T : Finset K := Polynomial.nthRootsFinset (2 ^ f + 1) (A * C + B * sg K f B) with hT
  have hcardT : Nat.card {u : K // u ∈ T} ≤ 2 ^ f + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have huniv : (Finset.univ.filter (fun u : K => u ∈ T)) = T := by ext u; simp
    rw [huniv, hT, Polynomial.nthRootsFinset_def]
    exact le_trans
      (Multiset.toFinset_card_le
        (m := Polynomial.nthRoots (2 ^ f + 1) (A * C + B * sg K f B)))
      (Polynomial.card_nthRoots _ _)
  refine le_trans (Nat.card_le_card_of_injective
    (fun β : {β : K // A * (β * sg K f β) + B * sg K f β + sg K f B * β + C = 0} =>
      (⟨A * β.1 + B, hmaps β.1 β.2⟩ : {u : K // u ∈ T})) ?_) hcardT
  intro β γ h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext (mul_left_cancel₀ hA (add_right_cancel h))

theorem card_not_nrvec_le (hK : Nat.card K = (2 ^ f) ^ 2) {δ : Fin 4 → K}
    (hδ : δ ∈ (W2 : Submodule K (Fin 4 → K))) (hδn : NRvec f δ) {w : Fin 4 → K}
    (hw : w ∈ (W2 : Submodule K (Fin 4 → K))) {α : K} (hα : α ≠ 0) :
    Nat.card {s : K // ¬ NRvec f (w + (α * s) • δ)} ≤ 2 ^ f + 1 := by
  classical
  haveI := Fintype.ofFinite K
  set A : K := δ 1 * sg K f (δ 2) + δ 2 * sg K f (δ 1) with hAdef
  set B : K := w 1 * sg K f (δ 2) + w 2 * sg K f (δ 1) with hBdef
  set C : K := w 1 * sg K f (w 2) + w 2 * sg K f (w 1) with hCdef
  have hA_ne : A ≠ 0 := by
    rw [hAdef]
    exact ((plh_nrvec_iff_det f hK hδ).mp hδn).2
  have hAf : sg K f A = A := by
    rw [hAdef]
    simp only [map_add, map_mul, sg_sg hK]
    ring
  have hsub : ∀ s : K, ¬ NRvec f (w + (α * s) • δ) →
      A * ((α * s) * sg K f (α * s)) + B * sg K f (α * s) + sg K f B * (α * s) + C = 0 := by
    intro s hs
    have hv : w + (α * s) • δ ∈ (W2 : Submodule K (Fin 4 → K)) :=
      Submodule.add_mem _ hw (Submodule.smul_mem _ _ hδ)
    have hzero := plh_det_eq_zero_of_not_nrvec f hK hv hs
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hzero
    rw [plh_det_expand f hK (α * s)] at hzero
    simpa only [hAdef, hBdef, hCdef] using hzero
  refine le_trans (Nat.card_le_card_of_injective
    (fun s : {s : K // ¬ NRvec f (w + (α * s) • δ)} =>
      (⟨α * s.1, hsub s.1 s.2⟩ :
        {β : K // A * (β * sg K f β) + B * sg K f β + sg K f B * β + C = 0})) ?_)
    (plh_card_hermitian_le f hK hA_ne hAf)
  intro s t h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext (mul_left_cancel₀ hα h)

private theorem plh_W2_le_span_dirVec {ω ω' : K} (h : ω ≠ ω') :
    W2 ≤ Submodule.span K {dirVec ω} ⊔ Submodule.span K {dirVec ω'} := by
  intro v hv
  obtain ⟨hv0, hv3⟩ := (mem_W2_iff v).mp hv
  set y : K := (v 2 + v 1 * ω) / (ω' + ω) with hy
  set x : K := v 1 + y with hx
  have hne : ω' + ω ≠ 0 := fun h0 => h (CharTwo.add_eq_zero.mp h0).symm
  have hxy : x + y = v 1 := by rw [hx, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hdd : y * (ω' + ω) = v 2 + v 1 * ω := by
    rw [hy, div_mul_cancel₀ _ hne]
  have hxω : x * ω + y * ω' = v 2 := by
    calc x * ω + y * ω'
        = v 1 * ω + (y * ω + y * ω') := by rw [hx]; ring
      _ = v 1 * ω + y * (ω + ω') := by ring
      _ = v 1 * ω + y * (ω' + ω) := by rw [add_comm ω ω']
      _ = v 1 * ω + (v 2 + v 1 * ω) := by rw [hdd]
      _ = v 2 := by
            rw [add_comm (v 1 * ω) (v 2 + v 1 * ω), add_assoc, CharTwo.add_self_eq_zero,
              add_zero]
  rw [Submodule.mem_sup]
  refine ⟨x • dirVec ω, ?_, y • dirVec ω', ?_, ?_⟩
  · rw [Submodule.mem_span_singleton]; exact ⟨x, rfl⟩
  · rw [Submodule.mem_span_singleton]; exact ⟨y, rfl⟩
  · funext j
    fin_cases j
    · simp [dirVec, hv0]
    · simpa [dirVec] using hxy
    · simpa [dirVec] using hxω
    · simp [dirVec, hv3]

theorem exists_nrvec_dir_avoid (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (S : Finset (Submodule K (Fin 4 → K))) (hS : ∀ P ∈ S, P ≤ Vtail ∧ ¬ W2 ≤ P)
    (hcard : S.card ≤ 3) : ∃ ω : K, sg K f ω ≠ ω ∧ ∀ P ∈ S, dirVec ω ∉ P := by
  classical
  haveI := Fintype.ofFinite K
  set bad : Finset K := S.biUnion (fun P => Finset.univ.filter (fun ω => dirVec ω ∈ P)) with hbad
  have hbad_le : bad.card ≤ 3 := by
    calc bad.card ≤ ∑ P ∈ S, (Finset.univ.filter (fun ω => dirVec ω ∈ P)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ P ∈ S, 1 := by
          refine Finset.sum_le_sum ?_
          intro P hP
          refine Finset.card_le_one.mpr ?_
          intro a ha b hb
          by_contra hab
          have hW2P : W2 ≤ P := by
            refine (plh_W2_le_span_dirVec hab).trans ?_
            exact sup_le
              ((Submodule.span_singleton_le_iff_mem (dirVec a) P).mpr (Finset.mem_filter.mp ha).2)
              ((Submodule.span_singleton_le_iff_mem (dirVec b) P).mpr (Finset.mem_filter.mp hb).2)
          exact (hS P hP).2 hW2P
      _ = S.card := by simp
      _ ≤ 3 := hcard
  set M : Finset K := Finset.univ.filter (fun ω => sg K f ω ≠ ω) with hM
  have hMcard : M.card = Nat.card {ω : K // sg K f ω ≠ ω} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hmoved : Nat.card K - 2 ^ f ≤ M.card := by
    rw [hMcard]
    exact card_sg_moved_ge (K := K) (f := f) hK
  have hgt : 3 < M.card := by
    have h3 : 3 < Nat.card K - 2 ^ f := by
      rw [hK]
      have hmul : 2 ^ f * (2 ^ f - 1) = (2 ^ f) ^ 2 - 2 ^ f := by
        rw [pow_two, Nat.mul_sub_left_distrib, Nat.mul_one]
      rw [← hmul]
      calc 3 < 4 * 3 := by norm_num
        _ ≤ 2 ^ f * (2 ^ f - 1) := Nat.mul_le_mul hq (by omega)
    omega
  obtain ⟨ω, hωM, hωbad⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (by omega : bad.card < M.card)
  rw [hM] at hωM
  rw [hbad] at hωbad
  refine ⟨ω, (Finset.mem_filter.mp hωM).2, ?_⟩
  intro P hP hmem
  exact hωbad (Finset.mem_biUnion.mpr
    ⟨P, hP, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩⟩)

end CFSG.ClassicalInvolution.Phan.PhanE

end
