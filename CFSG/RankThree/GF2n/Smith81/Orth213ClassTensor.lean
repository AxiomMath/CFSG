module

public import CFSG.RankThree.GF2n.Smith81.Orth213ClassDefs
public import CFSG.RankThree.GF2n.Smith81.OrthFrameChange

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthClass

open QuadraticMap

section Tensors

variable {K : Type} [Field K] {ι : Type} {qU : QuadraticForm K (ι → K)}

theorem tCount_eq_ncard_pairTypeA (I : Set ((ι → K) × (ι → K))) :
    tCount qU I = {p | p ∈ I ∧ PairTypeA qU p}.ncard :=
  rfl

theorem qU_eq_zero_of_smul_eq_smul {v w : ι → K} (hqv : qU v = 0) {d c : K} (hd : d ≠ 0)
    (h : d • w = c • v) : qU w = 0 := by
  have hw : w = (d⁻¹ * c) • v := by
    rw [mul_smul, ← h, inv_smul_smul₀ hd]
  rw [hw, QuadraticMap.map_smul, hqv, smul_zero]

theorem pairTypeA_mk_smul_iff {u : ι → K} (hu0 : u ≠ 0) (hqu : qU u = 0) (s : ι → K) (t : K) :
    PairTypeA qU (s, t • u) ↔ (t = 0 ∧ s ≠ 0 ∧ qU s = 0) ∨ (t ≠ 0 ∧ ∃ α : K, s = α • u) := by
  constructor
  · rintro ⟨c₁, c₂, v, hc, hv0, hqv, hp⟩
    obtain ⟨hs, ht⟩ := Prod.mk.inj hp
    by_cases ht0 : t = 0
    · left
      have hc2 : c₂ = 0 := by
        rw [ht0, zero_smul] at ht
        exact (smul_eq_zero.mp ht.symm).resolve_right hv0
      have hc1 : c₁ ≠ 0 := hc.resolve_right (not_not.mpr hc2)
      refine ⟨ht0, ?_, ?_⟩
      · rw [hs]
        exact smul_ne_zero hc1 hv0
      · rw [hs, QuadraticMap.map_smul, hqv, smul_zero]
    · right
      refine ⟨ht0, c₁ * c₂⁻¹ * t, ?_⟩
      have hc2 : c₂ ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ht
        exact ht0 ((smul_eq_zero.mp ht).resolve_right hu0)
      have hv : v = (c₂⁻¹ * t) • u := by
        rw [mul_smul, ht, inv_smul_smul₀ hc2]
      rw [hs, hv, smul_smul, mul_assoc]
  · rintro (⟨rfl, hs0, hqs⟩ | ⟨ht0, α, rfl⟩)
    · exact ⟨1, 0, s, Or.inl one_ne_zero, hs0, hqs, by simp⟩
    · exact ⟨α, t, u, Or.inr ht0, hu0, hqu, rfl⟩

end Tensors

section Counting

variable {K : Type} [Field K] [Finite K] {ι : Type} [Finite ι] {qU : QuadraticForm K (ι → K)}

theorem ncard_nonzero_singular_add_one (P : (ι → K) → Prop) (hP : P 0) :
    {s | P s ∧ qU s = 0 ∧ s ≠ 0}.ncard + 1 = nSing qU P := by
  have h0 : (0 : ι → K) ∈ {s | P s ∧ qU s = 0} := ⟨hP, map_zero qU⟩
  have h := Set.ncard_sdiff_singleton_add_one h0
  have e : {s | P s ∧ qU s = 0} \ {0} = {s | P s ∧ qU s = 0 ∧ s ≠ 0} := by
    ext s
    simp [and_assoc]
  rw [e] at h
  exact h

end Counting

section Scalars

variable {K : Type} [Field K] [Finite K]

theorem ncard_nonzero_scalars_add_one : {t : K | t ≠ 0}.ncard + 1 = Nat.card K := by
  have h := Set.ncard_sdiff_singleton_add_one (Set.mem_univ (0 : K))
  have e : (Set.univ \ {0} : Set K) = {t | t ≠ 0} := by
    ext t
    simp
  rw [e, Set.ncard_univ] at h
  exact h

end Scalars

section LemmaT

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
  {qU : QuadraticForm K (ι → K)}

set_option linter.unusedSectionVars false in
theorem tCount_Ish_ne {u w : ι → K} (hu0 : u ≠ 0) (hqu : qU u = 0) (huw : polar qU u w = 0)
    {β : K} (hβ : β ≠ 0) :
    tCount qU (Ish qU u w β) + 1 = nSing qU (fun s => polar qU s u = 0 ∧ polar qU s w = 0) := by
  have hset : {p | p ∈ Ish qU u w β ∧ PairTypeA qU p} =
      (fun s : ι → K => (s, (0 : ι → K))) ''
        {s | (polar qU s u = 0 ∧ polar qU s w = 0) ∧ qU s = 0 ∧ s ≠ 0} := by
    ext ⟨s, y⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.mk.injEq, Ish]
    constructor
    · rintro ⟨⟨hsu, t, rfl, hsw⟩, hA⟩
      rcases (pairTypeA_mk_smul_iff hu0 hqu s t).mp hA with ⟨rfl, hs0, hqs⟩ | ⟨ht0, α, rfl⟩
      · exact ⟨s, ⟨⟨hsu, by simpa using hsw⟩, hqs, hs0⟩, rfl, by simp⟩
      · exfalso
        rw [polar_smul_left, huw, smul_zero] at hsw
        exact ht0 ((mul_eq_zero.mp hsw.symm).resolve_left hβ)
    · rintro ⟨s', ⟨⟨hsu, hsw⟩, hqs, hs0⟩, rfl, rfl⟩
      refine ⟨⟨hsu, 0, by simp, by simpa using hsw⟩, ?_⟩
      simpa using (pairTypeA_mk_smul_iff hu0 hqu s' 0).mpr (Or.inl ⟨rfl, hs0, hqs⟩)
  have hinj : Function.Injective (fun s : ι → K => (s, (0 : ι → K))) :=
    fun a b h => (Prod.mk.inj h).1
  rw [tCount_eq_ncard_pairTypeA, hset, Set.ncard_image_of_injective _ hinj]
  exact ncard_nonzero_singular_add_one _ ⟨polar_zero_left _ _, polar_zero_left _ _⟩

set_option linter.unusedSectionVars false in
theorem tCount_Ish_zero {u w : ι → K} (hu0 : u ≠ 0) (hqu : qU u = 0) (huw : polar qU u w = 0) :
    tCount qU (Ish qU u w 0) + 1 + Nat.card K =
      nSing qU (fun s => polar qU s u = 0 ∧ polar qU s w = 0) + Nat.card K ^ 2 := by
  have hset : {p | p ∈ Ish qU u w 0 ∧ PairTypeA qU p} =
      (fun s : ι → K => (s, (0 : ι → K))) ''
        {s | (polar qU s u = 0 ∧ polar qU s w = 0) ∧ qU s = 0 ∧ s ≠ 0} ∪
      (fun x : K × K => (x.1 • u, x.2 • u)) '' (Set.univ ×ˢ {t : K | t ≠ 0}) := by
    ext ⟨s, y⟩
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Prod.mk.injEq, Ish]
    constructor
    · rintro ⟨⟨hsu, t, rfl, hsw⟩, hA⟩
      rcases (pairTypeA_mk_smul_iff hu0 hqu s t).mp hA with ⟨rfl, hs0, hqs⟩ | ⟨ht0, α, rfl⟩
      · exact Or.inl ⟨s, ⟨⟨hsu, by simpa using hsw⟩, hqs, hs0⟩, rfl, by simp⟩
      · exact Or.inr ⟨(α, t), ⟨Set.mem_univ _, ht0⟩, rfl, rfl⟩
    · rintro (⟨s', ⟨⟨hsu, hsw⟩, hqs, hs0⟩, rfl, rfl⟩ | ⟨⟨a, t⟩, ⟨-, ht0⟩, rfl, rfl⟩)
      · refine ⟨⟨hsu, 0, by simp, by simpa using hsw⟩, ?_⟩
        simpa using (pairTypeA_mk_smul_iff hu0 hqu s' 0).mpr (Or.inl ⟨rfl, hs0, hqs⟩)
      · refine ⟨⟨?_, t, rfl, ?_⟩, ?_⟩
        · rw [polar_smul_left, polar_self, hqu]
          simp
        · rw [polar_smul_left, huw]
          simp
        · exact (pairTypeA_mk_smul_iff hu0 hqu _ t).mpr (Or.inr ⟨ht0, a, rfl⟩)
  have hinj1 : Function.Injective (fun s : ι → K => (s, (0 : ι → K))) :=
    fun a b h => (Prod.mk.inj h).1
  have hinj2 : Function.Injective (fun x : K × K => (x.1 • u, x.2 • u)) := by
    rintro ⟨a, t⟩ ⟨a', t'⟩ h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    simp only at h1 h2
    rw [smul_left_inj hu0] at h1 h2
    rw [h1, h2]
  have hdisj : Disjoint ((fun s : ι → K => (s, (0 : ι → K))) ''
        {s | (polar qU s u = 0 ∧ polar qU s w = 0) ∧ qU s = 0 ∧ s ≠ 0})
      ((fun x : K × K => (x.1 • u, x.2 • u)) '' (Set.univ ×ˢ {t : K | t ≠ 0})) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, -, rfl⟩ ⟨⟨a, t⟩, ⟨-, ht0⟩, h⟩
    have h2 := (Prod.mk.inj h).2
    exact ht0 ((smul_eq_zero.mp h2).resolve_right hu0)
  have h1 := ncard_nonzero_singular_add_one (qU := qU)
    (fun s => polar qU s u = 0 ∧ polar qU s w = 0) ⟨polar_zero_left _ _, polar_zero_left _ _⟩
  have h2 : Nat.card K * ({t : K | t ≠ 0}.ncard + 1) = Nat.card K * Nat.card K := by
    rw [ncard_nonzero_scalars_add_one]
  rw [tCount_eq_ncard_pairTypeA, hset, Set.ncard_union_eq hdisj,
    Set.ncard_image_of_injective _ hinj1, Set.ncard_image_of_injective _ hinj2, Set.ncard_prod,
    Set.ncard_univ, ← h1]
  nlinarith [h2]

set_option linter.unusedSectionVars false in
theorem tCount_pureLine {d₀ d₁ : K} (hd : d₀ ≠ 0 ∨ d₁ ≠ 0) (u : ι → K) :
    tCount qU {p | ∃ w, polar qU w u = 0 ∧ p = (d₀ • w, d₁ • w)} + 1 =
      nSing qU (fun s => polar qU s u = 0) := by
  have hset : {p | p ∈ {p | ∃ w, polar qU w u = 0 ∧ p = (d₀ • w, d₁ • w)} ∧ PairTypeA qU p} =
      (fun w : ι → K => (d₀ • w, d₁ • w)) '' {w | polar qU w u = 0 ∧ qU w = 0 ∧ w ≠ 0} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨w, hwu, rfl⟩, c₁, c₂, v, hc, hv0, hqv, hp⟩
      obtain ⟨h1, h2⟩ := Prod.mk.inj hp
      refine ⟨w, ⟨hwu, ?_, ?_⟩, rfl⟩
      · rcases hd with hd0 | hd1
        · exact qU_eq_zero_of_smul_eq_smul hqv hd0 h1
        · exact qU_eq_zero_of_smul_eq_smul hqv hd1 h2
      · rintro rfl
        rw [smul_zero] at h1 h2
        rcases hc with hc1 | hc2
        · exact hc1 ((smul_eq_zero.mp h1.symm).resolve_right hv0)
        · exact hc2 ((smul_eq_zero.mp h2.symm).resolve_right hv0)
    · rintro ⟨w, ⟨hwu, hqw, hw0⟩, rfl⟩
      exact ⟨⟨w, hwu, rfl⟩, d₀, d₁, w, hd, hw0, hqw, rfl⟩
  have hinj : Function.Injective (fun w : ι → K => (d₀ • w, d₁ • w)) := by
    intro a b h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    rcases hd with hd0 | hd1
    · exact (smul_right_inj hd0).mp h1
    · exact (smul_right_inj hd1).mp h2
  rw [tCount_eq_ncard_pairTypeA, hset, Set.ncard_image_of_injective _ hinj]
  exact ncard_nonzero_singular_add_one (fun s => polar qU s u = 0) (polar_zero_left _ _)

set_option linter.unusedSectionVars false in
theorem tCount_image (H : Matrix (Fin 2) (Fin 2) K) (hH : H.det ≠ 0)
    (I : Set ((ι → K) × (ι → K))) :
    tCount qU ((fun p => orthTensor H id p) '' I) = tCount qU I := by
  let h : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero H hH
  have hcoe : (h : Matrix (Fin 2) (Fin 2) K) = H :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero H hH
  have hinj : Function.Injective (fun p : (ι → K) × (ι → K) => orthTensor H id p) := by
    intro a b hab
    apply (orthTensorEquiv h).injective
    rw [orthTensorEquiv_apply, orthTensorEquiv_apply, hcoe]
    exact hab
  have hset : {p | p ∈ (fun p => orthTensor H id p) '' I ∧ PairTypeA qU p} =
      (fun p => orthTensor H id p) '' {p | p ∈ I ∧ PairTypeA qU p} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, hA⟩
      refine ⟨q, ⟨hq, ?_⟩, rfl⟩
      rw [← hcoe] at hA
      exact (pairTypeA_orthTensor_id_iff h qU q).mp hA
    · rintro ⟨q, ⟨hq, hA⟩, rfl⟩
      refine ⟨⟨q, hq, rfl⟩, ?_⟩
      rw [← hcoe]
      exact (pairTypeA_orthTensor_id_iff h qU q).mpr hA
  rw [tCount_eq_ncard_pairTypeA, hset, Set.ncard_image_of_injective _ hinj]
  rfl

end LemmaT

end CFSG.RankThree.GF2n.Smith81.OrthClass
