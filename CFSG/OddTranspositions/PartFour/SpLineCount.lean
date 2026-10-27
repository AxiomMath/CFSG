module

public import CFSG.OddTranspositions.PartFour.LinePolar
public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpNormal
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsC
import CFSG.RankThree.PartOne.KC.SymplecticFullRankTwo

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {k : ℕ} {F : Type} [Field F]

theorem spForm_single_inl_left (i : Fin k) (v : Fin k ⊕ Fin k → F) :
    spForm k F (Pi.single (Sum.inl i) (1 : F)) v = v (Sum.inr i) := by
  rw [spForm_apply]
  simp [dotProduct, Pi.single_apply,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, Matrix.fromBlocks_mulVec]

theorem spForm_single_inl_right (i : Fin k) (v : Fin k ⊕ Fin k → F) :
    spForm k F v (Pi.single (Sum.inl i) (1 : F)) = - v (Sum.inr i) := by
  have h := spForm_isAlt.neg_eq (Pi.single (Sum.inl i) (1 : F)) v
  rw [spForm_single_inl_left] at h
  exact h.symm

theorem spForm_single_inr_right (i : Fin k) (v : Fin k ⊕ Fin k → F) :
    spForm k F v (Pi.single (Sum.inr i) (1 : F)) = v (Sum.inl i) := by
  rw [spForm_apply]
  have hmv : Matrix.mulVec (CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F k)
      (Pi.single (Sum.inr i) (1 : F) : Fin k ⊕ Fin k → F) =
      Pi.single (Sum.inl i) (1 : F) := by
    funext a
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (Sum.inr i)]
    · rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply]
      rcases a with j | j <;>
        simp [CFSG.ClassicalInvolution.Models.SymplecticPairs.par,
          CFSG.ClassicalInvolution.Models.SymplecticPairs.sgn, Pi.single_apply, eq_comm]
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp
  rw [hmv, dotProduct_single]
  simp

theorem spForm_single_inr_left (i : Fin k) (v : Fin k ⊕ Fin k → F) :
    spForm k F (Pi.single (Sum.inr i) (1 : F)) v = - v (Sum.inl i) := by
  have h := spForm_isAlt.neg_eq v (Pi.single (Sum.inr i) (1 : F))
  rw [spForm_single_inr_right] at h
  exact h.symm

theorem spForm_single_inl_inl (i j : Fin k) :
    spForm k F (Pi.single (Sum.inl i) (1 : F)) (Pi.single (Sum.inl j) (1 : F)) = 0 := by
  rw [spForm_single_inl_left]
  simp [Pi.single_apply]

theorem spForm_single_inr_inl (i j : Fin k) :
    spForm k F (Pi.single (Sum.inr i) (1 : F)) (Pi.single (Sum.inl j) (1 : F)) =
      if i = j then -1 else 0 := by
  rw [spForm_single_inr_left]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij, Pi.single_apply]

private theorem spLineCount_spTransvection_noncomm {a b : Fin k ⊕ Fin k → F}
    (hB : spForm k F a b ≠ 0) :
    spTransvection a (1 : F) * spTransvection b 1 ≠
      spTransvection b 1 * spTransvection a 1 := by
  intro h
  have hb : b ≠ 0 := fun h0 => hB (by rw [h0, map_zero])
  have h1 := congrArg (fun g : ↥(StatedSp k F) => spEnd g b) h
  simp only [spEnd_mul, Module.End.mul_apply, spEnd_spTransvection] at h1
  have h0 : spForm k F b b = 0 := spForm_isAlt b
  simp only [h0, mul_zero, zero_smul, add_zero, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, one_mul] at h1
  have h2 : ((0 + spForm k F b a * spForm k F a b) • b : Fin k ⊕ Fin k → F) = 0 := by
    simpa using h1
  rw [zero_add] at h2
  rcases smul_eq_zero.mp h2 with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hB (by
        have h5 := spForm_isAlt.neg_eq a b
        rw [h4] at h5
        exact neg_eq_zero.mp h5)
    · exact hB h4
  · exact hb h3

theorem commute_spTransvection_iff {a b : Fin k ⊕ Fin k → F} {c s : F} (hc : c ≠ 0)
    (hs : s ≠ 0) :
    Commute (spTransvection a c) (spTransvection b s) ↔ spForm k F a b = 0 := by
  constructor
  · intro h
    by_contra hne
    have hBA1 : Commute (spTransvection b s) (spTransvection a 1) :=
      (borel86_spn_commute_spTransvection_iff hc one_ne_zero (spTransvection b s)).mp h.symm
    have hA1B1 : Commute (spTransvection a 1) (spTransvection b 1) :=
      (borel86_spn_commute_spTransvection_iff hs one_ne_zero (spTransvection a 1)).mp hBA1.symm
    exact spLineCount_spTransvection_noncomm hne hA1B1
  · intro h
    have hba : spForm k F b a = 0 := by
      have h' := spForm_isAlt.neg_eq a b
      rw [h, neg_zero] at h'
      exact h'.symm
    exact (kFacts_spTransvection_comm_of_spForm_eq_zero (a := a) (c := b) hba s c).symm

theorem setOf_isConj_spTransvection {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) (c : F) :
    {x | IsConj (spTransvection a c) x} = {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := isConj_iff.mp hx
    have hne : spEnd g a ≠ 0 := by
      intro h0
      have h1 : spEnd (g⁻¹ * g) a = a := by
        rw [inv_mul_cancel, spEnd_one, Module.End.one_apply]
      rw [spEnd_mul, Module.End.mul_apply, h0, map_zero] at h1
      exact ha h1.symm
    refine ⟨spEnd g a, hne, ?_⟩
    rw [← hg, spTransvection_conj]
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨g, hg⟩ := exists_spEnd_eq ha hb
    refine isConj_iff.mpr ⟨g, ?_⟩
    rw [spTransvection_conj, hg]

theorem commute_spTransvection_smul_iff (y : ↥(StatedSp k F)) (a : Fin k ⊕ Fin k → F)
    {μ c : F} (hμ : μ ≠ 0) (hc : c ≠ 0) :
    Commute y (spTransvection (μ • a) c) ↔ Commute y (spTransvection a c) := by
  rw [CFSG.RankThree.PartOne.CTP.spTransvection_smul]
  exact (borel86_spn_commute_spTransvection_iff hc (mul_ne_zero (mul_ne_zero hμ hμ) hc) y).symm

private theorem spLineCount_inr_coord_eq_zero_of_mem_lineMem {i j : Fin k}
    {c : F} (hc : c ≠ 0) {x : ↥(StatedSp k F)}
    (hx : x ∈ lineMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
      (spTransvection (Pi.single (Sum.inl i) 1) c) (spTransvection (Pi.single (Sum.inl j) 1) c))
    {z : Fin k ⊕ Fin k → F} (hxz : x = spTransvection z c) :
    ∀ m : Fin k, z (Sum.inr m) = 0 := by
  classical
  let S : Set ↥(StatedSp k F) := {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
  let ei : Fin k ⊕ Fin k → F := Pi.single (Sum.inl i) 1
  let ej : Fin k ⊕ Fin k → F := Pi.single (Sum.inl j) 1
  let v : ↥(StatedSp k F) := spTransvection ei c
  let w : ↥(StatedSp k F) := spTransvection ej c
  have hx2 : perpMem S v ∩ perpMem S w ⊆ perpMem S (spTransvection z c) := by
    simpa [S, v, w, ei, ej, hxz] using hx.2
  intro m
  let y : ↥(StatedSp k F) := spTransvection (Pi.single (Sum.inl m) (1 : F)) c
  have hyS : y ∈ S := ⟨_, Pi.single_ne_zero_iff.2 one_ne_zero, rfl⟩
  have hyv : y ∈ perpMem S v := by
    refine mem_perpMem.mpr ⟨hyS, ?_⟩
    exact (commute_spTransvection_iff hc hc).mpr (by
      simpa [ei, v] using spForm_single_inl_inl m i)
  have hyw : y ∈ perpMem S w := by
    refine mem_perpMem.mpr ⟨hyS, ?_⟩
    exact (commute_spTransvection_iff hc hc).mpr (by
      simpa [ej, w] using spForm_single_inl_inl m j)
  have hyx : y ∈ perpMem S (spTransvection z c) := hx2 ⟨hyv, hyw⟩
  have hform : spForm k F (Pi.single (Sum.inl m) (1 : F)) z = 0 :=
    (commute_spTransvection_iff hc hc).mp (mem_perpMem.mp hyx).2
  rwa [spForm_single_inl_left] at hform

private theorem spLineCount_inl_coord_eq_zero_of_mem_lineMem {i j : Fin k}
    {c : F} (hc : c ≠ 0) {x : ↥(StatedSp k F)}
    (hx : x ∈ lineMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
      (spTransvection (Pi.single (Sum.inl i) 1) c) (spTransvection (Pi.single (Sum.inl j) 1) c))
    {z : Fin k ⊕ Fin k → F} (hxz : x = spTransvection z c) :
    ∀ m : Fin k, m ≠ i → m ≠ j → z (Sum.inl m) = 0 := by
  classical
  let S : Set ↥(StatedSp k F) := {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
  let ei : Fin k ⊕ Fin k → F := Pi.single (Sum.inl i) 1
  let ej : Fin k ⊕ Fin k → F := Pi.single (Sum.inl j) 1
  let v : ↥(StatedSp k F) := spTransvection ei c
  let w : ↥(StatedSp k F) := spTransvection ej c
  have hx2 : perpMem S v ∩ perpMem S w ⊆ perpMem S (spTransvection z c) := by
    simpa [S, v, w, ei, ej, hxz] using hx.2
  intro m hmi hmj
  let y : ↥(StatedSp k F) := spTransvection (Pi.single (Sum.inr m) (1 : F)) c
  have hyS : y ∈ S := ⟨_, Pi.single_ne_zero_iff.2 one_ne_zero, rfl⟩
  have hv0 : spForm k F (Pi.single (Sum.inr m) (1 : F)) ei = 0 := by
    have h := spForm_single_inr_inl (F := F) m i
    simpa [ei, hmi] using h
  have hw0 : spForm k F (Pi.single (Sum.inr m) (1 : F)) ej = 0 := by
    have h := spForm_single_inr_inl (F := F) m j
    simpa [ej, hmj] using h
  have hyv : y ∈ perpMem S v := by
    refine mem_perpMem.mpr ⟨hyS, ?_⟩
    exact (commute_spTransvection_iff hc hc).mpr (by simpa [v] using hv0)
  have hyw : y ∈ perpMem S w := by
    refine mem_perpMem.mpr ⟨hyS, ?_⟩
    exact (commute_spTransvection_iff hc hc).mpr (by simpa [w] using hw0)
  have hyx : y ∈ perpMem S (spTransvection z c) := hx2 ⟨hyv, hyw⟩
  have hform : spForm k F (Pi.single (Sum.inr m) (1 : F)) z = 0 :=
    (commute_spTransvection_iff hc hc).mp (mem_perpMem.mp hyx).2
  rw [spForm_single_inr_left] at hform
  exact neg_eq_zero.mp hform

private theorem spLineCount_eq_smul_single_add {i j : Fin k} (hij : i ≠ j)
    {z : Fin k ⊕ Fin k → F} (hz0 : z ≠ 0)
    (hz_inr : ∀ m : Fin k, z (Sum.inr m) = 0)
    (hz_inl : ∀ m : Fin k, m ≠ i → m ≠ j → z (Sum.inl m) = 0) :
    ∃ s t : F, (s ≠ 0 ∨ t ≠ 0) ∧
      z = s • Pi.single (Sum.inl i) 1 + t • Pi.single (Sum.inl j) 1 := by
  let ei : Fin k ⊕ Fin k → F := Pi.single (Sum.inl i) 1
  let ej : Fin k ⊕ Fin k → F := Pi.single (Sum.inl j) 1
  let s : F := z (Sum.inl i)
  let t : F := z (Sum.inl j)
  have hz : z = s • ei + t • ej := by
    funext l
    rcases l with m | m
    · by_cases hmi : m = i
      · rw [hmi]
        simp [s, t, ei, ej, Pi.single_apply, Ne.symm hij]
      · by_cases hmj : m = j
        · rw [hmj]
          simp [s, t, ei, ej, Pi.single_apply, hij]
        · rw [hz_inl m hmi hmj]
          simp [ei, ej, Pi.single_apply, hmi, hmj]
    · rw [hz_inr m]
      simp [ei, ej, Pi.single_apply]
  have hst : s ≠ 0 ∨ t ≠ 0 := by
    by_contra h
    rcases not_or.mp h with ⟨hs, ht⟩
    have hs0 : s = 0 := not_not.mp hs
    have ht0 : t = 0 := not_not.mp ht
    apply hz0
    rw [hz, hs0, ht0]
    simp
  refine ⟨s, t, hst, ?_⟩
  simpa [ei, ej] using hz

theorem exists_eq_spTransvection_of_mem_lineMem {i j : Fin k} (hij : i ≠ j) {c : F}
    (hc : c ≠ 0) {x : ↥(StatedSp k F)}
    (hx : x ∈ lineMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
      (spTransvection (Pi.single (Sum.inl i) 1) c) (spTransvection (Pi.single (Sum.inl j) 1) c)) :
    ∃ s t : F, (s ≠ 0 ∨ t ≠ 0) ∧
      x = spTransvection (s • Pi.single (Sum.inl i) 1 + t • Pi.single (Sum.inl j) 1) c := by
  classical
  obtain ⟨z, hz0, hxz⟩ : ∃ z, z ≠ 0 ∧ x = spTransvection z c := hx.1
  have hz_inr := spLineCount_inr_coord_eq_zero_of_mem_lineMem (k := k) (i := i) (j := j) hc hx hxz
  have hz_inl := spLineCount_inl_coord_eq_zero_of_mem_lineMem (k := k) (i := i) (j := j) hc hx hxz
  obtain ⟨s, t, hst, hz⟩ := spLineCount_eq_smul_single_add hij hz0 hz_inr hz_inl
  refine ⟨s, t, hst, ?_⟩
  rw [hxz, hz]

private theorem spLineCount_perpMem_smul_inl_eq {j : Fin k} {c t : F} (ht : t ≠ 0)
    (hc : c ≠ 0) :
    perpMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
        (spTransvection (t • Pi.single (Sum.inl j) 1) c) =
      perpMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
        (spTransvection (Pi.single (Sum.inl j) 1) c) := by
  ext y
  rw [mem_perpMem, mem_perpMem]
  exact ⟨fun h => ⟨h.1, (commute_spTransvection_smul_iff y (Pi.single (Sum.inl j) 1) ht hc).mp h.2⟩,
    fun h => ⟨h.1, (commute_spTransvection_smul_iff y (Pi.single (Sum.inl j) 1) ht hc).mpr h.2⟩⟩

private theorem spLineCount_perpMem_smul_add_eq {i j : Fin k} {c s u : F} (hs : s ≠ 0)
    (hc : c ≠ 0) :
    perpMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
        (spTransvection (s • (Pi.single (Sum.inl i) 1 + u • Pi.single (Sum.inl j) 1)) c) =
      perpMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
        (spTransvection (Pi.single (Sum.inl i) 1 + u • Pi.single (Sum.inl j) 1) c) := by
  ext y
  rw [mem_perpMem, mem_perpMem]
  exact ⟨fun h => ⟨h.1, (commute_spTransvection_smul_iff y _ hs hc).mp h.2⟩,
    fun h => ⟨h.1, (commute_spTransvection_smul_iff y _ hs hc).mpr h.2⟩⟩

private theorem spLineCount_image_subset {i j : Fin k} (hij : i ≠ j) {c : F} (hc : c ≠ 0) :
    perpMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} ''
        lineMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
          (spTransvection (Pi.single (Sum.inl i) 1) c)
          (spTransvection (Pi.single (Sum.inl j) 1) c) ⊆
      insert (perpMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
          (spTransvection (Pi.single (Sum.inl j) 1) c))
        (Set.range fun u : F => perpMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
          (spTransvection (Pi.single (Sum.inl i) 1 + u • Pi.single (Sum.inl j) 1) c)) := by
  classical
  let S : Set ↥(StatedSp k F) := {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
  let ei : Fin k ⊕ Fin k → F := Pi.single (Sum.inl i) 1
  let ej : Fin k ⊕ Fin k → F := Pi.single (Sum.inl j) 1
  let P : (Fin k ⊕ Fin k → F) → Set ↥(StatedSp k F) := fun z => perpMem S (spTransvection z c)
  let T : Set (Set ↥(StatedSp k F)) := insert (P ej) (Set.range fun u : F => P (ei + u • ej))
  have hsub : perpMem S '' lineMem S (spTransvection ei c) (spTransvection ej c) ⊆ T := by
    rintro _ ⟨x, hxline, rfl⟩
    obtain ⟨s, t, hst, hxeq⟩ := exists_eq_spTransvection_of_mem_lineMem (k := k) hij hc
      (x := x) (by simpa [S, ei, ej] using hxline)
    by_cases hs : s = 0
    · have ht : t ≠ 0 := by
        rcases hst with hs' | ht
        · exact absurd hs hs'
        · exact ht
      have hPx : perpMem S x = P ej := by
        rw [hxeq, hs, zero_smul, zero_add]
        simpa [S, ej, P] using spLineCount_perpMem_smul_inl_eq (j := j) ht hc
      rw [hPx]
      exact Set.mem_insert _ _
    · have hts : s * (t / s) = t := by
        rw [mul_comm, div_mul_cancel₀ t hs]
      have hx' : x = spTransvection (s • (ei + (t / s) • ej)) c := by
        rw [hxeq]
        congr 1
        rw [smul_add, smul_smul, hts]
      have hPx : perpMem S x = P (ei + (t / s) • ej) := by
        rw [hx']
        simpa [S, ei, ej, P] using spLineCount_perpMem_smul_add_eq (i := i) (j := j) (c := c) hs hc
      rw [hPx]
      exact Set.mem_insert_of_mem (P ej) ⟨t / s, rfl⟩
  simpa [S, ei, ej, P, T] using hsub

theorem ncard_perpMem_image_lineMem_le [Finite F] {i j : Fin k} (hij : i ≠ j) {c : F}
    (hc : c ≠ 0) :
    (perpMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} ''
        lineMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
          (spTransvection (Pi.single (Sum.inl i) 1) c)
          (spTransvection (Pi.single (Sum.inl j) 1) c)).ncard ≤ Nat.card F + 1 := by
  classical
  let S : Set ↥(StatedSp k F) := {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
  let ei : Fin k ⊕ Fin k → F := Pi.single (Sum.inl i) 1
  let ej : Fin k ⊕ Fin k → F := Pi.single (Sum.inl j) 1
  let P : (Fin k ⊕ Fin k → F) → Set ↥(StatedSp k F) := fun z => perpMem S (spTransvection z c)
  let T : Set (Set ↥(StatedSp k F)) := insert (P ej) (Set.range fun u : F => P (ei + u • ej))
  have hsub : perpMem S '' lineMem S (spTransvection ei c) (spTransvection ej c) ⊆ T := by
    simpa [S, ei, ej, P, T] using spLineCount_image_subset (k := k) hij hc
  have hrange : (Set.range fun u : F => P (ei + u • ej)).ncard ≤ Nat.card F := by
    rw [← Set.image_univ]
    calc
      ((fun u : F => P (ei + u • ej)) '' (Set.univ : Set F)).ncard
          ≤ (Set.univ : Set F).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = Nat.card F := Set.ncard_univ F
  have hT : T.ncard ≤ Nat.card F + 1 := by
    change (insert (P ej) (Set.range fun u : F => P (ei + u • ej))).ncard ≤ Nat.card F + 1
    calc
      (insert (P ej) (Set.range fun u : F => P (ei + u • ej))).ncard ≤
          (Set.range fun u : F => P (ei + u • ej)).ncard + 1 :=
        Set.ncard_insert_le _ _
      _ ≤ Nat.card F + 1 := Nat.add_le_add_right hrange 1
  have hsub' : perpMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} ''
      lineMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
        (spTransvection (Pi.single (Sum.inl i) 1) c)
        (spTransvection (Pi.single (Sum.inl j) 1) c) ⊆ T := by
    simpa [S, ei, ej] using hsub
  exact (Set.ncard_le_ncard hsub' (Set.toFinite _)).trans hT

private theorem spLineCount_perpMem_ne {i j : Fin k} (hij : i ≠ j) {c : F} (hc : c ≠ 0) :
    perpMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
        (spTransvection (Pi.single (Sum.inl i) 1) c) ≠
      perpMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
        (spTransvection (Pi.single (Sum.inl j) 1) c) := by
  classical
  let S : Set ↥(StatedSp k F) := {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
  let ei : Fin k ⊕ Fin k → F := Pi.single (Sum.inl i) 1
  let ej : Fin k ⊕ Fin k → F := Pi.single (Sum.inl j) 1
  let v : ↥(StatedSp k F) := spTransvection ei c
  let w : ↥(StatedSp k F) := spTransvection ej c
  change perpMem S v ≠ perpMem S w
  let y : ↥(StatedSp k F) := spTransvection (Pi.single (Sum.inr j) (1 : F)) c
  have hyS : y ∈ S := ⟨_, Pi.single_ne_zero_iff.2 one_ne_zero, rfl⟩
  have hyv : y ∈ perpMem S v := by
    refine mem_perpMem.mpr ⟨hyS, ?_⟩
    refine (commute_spTransvection_iff hc hc).mpr ?_
    have hzero : spForm k F (Pi.single (Sum.inr j) (1 : F)) ei = 0 := by
      have h := spForm_single_inr_inl (F := F) j i
      simpa [ei, Ne.symm hij] using h
    exact hzero
  have hyw : y ∉ perpMem S w := by
    intro hy
    have hcommw : Commute y w := (mem_perpMem.mp hy).2
    have hform : spForm k F (Pi.single (Sum.inr j) (1 : F)) ej = 0 :=
      (commute_spTransvection_iff hc hc).mp hcommw
    have hneg : spForm k F (Pi.single (Sum.inr j) (1 : F)) ej = -1 := by
      have h := spForm_single_inr_inl (F := F) j j
      simpa [ej] using h
    rw [hneg] at hform
    exact (neg_ne_zero.mpr one_ne_zero) hform
  intro heq
  exact hyw (heq ▸ hyv)

theorem exists_lineMem_ncard_le_of_isSymplecticTransvectionIn [Finite F] (hk : 2 ≤ k)
    {t₀ : ↥(StatedSp k F)} (ht : IsSymplecticTransvectionIn k t₀) :
    ∃ v ∈ {x | IsConj t₀ x}, ∃ w ∈ {x | IsConj t₀ x}, Commute v w ∧
      perpMem {x | IsConj t₀ x} v ≠ perpMem {x | IsConj t₀ x} w ∧
      (perpMem {x | IsConj t₀ x} '' lineMem {x | IsConj t₀ x} v w).ncard ≤ Nat.card F + 1 := by
  classical
  obtain ⟨a₀, c, ha₀, hc, rfl⟩ := borel86_spn_eq_spTransvection ht
  rw [setOf_isConj_spTransvection ha₀ c]
  let S : Set ↥(StatedSp k F) := {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  let ei : Fin k ⊕ Fin k → F := Pi.single (Sum.inl i) 1
  let ej : Fin k ⊕ Fin k → F := Pi.single (Sum.inl j) 1
  let v : ↥(StatedSp k F) := spTransvection ei c
  let w : ↥(StatedSp k F) := spTransvection ej c
  have hv : v ∈ S := ⟨ei, Pi.single_ne_zero_iff.2 one_ne_zero, rfl⟩
  have hw : w ∈ S := ⟨ej, Pi.single_ne_zero_iff.2 one_ne_zero, rfl⟩
  have hcomm : Commute v w := by
    refine (commute_spTransvection_iff hc hc).mpr ?_
    simpa [ei, ej] using spForm_single_inl_inl i j
  have hne : perpMem S v ≠ perpMem S w := by
    simpa [S, v, w, ei, ej] using spLineCount_perpMem_ne (k := k) hij hc
  refine ⟨v, hv, w, hw, hcomm, hne, ?_⟩
  simpa [S, v, w, ei, ej] using
    (ncard_perpMem_image_lineMem_le (k := k) (F := F) (i := i) (j := j) hij (c := c) hc)

end CFSG.OddTranspositions.PartFour
