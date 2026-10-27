module

public import CFSG.LocalAnalysis.StandardType.PhanELocalClsT
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A13pDef
public import CFSG.LocalAnalysis.StandardType.PhanELocalHerm4

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] noncomputable def D13p : TData K where
  okL u L := (u ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (u ⊔ Vsub 4 1) = Vsub 4 1 ∧
    (L ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (L ⊔ Vsub 4 1) = Vsub 4 1

private theorem plb_hh_zero_right (u : Fin 4 → K) : hh f u 0 = 0 := by
  simpa using hh_smul_right (f := f) (0 : K) u (0 : Fin 4 → K)

theorem gram_zero_right (u : Fin 4 → K) : gram f u 0 = 0 := by
  simpa using gram_smul_right (f := f) (0 : K) u (0 : Fin 4 → K)

theorem ne_zero_of_aniso {u : Fin 4 → K} (hu : Aniso f u) : u ≠ 0 :=
  fun h => hu (by rw [h]; exact plb_hh_zero_right (f := f) 0)

private theorem plb_linearIndependent_pair {x y : Fin 4 → K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hne : Submodule.span K {x} ≠ Submodule.span K {y}) :
    ∀ a b : K, a • x + b • y = 0 → a = 0 ∧ b = 0 := by
  intro a b hab
  have hx_not_mem : x ∉ Submodule.span K {y} := by
    intro hxmem
    apply hne
    have hle : Submodule.span K {x} ≤ Submodule.span K {y} :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxmem)
    exact Submodule.eq_of_le_of_finrank_eq hle
      (by rw [finrank_span_singleton hx, finrank_span_singleton hy])
  have hb : b = 0 := by
    by_contra hb0
    apply hne
    have hy_mem : y ∈ Submodule.span K {x} := by
      have h1 : b • y = -(a • x) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hab
      have h2 : y = b⁻¹ • (-(a • x)) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ hb0, one_smul]
      rw [h2]
      exact Submodule.smul_mem _ _
        (Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
    have hle : Submodule.span K {y} ≤ Submodule.span K {x} :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hy_mem)
    exact (Submodule.eq_of_le_of_finrank_eq hle
      (by rw [finrank_span_singleton hx, finrank_span_singleton hy])).symm
  have ha : a = 0 := by
    have : a • x = 0 := by simpa [hb] using hab
    exact (smul_eq_zero.mp this).resolve_right hx
  exact ⟨ha, hb⟩

private theorem plb_mem_perpB_sup_of {x y u : Fin 4 → K} (hux : hh f x u = 0)
    (huy : hh f y u = 0) :
    u ∈ perpB K f 4 1 4
      (Submodule.span K {x} ⊔ Submodule.span K {y} ⊔ Vsub (K := K) 4 1) := by
  rw [mem_perpB4_iff]
  intro w hw
  obtain ⟨z, hz, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz₁
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hz₂
  simp only [hh_add_left, hh_smul_left]
  rw [hux, huy, hh_of_mem_Vsub_left (f := f) hv]
  ring

private theorem plb_inf_eq_bot_iff {A B : Submodule K (Fin 4 → K)} (hA : finrank K A = 1) :
    A ⊓ B = ⊥ ↔ ¬ A ≤ B := by
  constructor
  · intro h hle
    have hAle : A ≤ ⊥ := by
      rw [← h]
      exact le_inf le_rfl hle
    have hbot : A = ⊥ := le_bot_iff.mp hAle
    have hfin : finrank K A = 0 := by rw [hbot, finrank_bot]
    omega
  · intro h
    by_contra hne
    have hle1 : finrank K ↥(A ⊓ B) ≤ 1 := by
      rw [← hA]
      exact Submodule.finrank_mono inf_le_left
    have hne1 : finrank K ↥(A ⊓ B) ≠ 1 := by
      intro heq
      have hAB : A ≤ B := by
        have he : A ⊓ B = A :=
          Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [heq, hA])
        rw [← he]
        exact inf_le_right
      exact h hAB
    have h0 : finrank K ↥(A ⊓ B) = 0 := by omega
    exact hne (Submodule.finrank_eq_zero.mp h0)

theorem finrank_sup_sup_eq_three {a b t : Submodule K (Fin 4 → K)} (ha : BPt a) (hb : BPt b)
    (ht : BPt t) (hab : a ≠ b) (htab : ¬ t ≤ a ⊔ b) :
    finrank K ↥(a ⊔ b ⊔ t) = 3 := by
  have ha' : a ≤ Vtail ∧ finrank K a = 1 := ha
  have hb' : b ≤ Vtail ∧ finrank K b = 1 := hb
  have ht' : t ≤ Vtail ∧ finrank K t = 1 := ht
  have hab2 : finrank K ↥(a ⊔ b) = 2 := finrank_sup_of_ne_pts ha'.2 hb'.2 hab
  have hdisj : Disjoint (a ⊔ b) t := by
    rw [disjoint_iff, inf_comm]
    exact (plb_inf_eq_bot_iff ht'.2).mpr htab
  rw [finrank_sup_of_disjoint hdisj, hab2, ht'.2]

theorem span_ne_of_gram_ne {x y : Fin 4 → K} (hg : gram f x y ≠ 0) :
    Submodule.span K {x} ≠ Submodule.span K {y} := by
  intro h
  apply hg
  have hy_mem : y ∈ Submodule.span K {x} := by
    rw [h]
    exact Submodule.mem_span_singleton_self y
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy_mem
  rw [← hc, gram_smul_right, gram_self, mul_zero]

theorem map_tailProj_sup_Vsub (S : Submodule K (Fin 4 → K)) :
    S.map tailProj ⊔ Vsub 4 1 = S ⊔ Vsub 4 1 := by
  have hcomp : tailProj.comp tailProj = (tailProj : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) := by
    ext v j
    by_cases hj : j = 0
    · subst hj
      simp [tailProj]
    · simp [tailProj, hj]
  have hmap : (S.map tailProj).map tailProj = S.map tailProj := by
    rw [← Submodule.map_comp, hcomp]
  rw [sup_Vsub_eq_comap (S := S.map tailProj), hmap, ← sup_Vsub_eq_comap (S := S)]

theorem admT_D13p : AdmT (D13p (K := K) f) = Adm13p (K := K) f := by
  funext p L H
  simp only [AdmT, D13p, Adm13p, map_tailProj_sup_Vsub]

theorem exists_vec_of_BPt {u : Submodule K (Fin 4 → K)} (hu : BPt u) :
    ∃ x : Fin 4 → K, x 0 = 0 ∧ x ≠ 0 ∧ u = Submodule.span K {x} := by
  have hu' : u ≤ Vtail ∧ finrank K u = 1 := hu
  have hne : u ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hu'
    exact zero_ne_one hu'.2
  obtain ⟨x, hxu, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨x, ?_, hx_ne, ?_⟩
  · have : x ∈ (Vtail : Submodule K (Fin 4 → K)) := hu'.1 hxu
    simpa [Vtail] using this
  · have hle : Submodule.span K {x} ≤ u :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxu)
    have hfr : finrank K (Submodule.span K {x}) = 1 := finrank_span_singleton hx_ne
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, hu'.2])).symm

theorem okL_pt_iff {x : Fin 4 → K} (hx0 : x 0 = 0) (hx : x ≠ 0) :
    (Submodule.span K {x} ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (Submodule.span K {x} ⊔ Vsub 4 1) =
      Vsub 4 1 ↔ Aniso f x := by
  set U : Submodule K (Fin 4 → K) := Submodule.span K {x} ⊔ Vsub (K := K) 4 1 with hU
  have hVle : Vsub (K := K) 4 1 ≤ U := le_sup_right
  have hle : Vsub (K := K) 4 1 ≤ U ⊓ perpB K f 4 1 4 U :=
    le_inf hVle (Vsub_le_perpB (f := f) U)
  constructor
  · intro heq hxx
    have hxU : x ∈ U := Submodule.mem_sup_left (Submodule.mem_span_singleton_self x)
    have hxperp : x ∈ perpB K f 4 1 4 U := by
      rw [mem_perpB4_iff]
      intro u hu
      obtain ⟨a, ha, v, hv, hav⟩ := Submodule.mem_sup.mp hu
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
      rw [← hav, ← hc]
      simp only [hh_add_left, hh_smul_left]
      rw [hh_of_mem_Vsub_left (f := f) hv, hxx]
      ring
    have hxmem : x ∈ Vsub (K := K) 4 1 :=
      heq ▸ (show x ∈ U ⊓ perpB K f 4 1 4 U from ⟨hxU, hxperp⟩)
    apply hx
    funext j
    rcases Nat.eq_zero_or_pos j.val with hj | hj
    · have hj0 : j = 0 := Fin.ext hj
      subst hj0
      exact hx0
    · exact hxmem j hj
  · intro hxx
    apply le_antisymm _ hle
    intro u hu
    obtain ⟨huU, huperp⟩ := Submodule.mem_inf.mp hu
    obtain ⟨a, ha, v, hv, hav⟩ := Submodule.mem_sup.mp huU
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
    rw [← hav, ← hc] at huperp
    have h0 : hh f x (c • x + v) = 0 :=
      (mem_perpB4_iff (K := K) (f := f) U (c • x + v)).mp huperp x
        (Submodule.mem_sup_left (Submodule.mem_span_singleton_self x))
    rw [hh_add_right, hh_smul_right, hh_of_mem_Vsub_right (f := f) hv, add_zero] at h0
    have hc0 : c = 0 := (mul_eq_zero.mp h0).resolve_right hxx
    rw [← hav, ← hc, hc0, zero_smul, zero_add]
    exact hv

theorem okL_line_iff (hK : Nat.card K = (2 ^ f) ^ 2) {x y : Fin 4 → K} (hx0 : x 0 = 0)
    (hy0 : y 0 = 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hne : Submodule.span K {x} ≠ Submodule.span K {y}) :
    (Submodule.span K {x} ⊔ Submodule.span K {y} ⊔ Vsub 4 1) ⊓
        perpB K f 4 1 4 (Submodule.span K {x} ⊔ Submodule.span K {y} ⊔ Vsub 4 1) =
      Vsub 4 1 ↔ gram f x y ≠ 0 := by
  set M : Submodule K (Fin 4 → K) :=
    Submodule.span K {x} ⊔ Submodule.span K {y} ⊔ Vsub (K := K) 4 1 with hM
  have hle : Vsub (K := K) 4 1 ≤ M ⊓ perpB K f 4 1 4 M :=
    le_inf le_sup_right (Vsub_le_perpB (f := f) M)
  constructor
  · intro heq
    by_contra hgram
    by_cases hcase : hh f x x ≠ 0 ∨ hh f x y ≠ 0
    · let u : Fin 4 → K := hh f x y • x + (-(hh f x x)) • y
      have hu_def : u = hh f x y • x + (-(hh f x x)) • y := rfl
      have hu_s : u ∈ Submodule.span K {x} ⊔ Submodule.span K {y} :=
        Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y))
      have huM : u ∈ M := Submodule.mem_sup_left hu_s
      have hux : hh f x u = 0 := by
        rw [hu_def]
        simp only [hh_add_right, hh_smul_right]
        ring
      have huy : hh f y u = 0 := by
        rw [hu_def]
        simp only [hh_add_right, hh_smul_right]
        have h := hgram
        rw [gram] at h
        linear_combination (-1 : K) * h
      have huperp : u ∈ perpB K f 4 1 4 M := plb_mem_perpB_sup_of (f := f) hux huy
      have hxV : x ∈ (Vtail : Submodule K (Fin 4 → K)) := by simpa [Vtail] using hx0
      have hyV : y ∈ (Vtail : Submodule K (Fin 4 → K)) := by simpa [Vtail] using hy0
      have hspan_le : Submodule.span K {x} ⊔ Submodule.span K {y} ≤ Vtail :=
        sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxV))
          (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hyV))
      have huV : u ∈ Vtail := hspan_le hu_s
      have hu_ne : u ≠ 0 := by
        intro h0
        rw [hu_def] at h0
        have hAB := plb_linearIndependent_pair hx hy hne
          (hh f x y) (-(hh f x x)) h0
        obtain ⟨hB0, hA0⟩ := hAB
        rcases hcase with hA | hB
        · exact hA (neg_eq_zero.mp hA0)
        · exact hB hB0
      have hu_not : u ∉ Vsub (K := K) 4 1 := by
        intro huV1
        have hmem : u ∈ (Vtail : Submodule K (Fin 4 → K)) ⊓ Vsub (K := K) 4 1 := ⟨huV, huV1⟩
        rw [Vtail_inf_Vsub] at hmem
        exact hu_ne (by simpa using hmem)
      exact hu_not (heq ▸ (show u ∈ M ⊓ perpB K f 4 1 4 M from ⟨huM, huperp⟩))
    · have hnot := not_or.mp hcase
      have hA0 : hh f x x = 0 := not_not.mp hnot.1
      have hB0 : hh f x y = 0 := not_not.mp hnot.2
      have hyx0 : hh f y x = 0 := by
        rw [hh_symm (K := K) (f := f) hK x y, hB0, map_zero]
      have hxM : x ∈ M :=
        Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_span_singleton_self x))
      have huperp : x ∈ perpB K f 4 1 4 M := plb_mem_perpB_sup_of (f := f) hA0 hyx0
      have hx_not : x ∉ Vsub (K := K) 4 1 := by
        intro hxV1
        have hxV : x ∈ Vtail := by
          show x 0 = 0
          exact hx0
        have hmem : x ∈ (Vtail : Submodule K (Fin 4 → K)) ⊓ Vsub (K := K) 4 1 := ⟨hxV, hxV1⟩
        rw [Vtail_inf_Vsub] at hmem
        exact hx (by simpa using hmem)
      exact hx_not (heq ▸ (show x ∈ M ⊓ perpB K f 4 1 4 M from ⟨hxM, huperp⟩))
  · intro hgram
    apply le_antisymm _ hle
    intro u hu
    obtain ⟨huM, huperp⟩ := Submodule.mem_inf.mp hu
    obtain ⟨z, hz, v, hv, hzv⟩ := Submodule.mem_sup.mp huM
    obtain ⟨z₁, hz₁, z₂, hz₂, hz₁z₂⟩ := Submodule.mem_sup.mp hz
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hz₁
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hz₂
    have hu_eq : u = a • x + b • y + v := by
      rw [← hzv, ← hz₁z₂, ← ha, ← hb]
    have hxM : x ∈ M :=
      Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_span_singleton_self x))
    have hyM : y ∈ M :=
      Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y))
    have h1 : a * hh f x x + b * hh f x y = 0 := by
      have h := (mem_perpB4_iff (K := K) (f := f) M u).mp huperp x hxM
      rw [hu_eq, hh_add_right, hh_add_right, hh_smul_right, hh_smul_right,
        hh_of_mem_Vsub_right (f := f) hv, add_zero] at h
      exact h
    have h2 : a * hh f y x + b * hh f y y = 0 := by
      have h := (mem_perpB4_iff (K := K) (f := f) M u).mp huperp y hyM
      rw [hu_eq, hh_add_right, hh_add_right, hh_smul_right, hh_smul_right,
        hh_of_mem_Vsub_right (f := f) hv, add_zero] at h
      exact h
    have ha0 : a = 0 := by
      have hmul : a * gram f x y = 0 := by
        rw [gram]
        linear_combination (hh f y y) * h1 - (hh f x y) * h2
      exact (mul_eq_zero.mp hmul).resolve_right hgram
    have hb0 : b = 0 := by
      have hmul : b * gram f x y = 0 := by
        rw [gram]
        linear_combination (hh f x x) * h2 - (hh f y x) * h1
      exact (mul_eq_zero.mp hmul).resolve_right hgram
    rw [hu_eq, ha0, hb0, zero_smul, zero_smul, zero_add, zero_add]
    exact hv

theorem bAdj_span_iff (hK : Nat.card K = (2 ^ f) ^ 2) {x y : Fin 4 → K} (hx0 : x 0 = 0)
    (hy0 : y 0 = 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    BAdj (D13p (K := K) f) (Submodule.span K {x}) (Submodule.span K {y}) ↔
      Aniso f x ∧ Aniso f y ∧ gram f x y ≠ 0 := by
  have hptx := okL_pt_iff (K := K) (f := f) hx0 hx
  have hpty := okL_pt_iff (K := K) (f := f) hy0 hy
  constructor
  · intro h
    simp only [BAdj] at h
    obtain ⟨hne, hoku, hokv⟩ := h
    simp only [D13p] at hoku hokv
    obtain ⟨hoku1, hoku2⟩ := hoku
    obtain ⟨hokv1, -⟩ := hokv
    refine ⟨hptx.mp hoku1, hpty.mp hokv1, ?_⟩
    exact (okL_line_iff (K := K) (f := f) hK hx0 hy0 hx hy hne).mp hoku2
  · rintro ⟨hax, hay, hg⟩
    have hne : Submodule.span K {x} ≠ Submodule.span K {y} :=
      span_ne_of_gram_ne (f := f) hg
    have hline : (Submodule.span K {x} ⊔ Submodule.span K {y} ⊔ Vsub 4 1) ⊓
        perpB K f 4 1 4 (Submodule.span K {x} ⊔ Submodule.span K {y} ⊔ Vsub 4 1) =
        Vsub 4 1 := (okL_line_iff (K := K) (f := f) hK hx0 hy0 hx hy hne).mpr hg
    simp only [BAdj, D13p]
    exact ⟨hne, ⟨hptx.mpr hax, hline⟩, ⟨hpty.mpr hay, hline⟩⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
