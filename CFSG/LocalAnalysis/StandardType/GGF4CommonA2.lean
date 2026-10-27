module

public import Mathlib.GroupTheory.Coxeter.Inversion
import CFSG.LocalAnalysis.StandardType.GGF4A3ResidualRep
import CFSG.LocalAnalysis.StandardType.GGF4CommPair
import CFSG.LocalAnalysis.StandardType.GGF4Frame
import CFSG.LocalAnalysis.StandardType.GGF4OrigRep
import CFSG.LocalAnalysis.StandardType.GGF4ReflectionClass

namespace CFSG.StandardType.F4Model

variable {W : Type} [Group W]

private def f4H : F4Vec := ⟨2, 3, 4, 2⟩

set_option synthInstance.maxSize 1024 in
private theorem short_fix_e1_commb : ∀ x, x < 24 → T1 x = 2 → (Rm x).mulv f4E1 = f4E1 →
    ∀ y, y < 24 → T1 y = 2 → (Rm y).mulv f4E1 = f4E1 → commb (Rm x) (Rm y) = true := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
private theorem long_fix_f4H_commb : ∀ x, x < 24 → T1 x = 1 → (Rm x).mulv f4H = f4H →
    ∀ y, y < 24 → T1 y = 1 → (Rm y).mulv f4H = f4H → commb (Rm x) (Rm y) = true := by
  decide +kernel

namespace F4Rep

variable (R : F4Rep W)

private theorem mulVec_f4H_of_mem_closureC {z : W}
    (hz : z ∈ Subgroup.closure ({R.s 3, R.s 2, R.s 1} : Set W)) :
    (R.ρ z).mulVec f4H.toFun = f4H.toFun := by
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;>
      · rw [R.hs, M4.toMat_mulVec]
        exact congrArg F4Vec.toFun (by decide +kernel)
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, ← Matrix.mulVec_mulVec, hy, hx]
  | inv x _ hx =>
    calc (R.ρ x⁻¹).mulVec f4H.toFun = (R.ρ x⁻¹).mulVec ((R.ρ x).mulVec f4H.toFun) := by rw [hx]
      _ = f4H.toFun := R.inv_mulVec_mulVec x _

private theorem conj_mem_closure_of_conj {b : Fin 3 → W} {g t₀ t₁ t₂ : W}
    (hg : g * b 0 * g⁻¹ = t₀ ∧ g * b 1 * g⁻¹ = t₁ ∧ g * b 2 * g⁻¹ = t₂) {u : W}
    (hu : u ∈ Subgroup.closure (Set.range b)) :
    g * u * g⁻¹ ∈ Subgroup.closure ({t₀, t₁, t₂} : Set W) := by
  have hle : Subgroup.closure (Set.range b) ≤
      conjSub g (Subgroup.closure ({t₀, t₁, t₂} : Set W)) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_conjSub]
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
    rcases hi with rfl | rfl | rfl
    · rw [hg.1]; exact Subgroup.subset_closure (by simp)
    · rw [hg.2.1]; exact Subgroup.subset_closure (by simp)
    · rw [hg.2.2]; exact Subgroup.subset_closure (by simp)
  exact mem_conjSub.1 (hle hu)

private theorem commute_of_conj_commb {u v g : W} {x y : ℕ}
    (hx : R.ρ (g * u * g⁻¹) = (Rm x).toMat) (hy : R.ρ (g * v * g⁻¹) = (Rm y).toMat)
    (h : commb (Rm x) (Rm y) = true) : u * v = v * u := by
  have h' : g * u * g⁻¹ * (g * v * g⁻¹) = g * v * g⁻¹ * (g * u * g⁻¹) := by
    apply R.inj
    rw [R.rho_mul hx hy, R.rho_mul hy hx, (commb_iff _ _).1 h]
  have h'' : g * (u * v) * g⁻¹ = g * (v * u) * g⁻¹ := by
    calc g * (u * v) * g⁻¹ = g * u * g⁻¹ * (g * v * g⁻¹) := by group
      _ = g * v * g⁻¹ * (g * u * g⁻¹) := h'
      _ = g * (v * u) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h'')

private theorem commute_of_short_mem_closureB {g u v : W} (hu : R.IsRefl u) (hv : R.IsRefl v)
    (hcu : R.cls u = 2) (hcv : R.cls v = 2)
    (hgu : g * u * g⁻¹ ∈ Subgroup.closure ({R.s 0, R.s 1, R.s 2} : Set W))
    (hgv : g * v * g⁻¹ ∈ Subgroup.closure ({R.s 0, R.s 1, R.s 2} : Set W)) : u * v = v * u := by
  obtain ⟨x, hx, ρx⟩ := R.refl_rep (hu.conj g)
  obtain ⟨y, hy, ρy⟩ := R.refl_rep (hv.conj g)
  have hTx : T1 x = 2 := by rw [← R.cls_eq hx ρx, R.cls_conj hu, hcu]
  have hTy : T1 y = 2 := by rw [← R.cls_eq hy ρy, R.cls_conj hv, hcv]
  have hfx : (Rm x).mulv f4E1 = f4E1 := by
    apply F4Vec.toFun_injective
    rw [← M4.toMat_mulVec, ← ρx]
    exact R.mulVec_e1_of_mem_closureB hgu
  have hfy : (Rm y).mulv f4E1 = f4E1 := by
    apply F4Vec.toFun_injective
    rw [← M4.toMat_mulVec, ← ρy]
    exact R.mulVec_e1_of_mem_closureB hgv
  exact R.commute_of_conj_commb ρx ρy (short_fix_e1_commb x hx hTx hfx y hy hTy hfy)

private theorem commute_of_long_mem_closureC {g u v : W} (hu : R.IsRefl u) (hv : R.IsRefl v)
    (hcu : R.cls u = 1) (hcv : R.cls v = 1)
    (hgu : g * u * g⁻¹ ∈ Subgroup.closure ({R.s 3, R.s 2, R.s 1} : Set W))
    (hgv : g * v * g⁻¹ ∈ Subgroup.closure ({R.s 3, R.s 2, R.s 1} : Set W)) : u * v = v * u := by
  obtain ⟨x, hx, ρx⟩ := R.refl_rep (hu.conj g)
  obtain ⟨y, hy, ρy⟩ := R.refl_rep (hv.conj g)
  have hTx : T1 x = 1 := by rw [← R.cls_eq hx ρx, R.cls_conj hu, hcu]
  have hTy : T1 y = 1 := by rw [← R.cls_eq hy ρy, R.cls_conj hv, hcv]
  have hfx : (Rm x).mulv f4H = f4H := by
    apply F4Vec.toFun_injective
    rw [← M4.toMat_mulVec, ← ρx]
    exact R.mulVec_f4H_of_mem_closureC hgu
  have hfy : (Rm y).mulv f4H = f4H := by
    apply F4Vec.toFun_injective
    rw [← M4.toMat_mulVec, ← ρy]
    exact R.mulVec_f4H_of_mem_closureC hgv
  exact R.commute_of_conj_commb ρx ρy (long_fix_f4H_commb x hx hTx hfx y hy hTy hfy)

end F4Rep

private theorem refl_char_cases {cs : CoxeterSystem CoxeterMatrix.F₄ W} {R : F4Rep W}
    (hRs : ∀ i, R.s i = cs.simple i) {t : W} (ht : cs.IsReflection t) :
    (classCharacter cs 0 t ≠ 1 ∧ classCharacter cs 1 t = 1 ∧ R.cls t = 1) ∨
      (classCharacter cs 0 t = 1 ∧ classCharacter cs 1 t ≠ 1 ∧ R.cls t = 2) := by
  obtain ⟨w, j, rfl⟩ := ht
  have hj : R.IsRefl (R.s j) := ⟨1, j, by simp⟩
  rw [classCharacter_conj, classCharacter_conj, classCharacter_simple, classCharacter_simple,
    ← hRs j, R.cls_conj hj w, R.cls_s j]
  fin_cases j <;> decide

private theorem orderOf_mul_ne_three {cs : CoxeterSystem CoxeterMatrix.F₄ W} {u v : W}
    (hu : cs.IsReflection u) (hv : cs.IsReflection v) (h : u * v = v * u) :
    orderOf (u * v) ≠ 3 := by
  intro h3
  have h2 : (u * v) ^ 2 = 1 := by
    calc (u * v) ^ 2 = u * v * (u * v) := pow_two _
      _ = u * v * (v * u) := by rw [h]
      _ = u * (v * v) * u := by group
      _ = 1 := by rw [hv.mul_self, mul_one, hu.mul_self]
  have h3' := orderOf_dvd_of_pow_eq_one h2
  rw [h3] at h3'
  norm_num at h3'

end CFSG.StandardType.F4Model

public section

namespace CFSG.StandardType.F4Model

variable {W : Type} [Group W]

theorem closure_ne_top_of_common_a2 (cs : CoxeterSystem CoxeterMatrix.F₄ W) {a b : Fin 3 → W}
    (ha : ∀ i, cs.IsReflection (a i)) (hb : ∀ i, cs.IsReflection (b i))
    (ha01 : orderOf (a 0 * a 1) = 3) (ha12 : orderOf (a 1 * a 2) = 3)
    (ha02 : orderOf (a 0 * a 2) = 2) (hb01 : orderOf (b 0 * b 1) = 3)
    (hb12 : orderOf (b 1 * b 2) = 3 ∨ orderOf (b 1 * b 2) = 4) (hb02 : orderOf (b 0 * b 2) = 2)
    {u v : W} (hu : cs.IsReflection u) (hv : cs.IsReflection v) (huv : orderOf (u * v) = 3)
    (hua : u ∈ Subgroup.closure (Set.range a)) (hva : v ∈ Subgroup.closure (Set.range a))
    (hub : u ∈ Subgroup.closure (Set.range b)) (hvb : v ∈ Subgroup.closure (Set.range b)) :
    Subgroup.closure (Set.range a ∪ Set.range b) ≠ ⊤ := by
  obtain ⟨R, hRs⟩ := exists_f4Rep cs
  have hRa : ∀ i, R.IsRefl (a i) := fun i => (F4Rep.isRefl_iff hRs).2 (ha i)
  have hRb : ∀ i, R.IsRefl (b i) := fun i => (F4Rep.isRefl_iff hRs).2 (hb i)
  have hi3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  obtain ⟨k, hk0⟩ : ∃ k : Fin 2, classCharacter cs k (a 0) = 1 := by
    rcases refl_char_cases hRs (ha 0) with h | h
    · exact ⟨1, h.2.1⟩
    · exact ⟨0, h.1⟩
  have hk1 : classCharacter cs k (a 1) = 1 := by
    rwa [← classCharacter_eq_of_order_three cs k ha01]
  have hk2 : classCharacter cs k (a 2) = 1 := by
    rwa [← classCharacter_eq_of_order_three cs k ha12]
  have hka : ∀ i, classCharacter cs k (a i) = 1 := fun i => by
    rcases hi3 i with rfl | rfl | rfl <;> assumption
  have hker : Subgroup.closure (Set.range a) ≤ (classCharacter cs k).ker :=
    (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact hka i)
  have hku : classCharacter cs k u = 1 := hker hua
  have hkv : classCharacter cs k v = 1 := hker hva
  by_cases hkb : classCharacter cs k (b 0) = 1
  ·
    have hkb1 : classCharacter cs k (b 1) = 1 := by
      rwa [← classCharacter_eq_of_order_three cs k hb01]
    obtain ⟨H, hH_ne, hHa, hH_exists, hH_order⟩ := R.a3_core hRa ha01 ha12 ha02
    have hfive : Subgroup.closure ({a 0, a 1, a 2, b 0, b 1} : Set W) ≠ ⊤ := by
      intro htop
      obtain ⟨j, hj⟩ : ∃ j : Fin 4, classCharacter cs k (cs.simple j) ≠ 1 := by
        obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> decide
        · exact ⟨0, by rw [classCharacter_simple]; decide⟩
        · exact ⟨2, by rw [classCharacter_simple]; decide⟩
      have hle : Subgroup.closure ({a 0, a 1, a 2, b 0, b 1} : Set W) ≤
          (classCharacter cs k).ker := by
        rw [Subgroup.closure_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        exacts [hka 0, hka 1, hka 2, hkb, hkb1]
      exact hj (hle (by rw [htop]; exact Subgroup.mem_top _))
    rcases hH_order (b 0) (b 1) (hRb 0) (hRb 1) hb01 with hall | htop
    · obtain ⟨j, hj⟩ := hH_exists (b 2) (hRb 2)
      intro htop
      apply hH_ne j
      rw [eq_top_iff, ← htop, Subgroup.closure_le]
      rintro z (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact hHa i j
      · rcases hi3 i with rfl | rfl | rfl
        exacts [(hall j).1, (hall j).2, hj]
    · exact absurd htop hfive
  · exfalso
    rcases hb12 with hb12 | hb12
    ·
      have hkb1 : classCharacter cs k (b 1) ≠ 1 := by
        rwa [← classCharacter_eq_of_order_three cs k hb01]
      have hkb2 : classCharacter cs k (b 2) ≠ 1 := by
        rwa [← classCharacter_eq_of_order_three cs k hb12]
      have hkb' : ∀ i, classCharacter cs k (b i) ≠ 1 := fun i => by
        rcases hi3 i with rfl | rfl | rfl <;> assumption
      obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> decide
      · have h1 : Subgroup.closure (Set.range b) ≤ (classCharacter cs 1).ker :=
          (Subgroup.closure_le _).2 (by
            rintro _ ⟨i, rfl⟩
            exact ((refl_char_cases hRs (hb i)).resolve_right fun h => hkb' i h.1).2.1)
        rcases refl_char_cases hRs hu with h | h
        · exact h.1 hku
        · exact h.2.1 (h1 hub)
      · have h0 : Subgroup.closure (Set.range b) ≤ (classCharacter cs 0).ker :=
          (Subgroup.closure_le _).2 (by
            rintro _ ⟨i, rfl⟩
            exact ((refl_char_cases hRs (hb i)).resolve_left fun h => hkb' i h.2.1).1)
        rcases refl_char_cases hRs hu with h | h
        · exact h.1 (h0 hub)
        · exact h.2.1 hku
    ·
      have hRu : R.IsRefl u := (F4Rep.isRefl_iff hRs).2 hu
      have hRv : R.IsRefl v := (F4Rep.isRefl_iff hRs).2 hv
      obtain ⟨g, hg | hg⟩ := R.classify (hRb 0) (hRb 1) (hRb 2) hb01 hb12 hb02
      · have hk : classValue k 0 ≠ 1 := by
          rwa [← classCharacter_conj cs k g (b 0), hg.1, hRs, classCharacter_simple] at hkb
        obtain rfl : k = 0 := by
          obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> decide
          · rfl
          · exact (hk (by decide)).elim
        have hcu : R.cls u = 2 :=
          ((refl_char_cases hRs hu).resolve_left fun h => h.1 hku).2.2
        have hcv : R.cls v = 2 :=
          ((refl_char_cases hRs hv).resolve_left fun h => h.1 hkv).2.2
        exact orderOf_mul_ne_three hu hv (R.commute_of_short_mem_closureB hRu hRv hcu hcv
          (F4Rep.conj_mem_closure_of_conj hg hub) (F4Rep.conj_mem_closure_of_conj hg hvb)) huv
      · have hk : classValue k 3 ≠ 1 := by
          rwa [← classCharacter_conj cs k g (b 0), hg.1, hRs, classCharacter_simple] at hkb
        obtain rfl : k = 1 := by
          obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> decide
          · exact (hk (by decide)).elim
          · rfl
        have hcu : R.cls u = 1 :=
          ((refl_char_cases hRs hu).resolve_right fun h => h.2.1 hku).2.2
        have hcv : R.cls v = 1 :=
          ((refl_char_cases hRs hv).resolve_right fun h => h.2.1 hkv).2.2
        exact orderOf_mul_ne_three hu hv (R.commute_of_long_mem_closureC hRu hRv hcu hcv
          (F4Rep.conj_mem_closure_of_conj hg hub) (F4Rep.conj_mem_closure_of_conj hg hvb)) huv

end CFSG.StandardType.F4Model

end
