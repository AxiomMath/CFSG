module

public import CFSG.Quasithin.Background.HTriSp4

public section

namespace CFSG.Quasithin

namespace H

namespace Tri

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {K : Type*} [Field K]

theorem eq_flagSpace_of_invariant_of {U : Subgroup (GL (Fin 3) K)} (hU : U ≤ uni3 K)
    (h01 : ∀ t : K, ∃ u ∈ U, (u : Matrix (Fin 3) (Fin 3) K) 0 1 = t)
    (h12 : ∀ t : K, ∃ u ∈ U, (u : Matrix (Fin 3) (Fin 3) K) 1 2 = t)
    {W : Submodule K (Fin 3 → K)}
    (hW : ∀ u ∈ U, ∀ v ∈ W, (u : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) :
    ∃ m ≤ 3, W = LinearFlag.flagSpace 3 K m := by
  classical
  have hdiff : ∀ u ∈ U, ∀ v ∈ W, (![(u : Matrix (Fin 3) (Fin 3) K) 0 1 * v 1 +
      (u : Matrix (Fin 3) (Fin 3) K) 0 2 * v 2, (u : Matrix (Fin 3) (Fin 3) K) 1 2 * v 2, 0] :
        Fin 3 → K) ∈ W := by
    intro u hu v hv
    obtain ⟨hlow, hdiag⟩ := uni3_entries (hU hu)
    have h := W.sub_mem (hW u hu v hv) hv
    convert h using 1
    ext i
    have h10 := hlow 1 0 (by decide)
    have h20 := hlow 2 0 (by decide)
    have h21 := hlow 2 1 (by decide)
    have h00 := hdiag 0
    have h11 := hdiag 1
    have h22 := hdiag 2
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h20, h21, h00, h11,
      h22]
    ring
  by_cases h2 : ∃ v ∈ W, v 2 ≠ 0
  · obtain ⟨v, hvW, hv2⟩ := h2
    obtain ⟨u, hu, hu12⟩ := h12 1
    have hd := hdiff u hu v hvW
    rw [hu12] at hd
    obtain ⟨u', hu', hu'01⟩ := h01 1
    have hd' := hdiff u' hu' _ hd
    have e0 : (Pi.single 0 1 : Fin 3 → K) ∈ W := by
      have h := W.smul_mem (v 2)⁻¹ hd'
      convert h using 1
      ext i
      fin_cases i <;> simp [hu'01, hv2]
    have e1 : (Pi.single 1 1 : Fin 3 → K) ∈ W := by
      have h := W.smul_mem (v 2)⁻¹ (W.sub_mem hd (W.smul_mem
        ((u : Matrix (Fin 3) (Fin 3) K) 0 1 * v 1 + (u : Matrix (Fin 3) (Fin 3) K) 0 2 * v 2) e0))
      convert h using 1
      ext i
      fin_cases i <;> simp [hv2, Matrix.vecHead, Matrix.vecTail]
    have e2 : (Pi.single 2 1 : Fin 3 → K) ∈ W := by
      have h := W.smul_mem (v 2)⁻¹ (W.sub_mem (W.sub_mem hvW (W.smul_mem (v 0) e0))
        (W.smul_mem (v 1) e1))
      convert h using 1
      ext i
      fin_cases i <;> simp [hv2]
    refine ⟨3, le_rfl, le_antisymm (fun x _ => ?_) (flagSpace_le_of fun j _ => ?_)⟩
    · rw [LinearFlag.mem_flagSpace]
      intro j hj
      exact absurd j.2 (by omega)
    · fin_cases j
      exacts [e0, e1, e2]
  push Not at h2
  by_cases h1 : ∃ v ∈ W, v 1 ≠ 0
  · obtain ⟨v, hvW, hv1⟩ := h1
    have hv2 := h2 v hvW
    obtain ⟨u, hu, hu01⟩ := h01 1
    have hd := hdiff u hu v hvW
    have e0 : (Pi.single 0 1 : Fin 3 → K) ∈ W := by
      have h := W.smul_mem (v 1)⁻¹ hd
      convert h using 1
      ext i
      fin_cases i <;> simp [hu01, hv1, hv2]
    have e1 : (Pi.single 1 1 : Fin 3 → K) ∈ W := by
      have h := W.smul_mem (v 1)⁻¹ (W.sub_mem hvW (W.smul_mem (v 0) e0))
      convert h using 1
      ext i
      fin_cases i <;> simp [hv1, hv2]
    refine ⟨2, by norm_num, le_antisymm (fun x hx => ?_) (flagSpace_le_of fun j hj => ?_)⟩
    · rw [LinearFlag.mem_flagSpace]
      intro j hj
      fin_cases j <;> simp at hj
      exact h2 x hx
    · fin_cases j <;> simp at hj
      exacts [e0, e1]
  push Not at h1
  by_cases h0 : ∃ v ∈ W, v 0 ≠ 0
  · obtain ⟨v, hvW, hv0⟩ := h0
    have e0 : (Pi.single 0 1 : Fin 3 → K) ∈ W := by
      have h := W.smul_mem (v 0)⁻¹ hvW
      convert h using 1
      ext i
      fin_cases i <;> simp [hv0, h1 v hvW, h2 v hvW]
    refine ⟨1, by norm_num, le_antisymm (fun x hx => ?_) (flagSpace_le_of fun j hj => ?_)⟩
    · rw [LinearFlag.mem_flagSpace]
      intro j hj
      fin_cases j <;> simp at hj
      exacts [h1 x hx, h2 x hx]
    · fin_cases j <;> simp at hj
      exact e0
  push Not at h0
  refine ⟨0, by norm_num, ?_⟩
  rw [LinearFlag.flagSpace_zero, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  ext i
  fin_cases i
  exacts [h0 x hx, h1 x hx, h2 x hx]

theorem stab_of_normal_of {Q O U : Subgroup (GL (Fin 3) K)} (hUQ : U ≤ Q) (hU : U ≤ uni3 K)
    (h01 : ∀ t : K, ∃ u ∈ U, (u : Matrix (Fin 3) (Fin 3) K) 0 1 = t)
    (h12 : ∀ t : K, ∃ u ∈ U, (u : Matrix (Fin 3) (Fin 3) K) 1 2 = t) (hO1 : O ≠ ⊥)
    (hOU : O ≤ U) (hQN : Q ≤ Subgroup.normalizer (O : Set (GL (Fin 3) K))) :
    Q ≤ flagStab 3 1 K ∨ Q ≤ flagStab 3 2 K := by
  classical
  let W : Submodule K (Fin 3 → K) :=
    { carrier := {v | ∀ o ∈ O, (o : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v}
      add_mem' := fun {v w} hv hw o ho => by rw [mulVec_add, hv o ho, hw o ho]
      zero_mem' := fun o _ => mulVec_zero _
      smul_mem' := fun c v hv o ho => by rw [mulVec_smul, hv o ho] }
  have hmemW : ∀ {v : Fin 3 → K}, v ∈ W ↔ ∀ o ∈ O, (o : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v :=
    Iff.rfl
  have hpres : ∀ g ∈ Subgroup.normalizer (O : Set (GL (Fin 3) K)), ∀ v ∈ W,
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
    intro g hg v hv
    rw [hmemW]
    intro o ho
    have h1 : g⁻¹ * o * g ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) o).mp ho
      simpa using this
    have h2 := hmemW.mp hv _ h1
    have h3 : (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ * o * g : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = (o : Matrix (Fin 3) (Fin 3) K) * g := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    calc (o : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
        = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (((g⁻¹ * o * g : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by rw [mulVec_mulVec, mulVec_mulVec, h3]
      _ = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v := by rw [h2]
  obtain ⟨m, -, hWm⟩ := eq_flagSpace_of_invariant_of hU h01 h12 fun u hu v hv =>
    hpres u (hQN (hUQ hu)) v hv
  have hcol : ∀ (M : Matrix (Fin 3) (Fin 3) K) (j i : Fin 3),
      (M *ᵥ Pi.single j 1) i = M i j := fun M j i => by
    rw [mulVec_single_one]
    rfl
  have he0 : (Pi.single 0 1 : Fin 3 → K) ∈ W := by
    rw [hmemW]
    intro o ho
    obtain ⟨hlow, hdiag⟩ := uni3_entries (hU (hOU ho))
    ext i
    rw [hcol]
    fin_cases i
    · simpa using hdiag 0
    · simpa using hlow 1 0 (by decide)
    · simpa using hlow 2 0 (by decide)
  have hWtop : ∃ v, v ∉ W := by
    by_contra h
    push Not at h
    apply hO1
    rw [eq_bot_iff]
    intro o ho
    rw [Subgroup.mem_bot]
    apply Units.ext
    ext i j
    have h1 := congrFun (hmemW.mp (h (Pi.single j 1)) o ho) i
    rw [hcol] at h1
    rw [h1, Units.val_one, one_apply, Pi.single_apply]
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [LinearFlag.flagSpace_zero] at hWm
    have h1 : (Pi.single 0 1 : Fin 3 → K) ∈ (⊥ : Submodule K (Fin 3 → K)) := hWm ▸ he0
    rw [Submodule.mem_bot] at h1
    have := congrFun h1 0
    simp at this
  have hm2 : m ≤ 2 := by
    by_contra hm
    obtain ⟨v, hv⟩ := hWtop
    apply hv
    rw [hWm, LinearFlag.mem_flagSpace]
    intro j hj
    have := j.2
    omega
  have hstab : Q ≤ flagStab 3 m K := fun g hg => mem_flagStab.mpr fun i j hj hi => by
    have h := hpres g (hQN hg) _ ((hWm ▸ single_mem_flagSpace hj : _ ∈ W))
    rw [hWm, LinearFlag.mem_flagSpace] at h
    have h' := h i hi
    rw [hcol] at h'
    exact h'
  have hm : m = 1 ∨ m = 2 := by omega
  rcases hm with rfl | rfl
  · exact Or.inl hstab
  · exact Or.inr hstab

theorem triangular_three_of [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {B U E : Subgroup (GL (Fin 3) K)} (hU : U ≤ uni3 K)
    (h01 : ∀ t : K, ∃ u ∈ U, (u : Matrix (Fin 3) (Fin 3) K) 0 1 = t)
    (h12 : ∀ t : K, ∃ u ∈ U, (u : Matrix (Fin 3) (Fin 3) K) 1 2 = t) (hEU : E ≤ U)
    (hEr : E ≤ rootGL (0 : Fin 3) 2 (by decide)) (hE4 : 4 ≤ Nat.card E)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBodd : Odd (Nat.card B))
    (hBU : (B : Set (GL (Fin 3) K)) * (U : Set (GL (Fin 3) K)) =
      (U : Set (GL (Fin 3) K)) * B) :
    B ≤ borGL 3 K := by
  have hUp : IsPGroup 2 U := isPGroup_uni3.to_le hU
  have hU3 : U ≤ borGL 3 K := hU.trans (uniGL_le_borGL 3)
  rcases exists_normal_or_le_normalizer hBab hBodd hUp hBU with ⟨O, hO1, hOU, hON⟩ | hN
  · rcases stab_of_normal_of le_sup_right hU h01 h12 hO1 hOU hON with hQ1 | hQ2
    ·
      have hQ' : ∀ g ∈ B ⊔ U, ∀ i : Fin 2,
          (g : Matrix (Fin 3) (Fin 3) K) i.succ 0 = 0 := fun g hg i =>
        mem_flagStab.mp (hQ1 hg) _ _ (by simp) (by simp)
      have hmap : (U.subgroupOf (B ⊔ U)).map (succHom hQ') = uni2 K := by
        apply le_antisymm
        · rintro _ ⟨u, hu, rfl⟩
          obtain ⟨hlow, hdiag⟩ := uni3_entries (hU hu)
          refine mem_rootGL.mpr ⟨((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2, ?_⟩
          apply Units.ext
          change succMat ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
            transvection (0 : Fin 2) 1 _
          ext i j
          fin_cases i <;> fin_cases j
          · simpa [succMat, transvection] using hdiag 1
          · simp [succMat, transvection]
          · simpa [succMat, transvection] using hlow 2 1 (by decide)
          · simpa [succMat, transvection] using hdiag 2
        · rintro _ ⟨c, rfl⟩
          obtain ⟨u, hu, hu12⟩ := h12 (Multiplicative.toAdd c)
          obtain ⟨hlow, hdiag⟩ := uni3_entries (hU hu)
          refine ⟨⟨u, le_sup_right (a := B) hu⟩, hu, ?_⟩
          apply Units.ext
          change succMat ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
            transvection (0 : Fin 2) 1 (Multiplicative.toAdd c)
          ext i j
          fin_cases i <;> fin_cases j
          · simpa [succMat, transvection] using hdiag 1
          · simpa [succMat, transvection] using hu12
          · simpa [succMat, transvection] using hlow 2 1 (by decide)
          · simpa [succMat, transvection] using hdiag 2
      have hB2 := map_le_borGL_two hK (succHom hQ') le_sup_left le_sup_right hmap hBab hBodd hBU
      intro b hb
      have hbQ : b ∈ B ⊔ U := le_sup_left (b := U) hb
      have hb' : succHom hQ' ⟨b, hbQ⟩ ∈ borGL 2 K := hB2 ⟨⟨b, hbQ⟩, hb, rfl⟩
      rw [mem_borGL_two] at hb'
      exact mem_borGL_three.mpr ⟨hQ' b hbQ 0, hQ' b hbQ 1, hb'⟩
    ·
      have hmap : (U.subgroupOf (B ⊔ U)).map (topHom (by norm_num : 2 ≤ 3) hQ2) = uni2 K := by
        apply le_antisymm
        · rintro _ ⟨u, hu, rfl⟩
          obtain ⟨hlow, hdiag⟩ := uni3_entries (hU hu)
          refine mem_rootGL.mpr ⟨((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1, ?_⟩
          apply Units.ext
          change topMat (by norm_num : 2 ≤ 3) ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
            transvection (0 : Fin 2) 1 _
          ext i j
          fin_cases i <;> fin_cases j
          · simpa [topMat, transvection] using hdiag 0
          · simp [topMat, transvection]
          · simpa [topMat, transvection] using hlow 1 0 (by decide)
          · simpa [topMat, transvection] using hdiag 1
        · rintro _ ⟨c, rfl⟩
          obtain ⟨u, hu, hu01⟩ := h01 (Multiplicative.toAdd c)
          obtain ⟨hlow, hdiag⟩ := uni3_entries (hU hu)
          refine ⟨⟨u, le_sup_right (a := B) hu⟩, hu, ?_⟩
          apply Units.ext
          change topMat (by norm_num : 2 ≤ 3) ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
            transvection (0 : Fin 2) 1 (Multiplicative.toAdd c)
          ext i j
          fin_cases i <;> fin_cases j
          · simpa [topMat, transvection] using hdiag 0
          · simpa [topMat, transvection] using hu01
          · simpa [topMat, transvection] using hlow 1 0 (by decide)
          · simpa [topMat, transvection] using hdiag 1
      have hB2 := map_le_borGL_two hK (topHom (by norm_num : 2 ≤ 3) hQ2) le_sup_left
        le_sup_right hmap hBab hBodd hBU
      intro b hb
      have hbQ : b ∈ B ⊔ U := le_sup_left (b := U) hb
      have hb' := hB2 ⟨⟨b, hbQ⟩, hb, rfl⟩
      rw [mem_borGL_two] at hb'
      have h2 := mem_flagStab.mp (hQ2 hbQ)
      exact mem_borGL_three.mpr ⟨hb', h2 2 0 (by simp) (by simp), h2 2 1 (by simp) (by simp)⟩
  ·
    refine le_of_commute (E := E) (hEU.trans hN) (fun a ha b hb => rootGL_comm a (hEr ha) b
      (hEr hb)) (fun e he => rootGL_mul_self e (hEr he)) hE4 hBodd ?_
    intro e he he1 b _ heb
    obtain ⟨c, rfl⟩ := mem_rootGL.mp (hEr he)
    have hc0 := ne_zero_of_trGL_ne_one he1
    have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) heb
    simp only [Units.val_mul, coe_trGL] at h1
    obtain ⟨hr, hs⟩ := entry_eq_zero_of_commute hc0 h1
    exact mem_borGL_three.mpr ⟨hr 1 (by decide), hr 2 (by decide), hs 1 (by decide)⟩

end Tri

end H

end CFSG.Quasithin
