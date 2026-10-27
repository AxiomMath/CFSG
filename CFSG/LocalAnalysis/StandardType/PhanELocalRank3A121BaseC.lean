module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A121BaseA

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

private theorem plh_finrank_W2 : finrank K (W2 : Submodule K (Fin 4 → K)) = 2 := by
  let e : (W2 : Submodule K (Fin 4 → K)) ≃ₗ[K] (Fin 2 → K) :=
    { toFun := fun v => ![v.1 1, v.1 2]
      invFun := fun w => ⟨![0, w 0, w 1, 0], by
        rw [mem_W2_iff]
        exact ⟨by simp, by simp⟩⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext j
        obtain ⟨h0, h3⟩ := (mem_W2_iff v.1).mp v.2
        fin_cases j <;> simp [h0, h3]
      right_inv := fun w => by
        funext j
        fin_cases j <;> simp
      map_add' := fun v w => by
        funext j
        fin_cases j <;> simp
      map_smul' := fun a v => by
        funext j
        fin_cases j <;> simp }
  have h := e.finrank_eq
  rw [Module.finrank_fin_fun] at h
  exact h

private theorem plh_W2_of_gen {c₀ y₀ : Fin 4 → K}
    (hc₀ : c₀ ∈ (Vtail : Submodule K (Fin 4 → K)))
    (hy₀ : y₀ ∈ (Vtail : Submodule K (Fin 4 → K))) :
    y₀ 3 • c₀ - c₀ 3 • y₀ ∈ (W2 : Submodule K (Fin 4 → K)) := by
  rw [mem_W2_iff]
  constructor
  · have hc0 : c₀ 0 = 0 := by simpa [Vtail] using hc₀
    have hy0 : y₀ 0 = 0 := by simpa [Vtail] using hy₀
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc0, hy0]
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

private theorem plh_inf_eq_bot_of_not_le {p T : Submodule K (Fin 4 → K)}
    (hp : finrank K p = 1) (hnot : ¬ p ≤ T) : p ⊓ T = ⊥ := by
  by_contra h
  have h0 : finrank K ↥(p ⊓ T) ≠ 0 := fun h0 => h (Submodule.finrank_eq_zero.mp h0)
  have hle : finrank K ↥(p ⊓ T) ≤ 1 := hp ▸ Submodule.finrank_mono inf_le_left
  have h1 : finrank K ↥(p ⊓ T) = 1 := by omega
  have heq : p ⊓ T = p := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, hp])
  exact hnot (heq ▸ inf_le_right)

private theorem plh_not_le_of_dirVec_notMem {x₀ δ : Fin 4 → K}
    {T : Submodule K (Fin 4 → K)} (hxT : x₀ ∈ T) (hδT : δ ∉ T) {s : K} (hs : s ≠ 0) :
    ¬ Submodule.span K {x₀ + s • δ} ≤ T := by
  intro hle
  have h1 : x₀ + s • δ ∈ T := hle (Submodule.mem_span_singleton_self _)
  have h2 : s • δ ∈ T := by
    have h := T.sub_mem h1 hxT
    have heq : (x₀ + s • δ) - x₀ = s • δ := by abel
    rwa [heq] at h
  have h3 : δ ∈ T := by
    have h := T.smul_mem s⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at h
  exact hδT h3

theorem a121_cone (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ∀ x y z : Submodule K (Fin 4 → K), BPt x → BPt y → BPt z →
      BAdj (D121 (K := K) f) x y → BAdj (D121 (K := K) f) y z → BAdj (D121 (K := K) f) z x →
      ∃ t, BPt t ∧ BAdj (D121 (K := K) f) x t ∧ BAdj (D121 (K := K) f) y t ∧
        BAdj (D121 (K := K) f) z t ∧ finrank K ↥(x ⊔ y ⊔ t) = 3 ∧
        finrank K ↥(y ⊔ z ⊔ t) = 3 ∧ finrank K ↥(z ⊔ x ⊔ t) = 3 := by
  intro x y z hx hy hz hxy hyz hzx
  classical
  haveI := Fintype.ofFinite K
  obtain ⟨x₀, rfl, hx₀V, hx₀3⟩ := exists_gen_off_V3 hx (hxy.2.1).1
  obtain ⟨y₀, rfl, hy₀V, hy₀3⟩ := exists_gen_off_V3 hy (hyz.2.1).1
  obtain ⟨z₀, rfl, hz₀V, hz₀3⟩ := exists_gen_off_V3 hz (hzx.2.1).1
  have hxy2 : finrank K ↥(Submodule.span K {x₀} ⊔ Submodule.span K {y₀}) = 2 :=
    finrank_sup_of_ne_pts hx.2 hy.2 hxy.1
  have hyz2 : finrank K ↥(Submodule.span K {y₀} ⊔ Submodule.span K {z₀}) = 2 :=
    finrank_sup_of_ne_pts hy.2 hz.2 hyz.1
  have hzx2 : finrank K ↥(Submodule.span K {z₀} ⊔ Submodule.span K {x₀}) = 2 :=
    finrank_sup_of_ne_pts hz.2 hx.2 hzx.1
  have hnotW2xy : ¬ (W2 : Submodule K (Fin 4 → K)) ≤
      Submodule.span K {x₀} ⊔ Submodule.span K {y₀} := by
    intro hle
    have hfin : finrank K (W2 : Submodule K (Fin 4 → K)) =
        finrank K ↥(Submodule.span K {x₀} ⊔ Submodule.span K {y₀}) := by
      rw [plh_finrank_W2, hxy2]
    have heq : (W2 : Submodule K (Fin 4 → K)) =
        Submodule.span K {x₀} ⊔ Submodule.span K {y₀} :=
      Submodule.eq_of_le_of_finrank_eq hle hfin
    have hxW2 : Submodule.span K {x₀} ≤ (W2 : Submodule K (Fin 4 → K)) := by
      rw [heq]
      exact le_sup_left
    have hxV3 : Submodule.span K {x₀} ≤ Vsub 4 3 := hxW2.trans inf_le_right
    have hbot : Submodule.span K {x₀} = ⊥ := by
      rw [← inf_eq_left.mpr hxV3]
      exact (hxy.2.1).1
    have h0 : finrank K ↥(Submodule.span K {x₀}) = 0 := by rw [hbot, finrank_bot]
    exact Nat.zero_ne_one (h0.symm.trans hx.2)
  have hnotW2yz : ¬ (W2 : Submodule K (Fin 4 → K)) ≤
      Submodule.span K {y₀} ⊔ Submodule.span K {z₀} := by
    intro hle
    have hfin : finrank K (W2 : Submodule K (Fin 4 → K)) =
        finrank K ↥(Submodule.span K {y₀} ⊔ Submodule.span K {z₀}) := by
      rw [plh_finrank_W2, hyz2]
    have heq : (W2 : Submodule K (Fin 4 → K)) =
        Submodule.span K {y₀} ⊔ Submodule.span K {z₀} :=
      Submodule.eq_of_le_of_finrank_eq hle hfin
    have hyW2 : Submodule.span K {y₀} ≤ (W2 : Submodule K (Fin 4 → K)) := by
      rw [heq]
      exact le_sup_left
    have hyV3 : Submodule.span K {y₀} ≤ Vsub 4 3 := hyW2.trans inf_le_right
    have hbot : Submodule.span K {y₀} = ⊥ := by
      rw [← inf_eq_left.mpr hyV3]
      exact (hyz.2.1).1
    have h0 : finrank K ↥(Submodule.span K {y₀}) = 0 := by rw [hbot, finrank_bot]
    exact Nat.zero_ne_one (h0.symm.trans hy.2)
  have hnotW2zx : ¬ (W2 : Submodule K (Fin 4 → K)) ≤
      Submodule.span K {z₀} ⊔ Submodule.span K {x₀} := by
    intro hle
    have hfin : finrank K (W2 : Submodule K (Fin 4 → K)) =
        finrank K ↥(Submodule.span K {z₀} ⊔ Submodule.span K {x₀}) := by
      rw [plh_finrank_W2, hzx2]
    have heq : (W2 : Submodule K (Fin 4 → K)) =
        Submodule.span K {z₀} ⊔ Submodule.span K {x₀} :=
      Submodule.eq_of_le_of_finrank_eq hle hfin
    have hzW2 : Submodule.span K {z₀} ≤ (W2 : Submodule K (Fin 4 → K)) := by
      rw [heq]
      exact le_sup_left
    have hzV3 : Submodule.span K {z₀} ≤ Vsub 4 3 := hzW2.trans inf_le_right
    have hbot : Submodule.span K {z₀} = ⊥ := by
      rw [← inf_eq_left.mpr hzV3]
      exact (hzx.2.1).1
    have h0 : finrank K ↥(Submodule.span K {z₀}) = 0 := by rw [hbot, finrank_bot]
    exact Nat.zero_ne_one (h0.symm.trans hz.2)
  let S : Finset (Submodule K (Fin 4 → K)) :=
    {Submodule.span K {x₀} ⊔ Submodule.span K {y₀},
     Submodule.span K {y₀} ⊔ Submodule.span K {z₀},
     Submodule.span K {z₀} ⊔ Submodule.span K {x₀}}
  have hS : ∀ P ∈ S, P ≤ (Vtail : Submodule K (Fin 4 → K)) ∧
      ¬ (W2 : Submodule K (Fin 4 → K)) ≤ P := by
    intro P hP
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl | rfl
    · exact ⟨sup_le hx.1 hy.1, hnotW2xy⟩
    · exact ⟨sup_le hy.1 hz.1, hnotW2yz⟩
    · exact ⟨sup_le hz.1 hx.1, hnotW2zx⟩
  have hcardS : S.card ≤ 3 := by
    simpa [S] using Finset.card_le_three
      (a := Submodule.span K {x₀} ⊔ Submodule.span K {y₀})
      (b := Submodule.span K {y₀} ⊔ Submodule.span K {z₀})
      (c := Submodule.span K {z₀} ⊔ Submodule.span K {x₀})
  obtain ⟨ω, hω, hωavoid⟩ := exists_nrvec_dir_avoid f hK hq S hS hcardS
  let δ : Fin 4 → K := dirVec ω
  have hδn : NRvec f δ := (nrvec_dirVec f hK hω).1
  have hδW2 : δ ∈ (W2 : Submodule K (Fin 4 → K)) := (nrvec_dirVec f hK hω).2
  have hδ0 : δ 0 = 0 := ((mem_W2_iff δ).mp hδW2).1
  have hδ3 : δ 3 = 0 := ((mem_W2_iff δ).mp hδW2).2
  have hx₀0 : x₀ 0 = 0 := by simpa [Vtail] using hx₀V
  have hδxy : δ ∉ Submodule.span K {x₀} ⊔ Submodule.span K {y₀} :=
    hωavoid _ (by simp [S])
  have hδyz : δ ∉ Submodule.span K {y₀} ⊔ Submodule.span K {z₀} :=
    hωavoid _ (by simp [S])
  have hδzx : δ ∉ Submodule.span K {z₀} ⊔ Submodule.span K {x₀} :=
    hωavoid _ (by simp [S])
  let B0 : Finset K := {0}
  let By : Finset K := Finset.univ.filter
    (fun s : K => ¬ NRvec f ((y₀ 3 • x₀ - x₀ 3 • y₀) + (y₀ 3 * s) • δ))
  let Bz : Finset K := Finset.univ.filter
    (fun s : K => ¬ NRvec f ((z₀ 3 • x₀ - x₀ 3 • z₀) + (z₀ 3 * s) • δ))
  let Bl : Finset K := Finset.univ.filter
    (fun s : K => x₀ + s • δ ∈ Submodule.span K {y₀} ⊔ Submodule.span K {z₀})
  let B : Finset K := B0 ∪ By ∪ Bz ∪ Bl
  have hB0 : B0.card ≤ 1 := by simp [B0]
  have hBy : By.card ≤ 2 ^ f + 1 := by
    have h := card_not_nrvec_le f hK hδW2 hδn
      (w := y₀ 3 • x₀ - x₀ 3 • y₀) (plh_W2_of_gen hx₀V hy₀V) (α := y₀ 3) hy₀3
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    exact h
  have hBz : Bz.card ≤ 2 ^ f + 1 := by
    have h := card_not_nrvec_le f hK hδW2 hδn
      (w := z₀ 3 • x₀ - x₀ 3 • z₀) (plh_W2_of_gen hx₀V hz₀V) (α := z₀ 3) hz₀3
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    exact h
  have hBl : Bl.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro s hs s' hs'
    by_contra hne
    have hs1 : x₀ + s • δ ∈ Submodule.span K {y₀} ⊔ Submodule.span K {z₀} :=
      (Finset.mem_filter.mp hs).2
    have hs2 : x₀ + s' • δ ∈ Submodule.span K {y₀} ⊔ Submodule.span K {z₀} :=
      (Finset.mem_filter.mp hs').2
    have hmem := (Submodule.span K {y₀} ⊔ Submodule.span K {z₀}).sub_mem hs1 hs2
    have hkey : (s - s') • δ = (x₀ + s • δ) - (x₀ + s' • δ) := by
      rw [sub_smul]; abel
    rw [← hkey] at hmem
    have hsne : s - s' ≠ 0 := sub_ne_zero.mpr hne
    have hδmem : δ ∈ Submodule.span K {y₀} ⊔ Submodule.span K {z₀} := by
      have hm := (Submodule.span K {y₀} ⊔ Submodule.span K {z₀}).smul_mem (s - s')⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hsne, one_smul] at hm
    exact hδyz hδmem
  have hBcard : B.card < Nat.card K := by
    have h1 : B.card ≤ (B0 ∪ By ∪ Bz).card + Bl.card := Finset.card_union_le _ _
    have h2 : (B0 ∪ By ∪ Bz).card ≤ (B0 ∪ By).card + Bz.card := Finset.card_union_le _ _
    have h3 : (B0 ∪ By).card ≤ B0.card + By.card := Finset.card_union_le _ _
    have hbig : 1 + (2 ^ f + 1) + (2 ^ f + 1) + 1 < (2 ^ f) ^ 2 := by
      nlinarith [hq, sq_nonneg (2 ^ f - 3)]
    rw [hK]
    nlinarith [h1, h2, h3, hB0, hBy, hBz, hBl, hbig]
  have hBcard' : B.card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hBcard
  obtain ⟨s, -, hsB⟩ := Finset.exists_mem_notMem_of_card_lt_card hBcard'
  have hs0 : s ≠ 0 := by
    intro hs_eq
    exact hsB (by rw [hs_eq]; simp [B, B0])
  have hsy : NRvec f ((y₀ 3 • x₀ - x₀ 3 • y₀) + (y₀ 3 * s) • δ) := by
    by_contra h
    apply hsB
    show s ∈ B0 ∪ By ∪ Bz ∪ Bl
    exact Finset.mem_union_left Bl
      (Finset.mem_union_left Bz (Finset.mem_union_right B0
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
  have hsz : NRvec f ((z₀ 3 • x₀ - x₀ 3 • z₀) + (z₀ 3 * s) • δ) := by
    by_contra h
    apply hsB
    show s ∈ B0 ∪ By ∪ Bz ∪ Bl
    exact Finset.mem_union_left Bl
      (Finset.mem_union_right (B0 ∪ By)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  have hsl : x₀ + s • δ ∉ Submodule.span K {y₀} ⊔ Submodule.span K {z₀} := by
    intro hmem
    apply hsB
    show s ∈ B0 ∪ By ∪ Bz ∪ Bl
    exact Finset.mem_union_right (B0 ∪ By ∪ Bz)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩)
  have hne : x₀ + s • δ ≠ 0 := by
    intro h0
    have h3 := congrFun h0 3
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hδ3] at h3
    exact hx₀3 h3
  have ht1 : finrank K (Submodule.span K {x₀ + s • δ}) = 1 := finrank_span_singleton hne
  have htV : Submodule.span K {x₀ + s • δ} ≤ (Vtail : Submodule K (Fin 4 → K)) := by
    rw [Submodule.span_singleton_le_iff_mem]
    show (x₀ + s • δ) 0 = 0
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx₀0, hδ0]
  refine ⟨Submodule.span K {x₀ + s • δ}, ⟨htV, ht1⟩,
    badj121_self f hK hx₀V hx₀3 hδW2 hδn hs0,
    badj121_line f hK hx₀V hx₀3 hy₀V hy₀3 hδW2 hsy,
    badj121_line f hK hx₀V hx₀3 hz₀V hz₀3 hδW2 hsz, ?_, ?_, ?_⟩
  · have hnot : ¬ Submodule.span K {x₀ + s • δ} ≤
        Submodule.span K {x₀} ⊔ Submodule.span K {y₀} :=
      plh_not_le_of_dirVec_notMem
        (T := Submodule.span K {x₀} ⊔ Submodule.span K {y₀})
        (Submodule.mem_sup_left (Submodule.mem_span_singleton_self x₀)) hδxy hs0
    have hd : Disjoint (Submodule.span K {x₀} ⊔ Submodule.span K {y₀})
        (Submodule.span K {x₀ + s • δ}) :=
      disjoint_iff.mpr (by rw [inf_comm]; exact plh_inf_eq_bot_of_not_le ht1 hnot)
    have h := finrank_sup_of_disjoint hd
    rw [hxy2, ht1] at h
    simpa using h
  · have hnot : ¬ Submodule.span K {x₀ + s • δ} ≤
        Submodule.span K {y₀} ⊔ Submodule.span K {z₀} :=
      fun hle => hsl (hle (Submodule.mem_span_singleton_self _))
    have hd : Disjoint (Submodule.span K {y₀} ⊔ Submodule.span K {z₀})
        (Submodule.span K {x₀ + s • δ}) :=
      disjoint_iff.mpr (by rw [inf_comm]; exact plh_inf_eq_bot_of_not_le ht1 hnot)
    have h := finrank_sup_of_disjoint hd
    rw [hyz2, ht1] at h
    simpa using h
  · have hnot : ¬ Submodule.span K {x₀ + s • δ} ≤
        Submodule.span K {z₀} ⊔ Submodule.span K {x₀} :=
      plh_not_le_of_dirVec_notMem
        (T := Submodule.span K {z₀} ⊔ Submodule.span K {x₀})
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x₀)) hδzx hs0
    have hd : Disjoint (Submodule.span K {z₀} ⊔ Submodule.span K {x₀})
        (Submodule.span K {x₀ + s • δ}) :=
      disjoint_iff.mpr (by rw [inf_comm]; exact plh_inf_eq_bot_of_not_le ht1 hnot)
    have h := finrank_sup_of_disjoint hd
    rw [hzx2, ht1] at h
    simpa using h

end CFSG.ClassicalInvolution.Phan.PhanE

end
