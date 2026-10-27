module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A121T
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A121Nr

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

private theorem plh_mem_Vsub3 (v : Fin 4 → K) : v ∈ Vsub 4 3 ↔ v 3 = 0 := by
  constructor
  · intro hv
    exact hv 3 (by norm_num)
  · intro hv j hj
    have hj3 : j = 3 := Fin.ext (by omega)
    subst hj3
    exact hv

private theorem plh_span_inf_Vsub3_bot {c : Fin 4 → K} (hc : c 3 ≠ 0) :
    Submodule.span K {c} ⊓ Vsub 4 3 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  obtain ⟨hvs, hv3⟩ := Submodule.mem_inf.mp hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hvs
  have h3 : a * c 3 = 0 := by
    have hmem := (plh_mem_Vsub3 (a • c)).mp hv3
    simpa using hmem
  have ha : a = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h hc
  rw [ha, zero_smul]

private theorem plh_okL_D121 (p L : Submodule K (Fin 4 → K)) :
    (D121 (K := K) f).okL p L ↔ p ⊓ Vsub 4 3 = ⊥ ∧
      (L ⊓ Vsub 4 3) ⊓ sgS K f 4 (L ⊓ Vsub 4 3) = ⊥ := Iff.rfl

theorem nrvec_smul (hK : Nat.card K = (2 ^ f) ^ 2) {a : K} (ha : a ≠ 0) {w : Fin 4 → K} :
    NRvec f (a • w) ↔ NRvec f w := by
  have hspan : Submodule.span K {a • w} = Submodule.span K {w} :=
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha) w
  have h0 : a • w ≠ 0 ↔ w ≠ 0 := by
    constructor
    · intro h hw
      exact h (by rw [hw, smul_zero])
    · intro hw h
      rcases smul_eq_zero.mp h with ha' | hw'
      · exact ha ha'
      · exact hw hw'
  simp only [NRvec, hspan]
  exact and_congr h0 Iff.rfl

theorem exists_gen_off_V3 {u : Submodule K (Fin 4 → K)} (hu : BPt u)
    (hu3 : u ⊓ Vsub 4 3 = ⊥) :
    ∃ u₀ : Fin 4 → K, u = Submodule.span K {u₀} ∧ u₀ ∈ (Vtail : Submodule K (Fin 4 → K)) ∧
      u₀ 3 ≠ 0 := by
  obtain ⟨u₀, hu₀ne, hu₀span⟩ :=
    CFSG.ClassicalInvolution.Phan.exists_eq_span_of_finrank_eq_one hu.2
  have hu₀mem : u₀ ∈ u := hu₀span.symm ▸ Submodule.mem_span_singleton_self u₀
  refine ⟨u₀, hu₀span, hu.1 hu₀mem, ?_⟩
  intro h3
  have hmem : u₀ ∈ u ⊓ Vsub 4 3 := ⟨hu₀mem, (plh_mem_Vsub3 u₀).mpr h3⟩
  rw [hu3] at hmem
  exact hu₀ne (by simpa using hmem)

theorem sup_inf_V3 {c₀ y₀ : Fin 4 → K} (hc₀ : c₀ ∈ (Vtail : Submodule K (Fin 4 → K)))
    (hy₀ : y₀ ∈ (Vtail : Submodule K (Fin 4 → K))) (hc3 : c₀ 3 ≠ 0) (hy3 : y₀ 3 ≠ 0)
    (hne : Submodule.span K {c₀} ≠ Submodule.span K {y₀}) :
    (Submodule.span K {c₀} ⊔ Submodule.span K {y₀}) ⊓ Vsub 4 3 =
        Submodule.span K {y₀ 3 • c₀ - c₀ 3 • y₀} ∧
      y₀ 3 • c₀ - c₀ 3 • y₀ ∈ (W2 : Submodule K (Fin 4 → K)) ∧ y₀ 3 • c₀ - c₀ 3 • y₀ ≠ 0 := by
  set e : Fin 4 → K := y₀ 3 • c₀ - c₀ 3 • y₀ with he
  have hc0 : c₀ 0 = 0 := by simpa [Vtail] using hc₀
  have hy0 : y₀ 0 = 0 := by simpa [Vtail] using hy₀
  have hc0ne : c₀ ≠ 0 := fun h => hc3 (by simp [h])
  have hy0ne : y₀ ≠ 0 := fun h => hy3 (by simp [h])
  have heW2 : e ∈ (W2 : Submodule K (Fin 4 → K)) := by
    rw [mem_W2_iff]
    constructor
    · show e 0 = 0
      rw [he]
      simp [hc0, hy0]
    · show e 3 = 0
      rw [he]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have he_mem : e ∈ Submodule.span K {c₀} ⊔ Submodule.span K {y₀} := by
    rw [he]
    exact Submodule.sub_mem_sup
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c₀))
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y₀))
  have he_ne0 : e ≠ 0 := by
    intro he0
    rw [he] at he0
    have hcyeq : y₀ 3 • c₀ = c₀ 3 • y₀ := sub_eq_zero.mp he0
    have hcy : c₀ ∈ Submodule.span K {y₀} := by
      rw [Submodule.mem_span_singleton]
      refine ⟨(y₀ 3)⁻¹ * c₀ 3, ?_⟩
      calc ((y₀ 3)⁻¹ * c₀ 3) • y₀ = (y₀ 3)⁻¹ • (c₀ 3 • y₀) := by rw [smul_smul]
        _ = (y₀ 3)⁻¹ • (y₀ 3 • c₀) := by rw [← hcyeq]
        _ = c₀ := by rw [smul_smul, inv_mul_cancel₀ hy3, one_smul]
    have hle : Submodule.span K {c₀} ≤ Submodule.span K {y₀} :=
      (Submodule.span_singleton_le_iff_mem c₀ (Submodule.span K {y₀})).mpr hcy
    exact hne (Submodule.eq_of_le_of_finrank_eq hle (by
      rw [finrank_span_singleton hc0ne, finrank_span_singleton hy0ne]))
  have hΛ2 : finrank K ↥(Submodule.span K {c₀} ⊔ Submodule.span K {y₀}) = 2 :=
    finrank_sup_of_ne_pts (finrank_span_singleton hc0ne) (finrank_span_singleton hy0ne) hne
  have hV3 : finrank K (Vsub (K := K) 4 3) = 3 := by
    simpa using finrank_Vsub (K := K) (n := 4) (c := 3) (by norm_num)
  have hsup4 : finrank K ↥((Submodule.span K {c₀} ⊔ Submodule.span K {y₀}) ⊔ Vsub 4 3) = 4 := by
    have hle : finrank K ↥((Submodule.span K {c₀} ⊔ Submodule.span K {y₀}) ⊔ Vsub 4 3) ≤ 4 := by
      have h := Submodule.finrank_mono (le_top :
        ((Submodule.span K {c₀} ⊔ Submodule.span K {y₀}) ⊔ Vsub 4 3) ≤ ⊤)
      rwa [finrank_top, Module.finrank_fin_fun] at h
    have hlt : 3 < finrank K ↥((Submodule.span K {c₀} ⊔ Submodule.span K {y₀}) ⊔ Vsub 4 3) := by
      have hss : Vsub (K := K) 4 3 <
          (Submodule.span K {c₀} ⊔ Submodule.span K {y₀}) ⊔ Vsub 4 3 := by
        refine lt_of_le_of_ne le_sup_right ?_
        intro heq
        have hcmem' : c₀ ∈
            (Submodule.span K {c₀} ⊔ Submodule.span K {y₀}) ⊔ Vsub 4 3 :=
          Submodule.mem_sup_left (Submodule.mem_sup_left
            (Submodule.mem_span_singleton_self c₀))
        have hcmem : c₀ ∈ Vsub (K := K) 4 3 := heq.symm ▸ hcmem'
        exact hc3 ((plh_mem_Vsub3 c₀).mp hcmem)
      have hlt' := Submodule.finrank_lt_finrank_of_lt hss
      rwa [hV3] at hlt'
    omega
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span K {c₀} ⊔ Submodule.span K {y₀}) (Vsub (K := K) 4 3)
  rw [hsup4, hΛ2, hV3] at hsum
  have hfin : finrank K ↥((Submodule.span K {c₀} ⊔ Submodule.span K {y₀}) ⊓ Vsub 4 3) = 1 := by
    omega
  have he_inf : e ∈ (Submodule.span K {c₀} ⊔ Submodule.span K {y₀}) ⊓ Vsub 4 3 :=
    ⟨he_mem, (inf_le_right : (W2 : Submodule K (Fin 4 → K)) ≤ Vsub 4 3) heW2⟩
  have hspan_le : Submodule.span K {e} ≤
      (Submodule.span K {c₀} ⊔ Submodule.span K {y₀}) ⊓ Vsub 4 3 :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr he_inf)
  refine ⟨(Submodule.eq_of_le_of_finrank_eq hspan_le ?_).symm, heW2, he_ne0⟩
  rw [finrank_span_singleton he_ne0, hfin]

theorem badj121_iff_nrvec (hK : Nat.card K = (2 ^ f) ^ 2) {c₀ y₀ : Fin 4 → K}
    (hc₀ : c₀ ∈ (Vtail : Submodule K (Fin 4 → K))) (hy₀ : y₀ ∈ (Vtail : Submodule K (Fin 4 → K)))
    (hc3 : c₀ 3 ≠ 0) (hy3 : y₀ 3 ≠ 0) (hne : Submodule.span K {c₀} ≠ Submodule.span K {y₀}) :
    BAdj (D121 (K := K) f) (Submodule.span K {c₀}) (Submodule.span K {y₀}) ↔
      NRvec f (y₀ 3 • c₀ - c₀ 3 • y₀) := by
  obtain ⟨hΛinf, -, hene⟩ := sup_inf_V3 hc₀ hy₀ hc3 hy3 hne
  have hu3 := plh_span_inf_Vsub3_bot (K := K) hc3
  have hy3bot := plh_span_inf_Vsub3_bot (K := K) hy3
  rw [BAdj, plh_okL_D121 f, plh_okL_D121 f, hΛinf, NRvec]
  constructor
  · rintro ⟨-, ⟨-, hC⟩, -⟩
    exact ⟨hene, hC⟩
  · rintro ⟨-, hC⟩
    exact ⟨hne, ⟨hu3, hC⟩, ⟨hy3bot, hC⟩⟩

theorem badj121_self (hK : Nat.card K = (2 ^ f) ^ 2) {c₀ δ : Fin 4 → K}
    (hc₀ : c₀ ∈ (Vtail : Submodule K (Fin 4 → K))) (hc3 : c₀ 3 ≠ 0)
    (hδ : δ ∈ (W2 : Submodule K (Fin 4 → K))) (hδn : NRvec f δ) {s : K} (hs : s ≠ 0) :
    BAdj (D121 (K := K) f) (Submodule.span K {c₀}) (Submodule.span K {c₀ + s • δ}) := by
  have hδ2 := (mem_W2_iff δ).mp hδ
  have hδV : δ ∈ (Vtail : Submodule K (Fin 4 → K)) := by
    show δ 0 = 0
    exact hδ2.1
  have hδ3 : δ 3 = 0 := hδ2.2
  have ht₀V : c₀ + s • δ ∈ (Vtail : Submodule K (Fin 4 → K)) :=
    Vtail.add_mem hc₀ (Vtail.smul_mem s hδV)
  have ht₀3 : (c₀ + s • δ) 3 ≠ 0 := by
    simpa [hδ3] using hc3
  have ht₀3eq : (c₀ + s • δ) 3 = c₀ 3 := by
    simp [hδ3]
  have hne' : Submodule.span K {c₀} ≠ Submodule.span K {c₀ + s • δ} := by
    intro heq
    have ht₀mem : c₀ + s • δ ∈ Submodule.span K {c₀} :=
      heq.symm ▸ Submodule.mem_span_singleton_self (c₀ + s • δ)
    have hdiff : (c₀ + s • δ) - c₀ ∈ Submodule.span K {c₀} :=
      Submodule.sub_mem _ ht₀mem (Submodule.mem_span_singleton_self c₀)
    rw [add_sub_cancel_left] at hdiff
    have hδmem : δ ∈ Submodule.span K {c₀} := by
      have hδeq : δ = s⁻¹ • (s • δ) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
      rw [hδeq]
      exact Submodule.smul_mem _ _ hdiff
    have hδinf : δ ∈ Submodule.span K {c₀} ⊓ Vsub 4 3 :=
      ⟨hδmem, (plh_mem_Vsub3 δ).mpr hδ3⟩
    rw [plh_span_inf_Vsub3_bot (K := K) hc3] at hδinf
    exact hδn.1 (by simpa using hδinf)
  have hvec : (c₀ + s • δ) 3 • c₀ - c₀ 3 • (c₀ + s • δ) = (-(c₀ 3 * s)) • δ := by
    rw [ht₀3eq, smul_add, smul_smul, neg_smul]
    abel
  refine (badj121_iff_nrvec f hK hc₀ ht₀V hc3 ht₀3 hne').mpr ?_
  rw [hvec]
  exact (nrvec_smul f hK (a := -(c₀ 3 * s))
    (neg_ne_zero.mpr (mul_ne_zero hc3 hs))).mpr hδn

theorem badj121_line (hK : Nat.card K = (2 ^ f) ^ 2) {c₀ y₀ δ : Fin 4 → K}
    (hc₀ : c₀ ∈ (Vtail : Submodule K (Fin 4 → K))) (hc3 : c₀ 3 ≠ 0)
    (hy₀ : y₀ ∈ (Vtail : Submodule K (Fin 4 → K))) (hy3 : y₀ 3 ≠ 0)
    (hδ : δ ∈ (W2 : Submodule K (Fin 4 → K))) {s : K}
    (hn : NRvec f ((y₀ 3 • c₀ - c₀ 3 • y₀) + (y₀ 3 * s) • δ)) :
    BAdj (D121 (K := K) f) (Submodule.span K {y₀}) (Submodule.span K {c₀ + s • δ}) := by
  have hδ2 := (mem_W2_iff δ).mp hδ
  have hδV : δ ∈ (Vtail : Submodule K (Fin 4 → K)) := by
    show δ 0 = 0
    exact hδ2.1
  have hδ3 : δ 3 = 0 := hδ2.2
  have ht₀V : c₀ + s • δ ∈ (Vtail : Submodule K (Fin 4 → K)) :=
    Vtail.add_mem hc₀ (Vtail.smul_mem s hδV)
  have ht₀3eq : (c₀ + s • δ) 3 = c₀ 3 := by
    simp [hδ3]
  have ht₀3 : (c₀ + s • δ) 3 ≠ 0 := by
    rw [ht₀3eq]
    exact hc3
  have hvec : (c₀ + s • δ) 3 • y₀ - y₀ 3 • (c₀ + s • δ) =
      -((y₀ 3 • c₀ - c₀ 3 • y₀) + (y₀ 3 * s) • δ) := by
    rw [ht₀3eq, smul_add, smul_smul]
    abel
  have hne' : Submodule.span K {y₀} ≠ Submodule.span K {c₀ + s • δ} := by
    intro heq
    have ht₀mem : c₀ + s • δ ∈ Submodule.span K {y₀} :=
      heq.symm ▸ Submodule.mem_span_singleton_self (c₀ + s • δ)
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp ht₀mem
    have ht₀3b : (c₀ + s • δ) 3 = b * y₀ 3 := by
      have h3 := congrFun hb 3
      simpa using h3.symm
    have hzero : y₀ 3 • (c₀ + s • δ) - (c₀ + s • δ) 3 • y₀ = 0 := by
      rw [ht₀3b, ← hb, smul_smul, mul_comm (y₀ 3) b, sub_self]
    have hvec2 : (y₀ 3 • c₀ - c₀ 3 • y₀) + (y₀ 3 * s) • δ =
        y₀ 3 • (c₀ + s • δ) - (c₀ + s • δ) 3 • y₀ := by
      rw [ht₀3eq, smul_add, smul_smul]
      abel
    rw [← hvec2] at hzero
    exact hn.1 hzero
  have hX : NRvec f ((-1 : K) • ((y₀ 3 • c₀ - c₀ 3 • y₀) + (y₀ 3 * s) • δ)) :=
    (nrvec_smul f hK (a := (-1 : K)) (by norm_num)).mpr hn
  refine (badj121_iff_nrvec f hK hy₀ ht₀V hy3 ht₀3 hne').mpr ?_
  rw [hvec]
  simpa only [neg_one_smul] using hX

theorem a121_link (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ∀ p L : Submodule K (Fin 4 → K), BFl p L → (D121 (K := K) f).okL p L →
      ∃ L₂ L₃ : Submodule K (Fin 4 → K), L₂ ≠ L₃ ∧ BFl p L₂ ∧ BFl p L₃ ∧
        (D121 (K := K) f).okL p L₂ ∧ (D121 (K := K) f).okL p L₃ := by
  intro p L hBFl hok
  obtain ⟨ω₁, hω₁, _, _⟩ := exists_sg_moved_avoid hK hq 0 0
  obtain ⟨ω₂, hω₂, hω₂ne, _⟩ := exists_sg_moved_avoid hK hq ω₁ ω₁
  have hn₁ := nrvec_dirVec (K := K) f hK hω₁
  have hn₂ := nrvec_dirVec (K := K) f hK hω₂
  have hokp : p ⊓ Vsub 4 3 = ⊥ := ((plh_okL_D121 f p L).mp hok).1
  have hN₂V3 : Submodule.span K {dirVec ω₁} ≤ Vsub 4 3 :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      ((inf_le_right : (W2 : Submodule K (Fin 4 → K)) ≤ Vsub 4 3) hn₁.2))
  have hN₃V3 : Submodule.span K {dirVec ω₂} ≤ Vsub 4 3 :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      ((inf_le_right : (W2 : Submodule K (Fin 4 → K)) ≤ Vsub 4 3) hn₂.2))
  have hN₂Vtail : Submodule.span K {dirVec ω₁} ≤ Vtail :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      ((inf_le_left : (W2 : Submodule K (Fin 4 → K)) ≤ Vtail) hn₁.2))
  have hN₃Vtail : Submodule.span K {dirVec ω₂} ≤ Vtail :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      ((inf_le_left : (W2 : Submodule K (Fin 4 → K)) ≤ Vtail) hn₂.2))
  have hN₂fin : finrank K (Submodule.span K {dirVec ω₁}) = 1 :=
    finrank_span_singleton hn₁.1.1
  have hN₃fin : finrank K (Submodule.span K {dirVec ω₂}) = 1 :=
    finrank_span_singleton hn₂.1.1
  have hpd₂ : p ⊓ Submodule.span K {dirVec ω₁} = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left p hN₂V3).trans (le_of_eq hokp))
  have hpd₃ : p ⊓ Submodule.span K {dirVec ω₂} = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left p hN₃V3).trans (le_of_eq hokp))
  have hS₂ : (p ⊔ Submodule.span K {dirVec ω₁}) ⊓ Vsub 4 3 =
      Submodule.span K {dirVec ω₁} := by
    rw [sup_comm p (Submodule.span K {dirVec ω₁}), sup_inf_assoc_of_le p hN₂V3, hokp,
      sup_bot_eq]
  have hS₃ : (p ⊔ Submodule.span K {dirVec ω₂}) ⊓ Vsub 4 3 =
      Submodule.span K {dirVec ω₂} := by
    rw [sup_comm p (Submodule.span K {dirVec ω₂}), sup_inf_assoc_of_le p hN₃V3, hokp,
      sup_bot_eq]
  have hok₂ : (D121 (K := K) f).okL p (p ⊔ Submodule.span K {dirVec ω₁}) := by
    rw [plh_okL_D121 f]
    exact ⟨hokp, by rw [hS₂]; exact hn₁.1.2⟩
  have hok₃ : (D121 (K := K) f).okL p (p ⊔ Submodule.span K {dirVec ω₂}) := by
    rw [plh_okL_D121 f]
    exact ⟨hokp, by rw [hS₃]; exact hn₂.1.2⟩
  have hfl₂ : BFl p (p ⊔ Submodule.span K {dirVec ω₁}) := by
    refine ⟨le_sup_left, ?_, hBFl.2.2.1, ?_⟩
    · exact sup_le (hBFl.1.trans hBFl.2.1) hN₂Vtail
    · have hsum := Submodule.finrank_sup_add_finrank_inf_eq p (Submodule.span K {dirVec ω₁})
      rw [hpd₂, finrank_bot, hBFl.2.2.1, hN₂fin] at hsum
      omega
  have hfl₃ : BFl p (p ⊔ Submodule.span K {dirVec ω₂}) := by
    refine ⟨le_sup_left, ?_, hBFl.2.2.1, ?_⟩
    · exact sup_le (hBFl.1.trans hBFl.2.1) hN₃Vtail
    · have hsum := Submodule.finrank_sup_add_finrank_inf_eq p (Submodule.span K {dirVec ω₂})
      rw [hpd₃, finrank_bot, hBFl.2.2.1, hN₃fin] at hsum
      omega
  have hNne : Submodule.span K {dirVec ω₁} ≠ Submodule.span K {dirVec ω₂} := by
    intro heq
    have hmem : dirVec ω₂ ∈ Submodule.span K {dirVec ω₁} :=
      heq.symm ▸ Submodule.mem_span_singleton_self (dirVec ω₂)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have ha1 : a = 1 := by
      have h1 := congrFun ha 1
      simpa [dirVec] using h1
    have h12 : ω₁ = ω₂ := by
      rw [ha1, one_smul] at ha
      have h2 := congrFun ha 2
      simpa [dirVec] using h2
    exact hω₂ne h12.symm
  have hLne : p ⊔ Submodule.span K {dirVec ω₁} ≠ p ⊔ Submodule.span K {dirVec ω₂} := by
    intro heq
    exact hNne (by rw [← hS₂, ← hS₃, heq])
  exact ⟨p ⊔ Submodule.span K {dirVec ω₁}, p ⊔ Submodule.span K {dirVec ω₂}, hLne, hfl₂, hfl₃,
    hok₂, hok₃⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
