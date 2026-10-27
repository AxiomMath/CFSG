module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Def
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R3

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (f45)

@[expose] def sW : List ℕ := D1w.getD 8 []

@[expose] def tW : List ℕ := D2w.getD 24 []

theorem sW_mem : sW ∈ D1w := by decide +kernel

theorem tW_mem : tW ∈ D2w := by decide +kernel

@[expose] def cxS : Ah := aW sW

@[expose] def cxT : Ah := aW tW

theorem repL_cxS : RepL (evalAL sW) (cxS : P45) := repL_aW sW

theorem repL_cxT : RepL (evalAL tW) (cxT : P45) := repL_aW tW

theorem cxS_mem_P1h : cxS ∈ P1h := mem_P1h_of_repL repL_cxS (D1_check.2.2.1 sW sW_mem)

theorem cxT_mem_P2h : cxT ∈ P2h := mem_P2h_of_repL repL_cxT (D2_check.2.2.1 tW tW_mem)

theorem cxS_comm_f : cxS * fhatA = fhatA * cxS :=
  comm_of_comp_comm (v := fhatA) repL_fhat repL_cxS
    (D1_check.2.2.2 _ (Dl1_eq ▸ List.mem_map.2 ⟨sW, sW_mem, rfl⟩))

theorem cxT_comm_f : cxT * fhatA = fhatA * cxT :=
  comm_of_comp_comm (v := fhatA) repL_fhat repL_cxT
    (D2_check.2.2.2 _ (Dl2_eq ▸ List.mem_map.2 ⟨tW, tW_mem, rfl⟩))

@[expose] def memBL (l : PL) : Bool := l.getD 0 0 == 0 && sameSet (imgSet l L0) L0

theorem memBL_iff {g : Ah} {l : PL} (h : RepL l (g : P45)) : g ∈ Bh ↔ memBL l = true := by
  have hg0 : l.getD 0 0 = ((g : P45) 0 : ℕ) := h.2 0
  have h1 : g ∈ P1h ↔ l.getD 0 0 = 0 := by
    rw [mem_P1h_iff, hg0, ← Fin.val_inj]
    rfl
  have h2 : g ∈ P2h ↔ sameSet (imgSet l L0) L0 = true := by
    rw [mem_P2h_iff, L0S, image_lineSet h (by decide)]
    exact ⟨sameSet_of_lineSet_eq, lineSet_eq_of_sameSet⟩
  rw [Subgroup.mem_inf, h1, h2]
  simp [memBL]

theorem sign_gAP (k : ℕ) : Equiv.Perm.sign (gAP k) = if k % 4 = 3 then -1 else 1 := by
  unfold gAP
  by_cases h0 : k % 4 = 0
  · simp [h0, sign_of_mem_Xs (Xs_eq ▸ x45_mem)]
  by_cases h1 : k % 4 = 1
  · simp [h1, sign_of_mem_Xs (Xs_eq ▸ y45_mem)]
  by_cases h2 : k % 4 = 2
  · simp [h2, map_inv, sign_of_mem_Xs (Xs_eq ▸ y45_mem)]
  have h3 : k % 4 = 3 := by omega
  have : Equiv.Perm.sign f45 = -1 := by decide +kernel
  simp [h3, this]

theorem sign_wordAP (w : List ℕ) :
    Equiv.Perm.sign (wordAP w) = (-1) ^ (w.filter fun k => k % 4 = 3).length := by
  induction w with
  | nil => simp [wordAP]
  | cons k w ih =>
    have e : wordAP (k :: w) = gAP k * wordAP w := by simp [wordAP]
    rw [e, map_mul, ih, sign_gAP]
    by_cases hk : k % 4 = 3
    · simp [hk, pow_succ, mul_comm]
    · simp [hk]

theorem aW_mem_Yh {w : List ℕ}
    (h : (w.filter fun k => k % 4 = 3).length % 2 = 0) : aW w ∈ Yh := by
  rw [← signA_eq_one_iff, signA_apply]
  show Equiv.Perm.sign (wordAP w) = 1
  rw [sign_wordAP]
  exact (Nat.even_iff.2 h).neg_one_pow

theorem cxS_mem_Yh : cxS ∈ Yh := aW_mem_Yh (by decide +kernel)

theorem cxT_mem_Yh : cxT ∈ Yh := aW_mem_Yh (by decide +kernel)

theorem cxS_mem_D1h : cxS ∈ D1h :=
  ⟨⟨cxS_mem_P1h, cxS_mem_Yh⟩, Subgroup.mem_centralizer_singleton_iff.2 cxS_comm_f⟩

theorem cxT_mem_D2h : cxT ∈ D2h :=
  ⟨⟨cxT_mem_P2h, cxT_mem_Yh⟩, Subgroup.mem_centralizer_singleton_iff.2 cxT_comm_f⟩

theorem cxS_not_mem_Bh : cxS ∉ Bh := by
  rw [memBL_iff repL_cxS]
  have : memBL (evalAL sW) = false := by decide +kernel
  simp [this]

theorem cxT_not_mem_Bh : cxT ∉ Bh := by
  rw [memBL_iff repL_cxT]
  have : memBL (evalAL tW) = false := by decide +kernel
  simp [this]

theorem cxS_sq : cxS * cxS = 1 :=
  eq_of_repL_eq (repL_mul repL_cxS repL_cxS) (repL_one 45) (by decide +kernel)

theorem cxT_sq : cxT * cxT = 1 :=
  eq_of_repL_eq (repL_mul repL_cxT repL_cxT) (repL_one 45) (by decide +kernel)

theorem cox_pow : (cxS * cxT) ^ 4 = 1 ∧ (cxS * cxT) ^ 2 ≠ 1 := by
  have hst : RepL (comp (evalAL sW) (evalAL tW)) ((cxS * cxT : Ah) : P45) :=
    repL_mul repL_cxS repL_cxT
  refine ⟨?_, ?_⟩
  · apply Subtype.ext
    apply eq_of_repL (l := powL (comp (evalAL sW) (evalAL tW)) 4) (repL_powL hst 4)
    have : powL (comp (evalAL sW) (evalAL tW)) 4 = idL := by decide +kernel
    rw [this]
    exact repL_one 45
  · intro h
    have h2 : RepL (powL (comp (evalAL sW) (evalAL tW)) 2) (((cxS * cxT : Ah) ^ 2 : Ah) : P45) :=
      repL_powL hst 2
    rw [h] at h2
    have h3 : powL (comp (evalAL sW) (evalAL tW)) 2 = idL := repL_unique h2 (repL_one 45)
    have : powL (comp (evalAL sW) (evalAL tW)) 2 ≠ idL := by decide +kernel
    exact this h3

theorem isCoxPair_st : IsCoxPair cxS cxT :=
  ⟨cxS_mem_D1h, cxS_not_mem_Bh, by simpa [pow_two] using cxS_sq, cxT_mem_D2h, cxT_not_mem_Bh,
    by simpa [pow_two] using cxT_sq, cox_pow.1, cox_pow.2⟩

theorem nfix_sA : nfix (cxS : P45) = 13 := by
  rw [nfix_of_repL repL_cxS]
  decide +kernel

theorem nfix_tA : nfix (cxT : P45) = 5 := by
  rw [nfix_of_repL repL_cxT]
  decide +kernel

theorem cxS_dec : ∃ α ∈ Alt1h, ∃ u ∈ Uh, xA * cxS = α * u := by
  have hex : ∃ a ∈ Alt1L, ∃ u ∈ UL, comp a u = comp xL (evalAL sW) := by decide +kernel
  obtain ⟨a, ha, u, hu, hau⟩ := hex
  obtain ⟨α, hα, hαr⟩ := exists_elt_Alt1 ha
  have hu' : ∃ μ : Ah, μ ∈ Uh ∧ RepL u (μ : P45) := by
    obtain ⟨μ, -, hμ⟩ := exists_That_of_mem_Thl (UL_check.2.2.2.2.1 u hu).1
    exact ⟨μ, ⟨u, hu, hμ⟩, hμ⟩
  obtain ⟨μ, hμ, hμr⟩ := hu'
  refine ⟨α, hα, μ, hμ, ?_⟩
  have h1 : RepL (comp xL (evalAL sW)) ((α * μ : Ah) : P45) := by
    rw [← hau]
    exact repL_mul hαr hμr
  exact Subtype.ext (eq_of_repL (repL_mul repL_x repL_cxS) h1)

theorem cxT_dec : ∃ u₁ ∈ Uh, ∃ i : ℕ, i < 3 ∧ ∃ u₂ ∈ Uh,
    xA * dA * cxT = u₁ * bA ^ i * u₂ := by
  have hex : ∃ u₁ ∈ UL, ∃ i ∈ [0, 1, 2], ∃ u₂ ∈ UL,
      comp (comp u₁ (powL (evalAL wb) i)) u₂ = comp (comp xL dL) (evalAL tW) := by
    decide +kernel
  obtain ⟨u₁, hu₁, i, hi, u₂, hu₂, hu⟩ := hex
  have hUel : ∀ u ∈ UL, ∃ μ : Ah, μ ∈ Uh ∧ RepL u (μ : P45) := by
    intro u hu
    obtain ⟨μ, -, hμ⟩ := exists_That_of_mem_Thl (UL_check.2.2.2.2.1 u hu).1
    exact ⟨μ, ⟨u, hu, hμ⟩, hμ⟩
  obtain ⟨μ₁, hμ₁, hμ₁r⟩ := hUel u₁ hu₁
  obtain ⟨μ₂, hμ₂, hμ₂r⟩ := hUel u₂ hu₂
  have hi3 : i < 3 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    omega
  refine ⟨μ₁, hμ₁, i, hi3, μ₂, hμ₂, ?_⟩
  have h1 : RepL (comp (comp xL dL) (evalAL tW)) ((μ₁ * bA ^ i * μ₂ : Ah) : P45) := by
    rw [← hu]
    exact repL_mul (repL_mul hμ₁r (repL_powL repL_bA i)) hμ₂r
  exact Subtype.ext (eq_of_repL (repL_mul (repL_mul repL_x repL_dA) repL_cxT) h1)

end CFSG.Quasithin.H13.F431.U42Aut
