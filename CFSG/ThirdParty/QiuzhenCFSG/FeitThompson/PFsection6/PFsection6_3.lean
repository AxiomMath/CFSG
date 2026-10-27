module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Classical

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section6

universe v
universe u

@[expose] public def theorem_6_3_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K M H1 H : Subgroup L)
    (S SM SH1 : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_6_1_statement K S T →
    M.Normal →
      H1.Normal →
        H.Normal →
          inducedKernelFamily K M SM →
            M ≤ H1 →
              H1 ≤ H →
                H ≤ K →
                  nilpotentQuotient M H →
                    inducedKernelFamily K H1 SH1 →
                      coherentFamily SH1 T →
                        H1.relIndex H > 4 * (K.relIndex (⊤ : Subgroup L)) ^ 2 + 1 →
                          coherentFamily SM T

/-- Peterfalvi Hypothesis `(6.4)`. -/


public theorem theorem_6_3_commutator_le_of_maximal
    {L : Type*} [Group L] [Finite L]
    {B A H : Subgroup L}
    (hBnorm : B.Normal) (hAnorm : A.Normal) (hHnorm : H.Normal)
    (hBA : B < A) (hAH : A ≤ H)
    (hnil : Group.IsNilpotent (H ⧸ B.subgroupOf H))
    (hmax : ∀ E : Subgroup L, B ≤ E → E < A → E.Normal → E ≤ B) :
    ⁅A, H⁆ ≤ B := by
  classical
  let Bsub : Subgroup H := B.subgroupOf H
  haveI : Bsub.Normal := hBnorm.subgroupOf H
  let q : H →* H ⧸ Bsub := QuotientGroup.mk' Bsub
  let Asub : Subgroup H := A.subgroupOf H
  haveI : Asub.Normal := hAnorm.subgroupOf H
  let N : Subgroup (H ⧸ Bsub) := Asub.map q
  haveI : N.Normal := QuotientGroup.map_normal Bsub Asub
  have hN_ne_bot : N ≠ ⊥ := by
    intro hNbot
    have hAB : A ≤ B := by
      intro a haA
      have haH : a ∈ H := hAH haA
      let aH : H := ⟨a, haH⟩
      have haAsub : aH ∈ Asub := haA
      have hqa_mem : q aH ∈ N := by
        exact ⟨aH, haAsub, rfl⟩
      have hqa_bot : q aH ∈ (⊥ : Subgroup (H ⧸ Bsub)) := by
        simpa [N, hNbot] using hqa_mem
      have hqa_one : q aH = 1 := by
        simpa using hqa_bot
      have haBsub : aH ∈ Bsub := by
        exact (QuotientGroup.eq_one_iff (N := Bsub) (x := aH)).1 hqa_one
      exact haBsub
    exact hBA.not_ge hAB
  have hcomm_lt : ⁅N, (⊤ : Subgroup (H ⧸ Bsub))⁆ < N := by
    letI : Group.IsNilpotent (H ⧸ Bsub) := hnil
    exact nilpotent_commutator_lt_self_of_normal N hN_ne_bot
  let C : Subgroup L := ⁅A, H⁆
  have hC_le_A : C ≤ A := by
    exact Subgroup.commutator_le_left (H₁ := A) (H₂ := H)
  have hC_le_H : C ≤ H := by
    exact Subgroup.commutator_le_right (H₁ := A) (H₂ := H)
  let E : Subgroup L := B ⊔ C
  have hE_le_A : E ≤ A := by
    exact sup_le hBA.le hC_le_A
  have hE_normal : E.Normal := by
    dsimp [E, C]
    infer_instance
  have hE_lt_A : E < A := by
    refine lt_of_le_of_ne hE_le_A ?_
    intro hEAeq
    have hA_le_E : A ≤ E := by rw [hEAeq]
    have hAsub_le_Esub : Asub ≤ E.subgroupOf H := by
      intro x hx
      exact hA_le_E hx
    have hN_le_Eimage : N ≤ (E.subgroupOf H).map q := by
      exact Subgroup.map_mono hAsub_le_Esub
    have hBsub_map_bot : Bsub.map q = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rcases hy with ⟨b, hb, rfl⟩
      exact (QuotientGroup.eq_one_iff (N := Bsub) (x := b)).2 hb
    have hCsub_eq : C.subgroupOf H = ⁅Asub, (⊤ : Subgroup H)⁆ := by
      exact Subgroup.map_injective H.subtype_injective (by
        calc
        (C.subgroupOf H).map H.subtype = C := by
          exact Subgroup.map_subgroupOf_eq_of_le hC_le_H
        _ = ⁅A, H⁆ := rfl
        _ = (⁅Asub, H.subgroupOf H⁆).map H.subtype := by
          exact (commutator_subgroupOf_map_eq H H A le_rfl hAH).symm
        _ = (⁅Asub, (⊤ : Subgroup H)⁆).map H.subtype := by
          simp)
    have hCimage_le : (C.subgroupOf H).map q ≤
        ⁅N, (⊤ : Subgroup (H ⧸ Bsub))⁆ := by
      rw [hCsub_eq]
      calc
        (⁅Asub, (⊤ : Subgroup H)⁆).map q ≤
            ⁅Asub.map q, ((⊤ : Subgroup H).map q)⁆ := by
          rw [Subgroup.map_commutator]
        _ ≤ ⁅N, (⊤ : Subgroup (H ⧸ Bsub))⁆ := by
          rw [show Asub.map q = N from rfl]
          exact Subgroup.commutator_mono le_rfl le_top
    have hEimage_le : (E.subgroupOf H).map q ≤
        ⁅N, (⊤ : Subgroup (H ⧸ Bsub))⁆ := by
      have hsubsup : E.subgroupOf H = Bsub ⊔ C.subgroupOf H := by
        calc
          E.subgroupOf H = (B ⊔ C).subgroupOf H := rfl
          _ = B.subgroupOf H ⊔ C.subgroupOf H :=
            Subgroup.subgroupOf_sup (A := B) (A' := C) (B := H)
              (hBA.le.trans hAH) hC_le_H
      rw [hsubsup, Subgroup.map_sup]
      exact sup_le (by simp [Bsub, hBsub_map_bot]) hCimage_le
    exact hcomm_lt.not_ge (hN_le_Eimage.trans hEimage_le)
  have hC_le_E : C ≤ E := le_sup_right
  intro x hx
  exact (hmax E le_sup_left hE_lt_A hE_normal) (hC_le_E hx)

public theorem theorem_6_3_arithmetic_contradiction
    {L : Type*} [Group L] [Finite L]
    (K A H1 H : Subgroup L)
    (hAH1 : A ≤ H1) (hH1H : H1 ≤ H) (hHK : H ≤ K)
    (hbound : H1.relIndex H > 4 * (K.relIndex (⊤ : Subgroup L)) ^ 2 + 1)
    (hineq : (2 : ℝ) * (H.relIndex (⊤ : Subgroup L) : ℝ) *
        Real.sqrt (A.relIndex H : ℝ) ≥ (A.relIndex K : ℝ) - 1) :
    False := by
  let x : ℕ := A.relIndex H
  let y : ℕ := H.relIndex K
  let z : ℕ := K.relIndex (⊤ : Subgroup L)
  have hAH : A ≤ H := hAH1.trans hH1H
  have hx : 1 ≤ x := by
    have hne : A.relIndex H ≠ 0 := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
    omega
  have hy : 1 ≤ y := by
    have hne : H.relIndex K ≠ 0 := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
    omega
  have hH1_le_x : H1.relIndex H ≤ x := by
    have hrel : A.relIndex H1 * H1.relIndex H = A.relIndex H := by
      exact Subgroup.relIndex_mul_relIndex A H1 H hAH1 hH1H
    have hpos : 1 ≤ A.relIndex H1 := by
      have hne : A.relIndex H1 ≠ 0 := by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite
      omega
    calc
      H1.relIndex H ≤ A.relIndex H1 * H1.relIndex H :=
        Nat.le_mul_of_pos_left (H1.relIndex H) hpos
      _ = x := by simpa [x] using hrel
  have hgap : 4 * z ^ 2 + 1 < x := by
    exact lt_of_lt_of_le hbound hH1_le_x
  have hrelAK : A.relIndex H * H.relIndex K = A.relIndex K := by
    exact Subgroup.relIndex_mul_relIndex A H K hAH hHK
  have hrelHtop : H.relIndex K * K.relIndex (⊤ : Subgroup L) =
      H.relIndex (⊤ : Subgroup L) := by
    exact Subgroup.relIndex_mul_relIndex H K ⊤ hHK le_top
  have hineq' : ((x * y : ℕ) : ℝ) - 1 ≤
      (2 : ℝ) * ((y * z : ℕ) : ℝ) * Real.sqrt (x : ℝ) := by
    have h := hineq
    rw [← hrelAK, ← hrelHtop] at h
    simpa [x, y, z, mul_assoc, mul_left_comm, mul_comm] using h
  have hypos : (0 : ℝ) < (y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hy)
  have hxnonneg : 0 ≤ (x : ℝ) - 1 := by
    have hxreal : (1 : ℝ) ≤ x := by exact_mod_cast hx
    linarith
  have hmul_left : (y : ℝ) * ((x : ℝ) - 1) ≤ ((x * y : ℕ) : ℝ) - 1 := by
    have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
    rw [Nat.cast_mul]
    nlinarith
  have hmul_bound : (y : ℝ) * ((x : ℝ) - 1) ≤
      (y : ℝ) * ((2 : ℝ) * (z : ℝ) * Real.sqrt (x : ℝ)) := by
    calc
      (y : ℝ) * ((x : ℝ) - 1) ≤ ((x * y : ℕ) : ℝ) - 1 := hmul_left
      _ ≤ (2 : ℝ) * ((y * z : ℕ) : ℝ) * Real.sqrt (x : ℝ) := hineq'
      _ = (y : ℝ) * ((2 : ℝ) * (z : ℝ) * Real.sqrt (x : ℝ)) := by
        rw [Nat.cast_mul]
        ring
  have hbound' : (x : ℝ) - 1 ≤
      (2 : ℝ) * (z : ℝ) * Real.sqrt (x : ℝ) := by
    nlinarith
  have hsq : ((x : ℝ) - 1) ^ 2 ≤
      ((2 : ℝ) * (z : ℝ) * Real.sqrt (x : ℝ)) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hxnonneg hbound'
  have hsqrt_sq : Real.sqrt (x : ℝ) ^ 2 = (x : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsq2 : ((x : ℝ) - 1) ^ 2 ≤ (4 : ℝ) * (z : ℝ) ^ 2 * (x : ℝ) := by
    nlinarith
  have hgap3 : (4 : ℝ) * (z : ℝ) ^ 2 + 1 ≤ (x : ℝ) - 1 := by
    have hn : 4 * z ^ 2 + 1 ≤ x - 1 := by omega
    exact_mod_cast hn
  nlinarith [sq_nonneg ((x : ℝ) - 1 - (4 : ℝ) * (z : ℝ) ^ 2)]

public theorem theorem_6_3
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K M H1 H : Subgroup L)
    (S SM SH1 : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) :
    theorem_6_3_statement K M H1 H S SM SH1 T := by
  classical
  intro h61 hMnorm hH1norm hHnorm hSM hMH1 hH1H hHK hnil hSH1 hcohSH1 hbound
  have hSbot : inducedKernelFamily K ⊥ S := hypothesis_6_1_inducedKernelFamily_bot h61
  let P : Subgroup L → Prop := fun A =>
    M ≤ A ∧ A ≤ H1 ∧ A.Normal ∧ coherentFamily (inducedKernelFamilyOf K A S) T
  have hPH1 : P H1 := by
    refine ⟨hMH1, le_rfl, hH1norm, ?_⟩
    have hcanon : inducedKernelFamilyOf K H1 S = SH1 :=
      inducedKernelFamilyOf_eq_of_family hSbot hSH1
    simpa [hcanon]
  rcases Finite.exists_le_minimal (p := P) hPH1 with ⟨A, _hA_le_H1_sel, hAmin⟩
  rcases hAmin.prop with ⟨hMA, hAH1, hAnorm, hcohA⟩
  by_cases hAeqM : A = M
  · subst A
    have hcanon : inducedKernelFamilyOf K M S = SM :=
      inducedKernelFamilyOf_eq_of_family hSbot hSM
    simpa [hcanon] using hcohA
  · have hMltA : M < A := by
      refine lt_of_le_of_ne hMA ?_
      exact fun hMAeq => hAeqM hMAeq.symm
    let PB : Subgroup L → Prop := fun B => M ≤ B ∧ B < A ∧ B.Normal
    have hPBM : PB M := ⟨le_rfl, hMltA, hMnorm⟩
    rcases Finite.exists_le_maximal (p := PB) hPBM with ⟨B, _hMB_sel, hBmax⟩
    rcases hBmax.prop with ⟨hMB, hBA, hBnorm⟩
    let SA : Finset (Section1.ClassFunction L) := inducedKernelFamilyOf K A S
    let SB : Finset (Section1.ClassFunction L) := inducedKernelFamilyOf K B S
    have hA_le_K : A ≤ K := (hAH1.trans hH1H).trans hHK
    have hB_le_K : B ≤ K := hBA.le.trans hA_le_K
    have hSA : inducedKernelFamily K A SA := inducedKernelFamilyOf_isFamily hSbot hA_le_K
    have hSB : inducedKernelFamily K B SB := inducedKernelFamilyOf_isFamily hSbot hB_le_K
    have hnotSB : ¬ coherentFamily SB T := by
      intro hcohB
      have hPB : P B := ⟨hMB, hBA.le.trans hAH1, hBnorm, hcohB⟩
      have hA_le_B : A ≤ B := hAmin.le_of_le hPB hBA.le
      exact hBA.not_ge hA_le_B
    have hH1ltH : H1 < H := by
      refine lt_of_le_not_ge hH1H ?_
      intro hHH1
      have hrel : H1.relIndex H = 1 := (Subgroup.relIndex_eq_one).2 hHH1
      omega
    have hAltH : A < H := lt_of_le_of_lt hAH1 hH1ltH
    have hAltK : A < K := hAltH.trans_le hHK
    have hSBne : SB.Nonempty := by
      have hBltK : B < K := hBA.trans hAltK
      rcases inducedKernelFamily_nonempty_of_solvable_proper
          h61.2.2.1 hBnorm hBltK hSB with ⟨χ, hχ⟩
      exact ⟨χ, hχ⟩
    have hnilHB : Group.IsNilpotent (H ⧸ B.subgroupOf H) :=
      nilpotentQuotient_of_le_right hnil hMB hBnorm
    have hcomm : ⁅A, H⁆ ≤ B :=
      theorem_6_3_commutator_le_of_maximal hBnorm hAnorm hHnorm hBA hAltH.le hnilHB
        (by
          intro E hBE hEltA hEnorm
          exact hBmax.le_of_ge ⟨hMB.trans hBE, hEltA, hEnorm⟩ hBE)
    have hcent : centralQuotientHypothesis K B H A :=
      ⟨hBA.le, hAltH.le, hHK, hBnorm, hHnorm, hAnorm, hcomm⟩
    have hineq := theorem_6_2 K A B H A S SA SB T
      h61 hSA hSB hAnorm hAltK hcent hcohA hSBne hnotSB
    exact False.elim
      (theorem_6_3_arithmetic_contradiction K A H1 H hAH1 hH1H hHK hbound hineq)

end CFSG.Section6
