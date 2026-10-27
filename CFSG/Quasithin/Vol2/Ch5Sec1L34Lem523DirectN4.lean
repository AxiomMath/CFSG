module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectN3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise
open CFSG.Quasithin.H13.Direct523Semi CFSG.Quasithin.H13.Direct523Count
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL)

variable {G : Type} [Group G] [Finite G] {T M L V H B D D₃ Z₁ : Subgroup G} {n : ℕ}

@[expose] def rhoFamily {L N : Subgroup G} {m : ℕ} (D : NatL2Data L N m) (U' : Subgroup G) :
    Set ((Fin 2 → D.K) ≃+ (Fin 2 → D.K)) :=
  {B | ∃ u ∈ U', ∃ hu : u ∈ Subgroup.normalizer (N : Set G), B = D.conj ⟨u, hu⟩}

theorem uB_zero {K : Type} [Field K] : uB (0 : K) = AddEquiv.refl _ := by
  refine AddEquiv.ext fun w => ?_
  funext i
  fin_cases i <;> simp [uB_apply]

theorem exists_sq_ne {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    ∃ x : K, x ^ 2 ≠ x := by
  by_contra h
  push_neg at h
  have hsub : (Set.univ : Set K) ⊆ ({0, 1} : Set K) := by
    intro x _
    have hx : x * (x - 1) = 0 := by linear_combination h x
    rcases mul_eq_zero.1 hx with h0 | h1
    · simp [h0]
    · simp [sub_eq_zero.1 h1]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ, hK] at h1
  have h2 : ({0, 1} : Set K).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  omega

theorem exists_ne_ne {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) (c : K) :
    ∃ β : K, β ≠ 0 ∧ β ≠ c := by
  by_contra h
  push_neg at h
  have hsub : (Set.univ : Set K) ⊆ ({0, c} : Set K) := by
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · simp [h x hx]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ, hK] at h1
  have h2 : ({0, c} : Set K).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  omega

theorem U_action_list (s : Setup521 G T M L V H B D D₃ Z₁ n) (h5114 : Stmt5_1_14_first)
    (hF : L2TorusFact)
    (hU : ¬ IsMulCommutative ↥(Ugrp Z₁ D₃))
    {N : Subgroup G} (D : NatL2Data L N 2) {z : G} (hz : z ∈ Z₁) (hz1 : z ≠ 1) (hzN : z ∈ N)
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hroot : D.SylowAdapted (T ⊓ L))
    (hV2 : ∀ v ∈ conjClosure Z₁ D₃, ∃ hv : v ∈ N, ∃ μ : D.K, μ ^ 4 = μ ∧
      coordN D v hv = μ • coordN D z hzN) :
    ∃ a₀ : D.K, a₀ ≠ 0 ∧ coordN D z hzN = a₀ • Direct523Semi.e₁ ∧
    ∃ (uA : G) (huA : uA ∈ Ugrp Z₁ D₃) (huAN : uA ∈ Subgroup.normalizer (N : Set G))
      (σA : D.K ≃+* D.K), IsSemi (D.conj ⟨uA, huAN⟩) σA ∧ (∀ x, σA x = x ^ 2) ∧
    ∃ c : D.K, c ≠ 0 ∧
      (∀ β : D.K, (uB β).trans (D.conj ⟨uA, huAN⟩) = (D.conj ⟨uA, huAN⟩).trans (uB β) →
        β = 0 ∨ β = c) ∧
      ∀ u ∈ Ugrp Z₁ D₃, ∀ hu : u ∈ Subgroup.normalizer (N : Set G),
        D.conj ⟨u, hu⟩ = uB 0 ∨ D.conj ⟨u, hu⟩ = uB c ∨
          D.conj ⟨u, hu⟩ = (D.conj ⟨uA, huAN⟩).trans (uB 0) ∨
          D.conj ⟨u, hu⟩ = (D.conj ⟨uA, huAN⟩).trans (uB c) := by
  obtain ⟨a₀, ha₀, hwa⟩ := coord_z_eq s D hroot hTN hz hz1 hzN
  obtain ⟨uA, huA, huAN, σA, hσA, hσA_ne⟩ :=
    exists_frob_semilinear s h5114 hF hU D hz hzN hTN hV2
  have hK : Nat.card D.K = 4 := by rw [D.card]; norm_num
  haveI : CharP D.K 2 :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card D.card
  have hσA2 : ∀ x, σA x = x ^ 2 := (semi_aut_cases hK σA).resolve_left hσA_ne
  have huL : ∀ u ∈ T, u ∈ Subgroup.normalizer (L : Set G) := fun u hu =>
    (s.hyp.hyp.toHyp5_0_1.T_le.trans s.hyp.hyp.toHyp5_0_1.normal) hu
  have hfix : ∀ B ∈ rhoFamily D (Ugrp Z₁ D₃), B (a₀ • Direct523Semi.e₁) = a₀ • Direct523Semi.e₁ := by
    intro B hB
    obtain ⟨u, hu, hun, rfl⟩ := hB
    rw [← hwa]
    exact conj_fix_of_centralizes D hun (Subgroup.mem_centralizer_iff.mp (s.U_le_G₁ hu) z hz).symm
  have hinv : ∀ B ∈ rhoFamily D (Ugrp Z₁ D₃), ∀ w, B (B w) = w := by
    intro B hB w
    obtain ⟨u, hu, hun, rfl⟩ := hB
    rw [← NatL2Data.conj_mul]
    have hsq : u * u ∈ Z₁ := by
      rw [← sq]
      exact s.sq_mem_Z₁ h5114 hF hu
    exact conj_Z₁_trivial s h5114 hF D hz hz1 hzN hsq (hc' := mul_mem hun hun) w
  have hsemi : ∀ B ∈ rhoFamily D (Ugrp Z₁ D₃), ∃ σ : D.K ≃+* D.K, IsSemi B σ := by
    intro B hB
    obtain ⟨u, hu, hun, rfl⟩ := hB
    obtain ⟨σ, hσ⟩ := D.exists_semilinear ⟨u, hun⟩ (huL u (Ugrp_le_T s h5114 hF hu))
    exact ⟨σ, hσ⟩
  have hcomp : ∀ B ∈ rhoFamily D (Ugrp Z₁ D₃), ∀ C ∈ rhoFamily D (Ugrp Z₁ D₃),
      B.trans C ∈ rhoFamily D (Ugrp Z₁ D₃) := by
    intro B hB C hC
    obtain ⟨u, hu, hun, rfl⟩ := hB
    obtain ⟨v, hv, hvn, rfl⟩ := hC
    exact ⟨v * u, mul_mem hv hu, mul_mem hvn hun, (conj_mul_eq D hvn hun).symm⟩
  have hcomm : ∀ B ∈ rhoFamily D (Ugrp Z₁ D₃), ∀ C ∈ rhoFamily D (Ugrp Z₁ D₃),
      B.trans C = C.trans B := by
    intro B hB C hC
    obtain ⟨u, hu, hun, rfl⟩ := hB
    obtain ⟨v, hv, hvn, rfl⟩ := hC
    have hc : u⁻¹ * v⁻¹ * u * v ∈ Z₁ := s.comm_mem_Z₁ h5114 hF hu hv
    have hcN : u⁻¹ * v⁻¹ * u * v ∈ Subgroup.normalizer (N : Set G) :=
      mul_mem (mul_mem (mul_mem (inv_mem hun) (inv_mem hvn)) hun) hvn
    have hW : u * v = (v * u) * (u⁻¹ * v⁻¹ * u * v) := by group
    have e1 : D.conj ⟨u * v, mul_mem hun hvn⟩ = D.conj ⟨v * u, mul_mem hvn hun⟩ := by
      have h1 : D.conj ⟨u * v, mul_mem hun hvn⟩ =
          D.conj ⟨(v * u) * (u⁻¹ * v⁻¹ * u * v), mul_mem (mul_mem hvn hun) hcN⟩ :=
        congrArg D.conj (Subtype.ext hW)
      rw [h1, conj_mul_eq D (mul_mem hvn hun) hcN]
      refine AddEquiv.ext fun w => ?_
      rw [AddEquiv.trans_apply, conj_Z₁_trivial s h5114 hF D hz hz1 hzN hc (hc' := hcN) w]
    rw [← conj_mul_eq D hvn hun, ← conj_mul_eq D hun hvn]
    exact e1.symm
  have hA : D.conj ⟨uA, huAN⟩ ∈ rhoFamily D (Ugrp Z₁ D₃) := ⟨uA, huA, huAN, rfl⟩
  obtain ⟨c, hc0, hcomm_iff, hlist⟩ :=
    count_le_four hK ha₀ (rhoFamily D (Ugrp Z₁ D₃)) hfix hinv hsemi hcomp hcomm hA hσA hσA2
  exact ⟨a₀, ha₀, hwa, uA, huA, huAN, σA, hσA, hσA2, c, hc0, hcomm_iff,
    fun u hu hun => hlist _ ⟨u, hu, hun, rfl⟩⟩

end CFSG.Quasithin.H13
