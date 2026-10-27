module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectN4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise
open CFSG.Quasithin.H13.Direct523Semi CFSG.Quasithin.H13.Direct523Count
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL)

variable {G : Type} [Group G] [Finite G] {T M L V H B D D₃ Z₁ : Subgroup G} {n : ℕ}

theorem conj_invol (s : Setup521 G T M L V H B D D₃ Z₁ n) (h5114 : Stmt5_1_14_first)
    (hF : L2TorusFact) {N : Subgroup G} {m : ℕ} (D : NatL2Data L N m) {z : G} (hz : z ∈ Z₁)
    (hz1 : z ≠ 1) (hzN : z ∈ N) {u : G} (hu : u ∈ Ugrp Z₁ D₃)
    (hun : u ∈ Subgroup.normalizer (N : Set G)) (w : Fin 2 → D.K) :
    D.conj ⟨u, hun⟩ (D.conj ⟨u, hun⟩ w) = w := by
  rw [← NatL2Data.conj_mul]
  have hsq : u * u ∈ Z₁ := by
    rw [← sq]
    exact s.sq_mem_Z₁ h5114 hF hu
  exact conj_Z₁_trivial s h5114 hF D hz hz1 hzN hsq (hc' := mul_mem hun hun) w

theorem Ugrp_has_uB (s : Setup521 G T M L V H B D D₃ Z₁ n) (h5114 : Stmt5_1_14_first)
    (hF : L2TorusFact)
    (hU : ¬ IsMulCommutative ↥(Ugrp Z₁ D₃))
    {N : Subgroup G} (D : NatL2Data L N 2) {z : G} (hz : z ∈ Z₁) (hz1 : z ≠ 1) (hzN : z ∈ N)
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hroot : D.SylowAdapted (T ⊓ L))
    (hV2 : ∀ v ∈ conjClosure Z₁ D₃, ∃ hv : v ∈ N, ∃ μ : D.K, μ ^ 4 = μ ∧
      coordN D v hv = μ • coordN D z hzN) :
    ∃ c : D.K, c ≠ 0 ∧ ∃ u₁ ∈ Ugrp Z₁ D₃, ∃ hu₁ : u₁ ∈ Subgroup.normalizer (N : Set G),
      D.conj ⟨u₁, hu₁⟩ = uB c := by
  obtain ⟨a₀, ha₀, hwa, uA, huA, huAN, σA, hσA, hσA2, c, hc0, hcomm_iff, hlist⟩ :=
    U_action_list s h5114 hF hU D hz hz1 hzN hTN hroot hV2
  refine ⟨c, hc0, ?_⟩
  by_contra hcon
  push Not at hcon
  have hK : Nat.card D.K = 4 := by rw [D.card]; norm_num
  haveI : CharP D.K 2 :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card D.card
  have hAinv : ∀ w, D.conj ⟨uA, huAN⟩ (D.conj ⟨uA, huAN⟩ w) = w :=
    fun w => conj_invol s h5114 hF D hz hz1 hzN huA huAN w
  have hstep : ∀ u ∈ Ugrp Z₁ D₃, ∀ hu : u ∈ Subgroup.normalizer (N : Set G),
      D.conj ⟨u, hu⟩ = uB 0 ∨ D.conj ⟨u, hu⟩ = (D.conj ⟨uA, huAN⟩).trans (uB 0) := by
    intro u hu hun
    rcases hlist u hu hun with h | h | h | h
    · exact Or.inl h
    · exact absurd h (hcon u hu hun)
    · exact Or.inr h
    · exfalso
      have hmul : u * uA ∈ Ugrp Z₁ D₃ := mul_mem hu huA
      have e : D.conj ⟨u * uA, mul_mem hun huAN⟩ =
          (D.conj ⟨uA, huAN⟩).trans (D.conj ⟨u, hun⟩) := conj_mul_eq D hun huAN
      have hX : (D.conj ⟨uA, huAN⟩).trans (D.conj ⟨u, hun⟩) = uB c := by
        rw [h]
        refine AddEquiv.ext fun w => ?_
        simp only [AddEquiv.trans_apply]
        rw [hAinv]
      exact hcon (u * uA) hmul (mul_mem hun huAN) (e.trans hX)
  obtain ⟨β, hβ0, hβc⟩ := exists_ne_ne hK c
  unfold NatL2Data.SylowAdapted at hroot
  obtain ⟨-, h2⟩ := hroot
  obtain ⟨g, hgL, hgS, hg⟩ := h2 β
  have hgT : g ∈ T := (inf_le_left : T ⊓ L ≤ T) hgS
  have hgN : g ∈ Subgroup.normalizer (N : Set G) := hTN hgT
  have hgU : g * uA * g⁻¹ ∈ Ugrp Z₁ D₃ :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.Quasithin.le_normalizer_conjClosure (conjClosure Z₁ D₃)
        (Subgroup.centralizer (Z₁ : Set G)) (T_le_centralizer_Z₁ s hgT)) uA).mp huA
  have hu'N : g * uA * g⁻¹ ∈ Subgroup.normalizer (N : Set G) :=
    mul_mem (mul_mem hgN huAN) (inv_mem hgN)
  have hrel : (D.conj ⟨g, hgN⟩).trans (D.conj ⟨g * uA * g⁻¹, hu'N⟩) =
      (D.conj ⟨uA, huAN⟩).trans (D.conj ⟨g, hgN⟩) := by
    have key : D.conj ⟨g * uA, mul_mem hgN huAN⟩ =
        D.conj ⟨g * uA * g⁻¹ * g, mul_mem hu'N hgN⟩ :=
      congrArg D.conj (Subtype.ext (by group))
    rw [conj_mul_eq D hgN huAN, conj_mul_eq D hu'N hgN] at key
    exact key.symm
  have hρ : D.conj ⟨g, hgN⟩ = uB β :=
    AddEquiv.ext fun w => by
      rw [← unipSL_mulVec]
      exact hg w
  rcases hstep (g * uA * g⁻¹) hgU hu'N with hB0 | hB1
  ·
    rw [hB0] at hrel
    have hAid : D.conj ⟨uA, huAN⟩ = AddEquiv.refl _ := by
      refine AddEquiv.ext fun w => ?_
      have h := congrArg (fun F : (Fin 2 → D.K) ≃+ (Fin 2 → D.K) => F w) hrel
      simp only [AddEquiv.trans_apply, uB_zero, AddEquiv.refl_apply] at h
      exact ((D.conj ⟨g, hgN⟩).injective h).symm
    obtain ⟨x, hx⟩ := exists_sq_ne hK
    have hσrefl := sigma_eq_refl_of_id hσA hAid
    apply hx
    rw [← hσA2 x, hσrefl]
    rfl
  ·
    have hA' : (D.conj ⟨uA, huAN⟩).trans (uB 0) = D.conj ⟨uA, huAN⟩ :=
      AddEquiv.ext fun w => by
        simp only [AddEquiv.trans_apply, uB_zero, AddEquiv.refl_apply]
    rw [hB1, hA', hρ] at hrel
    rcases hcomm_iff β hrel with h | h
    · exact hβ0 h
    · exact hβc h

end CFSG.Quasithin.H13
