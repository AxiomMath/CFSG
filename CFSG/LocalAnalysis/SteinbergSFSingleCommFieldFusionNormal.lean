module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionDefs

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixFF_ff0 (hK : SixKConclusion φ t i) : FF0Concl φ t i := by
  intro g hg
  have ht : t ∈ Tplus φ t i := by
    have h : t ∈ Tplus φ t i ⊓ centralizer ({t} : Set G) := by
      rw [hK.centralizer_Tplus]
      exact mem_sup_right (mem_zpowers t)
    exact (Subgroup.mem_inf.mp h).1
  have hmem : g⁻¹ * t * g ∈ Tplus φ t i := by
    have h := (mem_normalizer_iff.mp (inv_mem hg) t).mp ht
    rwa [inv_inv] at h
  obtain ⟨s, hs, hconj⟩ := hK.slice g hmem
  refine ⟨s, hs, ?_⟩
  have h1 : t * g = g * (s⁻¹ * t * s) := by
    rw [← hconj]
    group
  have h2 : t * (g * s⁻¹) = g * s⁻¹ * t := by
    calc t * (g * s⁻¹) = (t * g) * s⁻¹ := by group
      _ = (g * (s⁻¹ * t * s)) * s⁻¹ := by rw [h1]
      _ = g * s⁻¹ * t := by group
  exact mem_centralizer_singleton_iff.mpr h2.symm

theorem sixFF_ff1_aux_mem_normalizer {A : Subgroup G} {y : G}
    (h : ∀ x ∈ A, y * x * y⁻¹ ∈ A) (h' : ∀ x ∈ A, y⁻¹ * x * y⁻¹⁻¹ ∈ A) :
    y ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  intro n
  refine ⟨fun hn => h n hn, fun hn => ?_⟩
  have h2 := h' (y * n * y⁻¹) hn
  have e : y⁻¹ * (y * n * y⁻¹) * y⁻¹⁻¹ = n := by group
  rw [e] at h2
  exact h2

theorem sixFF_ff1_aux_conj_mem {Tp : Subgroup G} {y x : G} (hy : y ∈ normalizer (Tp : Set G))
    (hyC : y ∈ centralizer ({t} : Set G)) (hx : x ∈ Tp ⊓ centralizer ({t} : Set G)) :
    y * x * y⁻¹ ∈ Tp ⊓ centralizer ({t} : Set G) :=
  Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp hy x).mp (Subgroup.mem_inf.mp hx).1,
    mul_mem (mul_mem hyC (Subgroup.mem_inf.mp hx).2) (inv_mem hyC)⟩

theorem sixFF_ff1_aux_inf (hS : SCSetting L K n φ t i) (hK : SixKConclusion φ t i) :
    (P φ ⊔ zpowers t) ⊓ L = P φ := by
  have hPL : P φ ≤ L := pull_le φ (antiUnipotent K)
  have hPC : P φ ≤ centralizer ({t} : Set G) := by
    rw [← hK.centralizer_S]
    exact inf_le_right
  have ht2 : t ^ 2 = 1 := by
    rw [sq]
    exact hS.fc.setup.t_mul_t
  have htL : t ∉ L := hS.fc.setup.t_not_mem_L
  have hcomm : ∀ a ∈ P φ, a * t = t * a := fun a ha => mem_centralizer_singleton_iff.mp (hPC ha)
  apply le_antisymm
  · rw [sup_comm]
    exact FieldInvolution.sup_zpowers_inf_le ht2 hPL htL hcomm
  · exact le_inf le_sup_left hPL

theorem sixFF_ff1_aux_normalizer_Q (hK : SixKConclusion φ t i) {y : G}
    (hy : y ∈ normalizer (Tplus φ t i : Set G)) (hyC : y ∈ centralizer ({t} : Set G)) :
    y ∈ normalizer ((P φ ⊔ zpowers t : Subgroup G) : Set G) := by
  rw [← hK.centralizer_Tplus]
  exact sixFF_ff1_aux_mem_normalizer
    (fun x hx => sixFF_ff1_aux_conj_mem hy hyC hx)
    (fun x hx => sixFF_ff1_aux_conj_mem (inv_mem hy) (inv_mem hyC) hx)

theorem sixFF_ff1_aux_P_forward (hS : SCSetting L K n φ t i) (hK : SixKConclusion φ t i) {y : G}
    (hy : y ∈ normalizer (Tplus φ t i : Set G)) (hyC : y ∈ centralizer ({t} : Set G)) :
    ∀ x ∈ P φ, y * x * y⁻¹ ∈ P φ := by
  intro x hx
  have hL : y ∈ normalizer (L : Set G) := hS.fc.setup.cent_le hyC
  have h1 : y * x * y⁻¹ ∈ (P φ ⊔ zpowers t) ⊓ L :=
    Subgroup.mem_inf.mpr
      ⟨(mem_normalizer_iff.mp (sixFF_ff1_aux_normalizer_Q hK hy hyC) x).mp (mem_sup_left hx),
        (mem_normalizer_iff.mp hL x).mp (pull_le φ (antiUnipotent K) hx)⟩
  rw [sixFF_ff1_aux_inf hS hK] at h1
  exact h1

theorem sixFF_ff1_aux_U_forward (hH : SixHConclusion φ t i) {y : G}
    (hy : y ∈ normalizer (Tplus φ t i : Set G)) : ∀ x ∈ U φ i, y * x * y⁻¹ ∈ U φ i := by
  intro x hx
  rw [← hH.center_Tplus] at hx ⊢
  exact GomiFusion.Setup.conj_mem_center hy hx

theorem sixFF_ff1_aux_inf_U : U φ Axis.one ⊓ U φ Axis.two = ⊥ := by
  show pull φ (rootU K Axis.one) ⊓ pull φ (rootU K Axis.two) = ⊥
  rw [← pull_inf, FullCenter.rootU_inf, pull_bot]

theorem sixFF_ff1_aux_U_ne_bot (k : Axis) : U φ k ≠ ⊥ := by
  intro h
  have h1 : Nat.card (U φ k) = Nat.card K := by
    rw [card_pull, FullCenter.card_rootU]
  rw [h, Subgroup.card_bot] at h1
  have h2 : 1 < Nat.card K := Finite.one_lt_card
  omega

theorem sixFF_ff1_aux_forward (hS : SCSetting L K n φ t i) (hK : SixKConclusion φ t i) {y : G}
    (hy : y ∈ normalizer (Tplus φ t i : Set G)) (hyC : y ∈ centralizer ({t} : Set G))
    (k : Axis) (hU : ∀ x ∈ U φ k, y * x * y⁻¹ ∈ U φ k) :
    ∀ x ∈ U φ k.swap, y * x * y⁻¹ ∈ U φ k.swap := by
  have hconj := hS.fc.conj_axis y (sixFF_ff1_aux_normalizer_Q hK hy hyC)
  cases k with
  | one =>
    rcases hconj with ⟨-, hA⟩ | ⟨hB, -⟩
    · exact hA
    · exfalso
      have hbot : U φ Axis.one = ⊥ := by
        rw [eq_bot_iff_forall]
        intro x hx
        have h3 : y * x * y⁻¹ ∈ U φ Axis.one ⊓ U φ Axis.two :=
          Subgroup.mem_inf.mpr ⟨hU x hx, hB x hx⟩
        rw [sixFF_ff1_aux_inf_U, Subgroup.mem_bot] at h3
        calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
          _ = 1 := by rw [h3]; group
      exact sixFF_ff1_aux_U_ne_bot Axis.one hbot
  | two =>
    rcases hconj with ⟨hA, -⟩ | ⟨-, hB⟩
    · exact hA
    · exfalso
      have hbot : U φ Axis.two = ⊥ := by
        rw [eq_bot_iff_forall]
        intro x hx
        have h3 : y * x * y⁻¹ ∈ U φ Axis.two ⊓ U φ Axis.one :=
          Subgroup.mem_inf.mpr ⟨hU x hx, hB x hx⟩
        rw [inf_comm, sixFF_ff1_aux_inf_U, Subgroup.mem_bot] at h3
        calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
          _ = 1 := by rw [h3]; group
      exact sixFF_ff1_aux_U_ne_bot Axis.two hbot

theorem sixFF_ff1 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hK : SixKConclusion φ t i) : FF1Concl φ t i := by
  intro y hy hyC
  have hP : y ∈ normalizer (P φ : Set G) :=
    sixFF_ff1_aux_mem_normalizer (sixFF_ff1_aux_P_forward hS hK hy hyC)
      (sixFF_ff1_aux_P_forward hS hK (inv_mem hy) (inv_mem hyC))
  have hUi : y ∈ normalizer (U φ i : Set G) :=
    sixFF_ff1_aux_mem_normalizer (sixFF_ff1_aux_U_forward hH hy)
      (sixFF_ff1_aux_U_forward hH (inv_mem hy))
  have hUj : y ∈ normalizer (U φ i.swap : Set G) :=
    sixFF_ff1_aux_mem_normalizer
      (sixFF_ff1_aux_forward hS hK hy hyC i (sixFF_ff1_aux_U_forward hH hy))
      (sixFF_ff1_aux_forward hS hK (inv_mem hy) (inv_mem hyC) i
        (sixFF_ff1_aux_U_forward hH (inv_mem hy)))
  exact ⟨hP, hUi, hUj⟩

theorem sixFF_ff2_aux_iff {S : Subgroup (antiSp K)} (y : normalizer (L : Set G))
    (hy : (y : G) ∈ normalizer ((pull φ S : Subgroup G) : Set G)) (x : antiSp K) :
    FieldInvolution.transAct φ y x ∈ S ↔ x ∈ S := by
  calc FieldInvolution.transAct φ y x ∈ S
      ↔ ((φ.symm (FieldInvolution.transAct φ y x) : L) : G) ∈ pull φ S := symm_mem_pull.symm
    _ ↔ ((φ.symm x : L) : G) ∈ pull φ S := by
        rw [FieldInvolution.coe_symm_transAct]
        exact (mem_normalizer_iff.mp hy _).symm
    _ ↔ x ∈ S := symm_mem_pull

theorem sixFF_ff2_aux_dSp_mem (r s : Kˣ) :
    CFSG.QuasithinUnique.Fin257.Sp4.dSp r s ∈ diagTorus K :=
  ⟨((r⁻¹ : Kˣ) : K), ((s⁻¹ : Kˣ) : K), Units.ne_zero _, Units.ne_zero _, by
    rw [CFSG.QuasithinUnique.Fin257.Sp4.glMat_dSp]
    simp [CFSG.QuasithinUnique.Fin257.Sp4.dSpMat, diagMat]⟩

theorem sixFF_ff2 (hS : SCSetting L K n φ t i) : FF2Concl n φ t i := by
  intro y _hyC hyP hyUi hyUj
  have hn : 2 ≤ n := hS.fc.setup.two_le
  have hK : Nat.card K = 2 ^ n := hS.fc.setup.card_K
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hn)
  have hyU2 : (y : G) ∈ normalizer ((pull φ (rootU K Axis.two) : Subgroup G) : Set G) := by
    cases i
    · exact hyUj
    · exact hyUi
  have hstab : FieldInvolution.transAct φ y ∈ autStab (rootU K Axis.two) :=
    mem_autStab.mpr fun x => sixFF_ff2_aux_iff y hyU2 x
  have hA : ∀ x, FieldInvolution.transAct φ y x ∈ radA2 K ↔ x ∈ radA2 K :=
    mem_autStab.mp (autStab_le_autStab_of_structure (rootAxisStructure_two hK4) hstab)
  have hU : ∀ x ∈ antiUnipotent K, FieldInvolution.transAct φ y x ∈ antiUnipotent K :=
    fun x hx => (sixFF_ff2_aux_iff y hyP x).mpr hx
  obtain ⟨p, hp, r, s, k, hk, hα⟩ :=
    FieldInvolution.exists_conj_mul_dSp_frobAut_pow hn hK (FieldInvolution.transAct φ y) hA hU
  exact ⟨p, hp, CFSG.QuasithinUnique.Fin257.Sp4.dSp r s, sixFF_ff2_aux_dSp_mem r s, k, hk, hα⟩

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
