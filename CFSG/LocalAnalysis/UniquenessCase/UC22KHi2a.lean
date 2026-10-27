module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xn
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22se

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x P22s

variable {G : Type} [Group G] [Finite G]

namespace P22k2

@[expose] def T1 (D : Data G) (Y : Subgroup (MBar D.M D.U)) : Subgroup G :=
  D.T ⊓ normalizer (preN D Y : Set G)

theorem T1_le_T (D : Data G) (Y : Subgroup (MBar D.M D.U)) : T1 D Y ≤ D.T := inf_le_left

theorem T1_le_M (D : Data G) (Y : Subgroup (MBar D.M D.U)) : T1 D Y ≤ D.M :=
  inf_le_left.trans D.sylowM.le

theorem isPGroup_T1 (D : Data G) (Y : Subgroup (MBar D.M D.U)) : IsPGroup 2 ↥(T1 D Y) :=
  D.sylowM.isPGroup.to_le inf_le_left

theorem T1_le_normalizer_preN (D : Data G) (Y : Subgroup (MBar D.M D.U)) :
    T1 D Y ≤ normalizer (preN D Y : Set G) := inf_le_right

theorem mem_normalizer_preN (D : Data G) {Y : Subgroup (MBar D.M D.U)} {x : G} (hx : x ∈ D.M)
    (hxY : (QuotientGroup.mk ⟨x, hx⟩ : MBar D.M D.U) ∈ normalizer (Y : Set (MBar D.M D.U))) :
    x ∈ normalizer (preN D Y : Set G) :=
  mem_normalizer_inf (uc22p22t_M_le_normalizer_jOf D hx) (mem_normalizer_preMbar D hx hxY)

theorem T1_conj_mem (D : Data G) {Y : Subgroup (MBar D.M D.U)} (hY : Y ≤ mbarImage D.M D.U (proofN D)) {x : G}
    (hx : x ∈ T1 D Y) {y : MBar D.M D.U} (hy : y ∈ Y) :
    (QuotientGroup.mk ⟨x, T1_le_M D Y hx⟩ : MBar D.M D.U) * y *
      (QuotientGroup.mk ⟨x, T1_le_M D Y hx⟩ : MBar D.M D.U)⁻¹ ∈ Y := by
  have hy' : y ∈ mbarImage D.M D.U (preN D Y) := by rw [mbarImage_preN D hY]; exact hy
  obtain ⟨n, hn, rfl⟩ := hy'
  have hnN : (n : G) ∈ preN D Y := hn
  have hxM := T1_le_M D Y hx
  have hcN : x * (n : G) * x⁻¹ ∈ preN D Y := (Subgroup.mem_normalizer_iff.1 hx.2 _).1 hnN
  have hcM : x * (n : G) * x⁻¹ ∈ D.M := D.M.mul_mem (D.M.mul_mem hxM n.2) (D.M.inv_mem hxM)
  have hmem : (QuotientGroup.mk ⟨x * (n : G) * x⁻¹, hcM⟩ : MBar D.M D.U) ∈ mbarImage D.M D.U (preN D Y) :=
    ⟨⟨_, hcM⟩, hcN, rfl⟩
  rw [mbarImage_preN D hY] at hmem
  convert hmem using 1
  change _ = QuotientGroup.mk ((⟨x, hxM⟩ : ↥D.M) * n * (⟨x, hxM⟩ : ↥D.M)⁻¹)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rfl

theorem T1_le_normalizer_preMbar (D : Data G) {Y : Subgroup (MBar D.M D.U)}
    (hY : Y ≤ mbarImage D.M D.U (proofN D)) : T1 D Y ≤ normalizer (preMbar D Y : Set G) := by
  intro x hx
  refine mem_normalizer_preMbar D (T1_le_M D Y hx) ?_
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => T1_conj_mem D hY hx hz, fun hz => ?_⟩
  have h := T1_conj_mem D hY (inv_mem hx) hz
  have e : (QuotientGroup.mk ⟨x⁻¹, T1_le_M D Y (inv_mem hx)⟩ : MBar D.M D.U) =
      (QuotientGroup.mk ⟨x, T1_le_M D Y hx⟩ : MBar D.M D.U)⁻¹ := rfl
  rw [e, inv_inv] at h
  simpa [mul_assoc] using h

theorem pCoreOf_le_T1 (D : Data G) (Y : Subgroup (MBar D.M D.U)) : pCoreOf 2 D.M ≤ T1 D Y := by
  have hU := (uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).1
  refine le_inf (uc22p22e_pCoreOf_le_T D) fun q hq => ?_
  have hqM : q ∈ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M hq
  have hqC : q ∈ centralizer (D.U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.1 (hU hu).2 q hq).symm
  have h1 : (QuotientGroup.mk ⟨q, hqM⟩ : MBar D.M D.U) = 1 :=
    (uc22br_gt_mk_eq_one_iff (uc22p22xf_hV D) ⟨q, hqM⟩).2 hqC
  exact mem_normalizer_preN D hqM (by rw [h1]; exact Subgroup.one_mem _)

theorem T_le_normalizer_proofS (D : Data G) : D.T ≤ normalizer (proofS D : Set G) :=
  fun t ht => mem_normalizer_inf' (Subgroup.le_normalizer ht)
    (mem_normalizer_centralizer (uc22p22se_T_le_normalizer_proofE D ht))

theorem T1_le_normalizer_proofS (D : Data G) (Y : Subgroup (MBar D.M D.U)) :
    T1 D Y ≤ normalizer (proofS D : Set G) := (T1_le_T D Y).trans (T_le_normalizer_proofS D)

theorem proofS_le_T1 (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U))
    (hNb : NbarSplit D Nb) (i : Fin m) : proofS D ≤ T1 D (Nb i) :=
  le_inf inf_le_left fun s hs => (uc22p22x_S_normalizes D Ch h2 h3 h51 hH c m Nb hNb i hs).2.1

theorem thompsonJ_T1 (D : Data G) {Y : Subgroup (MBar D.M D.U)} (hS : proofS D ≤ T1 D Y) :
    CFSG.Quasithin.thompsonJ (T1 D Y) = CFSG.Quasithin.thompsonJ D.T := by
  refine CFSG.Quasithin.B6.thompsonJ_eq_of_le ?_ (T1_le_T D Y)
  rw [← uc22p22se_jOf_eq]
  exact (jOf_T_le_proofS D).trans hS

theorem omegaOneCenterOf_T1 (D : Data G) {Y : Subgroup (MBar D.M D.U)} (hS : proofS D ≤ T1 D Y) :
    CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ (T1 D Y)) = proofE D := by
  rw [thompsonJ_T1 D hS, uc22p22se_proofE_eq]

theorem baum_T1 (D : Data G) {Y : Subgroup (MBar D.M D.U)} (hS : proofS D ≤ T1 D Y) :
    CFSG.Quasithin.baum (T1 D Y) = proofS D := by
  unfold CFSG.Quasithin.baum
  rw [omegaOneCenterOf_T1 D hS]
  apply le_antisymm
  · exact le_inf ((inf_le_left : T1 D Y ⊓ _ ≤ T1 D Y).trans (T1_le_T D Y)) inf_le_right
  · exact le_inf hS inf_le_right

theorem not_two_dvd_relIndex_sup {S X : Subgroup G} (hSX : S ≤ normalizer (X : Set G))
    (hodd : ¬ 2 ∣ (S ⊓ X).relIndex X) : ¬ 2 ∣ S.relIndex (X ⊔ S) := by
  have hcard := CFSG.LocalAnalysis.EvenBN.Tits.N.card_sup_mul_card_inf' hSX
  have h1 := Subgroup.relIndex_mul_card S (X ⊔ S)
  have h2 := Subgroup.relIndex_mul_card (S ⊓ X) X
  rw [inf_eq_left.2 (le_sup_right : S ≤ X ⊔ S)] at h1
  rw [inf_assoc, inf_idem] at h2
  have hpos1 : 0 < Nat.card S := Nat.card_pos
  have hpos2 : 0 < Nat.card (S ⊓ X : Subgroup G) := Nat.card_pos
  have hrel : S.relIndex (X ⊔ S) = (S ⊓ X).relIndex X := by
    rw [sup_comm] at hcard
    have key : S.relIndex (X ⊔ S) * (Nat.card S * Nat.card (S ⊓ X : Subgroup G)) =
        (S ⊓ X).relIndex X * (Nat.card S * Nat.card (S ⊓ X : Subgroup G)) := by
      calc S.relIndex (X ⊔ S) * (Nat.card S * Nat.card (S ⊓ X : Subgroup G))
          = (S.relIndex (X ⊔ S) * Nat.card S) * Nat.card (S ⊓ X : Subgroup G) := by ring
        _ = Nat.card S * Nat.card X := by rw [h1, hcard]
        _ = (S ⊓ X).relIndex X * (Nat.card S * Nat.card (S ⊓ X : Subgroup G)) := by
            rw [← h2]; ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos1 hpos2) key
  rwa [hrel]

end P22k2

end CFSG.LocalAnalysis.UniquenessCase.UC22
