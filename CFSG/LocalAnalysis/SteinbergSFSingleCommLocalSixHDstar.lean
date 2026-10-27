module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixHSecond

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Concl

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] def H11Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  Mc φ t i ⊓ Kc φ t i.swap = F φ t ⊓ D φ t i.swap ∧
    Mhat φ t i i ⊓ Kc φ t i.swap = F φ t ⊓ D φ t i.swap ∧
    Nat.card (Dstar φ t i) = Nat.card K ^ 8 ∧
    ((Mhat φ t i i).subgroupOf (Dstar φ t i)).Normal ∧
    Dstar φ t i = T₁ φ t i ⊓ S φ t i

@[expose] def H12Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ a ∈ A φ i.swap, a ∉ Z₀ φ → ∀ m ∈ Mhat φ t i i, (a⁻¹ * m⁻¹ * a * m ∈ U φ i ↔ m ∈ Mc φ t i)

@[expose] def H13Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∃ _ : ((U φ i).subgroupOf (Dstar φ t i)).Normal,
    SixG.MNMaximal (Dstar φ t i) (Mhat φ t i i) (Mc φ t i ⊔ Kc φ t i.swap) (Dstar φ t i)
      (U φ i)

@[expose] def H14Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  (center ↥(Mhat φ t i i)).map (Mhat φ t i i).subtype = U φ i

end Concl

section Steps

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

open scoped Pointwise

theorem sixH_h11_K_le_P2 (hS : SCSetting L K n φ t i) :
    Kc φ t i.swap ≤ P₂ φ t i.swap :=
  (sixH_h7_Kj_le hS).trans (SixF.Mhat_le_P₂ hS.fc i)

theorem sixH_h11_K_le_T1 (hS : SCSetting L K n φ t i) :
    Kc φ t i.swap ≤ T₁ φ t i := by
  have hH : ∀ k : Axis, R φ t Axis.one ⊓ R φ t Axis.two ≤ R φ t k := by
    intro k
    cases k
    · exact inf_le_left
    · exact inf_le_right
  have hKR : Kc φ t i.swap ≤ R φ t i :=
    (SixG.K_le_H hS.fc i.swap).trans
      ((le_of_eq (FullCenterParabolic.R_inf_R hS.fc).symm).trans (hH i))
  exact hKR.trans le_sup_left

theorem sixH_h11_Mhat_le_T1 (hS : SCSetting L K n φ t i) :
    Mhat φ t i i ≤ T₁ φ t i :=
  (SixF.Mhat_le_P₁ hS.fc i hS.ne_bot hS.eq_bot).trans le_sup_right

theorem sixH_h11_Mhat_le_S (k : Axis) : Mhat φ t i k ≤ S φ t i := by
  cases k
  · exact le_sup_left
  · exact le_sup_right

theorem sixH_h11_inf_M_K (hS : SCSetting L K n φ t i) :
    Mc φ t i ⊓ Kc φ t i.swap = F φ t ⊓ D φ t i.swap := by
  have hMC := le_of_eq (NextCores.M_inf_C hS.fc i hS.ne_bot hS.eq_bot)
  apply le_antisymm
  · rintro m ⟨hmM, hmK⟩
    have hm' : m ∈ ((A φ i.swap : Subgroup G) : Set G) *
        ((F φ t ⊓ D φ t i.swap : Subgroup G) : Set G) := by
      rw [FullCenterWeyl.K_mul hS.fc i.swap]
      exact hmK
    obtain ⟨a, ha, f, hf, rfl⟩ := Set.mem_mul.mp hm'
    have hf' : f ∈ F φ t ⊓ D φ t i.swap := hf
    have ha' : a ∈ A φ i.swap := ha
    have hfM : f ∈ Mc φ t i :=
      NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot (Subgroup.mem_inf.mp hf').1
    have haM : a ∈ Mc φ t i := by
      have h : a * f * f⁻¹ ∈ Mc φ t i := (Mc φ t i).mul_mem hmM ((Mc φ t i).inv_mem hfM)
      rwa [mul_inv_cancel_right] at h
    have haZ := hMC (Subgroup.mem_inf.mpr ⟨haM, FullCenterWeyl.A_le_C hS.fc i.swap ha'⟩)
    exact mul_mem (FullCenterTorus.ZP_le_Fi hS.fc i.swap haZ) hf'
  · intro m hm
    have hmF : m ∈ Mc φ t i :=
      NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot (Subgroup.mem_inf.mp hm).1
    exact Subgroup.mem_inf.mpr
      ⟨hmF, (le_sup_right : F φ t ⊓ D φ t i.swap ≤ Kc φ t i.swap) hm⟩

theorem sixH_h11_inf_Mhat_K (hS : SCSetting L K n φ t i) (h8 : H8Concl φ t i) :
    Mhat φ t i i ⊓ Kc φ t i.swap = F φ t ⊓ D φ t i.swap := by
  obtain ⟨h81, -⟩ := h8
  apply le_antisymm
  · have h1 : Mhat φ t i i ⊓ Kc φ t i.swap ≤ Mhat φ t i i ⊓ P₂ φ t i.swap :=
      le_inf inf_le_left (inf_le_right.trans (sixH_h11_K_le_P2 hS))
    have hMc : Mhat φ t i i ⊓ Kc φ t i.swap ≤ Mc φ t i := h1.trans (le_of_eq h81)
    exact (le_inf hMc inf_le_right).trans_eq (sixH_h11_inf_M_K hS)
  · intro m hm
    have hmF : m ∈ Mc φ t i :=
      NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot (Subgroup.mem_inf.mp hm).1
    exact Subgroup.mem_inf.mpr
      ⟨(le_sup_left : Mc φ t i ≤ Mhat φ t i i) hmF,
        (le_sup_right : F φ t ⊓ D φ t i.swap ≤ Kc φ t i.swap) hm⟩

theorem sixH_h11_card_Dstar (hS : SCSetting L K n φ t i)
    (hN : Kc φ t i.swap ≤ normalizer (Mhat φ t i i : Set G))
    (hinf : Mhat φ t i i ⊓ Kc φ t i.swap = F φ t ⊓ D φ t i.swap) :
    Nat.card (Dstar φ t i) = Nat.card K ^ 8 := by
  have hc : Nat.card (Dstar φ t i) * Nat.card (Mhat φ t i i ⊓ Kc φ t i.swap : Subgroup G) =
      Nat.card (Mhat φ t i i) * Nat.card (Kc φ t i.swap) :=
    CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hN
  rw [hinf, FullCenterTorus.card_Fi hS.fc i.swap, SixF.card_Mhat hS.fc i hS.ne_bot hS.eq_bot,
    FullCenterWeyl.card_K hS.fc i.swap] at hc
  have hq : 0 < Nat.card K ^ 3 := pow_pos Nat.card_pos 3
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [hc]
  ring

theorem sixH_h11_normal (hN : Dstar φ t i ≤ normalizer (Mhat φ t i i : Set G)) :
    ((Mhat φ t i i).subgroupOf (Dstar φ t i)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (le_sup_left : Mhat φ t i i ≤ Dstar φ t i)).mpr hN

theorem sixH_h11_eq_inf (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h8 : H8Concl φ t i) (hcard : Nat.card (Dstar φ t i) = Nat.card K ^ 8) :
    Dstar φ t i = T₁ φ t i ⊓ S φ t i := by
  obtain ⟨-, -, hcS, hsup, -, hnS⟩ := h8
  have hDT1 : Dstar φ t i ≤ T₁ φ t i :=
    sup_le (sixH_h11_Mhat_le_T1 hS) (sixH_h11_K_le_T1 hS)
  have hDS : Dstar φ t i ≤ S φ t i :=
    sup_le (sixH_h11_Mhat_le_S i) ((sixH_h7_Kj_le hS).trans (sixH_h11_Mhat_le_S i.swap))
  have hSTp : S φ t i ≤ Tplus φ t i :=
    le_trans (le_sup_left : S φ t i ≤ S φ t i ⊔ zpowers t) (le_of_eq hsup)
  have hTbar : T₁ φ t i ≤ Tbar φ t i := le_sup_left
  have hTp : T₁ φ t i ≤ Tplus φ t i := le_trans hTbar le_sup_left
  have hzR : zpowers t ≤ R φ t i :=
    le_trans (le_sup_right : zpowers t ≤ P φ ⊔ zpowers t) le_sup_left
  have hzT1 : zpowers t ≤ T₁ φ t i := le_trans hzR le_sup_left
  have hNS : Tplus φ t i ≤ normalizer (S φ t i : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSTp).mp hnS
  have hT1N : T₁ φ t i ≤ normalizer (S φ t i : Set G) := hTp.trans hNS
  have hc1 : Nat.card (S φ t i ⊔ T₁ φ t i : Subgroup G) *
      Nat.card (S φ t i ⊓ T₁ φ t i : Subgroup G) =
        Nat.card (S φ t i) * Nat.card (T₁ φ t i : Subgroup G) :=
    CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hT1N
  have hge : Tplus φ t i ≤ S φ t i ⊔ T₁ φ t i := by
    rw [← hsup]
    exact sup_le le_sup_left (le_trans hzT1 le_sup_right)
  have hSup : S φ t i ⊔ T₁ φ t i = Tplus φ t i := le_antisymm (sup_le hSTp hTp) hge
  rw [hSup, SixG.card_Tplus hS.fc i hS.ne_bot hS.eq_bot hM2, hcS,
    NextCores.card_T₁ hS.fc i hS.ne_bot hS.eq_bot] at hc1
  have hq : 0 < 2 * Nat.card K ^ 10 := mul_pos two_pos (pow_pos Nat.card_pos 10)
  have hSI : Nat.card (S φ t i ⊓ T₁ φ t i : Subgroup G) = Nat.card K ^ 8 := by
    apply Nat.eq_of_mul_eq_mul_left hq
    rw [hc1]
    ring
  have hcard' : Nat.card (T₁ φ t i ⊓ S φ t i : Subgroup G) ≤ Nat.card (Dstar φ t i) :=
    le_of_eq (by rw [inf_comm, hSI, hcard])
  exact Subgroup.eq_of_le_of_card_ge (le_inf hDT1 hDS) hcard'

theorem sixH_h11 (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h4 : H4Concl φ t i) (h6 : H6Concl φ t i) (h8 : H8Concl φ t i) : H11Concl φ t i := by
  obtain ⟨-, h4N⟩ := h4
  have hinf := sixH_h11_inf_Mhat_K hS h8
  have hN : Kc φ t i.swap ≤ normalizer (Mhat φ t i i : Set G) :=
    (sixH_h11_K_le_T1 hS).trans h4N
  have hDN : Dstar φ t i ≤ normalizer (Mhat φ t i i : Set G) :=
    sup_le Subgroup.le_normalizer hN
  have hcard := sixH_h11_card_Dstar hS hN hinf
  unfold H11Concl
  exact ⟨sixH_h11_inf_M_K hS, hinf, hcard, sixH_h11_normal hDN,
    sixH_h11_eq_inf hS hM2 h8 hcard⟩

theorem sixH_h12_t_comm_A (hS : SCSetting L K n φ t i) (k : Axis) {a : G} (ha : a ∈ A φ k) :
    t * a = a * t :=
  (Subgroup.mem_centralizer_singleton_iff.mp (FullCenterWeyl.A_le_C hS.fc k ha)).symm

theorem sixH_h12_t_comm_w (hS : SCSetting L K n φ t i) (k : Axis) : t * w φ k = w φ k * t :=
  (Subgroup.mem_centralizer_singleton_iff.mp (FullCenterWeyl.w_facts hS.fc k).1).symm

theorem sixH_h12_t_comm_U (hS : SCSetting L K n φ t i) (k : Axis) {u : G} (hu : u ∈ U φ k) :
    t * u = u * t :=
  (Subgroup.mem_centralizer_singleton_iff.mp
    (hS.fc.setup.L_le (pull_le φ _ hu))).symm

theorem sixH_h12_t_normalizes_W (hS : SCSetting L K n φ t i) {y : G} (hy : y ∈ Wk φ t i.swap) :
    t⁻¹ * y * t ∈ Wk φ t i.swap := by
  have hV : Vtor φ t i i.swap = Wk φ t i.swap :=
    RootStandard.V_swap_eq hS.fc i hS.ne_bot hS.eq_bot
  have hN : t ∈ normalizer ((Vtor φ t i i.swap : Subgroup G) : Set G) :=
    RootStandard.t_mem_normalizer_V hS.fc i hS.ne_bot hS.eq_bot i.swap
  rw [hV] at hN
  exact (Subgroup.mem_normalizer_iff''.mp hN y).mp hy

theorem sixH_h12_W_comm (hS : SCSetting L K n φ t i) {y y' : G} (hy : y ∈ Wk φ t i.swap)
    (hy' : y' ∈ Wk φ t i.swap) : y * y' = y' * y :=
  FullCenterTorus.F_comm hS.fc (inf_le_left (a := F φ t) hy) (inf_le_left (a := F φ t) hy')

theorem sixH_h12_W_sq (hS : SCSetting L K n φ t i) {y : G} (hy : y ∈ Wk φ t i.swap) :
    y * y = 1 :=
  SingleComm.sq_W_swap hS.fc i hS.ne_bot hS.eq_bot hy

theorem sixH_h12_W_fixed (hS : SCSetting L K n φ t i) {y : G} (hy : y ∈ Wk φ t i.swap)
    (hty : t * y = y * t) : y ∈ U φ i.swap := by
  have h := FullCenterTorus.W_inf_C hS.fc i.swap
  exact h.le ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hty.symm⟩

theorem sixH_h12_not_mem_U {a : G} (ha : a ∈ A φ i.swap) (haZ : a ∉ Z₀ φ) {u : G}
    (hu : u ∈ U φ i.swap) (hu1 : u ≠ 1) :
    a⁻¹ * ((w φ i)⁻¹ * u * w φ i)⁻¹ * a * ((w φ i)⁻¹ * u * w φ i) ∉ U φ i := by
  obtain ⟨hyA, hyZ⟩ := (sixH_s2_weyl (φ := φ) i).2 u hu hu1
  obtain ⟨-, h1, h2⟩ := sixH_s1_pairing i hyA hyZ ha haZ
  intro hmem
  have hinv := (U φ i).inv_mem hmem
  have e : (a⁻¹ * ((w φ i)⁻¹ * u * w φ i)⁻¹ * a * ((w φ i)⁻¹ * u * w φ i))⁻¹ =
      ((w φ i)⁻¹ * u * w φ i)⁻¹ * a⁻¹ * ((w φ i)⁻¹ * u * w φ i) * a := by group
  rw [e] at hinv
  cases i
  · exact h1 hinv
  · exact h2 hinv

theorem sixH_h13_U_le_Mhat (h3 : H3Concl φ t i) : U φ i ≤ Mhat φ t i i := by
  rw [← h3.2]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨y, hy, rfl⟩
  exact mul_mem hy hy

theorem sixH_h12_comm_mul {N V : Subgroup G} (hNV : N ≤ V)
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x⁻¹ * y⁻¹ * x * y ∈ N) {a y y' : G} (hy' : y' ∈ V)
    (h1 : a⁻¹ * y⁻¹ * a * y ∈ N) (h2 : a⁻¹ * y'⁻¹ * a * y' ∈ N) :
    a⁻¹ * (y * y')⁻¹ * a * (y * y') ∈ N := by
  have e : a⁻¹ * (y * y')⁻¹ * a * (y * y') =
      (a⁻¹ * y'⁻¹ * a * y') * ((a⁻¹ * y⁻¹ * a * y) *
        ((a⁻¹ * y⁻¹ * a * y)⁻¹ * y'⁻¹ * (a⁻¹ * y⁻¹ * a * y) * y')) := by group
  rw [e]
  exact mul_mem h2 (mul_mem h1 (hcomm _ (hNV h1) y' hy'))

theorem sixH_h12_conj_t (hS : SCSetting L K n φ t i) {a : G} (ha : a ∈ A φ i.swap) (y₀ : G) :
    a⁻¹ * ((w φ i)⁻¹ * (t * y₀ * t) * w φ i)⁻¹ * a * ((w φ i)⁻¹ * (t * y₀ * t) * w φ i) =
      t * (a⁻¹ * ((w φ i)⁻¹ * y₀ * w φ i)⁻¹ * a * ((w φ i)⁻¹ * y₀ * w φ i)) * t := by
  have htt : t * t = 1 := SixF.t_mul_t hS.fc
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hwt : t * w φ i = w φ i * t := sixH_h12_t_comm_w hS i
  have hat : t * a = a * t := sixH_h12_t_comm_A hS i.swap ha
  have hwinv : t * (w φ i)⁻¹ = (w φ i)⁻¹ * t := (Commute.inv_right (show Commute t (w φ i) from hwt)).eq
  have hat' : t * a⁻¹ = a⁻¹ * t := (Commute.inv_right (show Commute t a from hat)).eq
  have hta : t * a * t = a := by rw [hat, mul_assoc, htt, mul_one]
  have e1 : (w φ i)⁻¹ * (t * y₀ * t) * w φ i = t * ((w φ i)⁻¹ * y₀ * w φ i) * t := by
    calc (w φ i)⁻¹ * (t * y₀ * t) * w φ i = ((w φ i)⁻¹ * t) * y₀ * (t * w φ i) := by group
      _ = (t * (w φ i)⁻¹) * y₀ * (w φ i * t) := by rw [← hwinv, hwt]
      _ = t * ((w φ i)⁻¹ * y₀ * w φ i) * t := by group
  rw [e1]
  generalize (w φ i)⁻¹ * y₀ * w φ i = Y
  calc a⁻¹ * (t * Y * t)⁻¹ * a * (t * Y * t)
      = a⁻¹ * (t⁻¹ * Y⁻¹ * t⁻¹) * a * (t * Y * t) := by group
    _ = a⁻¹ * (t * Y⁻¹ * t) * a * (t * Y * t) := by rw [htinv]
    _ = (a⁻¹ * t) * Y⁻¹ * (t * a * t) * Y * t := by group
    _ = (t * a⁻¹) * Y⁻¹ * a * Y * t := by rw [← hat', hta]
    _ = t * (a⁻¹ * Y⁻¹ * a * Y) * t := by group

theorem sixH_h12_t_conj_U (hS : SCSetting L K n φ t i) {c : G} (hc : c ∈ U φ i) :
    t * c * t = c := by
  rw [sixH_h12_t_comm_U hS i hc, mul_assoc, SixF.t_mul_t hS.fc, mul_one]

theorem sixH_h12_key (hS : SCSetting L K n φ t i) (h3 : H3Concl φ t i) {a : G}
    (ha : a ∈ A φ i.swap) (haZ : a ∉ Z₀ φ) {y₀ : G} (hy₀ : y₀ ∈ Wk φ t i.swap)
    (hc : a⁻¹ * ((w φ i)⁻¹ * y₀ * w φ i)⁻¹ * a * ((w φ i)⁻¹ * y₀ * w φ i) ∈ U φ i) :
    y₀ = 1 := by
  have htt : t * t = 1 := SixF.t_mul_t hS.fc
  have hy₁ : t * y₀ * t ∈ Wk φ t i.swap := by
    have := sixH_h12_t_normalizes_W hS hy₀
    rwa [inv_eq_of_mul_eq_one_right htt] at this
  have hu : y₀ * (t * y₀ * t) ∈ U φ i.swap := by
    refine sixH_h12_W_fixed hS (mul_mem hy₀ hy₁) ?_
    have h1 : t * (y₀ * (t * y₀ * t)) = (t * y₀ * t) * y₀ * t := by group
    rw [h1, sixH_h12_W_comm hS hy₁ hy₀]
  have hM : Wk φ t i.swap ≤ Mc φ t i :=
    (inf_le_left : Wk φ t i.swap ≤ F φ t).trans (NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot)
  have hy'M : (w φ i)⁻¹ * (t * y₀ * t) * w φ i ∈ Mhat φ t i i := by
    have h1 : w φ i * ((w φ i)⁻¹ * (t * y₀ * t) * w φ i) * (w φ i)⁻¹ ∈ Mc φ t i := by
      rw [show w φ i * ((w φ i)⁻¹ * (t * y₀ * t) * w φ i) * (w φ i)⁻¹ = t * y₀ * t by group]
      exact hM hy₁
    exact (le_sup_right : Mw φ t i i ≤ Mhat φ t i i) (FullCenterWeyl.mem_map_conj_inv.mpr h1)
  have hy'U : a⁻¹ * ((w φ i)⁻¹ * (t * y₀ * t) * w φ i)⁻¹ * a *
      ((w φ i)⁻¹ * (t * y₀ * t) * w φ i) ∈ U φ i := by
    rw [sixH_h12_conj_t hS ha y₀, sixH_h12_t_conj_U hS hc]
    exact hc
  have hprod := sixH_h12_comm_mul (sixH_h13_U_le_Mhat h3) h3.1 hy'M hc hy'U
  have hyy' : (w φ i)⁻¹ * y₀ * w φ i * ((w φ i)⁻¹ * (t * y₀ * t) * w φ i) =
      (w φ i)⁻¹ * (y₀ * (t * y₀ * t)) * w φ i := by group
  rw [hyy'] at hprod
  by_cases hu1 : y₀ * (t * y₀ * t) = 1
  · have hz : t * y₀ * t = y₀ := by
      have h1 : t * y₀ * t = y₀⁻¹ := eq_inv_of_mul_eq_one_right hu1
      rw [h1]
      exact inv_eq_of_mul_eq_one_right (sixH_h12_W_sq hS hy₀)
    have hty : t * y₀ = y₀ * t := by
      calc t * y₀ = t * y₀ * (t * t) := by rw [htt, mul_one]
        _ = (t * y₀ * t) * t := by group
        _ = y₀ * t := by rw [hz]
    by_contra hy01
    exact sixH_h12_not_mem_U ha haZ (sixH_h12_W_fixed hS hy₀ hty) hy01 hc
  · exact absurd hprod (sixH_h12_not_mem_U ha haZ hu hu1)

theorem sixH_h12_decomp (hS : SCSetting L K n φ t i) {m : G} (hm : m ∈ Mhat φ t i i) :
    ∃ m₁ ∈ Mc φ t i, ∃ y₀ ∈ Wk φ t i.swap, m = m₁ * ((w φ i)⁻¹ * y₀ * w φ i) := by
  have hm' : m ∈ ((Mc φ t i : Subgroup G) : Set G) * ((Mw φ t i i : Subgroup G) : Set G) := by
    rw [SixF.M_mul_Mw hS.fc i hS.ne_bot hS.eq_bot]
    exact hm
  obtain ⟨x, hx, z, hz, rfl⟩ := Set.mem_mul.mp hm'
  have hz' : w φ i * z * (w φ i)⁻¹ ∈ Mc φ t i := FullCenterWeyl.mem_map_conj_inv.mp hz
  obtain ⟨v, hv, y₀, hy₀, hvy⟩ := RootStandard.exists_V_mul_W hS.fc i hS.ne_bot hS.eq_bot hz'
  have hVi : Vtor φ t i i = Mc φ t i ⊓ Mw φ t i i :=
    (SixF.M_inf_Mw hS.fc i hS.ne_bot hS.eq_bot).symm
  have hv' : v ∈ Vtor φ t i i := hv
  rw [hVi] at hv'
  obtain ⟨-, hvw⟩ := Subgroup.mem_inf.mp hv'
  have hv1 : w φ i * v * (w φ i)⁻¹ ∈ Mc φ t i := FullCenterWeyl.mem_map_conj_inv.mp hvw
  have hwinv : (w φ i)⁻¹ = w φ i := FullCenterWeyl.w_inv i
  have hv2 : (w φ i)⁻¹ * v * w φ i ∈ Mc φ t i := by
    rw [hwinv]
    rw [hwinv] at hv1
    exact hv1
  refine ⟨x * ((w φ i)⁻¹ * v * w φ i), mul_mem hx hv2, y₀, hy₀, ?_⟩
  have hzv : z = (w φ i)⁻¹ * (v * y₀) * w φ i := by
    rw [← hvy]
    group
  rw [hzv]
  group

theorem sixH_h12 (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h3 : H3Concl φ t i) (h4 : H4Concl φ t i) (h6 : H6Concl φ t i) : H12Concl φ t i := by
  clear h4
  intro a ha haZ m hm
  have hAK : a ∈ Kc φ t i.swap := (le_sup_left : A φ i.swap ≤ Kc φ t i.swap) ha
  constructor
  · intro hc
    obtain ⟨m₁, hm₁, y₀, hy₀, rfl⟩ := sixH_h12_decomp hS hm
    have hcomm : a * m₁ = m₁ * a :=
      h6 a hAK m₁ ((le_sup_left : Mc φ t i ≤ Mhat φ t i i.swap) hm₁)
    have h1 : m₁⁻¹ * a * m₁ = a := by rw [mul_assoc, hcomm, inv_mul_cancel_left]
    have e : a⁻¹ * (m₁ * ((w φ i)⁻¹ * y₀ * w φ i))⁻¹ * a * (m₁ * ((w φ i)⁻¹ * y₀ * w φ i)) =
        a⁻¹ * ((w φ i)⁻¹ * y₀ * w φ i)⁻¹ * a * ((w φ i)⁻¹ * y₀ * w φ i) := by
      calc a⁻¹ * (m₁ * ((w φ i)⁻¹ * y₀ * w φ i))⁻¹ * a * (m₁ * ((w φ i)⁻¹ * y₀ * w φ i))
          = a⁻¹ * ((w φ i)⁻¹ * y₀ * w φ i)⁻¹ * (m₁⁻¹ * a * m₁) * ((w φ i)⁻¹ * y₀ * w φ i) := by
            group
        _ = a⁻¹ * ((w φ i)⁻¹ * y₀ * w φ i)⁻¹ * a * ((w φ i)⁻¹ * y₀ * w φ i) := by rw [h1]
    rw [e] at hc
    have hy := sixH_h12_key hS h3 ha haZ hy₀ hc
    rw [hy]
    simpa using hm₁
  · intro hmM
    have hcomm : a * m = m * a :=
      h6 a hAK m ((le_sup_left : Mc φ t i ≤ Mhat φ t i i.swap) hmM)
    have e : a⁻¹ * m⁻¹ * a * m = 1 := by
      calc a⁻¹ * m⁻¹ * a * m = a⁻¹ * m⁻¹ * (a * m) := by group
        _ = a⁻¹ * m⁻¹ * (m * a) := by rw [hcomm]
        _ = 1 := by group
    rw [e]
    exact one_mem _

theorem sixH_h13_sq_mem (h3 : H3Concl φ t i) {g : G} (hg : g ∈ Mhat φ t i i) :
    g * g ∈ U φ i := by
  rw [← h3.2]
  exact Subgroup.subset_closure ⟨g, hg, rfl⟩

theorem sixH_h13_Mhat_le_normalizer_U (h3 : H3Concl φ t i) :
    Mhat φ t i i ≤ normalizer (U φ i : Set G) := by
  refine sixH_h5_le_normalizer_of_conj fun g hg c hc => ?_
  have h1 := h3.1 g⁻¹ (inv_mem hg) c⁻¹ (inv_mem (sixH_h13_U_le_Mhat h3 hc))
  have e : g * c * g⁻¹ = (g⁻¹⁻¹ * c⁻¹⁻¹ * g⁻¹ * c⁻¹) * c := by group
  rw [e]
  exact mul_mem h1 hc

theorem sixH_h13_K_le_normalizer_U (hS : SCSetting L K n φ t i) :
    Kc φ t i.swap ≤ normalizer (U φ i : Set G) := by
  refine sixH_h5_le_normalizer_of_conj fun g hg c hc => ?_
  rw [hS.fc.H_centralizes_U i (FullCenterWeyl.K_le_H hS.fc i.swap hg) hc]
  exact hc

theorem sixH_h13_U_le_Mc (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i) :
    U φ i ≤ Mc φ t i := by
  have h : closure {x : G | ∃ y ∈ Mc φ t i, x = y * y} = U φ i :=
    SixG.closure_sq_M hS.fc i hS.ne_bot hS.eq_bot hM2
  rw [← h]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨y, hy, rfl⟩
  exact mul_mem hy hy

theorem sixH_h13_outside (hS : SCSetting L K n φ t i) (h3 : H3Concl φ t i) (h4 : H4Concl φ t i)
    (h12 : H12Concl φ t i) {x : G} (hx : x ∈ Dstar φ t i) (hxM : x ∉ Mhat φ t i i)
    (hx2 : x * x ∈ U φ i) : x ∈ Mc φ t i ⊔ Kc φ t i.swap := by
  have hKN : Kc φ t i.swap ≤ normalizer (Mhat φ t i i : Set G) :=
    (sixH_h11_K_le_T1 hS).trans h4.2
  have hx' : x ∈ ((Mhat φ t i i : Subgroup G) : Set G) * ((Kc φ t i.swap : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hKN]
    exact hx
  obtain ⟨m, hm, k, hk, rfl⟩ := Set.mem_mul.mp hx'
  have hk' : k ∈ ((A φ i.swap : Subgroup G) : Set G) *
      ((F φ t ⊓ D φ t i.swap : Subgroup G) : Set G) := by
    rw [FullCenterWeyl.K_mul hS.fc i.swap]
    exact hk
  obtain ⟨a, ha, f, hf, rfl⟩ := Set.mem_mul.mp hk'
  have hFM : F φ t ≤ Mhat φ t i i :=
    (NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot).trans le_sup_left
  have hfM : f ∈ Mhat φ t i i := hFM (Subgroup.mem_inf.mp hf).1
  have haZ : a ∉ Z₀ φ := by
    intro haZ
    apply hxM
    have haF : a ∈ F φ t ⊓ D φ t i.swap := FullCenterTorus.ZP_le_Fi hS.fc i.swap haZ
    exact mul_mem hm (mul_mem (hFM (Subgroup.mem_inf.mp haF).1) hfM)
  have haK : a ∈ Kc φ t i.swap := (le_sup_left : A φ i.swap ≤ Kc φ t i.swap) ha
  have haN : a ∈ normalizer (Mhat φ t i i : Set G) := hKN haK
  obtain ⟨m2, hm2, hxe⟩ : ∃ m2 ∈ Mhat φ t i i, m * (a * f) = a * m2 :=
    ⟨a⁻¹ * m * a * f, mul_mem ((Subgroup.mem_normalizer_iff''.mp haN m).mp hm) hfM, by group⟩
  rw [hxe] at hx2 ⊢
  have haa : a * a = 1 := SingleComm.A_mul_self hS.fc i.swap ha
  have hg : a⁻¹ * m2 * a ∈ Mhat φ t i i := (Subgroup.mem_normalizer_iff''.mp haN m2).mp hm2
  have e1 : (a * m2) * (a * m2) = (a⁻¹ * m2 * a) * m2 := by
    calc (a * m2) * (a * m2) = (a * a) * (a⁻¹ * m2 * a) * m2 := by group
      _ = (a⁻¹ * m2 * a) * m2 := by rw [haa, one_mul]
  have e2 : a⁻¹ * m2⁻¹ * a * m2 =
      ((a⁻¹ * m2 * a) * (a⁻¹ * m2 * a))⁻¹ * ((a⁻¹ * m2 * a) * m2) := by group
  have hcomm : a⁻¹ * m2⁻¹ * a * m2 ∈ U φ i := by
    rw [e2]
    rw [e1] at hx2
    exact mul_mem (inv_mem (sixH_h13_sq_mem h3 hg)) hx2
  have hm2M : m2 ∈ Mc φ t i := (h12 a ha haZ m2 hm2).mp hcomm
  exact mul_mem (Subgroup.mem_sup_right haK) (Subgroup.mem_sup_left hm2M)

theorem sixH_h13_comm_aux {m m' k k' : G} (h1 : m * k = k * m) (h2 : m * k' = k' * m)
    (h3 : m' * k = k * m') (h4 : m' * k' = k' * m') (h5 : k * k' = k' * k) :
    (m * k) * (m' * k') * (m * k)⁻¹ * (m' * k')⁻¹ = m * m' * m⁻¹ * m'⁻¹ := by
  have hxy : (m * k) * (m' * k') = (m * m') * (k * k') := by
    calc (m * k) * (m' * k') = m * (k * m') * k' := by group
      _ = m * (m' * k) * k' := by rw [← h3]
      _ = (m * m') * (k * k') := by group
  have hyx : (m' * k') * (m * k) = (m' * m) * (k * k') := by
    calc (m' * k') * (m * k) = m' * (k' * m) * k := by group
      _ = m' * (m * k') * k := by rw [← h2]
      _ = m' * m * (k' * k) := by group
      _ = (m' * m) * (k * k') := by rw [h5]
  calc (m * k) * (m' * k') * (m * k)⁻¹ * (m' * k')⁻¹
      = ((m * k) * (m' * k')) * ((m' * k') * (m * k))⁻¹ := by group
    _ = ((m * m') * (k * k')) * ((m' * m) * (k * k'))⁻¹ := by rw [hxy, hyx]
    _ = m * m' * m⁻¹ * m'⁻¹ := by group

theorem sixH_h13_elem_N (hS : SCSetting L K n φ t i) (h3 : H3Concl φ t i) (h6 : H6Concl φ t i)
    {x y : G} (hx : x ∈ Mc φ t i ⊔ Kc φ t i.swap) (hy : y ∈ Mc φ t i ⊔ Kc φ t i.swap) :
    x * y * x⁻¹ * y⁻¹ ∈ U φ i ∧ x * x ∈ U φ i := by
  have hMM : Mc φ t i ≤ Mhat φ t i i := le_sup_left
  have hMj : Mc φ t i ≤ Mhat φ t i i.swap := le_sup_left
  have hcomm : ∀ m ∈ Mc φ t i, ∀ k ∈ Kc φ t i.swap, m * k = k * m :=
    fun m hm k hk => (h6 k hk m (hMj hm)).symm
  have hKN : Kc φ t i.swap ≤ normalizer (Mc φ t i : Set G) :=
    sixH_h5_le_normalizer_of_conj fun g hg c hc => by
      rw [← hcomm c hc g hg, mul_inv_cancel_right]
      exact hc
  have hprod : ∀ z ∈ Mc φ t i ⊔ Kc φ t i.swap,
      ∃ m ∈ Mc φ t i, ∃ k ∈ Kc φ t i.swap, z = m * k := by
    intro z hz
    have hz' : z ∈ ((Mc φ t i : Subgroup G) : Set G) * ((Kc φ t i.swap : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hKN]
      exact hz
    obtain ⟨m, hm, k, hk, rfl⟩ := Set.mem_mul.mp hz'
    exact ⟨m, hm, k, hk, rfl⟩
  have hK1 : ∀ k ∈ Kc φ t i.swap, k * k = 1 := fun k hk =>
    SingleComm.K_sq hS.fc i.swap (fun w hw => SingleComm.sq_W_swap hS.fc i hS.ne_bot hS.eq_bot hw)
      hk
  obtain ⟨m, hm, k, hk, rfl⟩ := hprod x hx
  obtain ⟨m', hm', k', hk', rfl⟩ := hprod y hy
  refine ⟨?_, ?_⟩
  · rw [sixH_h13_comm_aux (hcomm m hm k hk) (hcomm m hm k' hk') (hcomm m' hm' k hk)
      (hcomm m' hm' k' hk') (FullCenterWeyl.K_comm hS.fc i.swap hk hk')]
    have h := h3.1 m⁻¹ (inv_mem (hMM hm)) m'⁻¹ (inv_mem (hMM hm'))
    simpa only [inv_inv] using h
  · have e : (m * k) * (m * k) = (m * m) * (k * k) := by
      calc (m * k) * (m * k) = m * (k * m) * k := by group
        _ = m * (m * k) * k := by rw [← hcomm m hm k hk]
        _ = (m * m) * (k * k) := by group
    rw [e, hK1 k hk, mul_one]
    exact sixH_h13_sq_mem h3 (hMM hm)

theorem sixH_h13_not_Mhat_le_N (hS : SCSetting L K n φ t i) :
    ¬ Mhat φ t i i ≤ Mc φ t i ⊔ Kc φ t i.swap := by
  intro hle
  have h1 : Nat.card (Mhat φ t i i) ≤ Nat.card (Mc φ t i ⊔ Kc φ t i.swap : Subgroup G) :=
    Subgroup.card_le_of_le hle
  rw [SixF.card_Mhat hS.fc i hS.ne_bot hS.eq_bot,
    SixG.card_M_sup_K hS.fc i hS.ne_bot hS.eq_bot] at h1
  have hq := hS.fc.four_le_card
  have h2 : Nat.card K ^ 6 < Nat.card K ^ 7 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem sixH_h13_not_N_le_Mhat (hS : SCSetting L K n φ t i) (h11 : H11Concl φ t i) :
    ¬ Mc φ t i ⊔ Kc φ t i.swap ≤ Mhat φ t i i := by
  intro hle
  have hK : Kc φ t i.swap ≤ F φ t ⊓ D φ t i.swap :=
    (le_inf (le_sup_right.trans hle) le_rfl : Kc φ t i.swap ≤ Mhat φ t i i ⊓ Kc φ t i.swap).trans
      h11.2.1.le
  have h1 : Nat.card (Kc φ t i.swap) ≤ Nat.card (F φ t ⊓ D φ t i.swap : Subgroup G) :=
    Subgroup.card_le_of_le hK
  rw [FullCenterWeyl.card_K hS.fc i.swap, FullCenterTorus.card_Fi hS.fc i.swap] at h1
  have hq := hS.fc.four_le_card
  have h2 : Nat.card K ^ 3 < Nat.card K ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem sixH_h13_cover (hS : SCSetting L K n φ t i) (h3 : H3Concl φ t i) (h4 : H4Concl φ t i)
    (h12 : H12Concl φ t i) {E : Subgroup G} (hED : E ≤ Dstar φ t i)
    (hE : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ U φ i ∧ x * x ∈ U φ i) :
    E ≤ Mhat φ t i i ∨ E ≤ Mc φ t i ⊔ Kc φ t i.swap := by
  by_cases hEM : E ≤ Mhat φ t i i
  · exact Or.inl hEM
  · right
    obtain ⟨x₀, hx₀E, hx₀M⟩ := SetLike.not_le_iff_exists.mp hEM
    have hx₀N : x₀ ∈ Mc φ t i ⊔ Kc φ t i.swap :=
      sixH_h13_outside hS h3 h4 h12 (hED hx₀E) hx₀M (hE x₀ hx₀E x₀ hx₀E).2
    intro e heE
    by_cases heM : e ∈ Mhat φ t i i
    · have hex : e * x₀ ∈ E := mul_mem heE hx₀E
      have hexM : e * x₀ ∉ Mhat φ t i i := fun h => hx₀M (by
        have := mul_mem (inv_mem heM) h
        rwa [inv_mul_cancel_left] at this)
      have hexN := sixH_h13_outside hS h3 h4 h12 (hED hex) hexM (hE _ hex _ hex).2
      have := mul_mem hexN (inv_mem hx₀N)
      rwa [mul_inv_cancel_right] at this
    · exact sixH_h13_outside hS h3 h4 h12 (hED heE) heM (hE e heE e heE).2

theorem sixH_h13 (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h3 : H3Concl φ t i) (h4 : H4Concl φ t i) (h6 : H6Concl φ t i) (h11 : H11Concl φ t i)
    (h12 : H12Concl φ t i) : H13Concl φ t i := by
  have hUD : U φ i ≤ Dstar φ t i := (sixH_h13_U_le_Mhat h3).trans le_sup_left
  have hNormal : ((U φ i).subgroupOf (Dstar φ t i)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUD).mpr
      (sup_le (sixH_h13_Mhat_le_normalizer_U h3) (sixH_h13_K_le_normalizer_U hS))
  unfold H13Concl
  refine ⟨hNormal, ?_⟩
  intro E
  exact SixG.maximal_map_iff hUD le_rfl (sixH_h13_U_le_Mhat h3)
    ((sixH_h13_U_le_Mc hS hM2).trans le_sup_left) le_sup_left
    (sup_le ((le_sup_left : Mc φ t i ≤ Mhat φ t i i).trans le_sup_left) le_sup_right)
    (fun x hx y hy => ⟨by simpa only [inv_inv] using h3.1 x⁻¹ (inv_mem hx) y⁻¹ (inv_mem hy),
      sixH_h13_sq_mem h3 hx⟩)
    (fun x hx y hy => sixH_h13_elem_N hS h3 h6 hx hy)
    (fun E' hED he => sixH_h13_cover hS h3 h4 h12 hED he)
    (sixH_h13_not_Mhat_le_N hS) (sixH_h13_not_N_le_Mhat hS h11) E

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
