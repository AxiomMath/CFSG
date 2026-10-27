module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixHBase
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixHCenter

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Concl

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] def H5Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  Mhat φ t i i.swap ≤ T₀ φ t i.swap ∧ ((Mhat φ t i i.swap).subgroupOf (T₀ φ t i.swap)).Normal

@[expose] def H6Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ k ∈ Kc φ t i.swap, ∀ m ∈ Mhat φ t i i.swap, k * m = m * k

@[expose] def H7Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  centralizer (Kc φ t i.swap : Set G) ⊓ T₀ φ t i.swap = Mhat φ t i i.swap ∧
    SixG.MNNormalIn (Mhat φ t i i.swap) (Tplus φ t i) (J₀ φ)

@[expose] def H8Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  Mhat φ t i i ⊓ P₂ φ t i.swap = Mc φ t i ∧
    Mhat φ t i Axis.one ⊓ Mhat φ t i Axis.two = Mc φ t i ∧
    Nat.card (S φ t i) = Nat.card K ^ 10 ∧ S φ t i ⊔ zpowers t = Tplus φ t i ∧
    S φ t i ⊓ zpowers t = ⊥ ∧ ((S φ t i).subgroupOf (Tplus φ t i)).Normal

@[expose] def H9Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  SixG.MNNormalIn (Mc φ t i) (Tplus φ t i) (J₀ φ)

end Concl

section Steps

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixH_h5_le_normalizer_of_conj {Q T : Subgroup G}
    (hN : ∀ g ∈ T, ∀ c ∈ Q, g * c * g⁻¹ ∈ Q) : T ≤ normalizer (Q : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨hN g hg c, fun hc => ?_⟩
  simpa [mul_assoc] using hN g⁻¹ (inv_mem hg) (g * c * g⁻¹) hc

theorem sixH_h5_T0_eq (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i) :
    T₀ φ t i.swap = Astar φ t i ⊔ P₂ φ t i.swap := by
  have hAT : Astar φ t i ≤ T₀ φ t i.swap :=
    (SixG.Astar_le_T₂ hS.fc i hS.ne_bot hS.eq_bot).trans inf_le_left
  have hPT : P₂ φ t i.swap ≤ T₀ φ t i.swap := le_sup_right
  have hTT : T₀ φ t i.swap ≤ Tplus φ t i := le_sup_right
  have hAn : SixG.MNNormalIn (Astar φ t i) (Tplus φ t i) (J₀ φ) :=
    SixG.normalIn_Astar hS.fc i hS.ne_bot hS.eq_bot hM2
  obtain ⟨hA1, hA2, -⟩ := hAn
  have hNA : Tplus φ t i ≤ normalizer (Astar φ t i : Set G) :=
    sixH_h5_le_normalizer_of_conj fun g hg a ha =>
      (Subgroup.normal_subgroupOf_iff hA1).mp hA2 a g ha hg
  have hPN : P₂ φ t i.swap ≤ normalizer (Astar φ t i : Set G) :=
    hPT.trans (hTT.trans hNA)
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hPN
  have hinf : Astar φ t i ⊓ P₂ φ t i.swap = Cstar φ t i :=
    SixG.Astar_inf_P₂ hS.fc i hS.ne_bot hS.eq_bot
  have hcA : Nat.card (Astar φ t i) = Nat.card K ^ 8 :=
    SixG.card_Astar hS.fc i hS.ne_bot hS.eq_bot
  have hcP : Nat.card (P₂ φ t i.swap) = 2 * Nat.card K ^ 8 :=
    NextCores.card_P₂ hS.fc i hS.ne_bot hS.eq_bot
  have hcC : Nat.card (Cstar φ t i) = Nat.card K ^ 7 :=
    SixG.card_Cstar hS.fc i hS.ne_bot hS.eq_bot
  have hcT : Nat.card (T₀ φ t i.swap) = 2 * Nat.card K ^ 9 :=
    NextCores.card_T₀ hS.fc i hS.ne_bot hS.eq_bot
  rw [hinf, hcC, hcA, hcP] at hcard
  have hq : 0 < Nat.card K ^ 7 := pow_pos Nat.card_pos 7
  have hX : Nat.card (Astar φ t i ⊔ P₂ φ t i.swap : Subgroup G) = 2 * Nat.card K ^ 9 := by
    apply Nat.eq_of_mul_eq_mul_right hq
    rw [hcard]
    ring
  have hsup : Astar φ t i ⊔ P₂ φ t i.swap ≤ T₀ φ t i.swap := sup_le hAT hPT
  exact (Subgroup.eq_of_le_of_card_ge hsup (le_of_eq (by rw [hcT, hX]))).symm

theorem sixH_h5_comm (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i) :
    ∀ x ∈ T₀ φ t i.swap, ∀ y ∈ T₀ φ t i.swap, x * y * x⁻¹ * y⁻¹ ∈ Cstar φ t i := by
  have hT := sixH_h5_T0_eq hS hM2
  have hAT : Astar φ t i ≤ T₀ φ t i.swap :=
    (SixG.Astar_le_T₂ hS.fc i hS.ne_bot hS.eq_bot).trans inf_le_left
  have hPT : P₂ φ t i.swap ≤ T₀ φ t i.swap := le_sup_right
  have hTT : T₀ φ t i.swap ≤ Tplus φ t i := le_sup_right
  have hAn : SixG.MNNormalIn (Astar φ t i) (Tplus φ t i) (J₀ φ) :=
    SixG.normalIn_Astar hS.fc i hS.ne_bot hS.eq_bot hM2
  obtain ⟨hA1, hA2, -⟩ := hAn
  have hinf : Astar φ t i ⊓ P₂ φ t i.swap = Cstar φ t i :=
    SixG.Astar_inf_P₂ hS.fc i hS.ne_bot hS.eq_bot
  have hAeq : Astar φ t i = Bstar φ t i ⊔ Xk φ t i.swap :=
    SixG.Astar_eq hS.fc i
  have hCeq : Cstar φ t i = Mc φ t i ⊔ Xk φ t i.swap :=
    SixG.Cstar_eq hS.fc i hS.ne_bot hS.eq_bot
  have hAc : ∀ g ∈ T₀ φ t i.swap, ∀ a ∈ Astar φ t i, g * a * g⁻¹ ∈ Astar φ t i :=
    fun g hg a ha => (Subgroup.normal_subgroupOf_iff hA1).mp hA2 a g ha (hTT hg)
  have hPc : ∀ g ∈ T₀ φ t i.swap, ∀ p ∈ P₂ φ t i.swap, g * p * g⁻¹ ∈ P₂ φ t i.swap :=
    fun g hg p hp =>
      (Subgroup.mem_normalizer_iff.mp (SixG.T₀_le_normalizer_P₂ hS.fc i.swap hg) p).mp hp
  have hCc : ∀ g ∈ T₀ φ t i.swap, ∀ c ∈ Cstar φ t i, g * c * g⁻¹ ∈ Cstar φ t i := by
    intro g hg c hc
    rw [← hinf] at hc ⊢
    obtain ⟨hcA, hcP⟩ := Subgroup.mem_inf.mp hc
    exact Subgroup.mem_inf.mpr ⟨hAc g hg c hcA, hPc g hg c hcP⟩
  have hZ' : Astar φ t i ⊔ P₂ φ t i.swap ≤ normalizer (Cstar φ t i : Set G) := by
    rw [← hT]
    exact sixH_h5_le_normalizer_of_conj hCc
  have hZA : Astar φ t i ≤ normalizer (Cstar φ t i : Set G) := le_sup_left.trans hZ'
  have hZB : Bstar φ t i ⊔ Xk φ t i.swap ≤ normalizer (Cstar φ t i : Set G) := by
    rw [← hAeq]
    exact hZA
  have hXC : Xk φ t i.swap ≤ Cstar φ t i := by
    rw [hCeq]
    exact le_sup_right
  have hBB : ∀ a ∈ Bstar φ t i, ∀ b ∈ Bstar φ t i, a * b * a⁻¹ * b⁻¹ ∈ Cstar φ t i :=
    fun a ha b hb => SixG.K_le_Cstar hS.fc i hS.ne_bot hS.eq_bot
      (SixG.elem_Bstar hS.fc i hS.ne_bot hS.eq_bot hM2 ha hb).1
  have hBX : ∀ a ∈ Bstar φ t i, ∀ b ∈ Xk φ t i.swap, a * b * a⁻¹ * b⁻¹ ∈ Cstar φ t i := by
    intro a ha b hb
    have haA : a ∈ Astar φ t i := by
      rw [hAeq]
      exact (le_sup_left : Bstar φ t i ≤ Bstar φ t i ⊔ Xk φ t i.swap) ha
    exact mul_mem (hCc a (hAT haA) b (hXC hb)) (inv_mem (hXC hb))
  have hXX : ∀ a ∈ Xk φ t i.swap, ∀ b ∈ Xk φ t i.swap, a * b * a⁻¹ * b⁻¹ ∈ Cstar φ t i :=
    fun a ha b hb =>
      mul_mem (mul_mem (mul_mem (hXC ha) (hXC hb)) (inv_mem (hXC ha))) (inv_mem (hXC hb))
  have hAA : ∀ a ∈ Astar φ t i, ∀ b ∈ Astar φ t i, a * b * a⁻¹ * b⁻¹ ∈ Cstar φ t i := by
    intro a ha b hb
    rw [hAeq] at ha hb
    exact SixG.comm_sup_of_comm hZB hBB hBX hXX ha hb
  have hAP : ∀ a ∈ Astar φ t i, ∀ b ∈ P₂ φ t i.swap, a * b * a⁻¹ * b⁻¹ ∈ Cstar φ t i := by
    intro a ha b hb
    rw [← hinf]
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (hPc a (hAT ha) b hb) (inv_mem hb)⟩
    have h1 : b * a⁻¹ * b⁻¹ ∈ Astar φ t i := hAc b (hPT hb) a⁻¹ (inv_mem ha)
    simpa only [mul_assoc] using mul_mem ha h1
  have hPP : ∀ a ∈ P₂ φ t i.swap, ∀ b ∈ P₂ φ t i.swap, a * b * a⁻¹ * b⁻¹ ∈ Cstar φ t i := by
    intro a ha b hb
    have h := SixF.comm_P₂_mem_X hS.fc i hS.ne_bot hS.eq_bot (inv_mem ha) (inv_mem hb)
    simp only [inv_inv] at h
    exact hXC h
  intro x hx y hy
  rw [hT] at hx hy
  exact SixG.comm_sup_of_comm hZ' hAA hAP hPP hx hy

theorem sixH_h5 (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i) :
    H5Concl φ t i := by
  have hle : Mhat φ t i i.swap ≤ T₀ φ t i.swap :=
    (SixF.Mhat_le_P₂ hS.fc i).trans le_sup_right
  have hFw : Fw φ t i.swap ≤ Mhat φ t i i.swap :=
    (Subgroup.map_mono (NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot)).trans le_sup_right
  have hCM : Cstar φ t i ≤ Mhat φ t i i.swap := sup_le le_sup_left hFw
  unfold H5Concl
  refine ⟨hle, (Subgroup.normal_subgroupOf_iff hle).mpr ?_⟩
  intro m x hm hx
  have h2 := mul_mem (hCM (sixH_h5_comm hS hM2 x hx m (hle hm))) hm
  simpa [mul_assoc] using h2

theorem sixH_h6_swap_swap (k : Axis) : k.swap.swap = k := by
  cases k <;> rfl

theorem sixH_h6_sup_comm {X Y : Subgroup G} {z : G}
    (hX : ∀ x ∈ X, x * z = z * x) (hY : ∀ y ∈ Y, y * z = z * y) :
    ∀ m ∈ X ⊔ Y, m * z = z * m := by
  have hle : X ⊔ Y ≤ Subgroup.centralizer ({z} : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact (hX x hx).symm
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact (hY y hy).symm
  intro m hm
  exact (Subgroup.mem_centralizer_iff.mp (hle hm) z (Set.mem_singleton z)).symm

theorem sixH_h6_conj_mem_cen {M : Subgroup G} {g x : G} (hg : g ∈ normalizer (M : Set G))
    (hx : x ∈ Subgroup.centralizer (M : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (M : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro h hh
  have hh' : g⁻¹ * h * g ∈ (M : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hg
    refine (hg (g⁻¹ * h * g)).mpr ?_
    have e : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
    rw [e]
    exact hh
  have hc := hx (g⁻¹ * h * g) hh'
  calc h * (g * x * g⁻¹) = g * ((g⁻¹ * h * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * h * g)) * g⁻¹ := by rw [hc]
    _ = g * x * g⁻¹ * h := by group

theorem sixH_h6_U_central (h1 : H1Concl φ t i) {u g : G} (hu : u ∈ U φ i)
    (hg : g ∈ Tplus φ t i) : g * u = u * g := by
  unfold H1Concl at h1
  rw [← h1] at hu
  obtain ⟨z, hz, hzu⟩ := Subgroup.mem_map.mp hu
  rw [← hzu]
  have hc : (⟨g, hg⟩ : ↥(Tplus φ t i)) * z = z * ⟨g, hg⟩ := Subgroup.mem_center_iff.mp hz _
  exact congrArg Subtype.val hc

theorem sixH_h6_Wk_Mc (hS : SCSetting L K n φ t i) {z : G} (hz : z ∈ Wk φ t i.swap)
    {y : G} (hy : y ∈ Mc φ t i) : z * y = y * z := by
  obtain ⟨a, ha, w', hw', rfl⟩ := RootStandard.exists_V_mul_W hS.fc i hS.ne_bot hS.eq_bot hy
  have hza : z * a = a * z :=
    (RootStandard.V_comm_W_swap hS.fc i hS.ne_bot hS.eq_bot ha hz).symm
  have hWF : Wk φ t i.swap ≤ F φ t := inf_le_left
  have hzw : z * w' = w' * z := FullCenterTorus.F_comm hS.fc (hWF hz) (hWF hw')
  calc z * (a * w') = (z * a) * w' := (mul_assoc _ _ _).symm
    _ = (a * z) * w' := by rw [hza]
    _ = a * (z * w') := mul_assoc _ _ _
    _ = a * (w' * z) := by rw [hzw]
    _ = a * w' * z := (mul_assoc _ _ _).symm

theorem sixH_h6_Wk_Mw (hS : SCSetting L K n φ t i)
    (hsw : ∀ x ∈ Vtor φ t i i.swap, (w φ i.swap)⁻¹ * x * w φ i.swap ∈ Vtor φ t i i.swap)
    {z m : G} (hz : z ∈ Wk φ t i.swap) (hm : m ∈ Mw φ t i i.swap) : z * m = m * z := by
  have hwinv : (w φ i.swap)⁻¹ = w φ i.swap :=
    inv_eq_of_mul_eq_one_right (FullCenterWeyl.w_mul_self (φ := φ) i.swap)
  have hV : Vtor φ t i i.swap = Wk φ t i.swap :=
    RootStandard.V_swap_eq hS.fc i hS.ne_bot hS.eq_bot
  have hzc : w φ i.swap * z * (w φ i.swap)⁻¹ ∈ Wk φ t i.swap := by
    rw [← hV, hwinv]
    have h2 := hsw z (by rw [hV]; exact hz)
    rwa [hwinv] at h2
  have hy : w φ i.swap * m * (w φ i.swap)⁻¹ ∈ Mc φ t i :=
    FullCenterWeyl.mem_map_conj_inv.mp hm
  have hc := sixH_h6_Wk_Mc hS hzc hy
  have e1 : w φ i.swap * (z * m) * (w φ i.swap)⁻¹
      = (w φ i.swap * z * (w φ i.swap)⁻¹) * (w φ i.swap * m * (w φ i.swap)⁻¹) := by group
  have e2 : w φ i.swap * (m * z) * (w φ i.swap)⁻¹
      = (w φ i.swap * m * (w φ i.swap)⁻¹) * (w φ i.swap * z * (w φ i.swap)⁻¹) := by group
  calc z * m = (w φ i.swap)⁻¹ * (w φ i.swap * (z * m) * (w φ i.swap)⁻¹) * w φ i.swap := by group
    _ = (w φ i.swap)⁻¹ * (w φ i.swap * (m * z) * (w φ i.swap)⁻¹) * w φ i.swap := by
        rw [e1, e2, hc]
    _ = m * z := by group

theorem sixH_h6 (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1 : H1Concl φ t i) (h2b : H2bConcl φ t i) (h5 : H5Concl φ t i) : H6Concl φ t i := by
  unfold H5Concl at h5
  unfold H2bConcl at h2b
  have hle : Mhat φ t i i.swap ≤ T₀ φ t i.swap := h5.1
  have hMj : Mhat φ t i i.swap ≤ Tplus φ t i := hle.trans le_sup_right
  have hsw : ∀ x ∈ Vtor φ t i i.swap, (w φ i.swap)⁻¹ * x * w φ i.swap ∈ Vtor φ t i i.swap :=
    h2b.2
  have hWC : Wk φ t i.swap ≤ centralizer (Mhat φ t i i.swap : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    exact sixH_h6_sup_comm (X := Mc φ t i) (Y := Mw φ t i i.swap) (z := z)
      (fun y hy => (sixH_h6_Wk_Mc hS hz hy).symm) (fun m hm => (sixH_h6_Wk_Mw hS hsw hz hm).symm)
  have hUCen : U φ i ≤ centralizer (Mhat φ t i i.swap : Set G) := by
    intro u hu
    exact Subgroup.mem_centralizer_iff.mpr (fun m hm => sixH_h6_U_central h1 hu (hMj hm))
  have hPT0 : P φ ≤ T₀ φ t i.swap := le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  have hT0N_M : T₀ φ t i.swap ≤ normalizer (Mhat φ t i i.swap : Set G) :=
    sixH_h5_le_normalizer_of_conj fun g hg c hc =>
      (Subgroup.normal_subgroupOf_iff hle).mp h5.2 c g hc hg
  have hAN : T₀ φ t i.swap ≤ normalizer (A φ i.swap : Set G) :=
    SixG.le_normalizer_A_of_E hS.fc i.swap (le_trans (NextCores.T₀_le_En hS.fc i.swap) inf_le_left)
  have hPAN : P φ ≤ normalizer (A φ i.swap : Set G) := hPT0.trans hAN
  have hPN : P φ ≤ normalizer (Mhat φ t i i.swap : Set G) := hPT0.trans hT0N_M
  have hwN : w φ i.swap ∈ normalizer (Mhat φ t i i.swap : Set G) :=
    SixF.w_mem_normalizer_Mhat' i i.swap
  have hUA : U φ i ≤ A φ i.swap :=
    pull_mono φ ((FullCenter.rootU_le_center (K := K) i).trans
      (FullCenter.center_le_rootA (K := K) i.swap))
  have hX : A φ i.swap ⊓ centralizer (Mhat φ t i i.swap : Set G) = A φ i.swap := by
    apply sixH_s3_invariant_A i
    · exact inf_le_left
    · intro p hp x hx
      obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (hPAN hp) x).mp hxA, sixH_h6_conj_mem_cen (hPN hp) hxC⟩
    · intro x hx
      obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr
        ⟨FullCenterWeyl.conj_w_mem_A hS.fc i.swap hxA, sixH_h6_conj_mem_cen hwN hxC⟩
    · exact le_inf hUA hUCen
  have hAC : A φ i.swap ≤ centralizer (Mhat φ t i i.swap : Set G) := inf_eq_left.mp hX
  have hWU : (Wk φ t i.swap : Set G) * (U φ i : Set G) = (F φ t ⊓ D φ t i.swap : Set G) := by
    have h := FullCenterTorus.W_mul_U hS.fc i.swap
    rw [sixH_h6_swap_swap] at h
    exact h
  have hFD : F φ t ⊓ D φ t i.swap ≤ centralizer (Mhat φ t i i.swap : Set G) := by
    intro x hx
    have hx' : x ∈ (Wk φ t i.swap : Set G) * (U φ i : Set G) := by
      rw [hWU]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
    exact mul_mem (hWC ha) (hUCen hb)
  have hKC : Kc φ t i.swap ≤ centralizer (Mhat φ t i i.swap : Set G) := sup_le hAC hFD
  unfold H6Concl
  intro k hk m hm
  exact (Subgroup.mem_centralizer_iff.mp (hKC hk) m hm).symm

theorem sixH_h7_alg {a w t u c : G} (hc : a * w * a⁻¹ * w⁻¹ = c) (hwt : w⁻¹ * t * w = t * u)
    (hwu : w * u = u * w) (hau : a * u = u * a) (hb : a * t⁻¹ * w = w * (a * t⁻¹)) : c = u := by
  have h1 : a * w = c * w * a := by rw [← hc]; group
  have h2' : w⁻¹ * t⁻¹ * w = u⁻¹ * t⁻¹ := by
    calc w⁻¹ * t⁻¹ * w = (w⁻¹ * t * w)⁻¹ := by group
      _ = (t * u)⁻¹ := by rw [hwt]
      _ = u⁻¹ * t⁻¹ := by group
  have h2 : t⁻¹ * w = w * (u⁻¹ * t⁻¹) := by
    calc t⁻¹ * w = w * (w⁻¹ * t⁻¹ * w) := by group
      _ = w * (u⁻¹ * t⁻¹) := by rw [h2']
  have h3 : a * u⁻¹ = u⁻¹ * a := (Commute.inv_right (show Commute a u from hau))
  have h4 : a * t⁻¹ * w = (c * w * u⁻¹) * (a * t⁻¹) := by
    calc a * t⁻¹ * w = a * (t⁻¹ * w) := by group
      _ = a * (w * (u⁻¹ * t⁻¹)) := by rw [h2]
      _ = (a * w) * (u⁻¹ * t⁻¹) := by group
      _ = (c * w * a) * (u⁻¹ * t⁻¹) := by rw [h1]
      _ = c * w * (a * u⁻¹) * t⁻¹ := by group
      _ = c * w * (u⁻¹ * a) * t⁻¹ := by rw [h3]
      _ = (c * w * u⁻¹) * (a * t⁻¹) := by group
  have h5 : c * w * u⁻¹ = w := mul_right_cancel (h4.symm.trans hb)
  calc c = (c * w * u⁻¹) * u * w⁻¹ := by group
    _ = w * u * w⁻¹ := by rw [h5]
    _ = u * w * w⁻¹ := by rw [hwu]
    _ = u := by group

theorem sixH_h7_no_t (hS : SCSetting L K n φ t i) {a : G} (ha : a ∈ A φ i)
    (hc : ∀ k ∈ Kc φ t i.swap, k * (a * t⁻¹) = (a * t⁻¹) * k) : False := by
  have h := hS.fc
  have hu1 : RootAxisTwoCore.coordG φ i.swap 1 ≠ 1 := fun e1 =>
    one_ne_zero (RootAxisTwoCore.coordG_injective φ i.swap
      (e1.trans (RootAxisTwoCore.coordG_zero φ i.swap).symm))
  have huU : RootAxisTwoCore.coordG φ i.swap 1 ∈ U φ i.swap :=
    RootAxisTwoCore.coordG_mem φ i.swap 1
  obtain ⟨w, hw, -, hwt, hwu⟩ := RootStandard.exists_W_kappa h i.swap huU
  have hwF : w ∈ F φ t ⊓ D φ t i.swap := FullCenterTorus.W_le_Fi h i.swap hw
  have hwK : w ∈ Kc φ t i.swap := Subgroup.mem_sup_right hwF
  have hcm : a * w * a⁻¹ * w⁻¹ ∈ ⁅A φ i, F φ t ⊓ D φ t i.swap⁆ :=
    Subgroup.commutator_mem_commutator ha hwF
  rw [((FullCenterWeyl.cross_dich h i).resolve_left hS.ne_bot).1] at hcm
  have hZ : RootAxisTwoCore.coordG φ i.swap 1 ∈ Z₀ φ :=
    pull_mono φ (FullCenter.rootU_le_center (K := K) i.swap) huU
  have hau : a * RootAxisTwoCore.coordG φ i.swap 1 = RootAxisTwoCore.coordG φ i.swap 1 * a :=
    FullCenterTorus.comm_ZP h (FullCenterWeyl.A_le_H h i ha) hZ
  have hcu := sixH_h7_alg (c := a * w * a⁻¹ * w⁻¹) rfl hwt hwu hau (hc w hwK).symm
  have hbot : RootAxisTwoCore.coordG φ i.swap 1 ∈ U φ i ⊓ U φ i.swap :=
    Subgroup.mem_inf.mpr ⟨hcu ▸ hcm, huU⟩
  rw [FullCenterTorus.U_inf_U_swap (φ := φ) i, Subgroup.mem_bot] at hbot
  exact hu1 hbot

theorem sixH_h7_t_normalizes_A (hS : SCSetting L K n φ t i) :
    t ∈ normalizer (A φ i : Set G) :=
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun _ ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (FullCenterWeyl.A_le_C hS.fc i ha))

theorem sixH_h7_core (hS : SCSetting L K n φ t i) {b : G} (hb : b ∈ A φ i ⊔ zpowers t)
    (hc : ∀ k ∈ Kc φ t i.swap, k * b = b * k) : b ∈ Z₀ φ := by
  have h := hS.fc
  rcases SixG.mem_or_mul_t_mem h (sixH_h7_t_normalizes_A hS) hb with hA | hA
  · obtain ⟨x, hx, hxZ⟩ := FullCenterWeyl.exists_Fi_not_ZP h i.swap
    have hxK : x ∈ Kc φ t i.swap := Subgroup.mem_sup_right hx
    have hax : b ∈ A φ i ⊓ centralizer ({x} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hA, Subgroup.mem_centralizer_singleton_iff.mpr (hc x hxK).symm⟩
    rwa [(FullCenterWeyl.centers_of_ne_bot h i hS.ne_bot).2.2 x hx hxZ] at hax
  · exfalso
    refine sixH_h7_no_t hS hA fun k hk => ?_
    rw [mul_inv_cancel_right]
    exact hc k hk

theorem sixH_h7_Fw_le (hS : SCSetting L K n φ t i) : Fw φ t i.swap ≤ Mhat φ t i i.swap :=
  (Subgroup.map_mono (NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot)).trans le_sup_right

theorem sixH_h7_Kj_le (hS : SCSetting L K n φ t i) : Kc φ t i.swap ≤ Mhat φ t i i.swap :=
  (SixG.K_le_Cstar hS.fc i hS.ne_bot hS.eq_bot).trans (sup_le le_sup_left (sixH_h7_Fw_le hS))

theorem sixH_h7_Z_le (hS : SCSetting L K n φ t i) : Z₀ φ ≤ Mhat φ t i i.swap :=
  (pull_mono φ (FullCenter.center_le_rootA (K := K) i.swap)).trans
    (le_sup_left.trans (sixH_h7_Kj_le hS))

theorem sixH_h7_Astar_le (hS : SCSetting L K n φ t i) :
    Astar φ t i ≤ Mhat φ t i i.swap ⊔ A φ i := by
  have hFM : F φ t ≤ Mc φ t i := NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot
  have hMM : Mc φ t i ≤ Mhat φ t i i.swap := le_sup_left
  have hKi : Kc φ t i ≤ Mhat φ t i i.swap ⊔ A φ i :=
    sup_le le_sup_right ((inf_le_left.trans (hFM.trans hMM)).trans le_sup_left)
  have hKs : Kstar φ t ≤ Mhat φ t i i.swap ⊔ A φ i := by
    have e : Kstar φ t = Kc φ t i ⊔ Kc φ t i.swap := by
      cases i
      · rfl
      · exact sup_comm _ _
    rw [e]
    exact sup_le hKi ((sixH_h7_Kj_le hS).trans le_sup_left)
  exact sup_le (sup_le (hMM.trans le_sup_left) hKs) ((sixH_h7_Fw_le hS).trans le_sup_left)

theorem sixH_h7_T0_le (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i) :
    T₀ φ t i.swap ≤ Mhat φ t i i.swap ⊔ (A φ i ⊔ zpowers t) := by
  have hP : P₂ φ t i.swap = Mhat φ t i i.swap ⊔ zpowers t :=
    (SixF.Mhat_sup_t_swap hS.fc i hS.ne_bot hS.eq_bot).symm
  rw [sixH_h5_T0_eq hS hM2, hP]
  exact sup_le ((sixH_h7_Astar_le hS).trans (sup_le_sup_left le_sup_left _))
    (sup_le le_sup_left (le_sup_of_le_right le_sup_right))

theorem sixH_h7 (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1 : H1Concl φ t i) (h5 : H5Concl φ t i) (h6 : H6Concl φ t i) : H7Concl φ t i := by
  have h := hS.fc
  unfold H5Concl at h5
  unfold H6Concl at h6
  have hMT : Mhat φ t i i.swap ≤ T₀ φ t i.swap := h5.1
  have hT0N : T₀ φ t i.swap ≤ normalizer (Mhat φ t i i.swap : Set G) :=
    sixH_h5_le_normalizer_of_conj fun g hg c hc =>
      (Subgroup.normal_subgroupOf_iff hMT).mp h5.2 c g hc hg
  have hKsA : Kstar φ t ≤ Astar φ t i := (le_sup_right : Kstar φ t ≤ Mc φ t i ⊔ Kstar φ t).trans
    le_sup_left
  have hKiKs : Kc φ t i ≤ Kstar φ t := by
    cases i
    · exact le_sup_left
    · exact le_sup_right
  have hAT : A φ i ≤ T₀ φ t i.swap :=
    ((le_sup_left : A φ i ≤ Kc φ t i).trans hKiKs).trans
      (hKsA.trans ((SixG.Astar_le_T₂ h i hS.ne_bot hS.eq_bot).trans inf_le_left))
  have htT : zpowers t ≤ T₀ φ t i.swap :=
    zpowers_le.mpr ((le_sup_right : P₂ φ t i.swap ≤ T₀ φ t i.swap)
      (NextCores.t_mem_P₂ h i hS.ne_bot hS.eq_bot))
  have hB : A φ i ⊔ zpowers t ≤ normalizer (Mhat φ t i i.swap : Set G) :=
    (sup_le hAT htT).trans hT0N
  have hEq : centralizer (Kc φ t i.swap : Set G) ⊓ T₀ φ t i.swap = Mhat φ t i i.swap := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨hxC, hxT⟩ := Subgroup.mem_inf.mp hx
      have hxS := sixH_h7_T0_le hS hM2 hxT
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hB] at hxS
      obtain ⟨m, hm, b, hb, rfl⟩ := Set.mem_mul.mp hxS
      have hbC : ∀ k ∈ Kc φ t i.swap, k * b = b * k := by
        intro k hk
        have e1 := Subgroup.mem_centralizer_iff.mp hxC k hk
        have e2 := h6 k hk m hm
        apply mul_left_cancel (a := m)
        calc m * (k * b) = (m * k) * b := (mul_assoc _ _ _).symm
          _ = (k * m) * b := by rw [e2]
          _ = k * (m * b) := mul_assoc _ _ _
          _ = m * b * k := e1
          _ = m * (b * k) := mul_assoc _ _ _
      exact mul_mem hm (sixH_h7_Z_le hS (sixH_h7_core hS hb hbC))
    · exact Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_centralizer_iff.mpr fun k hk => h6 k hk x hx, hMT hx⟩
  have hKn := SixG.normalIn_K h i hS.ne_bot hS.eq_bot hM2
  have hNK : Tplus φ t i ≤ normalizer (Kc φ t i.swap : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKn.1).mp hKn.2.1
  have hNT : Tplus φ t i ≤ normalizer (T₀ φ t i.swap : Set G) :=
    SixG.Tplus_le_normalizer_T₀ h i hS.ne_bot hS.eq_bot hM2
  have hTN := sixH_g4_normalizer hNK hNT
  rw [hEq] at hTN
  exact ⟨hEq, SixG.normalIn_of (hMT.trans le_sup_right) hTN
    (SixF.J_le_normalizer_Mhat_swap h i hS.ne_bot hS.eq_bot)⟩

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
