module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixHSecond
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixHCenterB

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Steps

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

open scoped Pointwise

theorem sixH_h8_t_ne_one (h : FullCenter.FCHyp L K n φ t) : t ≠ 1 := by
  intro ht
  exact h.not_conj 1 (by simp [ht])

theorem sixH_h8_t_mul_t (h : FullCenter.FCHyp L K n φ t) : t * t = 1 :=
  h.setup.t_mul_t

theorem sixH_h8_Mhat_le_Tplus (hS : SCSetting L K n φ t i) :
    Mhat φ t i i ≤ Tplus φ t i := by
  have e1 : Mc φ t i ⊔ Mw φ t i i ≤ P₁ φ t i :=
    SixF.Mhat_le_P₁ hS.fc i hS.ne_bot hS.eq_bot
  have h1 : P₁ φ t i ≤ T₁ φ t i := le_sup_right
  have h2 : T₁ φ t i ≤ Tbar φ t i := le_sup_left
  have h3 : Tbar φ t i ≤ Tplus φ t i := le_sup_left
  exact e1.trans (h1.trans (h2.trans h3))

theorem sixH_h8_inf_P2 (hS : SCSetting L K n φ t i) :
    Mhat φ t i i ⊓ P₂ φ t i.swap = Mc φ t i := by
  have eP0 : Mc φ t i ⊔ zpowers t = P₀ φ t i :=
    NextCores.M_sup_t hS.fc i hS.ne_bot hS.eq_bot
  have einf : (Mc φ t i ⊔ Mw φ t i i) ⊓ zpowers t = ⊥ :=
    SixF.Mhat_inf_t hS.fc i hS.ne_bot hS.eq_bot
  have hLE : zpowers t ≤ normalizer (Mc φ t i : Set G) :=
    zpowers_le.mpr (NextCores.t_mem_normalizer_M hS.fc i hS.ne_bot hS.eq_bot)
  have eprod : ((Mc φ t i ⊔ zpowers t : Subgroup G) : Set G) =
      (Mc φ t i : Set G) * (zpowers t : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hLE
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM, hxP⟩ := mem_inf.mp hx
    have hxP₁ : x ∈ P₁ φ t i := SixF.Mhat_le_P₁ hS.fc i hS.ne_bot hS.eq_bot hxM
    have hx0 : x ∈ (Mc φ t i ⊔ zpowers t : Subgroup G) := by
      rw [eP0]
      exact ⟨hxP₁, hxP⟩
    have hx1 : x ∈ (Mc φ t i : Set G) * (zpowers t : Set G) := by
      rw [← eprod]
      exact hx0
    obtain ⟨m, hm, b, hb, hmb⟩ := Set.mem_mul.mp hx1
    have hb' : b = m⁻¹ * x := by rw [← hmb, inv_mul_cancel_left]
    have hbM : b ∈ Mhat φ t i i := by
      rw [hb']
      exact mul_mem (inv_mem ((le_sup_left : Mc φ t i ≤ Mhat φ t i i) hm)) hxM
    have hb1 : b = 1 := by
      have h0 : b ∈ (⊥ : Subgroup G) := by
        rw [← einf]
        exact ⟨hbM, hb⟩
      exact Subgroup.mem_bot.mp h0
    rw [← hmb, hb1, mul_one]
    exact hm
  · exact le_inf le_sup_left (SixF.M_le_P₂ hS.fc i)

theorem sixH_h8_inf_swap (hS : SCSetting L K n φ t i) :
    Mhat φ t i i ⊓ Mhat φ t i i.swap = Mc φ t i := by
  apply le_antisymm
  · have h1 : Mhat φ t i i ⊓ Mhat φ t i i.swap ≤ Mhat φ t i i ⊓ P₂ φ t i.swap :=
      inf_le_inf_left _ (SixF.Mhat_le_P₂ hS.fc i)
    rw [sixH_h8_inf_P2 hS] at h1
    exact h1
  · exact le_inf le_sup_left le_sup_left

theorem sixH_h8_one_two (hS : SCSetting L K n φ t i) :
    Mhat φ t i Axis.one ⊓ Mhat φ t i Axis.two = Mc φ t i := by
  cases i with
  | one => exact sixH_h8_inf_swap hS
  | two => rw [inf_comm]; exact sixH_h8_inf_swap hS

theorem sixH_h8_S_eq : S φ t i = Mhat φ t i i ⊔ Mhat φ t i i.swap := by
  cases i with
  | one => rfl
  | two => exact sup_comm _ _

theorem sixH_h8_t_mem_normalizer_S (hS : SCSetting L K n φ t i) :
    t ∈ normalizer ((S φ t i : Subgroup G) : Set G) := by
  rw [sixH_h8_S_eq]
  exact Subgroup.inf_normalizer_le_normalizer_sup _ _ (Subgroup.mem_inf.mpr
    ⟨SixF.t_mem_normalizer_Mhat hS.fc i hS.ne_bot hS.eq_bot,
      SixF.t_mem_normalizer_Mhat_swap hS.fc i hS.ne_bot hS.eq_bot⟩)

theorem sixH_h8_Mhat_swap_le_Tplus (h7 : H7Concl φ t i) : Mhat φ t i i.swap ≤ Tplus φ t i := by
  obtain ⟨-, hX⟩ := h7
  obtain ⟨hXT, -, -⟩ := hX
  exact hXT

theorem sixH_h8_hBN (hS : SCSetting L K n φ t i) (h7 : H7Concl φ t i) :
    Mhat φ t i i ≤ normalizer (Mhat φ t i i.swap : Set G) := by
  obtain ⟨-, hX⟩ := h7
  obtain ⟨hXT, hXN, -⟩ := hX
  exact (sixH_h8_Mhat_le_Tplus hS).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hXT).mp hXN)

theorem sixH_h8_S_le_Tplus (hS : SCSetting L K n φ t i) (h7 : H7Concl φ t i) :
    S φ t i ≤ Tplus φ t i := by
  rw [sixH_h8_S_eq]
  exact sup_le (sixH_h8_Mhat_le_Tplus hS) (sixH_h8_Mhat_swap_le_Tplus h7)

theorem sixH_h8_card_S (hS : SCSetting L K n φ t i) (h7 : H7Concl φ t i) :
    Nat.card (S φ t i) = Nat.card K ^ 10 := by
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (sixH_h8_hBN hS h7)
  have c1 : Nat.card (Mhat φ t i i) = Nat.card K ^ 7 :=
    SixF.card_Mhat hS.fc i hS.ne_bot hS.eq_bot
  have c2 : Nat.card (Mhat φ t i i.swap) = Nat.card K ^ 8 :=
    SixF.card_Mhat_swap hS.fc i hS.ne_bot hS.eq_bot
  have c3 : Nat.card (Mc φ t i) = Nat.card K ^ 5 :=
    NextCores.card_M hS.fc i hS.ne_bot hS.eq_bot
  have hinf : Mhat φ t i i.swap ⊓ Mhat φ t i i = Mc φ t i := by
    rw [inf_comm]
    exact sixH_h8_inf_swap hS
  have hsup : Mhat φ t i i.swap ⊔ Mhat φ t i i = S φ t i := by
    rw [sixH_h8_S_eq]
    exact sup_comm _ _
  rw [hinf, hsup, c1, c2, c3] at hcard
  have hq : 0 < Nat.card K ^ 5 := pow_pos Nat.card_pos 5
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [hcard]
  ring

theorem sixH_h8_t_not_mem_S (hS : SCSetting L K n φ t i) (h7 : H7Concl φ t i) :
    t ∉ S φ t i := by
  intro ht
  have hprod : ((Mhat φ t i i ⊔ Mhat φ t i i.swap : Subgroup G) : Set G) =
      (Mhat φ t i i : Set G) * (Mhat φ t i i.swap : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (sixH_h8_hBN hS h7)
  rw [sixH_h8_S_eq] at ht
  have ht' : t ∈ ((Mhat φ t i i ⊔ Mhat φ t i i.swap : Subgroup G) : Set G) := ht
  rw [hprod] at ht'
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp ht'
  have ha' : a ∈ Mhat φ t i i := ha
  have hb' : b ∈ Mhat φ t i i.swap := hb
  have hbP : b ∈ P₂ φ t i.swap := (SixF.Mhat_le_P₂ hS.fc i) hb'
  have htP : t ∈ P₂ φ t i.swap := NextCores.t_mem_P₂ hS.fc i hS.ne_bot hS.eq_bot
  have haP : a ∈ P₂ φ t i.swap := by
    have e : a = t * b⁻¹ := eq_mul_inv_of_mul_eq hab
    rw [e]
    exact mul_mem htP (inv_mem hbP)
  have haM : a ∈ Mc φ t i := by
    have h0 : a ∈ Mhat φ t i i ⊓ P₂ φ t i.swap := Subgroup.mem_inf.mpr ⟨ha', haP⟩
    rw [sixH_h8_inf_P2 hS] at h0
    exact h0
  have htM : t ∈ Mhat φ t i i.swap := by
    have h0 : a * b ∈ Mhat φ t i i.swap :=
      mul_mem ((le_sup_left : Mc φ t i ≤ Mhat φ t i i.swap) haM) hb'
    rw [hab] at h0
    exact h0
  have hinf0 : Mhat φ t i i.swap ⊓ zpowers t = ⊥ :=
    SixF.Mhat_inf_t_swap hS.fc i hS.ne_bot hS.eq_bot
  have h0 : t ∈ Mhat φ t i i.swap ⊓ zpowers t := Subgroup.mem_inf.mpr ⟨htM, mem_zpowers t⟩
  rw [hinf0] at h0
  exact sixH_h8_t_ne_one hS.fc (Subgroup.mem_bot.mp h0)

theorem sixH_h8_inf_t (hS : SCSetting L K n φ t i) (h7 : H7Concl φ t i) :
    S φ t i ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxS, hxt⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxt
  rw [Subgroup.mem_bot]
  rcases RootAxisTwoCore.zpow_eq_one_or_eq (sixH_h8_t_mul_t hS.fc) k with h | h
  · rw [hk] at h
    exact h
  · rw [hk] at h
    rw [h] at hxS
    exact absurd hxS (sixH_h8_t_not_mem_S hS h7)

theorem sixH_h8_sup_t (hS : SCSetting L K n φ t i) (h7 : H7Concl φ t i)
    (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i) :
    S φ t i ⊔ zpowers t = Tplus φ t i := by
  have htT : t ∈ Tplus φ t i :=
    ((le_sup_right : P₂ φ t i.swap ≤ T₀ φ t i.swap).trans
      (le_sup_right : T₀ φ t i.swap ≤ Tplus φ t i))
      (NextCores.t_mem_P₂ hS.fc i hS.ne_bot hS.eq_bot)
  have htZ : zpowers t ≤ normalizer ((S φ t i : Subgroup G) : Set G) :=
    zpowers_le.mpr (sixH_h8_t_mem_normalizer_S hS)
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer htZ
  have ht2 : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact sixH_h8_t_mul_t hS.fc)
      (sixH_h8_t_ne_one hS.fc)
  rw [sixH_h8_inf_t hS h7, Subgroup.card_bot, ht2, sixH_h8_card_S hS h7, mul_one] at hcard
  have hX : Nat.card (S φ t i ⊔ zpowers t : Subgroup G) = 2 * Nat.card K ^ 10 :=
    hcard.trans (mul_comm _ _)
  have hle : S φ t i ⊔ zpowers t ≤ Tplus φ t i :=
    sup_le (sixH_h8_S_le_Tplus hS h7) (zpowers_le.mpr htT)
  have hcT : Nat.card (Tplus φ t i) = 2 * Nat.card K ^ 10 :=
    SixG.card_Tplus hS.fc i hS.ne_bot hS.eq_bot hM2
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hcT.trans hX.symm))

theorem sixH_h8_normal (hS : SCSetting L K n φ t i) (h7 : H7Concl φ t i)
    (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i) :
    ((S φ t i).subgroupOf (Tplus φ t i)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (sixH_h8_S_le_Tplus hS h7),
    ← sixH_h8_sup_t hS h7 hM2]
  exact sup_le Subgroup.le_normalizer (zpowers_le.mpr (sixH_h8_t_mem_normalizer_S hS))

theorem sixH_h8 (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h7 : H7Concl φ t i) : H8Concl φ t i := by
  unfold H8Concl
  exact ⟨sixH_h8_inf_P2 hS, sixH_h8_one_two hS, sixH_h8_card_S hS h7,
    sixH_h8_sup_t hS h7 hM2, sixH_h8_inf_t hS h7, sixH_h8_normal hS h7 hM2⟩

theorem sixH_h9_axis_cases (i k : Axis) : k = i ∨ k = i.swap := by
  cases i <;> cases k <;> simp [Axis.swap]

theorem sixH_h9_swap_swap (i : Axis) : i.swap.swap = i := by cases i <;> rfl

theorem sixH_h9_U_central (h1 : H1Concl φ t i) {u g : G} (hu : u ∈ U φ i)
    (hg : g ∈ Tplus φ t i) : g * u = u * g := by
  rw [← h1] at hu
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hu
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨g, hg⟩)

theorem sixH_h9_Cu {T N : Subgroup G} (hN : ∀ u ∈ N, ∀ g ∈ T, g * u = u * g) (y : G) :
    ∃ C : Subgroup G, ∀ z, z ∈ C ↔ z ∈ T ∧ z⁻¹ * y⁻¹ * z * y ∈ N := by
  refine ⟨{ carrier := {z | z ∈ T ∧ z⁻¹ * y⁻¹ * z * y ∈ N}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun z => Iff.rfl⟩
  · rintro a b ⟨haT, ha⟩ ⟨hbT, hb⟩
    refine ⟨mul_mem haT hbT, ?_⟩
    have e : (a * b)⁻¹ * y⁻¹ * (a * b) * y =
        (b⁻¹ * (a⁻¹ * y⁻¹ * a * y) * b) * (b⁻¹ * y⁻¹ * b * y) := by group
    have hc : b⁻¹ * (a⁻¹ * y⁻¹ * a * y) * b = a⁻¹ * y⁻¹ * a * y := by
      rw [mul_assoc, ← hN _ ha b hbT, inv_mul_cancel_left]
    rw [e, hc]
    exact mul_mem ha hb
  · refine ⟨one_mem T, ?_⟩
    simp
  · rintro z ⟨hzT, hz⟩
    refine ⟨inv_mem hzT, ?_⟩
    have e : (z⁻¹)⁻¹ * y⁻¹ * z⁻¹ * y = z * (z⁻¹ * y⁻¹ * z * y)⁻¹ * z⁻¹ := by group
    have hc : z * (z⁻¹ * y⁻¹ * z * y)⁻¹ * z⁻¹ = (z⁻¹ * y⁻¹ * z * y)⁻¹ := by
      rw [hN _ (inv_mem hz) z hzT, mul_assoc, mul_inv_cancel, mul_one]
    show (z⁻¹)⁻¹ * y⁻¹ * z⁻¹ * y ∈ N
    rw [e, hc]
    exact inv_mem hz

theorem sixH_h9_exists_A_not_Z (h : FullCenter.FCHyp L K n φ t) (k : Axis) :
    ∃ y ∈ A φ k, y ∉ Z₀ φ := by
  haveI : Nontrivial (U φ k.swap) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [FullCenter.FCHyp.card_U (φ := φ) k.swap]
    exact SixG.one_lt_card_K h
  obtain ⟨u, hu⟩ := exists_ne (1 : U φ k.swap)
  have := (sixH_s2_weyl (φ := φ) k).2 u.1 u.2 (fun h1 => hu (Subtype.ext h1))
  exact ⟨_, this.1, this.2⟩

theorem sixH_h9_comm (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1 : H1Concl φ t i) (h2a : H2aConcl φ t i) (h3 : H3Concl φ t i) (h6 : H6Concl φ t i)
    {m y : G} (hm : m ∈ Mc φ t i) (hy : y ∈ Bstar φ t i) : m⁻¹ * y⁻¹ * m * y ∈ U φ i := by
  have hB := SixG.normalIn_Bstar hS.fc i hS.ne_bot hS.eq_bot hM2
  have hBT : Bstar φ t i ≤ Tplus φ t i := hB.1
  have hMB : Mc φ t i ≤ Bstar φ t i := le_sup_left
  obtain ⟨C, hC⟩ := sixH_h9_Cu (T := Tplus φ t i) (N := U φ i)
    (fun u hu g hg => sixH_h9_U_central h1 hu hg) m
  have hK : ∀ k : Axis, Kc φ t k ≤ C := by
    intro k z hz
    have hzB : z ∈ Bstar φ t i := by
      have hk : Kc φ t k ≤ Kstar φ t := by
        cases k
        · exact le_sup_left
        · exact le_sup_right
      exact (le_sup_right : Kstar φ t ≤ Bstar φ t i) (hk hz)
    refine (hC z).mpr ⟨hBT hzB, ?_⟩
    rcases sixH_h9_axis_cases i k with rfl | rfl
    · exact h3.1 z (sixH_h4a_K_le_Mhat hS hz) m ((le_sup_left : Mc φ t k ≤ Mhat φ t k k) hm)
    · have hc : z * m = m * z :=
        h6 z hz m ((le_sup_left : Mc φ t i ≤ Mhat φ t i i.swap) hm)
      have e : z⁻¹ * m⁻¹ * z * m = (m * z)⁻¹ * (z * m) := by group
      rw [e, hc, inv_mul_cancel]
      exact one_mem _
  have hle : Bstar φ t i ≤ C := by
    refine sup_le (fun z hz => ?_) (sup_le (hK Axis.one) (hK Axis.two))
    exact (hC z).mpr ⟨hBT (hMB hz), h2a.comm_M z hz m hm⟩
  have hyC := ((hC y).mp (hle hy)).2
  have e : m⁻¹ * y⁻¹ * m * y = (y⁻¹ * m⁻¹ * y * m)⁻¹ := by group
  rw [e]
  exact inv_mem hyC

theorem sixH_h9_A_le_normalizer (h : FullCenter.FCHyp L K n φ t) (i : Axis) :
    A φ i.swap ≤ normalizer (A φ i : Set G) :=
  sixH_h5_le_normalizer_of_conj fun _ hx _ ha =>
    FullCenterWeyl.conj_H_mem_A h i (FullCenterWeyl.A_le_H h _ hx) ha

theorem sixH_h9_P_eq (i : Axis) : P φ = A φ i ⊔ A φ i.swap := by
  have h0 : P φ = A φ Axis.one ⊔ A φ Axis.two := FullCenterParabolic.P_eq_A_sup_A
  cases i
  · exact h0
  · rw [h0, sup_comm]
    rfl

theorem sixH_h9_decomp (hS : SCSetting L K n φ t i) {x : G} (hx : x ∈ Bstar φ t i) :
    ∃ m ∈ Mc φ t i, ∃ a ∈ A φ i, ∃ b ∈ A φ i.swap, x = m * (a * b) := by
  have e1 : (Mc φ t i : Set G) * (Kstar φ t : Set G) = (Bstar φ t i : Set G) :=
    SixG.Bstar_mul hS.fc i hS.ne_bot hS.eq_bot
  have hx1 : x ∈ (Mc φ t i : Set G) * (Kstar φ t : Set G) := by
    rw [e1]
    exact hx
  obtain ⟨m₀, hm₀, k, hk, rfl⟩ := Set.mem_mul.mp hx1
  have e2 : (F φ t : Set G) * (P φ : Set G) = (Kstar φ t : Set G) := FullCenterWeyl.F_mul_P hS.fc
  have hk1 : k ∈ (F φ t : Set G) * (P φ : Set G) := by
    rw [e2]
    exact hk
  obtain ⟨f, hf, p, hp, rfl⟩ := Set.mem_mul.mp hk1
  have e3 : ((A φ i ⊔ A φ i.swap : Subgroup G) : Set G) =
      (A φ i : Set G) * (A φ i.swap : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (sixH_h9_A_le_normalizer hS.fc i)
  have hp1 : p ∈ ((A φ i ⊔ A φ i.swap : Subgroup G) : Set G) := by
    rw [← sixH_h9_P_eq i]
    exact hp
  rw [e3] at hp1
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hp1
  exact ⟨m₀ * f, mul_mem hm₀ (NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot hf), a, ha, b, hb,
    by group⟩

theorem sixH_h9_comm_mul_right {a b y : G} (hb : b * y = y * b) :
    (a * b)⁻¹ * y⁻¹ * (a * b) * y = b⁻¹ * (a⁻¹ * y⁻¹ * a * y) * b := by
  calc (a * b)⁻¹ * y⁻¹ * (a * b) * y = b⁻¹ * (a⁻¹ * y⁻¹ * a) * (b * y) := by group
    _ = b⁻¹ * (a⁻¹ * y⁻¹ * a) * (y * b) := by rw [hb]
    _ = b⁻¹ * (a⁻¹ * y⁻¹ * a * y) * b := by group

theorem sixH_h9_comm_mul_left {a b y : G} (ha : a * y = y * a) :
    (a * b)⁻¹ * y⁻¹ * (a * b) * y = b⁻¹ * y⁻¹ * b * y := by
  have h : a⁻¹ * y⁻¹ * a = y⁻¹ := by
    calc a⁻¹ * y⁻¹ * a = (y * a)⁻¹ * a := by group
      _ = (a * y)⁻¹ * a := by rw [ha]
      _ = y⁻¹ := by group
  calc (a * b)⁻¹ * y⁻¹ * (a * b) * y = b⁻¹ * (a⁻¹ * y⁻¹ * a) * b * y := by group
    _ = b⁻¹ * y⁻¹ * b * y := by rw [h]

theorem sixH_h9_not_mem_U {c : G} (h₁ : c ∉ U φ Axis.one) (h₂ : c ∉ U φ Axis.two) :
    c ∉ U φ i := by
  cases i
  · exact h₁
  · exact h₂

theorem sixH_h9_A_le_Bstar (k : Axis) : A φ k ≤ Bstar φ t i := by
  have hk : Kc φ t k ≤ Kstar φ t := by
    cases k
    · exact le_sup_left
    · exact le_sup_right
  exact (le_sup_left : A φ k ≤ Kc φ t k).trans (hk.trans le_sup_right)

theorem sixH_h9_mem_M (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1 : H1Concl φ t i) (h2a : H2aConcl φ t i) (h3 : H3Concl φ t i) (h6 : H6Concl φ t i)
    {x : G} (hxB : x ∈ Bstar φ t i)
    (hx : ∀ y ∈ Bstar φ t i, x⁻¹ * y⁻¹ * x * y ∈ U φ i) : x ∈ Mc φ t i := by
  obtain ⟨m, hm, a, ha, b, hb, rfl⟩ := sixH_h9_decomp hS hxB
  have hB := SixG.normalIn_Bstar hS.fc i hS.ne_bot hS.eq_bot hM2
  have hBT : Bstar φ t i ≤ Tplus φ t i := hB.1
  have hmB : m ∈ Bstar φ t i := (le_sup_left : Mc φ t i ≤ Bstar φ t i) hm
  have hZM : Z₀ φ ≤ Mc φ t i :=
    (FullCenterTorus.ZP_le_F hS.fc).trans (NextCores.F_le_M hS.fc i hS.ne_bot hS.eq_bot)
  have hab : ∀ y ∈ Bstar φ t i, (a * b)⁻¹ * y⁻¹ * (a * b) * y ∈ U φ i := by
    intro y hy
    obtain ⟨C, hC⟩ := sixH_h9_Cu (T := Tplus φ t i) (N := U φ i)
      (fun u hu g hg => sixH_h9_U_central h1 hu hg) y
    have hxC : m * (a * b) ∈ C := (hC _).mpr ⟨hBT hxB, hx y hy⟩
    have hmC : m ∈ C :=
      (hC _).mpr ⟨hBT hmB, sixH_h9_comm hS hM2 h1 h2a h3 h6 hm hy⟩
    have hbC : a * b ∈ C := by
      have := mul_mem (inv_mem hmC) hxC
      simpa using this
    exact ((hC _).mp hbC).2
  have haZ : a ∈ Z₀ φ := by
    by_contra haZ
    obtain ⟨y, hy, hyZ⟩ := sixH_h9_exists_A_not_Z hS.fc i.swap
    have hu := hab y (sixH_h9_A_le_Bstar _ hy)
    have hbc : b * y = y * b := FullCenterRadical.A_mul_comm hS.fc i.swap hb hy
    rw [sixH_h9_comm_mul_right hbc] at hu
    have hbT : b ∈ Tplus φ t i := hBT (sixH_h9_A_le_Bstar _ hb)
    have hcU : a⁻¹ * y⁻¹ * a * y ∈ U φ i := by
      have e : a⁻¹ * y⁻¹ * a * y = b * (b⁻¹ * (a⁻¹ * y⁻¹ * a * y) * b) * b⁻¹ := by group
      rw [e, sixH_h9_U_central h1 hu hbT, mul_inv_cancel_right]
      exact hu
    have hS1 := sixH_s1_pairing i ha haZ hy hyZ
    exact sixH_h9_not_mem_U hS1.2.1 hS1.2.2 hcU
  have hbZ : b ∈ Z₀ φ := by
    by_contra hbZ
    obtain ⟨y, hy, hyZ⟩ := sixH_h9_exists_A_not_Z hS.fc i
    have hu := hab y (sixH_h9_A_le_Bstar _ hy)
    have hac : a * y = y * a := FullCenterRadical.A_mul_comm hS.fc i ha hy
    rw [sixH_h9_comm_mul_left hac] at hu
    have hS1 := sixH_s1_pairing i.swap hb hbZ (by rw [sixH_h9_swap_swap]; exact hy) hyZ
    exact sixH_h9_not_mem_U hS1.2.1 hS1.2.2 hu
  exact mul_mem hm (mul_mem (hZM haZ) (hZM hbZ))

theorem sixH_h9 (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1 : H1Concl φ t i) (h2a : H2aConcl φ t i) (h3 : H3Concl φ t i) (h6 : H6Concl φ t i) :
    H9Concl φ t i := by
  unfold H9Concl
  have hB := SixG.normalIn_Bstar hS.fc i hS.ne_bot hS.eq_bot hM2
  have hBT : Bstar φ t i ≤ Tplus φ t i := hB.1
  have hMB : Mc φ t i ≤ Bstar φ t i := le_sup_left
  have hMT : Mc φ t i ≤ Tplus φ t i := hMB.trans hBT
  refine ⟨hMT, ?_, NextCores.J_le_normalizer_M hS.fc i hS.ne_bot hS.eq_bot⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMT]
  have hBN : Tplus φ t i ≤ normalizer (Bstar φ t i : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBT).mp hB.2.1
  refine sixH_h5_le_normalizer_of_conj fun g hg x hx => ?_
  have hxB : x ∈ Bstar φ t i := hMB hx
  refine sixH_h9_mem_M hS hM2 h1 h2a h3 h6
    ((Subgroup.mem_normalizer_iff.mp (hBN hg) x).mp hxB) fun y hy => ?_
  have hy' : g⁻¹ * y * g ∈ Bstar φ t i := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hBN (inv_mem hg)) y).mp hy
  have hc := sixH_h9_comm hS hM2 h1 h2a h3 h6 hx hy'
  have e : (g * x * g⁻¹)⁻¹ * y⁻¹ * (g * x * g⁻¹) * y =
      g * (x⁻¹ * (g⁻¹ * y * g)⁻¹ * x * (g⁻¹ * y * g)) * g⁻¹ := by group
  rw [e, sixH_h9_U_central h1 hc hg, mul_inv_cancel_right]
  exact hc

theorem sixH_h10_w_mul (k : Axis) : w φ k * w φ k = 1 := FullCenterWeyl.w_mul_self (φ := φ) k

theorem sixH_h10_M_conj (h7 : H7Concl φ t i) (h9 : H9Concl φ t i) {g y : G}
    (hg : g ∈ Mhat φ t i i.swap) (hy : y ∈ Mc φ t i) : g * y * g⁻¹ ∈ Mc φ t i := by
  have hgT : g ∈ Tplus φ t i := sixH_h8_Mhat_swap_le_Tplus h7 hg
  have hN : Tplus φ t i ≤ normalizer (Mc φ t i : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h9.1).mp h9.2.1
  exact (Subgroup.mem_normalizer_iff.mp (hN hgT) y).mp hy

theorem sixH_h10_Mw_conj (h7 : H7Concl φ t i) (h9 : H9Concl φ t i) {g x : G}
    (hg : g ∈ Mhat φ t i i.swap) (hx : x ∈ Mw φ t i i.swap) :
    g * x * g⁻¹ ∈ Mw φ t i i.swap := by
  rw [FullCenterWeyl.mem_map_conj_inv] at hx ⊢
  have hwN : w φ i.swap ∈ normalizer ((Mhat φ t i i.swap : Subgroup G) : Set G) :=
    SixF.w_mem_normalizer_Mhat' i i.swap
  have hgw : w φ i.swap * g * (w φ i.swap)⁻¹ ∈ Mhat φ t i i.swap :=
    (Subgroup.mem_normalizer_iff.mp hwN g).mp hg
  have h := sixH_h10_M_conj h7 h9 hgw hx
  have e : w φ i.swap * (g * x * g⁻¹) * (w φ i.swap)⁻¹ =
      (w φ i.swap * g * (w φ i.swap)⁻¹) * (w φ i.swap * x * (w φ i.swap)⁻¹) *
        (w φ i.swap * g * (w φ i.swap)⁻¹)⁻¹ := by group
  rw [e]
  exact h

theorem sixH_h10_comm_Mw_M (hS : SCSetting L K n φ t i) (h7 : H7Concl φ t i)
    (h9 : H9Concl φ t i) {m' u : G} (hm' : m' ∈ Mw φ t i i.swap) (hu : u ∈ Mc φ t i) :
    m'⁻¹ * u⁻¹ * m' * u ∈ Wk φ t i.swap := by
  have hW : Mc φ t i ⊓ Mw φ t i i.swap = Wk φ t i.swap :=
    SixF.M_inf_Mw_swap hS.fc i hS.ne_bot hS.eq_bot
  rw [← hW]
  have hm'H : m' ∈ Mhat φ t i i.swap := (le_sup_right : Mw φ t i i.swap ≤ Mhat φ t i i.swap) hm'
  have huH : u⁻¹ ∈ Mhat φ t i i.swap :=
    inv_mem ((le_sup_left : Mc φ t i ≤ Mhat φ t i i.swap) hu)
  have hA : m'⁻¹ * u⁻¹ * m' * u ∈ Mc φ t i := by
    have h := sixH_h10_M_conj h7 h9 (inv_mem hm'H) (inv_mem hu)
    have e : m'⁻¹ * u⁻¹ * m' * u = (m'⁻¹ * u⁻¹ * m'⁻¹⁻¹) * u := by group
    rw [e]
    exact mul_mem h hu
  have hB : m'⁻¹ * u⁻¹ * m' * u ∈ Mw φ t i i.swap := by
    have h := sixH_h10_Mw_conj h7 h9 huH hm'
    have e : m'⁻¹ * u⁻¹ * m' * u = m'⁻¹ * (u⁻¹ * m' * u⁻¹⁻¹) := by group
    rw [e]
    exact mul_mem (inv_mem hm') h
  exact Subgroup.mem_inf.mpr ⟨hA, hB⟩

theorem sixH_h10_U_inf_W (hS : SCSetting L K n φ t i) (h2d : H2dConcl φ t i) {x : G}
    (hxU : x ∈ U φ i) (hxW : x ∈ Wk φ t i.swap) : x = 1 := by
  have hxV : x ∈ Vtor φ t i i := by
    rw [← h2d.1] at hxU
    obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.mp hxU
    exact c.2
  have h0 : x ∈ Vtor φ t i i ⊓ Wk φ t i.swap := Subgroup.mem_inf.mpr ⟨hxV, hxW⟩
  rw [RootStandard.V_inf_W_swap hS.fc i hS.ne_bot hS.eq_bot] at h0
  exact Subgroup.mem_bot.mp h0

theorem sixH_h10_central_M (hS : SCSetting L K n φ t i) (h1 : H1Concl φ t i)
    (h2a : H2aConcl φ t i) (h2d : H2dConcl φ t i) (h7 : H7Concl φ t i) (h9 : H9Concl φ t i)
    {m m' : G} (hm : m ∈ Mc φ t i) (hm' : m' ∈ Mw φ t i i.swap)
    (hz : ∀ g ∈ Mhat φ t i i.swap, (m * m') * g = g * (m * m')) :
    ∀ u ∈ Mc φ t i, m * u = u * m := by
  intro u hu
  have huH : u ∈ Mhat φ t i i.swap := (le_sup_left : Mc φ t i ≤ Mhat φ t i i.swap) hu
  have hm'H : m' ∈ Mhat φ t i i.swap := (le_sup_right : Mw φ t i i.swap ≤ Mhat φ t i i.swap) hm'
  have hm'T : m' ∈ Tplus φ t i := sixH_h8_Mhat_swap_le_Tplus h7 hm'H
  have hdU : m⁻¹ * u⁻¹ * m * u ∈ U φ i := h2a.comm_M m hm u hu
  have hcW : m'⁻¹ * u⁻¹ * m' * u ∈ Wk φ t i.swap := sixH_h10_comm_Mw_M hS h7 h9 hm' hu
  have e1 : (m * m')⁻¹ * u⁻¹ * (m * m') * u =
      (m'⁻¹ * (m⁻¹ * u⁻¹ * m * u) * m') * (m'⁻¹ * u⁻¹ * m' * u) := by group
  have e2 : (m * m')⁻¹ * u⁻¹ * (m * m') * u = 1 := by
    calc (m * m')⁻¹ * u⁻¹ * (m * m') * u = (m * m')⁻¹ * u⁻¹ * ((m * m') * u) := by group
      _ = (m * m')⁻¹ * u⁻¹ * (u * (m * m')) := by rw [hz u huH]
      _ = 1 := by group
  have e3 : m'⁻¹ * (m⁻¹ * u⁻¹ * m * u) * m' = m⁻¹ * u⁻¹ * m * u := by
    rw [mul_assoc, ← sixH_h9_U_central h1 hdU hm'T, inv_mul_cancel_left]
  rw [e3] at e1
  have hd : m⁻¹ * u⁻¹ * m * u ∈ Wk φ t i.swap := by
    have h := eq_inv_of_mul_eq_one_left (e1.symm.trans e2)
    rw [h]
    exact inv_mem hcW
  have hd1 := sixH_h10_U_inf_W hS h2d hdU hd
  have : (u * m)⁻¹ * (m * u) = 1 := by
    rw [← hd1]
    group
  exact (inv_mul_eq_one.mp this).symm

theorem sixH_h10_Z_M_le_K (hS : SCSetting L K n φ t i) (h2d : H2dConcl φ t i) {m : G}
    (hm : m ∈ Mc φ t i) (hc : ∀ u ∈ Mc φ t i, m * u = u * m) : m ∈ Kc φ t i.swap := by
  obtain ⟨v, hv, y, hy, rfl⟩ := RootStandard.exists_V_mul_W hS.fc i hS.ne_bot hS.eq_bot hm
  have hvU : v ∈ U φ i := by
    rw [← h2d.1]
    refine ⟨⟨v, hv⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    have hgM : (g : G) ∈ Mc φ t i := (Subgroup.mem_inf.mp g.2).1
    have hyg : (g : G) * y = y * g :=
      RootStandard.V_comm_W_swap hS.fc i hS.ne_bot hS.eq_bot g.2 hy
    have h := hc g hgM
    have h' : (v * g) * y = (g * v) * y := by
      calc (v * g) * y = v * (g * y) := by rw [mul_assoc]
        _ = v * (y * g) := by rw [hyg]
        _ = (v * y) * g := by rw [mul_assoc]
        _ = g * (v * y) := h
        _ = (g * v) * y := by rw [mul_assoc]
    exact Subtype.ext (mul_right_cancel h').symm
  exact mul_mem (SixG.U_le_K i i.swap hvU)
    ((FullCenterTorus.W_le_Fi hS.fc i.swap).trans le_sup_right hy)

theorem sixH_h10_w_conj_conj (k : Axis) (x : G) :
    w φ k * (w φ k * x * (w φ k)⁻¹) * (w φ k)⁻¹ = x := by
  have e : w φ k * (w φ k * x * (w φ k)⁻¹) * (w φ k)⁻¹ =
      (w φ k * w φ k) * x * (w φ k * w φ k)⁻¹ := by group
  rw [e, sixH_h10_w_mul k]
  simp

theorem sixH_h10_conj_central {z : G} (hz : ∀ g ∈ Mhat φ t i i.swap, z * g = g * z) :
    ∀ g ∈ Mhat φ t i i.swap, (w φ i.swap * z * (w φ i.swap)⁻¹) * g =
      g * (w φ i.swap * z * (w φ i.swap)⁻¹) := by
  intro g hg
  have hwN : w φ i.swap ∈ normalizer ((Mhat φ t i i.swap : Subgroup G) : Set G) :=
    SixF.w_mem_normalizer_Mhat' i i.swap
  have hg' : (w φ i.swap)⁻¹ * g * w φ i.swap ∈ Mhat φ t i i.swap := by
    refine (Subgroup.mem_normalizer_iff.mp hwN _).mpr ?_
    have e : w φ i.swap * ((w φ i.swap)⁻¹ * g * w φ i.swap) * (w φ i.swap)⁻¹ = g := by group
    rw [e]
    exact hg
  calc (w φ i.swap * z * (w φ i.swap)⁻¹) * g
      = w φ i.swap * (z * ((w φ i.swap)⁻¹ * g * w φ i.swap)) * (w φ i.swap)⁻¹ := by group
    _ = w φ i.swap * (((w φ i.swap)⁻¹ * g * w φ i.swap) * z) * (w φ i.swap)⁻¹ := by
        rw [hz _ hg']
    _ = g * (w φ i.swap * z * (w φ i.swap)⁻¹) := by group

theorem sixH_h10_center_le (hS : SCSetting L K n φ t i) (h1 : H1Concl φ t i)
    (h2a : H2aConcl φ t i) (h2d : H2dConcl φ t i) (h7 : H7Concl φ t i) (h9 : H9Concl φ t i)
    {z : G} (hzM : z ∈ Mhat φ t i i.swap) (hz : ∀ g ∈ Mhat φ t i i.swap, z * g = g * z) :
    z ∈ Kc φ t i.swap := by
  have hz1 : z ∈ (Mc φ t i : Set G) * (Mw φ t i i.swap : Set G) := by
    rw [SixF.M_mul_Mw_swap hS.fc i hS.ne_bot hS.eq_bot]
    exact hzM
  obtain ⟨m, hm0, m', hm'0, rfl⟩ := Set.mem_mul.mp hz1
  have hm : m ∈ Mc φ t i := hm0
  have hm' : m' ∈ Mw φ t i i.swap := hm'0
  have hmK : m ∈ Kc φ t i.swap :=
    sixH_h10_Z_M_le_K hS h2d hm (sixH_h10_central_M hS h1 h2a h2d h7 h9 hm hm' hz)
  have hnM : w φ i.swap * m' * (w φ i.swap)⁻¹ ∈ Mc φ t i := FullCenterWeyl.mem_map_conj_inv.mp hm'
  have hm''w : w φ i.swap * m * (w φ i.swap)⁻¹ ∈ Mw φ t i i.swap := by
    rw [FullCenterWeyl.mem_map_conj_inv, sixH_h10_w_conj_conj]
    exact hm
  have hnH : (w φ i.swap * m' * (w φ i.swap)⁻¹)⁻¹ ∈ Mhat φ t i i.swap :=
    inv_mem ((le_sup_left : Mc φ t i ≤ Mhat φ t i i.swap) hnM)
  have hm3 : (w φ i.swap * m' * (w φ i.swap)⁻¹)⁻¹ * (w φ i.swap * m * (w φ i.swap)⁻¹) *
      (w φ i.swap * m' * (w φ i.swap)⁻¹) ∈ Mw φ t i i.swap := by
    have h := sixH_h10_Mw_conj h7 h9 hnH hm''w
    simpa using h
  have hzc := sixH_h10_conj_central (t := t) (i := i) (z := m * m') hz
  have e : (w φ i.swap * m' * (w φ i.swap)⁻¹) *
      ((w φ i.swap * m' * (w φ i.swap)⁻¹)⁻¹ * (w φ i.swap * m * (w φ i.swap)⁻¹) *
        (w φ i.swap * m' * (w φ i.swap)⁻¹)) =
      w φ i.swap * (m * m') * (w φ i.swap)⁻¹ := by group
  have hnK : w φ i.swap * m' * (w φ i.swap)⁻¹ ∈ Kc φ t i.swap := by
    refine sixH_h10_Z_M_le_K hS h2d hnM ?_
    refine sixH_h10_central_M hS h1 h2a h2d h7 h9 hnM hm3 ?_
    rw [e]
    exact hzc
  have hm'K : m' ∈ Kc φ t i.swap := by
    have h := FullCenterWeyl.conj_w_mem_K hS.fc i.swap hnK
    rwa [sixH_h10_w_conj_conj] at h
  exact mul_mem hmK hm'K

theorem sixH_h10_center (hS : SCSetting L K n φ t i) (h1 : H1Concl φ t i)
    (h2a : H2aConcl φ t i) (h2d : H2dConcl φ t i) (h6 : H6Concl φ t i) (h7 : H7Concl φ t i)
    (h9 : H9Concl φ t i) :
    (center ↥(Mhat φ t i i.swap)).map (Mhat φ t i i.swap).subtype = Kc φ t i.swap := by
  apply le_antisymm
  · rintro z ⟨c, hc, rfl⟩
    refine sixH_h10_center_le hS h1 h2a h2d h7 h9 c.2 fun g hg => ?_
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨g, hg⟩)).symm
  · intro z hz
    refine ⟨⟨z, sixH_h7_Kj_le hS hz⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    exact Subtype.ext (h6 z hz g g.2).symm

theorem sixH_h10_sq_conj {g : G} (hg : g ∈ normalizer ((Mhat φ t i i.swap : Subgroup G) : Set G))
    {x : G} (hx : x ∈ closure {x : G | ∃ y ∈ Mhat φ t i i.swap, x = y * y}) :
    g * x * g⁻¹ ∈ closure {x : G | ∃ y ∈ Mhat φ t i i.swap, x = y * y} := by
  have hle : closure {x : G | ∃ y ∈ Mhat φ t i i.swap, x = y * y} ≤
      (closure {x : G | ∃ y ∈ Mhat φ t i i.swap, x = y * y}).comap
        (MulAut.conj g).toMonoidHom := by
    rw [closure_le]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : g * y * g⁻¹ ∈ Mhat φ t i i.swap := (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    show g * (y * y) * g⁻¹ ∈ closure {x : G | ∃ y ∈ Mhat φ t i i.swap, x = y * y}
    apply Subgroup.subset_closure
    exact ⟨g * y * g⁻¹, hy', by group⟩
  exact hle hx

theorem sixH_h10_sq_mem_K (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h6 : H6Concl φ t i) (h7 : H7Concl φ t i) (h9 : H9Concl φ t i) {y : G}
    (hy : y ∈ Mhat φ t i i.swap) : y * y ∈ Kc φ t i.swap := by
  have hy1 : y ∈ (Mc φ t i : Set G) * (Mw φ t i i.swap : Set G) := by
    rw [SixF.M_mul_Mw_swap hS.fc i hS.ne_bot hS.eq_bot]
    exact hy
  obtain ⟨m, hm0, m', hm'0, rfl⟩ := Set.mem_mul.mp hy1
  have hm : m ∈ Mc φ t i := hm0
  have hm' : m' ∈ Mw φ t i i.swap := hm'0
  have hm'H : m' ∈ Mhat φ t i i.swap := (le_sup_right : Mw φ t i i.swap ≤ Mhat φ t i i.swap) hm'
  have hcW : m'⁻¹ * m⁻¹ * m' * m ∈ Wk φ t i.swap := sixH_h10_comm_Mw_M hS h7 h9 hm' hm
  have hcK : m'⁻¹ * m⁻¹ * m' * m ∈ Kc φ t i.swap :=
    ((FullCenterTorus.W_le_Fi hS.fc i.swap).trans le_sup_right) hcW
  have hcc : (m'⁻¹ * m⁻¹ * m' * m) * m' = m' * (m'⁻¹ * m⁻¹ * m' * m) := h6 _ hcK m' hm'H
  have e : (m * m') * (m * m') =
      ((m * m) * (m' * (m'⁻¹ * m⁻¹ * m' * m) * m'⁻¹)) * (m' * m') := by group
  have e2 : m' * (m'⁻¹ * m⁻¹ * m' * m) * m'⁻¹ = m'⁻¹ * m⁻¹ * m' * m := by
    rw [← hcc, mul_inv_cancel_right]
  have hnM : w φ i.swap * m' * (w φ i.swap)⁻¹ ∈ Mc φ t i := FullCenterWeyl.mem_map_conj_inv.mp hm'
  have hnnK : (w φ i.swap * m' * (w φ i.swap)⁻¹) * (w φ i.swap * m' * (w φ i.swap)⁻¹) ∈
      Kc φ t i.swap := SixG.U_le_K i i.swap (hM2 _ hnM)
  have hm'm' : m' * m' ∈ Kc φ t i.swap := by
    have h := FullCenterWeyl.conj_w_mem_K hS.fc i.swap hnnK
    have e3 : w φ i.swap * ((w φ i.swap * m' * (w φ i.swap)⁻¹) *
        (w φ i.swap * m' * (w φ i.swap)⁻¹)) * (w φ i.swap)⁻¹ = m' * m' := by
      have e4 : w φ i.swap * ((w φ i.swap * m' * (w φ i.swap)⁻¹) *
          (w φ i.swap * m' * (w φ i.swap)⁻¹)) * (w φ i.swap)⁻¹ =
          (w φ i.swap * w φ i.swap) * (m' * m') * (w φ i.swap * w φ i.swap)⁻¹ := by group
      rw [e4, sixH_h10_w_mul]
      simp
    rwa [e3] at h
  rw [e, e2]
  exact mul_mem (mul_mem (SixG.U_le_K i i.swap (hM2 m hm)) hcK) hm'm'

theorem sixH_h10_A_le_sq (hS : SCSetting L K n φ t i) (h2a : H2aConcl φ t i)
    (h7 : H7Concl φ t i) :
    A φ i.swap ≤ closure {x : G | ∃ y ∈ Mhat φ t i i.swap, x = y * y} := by
  have hwN : w φ i.swap ∈ normalizer ((Mhat φ t i i.swap : Subgroup G) : Set G) :=
    SixF.w_mem_normalizer_Mhat' i i.swap
  have hTN : Tplus φ t i ≤ normalizer ((Mhat φ t i i.swap : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h7.2.1).mp h7.2.2.1
  have hPT : P φ ≤ Tplus φ t i :=
    (le_sup_left : P φ ≤ Q φ t).trans ((SixG.Q_le_Tbar hS.fc i).trans le_sup_left)
  have hUA : U φ i ≤ A φ i.swap :=
    pull_mono φ ((FullCenter.rootU_le_center i).trans (FullCenter.center_le_rootA i.swap))
  have hUsq : U φ i ≤ closure {x : G | ∃ y ∈ Mhat φ t i i.swap, x = y * y} := by
    rw [← h2a.sq_M]
    exact Subgroup.closure_mono fun x ⟨y, hy, hx⟩ =>
      ⟨y, (le_sup_left : Mc φ t i ≤ Mhat φ t i i.swap) hy, hx⟩
  have hX := sixH_s3_invariant_A (φ := φ) i
    (X := closure {x : G | ∃ y ∈ Mhat φ t i i.swap, x = y * y} ⊓ A φ i.swap) inf_le_right
    (fun p hp x hx => Subgroup.mem_inf.mpr
      ⟨sixH_h10_sq_conj (hTN (hPT hp)) (Subgroup.mem_inf.mp hx).1,
        FullCenterWeyl.conj_H_mem_A hS.fc i.swap (FullCenterWeyl.P_le_H hp)
          (Subgroup.mem_inf.mp hx).2⟩)
    (fun x hx => Subgroup.mem_inf.mpr
      ⟨sixH_h10_sq_conj hwN (Subgroup.mem_inf.mp hx).1,
        FullCenterWeyl.conj_w_mem_A hS.fc i.swap (Subgroup.mem_inf.mp hx).2⟩)
    (fun u hu => Subgroup.mem_inf.mpr ⟨hUsq hu, hUA hu⟩)
  intro x hx
  rw [← hX] at hx
  exact (Subgroup.mem_inf.mp hx).1

theorem sixH_h10_sq (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1a : Tplus φ t i ⊓ normalizer (A φ i.swap : Set G) = T₀ φ t i.swap)
    (h2a : H2aConcl φ t i) (h6 : H6Concl φ t i) (h7 : H7Concl φ t i) (h9 : H9Concl φ t i) :
    closure {x : G | ∃ y ∈ Mhat φ t i i.swap, x = y * y} = Kc φ t i.swap := by
  have hSqK : closure {x : G | ∃ y ∈ Mhat φ t i i.swap, x = y * y} ≤ Kc φ t i.swap := by
    rw [closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact sixH_h10_sq_mem_K hS hM2 h6 h7 h9 hy
  have hAS := sixH_h10_A_le_sq hS h2a h7
  have hJ : ∀ j ∈ J₀ φ, ∀ x ∈ closure {x : G | ∃ y ∈ Mhat φ t i i.swap, x = y * y},
      j * x * j⁻¹ ∈ closure {x : G | ∃ y ∈ Mhat φ t i i.swap, x = y * y} :=
    fun j hj x hx => sixH_h10_sq_conj (h7.2.2.2 hj) hx
  rcases sixH_i2_irreducible_K hS hAS hSqK hJ with h | h
  · exfalso
    have hTN : Tplus φ t i ≤ normalizer ((Mhat φ t i i.swap : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer h7.2.1).mp h7.2.2.1
    have hTA : Tplus φ t i ≤ normalizer (A φ i.swap : Set G) := by
      refine sixH_h5_le_normalizer_of_conj fun g hg c hc => ?_
      rw [← h] at hc ⊢
      exact sixH_h10_sq_conj (hTN hg) hc
    have hle : Tplus φ t i ≤ T₀ φ t i.swap := by
      rw [← h1a]
      exact le_inf le_rfl hTA
    exact SixG.T₀_ne_Tplus hS.fc i hS.ne_bot hS.eq_bot hM2 hle
  · exact h

theorem sixH_h10 (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1a : Tplus φ t i ⊓ normalizer (A φ i.swap : Set G) = T₀ φ t i.swap)
    (h1 : H1Concl φ t i) (h2a : H2aConcl φ t i) (h2d : H2dConcl φ t i) (h6 : H6Concl φ t i)
    (h7 : H7Concl φ t i) (h9 : H9Concl φ t i) :
    (center ↥(Mhat φ t i i.swap)).map (Mhat φ t i i.swap).subtype = Kc φ t i.swap ∧
      closure {x : G | ∃ y ∈ Mhat φ t i i.swap, x = y * y} = Kc φ t i.swap := by
  exact ⟨sixH_h10_center hS h1 h2a h2d h6 h7 h9, sixH_h10_sq hS hM2 h1a h2a h6 h7 h9⟩

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
