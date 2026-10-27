module

public import CFSG.Quasithin.Vol2.E2TenSevenPair
public import CFSG.Quasithin.Vol2.E2TenSevenMult
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 CFSG.Blueprint.Multiplier

namespace E2

open scoped commutatorElement

theorem two_le_of_isPSp4 {Y : Type} [Group Y] {n : ℕ} (h : IsPSp4 2 n Y) : 2 ≤ n := by
  obtain ⟨⟨-, hf, -, hne⟩, -⟩ := h
  by_contra hn
  have h1 : n = 1 := by omega
  subst h1
  exact hne rfl

theorem isSimpleGroup_of_isPSp4 {Y : Type} [Group Y] {n : ℕ} (h : IsPSp4 2 n Y) :
    IsSimpleGroup Y := by
  have hn := two_le_of_isPSp4 h
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := h
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
    (Or.inl (Or.inr h4))
  exact MulEquiv.isSimpleGroup eK

theorem psp_row_param {n : ℕ} (hn : 2 ≤ n) :
    5 ≤ 2 ^ n ∨ 2 ^ n = 4 ∨ (2 ^ n = 2 ∧ 4 ≤ 2) ∨ (2 ^ n = 3 ∧ 3 ≤ 2) := by
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
  · exact Or.inr (Or.inl rfl)
  · left
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3

theorem commutator_eq_top_of_isPSp4
    {Y : Type} [Group Y] {n : ℕ} (h : IsPSp4 2 n Y) :
    commutator Y = ⊤ :=
  (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_row h
    (psp_row_param (two_le_of_isPSp4 h))).1

theorem center_eq_bot_of_isPSp4
    {L Y : Type} [Group L] [Group Y] [Group.IsPerfect L] {n : ℕ}
    (hY : IsPSp4 2 n Y) (e : L ⧸ Subgroup.center L ≃* Y) : Subgroup.center L = ⊥ := by
  have hn := two_le_of_isPSp4 hY
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_row hY
    (psp_row_param hn)
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hg : genericOrders .PSp 2 2 n = (1, 1) := by
    show (Nat.gcd 2 (2 ^ n - 1), 1) = (1, 1)
    rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd)]
  have he : exceptionalOrders .PSp 2 2 n = (1, 1) := rfl
  have : Subsingleton (generic .PSp 2 2 n × exceptional .PSp 2 2 n) := by
    unfold generic exceptional
    rw [hg, he]
    show Subsingleton ((Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) ×
      (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)))
    infer_instance
  have : Subsingleton (CFSG.Open.griessHopfMultiplier Y) := eM.toEquiv.subsingleton
  obtain ⟨φ, hφ⟩ := exists_surjective_center e
  exact eq_bot_of_surjective_subsingleton φ hφ

namespace Pair

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem e2_10_eight
    (h : Pair X T M V g) {n : ℕ}
    (hY : IsPSp4 2 n (StarQuot M X)) :
    pCoreOf 2 X = kerIn M X ∧
      (∃ C E : Subgroup G, PP M V X g ≤ C ∧ C ≤ X ∧ PP M V X g ≤ E ∧ E ≤ X ∧
        (∃ (_ : ((PP M V X g).subgroupOf C).Normal),
          Nonempty (↥C ⧸ (PP M V X g).subgroupOf C ≃* StarQuot M X)) ∧
        (∀ x ∈ E, x ^ 2 ∈ PP M V X g) ∧
        (∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ PP M V X g) ∧
        ⁅C, E⁆ ≤ PP M V X g ∧ C ⊓ E = PP M V X g ∧ C ⊔ E = X) ∧
      pCoreOf 2 (oTwoUpper X ⊔ PP M V X g) = PP M V X g ∧
      ∃ (_ : ((PP M V X g).subgroupOf (oTwoUpper X ⊔ PP M V X g)).Normal),
        Nonempty (↥(oTwoUpper X ⊔ PP M V X g) ⧸
            (PP M V X g).subgroupOf (oTwoUpper X ⊔ PP M V X g) ≃*
          ↥(commutator (StarQuot M X))) := by
  have hXs := isSimpleGroup_of_isPSp4 hY
  have hXp := commutator_eq_top_of_isPSp4 hY
  have := hXs.toNontrivial
  have hXna := nonabelian_of_commutator_eq_top hXp
  have := h.normal_P
  have := h.normal_Jbar
  set e := h.quotJbarEquiv
  have hS : commutator (Xbar M V X g ⧸ Jbar M V X g) = ⊤ := commutator_eq_top_of_mulEquiv e hXp
  have hsimp : IsSimpleGroup (Xbar M V X g ⧸ Jbar M V X g) := MulEquiv.isSimpleGroup e
  have hna : ∃ a b : Xbar M V X g ⧸ Jbar M V X g, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hXna
    exact ⟨e.symm a, e.symm b, fun hh => hab (by simpa using congrArg e hh)⟩
  have hJc := h.Jbar_le_center
  obtain ⟨hLq, ⟨eL⟩⟩ := quasisimple_commutator _ hJc hS hsimp hna
  set Lb := commutator (Xbar M V X g) with hLb
  have : Group.IsPerfect ↥Lb := hLq.1
  set eX : ↥Lb ⧸ Subgroup.center ↥Lb ≃* StarQuot M X := eL.trans e
  have hb : Subgroup.center ↥Lb = ⊥ := center_eq_bot_of_isPSp4 hY eX
  obtain ⟨hZ, hsq, hJ⟩ := h.center_quot_facts hXs hXp hXna (lift_of_center_eq_bot hb)
  have hLJ := commutator_sup_eq_top _ hS
  have hZc := map_center_commutator_eq _ hJc hS hsimp hna
  rw [hb, Subgroup.map_bot] at hZc
  have hJ2 : ∀ j ∈ Jbar M V X g, j * j = 1 := fun j hj => hsq j (hZ ▸ hj)
  have hsqL : ∀ x : Xbar M V X g, x * x ∈ Lb := by
    intro x
    obtain ⟨l, hl, j, hj, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (hLJ ▸ Subgroup.mem_top x)
    have hjc := Subgroup.mem_center_iff.1 (hJc hj)
    have e1 : l * j * (l * j) = l * l * (j * j) := by
      calc l * j * (l * j) = l * (j * l) * j := by group
        _ = l * (l * j) * j := by rw [hjc l]
        _ = l * l * (j * j) := by group
    rw [e1, hJ2 j hj, mul_one]
    exact Lb.mul_mem hl hl
  have hH := h.oTwoUpper_sup_P_eq hLq.1 hsqL
  let eLX : ↥Lb ≃* StarQuot M X :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hb.symm)).trans eX
  have hsimpL : IsSimpleGroup ↥Lb := MulEquiv.isSimpleGroup eLX
  let eC : StarQuot M X ≃* ↥(commutator (StarQuot M X)) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hXp.symm)
  obtain ⟨hN, ⟨eQ⟩⟩ := exists_quot_equiv (M := M) (V := V) (g := g) Lb
  refine ⟨hJ, ⟨pre M V X g Lb, pre M V X g (Jbar M V X g), h.P_le_pre _, pre_le_X _,
    h.P_le_pre _, pre_le_X _, ⟨hN, ⟨eQ.trans eLX⟩⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxX, hxJ⟩ := mem_pre.1 hx
    have hx2 : x ^ 2 ∈ X := X.pow_mem hxX 2
    rw [← piX_eq_one_iff hx2]
    have e1 : (⟨x ^ 2, hx2⟩ : X) = ⟨x, hxX⟩ * ⟨x, hxX⟩ := Subtype.ext (pow_two x)
    rw [e1, map_mul]
    exact hJ2 _ hxJ
  · intro x hx y hy
    obtain ⟨hxX, hxJ⟩ := mem_pre.1 hx
    obtain ⟨hyX, -⟩ := mem_pre.1 hy
    have hc : x * y * x⁻¹ * y⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem hxX hyX) (X.inv_mem hxX)) (X.inv_mem hyX)
    rw [← piX_eq_one_iff hc]
    have e1 : (⟨x * y * x⁻¹ * y⁻¹, hc⟩ : X) =
        ⟨x, hxX⟩ * ⟨y, hyX⟩ * (⟨x, hxX⟩ : X)⁻¹ * (⟨y, hyX⟩ : X)⁻¹ := Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv,
      ← Subgroup.mem_center_iff.1 (hJc hxJ), mul_inv_cancel_right, mul_inv_cancel]
  · rw [Subgroup.commutator_comm]
    exact commutator_pre_le hJc (pre_le_X _)
  · refine le_antisymm (fun x hx => ?_) (le_inf (h.P_le_pre _) (h.P_le_pre _))
    obtain ⟨hxX, hxL⟩ := mem_pre.1 hx.1
    obtain ⟨hxX', hxJ⟩ := mem_pre.1 hx.2
    have h1 : piX M V X g ⟨x, hxX⟩ ∈ Lb ⊓ Jbar M V X g := ⟨hxL, hxJ⟩
    rw [← hZc, Subgroup.mem_bot] at h1
    exact (piX_eq_one_iff hxX).1 h1
  · refine le_antisymm (sup_le (pre_le_X _) (pre_le_X _)) (fun x hxX => ?_)
    have hx : piX M V X g ⟨x, hxX⟩ ∈ Lb ⊔ Jbar M V X g := by
      rw [hLJ]
      exact Subgroup.mem_top _
    obtain ⟨a, ha, l, hl, hal⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ((PP M V X g).subgroupOf X) a
    have hyL : (y : G) ∈ pre M V X g Lb := mem_pre.2 ⟨y.2, ha⟩
    have hz : (y : G)⁻¹ * x ∈ pre M V X g (Jbar M V X g) := by
      refine mem_pre.2 ⟨X.mul_mem (X.inv_mem y.2) hxX, ?_⟩
      have e1 : (⟨(y : G)⁻¹ * x, X.mul_mem (X.inv_mem y.2) hxX⟩ : X) = y⁻¹ * ⟨x, hxX⟩ :=
        Subtype.ext rfl
      rw [e1, map_mul, map_inv, ← hal]
      simpa using hl
    have e2 : x = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [e2]
    exact Subgroup.mul_mem_sup hyL hz
  · rw [hH]
    exact h.pCoreOf_pre_eq hsimpL hLq.1
  · rw [hH]
    exact ⟨hN, ⟨eQ.trans (eLX.trans eC)⟩⟩

end Pair

end E2

theorem ASInputs.as_E_2_10_eight_holds :
    ASInputs.AS_E_2_10_eight := by
  rintro G _ _ X T M V g h ⟨n, -, hY⟩
  exact h.e2_10_eight hY

end CFSG.Quasithin
