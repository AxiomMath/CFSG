module

public import CFSG.RankThree.GF2n.Tim78S48PairQuot
import CFSG.RankThree.GF2n.Tim78S4Conj
import CFSG.RankThree.GF2n.Tim78Frattini
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

section Certified


theorem T_inf_W (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) :
    T ⊓ (B ⊔ conjSubgroup g B) = B := by
  refine le_antisymm (fun x hx => ?_) (le_inf H.B_le_T le_sup_left)
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun x hx y hy => H.commute_of_conj_le_M h48.leM y hy x hx |>.symm) hx.2
  have hbT : b ∈ T := by
    have := T.mul_mem (T.inv_mem (H.B_le_T ha)) hx.1
    rwa [inv_mul_cancel_left] at this
  have : b ∈ conjSubgroup g B ⊓ T := ⟨hb, hbT⟩
  rw [H.Bg_inf_T hCen hU hP, Subgroup.mem_bot] at this
  rw [this, mul_one]
  exact ha

theorem Tg_inf_W (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) :
    conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) = conjSubgroup g B := by
  refine le_antisymm (fun x hx => ?_) (le_inf (Subgroup.map_mono H.B_le_T) le_sup_right)
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun x hx y hy => H.commute_of_conj_le_M h48.leM y hy x hx |>.symm) hx.2
  have haT : a ∈ conjSubgroup g T := by
    have := (conjSubgroup g T).mul_mem hx.1 ((conjSubgroup g T).inv_mem
      (Subgroup.map_mono H.B_le_T hb))
    rwa [mul_inv_cancel_right] at this
  have : a ∈ B ⊓ conjSubgroup g T := ⟨ha, haT⟩
  rw [H.B_inf_Tg hCen hU hP, Subgroup.mem_bot] at this
  rw [this, one_mul]
  exact hb

theorem Bg_inf_Q (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hP : ¬ conjSubgroup g B ≤ P) : conjSubgroup g B ⊓ Q = ⊥ := by
  by_contra h
  exact hP (H.tim78_4_5 hCen hU g h)

theorem B_inf_Qg (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hP : ¬ conjSubgroup g B ≤ P) : B ⊓ conjSubgroup g Q = ⊥ := by
  by_contra h
  apply hP
  have h1 : conjSubgroup g⁻¹ B ⊓ Q ≠ ⊥ := by
    intro hbot
    apply h
    have : conjSubgroup g (conjSubgroup g⁻¹ B ⊓ Q) = B ⊓ conjSubgroup g Q := by
      rw [conjSubgroup_inf, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
    rw [← this, hbot]
    exact Subgroup.map_bot _
  have := H.conj_inv_le_P_of_conj_le_P (H.tim78_4_5 hCen hU g⁻¹ h1)
  rwa [inv_inv] at this

theorem Z_le_kernel (h48 : Hyp48 M B T g) :
    T ⊓ conjSubgroup g Q ≤ kernel48 B T g := by
  intro z hz
  refine (H.T_mem_kernel_iff h48 hz.1 (Subgroup.mem_sup_left hz.1)).mpr fun b hb => ?_
  have := (H.conj_B_le_center H.B_le_Q le_rfl hb).2
  exact Subgroup.mem_centralizer_iff.mp this z hz.2

theorem Z_elem (hP : ¬ conjSubgroup g B ≤ P) :
    Assembly.IsElemAbelian 2 (T ⊓ conjSubgroup g Q) := by
  have hc : ∀ a ∈ T ⊓ conjSubgroup g Q, ∀ b ∈ T ⊓ conjSubgroup g Q, a * b = b * a := by
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ B := H.commutator_mem (H.T_le_Q ha.1) (H.T_le_Q hb.1)
    have h2 : ⁅a, b⁆ ∈ conjSubgroup g B := (H.conj g).commutator_mem ha.2 hb.2
    have h3 : ⁅a, b⁆ ∈ B ⊓ conjSubgroup g B := ⟨h1, h2⟩
    rw [H.B_inf_Bg hP, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  refine ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  have h1 : x ^ 2 ∈ B := H.sq_mem (H.T_le_Q hx.1)
  have h2 : x ^ 2 ∈ conjSubgroup g B := (H.conj g).sq_mem hx.2
  have h3 : x ^ 2 ∈ B ⊓ conjSubgroup g B := ⟨h1, h2⟩
  rwa [H.B_inf_Bg hP, Subgroup.mem_bot] at h3

theorem Z_le_Tg (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) :
    T ⊓ conjSubgroup g Q ≤ conjSubgroup g T := by
  obtain ⟨x, hxX, hxT, hxB⟩ := H.exists_conj_Tg hCen hU h48 hP
  set Z := T ⊓ conjSubgroup g Q with hZ
  set W := B ⊔ conjSubgroup g B with hW
  have hZc : ∀ z ∈ Z, ∀ w ∈ W, z * w = w * z := fun z hz w hw =>
    (Subgroup.mem_centralizer_iff.mp (H.Z_le_kernel h48 hz).2 w hw).symm
  have hZN : Z ≤ Subgroup.normalizer (W : Set G) := le_normalizer_of_comm hZc
  have hW0e : Assembly.IsElemAbelian 2 (W ⊔ Z) :=
    IsElemAbelian.sup_of_commute (H.W_elem h48) (H.Z_elem hP) fun a ha b hb => (hZc b hb a ha).symm
  have hW0c : ∀ a ∈ W ⊔ Z, ∀ b ∈ W ⊔ Z, a * b = b * a := fun a ha b hb =>
    comm_of_isElemAbelian hW0e ha hb
  have hWZ : W ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have h1 : w ∈ T ⊓ W := ⟨hw.2.1, hw.1⟩
    rw [H.T_inf_W hCen hU h48 hP] at h1
    have h2 : w ∈ B ⊓ conjSubgroup g Q := ⟨h1, hw.2.2⟩
    rwa [H.B_inf_Qg hCen hU hP] at h2
  have hcardW0 : Nat.card (W ⊔ Z : Subgroup G) = Nat.card B ^ 2 * Nat.card Z := by
    have h := PartTwo.Sec6.card_sup_mul_card_inf hZN
    rw [sup_comm, inf_comm, hWZ, Subgroup.card_bot, mul_one, H.card_W h48 hP] at h
    rw [h, mul_comm]
  have hTW0 : T ≤ Subgroup.normalizer ((W ⊔ Z : Subgroup G) : Set G) := fun t ht => by
    refine Subgroup.mem_normalizer_fintype fun w₀ hw₀ => ?_
    obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_of_mem_sup hZN hw₀
    have e : t * (w * z) * t⁻¹ = (t * w * t⁻¹) * (⁅t, z⁆ * z) := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine (W ⊔ Z).mul_mem (Subgroup.mem_sup_left
      ((Subgroup.mem_normalizer_iff.mp (H.T_le_normalizer_W h48 ht) w).mp hw))
      ((W ⊔ Z).mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right hz))
    exact (le_sup_left : B ≤ W) (H.commutator_mem (H.T_le_Q ht) (H.T_le_Q hz.1))
  have hTgW0 : conjSubgroup g T ≤ Subgroup.normalizer ((W ⊔ Z : Subgroup G) : Set G) :=
    fun t ht => by
    refine Subgroup.mem_normalizer_fintype fun w₀ hw₀ => ?_
    obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_of_mem_sup hZN hw₀
    have e : t * (w * z) * t⁻¹ = (t * w * t⁻¹) * (⁅t, z⁆ * z) := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine (W ⊔ Z).mul_mem (Subgroup.mem_sup_left
      ((Subgroup.mem_normalizer_iff.mp (H.Tg_le_normalizer_W h48 ht) w).mp hw))
      ((W ⊔ Z).mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right hz))
    exact (le_sup_right : conjSubgroup g B ≤ W) ((H.conj g).commutator_mem
      ((H.conj g).T_le_Q ht) hz.2)
  have hXW0 : T ⊔ conjSubgroup g T ≤ Subgroup.normalizer ((W ⊔ Z : Subgroup G) : Set G) :=
    sup_le hTW0 hTgW0
  have hTW0eq : T ⊓ (W ⊔ Z) = B ⊔ Z := by
    refine le_antisymm (fun y hy => ?_) (sup_le (le_inf H.B_le_T
      (le_sup_left.trans le_sup_left)) (le_inf inf_le_left le_sup_right))
    obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_of_mem_sup hZN hy.2
    have hwT : w ∈ T := by
      have := T.mul_mem hy.1 (T.inv_mem hz.1)
      rwa [mul_inv_cancel_right] at this
    have hwB : w ∈ B := by
      have : w ∈ T ⊓ W := ⟨hwT, hw⟩
      rwa [H.T_inf_W hCen hU h48 hP] at this
    exact (B ⊔ Z).mul_mem (Subgroup.mem_sup_left hwB) (Subgroup.mem_sup_right hz)
  have hBZ : B ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : y ∈ B ⊓ conjSubgroup g Q := ⟨hy.1, hy.2.2⟩
    rwa [H.B_inf_Qg hCen hU hP] at this
  have hZB : Z ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_comm fun z hz b hb => H.T_comm_B hz.1 hb
  have hcardTW0 : Nat.card (T ⊓ (W ⊔ Z) : Subgroup G) = Nat.card B * Nat.card Z := by
    rw [hTW0eq]
    have h := PartTwo.Sec6.card_sup_mul_card_inf hZB
    rw [sup_comm, inf_comm, hBZ, Subgroup.card_bot, mul_one] at h
    rw [h, mul_comm]
  have hTgW0eq : conjSubgroup g T ⊓ (W ⊔ Z) = conjSubgroup x (T ⊓ (W ⊔ Z)) := by
    rw [conjSubgroup_inf, ← hxT, conjSubgroup_eq_self_iff.mpr (hXW0 hxX)]
  have hcardTgW0 : Nat.card (conjSubgroup g T ⊓ (W ⊔ Z) : Subgroup G) =
      Nat.card B * Nat.card Z := by
    rw [hTgW0eq, card_conjSubgroup, hcardTW0]
  have hN : T ⊓ (W ⊔ Z) ≤ Subgroup.normalizer ((conjSubgroup g T ⊓ (W ⊔ Z) : Subgroup G) : Set G) :=
    le_normalizer_of_comm fun a ha b hb => hW0c a ha.2 b hb.2
  have h := PartTwo.Sec6.card_sup_mul_card_inf hN
  rw [hcardTW0, hcardTgW0] at h
  have hle : Nat.card ((T ⊓ (W ⊔ Z)) ⊔ (conjSubgroup g T ⊓ (W ⊔ Z)) : Subgroup G) ≤
      Nat.card (W ⊔ Z : Subgroup G) := Subgroup.card_le_of_le (sup_le inf_le_right inf_le_right)
  rw [hcardW0] at hle
  have hinf : Nat.card Z ≤
      Nat.card ((T ⊓ (W ⊔ Z)) ⊓ (conjSubgroup g T ⊓ (W ⊔ Z)) : Subgroup G) := by
    by_contra hlt
    push Not at hlt
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    have hBpos : 0 < Nat.card B := Nat.card_pos
    have h1 : Nat.card ((T ⊓ (W ⊔ Z)) ⊔ (conjSubgroup g T ⊓ (W ⊔ Z)) : Subgroup G) *
        Nat.card ((T ⊓ (W ⊔ Z)) ⊓ (conjSubgroup g T ⊓ (W ⊔ Z)) : Subgroup G) ≤
        (Nat.card B ^ 2 * Nat.card Z) *
          Nat.card ((T ⊓ (W ⊔ Z)) ⊓ (conjSubgroup g T ⊓ (W ⊔ Z)) : Subgroup G) :=
      Nat.mul_le_mul_right _ hle
    have h2 : (Nat.card B ^ 2 * Nat.card Z) *
        Nat.card ((T ⊓ (W ⊔ Z)) ⊓ (conjSubgroup g T ⊓ (W ⊔ Z)) : Subgroup G) <
        (Nat.card B ^ 2 * Nat.card Z) * Nat.card Z :=
      Nat.mul_lt_mul_of_pos_left hlt (by positivity)
    nlinarith
  have hsub : (T ⊓ (W ⊔ Z)) ⊓ (conjSubgroup g T ⊓ (W ⊔ Z)) ≤ Z := fun y hy =>
    ⟨hy.1.1, Subgroup.map_mono H.T_le_Q hy.2.1⟩
  have heq : (T ⊓ (W ⊔ Z)) ⊓ (conjSubgroup g T ⊓ (W ⊔ Z)) = Z :=
    Subgroup.eq_of_le_of_card_ge hsub hinf
  intro z hz
  have : z ∈ (T ⊓ (W ⊔ Z)) ⊓ (conjSubgroup g T ⊓ (W ⊔ Z)) := by rw [heq]; exact hz
  exact this.2.1

theorem inf_Tg_eq_inf_Qg (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) :
    T ⊓ conjSubgroup g T = T ⊓ conjSubgroup g Q :=
  le_antisymm (inf_le_inf_left _ (Subgroup.map_mono H.T_le_Q))
    (le_inf inf_le_left (H.Z_le_Tg hCen hU h48 hP))

theorem comm_zpow_mem_B {a : G} (haM : a ∈ M) (h : ∀ r ∈ Q, ⁅a, r⁆ ∈ B) (k : ℤ) {r : G}
    (hr : r ∈ Q) : ⁅a ^ k, r⁆ ∈ B := by
  have hMB : ∀ b ∈ B, a * b * a⁻¹ ∈ B := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_B haM) b).mp hb
  have hMB' : ∀ b ∈ B, a⁻¹ * b * a ∈ B := fun b hb => by
    have := (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_B (M.inv_mem haM)) b).mp hb
    simpa using this
  induction k using Int.induction_on with
  | zero => simpa using B.one_mem
  | succ n ih =>
    have e : ⁅a ^ ((n : ℤ) + 1), r⁆ = a * ⁅a ^ (n : ℤ), r⁆ * a⁻¹ * ⁅a, r⁆ := by
      rw [zpow_add_one]
      simp only [commutatorElement_def]; group
    rw [e]
    exact B.mul_mem (hMB _ ih) (h r hr)
  | pred n ih =>
    have e : ⁅a ^ (-(n : ℤ) - 1), r⁆ = a⁻¹ * ⁅a ^ (-(n : ℤ)), r⁆ * a * ⁅a⁻¹, r⁆ := by
      rw [zpow_sub_one]
      simp only [commutatorElement_def]; group
    have h1 : ⁅a⁻¹, r⁆ ∈ B := by
      have e1 : ⁅a⁻¹, r⁆ = a⁻¹ * ⁅a, r⁆⁻¹ * a := by simp only [commutatorElement_def]; group
      rw [e1]
      exact hMB' _ (B.inv_mem (h r hr))
    rw [e]
    exact B.mul_mem (hMB' _ ih) h1

theorem mem_Q_of_comm_le_B {a : G} (haM : a ∈ M) (h : ∀ r ∈ Q, ⁅a, r⁆ ∈ B) : a ∈ Q := by
  refine H.le_Q_of_stabilizes (A := Subgroup.zpowers a) (Subgroup.zpowers_le.mpr haM) ?_
    (Subgroup.mem_zpowers a)
  intro m hm a' ha' r hr
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_conjSubgroup.mp ha')
  have hr' : m⁻¹ * r * m ∈ Q := (Subgroup.mem_normalizer_iff.mp
    (H.M_le_normalizer_Q (M.inv_mem hm)) r).mp hr |> fun h' => by simpa using h'
  have h1 := H.comm_zpow_mem_B haM h k hr'
  have e : ⁅a', r⁆ = m * ⁅a ^ k, m⁻¹ * r * m⁆ * m⁻¹ := by
    have : a' = m * a ^ k * m⁻¹ := by rw [hk]; group
    rw [this]
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_B hm) _).mp h1

theorem comm_sq_mem_conj_of_mem {N : Subgroup G} (hBN : B ≤ N) (hNQ : N ≤ Q)
    (hNT : conjSubgroup g N ⊓ T = ⊥) {y : G} (hy : y ∈ T)
    (hyN : y ∈ Subgroup.normalizer (conjSubgroup g N : Set G)) :
    ∀ s ∈ conjSubgroup g N, s⁻¹ * (y ^ 2 * s * (y ^ 2)⁻¹) ∈ conjSubgroup g B := by
  intro s hs
  by_cases hy2 : y ^ 2 = 1
  · rw [hy2]
    simpa using (conjSubgroup g B).one_mem
  set S := conjSubgroup g N with hSdef
  have hS2 : IsPGroup 2 S := (H.isPGroup_Q.to_le hNQ).map _
  have hΦ : inSubgroup frattini S ≤ S ⊓ Subgroup.centralizer (S : Set G) :=
    (H.frattini_conj_le hNQ).trans (H.conj_B_le_center hBN hNQ)
  have hyB : y ^ 2 ∈ B := H.sq_mem (H.T_le_Q hy)
  have hx : ∃ k : ℕ, y ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := H.isPGroup_Q ⟨y, H.T_le_Q hy⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hC : S ⊓ Subgroup.centralizer ({y} : Set G) =
      S ⊓ Subgroup.centralizer ({y ^ 2} : Set G) := by
    apply le_antisymm
    · intro c hc
      have hc2 : c * y = y * c :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
      have h0 : Commute c y := hc2
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hc).1,
        Subgroup.mem_centralizer_singleton_iff.mpr (h0.pow_right 2)⟩
    · intro c hc
      obtain ⟨hcS, hcC⟩ := Subgroup.mem_inf.mp hc
      have hcM : c ∈ M := H.normalizer_eq_and_centralizer_le.2 _ hyB hy2 hcC
      have h1 : ⁅c, y⁆ ∈ S := by
        have e : ⁅c, y⁆ = c * (y * c⁻¹ * y⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact S.mul_mem hcS ((Subgroup.mem_normalizer_iff.mp hyN c⁻¹).mp (S.inv_mem hcS))
      have h2 : ⁅c, y⁆ ∈ T := by
        have e : ⁅c, y⁆ = (c * y * c⁻¹) * y⁻¹ := by
          simp only [commutatorElement_def]
        rw [e]
        exact T.mul_mem ((Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_T hcM) y).mp hy)
          (T.inv_mem hy)
      have h3 : ⁅c, y⁆ ∈ S ⊓ T := ⟨h1, h2⟩
      rw [hNT, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
      exact Subgroup.mem_inf.mpr ⟨hcS, Subgroup.mem_centralizer_singleton_iff.mpr h3⟩
  exact H.frattini_conj_le hNQ ((tim78_2_2 hS2 hΦ hyN hx hC).2 s hs)

theorem T_inf_Pg (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) : T ⊓ conjSubgroup g P = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hyQ : y ∈ T ⊓ conjSubgroup g Q := ⟨hy.1, Subgroup.map_mono H.P_le_Q hy.2⟩
  have hyTg : y ∈ conjSubgroup g T := (H.Z_le_Tg hCen hU h48 hP) hyQ
  have h1 : y ∈ conjSubgroup g (T ⊓ P) := by
    rw [conjSubgroup_inf]
    exact ⟨hyTg, hy.2⟩
  rw [inf_comm, H.P_inf_T] at h1
  have : y ∈ conjSubgroup g B ⊓ T := ⟨h1, hy.1⟩
  rwa [H.Bg_inf_T hCen hU hP] at this

theorem T0_sq_eq_one (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) {y : G}
    (hy : y ∈ T ⊓ kernel48 B T g) : y * y = 1 := by
  by_contra hy2
  have hyT := hy.1
  have hyMg : y ∈ conjSubgroup g M := H.kernel_le_Mg hy.2
  have hyN : y ∈ Subgroup.normalizer (conjSubgroup g P : Set G) :=
    mem_normalizer_conj_of_mem_conj H.M_le_normalizer_P hyMg
  have hNT : conjSubgroup g P ⊓ T = ⊥ := by
    rw [inf_comm]
    exact H.T_inf_Pg hCen hU h48 hP
  have hsq := H.comm_sq_mem_conj_of_mem H.B_le_P H.P_le_Q hNT hyT hyN
  have hu : y ^ 2 ∈ B := H.sq_mem (H.T_le_Q hyT)
  have hTgP : conjSubgroup g T ≤ Subgroup.normalizer (conjSubgroup g P : Set G) :=
    le_normalizer_of_comm fun t ht p hp => H.conj_T_le_centralizer_conj_P g t ht p hp
  have hcomm : ∀ r ∈ conjSubgroup g Q, ⁅y ^ 2, r⁆ ∈ conjSubgroup g B := by
    intro r hr
    rw [(H.conj g).Q_eq_sup] at hr
    obtain ⟨p, hp, t, ht, rfl⟩ := exists_mul_of_mem_sup hTgP hr
    have hp1 : ⁅y ^ 2, p⁆ ∈ conjSubgroup g B := by
      have h1 := hsq p hp
      have hpQ : p ∈ conjSubgroup g Q := Subgroup.map_mono H.P_le_Q hp
      have hb := (H.conj g).center_Q h1 hpQ
      have e : ⁅y ^ 2, p⁆ = p⁻¹ * (y ^ 2 * p * (y ^ 2)⁻¹) := by
        calc ⁅y ^ 2, p⁆ = p * (p⁻¹ * (y ^ 2 * p * (y ^ 2)⁻¹)) * p⁻¹ := by
              simp only [commutatorElement_def]; group
          _ = p⁻¹ * (y ^ 2 * p * (y ^ 2)⁻¹) := by rw [← hb]; group
      rw [e]
      exact h1
    have ht1 : ⁅y ^ 2, t⁆ ∈ conjSubgroup g B := h48.comm_Tg _ hu t ht
    have htQ : t ∈ conjSubgroup g Q := (H.conj g).T_le_Q ht
    have hpQ : p ∈ conjSubgroup g Q := Subgroup.map_mono H.P_le_Q hp
    have e : ⁅y ^ 2, p * t⁆ = ⁅y ^ 2, p⁆ * (p * ⁅y ^ 2, t⁆ * p⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e, show p * ⁅y ^ 2, t⁆ * p⁻¹ = ⁅y ^ 2, t⁆ by
      rw [← (H.conj g).center_Q ht1 hpQ]; group]
    exact (conjSubgroup g B).mul_mem hp1 ht1
  have hy2Mg : y ^ 2 ∈ conjSubgroup g M := (conjSubgroup g M).pow_mem hyMg 2
  have hQg := (H.conj g).mem_Q_of_comm_le_B hy2Mg hcomm
  have : y ^ 2 ∈ B ⊓ conjSubgroup g Q := ⟨hu, hQg⟩
  rw [H.B_inf_Qg hCen hU hP, Subgroup.mem_bot] at this
  exact hy2 (by rw [← sq]; exact this)

theorem T0_elem (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) :
    Assembly.IsElemAbelian 2 (T ⊓ kernel48 B T g) := by
  have hc : ∀ a ∈ T ⊓ kernel48 B T g, ∀ b ∈ T ⊓ kernel48 B T g, a * b = b * a := fun a ha b hb =>
    comm_of_mul_self_eq_one (H.T0_sq_eq_one hCen hU h48 hP ha) (H.T0_sq_eq_one hCen hU h48 hP hb)
      (H.T0_sq_eq_one hCen hU h48 hP (mul_mem ha hb))
  exact ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, fun x hx => by
    rw [sq]; exact H.T0_sq_eq_one hCen hU h48 hP hx⟩

theorem T0'_elem (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) :
    Assembly.IsElemAbelian 2 (conjSubgroup g T ⊓ kernel48 B T g) := by
  obtain ⟨x, hxX, hxT, -⟩ := H.exists_conj_Tg hCen hU h48 hP
  have e : conjSubgroup g T ⊓ kernel48 B T g = conjSubgroup x (T ⊓ kernel48 B T g) := by
    rw [conjSubgroup_inf, ← hxT, conjSubgroup_eq_self_iff.mpr (H.X_le_normalizer_kernel h48 hxX)]
  rw [e]
  exact isElemAbelian_conjSubgroup (H.T0_elem hCen hU h48 hP) x

theorem T0_comm_T0' (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) :
    ∀ a ∈ T ⊓ kernel48 B T g, ∀ y ∈ conjSubgroup g T ⊓ kernel48 B T g, a * y = y * a := by
  set K := kernel48 B T g with hK
  have hT0e := H.T0_elem hCen hU h48 hP
  set 𝒞 : Set G := {c | ∃ a ∈ T ⊓ K, ∃ y ∈ conjSubgroup g T ⊓ K, c = ⁅a, y⁆} with h𝒞
  have hKX : ∀ x ∈ T ⊔ conjSubgroup g T, ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun x hx k hk =>
    (Subgroup.mem_normalizer_iff.mp (H.X_le_normalizer_kernel h48 hx) k).mp hk
  have hcT : ∀ a ∈ T ⊓ K, ∀ y ∈ conjSubgroup g T ⊓ K, ⁅a, y⁆ ∈ T ⊓ K := by
    intro a ha y hy
    refine ⟨?_, ?_⟩
    · have e : ⁅a, y⁆ = a * (y * a⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact T.mul_mem ha.1 ((Subgroup.mem_normalizer_iff.mp (H.kernel_le_normalizer_T hy.2) a⁻¹).mp
        (T.inv_mem ha.1) |> fun h => by simpa [mul_assoc] using h)
    · have e : ⁅a, y⁆ = (a * y * a⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact K.mul_mem (hKX a (Subgroup.mem_sup_left ha.1) y hy.2 |> fun h => by
        simpa [mul_assoc] using h) (K.inv_mem hy.2)
  have hcTg : ∀ a ∈ T ⊓ K, ∀ y ∈ conjSubgroup g T ⊓ K, ⁅a, y⁆ ∈ conjSubgroup g T ⊓ K := by
    intro a ha y hy
    refine ⟨?_, (hcT a ha y hy).2⟩
    have e : ⁅a, y⁆ = (a * y * a⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact (conjSubgroup g T).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (H.kernel_le_normalizer_Tg ha.2) y).mp hy.1) ((conjSubgroup g T).inv_mem hy.1)
  have hinv : ∀ t ∈ T, ∀ c ∈ 𝒞, t * c * t⁻¹ ∈ 𝒞 := by
    rintro t ht _ ⟨a, ha, y, hy, rfl⟩
    have htX : t ∈ T ⊔ conjSubgroup g T := Subgroup.mem_sup_left ht
    have ha' : t * a * t⁻¹ ∈ T ⊓ K :=
      ⟨T.mul_mem (T.mul_mem ht ha.1) (T.inv_mem ht), hKX t htX a ha.2⟩
    have hz : ⁅t, y⁆ ∈ T ⊓ K := by
      refine ⟨?_, ?_⟩
      · have e : ⁅t, y⁆ = t * (y * t⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
        rw [e]
        exact T.mul_mem ht ((Subgroup.mem_normalizer_iff.mp (H.kernel_le_normalizer_T hy.2) t⁻¹).mp
          (T.inv_mem ht) |> fun h => by simpa [mul_assoc] using h)
      · have e : ⁅t, y⁆ = (t * y * t⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
        rw [e]
        exact K.mul_mem (hKX t htX y hy.2) (K.inv_mem hy.2)
    refine ⟨t * a * t⁻¹, ha', y, hy, ?_⟩
    have e1 : t * ⁅a, y⁆ * t⁻¹ = ⁅t * a * t⁻¹, ⁅t, y⁆ * y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e1]
    have h1 : (t * a * t⁻¹) * ⁅t, y⁆ = ⁅t, y⁆ * (t * a * t⁻¹) := comm_of_isElemAbelian hT0e ha' hz
    have h2 : ⁅t * a * t⁻¹, y⁆ * ⁅t, y⁆ = ⁅t, y⁆ * ⁅t * a * t⁻¹, y⁆ :=
      comm_of_isElemAbelian hT0e (hcT _ ha' y hy) hz
    calc ⁅t * a * t⁻¹, ⁅t, y⁆ * y⁆
        = (t * a * t⁻¹) * ⁅t, y⁆ * (y * (t * a * t⁻¹)⁻¹ * y⁻¹) * ⁅t, y⁆⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = ⁅t, y⁆ * (t * a * t⁻¹) * (y * (t * a * t⁻¹)⁻¹ * y⁻¹) * ⁅t, y⁆⁻¹ := by rw [h1]
      _ = ⁅t, y⁆ * ⁅t * a * t⁻¹, y⁆ * ⁅t, y⁆⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = ⁅t * a * t⁻¹, y⁆ * ⁅t, y⁆ * ⁅t, y⁆⁻¹ := by rw [← h2]
      _ = ⁅t * a * t⁻¹, y⁆ := by group
  set E := Subgroup.closure 𝒞 with hE
  have hE_T : E ≤ T := (Subgroup.closure_le T).mpr fun c hc => by
    obtain ⟨a, ha, y, hy, rfl⟩ := hc
    exact (hcT a ha y hy).1
  have hE_Tg : E ≤ conjSubgroup g T := (Subgroup.closure_le _).mpr fun c hc => by
    obtain ⟨a, ha, y, hy, rfl⟩ := hc
    exact (hcTg a ha y hy).1
  have hTE : T ≤ Subgroup.normalizer (E : Set G) := fun t ht => by
    refine Subgroup.mem_normalizer_fintype fun e he => ?_
    induction he using Subgroup.closure_induction with
    | mem c hc => exact Subgroup.subset_closure (hinv t ht c hc)
    | one => simpa using E.one_mem
    | mul a b _ _ iha ihb =>
      have : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
      rw [this]
      exact E.mul_mem iha ihb
    | inv a _ iha =>
      have : t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
      rw [this]
      exact E.inv_mem iha
  have hEbot : E = ⊥ := by
    by_contra hne
    obtain ⟨b, hbE, hbB, hb1⟩ := H.exists_mem_B_of_normalizes H.T_le_Q H.B_le_T
      H.M_le_normalizer_T hE_T hne hTE
    have : b ∈ B ⊓ conjSubgroup g T := ⟨hbB, hE_Tg hbE⟩
    rw [H.B_inf_Tg hCen hU hP, Subgroup.mem_bot] at this
    exact hb1 this
  intro a ha y hy
  have h1 : ⁅a, y⁆ ∈ E := Subgroup.subset_closure ⟨a, ha, y, hy, rfl⟩
  rw [hEbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem kernel_elem (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) :
    Assembly.IsElemAbelian 2 (kernel48 B T g) := by
  rw [H.kernel48_eq_kernelGen hCen hU h48 hP]
  exact IsElemAbelian.sup_of_commute (H.T0_elem hCen hU h48 hP) (H.T0'_elem hCen hU h48 hP)
    (H.T0_comm_T0' hCen hU h48 hP)

theorem phase1a (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) : Phase1a Q B T g := by
  have hKeq := H.kernel48_eq_kernelGen hCen hU h48 hP
  haveI := H.normal_kernelGen h48
  have hQP := H.quotPair48 hCen hU h48 hP
  obtain ⟨-, hmod⟩ := hQP.models hCen hU
  have hcard : Nat.card ((T.subgroupOf (T ⊔ conjSubgroup g T)).map
      (QuotientGroup.mk' ((kernelGen48 B T g).subgroupOf (T ⊔ conjSubgroup g T)))) =
      (T ⊓ kernelGen48 B T g).relIndex T :=
    (relIndex_eq_card_map_mk (X := T ⊔ conjSubgroup g T) (N := kernelGen48 B T g)
      le_sup_left).symm
  unfold Phase1a
  refine ⟨H.kernel_elem hCen hU h48 hP, hKeq, H.inf_Tg_eq_inf_Qg hCen hU h48 hP, ?_, ?_⟩
  · ext t
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨htT, htK⟩
      exact ⟨htT, Subgroup.mem_centralizer_iff.mpr fun b hb =>
        ((H.T_mem_kernel_iff h48 htT (Subgroup.mem_sup_left htT)).mp htK b hb).symm⟩
    · rintro ⟨htT, htC⟩
      exact ⟨htT, (H.T_mem_kernel_iff h48 htT (Subgroup.mem_sup_left htT)).mpr fun b hb =>
        (Subgroup.mem_centralizer_iff.mp htC b hb).symm⟩
  · rw [hKeq]
    rcases hmod with ⟨f, hf, hT, ⟨e⟩⟩ | ⟨a, ha, hT, ⟨e⟩⟩ | ⟨m, hm, h3, hT, ⟨e⟩⟩
    · exact Or.inl ⟨f, hf, hcard ▸ hT, this, ⟨e⟩⟩
    · exact Or.inr (Or.inl ⟨a, ha, hcard ▸ hT, this, ⟨e⟩⟩)
    · exact Or.inr (Or.inr ⟨m, hm, h3, hcard ▸ hT, this, ⟨e⟩⟩)

end Certified

end Hyp4

end CFSG.RankThree.GF2n.Tim78
