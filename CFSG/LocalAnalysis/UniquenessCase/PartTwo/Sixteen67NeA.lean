module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Cfg1667Ne (M V₀ V W₁ W₂ : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 V
  ne_bot : V₀ ≠ ⊥
  sup_eq : W₁ ⊔ W₂ = V
  inf_eq : W₁ ⊓ W₂ = V₀
  card₁ : Nat.card W₁ = 4 * Nat.card V₀
  card₂ : Nat.card W₂ = 4 * Nat.card V₀
  normalizer_eq : normalizer (V : Set G) = M
  normalizer₀ : normalizer (V₀ : Set G) = M
  isTI : CFSG.CGT.Timmesfeld75.IsTI V₀
  perm : ∀ m ∈ M, (conjSubgroup W₁ m = W₁ ∧ conjSubgroup W₂ m = W₂) ∨
    (conjSubgroup W₁ m = W₂ ∧ conjSubgroup W₂ m = W₁)
  centralizer_le : ∀ w : G, w ∈ W₁ ∨ w ∈ W₂ → w ≠ 1 → centralizer ({w} : Set G) ≤ M
  inf_conj_eq_bot : ∀ y : G, y ∉ M → V ⊓ conjSubgroup W₁ y = ⊥ ∧ V ⊓ conjSubgroup W₂ y = ⊥
  comm_eq_bot : ∀ y : G, conjSubgroup V y ≤ M → ⁅V, conjSubgroup V y⁆ = ⊥

namespace Cfg1667Ne

variable {M V₀ V W₁ W₂ : Subgroup G}

private theorem comm_of_mem_of_isElemAbelian {A : Subgroup G} (hA : IsElemAbelian 2 A)
    {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  Subtype.ext_iff.mp (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem W₁_le (h : Cfg1667Ne M V₀ V W₁ W₂) : W₁ ≤ V := by
  rw [← h.sup_eq]
  exact le_sup_left

theorem W₂_le (h : Cfg1667Ne M V₀ V W₁ W₂) : W₂ ≤ V := by
  rw [← h.sup_eq]
  exact le_sup_right

theorem V₀_le₁ (h : Cfg1667Ne M V₀ V W₁ W₂) : V₀ ≤ W₁ := by
  rw [← h.inf_eq]
  exact inf_le_left

theorem V₀_le₂ (h : Cfg1667Ne M V₀ V W₁ W₂) : V₀ ≤ W₂ := by
  rw [← h.inf_eq]
  exact inf_le_right

theorem V₀_le (h : Cfg1667Ne M V₀ V W₁ W₂) : V₀ ≤ V :=
  (V₀_le₁ h).trans (W₁_le h)

theorem le_M (h : Cfg1667Ne M V₀ V W₁ W₂) : V ≤ M := by
  rw [← h.normalizer_eq]
  exact Subgroup.le_normalizer

theorem le_normalizer₀ (h : Cfg1667Ne M V₀ V W₁ W₂) : M ≤ normalizer (V₀ : Set G) :=
  h.normalizer₀.ge

theorem card_V (h : Cfg1667Ne M V₀ V W₁ W₂) : Nat.card V = 16 * Nat.card V₀ := by
  have hcomm : ∀ x ∈ W₁, ∀ y ∈ W₂, x * y = y * x := fun x hx y hy =>
    comm_of_mem_of_isElemAbelian h.elemAbelian (W₁_le h hx) (W₂_le h hy)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute W₁ W₂ hcomm).1
  rw [h.sup_eq, h.inf_eq, h.card₁, h.card₂] at hcard
  have hx : Nat.card V * Nat.card V₀ = 16 * Nat.card V₀ * Nat.card V₀ := by
    calc Nat.card V * Nat.card V₀ = 4 * Nat.card V₀ * (4 * Nat.card V₀) := hcard
      _ = 16 * Nat.card V₀ * Nat.card V₀ := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := V₀)) hx

theorem W₁_ne_W₂ (h : Cfg1667Ne M V₀ V W₁ W₂) : W₁ ≠ W₂ := by
  intro hEq
  have hV₀W : V₀ = W₁ := by rw [← h.inf_eq, hEq, inf_idem]
  have hpos : 0 < Nat.card W₁ := Nat.card_pos (α := W₁)
  have hcard := h.card₁
  rw [hV₀W] at hcard
  omega

theorem inf_conj_eq_bot' (h : Cfg1667Ne M V₀ V W₁ W₂) {y : G} (hy : y ∉ M) :
    W₁ ⊓ conjSubgroup V y = ⊥ ∧ W₂ ⊓ conjSubgroup V y = ⊥ := by
  have hy' : y⁻¹ ∉ M := fun hmem => hy (by simpa using inv_mem hmem)
  constructor
  · rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    obtain ⟨haW, haV⟩ := Subgroup.mem_inf.mp ha
    have hV' : y * a * y⁻¹ ∈ V := mem_conjSubgroup_iff.mp haV
    have hW' : y * a * y⁻¹ ∈ conjSubgroup W₁ y⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have h1 : y⁻¹ * (y * a * y⁻¹) * y⁻¹⁻¹ = a := by group
      rw [h1]
      exact haW
    have hbot := (h.inf_conj_eq_bot y⁻¹ hy').1
    have hmem : y * a * y⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact ⟨hV', hW'⟩
    have hone : y * a * y⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = 1 := by rw [hone]; group
  · rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    obtain ⟨haW, haV⟩ := Subgroup.mem_inf.mp ha
    have hV' : y * a * y⁻¹ ∈ V := mem_conjSubgroup_iff.mp haV
    have hW' : y * a * y⁻¹ ∈ conjSubgroup W₂ y⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have h1 : y⁻¹ * (y * a * y⁻¹) * y⁻¹⁻¹ = a := by group
      rw [h1]
      exact haW
    have hbot := (h.inf_conj_eq_bot y⁻¹ hy').2
    have hmem : y * a * y⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact ⟨hV', hW'⟩
    have hone : y * a * y⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = 1 := by rw [hone]; group

theorem inf_conj_V₀_eq_bot (h : Cfg1667Ne M V₀ V W₁ W₂) {y : G} (hy : y ∉ M) :
    V ⊓ conjSubgroup V₀ y = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxV, hxV₀⟩ := Subgroup.mem_inf.mp hx
  have hxW : x ∈ V ⊓ conjSubgroup W₁ y :=
    ⟨hxV, E3.conjSubgroup_mono_left y (V₀_le₁ h) hxV₀⟩
  rw [(h.inf_conj_eq_bot y hy).1] at hxW
  exact Subgroup.mem_bot.mp hxW

theorem V₀_inf_conj_eq_bot (h : Cfg1667Ne M V₀ V W₁ W₂) {y : G} (hy : y ∉ M) :
    V₀ ⊓ conjSubgroup V y = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxV₀, hxV⟩ := Subgroup.mem_inf.mp hx
  have hxW : x ∈ W₁ ⊓ conjSubgroup V y := ⟨V₀_le₁ h hxV₀, hxV⟩
  rw [(inf_conj_eq_bot' h hy).1] at hxW
  exact Subgroup.mem_bot.mp hxW

theorem card_inf_conj_le (h : Cfg1667Ne M V₀ V W₁ W₂) {y : G} (hy : y ∉ M) :
    Nat.card (V ⊓ conjSubgroup V y : Subgroup G) ≤ 4 := by
  set P : Subgroup G := V ⊓ conjSubgroup V y with hPdef
  have hWy_le : conjSubgroup W₁ y ≤ conjSubgroup V y :=
    E3.conjSubgroup_mono_left y (W₁_le h)
  have hPVy : P ≤ conjSubgroup V y := by rw [hPdef]; exact inf_le_right
  have hcomm : ∀ a ∈ P, ∀ b ∈ conjSubgroup W₁ y, a * b = b * a := fun a ha b hb =>
    comm_of_mem_of_isElemAbelian (E3.isElemAbelian_conjSubgroup h.elemAbelian y)
      (hPVy ha) (hWy_le hb)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute P (conjSubgroup W₁ y)
    hcomm).1
  have hbot : P ⊓ conjSubgroup W₁ y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxP, hxW⟩ := Subgroup.mem_inf.mp hx
    have hxV : x ∈ V := (Subgroup.mem_inf.mp hxP).1
    have hmem : x ∈ V ⊓ conjSubgroup W₁ y := ⟨hxV, hxW⟩
    rw [(h.inf_conj_eq_bot y hy).1] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hcard' : Nat.card (P ⊔ conjSubgroup W₁ y : Subgroup G) =
      Nat.card P * Nat.card (conjSubgroup W₁ y) := by
    have h1 := hcard
    rw [hbot] at h1
    simpa using h1
  have hsup_le : P ⊔ conjSubgroup W₁ y ≤ conjSubgroup V y := sup_le hPVy hWy_le
  have hleVy : Nat.card (P ⊔ conjSubgroup W₁ y : Subgroup G) ≤
      Nat.card (conjSubgroup V y) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hsup_le)
      (Subgroup.inclusion_injective hsup_le)
  have hVysize : Nat.card (conjSubgroup V y) = 16 * Nat.card V₀ := by
    rw [E3.card_conjSubgroup, card_V h]
  have hWysize : Nat.card (conjSubgroup W₁ y) = 4 * Nat.card V₀ := by
    rw [E3.card_conjSubgroup, h.card₁]
  have hbound : Nat.card P * (4 * Nat.card V₀) ≤ 16 * Nat.card V₀ := by
    calc Nat.card P * (4 * Nat.card V₀) = Nat.card P * Nat.card (conjSubgroup W₁ y) := by
          rw [hWysize]
      _ = Nat.card (P ⊔ conjSubgroup W₁ y : Subgroup G) := hcard'.symm
      _ ≤ Nat.card (conjSubgroup V y) := hleVy
      _ = 16 * Nat.card V₀ := hVysize
  have hbound' : (Nat.card P * 4) * Nat.card V₀ ≤ 16 * Nat.card V₀ := by
    calc (Nat.card P * 4) * Nat.card V₀ = Nat.card P * (4 * Nat.card V₀) := by ring
      _ ≤ 16 * Nat.card V₀ := hbound
  have hP4 : Nat.card P * 4 ≤ 16 :=
    Nat.le_of_mul_le_mul_right hbound' (Nat.card_pos (α := V₀))
  have hP : Nat.card P ≤ 4 := by omega
  simpa [hPdef] using hP

theorem centralizer_le_of_eight_le (h : Cfg1667Ne M V₀ V W₁ W₂) {F : Subgroup G} (hFV : F ≤ V)
    (hF : 8 ≤ Nat.card F) : centralizer (F : Set G) ≤ M := by
  have hcomm : ∀ x ∈ F, ∀ y ∈ W₁, x * y = y * x := fun x hx y hy =>
    comm_of_mem_of_isElemAbelian h.elemAbelian (hFV hx) (W₁_le h hy)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute F W₁ hcomm).1
  have hleV : Nat.card (F ⊔ W₁ : Subgroup G) ≤ Nat.card V :=
    Nat.card_le_card_of_injective (Subgroup.inclusion (sup_le hFV (W₁_le h)))
      (Subgroup.inclusion_injective (sup_le hFV (W₁_le h)))
  have hleV' : Nat.card (F ⊔ W₁ : Subgroup G) ≤ 16 * Nat.card V₀ := by
    rw [← card_V h]
    exact hleV
  have hstep2 : 8 * (4 * Nat.card V₀) ≤ Nat.card F * Nat.card W₁ := by
    rw [h.card₁]
    exact Nat.mul_le_mul_right (4 * Nat.card V₀) hF
  have hb : 32 * Nat.card V₀ ≤ 16 * Nat.card V₀ * Nat.card (F ⊓ W₁ : Subgroup G) := by
    calc 32 * Nat.card V₀ = 8 * (4 * Nat.card V₀) := by ring
      _ ≤ Nat.card F * Nat.card W₁ := hstep2
      _ = Nat.card (F ⊔ W₁ : Subgroup G) * Nat.card (F ⊓ W₁ : Subgroup G) := hcard.symm
      _ ≤ 16 * Nat.card V₀ * Nat.card (F ⊓ W₁ : Subgroup G) :=
            Nat.mul_le_mul_right _ hleV'
  have hb2 : 2 ≤ Nat.card (F ⊓ W₁ : Subgroup G) := by
    have h' : 32 * Nat.card V₀ ≤ (16 * Nat.card (F ⊓ W₁ : Subgroup G)) * Nat.card V₀ := by
      calc 32 * Nat.card V₀ ≤ 16 * Nat.card V₀ * Nat.card (F ⊓ W₁ : Subgroup G) := hb
        _ = 16 * Nat.card (F ⊓ W₁ : Subgroup G) * Nat.card V₀ := by ring
    have := Nat.le_of_mul_le_mul_right h' (Nat.card_pos (α := V₀))
    omega
  have hne : F ⊓ W₁ ≠ ⊥ := by
    intro hbot
    have : Nat.card (F ⊓ W₁ : Subgroup G) = 1 := Subgroup.card_eq_one.mpr hbot
    omega
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have haF : (a : G) ∈ F := (Subgroup.mem_inf.mp a.2).1
  have haW : (a : G) ∈ W₁ := (Subgroup.mem_inf.mp a.2).2
  have ha1 : (a : G) ≠ 1 := fun hh => ha (Subtype.ext hh)
  have hle : centralizer (F : Set G) ≤ centralizer ({(a : G)} : Set G) :=
    Subgroup.centralizer_le (by rintro x (rfl : x = (a : G)); exact haF)
  exact hle.trans (h.centralizer_le (a : G) (Or.inl haW) ha1)

theorem lt_rMV (h : Cfg1667Ne M V₀ V W₁ W₂) : ((mSub V₀ + 1 : ℕ) : ℕ∞) < rMV M V := by
  have hVp : IsPGroup 2 V := IsElemAbelian.isPGroup h.elemAbelian
  have hle : ((mSub V₀ + 2 : ℕ) : ℕ∞) ≤ rMV M V := by
    unfold rMV
    refine le_iInf₂ fun U hU => ?_
    have hUle : U ≤ V := hU.1
    have hUp : IsPGroup 2 U := hVp.to_le hUle
    have hU4 : Nat.card U ≤ 4 := by
      have hnot8 : ¬ 8 ≤ Nat.card U :=
        fun h8 => hU.2 (centralizer_le_of_eight_le h hUle h8)
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hUp
      have hklt : k < 3 := by
        have hpow : 2 ^ k < 2 ^ 3 := by
          rw [← hk]
          norm_num
          exact Nat.lt_of_not_le hnot8
        exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hpow
      calc Nat.card U = 2 ^ k := hk
        _ ≤ 2 ^ 2 := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) (by omega : k ≤ 2)
        _ = 4 := by norm_num
    have hcardV : Nat.card V = 2 ^ (mSub V₀ + 4) := by
      calc Nat.card V = 16 * Nat.card V₀ := card_V h
        _ = 2 ^ 4 * 2 ^ mSub V₀ := by
              rw [card_eq_two_pow_mSub (hVp.to_le (V₀_le h))]
              norm_num
        _ = 2 ^ (4 + mSub V₀) := by rw [pow_add]
        _ = 2 ^ (mSub V₀ + 4) := by rw [add_comm]
    have hcardU : Nat.card V = 2 ^ E3.mQuot V U * Nat.card U :=
      E3.card_eq_two_pow_mul hVp hUle
    have hkey : 2 ^ (mSub V₀ + 4) ≤ 2 ^ (E3.mQuot V U + 2) := by
      calc 2 ^ (mSub V₀ + 4) = Nat.card V := hcardV.symm
        _ = 2 ^ E3.mQuot V U * Nat.card U := hcardU
        _ ≤ 2 ^ E3.mQuot V U * 2 ^ 2 := Nat.mul_le_mul_left _ (by
              calc Nat.card U ≤ 4 := hU4
                _ = 2 ^ 2 := by norm_num)
        _ = 2 ^ (E3.mQuot V U + 2) := by rw [pow_add]
    have hm : mSub V₀ + 4 ≤ E3.mQuot V U + 2 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hkey
    have hm' : mSub V₀ + 2 ≤ E3.mQuot V U := by omega
    exact ENat.natCast_le_natCast.mpr hm'
  calc ((mSub V₀ + 1 : ℕ) : ℕ∞) < ((mSub V₀ + 2 : ℕ) : ℕ∞) :=
        ENat.natCast_lt_natCast.mpr (by omega)
    _ ≤ rMV M V := hle

theorem swap (h : Cfg1667Ne M V₀ V W₁ W₂) : Cfg1667Ne M V₀ V W₂ W₁ := by
  refine ⟨h.elemAbelian, h.ne_bot, ?_, ?_, h.card₂, h.card₁, h.normalizer_eq, h.normalizer₀,
    h.isTI, ?_, ?_, ?_, h.comm_eq_bot⟩
  · rw [sup_comm]
    exact h.sup_eq
  · rw [inf_comm]
    exact h.inf_eq
  · intro m hm
    rcases h.perm m hm with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨hb, ha⟩
    · exact Or.inr ⟨hb, ha⟩
  · intro w hw hw1
    exact h.centralizer_le w hw.symm hw1
  · intro y hy
    obtain ⟨h1, h2⟩ := h.inf_conj_eq_bot y hy
    exact ⟨h2, h1⟩

private theorem conjSubgroup_sup (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊔ B) g = conjSubgroup A g ⊔ conjSubgroup B g := by
  unfold conjSubgroup
  exact Subgroup.map_sup A B _

theorem conj (h : Cfg1667Ne M V₀ V W₁ W₂) (g : G) :
    Cfg1667Ne (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) (conjSubgroup W₁ g)
      (conjSubgroup W₂ g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact E3.isElemAbelian_conjSubgroup h.elemAbelian g
  · exact fun hbot => h.ne_bot (conjSubgroup_eq_bot_iff.mp hbot)
  · simp only [← conjSubgroup_sup, h.sup_eq]
  · simp only [← E3.conjSubgroup_inf, h.inf_eq]
  · simp only [E3.card_conjSubgroup, h.card₁]
  · simp only [E3.card_conjSubgroup, h.card₂]
  · simp only [← E3.conjSubgroup_normalizer, h.normalizer_eq]
  · simp only [← E3.conjSubgroup_normalizer, h.normalizer₀]
  · exact CFSG.LocalAnalysis.WeakClosure81.isTI_conj h.isTI g
  · intro m hm
    set m' : G := g * m * g⁻¹ with hm'def
    have hm'M : m' ∈ M := by rw [hm'def]; exact mem_conjSubgroup_iff.mp hm
    have hmul : g * m = m' * g := by rw [hm'def]; group
    have h₁ : conjSubgroup (conjSubgroup W₁ g) m = conjSubgroup (conjSubgroup W₁ m') g := by
      rw [conjSubgroup_conjSubgroup, hmul, ← conjSubgroup_conjSubgroup]
    have h₂ : conjSubgroup (conjSubgroup W₂ g) m = conjSubgroup (conjSubgroup W₂ m') g := by
      rw [conjSubgroup_conjSubgroup, hmul, ← conjSubgroup_conjSubgroup]
    rcases h.perm m' hm'M with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨h₁.trans (by rw [ha]), h₂.trans (by rw [hb])⟩
    · exact Or.inr ⟨h₁.trans (by rw [ha]), h₂.trans (by rw [hb])⟩
  · intro w hw hw1
    set w' : G := g * w * g⁻¹ with hw'def
    have hw'mem : w' ∈ W₁ ∨ w' ∈ W₂ := by
      rcases hw with hw | hw
      · exact Or.inl (by rw [hw'def]; exact mem_conjSubgroup_iff.mp hw)
      · exact Or.inr (by rw [hw'def]; exact mem_conjSubgroup_iff.mp hw)
    have hw'1 : w' ≠ 1 := by
      intro hzero
      apply hw1
      rw [hw'def] at hzero
      calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
        _ = 1 := by rw [hzero]; group
    have hle := h.centralizer_le w' hw'mem hw'1
    intro x hx
    rw [mem_conjSubgroup_iff]
    apply hle
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    rw [hw'def]
    calc g * x * g⁻¹ * (g * w * g⁻¹) = g * (x * w) * g⁻¹ := by group
      _ = g * (w * x) * g⁻¹ := by rw [hx]
      _ = g * w * g⁻¹ * (g * x * g⁻¹) := by group
  · intro y hyM
    constructor
    · set y' : G := g * y * g⁻¹ with hy'def
      have hy'M : y' ∉ M := fun hy' => hyM (by
        rw [mem_conjSubgroup_iff]; rwa [← hy'def])
      have hyy : g * y = y' * g := by rw [hy'def]; group
      have hc : conjSubgroup (conjSubgroup W₁ g) y = conjSubgroup (conjSubgroup W₁ y') g := by
        rw [conjSubgroup_conjSubgroup, hyy, ← conjSubgroup_conjSubgroup]
      have hinf : (conjSubgroup V g ⊓ conjSubgroup (conjSubgroup W₁ g) y : Subgroup G)
          = conjSubgroup (V ⊓ conjSubgroup W₁ y') g := by
        rw [hc, ← E3.conjSubgroup_inf]
      rw [hinf, conjSubgroup_eq_bot_iff]
      exact (h.inf_conj_eq_bot y' hy'M).1
    · set y' : G := g * y * g⁻¹ with hy'def
      have hy'M : y' ∉ M := fun hy' => hyM (by
        rw [mem_conjSubgroup_iff]; rwa [← hy'def])
      have hyy : g * y = y' * g := by rw [hy'def]; group
      have hc : conjSubgroup (conjSubgroup W₂ g) y = conjSubgroup (conjSubgroup W₂ y') g := by
        rw [conjSubgroup_conjSubgroup, hyy, ← conjSubgroup_conjSubgroup]
      have hinf : (conjSubgroup V g ⊓ conjSubgroup (conjSubgroup W₂ g) y : Subgroup G)
          = conjSubgroup (V ⊓ conjSubgroup W₂ y') g := by
        rw [hc, ← E3.conjSubgroup_inf]
      rw [hinf, conjSubgroup_eq_bot_iff]
      exact (h.inf_conj_eq_bot y' hy'M).2
  · intro y hyle
    set y' : G := g * y * g⁻¹ with hy'def
    have hyy : g * y = y' * g := by rw [hy'def]; group
    have hc : conjSubgroup (conjSubgroup V g) y = conjSubgroup (conjSubgroup V y') g := by
      rw [conjSubgroup_conjSubgroup, hyy, ← conjSubgroup_conjSubgroup]
    have hy'M : conjSubgroup V y' ≤ M := by
      refine (E3.conjSubgroup_le_conjSubgroup_iff (A := conjSubgroup V y') (B := M) g).mp ?_
      rw [← hc]
      exact hyle
    rw [hc, ← E3.conjSubgroup_commutator V (conjSubgroup V y') g, h.comm_eq_bot y' hy'M,
      E3.conjSubgroup_bot]

end Cfg1667Ne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
