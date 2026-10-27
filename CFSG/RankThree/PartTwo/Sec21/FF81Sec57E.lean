module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec57D
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec57C
import CFSG.RankThree.PartTwo.Sec21.FF81Sec52M
import CFSG.RankThree.PartTwo.Sec21.FF81Sec53
import CFSG.RankThree.PartTwo.Sec21.FF81Sec54
import CFSG.RankThree.PartTwo.Sec21.FF81Sec56C
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CSyl
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open P51 (V e)

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

theorem S57.conj_mem_cen {g a y : G} (hy : y ∈ Cen a) : g * y * g⁻¹ ∈ Cen (g * a * g⁻¹) :=
  Subgroup.mem_centralizer_singleton_iff.mpr
    (S57.conj_comm (Subgroup.mem_centralizer_singleton_iff.mp hy))

theorem S57.cen_eq_of_zpowers_eq {x y : G} (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    Cen x = Cen y := by
  have key : ∀ {x y : G}, x ∈ Subgroup.zpowers y → Cen y ≤ Cen x := fun hx c hc => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((Commute.zpow_right
      (show Commute c _ from Subgroup.mem_centralizer_singleton_iff.mp hc) k).eq)
  refine le_antisymm (key ?_) (key ?_)
  · rw [h]; exact Subgroup.mem_zpowers y
  · rw [← h]; exact Subgroup.mem_zpowers x

theorem S57.card_inf_cen_conj {A : Subgroup G} {g : G} (hg : g ∈ A) (x : G) :
    Nat.card ↥(A ⊓ Cen (g * x * g⁻¹)) = Nat.card ↥(A ⊓ Cen x) := by
  have hmap : (A ⊓ Cen x).map (MulAut.conj g).toMonoidHom = A ⊓ Cen (g * x * g⁻¹) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hy
      exact Subgroup.mem_inf.mpr ⟨A.mul_mem (A.mul_mem hg h1) (A.inv_mem hg),
        S57.conj_mem_cen h2⟩
    · intro hz
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hz
      refine ⟨g⁻¹ * z * g, Subgroup.mem_inf.mpr ⟨A.mul_mem (A.mul_mem (A.inv_mem hg) h1) hg, ?_⟩,
        by simp [MulAut.conj_apply, mul_assoc]⟩
      have := S57.conj_mem_cen (g := g⁻¹) h2
      rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group, inv_inv] at this
  rw [← hmap]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem S57.map_conj_cen (g a : G) :
    (Cen a).map (MulAut.conj g).toMonoidHom = Cen (g * a * g⁻¹) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact S57.conj_mem_cen hy
  · intro hz
    refine ⟨g⁻¹ * z * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := S57.conj_mem_cen (g := g⁻¹) hz
    rwa [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group, inv_inv] at this

theorem S57.card_cen2_conj (g a x : G) :
    Nat.card ↥(Cen (g * a * g⁻¹) ⊓ Cen (g * x * g⁻¹)) = Nat.card ↥(Cen a ⊓ Cen x) := by
  rw [← S57.map_conj_cen, ← S57.map_conj_cen,
    ← Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem S57.mem_inf_cen_conj {A : Subgroup G} {g x z : G} (hg : g ∈ A)
    (hz : z ∈ A ⊓ Cen (g * x * g⁻¹)) : g⁻¹ * z * g ∈ A ⊓ Cen x := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨A.mul_mem (A.mul_mem (A.inv_mem hg) h1) hg, ?_⟩
  have := S57.conj_mem_cen (g := g⁻¹) h2
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group, inv_inv] at this

section E

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
  (hJs : OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ Cen s₀)
include h5 hJs

theorem FF81Sec5.card_β_sup {M' : Subgroup G} (hM' : M' ≤ M₅₇ b b₁ b₂ b₃ s₀) :
    Nat.card ↥(Subgroup.zpowers (β' b₂ b₃) ⊔ M') = 3 * Nat.card M' := by
  have hc : ∀ x ∈ Subgroup.zpowers (β' b₂ b₃), ∀ y ∈ M', x * y = y * x := fun x hx y hy => by
    have hyβ : y * β' b₂ b₃ = β' b₂ b₃ * y := Subgroup.mem_centralizer_singleton_iff.mp
      (((S57.M_le_cenS hJs).trans (S57.cenS_pair_le_left _ _)) (hM' hy))
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_right (show Commute y (β' b₂ b₃) from hyβ) k).eq).symm
  have hinf : Subgroup.zpowers (β' b₂ b₃) ⊓ M' = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ hM').trans (h5.zpowers_β_inf_M hJs).le)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).1
  rwa [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, h5.β_orderOf] at hcard

theorem FF81Sec5.β_sup_le_cen {x : G} (hx : x ∈ M₅₇ b b₁ b₂ b₃ s₀) :
    Subgroup.zpowers (β' b₂ b₃) ⊔ (M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen x) ≤ Cen (β' b₂ b₃) ⊓ Cen x := by
  have hMβ : M₅₇ b b₁ b₂ b₃ s₀ ≤ Cen (β' b₂ b₃) :=
    (S57.M_le_cenS hJs).trans (S57.cenS_pair_le_left _ _)
  refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, ?_⟩)) (inf_le_inf_right _ hMβ)
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp (hMβ hx)).symm

theorem FF81Sec5.card_le_cen {x : G} (hx : x ∈ M₅₇ b b₁ b₂ b₃ s₀) :
    3 * Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen x) ≤ Nat.card ↥(Cen (β' b₂ b₃) ⊓ Cen x) := by
  rw [← h5.card_β_sup hJs inf_le_left]
  exact Subgroup.card_le_of_le (h5.β_sup_le_cen hJs hx)

theorem FF81Sec5.cen_eq_of_card {x : G} (hx : x ∈ M₅₇ b b₁ b₂ b₃ s₀)
    (hle : Nat.card ↥(Cen (β' b₂ b₃) ⊓ Cen x) ≤ 3 * Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen x)) :
    Cen (β' b₂ b₃) ⊓ Cen x = Subgroup.zpowers (β' b₂ b₃) ⊔ (M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen x) := by
  refine (Subgroup.eq_of_le_of_card_ge (h5.β_sup_le_cen hJs hx) ?_).symm
  rwa [h5.card_β_sup hJs inf_le_left]

theorem FF81Sec5.cen_β_b (hSR3 : KF_Sp6ShortRoot3) (hCls : KF_Sp6Cls)
    (hmod : StatedClassicalModel (M₅₇ b b₁ b₂ b₃ s₀) .PSp 3 2 1)
    (hbJ : b ∈ OUp 3 (CenS (Subgroup.closure {b₂, b₃}))) :
    Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen b) = 108 ∧
      Cen (β' b₂ b₃) ⊓ Cen b = Subgroup.zpowers (β' b₂ b₃) ⊔ (M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen b) := by
  have hB := h5.basis
  have hA : ∀ {a : G}, a ∈ ({b, b₁, b₂ * b₃} : Set G) → a ∈ A₁sub b b₁ b₂ b₃ :=
    fun ha => Subgroup.subset_closure ha
  have h108 : Nat.card ↥(L ⊓ Cen (β' b₂ b₃)) = 108 :=
    hSR3 G L hB.hyp.model b₁ b₂ b₃ hB.hb₁ hB.hb₂ hB.hb₃ hB.elem hB.selfcen hB.monoL_stab s₀
      h5.hs₀L h5.hs₀ (h5.s₀_comm (hA (by simp))).symm (h5.s₀_comm h5.u_mem_A₁).symm h5.hs₀b
  have hbβ : b * β' b₂ b₃ = β' b₂ b₃ * b := h5.β_comm_A₁ (hA (by simp))
  have hle : Cen (β' b₂ b₃) ⊓ Cen b ≤ Subgroup.zpowers b ⊔ (L ⊓ Cen (β' b₂ b₃)) := by
    intro y hy
    obtain ⟨hyβ, hyb⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨i, l, hl, rfl⟩ := hB.cen_dec' h5.opp_eq_bot hyb
    have hbi : b ^ i ∈ Cen (β' b₂ b₃) := Subgroup.zpow_mem _
      (Subgroup.mem_centralizer_singleton_iff.mpr hbβ) i
    have hlβ : l ∈ Cen (β' b₂ b₃) := by
      have := (Cen (β' b₂ b₃)).mul_mem ((Cen (β' b₂ b₃)).inv_mem hbi) hyβ
      rwa [inv_mul_cancel_left] at this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers b i))
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hl, hlβ⟩))
  have hnor : L ⊓ Cen (β' b₂ b₃) ≤ Subgroup.normalizer
      ((Subgroup.zpowers b : Subgroup G) : Set G) :=
    fun l hl => Subgroup.mem_normalizer_fintype fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hlb : l * b = b * l :=
        Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC (Subgroup.mem_inf.mp hl).1)
      rw [((Commute.zpow_right (show Commute l b from hlb) k).eq), mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers b k
  have h324 : Nat.card ↥(Cen (β' b₂ b₃) ⊓ Cen b) ≤ 324 := by
    have h1 := S57.card_sup_le hnor
    rw [Nat.card_zpowers, h5.orderOf_b, h108] at h1
    exact (Subgroup.card_le_of_le hle).trans h1
  have hbM : b ∈ M₅₇ b b₁ b₂ b₃ s₀ := Subgroup.mem_sup_left hbJ
  have h3 := h5.card_le_cen hJs hbM
  have hcls := (hCls G _ hmod).1 b hbM h5.orderOf_b
  have hc : Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen b) = 108 := by omega
  exact ⟨hc, h5.cen_eq_of_card hJs hbM (by omega)⟩

theorem FF81Sec5.b₃_not_mem_zpowers_b₂ : b₃ ∉ Subgroup.zpowers b₂ := by
  intro h
  obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers).mpr h
  simp only at hn
  have h3 : b₂ ^ 3 = 1 := h5.basis.B_cube (h5.ε_e2 ▸ h5.ε_mem _)
  have hmod : h5.ε (((n : ℕ) : ZMod 3) • e 2) = b₃ := by
    rw [h5.ε_smul, h5.ε_e2, ZMod.val_natCast, ← hn]
    conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, h3, one_pow, mul_one]
  have hmod' := hmod.trans h5.ε_e3.symm
  have hne : ∀ c : ZMod 3, c • e 2 ≠ (e 3 : V) := by decide
  exact hne _ (h5.ε_inj hmod')

theorem FF81Sec5.cen_β_u (hKF : KF_Sp6Levi) (hCls : KF_Sp6Cls)
    (hmod : StatedClassicalModel (M₅₇ b b₁ b₂ b₃ s₀) .PSp 3 2 1)
    (e6 : ↥(OUp 3 (CenS (Subgroup.closure {b₂, b₃}))) ≃* Equiv.Perm (Fin 6)) :
    Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen (b₂ * b₃)) = 2160 ∧
      Cen (β' b₂ b₃) ⊓ Cen (b₂ * b₃) =
        Subgroup.zpowers (β' b₂ b₃) ⊔ (M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen (b₂ * b₃)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB := h5.basis
  have hb₂B : b₂ ∈ B := h5.ε_e2 ▸ h5.ε_mem _
  have hb₃B : b₃ ∈ B := h5.ε_e3 ▸ h5.ε_mem _
  obtain ⟨m, hm, hiff, -, -⟩ := h5.setup
  have hb₂ : Subgroup.zpowers b₂ ∈ ConjLines B b := by
    have h := (hiff (e 2) (by decide)).mpr (by rcases hm with rfl | rfl <;> decide)
    rwa [h5.ε_e2] at h
  obtain ⟨-, g, hg⟩ := hb₂
  have hzg : Subgroup.zpowers (g * b * g⁻¹) = Subgroup.zpowers b₂ := by
    rw [← hg, conjBy, MonoidHom.map_zpowers]; rfl
  have hCb₂ : Cen b₂ = Cen (g * b * g⁻¹) := S57.cen_eq_of_zpowers_eq hzg.symm
  set x := g⁻¹ * b₃ * g with hx
  have hb₃x : b₃ = g * x * g⁻¹ := by rw [hx]; group
  have hxb : x ∈ Cen b := by
    have h1 : b₃ ∈ Cen (g * b * g⁻¹) := by
      rw [← hCb₂]; exact Subgroup.mem_centralizer_singleton_iff.mpr (hB.B_comm hb₃B hb₂B)
    have := S57.conj_mem_cen (g := g⁻¹) h1
    rwa [show g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b by group, inv_inv] at this
  have hxb' : Commute x b := Subgroup.mem_centralizer_singleton_iff.mp hxb
  have hbx : b ∈ Cen x := Subgroup.mem_centralizer_singleton_iff.mpr hxb'.symm.eq
  obtain ⟨i, l, hl, hxl⟩ := hB.cen_dec' h5.opp_eq_bot hxb
  have hl' : l = (b ^ i)⁻¹ * x := by rw [hxl]; group
  have hl1 : l ≠ 1 := by
    rintro rfl
    rw [mul_one] at hxl
    refine h5.b₃_not_mem_zpowers_b₂ hJs ?_
    rw [← hzg, hb₃x, hxl, ← conj_zpow]
    exact Subgroup.zpow_mem_zpowers _ i
  have hb3 : b ^ 3 = 1 := by rw [← h5.orderOf_b, pow_orderOf_eq_one]
  have hx3 : x ^ 3 = 1 := by
    have : x = g⁻¹ * b₃ * g⁻¹⁻¹ := by rw [inv_inv]
    rw [this, conj_pow, hB.B_cube hb₃B]; group
  have hl3 : l ^ 3 = 1 := by
    rw [hl', (((hxb'.symm.zpow_left i).inv_left)).mul_pow, hx3, mul_one, inv_pow,
      ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow, inv_one]
  have hlo : orderOf l = 3 := orderOf_eq_prime hl3 hl1
  have hcl : Cen b ⊓ Cen x ≤ Cen l := fun z hz => by
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hz
    have hzb : Commute z b := Subgroup.mem_centralizer_singleton_iff.mp h1
    have hzx : Commute z x := Subgroup.mem_centralizer_singleton_iff.mp h2
    rw [hl']
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((hzb.zpow_right i).inv_right.mul_right hzx).eq
  have hbbx : b ∈ Cen b ⊓ Cen x :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hbx⟩
  have hle : Cen b ⊓ Cen x ≤ Subgroup.zpowers b ⊔ (L ⊓ Cen l) := by
    intro y hy
    obtain ⟨j, l', hl'L, rfl⟩ := hB.cen_dec' h5.opp_eq_bot (Subgroup.mem_inf.mp hy).1
    have hl'c : l' ∈ Cen b ⊓ Cen x := by
      have := (Cen b ⊓ Cen x).mul_mem ((Cen b ⊓ Cen x).inv_mem
        ((Cen b ⊓ Cen x).zpow_mem hbbx j)) hy
      rwa [inv_mul_cancel_left] at this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers b j))
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hl'L, hcl hl'c⟩))
  have hnor : L ⊓ Cen l ≤ Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) :=
    fun l₀ hl₀ => Subgroup.mem_normalizer_fintype fun y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hlb : Commute l₀ b :=
        Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC (Subgroup.mem_inf.mp hl₀).1)
      rw [(hlb.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers b k
  have hLl := (hCls G L hB.hyp.model).1 l hl hlo
  have h6480 : Nat.card ↥(Cen b ⊓ Cen x) ≤ 6480 := by
    have h1 := S57.card_sup_le hnor
    rw [Nat.card_zpowers, h5.orderOf_b] at h1
    have := (Subgroup.card_le_of_le hle).trans h1
    omega
  have hβu : β' b₂ b₃ * (b₂ * b₃)⁻¹ = b₃ := by
    have hc : b₂ * b₃ = b₃ * b₂ := hB.B_comm hb₂B hb₃B
    calc β' b₂ b₃ * (b₂ * b₃)⁻¹ = b₂ * b₃ * b₂⁻¹ := by rw [β']; group
      _ = b₃ := by rw [hc]; group
  have hK : Cen (β' b₂ b₃) ⊓ Cen (b₂ * b₃) ≤ Cen b₂ ⊓ Cen b₃ := fun z hz => by
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hz
    have hzβ : Commute z (β' b₂ b₃) := Subgroup.mem_centralizer_singleton_iff.mp h1
    have hzu : Commute z (b₂ * b₃) := Subgroup.mem_centralizer_singleton_iff.mp h2
    have hz3 : Commute z b₃ := hβu ▸ hzβ.mul_right hzu.inv_right
    have hz2 : Commute z b₂ := by
      have := hzu.mul_right hz3.inv_right
      rwa [mul_inv_cancel_right] at this
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hz2.eq,
      Subgroup.mem_centralizer_singleton_iff.mpr hz3.eq⟩
  have hcard : Nat.card ↥(Cen (β' b₂ b₃) ⊓ Cen (b₂ * b₃)) ≤ 6480 := by
    calc _ ≤ Nat.card ↥(Cen b₂ ⊓ Cen b₃) := Subgroup.card_le_of_le hK
      _ = Nat.card ↥(Cen b ⊓ Cen x) := by rw [hCb₂, hb₃x, S57.card_cen2_conj]
      _ ≤ 6480 := h6480
  have huM : b₂ * b₃ ∈ M₅₇ b b₁ b₂ b₃ s₀ := Subgroup.mem_sup_right (h5.A₁_le_H hKF h5.u_mem_A₁)
  have hJu : OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen (b₂ * b₃) :=
    fun j hj => by
    obtain ⟨h2, h3⟩ := mem_cenS_pair_iff.mp (OUp_le _ hj)
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hj, Subgroup.mem_centralizer_singleton_iff.mpr
      ((Commute.mul_right (show Commute j b₂ from h2) (show Commute j b₃ from h3)).eq)⟩
  have h5d : 5 ∣ Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen (b₂ * b₃)) :=
    (show 5 ∣ 720 by norm_num).trans (S57.card_J e6 ▸ Subgroup.card_dvd_of_le hJu)
  have hc : Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen (b₂ * b₃)) = 2160 := by
    rcases (hCls G _ hmod).1 _ huM h5.orderOf_u with h | h | h
    · exact h
    · rw [h] at h5d; norm_num at h5d
    · rw [h] at h5d; norm_num at h5d
  exact ⟨hc, h5.cen_eq_of_card hJs huM (by omega)⟩

theorem FF81Sec5.mem_of_pow2 {M' : Subgroup G} (hM' : M' ≤ M₅₇ b b₁ b₂ b₃ s₀) {x : G}
    (hx : x ∈ Subgroup.zpowers (β' b₂ b₃) ⊔ M') {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ M' := by
  obtain ⟨a, ha, m, hm, rfl⟩ := h5.mem_β_sup hJs hM' hx
  have hmβ : Commute m (β' b₂ b₃) := Subgroup.mem_centralizer_singleton_iff.mp
    (((S57.M_le_cenS hJs).trans (S57.cenS_pair_le_left _ _)) (hM' hm))
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hcm : Commute (β' b₂ b₃ ^ j) m := (hmβ.zpow_right j).symm
  have h1 : (β' b₂ b₃ ^ j) ^ 2 ^ k = (m ^ 2 ^ k)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hcm.mul_pow]; exact hk
  have hin : (β' b₂ b₃ ^ j) ^ 2 ^ k ∈ Subgroup.zpowers (β' b₂ b₃) ⊓ M₅₇ b b₁ b₂ b₃ s₀ :=
    Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem _ (Subgroup.zpow_mem_zpowers _ j) _,
      (by rw [h1]; exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (hM' hm) _))⟩
  rw [h5.zpowers_β_inf_M hJs, Subgroup.mem_bot] at hin
  have h3 : (β' b₂ b₃ ^ j) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h5.β_cube, one_zpow]
  have hcop : (2 ^ k).gcd 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
  have h1' : β' b₂ b₃ ^ j = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hin, h3⟩
    rwa [hcop, pow_one] at this
  rw [h1', one_mul]; exact hm

variable (hCls : KF_Sp6Cls) (hmod : StatedClassicalModel (M₅₇ b b₁ b₂ b₃ s₀) .PSp 3 2 1)
  (hbM : b ∈ M₅₇ b b₁ b₂ b₃ s₀) (huM : b₂ * b₃ ∈ M₅₇ b b₁ b₂ b₃ s₀)
  (hb : Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen b) = 108 ∧
    Cen (β' b₂ b₃) ⊓ Cen b = Subgroup.zpowers (β' b₂ b₃) ⊔ (M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen b))
  (hu : Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen (b₂ * b₃)) = 2160 ∧
    Cen (β' b₂ b₃) ⊓ Cen (b₂ * b₃) =
      Subgroup.zpowers (β' b₂ b₃) ⊔ (M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen (b₂ * b₃)))
include hCls hmod hbM huM hb hu

theorem FF81Sec5.cen_cls {y : G} (hy : y ∈ M₅₇ b b₁ b₂ b₃ s₀) (hy3 : orderOf y = 3)
    (hc : Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen y) = 108 ∨
      Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen y) = 2160) :
    Cen (β' b₂ b₃) ⊓ Cen y ≤ Subgroup.zpowers (β' b₂ b₃) ⊔ M₅₇ b b₁ b₂ b₃ s₀ ∧
      Nat.card ↥(Cen (β' b₂ b₃) ⊓ Cen y) = 3 * Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen y) := by
  have hx : ∃ x ∈ M₅₇ b b₁ b₂ b₃ s₀, orderOf x = 3 ∧
      Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen x) = Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen y) ∧
      Cen (β' b₂ b₃) ⊓ Cen x = Subgroup.zpowers (β' b₂ b₃) ⊔ (M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen x) := by
    rcases hc with h | h
    · exact ⟨b, hbM, h5.orderOf_b, hb.1.trans h.symm, hb.2⟩
    · exact ⟨_, huM, h5.orderOf_u, hu.1.trans h.symm, hu.2⟩
  obtain ⟨x, hxM, hx3, hcard, hxeq⟩ := hx
  obtain ⟨m, hmM, rfl⟩ := (hCls G _ hmod).2.1 x hxM y hy hx3 hy3 hcard
  have hMβ : M₅₇ b b₁ b₂ b₃ s₀ ≤ Cen (β' b₂ b₃) :=
    (S57.M_le_cenS hJs).trans (S57.cenS_pair_le_left _ _)
  have hmβ := hMβ hmM
  refine ⟨fun z hz => ?_, ?_⟩
  · have h1 := S57.mem_inf_cen_conj hmβ hz
    rw [hxeq] at h1
    have h2 : m⁻¹ * z * m ∈ Subgroup.zpowers (β' b₂ b₃) ⊔ M₅₇ b b₁ b₂ b₃ s₀ :=
      (sup_le_sup_left (inf_le_left (b := Cen x)) (Subgroup.zpowers (β' b₂ b₃))) h1
    have hm' : m ∈ Subgroup.zpowers (β' b₂ b₃) ⊔ M₅₇ b b₁ b₂ b₃ s₀ := Subgroup.mem_sup_right hmM
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hm' h2) (Subgroup.inv_mem _ hm')
    rwa [show m * (m⁻¹ * z * m) * m⁻¹ = z by group] at this
  · rw [S57.card_inf_cen_conj hmβ, S57.card_inf_cen_conj hmM, hxeq,
      h5.card_β_sup hJs inf_le_left]

theorem FF81Sec5.key_fusion {s : G} (hsM : s ∈ M₅₇ b b₁ b₂ b₃ s₀) (hs2 : orderOf s = 2)
    (hs5 : 5 ∣ Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen s))
    (hF1 : Cen (β' b₂ b₃) ⊓ Cen s =
      Subgroup.zpowers (β' b₂ b₃) ⊔ (M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen s))
    {g : G} (hg : g ∈ Cen (β' b₂ b₃)) (hτ : g * s * g⁻¹ ∈ M₅₇ b b₁ b₂ b₃ s₀) :
    g ∈ Subgroup.zpowers (β' b₂ b₃) ⊔ M₅₇ b b₁ b₂ b₃ s₀ := by
  have hMβ : M₅₇ b b₁ b₂ b₃ s₀ ≤ Cen (β' b₂ b₃) :=
    (S57.M_le_cenS hJs).trans (S57.cenS_pair_le_left _ _)
  have hτ2 : orderOf (g * s * g⁻¹) = 2 := by
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective s
    simpa [MulAut.conj_apply, hs2] using h
  obtain ⟨γ, hγ, hγ3, hγc, k, hk, hk2, hkγ⟩ := (hCls G _ hmod).2.2.2.1 _ hτ hτ2
  obtain ⟨hγM, hγτ⟩ := Subgroup.mem_inf.mp hγ
  obtain ⟨hkM, hkτ⟩ := Subgroup.mem_inf.mp hk
  have hpull : ∀ {w : G}, w ∈ M₅₇ b b₁ b₂ b₃ s₀ → w ∈ Cen (g * s * g⁻¹) → w * w = 1 →
      g⁻¹ * w * g ∈ M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen s := by
    intro w hwM hwτ hw2
    have h1 : g⁻¹ * w * g ∈ Cen (β' b₂ b₃) ⊓ Cen s :=
      S57.mem_inf_cen_conj hg (Subgroup.mem_inf.mpr ⟨hMβ hwM, hwτ⟩)
    rw [hF1] at h1
    refine h5.mem_of_sq hJs inf_le_left h1 ?_
    calc g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
      _ = 1 := by rw [hw2]; group
  have hkk : k * k = 1 := by rw [← sq, ← hk2, pow_orderOf_eq_one]
  have hk' := hpull hkM hkτ hkk
  have hγk' := hpull ((M₅₇ b b₁ b₂ b₃ s₀).mul_mem hγM hkM) ((Cen _).mul_mem hγτ hkτ) (by
    calc γ * k * (γ * k) = γ * (k * γ * k⁻¹) * (k * k) := by group
      _ = 1 := by rw [hkγ, hkk]; group)
  have hγ' : g⁻¹ * γ * g ∈ M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen s := by
    have : g⁻¹ * γ * g = g⁻¹ * (γ * k) * g * (g⁻¹ * k * g)⁻¹ := by group
    rw [this]; exact Subgroup.mul_mem _ hγk' (Subgroup.inv_mem _ hk')
  have hγ'M := (Subgroup.mem_inf.mp hγ').1
  have hγ'3 : orderOf (g⁻¹ * γ * g) = 3 := by
    have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective γ
    simpa [MulAut.conj_apply, hγ3] using h
  have hcc : Nat.card ↥(Cen (β' b₂ b₃) ⊓ Cen γ) =
      Nat.card ↥(Cen (β' b₂ b₃) ⊓ Cen (g⁻¹ * γ * g)) := by
    conv_lhs => rw [show γ = g * (g⁻¹ * γ * g) * g⁻¹ by group]
    exact S57.card_inf_cen_conj hg _
  have hPγ := h5.cen_cls hJs hCls hmod hbM huM hb hu hγM hγ3 hγc
  have hQ := h5.card_le_cen hJs hγ'M
  have h648 := (hCls G _ hmod).2.2.1 s hsM hs2 hs5 _ hγ' hγ'3
  have hc' : Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen (g⁻¹ * γ * g)) = 108 ∨
      Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen (g⁻¹ * γ * g)) = 2160 := by
    rcases (hCls G _ hmod).1 _ hγ'M hγ'3 with h | h | h
    · exact Or.inr h
    · exact absurd h h648
    · exact Or.inl h
  have hPγ' := h5.cen_cls hJs hCls hmod hbM huM hb hu hγ'M hγ'3 hc'
  have hceq : Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen (g⁻¹ * γ * g)) =
      Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen γ) := by omega
  obtain ⟨m, hmM, hm⟩ := (hCls G _ hmod).2.1 _ hγ'M γ hγM hγ'3 hγ3 hceq
  have hyγ : m * g⁻¹ * γ * (m * g⁻¹)⁻¹ = γ := by
    calc m * g⁻¹ * γ * (m * g⁻¹)⁻¹ = m * (g⁻¹ * γ * g) * m⁻¹ := by group
      _ = γ := hm
  have hy : m * g⁻¹ ∈ Cen (β' b₂ b₃) ⊓ Cen γ := by
    refine Subgroup.mem_inf.mpr ⟨(Cen _).mul_mem (hMβ hmM) ((Cen _).inv_mem hg), ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc m * g⁻¹ * γ = m * g⁻¹ * γ * (m * g⁻¹)⁻¹ * (m * g⁻¹) := by group
      _ = γ * (m * g⁻¹) := by rw [hyγ]
  have h1 := hPγ.1 hy
  rw [show g = (m * g⁻¹)⁻¹ * m by group]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) (Subgroup.mem_sup_right hmM)

end E

section T

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
  (hJs : OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ Cen s₀)
include h5 hJs

theorem FF81Sec5.T_max {s : G}
    (hkey : ∀ g ∈ Cen (β' b₂ b₃), g * s * g⁻¹ ∈ M₅₇ b b₁ b₂ b₃ s₀ →
      g ∈ Subgroup.zpowers (β' b₂ b₃) ⊔ M₅₇ b b₁ b₂ b₃ s₀)
    (hF1 : Cen (β' b₂ b₃) ⊓ Cen s =
      Subgroup.zpowers (β' b₂ b₃) ⊔ (M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen s))
    (hcs : Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen s) = 23040) (hs2 : orderOf s = 2)
    {T : Subgroup G} (hTle : T ≤ M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen s) (hT : Nat.card T = 512) (hsT : s ∈ T)
    (huniq : ∀ y ∈ T, (∀ t ∈ T, y * t = t * y) → orderOf y = 2 →
      5 ∣ Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen y) → y = s) :
    ∀ P : Subgroup G, P ≤ Cen (β' b₂ b₃) → IsPGroup 2 P → T ≤ P → P = T := by
  intro P hPC hP2 hTP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMβ : M₅₇ b b₁ b₂ b₃ s₀ ≤ Cen (β' b₂ b₃) :=
    (S57.M_le_cenS hJs).trans (S57.cenS_pair_le_left _ _)
  have hsM : s ∈ M₅₇ b b₁ b₂ b₃ s₀ := (Subgroup.mem_inf.mp (hTle hsT)).1
  have hmaxM : ∀ Q : Subgroup G, Q ≤ M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen s → IsPGroup 2 Q → T ≤ Q →
      Q = T := by
    intro Q hQ hQ2 hTQ
    obtain ⟨a, ha⟩ := hQ2.exists_card_eq
    have hdvd : 2 ^ a ∣ 23040 := ha ▸ hcs ▸ Subgroup.card_dvd_of_le hQ
    have ha9 : a ≤ 9 := by
      by_contra h
      have : 2 ^ 10 ∣ 23040 := (pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    refine (Subgroup.eq_of_le_of_card_ge hTQ ?_).symm
    rw [ha, hT]
    calc 2 ^ a ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) ha9
      _ = 512 := by norm_num
  by_contra hne
  have hlt : T.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm (fun x hx => ?_) hTP)
    have : (⟨x, hx⟩ : P) ∈ T.subgroupOf P := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  haveI := hP2.isNilpotent
  obtain ⟨n, hnN, hnT⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent _ hlt)
  have hn₀T : (n : G) ∉ T := fun h => hnT (Subgroup.mem_subgroupOf.mpr h)
  have hnorm : ∀ {c : ↥P}, c ∈ Subgroup.normalizer ((T.subgroupOf P : Subgroup ↥P) : Set ↥P) →
      ∀ t ∈ T, (c : G) * t * (c : G)⁻¹ ∈ T := by
    intro c hc t ht
    have h1 := (Subgroup.mem_normalizer_iff.mp hc ⟨t, hTP ht⟩).mp (Subgroup.mem_subgroupOf.mpr ht)
    simpa using Subgroup.mem_subgroupOf.mp h1
  have hn1 := hnorm hnN
  have hn2 : ∀ t ∈ T, (n : G)⁻¹ * t * (n : G)⁻¹⁻¹ ∈ T := by
    have := hnorm (Subgroup.inv_mem _ hnN)
    simpa using this
  set n₀ : G := (n : G) with hn₀
  have hzT : n₀ * s * n₀⁻¹ ∈ T := hn1 s hsT
  have hcent : ∀ t ∈ T, n₀ * s * n₀⁻¹ * t = t * (n₀ * s * n₀⁻¹) := by
    intro t ht
    have ht' : n₀⁻¹ * t * n₀ ∈ Cen s := by
      have := (Subgroup.mem_inf.mp (hTle (hn2 t ht))).2
      rwa [inv_inv] at this
    have hc : n₀⁻¹ * t * n₀ * s = s * (n₀⁻¹ * t * n₀) :=
      Subgroup.mem_centralizer_singleton_iff.mp ht'
    calc n₀ * s * n₀⁻¹ * t = n₀ * (s * (n₀⁻¹ * t * n₀)) * n₀⁻¹ := by group
      _ = n₀ * (n₀⁻¹ * t * n₀ * s) * n₀⁻¹ := by rw [hc]
      _ = t * (n₀ * s * n₀⁻¹) := by group
  have hzo : orderOf (n₀ * s * n₀⁻¹) = 2 := by
    have h := orderOf_injective (MulAut.conj n₀).toMonoidHom (MulAut.conj n₀).injective s
    simpa [MulAut.conj_apply, hs2] using h
  have hzM : n₀ * s * n₀⁻¹ ∈ M₅₇ b b₁ b₂ b₃ s₀ := (Subgroup.mem_inf.mp (hTle hzT)).1
  have hn₀C : n₀ ∈ Cen (β' b₂ b₃) := hPC n.2
  obtain ⟨a, ha, m, hm, hnam⟩ := h5.mem_β_sup hJs le_rfl (hkey n₀ hn₀C hzM)
  have hz' : n₀ * s * n₀⁻¹ = m * s * m⁻¹ := by
    have hw : m * s * m⁻¹ ∈ Cen (β' b₂ b₃) := hMβ ((M₅₇ b b₁ b₂ b₃ s₀).mul_mem
      ((M₅₇ b b₁ b₂ b₃ s₀).mul_mem hm hsM) ((M₅₇ b b₁ b₂ b₃ s₀).inv_mem hm))
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hc : Commute (m * s * m⁻¹) (β' b₂ b₃ ^ k) :=
      (show Commute (m * s * m⁻¹) (β' b₂ b₃) from
        Subgroup.mem_centralizer_singleton_iff.mp hw).zpow_right k
    calc n₀ * s * n₀⁻¹ = β' b₂ b₃ ^ k * (m * s * m⁻¹) * (β' b₂ b₃ ^ k)⁻¹ := by
          rw [hnam]; group
      _ = m * s * m⁻¹ := by rw [← hc.eq]; group
  have hz5 : 5 ∣ Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen (n₀ * s * n₀⁻¹)) := by
    rw [hz', S57.card_inf_cen_conj hm, hcs]; norm_num
  have hzs := huniq _ hzT hcent hzo hz5
  have hn₀s : n₀ ∈ Cen s := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc n₀ * s = n₀ * s * n₀⁻¹ * n₀ := by group
      _ = s * n₀ := by rw [hzs]
  have hn₀D : n₀ ∈ Subgroup.zpowers (β' b₂ b₃) ⊔ (M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen s) := by
    rw [← hF1]; exact Subgroup.mem_inf.mpr ⟨hn₀C, hn₀s⟩
  obtain ⟨k2, hk2⟩ := hP2 n
  have hk2' : n₀ ^ 2 ^ k2 = 1 := by
    rw [hn₀, ← Subgroup.coe_pow, hk2, Subgroup.coe_one]
  have hn₀Ms := h5.mem_of_pow2 hJs inf_le_left hn₀D hk2'
  have hQ := hmaxM (P ⊓ (M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen s)) inf_le_right (hP2.to_le inf_le_left)
    (le_inf hTP hTle)
  exact hn₀T (hQ ▸ Subgroup.mem_inf.mpr ⟨n.2, hn₀Ms⟩)

end T

theorem ff81_5_7b_of (hKF : KF_Sp6Levi) (hCls : KF_Sp6Cls)
    (hSR3 : KF_Sp6ShortRoot3) : FF81_5_7b := by
  intro hHolt G _ _ b L B b₁ b₂ b₃ t₀ s₀ h5 _ c hmod _ _
  obtain ⟨-, -, ⟨⟨e6⟩, hJs, hbJ, -⟩, -, -, c6, hD⟩ := id c
  obtain ⟨t, ht⟩ := h5.exists_t₃
  obtain ⟨hsM, hcs, hF1⟩ := h5.cen_β_sstar hJs ht hKF hCls hmod c6 hD e6
  have hs2 := h5.orderOf_sstar ht
  have hMβ : M₅₇ b b₁ b₂ b₃ s₀ ≤ Cen (β' b₂ b₃) :=
    (S57.M_le_cenS hJs).trans (S57.cenS_pair_le_left _ _)
  have hbM : b ∈ M₅₇ b b₁ b₂ b₃ s₀ := Subgroup.mem_sup_left hbJ
  have huM : b₂ * b₃ ∈ M₅₇ b b₁ b₂ b₃ s₀ := Subgroup.mem_sup_right (h5.A₁_le_H hKF h5.u_mem_A₁)
  have hb := h5.cen_β_b hJs hSR3 hCls hmod hbJ
  have hu := h5.cen_β_u hJs hKF hCls hmod e6
  have hs5 : 5 ∣ Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen (t * s₀ * t⁻¹)) := by rw [hcs]; norm_num
  have hkey : ∀ g ∈ Cen (β' b₂ b₃), g * (t * s₀ * t⁻¹) * g⁻¹ ∈ M₅₇ b b₁ b₂ b₃ s₀ →
      g ∈ Subgroup.zpowers (β' b₂ b₃) ⊔ M₅₇ b b₁ b₂ b₃ s₀ := fun g hg hτ =>
    h5.key_fusion hJs hCls hmod hbM huM hb hu hsM hs2 hs5 hF1 hg hτ
  obtain ⟨T, hTle, hT, hsT, huniq⟩ := ((hCls G _ hmod).2.2.2.2 _ hsM hs2 hs5).2
  refine le_antisymm (h5.β_sup_M_le hJs) ?_
  refine S57.holt_mod hHolt (Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) hMβ ?_ (h5.zpowers_β_inf_M hJs) hmod hsM
    hs2 (hTle.trans (inf_le_left.trans hMβ)) (hTle.trans inf_le_right) hsT
    (IsPGroup.of_card (n := 9) (hT.trans (by norm_num)))
    (h5.T_max hJs hkey hF1 hcs hs2 hTle hT hsT huniq) ?_
  · intro c hc x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcb : Commute c (β' b₂ b₃ ^ k) :=
      (show Commute c (β' b₂ b₃) from Subgroup.mem_centralizer_singleton_iff.mp hc).zpow_right k
    rw [hcb.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k
  · intro g hg h
    have h2 : g⁻¹ * (t * s₀ * t⁻¹) * g * (g⁻¹ * (t * s₀ * t⁻¹) * g) = 1 := by
      have hss : t * s₀ * t⁻¹ * (t * s₀ * t⁻¹) = 1 := by
        rw [← sq, ← hs2, pow_orderOf_eq_one]
      calc g⁻¹ * (t * s₀ * t⁻¹) * g * (g⁻¹ * (t * s₀ * t⁻¹) * g)
          = g⁻¹ * (t * s₀ * t⁻¹ * (t * s₀ * t⁻¹)) * g := by group
        _ = 1 := by rw [hss]; group
    have hM := h5.mem_of_sq hJs le_rfl h h2
    have := hkey g⁻¹ ((Cen _).inv_mem hg) (by rwa [inv_inv])
    simpa using Subgroup.inv_mem _ this

end CFSG.RankThree.PartTwo.Sec21.FF81
