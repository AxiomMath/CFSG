module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightBasic
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem NOf_inf_eq_bot (h : Hyp64 n M V₀ V g) : NOf M V g ⊓ V₀ = ⊥ := by
  by_cases hV₀ : V₀ = ⊥
  · rw [hV₀, inf_bot_eq]
  rw [eq_bot_iff]
  intro w hw
  rw [mem_bot]
  by_contra hw1
  have hVgL : conjSubgroup V g ≤ LOf V g := le_sup_right
  have hcen : conjSubgroup V g ≤ centralizer ({w} : Set G) := by
    intro y hy
    rw [mem_centralizer_iff]
    rintro x rfl
    exact ((mem_centralizer_iff.1 (NOf_le_centralizer_L h hw.1)) y (hVgL hy)).symm
  exact h.inCalOStar.1.1.1
    (hcen.trans (centralizer_le_M_of_mem_V₀ (h.isTI hV₀) (h.normalizer₀ hV₀) hw.2 hw1))

theorem inf_centralizer_zpowers_eq_NOf (h : Hyp64 n M V₀ V g) {Y : Subgroup G}
    (hY : IsFixedPointFreeTorus M V g Y) {y : G} (hy : y ∈ Y) (hy1 : y ≠ 1) :
    V ⊓ centralizer ((zpowers y : Subgroup G) : Set G) = NOf M V g := by
  apply le_antisymm
  · rintro v ⟨hv, hvc⟩
    have hyv : y * v = v * y := (mem_centralizer_iff.1 hvc) y (mem_zpowers y)
    exact hY.2 y hy hy1 v hv (by rw [hyv, mul_inv_cancel_right])
  · intro e he
    have hyL : zpowers y ≤ LOf V g := (zpowers_le).2 (hY.1.1 hy).1.1
    exact ⟨he.1.1, centralizer_le hyL (NOf_le_centralizer_L h he)⟩

theorem cTilde_le_preBarSub (h : Hyp64 n M V₀ V g)
    (Xbar : Subgroup (MulAut (Vtil V₀ V h.elemAbelian))) :
    F11.CTilde M V₀ V ≤ preBarSub M V₀ V h.elemAbelian Xbar := by
  intro c hc
  obtain ⟨hcM, hs, h1⟩ := (mem_cTilde_iff h.elemAbelian h.normalizer_eq.symm.le).1 hc
  exact (mem_preBarSub M V₀ V h.elemAbelian Xbar).2 ⟨hcM, hs, h1 ▸ Xbar.one_mem⟩

theorem le_normalizer_cTilde (h : Hyp64 n M V₀ V g) :
    M ≤ normalizer (F11.CTilde M V₀ V : Set G) := by
  exact (normal_subgroupOf_iff_le_normalizer (cTilde_le_M M V₀ V)).1
    (cTilde_subgroupOf_normal h.elemAbelian h.normalizer_eq.symm.le h.le_normalizer₀)

theorem mul_inv_mem_cTilde_of_mem_preBarSub (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    (hirr : ConjGenerated M V₀ V) {Y : Subgroup G} (hY : Y ≤ LOf V g ⊓ M ⊓ conjSubgroup M g)
    {Xbar : Subgroup (MulAut (Vtil V₀ V h.elemAbelian))}
    (hXM : Xbar ≤ Mbar M V₀ V h.elemAbelian)
    (hXnorm : ∀ m ∈ Mbar M V₀ V h.elemAbelian, ∀ x ∈ Xbar, m * x * m⁻¹ ∈ Xbar)
    (hXB : ⁅Xbar, barSub V₀ V h.elemAbelian (BOf M V g)⁆ = ⊥) {x y : G}
    (hx : x ∈ preBarSub M V₀ V h.elemAbelian Xbar) (hy : y ∈ Y) :
    x * y * x⁻¹ * y⁻¹ ∈ F11.CTilde M V₀ V := by
  have hXY := commutator_eq_bot_of_forall_normalizing h hgen hirr hY hXM hXnorm hXB
  have hM : M ≤ normalizer (V : Set G) := h.normalizer_eq.symm.le
  obtain ⟨hxM, hxs, hxX⟩ := (mem_preBarSub M V₀ V h.elemAbelian Xbar).1 hx
  have hyM : y ∈ M := (hY hy).1.2
  have hys : y ∈ stabTil V₀ V :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.le_stabTil hM h.le_normalizer₀ hyM
  have hc := commutator_mem_commutator hxX (actTil_mem_barSub V₀ V h.elemAbelian hy hys)
  rw [hXY, mem_bot, ← map_commutatorElement] at hc
  have hs : x * y * x⁻¹ * y⁻¹ ∈ stabTil V₀ V :=
    mul_mem (mul_mem (mul_mem hxs hys) (inv_mem hxs)) (inv_mem hys)
  refine (mem_cTilde_iff h.elemAbelian hM).2
    ⟨M.mul_mem (M.mul_mem (M.mul_mem hxM hyM) (M.inv_mem hxM)) (M.inv_mem hyM), hs, ?_⟩
  exact hc

theorem preBarSub_le_normalizer_sup (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    (hirr : ConjGenerated M V₀ V) {Y : Subgroup G} (hY : Y ≤ LOf V g ⊓ M ⊓ conjSubgroup M g)
    {Xbar : Subgroup (MulAut (Vtil V₀ V h.elemAbelian))}
    (hXM : Xbar ≤ Mbar M V₀ V h.elemAbelian)
    (hXnorm : ∀ m ∈ Mbar M V₀ V h.elemAbelian, ∀ x ∈ Xbar, m * x * m⁻¹ ∈ Xbar)
    (hXB : ⁅Xbar, barSub V₀ V h.elemAbelian (BOf M V g)⁆ = ⊥) {Z : Subgroup G} (hZY : Z ≤ Y) :
    preBarSub M V₀ V h.elemAbelian Xbar ≤
      normalizer ((Z ⊔ F11.CTilde M V₀ V : Subgroup G) : Set G) := by
  set C := F11.CTilde M V₀ V with hC
  have hMC : M ≤ normalizer (C : Set G) := le_normalizer_cTilde h
  have hZC : Z ≤ normalizer (C : Set G) := fun z hz => hMC (hY (hZY hz)).1.2
  have key : ∀ x ∈ preBarSub M V₀ V h.elemAbelian Xbar, ∀ w ∈ Z ⊔ C, x * w * x⁻¹ ∈ Z ⊔ C := by
    intro x hx w hw
    have hw' : w ∈ ((Z ⊔ C : Subgroup G) : Set G) := hw
    rw [coe_mul_of_left_le_normalizer_right Z C hZC] at hw'
    obtain ⟨z, hz, c, hc, rfl⟩ := Set.mem_mul.1 hw'
    have h1 : x * z * x⁻¹ * z⁻¹ ∈ C :=
      mul_inv_mem_cTilde_of_mem_preBarSub h hgen hirr hY hXM hXnorm hXB hx (hZY hz)
    have h2 : x * c * x⁻¹ ∈ C := (mem_normalizer_iff.1 (hMC hx.1) c).1 hc
    have : x * (z * c) * x⁻¹ = (x * z * x⁻¹ * z⁻¹) * z * (x * c * x⁻¹) := by group
    rw [this]
    exact mul_mem (mul_mem (mem_sup_right h1) (mem_sup_left hz)) (mem_sup_right h2)
  intro x hx
  rw [mem_normalizer_iff]
  intro w
  refine ⟨key x hx w, fun hw => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ hw
  have e : x⁻¹ * (x * w * x⁻¹) * x⁻¹⁻¹ = w := by group
  rwa [e] at this

theorem conj_mul_inv_mem_V₀_of_mem_sup (h : Hyp64 n M V₀ V g) {Z : Subgroup G}
    (hZ : Z ≤ LOf V g ⊓ M) {q : G} (hq : q ∈ Z ⊔ F11.CTilde M V₀ V) {e : G}
    (he : e ∈ NOf M V g) : q * e * q⁻¹ * e⁻¹ ∈ V₀ := by
  set C := F11.CTilde M V₀ V with hC
  have hM : M ≤ normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hZC : Z ≤ normalizer (C : Set G) := fun z hz => le_normalizer_cTilde h (hZ hz).2
  have hq' : q ∈ ((Z ⊔ C : Subgroup G) : Set G) := hq
  rw [coe_mul_of_left_le_normalizer_right Z C hZC] at hq'
  obtain ⟨z, hz, c, hc, rfl⟩ := Set.mem_mul.1 hq'
  have hn : c * e * c⁻¹ * e⁻¹ ∈ V₀ := mem_cTilde_mul_inv h.elemAbelian hM hc he.1.1
  have hze : z * e = e * z := (mem_centralizer_iff.1 (NOf_le_centralizer_L h he)) z (hZ hz).1
  have hzV₀ : z * (c * e * c⁻¹ * e⁻¹) * z⁻¹ ∈ V₀ :=
    (mem_normalizer_iff.1 (h.le_normalizer₀ (hZ hz).2) _).1 hn
  have hz1 : z * e * z⁻¹ * e⁻¹ = 1 := by rw [hze]; group
  have : z * c * e * (z * c)⁻¹ * e⁻¹ =
      z * (c * e * c⁻¹ * e⁻¹) * z⁻¹ * (z * e * z⁻¹ * e⁻¹) := by group
  rw [this, hz1, mul_one]
  exact hzV₀

theorem prime_dvd_two_pow_mQuot_sub_one (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    (hirr : ConjGenerated M V₀ V) {Y : Subgroup G} (hY : IsRegularTorus M V g Y)
    {Xbar : Subgroup (MulAut (Vtil V₀ V h.elemAbelian))} (hX1 : Xbar ≠ ⊥)
    (hXM : Xbar ≤ Mbar M V₀ V h.elemAbelian)
    (hXnorm : ∀ m ∈ Mbar M V₀ V h.elemAbelian, ∀ x ∈ Xbar, m * x * m⁻¹ ∈ Xbar)
    (hXB : ⁅Xbar, barSub V₀ V h.elemAbelian (BOf M V g)⁆ = ⊥) {p : ℕ} (hp : p.Prime)
    (hpX : p ∣ Nat.card Xbar) : p ∣ 2 ^ E3.mQuot V (UOf M V g) - 1 := by
  obtain ⟨-, -, hexp⟩ := fourteen_eight_one h hgen hirr hY hX1 hXM hXnorm hXB
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Xbar) p hpX
  have := orderOf_dvd_of_pow_eq_one (hexp x x.2)
  rwa [Subgroup.orderOf_coe, hx] at this

end CFSG.LocalAnalysis.WeakClosure81
