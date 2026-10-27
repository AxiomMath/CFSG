module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightTorus
public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightTwoA
public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightTwoB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem odd_card_of_isRegularTorus {Y : Subgroup G} (hY : IsRegularTorus M V g Y) :
    Odd (Nat.card Y) := by
  have h1 : 0 < Nat.card Y := Nat.card_pos
  rw [hY.2.1] at h1 ⊢
  have hm : E3.mQuot V (UOf M V g) ≠ 0 := by
    intro h0; rw [h0] at h1; simp at h1
  exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, hm⟩) odd_one

theorem exists_le_isSylowIn_inf_centralizer_eq_NOf (h : Hyp64 n M V₀ V g) {Y : Subgroup G}
    (hY : IsFixedPointFreeTorus M V g Y) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpY : p ∣ Nat.card Y) :
    ∃ Z Q : Subgroup G, Z ≤ Y ∧ Z ≤ Q ∧ IsSylowIn p Q (Z ⊔ F11.CTilde M V₀ V) ∧
      V ⊓ centralizer (Q : Set G) = NOf M V g := by
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) p hpY
  have hy₀1 : (y₀ : G) ≠ 1 := by
    intro h1
    have : y₀ = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hy₀
    exact (Fact.out : p.Prime).one_lt.ne' hy₀.symm
  set Z : Subgroup G := zpowers (y₀ : G) with hZ
  have hZY : Z ≤ Y := (zpowers_le).2 y₀.2
  have hZp : IsPGroup p Z := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy₀, pow_one]
  obtain ⟨Q, hQ, hZQ⟩ := exists_isSylowIn_ge p (le_sup_left : Z ≤ Z ⊔ F11.CTilde M V₀ V) hZp
  have hZM : Z ≤ LOf V g ⊓ M := fun z hz => ⟨(hY.1.1 (hZY hz)).1.1, (hY.1.1 (hZY hz)).1.2⟩
  have hsupM : Z ⊔ F11.CTilde M V₀ V ≤ M := sup_le (hZM.trans inf_le_right) (cTilde_le_M _ _ _)
  have hQM : Q ≤ M := hQ.le.trans hsupM
  refine ⟨Z, Q, hZY, hZQ, hQ, ?_⟩
  exact inf_centralizer_eq_of_isPGroup hp2 h.elemAbelian h.le
    (fun e he => he.1.1) (NOf_inf_eq_bot h) hQ.isPGroup
    (hQM.trans h.normalizer_eq.symm.le) (hQM.trans h.le_normalizer₀) hZQ
    (inf_centralizer_zpowers_eq_NOf h hY y₀.2 hy₀1)
    (fun q hq e he => conj_mul_inv_mem_V₀_of_mem_sup h hZM (hQ.le hq) he)

theorem exists_isSylowIn_preBarSub_le_normalizer (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    (hirr : ConjGenerated M V₀ V) {Y : Subgroup G} (hY : IsFixedPointFreeTorus M V g Y)
    {Xbar : Subgroup (MulAut (Vtil V₀ V h.elemAbelian))} (hX1 : Xbar ≠ ⊥)
    (hXM : Xbar ≤ Mbar M V₀ V h.elemAbelian)
    (hXnorm : ∀ m ∈ Mbar M V₀ V h.elemAbelian, ∀ x ∈ Xbar, m * x * m⁻¹ ∈ Xbar)
    (hXB : ⁅Xbar, barSub V₀ V h.elemAbelian (BOf M V g)⁆ = ⊥) {p : ℕ} (hp : p.Prime)
    (hpX : p ∣ Nat.card Xbar) :
    ∃ P : Subgroup G, IsSylowIn p P (preBarSub M V₀ V h.elemAbelian Xbar) ∧
      P ≤ normalizer (NOf M V g : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpn := prime_dvd_two_pow_mQuot_sub_one h hgen hirr hY.1 hX1 hXM hXnorm hXB hp hpX
  have hpY : p ∣ Nat.card Y := by rw [hY.1.2.1]; exact hpn
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 (odd_card_of_isRegularTorus hY.1)) (even_iff_two_dvd.2 hpY)
  obtain ⟨Z, Q, hZY, hZQ, hQ, hCVQ⟩ := exists_le_isSylowIn_inf_centralizer_eq_NOf h hY hp2 hpY
  set C := F11.CTilde M V₀ V with hC
  set X := preBarSub M V₀ V h.elemAbelian Xbar with hX
  have hZM : Z ≤ M := fun z hz => (hY.1.1 (hZY hz)).1.2
  have hMC := le_normalizer_cTilde h
  have hXM' : X ≤ M := inf_le_left
  have hXZC := preBarSub_le_normalizer_sup h hgen hirr hY.1.1 hXM hXnorm hXB hZY
  have hfr := exists_inv_mul_mem_normalizer_of_isSylowIn (hZM.trans hMC) hXZC hZQ hQ
  set N := X ⊓ normalizer (NOf M V g : Set G) with hN
  have hCX : C ≤ X := cTilde_le_preBarSub h Xbar
  have hXN : ∀ x ∈ X, ∃ c ∈ C, c⁻¹ * x ∈ N := by
    intro x hx
    obtain ⟨c, hc, hcx⟩ := hfr x hx
    refine ⟨c, hc, X.mul_mem (X.inv_mem (hCX hc)) hx, ?_⟩
    have hcxM : c⁻¹ * x ∈ M := hXM' (X.mul_mem (X.inv_mem (hCX hc)) hx)
    have := mem_normalizer_inf_centralizer_of_mem_normalizer
      (h.normalizer_eq.symm.le hcxM) hcx
    rwa [hCVQ] at this
  have hsupM : Z ⊔ C ≤ M := sup_le hZM (cTilde_le_M _ _ _)
  have hCn : (C.subgroupOf (Z ⊔ C)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_right).2 (hsupM.trans hMC)
  have hS := hQ.inf_normal le_sup_right hCn
  have hQE : Q ≤ centralizer (NOf M V g : Set G) :=
    Subgroup.le_centralizer_iff.1 (hCVQ ▸ inf_le_right)
  have hSN : Q ⊓ C ≤ N := fun s hs =>
    Subgroup.mem_inf.2 ⟨hCX hs.2, Subgroup.centralizer_le_normalizer _ (hQE hs.1)⟩
  obtain ⟨R, hR, -⟩ := exists_isSylowIn_ge p hSN hS.isPGroup
  exact ⟨R, isSylowIn_of_forall_inv_mul_mem hCX (hXM'.trans hMC) inf_le_left hXN hS hSN hR,
    hR.le.trans inf_le_right⟩

theorem fourteen_eight_two
    (h : Hyp64 n M V₀ V g) (hirr : ConjGenerated M V₀ V)
    {Xbar : Subgroup (MulAut (Vtil V₀ V h.elemAbelian))} (hX1 : Xbar ≠ ⊥)
    (hXM : Xbar ≤ Mbar M V₀ V h.elemAbelian)
    (hXnorm : ∀ m ∈ Mbar M V₀ V h.elemAbelian, ∀ x ∈ Xbar, m * x * m⁻¹ ∈ Xbar)
    (hXB : ⁅Xbar, barSub V₀ V h.elemAbelian (BOf M V g)⁆ = ⊥) {p : ℕ} (hp : p.Prime)
    (hpX : p ∣ Nat.card Xbar) :
    ∃ P : Subgroup G, IsSylowIn p P (preBarSub M V₀ V h.elemAbelian Xbar) ∧
      P ≤ normalizer (NOf M V g : Set G) := by
  obtain ⟨Y, hY⟩ := exists_isFixedPointFreeTorus h
  exact exists_isSylowIn_preBarSub_le_normalizer h (genHyp_of_hyp64 h) hirr hY hX1 hXM hXnorm
    hXB hp hpX

theorem conjGenerated_of_weakClosureSetting {D : Data G} (h : WeakClosureSetting D V₀ V)
    (hV₀ : V₀ ≠ ⊥) : ConjGenerated D.M V₀ V := by
  exact fun v hv hv0 => (h.gen hV₀ v hv hv0).symm

theorem w3Lem148_2_holds :
    W3Lem148_2 G := by
  intro D V₀ V h hV₀ g hO Xbar hX1 hXM hXnorm hXB p hp hpX
  exact fourteen_eight_two (hyp64_of_weakClosureSetting h hO)
    (conjGenerated_of_weakClosureSetting h hV₀) hX1 hXM hXnorm hXB hp hpX

end CFSG.LocalAnalysis.WeakClosure81
