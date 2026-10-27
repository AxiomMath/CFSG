module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Pair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43Main
public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveCent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_bot_geom {D : Data G} (h22 : R1622 D) (h41 : R16_41 D) (h42 : R16_42 D)
    (h431 : R16_43_1 D) (hkitB : OmegaKitB) (hkitC : OmegaKitC) (hkitE : OmegaKitE16)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV)
    (hc : Case167_1 D ⊥ V hV L) {g : G} (h1 : InCalO 1 D.M ⊥ V g) :
    Hyp612Sym 1 D.M V g ∧ PrimGeom D.M V g := by
  have hVg : ¬ conjSubgroup V g ≤ D.M := h1.1.1
  have hVM : ¬ V ≤ conjSubgroup D.M g := h1.2.1
  have hm : E3.mQuot (conjSubgroup V g) D.M ≤ 1 := h1.2.2.1
  have hVg2 : IsPGroup 2 (conjSubgroup V g) :=
    E3.isPGroup_conjSubgroup (CFSG.Open.IsElemAbelian.isPGroup hV) g
  have hmq : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M) =
      E3.mQuot (conjSubgroup V g) D.M := by
    unfold E3.mQuot
    rw [Subgroup.inf_relIndex_left]
  have hm1 : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M) = 1 := by
    rw [hmq]
    have hne : E3.mQuot (conjSubgroup V g) D.M ≠ 0 := by
      intro h0
      have h0' : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M) = 0 := hmq.trans h0
      have heq : conjSubgroup V g ⊓ D.M = conjSubgroup V g :=
        (E3.mQuot_eq_zero_iff hVg2 inf_le_left).1 h0'
      exact hVg (heq ▸ inf_le_right)
    omega
  have hA : (conjSubgroup V g ⊓ D.M) ∈ E3.gammaSet V 1 D.M :=
    ⟨inf_le_right, g, inf_le_left, hm1⟩
  have hyp : Hyp1643 D ⊥ V 1 (conjSubgroup V g ⊓ D.M) g :=
    ⟨Or.inr ⟨rfl, rfl⟩, hA, inf_le_left⟩
  obtain ⟨hVgM, hG⟩ := s16c1G43_pack h42 h431 hkitB hkitC hkitE hS hc hyp hVM
  have hy' := s16c1G43_hyp1643_inv (D := D) (V := V) hG.relIndex_U
  have hnot' := s16c1G43_not_le_inv (M := D.M) (V := V) hVgM
  obtain ⟨-, hG'⟩ := s16c1G43_pack h42 h431 hkitB hkitC hkitE hS hc hy' hnot'
  have hM := hS.setting.hyp151.hyp125.normalizer_eq
  have hV64 := s16c1G43_card_V hc
  have hlt := s16c1G43_lt_rStar h22 h41 hS hc
  exact ⟨s16c1G43_hyp612Sym hV hM hV64 hlt hVgM hVM hG hG'.half, hG⟩

theorem s16c1_G47_rotation_mem {n : ℕ} {M V : Subgroup G} {g : G} (h : Hyp612Sym n M V g)
    {w w' : G} (hw : w ∈ V) (hww : w * w = 1) (hw'w' : w' * w' = 1) {k : ℕ}
    (hk : (w * w') ^ k ∈ CKOf M V g) : (w * w') ^ (2 * k) ∈ UOf M V g := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hw'i : w'⁻¹ = w' := inv_eq_of_mul_eq_one_right hw'w'
  have h1 : w * (w * w') * w⁻¹ = (w * w')⁻¹ := by
    rw [mul_inv_rev, hwi, hw'i]
    calc w * (w * w') * w = (w * w) * w' * w := by group
      _ = w' * w := by rw [hww, one_mul]
  have h2 : w * (w * w') ^ k * w⁻¹ = ((w * w') ^ k)⁻¹ := by
    rw [← conj_pow, h1, inv_pow]
  have h3 : w * ((w * w') ^ k)⁻¹ * w⁻¹ = (w * w') ^ k := by
    calc w * ((w * w') ^ k)⁻¹ * w⁻¹ = (w * (w * w') ^ k * w⁻¹)⁻¹ := by group
      _ = (w * w') ^ k := by rw [h2, inv_inv]
  have h4 : ⁅(w * w') ^ k, w⁆ = (w * w') ^ (2 * k) := by
    rw [commutatorElement_def, pow_mul', pow_two]
    calc (w * w') ^ k * w * ((w * w') ^ k)⁻¹ * w⁻¹
        = (w * w') ^ k * (w * ((w * w') ^ k)⁻¹ * w⁻¹) := by group
      _ = (w * w') ^ k * (w * w') ^ k := by rw [h3]
  rw [← h4]
  exact h.commutator_CKOf_V_mem_U hk hw

theorem s16c1_G47_bot_ord {M V K : Subgroup G} {g : G} (h : Hyp612Sym 1 M V g)
    (hG : PrimGeom M V g)
    (hK : (K : Set G) = ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) *
      ((V ⊓ conjSubgroup M g : Subgroup G) : Set G)) {w w' : G} (hw : w ∈ V)
    (hw' : w' ∈ conjSubgroup V g) (hww : w * w = 1) (hw'w' : w' * w' = 1) {n : ℕ}
    (hodd : Odd n) (hn1 : n ≠ 1) (hn : ∀ j : ℕ, (w * w') ^ j ∈ K ↔ n ∣ j) :
    n = 3 ∨ n = 5 := by
  have hKeq : K = KOf M V g :=
    SetLike.coe_injective (hK.trans h.coe_KOf_eq_BOf_mul_UOf.symm)
  subst hKeq
  have hKL : KOf M V g ≤ LOf V g := by
    unfold KOf LOf UOf BOf
    exact sup_le_sup inf_le_left inf_le_left
  have hUab : ∀ x ∈ UOf M V g, ∀ y ∈ UOf M V g, x * y = y * x :=
    fun x hx y hy => h.elemAbelian.comm hx.1 hy.1
  obtain ⟨k, hk1, hk6, hkc⟩ := s16c1_G47_pair (K := KOf M V g) (U := UOf M V g)
    (B := BOf M V g) (N := NOf M V g) le_sup_left le_sup_right
    (fun k hk => by
      obtain ⟨u, hu, b, hb, rfl⟩ := (h.mem_KOf_iff).1 hk
      exact ⟨u, hu, b, hb, rfl⟩)
    hUab (fun x hx => by simpa [pow_two] using h.elemAbelian.2 x hx.1)
    (fun x hx => by simpa [pow_two] using h.elemAbelian_conj.2 x hx.1) rfl
    (fun k hk k' hk' => h.commutator_KOf_KOf_mem_N hk hk')
    (fun n hn k hk => (h.mul_comm_of_mem_NOf hn (hKL hk)).symm)
    (fun b hb hcomm => by
      refine Subgroup.mem_inf.2
        ⟨h.centralizer_le' (Subgroup.mem_inf.2 ⟨hb.1, ?_⟩), h.conjV_le_conjM hb.1⟩
      exact Subgroup.mem_centralizer_iff.2 hcomm)
    hG.card_U hG.card_B hG.card_N
    (w := w) (w' := w')
    (fun u hu => by
      rw [h.elemAbelian.comm hw hu.1]
      group)
    (fun b hb => h.commutator_mem_U hb hw)
    (fun b hb => by
      rw [h.elemAbelian_conj.comm hw' hb.1]
      group)
    (fun u hu => h.commutator_mem_B hu hw')
  have hy : (w * w') ^ k ∈ CKOf M V g := by
    refine (h.mem_CKOf_iff).2 ⟨?_, fun x hx => hkc x hx⟩
    exact (LOf V g).pow_mem ((LOf V g).mul_mem (Subgroup.mem_sup_left hw)
      (Subgroup.mem_sup_right hw')) k
  have hrot := s16c1_G47_rotation_mem h hw hww hw'w' hy
  have hdvd2 : n ∣ 2 * k := (hn (2 * k)).1 (Subgroup.mem_sup_left hrot)
  have hdvd : n ∣ k := Nat.Coprime.dvd_of_dvd_mul_left hodd.coprime_two_right hdvd2
  have hle : n ≤ k := Nat.le_of_dvd (by omega) hdvd
  obtain ⟨m, hm⟩ := hodd
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
