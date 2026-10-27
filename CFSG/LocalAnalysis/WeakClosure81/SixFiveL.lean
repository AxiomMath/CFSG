module

public import CFSG.LocalAnalysis.WeakClosure81.SixFiveK
import CFSG.LocalAnalysis.WeakClosure81.FourteenTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s65_SixFiveL_relIndex_eq_card {G : Type*} [Group G] [Finite G]
    {U V₀ N : Subgroup G} [IsMulCommutative U] (hU : U = V₀ ⊔ N)
    (hinf : V₀ ⊓ N = ⊥) : N.relIndex U = Nat.card V₀ := by
  have hV₀U : V₀ ≤ U := by rw [hU]; exact le_sup_left
  have hNU : N ≤ U := by rw [hU]; exact le_sup_right
  haveI : (N.subgroupOf U).Normal := inferInstance
  have hsup : N.subgroupOf U ⊔ V₀.subgroupOf U = ⊤ := by
    have h1 : (V₀ ⊔ N).subgroupOf U = ⊤ := by rw [← hU, Subgroup.subgroupOf_self]
    rw [Subgroup.subgroupOf_sup hV₀U hNU] at h1
    rw [sup_comm]
    exact h1
  have hinf' : (N.subgroupOf U) ⊓ (V₀.subgroupOf U) = ⊥ := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · rintro ⟨hxN, hxV⟩
      have h : (x : G) ∈ V₀ ⊓ N := ⟨hxV, hxN⟩
      rw [hinf] at h
      exact Subtype.ext (Subgroup.mem_bot.1 h)
    · intro hx
      rw [hx]
      exact ⟨one_mem _, one_mem _⟩
  calc N.relIndex U = (N.subgroupOf U).relIndex ⊤ := by
        rw [← Subgroup.relIndex_subgroupOf (H := N) (K := U) (L := U) le_rfl,
          Subgroup.subgroupOf_self]
    _ = (N.subgroupOf U).relIndex (V₀.subgroupOf U) := by
        rw [← hsup, Subgroup.relIndex_sup_left]
    _ = ((N.subgroupOf U) ⊓ (V₀.subgroupOf U)).relIndex (V₀.subgroupOf U) :=
        (Subgroup.inf_relIndex_right (H := N.subgroupOf U) (K := V₀.subgroupOf U)).symm
    _ = (⊥ : Subgroup U).relIndex (V₀.subgroupOf U) := by rw [hinf']
    _ = Nat.card (V₀.subgroupOf U) := Subgroup.relIndex_bot_left (V₀.subgroupOf U)
    _ = Nat.card V₀ := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₀U).toEquiv

namespace Hyp65

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem V₀_le_U_of_le_K (h : Hyp65 n M V₀ V g) (hV₀K : V₀ ≤ KOf M V g) :
    V₀ ≤ UOf M V g := by
  rw [← h.V_inf_K]
  exact le_inf h.le hV₀K

theorem Z0_eq_V₀_of_le_K (h : Hyp65 n M V₀ V g) (hV₀K : V₀ ≤ KOf M V g) :
    Z0Of M V₀ g = V₀ := by
  unfold Z0Of
  exact inf_eq_left.2 ((V₀_le_U_of_le_K h hV₀K).trans inf_le_right)

theorem conjV₀_le_B_of_le_K (h : Hyp65 n M V₀ V g) (hV₀K : V₀ ≤ KOf M V g) :
    conjSubgroup V₀ g ≤ BOf M V g := by
  rw [← h.conjV_inf_K]
  exact le_inf (conjSubgroup_mono h.le g) ((conjV₀_le_K_iff h).2 hV₀K)

theorem Y_eq_conjV₀_of_le_K (h : Hyp65 n M V₀ V g) (hV₀K : V₀ ≤ KOf M V g) :
    YOf M V₀ g = conjSubgroup V₀ g := by
  unfold YOf
  exact inf_eq_left.2 ((conjV₀_le_B_of_le_K h hV₀K).trans inf_le_right)

theorem commutator_conjV₀_V_le_V₀ (h : Hyp65 n M V₀ V g) (hV₀K : V₀ ≤ KOf M V g) :
    ⁅conjSubgroup V₀ g, V⁆ ≤ V₀ := by
  rw [← Y_eq_conjV₀_of_le_K h hV₀K]
  exact (commutator_Y_V_le_Z0 h).trans (le_of_eq (Z0_eq_V₀_of_le_K h hV₀K))

theorem centralizer_V_B_eq (h : Hyp65 n M V₀ V g) (hgen : GenHyp M V g)
    (hlK : ∃ l ∈ LOf V g, conjSubgroup V g = conjSubgroup V l) (hV₀K : V₀ ≤ KOf M V g) :
    V ⊓ centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) =
      (V ⊓ conjSubgroup V g) ⊔ V₀ := by
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨hvV, hvC⟩ := hv
    have hvU : v ∈ UOf M V g := by
      by_contra hvU
      have hBU : BOf M V g ≤ UOf M V g := by
        intro b hb
        have hbK : b ∈ KOf M V g :=
          (show BOf M V g ≤ UOf M V g ⊔ BOf M V g from le_sup_right) hb
        have hbN : ⁅b, v⁆ ∈ NOf M V g := by
          have h1 : ⁅b, v⁆ = 1 := by
            rw [commutatorElement_eq_one_iff_mul_comm]
            exact (Subgroup.mem_centralizer_iff.1 hvC) b hb
          rw [h1]
          exact one_mem _
        exact stepB h hgen hlK hvV hvU b hbK hbN
      exact not_B_le_U h hBU
    obtain ⟨x, hxVg, hxM⟩ : ∃ x ∈ conjSubgroup V g, x ∉ M := by
      by_contra hcon
      apply h.not_conjV_le_M
      intro x hx
      by_contra hxM
      exact hcon ⟨x, hx, hxM⟩
    have hxB : x ∉ BOf M V g := fun hb => hxM hb.2
    have hvMg : v ∈ conjSubgroup M g :=
      (show UOf M V g ≤ conjSubgroup M g from inf_le_right) hvU
    have hvOneDual : v ∈ V ⊓ conjSubgroup M g ⊓
        centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) :=
      ⟨⟨hvV, hvMg⟩, hvC⟩
    have hvCT : v ∈ F11.CTilde (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) :=
      h.inCalO1.2.2 hvOneDual
    have hy : ⁅v, x⁆ ∈ conjSubgroup V₀ g := by
      have hmem := (FourteenTwo.mem_cTilde_iff_comm.1 hvCT).2.2 x hxVg
      simpa only [commutatorElement_def] using hmem
    obtain ⟨z, hzV₀, hzx⟩ :=
      exists_commutator_eq_of_V₀_le_K h hgen hlK hV₀K hxVg hxB (⁅v, x⁆) hy
    have hzZ0 : z ∈ Z0Of M V₀ g := by
      rw [Z0_eq_V₀_of_le_K h hV₀K]
      exact hzV₀
    have hyY : ⁅v, x⁆ ∈ YOf M V₀ g := by
      rw [Y_eq_conjV₀_of_le_K h hV₀K]
      exact hy
    have hz_inv : ⁅z⁻¹, x⁆ = (⁅v, x⁆)⁻¹ := by
      have h1 : ⁅z⁻¹, x⁆ = z⁻¹ * (⁅v, x⁆)⁻¹ * z := by
        rw [commutatorElement_inv_left, ← commutatorElement_inv z x, hzx]
      rw [h1]
      have hzy : Commute z (⁅v, x⁆) := Z0_Y_comm h hzZ0 hyY
      rw [hzy.inv_left.inv_right.eq]
      group
    have hk1 : ⁅v * z⁻¹, x⁆ = 1 := by
      rw [commutatorElement_mul_left_eq_conj_mul, hz_inv]
      have hvy : Commute v (⁅v, x⁆) :=
        Subgroup.mem_centralizer_iff.1 (Y_le_centralizer_U h hyY) v hvU
      have hvconj : v * (⁅v, x⁆)⁻¹ * v⁻¹ = (⁅v, x⁆)⁻¹ := by
        rw [hvy.inv_right.eq]
        group
      rw [hvconj]
      group
    have hvzK : v * z⁻¹ ∈ KOf M V g :=
      (KOf M V g).mul_mem
        ((show UOf M V g ≤ KOf M V g from le_sup_left) hvU)
        ((KOf M V g).inv_mem ((show V₀ ≤ KOf M V g from hV₀K) hzV₀))
    have hvzN : ⁅v * z⁻¹, x⁆ ∈ NOf M V g := by
      rw [hk1]
      exact one_mem _
    have hvzB : v * z⁻¹ ∈ BOf M V g :=
      stepA h hgen hlK hxVg hxB (v * z⁻¹) hvzK hvzN
    have hvz_inf : v * z⁻¹ ∈ V ⊓ conjSubgroup V g :=
      ⟨V.mul_mem hvV (V.inv_mem (h.le hzV₀)),
        (show BOf M V g ≤ conjSubgroup V g from inf_le_left) hvzB⟩
    have hfin : v = (v * z⁻¹) * z := by group
    rw [hfin]
    exact ((V ⊓ conjSubgroup V g) ⊔ V₀).mul_mem
      (Subgroup.mem_sup_left hvz_inf) (Subgroup.mem_sup_right hzV₀)
  · refine sup_le ?_ ?_
    · refine le_inf inf_le_left ?_
      rw [← NOf_eq M V g h.le_M]
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.1 (N_le_centralizer_L h hn)) b
        ((show BOf M V g ≤ LOf V g from
          (show BOf M V g ≤ conjSubgroup V g from inf_le_left).trans le_sup_right) hb)
    · refine le_inf h.le ?_
      rw [← Z0_eq_V₀_of_le_K h hV₀K]
      exact Z0_le_centralizer_B h

theorem mQuot_N_eq_of_U_eq (h : Hyp65 n M V₀ V g) (hU : UOf M V g = V₀ ⊔ NOf M V g) :
    E3.mQuot V (NOf M V g) = E3.mQuot V (conjSubgroup M g) + mSub V₀ := by
  haveI hVcomm : IsMulCommutative V := h.elemAbelian.1
  haveI hUcomm : IsMulCommutative (UOf M V g) :=
    IsMulCommutative.of_comm fun a b =>
      Subtype.ext (by
        simpa only [Subgroup.coe_mul] using
          setLike_mul_comm (s := V)
            ((show UOf M V g ≤ V from inf_le_left) a.2)
            ((show UOf M V g ≤ V from inf_le_left) b.2))
  have h1 := E3.mQuot_add (V := V) (U := NOf M V g) (U' := UOf M V g)
    (show NOf M V g ≤ UOf M V g from inf_le_left)
    (show UOf M V g ≤ V from inf_le_left)
  rw [h1]
  have hVU : E3.mQuot V (UOf M V g) = E3.mQuot V (conjSubgroup M g) := by
    unfold E3.mQuot
    rw [show (UOf M V g).relIndex V = (conjSubgroup M g).relIndex V by
      rw [UOf, Subgroup.inf_relIndex_left]]
  have hUN : E3.mQuot (UOf M V g) (NOf M V g) = mSub V₀ := by
    unfold E3.mQuot
    rw [s65_SixFiveL_relIndex_eq_card (U := UOf M V g) (V₀ := V₀) (N := NOf M V g)
      hU (V₀_inf_N h)]
    rw [card_eq_two_pow_mSub ((CFSG.Open.IsElemAbelian.isPGroup h.elemAbelian).to_le h.le)]
    exact padicValNat.prime_pow (mSub V₀)
  rw [hUN, hVU]
  exact add_comm _ _

theorem rMV_le_mQuot_N (h : Hyp65 n M V₀ V g) :
    rMV M V ≤ (E3.mQuot V (NOf M V g) : ℕ∞) := by
  have hNV : NOf M V g ≤ V :=
    (show NOf M V g ≤ UOf M V g from inf_le_left).trans inf_le_left
  have hnc : ¬ centralizer (NOf M V g : Set G) ≤ M := by
    intro hc
    exact h.L_not_le_M ((Subgroup.le_centralizer_iff.1 (N_le_centralizer_L h)).trans hc)
  unfold rMV
  exact iInf₂_le (NOf M V g) ⟨hNV, hnc⟩

section Certified

theorem inCalOStar_of_V₀_le_K (h : Hyp65 n M V₀ V g) (hV₀K : V₀ ≤ KOf M V g)
    (hne : (V ⊓ conjSubgroup V g) ⊔ V₀ ≠ V ⊓ conjSubgroup M g) :
    InCalOStar n M V₀ V g := by
  obtain ⟨hKn, hKset, hshape, hlK, -⟩ := six_five_one h
  exact ⟨h.inCalO1.1, KOf M V g, hKn, hKset, hshape, hlK,
    commutator_conjV₀_V_le_V₀ h hV₀K,
    centralizer_V_B_eq h h.genHyp h.exists_conj hV₀K, hne⟩

theorem six_five_four (h : Hyp65 n M V₀ V g) (hV₀K : V₀ ≤ KOf M V g)
    (hnot : ¬ InCalOStar n M V₀ V g) :
    UOf M V g = V₀ ⊔ NOf M V g ∧
      rMV M V ≤ ((mSub V₀ + E3.mQuot V (conjSubgroup M g) : ℕ) : ℕ∞) := by
  have hNsup : (V ⊓ conjSubgroup V g) ⊔ V₀ = V ⊓ conjSubgroup M g := by
    by_contra hne
    exact hnot (inCalOStar_of_V₀_le_K h hV₀K hne)
  have hU : UOf M V g = V₀ ⊔ NOf M V g := by
    change V ⊓ conjSubgroup M g = V₀ ⊔ NOf M V g
    rw [← hNsup, ← NOf_eq M V g h.le_M, sup_comm]
  refine ⟨hU, ?_⟩
  have h9 := rMV_le_mQuot_N h
  have h8 := mQuot_N_eq_of_U_eq h hU
  calc rMV M V ≤ (E3.mQuot V (NOf M V g) : ℕ∞) := h9
    _ = ((E3.mQuot V (conjSubgroup M g) + mSub V₀ : ℕ) : ℕ∞) := by rw [h8]
    _ = ((mSub V₀ + E3.mQuot V (conjSubgroup M g) : ℕ) : ℕ∞) := by rw [add_comm]

theorem inCalOStar_of_lt_rMV (h : Hyp65 n M V₀ V g)
    (hr : ((mSub V₀ + n : ℕ) : ℕ∞) < rMV M V) : InCalOStar n M V₀ V g := by
  by_cases hV₀K : V₀ ≤ KOf M V g
  · by_contra hnot
    obtain ⟨-, hrle⟩ := six_five_four h hV₀K hnot
    have hCA : ((mSub V₀ + E3.mQuot V (conjSubgroup M g) : ℕ) : ℕ∞) ≤
        ((mSub V₀ + n : ℕ) : ℕ∞) :=
      WithTop.coe_le_coe.2 (add_le_add le_rfl (h.mQuot_le))
    exact absurd hr (not_lt.2 (hrle.trans hCA))
  · have hlt := hr
    rw [rMV_eq_mSub h hV₀K] at hlt
    exact absurd hlt
      (not_lt.2 (WithTop.coe_le_coe.2 (Nat.le_add_right (mSub V₀) n)))

end Certified

end Hyp65

end CFSG.LocalAnalysis.WeakClosure81
