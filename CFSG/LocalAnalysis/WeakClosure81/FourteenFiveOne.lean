module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenFiveSetup
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFiveTorus
public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightTwoA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace FourteenFive

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

section Certified


theorem not_two_le_mQuot (h15 : Hyp15 M V₀ V) (h : Hyp65 n M V₀ V g)
    (hV₀K : ¬ V₀ ≤ KOf M V g) : ¬ 2 ≤ E3.mQuot V (conjSubgroup M g) := by
  intro h2
  obtain ⟨Y, hYL, hYcard, hYfix⟩ := exists_torus h h2
  have hYne1 : Nat.card Y ≠ 1 := by
    rw [hYcard]
    have hm2 : 4 ≤ 2 ^ E3.mQuot V (conjSubgroup M g) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ E3.mQuot V (conjSubgroup M g) := Nat.pow_le_pow_right (by norm_num) h2
    omega
  obtain ⟨p, hp, hpY⟩ := Nat.exists_prime_and_dvd hYne1
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (Nat.card Y) := by
    rw [hYcard]
    have hm : E3.mQuot V (conjSubgroup M g) ≠ 0 := by omega
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, hm⟩) odd_one
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpY)
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) p hpY
  have hy₀1 : (y₀ : G) ≠ 1 := by
    intro h1
    have : y₀ = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hy₀
    exact hp.one_lt.ne' hy₀.symm
  set Z : Subgroup G := zpowers (y₀ : G) with hZdef
  have hZY : Z ≤ Y := (zpowers_le).2 y₀.2
  have hy₀Z : (y₀ : G) ∈ Z := Subgroup.mem_zpowers (y₀ : G)
  have hZp : IsPGroup p Z := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy₀, pow_one]
  have hZM : Z ≤ LOf V g ⊓ M := fun z hz => hYL (hZY hz)
  have hZL : Z ≤ LOf V g := hZM.trans inf_le_left
  have hZC : Z ≤ F11.CTilde M V₀ V :=
    (hZM.trans (le_of_eq (inf_comm (LOf V g) M))).trans (inf_LOf_le_cTilde h hV₀K)
  have hZfix : V ⊓ centralizer (Z : Set G) ≤ NOf M V g := by
    intro v hv
    obtain ⟨hvV, hvC⟩ := hv
    have hyv : (y₀ : G) * v * (y₀ : G)⁻¹ = v := by
      have hcomm := Subgroup.mem_centralizer_iff.1 hvC (y₀ : G) (Subgroup.mem_zpowers (y₀ : G))
      rw [hcomm, mul_inv_cancel_right]
    exact hYfix (y₀ : G) (hZY hy₀Z) hy₀1 v hvV hyv
  have hNOfV : NOf M V g ≤ V := by
    rw [NOf, UOf]
    exact inf_le_left.trans inf_le_left
  have hNOfV₀ : NOf M V g ⊓ V₀ = ⊥ := by
    rw [inf_comm]
    exact h.V₀_inf_N
  have hNOfZ : NOf M V g ≤ centralizer (Z : Set G) :=
    (Subgroup.le_centralizer_iff (H := NOf M V g) (K := Z)).2
      (hZL.trans (Subgroup.le_centralizer_iff.1 h.N_le_centralizer_L))
  have hZV : V ⊓ centralizer (Z : Set G) = NOf M V g := by
    refine le_antisymm hZfix ?_
    intro v hv
    exact ⟨hNOfV hv, hNOfZ hv⟩
  obtain ⟨Q, hQ, hZQ⟩ :=
    exists_isSylowIn_ge p (le_sup_left : Z ≤ Z ⊔ F11.CTilde M V₀ V) hZp
  have hsupM : Z ⊔ F11.CTilde M V₀ V ≤ M :=
    sup_le (hZM.trans inf_le_right) (cTilde_le_M _ _ _)
  have hQM : Q ≤ M := hQ.le.trans hsupM
  have hQC : Q ≤ F11.CTilde M V₀ V := hQ.le.trans (le_of_eq (sup_eq_right.2 hZC))
  have hQE : ∀ q ∈ Q, ∀ e ∈ NOf M V g, q * e * q⁻¹ * e⁻¹ ∈ V₀ := by
    intro q hq e he
    exact (FourteenTwo.mem_cTilde_iff_comm.1 (hQC hq)).2.2 e (hNOfV he)
  have hCVQ : V ⊓ centralizer (Q : Set G) = NOf M V g :=
    inf_centralizer_eq_of_isPGroup (V := V) (V₀ := V₀) (E := NOf M V g) (Z := Z) (Q := Q)
      hp2 h.elemAbelian h.le hNOfV hNOfV₀ hQ.isPGroup
      (by rw [h.normalizer_eq]; exact hQM) (by rw [h.normalizer₀]; exact hQM) hZQ hZV hQE
  have hMnormC : M ≤ normalizer (F11.CTilde M V₀ V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (cTilde_le_M M V₀ V)).1
      (cTilde_subgroupOf_normal h.elemAbelian h.normalizer_eq.symm.le h.normalizer₀.symm.le)
  have hZCn : Z ≤ normalizer (F11.CTilde M V₀ V : Set G) := hZC.trans Subgroup.le_normalizer
  have hXZC : M ≤ normalizer (((Z ⊔ F11.CTilde M V₀ V) : Subgroup G) : Set G) := by
    rw [sup_eq_right.2 hZC]
    exact hMnormC
  have hfr := exists_inv_mul_mem_normalizer_of_isSylowIn hZCn hXZC hZQ hQ
  have hmul : ∀ m ∈ M, ∃ c ∈ F11.CTilde M V₀ V,
      ∃ x ∈ M ⊓ normalizer (NOf M V g : Set G), m = c * x := by
    intro m hm
    obtain ⟨c, hc, hcm⟩ := hfr m hm
    have hcM : c ∈ M := cTilde_le_M M V₀ V hc
    refine ⟨c, hc, c⁻¹ * m, ⟨M.mul_mem (M.inv_mem hcM) hm, ?_⟩, by group⟩
    have hcmM : c⁻¹ * m ∈ M := M.mul_mem (M.inv_mem hcM) hm
    have hcmV : c⁻¹ * m ∈ normalizer (V : Set G) := by
      rw [h.normalizer_eq]
      exact hcmM
    have hmem := mem_normalizer_inf_centralizer_of_mem_normalizer (V := V) (Q := Q) hcmV hcm
    rwa [hCVQ] at hmem
  exact false_of_forall_eq_mul h15 h hV₀K hmul

theorem fourteen_five_one (h15 : Hyp15 M V₀ V) (hO : InCalO1 n M V₀ V g)
    (hc : ¬ ⁅conjSubgroup V₀ g, V ⊓ conjSubgroup M g⁆ ≤ V₀) :
    E3.mQuot V (conjSubgroup M g) = 1 ∧ rMV M V = (mSub V₀ : ℕ∞) := by
  have h := hyp65_of_hyp15 h15 hO
  have hV₀K := not_V₀_le_K h hc
  refine ⟨?_, h.rMV_eq_mSub hV₀K⟩
  have h1 := one_le_mQuot h
  have h2 := not_two_le_mQuot h15 h hV₀K
  omega

end Certified

end FourteenFive

end CFSG.LocalAnalysis.WeakClosure81
