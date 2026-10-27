module

public import CFSG.LocalAnalysis.WeakClosure81.W15Defs
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveL

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace FourteenFive

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem hyp65_of_hyp15 (h : Hyp15 M V₀ V) (hO : InCalO1 n M V₀ V g) : Hyp65 n M V₀ V g := by
  exact ⟨h.h6.elemAbelian, h.h6.le, h.ne_bot, h.h6.normalizer_eq, h.normalizer₀, h.isTI, hO⟩

private theorem eq_two_of_relIndex_dvd_two_pow {H K : Subgroup G} {k : ℕ}
    (hdiv : H.relIndex K ∣ 2 ^ k) (hval : padicValNat 2 (H.relIndex K) = 1) :
    H.relIndex K = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdiv
  rw [hj, padicValNat.prime_pow] at hval
  rw [hval, pow_one] at hj
  exact hj

theorem not_V₀_le_K (h : Hyp65 n M V₀ V g)
    (hc : ¬ ⁅conjSubgroup V₀ g, V ⊓ conjSubgroup M g⁆ ≤ V₀) : ¬ V₀ ≤ KOf M V g := by
  intro hV₀K
  exact hc ((Subgroup.commutator_mono le_rfl inf_le_left).trans
    (h.commutator_conjV₀_V_le_V₀ hV₀K))

theorem one_le_mQuot (h : Hyp65 n M V₀ V g) : 1 ≤ E3.mQuot V (conjSubgroup M g) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup h.elemAbelian).exists_card_eq
  have hdiv : (conjSubgroup M g).relIndex V ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.relIndex_dvd_card (H := conjSubgroup M g) (K := V)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdiv
  unfold E3.mQuot
  rw [hj, padicValNat.prime_pow]
  by_contra hlt
  have hj0 : j = 0 := by omega
  rw [hj0, pow_zero] at hj
  exact h.not_V_le_conjM (Subgroup.relIndex_eq_one.1 hj)

theorem relIndex_U_eq_two (h : Hyp65 n M V₀ V g) (h1 : E3.mQuot V (conjSubgroup M g) = 1) :
    (UOf M V g).relIndex V = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup h.elemAbelian).exists_card_eq
  have hval : padicValNat 2 ((V ⊓ conjSubgroup M g).relIndex V) = 1 := by
    rw [Subgroup.inf_relIndex_left]
    unfold E3.mQuot at h1
    exact h1
  have hdiv : (V ⊓ conjSubgroup M g).relIndex V ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.relIndex_dvd_card (H := V ⊓ conjSubgroup M g) (K := V)
  rw [UOf]
  exact eq_two_of_relIndex_dvd_two_pow hdiv hval

section Certified


theorem inf_LOf_le_cTilde (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g) :
    M ⊓ LOf V g ≤ F11.CTilde M V₀ V := by
  have hLN : LOf V g ≤ centralizer (NOf M V g : Set G) :=
    (Subgroup.le_centralizer_iff (H := NOf M V g) (K := LOf V g)).1 h.N_le_centralizer_L
  have hVL : V ≤ LOf V g := by rw [LOf]; exact le_sup_left
  have hV₀L : V₀ ≤ LOf V g := h.le.trans hVL
  have hV₀normN : V₀ ≤ normalizer (NOf M V g : Set G) :=
    hV₀L.trans (hLN.trans (Subgroup.centralizer_le_normalizer (NOf M V g : Set G)))
  intro x hx
  rw [FourteenTwo.mem_cTilde_iff_comm]
  obtain ⟨hxM, hxL⟩ := hx
  have hxN : x ∈ normalizer (V₀ : Set G) := by rw [h.normalizer₀]; exact hxM
  refine ⟨hxM, hxN, ?_⟩
  intro v hv
  rw [h.V_eq_V₀_sup_N hV₀K] at hv
  have hv' : v ∈ ((V₀ ⊔ NOf M V g : Subgroup G) : Set G) := hv
  rw [Subgroup.coe_mul_of_left_le_normalizer_right V₀ (NOf M V g) hV₀normN] at hv'
  obtain ⟨v₀, hv₀, n, hn, hvn⟩ := Set.mem_mul.1 hv'
  rw [← hvn]
  have hxv₀ : x * v₀ * x⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hxN v₀).1 hv₀
  have hxn : x * n * x⁻¹ = n := by
    have hcomm : x * n = n * x :=
      Subgroup.mem_centralizer_iff.1 (h.N_le_centralizer_L hn) x hxL
    rw [hcomm]; group
  have hkey : x * (v₀ * n) * x⁻¹ * (v₀ * n)⁻¹ = x * v₀ * x⁻¹ * v₀⁻¹ := by
    rw [show x * (v₀ * n) * x⁻¹ * (v₀ * n)⁻¹
          = (x * v₀ * x⁻¹) * (x * n * x⁻¹) * (v₀ * n)⁻¹ by group]
    rw [hxn]
    group
  rw [hkey]
  exact V₀.mul_mem hxv₀ (V₀.inv_mem hv₀)

theorem N_ne_bot (h15 : Hyp15 M V₀ V) (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g) :
    NOf M V g ≠ ⊥ := by
  intro hN
  have hV : V = V₀ := by rw [h.V_eq_V₀_sup_N hV₀K, hN, sup_bot_eq]
  exact h15.h6.ne_top h15.ne_bot hV.symm

theorem false_of_forall_eq_mul (h15 : Hyp15 M V₀ V) (h : Hyp65 n M V₀ V g)
    (hV₀K : ¬ V₀ ≤ KOf M V g)
    (hmul : ∀ m ∈ M, ∃ c ∈ F11.CTilde M V₀ V,
      ∃ x ∈ M ⊓ normalizer (NOf M V g : Set G), m = c * x) : False := by
  have hNne : NOf M V g ≠ ⊥ := N_ne_bot h15 h hV₀K
  have hUV : NOf M V g ≤ V := by
    rw [NOf, UOf]
    exact inf_le_left.trans inf_le_left
  have hMnormC : M ≤ normalizer (F11.CTilde M V₀ V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (cTilde_le_M M V₀ V)).1
      (cTilde_subgroupOf_normal h.elemAbelian (le_of_eq h.normalizer_eq.symm)
        (le_of_eq h.normalizer₀.symm))
  have hCU : M ⊓ centralizer (V : Set G) ≤
      M ⊓ normalizer (NOf M V g : Set G) := by
    intro x hx
    obtain ⟨hxM, hxC⟩ := hx
    refine ⟨hxM, ?_⟩
    have hxCN : x ∈ centralizer (NOf M V g : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      exact Subgroup.mem_centralizer_iff.1 hxC n (hUV hn)
    exact Subgroup.centralizer_le_normalizer (NOf M V g : Set G) hxCN
  have hmul' : ∀ m ∈ M, ∃ x ∈ M ⊓ normalizer (NOf M V g : Set G),
      ∃ c ∈ F11.CTilde M V₀ V, m = x * c := by
    intro m hm
    obtain ⟨c, hc, x, hx, hmx⟩ := hmul m hm
    refine ⟨x, hx, x⁻¹ * c * x, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff''.1 (hMnormC hx.1) c).1 hc
    · rw [hmx]; group
  have hle : normalizer (NOf M V g : Set G) ≤ M :=
    h15.s14c (NOf M V g) hUV hNne hCU hmul'
  apply h.not_conjV_le_M
  calc conjSubgroup V g ≤ LOf V g := by rw [LOf]; exact le_sup_right
    _ ≤ centralizer (NOf M V g : Set G) :=
        Subgroup.le_centralizer_iff.1 h.N_le_centralizer_L
    _ ≤ normalizer (NOf M V g : Set G) := Subgroup.centralizer_le_normalizer _
    _ ≤ M := hle

end Certified

end FourteenFive

end CFSG.LocalAnalysis.WeakClosure81
