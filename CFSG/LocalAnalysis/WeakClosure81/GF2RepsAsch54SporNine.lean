module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporOrder

import CFSG.GH74.QTGen4.U42.L28Nine
import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Class
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.ComponentClassification.CatLeaf
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.LocalAnalysis.GLTheoremA.List93 (lie2Tags mem_lie2Tags)

theorem lieModel_psl_two_three_of_isCalL0_of_card_eq (hO : LieOrderFormulasInput) {X : Type}
    [Group X] (hX : IsCalL0 X) (hc : Nat.card X = 504) : LieModel X .PSL 2 2 3 := by
  have key : ∀ {t : StatedLieTag} {n f : ℕ}, LieModel X t n 2 f →
      (2 < f ∨ calL0Small t n f = true) → t = .PSL ∧ n = 2 ∧ f = 3 := by
    intro t n f hL hs
    have hadm := hL.admissible
    obtain ⟨-, hord, hv⟩ := hO X t n 2 f hadm hL
    have hle : lieSylowExponent t n * f ≤ 3 := by
      by_contra hlt
      have h16 : 2 ^ 4 ∣ Nat.card X :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by rw [hc]; norm_num)).2
          (by omega)
      rw [hc] at h16
      exact absurd h16 (by norm_num)
    obtain ⟨hn, hf⟩ := CFSG.LocalAnalysis.GLTheoremA.HDesc.bounds_of_adm hadm rfl
    rw [hc] at hord
    have hfin : ∀ t ∈ lie2Tags, ∀ n < 5, ∀ f < 4, (lieAdmTwo t n f = true ∧
        (2 < f ∨ calL0Small t n f = true) ∧ lieSylowExponent t n * f ≤ 3 ∧
        504 * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f)) →
        t = .PSL ∧ n = 2 ∧ f = 3 := by
      decide +kernel
    exact hfin t (mem_lie2Tags t) n (by omega) f (by omega)
      ⟨lieAdmTwo_of_admissible hadm, hs, hle, hord⟩
  rcases hX with ⟨f, hf, t, n, hL⟩ | hL | hL | hL | hL | hL | hA
  · obtain ⟨rfl, rfl, rfl⟩ := key hL (Or.inl hf)
    exact hL
  · exact absurd (key (t := .trialityD4) (n := 0) (f := 1) hL (Or.inr (by decide))).1 (by decide)
  · exact absurd (key (t := .trialityD4) (n := 0) (f := 2) hL (Or.inr (by decide))).1 (by decide)
  · exact absurd (key (t := .PSU) (n := 4) (f := 2) hL (Or.inr (by decide))).1 (by decide)
  · exact absurd (key (t := .PSU) (n := 5) (f := 2) hL (Or.inr (by decide))).1 (by decide)
  · exact absurd (key (t := .POmegaMinus) (n := 4) (f := 2) hL (Or.inr (by decide))).1
      (by decide)
  · obtain ⟨e⟩ : Nonempty (X ≃* alternatingGroup (Fin 9)) := hA
    have h9 : Nat.card X = 181440 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    omega

theorem exists_orderOf_nine_of_isCompositionFactor {X : Type} [Group X] [Finite X] {L : Type}
    [Group L] (hL : E1.IsCompositionFactor X L) {x : L} (hx : orderOf x = 9) :
    ∃ g : X, orderOf g = 9 := by
  obtain ⟨N, M, hN, -, -, -, -, ⟨e⟩⟩ := hL
  have := hN
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (e.symm x)
  have h9 : 9 ∣ orderOf m := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (N.subgroupOf M)) m
    rwa [QuotientGroup.mk'_apply, hm, MulEquiv.orderOf_eq, hx] at h
  obtain ⟨d, hd⟩ := h9
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h0 => (orderOf_pos m).ne' (by rw [hd, h0])
  refine ⟨((m ^ d : M) : X), ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_pow_of_dvd hd0.ne' ⟨9, by rw [hd, mul_comm]⟩, hd,
    Nat.mul_div_cancel _ hd0]

@[expose] def calL0NineCheck (k N : ℕ) : Bool :=
  decide (¬ 2 ^ (k + 1) ∣ N) && (calL0Orders k).all fun c => decide (c ∣ N → c = 504)

theorem not_hasCompFactor_isCalL0_of_dvd_of_pow_nine (hO : LieOrderFormulasInput) {k N : ℕ}
    (h : calL0NineCheck k N = true) {Y : Type} [Group Y] [Finite Y]
    (h9 : ∀ g : Y, g ^ 9 = 1 → g ^ 3 = 1) {A : Subgroup Y} (hA : Nat.card A ∣ N) :
    ¬ HasCompFactor A IsCalL0 := by
  rintro ⟨L, _, hL, hcal⟩
  simp only [calL0NineCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have hdvd : Nat.card L ∣ N := (isCompositionFactor_natCard_dvd hL).trans hA
  have h504 : Nat.card L = 504 :=
    h.2 _ (natCard_mem_calL0Orders hO hcal fun h' => h.1 (h'.trans hdvd)) hdvd
  obtain ⟨x, hx⟩ := CFSG.GH74.QTGen4.U42.L28Nine.exists_orderOf_nine_of_lieModel_psl2_three
    (lieModel_psl_two_three_of_isCalL0_of_card_eq hO hcal h504)
  obtain ⟨g, hg⟩ := exists_orderOf_nine_of_isCompositionFactor hL hx
  have hg' : orderOf (g : Y) = 9 := by rw [Subgroup.orderOf_coe, hg]
  have h91 : (g : Y) ^ 9 = 1 := by rw [← hg']; exact pow_orderOf_eq_one _
  have h3 := orderOf_dvd_of_pow_eq_one (h9 _ h91)
  rw [hg'] at h3
  norm_num at h3

end CFSG.LocalAnalysis.WeakClosure81

end
