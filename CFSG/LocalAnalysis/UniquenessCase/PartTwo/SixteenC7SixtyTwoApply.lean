module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEleven
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr CFSG.Quasithin.H13 CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Commute

theorem s16c7_mul_comm_of_mem_normalizer {V X : Subgroup G} {z n : G} (hz1 : z ≠ 1)
    (hz2 : z ^ 2 = 1) (hCX : V ⊓ centralizer (X : Set G) = Subgroup.zpowers z) (hzV : z ∈ V)
    (hnV : n ∈ normalizer (V : Set G)) (hnX : n ∈ normalizer (X : Set G)) :
    n * z = z * n := by
  have hzX : z ∈ centralizer (X : Set G) :=
    (Subgroup.mem_inf.1 (hCX ▸ Subgroup.mem_zpowers z : z ∈ V ⊓ centralizer (X : Set G))).2
  have hwV : n * z * n⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hnV z).1 hzV
  have hwX : n * z * n⁻¹ ∈ centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : n⁻¹ * x * n ∈ X := by
      have := (Subgroup.mem_normalizer_iff.1 ((normalizer (X : Set G)).inv_mem hnX) x).1 hx
      simpa using this
    have h1 : (n⁻¹ * x * n) * z = z * (n⁻¹ * x * n) := Subgroup.mem_centralizer_iff.1 hzX _ hx'
    calc x * (n * z * n⁻¹) = n * ((n⁻¹ * x * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * x * n)) * n⁻¹ := by rw [h1]
      _ = n * z * n⁻¹ * x := by group
  have hw : n * z * n⁻¹ ∈ Subgroup.zpowers z := hCX ▸ Subgroup.mem_inf.2 ⟨hwV, hwX⟩
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (orderOf_eq_prime hz2 hz1)).1 hw with h | h
  · exfalso
    apply hz1
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · calc n * z = (n * z * n⁻¹) * n := by group
      _ = z * n := by rw [h]

end Commute

section Hypotheses

theorem s16c7_odd_relIndex_of_le (D : Data G) {H : Subgroup G} (hT : D.T ≤ H) :
    Odd (D.M.relIndex H) := by
  have h1 : D.M.relIndex H ∣ D.T.relIndex H := Subgroup.relIndex_dvd_of_le_left H D.sylowM.le
  have h2 : ¬ 2 ∣ D.T.relIndex H := (TwelveShort.isSylowIn_of_le D hT).2.2
  exact Nat.odd_iff.2 (by
    by_contra hc
    exact h2 (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero (by omega)) h1))

theorem s16c7_seven_dvd_card_centralizer_inf (D : Data G) (hx : DataExt D) (hsig : D.sig = {7})
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil ⊥ V)
    {A : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hreal : (tensorPairModel SL32 SL32).RealizesMod A)
    (hMA : Mbar D.M ⊥ V hV ≤ normalizer (A : Set (MulAut (Vtil ⊥ V hV)))) {z : G} (hzV : z ∈ V) :
    7 ∣ Nat.card ↥(centralizer ({z} : Set G) ⊓ D.M) := by
  have h7s : (7 : ℕ) ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 7
  obtain ⟨E, hEM, hEel, hEc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (by norm_num : Nat.Prime 7) (hx.three_le 7 h7s)
  have hEs : E ≤ stabTil ⊥ V := hEM.trans hMs
  have hbar := s16c7_card_barSub_le hV hEs hEel.isPGroup hreal
    ((barSub_mono ⊥ V hV hEM).trans hMA)
  have h1 := s16c7_seven_dvd_card_inf_centralizer hV hEs hEc hbar
  have hsub : E ⊓ centralizer (V : Set G) ≤ centralizer ({z} : Set G) ⊓ D.M := by
    intro g hg
    obtain ⟨hgE, hgc⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨?_, hEM hgE⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact Subgroup.mem_centralizer_iff.1 hgc z hzV
  exact h1.trans (Subgroup.card_dvd_of_le hsub)

end Hypotheses

theorem s16c7_centralizer_le_of_thm145 (D : Data G) (h145 : Thm145 D)
    {V K₁ K₂ X : Subgroup G} {z : G} (hH : Hyp141 D K₁ K₂ X)
    (hMV : D.M ≤ normalizer (V : Set G)) (hzV : z ∈ V) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hCT : V ⊓ centralizer (D.T : Set G) = Subgroup.zpowers z)
    (hCX : V ⊓ centralizer (X : Set G) = Subgroup.zpowers z)
    (h7 : 7 ∣ Nat.card ↥(centralizer ({z} : Set G) ⊓ D.M)) :
    centralizer ({z} : Set G) ≤ D.M := by
  have hzT : z ∈ centralizer (D.T : Set G) :=
    (Subgroup.mem_inf.1 (hCT ▸ Subgroup.mem_zpowers z : z ∈ V ⊓ centralizer (D.T : Set G))).2
  have hzX : z ∈ centralizer (X : Set G) :=
    (Subgroup.mem_inf.1 (hCX ▸ Subgroup.mem_zpowers z : z ∈ V ⊓ centralizer (X : Set G))).2
  have hle : ∀ {Y : Subgroup G}, z ∈ centralizer (Y : Set G) → Y ≤ centralizer ({z} : Set G) := by
    intro Y hzY y hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (Subgroup.mem_centralizer_iff.1 hzY y hy).symm
  have hL : K₁ ⊔ K₂ ≤ D.M :=
    sup_le (uc22p22a_le_of_isSubnormal hH.mem₁.1) (uc22p22a_le_of_isSubnormal hH.mem₂.1)
  refine h145 K₁ K₂ X hH _ (hle hzX)
    (TwelveEleven.fstar_eq_pCoreOf_of_charTwo
      (D.standing.charTwo _ (uc22p22f_isTwoLocal_centralizer hz1 hz2)))
    (s16c7_odd_relIndex_of_le D (hle hzT)) ?_ h7
  intro n hn
  obtain ⟨hnL, hnX⟩ := Subgroup.mem_inf.1 hn
  have hcomm := s16c7_mul_comm_of_mem_normalizer hz1 hz2 hCX hzV (hMV (hL hnL)) hnX
  refine ⟨n, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, hnL⟩, hnX⟩, fun x _ => rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact hcomm.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
