module

public import CFSG.Quasithin.Background.D2Z13

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

section D219

variable {X : Subgroup (MulAut V)} {r : ℚ}

theorem eq_one_of_mem_fittingOf_of_sq (h : D217Hyp X r) {a : MulAut V} (haF : a ∈ fittingOf X)
    (ha2 : a ^ 2 = 1) : a = 1 := by
  have hodd := odd_card_fittingOf h.o2
  have hdvd : orderOf (⟨a, haF⟩ : ↥(fittingOf X)) ∣ Nat.card (fittingOf X) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hdvd
  have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one ha2
  have hcop : Nat.Coprime 2 (Nat.card (fittingOf X)) := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk]
    simp [Nat.coprime_comm]
  have : orderOf a ∣ Nat.gcd 2 (Nat.card (fittingOf X)) := Nat.dvd_gcd h2 (hdvd)
  rw [hcop, Nat.dvd_one] at this
  exact orderOf_eq_one_iff.mp this

theorem D214Hyp_of_D217Hyp (h : D217Hyp X r) {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X)
    (hnc : ¬ IsCyclic ↥A) : D214Hyp X A r := by
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  refine ⟨h.qhat, hA, hnc, ?_, ?_, h.sqtk⟩
  · intro a haA hcomm
    have haX : a ∈ X := hA2.le haA
    have ha2 : a ^ 2 = 1 := hA2.isElemAbelian2.2 a haA
    have haF : a ∈ fittingOf X := by
      refine h.fstar ⟨haX, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
      exact (hcomm f (fittingOf_le_oddFitting h.o2 hf)).symm
    exact eq_one_of_mem_fittingOf_of_sq h haF ha2
  · exact top_le_iff.mp (h.comm_fitting ▸ commV_mono (fittingOf_le_oddFitting h.o2))

theorem not_isCyclic_of_one_lt_rk {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A)
    (hrk : 1 < rk A) : ¬ IsCyclic ↥A := by
  intro hcyc
  have hexp : Monoid.exponent ↥A ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hA.2 x x.2)
  rw [IsCyclic.exponent_eq_card] at hexp
  have hc := card_eq_two_pow_of_isPGroup hA.isPGroup
  have h1 : 2 ^ 2 ≤ 2 ^ rk A := Nat.pow_le_pow_right (by norm_num) hrk
  have h2 := Nat.le_of_dvd (by norm_num) hexp
  omega

theorem D2_19 (hV : ∀ v : V, v ^ 2 = 1) (h : D217Hyp X r) {A : Subgroup (MulAut V)}
    (hA : A ∈ QhatStar X) (hrk : 1 < rk A) :
    D214Hyp X A r ∧ r = 3 / 2 ∧ ∀ B ∈ QhatStar X, 1 < rk B := by
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have h14 := D214Hyp_of_D217Hyp h hA (not_isCyclic_of_one_lt_rk hA2.isElemAbelian2 hrk)
  have hr := D2_14_6 hV h14
  refine ⟨h14, hr, fun B hB => ?_⟩
  by_contra hle
  push Not at hle
  obtain ⟨r'', -, -, ⟨⟨hB2, -⟩, -⟩, -⟩ := QhatStar_spec hB
  have hpos := hB2.rk_pos
  have hcard : Nat.card B = 2 := by
    rw [card_eq_two_pow_of_isPGroup hB2.isElemAbelian2.isPGroup]
    have : rk B = 1 := by omega
    rw [this]; norm_num
  rcases (D2_18 hV h hB hcard).2 with h1 | h1 <;> rw [hr] at h1 <;> norm_num at h1

end D219

end CFSG.Quasithin
