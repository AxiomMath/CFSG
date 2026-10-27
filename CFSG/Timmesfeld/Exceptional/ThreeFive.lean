module

public import CFSG.Timmesfeld.Exceptional.H3Check
public import CFSG.Timmesfeld.Exceptional.FiveFiveFive

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Certificates CFSG.Certificates.CosetEnumeration

variable {G : Type*} [Group G]

namespace Exc

@[expose] def rels235 : List (List (Fin 3 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)],
    [(0, true), (1, true), (0, true), (1, true)],
    (List.replicate 3 [(0, true), (2, true)]).flatten,
    (List.replicate 5 [(1, true), (2, true)]).flatten]

theorem mk_pow_ten_235 : PresentedGroup.mk (wordRels rels235)
    (FreeGroup.mk (List.replicate 10 [(0, true), (1, true), (2, true)]).flatten) = 1 :=
  mk_eq_one_of_coverWalk (N := 120) (F := 360) (fx := H3Data.fx) (fc := H3Data.fc)
    (fy := H3Data.fy) (kind := H3Data.kind) (wi := H3Data.wi) (fs := H3Data.fs)
    (ft := H3Data.ft) (fo := H3Data.fo) (refs := H3Data.refs) (pl := H3Data.pl)
    (ffi := H3Data.ffi) (live := H3Data.live) (rels := wordRels rels235) rels235 H3Data.words
    (fun w hw => ⟨w, hw, rfl⟩) (by decide +kernel) H3Data.live_zero (by norm_num)
    H3Data.facts_all H3Data.cover_all _ (by decide +kernel)

end Exc

open Exc

theorem mul_mul_pow_ten_eq_one_of_three_five {u v c : G} (hu : u * u = 1) (hv : v * v = 1)
    (hc : c * c = 1) (huv : Commute u v) (h1 : (u * c) ^ 3 = 1) (h2 : (v * c) ^ 5 = 1) :
    (u * v * c) ^ 10 = 1 := by
  set x : Fin 3 → G := ![u, v, c] with hx
  have hrel : ∀ r ∈ rels235, signedProd x r = 1 := by
    intro r hr
    simp only [rels235, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [signedProd, hx] using hu
    · simpa [signedProd, hx] using hv
    · simpa [signedProd, hx] using hc
    · simp only [signedProd, hx, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ite_true]
      rw [show u * (v * (u * v)) = u * (v * u) * v by group, ← huv.eq,
        show u * (u * v) * v = u * u * (v * v) by group, hu, hv, one_mul]
    · rw [signedProd_replicate]
      simpa [signedProd, hx] using h1
    · rw [signedProd_replicate]
      simpa [signedProd, hx] using h2
  have k := signedProd_eq_one_of_mk_eq_one mk_pow_ten_235 x hrel
  rw [signedProd_replicate] at k
  simpa [signedProd, hx, mul_assoc] using k

theorem orderOf_eq_five_of_three_five {u v c : G} (hu : u * u = 1) (hv : v * v = 1)
    (hc : c * c = 1) (huv : Commute u v) (h1 : orderOf (u * c) = 3) (h2 : orderOf (v * c) = 5)
    (hodd : Odd (orderOf (u * v * c))) : orderOf (u * v * c) = 5 := by
  have h1' : (u * c) ^ 3 = 1 := by rw [← h1]; exact pow_orderOf_eq_one _
  have h2' : (v * c) ^ 5 = 1 := by rw [← h2]; exact pow_orderOf_eq_one _
  have h10 := mul_mul_pow_ten_eq_one_of_three_five hu hv hc huv h1' h2'
  have hdvd : orderOf (u * v * c) ∣ 2 * 5 := orderOf_dvd_of_pow_eq_one h10
  have h5 : orderOf (u * v * c) ∣ 5 :=
    Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_two_right).2 hodd) hdvd
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 h5 with h | h
  · exfalso
    have h0 : u * v * c = 1 := orderOf_eq_one_iff.1 h
    have hc' : c = v * u := by
      rw [eq_inv_of_mul_eq_one_right h0, mul_inv_rev, inv_eq_of_mul_eq_one_right hu,
        inv_eq_of_mul_eq_one_right hv]
    have huc : u * c = v := by rw [hc', ← mul_assoc, huv.eq, mul_assoc, hu, mul_one]
    rw [huc] at h1
    have : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hv)
    rw [h1] at this
    exact absurd this (by norm_num)
  · exact h

end CFSG.Timmesfeld.Moufang
