module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddEigen
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Walter.J1Props (elt wy11 wr11 wy19 wr19)

theorem Shape919.of_isJ1 {X : Type} [Group X] [Finite X] (h : IsJ1 X) : Shape919 X := by
  obtain ⟨hcard, hs, hinn⟩ := kJ1_holds X h
  refine ⟨hs, ?_, fun p hp hp2 => ?_, ?_, ?_⟩
  · rw [hcard]
    norm_num
  · refine CFSG.QuasithinUnique.Id2519.pRank_le_one_of_not_sq_dvd hp ?_
    rw [hcard]
    exact CFSG.QuasithinUnique.Id2519.not_sq_dvd_J1 hp hp2
  · have hsurj : Function.Surjective (MulAut.conj : X →* MulAut X) := fun θ => by
      obtain ⟨x, hx⟩ := hinn θ
      exact ⟨x, hx.symm⟩
    exact (Subgroup.card_dvd_of_surjective hsurj).trans (dvd_mul_left _ 2)
  · rintro ⟨e5⟩
    have hc := hcard
    rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hc
    norm_num [Nat.factorial] at hc

theorem exists_conj_pow_of_isJ1 {X : Type} [Group X] (h : IsJ1 X) :
    (∃ a b : X, orderOf a = 19 ∧ b * a * b⁻¹ = a ^ 8) ∧
      ∃ a b : X, orderOf a = 11 ∧ b * a * b⁻¹ = a ^ 2 := by
  obtain ⟨e⟩ := h
  let f : CFSG.Open.walterJ1 ≃* X := (e.trans CFSG.Walter.walterJ1EquivNative.symm).symm
  obtain ⟨h19, -⟩ := CFSG.Walter.J1Props.rels_r19
  obtain ⟨-, -, -, -, h11, -⟩ := CFSG.Walter.J1Props.rels_r
  obtain ⟨-, -, -, -, p11, n11, p19, n19⟩ := CFSG.Walter.J1Props.orders_yJ
  haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine ⟨⟨f (elt wy19), f (elt wr19), ?_, ?_⟩, f (elt wy11), f (elt wr11), ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime p19 n19
  · rw [← map_inv, ← map_mul, ← map_mul, h19, map_pow]
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime p11 n11
  · rw [← map_inv, ← map_mul, ← map_mul, h11, map_pow]

theorem false_of_conj_pow_of_mulEquiv {Q : Type} [Group Q] {K : Type} [Field K] [Finite K]
    {n p m : ℕ} {T : Subgroup (GL (Fin n) K)} (hT : T ≤ StatedSL n K) (e : Q ≃* StatedProj T)
    (hp : p.Prime) (hK : Nat.card K = p ^ m) (hn : 0 < n) (hn3 : n ≤ 3) {a b a' b' : Q}
    (ha : orderOf a = 19) (hab : b * a * b⁻¹ = a ^ 8) (ha' : orderOf a' = 11)
    (hab' : b' * a' * b'⁻¹ = a' ^ 2) : False := by
  by_cases hp19 : p = 19
  · have h := orderOf_le_of_conj_of_mulEquiv hT e hp (by norm_num) (by omega) hK hn (by omega)
      ha' hab'
    have h2 : orderOf ((2 : ℕ) : ZMod 11) = 10 :=
      (orderOf_eq_iff (by norm_num)).2 ⟨by decide, by decide⟩
    rw [h2] at h
    omega
  · have h := orderOf_le_of_conj_of_mulEquiv hT e hp (by norm_num) hp19 hK hn (by omega) ha hab
    have h8 : orderOf ((8 : ℕ) : ZMod 19) = 6 :=
      (orderOf_eq_iff (by norm_num)).2 ⟨by decide, by decide⟩
    rw [h8] at h
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
