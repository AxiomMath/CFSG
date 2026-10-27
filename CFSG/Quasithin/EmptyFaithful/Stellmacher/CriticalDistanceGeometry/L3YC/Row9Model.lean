module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Row9Models
import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.Stellmacher.CD.L3YC.Row9

open CFSG.Assembly.LowTwoRank CFSG.Quasithin

theorem CentralExp3.comp_equiv {X Y Y' : Type*} [Group X] [Group Y] [Group Y'] {φ : X →* Y}
    (h : CentralExp3 φ) (ψ : Y ≃* Y') : CentralExp3 (ψ.toMonoidHom.comp φ) := by
  refine ⟨ψ.surjective.comp h.surj, ?_, ?_⟩
  · intro x hx
    exact h.central x (by simpa using hx)
  · intro x hx
    exact h.exp3 x (by simpa using hx)

theorem row9_of_data {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (φ : X →* Y)
    (hφ : CentralExp3 φ) {m k o : ℕ}
    (hm : ∀ zt gt : X, zt ^ 2 = 1 → zt ≠ 1 → gt ^ 7 = 1 → gt ≠ 1 → zt * gt = gt * zt →
      Nat.card {c : X // (∃ n : ℕ, c ^ (2 ^ n) = 1) ∧ c * zt = zt * c ∧ c * gt = gt * c} ≤ m)
    (hc : Nat.card Y = 2 ^ k * o) (ho : Odd o) (hkm : 8 * m < 2 ^ k) :
    ∃ k o m : ℕ, Nat.card Y = 2 ^ k * o ∧ Odd o ∧ 8 * m < 2 ^ k ∧
      ∀ z g : Y, z ^ 2 = 1 → z ≠ 1 → orderOf g = 7 → z * g = g * z →
        ∀ Q : Subgroup Y, (∀ q ∈ Q, q * z = z * q ∧ q * g = g * q) → IsPGroup 2 Q →
          Nat.card ↥Q ≤ m :=
  ⟨k, o, m, hc, ho, hkm, fun z g hz2 hz1 hg hzg Q hQ hQp =>
    hφ.two_subgroup_bound hm hz2 hz1 hg hzg Q hQ hQp⟩

theorem row9_model_SL {Y : Type} [Group Y] [Finite Y] (h : IsSLEps3 true 7 Y) :
    ∃ k o m : ℕ, Nat.card Y = 2 ^ k * o ∧ Odd o ∧ 8 * m < 2 ^ k ∧
      ∀ z g : Y, z ^ 2 = 1 → z ≠ 1 → orderOf g = 7 → z * g = g * z →
        ∀ Q : Subgroup Y, (∀ q ∈ Q, q * z = z * q ∧ q * g = g * q) → IsPGroup 2 Q →
          Nat.card ↥Q ≤ m := by
  obtain ⟨K, _, hKfin, hK, ⟨e⟩⟩ := h
  have hX : Finite ↥(StatedSL 3 K) := inferInstance
  refine row9_of_data (X := ↥(StatedSL 3 K)) (e.symm.toMonoidHom.comp (MonoidHom.id _))
    (centralExp3_id.comp_equiv e.symm) (m := 2) (k := 5) (o := 175959) (HX_SL hK) ?_ (by decide)
    (by norm_num)
  rw [Nat.card_congr e.toEquiv, card_statedSL_three', hK]
  norm_num

theorem row9_model_PSL {Y : Type} [Group Y] [Finite Y] (h : IsPSLEps3 true 7 1 Y) :
    ∃ k o m : ℕ, Nat.card Y = 2 ^ k * o ∧ Odd o ∧ 8 * m < 2 ^ k ∧
      ∀ z g : Y, z ^ 2 = 1 → z ≠ 1 → orderOf g = 7 → z * g = g * z →
        ∀ Q : Subgroup Y, (∀ q ∈ Q, q * z = z * q ∧ q * g = g * q) → IsPGroup 2 Q →
          Nat.card ↥Q ≤ m := by
  have h' : IsPSL 3 7 1 Y := h
  obtain ⟨-, K, _, hKfin, hK, ⟨e⟩⟩ := h'
  have hK7 : Nat.card K = 7 := by simpa using hK
  have hX : Finite ↥(StatedSL 3 K) := inferInstance
  refine row9_of_data (X := ↥(StatedSL 3 K))
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf
      (StatedSL 3 K))))
    ((centralExp3_proj (StatedSL 3 K) (fun x hx => det_of_mem_statedSL hx)).comp_equiv e.symm)
    (m := 2) (k := 5) (o := 58653) (HX_SL hK7) ?_ (by decide) (by norm_num)
  have hc := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 3)
    (by norm_num)
  rw [Nat.card_congr e.toEquiv, hc, hK7]
  have hI : Finset.Icc 2 3 = {2, 3} := by decide
  rw [hI, Finset.prod_pair (by norm_num)]
  norm_num

theorem card_statedProj_SU7 {K : Type} [Field K] (hK : Nat.card K = 49) :
    Nat.card (StatedProj (StatedSU 3 7 K)) = 5663616 := by
  have hc := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (p := 7) (f := 1)
    (n := 3) (by norm_num) (by norm_num) (by rw [hK]; norm_num) (by norm_num)
  have hI : Finset.Icc 2 3 = {2, 3} := by decide
  have h2 : Nat.card (StatedProj (StatedSU 3 7 K)) = _ := hc
  rw [h2, hI, Finset.prod_pair (by norm_num)]
  norm_num

theorem card_statedSU7 {K : Type} [Field K] (hK : Nat.card K = 49) :
    Nat.card ↥(StatedSU 3 7 K) = 5663616 := by
  have hker := (CFSG.LinearGroups.unitary_scalar_kernel (K := K) (p := 7) (f := 1)
    (by norm_num) (by rw [hK]; norm_num) (n := 3) (by norm_num)).2.2
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 7 K))
  have h2 : Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 7 K)) = 1 := by
    have : Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 7 K)) =
        Nat.gcd 3 (7 ^ 1 + 1) := hker
    rw [this]; norm_num
  have h3 : Nat.card (StatedSU 3 7 K ⧸ (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 7 K)) =
      5663616 := card_statedProj_SU7 hK
  rw [h1, h2, h3]

theorem row9_model_SU {Y : Type} [Group Y] [Finite Y] (h : IsSLEps3 false 7 Y) :
    ∃ k o m : ℕ, Nat.card Y = 2 ^ k * o ∧ Odd o ∧ 8 * m < 2 ^ k ∧
      ∀ z g : Y, z ^ 2 = 1 → z ≠ 1 → orderOf g = 7 → z * g = g * z →
        ∀ Q : Subgroup Y, (∀ q ∈ Q, q * z = z * q ∧ q * g = g * q) → IsPGroup 2 Q →
          Nat.card ↥Q ≤ m := by
  have h' : IsSU3 7 Y := h
  obtain ⟨K, _, hKfin, hK, ⟨e⟩⟩ := h'
  have hK49 : Nat.card K = 49 := by simpa using hK
  have hX : Finite ↥(StatedSU 3 7 K) := inferInstance
  refine row9_of_data (X := ↥(StatedSU 3 7 K)) (e.symm.toMonoidHom.comp (MonoidHom.id _))
    (centralExp3_id.comp_equiv e.symm) (m := 8) (k := 7) (o := 44247) (HX_SU hK49) ?_
    (by decide) (by norm_num)
  rw [Nat.card_congr e.toEquiv, card_statedSU7 hK49]
  norm_num

theorem row9_model_PSU {Y : Type} [Group Y] [Finite Y] (h : IsPSLEps3 false 7 1 Y) :
    ∃ k o m : ℕ, Nat.card Y = 2 ^ k * o ∧ Odd o ∧ 8 * m < 2 ^ k ∧
      ∀ z g : Y, z ^ 2 = 1 → z ≠ 1 → orderOf g = 7 → z * g = g * z →
        ∀ Q : Subgroup Y, (∀ q ∈ Q, q * z = z * q ∧ q * g = g * q) → IsPGroup 2 Q →
          Nat.card ↥Q ≤ m := by
  have h' : IsPSU 3 7 1 Y := h
  obtain ⟨-, K, _, hKfin, hK, ⟨e0⟩⟩ := h'
  have hK49 : Nat.card K = 49 := by simpa using hK
  have e : Y ≃* StatedProj (StatedSU 3 7 K) := e0
  have hX : Finite ↥(StatedSU 3 7 K) := inferInstance
  have hU : ∀ x ∈ StatedSU 3 7 K, (x : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    fun x hx => ((mem_statedSU_iff7 hK49 x).mp hx).1
  refine row9_of_data (X := ↥(StatedSU 3 7 K))
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf
      (StatedSU 3 7 K))))
    ((centralExp3_proj (StatedSU 3 7 K) hU).comp_equiv e.symm)
    (m := 8) (k := 7) (o := 44247) (HX_SU hK49) ?_ (by decide) (by norm_num)
  rw [Nat.card_congr e.toEquiv, card_statedProj_SU7 hK49]
  norm_num

theorem row9_model (s : Bool) {Y : Type} [Group Y] [Finite Y]
    (h : IsPSLEps3 s 7 1 Y ∨ IsSLEps3 s 7 Y) :
    ∃ k o m : ℕ, Nat.card Y = 2 ^ k * o ∧ Odd o ∧ 8 * m < 2 ^ k ∧
      ∀ z g : Y, z ^ 2 = 1 → z ≠ 1 → orderOf g = 7 → z * g = g * z →
        ∀ Q : Subgroup Y, (∀ q ∈ Q, q * z = z * q ∧ q * g = g * q) → IsPGroup 2 Q →
          Nat.card ↥Q ≤ m := by
  cases s with
  | true =>
    rcases h with h | h
    · exact row9_model_PSL h
    · exact row9_model_SL h
  | false =>
    rcases h with h | h
    · exact row9_model_PSU h
    · exact row9_model_SU h

end CFSG.Quasithin.Stellmacher.CD.L3YC.Row9
