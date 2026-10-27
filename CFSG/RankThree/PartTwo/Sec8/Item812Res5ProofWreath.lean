module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434KitWreath
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item812Res5

open CFSG.RankThree.PartTwo.Sec4.Item434Kit CFSG.RankThree.PartTwo.Sec4.Item434AltPerm Subgroup

variable {H : Type*} [Group H] {z : Fin 3 → H} {t : H}

theorem vecElt_zero : vecElt z 0 = 1 := by
  simp [vecElt]

theorem eq_vec_three (v : Fin 3 → ZMod 3) : v = ![v 0, v 1, v 2] := by
  ext i
  fin_cases i <;> rfl

theorem vecElt_inv_of_add_eq_zero (hf : WreathFacts z t) {u w : Fin 3 → ZMod 3}
    (h : u + w = 0) : (vecElt z u)⁻¹ = vecElt z w := by
  rw [inv_eq_iff_mul_eq_one, ← vecElt_add hf, h, vecElt_zero]

theorem conj_sq_vecElt (hf : WreathFacts z t) (v : Fin 3 → ZMod 3) :
    t ^ 2 * vecElt z v * (t ^ 2)⁻¹ = vecElt z ![v 1, v 2, v 0] := by
  rw [show t ^ 2 * vecElt z v * (t ^ 2)⁻¹ = t * (t * vecElt z v * t⁻¹) * t⁻¹ by
      rw [sq, mul_inv_rev]; simp only [mul_assoc], conj_vecElt hf, conj_vecElt hf]
  rfl

theorem vecElt_mul_t_pow_three (hf : WreathFacts z t) (a b c : ZMod 3) :
    (vecElt z ![a, b, c] * t) ^ 3 = vecElt z ![a + b + c, a + b + c, a + b + c] := by
  have e : (vecElt z ![a, b, c] * t) ^ 3 = vecElt z ![a, b, c] *
      (t * vecElt z ![a, b, c] * t⁻¹) * (t ^ 2 * vecElt z ![a, b, c] * (t ^ 2)⁻¹) * t ^ 3 := by
    rw [pow_three]
    group
  rw [e, conj_vecElt hf, conj_sq_vecElt hf, hf.pow_t, mul_one, ← vecElt_add hf,
    ← vecElt_add hf]
  congr 1
  ext i
  fin_cases i <;> simp <;> ring

theorem vecElt_mul_t_sq_pow_three (hf : WreathFacts z t) (a b c : ZMod 3) :
    (vecElt z ![a, b, c] * t ^ 2) ^ 3 = vecElt z ![a + b + c, a + b + c, a + b + c] := by
  have ht6 : t ^ 6 = 1 := by
    rw [show 6 = 3 * 2 by rfl, pow_mul, hf.pow_t, one_pow]
  have ht4 : t ^ 4 * vecElt z ![a, b, c] * (t ^ 4)⁻¹ = t * vecElt z ![a, b, c] * t⁻¹ := by
    have h4 : t ^ 4 = t ^ 3 * t := by rw [← pow_succ]
    rw [h4, hf.pow_t, one_mul]
  have e : (vecElt z ![a, b, c] * t ^ 2) ^ 3 = vecElt z ![a, b, c] *
      (t ^ 2 * vecElt z ![a, b, c] * (t ^ 2)⁻¹) * (t ^ 4 * vecElt z ![a, b, c] * (t ^ 4)⁻¹) *
        t ^ 6 := by
    rw [pow_three]
    group
  rw [e, ht4, conj_vecElt hf, conj_sq_vecElt hf, ht6, mul_one, ← vecElt_add hf,
    ← vecElt_add hf]
  congr 1
  ext i
  fin_cases i <;> simp <;> ring

theorem val_eq_one_or_two {j : Fin 3} (hj : j ≠ 0) : (j : ℕ) = 1 ∨ (j : ℕ) = 2 := by
  have hj0 : (j : ℕ) ≠ 0 := fun h0 => hj (Fin.ext h0)
  have := j.isLt
  omega

theorem sum_eq_zero_of_pow_three (hf : WreathFacts z t) {a b c : ZMod 3} {j : Fin 3}
    (hj : j ≠ 0) (h3 : (vecElt z ![a, b, c] * t ^ (j : ℕ)) ^ 3 = 1) : a + b + c = 0 := by
  have hc : vecElt z ![a + b + c, a + b + c, a + b + c] = 1 := by
    rcases val_eq_one_or_two hj with h1 | h2
    · rw [h1, pow_one, vecElt_mul_t_pow_three hf] at h3
      exact h3
    · rw [h2, vecElt_mul_t_sq_pow_three hf] at h3
      exact h3
  simpa using congrFun (hf.inj _ hc) 0

theorem three_eq_zero_zmod : (3 : ZMod 3) = 0 := by decide

theorem exists_conj_eq_t_pow (hf : WreathFacts z t) {v : Fin 3 → ZMod 3} {j : Fin 3}
    (hj : j ≠ 0) (h3 : (vecElt z v * t ^ (j : ℕ)) ^ 3 = 1) :
    ∃ u : Fin 3 → ZMod 3,
      vecElt z u * (vecElt z v * t ^ (j : ℕ)) * (vecElt z u)⁻¹ = t ^ (j : ℕ) := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c : ZMod 3, v = ![a, b, c] := ⟨v 0, v 1, v 2, eq_vec_three v⟩
  have hs := sum_eq_zero_of_pow_three hf hj h3
  have h30 := three_eq_zero_zmod
  rcases val_eq_one_or_two hj with h1 | h2
  · refine ⟨![0, 2 * b, 2 * b + 2 * c], ?_⟩
    rw [h1, pow_one]
    have hinv : (vecElt z ![0, 2 * b, 2 * b + 2 * c])⁻¹ = vecElt z ![0, b, b + c] := by
      refine vecElt_inv_of_add_eq_zero hf ?_
      ext i
      fin_cases i <;> simp <;>
        first | linear_combination b * h30 | linear_combination (b + c) * h30
    have e : vecElt z ![0, 2 * b, 2 * b + 2 * c] * (vecElt z ![a, b, c] * t) *
        (vecElt z ![0, 2 * b, 2 * b + 2 * c])⁻¹ = vecElt z ![0, 2 * b, 2 * b + 2 * c] *
          vecElt z ![a, b, c] * (t * (vecElt z ![0, 2 * b, 2 * b + 2 * c])⁻¹ * t⁻¹) * t := by
      group
    rw [e, hinv, conj_vecElt hf, ← vecElt_add hf, ← vecElt_add hf]
    have hz : (![0, 2 * b, 2 * b + 2 * c] : Fin 3 → ZMod 3) + ![a, b, c] +
        ![(![0, b, b + c] : Fin 3 → ZMod 3) 2, (![0, b, b + c] : Fin 3 → ZMod 3) 0,
          (![0, b, b + c] : Fin 3 → ZMod 3) 1] = 0 := by
      ext i
      fin_cases i <;> simp <;>
        first | linear_combination hs | linear_combination b * h30 |
          linear_combination (b + c) * h30
    rw [hz, vecElt_zero, one_mul]
  · refine ⟨![0, a, a + b], ?_⟩
    rw [h2]
    have hinv : (vecElt z ![0, a, a + b])⁻¹ = vecElt z ![0, 2 * a, 2 * a + 2 * b] := by
      refine vecElt_inv_of_add_eq_zero hf ?_
      ext i
      fin_cases i <;> simp <;> first | linear_combination a * h30 |
        linear_combination (a + b) * h30
    have e : vecElt z ![0, a, a + b] * (vecElt z ![a, b, c] * t ^ 2) *
        (vecElt z ![0, a, a + b])⁻¹ = vecElt z ![0, a, a + b] * vecElt z ![a, b, c] *
          (t ^ 2 * (vecElt z ![0, a, a + b])⁻¹ * (t ^ 2)⁻¹) * t ^ 2 := by group
    rw [e, hinv, conj_sq_vecElt hf, ← vecElt_add hf, ← vecElt_add hf]
    have hz : (![0, a, a + b] : Fin 3 → ZMod 3) + ![a, b, c] +
        ![(![0, 2 * a, 2 * a + 2 * b] : Fin 3 → ZMod 3) 1,
          (![0, 2 * a, 2 * a + 2 * b] : Fin 3 → ZMod 3) 2,
          (![0, 2 * a, 2 * a + 2 * b] : Fin 3 → ZMod 3) 0] = 0 := by
      ext i
      fin_cases i <;> simp <;>
        first | linear_combination hs | linear_combination a * h30 |
          linear_combination (a + b) * h30
    rw [hz, vecElt_zero, one_mul]

theorem isElemAbelian_map_hom {K : Type*} [Group K] (f : H →* K) {E : Subgroup H}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) : CFSG.Assembly.IsElemAbelian 3 (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

variable [Finite H]

theorem exists_map_conj_le_wreathW (hW : Nat.card (wreathW z t) = 3 ^ (Nat.card H).factorization 3)
    {S : Subgroup H} (hS : IsPGroup 3 S) :
    ∃ g : H, S.map (MulAut.conj g⁻¹).toMonoidHom ≤ wreathW z t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_le_map_conj_of_card hW hS
  exact ⟨g, map_conj_inv_le hg⟩

theorem card_inf_centralizer_le_three (hf : WreathFacts z t)
    (hW : Nat.card (wreathW z t) = 3 ^ (Nat.card H).factorization 3)
    (h81 : Nat.card (wreathW z t) = 81) {S E : Subgroup H} (hS : IsPGroup 3 S) (hES : E ≤ S)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) {y : H} (hyS : y ∈ S)
    (hyE : y ∉ E) : Nat.card (E ⊓ Subgroup.centralizer {y} : Subgroup H) ≤ 3 := by
  obtain ⟨g, hg⟩ := exists_map_conj_le_wreathW hW hS
  set c : H →* H := (MulAut.conj g⁻¹).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj g⁻¹).injective
  have hEW : E.map c ≤ wreathW z t := (Subgroup.map_mono hES).trans hg
  have hEA : E.map c = baseA z := eq_baseA_of_le_wreathW hf h81 hEW (isElemAbelian_map_hom c hE)
    (by rw [Subgroup.card_map_of_injective hcinj, hE27])
  have hyW : c y ∈ wreathW z t := hg ⟨y, hyS, rfl⟩
  obtain ⟨v, j, hvj⟩ := mem_wreathW hf hyW
  have hj : j ≠ 0 := by
    rintro rfl
    apply hyE
    have hyA : c y ∈ E.map c := by
      rw [hEA, hvj, Fin.val_zero, pow_zero, mul_one]
      exact vecElt_mem_baseA hf v
    obtain ⟨x, hx, hxy⟩ := hyA
    rwa [← hcinj hxy]
  have hle : (E ⊓ Subgroup.centralizer {y} : Subgroup H).map c ≤
      zpowers (vecElt z ![1, 1, 1]) := by
    rintro _ ⟨x, ⟨hxE, hxy⟩, rfl⟩
    have hxA : c x ∈ baseA z := hEA ▸ ⟨x, hxE, rfl⟩
    obtain ⟨u, hu⟩ := (mem_baseA_iff hf).mp hxA
    have hcomm : c x * c y = c y * c x := by
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hxy]
    rw [← hu, hvj] at hcomm
    have huv : vecElt z u * vecElt z v = vecElt z v * vecElt z u := by
      rw [← vecElt_add hf, ← vecElt_add hf, add_comm]
    have h2 : vecElt z u * t ^ (j : ℕ) = t ^ (j : ℕ) * vecElt z u := by
      have h3 : vecElt z v * (vecElt z u * t ^ (j : ℕ)) =
          vecElt z v * (t ^ (j : ℕ) * vecElt z u) := by
        rw [← mul_assoc, ← huv, mul_assoc, hcomm, mul_assoc]
      exact mul_left_cancel h3
    obtain ⟨h01, h12⟩ := eq_of_commute hf hj h2
    rw [← hu]
    exact vecElt_mem_zpowers_of_const hf h01 h12
  have hz3 : Nat.card (zpowers (vecElt z ![1, 1, 1])) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num)
      (orderOf_dvd_of_pow_eq_one ((isElemAbelian_baseA hf).2 _ (vecElt_mem_baseA hf _)))
  calc Nat.card (E ⊓ Subgroup.centralizer {y} : Subgroup H)
      = Nat.card ((E ⊓ Subgroup.centralizer {y} : Subgroup H).map c) :=
        (Subgroup.card_map_of_injective hcinj).symm
    _ ≤ Nat.card (zpowers (vecElt z ![1, 1, 1])) := Subgroup.card_le_of_le hle
    _ ≤ 3 := hz3

theorem exists_eq_map_conj_baseA (hf : WreathFacts z t)
    (hW : Nat.card (wreathW z t) = 3 ^ (Nat.card H).factorization 3)
    (h81 : Nat.card (wreathW z t) = 81) {E : Subgroup H} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) : ∃ h : H, E = (baseA z).map (MulAut.conj h).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 3) (by rw [hE27]; norm_num)
  obtain ⟨h, hh⟩ := exists_le_map_conj_of_card hW hEp
  refine ⟨h, ?_⟩
  have hE'W := map_conj_inv_le hh
  have heq := eq_baseA_of_le_wreathW hf h81 hE'W
    (isElemAbelian_map_hom (MulAut.conj h⁻¹).toMonoidHom hE)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective, hE27])
  rw [← heq, map_conj_map_conj_inv]

theorem exists_conj_mem_of_conj_t (hf : WreathFacts z t)
    (hW : Nat.card (wreathW z t) = 3 ^ (Nat.card H).factorization 3)
    (h81 : Nat.card (wreathW z t) = 81) {k : H} (hk : k * t * k⁻¹ ∈ baseA z)
    {E : Subgroup H} (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) {y : H}
    (hy : y ^ 3 = 1) : ∃ g : H, g * y * g⁻¹ ∈ E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h, rfl⟩ := exists_eq_map_conj_baseA hf hW h81 hE hE27
  have hyp : IsPGroup 3 (zpowers y) := by
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3, pow_one])
  obtain ⟨g, hg⟩ := exists_map_conj_le_wreathW hW hyp
  have hyW : g⁻¹ * y * g ∈ wreathW z t := by
    have := hg ⟨y, mem_zpowers y, rfl⟩
    simpa [MulAut.conj_apply] using this
  obtain ⟨v, j, hvj⟩ := mem_wreathW hf hyW
  have hmem : ∀ x ∈ baseA z, h * x * h⁻¹ ∈ (baseA z).map (MulAut.conj h).toMonoidHom :=
    fun x hx => ⟨x, hx, rfl⟩
  by_cases hj : j = 0
  · refine ⟨h * g⁻¹, ?_⟩
    have e : h * g⁻¹ * y * (h * g⁻¹)⁻¹ = h * (g⁻¹ * y * g) * h⁻¹ := by group
    rw [e, hvj, hj, Fin.val_zero, pow_zero, mul_one]
    exact hmem _ (vecElt_mem_baseA hf v)
  · have h3 : (vecElt z v * t ^ (j : ℕ)) ^ 3 = 1 :=
      calc (vecElt z v * t ^ (j : ℕ)) ^ 3 = (g⁻¹ * y * g⁻¹⁻¹) ^ 3 := by rw [inv_inv, hvj]
        _ = g⁻¹ * y ^ 3 * g⁻¹⁻¹ := conj_pow
        _ = 1 := by rw [hy]; group
    obtain ⟨u, hu⟩ := exists_conj_eq_t_pow hf hj h3
    refine ⟨h * k * vecElt z u * g⁻¹, ?_⟩
    have e : h * k * vecElt z u * g⁻¹ * y * (h * k * vecElt z u * g⁻¹)⁻¹ =
        h * (k * (vecElt z u * (g⁻¹ * y * g) * (vecElt z u)⁻¹) * k⁻¹) * h⁻¹ := by group
    rw [e, hvj, hu, ← conj_pow]
    exact hmem _ (pow_mem hk _)

end CFSG.RankThree.PartTwo.Sec8.Item812Res5
