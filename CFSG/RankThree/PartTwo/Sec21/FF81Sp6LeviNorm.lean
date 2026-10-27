module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check
public import Certificates.Certificate799650
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Levi

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec4.Item434Kit
open CFSG.RankThree.PartTwo.Sec21.FF79 (Cen Nor)

abbrev LeviN {G : Type} [Group G] (L : Subgroup G) (u v : G) : Prop :=
  L ⊓ Cen (u * v) ≤ Nor (Subgroup.closure ({u, v} : Set G))

theorem LeviN.map {G G' : Type} [Group G] [Group G'] {f : G →* G'} (hf : Function.Injective f)
    {L : Subgroup G} {u v : G} (h : LeviN L u v) : LeviN (L.map f) (f u) (f v) := by
  intro y hy
  obtain ⟨hyL, hyC⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨y₀, hy₀L, rfl⟩ := Subgroup.mem_map.mp hyL
  have hy₀C : y₀ ∈ Cen (u * v) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
    apply hf
    simp only [map_mul]
    exact hyC
  have h1 := h (Subgroup.mem_inf.mpr ⟨hy₀L, hy₀C⟩)
  have h2 := Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f h1)
  rwa [MonoidHom.map_closure, Set.image_pair] at h2

theorem LeviN.conj {G : Type} [Group G] {u v : G} (h : LeviN ⊤ u v) (g : G) :
    LeviN ⊤ (g * u * g⁻¹) (g * v * g⁻¹) := by
  have := LeviN.map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective h
  rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at this

theorem LeviN.symm {G : Type} [Group G] {L : Subgroup G} {u v : G} (h : LeviN L u v)
    (hc : u * v = v * u) : LeviN L v u := by
  intro y hy
  obtain ⟨hyL, hyC⟩ := Subgroup.mem_inf.mp hy
  have hyC' : y ∈ Cen (u * v) := by rw [hc]; exact hyC
  have := h (Subgroup.mem_inf.mpr ⟨hyL, hyC'⟩)
  rwa [Set.pair_comm] at this

theorem LeviN.inv {G : Type} [Group G] {u v : G} (h : LeviN ⊤ u v) (hc : u * v = v * u) :
    LeviN ⊤ u⁻¹ v⁻¹ := by
  intro y hy
  obtain ⟨-, hyC⟩ := Subgroup.mem_inf.mp hy
  have e : u⁻¹ * v⁻¹ = (u * v)⁻¹ := by rw [hc, mul_inv_rev]
  have hyC' : y ∈ Cen (u * v) := by
    rw [e, Subgroup.mem_centralizer_singleton_iff] at hyC
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Commute.inv_right_iff.mp (show Commute y (u * v)⁻¹ from hyC)
  have := h (Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, hyC'⟩)
  have hcl : Subgroup.closure ({u⁻¹, v⁻¹} : Set G) = Subgroup.closure {u, v} := by
    rw [← Subgroup.closure_inv]
    congr 1
    ext x
    simp [Set.mem_inv]
  rwa [hcl]

theorem mem_normalizer_of_conj_mem {G : Type} [Group G] [Finite G] {S : Set G} {y : G}
    (h : ∀ x ∈ S, y * x * y⁻¹ ∈ Subgroup.closure S) : y ∈ Nor (Subgroup.closure S) := by
  have hle : (Subgroup.closure S).map (MulAut.conj y).toMonoidHom ≤ Subgroup.closure S := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro x hx
    exact h x hx
  exact Subgroup.mem_normalizer_fintype fun n hn => hle ⟨n, hn, rfl⟩

theorem val_eq_one_or_two {a : ZMod 3} (ha : a ≠ 0) : a.val = 1 ∨ a.val = 2 := by
  fin_cases a
  · exact absurd rfl ha
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem conj_pow_eq (g x : H6) (k : ℕ) : g * x ^ k * g⁻¹ = (g * x * g⁻¹) ^ k := by
  have h := map_pow (MulAut.conj g) x k
  simpa only [MulAut.conj_apply] using h

section Cert


theorem levi_table {j : Fin 5} (hj : j = 3 ∨ j = 4) {y : H6} (hy : y ∈ centSub j) :
    (∃ a b : ℕ, y * zH 0 = (zH 0 ^ a * zH 1 ^ b) * y) ∧
      ∃ a b : ℕ, y * zH 1 = (zH 0 ^ a * zH 1 ^ b) * y := by
  obtain ⟨t, ht, hcode, -⟩ := exists_code_closure _ _ _ (cent_spec j).2.1 hy
  have hcheck : leviCheck = true := Certificates.certificate799650
  simp only [leviCheck, Bool.and_eq_true] at hcheck
  have hpred : leviPred ((closureT ((centGens j).map Prod.fst)).getD t []) = true := by
    rcases hj with rfl | rfl
    · exact allCheck_spec hcheck.1 ht
    · exact allCheck_spec hcheck.2 ht
  simp only [leviPred, Bool.and_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq] at hpred
  obtain ⟨⟨a, -, b, -, h0⟩, ⟨a', -, b', -, h1⟩⟩ := hpred
  have hm : ∀ a b : ℕ, mat6 (zH 0 ^ a * zH 1 ^ b) = dec6 (vecCode a b 0) := fun a b => by
    have := mat6_pow_mul a b 0
    rwa [pow_zero, mul_one] at this
  refine ⟨⟨a, b, ?_⟩, ⟨a', b', ?_⟩⟩
  · apply mat6_injective
    rw [map_mul, map_mul, hm, ← hcode, mat6_zH, ← dec6_mul6, ← dec6_mul6, h0]
  · apply mat6_injective
    rw [map_mul, map_mul, hm, ← hcode, mat6_zH, ← dec6_mul6, ← dec6_mul6, h1]

theorem pow_mul_pow_mem_closure (a b : ℕ) :
    zH 0 ^ a * zH 1 ^ b ∈ Subgroup.closure ({zH 0, zH 1} : Set H6) :=
  mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
    (pow_mem (Subgroup.subset_closure (by simp)) _)

theorem mem_normalizer_of_table {j : Fin 5} (hj : j = 3 ∨ j = 4) {y : H6} (hy : y ∈ centSub j) :
    y ∈ Nor (Subgroup.closure ({zH 0, zH 1} : Set H6)) := by
  obtain ⟨⟨a, b, h0⟩, ⟨a', b', h1⟩⟩ := levi_table hj hy
  refine mem_normalizer_of_conj_mem ?_
  intro x hx
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx
  · rw [hx, h0, mul_inv_cancel_right]
    exact pow_mul_pow_mem_closure a b
  · rw [hx, h1, mul_inv_cancel_right]
    exact pow_mul_pow_mem_closure a' b'

private theorem aVec_three : aVec 3 = ![1, 1, 0] := by
  ext i
  fin_cases i <;> rfl

private theorem aVec_four : aVec 4 = ![1, 2, 0] := by
  ext i
  fin_cases i <;> rfl

private theorem aElt_three : aElt 3 = zH 0 * zH 1 := by
  rw [aElt, aVec_three]
  simp only [vecElt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [show (1 : ZMod 3).val = 1 from rfl, show (0 : ZMod 3).val = 0 from rfl, pow_one, pow_one,
    pow_zero, mul_one]

private theorem aElt_four : aElt 4 = zH 0 * zH 1 ^ 2 := by
  rw [aElt, aVec_four]
  simp only [vecElt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [show (1 : ZMod 3).val = 1 from rfl, show (2 : ZMod 3).val = 2 from rfl,
    show (0 : ZMod 3).val = 0 from rfl, pow_one, pow_zero, mul_one]

theorem closure_zero_sq :
    Subgroup.closure ({zH 0, zH 1 ^ 2} : Set H6) = Subgroup.closure {zH 0, zH 1} := by
  have h : (zH 1 ^ 2) ^ 2 = zH 1 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, zH_pow_three, one_mul]
  have a0 : zH 0 ∈ Subgroup.closure ({zH 0, zH 1} : Set H6) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have a1 : zH 1 ∈ Subgroup.closure ({zH 0, zH 1} : Set H6) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have b0 : zH 0 ∈ Subgroup.closure ({zH 0, zH 1 ^ 2} : Set H6) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have b1 : zH 1 ^ 2 ∈ Subgroup.closure ({zH 0, zH 1 ^ 2} : Set H6) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  apply le_antisymm
  · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨a0, pow_mem a1 2⟩
  · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨b0, ?_⟩
    have h3 := pow_mem b1 2
    rwa [h] at h3

theorem leviN_zero_one : LeviN ⊤ (zH 0) (zH 1) := by
  intro y hy
  obtain ⟨-, hyC⟩ := Subgroup.mem_inf.mp hy
  refine mem_normalizer_of_table (j := 3) (Or.inl rfl) ?_
  rw [centSub_eq, aElt_three]
  exact hyC

theorem leviN_zero_one_sq : LeviN ⊤ (zH 0) (zH 1 ^ 2) := by
  intro y hy
  obtain ⟨-, hyC⟩ := Subgroup.mem_inf.mp hy
  have h : y ∈ Nor (Subgroup.closure ({zH 0, zH 1} : Set H6)) := by
    refine mem_normalizer_of_table (j := 4) (Or.inr rfl) ?_
    rw [centSub_eq, aElt_four]
    exact hyC
  rwa [closure_zero_sq]

theorem zH_inv_eq_sq (i : Fin 3) : (zH i)⁻¹ = zH i ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact zH_pow_three i)

theorem zH_sq_inv_eq (i : Fin 3) : (zH i ^ 2)⁻¹ = zH i := by
  rw [← zH_inv_eq_sq, inv_inv]

theorem conj_tpow (μ p : Fin 3) : Sec4.Item434SmallTwoIII.tH ^ μ.val * zH p * (Sec4.Item434SmallTwoIII.tH ^ μ.val)⁻¹ = zH (p + μ) := by
  fin_cases μ
  · simp
  · show CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 1 * zH p * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 1)⁻¹ = zH (p + 1)
    rw [pow_one, tH_conj]
  · show CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 2 * zH p * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 2)⁻¹ = zH (p + 2)
    rw [sq, mul_inv_rev, show CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * zH p * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹ * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹) =
      CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * zH p * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹) * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹ by group, tH_conj, tH_conj, add_assoc]
    rfl

theorem leviN_base {a c : ZMod 3} (ha : a ≠ 0) (hc : c ≠ 0) :
    LeviN ⊤ (zH 0 ^ a.val) (zH 1 ^ c.val) := by
  have hcomm : zH 0 * zH 1 = zH 1 * zH 0 := zH_comm 0 1
  have hcomm2 : zH 0 * zH 1 ^ 2 = zH 1 ^ 2 * zH 0 :=
    (Commute.pow_right (show Commute (zH 0) (zH 1) from hcomm) 2).eq
  rcases val_eq_one_or_two ha with h1 | h1 <;> rcases val_eq_one_or_two hc with h2 | h2 <;>
    rw [h1, h2]
  · rw [pow_one, pow_one]
    exact leviN_zero_one
  · rw [pow_one]
    exact leviN_zero_one_sq
  · have h := leviN_zero_one_sq.inv hcomm2
    rwa [zH_inv_eq_sq, zH_sq_inv_eq, ← pow_one (zH 1)] at h
  · have h := leviN_zero_one.inv hcomm
    rwa [zH_inv_eq_sq, zH_inv_eq_sq] at h

theorem leviN_zH {p q : Fin 3} (hpq : p ≠ q) {a c : ZMod 3} (ha : a ≠ 0) (hc : c ≠ 0) :
    LeviN ⊤ (zH p ^ a.val) (zH q ^ c.val) := by
  have shift : ∀ (μ : Fin 3) {a c : ZMod 3}, a ≠ 0 → c ≠ 0 →
      LeviN ⊤ (zH (0 + μ) ^ a.val) (zH (1 + μ) ^ c.val) := by
    intro μ a c ha hc
    have h := (leviN_base ha hc).conj (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ μ.val)
    rwa [conj_pow_eq, conj_pow_eq, conj_tpow, conj_tpow] at h
  have hcyc : ∀ p q : Fin 3, p ≠ q → q = p + 1 ∨ p = q + 1 := by decide
  rcases hcyc p q hpq with h | h
  · have h' := shift p ha hc
    rwa [zero_add, add_comm, ← h] at h'
  · have h' := shift q hc ha
    rw [zero_add, add_comm, ← h] at h'
    refine h'.symm ?_
    exact (Commute.pow_pow (zH_comm q p) _ _).eq

end Cert

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Levi
