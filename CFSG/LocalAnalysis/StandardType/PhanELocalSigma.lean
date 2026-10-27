module

public import CFSG.LocalAnalysis.StandardType.PhanELocalModels


public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.BorelTits Module

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ}

theorem sg_sg (hK : Nat.card K = (2 ^ f) ^ 2) (a : K) : sg K f (sg K f a) = a :=
  unitaryInvolution_involutive hK a

theorem sgv_apply (v : Fin n → K) (i : Fin n) : sgv K f n v i = sg K f (v i) := rfl

theorem sgv_sgv (hK : Nat.card K = (2 ^ f) ^ 2) (v : Fin n → K) :
    sgv K f n (sgv K f n v) = v := by
  funext i
  exact sg_sg hK (v i)

theorem mem_sgS {U : Submodule K (Fin n → K)} {v : Fin n → K} :
    v ∈ sgS K f n U ↔ sgv K f n v ∈ U := Iff.rfl

private theorem pls2_sgS_eq_map (hK : Nat.card K = (2 ^ f) ^ 2)
    (U : Submodule K (Fin n → K)) :
    sgS K f n U = U.map (sgv K f n) := by
  ext v
  rw [mem_sgS, Submodule.mem_map]
  constructor
  · intro hv
    exact ⟨sgv K f n v, hv, sgv_sgv hK v⟩
  · rintro ⟨u, hu, rfl⟩
    rw [sgv_sgv hK]
    exact hu

theorem sgS_sgS (hK : Nat.card K = (2 ^ f) ^ 2) (U : Submodule K (Fin n → K)) :
    sgS K f n (sgS K f n U) = U := by
  ext v
  rw [mem_sgS, mem_sgS, sgv_sgv hK]

theorem sgS_mono {U V : Submodule K (Fin n → K)} (h : U ≤ V) : sgS K f n U ≤ sgS K f n V := by
  intro v hv
  exact h hv

theorem sgS_inf (U V : Submodule K (Fin n → K)) :
    sgS K f n (U ⊓ V) = sgS K f n U ⊓ sgS K f n V :=
  Submodule.comap_inf U V (sgv K f n)

theorem sgS_sup (hK : Nat.card K = (2 ^ f) ^ 2) (U V : Submodule K (Fin n → K)) :
    sgS K f n (U ⊔ V) = sgS K f n U ⊔ sgS K f n V := by
  simp only [pls2_sgS_eq_map hK, Submodule.map_sup]

theorem sgS_top : sgS K f n (⊤ : Submodule K (Fin n → K)) = ⊤ :=
  Submodule.comap_top (sgv K f n)

theorem sgS_bot (hK : Nat.card K = (2 ^ f) ^ 2) :
    sgS K f n (⊥ : Submodule K (Fin n → K)) = ⊥ := by
  rw [pls2_sgS_eq_map hK]
  exact Submodule.map_bot (sgv K f n)

theorem sgS_Vsub (c : ℕ) : sgS K f n (Vsub (K := K) n c) = Vsub n c := by
  ext v
  rw [mem_sgS]
  constructor
  · intro hv j hj
    have h : sg K f (v j) = 0 := hv j hj
    exact (sg K f).map_eq_zero_iff.mp h
  · intro hv j hj
    rw [sgv_apply, hv j hj, map_zero]

private noncomputable def pls2_sgSAddEquiv (hK : Nat.card K = (2 ^ f) ^ 2)
    (U : Submodule K (Fin n → K)) : sgS K f n U ≃+ U where
  toFun v := ⟨sgv K f n v.1, v.2⟩
  invFun u := ⟨sgv K f n u.1, by
    rw [mem_sgS, sgv_sgv hK]
    exact u.2⟩
  left_inv v := Subtype.ext (sgv_sgv hK v.1)
  right_inv u := Subtype.ext (sgv_sgv hK u.1)
  map_add' a b := Subtype.ext (map_add (sgv K f n) a.1 b.1)

theorem finrank_sgS (hK : Nat.card K = (2 ^ f) ^ 2) (U : Submodule K (Fin n → K)) :
    finrank K (sgS K f n U) = finrank K U := by
  have h : Module.rank K (sgS K f n U) = Module.rank K U := by
    refine rank_eq_of_equiv_equiv (sg K f : K → K) (pls2_sgSAddEquiv hK U)
      (sg K f).bijective ?_
    intro r m
    apply Subtype.ext
    exact (sgv K f n).map_smulₛₗ r m.1
  simpa [Module.finrank] using congrArg Cardinal.toNat h

theorem sgS_span_singleton (hK : Nat.card K = (2 ^ f) ^ 2) (v : Fin n → K) :
    sgS K f n (Submodule.span K {v}) = Submodule.span K {sgv K f n v} := by
  rw [pls2_sgS_eq_map hK, Submodule.map_span]
  simp

theorem sgS_eq_iff (hK : Nat.card K = (2 ^ f) ^ 2) {U V : Submodule K (Fin n → K)} :
    sgS K f n U = V ↔ sgS K f n V = U := by
  constructor
  · intro h
    calc sgS K f n V = sgS K f n (sgS K f n U) := by rw [← h]
      _ = U := sgS_sgS hK U
  · intro h
    calc sgS K f n U = sgS K f n (sgS K f n V) := by rw [← h]
      _ = V := sgS_sgS hK V

theorem card_sg_fixed_le (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nat.card {a : K // sg K f a = a} ≤ 2 ^ f := by
  classical
  haveI := Fintype.ofFinite K
  have hbig : 1 < Nat.card K := Finite.one_lt_card
  rw [hK] at hbig
  have hq : 1 < 2 ^ f := by
    by_contra h
    have h1 : 2 ^ f = 1 := by
      have hpos : 0 < 2 ^ f := pow_pos (by norm_num) f
      omega
    rw [h1] at hbig
    norm_num at hbig
  set P : Polynomial K := Polynomial.X ^ 2 ^ f - Polynomial.X with hP
  have hdeg : P.natDegree = 2 ^ f := by
    rw [hP]
    exact FiniteField.X_pow_card_sub_X_natDegree_eq K hq
  have hp : P ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ.filter (fun a : K => sg K f a = a)).val ⊆ P.roots := by
    intro a ha
    rw [Finset.mem_val, Finset.mem_filter] at ha
    have ha' : a ^ 2 ^ f = a := by
      rw [← unitaryInvolution_apply]
      exact ha.2
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot.def, hP]
    simp [ha']
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg] at hle
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact hle

theorem card_sg_moved_ge (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nat.card K - 2 ^ f ≤ Nat.card {a : K // sg K f a ≠ a} := by
  classical
  haveI := Fintype.ofFinite K
  have hfix : Fintype.card {a : K // sg K f a = a} ≤ 2 ^ f := by
    simpa [Nat.card_eq_fintype_card] using card_sg_fixed_le (K := K) (f := f) hK
  have hK' : Fintype.card K = (2 ^ f) ^ 2 := by
    simpa [Nat.card_eq_fintype_card] using hK
  have hcompl : Fintype.card {a : K // sg K f a ≠ a} =
      Fintype.card K - Fintype.card {a : K // sg K f a = a} :=
    Fintype.card_subtype_compl (fun a : K => sg K f a = a)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcompl, hK']
  omega

private theorem pls2_exists_mem_avoid {α : Type*} [DecidableEq α] {s : Finset α}
    (hs : 3 ≤ s.card) (a b : α) : ∃ c ∈ s, c ≠ a ∧ c ≠ b := by
  classical
  let t := s.filter (fun c => c ≠ a ∧ c ≠ b)
  have hsplit := Finset.card_filter_add_card_filter_not (s := s)
    (p := fun c => c ≠ a ∧ c ≠ b)
  have hcompl_sub : (s.filter fun c => ¬ (c ≠ a ∧ c ≠ b)) ⊆ ({a, b} : Finset α) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    have hc' : ¬ (c ≠ a ∧ c ≠ b) := hc.2
    by_contra hcab
    rw [Finset.mem_insert, Finset.mem_singleton] at hcab
    exact hc' ⟨fun h => hcab (Or.inl h), fun h => hcab (Or.inr h)⟩
  have hcompl_card : (s.filter fun c => ¬ (c ≠ a ∧ c ≠ b)).card ≤ 2 := by
    have := Finset.card_le_card hcompl_sub
    have h2 : ({a, b} : Finset α).card ≤ 2 := Finset.card_le_two
    omega
  have hsplit' : t.card + (s.filter fun c => ¬ (c ≠ a ∧ c ≠ b)).card = s.card := hsplit
  have ht : 1 ≤ t.card := by omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < t.card)
  rw [Finset.mem_filter] at hc
  exact ⟨c, hc.1, hc.2.1, hc.2.2⟩

theorem exists_sg_moved_avoid (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (a b : K) :
    ∃ c : K, sg K f c ≠ c ∧ c ≠ a ∧ c ≠ b := by
  classical
  haveI := Fintype.ofFinite K
  have hge : 3 ≤ Nat.card K - 2 ^ f := by
    rw [hK, pow_two]
    have hmul : 4 * 3 ≤ 2 ^ f * (2 ^ f - 1) :=
      Nat.mul_le_mul hq (by omega)
    calc 3 ≤ 4 * 3 := by norm_num
      _ ≤ 2 ^ f * (2 ^ f - 1) := hmul
      _ = 2 ^ f * 2 ^ f - 2 ^ f := by rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hmoved := card_sg_moved_ge (K := K) (f := f) hK
  have h3 : 3 ≤ Nat.card {c : K // sg K f c ≠ c} := le_trans hge hmoved
  set s : Finset K := Finset.univ.filter (fun c => sg K f c ≠ c) with hs
  have hscard : s.card = Nat.card {c : K // sg K f c ≠ c} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  obtain ⟨c, hc, hca, hcb⟩ := pls2_exists_mem_avoid (by rw [hscard]; exact h3) a b
  refine ⟨c, ?_, hca, hcb⟩
  simpa [s] using (Finset.mem_filter.mp hc).2

private noncomputable def pls2_trace (hK : Nat.card K = (2 ^ f) ^ 2) : K →+ K where
  toFun c := c + sg K f c
  map_zero' := by simp
  map_add' c d := by
    simp only [map_add]
    ring

private theorem pls2_trace_fixed (hK : Nat.card K = (2 ^ f) ^ 2) (c : K) :
    sg K f (pls2_trace hK c) = pls2_trace hK c := by
  change sg K f (c + sg K f c) = c + sg K f c
  rw [map_add, sg_sg hK, add_comm]

private theorem pls2_card_trace_ker (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nat.card (pls2_trace hK).ker = Nat.card {c : K // sg K f c = c} := by
  refine Nat.card_congr ?_
  refine Equiv.subtypeEquivRight (fun c => ?_)
  show c ∈ (pls2_trace hK).ker ↔ sg K f c = c
  have hc : pls2_trace hK c = c + sg K f c := rfl
  constructor
  · intro h
    rw [AddMonoidHom.mem_ker, hc] at h
    exact (CharTwo.add_eq_zero.mp h).symm
  · intro h
    rw [AddMonoidHom.mem_ker, hc, h]
    exact CharTwo.add_eq_zero.mpr rfl

private theorem pls2_card_trace_range (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nat.card (pls2_trace hK).range = Nat.card {c : K // sg K f c = c} := by
  refine Nat.card_congr ?_
  refine Equiv.subtypeEquivRight (fun a => ?_)
  show (∃ c, pls2_trace hK c = a) ↔ sg K f a = a
  constructor
  · rintro ⟨c, rfl⟩
    exact pls2_trace_fixed hK c
  · intro ha
    obtain ⟨c, hc⟩ := exists_add_unitaryInvolution_eq hK ha
    exact ⟨c, hc⟩

theorem exists_sg_fixed_avoid (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (a b : K) :
    ∃ c : K, sg K f c = c ∧ c ≠ a ∧ c ≠ b := by
  classical
  haveI := Fintype.ofFinite K
  have hK0 : Nat.card {c : K // sg K f c = c} * Nat.card {c : K // sg K f c = c} =
      (2 ^ f) ^ 2 := by
    nth_rw 1 [← pls2_card_trace_ker hK]
    rw [← pls2_card_trace_range hK]
    rw [AddSubgroup.card_ker_mul_card_range (pls2_trace hK), hK]
  have h3 : 3 ≤ Nat.card {c : K // sg K f c = c} := by
    by_contra h
    have h2 : Nat.card {c : K // sg K f c = c} ≤ 2 := by omega
    have hmul : Nat.card {c : K // sg K f c = c} * Nat.card {c : K // sg K f c = c}
        ≤ 2 * 2 := Nat.mul_le_mul h2 h2
    have h16 : 16 ≤ Nat.card {c : K // sg K f c = c} * Nat.card {c : K // sg K f c = c} := by
      rw [hK0, pow_two]
      exact Nat.mul_le_mul hq hq
    omega
  set s : Finset K := Finset.univ.filter (fun c => sg K f c = c) with hs
  have hscard : s.card = Nat.card {c : K // sg K f c = c} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  obtain ⟨c, hc, hca, hcb⟩ := pls2_exists_mem_avoid (by rw [hscard]; exact h3) a b
  refine ⟨c, ?_, hca, hcb⟩
  simpa [s] using (Finset.mem_filter.mp hc).2

theorem exists_sg_trace (hK : Nat.card K = (2 ^ f) ^ 2) {a : K} (ha : sg K f a = a) :
    ∃ c : K, c + sg K f c = a :=
  exists_add_unitaryInvolution_eq hK ha

end CFSG.ClassicalInvolution.Phan.PhanE

end
