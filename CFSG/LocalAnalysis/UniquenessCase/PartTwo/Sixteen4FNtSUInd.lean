module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtSUBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtSUReduce

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

private theorem w183_herm_self_eq_ncard_support {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) {n : ℕ} (a : Fin n → K) :
    herm (s16ntSuSigma K) a a = ((Function.support a).ncard : K) := by
  classical
  have hterm : ∀ i : Fin n, s16ntSuSigma K (a i) * a i =
      (if a i = 0 then (0 : K) else 1) := by
    intro i
    by_cases hi : a i = 0
    · simp [hi]
    · rw [if_neg hi]; exact s16nt_su_norm_one hK hi
  have hsum : (∑ i : Fin n, (if a i = 0 then (0 : K) else 1)) =
      ((Function.support a).ncard : K) := by
    have hsupp : Function.support a = ↑(Finset.univ.filter fun i => a i ≠ 0) := by
      ext i; simp [Function.mem_support]
    rw [hsupp, Set.ncard_coe_finset]
    have hcongr : (∑ i : Fin n, (if a i = 0 then (0 : K) else 1)) =
        (∑ i : Fin n, (if a i ≠ 0 then (1 : K) else 0)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : a i = 0 <;> simp [hi]
    rw [hcongr, Finset.sum_boole]
  rw [herm]
  simp_rw [hterm]
  exact hsum

private theorem w183_su_ind_aux {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) (hσ : IsUnitaryInvolution (s16ntSuSigma K)) {n : ℕ}
    (J : Subgroup ↥(SUid (s16ntSuSigma K) n))
    (hbase : ∀ (a : Fin n → K) (g : SUid (s16ntSuSigma K) n),
      ((Function.support a).ncard = 2 ∨ (Function.support a).ncard = 4) →
        (∀ v : Fin n → K, g • v = v + herm (s16ntSuSigma K) a v • a) → g ∈ J)
    {a : Fin n → K} (ha : herm (s16ntSuSigma K) a a = 0)
    {g : SUid (s16ntSuSigma K) n}
    (hg : ∀ v : Fin n → K, g • v = v + herm (s16ntSuSigma K) a v • a) : g ∈ J := by
  have claim : ∀ m, ∀ a : Fin n → K, (Function.support a).ncard = m →
      herm (s16ntSuSigma K) a a = 0 →
      ∀ g : SUid (s16ntSuSigma K) n,
        (∀ v : Fin n → K, g • v = v + herm (s16ntSuSigma K) a v • a) → g ∈ J :=
    fun m => Nat.strong_induction_on m fun m ih a hk ha g hg => by
      rcases m with _ | _ | _ | _ | _ | m
      · have hsupp : Function.support a = ∅ :=
          (Set.ncard_eq_zero (s := Function.support a)).mp hk
        have ha0 : a = 0 := by
          funext i
          have hi : i ∉ Function.support a := by rw [hsupp]; exact Set.notMem_empty i
          simpa [Function.mem_support] using hi
        have hg1 : g = 1 := ext_smul _ fun v => by
          rw [hg v, ha0, herm_zero_left, zero_smul, add_zero, one_smul]
        rw [hg1]; exact J.one_mem
      · exfalso
        have h := w183_herm_self_eq_ncard_support hK a
        rw [hk, ha, Nat.cast_one] at h
        exact zero_ne_one h
      · exact hbase a g (Or.inl hk) hg
      · exfalso
        have h := w183_herm_self_eq_ncard_support hK a
        rw [hk, ha] at h
        obtain ⟨d, hd⟩ := (CharP.cast_eq_zero_iff K 2 3).mp h.symm
        omega
      · exact hbase a g (Or.inr hk) hg
      · obtain ⟨w, hw4, hww, hwa, hlt⟩ :=
          s16nt_su_supp_reduce hK (by rw [hk]; omega)
        have hc1 : (1 : K) + s16ntSuSigma K 1 = 0 := by
          rw [map_one]; exact CharTwo.add_self_eq_zero 1
        obtain ⟨gw, _, hgw⟩ := exists_mem_T_tv hσ.invol hww (c := 1) hc1
        have hgw' : ∀ v : Fin n → K, gw • v = v + herm (s16ntSuSigma K) w v • w :=
          fun v => by rw [hgw v, one_mul]
        have hgwJ : gw ∈ J := hbase w gw (Or.inr hw4) hgw'
        have hgwa : gw • a = a + w := by rw [hgw' a, hwa, one_smul]
        have hlt' : (Function.support (a + w)).ncard < m + 5 := lt_of_lt_of_eq hlt hk
        have hconj : ∀ v : Fin n → K, (gw * g * gw⁻¹) • v =
            v + herm (s16ntSuSigma K) (a + w) v • (a + w) := by
          intro v
          rw [conj_smul_of_tv gw g (c := 1) (fun u => by rw [one_mul]; exact hg u) v,
            hgwa, one_mul]
        have hww' : herm (s16ntSuSigma K) (a + w) (a + w) = 0 := by
          rw [← hgwa, herm_smul_smul, ha]
        have hIH : gw * g * gw⁻¹ ∈ J :=
          ih (Function.support (a + w)).ncard hlt' (a + w) rfl hww' _ hconj
        have hg_eq : g = gw⁻¹ * (gw * g * gw⁻¹) * gw := by group
        rw [hg_eq]
        exact J.mul_mem (J.mul_mem (J.inv_mem hgwJ) hIH) hgwJ
  exact claim _ a rfl ha g hg

theorem s16nt_su_ind {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {n : ℕ} (hn : 4 ≤ n) (J : Subgroup ↥(SUid (s16ntSuSigma K) n))
    (hbase : ∀ (a : Fin n → K) (g : SUid (s16ntSuSigma K) n),
      ((Function.support a).ncard = 2 ∨ (Function.support a).ncard = 4) →
        (∀ v : Fin n → K, g • v = v + herm (s16ntSuSigma K) a v • a) → g ∈ J) : J = ⊤ := by
  have hσ : IsUnitaryInvolution (s16ntSuSigma K) :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) (by rw [hK]; norm_num)
  rw [eq_top_iff]
  rw [← T_eq_top hσ (by omega) (fun h => by omega)]
  change Subgroup.closure (tvSet (s16ntSuSigma K) n) ≤ J
  rw [Subgroup.closure_le]
  rintro g ⟨a, c, ha, hc, hgt⟩
  have hc' : c * (c + 1) = 0 := by
    have h2 : c + c ^ 2 = 0 := by rw [← s16nt_su_sigma_apply]; exact hc
    calc c * (c + 1) = c ^ 2 + c := by ring
      _ = c + c ^ 2 := by rw [add_comm]
      _ = 0 := h2
  rcases mul_eq_zero.mp hc' with h0 | h1
  · have hg1 : g = 1 := ext_smul _ fun v => by
      rw [hgt v, h0, zero_mul, zero_smul, add_zero, one_smul]
    rw [hg1]; exact J.one_mem
  · have hc1 : c = 1 := by
      have h := (eq_neg_of_add_eq_zero_right h1).symm
      rwa [CharTwo.neg_eq] at h
    exact w183_su_ind_aux hK hσ J hbase ha fun v => by rw [hgt v, hc1, one_mul]

theorem s16nt_su_gen {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {n : ℕ} (hn : 4 ≤ n) {s : SUid (s16ntSuSigma K) n}
    (hs : ∀ v : Fin n → K,
      s • v = v + herm (s16ntSuSigma K) (s16ntSuV0 n K) v • s16ntSuV0 n K) :
    Subgroup.closure ((s16ntSuMono K n : Set ↥(SUid (s16ntSuSigma K) n)) ∪ {s}) = ⊤ := by
  have hM : s16ntSuMono K n ≤
      Subgroup.closure ((s16ntSuMono K n : Set ↥(SUid (s16ntSuSigma K) n)) ∪ {s}) :=
    fun _ hx => Subgroup.subset_closure (Set.mem_union_left _ hx)
  have hsJ : s ∈ Subgroup.closure ((s16ntSuMono K n : Set ↥(SUid (s16ntSuSigma K) n)) ∪ {s}) :=
    Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton s))
  exact s16nt_su_ind hK hn _ fun _ _ h2 hg => h2.elim (fun h2 => s16nt_su_base_two hK _ hM h2 hg)
    fun h2 => s16nt_su_base_four hK hn _ hM hs hsJ h2 hg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
