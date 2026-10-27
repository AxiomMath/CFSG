module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_13

namespace CFSG
end CFSG
open CFSG
/-! # Theorem 4.18(a) from BG Section 4 -/

universe u

section Main

open scoped FixedPoints

public theorem CFSG.groupRank_pCore_quotient_pPrimeCore_le_two
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hrank : primeRank p H ≤ 2) :
    groupRank (pCore p (H ⧸ pPrimeCore p H)) ≤ 2 := by
  let M : Subgroup H := pPrimeCore p H
  let q : H →* (H ⧸ M) := QuotientGroup.mk' M
  let R : Subgroup (H ⧸ M) := pCore p (H ⧸ M)
  have hR_p : IsPGroup p R := pCore_isPGroup (G := H ⧸ M) (p := p)
  let L : Subgroup H := Op_p'p p H
  have hM_le_L : M ≤ L := by
    intro x hx
    change q x ∈ pCore p (H ⧸ M)
    have hx1 : q x = 1 := (QuotientGroup.eq_one_iff (N := M) (x := x)).2 hx
    simp [q, hx1]
  have hmapL : L.map q = R := by
    dsimp [L, q, M, R, Op_p'p]
    simpa using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := QuotientGroup.mk' (pPrimeCore p H))
        (h := QuotientGroup.mk'_surjective (pPrimeCore p H))
        (H := pCore p (H ⧸ pPrimeCore p H)))
  let N : Subgroup L := M.subgroupOf L
  have hN_card : Nat.card N = Nat.card M := by
    have hmapN : N.map L.subtype = M := by
      simp [N, inf_eq_left.mpr hM_le_L]
    calc
      Nat.card N = Nat.card (N.map L.subtype) := by
        symm
        exact Subgroup.card_map_of_injective (K := N) (f := L.subtype) L.subtype_injective
      _ = Nat.card M := by rw [hmapN]
  let eLN : (↥L ⧸ N) ≃* R :=
    (quotientSubgroupRangeEquiv L M).trans (MulEquiv.subgroupCongr hmapL)
  have hquot_p : IsPGroup p (↥L ⧸ N) := hR_p.of_equiv eLN.symm
  have hNcop : Nat.Coprime p (Nat.card N) := by
    rw [hN_card]
    simpa [M] using (pPrimeCore_coprime_card (G := H) (p := p))
  have hN_index_cop : Nat.Coprime (Nat.card N) N.index := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hquot_p
    rw [Subgroup.index_eq_card, hn]
    exact hNcop.symm.pow_right n
  obtain ⟨K, hcompl⟩ := Subgroup.exists_right_complement'_of_coprime (N := N) hN_index_cop
  let qL : L →* (↥L ⧸ N) := QuotientGroup.mk' N
  let qK : K →* (↥L ⧸ N) := qL.comp K.subtype
  have hqK_inj : Function.Injective qK := by
    intro a b hab
    apply Subtype.ext
    change qL (a : L) = qL (b : L) at hab
    have habN : (a : L)⁻¹ * (b : L) ∈ N := QuotientGroup.eq.mp hab
    have habK : (a : L)⁻¹ * (b : L) ∈ K := K.mul_mem (K.inv_mem a.property) b.property
    have hab_one : (a : L)⁻¹ * (b : L) = 1 := (Subgroup.disjoint_def.mp hcompl.disjoint) habN habK
    have := congrArg (fun t : L => (a : L) * t) hab_one
    simpa [mul_assoc] using this.symm
  have hqK_surj : Function.Surjective qK := by
    intro y
    refine QuotientGroup.induction_on y ?_
    intro x
    have hx_sup : x ∈ N ⊔ K := by
      simp [hcompl.sup_eq_top]
    rcases (Subgroup.mem_sup_of_normal_left (s := N) (t := K) (x := x)).1 hx_sup with
      ⟨n, hnN, k, hkK, hnk⟩
    refine ⟨⟨k, hkK⟩, ?_⟩
    change qL (k : L) = qL x
    have hn1 : qL n = 1 := (QuotientGroup.eq_one_iff (N := N) (x := n)).2 hnN
    calc
      qL (k : L) = qL n * qL k := by simp [hn1]
      _ = qL (n * k) := by simp [qL]
      _ = qL x := by simp [hnk]
  let eKQ : K ≃* (↥L ⧸ N) := MulEquiv.ofBijective qK ⟨hqK_inj, hqK_surj⟩
  let eKR : K ≃* R := eKQ.trans eLN
  have hK_p : IsPGroup p K := hR_p.of_equiv eKR.symm
  let KH : Subgroup H := K.map L.subtype
  have hKH_p : IsPGroup p KH := IsPGroup.map (p := p) (H := K) hK_p L.subtype
  have hKH_rank_p : primeRank p KH ≤ 2 :=
    (primeRank_le_of_subgroup (S := KH) p).trans hrank
  have hKH_rank : groupRank KH ≤ 2 :=
    groupRank_le_two_of_primeRank_le_two_of_isPGroup hKH_p hKH_rank_p
  let eKH : K ≃* KH := Subgroup.equivMapOfInjective K L.subtype L.subtype_injective
  have hK_rank : groupRank K ≤ 2 :=
    (groupRank_le_of_equiv (R := KH) (S := K) eKH.symm).trans hKH_rank
  exact (groupRank_le_of_equiv (R := K) (S := R) eKR).trans hK_rank

public theorem CFSG.theorem_4_18_a {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hp_mem : p ∣ Nat.card G)
    (hrank : primeRank p G ≤ 2) :
    IsLargestPrimeDivisor p (Nat.card (G ⧸ pPrimeCore p G)) := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let Q := G ⧸ M
  let R : Subgroup Q := pCore p Q
  have hpodd : p ≠ 2 := Odd.ne_two_of_dvd_nat hodd hp_mem
  have : M.Normal := by
    dsimp [M]
    infer_instance
  have : Group.IsSolvable G := hsolv
  have hsolvQ : Group.IsSolvable Q := by infer_instance
  have hQodd : Odd (Nat.card Q) :=
    hodd.of_dvd_nat (Subgroup.card_quotient_dvd_card (s := M))
  have hM_coprime : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  have hcard_eq : Nat.card G = Nat.card Q * Nat.card M := by
    simpa [Q, M] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := G) (s := M))
  have hp_dvd_Q : p ∣ Nat.card Q := by
    exact hM_coprime.dvd_of_dvd_mul_right (hcard_eq ▸ hp_mem)
  have hR_p : IsPGroup p R := pCore_isPGroup (G := Q) (p := p)
  have hR_rank : groupRank R ≤ 2 := by
    simpa [Q, R, M] using groupRank_pCore_quotient_pPrimeCore_le_two
      (H := G) (p := p) hrank
  have hA3 : selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅ := by
    let : Fact (IsPGroup p R) := ⟨hR_p⟩
    exact (lemma_4_7 (R := R) (p := p) hpodd hR_p).2 hR_rank
  have hcoreQ : pPrimeCore p Q = ⊥ := by
    simpa [Q, M] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p))
  have hfit_eq : fittingSubgroup Q = R := Fitting_eq_pcore Q p hcoreQ
  have hcentR : Subgroup.centralizer (R : Set Q) ≤ R := by
    simpa [Q, R, hfit_eq] using
      centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := Q) hsolvQ
  let φ : Q →* MulAut R := MulAut.conjNormal (H := R)
  have hφker_le_R : φ.ker ≤ R := by
    intro x hx
    have hxcent : x ∈ Subgroup.centralizer (R : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hx_apply : φ x ⟨r, hr⟩ = ⟨r, hr⟩ := by
        rw [hx]
        rfl
      have hconj : x * r * x⁻¹ = r := by
        simpa [φ, MulAut.conjNormal_apply, MulAut.conj_apply] using congrArg Subtype.val hx_apply
      have := congrArg (fun t : Q => t * x) hconj
      simpa [mul_assoc] using this.symm
    exact hcentR hxcent
  let A : Subgroup (MulAut R) := φ.range
  have hφ_range_card : Nat.card A = Nat.card (Q ⧸ φ.ker) := by
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm
  refine ⟨Fact.out, ?_, ?_⟩
  · simpa [Q, M] using hp_dvd_Q
  · intro q hqprime hq_dvd
    by_cases hq_eq_p : q = p
    · omega
    · have : Fact q.Prime := ⟨hqprime⟩
      have hker_p : IsPGroup p φ.ker := hR_p.to_le hφker_le_R
      obtain ⟨n, hker_card⟩ := hker_p.exists_card_eq
      have hp_not_dvd_q : ¬ p ∣ q := by
        intro hpq
        have hq_eq_p' : q = p :=
          (Fact.out : Nat.Prime q).dvd_iff_eq (Fact.out : Nat.Prime p).ne_one |>.1 hpq
        exact hq_eq_p hq_eq_p'
      have hq_coprime_ker : Nat.Coprime q (Nat.card φ.ker) := by
        rw [hker_card]
        exact (Fact.out : Nat.Prime p).coprime_pow_of_not_dvd hp_not_dvd_q
      have hQ_card : Nat.card Q = Nat.card (Q ⧸ φ.ker) * Nat.card φ.ker := by
        simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := Q) (s := φ.ker))
      have hq_dvd_quot : q ∣ Nat.card (Q ⧸ φ.ker) := by
        exact hq_coprime_ker.dvd_of_dvd_mul_right (by simpa [Q, M, hQ_card] using hq_dvd)
      have hq_dvd_A : q ∣ Nat.card A := by
        simpa [hφ_range_card] using hq_dvd_quot
      have hq_dvd_aut : q ∣ Nat.card (MulAut R) :=
        hq_dvd_A.trans (Subgroup.card_subgroup_dvd_card A)
      let : Fact (IsPGroup p R) := ⟨hR_p⟩
      have hq_lt_p : q < p :=
        (lemma_4_13 (R := R) (p := p) (q := q) hpodd hA3 hq_dvd_aut hq_eq_p).2
      exact le_of_lt hq_lt_p

end Main
