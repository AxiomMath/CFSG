module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_17
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_b

namespace CFSG
end CFSG
open CFSG
/-! # Theorem 4.18(c) from BG Section 4 -/

universe u

section Main

open scoped FixedPoints

public theorem CFSG.theorem_4_18_c {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hp_mem : p ∣ Nat.card G)
    (hrank : primeRank p G ≤ 2) :
    HasNormalPComplement p (derivedSubgroup G) := by
  classical
  let : Group.IsSolvable G := hsolv
  let D : Subgroup G := derivedSubgroup G
  let M : Subgroup G := pPrimeCore p G
  let : M.Normal := by
    dsimp [M]
    infer_instance
  let Q := G ⧸ M
  let q : G →* Q := QuotientGroup.mk' M
  let DQ : Subgroup Q := derivedSubgroup Q
  let R : Subgroup Q := pCore p Q
  have hpodd : p ≠ 2 := by
    intro hp_two
    have hp_odd : Odd p := hodd.of_dvd_nat hp_mem
    rw [hp_two] at hp_odd
    norm_num [Nat.odd_iff] at hp_odd
  have : M.Normal := by
    dsimp [M]
    infer_instance
  have hsolvQ : Group.IsSolvable Q := by infer_instance
  have hQodd : Odd (Nat.card Q) := hodd.of_dvd_nat (Subgroup.card_quotient_dvd_card (s := M))
  have hcoreQ : pPrimeCore p Q = ⊥ := by
    simpa [Q, M] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p))
  have hR_p : IsPGroup p R := pCore_isPGroup (G := Q) (p := p)
  have hfit_eq : fittingSubgroup (G ⧸ M) = pCore p (G ⧸ M) := Fitting_eq_pcore (G ⧸ M) p hcoreQ
  have hcentR : Subgroup.centralizer (R : Set Q) ≤ R := by
    simpa [Q, R, hfit_eq] using
      centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := (G ⧸ M)) hsolvQ
  let L : Subgroup G := Op_p'p p G
  have hM_le_L : M ≤ L := by
    intro x hx
    change q x ∈ pCore p Q
    have hx1 : q x = 1 := (QuotientGroup.eq_one_iff (N := M) (x := x)).2 hx
    simp [Q, q, hx1]
  have hmapL : L.map q = R := by
    dsimp [L, q, M, Q, R, Op_p'p]
    simpa using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := QuotientGroup.mk' (pPrimeCore p G))
        (h := QuotientGroup.mk'_surjective (pPrimeCore p G))
        (H := pCore p (G ⧸ pPrimeCore p G)))
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
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
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
  let KG : Subgroup G := K.map L.subtype
  have hKG_p : IsPGroup p KG := IsPGroup.map (p := p) (H := K) hK_p L.subtype
  have hKG_rank_p : primeRank p KG ≤ 2 :=
    (primeRank_le_of_subgroup (S := KG) p).trans hrank
  have hKG_rank : groupRank KG ≤ 2 :=
    groupRank_le_two_of_primeRank_le_two_of_isPGroup hKG_p hKG_rank_p
  let eKG : K ≃* KG := Subgroup.equivMapOfInjective K L.subtype L.subtype_injective
  have hK_rank : groupRank K ≤ 2 :=
    (groupRank_le_of_equiv (R := KG) (S := K) eKG.symm).trans hKG_rank
  have hR_rank : groupRank R ≤ 2 :=
    (groupRank_le_of_equiv (R := K) (S := R) eKR).trans hK_rank
  let φ : Q →* MulAut R := MulAut.conjNormal (H := R)
  have hφker_eq_cent : φ.ker = Subgroup.centralizer (R : Set Q) := by
    ext x
    rw [Subgroup.mem_centralizer_iff, MonoidHom.mem_ker]
    constructor
    · intro hx r hr
      have hx_apply : (φ x) ⟨r, hr⟩ = ⟨r, hr⟩ := by
        simp [hx]
      have hconj : x * r * x⁻¹ = r := by
        simpa [φ] using congrArg Subtype.val hx_apply
      have := congrArg (fun t : Q => t * x) hconj
      simpa [mul_assoc] using this.symm
    · intro hx
      ext r
      have hcomm : (r : Q) * x = x * r := hx r r.2
      have hconj : x * (r : Q) * x⁻¹ = r := by
        calc
          x * (r : Q) * x⁻¹ = ((r : Q) * x) * x⁻¹ := by rw [hcomm]
          _ = r := by simp [mul_assoc]
      simpa [φ, MulAut.conjNormal_apply, MulAut.conj_apply] using hconj
  let A : Subgroup (MulAut R) := φ.range
  let φA : Q →* A := φ.rangeRestrict
  have hAodd : Odd (Nat.card A) := by
    exact hQodd.of_dvd_nat (Subgroup.card_dvd_of_surjective φ.rangeRestrict_surjective)
  have hsolvA : Group.IsSolvable A := by
    let : Group.IsSolvable Q := hsolvQ
    exact Group.isSolvable_of_surjective (f := φA) φ.rangeRestrict_surjective
  have hAder_p : IsPGroup p (derivedSubgroup A) := by
    let : Fact (IsPGroup p R) := ⟨hR_p⟩
    exact theorem_4_17 (R := R) (A := A) (p := p) hpodd hsolvA hR_rank hAodd
  have hmap_der : DQ.map φA = derivedSubgroup A := by
    simpa [DQ, derivedSubgroup, derivedSeries_one] using
      (map_derivedSeries_eq (f := φA) φ.rangeRestrict_surjective 1)
  let ψ : DQ →* derivedSubgroup A :=
    (φA.comp DQ.subtype).codRestrict (derivedSubgroup A) (by
      intro x
      rw [← hmap_der]
      exact Subgroup.mem_map_of_mem φA x.property)
  have hψker_le_R : ψ.ker ≤ R.subgroupOf DQ := by
    intro x hx
    have hx1 : ψ x = 1 := (MonoidHom.mem_ker).mp hx
    have hx1φ : φ (x : Q) = 1 := by
      change ((((ψ x : derivedSubgroup A) : A) : MulAut R) = 1)
      simpa [ψ, φA] using congrArg Subtype.val (congrArg Subtype.val hx1)
    have hxcent : (x : Q) ∈ Subgroup.centralizer (R : Set Q) := by
      rw [← hφker_eq_cent, MonoidHom.mem_ker]
      exact hx1φ
    have hxR : (x : Q) ∈ R := hcentR hxcent
    simpa [Subgroup.mem_subgroupOf] using hxR
  have hDQsub_ker_p : IsPGroup p DQ.subtype.ker :=
    IsPGroup.ker_isPGroup_of_injective (p := p) (ϕ := DQ.subtype) DQ.subtype_injective
  have hRsub_p : IsPGroup p (R.subgroupOf DQ) := by
    have hRsub_p' := hR_p.comap_of_ker_isPGroup DQ.subtype hDQsub_ker_p
    rw [Subgroup.comap_subtype] at hRsub_p'
    exact hRsub_p'
  have hψker_p : IsPGroup p ψ.ker := hRsub_p.to_le hψker_le_R
  have hDQ_p : IsPGroup p DQ := by
    have htop_p : IsPGroup p (⊤ : Subgroup (derivedSubgroup A)) := by
      simpa using hAder_p.to_subgroup (⊤ : Subgroup (derivedSubgroup A))
    have htopDQ_p : IsPGroup p (⊤ : Subgroup DQ) := by
      have htop_comap : Subgroup.comap ψ (⊤ : Subgroup (derivedSubgroup A)) = ⊤ := by
        ext x
        constructor
        · intro _
          exact Subgroup.mem_top x
        · intro _
          exact Subgroup.mem_top (ψ x)
      have htopDQ_p' := htop_p.comap_of_ker_isPGroup ψ hψker_p
      rw [htop_comap] at htopDQ_p'
      exact htopDQ_p'
    exact htopDQ_p.of_equiv Subgroup.topEquiv
  let Dbar : Subgroup Q := D.map q
  have hDbar_eq_DQ : Dbar = DQ := by
    simpa [D, Dbar, DQ, derivedSubgroup, derivedSeries_one] using
      (map_derivedSeries_eq (f := q) (QuotientGroup.mk'_surjective M) 1)
  let qD : D →* DQ :=
    (q.comp D.subtype).codRestrict DQ (by
      intro x
      rw [← hDbar_eq_DQ]
      exact Subgroup.mem_map_of_mem q x.property)
  have hqD_surj : Function.Surjective qD := by
    intro y
    have hy : (y : Q) ∈ Dbar := by
      simp [hDbar_eq_DQ]
    rcases hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    simpa [qD] using hxy
  have hkerMap_le_M : qD.ker.map D.subtype ≤ M := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hy1 : qD y = 1 := by simpa [MonoidHom.mem_ker] using hy
    have hyq : q (y : G) = 1 := by
      simpa [qD] using congrArg Subtype.val hy1
    exact (QuotientGroup.eq_one_iff (N := M) (x := (y : G))).1 hyq
  have hker_card_dvd : Nat.card qD.ker ∣ Nat.card M := by
    have hmap_dvd : Nat.card (qD.ker.map D.subtype) ∣ Nat.card M :=
      Subgroup.card_dvd_of_le hkerMap_le_M
    have hcard_eq : Nat.card (qD.ker.map D.subtype) = Nat.card qD.ker :=
      Subgroup.card_map_of_injective (K := qD.ker) (f := D.subtype) D.subtype_injective
    rw [hcard_eq] at hmap_dvd
    exact hmap_dvd
  have hkerCop : Nat.Coprime p (Nat.card qD.ker) := by
    exact Nat.Coprime.of_dvd_right hker_card_dvd (pPrimeCore_coprime_card (G := G) (p := p))
  have hDQ_comp : HasNormalPComplement p DQ := by
    refine ⟨⊥, inferInstance, by simp, ?_⟩
    exact hDQ_p.of_equiv (QuotientGroup.quotientBot (G := DQ)).symm
  exact hasNormalPComplement_of_surjective (G := D) (G' := DQ) (p := p) qD hqD_surj hkerCop hDQ_comp

end Main
