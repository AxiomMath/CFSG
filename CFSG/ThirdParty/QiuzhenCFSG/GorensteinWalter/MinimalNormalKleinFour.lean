module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965
public import Mathlib.GroupTheory.SchurZassenhaus

namespace CFSG
end CFSG
open CFSG

/-!
# Minimal normal Klein four subgroups

This module isolates the Klein-four branch of Proposition 9 in the
Gorenstein--Walter minimal-counterexample argument.  The first step shows that
a normal Klein four subgroup is self-centralizing; the minimal-normal
hypothesis will enter when constructing the complement used by the faithful
four-point action.
-/

universe u

namespace CFSG.GorensteinWalter

noncomputable section

/-- A normal Klein four subgroup of a Gorenstein--Walter minimal counterexample
is self-centralizing.

The normal-complement and odd-core results make its centralizer a `2`-group.
After placing that centralizer in a Sylow `2`-subgroup, the dihedral
centralizer bound forces every centralizing element back into the Klein four
subgroup. -/
public theorem centralizer_eq_of_minimalNormal_kleinFour
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal) (hH : IsKleinFour H) :
    Subgroup.centralizer (H : Set G) = H := by
  let : IsKleinFour H := hH
  let : IsMulCommutative H := IsKleinFour.isMulCommutative
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  have hNPC : Glauberman.NormalPComplement 2 (↥C) := by
    apply gw_prop9_centralizer_dihedral_normalTwoComplement hmin H hHnormal
    refine ⟨1, by omega, ?_⟩
    simpa using (IsKleinFour.nonempty_mulEquiv (G₁ := H) (G₂ := DihedralGroup 2))
  have hCO : oddCoreOf C = ⊥ := by
    simpa [C] using gw_prop9_centralizer_oddCore_trivial hmin H hHnormal
  have hCcore : pPrimeCore 2 (↥C) = ⊥ := by
    unfold oddCoreOf at hCO
    exact (Subgroup.map_eq_bot_iff_of_injective
      (pPrimeCore 2 (↥C)) C.subtype_injective).mp hCO
  have hCtwo : IsPGroup 2 (↥C) :=
    isPGroup_of_normalPComplement_of_pPrimeCore_eq_bot hNPC hCcore
  obtain ⟨S, hCleS⟩ := IsPGroup.exists_le_sylow hCtwo
  have hHleC : H ≤ C := by
    simpa [C] using (Subgroup.le_centralizer H)
  have hHleS : H ≤ (S : Subgroup G) := hHleC.trans hCleS
  let D : Subgroup S := H.subgroupOf (S : Subgroup G)
  have hDnormal : D.Normal := by
    apply (Subgroup.normal_subgroupOf_iff hHleS).2
    intro h k hh hk
    exact hHnormal.conj_mem h hh (k : G)
  have hDnc : ¬ IsCyclic D := by
    intro hDcyc
    apply IsKleinFour.not_isCyclic (G := H)
    exact (Subgroup.subgroupOfEquivOfLe hHleS).isCyclic.mp hDcyc
  rcases hmin.1 S with ⟨m, hm, ⟨eS⟩⟩
  have hDcent : Subgroup.centralizer (D : Set S) ≤ D :=
    centralizer_le_of_normal_dihedral_of_mulEquiv hm eS D hDnormal hDnc
  apply le_antisymm
  · intro x hx
    have hxS : x ∈ (S : Subgroup G) := hCleS hx
    let xs : S := ⟨x, hxS⟩
    have hxsC : xs ∈ Subgroup.centralizer (D : Set S) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hdH : (d : G) ∈ H := hd
      have hcomm : (d : G) * x = x * (d : G) :=
        (Subgroup.mem_centralizer_iff.mp hx) (d : G) hdH
      exact Subtype.ext hcomm
    exact hDcent hxsC
  · exact hHleC

/-- If `H` is a minimal normal Klein four subgroup of a
Gorenstein--Walter minimal counterexample, then `G/H` has order `3` or `6`.

The self-centralizer theorem embeds the quotient in `Aut(H) ≃ S₃`.  If its
order were prime to `3`, then `G` would be a `2`-group.  Conjugation on the
three nonidentity elements of `H` would then have a fixed point, whose cyclic
subgroup would be a forbidden proper nontrivial normal subgroup of `H`. -/
public theorem quotient_card_eq_three_or_six_of_minimalNormal_kleinFour
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal)
    (hHmin : ∀ M : Subgroup G, M.Normal → M ≤ H → M = ⊥ ∨ M = H)
    (hH : IsKleinFour H) :
    Nat.card (G ⧸ H) = 3 ∨ Nat.card (G ⧸ H) = 6 := by
  let : H.Normal := hHnormal
  let : IsKleinFour H := hH
  have hC : Subgroup.centralizer (H : Set G) = H :=
    centralizer_eq_of_minimalNormal_kleinFour hmin H hHnormal hH
  rcases quotient_centralizer_mulAut_embedding H with ⟨φ, hφ⟩
  let eQ : (G ⧸ H) ≃* (G ⧸ Subgroup.centralizer (H : Set G)) :=
    QuotientGroup.quotientMulEquivOfEq hC.symm
  let φH : (G ⧸ H) →* MulAut H := φ.comp eQ.toMonoidHom
  have hφH : Function.Injective φH := hφ.comp eQ.injective
  rcases gw_prop9_aut_kleinFour_is_S3 hH with ⟨eAut⟩
  let ψ : (G ⧸ H) →* Equiv.Perm (Fin 3) := eAut.toMonoidHom.comp φH
  have hψ : Function.Injective ψ := eAut.injective.comp hφH
  have hqdvd : Nat.card (G ⧸ H) ∣ 6 := by
    have hdvd := Subgroup.card_dvd_of_injective ψ hψ
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using hdvd
  have h3dvd : 3 ∣ Nat.card (G ⧸ H) := by
    by_contra h3
    have hqpos : 0 < Nat.card (G ⧸ H) := Nat.card_pos
    have hqle : Nat.card (G ⧸ H) ≤ 6 := Nat.le_of_dvd (by norm_num) hqdvd
    have hq12 : Nat.card (G ⧸ H) = 1 ∨ Nat.card (G ⧸ H) = 2 := by
      have hq3 : Nat.card (G ⧸ H) ≠ 3 := by
        intro hq
        apply h3
        simp [hq]
      have hq4 : Nat.card (G ⧸ H) ≠ 4 := by
        intro hq
        norm_num [hq] at hqdvd
      have hq5 : Nat.card (G ⧸ H) ≠ 5 := by
        intro hq
        norm_num [hq] at hqdvd
      have hq6 : Nat.card (G ⧸ H) ≠ 6 := by
        intro hq
        apply h3
        simp [hq]
      omega
    have hQtwo : IsPGroup 2 (G ⧸ H) := by
      rcases hq12 with hq1 | hq2
      · exact IsPGroup.of_card (n := 0) (by simp [hq1])
      · exact IsPGroup.of_card (n := 1) (by simp [hq2])
    have hHtwo : IsPGroup 2 H :=
      IsPGroup.of_card (n := 2) (by simp)
    have hGtwo : IsPGroup 2 G :=
      isPGroup_of_normal_subgroup_of_quotient H hHtwo hQtwo
    let : MulDistribMulAction G H :=
      MulDistribMulAction.compHom H (MulAut.conjNormal (H := H))
    let T : SubMulAction G H :=
      { carrier := {x | x ≠ (1 : H)}
        smul_mem' := by
          intro g x hx
          change MulAut.conjNormal g x ≠ (1 : H)
          exact (MulEquiv.map_ne_one_iff (MulAut.conjNormal g)).2 hx }
    have hTcard : Nat.card T = 3 := by
      dsimp [T]
      have hcardT : Nat.card (SubMulAction.ofStabilizer H (1 : H)) + 1 = Nat.card H :=
        SubMulAction.nat_card_ofStabilizer_add_one_eq H (1 : H)
      change Nat.card {x : H // x ≠ (1 : H)} + 1 = Nat.card H at hcardT
      have hsub := Nat.eq_sub_of_add_eq hcardT
      change Nat.card {x : H // x ≠ (1 : H)} = 3
      simpa using hsub
    have h2ndvdT : ¬ 2 ∣ Nat.card T := by
      rw [hTcard]
      norm_num
    rcases hGtwo.nonempty_fixed_point_of_prime_not_dvd_card T h2ndvdT with ⟨t, ht⟩
    let tG : G := t.1
    let M : Subgroup G := Subgroup.zpowers tG
    have htGne : tG ≠ 1 := by
      intro ht1
      apply t.2
      exact Subtype.ext ht1
    have hMne : M ≠ ⊥ := by
      simpa [M, tG, Subgroup.zpowers_eq_bot] using htGne
    have hMle : M ≤ H := by
      apply Subgroup.zpowers_le.mpr
      exact t.1.2
    have hMnormal : M.Normal := by
      rw [Subgroup.normal_iff_map_conj_eq]
      intro g
      dsimp [M]
      rw [MonoidHom.map_zpowers]
      congr 1
      have hfixT : g • t = t := ht g
      have hfixH : MulAut.conjNormal g t.1 = t.1 :=
        congrArg Subtype.val hfixT
      exact congrArg Subtype.val hfixH
    have hMneH : M ≠ H := by
      intro hMH
      apply IsKleinFour.not_isCyclic (G := H)
      rw [← hMH]
      infer_instance
    rcases hHmin M hMnormal hMle with hMbot | hMH
    · exact hMne hMbot
    · exact hMneH hMH
  have hqpos : 0 < Nat.card (G ⧸ H) := Nat.card_pos
  have hqle : Nat.card (G ⧸ H) ≤ 6 := Nat.le_of_dvd (by norm_num) hqdvd
  have hq1 : Nat.card (G ⧸ H) ≠ 1 := by
    intro hq
    norm_num [hq] at h3dvd
  have hq2 : Nat.card (G ⧸ H) ≠ 2 := by
    intro hq
    norm_num [hq] at h3dvd
  have hq4 : Nat.card (G ⧸ H) ≠ 4 := by
    intro hq
    norm_num [hq] at hqdvd
  have hq5 : Nat.card (G ⧸ H) ≠ 5 := by
    intro hq
    norm_num [hq] at hqdvd
  omega

/-- A minimal normal Klein four subgroup of a Gorenstein--Walter minimal
counterexample has a complement.

When `|G/H| = 3`, this is Schur--Zassenhaus.  When `|G/H| = 6`, pull back
`A₃ ⊴ S₃` to a normal subgroup `A` of index two, split `A = H ⋊ P`, and set
`K = N_G(P)`.  Frattini's argument gives `G = HK`.  The intersection
`H ∩ K` is normal in `G`; minimal normality and self-centrality force it to
be trivial. -/
public theorem exists_complement_of_minimalNormal_kleinFour
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal)
    (hHmin : ∀ M : Subgroup G, M.Normal → M ≤ H → M = ⊥ ∨ M = H)
    (hH : IsKleinFour H) :
    ∃ K : Subgroup G, H.IsComplement' K := by
  let : H.Normal := hHnormal
  let : IsKleinFour H := hH
  rcases quotient_card_eq_three_or_six_of_minimalNormal_kleinFour
      hmin H hHnormal hHmin hH with hq3 | hq6
  · have hHindex : H.index = 3 := by
      simpa [Subgroup.index_eq_card] using hq3
    have hcop : Nat.Coprime (Nat.card H) H.index := by
      rw [hH.card_four, hHindex]
      norm_num
    exact Subgroup.exists_right_complement'_of_coprime hcop
  · have hC : Subgroup.centralizer (H : Set G) = H :=
      centralizer_eq_of_minimalNormal_kleinFour hmin H hHnormal hH
    rcases quotient_centralizer_mulAut_embedding H with ⟨φ, hφ⟩
    let eQ : (G ⧸ H) ≃* (G ⧸ Subgroup.centralizer (H : Set G)) :=
      QuotientGroup.quotientMulEquivOfEq hC.symm
    let φH : (G ⧸ H) →* MulAut H := φ.comp eQ.toMonoidHom
    have hφH : Function.Injective φH := hφ.comp eQ.injective
    rcases gw_prop9_aut_kleinFour_is_S3 hH with ⟨eAut⟩
    let ψ : (G ⧸ H) →* Equiv.Perm (Fin 3) := eAut.toMonoidHom.comp φH
    have hψ : Function.Injective ψ := eAut.injective.comp hφH
    have hcardψ : Nat.card (G ⧸ H) = Nat.card (Equiv.Perm (Fin 3)) := by
      rw [hq6]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    have hψbij : Function.Bijective ψ :=
      (Nat.bijective_iff_injective_and_card ψ).2 ⟨hψ, hcardψ⟩
    let eS3 : (G ⧸ H) ≃* Equiv.Perm (Fin 3) := MulEquiv.ofBijective ψ hψbij
    let Abar : Subgroup (G ⧸ H) := eS3.symm.mapSubgroup (alternatingGroup (Fin 3))
    have hAbarNormal : Abar.Normal := by
      exact (eS3.symm.normal_map_iff).2 inferInstance
    let : Abar.Normal := hAbarNormal
    have hAbarCard : Nat.card Abar = 3 := by
      calc
        Nat.card Abar = Nat.card (alternatingGroup (Fin 3)) := by
          exact Subgroup.card_map_of_injective eS3.symm.injective
        _ = 3 := by
          rw [nat_card_alternatingGroup]
          norm_num [Nat.factorial]
    have hAbarIndex : Abar.index = 2 := by
      have hmul := Abar.card_mul_index
      rw [hAbarCard, hq6] at hmul
      omega
    let q : G →* G ⧸ H := QuotientGroup.mk' H
    let A : Subgroup G := Abar.comap q
    have hAnormal : A.Normal := hAbarNormal.comap q
    let : A.Normal := hAnormal
    have hHleA : H ≤ A := by
      intro h hh
      change q h ∈ Abar
      have hker : h ∈ q.ker := by
        simpa [q] using hh
      rw [MonoidHom.mem_ker] at hker
      rw [hker]
      exact Abar.one_mem
    have hAindex : A.index = 2 := by
      calc
        A.index = Abar.index := by
          exact Abar.index_comap_of_surjective (QuotientGroup.mk'_surjective H)
        _ = 2 := hAbarIndex
    have hHindex : H.index = 6 := by
      simpa [Subgroup.index_eq_card] using hq6
    have hHArelIndex : H.relIndex A = 3 := by
      have hmul := Subgroup.relIndex_mul_index hHleA
      rw [hAindex, hHindex] at hmul
      omega
    let HA : Subgroup A := H.subgroupOf A
    have hHAnormal : HA.Normal := by
      apply (Subgroup.normal_subgroupOf_iff hHleA).2
      intro h k hh hk
      exact hHnormal.conj_mem h hh (k : G)
    let : HA.Normal := hHAnormal
    have hHAcard : Nat.card HA = 4 := by
      calc
        Nat.card HA = Nat.card H :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleA).toEquiv
        _ = 4 := hH.card_four
    have hHAindex : HA.index = 3 := by
      simpa [HA, Subgroup.relIndex] using hHArelIndex
    have hHAcop : Nat.Coprime (Nat.card HA) HA.index := by
      rw [hHAcard, hHAindex]
      norm_num
    rcases Subgroup.exists_right_complement'_of_coprime hHAcop with ⟨P, hcompA⟩
    have hPindex : P.index = 4 := by
      simpa [hHAcard] using hcompA.index_eq_card
    have hAcard : Nat.card A = 12 := by
      have hmul := HA.card_mul_index
      rw [hHAcard, hHAindex] at hmul
      omega
    have hPcard : Nat.card P = 3 := by
      have hmul := hcompA.card_mul
      rw [hHAcard, hAcard] at hmul
      omega
    have hPthree : IsPGroup 3 P :=
      IsPGroup.of_card (n := 1) (by simp [hPcard])
    let P3 : Sylow 3 A := hPthree.toSylow (by rw [hPindex]; norm_num)
    have hP3coe : (P3 : Subgroup A) = P := by
      simp [P3]
    let Pmap : Subgroup G := P.map A.subtype
    let K : Subgroup G := Subgroup.normalizer (Pmap : Set G)
    have hFrattini : K ⊔ A = ⊤ := by
      simpa [K, Pmap, hP3coe] using P3.normalizer_sup_eq_top
    have hHAmap : HA.map A.subtype = H := by
      simpa [HA] using Subgroup.map_subgroupOf_eq_of_le hHleA
    have hHPdis : Disjoint H Pmap := by
      have hmap := Subgroup.disjoint_map A.subtype_injective hcompA.disjoint
      simpa [hHAmap, Pmap] using hmap
    have hPmapleK : Pmap ≤ K := Subgroup.le_normalizer
    have hHKtop : H ⊔ K = ⊤ := by
      apply top_unique
      rw [← hFrattini]
      apply sup_le
      · exact le_sup_right
      · intro a ha
        let aa : A := ⟨a, ha⟩
        rcases hcompA.2 aa with ⟨⟨h, p⟩, hp⟩
        have hha : (h : G) ∈ H := h.2
        have hpa : (p : G) ∈ Pmap :=
          Subgroup.mem_map_of_mem A.subtype p.2
        have heq : (h : G) * (p : G) = a := congrArg Subtype.val hp
        rw [← heq]
        exact (H ⊔ K).mul_mem
          ((le_sup_left : H ≤ H ⊔ K) hha)
          ((le_sup_right : K ≤ H ⊔ K) (hPmapleK hpa))
    let D : Subgroup G := H ⊓ K
    have hHnormD : H ≤ Subgroup.normalizer (D : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro h hh d hd
      have hcomm : h * d = d * h := by
        let : IsMulCommutative H := IsKleinFour.isMulCommutative
        exact congrArg Subtype.val (mul_comm' (⟨h, hh⟩ : H) ⟨d, hd.1⟩)
      have heq : h * d * h⁻¹ = d := by
        rw [hcomm]
        simp
      simpa [D, heq] using hd
    have hKnormD : K ≤ Subgroup.normalizer (D : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro k hk d hd
      exact ⟨hHnormal.conj_mem d hd.1 k,
        K.mul_mem (K.mul_mem hk hd.2) (K.inv_mem hk)⟩
    have hDnormal : D.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      apply top_unique
      rw [← hHKtop]
      exact sup_le hHnormD hKnormD
    have hDneH : D ≠ H := by
      intro hDH
      have hHleK : H ≤ K := by
        rw [← hDH]
        exact inf_le_right
      have hPcent : Pmap ≤ Subgroup.centralizer (H : Set G) := by
        intro p hp
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have hhK : h ∈ K := hHleK hh
        have hconjP : h * p * h⁻¹ ∈ Pmap :=
          (Subgroup.mem_normalizer_iff.mp hhK p).1 hp
        let c : G := h * p * h⁻¹ * p⁻¹
        have hcP : c ∈ Pmap := Pmap.mul_mem hconjP (Pmap.inv_mem hp)
        have hcH : c ∈ H := by
          have hpinv : p * h⁻¹ * p⁻¹ ∈ H :=
            hHnormal.conj_mem h⁻¹ (H.inv_mem hh) p
          change h * p * h⁻¹ * p⁻¹ ∈ H
          simpa only [mul_assoc] using H.mul_mem hh hpinv
        have hcbot : c ∈ (⊥ : Subgroup G) :=
          (disjoint_iff_inf_le.mp hHPdis) ⟨hcH, hcP⟩
        have hc1 : c = 1 := hcbot
        dsimp [c] at hc1
        calc
          h * p = (h * p * h⁻¹ * p⁻¹) * (p * h) := by group
          _ = p * h := by rw [hc1, one_mul]
      rw [hC] at hPcent
      have hPbot : Pmap = ⊥ := by
        apply le_bot_iff.mp
        intro p hp
        exact (disjoint_iff_inf_le.mp hHPdis) ⟨hPcent hp, hp⟩
      have hPmapCard : Nat.card Pmap = 3 := by
        calc
          Nat.card Pmap = Nat.card P :=
            Subgroup.card_map_of_injective A.subtype_injective
          _ = 3 := hPcard
      rw [hPbot] at hPmapCard
      norm_num at hPmapCard
    have hDleH : D ≤ H := inf_le_left
    have hDbot : D = ⊥ := by
      rcases hHmin D hDnormal hDleH with h | h
      · exact h
      · exact (hDneH h).elim
    have hHKdis : Disjoint H K := by
      rw [disjoint_iff_inf_le]
      simp [D, hDbot]
    refine ⟨K, Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hHKdis ?_⟩
    rw [← Subgroup.normal_mul H K, hHKtop]
    rfl

/-- Proposition 9, Klein-four branch: a minimal normal Klein four subgroup of
the minimal counterexample yields a faithful permutation representation on
four points. -/
public theorem minimalNormal_kleinFour_embeds_S4
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal) (_hHne : H ≠ ⊥)
    (hHmin : ∀ M : Subgroup G, M.Normal → M ≤ H → M = ⊥ ∨ M = H)
    (hH : IsKleinFour H) :
    ∃ φ : G →* Equiv.Perm (Fin 4), Function.Injective φ := by
  obtain ⟨K, hcomp⟩ :=
    exists_complement_of_minimalNormal_kleinFour hmin H hHnormal hHmin hH
  exact faithful_four_point_action_of_selfCentralizing_split_normal_kleinFour
    H K hHnormal hH hcomp
    (centralizer_eq_of_minimalNormal_kleinFour hmin H hHnormal hH)

end

end CFSG.GorensteinWalter
