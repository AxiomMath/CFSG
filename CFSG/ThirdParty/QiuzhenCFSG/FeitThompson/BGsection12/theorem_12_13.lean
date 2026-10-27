module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.theorem_12_12_b

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# theorem_12_13
-/

section Section12

variable {G : Type*} [Group G]

private theorem CFSG.section12_nonabelian_pSubgroup_not_isCyclic
    {P : Subgroup G} {p : Nat.Primes}
    (_hPp : IsPGroup p.val P) (hPnonab : ¬ IsMulCommutative P) :
    ¬ IsCyclic P := by
  intro hPcyc
  let : IsCyclic P := hPcyc
  exact hPnonab inferInstance

private theorem CFSG.section12_not_singleton_normalizer_of_subgroupNormalizerIn_le
    {M Mstar Z : Subgroup G}
    (hMstar : Mstar ∈ section9MaximalSubgroups G) (hMstar_ne : Mstar ≠ M)
    (hNZ_le_Mstar : subgroupNormalizerIn M (Z : Set G) ≤ Mstar) :
    section9MaximalSubgroupsContaining (Subgroup.normalizer (Z : Set G)) ≠ {M} := by
  classical
  intro huniq
  have hMmem :
      M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Z : Set G)) := by
    rw [huniq]
    simp
  have hNorm_le_M : Subgroup.normalizer (Z : Set G) ≤ M := hMmem.2
  have hNorm_le_local :
      Subgroup.normalizer (Z : Set G) ≤ subgroupNormalizerIn M (Z : Set G) := by
    intro g hg
    exact mem_subgroupNormalizerIn.mpr ⟨hg, hNorm_le_M hg⟩
  have hMstar_mem :
      Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Z : Set G)) :=
    ⟨hMstar, hNorm_le_local.trans hNZ_le_Mstar⟩
  have hMstar_eq_M : Mstar = M := by
    simpa [huniq] using hMstar_mem
  exact hMstar_ne hMstar_eq_M

section Finite

variable [Finite G]

private theorem CFSG.section12_rankTwo_sup_of_distinct_primeOrder_commuting
    {M Z X : Subgroup G} {p : Nat.Primes}
    (hZM : Z ≤ M) (hXM : X ≤ M)
    (hZcard : Nat.card Z = p.val) (hXcard : Nat.card X = p.val)
    (hZelem : IsElementaryAbelian p.val Z)
    (hXelem : IsElementaryAbelian p.val X)
    (hXcentZ : X ≤ Subgroup.centralizer (Z : Set G))
    (hZX : Z ≠ X) :
    Z ⊔ X ∈ section12RankTwoElementaryAbelianIn p M := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let : IsElementaryAbelian p.val Z := hZelem
  let : IsElementaryAbelian p.val X := hXelem
  have hdisj : Disjoint Z X := by
    rw [Subgroup.disjoint_def]
    intro z hzZ hzX
    by_contra hz_ne
    have hZsubX_top : Z.subgroupOf X = ⊤ := by
      have : Fact (Nat.card X).Prime := ⟨by simpa [hXcard] using p.property⟩
      have hsub_ne_bot : Z.subgroupOf X ≠ ⊥ := by
        intro hbot
        have hzsub : (⟨z, hzX⟩ : X) ∈ Z.subgroupOf X := hzZ
        have hzbot : (⟨z, hzX⟩ : X) ∈ (⊥ : Subgroup X) := by
          simpa [hbot] using hzsub
        exact hz_ne (by simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hzbot))
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card (Z.subgroupOf X) with hbot | htop
      · exact False.elim (hsub_ne_bot hbot)
      · exact htop
    have hXleZ : X ≤ Z := by
      intro y hy
      have hy_top : (⟨y, hy⟩ : X) ∈ (⊤ : Subgroup X) := by simp
      exact Subgroup.mem_subgroupOf.mp
        (by simpa [← hZsubX_top] using hy_top)
    have hZXcard : Nat.card Z ≤ Nat.card X := by
      rw [hZcard, hXcard]
    have hXZ : X = Z := Subgroup.eq_of_le_of_card_ge hXleZ hZXcard
    exact hZX hXZ.symm
  have hsupElem : IsElementaryAbelian p.val (Z ⊔ X : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer
      (G := G) (p := p.val) (E := Z) (C := X) hXcentZ
  let : IsElementaryAbelian p.val (Z ⊔ X : Subgroup G) := hsupElem
  have hcommSup : IsMulCommutative (Z ⊔ X : Subgroup G) := inferInstance
  have hZ_norm : (Z.subgroupOf (Z ⊔ X : Subgroup G)).Normal := by
    let : IsMulCommutative (Z ⊔ X : Subgroup G) := hcommSup
    let : CommGroup (Z ⊔ X : Subgroup G) := IsMulCommutative.instCommGroup
    infer_instance
  have hcomp :
      (Z.subgroupOf (Z ⊔ X : Subgroup G)).IsComplement'
        (X.subgroupOf (Z ⊔ X : Subgroup G)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro z hzZ hzX
      apply Subtype.ext
      exact Subgroup.disjoint_def.mp hdisj hzZ hzX
    · rw [Set.eq_univ_iff_forall]
      intro z
      let ZD : Subgroup (Z ⊔ X : Subgroup G) := Z.subgroupOf (Z ⊔ X : Subgroup G)
      let XD : Subgroup (Z ⊔ X : Subgroup G) := X.subgroupOf (Z ⊔ X : Subgroup G)
      have : ZD.Normal := by simpa [ZD] using hZ_norm
      have hsup_top : ZD ⊔ XD = ⊤ := by
        simpa [ZD, XD] using
          (Subgroup.subgroupOf_sup (A := Z) (A' := X) (B := Z ⊔ X)
            le_sup_left le_sup_right).symm
      have hz : z ∈ ZD ⊔ XD := by simp [hsup_top]
      rcases (Subgroup.mem_sup_of_normal_left
          (x := z) (s := ZD) (t := XD)).1 hz with
        ⟨z0, hz0, x0, hx0, hz0x0⟩
      exact ⟨z0, hz0, x0, hx0, hz0x0⟩
  have hsup_card : Nat.card (Z ⊔ X : Subgroup G) = p.val ^ 2 := by
    have hmul := hcomp.card_mul_card
    rw [section12_card_subgroupOf_eq (H := Z) (K := Z ⊔ X) le_sup_left,
      section12_card_subgroupOf_eq (H := X) (K := Z ⊔ X) le_sup_right,
      hZcard, hXcard] at hmul
    simpa [pow_two] using hmul.symm
  exact ⟨sup_le hZM hXM, hsup_card, hsupElem⟩

section MinCE

variable [IsMinCE G]

private theorem CFSG.section12_malpha_centralizer_omegaOneCenter_le_mstar_of_shape
    {M Mstar S : Subgroup G} {Q Y : Subgroup S} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hpα : p ∉ section10AlphaPrimes M)
    (hSleM : S ≤ M) (hSleMstar : S ≤ Mstar)
    (hQcard : Nat.card Q = p.val ^ 3)
    (hQnoncomm : ¬ IsMulCommutative Q)
    (hQexp : Monoid.exponent Q = p.val)
    (hYcyc : IsCyclic Y)
    (hcentral : IsCentralProduct Q Y)
    (hΩeq :
      (Ω₁Z p.val Y).map Y.subtype = (Subgroup.center Q).map Q.subtype) :
    subgroupCentralizerIn (section10Malpha M) (section10OmegaOneCenter p S) ≤ Mstar := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let Z : Subgroup G := section10OmegaOneCenter p S
  have hZeq :
      Z = ((Subgroup.center Q).map Q.subtype).map S.subtype := by
    simpa [Z] using
      section10_omegaOneCenter_eq_center_map_of_centralProduct
        (G := G) (P := S) (Q := Q) (Y := Y) (p := p)
        hQcard hQnoncomm hQexp hYcyc hcentral hΩeq
  let K : Subgroup G := subgroupCentralizerIn (section10Malpha M) Z
  have hQp : IsPGroup p.val Q := IsPGroup.of_card (n := 3) hQcard
  let : Fact (IsPGroup p.val Q) := ⟨hQp⟩
  have hQextra : IsExtraspecial p.val Q :=
    isExtraspecial_of_noncommutative_card_p3_exponent_p
      (K := Q) (p := p.val) hQcard hQexp hQnoncomm
  let : IsExtraspecial p.val Q := hQextra
  let ZQ : Subgroup Q := Subgroup.center Q
  have hZQ_normal : ZQ.Normal := by
    dsimp [ZQ]
    infer_instance
  have hZcard : Nat.card Z = p.val := by
    calc
      Nat.card Z =
          Nat.card (((Subgroup.center Q).map Q.subtype).map S.subtype) := by
            rw [hZeq]
      _ = Nat.card ((Subgroup.center Q).map Q.subtype) := by
            exact Subgroup.card_map_of_injective
              (K := (Subgroup.center Q).map Q.subtype) (f := S.subtype)
              S.subtype_injective
      _ = Nat.card (Subgroup.center Q) := by
            exact Subgroup.card_map_of_injective
              (K := Subgroup.center Q) (f := Q.subtype) Q.subtype_injective
      _ = p.val := IsExtraspecial.center_order_p p.val Q
  have hZelem : IsElementaryAbelian p.val Z := by
    simpa [Z] using section10OmegaOneCenter_isElementaryAbelian (G := G) (p := p) S
  have hK_le_malpha : K ≤ section10Malpha M := inf_le_left
  have hKp' : IsPiSubgroup (G := G) (section10PPrimeSet p) K := by
    intro q hqK
    rw [section10PPrimeSet, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hq_eq_p
    have hqα : q ∈ section10AlphaPrimes M :=
      (theorem_10_2_a (G := G) hM).1.p_in_pi_of_p_dvd_card q
        (hqK.trans (Subgroup.card_dvd_of_le hK_le_malpha))
    exact hpα (by simpa [hq_eq_p] using hqα)
  have hKcop : Nat.Coprime p.val (Nat.card K) := by
    refine Nat.coprime_of_dvd ?_
    intro q hqPrime hqp hqK
    have hq_eq_p : q = p.val := ((p.2.dvd_iff_eq hqPrime.ne_one).1 hqp).symm
    let q' : Nat.Primes := ⟨q, hqPrime⟩
    have hq'_not_p : q' ∉ ({p} : Set Nat.Primes) := by
      simpa [section10PPrimeSet] using hKp' q' hqK
    have hq'_eq_p : q' = p := Subtype.ext hq_eq_p
    exact hq'_not_p (by simp [hq'_eq_p])
  have hQ_le_normK :
      Q ≤ Subgroup.comap S.subtype (Subgroup.normalizer (K : Set G)) := by
    intro q hqQ
    rw [Subgroup.mem_comap]
    let qQ : Q := ⟨q, hqQ⟩
    have hq_norm_malpha :
        (q : G) ∈ Subgroup.normalizer (section10Malpha M : Set G) :=
      section10_le_normalizer_malpha_of_le
        (G := G) (M := M) (X := S) hSleM q.property
    have hq_cent_Z : (q : G) ∈ Subgroup.centralizer (Z : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [hZeq] at hz
      rcases Subgroup.mem_map.mp hz with ⟨zS, hzS, rfl⟩
      rcases Subgroup.mem_map.mp hzS with ⟨zQ, hzQ, hzQ_eq⟩
      have hcommQ : zQ * qQ = qQ * zQ :=
        (Subgroup.mem_center_iff.mp hzQ qQ).symm
      apply congrArg (fun u : Q => ((u : S) : G)) at hcommQ
      simpa [← hzQ_eq] using hcommQ
    have hq_norm_Z : (q : G) ∈ Subgroup.normalizer (Z : Set G) :=
      centralizer_le_normalizer Z hq_cent_Z
    have hq_norm_centZ :
        (q : G) ∈
          Subgroup.normalizer (Subgroup.centralizer (Z : Set G) : Set G) :=
      section12_normalizer_le_normalizer_centralizer (G := G) Z hq_norm_Z
    change (q : G) ∈ Subgroup.normalizer (K : Set G)
    simpa [K, subgroupCentralizerIn] using
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hq_norm_malpha, hq_norm_centZ⟩
  let qNorm : Q →* Subgroup.normalizer (K : Set G) :=
    { toFun := fun q => ⟨((q : S) : G), hQ_le_normK q.property⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        rfl }
  have : Subgroup.Normalizes (Subgroup.normalizer (K : Set G)) K := ⟨le_rfl⟩
  let : MulDistribMulAction Q K := MulDistribMulAction.compHom K qNorm
  have hZQ_fix_all : ZQ ≤ actionCentralizerIn (A := Q) (G := K) (⊤ : Subgroup Q) := by
    intro z hz
    rw [actionCentralizerIn]
    constructor
    · simp
    · change z ∈ fixingSubgroupOf Q K Set.univ
      rw [mem_fixingSubgroup_iff]
      intro k _
      apply Subtype.ext
      change (((z : Q) : S) : G) * (k : G) * (((z : Q) : S) : G)⁻¹ = (k : G)
      have hzZ : (((z : Q) : S) : G) ∈ Z := by
        rw [hZeq]
        exact Subgroup.mem_map.mpr
          ⟨(z : S), Subgroup.mem_map.mpr ⟨(z : Q), hz, rfl⟩, rfl⟩
      have hk_cent : (k : G) ∈ Subgroup.centralizer (Z : Set G) := k.property.2
      have hcomm := (Subgroup.mem_centralizer_iff.mp hk_cent) (((z : Q) : S) : G) hzZ
      calc
        (((z : Q) : S) : G) * (k : G) * (((z : Q) : S) : G)⁻¹ =
            (k : G) * (((z : Q) : S) : G) * (((z : Q) : S) : G)⁻¹ := by rw [hcomm]
        _ = (k : G) := by simp [mul_assoc]
  let : MulDistribMulAction (Q ⧸ ZQ) K :=
    section12_quotientMulDistribMulActionOfTrivial
      (A := Q) (M := K) (N := ZQ) hZQ_fix_all
  have : IsElementaryAbelian p.val (Q ⧸ ZQ) := by
    simpa [ZQ] using IsExtraspecial.quotient_elementary_abelian p.val Q
  have : IsMulCommutative (Q ⧸ ZQ) :=
    (inferInstance : IsElementaryAbelian p.val (Q ⧸ ZQ)).toIsMulCommutative
  let : CommGroup (Q ⧸ ZQ) := IsMulCommutative.instCommGroup
  have : Fact (IsPGroup p.val (Q ⧸ ZQ)) :=
    ⟨IsElementaryAbelian.isPGroup p.val (Q ⧸ ZQ)⟩
  have hquot_card : Nat.card (Q ⧸ ZQ) = p.val ^ 2 := by
    have hmul :
        Nat.card (Q ⧸ ZQ) * p.val = p.val ^ 2 * p.val := by
      calc
        Nat.card (Q ⧸ ZQ) * p.val =
            Nat.card (Q ⧸ ZQ) * Nat.card ZQ := by
              rw [show Nat.card ZQ = p.val by
                simpa [ZQ] using IsExtraspecial.center_order_p p.val Q]
        _ = Nat.card Q := by
              simpa [ZQ] using
                (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := Q)
                  (s := ZQ)).symm
        _ = p.val ^ 3 := hQcard
        _ = p.val ^ 2 * p.val := by ring
    exact Nat.eq_of_mul_eq_mul_right p.property.pos hmul
  have hquot_noncyc : ¬ IsCyclic (Q ⧸ ZQ) :=
    IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq
      (A := Q ⧸ ZQ) (p := p.val) hquot_card
  have hfix_top :
      (⨆ (a : Q ⧸ ZQ) (_ : a ≠ 1),
        fixedPointSubgroup (↥(Subgroup.zpowers a)) K) = ⊤ := by
    simpa using proposition_1_16_a (G := K) (A := Q ⧸ ZQ) p.val hKcop hquot_noncyc
  have hfixed_map_le :
      ∀ a : Q ⧸ ZQ, ∀ ha : a ≠ 1,
        (fixedPointSubgroup (↥(Subgroup.zpowers a)) K).map K.subtype ≤ Mstar := by
    intro a ha
    rcases QuotientGroup.mk'_surjective (N := ZQ) a with ⟨q, rfl⟩
    let XQ : Subgroup Q := Subgroup.zpowers q
    let X : Subgroup G := XQ.map (S.subtype.comp Q.subtype)
    have hq_not_ZQ : q ∉ ZQ := by
      intro hqZ
      exact ha ((QuotientGroup.eq_one_iff (N := ZQ) q).2 hqZ)
    have hq_ne : q ≠ 1 := by
      intro hq1
      exact hq_not_ZQ (by simp [ZQ, hq1])
    have hX_le_Mstar : X ≤ Mstar := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact hSleMstar ((y : Q) : S).property
    have hXcard : Nat.card X = p.val := by
      have hqpow : q ^ p.val = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent Q ∣ p.val by rw [hQexp]) q
      have horder : orderOf q = p.val := orderOf_eq_prime hqpow hq_ne
      calc
        Nat.card X = Nat.card XQ := by
          exact Subgroup.card_map_of_injective
            (K := XQ) (f := S.subtype.comp Q.subtype)
            (S.subtype_injective.comp Q.subtype_injective)
        _ = p.val := by
          change Nat.card (Subgroup.zpowers q) = p.val
          rw [Nat.card_zpowers]
          simpa using horder
    have hXelem : IsElementaryAbelian p.val X := by
      have hqpow : q ^ p.val = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent Q ∣ p.val by rw [hQexp]) q
      have : IsElementaryAbelian p.val XQ :=
        IsElementaryAbelian.zpowers_of_pow_eq_one (G := Q) (p := p.val) hqpow
      simpa [X, XQ] using
        IsElementaryAbelian.map (p := p.val)
          (A := XQ) (S.subtype.comp Q.subtype)
    have hXcentZ : X ≤ Subgroup.centralizer (Z : Set G) := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨xq, hxq, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [hZeq] at hz
      rcases Subgroup.mem_map.mp hz with ⟨zS, hzS, rfl⟩
      rcases Subgroup.mem_map.mp hzS with ⟨zq, hzq, hzq_eq⟩
      rcases Subgroup.mem_zpowers_iff.mp hxq with ⟨n, rfl⟩
      have hcomm0 : Commute zq q := by
        change zq * q = q * zq
        exact (Subgroup.mem_center_iff.mp hzq q).symm
      have hcomm : zq * q ^ n = q ^ n * zq := (hcomm0.zpow_right n).eq
      apply congrArg (fun u : Q => ((u : S) : G)) at hcomm
      simpa [← hzq_eq] using hcomm
    have hZX : Z ≠ X := by
      intro hZXeq
      have hqX : (((q : Q) : S) : G) ∈ X := by
        exact Subgroup.mem_map.mpr ⟨q, Subgroup.mem_zpowers q, rfl⟩
      have hqZ : (((q : Q) : S) : G) ∈ Z := by simpa [hZXeq] using hqX
      rw [hZeq] at hqZ
      rcases Subgroup.mem_map.mp hqZ with ⟨zS, hzS, hzS_eq⟩
      rcases Subgroup.mem_map.mp hzS with ⟨zq, hzq, hzq_eq⟩
      have hq_eq_zq : q = zq := by
        apply Q.subtype_injective
        calc
          (q : S) = zS := by
            exact S.subtype_injective hzS_eq.symm
          _ = (zq : S) := hzq_eq.symm
      exact hq_not_ZQ (by simpa [ZQ, hq_eq_zq] using hzq)
    have hZ_le_Mstar : Z ≤ Mstar := by
      intro z hz
      rw [hZeq] at hz
      rcases Subgroup.mem_map.mp hz with ⟨zS, _hzS, rfl⟩
      exact hSleMstar zS.property
    have hA2 : Z ⊔ X ∈ section12RankTwoElementaryAbelianIn p Mstar :=
      section12_rankTwo_sup_of_distinct_primeOrder_commuting
        (G := G) (M := Mstar) (Z := Z) (X := X) (p := p)
        hZ_le_Mstar hX_le_Mstar hZcard hXcard hZelem hXelem hXcentZ hZX
    have hcentA2_le_Mstar : Subgroup.centralizer ((Z ⊔ X : Subgroup G) : Set G) ≤ Mstar :=
      proposition_12_4_a (G := G) (M := Mstar) (A := Z ⊔ X) (p := p)
        hMstar hA2
    have hmap :
        XQ.map (QuotientGroup.mk' ZQ) =
          Subgroup.zpowers (QuotientGroup.mk' ZQ q) := by
      simp [XQ, MonoidHom.map_zpowers]
    have hfixed_quot_eq_XQ :
        fixedPointSubgroup (↥(Subgroup.zpowers (QuotientGroup.mk' ZQ q))) K =
          fixedPointSubgroup (↥XQ) K := by
      rw [← hmap]
      exact section12_fixedPointSubgroup_map_mk'_eq_of_trivial
        (A := Q) (M := K) (N := ZQ) (B := XQ) hZQ_fix_all
    intro k hk
    have hkfixXQ : k ∈ (fixedPointSubgroup (↥XQ) K).map K.subtype := by
      rw [← hfixed_quot_eq_XQ]
      exact hk
    rcases Subgroup.mem_map.mp hkfixXQ with ⟨kK, hkfix, hk_eq⟩
    have hkK : (k : G) ∈ K := by
      rw [← hk_eq]
      exact kK.property
    have hk_centZ : k ∈ Subgroup.centralizer (Z : Set G) := hkK.2
    have hk_centX : k ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨xq, hxq, rfl⟩
      have hfix_xq : (⟨xq, hxq⟩ : XQ) • kK = kK := by
        rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hkfix
        exact hkfix ⟨xq, hxq⟩
      have hfix_val := congrArg (fun u : K => (u : G)) hfix_xq
      have hconj :
          (((xq : Q) : S) : G) * (kK : G) * ((((xq : Q) : S) : G))⁻¹ =
            (kK : G) := by
        simpa [qNorm, XQ, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          MulAction.compHom_smul_def] using hfix_val
      have hcomm :
          (((xq : Q) : S) : G) * (kK : G) =
            (kK : G) * (((xq : Q) : S) : G) := by
        simpa [mul_assoc] using
          congrArg (fun t : G => t * (((xq : Q) : S) : G)) hconj
      have hk_eq_coe : (kK : G) = k := hk_eq
      calc
        (((xq : Q) : S) : G) * k =
            (((xq : Q) : S) : G) * (kK : G) := by rw [hk_eq_coe]
        _ = (kK : G) * (((xq : Q) : S) : G) := hcomm
        _ = k * (((xq : Q) : S) : G) := by rw [hk_eq_coe]
    have hk_cent_sup : k ∈ Subgroup.centralizer ((Z ⊔ X : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_sup_of_le_centralizers
        (G := G) (R := Subgroup.zpowers k) (A := Z) (B := X)
        (by
          intro y hy
          rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          have hcomm : Commute z k := by
            change z * k = k * z
            exact Subgroup.mem_centralizer_iff.mp hk_centZ z hz
          exact (hcomm.zpow_right n).eq)
        (by
          intro y hy
          rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          have hcomm : Commute x k := by
            change x * k = k * x
            exact Subgroup.mem_centralizer_iff.mp hk_centX x hx
          exact (hcomm.zpow_right n).eq)
        (Subgroup.mem_zpowers k)
    exact hcentA2_le_Mstar hk_cent_sup
  have htop_map_K : (⊤ : Subgroup K).map K.subtype = K := by
    simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := K))
  have hK_le_Mstar : K ≤ Mstar := by
    calc
      K = (⊤ : Subgroup K).map K.subtype := htop_map_K.symm
      _ =
          (⨆ (a : Q ⧸ ZQ) (_ : a ≠ 1),
            fixedPointSubgroup (↥(Subgroup.zpowers a)) K).map K.subtype := by
            simp [hfix_top]
      _ ≤ Mstar := by
            rw [Subgroup.map_iSup]
            refine iSup_le ?_
            intro a
            rw [Subgroup.map_iSup]
            refine iSup_le ?_
            intro ha
            exact hfixed_map_le a ha
  simpa [K, Z] using hK_le_Mstar

private theorem CFSG.section12_subgroupNormalizerIn_le_of_malpha_centralizer_le
    {M Mstar Z : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpα : p ∉ section10AlphaPrimes M) (hZp : IsPGroup p.val Z)
    (hZ_le : Z ≤ Mstar ⊓ M)
    (hjoin : Mstar ⊓ M ⊔ section10Mbeta M = M)
    (hαβ : section10AlphaPrimes M = section10BetaPrimes M)
    (hCα_le_Mstar : subgroupCentralizerIn (section10Malpha M) Z ≤ Mstar) :
    subgroupNormalizerIn M (Z : Set G) ≤ Mstar := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let K : Subgroup M := section10MalphaSubgroup M
  let U : Subgroup M := (Mstar ⊓ M).subgroupOf M
  let H : Subgroup M := Z.subgroupOf M
  have hZ_le_M : Z ≤ M := hZ_le.trans inf_le_right
  have hZ_le_U_amb : Z ≤ Mstar ⊓ M := hZ_le
  have hH_le_U : H ≤ U := by
    intro z hz
    change (z : G) ∈ Mstar ⊓ M
    exact hZ_le_U_amb hz
  have hHp : IsPGroup p.val H :=
    hZp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := Z) (K := M) hZ_le_M).symm
  have hKpi : IsPiSubgroup (G := M) ({p} : Set Nat.Primes)ᶜ K := by
    intro q hqK
    rw [Set.mem_compl_iff]
    intro hqp
    have hqα : q ∈ section10AlphaPrimes M :=
      (theorem_10_2_a (G := G) hM).2.p_in_pi_of_p_dvd_card q hqK
    have hq_eq : q = p := Set.mem_singleton_iff.mp hqp
    exact hpα (by simpa [hq_eq] using hqα)
  have hcop : Nat.Coprime (Nat.card H) (Nat.card K) :=
    section8_coprime_card_of_isPGroup_of_isPiSubgroup_compl
      (G := M) (π := ({p} : Set Nat.Primes)) (r := p)
      (R := H) (Y := K) (by simp) hHp hKpi
  have hβeqα : section10Mbeta M = section10Malpha M := by
    simp [section10Mbeta, section10Malpha, section10MbetaSubgroup,
      section10MalphaSubgroup, hαβ]
  have hKU : K ⊔ U = ⊤ := by
    apply Subgroup.map_injective M.subtype_injective
    have hKmap : K.map M.subtype = section10Malpha M := by
      rfl
    have hUmap : U.map M.subtype = Mstar ⊓ M := by
      simp [U]
    calc
      (K ⊔ U).map M.subtype =
          section10Malpha M ⊔ (Mstar ⊓ M) := by
            rw [Subgroup.map_sup, hKmap, hUmap]
      _ = section10Mbeta M ⊔ (Mstar ⊓ M) := by
            rw [hβeqα]
      _ = Mstar ⊓ M ⊔ section10Mbeta M := by
            rw [sup_comm]
      _ = M := hjoin
      _ = (⊤ : Subgroup M).map M.subtype := by
            simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := M)).symm
  have : K.Normal := section10MalphaSubgroup_normal (M := M)
  have : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hdecomp :
      (Subgroup.normalizer (G := M) (H : Set M) : Set M) =
        (subgroupCentralizerIn K H) * (subgroupNormalizerIn U H) :=
    lemma_6_5_b (G := M) (K := K) (U := U) (H := H) hKU hH_le_U hcop
  intro x hx
  rcases mem_subgroupNormalizerIn.mp hx with ⟨hxNorm, hxM⟩
  let xM : M := ⟨x, hxM⟩
  have hxM_norm : xM ∈ Subgroup.normalizer (G := M) (H : Set M) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hyH
      change ((xM * y * xM⁻¹ : M) : G) ∈ Z
      have hyZ : (y : G) ∈ Z := hyH
      have hxZ : x * (y : G) * x⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp hxNorm (y : G)).1 hyZ
      simpa [xM, mul_assoc] using hxZ
    · intro hyH
      change ((xM * y * xM⁻¹ : M) : G) ∈ Z at hyH
      have hyZ : x * (y : G) * x⁻¹ ∈ Z := by
        simpa [xM, mul_assoc] using hyH
      have hyZ' : (y : G) ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp hxNorm (y : G)).2 hyZ
      exact hyZ'
  have hx_prod :
      xM ∈ (subgroupCentralizerIn K H : Set M) *
          (subgroupNormalizerIn U H : Set M) := by
    have hxM_norm' : xM ∈ (Subgroup.normalizer (G := M) (H : Set M) : Set M) :=
      hxM_norm
    rw [hdecomp] at hxM_norm'
    exact hxM_norm'
  rcases hx_prod with ⟨c, hc, u, hu, hcu⟩
  have hcMstar : (c : G) ∈ Mstar := by
    apply hCα_le_Mstar
    refine ⟨?_, ?_⟩
    · change (c : G) ∈ section10Malpha M
      exact Subgroup.mem_map_of_mem M.subtype hc.1
    · change (c : G) ∈ Subgroup.centralizer (Z : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hzZ
      have hzM : z ∈ M := hZ_le_M hzZ
      let zM : M := ⟨z, hzM⟩
      have hzH : zM ∈ H := hzZ
      have hcommM : zM * c = c * zM :=
        (Subgroup.mem_centralizer_iff.mp hc.2) zM hzH
      exact congrArg (fun y : M => (y : G)) hcommM
  have huMstar : (u : G) ∈ Mstar := by
    have huU : u ∈ U := (mem_subgroupNormalizerIn.mp hu).2
    exact huU.1
  have hx_eq : x = (c : G) * (u : G) := by
    simpa [xM] using (congrArg (fun y : M => (y : G)) hcu).symm
  rw [hx_eq]
  exact Mstar.mul_mem hcMstar huMstar

private theorem CFSG.section12_nonabelian_pSubgroup_unique_of_rankTwo_maximal
    {P A : Subgroup G} {p : Nat.Primes}
    (hPp : IsPGroup p.val P) (hPnonab : ¬ IsMulCommutative P)
    (hA_P : A ∈ section12RankTwoElementaryAbelianIn p P)
    (hAmax : A ∈ maximalElementaryAbelianSubgroups p.val G) :
    P ∈ section9UniqueSubgroups G := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have hPnoncyc : ¬ IsCyclic P :=
    section12_nonabelian_pSubgroup_not_isCyclic (G := G) hPp hPnonab
  have hPproper : P ≠ ⊤ := IsMinCE.pSubgroup_ne_top (G := G) (p := p.val) hPp
  obtain ⟨M, hMcont⟩ :=
    section9_exists_maximalSubgroupsContaining_of_ne_top (G := G) hPproper
  refine ⟨hPproper, M, ?_⟩
  apply Set.eq_singleton_iff_unique_mem.mpr
  constructor
  · exact hMcont
  · intro Mstar hMstar
    by_contra hMstar_ne
    have hPleM : P ≤ M := hMcont.2
    have hPleMstar : P ≤ Mstar := hMstar.2
    have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
      section12_rankTwo_mono hA_P hPleM
    have hA_Mstar : A ∈ section12RankTwoElementaryAbelianIn p Mstar :=
      section12_rankTwo_mono hA_P hPleMstar
    have hPnil : Group.IsNilpotent P :=
      IsPGroup.isNilpotent (p := p.val) (G := P) (h := hPp)
    have hpσM : p ∈ section10SigmaPrimes M := by
      by_contra hpnot
      have hPπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ P := by
        intro q hqP
        have hq_mem : q ∈ ({p} : Set Nat.Primes) :=
          section8_isPiSubgroup_singleton_of_isPGroup (G := G) hPp q hqP
        simpa using (show q ∉ section10SigmaPrimes M from by
          intro hqσ
          exact hpnot (by simpa using hq_mem ▸ hqσ))
      exact hPnonab (corollary_12_10_a (G := G) hMcont.1 hPleM hPπ hPnil)
    have hpσMstar : p ∈ section10SigmaPrimes Mstar := by
      by_contra hpnot
      have hPπ : IsPiSubgroup (G := G) (section10SigmaPrimes Mstar)ᶜ P := by
        intro q hqP
        have hq_mem : q ∈ ({p} : Set Nat.Primes) :=
          section8_isPiSubgroup_singleton_of_isPGroup (G := G) hPp q hqP
        simpa using (show q ∉ section10SigmaPrimes Mstar from by
          intro hqσ
          exact hpnot (by simpa using hq_mem ▸ hqσ))
      exact hPnonab (corollary_12_10_a (G := G) hMstar.1 hPleMstar hPπ hPnil)
    have hNormP_le_M : Subgroup.normalizer (P : Set G) ≤ M :=
      corollary_12_10_d (G := G) hMcont.1 hpσM hPp hPleM hPnoncyc
    have hNormP_le_Mstar : Subgroup.normalizer (P : Set G) ≤ Mstar :=
      corollary_12_10_d (G := G) hMstar.1 hpσMstar hPp hPleMstar hPnoncyc
    have hA10 : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G := by
      simpa [section10RankTwoMaximalElementaryAbelianSubgroups] using
        (⟨section12_rankTwo_elementary hA_P, hAmax⟩ :
          A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G ∧
            A ∈ maximalElementaryAbelianSubgroups p.val G)
    have hpG : p ∈ subgroupPrimeSet (⊤ : Subgroup G) := by
      exact (section12_rankTwo_prime_mem hA_P).trans
        (Subgroup.card_dvd_of_le (show P ≤ (⊤ : Subgroup G) from le_top))
    let I : Subgroup G := M ⊓ Mstar
    have hP_le_I : P ≤ I := le_inf hPleM hPleMstar
    have hPsub_p : IsPGroup p.val (P.subgroupOf I) :=
      hPp.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := P) (K := I) hP_le_I).symm
    obtain ⟨S, hPsub_le_S⟩ :=
      IsPGroup.exists_le_sylow (G := I) (p := p.val) hPsub_p
    let Pamb : Subgroup G := section10AmbientSylowSubgroup I S
    have hP_le_Pamb : P ≤ Pamb := by
      intro x hx
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hP_le_I hx⟩,
          hPsub_le_S (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
    have hA_le_Pamb : A ≤ Pamb :=
      (section12_rankTwo_le hA_P).trans hP_le_Pamb
    have hPamb_p : IsPGroup p.val Pamb := by
      change IsPGroup p.val ((S : Subgroup I).map I.subtype)
      exact IsPGroup.map S.isPGroup' I.subtype
    have hPamb_le_M : Pamb ≤ M := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.2.1
    have hPamb_le_Mstar : Pamb ≤ Mstar := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.2.2
    have hPamb_noncyc : ¬ IsCyclic Pamb := by
      intro hcyc
      exact hPnoncyc (Subgroup.isCyclic_of_le (H := P) (H' := Pamb) hP_le_Pamb)
    have hPamb_nonab : ¬ IsMulCommutative Pamb := by
      intro hcomm
      let : IsMulCommutative Pamb := hcomm
      apply hPnonab
      refine ⟨⟨fun x y => ?_⟩⟩
      have hxPamb : (x : G) ∈ Pamb := hP_le_Pamb x.property
      have hyPamb : (y : G) ∈ Pamb := hP_le_Pamb y.property
      have hxy :
        (x : G) * (y : G) = (y : G) * (x : G) :=
        setLike_mul_comm
          (s := Pamb) hxPamb hyPamb
      exact Subtype.ext hxy
    have hPamb_proper : Pamb ≠ ⊤ := by
      intro htop
      have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        simpa [htop] using hPamb_le_M
      exact hMcont.1.1 (top_le_iff.mp htop_le_M)
    have hPamb_rank_le_two : groupRank Pamb ≤ 2 := by
      by_contra hnot
      have hPamb_rank_ge_three : 3 ≤ groupRank Pamb := by omega
      have hPamb_rank_ge_two : 2 ≤ groupRank Pamb := by omega
      have hPamb_unique : Pamb ∈ section9UniqueSubgroups G :=
        theorem_9_6 (G := G) hPamb_proper hPamb_rank_ge_two
          (Or.inl hPamb_rank_ge_three)
      rcases hPamb_unique with ⟨_hPamb_proper, N, hNuniq⟩
      have hM_cont_Pamb :
          M ∈ section9MaximalSubgroupsContaining Pamb :=
        ⟨hMcont.1, hPamb_le_M⟩
      have hMstar_cont_Pamb :
          Mstar ∈ section9MaximalSubgroupsContaining Pamb :=
        ⟨hMstar.1, hPamb_le_Mstar⟩
      have hM_eq_N : M = N := by
        have hsingle : M ∈ ({N} : Set (Subgroup G)) := by
          simpa [hNuniq] using hM_cont_Pamb
        simpa using hsingle
      have hMstar_eq_N : Mstar = N := by
        have hsingle : Mstar ∈ ({N} : Set (Subgroup G)) := by
          simpa [hNuniq] using hMstar_cont_Pamb
        simpa using hsingle
      exact hMstar_ne (hMstar_eq_N.trans hM_eq_N.symm)
    have hNormPamb_le_M :
        Subgroup.normalizer (Pamb : Set G) ≤ M :=
      corollary_12_10_d (G := G) (M := M) (P := Pamb) (p := p)
        hMcont.1 hpσM hPamb_p hPamb_le_M hPamb_noncyc
    have hNormPamb_le_Mstar :
        Subgroup.normalizer (Pamb : Set G) ≤ Mstar :=
      corollary_12_10_d (G := G) (M := Mstar) (P := Pamb) (p := p)
        hMstar.1 hpσMstar hPamb_p hPamb_le_Mstar hPamb_noncyc
    have hnormInf :
        Subgroup.normalizer
            (section8SubgroupInAmbient (S : Subgroup I) : Set G) ≤ I := by
      intro g hg
      have hg' : g ∈ Subgroup.normalizer (Pamb : Set G) := by
        simpa [Pamb, section10AmbientSylowSubgroup, section8SubgroupInAmbient] using hg
      exact ⟨hNormPamb_le_M hg', hNormPamb_le_Mstar hg'⟩
    rcases section8SubgroupInAmbient_sylow_of_normalizer_le
        (G := G) (p := p.val) (M := I) S hnormInf with
      ⟨Sg, hSg⟩
    have hPamb_eq_Sg : Pamb = (Sg : Subgroup G) := by
      simpa [Pamb, section10AmbientSylowSubgroup, section8SubgroupInAmbient] using
        hSg.symm
    have hSg_rank_le_two : groupRank (Sg : Subgroup G) ≤ 2 := by
      exact
        (groupRank_le_of_equiv
          (R := Pamb) (S := (Sg : Subgroup G))
          (MulEquiv.subgroupCongr hPamb_eq_Sg)).trans hPamb_rank_le_two
    have hSg_nonab : ¬ IsMulCommutative (Sg : Subgroup G) := by
      intro hcomm
      apply hPamb_nonab
      let : IsMulCommutative (Sg : Subgroup G) := hcomm
      refine ⟨⟨fun x y => ?_⟩⟩
      have hxSg : (x : G) ∈ (Sg : Subgroup G) := by
        exact hPamb_eq_Sg.le x.property
      have hySg : (y : G) ∈ (Sg : Subgroup G) := by
        exact hPamb_eq_Sg.le y.property
      have hxy :
        (x : G) * (y : G) = (y : G) * (x : G) :=
        setLike_mul_comm
          (s := (Sg : Subgroup G)) hxSg hySg
      exact Subtype.ext hxy
    have hSg_shape : section10SpecialRankTwoSylowShape (H := (Sg : Subgroup G)) p := by
      rcases corollary_10_7_b (G := G) Sg hSg_rank_le_two with hSg_comm | hshape
      · exact False.elim (hSg_nonab hSg_comm)
      · exact hshape
    have hSg_norm_Mstar_M :
        Subgroup.normalizer ((Sg : Subgroup G) : Set G) ≤ Mstar ⊓ M := by
      intro g hg
      have hg' : g ∈ Subgroup.normalizer (Pamb : Set G) := by
        simpa [hSg, Pamb, section10AmbientSylowSubgroup, section8SubgroupInAmbient] using hg
      exact ⟨hNormPamb_le_Mstar hg', hNormPamb_le_M hg'⟩
    have hSg_norm_M_Mstar :
        Subgroup.normalizer ((Sg : Subgroup G) : Set G) ≤ M ⊓ Mstar := by
      intro g hg
      have hg' : g ∈ Subgroup.normalizer (Pamb : Set G) := by
        simpa [hSg, Pamb, section10AmbientSylowSubgroup, section8SubgroupInAmbient] using hg
      exact ⟨hNormPamb_le_M hg', hNormPamb_le_Mstar hg'⟩
    have h109bM :
        Mstar ⊓ M ⊔ section10Mbeta M = M ∧
          section10AlphaPrimes M = section10BetaPrimes M :=
      corollary_10_9_b (G := G) (M := M) (H := Mstar)
        hMcont.1 hMstar.1 hMstar_ne ⟨p, Sg, hSg_norm_Mstar_M⟩
    have h109bMstar :
        M ⊓ Mstar ⊔ section10Mbeta Mstar = Mstar ∧
          section10AlphaPrimes Mstar = section10BetaPrimes Mstar :=
      corollary_10_9_b (G := G) (M := Mstar) (H := M)
        hMstar.1 hMcont.1 (fun h => hMstar_ne h.symm)
        ⟨p, Sg, hSg_norm_M_Mstar⟩
    have hMalpha_ne : section10Malpha M ≠ ⊥ := by
      have hβ_ne : section10Mbeta M ≠ ⊥ := by
        intro hβbot
        have hM_le_Mstar : M ≤ Mstar := by
          intro x hx
          have hxjoin : x ∈ Mstar ⊓ M ⊔ section10Mbeta M := by
            rw [h109bM.1]
            exact hx
          have hxinf : x ∈ Mstar ⊓ M := by
            simpa [hβbot] using hxjoin
          exact hxinf.1
        have hMstar_eq_M : Mstar = M :=
          (hMcont.1.le_iff_eq hMstar.1.1).mp hM_le_Mstar
        exact hMstar_ne hMstar_eq_M
      intro hαbot
      have hβ_eq_α : section10Mbeta M = section10Malpha M := by
        simp [section10Mbeta, section10Malpha, section10MbetaSubgroup,
          section10MalphaSubgroup, h109bM.2]
      exact hβ_ne (by simpa [hβ_eq_α] using hαbot)
    have hMstaralpha_ne : section10Malpha Mstar ≠ ⊥ := by
      have hβ_ne : section10Mbeta Mstar ≠ ⊥ := by
        intro hβbot
        have hMstar_le_M : Mstar ≤ M := by
          intro x hx
          have hxjoin : x ∈ M ⊓ Mstar ⊔ section10Mbeta Mstar := by
            rw [h109bMstar.1]
            exact hx
          have hxinf : x ∈ M ⊓ Mstar := by
            simpa [hβbot] using hxjoin
          exact hxinf.1
        have hM_eq_Mstar : M = Mstar :=
          (hMstar.1.le_iff_eq hMcont.1.1).mp hMstar_le_M
        exact hMstar_ne hM_eq_Mstar.symm
      intro hαbot
      have hβ_eq_α : section10Mbeta Mstar = section10Malpha Mstar := by
        simp [section10Mbeta, section10Malpha, section10MbetaSubgroup,
          section10MalphaSubgroup, h109bMstar.2]
      exact hβ_ne (by simpa [hβ_eq_α] using hαbot)
    have hExistsM :
        ∃ A₀ : Subgroup G,
          A₀ ∈ section10PrimeOrderSubgroupsIn p A ∧
            section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) =
              {M} := by
      by_contra hnone
      have hnotUnique :
          ∀ A₀ : Subgroup G, A₀ ∈ section10PrimeOrderSubgroupsIn p A →
            section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) ≠
              {M} := by
        intro A₀ hA₀ huniq
        exact hnone ⟨A₀, hA₀, huniq⟩
      exact hMalpha_ne (proposition_12_4_b (G := G) hMcont.1 hA_M hnotUnique).2.1
    have hExistsMstar :
        ∃ A₀ : Subgroup G,
          A₀ ∈ section10PrimeOrderSubgroupsIn p A ∧
            section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) =
              {Mstar} := by
      by_contra hnone
      have hnotUnique :
          ∀ A₀ : Subgroup G, A₀ ∈ section10PrimeOrderSubgroupsIn p A →
            section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) ≠
              {Mstar} := by
        intro A₀ hA₀ huniq
        exact hnone ⟨A₀, hA₀, huniq⟩
      exact hMstaralpha_ne
        (proposition_12_4_b (G := G) hMstar.1 hA_Mstar hnotUnique).2.1
    rcases hSg_shape with
      ⟨Qshape, Yshape, hQshape_card, hQshape_noncomm, hQshape_exp,
        hYshape_cyc, hQYshape_central, hOmegaYshape_centerQ⟩
    let Z : Subgroup G := section10OmegaOneCenter p Pamb
    let Qamb : Subgroup G := Qshape.map (Sg : Subgroup G).subtype
    have hZ_eq_centerQ :
        Z = (Subgroup.center Qshape).map
            ((Sg : Subgroup G).subtype.comp Qshape.subtype) := by
      have hPamb_eq_Sg' : Pamb = (Sg : Subgroup G) := hPamb_eq_Sg
      calc
        Z = section10OmegaOneCenter p (Sg : Subgroup G) := by
          simp [Z, hPamb_eq_Sg']
        _ =
            ((Subgroup.center Qshape).map Qshape.subtype).map
              (Sg : Subgroup G).subtype := by
          simpa using
            section10_omegaOneCenter_eq_center_map_of_centralProduct
              (G := G) (P := (Sg : Subgroup G)) (Q := Qshape) (Y := Yshape)
              (p := p) hQshape_card hQshape_noncomm hQshape_exp
              hYshape_cyc hQYshape_central hOmegaYshape_centerQ
        _ = (Subgroup.center Qshape).map
            ((Sg : Subgroup G).subtype.comp Qshape.subtype) := by
          rw [Subgroup.map_map]
    have hZp : IsPGroup p.val Z := by
      simpa [Z] using section10OmegaOneCenter_isPGroup (G := G) (p := p) Pamb
    have hZ_le_Pamb : Z ≤ Pamb := by
      intro z hz
      change z ∈ (Ω₁Z p.val Pamb).map Pamb.subtype at hz
      rcases Subgroup.mem_map.mp hz with ⟨zP, _hzΩ, rfl⟩
      exact zP.property
    have hZ_le_Mstar_M : Z ≤ Mstar ⊓ M :=
      le_inf (hZ_le_Pamb.trans hPamb_le_Mstar) (hZ_le_Pamb.trans hPamb_le_M)
    have hZ_le_M_Mstar : Z ≤ M ⊓ Mstar :=
      le_inf (hZ_le_Pamb.trans hPamb_le_M) (hZ_le_Pamb.trans hPamb_le_Mstar)
    have hpnotαM : p ∉ section10AlphaPrimes M := by
      intro hpα
      have hpβ : p ∈ section10BetaPrimes M := by
        simpa [h109bM.2] using hpα
      have hEmpty :
          section10RankTwoMaximalElementaryAbelianSubgroups p G = ∅ :=
        (proposition_10_14_a (G := G) (p := p) hpβ.2 Sg).2
      simp [hEmpty] at hA10
    have hpnotαMstar : p ∉ section10AlphaPrimes Mstar := by
      intro hpα
      have hpβ : p ∈ section10BetaPrimes Mstar := by
        simpa [h109bMstar.2] using hpα
      have hEmpty :
          section10RankTwoMaximalElementaryAbelianSubgroups p G = ∅ :=
        (proposition_10_14_a (G := G) (p := p) hpβ.2 Sg).2
      simp [hEmpty] at hA10
    have hZnotM :
        section9MaximalSubgroupsContaining (Subgroup.normalizer (Z : Set G)) ≠ {M} := by
      have hNZ_le_Mstar :
          subgroupNormalizerIn M (Z : Set G) ≤ Mstar := by
        have hCα_le_Mstar :
            subgroupCentralizerIn (section10Malpha M) Z ≤ Mstar := by
          have hSg_le_M : (Sg : Subgroup G) ≤ M := by
            simpa [← hPamb_eq_Sg] using hPamb_le_M
          have hSg_le_Mstar : (Sg : Subgroup G) ≤ Mstar := by
            simpa [← hPamb_eq_Sg] using hPamb_le_Mstar
          simpa [Z, hPamb_eq_Sg] using
            section12_malpha_centralizer_omegaOneCenter_le_mstar_of_shape
              (G := G) (M := M) (Mstar := Mstar) (S := (Sg : Subgroup G))
              (Q := Qshape) (Y := Yshape) (p := p)
              hMcont.1 hMstar.1 hpnotαM hSg_le_M hSg_le_Mstar
              hQshape_card hQshape_noncomm hQshape_exp hYshape_cyc
              hQYshape_central hOmegaYshape_centerQ
        exact
          section12_subgroupNormalizerIn_le_of_malpha_centralizer_le
            (G := G) (M := M) (Mstar := Mstar) (Z := Z) (p := p)
            hMcont.1 hpnotαM hZp hZ_le_Mstar_M h109bM.1 h109bM.2
            hCα_le_Mstar
      exact section12_not_singleton_normalizer_of_subgroupNormalizerIn_le
        (G := G) (M := M) (Mstar := Mstar) (Z := Z)
        hMstar.1 hMstar_ne hNZ_le_Mstar
    have hZnotMstar :
        section9MaximalSubgroupsContaining (Subgroup.normalizer (Z : Set G)) ≠
          {Mstar} := by
      have hNZ_le_M :
          subgroupNormalizerIn Mstar (Z : Set G) ≤ M := by
        have hCα_le_M :
            subgroupCentralizerIn (section10Malpha Mstar) Z ≤ M := by
          have hSg_le_M : (Sg : Subgroup G) ≤ M := by
            simpa [← hPamb_eq_Sg] using hPamb_le_M
          have hSg_le_Mstar : (Sg : Subgroup G) ≤ Mstar := by
            simpa [← hPamb_eq_Sg] using hPamb_le_Mstar
          simpa [Z, hPamb_eq_Sg] using
            section12_malpha_centralizer_omegaOneCenter_le_mstar_of_shape
              (G := G) (M := Mstar) (Mstar := M) (S := (Sg : Subgroup G))
              (Q := Qshape) (Y := Yshape) (p := p)
              hMstar.1 hMcont.1 hpnotαMstar hSg_le_Mstar hSg_le_M
              hQshape_card hQshape_noncomm hQshape_exp hYshape_cyc
              hQYshape_central hOmegaYshape_centerQ
        exact
          section12_subgroupNormalizerIn_le_of_malpha_centralizer_le
            (G := G) (M := Mstar) (Mstar := M) (Z := Z) (p := p)
            hMstar.1 hpnotαMstar hZp hZ_le_M_Mstar h109bMstar.1 h109bMstar.2
            hCα_le_M
      exact section12_not_singleton_normalizer_of_subgroupNormalizerIn_le
        (G := G) (M := Mstar) (Mstar := M) (Z := Z)
        hMcont.1 (fun h => hMstar_ne h.symm) hNZ_le_M
    rcases hExistsM with ⟨A₀, hA₀, hA₀uniq⟩
    rcases hExistsMstar with ⟨A₀star, hA₀star, hA₀staruniq⟩
    have hA₀neZ : A₀ ≠ Z := by
      intro hA₀Z
      exact hZnotM (by simpa [Z, hA₀Z] using hA₀uniq)
    have hA₀starneZ : A₀star ≠ Z := by
      intro hA₀starZ
      exact hZnotMstar (by simpa [Z, hA₀starZ] using hA₀staruniq)
    have htrans :
        ConjugationActionTransitiveOn (subgroupNormalizerIn Pamb (A : Set G))
          {X | X ∈ section10PrimeOrderSubgroupsIn p A ∧ X ≠ Z} := by
      simpa [Z] using
        lemma_10_13_c (G := G) (p := p) (A := A) (P := Pamb) (A₀ := A₀)
          hpG hA10 hPamb_p hPamb_nonab hA_le_Pamb hA₀
          (by simpa [Z] using hA₀neZ)
    obtain ⟨k, hk⟩ := htrans A₀ ⟨hA₀, hA₀neZ⟩
      A₀star ⟨hA₀star, hA₀starneZ⟩
    have hkPamb : (k : G) ∈ Pamb := (mem_subgroupNormalizerIn.mp k.property).2
    have hkM : (k : G) ∈ M := hPamb_le_M hkPamb
    have hnormA₀_le_M :
        Subgroup.normalizer (A₀ : Set G) ≤ M := by
      have hMmem :
          M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) := by
        rw [hA₀uniq]
        simp
      exact hMmem.2
    have hA₀star_conj_inv : A₀star.conjBy ((k : G)⁻¹) = A₀ := by
      rw [hk, section11_conjBy_inv (G := G) A₀ (k : G)]
    have hnormA₀star_conj_le :
        (Subgroup.normalizer (A₀star : Set G)).conjBy ((k : G)⁻¹) ≤
          Subgroup.normalizer (A₀ : Set G) := by
      have hraw :
          (Subgroup.normalizer (A₀star : Set G)).conjBy ((k : G)⁻¹) ≤
            Subgroup.normalizer (A₀star.conjBy ((k : G)⁻¹) : Set G) :=
        section11_conjBy_le_normalizer_conjBy_of_le_normalizer
          (G := G) (H := Subgroup.normalizer (A₀star : Set G)) (K := A₀star)
          le_rfl ((k : G)⁻¹)
      simpa [hA₀star_conj_inv] using hraw
    have hnormA₀star_le_M :
        Subgroup.normalizer (A₀star : Set G) ≤ M := by
      intro n hn
      have hn_conj :
          (k : G)⁻¹ * n * (k : G) ∈
            (Subgroup.normalizer (A₀star : Set G)).conjBy ((k : G)⁻¹) := by
        rw [Subgroup.conjBy, Subgroup.mem_map]
        exact ⟨n, hn, by simp [mul_assoc]⟩
      have hn_conj_M : (k : G)⁻¹ * n * (k : G) ∈ M :=
        hnormA₀_le_M (hnormA₀star_conj_le hn_conj)
      have hn_eq : n = (k : G) * ((k : G)⁻¹ * n * (k : G)) * (k : G)⁻¹ := by
        group
      rw [hn_eq]
      exact M.mul_mem (M.mul_mem hkM hn_conj_M) (M.inv_mem hkM)
    have hM_mem_star :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀star : Set G)) :=
      ⟨hMcont.1, hnormA₀star_le_M⟩
    have hM_eq_Mstar : M = Mstar := by
      have hsingle : M ∈ ({Mstar} : Set (Subgroup G)) := by
        simpa [hA₀staruniq] using hM_mem_star
      simpa using hsingle
    exact hMstar_ne hM_eq_Mstar.symm

/-- Theorem 12.13. -/
public theorem CFSG.theorem_12_13
    {P : Subgroup G} {p : Nat.Primes}
    (hPp : IsPGroup p.val P) (hPnonab : ¬ IsMulCommutative P) :
    P ∈ section9UniqueSubgroups G := by
  classical
  have hPnoncyc : ¬ IsCyclic P :=
    section12_nonabelian_pSubgroup_not_isCyclic (G := G) hPp hPnonab
  obtain ⟨A, hA_P⟩ :=
    section12_exists_rankTwo_in_noncyclic_pSubgroup (G := G) (P := P) (p := p)
      hPp hPnoncyc
  have hA_le_P : A ≤ P := section12_rankTwo_le hA_P
  have hArankTwo : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G :=
    section12_rankTwo_elementary hA_P
  by_cases hAmax : A ∈ maximalElementaryAbelianSubgroups p.val G
  · exact section12_nonabelian_pSubgroup_unique_of_rankTwo_maximal
      (G := G) (P := P) (A := A) (p := p) hPp hPnonab hA_P hAmax
  · have hAunique : A ∈ section9UniqueSubgroups G :=
      theorem_9_6_in_particular (G := G)
        ⟨p.val, p.2, hArankTwo, hAmax⟩
    have : Fact p.val.Prime := ⟨p.property⟩
    exact section9_unique_of_le hA_le_P
      (IsMinCE.pSubgroup_ne_top (G := G) (p := p.val) hPp) hAunique

end MinCE

end Finite

end Section12
