module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822R2
public import CFSG.Quasithin.Vol2.Ch8Sec2L822R3
public import CFSG.Quasithin.Vol2.Ch10SecABasic
public import CFSG.Quasithin.H13.A6S13821M22c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

private theorem res822R4_card_X {X : Type} [Group X] [Finite X]
    (e : X ⧸ Subgroup.center X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) :
    Nat.card X = 443520 * Nat.card (Subgroup.center X) := by
  have h22 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
    CFSG.Sporadic.Mathieu.card_M22
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), Nat.card_congr e.toEquiv, h22]

private theorem res822R4_card_quotient {X Q : Type} [Group X] [Finite X] [Group Q]
    (hX : CFSG.IsQuasisimple X)
    (hZ : Nat.card (Subgroup.center X) = 1 ∨ Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22)
    (ψ : X →* Q) (hψ : Function.Surjective ψ) (hnt : ¬ Subsingleton Q) :
    Nat.card Q = 1330560 ∨ Nat.card Q = 443520 := by
  have hne : ψ.ker ≠ ⊤ := by
    intro ht
    apply hnt
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hψ a
    obtain ⟨b', rfl⟩ := hψ b
    rw [MonoidHom.mem_ker.1 (ht ▸ Subgroup.mem_top a'), MonoidHom.mem_ker.1 (ht ▸ Subgroup.mem_top b')]
  have hle : ψ.ker ≤ Subgroup.center X :=
    CFSG.Quasithin.Vol2.Ch11.SecA.le_center_of_normal_ne_top hX hne
  have hd1 : Nat.card ψ.ker ∣ Nat.card (Subgroup.center X) := Subgroup.card_dvd_of_le hle
  have hX2 : Nat.card X = Nat.card Q * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv]
  rw [res822R4_card_X e] at hX2
  rcases hZ with hZ | hZ
  · rw [hZ] at hd1 hX2
    have hk : Nat.card ψ.ker = 1 := Nat.dvd_one.mp hd1
    rw [hk] at hX2
    omega
  · rw [hZ] at hd1 hX2
    rcases (Nat.dvd_prime Nat.prime_three).1 hd1 with hk | hk <;> rw [hk] at hX2 <;> omega

private theorem res822R4_threeRank2 {X : Type} [Group X] [Finite X]
    (hZ : Nat.card (Subgroup.center X) = 1 ∨ Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) :
    FFC.ThreeRank2 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h22 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
    CFSG.Sporadic.Mathieu.card_M22
  have hfin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    Nat.finite_of_card_ne_zero (by rw [h22]; norm_num)
  have hM : FFC.ThreeRank2 (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    FFC.ThreeRank2.of_pRank
      (a318Exclusion_m22 (X := CFSG.Blueprint.NativeSporadic.Carrier .M22) ⟨MulEquiv.refl _⟩).rank
  have hp : IsPGroup 3 (QuotientGroup.mk' (Subgroup.center X)).ker := by
    rw [QuotientGroup.ker_mk']
    rcases hZ with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h]; norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [h]; norm_num)
  exact FFC.ThreeRank2.of_surjective_pgroup_ker (QuotientGroup.mk' (Subgroup.center X))
    (QuotientGroup.mk'_surjective _) hp (hM.of_mulEquiv e.symm)

private theorem res822R4_mem_pCore_iff (L : Subgroup G) {z : G} (hz : z ∈ L) :
    (⟨z, hz⟩ : ↥L) ∈ CFSG.pCore 2 ↥L ↔ z ∈ CFSG.Open.pCoreOf 2 L :=
  res822_mem_pCoreOf_iff L hz

private theorem res822R4_starImage_quot [Finite G] {L M : Subgroup G}
    (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (h3 : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(starImage 3 (L.subgroupOf M)),
      Function.Surjective ψ ∧ ¬ Subsingleton ↥(starImage 3 (L.subgroupOf M)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ρ : ↥L →* PStar 3 ↥M :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)).comp (Subgroup.inclusion hLM)
  have hρrange : ρ.range = starImage 3 (L.subgroupOf M) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hLM k, k.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
  have hO2 : CFSG.pCore 2 ↥L ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (Subgroup.inclusion hLM x) : ↥M ⧸ CFSG.pPrimeCore 3 ↥M) = 1
    rw [QuotientGroup.eq_one_iff]
    have hxO : (x : G) ∈ CFSG.Open.pCoreOf 2 L := (res822R4_mem_pCore_iff L x.2).mp hx
    have hOn : ((CFSG.Open.pCoreOf 2 L).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLM)).mpr
        (hMN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
    have hO3 : Nat.Coprime 3 (Nat.card ↥((CFSG.Open.pCoreOf 2 L).subgroupOf M)) := by
      have h2 : IsPGroup 2 ↥((CFSG.Open.pCoreOf 2 L).subgroupOf M) :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).of_equiv
          (Subgroup.subgroupOfEquivOfLe ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLM)).symm
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
      rw [hn]
      exact Nat.Coprime.pow_right n (by norm_num)
    have hle : (CFSG.Open.pCoreOf 2 L).subgroupOf M ≤ CFSG.pPrimeCore 3 ↥M := le_sSup ⟨hOn, hO3⟩
    exact hle (Subgroup.mem_subgroupOf.mpr hxO)
  let ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(starImage 3 (L.subgroupOf M)) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L)
      (MonoidHom.codRestrict ρ (starImage 3 (L.subgroupOf M)) fun k => by
        rw [← hρrange]
        exact ⟨k, rfl⟩)
      (fun x hx => by
        apply Subtype.ext
        exact MonoidHom.mem_ker.mp (hO2 hx))
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hρrange] at hy
    obtain ⟨k, rfl⟩ := hy
    exact ⟨QuotientGroup.mk k, rfl⟩
  refine ⟨ψ, hψs, ?_⟩
  intro hsub
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥L ⧸ CFSG.pCore 2 ↥L) 3 h3
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) g
  have hk1 : ψ (QuotientGroup.mk' _ k) = 1 := Subsingleton.elim _ _
  have hρk : ρ k = 1 := congrArg Subtype.val hk1
  have hkL : Subgroup.inclusion hLM k ∈ CFSG.pPrimeCore 3 ↥M := (QuotientGroup.eq_one_iff _).mp hρk
  have hcop : Nat.Coprime 3 (Nat.card ↥(CFSG.pPrimeCore 3 ↥M)) :=
    CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥M)
  have hord : orderOf (⟨Subgroup.inclusion hLM k, hkL⟩ : ↥(CFSG.pPrimeCore 3 ↥M)) ∣
      Nat.card ↥(CFSG.pPrimeCore 3 ↥M) := orderOf_dvd_natCard _
  have h3k : 3 ∣ orderOf k := by
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) k
    rw [hg] at h1
    exact h1
  have h3' : 3 ∣ orderOf (⟨Subgroup.inclusion hLM k, hkL⟩ : ↥(CFSG.pPrimeCore 3 ↥M)) := by
    rw [Subgroup.orderOf_mk, orderOf_injective _ (Subgroup.inclusion_injective hLM) k]
    exact h3k
  exact absurd (Nat.Coprime.coprime_dvd_right (h3'.trans hord) hcop) (by norm_num)

theorem input822ThreeInL_of
    (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (h3228 : Stmt3_2_2_eight)
    (h711n : Stmt7_1_1_normal) : Input822ThreeInL := by
  intro G _ _ T L I hyp _ _ hc hrow hrowM _ y hyM hy3
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hLM : L ≤ fsuM T L :=
    (CFSG.Quasithin.Vol2.Ch10.SecA.le_fsuL0 T L).trans (CFSG.Quasithin.Vol2.Ch10.SecA.fsuL0_le_fsuM T L)
  have hMN : fsuM T L ≤ Subgroup.normalizer (L : Set G) :=
    le_of_eq (by show Subgroup.normalizer (fsuL0 T L : Set G) = _; rw [hL0])
  have hMSQ : SQTKGroup ↥(fsuM T L) :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian
      (CFSG.Quasithin.Vol2.Ch10.SecA.pCoreOf_fsuM_ne_bot hyp.fsu.faithful)
  have hLc : L ∈ cComp (fsuM T L) := CFSG.Quasithin.Vol2.Ch10.SecA.mem_cComp_fsuM hyp.fsu.faithful.1
  have hLc' := subgroupOf_mem_cComp hLc
  have hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hyp.fsu.quasisimple
  obtain ⟨eQ⟩ := CFSG.Quasithin.Vol2.Ch11.SecA.quotPCore_subgroupOf_equiv (L := L) hLM
  have hQ' : CFSG.IsQuasisimple (↥(L.subgroupOf (fsuM T L)) ⧸
      CFSG.pCore 2 ↥(L.subgroupOf (fsuM T L))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eQ.symm hQ
  have hM : MathieuCode22 (autOn L (fsuV T I)) ⊤ ⊥ := by
    have h := hrowM
    unfold Row711M22Code at h
    rw [hL0] at h
    exact h
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    obtain ⟨-, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
    rw [hL0] at hN
    exact le_sup_left.trans hN
  have hA := res822_autOn_iso hM
  obtain ⟨ψ0, hψ0s, hkerψ0, -⟩ := res822_psi_of hLV hA hQ
  obtain ⟨eA⟩ := hA
  have eZ : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      CFSG.Blueprint.NativeSporadic.Carrier .M22 :=
    (QuotientGroup.quotientMulEquivOfEq hkerψ0.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective ψ0 hψ0s).trans eA)
  have hSchur : SchurM22 := schurM22_holds
  have hZ : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 1 ∨
      Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 := by
    have hdvd : Nat.card ψ0.ker ∣ 12 :=
      hSchur _ hQ ψ0.ker hkerψ0.le ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ0 hψ0s).trans eA⟩
    have hO : CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := CFSG.Quasithin.B6.pCore_quotient_pCore
    have hodd : ¬ 2 ∣ Nat.card ψ0.ker := res822_not_two_dvd_card_of_central hkerψ0.le hO
    rw [← hkerψ0]
    generalize hk : Nat.card ψ0.ker = k at hdvd hodd ⊢
    have hle : k ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases k <;> omega
  have hTR : FFC.ThreeRank2 (↥L ⧸ CFSG.pCore 2 ↥L) := res822R4_threeRank2 hZ eZ
  have hr : 1 < CFSG.Open.pRank 3 (L.subgroupOf (fsuM T L)) := by
    rw [CFSG.Quasithin.Vol2.Ch11.SecA.pRank_subgroupOf_eq hLM Nat.prime_three (by norm_num)]
    have := hTR.pRank_two_le
    omega
  have hSQ := SQTKHyp.of_sqtkGroup ↥(fsuM T L) hMSQ
  have hconc := CFSG.Quasithin.a318 hF hMSQ (h36 _ hSQ) (h38 _ hSQ) hLc' hQ' Nat.prime_three
    (by norm_num) hr
  have hX3 : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [res822R4_card_X eZ]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨ψ', hψ's, hnt⟩ := res822R4_starImage_quot hLM hMN hX3
  have hcardS := res822R4_card_quotient hQ hZ eZ ψ' hψ's hnt
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, -, h3⟩
  ·
    have hy' : (⟨y, hyM⟩ : ↥(fsuM T L)) ∈ L.subgroupOf (fsuM T L) := by
      rw [h1]
      unfold CFSG.Quasithin.oPrimeResidualOf
      exact Subgroup.subset_closure ⟨Subgroup.mem_top _, 1, by rw [pow_one, Subgroup.orderOf_mk]; exact hy3⟩
    rw [hL0]
    exact Subgroup.mem_subgroupOf.mp hy'
  ·
    exfalso
    obtain ⟨s, q, hmod, hPSL, -⟩ := h2
    rcases hcardS with hc' | hc'
    · exact CFSG.Quasithin.H13.A6.HatM22.false_of_isPSLEps3q hc'
        CFSG.Quasithin.H13.A6.HatM22.l3Free_1330560 hmod hPSL
    · exact CFSG.Quasithin.H13.A6.HatM22.false_of_isPSLEps3q hc' CFSG.Quasithin.l3Free_443520 hmod hPSL
  · rcases h3 with h | h
    ·
      have hy' : (⟨y, hyM⟩ : ↥(fsuM T L)) ∈ L.subgroupOf (fsuM T L) := by
        rw [h]
        unfold CFSG.Quasithin.thetaOf
        exact Subgroup.subset_closure ⟨Subgroup.mem_top _, by rw [Subgroup.orderOf_mk]; exact hy3⟩
      rw [hL0]
      exact Subgroup.mem_subgroupOf.mp hy'
    ·
      exfalso
      obtain ⟨s, q, x, hSL, -⟩ := h
      exact CFSG.Quasithin.H13.A6.HatM22.false_of_isSLEps3 hcardS hSL

theorem res822ThreeCover_holds'
    (h3228 : Stmt3_2_2_eight) (h711n : Stmt7_1_1_normal) (hF : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) : Res822ThreeCover :=
  res822ThreeCover_holds h3228 h711n (input822ThreeInL_of hF h36 h38 h3228 h711n)

theorem res822CoverJ3_holds
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal) (hD15 : D15AsPrintedSQTK)
    (hS316 : AS316SylowNonsolvable) (hD125 : D125NonsolvableSQTK) (hB69 : B69Struct)
    (hM22 : M22Facts822) (hF : A318Facts) (h36 : A36ForSQTK) : Res822CoverJ3 :=
  res822CoverJ3_of h37 h38 h39 h3228 h325 h331 hC58 h317 h711n hD15 hS316 hD125 hB69 hM22
    (input822ThreeInL_of hF h36 h38 h3228 h711n)

end CFSG.Quasithin.H13
