module

public import CFSG.RankThree.PartTwo.Sec17.PropUStepFour
public import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofInner
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofHJList

public section

namespace CFSG.RankThree.PartTwo.Sec17.PropU

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def rho148 (A K : Subgroup G) [(ker148 A K).Normal] :
    ↥K →* ↥(K ⊔ A) ⧸ ker148 A K :=
  (QuotientGroup.mk' (ker148 A K)).comp (Subgroup.inclusion le_sup_left)

theorem ker_rho148 (A K : Subgroup G) [(ker148 A K).Normal] :
    (rho148 A K).ker = CFSG.pPrimeCore 3 ↥K := by
  ext x
  rw [MonoidHom.mem_ker, rho148, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, ker148, Subgroup.mem_subgroupOf, pPrimeCoreOf]
  exact Subgroup.mem_map_iff_mem K.subtype_injective

theorem img148_eq_map (A K X : Subgroup G) [(ker148 A K).Normal] (hXK : X ≤ K) :
    img148 A K X = (X.subgroupOf K).map (rho148 A K) := by
  ext q
  rw [img148, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hy
    refine ⟨⟨(y : G), hXK hy⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hy
    · rfl
  · rintro ⟨k, hk, rfl⟩
    refine ⟨Subgroup.inclusion (le_sup_left : K ≤ K ⊔ A) k, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_subgroupOf.mp hk

theorem pu_card_map_mul_card_inf_ker {L Q : Type} [Group L] [Group Q] (S : Subgroup L)
    (ρ : L →* Q) :
    Nat.card ↥(S.map ρ) * Nat.card ↥(S ⊓ ρ.ker) = Nat.card ↥S := by
  have hr : (ρ.comp S.subtype).range = S.map ρ := by
    rw [← MonoidHom.map_range, Subgroup.range_subtype]
  have hk : (ρ.comp S.subtype).ker = ρ.ker.comap S.subtype := rfl
  have e1 : (ρ.comp S.subtype).ker.map S.subtype = S ⊓ ρ.ker := by
    rw [hk, Subgroup.map_comap_eq, Subgroup.range_subtype]
  have hc : Nat.card ↥(ρ.comp S.subtype).ker = Nat.card ↥(S ⊓ ρ.ker) := by
    rw [← e1, Subgroup.card_map_of_injective S.subtype_injective]
  have h := Subgroup.card_ker_mul_card_range (ρ.comp S.subtype)
  rw [hr, hc, mul_comm] at h
  exact h

theorem card_map_mul_card_inf {K H : Subgroup G} {Q : Type} [Group Q] (ρ : ↥K →* Q)
    (hρ : ρ.ker = CFSG.pPrimeCore 3 ↥K) (hHK : H ≤ K) :
    Nat.card ↥((H.subgroupOf K).map ρ) * Nat.card ↥(H ⊓ pPrimeCoreOf 3 K) = Nat.card ↥H := by
  have h1 := pu_card_map_mul_card_inf_ker (H.subgroupOf K) ρ
  rw [hρ] at h1
  have e : Subgroup.map K.subtype (H.subgroupOf K ⊓ CFSG.pPrimeCore 3 ↥K)
      = H ⊓ pPrimeCoreOf 3 K := by
    rw [Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hHK]
    rfl
  have h2 : Nat.card ↥(H ⊓ pPrimeCoreOf 3 K)
      = Nat.card ↥(H.subgroupOf K ⊓ CFSG.pPrimeCore 3 ↥K) := by
    rw [← e, Subgroup.card_map_of_injective K.subtype_injective]
  have h3 : Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  rw [h2, ← h3]
  exact h1

theorem pPrimeCoreOf_eq_inf {K F : Subgroup G} (hFK : F ≤ K)
    (hKF : K ≤ Subgroup.normalizer (F : Set G)) :
    pPrimeCoreOf 3 F = F ⊓ pPrimeCoreOf 3 K := by
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  ·
    refine le_inf (CFSG.RankThree.PartTwo.Sec14.pPrimeCoreOf_le 3 F) ?_
    exact CFSG.RankThree.PartTwo.Sec14.le_pPrimeCoreOf
      ((CFSG.RankThree.PartTwo.Sec14.pPrimeCoreOf_le 3 F).trans hFK)
      (hKF.trans (CFSG.RankThree.PartTwo.Sec14.normalizer_le_normalizer_pPrimeCoreOf 3 F))
      (CFSG.RankThree.PartTwo.Sec14.coprime_card_pPrimeCoreOf 3 F)
  ·
    have hnorm : F ≤ Subgroup.normalizer ((F ⊓ pPrimeCoreOf 3 K : Subgroup G) : Set G) :=
      (le_inf Subgroup.le_normalizer
        (hFK.trans (CFSG.RankThree.PartTwo.Sec14.le_normalizer_pPrimeCoreOf 3 K))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hcop : Nat.Coprime 3 (Nat.card ↥(F ⊓ pPrimeCoreOf 3 K : Subgroup G)) :=
      Nat.Coprime.of_dvd_right
        (Subgroup.card_dvd_of_le (inf_le_right : F ⊓ pPrimeCoreOf 3 K ≤ pPrimeCoreOf 3 K))
        (CFSG.RankThree.PartTwo.Sec14.coprime_card_pPrimeCoreOf 3 K)
    exact CFSG.RankThree.PartTwo.Sec14.le_pPrimeCoreOf inf_le_left hnorm hcop

theorem card_quotient_pPrimeCore_mul (F : Subgroup G) :
    Nat.card (↥F ⧸ CFSG.pPrimeCore 3 ↥F) * Nat.card ↥(pPrimeCoreOf 3 F) = Nat.card ↥F := by
  rw [pPrimeCoreOf, Subgroup.card_map_of_injective F.subtype_injective]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pPrimeCore 3 ↥F)).symm

theorem inf_le_pCoreOf_two {M X : Subgroup G}
    (hXM : X ≤ Subgroup.normalizer (M : Set G)) (hM3 : ¬ 3 ∣ Nat.card M)
    (hX3 : oPrimeResidualOf 3 X = X) (hXJ : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* J2)) :
    X ⊓ M ≤ CFSG.Open.pCoreOf 2 X := by
  have hX3' : oPrimeResidual 3 ↥X = ⊤ := by
    have h : (oPrimeResidual 3 ↥X).map X.subtype = (⊤ : Subgroup ↥X).map X.subtype := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
      exact hX3
    exact Subgroup.map_injective X.subtype_injective h
  obtain ⟨e⟩ := hXJ
  haveI : IsSimpleGroup J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  haveI : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X) := e.isSimpleGroup
  haveI : (M.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXM
  rcases normal_le_or_eq_top (CFSG.pCore 2 ↥X) CFSG.pCore_isPGroup inferInstance hX3'
    (M.subgroupOf X) with hK | hK
  · intro g hg
    obtain ⟨hgX, hgM⟩ := Subgroup.mem_inf.mp hg
    have hmem : (⟨g, hgX⟩ : ↥X) ∈ M.subgroupOf X := Subgroup.mem_subgroupOf.mpr hgM
    exact (pu_mem_pCoreOf_iff (⟨g, hgX⟩ : ↥X)).mpr (hK hmem)
  · exfalso
    have hXM' : X ≤ M := by
      intro x hx
      have hmem : (⟨x, hx⟩ : ↥X) ∈ M.subgroupOf X := by
        rw [hK]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    have hq : Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = 604800 := by
      rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2]
    have h3X : 3 ∣ Nat.card ↥X := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X), hq]
      exact dvd_mul_of_dvd_left (by norm_num) _
    exact hM3 (h3X.trans (Subgroup.card_dvd_of_le hXM'))

theorem eq_of_mem_lA {A : Subgroup G} {c : G} {L : Subgroup G} (hch : Chosen136 A)
    (hΩ : omegaA A = {Subgroup.zpowers c}) (hL : L ∈ lA A c) (h3 : 3 ∣ Nat.card L) {c' : G}
    (hc' : Subgroup.zpowers c' ∈ omegaA A) {L' : Subgroup G} (hL' : L' ∈ lA A c') : L' = L := by
  have hc'eq : Subgroup.zpowers c' = Subgroup.zpowers c := by
    rw [hΩ] at hc'
    exact Set.mem_singleton_iff.mp hc'
  have hL'c : L' ∈ lA A c := by
    have h := CFSG.RankThree.PartTwo.Sec14.lA_eq_of_zpowers_eq (A := A) hc'eq
    rw [h] at hL'
    exact hL'
  have hcΩ : Subgroup.zpowers c ∈ omegaA A := by
    rw [hΩ]
    exact Set.mem_singleton _
  have hK := hch.2 c hcΩ L' hL'c
  exact (hK.2 L hL.1 h3).symm

theorem not_isoLThreePi_of_equiv_J2 {X : Type} [Group X]
    (h : Nonempty (X ≃* J2)) (p e : ℕ) [Fact p.Prime] : ¬ Sec4.IsoLThreePi X p e := by
  obtain ⟨f⟩ := h
  intro hX
  rcases hX with ⟨h1, ⟨g⟩⟩ | ⟨h2, ⟨g⟩⟩
  · exact CFSG.RankThree.PartTwo.KFacts.KS14.ks17J2NotList.1 p e
      (Or.inl ⟨h1, ⟨f.symm.trans g⟩⟩)
  · exact CFSG.RankThree.PartTwo.KFacts.KS14.ks17J2NotList.1 p e
      (Or.inr ⟨h2, ⟨f.symm.trans g⟩⟩)

theorem not_isLThreeEpsAt_of_equiv_J2 {X : Type} [Group X]
    (h : Nonempty (X ≃* J2)) (p f : ℕ) [Fact p.Prime] : ¬ IsLThreeEpsAt X p f := by
  obtain ⟨φ⟩ := h
  intro hX
  rcases hX with ⟨⟨g⟩⟩ | ⟨h2, ⟨g⟩⟩
  · exact CFSG.RankThree.PartTwo.KFacts.KS14.not_isLThreeEpsAt_j2 p f (Or.inl ⟨φ.symm.trans g⟩)
  · exact CFSG.RankThree.PartTwo.KFacts.KS14.not_isLThreeEpsAt_j2 p f
      (Or.inr ⟨h2, ⟨φ.symm.trans g⟩⟩)

theorem isEmpty_equiv_small_of_equiv_J2 {X : Type} [Group X]
    (h : Nonempty (X ≃* J2)) :
    IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧
      IsEmpty (X ≃* CFSG.Blueprint.NativeSporadic.M22) ∧
      (∀ _ : Fact (Nat.Prime 5), IsEmpty (X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∧
      (∀ _ : Fact (Nat.Prime 5), IsEmpty (X ≃* CFSG.Assembly.RankThreeEven.projSU 3 5 1)) := by
  obtain ⟨φ⟩ := h
  refine ⟨⟨fun g => ?_⟩, ⟨fun g => ?_⟩, fun _ => ⟨fun g => ?_⟩, fun _ => ⟨fun g => ?_⟩⟩
  · exact CFSG.RankThree.PartTwo.KFacts.KS14.ks17J2NotList.2.1.false (φ.symm.trans g)
  · exact CFSG.RankThree.PartTwo.KFacts.KS14.ks17J2NotList.2.2.false (φ.symm.trans g)
  · exact CFSG.RankThree.PartTwo.KFacts.KS14.not_isLThreeEpsAt_j2 5 2 (Or.inl ⟨φ.symm.trans g⟩)
  · exact CFSG.RankThree.PartTwo.KFacts.KS14.not_isLThreeEpsAt_j2 5 1
      (Or.inr ⟨by norm_num, ⟨φ.symm.trans g⟩⟩)

theorem isEmpty_equiv_alt_ten_of_equiv_J2 {X : Type} [Group X]
    (h : Nonempty (X ≃* J2)) : IsEmpty (X ≃* alternatingGroup (Fin 10)) := by
  obtain ⟨φ⟩ := h
  refine ⟨fun g => ?_⟩
  have hc := Nat.card_congr (φ.symm.trans g).toEquiv
  rw [CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2,
    CFSG.RankThree.PartTwo.KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2] at hc
  norm_num at hc

theorem pu_card_sup_mul_card_inf {Y : Type} [Group Y] (U V : Subgroup Y) [U.Normal] :
    Nat.card ↥(U ⊔ V) * Nat.card ↥(U ⊓ V) = Nat.card ↥U * Nat.card ↥V := by
  have h1 : U.relIndex (U ⊔ V) * Nat.card ↥U = Nat.card ↥(U ⊔ V) := by
    have h := Subgroup.relIndex_mul_card (H := U) (K := U ⊔ V)
    rwa [inf_eq_left.mpr (le_sup_left : U ≤ U ⊔ V)] at h
  have h2 : U.relIndex V * Nat.card ↥(U ⊓ V) = Nat.card ↥V :=
    Subgroup.relIndex_mul_card (H := U) (K := V)
  have h3 : U.relIndex (U ⊔ V) = U.relIndex V := by
    rw [sup_comm]
    exact Subgroup.relIndex_sup_right (H := V) (K := U)
  rw [← h1, ← h2, h3]
  ring

theorem not_dvd_card_of_case148 {Y : Type} [Group Y]
    (h : Sec4.IsTripleCover Y (alternatingGroup (Fin 6)) ∨ Nonempty (Y ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover Y CFSG.Blueprint.NativeSporadic.ON ∨ IsCentralProductA6Covers Y ∨
      IsA6CoverTimesA5 Y ∨ Nonempty (Y ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∨
      Nonempty (Y ≃* alternatingGroup (Fin 7)) ∨
      (∃ _ : Fact (Nat.Prime 7), Nonempty (Y ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))) :
    ¬ 604800 ∣ Nat.card Y := by
  rcases h with h | h | h | h | h | h | h | h
  ·
    rw [CFSG.RankThree.PartTwo.Sec14.HJRes2.card_of_isTripleCover_six h]
    omega
  ·
    obtain ⟨φ⟩ := h
    rw [Nat.card_congr φ.toEquiv,
      CFSG.RankThree.PartTwo.KFacts.KS14.card_alternatingGroup_five_seven_ten.1]
    omega
  ·
    rw [CFSG.RankThree.PartTwo.Sec14.HJRes2.card_of_isTripleCover_ON h]
    omega
  ·
    obtain ⟨U, V, hUn, hVn, hsup, _, hcard3, hU, hV⟩ := h
    have hU' := CFSG.RankThree.PartTwo.Sec14.HJRes2.card_of_isTripleCover_six hU
    have hV' := CFSG.RankThree.PartTwo.Sec14.HJRes2.card_of_isTripleCover_six hV
    have key := pu_card_sup_mul_card_inf U V
    rw [hsup, Subgroup.card_top, hcard3, hU', hV'] at key
    omega
  ·
    obtain ⟨U, V, hUn, hVn, hinf, hsup, hU, hV⟩ := h
    obtain ⟨φ⟩ := hV
    have hU' := CFSG.RankThree.PartTwo.Sec14.HJRes2.card_of_isTripleCover_six hU
    have hV' := Nat.card_congr φ.toEquiv
    rw [CFSG.RankThree.PartTwo.KFacts.KS14.card_alternatingGroup_five_seven_ten.1] at hV'
    have key := pu_card_sup_mul_card_inf U V
    rw [hsup, Subgroup.card_top, hinf, Subgroup.card_bot, hU', hV'] at key
    omega
  ·
    obtain ⟨φ⟩ := h
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod,
      CFSG.RankThree.PartTwo.KFacts.KS14.card_alternatingGroup_five_seven_ten.1]
    omega
  ·
    obtain ⟨φ⟩ := h
    rw [Nat.card_congr φ.toEquiv,
      CFSG.RankThree.PartTwo.KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    omega
  ·
    obtain ⟨hp, ⟨φ⟩⟩ := h
    haveI := hp
    rw [Nat.card_congr φ.toEquiv, CFSG.RankThree.PartTwo.Sec15.Proof1515.card_projSL_three_seven]
    omega

theorem X_image_facts {K X : Subgroup G} {Q : Type} [Group Q]
    (ρ : ↥K →* Q) (hρ : ρ.ker = CFSG.pPrimeCore 3 ↥K) (hXK : X ≤ K)
    (hX3 : oPrimeResidualOf 3 X = X) (hXJ : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* J2)) :
    X ⊓ pPrimeCoreOf 3 K ≤ CFSG.Open.pCoreOf 2 X ∧
      Nat.card ↥((X.subgroupOf K).map ρ) * Nat.card ↥(X ⊓ pPrimeCoreOf 3 K) =
        604800 * Nat.card ↥(CFSG.Open.pCoreOf 2 X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXN : X ≤ Subgroup.normalizer ((pPrimeCoreOf 3 K : Subgroup G) : Set G) :=
    hXK.trans (le_normalizer_pPrimeCoreOf 3 K)
  have hM3 : ¬ 3 ∣ Nat.card ↥(pPrimeCoreOf 3 K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
  refine ⟨inf_le_pCoreOf_two hXN hM3 hX3 hXJ, ?_⟩
  rw [card_map_mul_card_inf ρ hρ hXK]
  obtain ⟨e⟩ := hXJ
  have h1 : Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = 604800 :=
    (Nat.card_congr e.toEquiv).trans CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X)
  rw [h1] at h2
  have h3 : Nat.card ↥(CFSG.Open.pCoreOf 2 X) = Nat.card ↥(CFSG.pCore 2 ↥X) :=
    Subgroup.card_map_of_injective X.subtype_injective
  rw [h3]
  exact h2

theorem pc_abs {K D F X : Subgroup G} {Q : Type} [Group Q] [Finite Q]
    (ρ : ↥K →* Q) (hρ : ρ.ker = CFSG.pPrimeCore 3 ↥K) (hDK : D ≤ K) (hFD : F ≤ D)
    (hKF : K ≤ Subgroup.normalizer (F : Set G)) (hXF : X ≤ F)
    (hX3 : oPrimeResidualOf 3 X = X) (hXJ : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* J2))
    (hJ : Nat.card ↥((D.subgroupOf K).map ρ) = 604800) :
    Nat.card (↥F ⧸ CFSG.pPrimeCore 3 ↥F) = 604800 ∧
      X ⊓ pPrimeCoreOf 3 F = CFSG.Open.pCoreOf 2 X := by
  have hXD : X ≤ D := hXF.trans hFD
  have hFK : F ≤ K := hFD.trans hDK
  have hXK : X ≤ K := hXD.trans hDK
  obtain ⟨hXN, hXcard⟩ := X_image_facts ρ hρ hXK hX3 hXJ
  set N := pPrimeCoreOf 3 K with hN
  have hkm : Nat.card ↥(X ⊓ N) ∣ Nat.card ↥(CFSG.Open.pCoreOf 2 X) := Subgroup.card_dvd_of_le hXN
  obtain ⟨t, ht⟩ := hkm
  have hkpos : 0 < Nat.card ↥(X ⊓ N) := Nat.card_pos
  have hsub : ∀ {S T : Subgroup G}, S ≤ T → S.subgroupOf K ≤ T.subgroupOf K := fun h x hx => h hx
  have hmono : (X.subgroupOf K).map ρ ≤ (D.subgroupOf K).map ρ :=
    Subgroup.map_mono (hsub hXD)
  have hr_le : Nat.card ↥((X.subgroupOf K).map ρ) ≤ 604800 := by
    rw [← hJ]
    exact Subgroup.card_le_of_le hmono
  set r := Nat.card ↥((X.subgroupOf K).map ρ) with hr
  set k := Nat.card ↥(X ⊓ N) with hk
  have hrt : r = 604800 * t := by
    have h1 : r * k = 604800 * (k * t) := by rw [hXcard, ht]
    have h2 : r * k = (604800 * t) * k := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hkpos h2
  have ht1 : t = 1 := by
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · exfalso
        rw [h0, mul_zero] at ht
        have : 0 < Nat.card ↥(CFSG.Open.pCoreOf 2 X) := Nat.card_pos
        omega
      · exact h0
    have : 604800 * t ≤ 604800 := hrt ▸ hr_le
    omega
  have hr604 : r = 604800 := by rw [hrt, ht1]
  have hXNeq : X ⊓ N = CFSG.Open.pCoreOf 2 X := by
    refine Subgroup.eq_of_le_of_card_ge hXN ?_
    rw [ht, ht1, mul_one]
  have hmonoF : (F.subgroupOf K).map ρ ≤ (D.subgroupOf K).map ρ :=
    Subgroup.map_mono (hsub hFD)
  have hmonoXF : (X.subgroupOf K).map ρ ≤ (F.subgroupOf K).map ρ :=
    Subgroup.map_mono (hsub hXF)
  have hF604 : Nat.card ↥((F.subgroupOf K).map ρ) = 604800 := by
    refine le_antisymm (hJ ▸ Subgroup.card_le_of_le hmonoF) ?_
    rw [← hr604]
    exact Subgroup.card_le_of_le hmonoXF
  have hFcard := card_map_mul_card_inf ρ hρ hFK
  rw [hF604] at hFcard
  have hFN : pPrimeCoreOf 3 F = F ⊓ N := pPrimeCoreOf_eq_inf hFK hKF
  have hq := card_quotient_pPrimeCore_mul F
  rw [hFN] at hq
  have hFpos : 0 < Nat.card ↥(F ⊓ N) := Nat.card_pos
  refine ⟨?_, ?_⟩
  · have h2 : Nat.card (↥F ⧸ CFSG.pPrimeCore 3 ↥F) * Nat.card ↥(F ⊓ N) = 604800 * Nat.card ↥(F ⊓ N) := by
      rw [hq, hFcard]
    exact Nat.eq_of_mul_eq_mul_right hFpos h2
  · rw [hFN, ← inf_assoc, inf_eq_left.mpr hXF]
    exact hXNeq

section Item148Binders


theorem case148_j2 {A : Subgroup G}
    {c : G} {L K : Subgroup G} [(ker148 A K).Normal] (hcases : Item148Cases A (lB A) K)
    (hch : Chosen136 A) (hΩ : omegaA A = {Subgroup.zpowers c}) (hL : L ∈ lA A c)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* J2))
    (hdiv : 604800 ∣ Nat.card ↥(img148 A K (deltaZero A (lB A) K))) :
    Nonempty (↥(img148 A K (deltaZero A (lB A) K)) ≃* J2) := by
  classical
  have h3L : 3 ∣ Nat.card L := by
    obtain ⟨e⟩ := hJ
    have h1 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∣ Nat.card L :=
      Subgroup.card_quotient_dvd_card _
    rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2] at h1
    exact (by norm_num : 3 ∣ 604800).trans h1
  have hLJ : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* J2) := by
    intro c' L' hc' hL'
    rw [eq_of_mem_lA hch hΩ hL h3L hc' hL']
    exact hJ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    exfalso
    have hbot : img148 A K (deltaZero A (lB A) K) = ⊥ := by
      unfold img148
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      intro x hx
      exact h1 hx
    rw [hbot, Subgroup.card_bot] at hdiv
    omega
  ·
    obtain ⟨c', hc', -, L', hL', hcase⟩ := h2
    have hJL' := hLJ c' L' hc' hL'
    rcases hcase with h2i | ⟨hM, -⟩ | ⟨p, f, e, hp, -, -, hπ, -⟩ | ⟨-, h2iv⟩
    · exact ⟨h2i.some.trans hJL'.some⟩
    · exfalso
      rcases hM with hM | ⟨hp5, hM⟩ | ⟨hp5, hM⟩
      · exact (isEmpty_equiv_small_of_equiv_J2 hJL').2.1.false hM.some
      · exact ((isEmpty_equiv_small_of_equiv_J2 hJL').2.2.1 hp5).false hM.some
      · exact ((isEmpty_equiv_small_of_equiv_J2 hJL').2.2.2 hp5).false hM.some
    · exfalso
      haveI := hp
      exact not_isoLThreePi_of_equiv_J2 hJL' p (f * e) hπ
    · exfalso
      rcases h2iv with h | h
      · exact not_dvd_card_of_case148 (Or.inl h) hdiv
      · exact not_dvd_card_of_case148 (Or.inr (Or.inl h)) hdiv
  ·
    exfalso
    obtain ⟨c', d, L', hc', hL', hJ', -, -, -, -, h3⟩ := h3
    exact not_dvd_card_of_case148 (Or.inr (Or.inr h3)) hdiv
  ·
    exfalso
    obtain ⟨-, ⟨c', L', hc', hL', hA7⟩, -⟩ := h4
    exact (isEmpty_equiv_small_of_equiv_J2 (hLJ c' L' hc' hL')).1.false hA7.some
  ·
    exfalso
    obtain ⟨c', hcA, L', n, m, hc', hL', -, -, -, -, -, -, hEps, -⟩ := h5
    exact not_isLThreeEpsAt_of_equiv_J2 (hLJ c' L' hc' hL') 2 (n * m) hEps
  ·
    exfalso
    obtain ⟨-, -, h6⟩ := h6
    rw [hΩ, Set.ncard_singleton] at h6
    omega
  ·
    exfalso
    obtain ⟨a₁, a₂, L₁, L₂, J₁, J₂, p₁, f₁, e₁, p₂, f₂, e₂, hp₁, hp₂, ha₁, ha₂, hL₁, hL₂, -, -, -,
      -, -, -, -, -, -, -, -, hπ₁, hπ₂⟩ := h7
    haveI := hp₁
    exact not_isoLThreePi_of_equiv_J2 (hLJ a₁ L₁ ha₁ hL₁) p₁ (f₁ * e₁) hπ₁

end Item148Binders

theorem pu_oPrimeResidualOf_mono {p : ℕ} {K K' : Subgroup G} (h : K ≤ K') :
    oPrimeResidualOf p K ≤ oPrimeResidualOf p K' := by
  rw [oPrimeResidualOf_eq_closure, oPrimeResidualOf_eq_closure]
  exact Subgroup.closure_mono fun x ⟨hx, k, hk⟩ => ⟨h hx, k, hk⟩

theorem X_image_dvd {K X : Subgroup G} {Q : Type} [Group Q]
    (ρ : ↥K →* Q) (hρ : ρ.ker = CFSG.pPrimeCore 3 ↥K) (hXK : X ≤ K)
    (hX3 : oPrimeResidualOf 3 X = X) (hXJ : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* J2)) :
    604800 ∣ Nat.card ↥((X.subgroupOf K).map ρ) := by
  obtain ⟨hXN, hXcard⟩ := X_image_facts ρ hρ hXK hX3 hXJ
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hXN
  have hkpos : 0 < Nat.card ↥(X ⊓ pPrimeCoreOf 3 K) := Nat.card_pos
  have h1 : Nat.card ↥((X.subgroupOf K).map ρ) * Nat.card ↥(X ⊓ pPrimeCoreOf 3 K) =
      (604800 * t) * Nat.card ↥(X ⊓ pPrimeCoreOf 3 K) := by
    rw [hXcard, ht]; ring
  exact ⟨t, Nat.eq_of_mul_eq_mul_right hkpos h1⟩

section Item148Binders


theorem lemma33 {A : Subgroup G}
    {c : G} {L Y₀ : Subgroup G} (hs : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* J2))
    (hYJ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* J2))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h148 : Item148 A (lB A))
    (h149 : Item149 A (lB A)) {X K : Subgroup G} (hX4 : X ∈ scriptY4 A (lB A))
    (hXJ : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* J2)) (hK : K ∈ scriptY A) (hXK : X ≤ K) :
    K ≤ Subgroup.normalizer ((oPrimeResidualOf 3 (delta A (lB A) K) : Subgroup G) : Set G) ∧
      X ≤ oPrimeResidualOf 3 (delta A (lB A) K) ∧
      Nat.card (↥(oPrimeResidualOf 3 (delta A (lB A) K)) ⧸
        CFSG.pPrimeCore 3 ↥(oPrimeResidualOf 3 (delta A (lB A) K))) = 604800 ∧
      X ⊓ pPrimeCoreOf 3 (oPrimeResidualOf 3 (delta A (lB A) K)) = CFSG.Open.pCoreOf 2 X := by
  classical
  haveI := ker148_normal hK.2
  set F := oPrimeResidualOf 3 (delta A (lB A) K) with hF
  set D := deltaZero A (lB A) K with hD
  have hDK : D ≤ K := deltaZero_le K
  obtain ⟨e1, n1, -, -⟩ := h149 K hK
  have hFD : F ≤ D := by
    rw [hF, e1]
    exact (oPrimeResidualOf_le_self 3 _).trans (inSubgroup_oResidual_le_self 2 _)
  have hFK : F ≤ K := hFD.trans hDK
  have hKF : K ≤ Subgroup.normalizer (F : Set G) := by
    have hle : oPrimeResidualOf 3 (inSubgroup (oResidual 2) (deltaZero A (lB A) K)) ≤ K := by
      rw [← e1]; exact hFK
    have := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp n1
    rw [hF, e1]
    exact this
  have hX3 : oPrimeResidualOf 3 X = X := hX4.2.1.symm
  have hXF : X ≤ F := by
    have hXΔ : X ≤ delta A (lB A) K := by
      calc X = delta A (lB A) X := hX4.2.2.1
        _ ≤ delta A (lB A) K := delta_mono hXK
    calc X = oPrimeResidualOf 3 X := hX3.symm
      _ ≤ oPrimeResidualOf 3 (delta A (lB A) K) := pu_oPrimeResidualOf_mono hXΔ
  have hXD : X ≤ D := by
    calc X = deltaZero A (lB A) X := rank3II_15_1_lB hs.isE27 hbot hX4
      _ ≤ D := deltaZero_mono hXK
  set ρ := rho148 A K with hρdef
  have hρ : ρ.ker = CFSG.pPrimeCore 3 ↥K := ker_rho148 A K
  have himg : img148 A K D = (D.subgroupOf K).map ρ := img148_eq_map A K D hDK
  have hsub : ∀ {S T : Subgroup G}, S ≤ T → S.subgroupOf K ≤ T.subgroupOf K := fun h x hx => h hx
  have hdiv : 604800 ∣ Nat.card ↥(img148 A K D) := by
    rw [himg]
    exact (X_image_dvd ρ hρ hXK hX3 hXJ).trans
      (Subgroup.card_dvd_of_le (Subgroup.map_mono (hsub hXD)))
  have hΩ : omegaA A = {Subgroup.zpowers c} := by
    rcases hs.a10_or_omega with he | h
    · exact ((isEmpty_equiv_alt_ten_of_equiv_J2 hYJ).false he.some).elim
    · exact h
  have hcases : Item148Cases A (lB A) K := (h148 K hK).2
  have hiso := case148_j2 hcases hs.chosen136 hΩ hs.mem_lA hJ hdiv
  have hcardJ : Nat.card ↥((D.subgroupOf K).map ρ) = 604800 := by
    rw [← himg]
    obtain ⟨e⟩ := hiso
    rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2]
  obtain ⟨h1, h2⟩ := pc_abs ρ hρ hDK hFD hKF hXF hX3 hXJ hcardJ
  exact ⟨hKF, hXF, h1, h2⟩

end Item148Binders

end CFSG.RankThree.PartTwo.Sec17.PropU
