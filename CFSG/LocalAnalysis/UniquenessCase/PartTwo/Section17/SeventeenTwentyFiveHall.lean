module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFiveSteps
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFiveH2
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_T_sup_centSection {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) (hNL : D.M ≤ Subgroup.normalizer (L : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf 2 D.T (D.T ⊔ centSection D.M L (pCoreOf 2 L)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centSection D.M L (pCoreOf 2 L) with hC
  have hCM : C ≤ D.M := centSection_le _ _ _
  have hMnorm : D.M ≤ Subgroup.normalizer (C : Set G) := centSection_le_normalizer hNL
  have hTnorm : D.T ≤ Subgroup.normalizer (C : Set G) := D.sylowM.le.trans hMnorm
  have hSylC : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ C) C :=
    D.sylowM.inf_of_le_normalizer hCM hMnorm
  have hoddC : ¬ 2 ∣ (D.T ⊓ C).relIndex C :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hSylC).2.2
  have hsup : Nat.card ↥(D.T ⊔ C) * Nat.card ↥(D.T ⊓ C) =
      Nat.card ↥D.T * Nat.card ↥C :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hTnorm
  have hCcard : Nat.card ↥C = (D.T ⊓ C).relIndex C * Nat.card ↥(D.T ⊓ C) := by
    have h := Subgroup.relIndex_mul_card (H := D.T ⊓ C) (K := C)
    rw [inf_of_le_left (inf_le_right : D.T ⊓ C ≤ C)] at h
    exact h.symm
  have hYcard : Nat.card ↥(D.T ⊔ C) = Nat.card ↥D.T * (D.T ⊓ C).relIndex C := by
    have hpos : Nat.card ↥(D.T ⊓ C) ≠ 0 := (Nat.card_pos (α := ↥(D.T ⊓ C))).ne'
    rw [hCcard] at hsup
    refine mul_right_cancel₀ hpos ?_
    calc Nat.card ↥(D.T ⊔ C) * Nat.card ↥(D.T ⊓ C)
        = Nat.card ↥D.T * ((D.T ⊓ C).relIndex C * Nat.card ↥(D.T ⊓ C)) := hsup
      _ = Nat.card ↥D.T * (D.T ⊓ C).relIndex C * Nat.card ↥(D.T ⊓ C) := by ring
  have hrel : D.T.relIndex (D.T ⊔ C) = (D.T ⊓ C).relIndex C := by
    have h := Subgroup.relIndex_mul_card (H := D.T) (K := D.T ⊔ C)
    rw [inf_of_le_left (le_sup_left : D.T ≤ D.T ⊔ C)] at h
    rw [hYcard] at h
    refine mul_right_cancel₀ ((Nat.card_pos (α := ↥D.T)).ne') ?_
    rw [h, mul_comm (Nat.card ↥D.T) ((D.T ⊓ C).relIndex C)]
  exact (CFSG.ABGLocalTools.isSylowOf_iff).mpr
    ⟨le_sup_left, D.sylowM.isPGroup, by rw [hrel]; exact hoddC⟩

theorem exists_H2_of_J2
    {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h17_20 : R17_20At D V₀ V) (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (hSg : UC6S846.SigmaStd D) (h880 : F08.R880 D) (hJ2aut : K_J2_aut_five_rank)
    (hJ2 : IsSpor (Bar2 L) .J2) (hsig : D.sig = {5}) :
    ∃ H₂ : Subgroup G, D.T ≤ H₂ ∧
      H₂ ≤ D.T ⊔ centSection D.M L (pCoreOf 2 L) ∧ D.T.relIndex H₂ = 5 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hN : (L.subgroupOf D.M).Normal := (h17_20 L c).2.1
  have hNL : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 hN
  set C : Subgroup G := centSection D.M L (pCoreOf 2 L) with hCdef
  set Y : Subgroup G := D.T ⊔ C with hYdef
  have hTY : D.T ≤ Y := le_sup_left
  have hCY : C ≤ Y := le_sup_right
  have hYsolv : Group.IsSolvable ↥Y := solvable_sup_T_centSection hNL h17_22 h17_23 c
  have h5C : 5 ∣ Nat.card ↥C := five_dvd_centSection hNL hJ2 hJ2aut hSg hsig
  have h5Y : 5 ∣ Nat.card ↥Y := by
    have h1 : 5 ∣ Nat.card ↥(C.subgroupOf Y) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCY).toEquiv]
      exact h5C
    exact h1.trans (Subgroup.card_subgroup_dvd_card (C.subgroupOf Y))
  have hYrank : CFSG.Open.pRank 5 Y ≤ 1 :=
    pRank_five_sup_le_one hNL hJ2 hJ2aut hSg hsig h880 h17_22 h17_23 c
  have hSylY : CFSG.ABGLocalTools.IsSylowOf 2 D.T Y := isSylowOf_T_sup_centSection c hNL
  let primes25 : Set Nat.Primes := {q : Nat.Primes | (q : ℕ) = 2 ∨ (q : ℕ) = 5}
  have hTY2 : IsPGroup 2 (D.T.subgroupOf Y) :=
    D.sylowM.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hTY).symm
  have hTYpi : IsPiSubgroup primes25 (D.T.subgroupOf Y) := by
    intro q hq
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hTY2
    have hq2 : (q : ℕ) = 2 := by
      have hdvd : (q : ℕ) ∣ 2 ^ k := by rw [← hk]; exact hq
      exact (Nat.prime_dvd_prime_iff_eq q.2 Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow q.2 hdvd)
    exact Or.inl hq2
  obtain ⟨R, hR, hTR⟩ :=
    CFSG.SolvableHall.solvable_hall_containment hYsolv primes25 (D.T.subgroupOf Y) hTYpi
  have hRsolv : Group.IsSolvable ↥R :=
    Group.isSolvable_of_isSolvable_injective (f := R.subtype) R.subtype_injective
  have hRindex5 : ¬ 5 ∣ R.index := fun h5 =>
    hR.p_in_pi_of_p_dvd_index ⟨5, Nat.prime_five⟩ h5 (Or.inr rfl)
  have h5R : 5 ∣ Nat.card ↥R := by
    have h := Subgroup.index_mul_card R
    have hdvd : 5 ∣ R.index * Nat.card ↥R := by
      rw [h]; exact h5Y
    exact (Nat.Prime.dvd_mul Nat.prime_five).mp hdvd |>.resolve_left hRindex5
  let NR : Subgroup ↥R := CFSG.pCore 2 ↥R
  have hNRnormal : NR.Normal := CFSG.pCore_normal (p := 2) (G := ↥R)
  have hNR2 : IsPGroup 2 NR := CFSG.pCore_isPGroup (p := 2) (G := ↥R)
  have hNR5 : ¬ 5 ∣ Nat.card ↥NR := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hNR2
    rw [hk]
    intro hd
    exact (by norm_num : ¬ (5 : ℕ) ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd)
  let Rbar := ↥R ⧸ NR
  let piR : ↥R →* Rbar := QuotientGroup.mk' NR
  have hRbar_solv : Group.IsSolvable Rbar := inferInstance
  have h5Rbar : 5 ∣ Nat.card Rbar := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup NR
    have hdvd : 5 ∣ Nat.card Rbar * Nat.card ↥NR := by rw [← h]; exact h5R
    exact (Nat.Prime.dvd_mul Nat.prime_five).mp hdvd |>.resolve_right hNR5
  have hRbar_nt : Nontrivial Rbar := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    exact lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd Nat.card_pos h5Rbar)
  have hTYindex : ¬ 2 ∣ (D.T.subgroupOf Y).index :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hSylY).2.2
  have hTR2 : IsPGroup 2 ((D.T.subgroupOf Y).subgroupOf R) :=
    hTY2.of_equiv (Subgroup.subgroupOfEquivOfLe hTR).symm
  have hTRindex : ¬ 2 ∣ ((D.T.subgroupOf Y).subgroupOf R).index := by
    intro h2
    have hmul := Subgroup.relIndex_mul_index (H := D.T.subgroupOf Y) (K := R) hTR
    have hrel : (D.T.subgroupOf Y).relIndex R = ((D.T.subgroupOf Y).subgroupOf R).index := by
      simp [Subgroup.relIndex, sup_eq_right.mpr hTR]
    rw [hrel] at hmul
    exact hTYindex (h2.trans (hmul ▸ dvd_mul_right _ _ : _ ∣ (D.T.subgroupOf Y).index))
  have hRbar_rank : CFSG.Open.pRank 5 (⊤ : Subgroup Rbar) ≤ 1 := by
    have hquot := CFSG.SectionRank.pRank_quotient_eq (p := 5) NR hNR5
    have hRY : CFSG.Open.pRank 5 R ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥Y) :=
      CFSG.SectionRank.pRank_mono (by norm_num) le_top
    have htop : CFSG.Open.pRank 5 (⊤ : Subgroup ↥Y) = CFSG.Open.pRank 5 Y :=
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup Y).symm
    rw [hquot, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup R]
    exact hRY.trans (htop.le.trans hYrank)
  have hO2Rbar : CFSG.pCore 2 Rbar = ⊥ := by
    have hmap := CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker (p := 2) piR
      (QuotientGroup.mk'_surjective NR) (by rwa [QuotientGroup.ker_mk'])
    rw [← hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  obtain ⟨Mb, hMbNormal, hMbNe, hMbMin⟩ :=
    CFSG.exists_minimal_normal (G := Rbar) hRbar_solv hRbar_nt
  have : Mb.Normal := hMbNormal
  have : IsMinimalNormal Mb :=
    { minimal := fun K hK hle => by
        by_cases h : K = ⊥
        · exact Or.inl h
        · exact Or.inr (hMbMin K hK hle h) }
  have : Group.IsSolvable ↥Mb :=
    Group.isSolvable_of_isSolvable_injective (f := Mb.subtype) Mb.subtype_injective
  obtain ⟨p, hp, hElem⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian Mb
  have hMb1 : 1 < Nat.card ↥Mb := (Subgroup.one_lt_card_iff_ne_bot (H := Mb)).2 hMbNe
  have hp_dvd_Mb : p ∣ Nat.card ↥Mb := by
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥Mb) (by omega)
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥Mb) q hqdvd
    have hxp : (x : ↥Mb) ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p ↥Mb) x
    have hqdp : q ∣ p := by rw [← hxord]; exact orderOf_dvd_of_pow_eq_one hxp
    rw [← (Nat.prime_dvd_prime_iff_eq hq hp).mp hqdp]
    exact hqdvd
  have hp_dvd_R : p ∣ Nat.card ↥R :=
    (hp_dvd_Mb.trans (Subgroup.card_subgroup_dvd_card Mb)).trans
      (Subgroup.card_quotient_dvd_card NR)
  have hp25 : p = 2 ∨ p = 5 := by
    have hmem : ((⟨p, hp⟩ : Nat.Primes) : ℕ) = 2 ∨ ((⟨p, hp⟩ : Nat.Primes) : ℕ) = 5 :=
      hR.p_in_pi_of_p_dvd_card ⟨p, hp⟩ hp_dvd_R
    simpa using hmem
  have hp5 : p = 5 := by
    rcases hp25 with h2 | h5
    · exfalso
      have hMb2 : IsPGroup 2 ↥Mb := by
        rw [h2] at hElem
        exact IsElementaryAbelian.isPGroup 2 ↥Mb
      have hle : Mb ≤ CFSG.pCore 2 Rbar := le_sSup ⟨hMbNormal, hMb2⟩
      rw [hO2Rbar] at hle
      exact hMbNe (le_bot_iff.mp hle)
    · exact h5
  subst hp5
  have hMb5el : CFSG.Open.IsElemAbelian 5 (Mb : Subgroup Rbar) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 5 Mb).mp hElem
  have hMbcard_pow : Nat.card ↥Mb = 5 ^ CFSG.Open.pRank 5 Mb :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_five hMb5el
  have hrankMb : CFSG.Open.pRank 5 Mb ≤ CFSG.Open.pRank 5 (⊤ : Subgroup Rbar) :=
    CFSG.SectionRank.pRank_mono (by norm_num) le_top
  have hMbcard : Nat.card ↥Mb = 5 := by
    have hle : Nat.card ↥Mb ≤ 5 := by
      rw [hMbcard_pow]
      calc 5 ^ CFSG.Open.pRank 5 Mb ≤ 5 ^ 1 :=
            Nat.pow_le_pow_right (by norm_num) (hrankMb.trans hRbar_rank)
        _ = 5 := pow_one 5
    have hge : 5 ≤ Nat.card ↥Mb := Nat.le_of_dvd Nat.card_pos hp_dvd_Mb
    omega
  let Tbar : Subgroup Rbar := ((D.T.subgroupOf Y).subgroupOf R).map piR
  have hTbar2 : IsPGroup 2 Tbar := hTR2.map piR
  have hKbar_card : Nat.card ↥(Tbar ⊔ Mb) = 5 * Nat.card ↥Tbar := by
    have hMbT : Disjoint Mb Tbar := by
      refine Subgroup.disjoint_of_coprime_natCard ?_
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hTbar2
      rw [hMbcard, hk]
      exact Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 5 2)
    have hnorm : Tbar ≤ Subgroup.normalizer (Mb : Set Rbar) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hMbNormal]
      exact le_top
    have h :=
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Mb Tbar hnorm hMbT
    rw [sup_comm, h, hMbcard]
  have hNleTR : NR ≤ (D.T.subgroupOf Y).subgroupOf R :=
    IsPGroup.le_sylow_of_normal (N := NR) hNR2 (hTR2.toSylow hTRindex)
  have hTRcard : Nat.card ↥((D.T.subgroupOf Y).subgroupOf R) =
      Nat.card ↥NR * Nat.card ↥Tbar := by
    have hker : piR.ker = NR := QuotientGroup.ker_mk' NR
    have hrel := Subgroup.relIndex_ker (f := piR) (K := (D.T.subgroupOf Y).subgroupOf R)
    rw [hker] at hrel
    have hmul := Subgroup.relIndex_mul_card (H := NR) (K := (D.T.subgroupOf Y).subgroupOf R)
    rw [inf_of_le_left hNleTR, hrel] at hmul
    rw [hmul.symm, mul_comm]
  have hDTcard : Nat.card ↥((D.T.subgroupOf Y).subgroupOf R) = Nat.card ↥D.T := by
    have e1 : ↥((D.T.subgroupOf Y).subgroupOf R) ≃* ↥(D.T.subgroupOf Y) :=
      Subgroup.subgroupOfEquivOfLe hTR
    have e2 : ↥(D.T.subgroupOf Y) ≃* ↥D.T := Subgroup.subgroupOfEquivOfLe hTY
    exact Nat.card_congr (e1.trans e2).toEquiv
  have hKcard : Nat.card ↥((Tbar ⊔ Mb).comap piR) =
      Nat.card ↥NR * Nat.card ↥(Tbar ⊔ Mb) := by
    have hker : piR.ker = NR := QuotientGroup.ker_mk' NR
    have hrel := Subgroup.relIndex_ker (f := piR) (K := (Tbar ⊔ Mb).comap piR)
    rw [hker, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective NR)] at hrel
    have hle : NR ≤ (Tbar ⊔ Mb).comap piR :=
      hker.symm.le.trans (MonoidHom.ker_le_comap piR (Tbar ⊔ Mb))
    have hmul := Subgroup.relIndex_mul_card (H := NR) (K := (Tbar ⊔ Mb).comap piR)
    rw [inf_of_le_left hle, hrel] at hmul
    rw [hmul.symm, mul_comm]
  have hKfinal : Nat.card ↥((Tbar ⊔ Mb).comap piR) = 5 * Nat.card ↥D.T := by
    have hNT : Nat.card ↥NR * Nat.card ↥Tbar = Nat.card ↥D.T :=
      hTRcard.symm.trans hDTcard
    rw [hKcard, hKbar_card, ← hNT]
    ring
  have hTR_le_K : (D.T.subgroupOf Y).subgroupOf R ≤ (Tbar ⊔ Mb).comap piR := by
    intro x hx
    exact Subgroup.mem_comap.mpr
      (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem piR hx))
  have hTY_le_K : D.T.subgroupOf Y ≤ ((Tbar ⊔ Mb).comap piR).map R.subtype := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hTR hx⟩, hTR_le_K (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hTH2 : D.T ≤ (((Tbar ⊔ Mb).comap piR).map R.subtype).map Y.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hTY]
    exact Subgroup.map_mono hTY_le_K
  have hH2Y : (((Tbar ⊔ Mb).comap piR).map R.subtype).map Y.subtype ≤ Y :=
    Subgroup.map_subtype_le (H := Y) (K := ((Tbar ⊔ Mb).comap piR).map R.subtype)
  have hH2card : Nat.card ↥((((Tbar ⊔ Mb).comap piR).map R.subtype).map Y.subtype) =
      5 * Nat.card ↥D.T := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective,
      Subgroup.card_map_of_injective R.subtype_injective, hKfinal]
  refine ⟨_, hTH2, hH2Y, ?_⟩
  have hmul := Subgroup.relIndex_mul_card (H := D.T)
    (K := (((Tbar ⊔ Mb).comap piR).map R.subtype).map Y.subtype)
  rw [inf_of_le_left hTH2, hH2card] at hmul
  exact mul_right_cancel₀ ((Nat.card_pos (α := ↥D.T)).ne') hmul

theorem gap17_25_H2_hall_of
    {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h17_20 : R17_20At D V₀ V) (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (hSg : UC6S846.SigmaStd D) (h880 : F08.R880 D)
    (hJ2aut : K_J2_aut_five_rank) :
    Gap17_25_H2_hall D V₀ V L c.hyp125.isElemAbelian := by
  intro _hV0 _hP hJ2 hsig
  exact exists_H2_of_J2 c h17_20 h17_22 h17_23 hSg h880 hJ2aut hJ2 hsig

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
