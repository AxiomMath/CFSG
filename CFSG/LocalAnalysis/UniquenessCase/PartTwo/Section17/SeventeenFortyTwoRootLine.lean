module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SevenTwoL2Section
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SevenTwoSimpleSection
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.UniqueSetOfCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRank
public import CFSG.GroupTheory.PElementSubgroup
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42Bar
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]


private theorem pRank_top_bar2_lt_of_pRank_eq_two {X M : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.Open.pRank p M)
    (hcaseA : CFSG.Open.pRank p X = 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (Bar2 X)) < CFSG.Open.pRank p M := by
  have : Fact p.Prime := ⟨hp⟩
  have hcop : ¬ p ∣ Nat.card ↥(CFSG.pCore 2 ↥X) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup
      (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) hp hp2
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 X)) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥X) :=
    CFSG.SectionRank.pRank_quotient_eq (p := p) (CFSG.pCore 2 ↥X) hcop
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup ↥X) = CFSG.Open.pRank p X :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup X).symm
  omega

private theorem dvd_card_quotient_of_isL2 {Yt : Subgroup G} {N₀ : Subgroup ↥Yt} {p n : ℕ}
    (hN₀ : N₀.Normal)
    (hL2 : @IsL2 (↥Yt ⧸ N₀) (@QuotientGroup.Quotient.group _ _ N₀ hN₀) n)
    (hpn : p ∣ 2 ^ (2 * n) - 1) :
    p ∣ Nat.card (↥Yt ⧸ N₀) := by
  have hcard : Nat.card (↥Yt ⧸ N₀) = 2 ^ n * (4 ^ n - 1) :=
    (CFSG.Quasithin.H13.D42.card_of_lieModel_PSL2 hL2).1
  rw [hcard]
  have h4 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
    calc (4 : ℕ) ^ n = (2 ^ 2) ^ n := by norm_num
      _ = 2 ^ (2 * n) := by rw [pow_mul]
  rw [h4]
  exact hpn.trans (dvd_mul_left _ _)

private theorem dvd_card_inf_centralizer_of_rootLine
    {D : Data G} {X : Subgroup G} {p n r : ℕ}
    (hp : p ∈ D.sig) (h3 : 3 ≤ CFSG.Open.pRank p D.M)
    (hOp : UC22.F10.OpRes p D.M = D.M)
    (hZ : Subgroup.center (Bar2 X) = ⊥) (hOut : IsCyclic (Outer (Bar2 X)))
    (hr : r.Prime) (hr2 : r ≠ 2) (hX : X = Opp r D.M)
    (hcase : CFSG.Open.pRank p X = 2 ∨ IsU4 (Bar2 X) n)
    (hroot : ∀ E : Subgroup G, E ≤ X → IsElemAbelian r E → Nat.card E = r ^ 2 →
      ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = r ∧
        (∃ Yt : Subgroup G, Yt ≤ X ⊓ Subgroup.centralizer (B : Set G) ∧
          ∃ N₀ : Subgroup ↥Yt, ∃ hN : N₀.Normal,
            @IsL2 (↥Yt ⧸ N₀) (@QuotientGroup.Quotient.group _ _ N₀ hN) n) ∧
        (IsU4 (Bar2 X) n →
          2 ≤ CFSG.Open.pRank p (X ⊓ Subgroup.centralizer (B : Set G)) ∧
          p ∣ Nat.card ↥(X ⊓ Subgroup.centralizer (E : Set G))))
    {E : Subgroup G} (hED : E ≤ D.M) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) :
    p ∣ Nat.card ↥(D.M ⊓ Subgroup.centralizer (E : Set G)) := by
  classical
  have hp' : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  haveI : Fact p.Prime := ⟨hp'⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hXM : X ≤ D.M := by
    rw [hX]
    exact CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le r D.M
  have hMN : D.M ≤ Subgroup.normalizer (X : Set G) := by
    rw [hX]
    exact CFSG.LocalAnalysis.RankThreeUC.le_normalizer_pElementSubgroup r D.M
  have hEX : E ≤ X := by
    rw [hX]
    exact CFSG.le_pElementSubgroup_of_isPGroup hr hEel.isPGroup hED
  rcases hcase with hcaseA | hcaseB
  ·
    have hrankBar : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 X)) < CFSG.Open.pRank p D.M :=
      pRank_top_bar2_lt_of_pRank_eq_two hp' hp2 h3 hcaseA
    obtain ⟨S, hSle, hSp, hSne, hSc⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_isPGroup_le_centralizer_centOverO2
        hXM hMN hZ hOut hp' hp2 hOp hrankBar hr hr2 hEX hEel.isPGroup
    have hSD : S ≤ D.M := fun x hx =>
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp (hSle hx)).1
    have hSinf : S ≤ D.M ⊓ Subgroup.centralizer (E : Set G) := le_inf hSD hSc
    have hSdvd : p ∣ Nat.card ↥S := by
      rcases hSp.card_eq_or_dvd with h1 | h1
      · exact absurd (Subgroup.card_eq_one.mp h1) hSne
      · exact h1
    exact hSdvd.trans (Subgroup.card_dvd_of_le hSinf)
  ·
    obtain ⟨B, -, -, -, hU4⟩ := hroot E hEX hEel hEcard
    refine (hU4 hcaseB).2.trans (Subgroup.card_dvd_of_le ?_)
    exact inf_le_inf_right _ hXM

private theorem one_lt_pRank_centralizer_of_pRank_eq_two
    {D : Data G} {X : Subgroup G} {p n r : ℕ}
    (hp : p ∈ D.sig) (h3 : 3 ≤ CFSG.Open.pRank p D.M)
    (hOp : UC22.F10.OpRes p D.M = D.M)
    (hZ : Subgroup.center (Bar2 X) = ⊥) (hOut : IsCyclic (Outer (Bar2 X)))
    (hr : r.Prime) (hr2 : r ≠ 2) (hX : X = Opp r D.M)
    (hcaseA : CFSG.Open.pRank p X = 2)
    {E B Yt : Subgroup G} {N₀ : Subgroup ↥Yt}
    (hN₀ : N₀.Normal)
    (hL2 : @IsL2 (↥Yt ⧸ N₀) (@QuotientGroup.Quotient.group _ _ N₀ hN₀) n)
    (hpn : p ∣ 2 ^ (2 * n) - 1)
    (hBE : B ≤ E)
    (hYt : Yt ≤ X ⊓ Subgroup.centralizer (B : Set G))
    (hEX : E ≤ X) (hEel : IsElemAbelian r E) :
    1 < CFSG.Open.pRank p (Subgroup.centralizer (B : Set G) ⊓ D.M) := by
  classical
  have hp' : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  haveI : Fact p.Prime := ⟨hp'⟩
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : N₀.Normal := hN₀
  have hYtX : Yt ≤ X := hYt.trans inf_le_left
  have hYtC : Yt ≤ Subgroup.centralizer (B : Set G) := hYt.trans inf_le_right
  have hXM : X ≤ D.M := by
    rw [hX]
    exact CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le r D.M
  have hMN : D.M ≤ Subgroup.normalizer (X : Set G) := by
    rw [hX]
    exact CFSG.LocalAnalysis.RankThreeUC.le_normalizer_pElementSubgroup r D.M
  have hDM_O2 : D.M ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    hMN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hrankBar : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 X)) < CFSG.Open.pRank p D.M :=
    pRank_top_bar2_lt_of_pRank_eq_two hp' hp2 h3 hcaseA
  obtain ⟨S, hSle, hSp, hSne, hSc⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_isPGroup_le_centralizer_centOverO2
      hXM hMN hZ hOut hp' hp2 hOp hrankBar hr hr2 hEX hEel.isPGroup
  have hSD : S ≤ D.M := fun x hx =>
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp (hSle hx)).1
  have hScB : S ≤ Subgroup.centralizer (B : Set G) :=
    hSc.trans (Subgroup.centralizer_le (fun x hx => hBE hx))
  have hSdvd : p ∣ Nat.card ↥S := by
    rcases hSp.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hSne
    · exact h1
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) p hSdvd
  have hy₀G : orderOf ((y₀ : ↥S) : G) = p := by
    rw [Subgroup.orderOf_coe]
    exact hy₀
  set K : Subgroup G := Subgroup.centralizer (B : Set G) ⊓ D.M with hKdef
  set U : Subgroup G := pCoreOf 2 X ⊓ K with hUdef
  have hSK : S ≤ K := le_inf hScB hSD
  have hUK : U ≤ K := inf_le_right
  have hKD : K ≤ D.M := inf_le_right
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := by
    have h1 : K ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := hKD.trans hDM_O2
    exact (le_inf h1 Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hUnorm : (U.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKU
  haveI : (U.subgroupOf K).Normal := hUnorm
  have hUp : IsPGroup 2 U := by
    have h := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype
    exact h.to_inf_left
  have hUp' : IsPGroup 2 ↥(U.subgroupOf K) :=
    hUp.of_equiv (Subgroup.subgroupOfEquivOfLe hUK).symm
  have hNp : ¬ p ∣ Nat.card ↥(U.subgroupOf K) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hUp' hp' hp2
  have hSpK : IsPGroup p ↥(S.subgroupOf K) :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  have hcommU : ∀ s : ↥K, (s : G) ∈ S → ∀ t : ↥K, (t : G) ∈ Yt →
      (s : ↥K) * (t : ↥K) * (s : ↥K)⁻¹ * (t : ↥K)⁻¹ ∈ U.subgroupOf K := by
    intro s hs t ht
    have hst : (s : G) * (t : G) * (s : G)⁻¹ * (t : G)⁻¹ ∈ pCoreOf 2 X :=
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp (hSle hs)).2 (t : G)
        (hYtX ht)
    have hstK : (s : G) * (t : G) * (s : G)⁻¹ * (t : G)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem s.2 t.2) (K.inv_mem s.2)) (K.inv_mem t.2)
    exact ⟨hst, hstK⟩
  have hYtcent : (Yt.subgroupOf K).map (QuotientGroup.mk' (U.subgroupOf K)) ≤
      Subgroup.centralizer (((S.subgroupOf K).map (QuotientGroup.mk' (U.subgroupOf K))) :
        Set (↥K ⧸ U.subgroupOf K)) := by
    rintro z hz
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ha
    have hmem := hcommU s (Subgroup.mem_subgroupOf.mp hs) t (Subgroup.mem_subgroupOf.mp ht)
    have h2 : QuotientGroup.mk' (U.subgroupOf K) ((s : ↥K) * (t : ↥K)) =
        QuotientGroup.mk' (U.subgroupOf K) ((t : ↥K) * (s : ↥K)) := by
      have h3 : QuotientGroup.mk' (U.subgroupOf K) ((s : ↥K) * (t : ↥K)) *
          (QuotientGroup.mk' (U.subgroupOf K) ((t : ↥K) * (s : ↥K)))⁻¹ = 1 := by
        rw [← map_inv, ← map_mul]
        exact (QuotientGroup.eq_one_iff _).mpr (by convert hmem using 1; group)
      exact mul_inv_eq_one.mp h3
    calc QuotientGroup.mk' (U.subgroupOf K) s * QuotientGroup.mk' (U.subgroupOf K) t
        = QuotientGroup.mk' (U.subgroupOf K) ((s : ↥K) * (t : ↥K)) := (map_mul _ _ _).symm
      _ = QuotientGroup.mk' (U.subgroupOf K) ((t : ↥K) * (s : ↥K)) := h2
      _ = QuotientGroup.mk' (U.subgroupOf K) t * QuotientGroup.mk' (U.subgroupOf K) s :=
          map_mul _ _ _
  have hmapcent := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime
    (p := p) (U.subgroupOf K) hNp (S.subgroupOf K) hSpK
  have hpN0 : p ∣ Nat.card (↥Yt ⧸ N₀) := dvd_card_quotient_of_isL2 hN₀ hL2 hpn
  have hpYt : p ∣ Nat.card ↥Yt := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N₀]
    exact dvd_mul_of_dvd_left hpN0 _
  have hcardA : Nat.card ↥(Yt.subgroupOf K) =
      Nat.card ↥((Yt.subgroupOf K).map (QuotientGroup.mk' (U.subgroupOf K))) *
      Nat.card ↥((Yt.subgroupOf K) ⊓ (QuotientGroup.mk' (U.subgroupOf K)).ker) :=
    CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker _ _
  have hker : (QuotientGroup.mk' (U.subgroupOf K)).ker = U.subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker]
    exact QuotientGroup.eq_one_iff x
  have hpker : ¬ p ∣
      Nat.card ↥((Yt.subgroupOf K) ⊓ (QuotientGroup.mk' (U.subgroupOf K)).ker) := by
    rw [hker]
    exact fun hd => hNp (hd.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hYtK : Yt ≤ K := le_inf hYtC (hYtX.trans hXM)
  have hpYt' : p ∣ Nat.card ↥(Yt.subgroupOf K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYtK).toEquiv]
    exact hpYt
  have hpimg : p ∣ Nat.card ↥((Yt.subgroupOf K).map (QuotientGroup.mk' (U.subgroupOf K))) := by
    have h := hpYt'
    rw [hcardA] at h
    exact (hp'.dvd_mul.mp h).resolve_right hpker
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥((Yt.subgroupOf K).map (QuotientGroup.mk' (U.subgroupOf K)))) p hpimg
  have hzcent : ((z : ↥((Yt.subgroupOf K).map (QuotientGroup.mk' (U.subgroupOf K)))) :
      ↥K ⧸ U.subgroupOf K) ∈ Subgroup.centralizer
        (((S.subgroupOf K).map (QuotientGroup.mk' (U.subgroupOf K))) :
          Set (↥K ⧸ U.subgroupOf K)) :=
    hYtcent z.2
  have hzmem : ((z : ↥((Yt.subgroupOf K).map (QuotientGroup.mk' (U.subgroupOf K)))) :
      ↥K ⧸ U.subgroupOf K) ∈
      (Subgroup.centralizer ((S.subgroupOf K) : Set ↥K)).map
        (QuotientGroup.mk' (U.subgroupOf K)) := by
    rw [hmapcent]
    exact hzcent
  obtain ⟨c, hc, hcφ⟩ := Subgroup.mem_map.mp hzmem
  have hcφz : QuotientGroup.mk' (U.subgroupOf K) c =
      (z : ↥K ⧸ U.subgroupOf K) := hcφ
  have hzordG : orderOf (z : ↥K ⧸ U.subgroupOf K) = p := by
    rw [Subgroup.orderOf_coe]
    exact hzord
  have hpdvd_c : p ∣ orderOf c := by
    have h1 : orderOf (QuotientGroup.mk' (U.subgroupOf K) c) ∣ orderOf c :=
      orderOf_map_dvd _ c
    rw [hcφz, hzordG] at h1
    exact h1
  have hcp_mem : c ^ p ∈ U.subgroupOf K := by
    have h1 : QuotientGroup.mk' (U.subgroupOf K) (c ^ p) = 1 := by
      rw [map_pow, hcφz, ← hzordG, pow_orderOf_eq_one]
    exact (QuotientGroup.eq_one_iff (c ^ p)).mp h1
  have hordcp : orderOf (c ^ p) = orderOf c / p := by
    rw [orderOf_pow, Nat.gcd_eq_right hpdvd_c]
  have hordc : orderOf c = p * orderOf (c ^ p) := by
    rw [hordcp]
    exact (Nat.mul_div_cancel' hpdvd_c).symm
  have hm_pos : 0 < orderOf (c ^ p) := orderOf_pos _
  have hxm : orderOf (c ^ orderOf (c ^ p)) = p := by
    rw [orderOf_pow]
    have hgcd : Nat.gcd (orderOf c) (orderOf (c ^ p)) = orderOf (c ^ p) := by
      rw [hordc]
      exact Nat.gcd_eq_right (dvd_mul_left _ p)
    rw [hgcd, hordc, mul_comm p (orderOf (c ^ p)), Nat.mul_div_right _ hm_pos]
  have hcX : (c : G) ∈ X := by
    obtain ⟨t₀, ht₀, hφt₀⟩ := Subgroup.mem_map.mp z.2
    have hmem : c⁻¹ * t₀ ∈ U.subgroupOf K := by
      have h1 : QuotientGroup.mk' (U.subgroupOf K) (c⁻¹ * t₀) = 1 := by
        rw [map_mul, map_inv, hcφz]
        rw [← hφt₀, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff (c⁻¹ * t₀)).mp h1
    have huX : (((c⁻¹ * t₀ : ↥K) : G)) ∈ X :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
        (Subgroup.mem_subgroupOf.mp hmem).1
    have htX : ((t₀ : ↥K) : G) ∈ X := hYtX (Subgroup.mem_subgroupOf.mp ht₀)
    have hceq : (c : G) = ((t₀ : ↥K) : G) * ((((c⁻¹ * t₀ : ↥K) : G)))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hceq]
    exact X.mul_mem htX (X.inv_mem huX)
  have hxX : ((c ^ orderOf (c ^ p) : ↥K) : G) ∈ X := by
    rw [Subgroup.coe_pow]
    exact X.pow_mem hcX _
  have hcS : ∀ s : ↥(S.subgroupOf K), (c : ↥K) * s = s * (c : ↥K) := by
    intro s
    exact (Subgroup.mem_centralizer_iff.mp hc s s.2).symm
  have hcy : (c : G) * ((y₀ : ↥S) : G) = ((y₀ : ↥S) : G) * (c : G) := by
    have hyK : ((y₀ : ↥S) : G) ∈ K := hSK (y₀ : ↥S).2
    let yK : ↥(S.subgroupOf K) :=
      ⟨⟨((y₀ : ↥S) : G), hyK⟩, Subgroup.mem_subgroupOf.mpr (y₀ : ↥S).2⟩
    have h := hcS yK
    have h' := congrArg (fun z : ↥K => (z : G)) h
    simpa [yK, mul_comm] using h'
  have hxy : ((c ^ orderOf (c ^ p) : ↥K) : G) * ((y₀ : ↥S) : G) =
      ((y₀ : ↥S) : G) * ((c ^ orderOf (c ^ p) : ↥K) : G) := by
    have hcomm : Commute (c : G) ((y₀ : ↥S) : G) := hcy
    have h := (hcomm.pow_left (orderOf (c ^ p))).eq
    rw [Subgroup.coe_pow]
    exact h
  have hy_not : ((y₀ : ↥S) : G) ∉ Subgroup.zpowers ((c ^ orderOf (c ^ p) : ↥K) : G) := by
    intro hy
    have hyX : ((y₀ : ↥S) : G) ∈ X := (Subgroup.zpowers_le.mpr hxX) hy
    have hyCent : ((y₀ : ↥S) : G) ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.F08.CentOverO2 D.M X :=
      hSle (y₀ : ↥S).2
    have hcenter : (QuotientGroup.mk (⟨((y₀ : ↥S) : G), hyX⟩ : ↥X) : Bar2 X) ∈
        Subgroup.center (Bar2 X) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨zq, rfl⟩ := QuotientGroup.mk_surjective q
      have hmem : zq * (⟨((y₀ : ↥S) : G), hyX⟩ : ↥X) *
          ((⟨((y₀ : ↥S) : G), hyX⟩ : ↥X) * zq)⁻¹ ∈ CFSG.pCore 2 ↥X := by
        have h1 := (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp hyCent).2
          (zq : G) zq.2
        obtain ⟨w, hw, hwG⟩ := Subgroup.mem_map.mp h1
        have hweq : zq * (⟨((y₀ : ↥S) : G), hyX⟩ : ↥X) *
            ((⟨((y₀ : ↥S) : G), hyX⟩ : ↥X) * zq)⁻¹ = (⟨(w : G), w.2⟩ : ↥X)⁻¹ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [show (w : G) = ((y₀ : ↥S) : G) * (zq : G) * (((y₀ : ↥S) : G))⁻¹ * (zq : G)⁻¹
            from hwG]
          group
        rw [hweq]
        exact (CFSG.pCore 2 ↥X).inv_mem hw
      have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) zq *
          QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨((y₀ : ↥S) : G), hyX⟩ : ↥X) =
          QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨((y₀ : ↥S) : G), hyX⟩ : ↥X) *
            QuotientGroup.mk' (CFSG.pCore 2 ↥X) zq := by
        have h3 : QuotientGroup.mk' (CFSG.pCore 2 ↥X)
              (zq * (⟨((y₀ : ↥S) : G), hyX⟩ : ↥X)) *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥X)
              ((⟨((y₀ : ↥S) : G), hyX⟩ : ↥X) * zq))⁻¹ = 1 := by
          rw [← map_inv, ← map_mul]
          exact (QuotientGroup.eq_one_iff _).mpr hmem
        exact mul_inv_eq_one.mp h3
      exact h2
    rw [hZ, Subgroup.mem_bot] at hcenter
    have hyO2 : ((y₀ : ↥S) : G) ∈ pCoreOf 2 X := by
      have h1 : (⟨((y₀ : ↥S) : G), hyX⟩ : ↥X) ∈ CFSG.pCore 2 ↥X :=
        (QuotientGroup.eq_one_iff _).mp hcenter
      exact Subgroup.mem_map_of_mem X.subtype h1
    have h2grp : IsPGroup 2 (pCoreOf 2 X) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype
    have hpdvd : p ∣ Nat.card ↥(pCoreOf 2 X) := by
      have h := Subgroup.orderOf_dvd_natCard (pCoreOf 2 X) hyO2
      rwa [hy₀G] at h
    exact (CFSG.GroupTheory.not_dvd_card_of_isPGroup h2grp hp' hp2) hpdvd
  have hxcard : Nat.card ↥(Subgroup.zpowers ((c ^ orderOf (c ^ p) : ↥K) : G)) = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe]
    exact hxm
  have hcomm_zp : ∀ a ∈ Subgroup.zpowers ((c ^ orderOf (c ^ p) : ↥K) : G),
      a * ((y₀ : ↥S) : G) = ((y₀ : ↥S) : G) * a := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hcomm : Commute ((c ^ orderOf (c ^ p) : ↥K) : G) ((y₀ : ↥S) : G) := hxy
    exact (hcomm.zpow_left k).eq
  obtain ⟨hEel', hEcard'⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    hxcard hy₀G hy_not hcomm_zp
  have hxK : ((c ^ orderOf (c ^ p) : ↥K) : G) ∈ K := (c ^ orderOf (c ^ p) : ↥K).2
  have hyK : ((y₀ : ↥S) : G) ∈ K := hSK (y₀ : ↥S).2
  have hle : Subgroup.zpowers ((c ^ orderOf (c ^ p) : ↥K) : G) ⊔
      Subgroup.zpowers ((y₀ : ↥S) : G) ≤ K :=
    sup_le (Subgroup.zpowers_le.mpr hxK) (Subgroup.zpowers_le.mpr hyK)
  have h2 : 2 ≤ CFSG.Open.pRank p K :=
    CFSG.SectionRank.le_pRank hp'.one_lt hle hEel' (by rw [hEcard'])
  exact h2

theorem exists_mem_uniqueSet_rootLine
    {D : Data G} {X : Subgroup G} {p n r : ℕ}
    (h72 : F07.R72 D) (hK35 : UCK.K35w)
    (hp : p ∈ D.sig) (hsp : IsStronglyPEmbedded p D.M) (h3 : 3 ≤ CFSG.Open.pRank p D.M)
    (hOp : UC22.F10.OpRes p D.M = D.M) (hn : 3 ≤ n) (hpn : p ∣ 2 ^ n + 1)
    (hZ : Subgroup.center (Bar2 X) = ⊥) (hOut : IsCyclic (Outer (Bar2 X)))
    (hr : r.Prime) (hr2 : r ≠ 2) (hX : X = Opp r D.M)
    (hcase : CFSG.Open.pRank p X = 2 ∨ IsU4 (Bar2 X) n)
    (hroot : ∀ E : Subgroup G, E ≤ X → IsElemAbelian r E → Nat.card E = r ^ 2 →
      ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = r ∧
        (∃ Yt : Subgroup G, Yt ≤ X ⊓ Subgroup.centralizer (B : Set G) ∧
          ∃ N₀ : Subgroup ↥Yt, ∃ hN : N₀.Normal,
            @IsL2 (↥Yt ⧸ N₀) (@QuotientGroup.Quotient.group _ _ N₀ hN) n) ∧
        (IsU4 (Bar2 X) n →
          2 ≤ CFSG.Open.pRank p (X ⊓ Subgroup.centralizer (B : Set G)) ∧
          p ∣ Nat.card ↥(X ⊓ Subgroup.centralizer (E : Set G))))
    {E : Subgroup G} (hEX : E ≤ X) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) :
    ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = r ∧ Subgroup.centralizer (B : Set G) ≤ D.M ∧
      B ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
  classical
  have hp' : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  haveI : Fact p.Prime := ⟨hp'⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hXM : X ≤ D.M := by
    rw [hX]
    exact CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le r D.M
  have hpn' : p ∣ 2 ^ (2 * n) - 1 := by
    rw [CFSG.Timmesfeld.IsPrimitivePrimeDivisor.two_pow_two_mul_sub_one]
    exact dvd_mul_of_dvd_right hpn _
  have hS1 : ∀ E' : Subgroup G, E' ≤ D.M → IsElemAbelian r E' → Nat.card E' = r ^ 2 →
      p ∣ Nat.card ↥(D.M ⊓ Subgroup.centralizer (E' : Set G)) :=
    fun E' hE'D hE'el hE'card =>
      dvd_card_inf_centralizer_of_rootLine hp h3 hOp hZ hOut hr hr2 hX hcase hroot
        hE'D hE'el hE'card
  obtain ⟨B, hBE, hBcard, ⟨Yt, hYt, N₀, hN₀, hL2⟩, hU4⟩ := hroot E hEX hEel hEcard
  have hYtX : Yt ≤ X := hYt.trans inf_le_left
  have hYtC : Yt ≤ Subgroup.centralizer (B : Set G) := hYt.trans inf_le_right
  have hBD : B ≤ D.M := hBE.trans (hEX.trans hXM)
  have hrankB : 1 < CFSG.Open.pRank p (Subgroup.centralizer (B : Set G) ⊓ D.M) := by
    rcases hcase with hcaseA | hcaseB
    · exact one_lt_pRank_centralizer_of_pRank_eq_two hp h3 hOp hZ hOut hr hr2 hX hcaseA
        hN₀ hL2 hpn' hBE hYt hEX hEel
    · have h2 : 2 ≤ CFSG.Open.pRank p (Subgroup.centralizer (B : Set G) ⊓ D.M) := by
        refine le_trans (hU4 hcaseB).1 (CFSG.SectionRank.pRank_mono hp'.one_lt ?_)
        rw [inf_comm]
        exact inf_le_inf_left _ hXM
      omega
  have hcent : Subgroup.centralizer (B : Set G) ≤ D.M := by
    by_contra hHle
    set H : Subgroup G := Subgroup.centralizer (B : Set G) with hHdef
    haveI hGsimple : IsSimpleGroup G := D.standing.simple
    have hHtop : H ≠ ⊤ := by
      intro htop
      have hBcenter : B ≤ Subgroup.center G := by
        intro b hb
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ H := by rw [htop]; exact Subgroup.mem_top g
        exact (Subgroup.mem_centralizer_iff.mp hg b hb).symm
      have hne : Subgroup.center G ≠ ⊥ := by
        intro hbot
        have hle : B ≤ ⊥ := hbot ▸ hBcenter
        have h1 : Nat.card ↥B = 1 := by
          rw [show B = ⊥ from le_bot_iff.mp hle]
          exact Subgroup.card_bot
        rw [hBcard] at h1
        exact hr.ne_one h1
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hbot | htop'
      · exact hne hbot
      · haveI : IsMulCommutative G := by
          refine ⟨⟨fun a b => ?_⟩⟩
          have ha : a ∈ Subgroup.center G := by rw [htop']; exact Subgroup.mem_top a
          exact (Subgroup.mem_center_iff.mp ha b).symm
        obtain ⟨a, b, hab⟩ := D.standing.nonab
        exact hab (mul_comm a b)
    have hYtHD : Yt ≤ H ⊓ D.M := le_inf hYtC (hYtX.trans hXM)
    have hsimple : IsSimpleGroup (↥Yt ⧸ N₀) :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
    have hpN0 : p ∣ Nat.card (↥Yt ⧸ N₀) := dvd_card_quotient_of_isL2 hN₀ hL2 hpn'
    obtain ⟨Y, N, hN, hYle, ⟨eY⟩⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_normal_quotientEquiv_imageModK
        (D := D) hp' hYtHD (QuotientGroup.mk' N₀) (QuotientGroup.mk'_surjective N₀)
        hsimple hpN0
    have : N.Normal := hN
    have hL2' : IsL2 (↥Y ⧸ N) n :=
      CFSG.Blueprint.LieModel.of_mulEquiv eY.symm hL2
    exact hHle (CFSG.LocalAnalysis.UniquenessCase.PartTwo.le_M_of_no_isL2_section
      hK35 h72 hp' hp2 hsp hHtop hrankB hn hpn Y N hYle hL2')
  have hrankE : 2 ≤ CFSG.Open.pRank r D.M :=
    CFSG.SectionRank.le_pRank hr.one_lt (hEX.trans hXM) hEel (by rw [hEcard])
  refine ⟨B, hBE, hBcard, hcent, ?_⟩
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_uniqueSet_of_centralizer hp' hsp hr
    hBD hBcard hcent hrankE hS1

theorem mem_uniqueSet_of_rootLine
    {D : Data G} {X : Subgroup G} {p n r : ℕ}
    (h72 : F07.R72 D) (hK35 : UCK.K35w)
    (hp : p ∈ D.sig) (hsp : IsStronglyPEmbedded p D.M) (h3 : 3 ≤ CFSG.Open.pRank p D.M)
    (hOp : UC22.F10.OpRes p D.M = D.M) (hn : 3 ≤ n) (hpn : p ∣ 2 ^ n + 1)
    (hZ : Subgroup.center (Bar2 X) = ⊥) (hOut : IsCyclic (Outer (Bar2 X)))
    (hr : r.Prime) (hr2 : r ≠ 2) (hX : X = Opp r D.M)
    (hcase : CFSG.Open.pRank p X = 2 ∨ IsU4 (Bar2 X) n)
    (hroot : ∀ E : Subgroup G, E ≤ X → IsElemAbelian r E → Nat.card E = r ^ 2 →
      ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = r ∧
        (∃ Yt : Subgroup G, Yt ≤ X ⊓ Subgroup.centralizer (B : Set G) ∧
          ∃ N₀ : Subgroup ↥Yt, ∃ hN : N₀.Normal,
            @IsL2 (↥Yt ⧸ N₀) (@QuotientGroup.Quotient.group _ _ N₀ hN) n) ∧
        (IsU4 (Bar2 X) n →
          2 ≤ CFSG.Open.pRank p (X ⊓ Subgroup.centralizer (B : Set G)) ∧
          p ∣ Nat.card ↥(X ⊓ Subgroup.centralizer (E : Set G))))
    {E : Subgroup G} (hEX : E ≤ X) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) :
    E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
  classical
  have hXM : X ≤ D.M := by
    rw [hX]
    exact CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le r D.M
  obtain ⟨B, hBE, -, -, hBuniq⟩ :=
    exists_mem_uniqueSet_rootLine h72 hK35 hp hsp h3 hOp hn hpn hZ hOut hr hr2 hX hcase hroot
      hEX hEel hEcard
  exact CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hBuniq hBE (hEX.trans hXM)

private theorem dvd_card_inf_centralizer_of_pRank_eq_two
    {D : Data G} {X : Subgroup G} {p r : ℕ}
    (hp : p ∈ D.sig) (h3 : 3 ≤ CFSG.Open.pRank p D.M)
    (hOp : UC22.F10.OpRes p D.M = D.M)
    (hZ : Subgroup.center (Bar2 X) = ⊥) (hOut : IsCyclic (Outer (Bar2 X)))
    (hr : r.Prime) (hr2 : r ≠ 2) (hX : X = Opp r D.M)
    (hcaseA : CFSG.Open.pRank p X = 2)
    {E : Subgroup G} (hED : E ≤ D.M) (hEel : IsElemAbelian r E) :
    p ∣ Nat.card ↥(D.M ⊓ Subgroup.centralizer (E : Set G)) := by
  classical
  have hp' : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have : Fact p.Prime := ⟨hp'⟩
  have : Fact r.Prime := ⟨hr⟩
  have hXM : X ≤ D.M := by
    rw [hX]
    exact CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le r D.M
  have hMN : D.M ≤ Subgroup.normalizer (X : Set G) := by
    rw [hX]
    exact CFSG.LocalAnalysis.RankThreeUC.le_normalizer_pElementSubgroup r D.M
  have hEX : E ≤ X := by
    rw [hX]
    exact CFSG.le_pElementSubgroup_of_isPGroup hr hEel.isPGroup hED
  have hrankBar : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 X)) < CFSG.Open.pRank p D.M :=
    pRank_top_bar2_lt_of_pRank_eq_two hp' hp2 h3 hcaseA
  obtain ⟨S, hSle, hSp, hSne, hSc⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_isPGroup_le_centralizer_centOverO2
      hXM hMN hZ hOut hp' hp2 hOp hrankBar hr hr2 hEX hEel.isPGroup
  have hSD : S ≤ D.M := fun x hx =>
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp (hSle hx)).1
  have hSinf : S ≤ D.M ⊓ Subgroup.centralizer (E : Set G) := le_inf hSD hSc
  have hSdvd : p ∣ Nat.card ↥S := by
    rcases hSp.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hSne
    · exact h1
  exact hSdvd.trans (Subgroup.card_dvd_of_le hSinf)

theorem centralizer_le_and_mem_uniqueSet_of_rootLine_of_dvd
    {D : Data G} {X : Subgroup G} {p n r : ℕ}
    (h72 : F07.R72 D) (hK35 : UCK.K35w) (hp : p ∈ D.sig) (hsp : IsStronglyPEmbedded p D.M)
    (h3 : 3 ≤ CFSG.Open.pRank p D.M) (hOp : UC22.F10.OpRes p D.M = D.M) (hn : 3 ≤ n)
    (hpn : p ∣ 2 ^ (2 * n) - 1) (hZ : Subgroup.center (Bar2 X) = ⊥)
    (hOut : IsCyclic (Outer (Bar2 X))) (hr : r.Prime) (hr2 : r ≠ 2) (hX : X = Opp r D.M)
    (hcaseA : CFSG.Open.pRank p X = 2) {B Yt : Subgroup G} {N₀ : Subgroup ↥Yt}
    (hN₀ : N₀.Normal) (hL2 : @IsL2 (↥Yt ⧸ N₀) (@QuotientGroup.Quotient.group _ _ N₀ hN₀) n)
    (hBX : B ≤ X) (hBcard : Nat.card B = r)
    (hYt : Yt ≤ X ⊓ Subgroup.centralizer (B : Set G))
    (hrankE : 2 ≤ CFSG.Open.pRank r D.M) :
    Subgroup.centralizer (B : Set G) ≤ D.M ∧
      B ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
  classical
  have hp' : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have : Fact p.Prime := ⟨hp'⟩
  have : Fact r.Prime := ⟨hr⟩
  have hEel : IsElemAbelian r B :=
    CFSG.GroupTheory.isElemAbelian_of_card_prime (r := r) hBcard
  have hXM : X ≤ D.M := by
    rw [hX]
    exact CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le r D.M
  have hYtX : Yt ≤ X := hYt.trans inf_le_left
  have hYtC : Yt ≤ Subgroup.centralizer (B : Set G) := hYt.trans inf_le_right
  have hS1 : ∀ E' : Subgroup G, E' ≤ D.M → IsElemAbelian r E' →
      Nat.card E' = r ^ 2 → p ∣ Nat.card ↥(D.M ⊓ Subgroup.centralizer (E' : Set G)) :=
    fun E' hE'D hE'el _ =>
      dvd_card_inf_centralizer_of_pRank_eq_two hp h3 hOp hZ hOut hr hr2 hX hcaseA hE'D hE'el
  have hrankB : 1 < CFSG.Open.pRank p (Subgroup.centralizer (B : Set G) ⊓ D.M) :=
    one_lt_pRank_centralizer_of_pRank_eq_two hp h3 hOp hZ hOut hr hr2 hX hcaseA hN₀ hL2 hpn
      le_rfl hYt hBX hEel
  have hcent : Subgroup.centralizer (B : Set G) ≤ D.M := by
    by_contra hHle
    set H : Subgroup G := Subgroup.centralizer (B : Set G) with hHdef
    have hGsimple : IsSimpleGroup G := D.standing.simple
    have hHtop : H ≠ ⊤ := by
      intro htop
      have hBcenter : B ≤ Subgroup.center G := by
        intro b hb
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ H := by rw [htop]; exact Subgroup.mem_top g
        exact (Subgroup.mem_centralizer_iff.mp hg b hb).symm
      have hne : Subgroup.center G ≠ ⊥ := by
        intro hbot
        have hle : B ≤ ⊥ := hbot ▸ hBcenter
        have h1 : Nat.card ↥B = 1 := by
          rw [show B = ⊥ from le_bot_iff.mp hle]
          exact Subgroup.card_bot
        rw [hBcard] at h1
        exact hr.ne_one h1
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hbot | htop'
      · exact hne hbot
      · have : IsMulCommutative G := by
          refine ⟨⟨fun a b => ?_⟩⟩
          have ha : a ∈ Subgroup.center G := by rw [htop']; exact Subgroup.mem_top a
          exact (Subgroup.mem_center_iff.mp ha b).symm
        obtain ⟨a, b, hab⟩ := D.standing.nonab
        exact hab (mul_comm a b)
    have hYtHD : Yt ≤ H ⊓ D.M := le_inf hYtC (hYtX.trans hXM)
    have hsimple : IsSimpleGroup (↥Yt ⧸ N₀) :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
    have hpN0 : p ∣ Nat.card (↥Yt ⧸ N₀) := dvd_card_quotient_of_isL2 hN₀ hL2 hpn
    obtain ⟨Y, N, hN, hYle, ⟨eY⟩⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_normal_quotientEquiv_imageModK
        (D := D) hp' hYtHD (QuotientGroup.mk' N₀) (QuotientGroup.mk'_surjective N₀)
        hsimple hpN0
    have : N.Normal := hN
    have hL2' : IsL2 (↥Y ⧸ N) n :=
      CFSG.Blueprint.LieModel.of_mulEquiv eY.symm hL2
    exact hHle (CFSG.LocalAnalysis.UniquenessCase.PartTwo.le_M_of_no_isL2_section_of_dvd
      hK35 h72 hp' hp2 hsp hHtop hrankB hn hpn Y N hYle hL2')
  refine ⟨hcent, ?_⟩
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_uniqueSet_of_centralizer hp' hsp hr
    (hBX.trans hXM) hBcard hcent hrankE hS1

theorem centralizer_le_and_mem_uniqueSet_of_rootLine
    {D : Data G} {X : Subgroup G} {p n r : ℕ}
    (h72 : F07.R72 D) (hK35 : UCK.K35w) (hp : p ∈ D.sig) (hsp : IsStronglyPEmbedded p D.M)
    (h3 : 3 ≤ CFSG.Open.pRank p D.M) (hOp : UC22.F10.OpRes p D.M = D.M) (hn : 3 ≤ n)
    (hpn : p ∣ 2 ^ n + 1) (hZ : Subgroup.center (Bar2 X) = ⊥)
    (hOut : IsCyclic (Outer (Bar2 X))) (hr : r.Prime) (hr2 : r ≠ 2) (hX : X = Opp r D.M)
    (hcaseA : CFSG.Open.pRank p X = 2) {B Yt : Subgroup G} {N₀ : Subgroup ↥Yt}
    (hN₀ : N₀.Normal) (hL2 : @IsL2 (↥Yt ⧸ N₀) (@QuotientGroup.Quotient.group _ _ N₀ hN₀) n)
    (hBX : B ≤ X) (hBcard : Nat.card B = r)
    (hYt : Yt ≤ X ⊓ Subgroup.centralizer (B : Set G))
    (hrankE : 2 ≤ CFSG.Open.pRank r D.M) :
    Subgroup.centralizer (B : Set G) ≤ D.M ∧
      B ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
  centralizer_le_and_mem_uniqueSet_of_rootLine_of_dvd h72 hK35 hp hsp h3 hOp hn
    (by
      rw [CFSG.Timmesfeld.IsPrimitivePrimeDivisor.two_pow_two_mul_sub_one]
      exact dvd_mul_of_dvd_right hpn _)
    hZ hOut hr hr2 hX hcaseA hN₀ hL2 hBX hBcard hYt hrankE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
