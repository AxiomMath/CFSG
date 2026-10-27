module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65SylowCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65InversionLiftCoprime
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65FrattiniWeak
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK332
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem exists_inverts_of_sylowCenterInverted_image {Γ : Type} [Group Γ] [Finite Γ]
    {K Z P : Subgroup Γ} (hZ : Nat.card Z = 3) (hZK : Z ≤ K)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P K) (hZP : Z ≤ P)
    (hZc : Z ≤ Subgroup.centralizer (P : Set Γ))
    (hinv : SylowCenterInverted ↥(K.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)))) :
    ∃ n ∈ Subgroup.normalizer (Z : Set Γ), ∀ z ∈ Z, n * z * n⁻¹ = z⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup Γ := CFSG.pPrimeCore 3 Γ
  have : O.Normal := CFSG.pPrimeCore_normal
  have : IsCyclic ↥Z := isCyclic_of_prime_card (p := 3) hZ
  obtain ⟨z0, hz0gen⟩ := IsCyclic.exists_generator (α := ↥Z)
  have hz0ord : orderOf z0 = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hz0gen]
    exact hZ
  have hzp : Subgroup.zpowers (z0 : Γ) = Z := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr z0.2
    · exact le_of_eq (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz0ord, hZ])
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  set Qb : Sylow 3 ↥(K.map (QuotientGroup.mk' O)) :=
    Q.mapSurjective ((QuotientGroup.mk' O).subgroupMap_surjective K) with hQbdef
  have hQb_coe : (Qb : Subgroup ↥(K.map (QuotientGroup.mk' O))) =
      (Q : Subgroup ↥K).map ((QuotientGroup.mk' O).subgroupMap K) := by
    rw [hQbdef, Sylow.coe_mapSurjective]
  set zK : ↥K := ⟨(z0 : Γ), hZK z0.2⟩ with hzKdef
  have hzKQ : zK ∈ (Q : Subgroup ↥K) := by
    rw [hQ, Subgroup.mem_subgroupOf, hzKdef]
    exact hZP z0.2
  set zb : ↥(K.map (QuotientGroup.mk' O)) :=
    (QuotientGroup.mk' O).subgroupMap K zK with hzbdef
  have hzb_coe : ((zb : ↥(K.map (QuotientGroup.mk' O))) : Γ ⧸ O) =
      QuotientGroup.mk' O (z0 : Γ) := by
    rw [hzbdef, hzKdef]
    rfl
  have hzb_mem : zb ∈ (Qb : Subgroup ↥(K.map (QuotientGroup.mk' O))) := by
    rw [hQb_coe, hzbdef]
    exact Subgroup.mem_map_of_mem ((QuotientGroup.mk' O).subgroupMap K) hzKQ
  have hzb_cent : zb ∈ Subgroup.centralizer
      ((Qb : Subgroup ↥(K.map (QuotientGroup.mk' O))) : Set ↥(K.map (QuotientGroup.mk' O))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hQb_coe] at hy
    obtain ⟨q, hqQ, rfl⟩ := Subgroup.mem_map.mp hy
    have hqP : (q : Γ) ∈ P := by
      rw [hQ] at hqQ
      exact Subgroup.mem_subgroupOf.mp hqQ
    have hcomm : q * zK = zK * q := by
      apply Subtype.ext
      have h := (Subgroup.mem_centralizer_iff.mp (hZc z0.2)) (q : Γ) hqP
      simpa [hzKdef] using h
    rw [hzbdef]
    rw [← map_mul, ← map_mul, hcomm]
  have hzKord : orderOf zK = 3 := by
    rw [hzKdef, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hz0ord]
  have hzK3 : zK ^ 3 = 1 := by
    rw [← hzKord]
    exact pow_orderOf_eq_one zK
  have hzb_ord : orderOf zb = 3 := by
    apply orderOf_eq_prime
    · rw [hzbdef, ← map_pow, hzK3, map_one]
    · intro h1
      have hπ1 : QuotientGroup.mk' O (z0 : Γ) = 1 := by
        have h := congrArg (fun x : ↥(K.map (QuotientGroup.mk' O)) => (x : Γ ⧸ O)) h1
        rw [hzb_coe] at h
        simpa using h
      have hmemO : (z0 : Γ) ∈ O := (QuotientGroup.eq_one_iff (N := O) (z0 : Γ)).mp hπ1
      have hdvd : 3 ∣ Nat.card O := by
        rw [← hz0ord, ← Subgroup.orderOf_coe z0]
        exact Subgroup.orderOf_dvd_natCard O hmemO
      exact (Nat.prime_three.coprime_iff_not_dvd.mp
        (CFSG.pPrimeCore_coprime_card (p := 3) (G := Γ))) hdvd
  obtain ⟨tb, htb⟩ := hinv Qb zb hzb_mem hzb_cent hzb_ord
  have ht_z0 : (tb : Γ ⧸ O) * QuotientGroup.mk' O (z0 : Γ) * (tb : Γ ⧸ O)⁻¹ =
      (QuotientGroup.mk' O (z0 : Γ))⁻¹ := by
    have h := congrArg (fun x : ↥(K.map (QuotientGroup.mk' O)) => (x : Γ ⧸ O)) htb
    simpa [hzb_coe] using h
  refine exists_inverts_of_quotient_inverts (O := O) (t := (tb : Γ ⧸ O))
    (CFSG.pPrimeCore_coprime_card (p := 3) (G := Γ)) hZ ?_
  intro z hz
  have hzmem : z ∈ Subgroup.zpowers (z0 : Γ) := by rw [hzp]; exact hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzmem
  calc (tb : Γ ⧸ O) * QuotientGroup.mk' O z * (tb : Γ ⧸ O)⁻¹
      = (tb : Γ ⧸ O) * QuotientGroup.mk' O ((z0 : Γ) ^ k) * (tb : Γ ⧸ O)⁻¹ := by
          rw [hk]
    _ = (tb : Γ ⧸ O) * (QuotientGroup.mk' O (z0 : Γ)) ^ k * (tb : Γ ⧸ O)⁻¹ := by
          rw [map_zpow]
    _ = ((tb : Γ ⧸ O) * QuotientGroup.mk' O (z0 : Γ) * (tb : Γ ⧸ O)⁻¹) ^ k := by
          rw [conj_zpow]
    _ = ((QuotientGroup.mk' O (z0 : Γ))⁻¹) ^ k := by rw [ht_z0]
    _ = ((QuotientGroup.mk' O (z0 : Γ)) ^ k)⁻¹ := by rw [inv_zpow]
    _ = (QuotientGroup.mk' O ((z0 : Γ) ^ k))⁻¹ := by rw [map_zpow]
    _ = (QuotientGroup.mk' O z)⁻¹ := by rw [hk]

private theorem k332z3_exists_inverts_or_pRank_one
    (hK : CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan.K332Z3)
    (hInv : ∀ (Y : Type) [Group Y] [Finite Y],
      (CFSG.RankThree.PartTwo.Sec4.IsoGTwoPrime Y ∨
        Nonempty (Y ≃* CFSG.Blueprint.NativeSporadic.J2)) → SylowCenterInverted Y)
    {Γ : Type} [Group Γ] [Finite Γ] (hΓ : CFSG.Open.IsKGroup Γ)
    {Z : Subgroup Γ} (hZ : Nat.card Z = 3)
    (hwc : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn Z (Subgroup.normalizer (Z : Set Γ)))
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup Γ) ≤ 3) :
    (∃ n ∈ Subgroup.normalizer (Z : Set Γ), ∀ z ∈ Z, n * z * n⁻¹ = z⁻¹) ∨
      CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set Γ)) = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZK : Z ≤ Subgroup.normalClosure (Z : Set Γ) := Subgroup.subset_normalClosure
  have hZpg : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hZ)
  obtain ⟨S, hS, hZS⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.N588A.exists_isSylowOf_ge_of_le
      (K := ⊤) (Q := Z) le_top hZpg
  have hSN : S ≤ Subgroup.normalizer (Z : Set Γ) :=
    le_normalizer_of_isWeaklyClosedIn_normalizer hZS hS.isPGroup hwc
  have hwcS : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn Z S :=
    fun g hg => hwc g (hg.trans hSN)
  have hSrank : CFSG.Open.pRank 3 S ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans hrk
  by_cases hrank : CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set Γ)) = 1
  · exact Or.inr hrank
  · left
    have hge : 1 ≤ CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set Γ)) :=
      CFSG.LocalAnalysis.UniquenessCase.UCK.N588A.one_le_pRank Nat.prime_three hZK hZ
    have h2 : 2 ≤ CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set Γ)) := by omega
    let N : Subgroup Γ := CFSG.pPrimeCore 3 Γ
    let π : Γ →* Γ ⧸ N := QuotientGroup.mk' N
    have hmap : (Subgroup.normalClosure (Z : Set Γ)).map π =
        Subgroup.normalClosure ((Z.map π : Subgroup (Γ ⧸ N)) : Set (Γ ⧸ N)) :=
      Subgroup.map_normalClosure (Z : Set Γ) π (QuotientGroup.mk'_surjective N)
    have hinv : SylowCenterInverted ↥((Subgroup.normalClosure (Z : Set Γ)).map π) := by
      rw [hmap]
      exact hInv _ (hK Γ hΓ S Z hS hSrank hZS hZ hwcS h2)
    obtain ⟨P, hP, hZP⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.UCK.N588A.exists_isSylowOf_ge_of_le hZK hZpg
    have hZc : Z ≤ Subgroup.centralizer (P : Set Γ) :=
      le_centralizer_of_isWeaklyClosedIn_normalizer hZP hP.isPGroup hZ hwc
    exact exists_inverts_of_sylowCenterInverted_image hZ hZK hP hZP hZc hinv

private theorem k332z3_hInv_of_inputs
    (hJ2 : ∀ (Y : Type) [Group Y] [Finite Y], IsSpor Y .J2 → SylowCenterInverted Y)
    (hU33 : ∀ (Y : Type) [Group Y] [Finite Y],
      CFSG.Blueprint.LieModel Y .PSU 3 3 1 → SylowCenterInverted Y)
    (hG2 : ∀ (Y : Type) [Group Y] [Finite Y] (r f : ℕ), r.Prime →
      CFSG.Blueprint.LieModel Y .G2 0 r f → SylowCenterInverted Y) :
    ∀ (Y : Type) [Group Y] [Finite Y],
      (CFSG.RankThree.PartTwo.Sec4.IsoGTwoPrime Y ∨
        Nonempty (Y ≃* CFSG.Blueprint.NativeSporadic.J2)) → SylowCenterInverted Y := by
  intro Y _ _ h
  rcases h with hIso | hJ2e
  · unfold CFSG.RankThree.PartTwo.Sec4.IsoGTwoPrime at hIso
    rcases hIso with ⟨p, f, hmodel⟩ | hne
    · exact hG2 Y p f hmodel.1.1 (Or.inr (Or.inl ⟨rfl, by decide, hmodel⟩))
    · obtain ⟨e⟩ := hne
      exact hU33 Y
        (CFSG.RankThree.PartTwo.Sec19.Step1915WProof.lieModel_of_mulEquiv_projSU_three e)
  · exact hJ2 Y hJ2e

theorem exists_inverts_or_pRank_one_of_K332
    (hK : CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan.K332Z3)
    (hJ2 : ∀ (Y : Type) [Group Y] [Finite Y], IsSpor Y .J2 → SylowCenterInverted Y)
    (hU33 : ∀ (Y : Type) [Group Y] [Finite Y],
      CFSG.Blueprint.LieModel Y .PSU 3 3 1 → SylowCenterInverted Y)
    (hG2 : ∀ (Y : Type) [Group Y] [Finite Y] (r f : ℕ), r.Prime →
      CFSG.Blueprint.LieModel Y .G2 0 r f → SylowCenterInverted Y)
    {Γ : Type} [Group Γ] [Finite Γ] (hΓ : CFSG.Open.IsKGroup Γ)
    {Z : Subgroup Γ} (hZ : Nat.card Z = 3)
    (hwc : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn Z (Subgroup.normalizer (Z : Set Γ)))
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup Γ) ≤ 3) :
    (∃ n ∈ Subgroup.normalizer (Z : Set Γ), ∀ z ∈ Z, n * z * n⁻¹ = z⁻¹) ∨
      CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set Γ)) = 1 :=
  k332z3_exists_inverts_or_pRank_one hK (k332z3_hInv_of_inputs hJ2 hU33 hG2) hΓ hZ hwc hrk

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
