module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFittingN
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmega
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
public import CFSG.Adapters.StatedPSLTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem centTV_centralizer_V_le_M (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    Subgroup.centralizer (c.V : Set G) ≤ D.M := by
  have hUZ : D.U = D.Z := (h4 h1930 c).1
  have hNZ : Subgroup.normalizer (D.Z : Set G) = D.M := by
    rw [← hUZ]
    exact D.normalizer_U_eq
  have hZleV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  exact (Subgroup.centralizer_le hZleV).trans
    ((Subgroup.centralizer_le_normalizer (D.Z : Set G)).trans (le_of_eq hNZ))

theorem Ctx23L.sup_le_N (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) :
    c.L ⊔ D.T ≤ c.N := by
  have hNmem : c.N ∈ calMOf (c.L ⊔ D.T) := by
    rw [c.hN]
    simp
  exact hNmem.2

namespace Ctx23L

theorem sup_le_normalizer_V (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) :
    c.L ⊔ D.T ≤ Subgroup.normalizer (c.V : Set G) :=
  (Ctx23L.sup_le_N D Ch c).trans (uc22p22v_le_normalizer_conjClosure c.N D.Z)

theorem conj_mem_sup_inf_centralizer_V (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) :
    ∀ n ∈ c.L ⊔ D.T,
      ∀ x ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G),
        n * x * n⁻¹ ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) := by
  intro n hn x hx
  have hSV : c.L ⊔ D.T ≤ Subgroup.normalizer (c.V : Set G) :=
    sup_le_normalizer_V D Ch c
  have hSC : c.L ⊔ D.T ≤
      Subgroup.normalizer (Subgroup.centralizer (c.V : Set G) : Set G) :=
    hSV.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer c.V)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (c.L ⊔ D.T).mul_mem ((c.L ⊔ D.T).mul_mem hn hx.1) ((c.L ⊔ D.T).inv_mem hn)
  · exact (Subgroup.mem_normalizer_iff.mp (hSC hn) x).1 hx.2

theorem inf_centralizer_V_le_pCoreOf_L (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L := by
  classical
  let K0 : Subgroup G := c.L ⊓ Subgroup.centralizer (c.V : Set G)
  have hK0L : K0 ≤ c.L := inf_le_left
  have hK0normal : (K0.subgroupOf c.L).Normal := by
    refine Subgroup.Normal.mk ?_
    intro x hx l
    have hxK0 : (x : G) ∈ K0 := Subgroup.mem_subgroupOf.mp hx
    have hxL : (x : G) ∈ c.L := hxK0.1
    have hlS : (l : G) ∈ c.L ⊔ D.T := Subgroup.mem_sup_left l.2
    have hxK : (x : G) ∈ (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hxL, hxK0.2⟩
    have hconj := conj_mem_sup_inf_centralizer_V D Ch c (l : G) hlS (x : G) hxK
    have hconj' : ((l * x * l⁻¹ : ↥c.L) : G) ∈ K0 := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact c.L.mul_mem (c.L.mul_mem l.2 hxL) (c.L.inv_mem l.2)
      · simpa using (Subgroup.mem_inf.mp hconj).2
    exact Subgroup.mem_subgroupOf.mpr hconj'
  have hYnormal : (barImage c.L K0).Normal :=
    hK0normal.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨-, hL2, -⟩ := h23 h1930 c
  haveI : (barImage c.L K0).Normal := hYnormal
  haveI : IsSimpleGroup (Bar2 c.L) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (barImage c.L K0) with hbot | htop
  · exact le_pCoreOf_of_barImage_eq_bot hK0L hbot
  · exfalso
    have hCVleM : Subgroup.centralizer (c.V : Set G) ≤ D.M :=
      centTV_centralizer_V_le_M D Ch h4 h1930 c
    have hK0_le_M : K0 ≤ D.M := inf_le_right.trans hCVleM
    have hLTnorm : c.L ⊔ D.T ≤ Subgroup.normalizer (c.L : Set G) :=
      sup_le (Subgroup.le_normalizer (H := c.L)) c.hL.1.1
    have hnorm : ∀ n ∈ c.L ⊔ D.T, ∀ k ∈ c.L, n * k * n⁻¹ ∈ c.L := by
      intro n hn k hk
      exact (Subgroup.mem_normalizer_iff.mp (hLTnorm hn) k).1 hk
    have hO2L_le_O2S : CFSG.Open.pCoreOf 2 c.L ≤
        CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
      uc22main1_le_pCoreOf (K := c.L ⊔ D.T) (P := CFSG.Open.pCoreOf 2 c.L)
        ((uc22main1_pCoreOf_le c.L).trans le_sup_left)
        (uc22main1_isPGroup_pCoreOf c.L)
        (fun n hn x hx => uc22main1_conj_mem_pCoreOf hnorm hn hx)
    have hO2S_le_T : CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) ≤ D.T :=
      CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
        (CFSG.ABGLocalTools.isSylowOf_iff.mp
          (D.sylowG.of_le (le_sup_right : D.T ≤ c.L ⊔ D.T) le_top))
    have hO2L_le_M : CFSG.Open.pCoreOf 2 c.L ≤ D.M :=
      (hO2L_le_O2S.trans hO2S_le_T).trans D.sylowM.le
    have hL_le_sup : c.L ≤ K0 ⊔ CFSG.Open.pCoreOf 2 c.L := by
      intro l hl
      have hlbar : uc22p21cPi c.L ⟨l, hl⟩ ∈ barImage c.L K0 := by
        rw [htop]
        trivial
      obtain ⟨k, hkK0, hk⟩ := uc22p21c_mem_barImage.1 hlbar
      have hquot : uc22p21cPi c.L ((k : ↥c.L)⁻¹ * ⟨l, hl⟩) = 1 := by
        rw [map_mul, map_inv, hk, inv_mul_cancel]
      have hmem : (k : ↥c.L)⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥c.L :=
        (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥c.L) _).1 hquot
      have hmemG : (((k : ↥c.L)⁻¹ * ⟨l, hl⟩ : ↥c.L) : G) ∈
          CFSG.Open.pCoreOf 2 c.L :=
        ⟨_, hmem, rfl⟩
      have hl_eq : l = (k : G) * (((k : ↥c.L)⁻¹ * ⟨l, hl⟩ : ↥c.L) : G) := by
        simp [mul_assoc]
      rw [hl_eq]
      exact (K0 ⊔ CFSG.Open.pCoreOf 2 c.L).mul_mem
        (Subgroup.mem_sup_left hkK0) (Subgroup.mem_sup_right hmemG)
    have hL_le_M : c.L ≤ D.M :=
      hL_le_sup.trans (sup_le hK0_le_M hO2L_le_M)
    have hH : c.L ⊔ D.T ∈ hSet D.T D.M := c.hL.1.2.2.1
    exact hH.2.1 (sup_le hL_le_M D.sylowM.le)

theorem isPGroup_sup_inf_centralizer_V (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    IsPGroup 2 ↥((c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G)) := by
  classical
  let S : Subgroup G := c.L ⊔ D.T
  let C : Subgroup G := Subgroup.centralizer (c.V : Set G)
  let K : Subgroup G := S ⊓ C
  let K0 : Subgroup G := c.L ⊓ C
  have hK0_le_O2L : K0 ≤ CFSG.Open.pCoreOf 2 c.L :=
    inf_centralizer_V_le_pCoreOf_L D Ch h4 h23 h1930 c
  have hK0p : IsPGroup 2 K0 :=
    (uc22main1_isPGroup_pCoreOf c.L).to_le hK0_le_O2L
  have hLTnorm : S ≤ Subgroup.normalizer (c.L : Set G) := by
    exact sup_le (Subgroup.le_normalizer (H := c.L)) c.hL.1.1
  have hLnormalS : (c.L.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : c.L ≤ S)).2 hLTnorm
  let N : Subgroup ↥S := c.L.subgroupOf S
  haveI hNnormal : N.Normal := hLnormalS
  let π : ↥S →* (↥S ⧸ N) := QuotientGroup.mk' N
  have hsup : N ⊔ (D.T.subgroupOf S) = ⊤ := by
    have h := Subgroup.subgroupOf_sup (A := c.L) (A' := D.T) (B := c.L ⊔ D.T)
      (le_sup_left : c.L ≤ c.L ⊔ D.T) (le_sup_right : D.T ≤ c.L ⊔ D.T)
    rw [Subgroup.subgroupOf_self] at h
    simpa [N, S] using h.symm
  have hQp : IsPGroup 2 (↥S ⧸ N) := by
    rw [IsPGroup.iff_orderOf]
    intro q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hs_top : s ∈ N ⊔ (D.T.subgroupOf S) := by
      rw [hsup]
      trivial
    obtain ⟨l, hlN, t, htN, hlt⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := N) (t := D.T.subgroupOf S)).mp hs_top
    have htT : (t : G) ∈ D.T := Subgroup.mem_subgroupOf.mp htN
    have hqeq : π s = π t := by
      rw [← hlt, map_mul]
      have hl1 : π l = 1 := (QuotientGroup.eq_one_iff (N := N) l).2 hlN
      rw [hl1, one_mul]
    let t' : ↥D.T := ⟨(t : G), htT⟩
    have htS : (t' : G) ∈ c.L ⊔ D.T := (le_sup_right : D.T ≤ c.L ⊔ D.T) htT
    have ht'_eq : (⟨(t' : G), htS⟩ : ↥S) = t := Subtype.ext rfl
    have hTp : IsPGroup 2 D.T := CFSG.ABGLocalTools.IsSylowOf.isPGroup D.sylowG
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hTp) t'
    rw [hqeq]
    have hdvd : orderOf (π t) ∣ 2 ^ k := by
      have hmap : orderOf (π t) ∣ orderOf t' := by
        have h1 : π t = π (⟨(t' : G), htS⟩ : ↥S) := by rw [ht'_eq]
        rw [h1]
        simpa [Subgroup.orderOf_coe] using orderOf_map_dvd π (⟨(t' : G), htS⟩ : ↥S)
      simpa [hk] using hmap
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  rw [IsPGroup.iff_orderOf]
  intro x
  have hxS : (x : G) ∈ S := (Subgroup.mem_inf.mp x.2).1
  have hxC : (x : G) ∈ C := (Subgroup.mem_inf.mp x.2).2
  let xS : ↥S := ⟨(x : G), hxS⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hQp) (π xS)
  have hxpowL : (x : G) ^ (2 ^ a) ∈ c.L := by
    have hclass : π (xS ^ (2 ^ a)) = 1 := by
      rw [map_pow, ← ha]
      exact pow_orderOf_eq_one _
    have hmem : xS ^ (2 ^ a) ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) _).1 hclass
    exact Subgroup.mem_subgroupOf.mp hmem
  have hxpowK0 : (x : G) ^ (2 ^ a) ∈ K0 := by
    refine Subgroup.mem_inf.mpr ⟨hxpowL, ?_⟩
    exact C.pow_mem hxC _
  obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp hK0p)
    ⟨(x : G) ^ (2 ^ a), hxpowK0⟩
  have hpow_one : (x : G) ^ (2 ^ a * 2 ^ b) = 1 := by
    have h' : ((⟨(x : G) ^ (2 ^ a), hxpowK0⟩ : ↥K0) ^ (2 ^ b) : ↥K0) = 1 := by
      rw [← hb]
      exact pow_orderOf_eq_one _
    calc (x : G) ^ (2 ^ a * 2 ^ b) = ((x : G) ^ (2 ^ a)) ^ (2 ^ b) := by rw [pow_mul]
      _ = 1 := by simpa using congrArg Subtype.val h'
  have hdvd : orderOf (x : G) ∣ 2 ^ (a + b) := by
    rw [pow_add]
    exact orderOf_dvd_of_pow_eq_one hpow_one
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨j, by simpa [Subgroup.orderOf_coe] using hj⟩

end Ctx23L

theorem centTVLeO2LT_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) : CentTVLeO2LT D Ch := by
  intro h1930 c x hx
  have hKp : IsPGroup 2 ↥((c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G)) :=
    Ctx23L.isPGroup_sup_inf_centralizer_V D Ch h4 h23 h1930 c
  have hKconj := Ctx23L.conj_mem_sup_inf_centralizer_V D Ch c
  refine (uc22main1_le_pCoreOf (K := c.L ⊔ D.T)
    (P := (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G)) inf_le_left hKp ?_) ?_
  · intro n hn y hy
    exact hKconj n hn y hy
  · exact ⟨(le_sup_right : D.T ≤ c.L ⊔ D.T) hx.1, hx.2⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
