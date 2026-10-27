module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection14.corollary_14_3

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Theorem 14 4 from BG Section 14 -/

section Section14

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Theorem 14.4, uniqueness of `N(x)` in the nonsingleton case. -/
public theorem CFSG.theorem_14_4_unique_N
    {x : G} (hx : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty)
    (hcard : 1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x}) :
    ∃! N : Subgroup G,
      N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) := by
  classical
  obtain ⟨M, hM⟩ := hσ
  have hxMσ : x ∈ section10Msigma M := hM.2 (by simp)
  obtain ⟨q, z, hz_zpowx, _hz_zpow, _hz_ne, hzprime⟩ :=
    section14_exists_primeOrder_zpowers_in
      (G := G) (B := Subgroup.zpowers x) (Subgroup.mem_zpowers x) hx
  let X : Subgroup G := Subgroup.zpowers z
  have hXprime : X ∈ section10PrimeOrderSubgroupsIn q (Subgroup.zpowers x) := by
    simpa [X] using hzprime
  have hXorder : orderOf z = q.val := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn, X] using hXprime) with
      ⟨_hz, hzord⟩
    exact hzord
  have hXle_zpow : X ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hz_zpowx
  have hXcard : Nat.card X = q.val := by
    simp [X, hXorder]
  have hXne : X ≠ ⊥ := by
    intro hXbot
    have hcard_one : Nat.card X = 1 := by
      simp [hXbot]
    exact q.2.ne_one (hXcard.symm.trans hcard_one)
  have hXq : IsPGroup q.val X := by
    exact IsPGroup.of_card (n := 1) (by simpa [pow_one] using hXcard)
  have hXle_Mσ : X ≤ section10Msigma M :=
    hXle_zpow.trans (Subgroup.zpowers_le.2 hxMσ)
  have hXle_M : X ≤ M := hXle_Mσ.trans (section14_msigma_le M)
  have hqσ : q ∈ section10SigmaPrimes M := by
    have hqdivX : q.val ∣ Nat.card X := by rw [hXcard]
    have hqdivσ : q.val ∣ Nat.card (section10Msigma M) :=
      hqdivX.trans (Subgroup.card_dvd_of_le hXle_Mσ)
    exact ((theorem_10_2_b (G := G) hM.1).1).p_in_pi_of_p_dvd_card q hqdivσ
  have hXne_top : X ≠ ⊤ := by
    intro hXtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hXtop] using hXle_M
    exact hM.1.1 (top_le_iff.mp htop_le_M)
  have hNXne_top : Subgroup.normalizer (X : Set G) ≠ ⊤ := by
    intro hNtop
    have hXnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    letI : IsSimpleGroup G := IsMinCE.simple
    rcases hXnormal.eq_bot_or_eq_top with hXbot | hXtop
    · exact hXne hXbot
    · exact hXne_top hXtop
  have hΩsubset :
      section14MsigmaElement x ⊆ section14MsigmaFamily (X : Set G) := by
    intro L hL
    refine ⟨hL.1, ?_⟩
    exact hXle_zpow.trans (Subgroup.zpowers_le.2 (hL.2 (by simp)))
  have hL_conj :
      ∀ {L : Subgroup G}, L ∈ section14MsigmaElement x →
        L ∈ section10ConjugatesContaining M X := by
    intro L hL
    have hLX : L ∈ section14MsigmaFamily (X : Set G) := hΩsubset hL
    have hXle_L : X ≤ L := hLX.2.trans (section14_msigma_le L)
    by_contra hnot
    have hnotconjL : section12NotConjugate L M := by
      intro a hLa
      have hL_eq : L = M.conjBy a⁻¹ := by
        calc
          L = (L.conjBy a).conjBy a⁻¹ := by
            simpa using (section11_conjBy_inv (G := G) L a).symm
          _ = M.conjBy a⁻¹ := by rw [hLa]
      exact hnot ⟨a⁻¹, hL_eq, hXle_L⟩
    have hqσL : q ∈ section10SigmaPrimes L := by
      have hqdivX : q.val ∣ Nat.card X := by rw [hXcard]
      have hqdivLσ : q.val ∣ Nat.card (section10Msigma L) :=
        hqdivX.trans (Subgroup.card_dvd_of_le hLX.2)
      exact ((theorem_10_2_b (G := G) hL.1).1).p_in_pi_of_p_dvd_card q hqdivLσ
    have hσdisLM :
        Disjoint (section10SigmaPrimes M) (section10SigmaPrimes L) :=
      theorem_13_9 (G := G) hM.1 hL.1 hnotconjL
    rw [Set.disjoint_left] at hσdisLM
    exact hσdisLM hqσ hqσL
  let Ωx : Type _ := {L : Subgroup G // L ∈ section14MsigmaElement x}
  haveI : Nontrivial Ωx := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨Lsub, hLsub_ne⟩ := exists_ne (⟨M, hM⟩ : Ωx)
  let L : Subgroup G := Lsub.1
  have hL : L ∈ section14MsigmaElement x := Lsub.2
  have hL_ne_M : L ≠ M := by
    intro hEq
    exact hLsub_ne (Subtype.ext hEq)
  have htrans :
      ConjugationActionTransitiveOn (Subgroup.centralizer (X : Set G))
        (section10ConjugatesContaining M X) :=
    theorem_10_1_b (G := G) (M := M) (X := X) (p := q) hM.1 hqσ hXne hXq hXle_M
  have hM_conj : M ∈ section10ConjugatesContaining M X := by
    exact ⟨1, (section8_conjBy_one (G := G) M).symm, hXle_M⟩
  have hL_conj_mem : L ∈ section10ConjugatesContaining M X := hL_conj hL
  obtain ⟨c, hc_eq⟩ := htrans M hM_conj L hL_conj_mem
  have hNX_not_le_M : ¬ Subgroup.normalizer (X : Set G) ≤ M := by
    intro hNX_le_M
    have hcM : (c : G) ∈ M := hNX_le_M (centralizer_le_normalizer X c.property)
    have hc_norm_M : (c : G) ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.le_normalizer hcM
    have hMc : M.conjBy (c : G) = M :=
      section11_conjBy_eq_of_mem_normalizer hc_norm_M
    exact hL_ne_M (hc_eq.trans hMc)
  obtain ⟨N, hN⟩ :=
    section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) (H := Subgroup.normalizer (X : Set G)) hNXne_top
  have hN_ne_M : N ≠ M := by
    intro hEq
    exact hNX_not_le_M (hEq ▸ hN.2)
  have hXle_N : X ≤ N := Subgroup.le_normalizer.trans hN.2
  have hXinf : X ≤ M ⊓ N := le_inf hXle_M hXle_N
  obtain ⟨S, hXS⟩ :=
    IsPGroup.exists_le_sylow (G := (M ⊓ N : Subgroup G)) (p := q.val)
      (hXq.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := X) (K := M ⊓ N) hXinf).symm)
  have hXleS :
      X ≤ section10AmbientSylowSubgroup (M ⊓ N) S := by
    intro y hy
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hXinf hy⟩, hXS (by simpa [Subgroup.mem_subgroupOf] using hy), rfl⟩
  have hnotconj : section12NotConjugate N M :=
    proposition_12_15_a
      (G := G) (M := M) (Mstar := N) (X := X) (q := q) (S := S)
      hM.1 hqσ hXle_M hXne hXq hN hN_ne_M hXleS
  have hσdis :
      Disjoint (section10SigmaPrimes M) (section10SigmaPrimes N) :=
    theorem_13_9 (G := G) hM.1 hN.1 hnotconj
  have hq_not_sigma_N : q ∉ section10SigmaPrimes N := by
    rw [Set.disjoint_left] at hσdis
    exact fun hqσN => hσdis hqσ hqσN
  obtain ⟨hqτ2N, _hbetaN, hcomp⟩ :=
    proposition_12_15_e
      (G := G) (M := M) (Mstar := N) (X := X) (q := q) (S := S)
      hM.1 hqσ hXle_M hXne hXq hN hN_ne_M hXleS hq_not_sigma_N
  have hCx_le_CX :
      Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer (X : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro y hyX
    have hyx : y ∈ Subgroup.zpowers x := hXle_zpow hyX
    rcases Subgroup.mem_zpowers_iff.mp hyx with ⟨n, rfl⟩
    have hxg : Commute x g :=
      (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
    exact (hxg.zpow_left n).eq
  have hCX_le_N : Subgroup.centralizer (X : Set G) ≤ N :=
    (centralizer_le_normalizer X).trans hN.2
  have hCx_le_N :
      Subgroup.centralizer ({x} : Set G) ≤ N := hCx_le_CX.trans hCX_le_N
  have hxM : x ∈ M := section14_msigma_le M hxMσ
  have hMnorm : Subgroup.normalizer (M : Set G) = M := by
    apply le_antisymm
    · have hnorm_proper : Subgroup.normalizer (M : Set G) ≠ ⊤ := by
        intro hnorm_top
        have hMnormal : M.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
        letI : IsSimpleGroup G := IsMinCE.simple
        rcases (haveI := hMnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal M) with hMbot | hMtop
        · have hqM : q.val ∣ Nat.card M := hqσ.1
          have hq_one : q.val ∣ 1 := by simpa [hMbot] using hqM
          exact q.2.not_dvd_one hq_one
        · exact hM.1.1 hMtop
      exact le_of_eq ((hM.1.le_iff_eq hnorm_proper).mp
        Subgroup.le_normalizer)
    · exact Subgroup.le_normalizer
  let R : Subgroup G := elementCentralizerIn (section10Msigma N) x
  have hxN : x ∈ N := by
    apply hCx_le_N
    simpa using (Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl x))
  have hM_inf_sigmaN_bot : M ⊓ section10Msigma N = ⊥ := by
    have hdisj_comp : Disjoint (section10Msigma N) (M ⊓ N) := hcomp.2.2.2
    rw [Subgroup.disjoint_def] at hdisj_comp
    apply le_bot_iff.mp
    intro y hy
    exact hdisj_comp hy.2 ⟨hy.1, section14_msigma_le N hy.2⟩
  have hbase_sigma :
      ∀ {L : Subgroup G}, L ∈ section14MsigmaElement x →
        ∃! r : section10Msigma N, L = M.conjBy (r : G) := by
    intro L hL
    obtain ⟨u, hu_eq⟩ := htrans M hM_conj L (hL_conj hL)
    have huN : (u : G) ∈ N := hCX_le_N u.property
    let T : Subgroup N := (M ⊓ N).subgroupOf N
    have hTcomp : T.IsComplement' (section10MsigmaSubgroup N) := by
      simpa [T] using
        section14_complement_to_msigma_isComplement' (M := N) (E := M ⊓ N) hcomp
    have huTop : (⟨u, huN⟩ : N) ∈ section10MsigmaSubgroup N ⊔ T := by
      have htop : section10MsigmaSubgroup N ⊔ T = ⊤ := hTcomp.symm.sup_eq_top
      have : (⟨u, huN⟩ : N) ∈ (⊤ : Subgroup N) := by simp
      simp [htop]
    haveI : (section10MsigmaSubgroup N).Normal := inferInstance
    rcases (Subgroup.mem_sup_of_normal_left
        (s := section10MsigmaSubgroup N) (t := T) (x := (⟨u, huN⟩ : N))).1 huTop with
      ⟨rN, hrNσ, mN, hmT, hrm⟩
    have hmMN : (mN : G) ∈ M ⊓ N := by
      simpa [T, Subgroup.mem_subgroupOf] using hmT
    have hrσ : (rN : G) ∈ section10Msigma N := by
      exact Subgroup.mem_map.mpr ⟨rN, hrNσ, rfl⟩
    let rσ : section10Msigma N := ⟨(rN : G), hrσ⟩
    have hu_eq_rm : (u : G) = (rσ : G) * (mN : G) := by
      exact (congrArg Subtype.val hrm).symm
    have hm_norm_M : (mN : G) ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.le_normalizer hmMN.1
    have hL_eq_r : L = M.conjBy (rN : G) := by
      calc
        L = M.conjBy (u : G) := hu_eq
        _ = M.conjBy ((rσ : G) * (mN : G)) := by rw [hu_eq_rm]
        _ = (M.conjBy (mN : G)).conjBy (rσ : G) := by
              simpa using
                (section11_conjBy_conjBy (G := G) M (mN : G) (rσ : G)).symm
        _ = M.conjBy (rN : G) := by
              rw [section11_conjBy_eq_of_mem_normalizer hm_norm_M]
    refine ⟨rσ, hL_eq_r, ?_⟩
    intro r' hr'
    have hfix : M.conjBy (((rσ : G)⁻¹) * (r' : G)) = M := by
      calc
        M.conjBy (((rσ : G)⁻¹) * (r' : G)) =
            (M.conjBy (r' : G)).conjBy (rσ : G)⁻¹ := by
              simpa using
                (section11_conjBy_conjBy (G := G) M (r' : G) (rσ : G)⁻¹).symm
        _ = (M.conjBy (rσ : G)).conjBy (rσ : G)⁻¹ := by rw [← hr', ← hL_eq_r]
        _ = M := section11_conjBy_inv (G := G) M (rσ : G)
    have hfix_norm : ((rσ : G)⁻¹) * (r' : G) ∈ Subgroup.normalizer (M : Set G) :=
      section14_mem_normalizer_of_conjBy_eq (G := G) (H := M) hfix
    have hdiffM : ((rσ : G)⁻¹) * (r' : G) ∈ M := by
      simpa [hMnorm] using hfix_norm
    have hdiffσ : ((rσ : G)⁻¹) * (r' : G) ∈ section10Msigma N := by
      exact (section10Msigma N).mul_mem
        ((section10Msigma N).inv_mem rσ.property) r'.property
    have hdiff1 : ((rσ : G)⁻¹) * (r' : G) = 1 := by
      have hbot : ((rσ : G)⁻¹) * (r' : G) ∈ (⊥ : Subgroup G) := by
        simpa [hM_inf_sigmaN_bot] using
          (show ((rσ : G)⁻¹) * (r' : G) ∈ M ⊓ section10Msigma N from ⟨hdiffM, hdiffσ⟩)
      simpa using hbot
    apply Subtype.ext
    calc
      (r' : G) = (rσ : G) * (((rσ : G)⁻¹) * (r' : G)) := by group
      _ = (rσ : G) := by rw [hdiff1]; simp
  obtain ⟨rσ, hL_eq_rσ, huniqσ⟩ := hbase_sigma hL
  have hx_norm_sigma : x ∈ Subgroup.normalizer (section10Msigma N : Set G) :=
    section12_le_normalizer_msigma (M := N) hxN
  have hxinv_norm_sigma : x⁻¹ ∈ Subgroup.normalizer (section10Msigma N : Set G) :=
    Subgroup.inv_mem _ hx_norm_sigma
  have hrσx_mem : x⁻¹ * (rσ : G) * x ∈ section10Msigma N := by
    have hmem_conj : x⁻¹ * (rσ : G) * x ∈ (section10Msigma N).conjBy x⁻¹ := by
      exact Subgroup.mem_map.mpr ⟨(rσ : G), rσ.property, by
        simp [mul_assoc]⟩
    simpa [section11_conjBy_eq_of_mem_normalizer hxinv_norm_sigma] using hmem_conj
  let rσx : section10Msigma N := ⟨x⁻¹ * (rσ : G) * x, hrσx_mem⟩
  have hx_norm_M : x ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer hxM
  have hxinv_norm_L : x⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
    apply Subgroup.inv_mem
    exact Subgroup.le_normalizer (section14_msigma_le L (hL.2 (by simp)))
  have hMx : M.conjBy x = M := section11_conjBy_eq_of_mem_normalizer hx_norm_M
  have hL_eq_rσx : L = M.conjBy (rσx : G) := by
    calc
      L = L.conjBy x⁻¹ := by
        rw [section11_conjBy_eq_of_mem_normalizer hxinv_norm_L]
      _ = (M.conjBy (rσ : G)).conjBy x⁻¹ := by rw [hL_eq_rσ]
      _ = ((M.conjBy x).conjBy (rσ : G)).conjBy x⁻¹ := by
        have htmp : (M.conjBy x).conjBy (rσ : G) = M.conjBy (rσ : G) := by
          rw [hMx]
        rw [← htmp]
      _ = (M.conjBy ((rσ : G) * x)).conjBy x⁻¹ := by
        exact congrArg (fun H : Subgroup G => H.conjBy x⁻¹)
          (section11_conjBy_conjBy (G := G) M x (rσ : G))
      _ = M.conjBy (x⁻¹ * ((rσ : G) * x)) := by
        simpa [mul_assoc] using
          (section11_conjBy_conjBy (G := G) M ((rσ : G) * x) x⁻¹)
      _ = M.conjBy (rσx : G) := by
        dsimp [rσx]
        simp [mul_assoc]
  have hrσx_eq : rσx = rσ := huniqσ rσx hL_eq_rσx
  have hrσx_val : x⁻¹ * (rσ : G) * x = (rσ : G) := congrArg Subtype.val hrσx_eq
  have hrσ_comm : Commute (rσ : G) x := by
    have hmul_eq := congrArg (fun t : G => x * t) hrσx_val
    change (rσ : G) * x = x * (rσ : G)
    simpa [mul_assoc] using hmul_eq
  have hrσR : (rσ : G) ∈ R := by
    exact ⟨rσ.property, Subgroup.mem_centralizer_singleton_iff.mpr hrσ_comm⟩
  have hrσ_ne_one : (rσ : G) ≠ 1 := by
    intro hrσ1
    have hL_eq_M' : L = M := by
      calc
        L = M.conjBy (rσ : G) := hL_eq_rσ
        _ = M.conjBy (1 : G) := by rw [hrσ1]
        _ = M := section8_conjBy_one (G := G) M
    exact hL_ne_M hL_eq_M'
  have hqSupp : q ∈ section14ElementPrimeSupport x := by
    have hqdivX : q.val ∣ Nat.card X := by rw [hXcard]
    change q.val ∣ Nat.card (Subgroup.zpowers x)
    exact hqdivX.trans (Subgroup.card_dvd_of_le hXle_zpow)
  have hsuppσM : section14ElementPrimeSupport x ⊆ section10SigmaPrimes M := by
    intro p hpSupp
    have hpMsigma : p ∈ subgroupPrimeSet (section10Msigma M) := by
      exact section8_subgroupPrimeSet_mono
        (Subgroup.zpowers_le.2 hxMσ)
        (by simpa [section14ElementPrimeSupport] using hpSupp)
    exact ((theorem_10_2_b (G := G) hM.1).1).p_in_pi_of_p_dvd_card p hpMsigma
  have hxsigma' : section14IsPiElement (section10SigmaPrimes N)ᶜ x := by
    intro p hpSupp hpσN
    have hpσM : p ∈ section10SigmaPrimes M := hsuppσM hpSupp
    exact (Set.disjoint_left.mp hσdis) hpσM hpσN
  have hxcent_rσ : x ∈ elementCentralizerIn N (rσ : G) := by
    refine ⟨hxN, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hrσ_comm.symm
  have hcor :=
    corollary_14_3 (G := G) (M := N) (x := (rσ : G)) (x' := x) hN.1
      rσ.property hrσ_ne_one hx hxcent_rσ hxsigma'
  rcases hcor with hκ | hτ2
  · exfalso
    have hqκ : q ∈ section14KappaPrimes N := hκ.1 hqSupp
    have hqτ13 : q ∈ section12Tau1Primes N ∪ section12Tau3Primes N :=
      section14_kappa_subset_tau13 hqκ
    rcases hqτ13 with hqτ1 | hqτ3
    · have h1 : primeRank q.val N = 1 := hqτ1.2.2
      have h2 : primeRank q.val N = 2 := hqτ2N.2
      omega
    · have h1 : primeRank q.val N = 1 := hqτ3.2.2
      have h2 : primeRank q.val N = 2 := hqτ2N.2
      omega
  · refine ⟨N, ?_, ?_⟩
    · rw [hτ2.2.2]
      simp
    · intro N' hN'
      have hN'single : N' ∈ ({N} : Set (Subgroup G)) := by
        simpa [hτ2.2.2] using hN'
      simpa using hN'single

/-- The subgroup `N(x)` chosen from Theorem 14.4 in the nonsingleton case. -/
@[expose] public noncomputable def CFSG.section14N (x : G) : Subgroup G := by
  classical
  by_cases h :
      x ≠ 1 ∧ (section14MsigmaElement x).Nonempty ∧
        1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x}
  · exact Classical.choose
      (ExistsUnique.exists (theorem_14_4_unique_N (x := x) h.1 h.2.1 h.2.2))
  · exact ⊤

/-- The subgroup `R(x)` chosen from Theorem 14.4. -/
@[expose] public noncomputable def CFSG.section14R (x : G) : Subgroup G := by
  classical
  by_cases h :
      x ≠ 1 ∧ (section14MsigmaElement x).Nonempty ∧
        1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x}
  · exact elementCentralizerIn (section10Msigma (section14N x)) x
  · exact ⊥

public theorem CFSG.section14N_mem_of_nonsingleton
    {x : G} (hx : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty)
    (hcard : 1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x}) :
    section14N x ∈
      section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) := by
  classical
  have hcard' :
      1 < (section14MsigmaElement x).ncard := by
    simpa only [Nat.card_coe_set_eq] using hcard
  have hNdef :
      section14N x =
        Classical.choose
          (ExistsUnique.exists (theorem_14_4_unique_N (x := x) hx hσ hcard)) := by
    simp [section14N, hx, hσ, hcard']
  rw [hNdef]
  exact
    Classical.choose_spec
      (ExistsUnique.exists (theorem_14_4_unique_N (x := x) hx hσ hcard))

public theorem CFSG.section14_nonsingleton_of_conjBy_eq_maximal
    {x : G} (hx : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty)
    {N : Subgroup G} (hN : N ∈ section9MaximalSubgroups G)
    (g : G) (hgN : (section14N x).conjBy g = N) :
    1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x} := by
  by_contra hcard
  have hcard' :
      ¬ 1 < (section14MsigmaElement x).ncard := by
    simpa only [Nat.card_coe_set_eq] using hcard
  have htop : section14N x = ⊤ := by
    simp [section14N, hx, hσ, hcard']
  have htop_conj : ((⊤ : Subgroup G).conjBy g) = ⊤ := by
    simp [Subgroup.conjBy]
  have hNtop : N = ⊤ := by
    calc
      N = (section14N x).conjBy g := hgN.symm
      _ = (⊤ : Subgroup G).conjBy g := by rw [htop]
      _ = ⊤ := htop_conj
  exact hN.1 hNtop

private theorem CFSG.section14R_eq_of_nonsingleton
    {x : G} (hx : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty)
    (hcard : 1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x}) :
    section14R x = elementCentralizerIn (section10Msigma (section14N x)) x := by
  classical
  have hcard' :
      1 < (section14MsigmaElement x).ncard := by
    simpa only [Nat.card_coe_set_eq] using hcard
  simp [section14R, hx, hσ, hcard']

private theorem CFSG.section14_nonsingleton_member_data
    {x : G} (hx : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty)
    (hcard : 1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x})
    {M : Subgroup G} (hM : M ∈ section14MsigmaElement x) :
    section14NormalHallIn (section14R x) (Subgroup.centralizer ({x} : Set G)) ∧
      section14SharpTransitiveOn (section14R x) (section14MsigmaElement x) ∧
      section14Theorem14_4NData x (section14R x) (section14N x) M := by
  classical
  have hxMσ : x ∈ section10Msigma M := hM.2 (by simp)
  obtain ⟨q, z, hz_zpowx, _hz_zpow, _hz_ne, hzprime⟩ :=
    section14_exists_primeOrder_zpowers_in
      (G := G) (B := Subgroup.zpowers x) (Subgroup.mem_zpowers x) hx
  let X : Subgroup G := Subgroup.zpowers z
  have hXprime : X ∈ section10PrimeOrderSubgroupsIn q (Subgroup.zpowers x) := by
    simpa [X] using hzprime
  have hXorder : orderOf z = q.val := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn, X] using hXprime) with
      ⟨_hz, hzord⟩
    exact hzord
  have hXle_zpow : X ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hz_zpowx
  have hXcard : Nat.card X = q.val := by
    simp [X, hXorder]
  have hXne : X ≠ ⊥ := by
    intro hXbot
    have hcard_one : Nat.card X = 1 := by
      simp [hXbot]
    exact q.2.ne_one (hXcard.symm.trans hcard_one)
  have hXq : IsPGroup q.val X := by
    exact IsPGroup.of_card (n := 1) (by simpa [pow_one] using hXcard)
  have hXle_Mσ : X ≤ section10Msigma M :=
    hXle_zpow.trans (Subgroup.zpowers_le.2 hxMσ)
  have hXle_M : X ≤ M := hXle_Mσ.trans (section14_msigma_le M)
  have hqσ : q ∈ section10SigmaPrimes M := by
    have hqdivX : q.val ∣ Nat.card X := by rw [hXcard]
    have hqdivσ : q.val ∣ Nat.card (section10Msigma M) :=
      hqdivX.trans (Subgroup.card_dvd_of_le hXle_Mσ)
    exact ((theorem_10_2_b (G := G) hM.1).1).p_in_pi_of_p_dvd_card q hqdivσ
  have hXne_top : X ≠ ⊤ := by
    intro hXtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hXtop] using hXle_M
    exact hM.1.1 (top_le_iff.mp htop_le_M)
  have hNXne_top : Subgroup.normalizer (X : Set G) ≠ ⊤ := by
    intro hNtop
    have hXnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    letI : IsSimpleGroup G := IsMinCE.simple
    rcases hXnormal.eq_bot_or_eq_top with hXbot | hXtop
    · exact hXne hXbot
    · exact hXne_top hXtop
  have hΩsubset :
      section14MsigmaElement x ⊆ section14MsigmaFamily (X : Set G) := by
    intro L hL
    refine ⟨hL.1, ?_⟩
    exact hXle_zpow.trans (Subgroup.zpowers_le.2 (hL.2 (by simp)))
  have hL_conj :
      ∀ {L : Subgroup G}, L ∈ section14MsigmaElement x →
        L ∈ section10ConjugatesContaining M X := by
    intro L hL
    have hLX : L ∈ section14MsigmaFamily (X : Set G) := hΩsubset hL
    have hXle_L : X ≤ L := hLX.2.trans (section14_msigma_le L)
    by_contra hnot
    have hnotconjL : section12NotConjugate L M := by
      intro a hLa
      have hL_eq : L = M.conjBy a⁻¹ := by
        calc
          L = (L.conjBy a).conjBy a⁻¹ := by
            simpa using (section11_conjBy_inv (G := G) L a).symm
          _ = M.conjBy a⁻¹ := by rw [hLa]
      exact hnot ⟨a⁻¹, hL_eq, hXle_L⟩
    have hqσL : q ∈ section10SigmaPrimes L := by
      have hqdivX : q.val ∣ Nat.card X := by rw [hXcard]
      have hqdivLσ : q.val ∣ Nat.card (section10Msigma L) :=
        hqdivX.trans (Subgroup.card_dvd_of_le hLX.2)
      exact ((theorem_10_2_b (G := G) hL.1).1).p_in_pi_of_p_dvd_card q hqdivLσ
    have hσdisLM :
        Disjoint (section10SigmaPrimes M) (section10SigmaPrimes L) :=
      theorem_13_9 (G := G) hM.1 hL.1 hnotconjL
    rw [Set.disjoint_left] at hσdisLM
    exact hσdisLM hqσ hqσL
  let Ωx : Type _ := {L : Subgroup G // L ∈ section14MsigmaElement x}
  haveI : Nontrivial Ωx := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨Lsub, hLsub_ne⟩ := exists_ne (⟨M, hM⟩ : Ωx)
  let L : Subgroup G := Lsub.1
  have hL : L ∈ section14MsigmaElement x := Lsub.2
  have hL_ne_M : L ≠ M := by
    intro hEq
    exact hLsub_ne (Subtype.ext hEq)
  have htrans :
      ConjugationActionTransitiveOn (Subgroup.centralizer (X : Set G))
        (section10ConjugatesContaining M X) :=
    theorem_10_1_b (G := G) (M := M) (X := X) (p := q) hM.1 hqσ hXne hXq hXle_M
  have hM_conj : M ∈ section10ConjugatesContaining M X := by
    exact ⟨1, (section8_conjBy_one (G := G) M).symm, hXle_M⟩
  have hL_conj_mem : L ∈ section10ConjugatesContaining M X := hL_conj hL
  obtain ⟨c, hc_eq⟩ := htrans M hM_conj L hL_conj_mem
  have hNX_not_le_M : ¬ Subgroup.normalizer (X : Set G) ≤ M := by
    intro hNX_le_M
    have hcM : (c : G) ∈ M := hNX_le_M (centralizer_le_normalizer X c.property)
    have hc_norm_M : (c : G) ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.le_normalizer hcM
    have hMc : M.conjBy (c : G) = M :=
      section11_conjBy_eq_of_mem_normalizer hc_norm_M
    exact hL_ne_M (hc_eq.trans hMc)
  obtain ⟨N, hN⟩ :=
    section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) (H := Subgroup.normalizer (X : Set G)) hNXne_top
  have hN_ne_M : N ≠ M := by
    intro hEq
    exact hNX_not_le_M (hEq ▸ hN.2)
  have hXle_N : X ≤ N := Subgroup.le_normalizer.trans hN.2
  have hXinf : X ≤ M ⊓ N := le_inf hXle_M hXle_N
  obtain ⟨S, hXS⟩ :=
    IsPGroup.exists_le_sylow (G := (M ⊓ N : Subgroup G)) (p := q.val)
      (hXq.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := X) (K := M ⊓ N) hXinf).symm)
  have hXleS :
      X ≤ section10AmbientSylowSubgroup (M ⊓ N) S := by
    intro y hy
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hXinf hy⟩, hXS (by simpa [Subgroup.mem_subgroupOf] using hy), rfl⟩
  have hnotconj : section12NotConjugate N M :=
    proposition_12_15_a
      (G := G) (M := M) (Mstar := N) (X := X) (q := q) (S := S)
      hM.1 hqσ hXle_M hXne hXq hN hN_ne_M hXleS
  have hσdis :
      Disjoint (section10SigmaPrimes M) (section10SigmaPrimes N) :=
    theorem_13_9 (G := G) hM.1 hN.1 hnotconj
  have hq_not_sigma_N : q ∉ section10SigmaPrimes N := by
    rw [Set.disjoint_left] at hσdis
    exact fun hqσN => hσdis hqσ hqσN
  obtain ⟨hqτ2N, hbetaN, hcomp⟩ :=
    proposition_12_15_e
      (G := G) (M := M) (Mstar := N) (X := X) (q := q) (S := S)
      hM.1 hqσ hXle_M hXne hXq hN hN_ne_M hXleS hq_not_sigma_N
  have hCx_le_CX :
      Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer (X : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro y hyX
    have hyx : y ∈ Subgroup.zpowers x := hXle_zpow hyX
    rcases Subgroup.mem_zpowers_iff.mp hyx with ⟨n, rfl⟩
    have hxg : Commute x g :=
      (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
    exact (hxg.zpow_left n).eq
  have hCX_le_N : Subgroup.centralizer (X : Set G) ≤ N :=
    (centralizer_le_normalizer X).trans hN.2
  have hCx_le_N :
      Subgroup.centralizer ({x} : Set G) ≤ N := hCx_le_CX.trans hCX_le_N
  have hxM : x ∈ M := section14_msigma_le M hxMσ
  have hMnorm : Subgroup.normalizer (M : Set G) = M := by
    apply le_antisymm
    · have hnorm_proper : Subgroup.normalizer (M : Set G) ≠ ⊤ := by
        intro hnorm_top
        have hMnormal : M.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
        letI : IsSimpleGroup G := IsMinCE.simple
        rcases (haveI := hMnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal M) with hMbot | hMtop
        · have hqM : q.val ∣ Nat.card M := hqσ.1
          have hq_one : q.val ∣ 1 := by simpa [hMbot] using hqM
          exact q.2.not_dvd_one hq_one
        · exact hM.1.1 hMtop
      exact le_of_eq ((hM.1.le_iff_eq hnorm_proper).mp
        Subgroup.le_normalizer)
    · exact Subgroup.le_normalizer
  let R : Subgroup G := elementCentralizerIn (section10Msigma N) x
  have hRle_sigma : R ≤ section10Msigma N := by
    intro y hy
    exact hy.1
  have hRle_Cx : R ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    exact hy.2
  have hxN : x ∈ N := by
    apply hCx_le_N
    simpa using (Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl x))
  let T : Subgroup N := (M ⊓ N).subgroupOf N
  have hTcomp : T.IsComplement' (section10MsigmaSubgroup N) := by
    simpa [T] using
      section14_complement_to_msigma_isComplement' (M := N) (E := M ⊓ N) hcomp
  have hM_inf_sigmaN_bot : M ⊓ section10Msigma N = ⊥ := by
    have hdisj_comp : Disjoint (section10Msigma N) (M ⊓ N) := hcomp.2.2.2
    rw [Subgroup.disjoint_def] at hdisj_comp
    apply le_bot_iff.mp
    intro y hy
    exact hdisj_comp hy.2 ⟨hy.1, section14_msigma_le N hy.2⟩
  have hbase_sigma :
      ∀ {L : Subgroup G}, L ∈ section14MsigmaElement x →
        ∃! r : section10Msigma N, L = M.conjBy (r : G) := by
    intro L hL
    obtain ⟨u, hu_eq⟩ := htrans M hM_conj L (hL_conj hL)
    have huN : (u : G) ∈ N := hCX_le_N u.property
    have huTop : (⟨u, huN⟩ : N) ∈ section10MsigmaSubgroup N ⊔ T := by
      have htop : section10MsigmaSubgroup N ⊔ T = ⊤ := hTcomp.symm.sup_eq_top
      have : (⟨u, huN⟩ : N) ∈ (⊤ : Subgroup N) := by simp
      simp [htop]
    haveI : (section10MsigmaSubgroup N).Normal := inferInstance
    rcases (Subgroup.mem_sup_of_normal_left
        (s := section10MsigmaSubgroup N) (t := T) (x := (⟨u, huN⟩ : N))).1 huTop with
      ⟨rN, hrNσ, mN, hmT, hrm⟩
    have hmMN : (mN : G) ∈ M ⊓ N := by
      simpa [T, Subgroup.mem_subgroupOf] using hmT
    have hrσ : (rN : G) ∈ section10Msigma N := by
      exact Subgroup.mem_map.mpr ⟨rN, hrNσ, rfl⟩
    let rσ : section10Msigma N := ⟨(rN : G), hrσ⟩
    have hu_eq_rm : (u : G) = (rσ : G) * (mN : G) := by
      exact (congrArg Subtype.val hrm).symm
    have hm_norm_M : (mN : G) ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.le_normalizer hmMN.1
    have hL_eq_r : L = M.conjBy (rN : G) := by
      calc
        L = M.conjBy (u : G) := hu_eq
        _ = M.conjBy ((rσ : G) * (mN : G)) := by rw [hu_eq_rm]
        _ = (M.conjBy (mN : G)).conjBy (rσ : G) := by
              simpa using
                (section11_conjBy_conjBy (G := G) M (mN : G) (rσ : G)).symm
        _ = M.conjBy (rN : G) := by
              rw [section11_conjBy_eq_of_mem_normalizer hm_norm_M]
    refine ⟨rσ, hL_eq_r, ?_⟩
    intro r' hr'
    have hfix : M.conjBy (((rσ : G)⁻¹) * (r' : G)) = M := by
      calc
        M.conjBy (((rσ : G)⁻¹) * (r' : G)) =
            (M.conjBy (r' : G)).conjBy (rσ : G)⁻¹ := by
              simpa using
                (section11_conjBy_conjBy (G := G) M (r' : G) (rσ : G)⁻¹).symm
        _ = (M.conjBy (rσ : G)).conjBy (rσ : G)⁻¹ := by rw [← hr', ← hL_eq_r]
        _ = M := section11_conjBy_inv (G := G) M (rσ : G)
    have hfix_norm : ((rσ : G)⁻¹) * (r' : G) ∈ Subgroup.normalizer (M : Set G) :=
      section14_mem_normalizer_of_conjBy_eq (G := G) (H := M) hfix
    have hdiffM : ((rσ : G)⁻¹) * (r' : G) ∈ M := by
      simpa [hMnorm] using hfix_norm
    have hdiffσ : ((rσ : G)⁻¹) * (r' : G) ∈ section10Msigma N := by
      exact (section10Msigma N).mul_mem
        ((section10Msigma N).inv_mem rσ.property) r'.property
    have hdiff1 : ((rσ : G)⁻¹) * (r' : G) = 1 := by
      have hbot : ((rσ : G)⁻¹) * (r' : G) ∈ (⊥ : Subgroup G) := by
        simpa [hM_inf_sigmaN_bot] using
          (show ((rσ : G)⁻¹) * (r' : G) ∈ M ⊓ section10Msigma N from ⟨hdiffM, hdiffσ⟩)
      simpa using hbot
    apply Subtype.ext
    calc
      (r' : G) = (rσ : G) * (((rσ : G)⁻¹) * (r' : G)) := by group
      _ = (rσ : G) := by rw [hdiff1]; simp
  have hbase :
      ∀ {L : Subgroup G}, L ∈ section14MsigmaElement x →
        ∃! r : R, L = M.conjBy (r : G) := by
    intro L hL
    obtain ⟨rσ, hL_eq_rσ, huniqσ⟩ := hbase_sigma hL
    have hx_norm_sigma : x ∈ Subgroup.normalizer (section10Msigma N : Set G) :=
      section12_le_normalizer_msigma (M := N) hxN
    have hxinv_norm_sigma : x⁻¹ ∈ Subgroup.normalizer (section10Msigma N : Set G) :=
      Subgroup.inv_mem _ hx_norm_sigma
    have hrσx_mem : x⁻¹ * (rσ : G) * x ∈ section10Msigma N := by
      have hmem_conj : x⁻¹ * (rσ : G) * x ∈ (section10Msigma N).conjBy x⁻¹ := by
        exact Subgroup.mem_map.mpr ⟨(rσ : G), rσ.property, by
          simp [mul_assoc]⟩
      simpa [section11_conjBy_eq_of_mem_normalizer hxinv_norm_sigma] using hmem_conj
    let rσx : section10Msigma N := ⟨x⁻¹ * (rσ : G) * x, hrσx_mem⟩
    have hx_norm_M : x ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer hxM
    have hxinv_norm_L : x⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
      apply Subgroup.inv_mem
      exact Subgroup.le_normalizer (section14_msigma_le L (hL.2 (by simp)))
    have hMx : M.conjBy x = M := section11_conjBy_eq_of_mem_normalizer hx_norm_M
    have hL_eq_rσx : L = M.conjBy (rσx : G) := by
      calc
        L = L.conjBy x⁻¹ := by
          rw [section11_conjBy_eq_of_mem_normalizer hxinv_norm_L]
        _ = (M.conjBy (rσ : G)).conjBy x⁻¹ := by rw [hL_eq_rσ]
        _ = ((M.conjBy x).conjBy (rσ : G)).conjBy x⁻¹ := by
          have htmp : (M.conjBy x).conjBy (rσ : G) = M.conjBy (rσ : G) := by
            rw [hMx]
          rw [← htmp]
        _ = (M.conjBy ((rσ : G) * x)).conjBy x⁻¹ := by
          exact congrArg (fun H : Subgroup G => H.conjBy x⁻¹)
            (section11_conjBy_conjBy (G := G) M x (rσ : G))
        _ = M.conjBy (x⁻¹ * ((rσ : G) * x)) := by
          simpa [mul_assoc] using
            (section11_conjBy_conjBy (G := G) M ((rσ : G) * x) x⁻¹)
        _ = M.conjBy (rσx : G) := by
          dsimp [rσx]
          simp [mul_assoc]
    have hrσx_eq : rσx = rσ := huniqσ rσx hL_eq_rσx
    have hrσx_val : x⁻¹ * (rσ : G) * x = (rσ : G) := congrArg Subtype.val hrσx_eq
    have hrσ_comm : Commute (rσ : G) x := by
      have hmul_eq := congrArg (fun t : G => x * t) hrσx_val
      change (rσ : G) * x = x * (rσ : G)
      simpa [mul_assoc] using hmul_eq
    have hrσR : (rσ : G) ∈ R := by
      exact ⟨rσ.property, Subgroup.mem_centralizer_singleton_iff.mpr hrσ_comm⟩
    refine ⟨⟨(rσ : G), hrσR⟩, hL_eq_rσ, ?_⟩
    intro r' hr'
    have hσeq :
        (⟨(r' : G), hRle_sigma r'.property⟩ : section10Msigma N) = rσ :=
      huniqσ ⟨(r' : G), hRle_sigma r'.property⟩ hr'
    apply Subtype.ext
    show (r' : G) = (rσ : G)
    exact congrArg Subtype.val hσeq
  have hsharp : section14SharpTransitiveOn R (section14MsigmaElement x) := by
    intro Q₁ hQ₁ Q₂ hQ₂
    obtain ⟨r₁, hr₁, hr₁uniq⟩ := hbase hQ₁
    obtain ⟨r₂, hr₂, hr₂uniq⟩ := hbase hQ₂
    let k : R := ⟨(r₂ : G) * (r₁ : G)⁻¹, R.mul_mem r₂.property (R.inv_mem r₁.property)⟩
    refine ⟨k, ?_, ?_⟩
    · have hk_mul : (k : G) * (r₁ : G) = (r₂ : G) := by
        dsimp [k]
        group
      calc
        Q₂ = M.conjBy (r₂ : G) := hr₂
        _ = M.conjBy ((k : G) * (r₁ : G)) := by rw [hk_mul]
        _ = (M.conjBy (r₁ : G)).conjBy (k : G) := by
          simpa using (section11_conjBy_conjBy (G := G) M (r₁ : G) (k : G)).symm
        _ = Q₁.conjBy (k : G) := by rw [hr₁]
    · intro k' hk'
      have hrk_eq :
          (⟨(k' : G) * (r₁ : G), R.mul_mem k'.property r₁.property⟩ : R) = r₂ := by
        apply hr₂uniq
        calc
          Q₂ = Q₁.conjBy (k' : G) := hk'
          _ = (M.conjBy (r₁ : G)).conjBy (k' : G) := by rw [hr₁]
          _ = M.conjBy ((k' : G) * (r₁ : G)) := by
            simpa using (section11_conjBy_conjBy (G := G) M (r₁ : G) (k' : G))
      apply Subtype.ext
      have hmul_eq : (k' : G) * (r₁ : G) = (r₂ : G) := congrArg Subtype.val hrk_eq
      calc
        (k' : G) = ((k' : G) * (r₁ : G)) * (r₁ : G)⁻¹ := by group
        _ = (r₂ : G) * (r₁ : G)⁻¹ := by rw [hmul_eq]
        _ = (k : G) := rfl
  have hCx_le_norm_R :
      Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (R : Set G) := by
    intro c hc
    have hcN : c ∈ N := hCx_le_N hc
    have hc_norm_sigma : c ∈ Subgroup.normalizer (section10Msigma N : Set G) :=
      section12_le_normalizer_msigma (M := N) hcN
    have hc_norm_Cx :
        c ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) :=
      Subgroup.le_normalizer hc
    simpa [R, elementCentralizerIn] using
      (Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hc_norm_sigma, hc_norm_Cx⟩)
  have hRnorm : section10NormalIn R (Subgroup.centralizer ({x} : Set G)) := by
    refine ⟨hRle_Cx, ?_⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hRle_Cx).2 hCx_le_norm_R
  have hRhall :
      IsHallSubgroup (section10SigmaPrimes N)
        (R.subgroupOf (Subgroup.centralizer ({x} : Set G))) := by
    let Cx : Subgroup G := Subgroup.centralizer ({x} : Set G)
    let CxN : Subgroup N := Cx.subgroupOf N
    let A : Subgroup N := section10MsigmaSubgroup N ⊓ CxN
    have hσHall : IsHallSubgroup (section10SigmaPrimes N) (section10MsigmaSubgroup N) :=
      (theorem_10_2_b (G := G) hN.1).2
    have hAHall : IsHallSubgroup (section10SigmaPrimes N) (A.subgroupOf CxN) := by
      refine isHallSubgroup_of (G := CxN) (π := section10SigmaPrimes N)
        (H := A.subgroupOf CxN) ?_ ?_
      · intro q hq_dvd
        have hcard_eq : Nat.card (A.subgroupOf CxN) = Nat.card A := by
          exact Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (H := A) (K := CxN) inf_le_right).toEquiv
        have hq_dvd_H : q.val ∣ Nat.card (section10MsigmaSubgroup N) := by
          have hq_dvd_A : q.val ∣ Nat.card A := by
            simpa [hcard_eq] using hq_dvd
          exact hq_dvd_A.trans
            (Subgroup.card_dvd_of_le (show A ≤ section10MsigmaSubgroup N from by
              simp [A]))
        exact hσHall.p_in_pi_of_p_dvd_card q hq_dvd_H
      · intro q hqπ hq_dvd_idx
        have hidx_eq : (A.subgroupOf CxN).index = A.relIndex CxN := by
          rw [← Subgroup.relIndex_top_right (H := A.subgroupOf CxN)]
          simpa [A, CxN] using
            (Subgroup.relIndex_subgroupOf
              (H := A) (K := CxN) (L := CxN) (hKL := le_rfl))
        have hrel_eq :
            A.relIndex CxN =
              (section10MsigmaSubgroup N).relIndex
                (section10MsigmaSubgroup N ⊔ CxN) := by
          calc
            A.relIndex CxN = (section10MsigmaSubgroup N).relIndex CxN := by
              simpa [A, CxN, inf_comm] using
                (Subgroup.inf_relIndex_left
                  (H := CxN) (K := section10MsigmaSubgroup N))
            _ = (section10MsigmaSubgroup N).relIndex
                  (section10MsigmaSubgroup N ⊔ CxN) := by
              rw [sup_comm]
              exact
                (Subgroup.relIndex_sup_right
                  (H := CxN) (K := section10MsigmaSubgroup N)).symm
        have hrel_dvd_idx :
            (section10MsigmaSubgroup N).relIndex
                (section10MsigmaSubgroup N ⊔ CxN) ∣
              (section10MsigmaSubgroup N).index :=
          Subgroup.relIndex_dvd_index_of_le
            (H := section10MsigmaSubgroup N)
            (K := section10MsigmaSubgroup N ⊔ CxN) le_sup_left
        have hq_dvd_Hidx : q.val ∣ (section10MsigmaSubgroup N).index := by
          have hq_dvd_rel : q.val ∣ A.relIndex CxN := by
            simpa [hidx_eq] using hq_dvd_idx
          have hq_dvd_Hrel :
              q.val ∣ (section10MsigmaSubgroup N).relIndex
                (section10MsigmaSubgroup N ⊔ CxN) := by
            simpa [hrel_eq] using hq_dvd_rel
          exact hq_dvd_Hrel.trans hrel_dvd_idx
        exact (hσHall.p_in_pi_of_p_dvd_index q hq_dvd_Hidx) hqπ
    let eCx : CxN ≃* Cx := Subgroup.subgroupOfEquivOfLe (H := Cx) (K := N) hCx_le_N
    have hmap_eq :
        (A.subgroupOf CxN).map eCx.toMonoidHom = R.subgroupOf Cx := by
      ext y
      constructor
      · intro hy
        rcases Subgroup.mem_map.mp hy with ⟨z, hz, hzy⟩
        have hzA : (z : N) ∈ A := by
          simpa [Subgroup.mem_subgroupOf] using hz
        change (y : G) ∈ R
        have hzσG : (z : G) ∈ section10Msigma N := by
          have hzσsub : (z : N) ∈ (section10Msigma N).subgroupOf N := by
            simpa [section14_msigma_subgroupOf_eq] using hzA.1
          simpa [Subgroup.mem_subgroupOf] using hzσsub
        have hzCxG : (z : G) ∈ Cx := z.property
        have hval : (z : G) = (y : G) := congrArg Subtype.val hzy
        exact hval ▸ ⟨hzσG, hzCxG⟩
      · intro hy
        have hyN : (y : G) ∈ N := hCx_le_N y.property
        let yN : CxN := ⟨⟨(y : G), hyN⟩, by
          simp [CxN, Subgroup.mem_subgroupOf]⟩
        have hyA : (yN : N) ∈ A := by
          refine ⟨?_, ?_⟩
          · have hyσsub : (yN : N) ∈ (section10Msigma N).subgroupOf N := by
              simpa [Subgroup.mem_subgroupOf] using hy.1
            simpa [section14_msigma_subgroupOf_eq] using hyσsub
          · exact yN.property
        refine Subgroup.mem_map.mpr ⟨yN, ?_, ?_⟩
        · simpa [Subgroup.mem_subgroupOf] using hyA
        · ext
          rfl
    have hHallMap :
        IsHallSubgroup (section10SigmaPrimes N)
          ((A.subgroupOf CxN).map eCx.toMonoidHom) := by
      refine isHallSubgroup_of (G := Cx) (π := section10SigmaPrimes N)
        (H := (A.subgroupOf CxN).map eCx.toMonoidHom) ?_ ?_
      · intro q hq_dvd
        exact hAHall.p_in_pi_of_p_dvd_card q
          (hq_dvd.trans (Subgroup.card_map_dvd (H := A.subgroupOf CxN) eCx.toMonoidHom))
      · intro q hqπ hq_dvd_idx
        have hidx_dvd :
            ((A.subgroupOf CxN).map eCx.toMonoidHom).index ∣
              (A.subgroupOf CxN).index :=
          Subgroup.index_map_dvd (H := A.subgroupOf CxN) eCx.surjective
        exact (hAHall.p_in_pi_of_p_dvd_index q (hq_dvd_idx.trans hidx_dvd)) hqπ
    exact hmap_eq ▸ hHallMap
  obtain ⟨rσ, hL_eq_rσ, huniqσ⟩ := hbase_sigma hL
  have hx_norm_sigma : x ∈ Subgroup.normalizer (section10Msigma N : Set G) :=
    section12_le_normalizer_msigma (M := N) hxN
  have hxinv_norm_sigma : x⁻¹ ∈ Subgroup.normalizer (section10Msigma N : Set G) :=
    Subgroup.inv_mem _ hx_norm_sigma
  have hrσx_mem : x⁻¹ * (rσ : G) * x ∈ section10Msigma N := by
    have hmem_conj : x⁻¹ * (rσ : G) * x ∈ (section10Msigma N).conjBy x⁻¹ := by
      exact Subgroup.mem_map.mpr ⟨(rσ : G), rσ.property, by
        simp [mul_assoc]⟩
    simpa [section11_conjBy_eq_of_mem_normalizer hxinv_norm_sigma] using hmem_conj
  let rσx : section10Msigma N := ⟨x⁻¹ * (rσ : G) * x, hrσx_mem⟩
  have hx_norm_M : x ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer hxM
  have hxinv_norm_L : x⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
    apply Subgroup.inv_mem
    exact Subgroup.le_normalizer (section14_msigma_le L (hL.2 (by simp)))
  have hMx : M.conjBy x = M := section11_conjBy_eq_of_mem_normalizer hx_norm_M
  have hL_eq_rσx : L = M.conjBy (rσx : G) := by
    calc
      L = L.conjBy x⁻¹ := by
        rw [section11_conjBy_eq_of_mem_normalizer hxinv_norm_L]
      _ = (M.conjBy (rσ : G)).conjBy x⁻¹ := by rw [hL_eq_rσ]
      _ = ((M.conjBy x).conjBy (rσ : G)).conjBy x⁻¹ := by
        have htmp : (M.conjBy x).conjBy (rσ : G) = M.conjBy (rσ : G) := by
          rw [hMx]
        rw [← htmp]
      _ = (M.conjBy ((rσ : G) * x)).conjBy x⁻¹ := by
        exact congrArg (fun H : Subgroup G => H.conjBy x⁻¹)
          (section11_conjBy_conjBy (G := G) M x (rσ : G))
      _ = M.conjBy (x⁻¹ * ((rσ : G) * x)) := by
        simpa [mul_assoc] using
          (section11_conjBy_conjBy (G := G) M ((rσ : G) * x) x⁻¹)
      _ = M.conjBy (rσx : G) := by
        dsimp [rσx]
        simp [mul_assoc]
  have hrσx_eq : rσx = rσ := huniqσ rσx hL_eq_rσx
  have hrσx_val : x⁻¹ * (rσ : G) * x = (rσ : G) := congrArg Subtype.val hrσx_eq
  have hrσ_comm : Commute (rσ : G) x := by
    have hmul_eq := congrArg (fun t : G => x * t) hrσx_val
    change (rσ : G) * x = x * (rσ : G)
    simpa [mul_assoc] using hmul_eq
  have hrσR : (rσ : G) ∈ R := by
    exact ⟨rσ.property, Subgroup.mem_centralizer_singleton_iff.mpr hrσ_comm⟩
  have hrσ_ne_one : (rσ : G) ≠ 1 := by
    intro hrσ1
    have hL_eq_M' : L = M := by
      calc
        L = M.conjBy (rσ : G) := hL_eq_rσ
        _ = M.conjBy (1 : G) := by rw [hrσ1]
        _ = M := section8_conjBy_one (G := G) M
    exact hL_ne_M hL_eq_M'
  have hqSupp : q ∈ section14ElementPrimeSupport x := by
    have hqdivX : q.val ∣ Nat.card X := by rw [hXcard]
    change q.val ∣ Nat.card (Subgroup.zpowers x)
    exact hqdivX.trans (Subgroup.card_dvd_of_le hXle_zpow)
  have hsuppσM : section14ElementPrimeSupport x ⊆ section10SigmaPrimes M := by
    intro p hpSupp
    have hpMsigma : p ∈ subgroupPrimeSet (section10Msigma M) := by
      exact section8_subgroupPrimeSet_mono
        (Subgroup.zpowers_le.2 hxMσ)
        (by simpa [section14ElementPrimeSupport] using hpSupp)
    exact ((theorem_10_2_b (G := G) hM.1).1).p_in_pi_of_p_dvd_card p hpMsigma
  have hxsigma' : section14IsPiElement (section10SigmaPrimes N)ᶜ x := by
    intro p hpSupp hpσN
    have hpσM : p ∈ section10SigmaPrimes M := hsuppσM hpSupp
    exact (Set.disjoint_left.mp hσdis) hpσM hpσN
  have hxcent_rσ : x ∈ elementCentralizerIn N (rσ : G) := by
    refine ⟨hxN, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hrσ_comm.symm
  have hcor :=
    corollary_14_3 (G := G) (M := N) (x := (rσ : G)) (x' := x) hN.1
      rσ.property hrσ_ne_one hx hxcent_rσ hxsigma'
  rcases hcor with hκ | hτ2
  · exfalso
    have hqκ : q ∈ section14KappaPrimes N := hκ.1 hqSupp
    have hqτ13 : q ∈ section12Tau1Primes N ∪ section12Tau3Primes N :=
      section14_kappa_subset_tau13 hqκ
    rcases hqτ13 with hqτ1 | hqτ3
    · have h1 : primeRank q.val N = 1 := hqτ1.2.2
      have h2 : primeRank q.val N = 2 := hqτ2N.2
      omega
    · have h1 : primeRank q.val N = 1 := hqτ3.2.2
      have h2 : primeRank q.val N = 2 := hqτ2N.2
      omega
  have hRne : R ≠ ⊥ := by
    intro hRbot
    have hrbot : (rσ : G) ∈ (⊥ : Subgroup G) := by
      simpa [hRbot] using hrσR
    exact hrσ_ne_one (Subgroup.mem_bot.mp hrbot)
  have hcent_prod :
      ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) =
        (elementCentralizerIn (M ⊓ N) x : Set G) * (R : Set G) := by
    ext c
    constructor
    · intro hc
      have hcN : c ∈ N := hCx_le_N hc
      have hcTop : (⟨c, hcN⟩ : N) ∈ section10MsigmaSubgroup N ⊔ T := by
        have htop : section10MsigmaSubgroup N ⊔ T = ⊤ := hTcomp.symm.sup_eq_top
        have : (⟨c, hcN⟩ : N) ∈ (⊤ : Subgroup N) := by simp
        simp [htop]
      haveI : (section10MsigmaSubgroup N).Normal := inferInstance
      rcases (Subgroup.mem_sup_of_normal_left
          (s := section10MsigmaSubgroup N) (t := T) (x := (⟨c, hcN⟩ : N))).1 hcTop with
        ⟨rN, hrNσ, mN, hmT, hrm⟩
      have hmMN : (mN : G) ∈ M ⊓ N := by
        simpa [T, Subgroup.mem_subgroupOf] using hmT
      have hrσN : (rN : G) ∈ section10Msigma N := by
        exact Subgroup.mem_map.mpr ⟨rN, hrNσ, rfl⟩
      let rσc : section10Msigma N := ⟨(rN : G), hrσN⟩
      have hc_eq_rm : c = (rσc : G) * (mN : G) := by
        exact (congrArg Subtype.val hrm).symm
      have hm_norm_M : (mN : G) ∈ Subgroup.normalizer (M : Set G) :=
        Subgroup.le_normalizer hmMN.1
      let Lc : Subgroup G := M.conjBy c
      have hLc_eq_rσ : Lc = M.conjBy (rσc : G) := by
        dsimp [Lc]
        calc
          M.conjBy c = M.conjBy ((rσc : G) * (mN : G)) := by rw [hc_eq_rm]
          _ = (M.conjBy (mN : G)).conjBy (rσc : G) := by
                simpa using
                  (section11_conjBy_conjBy (G := G) M (mN : G) (rσc : G)).symm
          _ = M.conjBy (rσc : G) := by
                rw [section11_conjBy_eq_of_mem_normalizer hm_norm_M]
      have huniqσc :
          ∀ r' : section10Msigma N, Lc = M.conjBy (r' : G) → r' = rσc := by
        intro r' hr'
        have hfix : M.conjBy (((rσc : G)⁻¹) * (r' : G)) = M := by
          calc
            M.conjBy (((rσc : G)⁻¹) * (r' : G)) =
                (M.conjBy (r' : G)).conjBy (rσc : G)⁻¹ := by
                  simpa using
                    (section11_conjBy_conjBy (G := G) M (r' : G) (rσc : G)⁻¹).symm
            _ = (M.conjBy (rσc : G)).conjBy (rσc : G)⁻¹ := by rw [← hr', ← hLc_eq_rσ]
            _ = M := section11_conjBy_inv (G := G) M (rσc : G)
        have hfix_norm :
            ((rσc : G)⁻¹) * (r' : G) ∈ Subgroup.normalizer (M : Set G) :=
          section14_mem_normalizer_of_conjBy_eq (G := G) (H := M) hfix
        have hdiffM : ((rσc : G)⁻¹) * (r' : G) ∈ M := by
          simpa [hMnorm] using hfix_norm
        have hdiffσ : ((rσc : G)⁻¹) * (r' : G) ∈ section10Msigma N := by
          exact (section10Msigma N).mul_mem
            ((section10Msigma N).inv_mem rσc.property) r'.property
        have hdiff1 : ((rσc : G)⁻¹) * (r' : G) = 1 := by
          have hbot : ((rσc : G)⁻¹) * (r' : G) ∈ (⊥ : Subgroup G) := by
            simpa [hM_inf_sigmaN_bot] using
              (show ((rσc : G)⁻¹) * (r' : G) ∈ M ⊓ section10Msigma N from ⟨hdiffM, hdiffσ⟩)
          simpa using hbot
        apply Subtype.ext
        calc
          (r' : G) = (rσc : G) * (((rσc : G)⁻¹) * (r' : G)) := by group
          _ = (rσc : G) := by rw [hdiff1]; simp
      have hxLc : x ∈ Lc := by
        dsimp [Lc]
        exact Subgroup.mem_map.mpr ⟨x, hxM, by
          have hcomm : Commute c x :=
            Subgroup.mem_centralizer_singleton_iff.mp hc
          simp [mul_assoc, hcomm.eq]⟩
      have hxinv_norm_Lc : x⁻¹ ∈ Subgroup.normalizer (Lc : Set G) := by
        apply Subgroup.inv_mem
        exact Subgroup.le_normalizer hxLc
      have hrσxc_mem : x⁻¹ * (rσc : G) * x ∈ section10Msigma N := by
        have hmem_conj : x⁻¹ * (rσc : G) * x ∈ (section10Msigma N).conjBy x⁻¹ := by
          exact Subgroup.mem_map.mpr ⟨(rσc : G), rσc.property, by
            simp [mul_assoc]⟩
        simpa [section11_conjBy_eq_of_mem_normalizer hxinv_norm_sigma] using hmem_conj
      let rσxc : section10Msigma N := ⟨x⁻¹ * (rσc : G) * x, hrσxc_mem⟩
      have hLc_eq_rσxc : Lc = M.conjBy (rσxc : G) := by
        calc
          Lc = Lc.conjBy x⁻¹ := by
            rw [section11_conjBy_eq_of_mem_normalizer hxinv_norm_Lc]
          _ = (M.conjBy (rσc : G)).conjBy x⁻¹ := by rw [hLc_eq_rσ]
          _ = ((M.conjBy x).conjBy (rσc : G)).conjBy x⁻¹ := by
            have htmp : (M.conjBy x).conjBy (rσc : G) = M.conjBy (rσc : G) := by
              rw [hMx]
            rw [← htmp]
          _ = (M.conjBy ((rσc : G) * x)).conjBy x⁻¹ := by
            exact congrArg (fun H : Subgroup G => H.conjBy x⁻¹)
              (section11_conjBy_conjBy (G := G) M x (rσc : G))
          _ = M.conjBy (x⁻¹ * ((rσc : G) * x)) := by
            simpa [mul_assoc] using
              (section11_conjBy_conjBy (G := G) M ((rσc : G) * x) x⁻¹)
          _ = M.conjBy (rσxc : G) := by
            dsimp [rσxc]
            simp [mul_assoc]
      have hrσxc_eq : rσxc = rσc := huniqσc rσxc hLc_eq_rσxc
      have hrσxc_val :
          x⁻¹ * (rσc : G) * x = (rσc : G) := congrArg Subtype.val hrσxc_eq
      have hrσc_comm : Commute (rσc : G) x := by
        have hmul_eq := congrArg (fun t : G => x * t) hrσxc_val
        change (rσc : G) * x = x * (rσc : G)
        simpa [mul_assoc] using hmul_eq
      have hrσcR : (rσc : G) ∈ R := by
        exact ⟨rσc.property, Subgroup.mem_centralizer_singleton_iff.mpr hrσc_comm⟩
      have hm_comm : Commute (mN : G) x := by
        have hc_comm : Commute c x :=
          Subgroup.mem_centralizer_singleton_iff.mp hc
        have hleft :
            (rσc : G) * ((mN : G) * x) =
              (rσc : G) * (x * (mN : G)) := by
          calc
            (rσc : G) * ((mN : G) * x) = c * x := by rw [hc_eq_rm]; group
            _ = x * c := hc_comm.eq
            _ = x * ((rσc : G) * (mN : G)) := by rw [hc_eq_rm]
            _ = (rσc : G) * (x * (mN : G)) := by
              calc
                x * ((rσc : G) * (mN : G)) = (x * (rσc : G)) * (mN : G) := by
                  group
                _ = ((rσc : G) * x) * (mN : G) := by
                  rw [← hrσc_comm.eq]
                _ = (rσc : G) * (x * (mN : G)) := by
                  group
        have hcancel := congrArg (fun t : G => (rσc : G)⁻¹ * t) hleft
        show (mN : G) * x = x * (mN : G)
        simpa [mul_assoc] using hcancel
      have hmCx : (mN : G) ∈ elementCentralizerIn (M ⊓ N) x := by
        exact ⟨hmMN, Subgroup.mem_centralizer_singleton_iff.mpr hm_comm⟩
      have hmCxG : (mN : G) ∈ Subgroup.centralizer ({x} : Set G) := hmCx.2
      have hm_norm_R : (mN : G) ∈ Subgroup.normalizer (R : Set G) :=
        hCx_le_norm_R hmCxG
      have hminv_norm_R : (mN : G)⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
        Subgroup.inv_mem _ hm_norm_R
      have hr'R : (mN : G)⁻¹ * (rσc : G) * (mN : G) ∈ R := by
        simpa using
          (Subgroup.mem_normalizer_iff.mp hminv_norm_R (rσc : G)).1 hrσcR
      refine ⟨(mN : G), hmCx, (mN : G)⁻¹ * (rσc : G) * (mN : G), hr'R, ?_⟩
      calc
        (mN : G) * ((mN : G)⁻¹ * (rσc : G) * (mN : G)) = (rσc : G) * (mN : G) := by
          group
        _ = c := hc_eq_rm.symm
    · rintro ⟨m, hmCx, r, hrR, rfl⟩
      exact (Subgroup.centralizer ({x} : Set G)).mul_mem hmCx.2 (hRle_Cx hrR)
  have hτ2sigma : section12Tau2Primes N ⊆ section10SigmaPrimes M := by
    intro p hpτ2N
    obtain ⟨E₁₂N, E₁N, E₂N, E₃N, hEN⟩ :=
      section14_exists_EData_of_complement (G := G) (M := N) (E := M ⊓ N) hN.1 hcomp
    obtain ⟨A, hA⟩ :=
      section12_exists_rankTwo_in_E_of_tau2
        (G := G) (M := N) (E := M ⊓ N) (E₁₂ := E₁₂N)
        (E₁ := E₁N) (E₂ := E₂N) (E₃ := E₃N) hN.1 hEN hpτ2N
    have hAnormMN : section10NormalIn A (M ⊓ N) :=
      (corollary_12_6_a
        (G := G) (M := N) (E := M ⊓ N) (E₁₂ := E₁₂N)
        (E₁ := E₁N) (E₂ := E₂N) (E₃ := E₃N) (A := A) (p := p)
        hN.1 hEN hpτ2N hA).1
    have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
      section12_rankTwo_mono hA inf_le_left
    by_contra hp_not_sigma_M
    letI : Fact p.val.Prime := ⟨p.2⟩
    have hAelem := section12_rankTwo_elementary hA_M
    haveI : IsElementaryAbelian p.val A := hAelem.2
    have hprank_ge : 2 ≤ primeRank p.val M := by
      let A' : Subgroup M := A.subgroupOf M
      have hA'p : IsPGroup p.val A' :=
        (IsElementaryAbelian.isPGroup p.val A).of_equiv
          (Subgroup.subgroupOfEquivOfLe (H := A) (K := M) (section12_rankTwo_le hA_M)).symm
      have hA'comm : IsMulCommutative A' := by
        exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := M)
      have hgenA : 2 ≤ generatorRank A :=
        section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
          (p := p.val) hAelem.1
      have hgen_eq : generatorRank A' = generatorRank A := by
        rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
        exact Group.rank_congr
          (Subgroup.subgroupOfEquivOfLe (H := A) (K := M) (section12_rankTwo_le hA_M))
      have hgenA' : 2 ≤ generatorRank A' := by
        simpa [hgen_eq] using hgenA
      exact hgenA'.trans
        (section12_generatorRank_le_primeRank_of_subgroup
          (R := M) (q := p.val) (A := A') hA'p hA'comm)
    have hpM : p ∈ subgroupPrimeSet M := section12_rankTwo_prime_mem hA_M
    have hpτ2M : p ∈ section12Tau2Primes M := by
      have hp_le_two : primeRank p.val M ≤ 2 := by
        by_contra hnot
        have hgt : 2 < primeRank p.val M := by omega
        exact hp_not_sigma_M
          (section12_sigmaPrimes_mem_of_alphaPrimes_mem hM.1 ⟨hpM, hgt⟩)
      have hprank_eq : primeRank p.val M = 2 := by omega
      simpa [section12Tau2Primes] using ⟨hp_not_sigma_M, hprank_eq⟩
    have hAπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ A := by
      have hAp : IsPGroup p.val A := IsElementaryAbelian.isPGroup p.val A
      have hAsingle : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) A :=
        section8_isPiSubgroup_singleton_of_isPGroup hAp
      intro r hrA
      have hr_single : r ∈ ({p} : Set Nat.Primes) := hAsingle r hrA
      rw [Set.mem_compl_iff]
      rcases Set.mem_singleton_iff.mp hr_single with rfl
      exact hp_not_sigma_M
    obtain ⟨EM, E₁₂M, E₁M, E₂M, E₃M, hEM, hAEM⟩ :=
      section14_exists_EData_containing
        (G := G) (M := M) (K := A) hM.1 (section12_rankTwo_le hA_M) hAπ
    have hA_EM : A ∈ section12RankTwoElementaryAbelianIn p EM := by
      exact ⟨hAEM, section12_rankTwo_elementary hA⟩
    have hNormIn_eq_EM :
        subgroupNormalizerIn M (A : Set G) = EM :=
      (corollary_12_6_b
        (G := G) (M := M) (E := EM) (E₁₂ := E₁₂M) (E₁ := E₁M)
        (E₂ := E₂M) (E₃ := E₃M) (A := A) (p := p)
        hM.1 hEM hpτ2M hA_EM).2.1
    have hxMN : x ∈ M ⊓ N := ⟨hxM, hxN⟩
    have hx_norm_A : x ∈ Subgroup.normalizer (A : Set G) := by
      have hMN_le_normA :
          M ⊓ N ≤ Subgroup.normalizer (A : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hAnormMN.1).1 hAnormMN.2
      exact hMN_le_normA hxMN
    have hx_normIn_A : x ∈ subgroupNormalizerIn M (A : Set G) := by
      exact mem_subgroupNormalizerIn.mpr ⟨hx_norm_A, hxM⟩
    have hxEM : x ∈ EM := by
      simpa [hNormIn_eq_EM] using hx_normIn_A
    have hbotEM : x ∈ (⊥ : Subgroup G) := by
      have hdisjEM : Disjoint (section10Msigma M) EM := hEM.1.2.2.2
      exact Subgroup.disjoint_def.mp hdisjEM hxMσ hxEM
    exact hx (Subgroup.mem_bot.mp hbotEM)
  have hNnotP1 : N ∉ section14MFamilyP1 G := by
    intro hNP1
    have hqpos : 1 ≤ primeRank q.val N := by
      have hqrank : primeRank q.val N = 2 := hqτ2N.2
      omega
    have hqNprime : q ∈ subgroupPrimeSet N :=
      section14_prime_dvd_card_of_primeRank_pos
        (R := N) (p := q) hqpos
    have hqκ : q ∈ section14KappaPrimes N := by
      rw [hNP1.2]
      exact ⟨hqNprime, hqτ2N.1⟩
    have hqτ13 : q ∈ section12Tau1Primes N ∪ section12Tau3Primes N :=
      section14_kappa_subset_tau13 hqκ
    rcases hqτ13 with hqτ1 | hqτ3
    · have h1 : primeRank q.val N = 1 := hqτ1.2.2
      have h2 : primeRank q.val N = 2 := hqτ2N.2
      omega
    · have h1 : primeRank q.val N = 1 := hqτ3.2.2
      have h2 : primeRank q.val N = 2 := hqτ2N.2
      omega
  have hNF_or_P2 : N ∈ section14MFamilyF G ∪ section14MFamilyP2 G := by
    by_cases hκempty : section14KappaPrimes N = ∅
    · exact Or.inl ⟨hN.1, hκempty⟩
    · have hNP : N ∈ section14MFamilyP G := by
        exact ⟨hN.1, Set.nonempty_iff_ne_empty.mpr hκempty⟩
      exact Or.inr ⟨hNP, by
        intro hEq
        exact hNnotP1 ⟨hNP, hEq⟩⟩
  have hNchoice : N = section14N x := by
    obtain ⟨N0, hN0, huniqN0⟩ := theorem_14_4_unique_N (x := x) hx hσ hcard
    have hNCx :
        N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) := by
      rw [hτ2.2.2]
      simp
    have hNx :
        section14N x ∈
          section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
      section14N_mem_of_nonsingleton hx hσ hcard
    have hN_eq : N = N0 := huniqN0 N hNCx
    have hNx_eq : section14N x = N0 := huniqN0 (section14N x) hNx
    exact hN_eq.trans hNx_eq.symm
  have hRchoice : section14R x = R := by
    rw [section14R_eq_of_nonsingleton hx hσ hcard, ← hNchoice]
  have hNormalHallRx :
      section14NormalHallIn (section14R x) (Subgroup.centralizer ({x} : Set G)) := by
    have hNormalHallR :
        section14NormalHallIn R (Subgroup.centralizer ({x} : Set G)) := by
      exact ⟨hRle_Cx, hRnorm, ⟨section10SigmaPrimes N, hRhall⟩⟩
    simpa [hRchoice] using hNormalHallR
  have hSharpRx :
      section14SharpTransitiveOn (section14R x) (section14MsigmaElement x) := by
    simpa [hRchoice] using hsharp
  have hNData : section14Theorem14_4NData x (section14R x) (section14N x) M := by
    refine ⟨section14R_eq_of_nonsingleton hx hσ hcard, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hRchoice] using hRne
    · simpa [hRchoice, hNchoice] using hcent_prod
    · simpa [hNchoice] using hτ2.1
    · simpa [hNchoice] using hτ2sigma
    · simpa [hNchoice] using hbetaN
    · simpa [hNchoice] using hcomp
    · simpa [hNchoice] using hNF_or_P2
  exact ⟨hNormalHallRx, hSharpRx, hNData⟩

/-- Theorem 14.4: `C_G(x)` has `R(x)` acting sharply transitively on
`𝓜_σ(x)`, and in the nonsingleton case has a unique maximal overgroup. -/
public theorem CFSG.theorem_14_4
    {x : G} (hx : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty) :
    section14NormalHallIn (section14R x) (Subgroup.centralizer ({x} : Set G)) ∧
      section14SharpTransitiveOn (section14R x) (section14MsigmaElement x) ∧
      (1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x} →
        ∃ N : Subgroup G,
          N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
            (∀ M : Subgroup G, M ∈ section14MsigmaElement x →
              section14Theorem14_4NData x (section14R x) N M) ∧
            ∀ N' : Subgroup G,
              N' ∈ section9MaximalSubgroupsContaining
                (Subgroup.centralizer ({x} : Set G)) →
              N' = N) := by
  by_cases hcard : 1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x}
  · let M : Subgroup G := Classical.choose hσ
    have hM : M ∈ section14MsigmaElement x := Classical.choose_spec hσ
    obtain ⟨hHall, hSharp, _hDataM⟩ :=
      section14_nonsingleton_member_data (x := x) hx hσ hcard hM
    refine ⟨hHall, hSharp, ?_⟩
    intro _hcard'
    refine ⟨section14N x, section14N_mem_of_nonsingleton hx hσ hcard, ?_, ?_⟩
    · intro L hL
      exact (section14_nonsingleton_member_data (x := x) hx hσ hcard hL).2.2
    · intro N' hN'
      obtain ⟨N0, _hN0, huniqN0⟩ := theorem_14_4_unique_N (x := x) hx hσ hcard
      have hNx :
          section14N x ∈
            section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
        section14N_mem_of_nonsingleton hx hσ hcard
      have hN'_eq : N' = N0 := huniqN0 N' hN'
      have hNx_eq : section14N x = N0 := huniqN0 (section14N x) hNx
      exact hN'_eq.trans hNx_eq.symm
  · have hcard_one :
        Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x} = 1 := by
      have hΩne :
          Nonempty {M : Subgroup G // M ∈ section14MsigmaElement x} := by
        rcases hσ with ⟨M, hM⟩
        exact ⟨⟨M, hM⟩⟩
      have hpos :
          0 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x} :=
        Nat.card_pos_iff.mpr ⟨hΩne, inferInstance⟩
      omega
    have hcard' :
        ¬ 1 < (section14MsigmaElement x).ncard := by
      simpa only [Nat.card_coe_set_eq] using hcard
    have hRbot : section14R x = ⊥ := by
      simp [section14R, hx, hσ, hcard']
    have hHallBot :
        section14NormalHallIn (⊥ : Subgroup G)
          (Subgroup.centralizer ({x} : Set G)) := by
      refine ⟨bot_le, ?_, ?_⟩
      · exact ⟨bot_le, inferInstance⟩
      · refine ⟨∅, ?_⟩
        refine isHallSubgroup_of (G := Subgroup.centralizer ({x} : Set G))
          (π := (∅ : Set Nat.Primes))
          ((⊥ : Subgroup G).subgroupOf (Subgroup.centralizer ({x} : Set G))) ?_ ?_
        · intro p hpbot
          exact False.elim (p.2.not_dvd_one (by
            simpa [Subgroup.bot_subgroupOf] using hpbot))
        · intro p hpπ
          simp at hpπ
    have hSharpBot :
        section14SharpTransitiveOn (⊥ : Subgroup G) (section14MsigmaElement x) := by
      intro Q₁ hQ₁ Q₂ hQ₂
      let Ωx : Type _ := {M : Subgroup G // M ∈ section14MsigmaElement x}
      have hsub : Subsingleton Ωx :=
        (Nat.card_eq_one_iff_unique.mp hcard_one).1
      let Q₁' : Ωx := ⟨Q₁, hQ₁⟩
      let Q₂' : Ωx := ⟨Q₂, hQ₂⟩
      have hQeq : Q₁ = Q₂ := by
        exact congrArg Subtype.val
          (show Q₁' = Q₂' from Subsingleton.elim _ _)
      refine ⟨1, ?_, ?_⟩
      · simpa using hQeq.symm.trans (section8_conjBy_one (G := G) Q₁).symm
      · intro k hk
        exact Subsingleton.elim _ _
    refine ⟨by simpa [hRbot] using hHallBot, by simpa [hRbot] using hSharpBot, ?_⟩
    intro hcard'
    exact False.elim (hcard hcard')

/-- Theorem 14.4(a). -/
public theorem CFSG.theorem_14_4_a
    {x : G} (hx : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty)
    (hcard : 1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x})
    {M : Subgroup G} (hM : M ∈ section14MsigmaElement x) :
    section14R x = elementCentralizerIn (section10Msigma (section14N x)) x ∧
      section14R x ≠ ⊥ := by
  have hData := (section14_nonsingleton_member_data (x := x) hx hσ hcard hM).2.2
  exact ⟨hData.1, hData.2.1⟩

/-- Theorem 14.4(b). -/
public theorem CFSG.theorem_14_4_b
    {x : G} (hx : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty)
    (hcard : 1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x})
    {M : Subgroup G} (hM : M ∈ section14MsigmaElement x) :
    ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) =
      (elementCentralizerIn (M ⊓ section14N x) x : Set G) * (section14R x : Set G) := by
  exact (section14_nonsingleton_member_data (x := x) hx hσ hcard hM).2.2.2.2.1

/-- Theorem 14.4(c). -/
public theorem CFSG.theorem_14_4_c
    {x : G} (hx : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty)
    (hcard : 1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x})
    {M : Subgroup G} (hM : M ∈ section14MsigmaElement x) :
    section14ElementPrimeSupport x ⊆ section12Tau2Primes (section14N x) ∧
      section12Tau2Primes (section14N x) ⊆ section10SigmaPrimes M := by
  have hData := (section14_nonsingleton_member_data (x := x) hx hσ hcard hM).2.2
  exact ⟨hData.2.2.2.1, hData.2.2.2.2.1⟩


/-- Theorem 14.4(e). -/
public theorem CFSG.theorem_14_4_e
    {x : G} (hx : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty)
    (hcard : 1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x})
    {M : Subgroup G} (hM : M ∈ section14MsigmaElement x) :
    section12ComplementIn (section14N x) (section10Msigma (section14N x))
      (M ⊓ section14N x) := by
  have hData := (section14_nonsingleton_member_data (x := x) hx hσ hcard hM).2.2
  exact hData.2.2.2.2.2.2.1

/-- Theorem 14.4(f), D. Sibley's assertion. -/
public theorem CFSG.theorem_14_4_f
    {x : G} (hx : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty)
    (hcard : 1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x}) :
    section14N x ∈ section14MFamilyF G ∪ section14MFamilyP2 G := by
  let M : Subgroup G := Classical.choose hσ
  have hM : M ∈ section14MsigmaElement x := Classical.choose_spec hσ
  have hData := (section14_nonsingleton_member_data (x := x) hx hσ hcard hM).2.2
  exact hData.2.2.2.2.2.2.2

/-- The set `M̃ = {x x' | x ∈ M_σ# and x' ∈ R(x)}`. -/
@[expose] public def CFSG.section14Tilde (M : Subgroup G) : Set G :=
  {g | ∃ x : G, x ∈ section10Msigma M ∧ x ≠ 1 ∧
      ∃ x' : G, x' ∈ section14R x ∧ g = x * x'}

end Section14
