module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection16.theorem_16_I
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_1
import Mathlib.GroupTheory.Schreier
import Mathlib.Order.Preorder.Finite

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Theorem 16 ii from BG Section 16 -/

section MainResults

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_msigma_nonidentity_mem_ASet_public
    {M U : Subgroup G} {x : G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (hxσ : x ∈ section10Msigma M)
    (hxne : x ≠ 1) :
    x ∈ section16ASet M U := by
  classical
  have hxM : x ∈ M := section16_msigma_le (G := G) M hxσ
  have hxCent : x ∈ elementCentralizerIn (section10Msigma M) x := by
    refine ⟨hxσ, ?_⟩
    change x ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hCentNe :
      elementCentralizerIn (section10Msigma M) x ≠ ⊥ := by
    intro hbot
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using hxCent
    exact hxne (by simpa using hxbot)
  refine ⟨⟨hxM, hCentNe⟩, ?_, hxne⟩
  exact ⟨1, U.one_mem, x, hxσ, by simp⟩

public theorem CFSG.section16_ASet_le_normalizer_public
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section16KUData M K U) :
    M ≤ Subgroup.normalizer (section16ASet M U) := by
  classical
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hconj_mem :
      ∀ {m a : G}, m ∈ M → a ∈ section16ASet M U →
        m * a * m⁻¹ ∈ section16ASet M U := by
    intro m a hm ha
    by_cases haσ : a ∈ section10Msigma M
    · have hmNormSigma : m ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
        section12_le_normalizer_msigma (M := M) hm
      have hconjσ : m * a * m⁻¹ ∈ section10Msigma M :=
        (Subgroup.mem_normalizer_iff.mp hmNormSigma a).1 haσ
      have hconjne : m * a * m⁻¹ ≠ 1 := by
        intro h
        exact ha.2.2 (by
          have h' := congrArg (fun t : G => m⁻¹ * t * m) h
          simpa [mul_assoc] using h')
      exact section16_msigma_nonidentity_mem_ASet_public (G := G) hM hconjσ hconjne
    · exact
        (section16_ASet_diff_msigma_conj_mem_of_mem_M
          (G := G) (M := M) (K := K) (U := U) hM hKU15 hm ⟨ha, haσ⟩).1
  intro m hm
  change ∀ a : G, a ∈ section16ASet M U ↔
    m * a * m⁻¹ ∈ section16ASet M U
  intro a
  constructor
  · exact hconj_mem hm
  · intro hma
    have hback : m⁻¹ * (m * a * m⁻¹) * (m⁻¹)⁻¹ ∈ section16ASet M U :=
      hconj_mem (M.inv_mem hm) hma
    simpa [mul_assoc] using hback

private theorem CFSG.section16_ASet_diff_msigma_centralizer_le
    {M K U : Subgroup G} {a : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (ha : a ∈ section16ASet M U \ (section10Msigma M : Set G)) :
    Subgroup.centralizer ({a} : Set G) ≤ M := by
  classical
  rcases section16_ASet_diff_msigma_exists_prime_compl_zpow
      (G := G) (M := M) (K := K) (U := U) hM hKU ha with
    ⟨n, q, horder, hqcompl⟩
  have huniq :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer ({a ^ n} : Set G)) = {M} :=
    section16_ASet_diff_msigma_zpow_unique_centralizer
      (G := G) (M := M) (K := K) (U := U) hM ha horder hqcompl
  have hcentPow_le_M : Subgroup.centralizer ({a ^ n} : Set G) ≤ M := by
    have hMcont :
        M ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({a ^ n} : Set G)) := by
      simp [huniq]
    exact hMcont.2
  intro c hc
  apply hcentPow_le_M
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcomm : Commute c a := by
    change c * a = a * c
    exact Subgroup.mem_centralizer_singleton_iff.mp hc
  exact (hcomm.zpow_right n).eq


public theorem CFSG.section16_ASet_diff_msigma_unique_centralizer_of_coprime_public
    {M K U : Subgroup G} {a : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section16KUData M K U)
    (ha : a ∈ section16ASet M U \ (section10Msigma M : Set G))
    (hcop : Nat.Coprime (orderOf a) (Nat.card (section10Msigma M))) :
    section9MaximalSubgroupsContaining
      (Subgroup.centralizer ({a} : Set G)) = {M} := by
  classical
  have hKU15 : section15KUData M K U := by
    simpa [section16KUData] using hKU
  rcases section16_ASet_diff_msigma_conj_U_hat_of_coprime
      (G := G) (M := M) (K := K) (U := U) hM hKU15 ha hcop with
    ⟨u, m, huU, huHat, hune, hm, haConj⟩
  exact section16_centralizer_unique_of_conj_U_hat_element
    (G := G) (M := M) (K := K) (U := U) hM hKU15 hm huU huHat hune haConj


omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_AZeroSet_subset_ASet_of_K_eq_bot
    {M K U : Subgroup G}
    (hKU : section15KUData M K U)
    (hKbot : K = ⊥) :
    section16AZeroSet M K ⊆ section16ASet M U := by
  classical
  intro a ha
  rcases ha with ⟨haHat, haNotConj, hane⟩
  refine ⟨haHat, ?_, hane⟩
  have haM : a ∈ M := haHat.1
  have hcomp : section12ComplementIn M (section10Msigma M) (K ⊔ U) := hKU.2.2.1
  have haJoin : a ∈ section10Msigma M ⊔ U := by
    have haJoin0 : a ∈ section10Msigma M ⊔ (K ⊔ U) := by
      simpa [← hcomp.2.2.1] using haM
    simpa [hKbot] using haJoin0
  let N : Subgroup G := U ⊔ section10Msigma M
  have hUnorm : U ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hKU.2.2.2.1.1.trans (section12_le_normalizer_msigma (M := M))
  have hNset : ((N : Subgroup G) : Set G) =
      (U : Set G) * (section10Msigma M : Set G) := by
    simpa [N] using
      Subgroup.coe_mul_of_left_le_normalizer_right U (section10Msigma M) hUnorm
  have haN : a ∈ N := by
    simpa [N, sup_comm] using haJoin
  simpa [← hNset] using haN

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_mem_normalizer_singleton_of_mem_centralizer_singleton
    {a c : G}
    (hc : c ∈ Subgroup.centralizer ({a} : Set G)) :
    c ∈ Subgroup.normalizer ({a} : Set G) := by
  have hcomm : c * a = a * c :=
    Subgroup.mem_centralizer_singleton_iff.mp hc
  have hfix : c * a * c⁻¹ = a := by
    calc
      c * a * c⁻¹ = a * c * c⁻¹ := by rw [hcomm]
      _ = a := by simp [mul_assoc]
  change ∀ y : G, y ∈ ({a} : Set G) ↔ c * y * c⁻¹ ∈ ({a} : Set G)
  intro y
  constructor
  · intro hy
    have hy_eq : y = a := by simpa using hy
    simp [hy_eq, hfix]
  · intro hy
    have hy_eq : c * y * c⁻¹ = a := by simpa using hy
    have hfix_inv : c⁻¹ * a * c = a := by
      have h := congrArg (fun z : G => c⁻¹ * z * c) hfix
      simpa [mul_assoc] using h.symm
    have hy_a : y = a := by
      calc
        y = c⁻¹ * (c * y * c⁻¹) * c := by group
        _ = c⁻¹ * a * c := by rw [hy_eq]
        _ = a := hfix_inv
    simp [hy_a]

private theorem CFSG.section16_A0_diff_A_centralizer_le
    {M K U : Subgroup G} {a : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (ha : a ∈ section16AZeroSet M K \ section16ASet M U) :
    Subgroup.centralizer ({a} : Set G) ≤ M := by
  classical
  by_cases hKbot : K = ⊥
  · have haA : a ∈ section16ASet M U :=
      section16_AZeroSet_subset_ASet_of_K_eq_bot
        (G := G) (M := M) (K := K) (U := U) hKU hKbot ha.1
    exact False.elim (ha.2 haA)
  · have hMP : M ∈ section14MFamilyP G :=
      section16_MFamilyP_of_nontrivial_hall_kappa
        (G := G) hM hKU.1 hKbot
    have hConj :
        a ∈ section16ConjugatesOfSetBySet
          (section16HatZ K (section16Kstar M K)) (M : Set G) := by
      have hEq :=
        section16_conjugates_hatZ_eq_A0_diff_A
          (G := G) (M := M) (K := K) (U := U) hMP hKU
      simpa [hEq] using ha
    rcases hConj with ⟨t, htHat, m, hmM, ha_eq⟩
    intro c hc
    let d : G := m⁻¹ * c * m
    have hdCent : d ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcComm : c * a = a * c :=
        Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [ha_eq] at hcComm
      dsimp [d]
      calc
        (m⁻¹ * c * m) * t =
            m⁻¹ * (c * (m * t * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * t * m⁻¹) * c) * m := by rw [hcComm]
        _ = t * (m⁻¹ * c * m) := by group
    have hdNorm : d ∈ Subgroup.normalizer ({t} : Set G) :=
      section16_mem_normalizer_singleton_of_mem_centralizer_singleton
        (G := G) (a := t) (c := d) hdCent
    have hnormSingleton :
        Subgroup.normalizer ({t} : Set G) =
          section16ZSubgroup K (section16Kstar M K) := by
      have htHatW : t ∈ section16HatW K (section16Kstar M K) := by
        simpa [section16HatW, section16HatZ, section16ZSubgroup] using htHat
      exact section16_hatW_subset_normalizer_eq_of_caseP
        (G := G) (M := M) (K := K) (W0 := ({t} : Set G))
        hMP hKU.1 (Set.singleton_nonempty t) (by
          intro z hz
          have hz_eq : z = t := by simpa using hz
          simpa [hz_eq] using htHatW)
    have hdZ : d ∈ section16ZSubgroup K (section16Kstar M K) := by
      simpa [hnormSingleton] using hdNorm
    have hZleM : section16ZSubgroup K (section16Kstar M K) ≤ M := by
      refine sup_le hKU.1.1 ?_
      intro z hz
      exact section16_msigma_le (G := G) M hz.1
    have hdM : d ∈ M := hZleM hdZ
    have hc_eq : c = m * d * m⁻¹ := by
      dsimp [d]
      group
    rw [hc_eq]
    exact M.mul_mem (M.mul_mem hmM hdM) (M.inv_mem hmM)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_mem_M_of_mem_AChoice
    {M K U : Subgroup G} {X : Set G} {x : G}
    (hX : section16AChoice M K U X)
    (hx : x ∈ X) :
    x ∈ M := by
  rcases hX with hXA | hXA0
  · have hxA : x ∈ section16ASet M U := by
      simpa [hXA] using hx
    exact hxA.1.1
  · have hxA0 : x ∈ section16AZeroSet M K := by
      simpa [hXA0] using hx
    exact hxA0.1.1

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_conjugateInSubgroup_top_symm
    {x y : G}
    (hxy : section16ConjugateInSubgroup (⊤ : Subgroup G) x y) :
    section16ConjugateInSubgroup (⊤ : Subgroup G) y x := by
  rcases hxy with ⟨g, _hg, hgy⟩
  refine ⟨g⁻¹, by simp, ?_⟩
  rw [hgy]
  group

private theorem CFSG.section16_mem_msigma_of_conj_mem_AChoice
    {M K U : Subgroup G} {X : Set G} {x y : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hX : section16AChoice M K U X)
    (hxσ : x ∈ section10Msigma M)
    (hyX : y ∈ X)
    (hxy : section16ConjugateInSubgroup (⊤ : Subgroup G) x y) :
    y ∈ section10Msigma M := by
  classical
  have hyM : y ∈ M := section16_mem_M_of_mem_AChoice (G := G) hX hyX
  refine section16_mem_msigma_of_primeSupport_subset (G := G) hM hyM ?_
  rcases hxy with ⟨g, _hg, hgy⟩
  intro p hp
  have hp_x : p ∈ section14ElementPrimeSupport x := by
    have hsubset := section16_elementPrimeSupport_conj_subset (G := G) (x := x) (g := g)
    exact hsubset (by simpa [hgy] using hp)
  have hMx : M ∈ section14MsigmaElement x := by
    exact ⟨hM, by
      simpa [section14MsigmaElement, section14MsigmaFamily, Set.singleton_subset_iff]
        using hxσ⟩
  exact section16_primeSupport_subset_sigma_of_msigmaMember
    (G := G) (x := x) (M := M) hMx hp_x

private theorem CFSG.section16_ASet_diff_msigma_conjugator_mem_M
    {M K U : Subgroup G} {x y g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hx : x ∈ section16ASet M U \ (section10Msigma M : Set G))
    (hy : y ∈ section16ASet M U \ (section10Msigma M : Set G))
    (hgy : y = g * x * g⁻¹) :
    g ∈ M := by
  classical
  by_cases hgM : g ∈ M
  · exact hgM
  exfalso
  rcases section16_ASet_diff_msigma_exists_prime_compl_zpow
      (G := G) (M := M) (K := K) (U := U) hM hKU hx with
    ⟨n, q, hxpow_order, hqcompl⟩
  let z : G := x ^ n
  let w : G := y ^ n
  have hw_eq : w = g * z * g⁻¹ := by
    dsimp [z, w]
    rw [hgy]
    exact conj_zpow (i := n) (a := g) (b := x)
  have hw_order : orderOf w = q.val := by
    have hconj_order : orderOf (g * z * g⁻¹) = orderOf z := by
      simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq z
    rw [hw_eq, hconj_order]
    exact hxpow_order
  have huniq_z :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer ({z} : Set G)) = {M} := by
    simpa [z] using
      section16_ASet_diff_msigma_zpow_unique_centralizer
        (G := G) (M := M) (K := K) (U := U) hM hx hxpow_order hqcompl
  have huniq_w :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer ({w} : Set G)) = {M} := by
    simpa [w] using
      section16_ASet_diff_msigma_zpow_unique_centralizer
        (G := G) (M := M) (K := K) (U := U) hM hy hw_order hqcompl
  have hcent_z_le_M : Subgroup.centralizer ({z} : Set G) ≤ M := by
    have hMcont :
        M ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({z} : Set G)) := by
      simp [huniq_z]
    exact hMcont.2
  have hMg_cont :
      M.conjBy g ∈ section9MaximalSubgroupsContaining
        (Subgroup.centralizer ({w} : Set G)) := by
    refine ⟨section10_maximal_conjBy (G := G) hM g, ?_⟩
    intro c hcw
    have hcz : g⁻¹ * c * g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hcw ⊢
      rw [hw_eq] at hcw
      calc
        (g⁻¹ * c * g) * z =
            g⁻¹ * (c * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * c) * g := by rw [hcw]
        _ = z * (g⁻¹ * c * g) := by group
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨g⁻¹ * c * g, hcent_z_le_M hcz, ?_⟩
    simp [MulAut.conj_apply]
    group
  have hMg_eq_M : M.conjBy g = M := by
    have hsingle : M.conjBy g ∈ ({M} : Set (Subgroup G)) := by
      simpa [huniq_w] using hMg_cont
    simpa using hsingle
  have hgNormM : g ∈ Subgroup.normalizer (M : Set G) :=
    section16_mem_normalizer_of_conjBy_eq (G := G) hMg_eq_M
  exact hgM (by
    simpa [section16_maximal_normalizer_eq_self (G := G) hM] using hgNormM)

private theorem CFSG.section16_ASet_diff_msigma_fusion_in_M
    {M K U : Subgroup G} {x y : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hx : x ∈ section16ASet M U \ (section10Msigma M : Set G))
    (hy : y ∈ section16ASet M U \ (section10Msigma M : Set G))
    (hxy : section16ConjugateInSubgroup (⊤ : Subgroup G) x y) :
    section16ConjugateInSubgroup M x y := by
  rcases hxy with ⟨g, _hg, hgy⟩
  exact ⟨g,
    section16_ASet_diff_msigma_conjugator_mem_M
      (G := G) (M := M) (K := K) (U := U) hM hKU hx hy hgy,
    hgy⟩

private theorem CFSG.section16_A0_diff_A_primeSupport_subset
    {M K U : Subgroup G} {a : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (ha : a ∈ section16AZeroSet M K \ section16ASet M U) :
    section14ElementPrimeSupport a ⊆
      section14KappaPrimes M ∪ section10SigmaPrimes M := by
  classical
  by_cases hKbot : K = ⊥
  · have haA : a ∈ section16ASet M U :=
      section16_AZeroSet_subset_ASet_of_K_eq_bot
        (G := G) (M := M) (K := K) (U := U) hKU hKbot ha.1
    exact False.elim (ha.2 haA)
  · have hMP : M ∈ section14MFamilyP G :=
      section16_MFamilyP_of_nontrivial_hall_kappa
        (G := G) hM hKU.1 hKbot
    have hConj :
        a ∈ section16ConjugatesOfSetBySet
          (section16HatZ K (section16Kstar M K)) (M : Set G) := by
      have hEq :=
        section16_conjugates_hatZ_eq_A0_diff_A
          (G := G) (M := M) (K := K) (U := U) hMP hKU
      simpa [hEq] using ha
    rcases hConj with ⟨t, htHat, m, _hmM, ha_eq⟩
    have hZdp : section14ZInternalDirectProduct M K :=
      (theorem_14_7_d (G := G) (M := M) (K := K) hMP hKU.1).1
    rcases section16_hatZ_decomp_with_kstar_zpower
        (G := G) (M := M) (K := K) hMP hKU.1 hZdp htHat with
      ⟨s, k, hsKstar, _hsne, hkK, _hkne, ht_eq, hskComm, _hsT⟩
    intro p hp
    have hp_t : p ∈ section14ElementPrimeSupport t := by
      have hsubset := section16_elementPrimeSupport_conj_subset (G := G) (x := t) (g := m)
      exact hsubset (by simpa [ha_eq] using hp)
    have hp_dvd_t : p.val ∣ orderOf t := by
      simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hp_t
    have hp_mul : p.val ∣ orderOf s * orderOf k := by
      have hdiv : orderOf t ∣ orderOf s * orderOf k := by
        simpa [ht_eq] using hskComm.orderOf_mul_dvd_mul_orderOf
      exact hp_dvd_t.trans hdiv
    rcases p.property.dvd_mul.mp hp_mul with hp_s | hp_k
    · right
      have hpSuppS : p ∈ section14ElementPrimeSupport s := by
        simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hp_s
      exact section16_primeSupport_subset_sigma_of_msigmaMember
        (G := G) (x := s) (M := M)
        ⟨hM, by simpa [section16Kstar] using hsKstar.1⟩ hpSuppS
    · left
      have hpSuppK : p ∈ section14ElementPrimeSupport k := by
        simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hp_k
      exact section16_isPiElement_of_mem_hall (G := G) hKU.1 hkK hpSuppK

private theorem CFSG.section16_not_conjugate_ASet_diff_msigma_A0_diff_A
    {M K U : Subgroup G} {x y : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hx : x ∈ section16ASet M U \ (section10Msigma M : Set G))
    (hy : y ∈ section16AZeroSet M K \ section16ASet M U) :
    ¬ section16ConjugateInSubgroup (⊤ : Subgroup G) x y := by
  classical
  intro hxy
  rcases section16_ASet_diff_msigma_exists_prime_compl_zpow
      (G := G) (M := M) (K := K) (U := U) hM hKU hx with
    ⟨n, q, hxpow_order, hqcompl⟩
  have hq_dvd_x : q.val ∣ orderOf x := by
    have hxpow_mem : x ^ n ∈ Subgroup.zpowers x := by
      exact ⟨n, rfl⟩
    have hdiv := orderOf_dvd_of_mem_zpowers hxpow_mem
    simpa [hxpow_order] using hdiv
  rcases hxy with ⟨g, _hg, hgy⟩
  have horder_y : orderOf y = orderOf x := by
    rw [hgy]
    simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq x
  have hqSuppY : q ∈ section14ElementPrimeSupport y := by
    simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers,
      horder_y] using hq_dvd_x
  have hqUnion :
      q ∈ section14KappaPrimes M ∪ section10SigmaPrimes M :=
    section16_A0_diff_A_primeSupport_subset (G := G) hM hKU hy hqSuppY
  exact hqcompl hqUnion

private theorem CFSG.section16_A0_diff_A_conjugator_mem_M
    {M K U : Subgroup G} {x y g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hx : x ∈ section16AZeroSet M K \ section16ASet M U)
    (hy : y ∈ section16AZeroSet M K \ section16ASet M U)
    (hgy : y = g * x * g⁻¹) :
    g ∈ M := by
  classical
  by_cases hKbot : K = ⊥
  · have hxA : x ∈ section16ASet M U :=
      section16_AZeroSet_subset_ASet_of_K_eq_bot
        (G := G) (M := M) (K := K) (U := U) hKU hKbot hx.1
    exact False.elim (hx.2 hxA)
  · have hMP : M ∈ section14MFamilyP G :=
      section16_MFamilyP_of_nontrivial_hall_kappa
        (G := G) hM hKU.1 hKbot
    have hEq :=
      section16_conjugates_hatZ_eq_A0_diff_A
        (G := G) (M := M) (K := K) (U := U) hMP hKU
    have hxConj :
        x ∈ section16ConjugatesOfSetBySet
          (section16HatZ K (section16Kstar M K)) (M : Set G) := by
      simpa [hEq] using hx
    have hyConj :
        y ∈ section16ConjugatesOfSetBySet
          (section16HatZ K (section16Kstar M K)) (M : Set G) := by
      simpa [hEq] using hy
    rcases hxConj with ⟨t, htHat, m, hmM, hx_eq⟩
    rcases hyConj with ⟨u, huHat, n, hnM, hy_eq⟩
    let c : G := n⁻¹ * g * m
    have hu_conj : u = c * t * c⁻¹ := by
      dsimp [c]
      have hmain := congrArg (fun z : G => n⁻¹ * z * n) (hy_eq.symm.trans hgy)
      rw [hx_eq] at hmain
      simpa [mul_assoc] using hmain
    let Z : Subgroup G := section16ZSubgroup K (section16Kstar M K)
    have h147e := theorem_14_7_e (G := G) (M := M) (K := K) hMP hKU.1
    have hTI :
        section16TISubsetWithNormalizer (section16HatZ K (section16Kstar M K)) Z := by
      simpa [Z, section16HatZ, section16ZSubgroup, section16Kstar,
        section14WidehatZ, section14Z, section14KStar] using
        (section16_section14TISet_to_section16TISubsetWithNormalizer
          (G := G) h147e.1 h147e.2.1)
    have huConjSet :
        u ∈ section16ConjugateSet (section16HatZ K (section16Kstar M K)) c :=
      ⟨t, htHat, hu_conj⟩
    have hcZ : c ∈ Z := by
      rcases hTI.1 c with hConjEq | hsmall
      · have hcNorm : c ∈ Subgroup.normalizer (section16HatZ K (section16Kstar M K)) :=
          section16_mem_normalizer_of_conjugateSet_eq (G := G) hConjEq
        simpa [hTI.2] using hcNorm
      · have hu_one_mem : u ∈ ({1} : Set G) :=
          hsmall ⟨huHat, huConjSet⟩
        have hu_one : u = 1 := by simpa using hu_one_mem
        exact False.elim (huHat.2 (Or.inl (by simp [hu_one])))
    have hZleM : Z ≤ M := by
      refine sup_le hKU.1.1 ?_
      intro z hz
      exact section16_msigma_le (G := G) M hz.1
    have hcM : c ∈ M := hZleM hcZ
    have hg_eq : g = n * c * m⁻¹ := by
      dsimp [c]
      group
    rw [hg_eq]
    exact M.mul_mem (M.mul_mem hnM hcM) (M.inv_mem hmM)

private theorem CFSG.section16_A0_diff_A_fusion_in_M
    {M K U : Subgroup G} {x y : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hx : x ∈ section16AZeroSet M K \ section16ASet M U)
    (hy : y ∈ section16AZeroSet M K \ section16ASet M U)
    (hxy : section16ConjugateInSubgroup (⊤ : Subgroup G) x y) :
    section16ConjugateInSubgroup M x y := by
  rcases hxy with ⟨g, _hg, hgy⟩
  exact ⟨g,
    section16_A0_diff_A_conjugator_mem_M
      (G := G) (M := M) (K := K) (U := U) hM hKU hx hy hgy,
    hgy⟩

private def CFSG.section16SubgroupConjSetoid (G : Type*) [Group G] :
    Setoid (Subgroup G) where
  r A B := ∃ g : G, A = B.conjBy g
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro A
      refine ⟨1, ?_⟩
      ext x
      simp [Subgroup.conjBy]
    · intro A B hAB
      rcases hAB with ⟨g, hAB⟩
      refine ⟨g⁻¹, ?_⟩
      calc
        B = (B.conjBy g).conjBy g⁻¹ := by
          exact (section11_conjBy_inv (G := G) B g).symm
        _ = A.conjBy g⁻¹ := by rw [← hAB]
    · intro A B C hAB hBC
      rcases hAB with ⟨g, hAB⟩
      rcases hBC with ⟨h, hBC⟩
      refine ⟨g * h, ?_⟩
      calc
        A = B.conjBy g := hAB
        _ = (C.conjBy h).conjBy g := by rw [hBC]
        _ = C.conjBy (g * h) := section11_conjBy_conjBy (G := G) C h g

omit [IsMinCE G] in
public theorem CFSG.section16_exists_maximalConjugacyRepresentatives :
    ∃ Ms : List (Subgroup G), section16MaximalConjugacyRepresentatives (G := G) Ms := by
  classical
  let S : Setoid (Subgroup G) := section16SubgroupConjSetoid G
  letI : Setoid (Subgroup G) := S
  letI : Fintype (Quotient S) := Fintype.ofFinite _
  let qs : List (Quotient S) := (Finset.univ : Finset (Quotient S)).toList
  let reps : List (Subgroup G) := qs.map fun q => Quotient.out q
  let Ms : List (Subgroup G) := reps.filter fun M => M ∈ section9MaximalSubgroups G
  refine ⟨Ms, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro M hMmem
    exact of_decide_eq_true (List.mem_filter.mp hMmem).2
  · have hqnodup : qs.Nodup := by
      simpa [qs] using (Finset.nodup_toList (Finset.univ : Finset (Quotient S)))
    have hrepnodup : reps.Nodup := by
      simpa [reps] using hqnodup.map (Quotient.out_injective (s := S))
    exact hrepnodup.filter _
  · intro N hNmax
    let q : Quotient S := Quotient.mk'' N
    let R : Subgroup G := Quotient.out q
    have hRrelN : R ≈ N := by
      have hout : Quotient.mk'' R = q := by
        simp [R]
      exact Quotient.exact (by simpa [q] using hout)
    have hRmax : R ∈ section9MaximalSubgroups G := by
      rcases hRrelN with ⟨g, hR⟩
      simpa [hR] using section10_maximal_conjBy (G := G) hNmax g
    have hRreps : R ∈ reps := by
      refine List.mem_map.mpr ⟨q, ?_, rfl⟩
      exact Finset.mem_toList.mpr (Finset.mem_univ q)
    have hRMs : R ∈ Ms := by
      exact List.mem_filter.mpr ⟨hRreps, decide_eq_true hRmax⟩
    have hNconjR : ∃ g : G, N = R.conjBy g := by
      rcases hRrelN with ⟨g, hR⟩
      refine ⟨g⁻¹, ?_⟩
      calc
        N = (N.conjBy g).conjBy g⁻¹ := by
          exact (section11_conjBy_inv (G := G) N g).symm
        _ = R.conjBy g⁻¹ := by rw [← hR]
    refine ⟨R, ⟨hRMs, hNconjR⟩, ?_⟩
    intro M hM
    rcases hM with ⟨hMMs, hNconjM⟩
    rcases List.mem_filter.mp hMMs with ⟨hMreps, _hMmax⟩
    rcases List.mem_map.mp hMreps with ⟨qM, hqMmem, hMout⟩
    have hMrelN : M ≈ N := by
      rcases hNconjM with ⟨g, hN⟩
      refine ⟨g⁻¹, ?_⟩
      calc
        M = (M.conjBy g).conjBy g⁻¹ := by
          exact (section11_conjBy_inv (G := G) M g).symm
        _ = N.conjBy g⁻¹ := by rw [← hN]
    have hqM_eq_q : qM = q := by
      have hqM_mk : Quotient.mk'' M = qM := by
        simpa [hMout] using (Quotient.out_eq qM)
      have hmk_eq : Quotient.mk'' M = q := by
        simpa [q] using Quotient.sound hMrelN
      exact hqM_mk.symm.trans hmk_eq
    calc
      M = Quotient.out qM := hMout.symm
      _ = Quotient.out q := by rw [hqM_eq_q]
      _ = R := rfl

private theorem CFSG.section16_section14N_mem_and_data
    {M : Subgroup G} {x : G}
    (hxne : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty)
    (hcard : 1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x})
    (hM : M ∈ section14MsigmaElement x) :
    section14N x ∈
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
      ∀ L : Subgroup G, L ∈ section14MsigmaElement x →
        section14Theorem14_4NData x (section14R x) (section14N x) L := by
  classical
  let N0 : Subgroup G := section14N x
  have hN0type : N0 ∈ section14MFamilyF G ∪ section14MFamilyP2 G := by
    simpa [N0] using theorem_14_4_f (G := G) (x := x) hxne hσ hcard
  have hN0max : N0 ∈ section9MaximalSubgroups G := by
    rcases hN0type with hF | hP2
    · exact hF.1
    · exact hP2.1.1
  have hReq :
      section14R x = elementCentralizerIn (section10Msigma N0) x := by
    simpa [N0] using
      (theorem_14_4_a (G := G) (x := x) hxne hσ hcard hM).1
  have hprod :
      ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) =
        (elementCentralizerIn (M ⊓ N0) x : Set G) * (section14R x : Set G) := by
    simpa [N0] using
      theorem_14_4_b (G := G) (x := x) hxne hσ hcard hM
  have hRleN0 : section14R x ≤ N0 := by
    rw [hReq]
    intro y hy
    exact section16_msigma_le (G := G) N0 hy.1
  have hCentInfLeN0 : elementCentralizerIn (M ⊓ N0) x ≤ N0 := by
    intro y hy
    exact hy.1.2
  have hN0cont :
      N0 ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) := by
    refine ⟨hN0max, ?_⟩
    intro y hy
    have hySet : y ∈
        ((elementCentralizerIn (M ⊓ N0) x : Set G) * (section14R x : Set G)) := by
      simpa [← hprod] using hy
    rcases Set.mem_mul.mp hySet with ⟨a, ha, b, hb, hyab⟩
    rw [← hyab]
    exact N0.mul_mem (hCentInfLeN0 ha) (hRleN0 hb)
  have h14 := theorem_14_4 (G := G) (x := x) hxne hσ
  rcases h14.2.2 hcard with ⟨N, hNcont, hNdata, hNuniq⟩
  have hN0_eq : N0 = N := hNuniq N0 hN0cont
  refine ⟨by simpa [N0] using hN0cont, ?_⟩
  intro L hL
  simpa [N0, hN0_eq] using hNdata L hL

public theorem CFSG.section16_section14R_eq_bot_of_centralizer_le_public
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    {x : G} (hx : x ∈ section10Msigma M) (hxne : x ≠ 1)
    (hCGM : Subgroup.centralizer ({x} : Set G) ≤ M) :
    section14R x = (⊥ : Subgroup G) :=
  section16_section14R_eq_bot_of_centralizer_le (G := G) hM hx hxne hCGM

public theorem CFSG.section16_section14N_data_of_not_centralizer_le
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    {x : G} (hx : x ∈ section10Msigma M) (hxne : x ≠ 1)
    (hCGnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    section14N x ∈
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
      section14R x = elementCentralizerIn (section10Msigma (section14N x)) x ∧
        section16MFSubgroup (section14N x) (section10Msigma (section14N x)) := by
  classical
  have hMx : M ∈ section14MsigmaElement x := by
    exact ⟨hM, by simpa [section14MsigmaElement, section14MsigmaFamily,
      Set.singleton_subset_iff] using hx⟩
  have hσ : (section14MsigmaElement x).Nonempty := ⟨M, hMx⟩
  have hcard :
      1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x} :=
    section16_msigmaElement_card_gt_one_of_not_centralizer_le
      (G := G) hM hx hCGnot
  have hNpack :=
    section16_section14N_mem_and_data (G := G) (M := M) (x := x)
      hxne hσ hcard hMx
  have hNdataM : section14Theorem14_4NData x (section14R x) (section14N x) M :=
    hNpack.2 M hMx
  rcases hNdataM with
    ⟨hReq, hRne, _hprod, hsupp, _htau, _hbeta, _hcomp, hNF_or_P2⟩
  rcases section16_theoremD_auxiliary_data (G := G) (M := M) (N := section14N x)
      (x := x) hxne hNpack.1 hReq hRne hsupp hNF_or_P2 with
    ⟨NF, _NK, _NU, hNF, _hNKU, hNσ_eq, _hxA⟩
  have hNFσ :
      section16MFSubgroup (section14N x) (section10Msigma (section14N x)) := by
    simpa [hNσ_eq] using hNF
  exact ⟨hNpack.1, hReq, hNFσ⟩

private theorem CFSG.section16_theoremII_mem_msigma_of_mem_D
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (_hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X) :
    ∀ x : G, x ∈ section16TheoremIIDSet M X → x ∈ section10Msigma M := by
  classical
  intro x hxD
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  by_contra hxσ
  rcases hxD with ⟨hxX, _hxne, hxCentNotLe⟩
  rcases hX with hXA | hXA0
  · have hxA : x ∈ section16ASet M U := by
      simpa [hXA] using hxX
    exact hxCentNotLe
      (section16_ASet_diff_msigma_centralizer_le
        (G := G) (M := M) (K := K) (U := U) hM hKU15 ⟨hxA, hxσ⟩)
  · have hxA0 : x ∈ section16AZeroSet M K := by
      simpa [hXA0] using hxX
    by_cases hxA : x ∈ section16ASet M U
    · exact hxCentNotLe
        (section16_ASet_diff_msigma_centralizer_le
          (G := G) (M := M) (K := K) (U := U) hM hKU15 ⟨hxA, hxσ⟩)
    · exact hxCentNotLe
        (section16_A0_diff_A_centralizer_le
          (G := G) (M := M) (K := K) (U := U) hM hKU15 ⟨hxA0, hxA⟩)

private theorem CFSG.section16_theoremII_canonical_D_data
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {x : G} (hxD : x ∈ section16TheoremIIDSet M X) :
    let N : Subgroup G := section14N x
    ∃ NK NU : Subgroup G,
      N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
        section16MFSubgroup N (section10Msigma N) ∧
          section16KUData N NK NU ∧
            x ∈ section16ASet N NU \ (section10Msigma N : Set G) ∧
              (section16TypeI N (section10Msigma N) ∨
                section16TypeII N (section10Msigma N)) ∧
                section12ComplementIn N (section10Msigma N) (M ⊓ N) ∧
                  (section16TypeII N (section10Msigma N) →
                    section16FrobeniusWithCyclicComplement M MF ∧
                      section16TypeI M MF ∧
                        ¬ section16TISubset (MF : Set G)) := by
  classical
  dsimp
  let N : Subgroup G := section14N x
  have hxσM : x ∈ section10Msigma M :=
    section16_theoremII_mem_msigma_of_mem_D (G := G) hM hMF hKU hX x hxD
  have hxne : x ≠ 1 := hxD.2.1
  have hMx : M ∈ section14MsigmaElement x := by
      exact ⟨hM, by simpa [section14MsigmaElement, section14MsigmaFamily,
      Set.singleton_subset_iff] using hxσM⟩
  have hσ : (section14MsigmaElement x).Nonempty := ⟨M, hMx⟩
  have hcard :
      1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x} :=
    section16_msigmaElement_card_gt_one_of_not_centralizer_le
      (G := G) hM hxσM hxD.2.2
  have hNpack :=
    section16_section14N_mem_and_data (G := G) (M := M) (x := x)
      hxne hσ hcard hMx
  have hNcont : N ∈
      section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) := by
    simpa [N] using hNpack.1
  have hNdataM : section14Theorem14_4NData x (section14R x) N M := by
    simpa [N] using hNpack.2 M hMx
  rcases hNdataM with
    ⟨hReq, hRne, _hprod, hsupp, _htau, _hbeta, hcomp, hNF_or_P2⟩
  rcases section16_theoremD_auxiliary_data (G := G) (M := M) (N := N)
      (x := x) hxne hNcont hReq hRne hsupp hNF_or_P2 with
    ⟨NF, NK, NU, hNF, hNKU, hNσ_eq, hxA⟩
  have hNFσ : section16MFSubgroup N (section10Msigma N) := by
    simpa [hNσ_eq] using hNF
  have hType :
      section16TypeI N (section10Msigma N) ∨
        section16TypeII N (section10Msigma N) := by
    rcases hNF_or_P2 with hF | hP2
    · have hnotP : N ∉ section14MFamilyP G := by
        intro hP
        rcases hP.2 with ⟨p, hpκ⟩
        simp [hF.2] at hpκ
      exact Or.inl (section16_typeI_of_not_MFamilyP (G := G) hNcont.1 hNFσ hnotP)
    · exact Or.inr (section16_typeII_of_MFamilyP2 (G := G) hNFσ hNKU hP2)
  have hTypeII_consequence :
      section16TypeII N (section10Msigma N) →
        section16FrobeniusWithCyclicComplement M MF ∧
          section16TypeI M MF ∧
            ¬ section16TISubset (MF : Set G) := by
    intro hTypeII
    have hNKU15 : section15KUData N NK NU :=
      section16_kudata_to_section15 (G := G) hNKU
    have hCaseP2 : section16CaseP2 NK NU :=
      section16_caseP2_of_typeII (G := G) hNcont.1 hNFσ hNKU hTypeII
    have hNP2 : section16MaximalTypeP2 N := by
      have hNP2' : N ∈ section14MFamilyP2 G :=
        section16_MFamilyP2_of_nontrivial_U
          (G := G) hNcont.1 hNKU15 hCaseP2.1 hCaseP2.2
      simpa [section16MaximalTypeP2] using hNP2'
    rcases (theorem_16_D (G := G) hM hMF hKU).2.2 x hxσM hxne with
      ⟨R, _hRcomp, hR⟩
    rcases hR hxD.2.2 with
      ⟨N', huniq, _hReq', _hAux', _hType', _hComp', hP2impl⟩
    have hN_eq_N' : N = N' := by
      have hNmem : N ∈ ({N'} : Set (Subgroup G)) := by
        simpa [huniq] using hNcont
      simpa using hNmem
    have hNP2' : section16MaximalTypeP2 N' := by
      simpa [← hN_eq_N'] using hNP2
    rcases hP2impl hNP2' with ⟨hMFamF, hFrob, hNotTI⟩
    have hMnotP : M ∉ section14MFamilyP G := by
      intro hMP
      rcases hMP.2 with ⟨p, hpκ⟩
      simp [hMFamF.2] at hpκ
    exact ⟨hFrob, section16_typeI_of_not_MFamilyP (G := G) hM hMF hMnotP, hNotTI⟩
  refine ⟨NK, NU, hNcont, hNFσ, hNKU, ?_, hType, hcomp, hTypeII_consequence⟩
  simpa [N, hNσ_eq] using hxA

private noncomputable def CFSG.section16_theoremII_supportDataOf
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    (x : G) (hxD : x ∈ section16TheoremIIDSet M X) :
    Section16SupportData G :=
  let hData := section16_theoremII_canonical_D_data
    (G := G) hM hMF hKU hX hxD
  let NK : Subgroup G := Classical.choose hData
  let NU : Subgroup G := Classical.choose (Classical.choose_spec hData)
  { M := section14N x
    H := section10Msigma (section14N x)
    K := NK
    U := NU }

private theorem CFSG.section16_theoremII_supportDataOf_spec
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {x : G} (hxD : x ∈ section16TheoremIIDSet M X) :
    let P := section16_theoremII_supportDataOf (G := G) hM hMF hKU hX x hxD
    P.M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
      section16MFSubgroup P.M P.H ∧
        section16KUData P.M P.K P.U ∧
          x ∈ section16ASet P.M P.U \ (P.H : Set G) ∧
            (section16TypeI P.M P.H ∨ section16TypeII P.M P.H) ∧
              section12ComplementIn P.M P.H (M ⊓ P.M) ∧
                (section16TypeII P.M P.H →
                  section16FrobeniusWithCyclicComplement M MF ∧
                    section16TypeI M MF ∧
                      ¬ section16TISubset (MF : Set G)) := by
  classical
  dsimp [section16_theoremII_supportDataOf]
  let hData := section16_theoremII_canonical_D_data
    (G := G) hM hMF hKU hX hxD
  let NK : Subgroup G := Classical.choose hData
  let hDataNK := Classical.choose_spec hData
  let NU : Subgroup G := Classical.choose hDataNK
  have hSpec := Classical.choose_spec hDataNK
  simpa [hData, NK, hDataNK, NU] using hSpec

private def CFSG.section16_theoremII_supportRepCandidate
    (M : Subgroup G) (X : Set G) (R : Subgroup G) : Prop :=
  ∃ x : G, x ∈ section16TheoremIIDSet M X ∧
    ∃ g : G, section14N x = R.conjBy g

private noncomputable def CFSG.section16_theoremII_supportDataForRep
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    (R : Subgroup G)
    (hR : section16_theoremII_supportRepCandidate (G := G) M X R) :
    Section16SupportData G :=
  let x : G := Classical.choose hR
  let hxD : x ∈ section16TheoremIIDSet M X := (Classical.choose_spec hR).1
  section16_theoremII_supportDataOf (G := G) hM hMF hKU hX x hxD

private noncomputable def CFSG.section16_theoremII_supportList
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    (Ms : List (Subgroup G)) : List (Section16SupportData G) := by
  classical
  exact Ms.filterMap fun R =>
    if hR : section16_theoremII_supportRepCandidate (G := G) M X R then
      some (section16_theoremII_supportDataForRep (G := G) hM hMF hKU hX R hR)
    else
      none

private theorem CFSG.section16_theoremII_supportDataForRep_spec
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {R : Subgroup G}
    (hR : section16_theoremII_supportRepCandidate (G := G) M X R) :
    let P := section16_theoremII_supportDataForRep (G := G) hM hMF hKU hX R hR
    ∃ x : G, ∃ _hxD : x ∈ section16TheoremIIDSet M X, ∃ g : G,
      section14N x = R.conjBy g ∧
        P.M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
          section16MFSubgroup P.M P.H ∧
            section16KUData P.M P.K P.U ∧
              x ∈ section16ASet P.M P.U \ (P.H : Set G) ∧
                (section16TypeI P.M P.H ∨ section16TypeII P.M P.H) ∧
                  section12ComplementIn P.M P.H (M ⊓ P.M) ∧
                    (section16TypeII P.M P.H →
                      section16FrobeniusWithCyclicComplement M MF ∧
                        section16TypeI M MF ∧
                          ¬ section16TISubset (MF : Set G)) := by
  classical
  dsimp [section16_theoremII_supportDataForRep]
  let x : G := Classical.choose hR
  have hxSpec := Classical.choose_spec hR
  let hxD : x ∈ section16TheoremIIDSet M X := hxSpec.1
  rcases hxSpec.2 with ⟨g, hg⟩
  refine ⟨x, hxD, g, hg, ?_⟩
  simpa [x, hxD] using
    section16_theoremII_supportDataOf_spec (G := G) hM hMF hKU hX hxD

private theorem CFSG.section16_mem_theoremII_supportList
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {Ms : List (Subgroup G)} {P : Section16SupportData G}
    (hP : P ∈ section16_theoremII_supportList (G := G) hM hMF hKU hX Ms) :
    ∃ R : Subgroup G, R ∈ Ms ∧
      ∃ hR : section16_theoremII_supportRepCandidate (G := G) M X R,
        P = section16_theoremII_supportDataForRep (G := G) hM hMF hKU hX R hR := by
  classical
  rw [section16_theoremII_supportList, List.mem_filterMap] at hP
  rcases hP with ⟨R, hRmem, hsome⟩
  by_cases hR : section16_theoremII_supportRepCandidate (G := G) M X R
  · refine ⟨R, hRmem, hR, ?_⟩
    simpa [hR] using hsome.symm
  · simp [hR] at hsome


private theorem CFSG.section16_mf_le_derived_of_maximal
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF) :
    MF ≤ ambientDerivedSubgroup M := by
  rcases theorem_16_A (G := G) hM hMF with ⟨K, U, hA⟩
  dsimp [section16TheoremAConclusions] at hA
  rcases hA with
    ⟨_hA1, _hKcyc, _hKHall, _hKnorm, _hCompKM, _hUMsigmaNormal,
      _hProduct, _hUnormal, _hCentralizersU, _hKstarNe, _hCentralizersK,
      _hMFpos, hMFleSigma, hSigmaLeDerived, _hDerivedProper, _hQuotNil,
      _hSecondLeFitting, _hFittingEq, _hFittingLeDerived,
      _hProperBranch⟩
  exact hMFleSigma.trans hSigmaLeDerived

private theorem CFSG.section16_mf_isPiSubgroup_sigma_of_maximal
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF) :
    IsPiSubgroup (G := G) (section10SigmaPrimes M) MF := by
  rcases theorem_16_A (G := G) hM hMF with ⟨K, U, hA⟩
  dsimp [section16TheoremAConclusions] at hA
  rcases hA with
    ⟨hA1, _hKcyc, _hKHall, _hKnorm, _hCompKM, _hUMsigmaNormal,
      _hProduct, _hUnormal, _hCentralizersU, _hKstarNe, _hCentralizersK,
      _hMFpos, hMFleSigma, _hSigmaLeDerived, _hDerivedProper, _hQuotNil,
      _hSecondLeFitting, _hFittingEq, _hFittingLeDerived,
      _hProperBranch⟩
  have hSigmaHall :
      section12HallSubgroupIn (section10SigmaPrimes M) (section10Msigma M) M :=
    hA1.2.1
  intro p hpMF
  have hpSigmaSubgroup : p ∈ subgroupPrimeSet (section10Msigma M) :=
    section8_subgroupPrimeSet_mono hMFleSigma hpMF
  have hpSigmaCard : p.val ∣ Nat.card (section10Msigma M) := by
    simpa [subgroupPrimeSet] using hpSigmaSubgroup
  have hpSigmaSubgroupOf :
      p.val ∣ Nat.card ((section10Msigma M).subgroupOf M) := by
    simpa [section12_card_subgroupOf_eq hSigmaHall.1] using hpSigmaCard
  exact hSigmaHall.2.p_in_pi_of_p_dvd_card p hpSigmaSubgroupOf

private theorem CFSG.section16_theoremII_supportList_entry_facts
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {Ms : List (Subgroup G)} {P : Section16SupportData G}
    (hP : P ∈ section16_theoremII_supportList (G := G) hM hMF hKU hX Ms) :
    P.M ∈ section9MaximalSubgroups G ∧
      section16MFSubgroup P.M P.H ∧
        section16KUData P.M P.K P.U ∧
          (section16TypeI P.M P.H ∨ section16TypeII P.M P.H) ∧
            P.H ≤ ambientDerivedSubgroup P.M := by
  classical
  rcases section16_mem_theoremII_supportList
      (G := G) hM hMF hKU hX hP with
    ⟨R, _hRmem, hR, rfl⟩
  let P : Section16SupportData G :=
    section16_theoremII_supportDataForRep (G := G) hM hMF hKU hX R hR
  change
    P.M ∈ section9MaximalSubgroups G ∧
      section16MFSubgroup P.M P.H ∧
        section16KUData P.M P.K P.U ∧
          (section16TypeI P.M P.H ∨ section16TypeII P.M P.H) ∧
            P.H ≤ ambientDerivedSubgroup P.M
  rcases section16_theoremII_supportDataForRep_spec
      (G := G) hM hMF hKU hX hR with
    ⟨_x, _hxD, _g, _hNg, hPcont, hPMF, hPKU, _hxA, hPtype,
      _hPcomp, _hTypeII⟩
  exact ⟨hPcont.1, hPMF, hPKU, hPtype,
    section16_mf_le_derived_of_maximal (G := G) hPcont.1 hPMF⟩

private theorem CFSG.section16_theoremII_supportList_complement_split
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {Ms : List (Subgroup G)} {P : Section16SupportData G}
    (hP : P ∈ section16_theoremII_supportList (G := G) hM hMF hKU hX Ms) :
    P.M = P.H ⊔ (M ⊓ P.M) ∧ M ⊓ P.H = ⊥ := by
  classical
  rcases section16_mem_theoremII_supportList
      (G := G) hM hMF hKU hX hP with
    ⟨R, _hRmem, hR, rfl⟩
  let P : Section16SupportData G :=
    section16_theoremII_supportDataForRep (G := G) hM hMF hKU hX R hR
  change P.M = P.H ⊔ (M ⊓ P.M) ∧ M ⊓ P.H = ⊥
  rcases section16_theoremII_supportDataForRep_spec
      (G := G) hM hMF hKU hX hR with
    ⟨_x, _hxD, _g, _hNg, _hPcont, _hPMF, _hPKU, _hxA, _hPtype,
      hPcomp, _hTypeII⟩
  refine ⟨hPcomp.2.2.1, ?_⟩
  apply le_bot_iff.mp
  intro z hz
  exact hPcomp.2.2.2.le_bot ⟨hz.2, ⟨hz.1, hPcomp.1 hz.2⟩⟩

private theorem CFSG.section16_theoremII_supportList_typeII_consequence
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {Ms : List (Subgroup G)} :
    section16SomeSupportingSubgroupTypeII
        (section16_theoremII_supportList (G := G) hM hMF hKU hX Ms) →
      section16FrobeniusWithCyclicComplement M MF ∧
        section16TypeI M MF ∧
          ¬ section16TISubset (MF : Set G) := by
  classical
  rintro ⟨P, hPmem, hPTypeII⟩
  rcases section16_mem_theoremII_supportList
      (G := G) hM hMF hKU hX hPmem with
    ⟨R, _hRmem, hR, rfl⟩
  let P : Section16SupportData G :=
    section16_theoremII_supportDataForRep (G := G) hM hMF hKU hX R hR
  change section16TypeII P.M P.H at hPTypeII
  rcases section16_theoremII_supportDataForRep_spec
      (G := G) hM hMF hKU hX hR with
    ⟨_x, _hxD, _g, _hNg, _hPcont, _hPMF, _hPKU, _hxA, _hPtype,
      _hPcomp, hTypeII⟩
  exact hTypeII hPTypeII

private theorem CFSG.section16_supportDataForRep_eq_of_same_rep
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {R : Subgroup G}
    (hR hR' : section16_theoremII_supportRepCandidate (G := G) M X R) :
    section16_theoremII_supportDataForRep (G := G) hM hMF hKU hX R hR =
      section16_theoremII_supportDataForRep (G := G) hM hMF hKU hX R hR' := by
  have hproof : hR = hR' := Subsingleton.elim hR hR'
  cases hproof
  rfl

omit [IsMinCE G] in
private theorem CFSG.section16_notConjugate_of_distinct_maximal_representatives
    {Ms : List (Subgroup G)}
    (hMs : section16MaximalConjugacyRepresentatives (G := G) Ms)
    {R S : Subgroup G} (hRmem : R ∈ Ms) (hSmem : S ∈ Ms)
    (hRS : R ≠ S) :
    section12NotConjugate S R := by
  intro g hSgR
  have hRmax : R ∈ section9MaximalSubgroups G := hMs.1 R hRmem
  rcases hMs.2.2 R hRmax with ⟨T, _hT, huniq⟩
  have hR_eq_T : R = T :=
    huniq R ⟨hRmem, ⟨1, by simpa using (section8_conjBy_one (G := G) R).symm⟩⟩
  have hS_eq_T : S = T :=
    huniq S ⟨hSmem, ⟨g, hSgR.symm⟩⟩
  exact hRS (hR_eq_T.trans hS_eq_T.symm)

private theorem CFSG.section16_theoremII_supportDataForRep_isPiSubgroup_sigma_rep
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
  (hX : section16AChoice M K U X)
  {R : Subgroup G}
  (hR : section16_theoremII_supportRepCandidate (G := G) M X R) :
    IsPiSubgroup (G := G) (section10SigmaPrimes R)
      (section16_theoremII_supportDataForRep (G := G) hM hMF hKU hX R hR).H := by
  classical
  let x : G := Classical.choose hR
  have hxSpec := Classical.choose_spec hR
  have hxD : x ∈ section16TheoremIIDSet M X := hxSpec.1
  rcases hxSpec.2 with ⟨g, hNg⟩
  let P : Section16SupportData G :=
    section16_theoremII_supportDataOf (G := G) hM hMF hKU hX x hxD
  have hPspec := section16_theoremII_supportDataOf_spec
    (G := G) hM hMF hKU hX hxD
  have hPpi :
      IsPiSubgroup (G := G) (section10SigmaPrimes P.M) P.H := by
    simpa [P] using
      section16_mf_isPiSubgroup_sigma_of_maximal
        (G := G) (hPspec.1.1) (hPspec.2.1)
  have hPM_eq : P.M = R.conjBy g := by
    simpa [P, section16_theoremII_supportDataOf] using hNg
  rw [hPM_eq, section16_sigmaPrimes_conjBy (G := G) R g] at hPpi
  change IsPiSubgroup (G := G) (section10SigmaPrimes R) P.H
  exact hPpi

private theorem CFSG.section16_theoremII_supportList_pairwise_coprime
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {Ms : List (Subgroup G)}
    (hMs : section16MaximalConjugacyRepresentatives (G := G) Ms)
    {P Q : Section16SupportData G}
    (hPmem : P ∈ section16_theoremII_supportList (G := G) hM hMF hKU hX Ms)
    (hQmem : Q ∈ section16_theoremII_supportList (G := G) hM hMF hKU hX Ms)
    (hPQ : P ≠ Q) :
    Nat.Coprime (Nat.card P.H) (Nat.card Q.H) := by
  classical
  rcases section16_mem_theoremII_supportList
      (G := G) hM hMF hKU hX hPmem with
    ⟨R, hRmem, hR, rfl⟩
  rcases section16_mem_theoremII_supportList
      (G := G) hM hMF hKU hX hQmem with
    ⟨S, hSmem, hS, rfl⟩
  have hRS : R ≠ S := by
    intro hReq
    subst S
    exact hPQ
      (section16_supportDataForRep_eq_of_same_rep
        (G := G) hM hMF hKU hX hR hS)
  have hRmax : R ∈ section9MaximalSubgroups G := hMs.1 R hRmem
  have hSmax : S ∈ section9MaximalSubgroups G := hMs.1 S hSmem
  have hnotconj : section12NotConjugate S R :=
    section16_notConjugate_of_distinct_maximal_representatives
      (G := G) hMs hRmem hSmem hRS
  have hdis :
      Disjoint (section10SigmaPrimes R) (section10SigmaPrimes S) :=
    theorem_13_9 (G := G) hRmax hSmax hnotconj
  exact
    section16_coprime_card_of_isPiSubgroup_disjoint_primes
      (G := G)
      (section16_theoremII_supportDataForRep_isPiSubgroup_sigma_rep
        (G := G) hM hMF hKU hX hR)
      (section16_theoremII_supportDataForRep_isPiSubgroup_sigma_rep
        (G := G) hM hMF hKU hX hS)
      hdis

private theorem CFSG.section16_theoremII_supportList_mem_of_candidate
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {Ms : List (Subgroup G)} {R : Subgroup G}
    (hRmem : R ∈ Ms)
    (hR : section16_theoremII_supportRepCandidate (G := G) M X R) :
    section16_theoremII_supportDataForRep (G := G) hM hMF hKU hX R hR ∈
      section16_theoremII_supportList (G := G) hM hMF hKU hX Ms := by
  classical
  rw [section16_theoremII_supportList, List.mem_filterMap]
  refine ⟨R, hRmem, ?_⟩
  by_cases hR' : section16_theoremII_supportRepCandidate (G := G) M X R
  · simp [hR',
      section16_supportDataForRep_eq_of_same_rep
        (G := G) hM hMF hKU hX hR hR']
  · exact False.elim (hR' hR)

public theorem CFSG.section16_AZeroSet_conj_mem_of_mem_M
    {M K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    {x m : G} (hm : m ∈ M)
    (hx : x ∈ section16AZeroSet M K) :
    m * x * m⁻¹ ∈ section16AZeroSet M K := by
  classical
  rcases hx with ⟨hxHat, hxNotConj, hxne⟩
  have hMconj :
      M.conjBy m = M :=
    section11_conjBy_eq_of_mem_normalizer (H := M) (Subgroup.le_normalizer hm)
  have hxM : x ∈ M := hxHat.1
  have hyM : m * x * m⁻¹ ∈ M := by
    exact M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm)
  have hHat : m * x * m⁻¹ ∈ section16HatMsigmaSet M := by
    refine ⟨hyM, ?_⟩
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hxHat.2 with ⟨z, hz_ne⟩
    let zG : G := z
    have hzσ_conj0 :
        m * zG * m⁻¹ ∈ section10Msigma (M.conjBy m) :=
      section16_mem_msigma_conjBy (G := G) hM (a := m) z.property.1
    have hzσ_conj : m * zG * m⁻¹ ∈ section10Msigma M := by
      simpa [hMconj, zG] using hzσ_conj0
    have hzcent_conj :
        m * zG * m⁻¹ ∈
          Subgroup.centralizer ({m * x * m⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hzcomm : zG * x = x * zG :=
        Subgroup.mem_centralizer_singleton_iff.mp z.property.2
      have h := congrArg (fun t : G => m * t * m⁻¹) hzcomm
      simpa [zG, mul_assoc] using h
    have hz_conj_ne : m * zG * m⁻¹ ≠ 1 := by
      intro hconj
      apply hz_ne
      apply Subtype.ext
      have h := congrArg (fun t : G => m⁻¹ * t * m) hconj
      simpa [zG, mul_assoc] using h
    apply Subgroup.ne_bot_iff_exists_ne_one.mpr
    let w : elementCentralizerIn (section10Msigma M) (m * x * m⁻¹) :=
      ⟨m * zG * m⁻¹, ⟨hzσ_conj, hzcent_conj⟩⟩
    refine ⟨w, ?_⟩
    intro hw
    exact hz_conj_ne (by simpa [w] using congrArg Subtype.val hw)
  have hNotConj :
      m * x * m⁻¹ ∉
        section16ConjugatesOfSetBySet
          (section16NonidentityElements (K : Set G)) (M : Set G) := by
    intro hconj
    rcases hconj with ⟨k, hk, n, hnM, hy_eq⟩
    apply hxNotConj
    refine ⟨k, hk, m⁻¹ * n, M.mul_mem (M.inv_mem hm) hnM, ?_⟩
    have hback := congrArg (fun t : G => m⁻¹ * t * m) hy_eq
    simpa [mul_assoc] using hback
  have hyne : m * x * m⁻¹ ≠ 1 := by
    intro h
    exact hxne (by
      have h' := congrArg (fun t : G => m⁻¹ * t * m) h
      simpa [mul_assoc] using h')
  exact ⟨hHat, hNotConj, hyne⟩

private theorem CFSG.section16_theoremII_D_conj_mem_of_mem_M
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {x m : G} (hxD : x ∈ section16TheoremIIDSet M X) (hm : m ∈ M) :
    m * x * m⁻¹ ∈ section16TheoremIIDSet M X := by
  classical
  have hxσ : x ∈ section10Msigma M :=
    section16_theoremII_mem_msigma_of_mem_D (G := G) hM hMF hKU hX x hxD
  have hMconj :
      M.conjBy m = M :=
    section11_conjBy_eq_of_mem_normalizer (H := M) (Subgroup.le_normalizer hm)
  have hyσ0 :
      m * x * m⁻¹ ∈ section10Msigma (M.conjBy m) :=
    section16_mem_msigma_conjBy (G := G) hM (a := m) hxσ
  have hyσ : m * x * m⁻¹ ∈ section10Msigma M := by
    simpa [hMconj] using hyσ0
  have hyne : m * x * m⁻¹ ≠ 1 := by
    intro hy1
    apply hxD.2.1
    have h := congrArg (fun t : G => m⁻¹ * t * m) hy1
    simpa [mul_assoc] using h
  refine ⟨?_, hyne, ?_⟩
  · rcases hX with hXA | hXA0
    · simpa [hXA] using
        section16_msigma_nonidentity_mem_ASet_public (G := G) hM hyσ hyne
    · have hxA0 : x ∈ section16AZeroSet M K := by
        simpa [hXA0] using hxD.1
      simpa [hXA0] using
        section16_AZeroSet_conj_mem_of_mem_M (G := G) hM hm hxA0
  · intro hCyM
    apply hxD.2.2
    intro c hc
    have hc_conj :
        m * c * m⁻¹ ∈
          Subgroup.centralizer ({m * x * m⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      have h := congrArg (fun t : G => m * t * m⁻¹) hc
      simpa [mul_assoc] using h
    have hmcM : m * c * m⁻¹ ∈ M := hCyM hc_conj
    have hback : m⁻¹ * (m * c * m⁻¹) * m ∈ M :=
      M.mul_mem (M.mul_mem (M.inv_mem hm) hmcM) hm
    simpa [mul_assoc] using hback

private theorem CFSG.section16_section14N_mem_of_nonsingleton
    {x : G} (hx : x ≠ 1)
    (hσ : (section14MsigmaElement x).Nonempty)
    (hcard : 1 < Nat.card {M : Subgroup G // M ∈ section14MsigmaElement x}) :
    section14N x ∈
      section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) := by
  exact section14N_mem_of_nonsingleton (G := G) hx hσ hcard

private theorem CFSG.section16_section14N_conjBy_of_theoremII_D
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {x m : G} (hxD : x ∈ section16TheoremIIDSet M X) (hm : m ∈ M) :
    section14N (m * x * m⁻¹) = (section14N x).conjBy m := by
  classical
  let y : G := m * x * m⁻¹
  have hxσ : x ∈ section10Msigma M :=
    section16_theoremII_mem_msigma_of_mem_D (G := G) hM hMF hKU hX x hxD
  have hxne : x ≠ 1 := hxD.2.1
  have hMx : M ∈ section14MsigmaElement x := by
    exact ⟨hM, by simpa [section14MsigmaElement, section14MsigmaFamily,
      Set.singleton_subset_iff] using hxσ⟩
  have hσx : (section14MsigmaElement x).Nonempty := ⟨M, hMx⟩
  have hcardx :
      1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x} :=
    section16_msigmaElement_card_gt_one_of_not_centralizer_le
      (G := G) hM hxσ hxD.2.2
  have hNxcont :
      section14N x ∈
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
    section16_section14N_mem_of_nonsingleton (G := G) hxne hσx hcardx
  have hyD : y ∈ section16TheoremIIDSet M X := by
    simpa [y] using
      section16_theoremII_D_conj_mem_of_mem_M
        (G := G) hM hMF hKU hX hxD hm
  have hyσ : y ∈ section10Msigma M :=
    section16_theoremII_mem_msigma_of_mem_D (G := G) hM hMF hKU hX y hyD
  have hyne : y ≠ 1 := hyD.2.1
  have hMy : M ∈ section14MsigmaElement y := by
    exact ⟨hM, by simpa [section14MsigmaElement, section14MsigmaFamily,
      Set.singleton_subset_iff] using hyσ⟩
  have hσy : (section14MsigmaElement y).Nonempty := ⟨M, hMy⟩
  have hcardy :
      1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement y} :=
    section16_msigmaElement_card_gt_one_of_not_centralizer_le
      (G := G) hM hyσ hyD.2.2
  have hNycont :
      section14N y ∈
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)) :=
    section16_section14N_mem_of_nonsingleton (G := G) hyne hσy hcardy
  have hNxconjcont :
      (section14N x).conjBy m ∈
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)) := by
    refine ⟨section10_maximal_conjBy (G := G) hNxcont.1 m, ?_⟩
    intro c hc
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨m⁻¹ * c * m, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    apply hNxcont.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have h := congrArg (fun t : G => m⁻¹ * t * m) hc
    simpa [y, mul_assoc] using h
  obtain ⟨N0, _hN0, huniqN0⟩ :=
    theorem_14_4_unique_N (G := G) (x := y) hyne hσy hcardy
  have hNy_eq : section14N y = N0 := huniqN0 (section14N y) hNycont
  have hNxconj_eq : (section14N x).conjBy m = N0 :=
    huniqN0 ((section14N x).conjBy m) hNxconjcont
  exact hNy_eq.trans hNxconj_eq.symm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_K_eq_bot_of_kappa_empty
    {M K U : Subgroup G}
    (hKU : section15KUData M K U)
    (hκ : section14KappaPrimes M = ∅) :
    K = ⊥ := by
  classical
  by_contra hKbot
  have hcard_ne_one : Nat.card K ≠ 1 := by
    intro hcard
    exact hKbot ((Subgroup.card_eq_one (H := K)).1 hcard)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨p, hpprime, hpdiv⟩
  let q : Nat.Primes := ⟨p, hpprime⟩
  have hpdivSub : p ∣ Nat.card (K.subgroupOf M) := by
    simpa [section12_card_subgroupOf_eq hKU.1.1] using hpdiv
  have hqκ : q ∈ section14KappaPrimes M :=
    hKU.1.2.p_in_pi_of_p_dvd_card q (by simpa [q] using hpdivSub)
  simp [hκ] at hqκ

private theorem CFSG.section16_ASet_diff_msigma_absurd_of_tau2_empty
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hτ2 : section12Tau2Primes M = ∅)
    {a : G}
    (ha : a ∈ section16ASet M U \ (section10Msigma M : Set G)) :
    False := by
  classical
  rcases section16_ASet_diff_msigma_exists_prime_compl_zpow
      (G := G) (M := M) (K := K) (U := U) hM hKU ha with
    ⟨n, q, hzorder, hqcompl⟩
  rcases ha.1.1 with ⟨haM, hcent_ne⟩
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hcent_ne with ⟨xC, hxCne⟩
  let x : G := xC
  have hxSigma : x ∈ section10Msigma M := xC.property.1
  have hxne : x ≠ 1 := by
    intro hx
    exact hxCne (Subtype.ext hx)
  have hxcent_a : x ∈ Subgroup.centralizer ({a} : Set G) := xC.property.2
  have hz_ne : a ^ n ≠ 1 := by
    intro hz
    have hq_one : q.val = 1 := by
      simpa [hz] using hzorder.symm
    exact q.property.ne_one hq_one
  have hzM : a ^ n ∈ M := M.zpow_mem haM n
  have hzcent_x : a ^ n ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : Commute x a :=
      Subgroup.mem_centralizer_singleton_iff.mp hxcent_a
    exact (hcomm.zpow_right n).symm
  have hzcentIn : a ^ n ∈ elementCentralizerIn M x := ⟨hzM, hzcent_x⟩
  have hzsupport_compl :
      section14ElementPrimeSupport (a ^ n) ⊆
        ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) := by
    intro p hp
    have hpdiv : p.val ∣ q.val := by
      simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers, hzorder]
        using hp
    have hp_eq : p = q := by
      apply Subtype.ext
      exact (Nat.prime_dvd_prime_iff_eq p.property q.property).1 hpdiv
    simpa [hp_eq] using hqcompl
  have hzsigma' : section14IsPiElement (section10SigmaPrimes M)ᶜ (a ^ n) := by
    intro p hp hpσ
    exact hzsupport_compl hp (Or.inr hpσ)
  rcases corollary_14_3 (G := G) (M := M) hM hxSigma hxne hz_ne hzcentIn
      hzsigma' with hκ | hτ
  · have hqSupp : q ∈ section14ElementPrimeSupport (a ^ n) := by
      simp [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers, hzorder]
    exact hzsupport_compl hqSupp (Or.inl (hκ.1 hqSupp))
  · have hqSupp : q ∈ section14ElementPrimeSupport (a ^ n) := by
      simp [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers, hzorder]
    have hqτ2 : q ∈ section12Tau2Primes M := hτ.1 hqSupp
    simp [hτ2] at hqτ2

private theorem CFSG.section16_AZeroSet_subset_msigma_of_kappa_tau2_empty
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hκ : section14KappaPrimes M = ∅)
    (hτ2 : section12Tau2Primes M = ∅) :
    section16AZeroSet M K ⊆ section10Msigma M := by
  classical
  intro a ha
  by_cases haσ : a ∈ section10Msigma M
  · exact haσ
  by_cases haA : a ∈ section16ASet M U
  · exact False.elim
      (section16_ASet_diff_msigma_absurd_of_tau2_empty
        (G := G) (M := M) (K := K) (U := U) hM hKU hτ2 ⟨haA, haσ⟩)
  · have hsupp :
        section14ElementPrimeSupport a ⊆
          section14KappaPrimes M ∪ section10SigmaPrimes M :=
      section16_A0_diff_A_primeSupport_subset
        (G := G) (M := M) (K := K) (U := U) hM hKU ⟨ha, haA⟩
    have hsuppσ : section14ElementPrimeSupport a ⊆ section10SigmaPrimes M := by
      intro p hp
      rcases hsupp hp with hpκ | hpσ
      · simp [hκ] at hpκ
      · exact hpσ
    exact section16_mem_msigma_of_primeSupport_subset (G := G) hM ha.1.1 hsuppσ

private theorem CFSG.section16_mem_msigma_of_mem_AChoice_of_kappa_tau2_empty
    {M K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hX : section16AChoice M K U X)
    (hκ : section14KappaPrimes M = ∅)
    (hτ2 : section12Tau2Primes M = ∅)
    {x : G} (hx : x ∈ section16NonidentityElements X) :
    x ∈ section10Msigma M := by
  classical
  rcases hX with hXA | hXA0
  · have hxA : x ∈ section16ASet M U := by
      simpa [hXA] using hx.1
    by_cases hxσ : x ∈ section10Msigma M
    · exact hxσ
    · exact False.elim
        (section16_ASet_diff_msigma_absurd_of_tau2_empty
          (G := G) (M := M) (K := K) (U := U) hM hKU hτ2 ⟨hxA, hxσ⟩)
  · have hxA0 : x ∈ section16AZeroSet M K := by
      simpa [hXA0] using hx.1
    exact section16_AZeroSet_subset_msigma_of_kappa_tau2_empty
      (G := G) (M := M) (K := K) (U := U) hM hKU hκ hτ2 hxA0

private theorem CFSG.section16_elementCentralizerIn_le_msigma_of_kappa_tau2_empty
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hκ : section14KappaPrimes M = ∅)
    (hτ2 : section12Tau2Primes M = ∅)
    {x : G} (hxσ : x ∈ section10Msigma M) (hxne : x ≠ 1) :
    elementCentralizerIn M x ≤ section10Msigma M := by
  classical
  have hKbot : K = ⊥ :=
    section16_K_eq_bot_of_kappa_empty (G := G) hKU hκ
  intro c hc
  by_cases hcne : c = 1
  · simp [hcne]
  have hcHat : c ∈ section16HatMsigmaSet M := by
    refine ⟨hc.1, ?_⟩
    have hxCent_c : x ∈ Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hc.2).symm
    let xC : elementCentralizerIn (section10Msigma M) c := ⟨x, hxσ, hxCent_c⟩
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨xC, ?_⟩
    intro hxC_one
    exact hxne (by simpa [xC] using congrArg Subtype.val hxC_one)
  have hcA0 : c ∈ section16AZeroSet M K := by
    refine ⟨hcHat, ?_, hcne⟩
    intro hconj
    rcases hconj with ⟨k, hk, _m, _hmM, _hc_eq⟩
    have hkbot : k ∈ (⊥ : Subgroup G) := by
      simpa [hKbot] using hk.1
    exact hk.2 (by simpa using hkbot)
  exact section16_AZeroSet_subset_msigma_of_kappa_tau2_empty
    (G := G) (M := M) (K := K) (U := U) hM hKU hκ hτ2 hcA0

private noncomputable def CFSG.section16_conjByMulEquiv
    (H : Subgroup G) (g : G) :
    H ≃* H.conjBy g := by
  exact (MulAut.conj g).subgroupMap H

omit [IsMinCE G] in
private theorem CFSG.section16_primeRank_conjBy_eq
    (H : Subgroup G) (q : ℕ) (g : G) :
    primeRank q (H.conjBy g) = primeRank q H := by
  classical
  let e : H ≃* H.conjBy g := section16_conjByMulEquiv (G := G) H g
  exact le_antisymm
    (section10_primeRank_le_of_equiv_pre (R := H) (S := H.conjBy g) q e)
    (section10_primeRank_le_of_equiv_pre (R := H.conjBy g) (S := H) q e.symm)

omit [IsMinCE G] in
private theorem CFSG.section16_tau2Primes_conjBy
    (H : Subgroup G) (g : G) :
    section12Tau2Primes (H.conjBy g) = section12Tau2Primes H := by
  ext p
  constructor <;> intro hp
  · rw [section12Tau2Primes] at hp ⊢
    refine ⟨?_, ?_⟩
    · intro hpσ
      exact hp.1 (by
        simpa [section16_sigmaPrimes_conjBy (G := G) H g] using hpσ)
    · simpa [section16_primeRank_conjBy_eq (G := G) H p.val g] using hp.2
  · rw [section12Tau2Primes] at hp ⊢
    refine ⟨?_, ?_⟩
    · intro hpσ
      exact hp.1 (by
        simpa [section16_sigmaPrimes_conjBy (G := G) H g] using hpσ)
    · simpa [section16_primeRank_conjBy_eq (G := G) H p.val g] using hp.2

private theorem CFSG.section16_theoremII_supportList_centralizer_coprime
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {Ms : List (Subgroup G)}
    (_hMs : section16MaximalConjugacyRepresentatives (G := G) Ms) :
    ∀ P ∈ section16_theoremII_supportList (G := G) hM hMF hKU hX Ms,
      ∀ x : G, x ∈ section16NonidentityElements X →
        Nat.Coprime (Nat.card P.H) (Nat.card (elementCentralizerIn M x)) := by
  classical
  intro P hP x hxX
  rcases section16_mem_theoremII_supportList
      (G := G) hM hMF hKU hX hP with
    ⟨R, _hRmem, hR, rfl⟩
  let P : Section16SupportData G :=
    section16_theoremII_supportDataForRep (G := G) hM hMF hKU hX R hR
  change Nat.Coprime (Nat.card P.H) (Nat.card (elementCentralizerIn M x))
  let x0 : G := Classical.choose hR
  have hx0Spec := Classical.choose_spec hR
  have hx0D : x0 ∈ section16TheoremIIDSet M X := hx0Spec.1
  have hPM_eq : P.M = section14N x0 := by
    rfl
  have hPH_eq : P.H = section10Msigma P.M := by
    rfl
  have hx0σM : x0 ∈ section10Msigma M :=
    section16_theoremII_mem_msigma_of_mem_D (G := G) hM hMF hKU hX x0 hx0D
  have hMx0 : M ∈ section14MsigmaElement x0 := by
    exact ⟨hM, by simpa [section14MsigmaElement, section14MsigmaFamily,
      Set.singleton_subset_iff] using hx0σM⟩
  have hσx0 : (section14MsigmaElement x0).Nonempty := ⟨M, hMx0⟩
  have hcardx0 :
      1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x0} :=
    section16_msigmaElement_card_gt_one_of_not_centralizer_le
      (G := G) hM hx0σM hx0D.2.2
  have hNpack0 :=
    section16_section14N_mem_and_data (G := G) (M := M) (x := x0)
      hx0D.2.1 hσx0 hcardx0 hMx0
  have hPcont0 :
      P.M ∈
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({x0} : Set G)) := by
    simpa [hPM_eq] using hNpack0.1
  have hPdata0 :
      ∀ L : Subgroup G, L ∈ section14MsigmaElement x0 →
        section14Theorem14_4NData x0 (section14R x0) P.M L := by
    intro L hL
    simpa [hPM_eq] using hNpack0.2 L hL
  rcases section16_theoremII_supportDataForRep_spec
      (G := G) hM hMF hKU hX hR with
    ⟨_z, _hzD, _g, _hNg, _hPcont, hPMF, _hPKU, _hzA, _hPtype,
      _hPcomp, _hTypeII⟩
  have hPpi :
      IsPiSubgroup (G := G) (section10SigmaPrimes P.M) P.H :=
    section16_mf_isPiSubgroup_sigma_of_maximal
      (G := G) hPcont0.1 hPMF
  have hCpi :
      IsPiSubgroup (G := G) (subgroupPrimeSet (elementCentralizerIn M x))
        (elementCentralizerIn M x) :=
    section8_isPiSubgroup_of_subgroupPrimeSet_subset
      (G := G) (H := elementCentralizerIn M x)
      (π := subgroupPrimeSet (elementCentralizerIn M x)) (by intro p hp; exact hp)
  have hdis :
      Disjoint (section10SigmaPrimes P.M)
        (subgroupPrimeSet (elementCentralizerIn M x)) := by
    rw [Set.disjoint_left]
    intro q hqσP hqC
    have hqM : q ∈ subgroupPrimeSet M := by
      exact section8_subgroupPrimeSet_mono
        (G := G) (H := elementCentralizerIn M x) (K := M)
        (by intro z hz; exact hz.1) hqC
    have hinter :
        ¬ Disjoint (section10SigmaPrimes P.M) (subgroupPrimeSet M) := by
      rw [Set.not_disjoint_iff_nonempty_inter]
      exact ⟨q, hqσP, hqM⟩
    rcases lemma_14_13_a (G := G) (x := x0) hx0D.2.1 hσx0 hcardx0
        (M := M) (N := P.M) hMx0 hPcont0 hPdata0 hinter with
      ⟨hMFamF, hτ2empty, _hFrob⟩
    have hKU15 : section15KUData M K U :=
      section16_kudata_to_section15 (G := G) hKU
    have hxσM :
        x ∈ section10Msigma M :=
      section16_mem_msigma_of_mem_AChoice_of_kappa_tau2_empty
        (G := G) (M := M) (K := K) (U := U) (X := X)
        hM hKU15 hX hMFamF.2 hτ2empty hxX
    have hCent_le_sigma :
        elementCentralizerIn M x ≤ section10Msigma M :=
      section16_elementCentralizerIn_le_msigma_of_kappa_tau2_empty
        (G := G) (M := M) (K := K) (U := U)
        hM hKU15 hMFamF.2 hτ2empty hxσM hxX.2
    have hqσSub : q ∈ subgroupPrimeSet (section10Msigma M) :=
      section8_subgroupPrimeSet_mono
        (G := G) (H := elementCentralizerIn M x) (K := section10Msigma M)
        hCent_le_sigma hqC
    have hqσM : q ∈ section10SigmaPrimes M := by
      have hqdiv : q.val ∣ Nat.card (section10Msigma M) := by
        simpa [subgroupPrimeSet] using hqσSub
      exact ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card q hqdiv
    have hnotconj : section12NotConjugate P.M M := by
      intro g hPgM
      rcases section16_exists_prime_mem_elementPrimeSupport
          (G := G) hx0D.2.1 with
        ⟨r, hrSupp⟩
      have hPdataM := hPdata0 M hMx0
      rcases hPdataM with
        ⟨_hReq, _hRne, _hprod, hSuppTauP, _hTauP_le_sigmaM,
          _hbeta, _hcomp, _hNF_or_P2⟩
      have hrTauP : r ∈ section12Tau2Primes P.M := hSuppTauP hrSupp
      have hrTauPg : r ∈ section12Tau2Primes (P.M.conjBy g) := by
        simpa [section16_tau2Primes_conjBy (G := G) P.M g] using hrTauP
      have hrTauM : r ∈ section12Tau2Primes M := by
        simpa [hPgM] using hrTauPg
      simp [hτ2empty] at hrTauM
    have hσdis :
        Disjoint (section10SigmaPrimes M) (section10SigmaPrimes P.M) :=
      theorem_13_9 (G := G) hM hPcont0.1 hnotconj
    rw [Set.disjoint_left] at hσdis
    exact hσdis hqσM hqσP
  exact
    section16_coprime_card_of_isPiSubgroup_disjoint_primes
      (G := G) hPpi hCpi hdis

private theorem CFSG.section16_ASet_diff_msigma_subset_AZeroSet
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    section16ASet M U \ (section10Msigma M : Set G) ⊆
      section16AZeroSet M K := by
  classical
  intro a ha
  refine ⟨ha.1.1, ?_, ha.1.2.2⟩
  intro hconj
  rcases section16_ASet_diff_msigma_exists_prime_compl_zpow
      (G := G) (M := M) (K := K) (U := U) hM hKU ha with
    ⟨n, q, horder_a, hqcompl⟩
  rcases hconj with ⟨k, hk, m, _hmM, ha_eq⟩
  have hpow_eq : a ^ n = m * k ^ n * m⁻¹ := by
    rw [ha_eq]
    exact conj_zpow (i := n) (a := m) (b := k)
  have horder_k : orderOf (k ^ n) = q.val := by
    have hconj_order : orderOf (m * k ^ n * m⁻¹) = orderOf (k ^ n) := by
      simpa [MulAut.conj_apply] using (MulAut.conj m).orderOf_eq (k ^ n)
    rw [← hconj_order, ← hpow_eq]
    exact horder_a
  have hqKcard : q.val ∣ Nat.card K := by
    have hkpowK : k ^ n ∈ K := K.zpow_mem hk.1 n
    have hdiv := Subgroup.orderOf_dvd_natCard K hkpowK
    simpa [horder_k] using hdiv
  have hqKsubcard : q.val ∣ Nat.card (K.subgroupOf M) := by
    simpa [section12_card_subgroupOf_eq hKU.1.1] using hqKcard
  have hqκ : q ∈ section14KappaPrimes M :=
    hKU.1.2.p_in_pi_of_p_dvd_card q hqKsubcard
  exact hqcompl (Or.inl hqκ)


private theorem CFSG.section16_AZero_diff_msigma_conj_mem_of_mem_M
    {M K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    {m a : G} (hm : m ∈ M)
    (ha : a ∈ section16AZeroSet M K \ (section10Msigma M : Set G)) :
    m * a * m⁻¹ ∈ section16AZeroSet M K \ (section10Msigma M : Set G) := by
  classical
  refine ⟨section16_AZeroSet_conj_mem_of_mem_M (G := G) hM hm ha.1, ?_⟩
  intro hconjSigma
  have hmNormSigma : m ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    section12_le_normalizer_msigma (M := M) hm
  have hminvNormSigma :
      m⁻¹ ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    Subgroup.inv_mem _ hmNormSigma
  have haSigma : a ∈ section10Msigma M := by
    have hback :
        m⁻¹ * (m * a * m⁻¹) * (m⁻¹)⁻¹ ∈ section10Msigma M :=
      (Subgroup.mem_normalizer_iff.mp hminvNormSigma (m * a * m⁻¹)).1
        hconjSigma
    simpa [mul_assoc] using hback
  exact ha.2 haSigma

private theorem CFSG.section16_AZero_diff_msigma_le_normalizer_of_M
    {M K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    M ≤ Subgroup.normalizer
      (section16AZeroSet M K \ (section10Msigma M : Set G)) := by
  intro m hm
  change ∀ a : G,
    a ∈ section16AZeroSet M K \ (section10Msigma M : Set G) ↔
      m * a * m⁻¹ ∈ section16AZeroSet M K \ (section10Msigma M : Set G)
  intro a
  constructor
  · exact section16_AZero_diff_msigma_conj_mem_of_mem_M
      (G := G) (M := M) (K := K) hM hm
  · intro hconj
    have hback :=
      section16_AZero_diff_msigma_conj_mem_of_mem_M
        (G := G) (M := M) (K := K) hM (M.inv_mem hm) hconj
    simpa [mul_assoc] using hback

private theorem CFSG.section16_AZero_diff_msigma_conjugator_mem_M
    {M K U : Subgroup G} {x y g : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hx : x ∈ section16AZeroSet M K \ (section10Msigma M : Set G))
    (hy : y ∈ section16AZeroSet M K \ (section10Msigma M : Set G))
    (hgy : y = g * x * g⁻¹) :
    g ∈ M := by
  classical
  by_cases hxA : x ∈ section16ASet M U
  · by_cases hyA : y ∈ section16ASet M U
    · exact
        section16_ASet_diff_msigma_conjugator_mem_M
          (G := G) (M := M) (K := K) (U := U) hM hKU
          ⟨hxA, hx.2⟩ ⟨hyA, hy.2⟩ hgy
    · exact False.elim
        ((section16_not_conjugate_ASet_diff_msigma_A0_diff_A
          (G := G) (M := M) (K := K) (U := U) hM hKU
          ⟨hxA, hx.2⟩ ⟨hy.1, hyA⟩)
          ⟨g, by simp, hgy⟩)
  · by_cases hyA : y ∈ section16ASet M U
    · have hyx :
          section16ConjugateInSubgroup (⊤ : Subgroup G) y x := by
        refine ⟨g⁻¹, by simp, ?_⟩
        rw [hgy]
        group
      exact False.elim
        ((section16_not_conjugate_ASet_diff_msigma_A0_diff_A
          (G := G) (M := M) (K := K) (U := U) hM hKU
          ⟨hyA, hy.2⟩ ⟨hx.1, hxA⟩) hyx)
    · exact
        section16_A0_diff_A_conjugator_mem_M
          (G := G) (M := M) (K := K) (U := U) hM hKU
          ⟨hx.1, hxA⟩ ⟨hy.1, hyA⟩ hgy

private theorem CFSG.section16_AZero_diff_msigma_TI
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    section16TISubset (section16AZeroSet M K \ (section10Msigma M : Set G)) := by
  classical
  let T : Set G := section16AZeroSet M K \ (section10Msigma M : Set G)
  have hMnormT : M ≤ Subgroup.normalizer T :=
    section16_AZero_diff_msigma_le_normalizer_of_M (G := G) (M := M) (K := K) hM
  intro g
  by_cases hgM : g ∈ M
  · left
    ext z
    constructor
    · intro hz
      rcases hz with ⟨x, hxT, rfl⟩
      have hnorm := hMnormT hgM
      change ∀ a : G, a ∈ T ↔ g * a * g⁻¹ ∈ T at hnorm
      exact (hnorm x).1 hxT
    · intro hzT
      have hginvM : g⁻¹ ∈ M := M.inv_mem hgM
      have hxT : g⁻¹ * z * g ∈ T := by
        have hnorm := hMnormT hginvM
        change ∀ a : G, a ∈ T ↔ g⁻¹ * a * (g⁻¹)⁻¹ ∈ T at hnorm
        simpa using (hnorm z).1 hzT
      exact ⟨g⁻¹ * z * g, hxT, by group⟩
  · right
    intro z hz
    exfalso
    rcases hz with ⟨hzT, hzConj⟩
    rcases hzConj with ⟨x, hxT, hz_eq⟩
    exact hgM
      (section16_AZero_diff_msigma_conjugator_mem_M
        (G := G) (M := M) (K := K) (U := U) hM hKU hxT hzT hz_eq)

private theorem CFSG.section16_AZero_diff_msigma_normalizer_eq
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hne : (section16AZeroSet M K \ (section10Msigma M : Set G)).Nonempty) :
    Subgroup.normalizer
      (section16AZeroSet M K \ (section10Msigma M : Set G)) = M := by
  classical
  let T : Set G := section16AZeroSet M K \ (section10Msigma M : Set G)
  apply le_antisymm
  · intro g hg
    rcases hne with ⟨x, hxT⟩
    change g ∈ Subgroup.normalizer T at hg
    have hxT' : x ∈ T := by
      simpa [T] using hxT
    change ∀ y : G, y ∈ T ↔ g * y * g⁻¹ ∈ T at hg
    have hgxT' : g * x * g⁻¹ ∈ T :=
      (hg x).1 hxT'
    have hgxT : g * x * g⁻¹ ∈
        section16AZeroSet M K \ (section10Msigma M : Set G) := by
      simpa [T] using hgxT'
    exact
      section16_AZero_diff_msigma_conjugator_mem_M
        (G := G) (M := M) (K := K) (U := U) hM hKU hxT hgxT rfl
  · exact section16_AZero_diff_msigma_le_normalizer_of_M
      (G := G) (M := M) (K := K) hM

private theorem CFSG.section16_theoremII_support_AZero_diff_H_nonempty_TI
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {Ms : List (Subgroup G)} :
    ∀ P ∈ section16_theoremII_supportList (G := G) hM hMF hKU hX Ms,
      (section16AZeroSet P.M P.K \ (P.H : Set G)).Nonempty ∧
        section16TISubsetWithNormalizer
          (section16AZeroSet P.M P.K \ (P.H : Set G)) P.M := by
  classical
  intro P hP
  rcases section16_mem_theoremII_supportList
      (G := G) hM hMF hKU hX hP with
    ⟨R, _hRmem, hR, rfl⟩
  let P : Section16SupportData G :=
    section16_theoremII_supportDataForRep (G := G) hM hMF hKU hX R hR
  change
    (section16AZeroSet P.M P.K \ (P.H : Set G)).Nonempty ∧
      section16TISubsetWithNormalizer
        (section16AZeroSet P.M P.K \ (P.H : Set G)) P.M
  rcases section16_theoremII_supportDataForRep_spec
      (G := G) hM hMF hKU hX hR with
    ⟨x, _hxD, _g, _hNg, hPcont, _hPMF, hPKU, hxA, _hPtype,
      _hPcomp, _hTypeII⟩
  have hH_eq : P.H = section10Msigma P.M := by
    rfl
  have hPKU15 : section15KUData P.M P.K P.U :=
    section16_kudata_to_section15 (G := G) hPKU
  have hxA_msigma :
      x ∈ section16ASet P.M P.U \ (section10Msigma P.M : Set G) := by
    change x ∈ section16ASet P.M P.U ∧ x ∉ section10Msigma P.M
    change x ∈ section16ASet P.M P.U ∧ x ∉ P.H at hxA
    rw [hH_eq] at hxA
    exact hxA
  have hxA0 : x ∈ section16AZeroSet P.M P.K :=
    section16_ASet_diff_msigma_subset_AZeroSet (G := G) hPcont.1 hPKU15 hxA_msigma
  have hNonemptySigma :
      (section16AZeroSet P.M P.K \ (section10Msigma P.M : Set G)).Nonempty :=
    ⟨x, hxA0, hxA_msigma.2⟩
  have hTI :
      section16TISubset
        (section16AZeroSet P.M P.K \ (section10Msigma P.M : Set G)) :=
    section16_AZero_diff_msigma_TI
      (G := G) (M := P.M) (K := P.K) (U := P.U) hPcont.1 hPKU15
  have hNorm :
      Subgroup.normalizer
        (section16AZeroSet P.M P.K \ (section10Msigma P.M : Set G)) = P.M :=
    section16_AZero_diff_msigma_normalizer_eq
      (G := G) (M := P.M) (K := P.K) (U := P.U) hPcont.1 hPKU15
      hNonemptySigma
  refine ⟨?_, ?_⟩
  · simpa [hH_eq] using hNonemptySigma
  · refine ⟨?_, ?_⟩
    · simpa [hH_eq] using hTI
    · simpa [hH_eq] using hNorm

private theorem CFSG.section16_theoremII_supportList_coverage
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {Ms : List (Subgroup G)}
    (hMs : section16MaximalConjugacyRepresentatives (G := G) Ms) :
    ∀ x : G, x ∈ section16TheoremIIDSet M X →
      ∃ y : G, ∃ P : Section16SupportData G,
        y ∈ section16TheoremIIDSet M X ∧ section16ConjugateInSubgroup ⊤ x y ∧
          P ∈ section16_theoremII_supportList (G := G) hM hMF hKU hX Ms ∧
            ((Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) =
              (section16CentralizerInSet P.H ({y} : Set G) : Set G) *
                (elementCentralizerIn M y : Set G) ∧
            Subgroup.centralizer ({y} : Set G) ≤ P.M := by
  classical
  intro x hxD
  rcases section16_theoremII_canonical_D_data
      (G := G) hM hMF hKU hX hxD with
    ⟨_NKx, _NUx, hNxcont, _hNFx, _hKUx, _hxA, _hTypex, _hCompx, _hTypeIIx⟩
  rcases hMs.2.2 (section14N x) hNxcont.1 with
    ⟨R, hR, _hRuniq⟩
  rcases hR.2 with ⟨gx, hNxR⟩
  let hRcand : section16_theoremII_supportRepCandidate (G := G) M X R :=
    ⟨x, hxD, gx, hNxR⟩
  let P : Section16SupportData G :=
    section16_theoremII_supportDataForRep (G := G) hM hMF hKU hX R hRcand
  have hPmem :
      P ∈ section16_theoremII_supportList (G := G) hM hMF hKU hX Ms := by
    simpa [P, hRcand] using
      section16_theoremII_supportList_mem_of_candidate
        (G := G) hM hMF hKU hX hR.1 hRcand
  let x0 : G := Classical.choose hRcand
  have hx0Spec := Classical.choose_spec hRcand
  have hx0D : x0 ∈ section16TheoremIIDSet M X := hx0Spec.1
  rcases hx0Spec.2 with ⟨g0, hNx0R⟩
  have hPM_eq : P.M = section14N x0 := by
    rfl
  have hPH_eq : P.H = section10Msigma P.M := by
    rfl
  have hx0σM : x0 ∈ section10Msigma M :=
    section16_theoremII_mem_msigma_of_mem_D (G := G) hM hMF hKU hX x0 hx0D
  have hMx0 : M ∈ section14MsigmaElement x0 := by
    exact ⟨hM, by simpa [section14MsigmaElement, section14MsigmaFamily,
      Set.singleton_subset_iff] using hx0σM⟩
  have hσx0 : (section14MsigmaElement x0).Nonempty := ⟨M, hMx0⟩
  have hcardx0 :
      1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x0} :=
    section16_msigmaElement_card_gt_one_of_not_centralizer_le
      (G := G) hM hx0σM hx0D.2.2
  have hNpack0 :=
    section16_section14N_mem_and_data (G := G) (M := M) (x := x0)
      hx0D.2.1 hσx0 hcardx0 hMx0
  have hPcont0 :
      P.M ∈
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({x0} : Set G)) := by
    simpa [hPM_eq] using hNpack0.1
  have hPdata0 :
      ∀ L : Subgroup G, L ∈ section14MsigmaElement x0 →
        section14Theorem14_4NData x0 (section14R x0) P.M L := by
    intro L hL
    simpa [hPM_eq] using hNpack0.2 L hL
  have hgAlign : (section14N x).conjBy (g0 * gx⁻¹) = P.M := by
    calc
      (section14N x).conjBy (g0 * gx⁻¹)
          = (R.conjBy gx).conjBy (g0 * gx⁻¹) := by rw [hNxR]
      _ = R.conjBy ((g0 * gx⁻¹) * gx) := by
            rw [section11_conjBy_conjBy]
      _ = R.conjBy g0 := by simp [mul_assoc]
      _ = section14N x0 := hNx0R.symm
      _ = P.M := hPM_eq.symm
  have hxσM : x ∈ section10Msigma M :=
    section16_theoremII_mem_msigma_of_mem_D (G := G) hM hMF hKU hX x hxD
  rcases lemma_14_13_b (G := G) (x := x0) hx0D.2.1 hσx0 hcardx0
      (M := M) (N := P.M) hMx0 hPcont0 hPdata0
      (y := x) hxσM hxD.2.1 hxD.2.2 (g0 * gx⁻¹) hgAlign with
    ⟨m, hmM, hmN⟩
  let y : G := m * x * m⁻¹
  have hyD : y ∈ section16TheoremIIDSet M X := by
    simpa [y] using
      section16_theoremII_D_conj_mem_of_mem_M
        (G := G) hM hMF hKU hX hxD hmM
  have hxy : section16ConjugateInSubgroup (⊤ : Subgroup G) x y := by
    refine ⟨m, by simp, ?_⟩
    simp [y]
  have hyN_eq : section14N y = P.M := by
    calc
      section14N y = (section14N x).conjBy m := by
        simpa [y] using
          section16_section14N_conjBy_of_theoremII_D
            (G := G) hM hMF hKU hX hxD hmM
      _ = P.M := hmN
  rcases section16_theoremII_canonical_D_data
      (G := G) hM hMF hKU hX hyD with
    ⟨_NKy, _NUy, hNycont, _hNFy, _hKUy, _hyA, _hTypey, _hCompy, _hTypeIIy⟩
  have hCyP : Subgroup.centralizer ({y} : Set G) ≤ P.M := by
    simpa [hyN_eq] using hNycont.2
  have hyσM : y ∈ section10Msigma M :=
    section16_theoremII_mem_msigma_of_mem_D (G := G) hM hMF hKU hX y hyD
  have hMy : M ∈ section14MsigmaElement y := by
    exact ⟨hM, by simpa [section14MsigmaElement, section14MsigmaFamily,
      Set.singleton_subset_iff] using hyσM⟩
  have hσy : (section14MsigmaElement y).Nonempty := ⟨M, hMy⟩
  have hcardy :
      1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement y} :=
    section16_msigmaElement_card_gt_one_of_not_centralizer_le
      (G := G) hM hyσM hyD.2.2
  have hprod14 :
      ((Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) =
        (elementCentralizerIn (M ⊓ section14N y) y : Set G) *
          (section14R y : Set G) :=
    theorem_14_4_b (G := G) (x := y) hyD.2.1 hσy hcardy hMy
  have hEMinf :
      elementCentralizerIn (M ⊓ P.M) y = elementCentralizerIn M y :=
    section16_elementCentralizerIn_inf_eq_left_of_centralizer_le
      (G := G) (M := M) (N := P.M) (x := y) hCyP
  have hR_eq_PH :
      section14R y = section16CentralizerInSet P.H ({y} : Set G) := by
    calc
      section14R y =
          elementCentralizerIn (section10Msigma (section14N y)) y :=
        (theorem_14_4_a (G := G) (x := y) hyD.2.1 hσy hcardy hMy).1
      _ = elementCentralizerIn P.H y := by
            simp [hyN_eq, hPH_eq]
      _ = section16CentralizerInSet P.H ({y} : Set G) := rfl
  have hRnormC :
      Subgroup.centralizer ({y} : Set G) ≤
        Subgroup.normalizer (section14R y : Set G) := by
    rcases (theorem_14_4 (G := G) (x := y) hyD.2.1 hσy).1 with
      ⟨_hRleC, hRnormInC, _hRHall⟩
    exact section10_normalIn_le_normalizer (G := G) hRnormInC
  have hEM_norm_R :
      (elementCentralizerIn M y : Set G) ⊆
        Subgroup.normalizer (section14R y : Set G) := by
    intro z hz
    exact hRnormC hz.2
  have hcommProd :
      (elementCentralizerIn M y : Set G) * (section14R y : Set G) =
        (section14R y : Set G) * (elementCentralizerIn M y : Set G) :=
    Subgroup.set_mul_normalizer_comm
      (elementCentralizerIn M y : Set G) (section14R y) hEM_norm_R
  have hprodOrdered :
      ((Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) =
        (section14R y : Set G) * (elementCentralizerIn M y : Set G) := by
    calc
      ((Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G)
          = (elementCentralizerIn (M ⊓ section14N y) y : Set G) *
              (section14R y : Set G) := hprod14
      _ = (elementCentralizerIn (M ⊓ P.M) y : Set G) *
              (section14R y : Set G) := by rw [hyN_eq]
      _ = (elementCentralizerIn M y : Set G) * (section14R y : Set G) := by
            rw [hEMinf]
      _ = (section14R y : Set G) * (elementCentralizerIn M y : Set G) :=
            hcommProd
  have hprodTarget :
      ((Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) =
        (section16CentralizerInSet P.H ({y} : Set G) : Set G) *
          (elementCentralizerIn M y : Set G) := by
    simpa [hR_eq_PH] using hprodOrdered
  exact ⟨y, P, hyD, hxy, hPmem, hprodTarget, hCyP⟩

private theorem CFSG.section16_theoremII_D_subset_A
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X) :
    section16TheoremIIDSet M X ⊆ section16ASet M U := by
  intro x hxD
  exact section16_msigma_nonidentity_mem_ASet_public (G := G) hM
    (section16_theoremII_mem_msigma_of_mem_D (G := G) hM hMF hKU hX x hxD)
    hxD.2.1

private theorem CFSG.section16_theoremII_unique_centralizer_overgroup
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X) :
    ∀ x : G, x ∈ section16TheoremIIDSet M X →
      ∃ N : Subgroup G,
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {N} := by
  classical
  have hD : section16TheoremDConclusions M MF K U :=
    theorem_16_D (G := G) hM hMF hKU
  intro x hxD
  have hxσ : x ∈ section10Msigma M :=
    section16_theoremII_mem_msigma_of_mem_D (G := G) hM hMF hKU hX x hxD
  have hxne : x ≠ 1 := hxD.2.1
  rcases hD.2.2 x hxσ hxne with ⟨R, _hRcomp, hR⟩
  rcases hR hxD.2.2 with ⟨N, huniq, _hReq, _hAux, _hType, _hComp, _hP2⟩
  exact ⟨N, huniq⟩

private theorem CFSG.section16_theoremII_fusion_in_X
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X) :
    ∀ x y : G, x ∈ X → y ∈ X →
      section16ConjugateInSubgroup ⊤ x y → section16ConjugateInSubgroup M x y := by
  classical
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  intro x y hxX hyX hxy
  by_cases hx1 : x = 1
  · subst x
    rcases hxy with ⟨g, _hg, hgy⟩
    have hy1 : y = 1 := by simpa using hgy
    subst y
    exact ⟨1, M.one_mem, by simp⟩
  by_cases hxσ : x ∈ section10Msigma M
  · have hyσ : y ∈ section10Msigma M :=
      section16_mem_msigma_of_conj_mem_AChoice
        (G := G) (M := M) (K := K) (U := U) (X := X) hM hX hxσ hyX hxy
    exact (theorem_16_D (G := G) hM hMF hKU).1 x y hxσ hyσ hxy
  · rcases hX with hXA | hXA0
    · have hxA : x ∈ section16ASet M U := by
        simpa [hXA] using hxX
      have hyA : y ∈ section16ASet M U := by
        simpa [hXA] using hyX
      have hyσ_false : y ∉ section10Msigma M := by
        intro hyσ
        have hxσ' : x ∈ section10Msigma M :=
          section16_mem_msigma_of_conj_mem_AChoice
            (G := G) (M := M) (K := K) (U := U) (X := X) hM
            (Or.inl hXA) hyσ hxX
            (section16_conjugateInSubgroup_top_symm (G := G) hxy)
        exact hxσ hxσ'
      exact section16_ASet_diff_msigma_fusion_in_M
        (G := G) (M := M) (K := K) (U := U) hM hKU15
        ⟨hxA, hxσ⟩ ⟨hyA, hyσ_false⟩ hxy
    · have hxA0 : x ∈ section16AZeroSet M K := by
        simpa [hXA0] using hxX
      have hyA0 : y ∈ section16AZeroSet M K := by
        simpa [hXA0] using hyX
      have hyσ_false : y ∉ section10Msigma M := by
        intro hyσ
        have hxσ' : x ∈ section10Msigma M :=
          section16_mem_msigma_of_conj_mem_AChoice
            (G := G) (M := M) (K := K) (U := U) (X := X) hM
            (Or.inr hXA0) hyσ hxX
            (section16_conjugateInSubgroup_top_symm (G := G) hxy)
        exact hxσ hxσ'
      by_cases hxA : x ∈ section16ASet M U
      · by_cases hyA : y ∈ section16ASet M U
        · exact section16_ASet_diff_msigma_fusion_in_M
            (G := G) (M := M) (K := K) (U := U) hM hKU15
            ⟨hxA, hxσ⟩ ⟨hyA, hyσ_false⟩ hxy
        · exact False.elim
            (section16_not_conjugate_ASet_diff_msigma_A0_diff_A
              (G := G) (M := M) (K := K) (U := U) hM hKU15
              ⟨hxA, hxσ⟩ ⟨hyA0, hyA⟩ hxy)
      · by_cases hyA : y ∈ section16ASet M U
        · have hnot :=
            section16_not_conjugate_ASet_diff_msigma_A0_diff_A
              (G := G) (M := M) (K := K) (U := U) hM hKU15
              ⟨hyA, hyσ_false⟩ ⟨hxA0, hxA⟩
          exact False.elim
            (hnot (section16_conjugateInSubgroup_top_symm (G := G) hxy))
        · exact section16_A0_diff_A_fusion_in_M
            (G := G) (M := M) (K := K) (U := U) hM hKU15
            ⟨hxA0, hxA⟩ ⟨hyA0, hyA⟩ hxy

private theorem CFSG.section16_theoremII_supporting_system
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X) :
    (section16TheoremIIDSet M X).Nonempty →
      ∃ support : List (Section16SupportData G),
        section16TheoremIISupportingSystem M X (section16TheoremIIDSet M X) support ∧
          (section16SomeSupportingSubgroupTypeII support →
            section16FrobeniusWithCyclicComplement M MF ∧
              section16TypeI M MF ∧
                ¬ section16TISubset (MF : Set G)) := by
  classical
  intro _hDne
  rcases section16_exists_maximalConjugacyRepresentatives (G := G) with
    ⟨Ms, hMs⟩
  let support : List (Section16SupportData G) :=
    section16_theoremII_supportList (G := G) hM hMF hKU hX Ms
  refine ⟨support, ?_, ?_⟩
  · dsimp [section16TheoremIISupportingSystem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro P hP
      exact section16_theoremII_supportList_entry_facts
        (G := G) hM hMF hKU hX hP
    · intro P hP Q hQ hPQ
      exact section16_theoremII_supportList_pairwise_coprime
        (G := G) hM hMF hKU hX hMs hP hQ hPQ
    · intro P hP
      exact section16_theoremII_supportList_complement_split
        (G := G) hM hMF hKU hX hP
    · exact section16_theoremII_supportList_centralizer_coprime
        (G := G) hM hMF hKU hX hMs
    · exact section16_theoremII_support_AZero_diff_H_nonempty_TI
        (G := G) hM hMF hKU hX
    · exact section16_theoremII_supportList_coverage
        (G := G) hM hMF hKU hX hMs
  · exact section16_theoremII_supportList_typeII_consequence
      (G := G) hM hMF hKU hX

/-- In the notation of Theorem II, every element of `D` lies in `M_sigma`. -/
public theorem CFSG.theorem_16_II_mem_msigma_of_mem_D
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X) :
    ∀ x : G, x ∈ section16TheoremIIDSet M X → x ∈ section10Msigma M :=
  section16_theoremII_mem_msigma_of_mem_D (G := G) hM hMF hKU hX

/-- Canonical exact supporting data for an element of the Theorem II `D`-set. -/
public theorem CFSG.theorem_16_II_canonical_D_data
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {x : G} (hxD : x ∈ section16TheoremIIDSet M X) :
    let N : Subgroup G := section14N x
    ∃ NK NU : Subgroup G,
      N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
        section16MFSubgroup N (section10Msigma N) ∧
          section16KUData N NK NU ∧
            x ∈ section16ASet N NU \ (section10Msigma N : Set G) ∧
              (section16TypeI N (section10Msigma N) ∨
                section16TypeII N (section10Msigma N)) ∧
                section12ComplementIn N (section10Msigma N) (M ⊓ N) ∧
                  (section16TypeII N (section10Msigma N) →
                    section16FrobeniusWithCyclicComplement M MF ∧
                      section16TypeI M MF ∧
                        ¬ section16TISubset (MF : Set G)) :=
  section16_theoremII_canonical_D_data (G := G) hM hMF hKU hX hxD

/-- The Theorem D complement in the exact supporting subgroup attached to
an element of the Theorem II `D`-set. -/
public theorem CFSG.theorem_16_II_canonical_theoremDComplement
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {x : G} (hxD : x ∈ section16TheoremIIDSet M X) :
    let N : Subgroup G := section14N x
    section16TheoremDComplement M x (elementCentralizerIn (section10Msigma N) x) := by
  classical
  dsimp
  rcases theorem_16_II_canonical_D_data (G := G) hM hMF hKU hX hxD with
    ⟨_NK, _NU, hNcont, _hNF, _hNKU, _hxA, _hType, _hComp, _hTypeII⟩
  have hxσ : x ∈ section10Msigma M :=
    theorem_16_II_mem_msigma_of_mem_D (G := G) hM hMF hKU hX x hxD
  rcases (theorem_16_D (G := G) hM hMF hKU).2.2 x hxσ hxD.2.1 with
    ⟨R, hRcomp, hR⟩
  rcases hR hxD.2.2 with
    ⟨N', huniq, hReq, _hAux, _hType, _hComp, _hP2impl⟩
  have hNmem : section14N x ∈ ({N'} : Set (Subgroup G)) := by
    simpa [huniq] using hNcont
  have hN_eq : section14N x = N' := by
    simpa using hNmem
  have hR_eq : R = elementCentralizerIn (section10Msigma (section14N x)) x := by
    calc
      R = elementCentralizerIn (section10Msigma N') x := hReq
      _ = elementCentralizerIn (section10Msigma (section14N x)) x := by
        rw [hN_eq]
  simpa [hR_eq] using hRcomp

/-- The exact supporting subgroup attached to an element of the Theorem II
`D`-set has order coprime to every source centralizer in `M`. -/
public theorem CFSG.theorem_16_II_canonical_support_coprime
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X)
    {x : G} (hxD : x ∈ section16TheoremIIDSet M X) :
    let N : Subgroup G := section14N x
    ∀ y : G, y ∈ section16NonidentityElements X →
      Nat.Coprime (Nat.card (section10Msigma N))
        (Nat.card (elementCentralizerIn M y)) := by
  classical
  dsimp
  intro y hyX
  rcases theorem_16_II_canonical_D_data (G := G) hM hMF hKU hX hxD with
    ⟨_NK, _NU, hNcont, hNMF, _hNKU, _hxA, _hType, _hComp, _hTypeII⟩
  have hxσM : x ∈ section10Msigma M :=
    theorem_16_II_mem_msigma_of_mem_D (G := G) hM hMF hKU hX x hxD
  have hMx : M ∈ section14MsigmaElement x := by
    exact ⟨hM, by simpa [section14MsigmaElement, section14MsigmaFamily,
      Set.singleton_subset_iff] using hxσM⟩
  have hσx : (section14MsigmaElement x).Nonempty := ⟨M, hMx⟩
  have hcardx :
      1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x} :=
    section16_msigmaElement_card_gt_one_of_not_centralizer_le
      (G := G) hM hxσM hxD.2.2
  have hNpack :=
    section16_section14N_mem_and_data (G := G) (M := M) (x := x)
      hxD.2.1 hσx hcardx hMx
  have hNdata :
      ∀ L : Subgroup G, L ∈ section14MsigmaElement x →
        section14Theorem14_4NData x (section14R x) (section14N x) L := by
    intro L hL
    exact hNpack.2 L hL
  have hNpi :
      IsPiSubgroup (G := G) (section10SigmaPrimes (section14N x))
        (section10Msigma (section14N x)) :=
    section16_mf_isPiSubgroup_sigma_of_maximal
      (G := G) hNcont.1 hNMF
  have hCpi :
      IsPiSubgroup (G := G) (subgroupPrimeSet (elementCentralizerIn M y))
        (elementCentralizerIn M y) :=
    section8_isPiSubgroup_of_subgroupPrimeSet_subset
      (G := G) (H := elementCentralizerIn M y)
      (π := subgroupPrimeSet (elementCentralizerIn M y)) (by intro p hp; exact hp)
  have hdis :
      Disjoint (section10SigmaPrimes (section14N x))
        (subgroupPrimeSet (elementCentralizerIn M y)) := by
    rw [Set.disjoint_left]
    intro q hqσN hqC
    have hqM : q ∈ subgroupPrimeSet M := by
      exact section8_subgroupPrimeSet_mono
        (G := G) (H := elementCentralizerIn M y) (K := M)
        (by intro z hz; exact hz.1) hqC
    have hinter :
        ¬ Disjoint (section10SigmaPrimes (section14N x)) (subgroupPrimeSet M) := by
      rw [Set.not_disjoint_iff_nonempty_inter]
      exact ⟨q, hqσN, hqM⟩
    rcases lemma_14_13_a (G := G) (x := x) hxD.2.1 hσx hcardx
        (M := M) (N := section14N x) hMx hNcont hNdata hinter with
      ⟨hMFamF, hτ2empty, _hFrob⟩
    have hKU15 : section15KUData M K U :=
      section16_kudata_to_section15 (G := G) hKU
    have hyσM :
        y ∈ section10Msigma M :=
      section16_mem_msigma_of_mem_AChoice_of_kappa_tau2_empty
        (G := G) (M := M) (K := K) (U := U) (X := X)
        hM hKU15 hX hMFamF.2 hτ2empty hyX
    have hCent_le_sigma :
        elementCentralizerIn M y ≤ section10Msigma M :=
      section16_elementCentralizerIn_le_msigma_of_kappa_tau2_empty
        (G := G) (M := M) (K := K) (U := U)
        hM hKU15 hMFamF.2 hτ2empty hyσM hyX.2
    have hqσSub : q ∈ subgroupPrimeSet (section10Msigma M) :=
      section8_subgroupPrimeSet_mono
        (G := G) (H := elementCentralizerIn M y) (K := section10Msigma M)
        hCent_le_sigma hqC
    have hqσM : q ∈ section10SigmaPrimes M := by
      have hqdiv : q.val ∣ Nat.card (section10Msigma M) := by
        simpa [subgroupPrimeSet] using hqσSub
      exact ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card q hqdiv
    have hnotconj : section12NotConjugate (section14N x) M := by
      intro g hNgM
      rcases section16_exists_prime_mem_elementPrimeSupport
          (G := G) hxD.2.1 with
        ⟨r, hrSupp⟩
      have hNdataM := hNdata M hMx
      rcases hNdataM with
        ⟨_hReq, _hRne, _hprod, hSuppTauN, _hTauN_le_sigmaM,
          _hbeta, _hcomp, _hNF_or_P2⟩
      have hrTauN : r ∈ section12Tau2Primes (section14N x) :=
        hSuppTauN hrSupp
      have hrTauNg : r ∈ section12Tau2Primes ((section14N x).conjBy g) := by
        simpa [section16_tau2Primes_conjBy (G := G) (section14N x) g] using
          hrTauN
      have hrTauM : r ∈ section12Tau2Primes M := by
        simpa [hNgM] using hrTauNg
      simp [hτ2empty] at hrTauM
    have hσdis :
        Disjoint (section10SigmaPrimes M) (section10SigmaPrimes (section14N x)) :=
      theorem_13_9 (G := G) hM hNcont.1 hnotconj
    rw [Set.disjoint_left] at hσdis
    exact hσdis hqσM hqσN
  exact
    section16_coprime_card_of_isPiSubgroup_disjoint_primes
      (G := G) hNpi hCpi hdis

/-- Theorem II: the tamely-imbedded subset theorem for `A(M)` and `A_0(M)`. -/
public theorem CFSG.theorem_16_II
    {M MF K U : Subgroup G} {X : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hX : section16AChoice M K U X) :
    let D := section16TheoremIIDSet M X
    D ⊆ section16ASet M U ∧
      (∀ x : G, x ∈ D →
        ∃ N : Subgroup G, section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G)) = {N}) ∧
      (∀ x y : G, x ∈ X → y ∈ X →
        section16ConjugateInSubgroup ⊤ x y → section16ConjugateInSubgroup M x y) ∧
      (D.Nonempty →
        ∃ support : List (Section16SupportData G),
          section16TheoremIISupportingSystem M X D support ∧
            (section16SomeSupportingSubgroupTypeII support →
              section16FrobeniusWithCyclicComplement M MF ∧
                section16TypeI M MF ∧
                  ¬ section16TISubset (MF : Set G))) := by
  classical
  dsimp
  exact ⟨
    section16_theoremII_D_subset_A (G := G) hM hMF hKU hX,
    section16_theoremII_unique_centralizer_overgroup (G := G) hM hMF hKU hX,
    section16_theoremII_fusion_in_X (G := G) hM hMF hKU hX,
    section16_theoremII_supporting_system (G := G) hM hMF hKU hX⟩

end MainResults
