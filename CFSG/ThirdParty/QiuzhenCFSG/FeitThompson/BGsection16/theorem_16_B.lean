module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection16.theorem_16_A
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_1
import Mathlib.GroupTheory.Schreier
import Mathlib.Order.Preorder.Finite

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Theorem 16 b from BG Section 16 -/

section MainResults

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
private theorem CFSG.section16_one_mem_hatMsigmaSet
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    (1 : G) ∈ section16HatMsigmaSet M := by
  refine ⟨M.one_mem, ?_⟩
  have hcent_one :
      elementCentralizerIn (section10Msigma M) (1 : G) = section10Msigma M := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      refine ⟨hx, ?_⟩
      change x ∈ Subgroup.centralizer ({(1 : G)} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy_one : y = 1 := by simpa using hy
      subst y
      simp
  simpa [hcent_one] using theorem_10_2_e (G := G) hM

private theorem CFSG.section16_bot_inter_hatMsigmaSet_eq_singleton
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    ((⊥ : Subgroup G) : Set G) ∩ section16HatMsigmaSet M = ({1} : Set G) := by
  ext x
  constructor
  · intro hx
    have hx_one : x = 1 := by simpa using hx.1
    simp [hx_one]
  · intro hx
    have hx_one : x = 1 := by simpa using hx
    subst x
    exact ⟨by simp, section16_one_mem_hatMsigmaSet (G := G) hM⟩

public theorem CFSG.section16_groupRank_U_le_two_of_section15
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    groupRank U ≤ 2 := by
  classical
  let E : Subgroup G := K ⊔ U
  have hEcomp : section12ComplementToMsigma M E := by
    change section12ComplementIn M (section10Msigma M) (K ⊔ U)
    exact hKU.2.2.1
  let eE : E.subgroupOf M ≃* E :=
    Subgroup.subgroupOfEquivOfLe (H := E) (K := M) hEcomp.2.1
  have hE_rank : groupRank E ≤ 2 :=
    (groupRank_le_of_equiv eE).trans
      (section10_hall_compl_sigma_groupRank_le_two hM
        (section12_msigma_complement_isHall_sigma_compl hM hEcomp))
  have hUE : U ≤ E := by
    intro x hx
    exact Subgroup.mem_sup_right hx
  let eU : U.subgroupOf E ≃* U :=
    Subgroup.subgroupOfEquivOfLe (H := U) (K := E) hUE
  exact ((groupRank_le_of_equiv eU).trans
    (groupRank_le_of_subgroup (R := E) (U.subgroupOf E))).trans hE_rank

private theorem CFSG.section16_hasAbelianSylowRankAtMostTwo_of_section15
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    section16HasAbelianSylowRankAtMostTwo U := by
  classical
  have hUπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ U := by
    intro q hqU
    have hUHall := hKU.2.2.2.1
    have hcard : Nat.card (U.subgroupOf M) = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (H := U) (K := M) hUHall.1).toEquiv
    have hqκσ :
        q ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) :=
      hUHall.2.p_in_pi_of_p_dvd_card q (by simpa [hcard] using hqU)
    exact fun hqσ => hqκσ (Or.inr hqσ)
  have hU_rank : groupRank U ≤ 2 :=
    section16_groupRank_U_le_two_of_section15 (G := G) hM hKU
  intro p P
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hPcomm : IsMulCommutative (P : Subgroup U) :=
    section12_sylow_abelian_of_sigma_compl_nilpotent_subgroup
      (G := G) (M := M) (K := U) (p := p.val)
      hM hKU.2.2.2.1.1 hUπ P
  exact ⟨hPcomm,
    (generatorRank_le_groupRank_of_isPGroup_abelian_subgroup
      (R := U) (q := p.val) (A := (P : Subgroup U)) P.isPGroup' hPcomm).trans
        hU_rank⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_hatMsigmaSet_le_generatedCentralizers
    (M U : Subgroup G) :
    ((U : Set G) ∩ section16HatMsigmaSet M) ⊆
      (section15GeneratedMsigmaCentralizers M U : Set G) := by
  classical
  intro u hu
  rcases hu with ⟨huU, huHat⟩
  rcases huHat with ⟨_huM, hcent_ne⟩
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hcent_ne with ⟨xC, hxCne⟩
  let x : G := xC
  have hxMsigma : x ∈ section10Msigma M := xC.property.1
  have hxne : x ≠ 1 := by
    intro hx
    exact hxCne (Subtype.ext hx)
  have hxcent_u : x ∈ Subgroup.centralizer ({u} : Set G) := xC.property.2
  have huCent : u ∈ elementCentralizerIn U x := by
    refine ⟨huU, ?_⟩
    change u ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz_eq : z = x := by simpa using hz
    subst z
    exact Subgroup.mem_centralizer_singleton_iff.mp hxcent_u
  exact Subgroup.subset_closure ⟨x, hxMsigma, hxne, huCent⟩

private theorem CFSG.section16_setCommutative_hatMsigma_of_section15
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    section16SetCommutative ((U : Set G) ∩ section16HatMsigmaSet M) := by
  classical
  have hcomm : IsMulCommutative (section15GeneratedMsigmaCentralizers M U) :=
    lemma_15_1_d hM hKU
  letI : IsMulCommutative (section15GeneratedMsigmaCentralizers M U) := hcomm
  intro x hx y hy
  exact setLike_mul_comm
    (s := section15GeneratedMsigmaCentralizers M U)
    (section16_hatMsigmaSet_le_generatedCentralizers (G := G) M U hx)
    (section16_hatMsigmaSet_le_generatedCentralizers (G := G) M U hy)

omit [IsMinCE G] in
private theorem CFSG.section16_elementCentralizerIn_eq_bot_of_frobeniusJoin
    {M R : Subgroup G}
    (hFrob : section12FrobeniusJoinWithKernel (section10Msigma M) R) :
    ∀ r : G, r ∈ R → r ≠ 1 →
      elementCentralizerIn (section10Msigma M) r = ⊥ := by
  classical
  let K : Subgroup G := section10Msigma M
  let S : Subgroup G := K ⊔ R
  let Ksub : Subgroup S := K.subgroupOf S
  let Rsub : Subgroup S := R.subgroupOf S
  have hFrob' : IsFrobeniusGroupWithKernelComplement Ksub Rsub := by
    simpa [section12FrobeniusJoinWithKernel, K, S, Ksub, Rsub] using hFrob
  have hcent_local :
      ∀ x : Rsub, x ≠ 1 → elementCentralizerIn Ksub (x : S) = ⊥ :=
    (lemma_3_1 (G := S) Ksub Rsub hFrob'.kernel_ne_bot hFrob'.complement_ne_bot
      hFrob'.normal hFrob'.isComplement').1 hFrob'
  intro r hrR hrne
  apply le_antisymm ?_ bot_le
  intro y hy
  by_contra hyne
  have hrS : r ∈ S := Subgroup.mem_sup_right hrR
  let rS : S := ⟨r, hrS⟩
  have hrRsub : rS ∈ Rsub := by
    simpa [Rsub, Subgroup.mem_subgroupOf, rS] using hrR
  let rRsub : Rsub := ⟨rS, hrRsub⟩
  have hrRsub_ne : rRsub ≠ 1 := by
    intro h
    exact hrne (by
      simpa [rRsub, rS] using congrArg (fun z : Rsub => ((z : S) : G)) h)
  have hyK : y ∈ K := hy.1
  have hyS : y ∈ S := Subgroup.mem_sup_left hyK
  let yS : S := ⟨y, hyS⟩
  have hyKsub : yS ∈ Ksub := by
    simpa [Ksub, Subgroup.mem_subgroupOf, yS] using hyK
  have hyCentS : yS ∈ Subgroup.centralizer ({(rRsub : S)} : Set S) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hy.2
  have hyLocal : yS ∈ elementCentralizerIn Ksub (rRsub : S) :=
    ⟨hyKsub, hyCentS⟩
  have hybot : yS ∈ (⊥ : Subgroup S) := by
    simpa [hcent_local rRsub hrRsub_ne] using hyLocal
  have hyS_one : yS = 1 := by simpa using hybot
  have hy_one_in_G : (yS : G) = 1 :=
    congrArg (fun z : S => (z : G)) hyS_one
  have hy_one : y = 1 := by simpa [yS] using hy_one_in_G
  exact hyne hy_one

private theorem CFSG.section16_sameExponent_disjoint_hatMsigma_of_section15
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    ∃ U0 : Subgroup G, U0 ≤ U ∧ Monoid.exponent U0 = Monoid.exponent U ∧
      (U0 : Set G) ∩ section16HatMsigmaSet M = ({1} : Set G) := by
  classical
  by_cases hUne : U ≠ ⊥
  · rcases lemma_15_1_e_join hM hKU hUne with
      ⟨U0, hU0U, hexp, hFrob⟩
    refine ⟨U0, hU0U, hexp, ?_⟩
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxU0, hxHat⟩
      by_cases hxone : x = 1
      · simp [hxone]
      · have hcent_bot :
            elementCentralizerIn (section10Msigma M) x = ⊥ :=
          section16_elementCentralizerIn_eq_bot_of_frobeniusJoin
            (G := G) (M := M) (R := U0) hFrob x hxU0 hxone
        exact False.elim (hxHat.2 hcent_bot)
    · intro hx
      have hxone : x = 1 := by simpa using hx
      subst x
      exact ⟨U0.one_mem, section16_one_mem_hatMsigmaSet (G := G) hM⟩
  · have hUbot : U = ⊥ := by
      by_contra hUbot
      exact hUne hUbot
    subst U
    refine ⟨⊥, by simp, rfl,
      section16_bot_inter_hatMsigmaSet_eq_singleton (G := G) hM⟩

private theorem CFSG.section16_centralizer_unique_of_section15
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    ∀ X : Subgroup G, X ≤ U → X ≠ ⊥ →
      subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ →
        section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  intro X hXU hXne hcent
  exact (lemma_15_1_c (M := M) (K := K) (U := U) (X := X)
    hM hKU hXU hXne hcent).1

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_centralizer_zpowers_eq_singleton
    (u : G) :
    Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) =
      Subgroup.centralizer ({u} : Set G) := by
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hy u (Subgroup.mem_zpowers u)).symm
  · intro hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    have hcomm : Commute y u :=
      Subgroup.mem_centralizer_singleton_iff.mp hy
    exact (hcomm.zpow_right n).eq.symm

private theorem CFSG.section16_centralizer_unique_of_U_hat_element
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    {u : G} (huU : u ∈ U) (huHat : u ∈ section16HatMsigmaSet M)
    (hune : u ≠ 1) :
    section9MaximalSubgroupsContaining
      (Subgroup.centralizer ({u} : Set G)) = {M} := by
  classical
  have hXU : Subgroup.zpowers u ≤ U := Subgroup.zpowers_le.2 huU
  have hXne : Subgroup.zpowers u ≠ (⊥ : Subgroup G) := by
    intro hbot
    have hu_bot : u ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using (Subgroup.mem_zpowers u)
    exact hune (by simpa using hu_bot)
  have hcent :
      subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers u) ≠ ⊥ := by
    rcases huHat with ⟨_huM, hcent_u⟩
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hcent_u with ⟨yC, hyCne⟩
    let y : G := yC
    have hySub :
        y ∈ subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers u) := by
      refine ⟨yC.property.1, ?_⟩
      change y ∈ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
      have hcomm : Commute y u :=
        Subgroup.mem_centralizer_singleton_iff.mp yC.property.2
      exact (hcomm.zpow_right n).eq.symm
    let ySub : subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers u) :=
      ⟨y, hySub⟩
    exact Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨ySub, by
      intro hySub_one
      exact hyCne (Subtype.ext (by
        simpa [ySub, y] using congrArg Subtype.val hySub_one))⟩
  have huniq :=
    section16_centralizer_unique_of_section15 (G := G) (M := M) (K := K) (U := U)
      hM hKU (Subgroup.zpowers u) hXU hXne hcent
  simpa [section16_centralizer_zpowers_eq_singleton (G := G) u] using huniq

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_centralizer_singleton_conjBy_eq
    (u m : G) :
    (Subgroup.centralizer ({u} : Set G)).conjBy m =
      Subgroup.centralizer ({m * u * m⁻¹} : Set G) := by
  ext y
  constructor
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    simpa [MulAut.conj_apply, mul_assoc] using
      congrArg (fun t : G => m * t * m⁻¹) hz
  · intro hy
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨m⁻¹ * y * m, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      have h := congrArg (fun t : G => m⁻¹ * t * m) hy
      simpa [mul_assoc] using h
    · simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_maximalSubgroupsContaining_centralizer_singleton_conj
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    {u m : G} (hm : m ∈ M)
    (huniq :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer ({u} : Set G)) = {M}) :
    section9MaximalSubgroupsContaining
      (Subgroup.centralizer ({m * u * m⁻¹} : Set G)) = {M} := by
  classical
  ext H
  constructor
  · intro hH
    have hHinv :
        H.conjBy m⁻¹ ∈
          section9MaximalSubgroupsContaining
            (Subgroup.centralizer ({u} : Set G)) := by
      refine ⟨section10_maximal_conjBy (G := G) hH.1 m⁻¹, ?_⟩
      intro c hc
      have hconj :
          m * c * m⁻¹ ∈
            Subgroup.centralizer ({m * u * m⁻¹} : Set G) := by
        have hmap :
            m * c * m⁻¹ ∈
              (Subgroup.centralizer ({u} : Set G)).conjBy m :=
          Subgroup.mem_map.mpr ⟨c, hc, by simp [MulAut.conj_apply, mul_assoc]⟩
        simpa [section16_centralizer_singleton_conjBy_eq (G := G) u m] using hmap
      exact Subgroup.mem_map.mpr ⟨m * c * m⁻¹, hH.2 hconj, by
        simp [mul_assoc]⟩
    have hHinv_eq : H.conjBy m⁻¹ = M := by
      have hsingle : H.conjBy m⁻¹ ∈ ({M} : Set (Subgroup G)) := by
        simpa [huniq] using hHinv
      simpa using hsingle
    have hH_eq : H = M := by
      calc
        H = (H.conjBy m⁻¹).conjBy m := by
          simpa using (section11_conjBy_inv' (G := G) H m).symm
        _ = M.conjBy m := by rw [hHinv_eq]
        _ = M := section11_conjBy_eq_of_mem_normalizer
          (H := M) (Subgroup.le_normalizer hm)
    simp [hH_eq]
  · intro hHsingle
    have hH_eq : H = M := by simpa using hHsingle
    subst H
    have hMcont :
        M ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({u} : Set G)) := by
      simp [huniq]
    refine ⟨hM, ?_⟩
    intro c hc
    have hback :
        m⁻¹ * c * m ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      have h := congrArg (fun t : G => m⁻¹ * t * m) hc
      simpa [mul_assoc] using h
    have hbackM : m⁻¹ * c * m ∈ M := hMcont.2 hback
    have hc_eq : c = m * (m⁻¹ * c * m) * m⁻¹ := by group
    rw [hc_eq]
    exact M.mul_mem (M.mul_mem hm hbackM) (M.inv_mem hm)

public theorem CFSG.section16_centralizer_unique_of_conj_U_hat_element
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    {a u m : G} (hm : m ∈ M) (huU : u ∈ U)
    (huHat : u ∈ section16HatMsigmaSet M) (hune : u ≠ 1)
    (ha : a = m * u * m⁻¹) :
    section9MaximalSubgroupsContaining
      (Subgroup.centralizer ({a} : Set G)) = {M} := by
  subst a
  exact section16_maximalSubgroupsContaining_centralizer_singleton_conj
    (G := G) (M := M) hM hm
    (section16_centralizer_unique_of_U_hat_element
      (G := G) (M := M) (K := K) (U := U) hM hKU huU huHat hune)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_coprime_card_of_isPiSubgroup_disjoint_primes
    {π ρ : Set Nat.Primes} {A B : Subgroup G}
    (hA : IsPiSubgroup π A) (hB : IsPiSubgroup ρ B)
    (hπρ : Disjoint π ρ) :
    Nat.Coprime (Nat.card A) (Nat.card B) := by
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hqA hqB
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hqπ : q' ∈ π := hA q' hqA
  have hqρ : q' ∈ ρ := hB q' hqB
  exact (Set.disjoint_left.mp hπρ hqπ) hqρ

omit [Group G] [Finite G] [IsMinCE G] in
public theorem CFSG.section16_section2_mem_elementCentralizer_commute
    {L : Type*} [Group L] {g c : L}
    (hc : c ∈ Section2.elementCentralizer g) :
    g * c = c * g := by
  unfold Section2.elementCentralizer at hc
  rw [Subgroup.mem_centralizer_iff] at hc
  exact hc g (by simp)

omit [Group G] [Finite G] [IsMinCE G] in
private theorem CFSG.section16_section2_normalizesSet_subgroup_of_normal
    {L : Type*} [Group L]
    (K : Subgroup L) [K.Normal] (g : L) :
    Section2.normalizesSet (K : Set L) g := by
  intro x
  constructor
  · intro hx
    have hx' : g⁻¹ * (g * x * g⁻¹) * g ∈ K := by
      simpa [mul_assoc] using
        (show K.Normal from inferInstance).conj_mem (g * x * g⁻¹) hx g⁻¹
    simpa [Section2.conjBy, mul_assoc] using hx'
  · intro hx
    simpa [Section2.conjBy] using
      (show K.Normal from inferInstance).conj_mem x hx g

omit [Group G] [Finite G] [IsMinCE G] in
private theorem CFSG.section16_exists_multiple_card_pow_eq_self
    {L : Type*} [Group L] [Finite L]
    (K : Subgroup L) (g : L)
    (hcop : Nat.Coprime (orderOf g) (Nat.card K)) :
    ∃ n : ℕ, Nat.card K ∣ n ∧ g ^ n = g := by
  rcases exists_pow_eq_self_of_coprime (x := g) (n := Nat.card K) hcop.symm with
    ⟨m, hm⟩
  refine ⟨Nat.card K * m, ⟨m, rfl⟩, ?_⟩
  simpa [pow_mul] using hm

omit [Group G] [Finite G] [IsMinCE G] in
public theorem CFSG.section16_exists_centralizer_coset_conj_of_coprime
    {L : Type*} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L)
    (hcop : Nat.Coprime (orderOf g) (Nat.card K))
    (y : K) :
    ∃ r u : K,
      (u : L) ∈ Section2.centralizerIn K g ∧
        (u : L) * g = (r : L)⁻¹ * ((y : L) * g) * (r : L) := by
  classical
  rcases Section2.proposition_2_1 g K
      (section16_section2_normalizesSet_subgroup_of_normal K g) hcop with
    ⟨reps, _hcard, hreps, _hdisj, hcover⟩
  have hygCoset : (y : L) * g ∈ Section2.subgroupCosetByElement K g := by
    exact ⟨(y : L), y.2, rfl⟩
  have hygPiece :
      (y : L) * g ∈ {z | ∃ r ∈ reps, z ∈ Section2.conjugateCosetPiece K g r} := by
    simpa [hcover] using hygCoset
  rcases hygPiece with ⟨r, hr, hpiece⟩
  have hrK : r ∈ K := hreps r hr
  rcases hpiece with ⟨s, hs, hsEq⟩
  rcases hs with ⟨u, huCent, rfl⟩
  have huK : u ∈ K := (Subgroup.mem_inf.mp huCent).1
  refine ⟨⟨r, hrK⟩, ⟨u, huK⟩, huCent, ?_⟩
  simpa [Section2.conjBy, mul_assoc] using
    congrArg (fun t : L => r⁻¹ * t * r) hsEq.symm

omit [Group G] [Finite G] [IsMinCE G] in
private theorem CFSG.section16_exists_conj_mem_centralizer_of_coprime_conj
    {L : Type*} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L)
    (hcop : Nat.Coprime (orderOf g) (Nat.card K))
    {x y : K}
    (hyx : (y : L) * (g * (x : L) * g⁻¹) * (y : L)⁻¹ = (x : L)) :
    ∃ z : K, IsConj z x ∧ (z : L) ∈ Section2.centralizerIn K g := by
  classical
  have hygx_conj : ((y : L) * g) * (x : L) * (((y : L) * g)⁻¹) = (x : L) := by
    simpa [mul_assoc] using hyx
  have hygx_comm : ((y : L) * g) * (x : L) = (x : L) * ((y : L) * g) := by
    calc
      ((y : L) * g) * (x : L) =
          ((((y : L) * g) * (x : L) * (((y : L) * g)⁻¹)) * ((y : L) * g)) := by
            simp [mul_assoc]
      _ = (x : L) * ((y : L) * g) := by rw [hygx_conj]
  rcases Section2.proposition_2_1 g K
      (section16_section2_normalizesSet_subgroup_of_normal K g) hcop with
    ⟨reps, _hcard, hreps, _hdisj, hcover⟩
  have hygCoset : (y : L) * g ∈ Section2.subgroupCosetByElement K g := by
    exact ⟨(y : L), y.2, rfl⟩
  have hygPiece :
      (y : L) * g ∈ {z | ∃ r ∈ reps, z ∈ Section2.conjugateCosetPiece K g r} := by
    simpa [hcover] using hygCoset
  rcases hygPiece with ⟨r, hr, hpiece⟩
  have hrK : r ∈ K := hreps r hr
  rcases hpiece with ⟨s, hs, hsEq⟩
  rcases hs with ⟨u, huCent, rfl⟩
  have hugEq : u * g = r⁻¹ * ((y : L) * g) * r := by
    simpa [Section2.conjBy, mul_assoc] using
      congrArg (fun t : L => r⁻¹ * t * r) hsEq.symm
  let xr : K := ⟨r⁻¹ * (x : L) * r, by
    simpa [mul_assoc] using
      (show K.Normal from inferInstance).conj_mem (x : L) x.2 r⁻¹⟩
  have hxr_conj : IsConj xr x := by
    rw [isConj_iff]
    refine ⟨⟨r, hrK⟩, ?_⟩
    apply Subtype.ext
    simp [xr, mul_assoc]
  have hxr_comm_ug : Commute (xr : L) (u * g) := by
    change (xr : L) * (u * g) = (u * g) * (xr : L)
    calc
      (xr : L) * (u * g)
          = (r⁻¹ * (x : L) * r) * (r⁻¹ * ((y : L) * g) * r) := by
              rw [hugEq]
      _ = r⁻¹ * ((x : L) * ((y : L) * g)) * r := by simp [mul_assoc]
      _ = r⁻¹ * (((y : L) * g) * (x : L)) * r := by rw [hygx_comm]
      _ = (r⁻¹ * ((y : L) * g) * r) * (r⁻¹ * (x : L) * r) := by simp [mul_assoc]
      _ = (u * g) * (xr : L) := by rw [← hugEq]
  rcases section16_exists_multiple_card_pow_eq_self K g hcop with ⟨n, hnK, hgn⟩
  have huK : u ∈ K := (Subgroup.mem_inf.mp huCent).1
  have huPow : u ^ n = 1 := by
    rcases hnK with ⟨m, rfl⟩
    have hu_sub : (⟨u, huK⟩ : K) ^ Nat.card K = 1 := pow_card_eq_one'
    have hu_card : u ^ Nat.card K = 1 := by
      exact Subtype.ext_iff.mp hu_sub
    rw [pow_mul, hu_card, one_pow]
  have huComm : Commute u g := by
    change u * g = g * u
    exact (section16_section2_mem_elementCentralizer_commute
      ((Subgroup.mem_inf.mp huCent).2)).symm
  have hugPow : (u * g) ^ n = g := by
    calc
      (u * g) ^ n = u ^ n * g ^ n := huComm.mul_pow n
      _ = 1 * g := by rw [huPow, hgn]
      _ = g := by simp
  have hxr_comm_g : Commute (xr : L) g := by
    simpa [hugPow] using hxr_comm_ug.pow_right n
  refine ⟨xr, hxr_conj, ?_⟩
  refine Subgroup.mem_inf.mpr ⟨xr.2, ?_⟩
  unfold Section2.elementCentralizer
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  exact hxr_comm_g.symm.eq

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_ASet_diff_msigma_product_decomp
    {M U : Subgroup G}
    {a : G}
    (ha : a ∈ section16ASet M U \ (section10Msigma M : Set G)) :
    ∃ u s : G,
      u ∈ U ∧ s ∈ section10Msigma M ∧ u ≠ 1 ∧ a = u * s := by
  classical
  rcases ha with ⟨haA, haNotSigma⟩
  rcases haA with ⟨_haHat, haProd, _hane⟩
  rcases Set.mem_mul.mp haProd with ⟨u, huU, s, hsSigma, hua⟩
  refine ⟨u, s, huU, hsSigma, ?_, hua.symm⟩
  intro hu_one
  exact haNotSigma (by
    rw [← hua, hu_one]
    simpa using hsSigma)

private theorem CFSG.section16_ASet_diff_msigma_u_mem_hat
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    {a u s : G}
    (ha : a ∈ section16ASet M U \ (section10Msigma M : Set G))
    (huU : u ∈ U) (hsSigma : s ∈ section10Msigma M)
    (ha_eq : a = u * s) :
    u ∈ section16HatMsigmaSet M := by
  classical
  have huM : u ∈ M := hKU.2.2.2.1.1 huU
  have hsM : s ∈ M := section16_msigma_le (G := G) M hsSigma
  rcases ha.1.1 with ⟨_haM, hcent_ne⟩
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hcent_ne with ⟨xC, hxCne⟩
  let x : G := xC
  have hxSigma : x ∈ section10Msigma M := xC.property.1
  have hxne : x ≠ 1 := by
    intro hx
    exact hxCne (Subtype.ext hx)
  have hxcent_a : x ∈ Subgroup.centralizer ({a} : Set G) := xC.property.2
  have hxM : x ∈ M := section16_msigma_le (G := G) M hxSigma
  let uM : M := ⟨u, huM⟩
  let sM : M := ⟨s, hsM⟩
  let xM : M := ⟨x, hxM⟩
  let Sσ : Subgroup M := section10MsigmaSubgroup M
  have hsSσ : sM ∈ Sσ := by
    have hsSub : sM ∈ (section10Msigma M).subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf, sM] using hsSigma
    simpa [Sσ, section16_msigma_subgroupOf_eq (M := M)] using hsSub
  have hxSσ : xM ∈ Sσ := by
    have hxSub : xM ∈ (section10Msigma M).subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf, xM] using hxSigma
    simpa [Sσ, section16_msigma_subgroupOf_eq (M := M)] using hxSub
  let sσ : Sσ := ⟨sM, hsSσ⟩
  let xσ : Sσ := ⟨xM, hxSσ⟩
  let x0σ : Sσ := sσ * xσ * sσ⁻¹
  have hUπ :
      IsPiSubgroup ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ)
        (U.subgroupOf M) := by
    rcases hKU.2.2.2.1 with ⟨hUM, hUHall⟩
    intro p hp
    exact hUHall.p_in_pi_of_p_dvd_card p hp
  have hSσπ : IsPiSubgroup (section10SigmaPrimes M) Sσ := by
    intro p hp
    exact (theorem_10_2_b (G := G) hM).2.p_in_pi_of_p_dvd_card p hp
  have hπdisj :
      Disjoint ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ)
        (section10SigmaPrimes M) := by
    rw [Set.disjoint_left]
    intro p hpcomp hpσ
    exact hpcomp (Or.inr hpσ)
  have hcopUS :
      Nat.Coprime (Nat.card (U.subgroupOf M)) (Nat.card Sσ) :=
    section16_coprime_card_of_isPiSubgroup_disjoint_primes hUπ hSσπ hπdisj
  have huUsub : uM ∈ U.subgroupOf M := by
    simpa [Subgroup.mem_subgroupOf, uM] using huU
  have hcop_uS : Nat.Coprime (orderOf uM) (Nat.card Sσ) :=
    Nat.Coprime.of_dvd_left
      (Subgroup.orderOf_dvd_natCard (U.subgroupOf M) huUsub) hcopUS
  have hconjG : u * (s * x * s⁻¹) * u⁻¹ = x := by
    have hcomm : Commute x a :=
      Subgroup.mem_centralizer_singleton_iff.mp hxcent_a
    calc
      u * (s * x * s⁻¹) * u⁻¹ = (u * s) * x * (u * s)⁻¹ := by group
      _ = a * x * a⁻¹ := by rw [← ha_eq]
      _ = x * a * a⁻¹ := by rw [← hcomm.eq]
      _ = x := by group
  have hconjM : uM * (sM * xM * sM⁻¹) * uM⁻¹ = xM := by
    apply Subtype.ext
    simpa [uM, sM, xM, mul_assoc] using hconjG
  have hfixedClass :
      (sσ : M) * (uM * (x0σ : M) * uM⁻¹) * (sσ : M)⁻¹ = (x0σ : M) := by
    change sM * (uM * (sM * xM * sM⁻¹) * uM⁻¹) * sM⁻¹ =
      sM * xM * sM⁻¹
    rw [hconjM]
  have hxσ_ne : xσ ≠ 1 := by
    intro hxσ_one
    exact hxne (by
      simpa [xσ, xM] using congrArg (fun z : Sσ => ((z : M) : G)) hxσ_one)
  have hx0σ_ne : x0σ ≠ 1 := by
    intro hx0_one
    apply hxσ_ne
    calc
      xσ = sσ⁻¹ * x0σ * sσ := by
        simp [x0σ, mul_assoc]
      _ = 1 := by rw [hx0_one]; simp
  haveI : Sσ.Normal := by
    simpa [Sσ] using (section10MsigmaSubgroup_normal (M := M))
  rcases section16_exists_conj_mem_centralizer_of_coprime_conj
      (K := Sσ) (g := uM) hcop_uS (x := x0σ) (y := sσ) hfixedClass with
    ⟨zσ, hzConj, hzCent⟩
  have hzσ_ne : zσ ≠ 1 := by
    intro hz_one
    rcases isConj_iff.mp hzConj with ⟨c, hc⟩
    exact hx0σ_ne (by simpa [hz_one] using hc.symm)
  refine ⟨huM, ?_⟩
  apply Subgroup.ne_bot_iff_exists_ne_one.mpr
  have hzSigmaG : ((zσ : M) : G) ∈ section10Msigma M := by
    change ((zσ : M) : G) ∈ (section10MsigmaSubgroup M).map M.subtype
    exact Subgroup.mem_map.mpr ⟨(zσ : M), by simp [Sσ], rfl⟩
  have hzCentM : (zσ : M) ∈ Subgroup.centralizer ({uM} : Set M) := by
    have hz := (Subgroup.mem_inf.mp hzCent).2
    simpa [Section2.elementCentralizer] using hz
  have hzCentG : ((zσ : M) : G) ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcommM : Commute (zσ : M) uM :=
      Subgroup.mem_centralizer_singleton_iff.mp hzCentM
    simpa [uM] using congrArg (fun t : M => (t : G)) hcommM.eq
  let zC : elementCentralizerIn (section10Msigma M) u :=
    ⟨((zσ : M) : G), ⟨hzSigmaG, hzCentG⟩⟩
  refine ⟨zC, ?_⟩
  intro hzC_one
  apply hzσ_ne
  apply Subtype.ext
  have hzG_one : ((zσ : M) : G) = 1 := by
    simpa [zC] using congrArg Subtype.val hzC_one
  exact Subtype.ext hzG_one

public theorem CFSG.section16_ASet_diff_msigma_conj_U_hat_of_coprime
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    {a : G}
    (ha : a ∈ section16ASet M U \ (section10Msigma M : Set G))
    (hcop : Nat.Coprime (orderOf a) (Nat.card (section10Msigma M))) :
    ∃ u m : G,
      u ∈ U ∧ u ∈ section16HatMsigmaSet M ∧ u ≠ 1 ∧ m ∈ M ∧
        a = m * u * m⁻¹ := by
  classical
  rcases section16_ASet_diff_msigma_product_decomp (G := G) ha with
    ⟨u, s, huU, hsSigma, hu_ne, ha_eq⟩
  have huHat : u ∈ section16HatMsigmaSet M :=
    section16_ASet_diff_msigma_u_mem_hat
      (G := G) (M := M) (K := K) (U := U) hM hKU ha huU hsSigma ha_eq
  let Sσ : Subgroup M := section10MsigmaSubgroup M
  haveI : Sσ.Normal := by
    simpa [Sσ] using (section10MsigmaSubgroup_normal (M := M))
  have huM : u ∈ M := hKU.2.2.2.1.1 huU
  have hsM : s ∈ M := section16_msigma_le (G := G) M hsSigma
  have haM : a ∈ M := by
    rw [ha_eq]
    exact M.mul_mem huM hsM
  let uM : M := ⟨u, huM⟩
  let sM : M := ⟨s, hsM⟩
  let aM : M := ⟨a, haM⟩
  have hsSσ : sM ∈ Sσ := by
    have hsSub : sM ∈ (section10Msigma M).subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf, sM] using hsSigma
    simpa [Sσ, section16_msigma_subgroupOf_eq (M := M)] using hsSub
  have hUπ :
      IsPiSubgroup ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ)
        (U.subgroupOf M) := by
    rcases hKU.2.2.2.1 with ⟨hUM, hUHall⟩
    intro p hp
    exact hUHall.p_in_pi_of_p_dvd_card p hp
  have hSσπ : IsPiSubgroup (section10SigmaPrimes M) Sσ := by
    intro p hp
    exact (theorem_10_2_b (G := G) hM).2.p_in_pi_of_p_dvd_card p hp
  have hπdisj :
      Disjoint ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ)
        (section10SigmaPrimes M) := by
    rw [Set.disjoint_left]
    intro p hpcomp hpσ
    exact hpcomp (Or.inr hpσ)
  have hcopUS :
      Nat.Coprime (Nat.card (U.subgroupOf M)) (Nat.card Sσ) :=
    section16_coprime_card_of_isPiSubgroup_disjoint_primes hUπ hSσπ hπdisj
  have huUsub : uM ∈ U.subgroupOf M := by
    simpa [Subgroup.mem_subgroupOf, uM] using huU
  have hcop_uS : Nat.Coprime (orderOf uM) (Nat.card Sσ) :=
    Nat.Coprime.of_dvd_left
      (Subgroup.orderOf_dvd_natCard (U.subgroupOf M) huUsub) hcopUS
  let yM : M := uM * sM * uM⁻¹
  have hySσ : yM ∈ Sσ := by
    have huNormSigma : u ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
      section12_le_normalizer_msigma (M := M) huM
    have hsConj : u * s * u⁻¹ ∈ section10Msigma M :=
      (Subgroup.mem_normalizer_iff.mp huNormSigma s).1 hsSigma
    have hsSub : yM ∈ (section10Msigma M).subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf, yM, uM, sM, mul_assoc] using hsConj
    simpa [Sσ, section16_msigma_subgroupOf_eq (M := M)] using hsSub
  have haM_eq_yu : aM = yM * uM := by
    apply Subtype.ext
    simp [aM, yM, uM, sM, ha_eq, mul_assoc]
  rcases section16_exists_centralizer_coset_conj_of_coprime
      (K := Sσ) (g := uM) hcop_uS ⟨yM, hySσ⟩ with
    ⟨rσ, vσ, hvCent, hvu_eq⟩
  let rM : M := rσ
  let vM : M := vσ
  have hvSσ : vM ∈ Sσ := vσ.property
  have hvComm : Commute vM uM := by
    have hv := (Subgroup.mem_inf.mp hvCent).2
    change vM * uM = uM * vM
    exact (section16_section2_mem_elementCentralizer_commute hv).symm
  have hv_order_dvd_Sσ : orderOf vM ∣ Nat.card Sσ :=
    Subgroup.orderOf_dvd_natCard Sσ hvSσ
  have hcop_uv : Nat.Coprime (orderOf uM) (orderOf vM) :=
    hcop_uS.coprime_dvd_right hv_order_dvd_Sσ
  have hv_zpow_vu : vM ∈ Subgroup.zpowers (vM * uM) :=
    by
      have hupow : uM ^ orderOf uM = 1 := pow_orderOf_eq_one uM
      have hpow : (vM * uM) ^ orderOf uM = vM ^ orderOf uM := by
        rw [hvComm.mul_pow, hupow, mul_one]
      have hvmem : vM ∈ Subgroup.zpowers (vM ^ orderOf uM) := by
        rw [mem_zpowers_pow_iff]
        simpa [Nat.gcd_comm] using hcop_uv.symm.gcd_eq_one
      rcases hvmem with ⟨n, hn⟩
      refine ⟨(orderOf uM : ℤ) * n, ?_⟩
      calc
        (vM * uM) ^ ((orderOf uM : ℤ) * n) =
            ((vM * uM) ^ (orderOf uM : ℤ)) ^ n := by
              rw [zpow_mul]
        _ = ((vM * uM) ^ orderOf uM) ^ n := by
              rw [zpow_natCast]
        _ = (vM ^ orderOf uM) ^ n := by
              rw [hpow]
        _ = vM := by
              simpa using hn
  have horder_vu_eq_a : orderOf (vM * uM) = orderOf a := by
    have hconj_order :
        orderOf ((rM : M)⁻¹ * aM * (rM : M)) = orderOf aM := by
      simpa [MulAut.conj_apply] using (MulAut.conj (rM : M)⁻¹).orderOf_eq aM
    have hvu_eq' : vM * uM = (rM : M)⁻¹ * aM * (rM : M) := by
      calc
        vM * uM = (rM : M)⁻¹ * (yM * uM) * (rM : M) := hvu_eq
        _ = (rM : M)⁻¹ * aM * (rM : M) := by rw [← haM_eq_yu]
    calc
      orderOf (vM * uM) =
          orderOf ((rM : M)⁻¹ * aM * (rM : M)) := by rw [hvu_eq']
      _ = orderOf aM := hconj_order
      _ = orderOf a := by simp [aM]
  have hcardSσ_eq :
      Nat.card Sσ = Nat.card (section10Msigma M) := by
    calc
      Nat.card Sσ = Nat.card ((section10Msigma M).subgroupOf M) := by
        simp [Sσ, section16_msigma_subgroupOf_eq (M := M)]
      _ = Nat.card (section10Msigma M) :=
        section12_card_subgroupOf_eq (section16_msigma_le (G := G) M)
  have hcop_vu_Sσ : Nat.Coprime (orderOf (vM * uM)) (Nat.card Sσ) := by
    simpa [horder_vu_eq_a, hcardSσ_eq] using hcop
  have hv_order_dvd_vu : orderOf vM ∣ orderOf (vM * uM) :=
    orderOf_dvd_of_mem_zpowers hv_zpow_vu
  have hv_order_one : orderOf vM = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_vu_Sσ hv_order_dvd_vu hv_order_dvd_Sσ
  have hv_one : vM = 1 := orderOf_eq_one_iff.mp hv_order_one
  refine ⟨u, rM, huU, huHat, hu_ne, rM.property, ?_⟩
  have hu_eq_conj : (uM : M) = (rM : M)⁻¹ * aM * (rM : M) := by
    calc
      (uM : M) = vM * uM := by rw [hv_one, one_mul]
      _ = (rM : M)⁻¹ * (yM * uM) * (rM : M) := hvu_eq
      _ = (rM : M)⁻¹ * aM * (rM : M) := by rw [← haM_eq_yu]
  have ha_eq_conj : aM = (rM : M) * uM * (rM : M)⁻¹ := by
    have h := congrArg (fun t : M => (rM : M) * t * (rM : M)⁻¹) hu_eq_conj
    simpa [mul_assoc] using h.symm
  simpa [aM, uM, mul_assoc] using congrArg Subtype.val ha_eq_conj

public theorem CFSG.section16_ASet_diff_msigma_exists_prime_compl_zpow
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    {a : G}
    (ha : a ∈ section16ASet M U \ (section10Msigma M : Set G)) :
    ∃ n : ℤ, ∃ q : Nat.Primes,
      orderOf (a ^ n) = q.val ∧
        q ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) := by
  classical
  rcases section16_ASet_diff_msigma_product_decomp (G := G) ha with
    ⟨u, s, huU, hsSigma, hu_ne, ha_eq⟩
  let Sσ : Subgroup M := section10MsigmaSubgroup M
  haveI : Sσ.Normal := by
    simpa [Sσ] using (section10MsigmaSubgroup_normal (M := M))
  let qM : M →* M ⧸ Sσ := QuotientGroup.mk' Sσ
  have haM : a ∈ M := ha.1.1.1
  have huM : u ∈ M := hKU.2.2.2.1.1 huU
  have hsM : s ∈ M := section16_msigma_le (G := G) M hsSigma
  let aM : M := ⟨a, haM⟩
  let uM : M := ⟨u, huM⟩
  let sM : M := ⟨s, hsM⟩
  have hsSσ : sM ∈ Sσ := by
    have hsSub : sM ∈ (section10Msigma M).subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf, sM] using hsSigma
    simpa [Sσ, section16_msigma_subgroupOf_eq (M := M)] using hsSub
  have haM_eq : aM = uM * sM := by
    apply Subtype.ext
    simpa [aM, uM, sM] using ha_eq
  have hq_s : qM sM = 1 := by
    exact (QuotientGroup.eq_one_iff (N := Sσ) sM).2 hsSσ
  have hq_a_eq_u : qM aM = qM uM := by
    rw [haM_eq, map_mul, hq_s, mul_one]
  have hu_not_kernel : qM uM ≠ 1 := by
    intro huq
    have huSσ : uM ∈ Sσ :=
      (QuotientGroup.eq_one_iff (N := Sσ) uM).1 huq
    have huSigma : u ∈ section10Msigma M := by
      have huSub : uM ∈ (section10Msigma M).subgroupOf M := by
        simpa [Sσ, section16_msigma_subgroupOf_eq (M := M)] using huSσ
      simpa [Subgroup.mem_subgroupOf, uM] using huSub
    have huJoin : u ∈ K ⊔ section10Msigma M := Subgroup.mem_sup_right huSigma
    have hCompKMsigma :
        section12ComplementIn M (K ⊔ section10Msigma M) U :=
      section16_complement_k_msigma_of_KUData (G := G) hM hKU
    have huBot : u ∈ (⊥ : Subgroup G) :=
      Subgroup.disjoint_def.mp hCompKMsigma.2.2.2 huJoin huU
    exact hu_ne (by simpa using huBot)
  let A : Subgroup M := Subgroup.zpowers aM
  let Usub : Subgroup M := U.subgroupOf M
  have huUsub : uM ∈ Usub := by
    simpa [Usub, Subgroup.mem_subgroupOf, uM] using huU
  have hAmap_le_Umap : A.map qM ≤ Usub.map qM := by
    change (Subgroup.zpowers aM).map qM ≤ Usub.map qM
    rw [MonoidHom.map_zpowers, hq_a_eq_u]
    exact Subgroup.zpowers_le.2 (Subgroup.mem_map_of_mem qM huUsub)
  have hqa_mem : qM aM ∈ A.map qM :=
    Subgroup.mem_map_of_mem qM (Subgroup.mem_zpowers aM)
  have hAmap_ne : A.map qM ≠ ⊥ := by
    intro hbot
    have hqa_one : qM aM = 1 := by
      have hqa_bot : qM aM ∈ (⊥ : Subgroup (M ⧸ Sσ)) := by
        simpa [hbot] using hqa_mem
      simpa using hqa_bot
    exact hu_not_kernel (by simpa [hq_a_eq_u] using hqa_one)
  have hcard_ne_one : Nat.card (A.map qM) ≠ 1 := by
    intro hcard
    exact hAmap_ne ((Subgroup.eq_bot_iff_card (H := A.map qM)).2 hcard)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨q, hqprime, hqdivAmap⟩
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hqdivUmap : q ∣ Nat.card (Usub.map qM) :=
    hqdivAmap.trans (Subgroup.card_dvd_of_le hAmap_le_Umap)
  have hqdivUsub : q ∣ Nat.card Usub :=
    hqdivUmap.trans (Subgroup.card_map_dvd (H := Usub) qM)
  rcases hKU.2.2.2.1 with ⟨_hUM, hUHall⟩
  have hqcompl :
      q' ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) := by
    exact hUHall.p_in_pi_of_p_dvd_card q' (by simpa [q'] using hqdivUsub)
  have hqdivA : q ∣ Nat.card A :=
    hqdivAmap.trans (Subgroup.card_map_dvd (H := A) qM)
  haveI : Fact q.Prime := ⟨hqprime⟩
  rcases exists_prime_orderOf_dvd_card' (G := A) q hqdivA with ⟨zA, hzA_order⟩
  rcases Subgroup.mem_zpowers_iff.mp zA.property with ⟨n, hzA_eq⟩
  refine ⟨n, q', ?_, hqcompl⟩
  have hzG_eq : (((zA : A) : M) : G) = a ^ n := by
    have hzM_eq := congrArg (fun z : M => (z : G)) hzA_eq
    simpa [aM] using hzM_eq.symm
  have hz_order_M : orderOf ((zA : A) : M) = q := by
    simpa [Subgroup.orderOf_coe] using hzA_order
  have hz_order_G : orderOf (((zA : A) : M) : G) = q := by
    simpa [Subgroup.orderOf_coe] using hz_order_M
  simpa [q', ← hzG_eq] using hz_order_G

set_option linter.unusedVariables false in
public theorem CFSG.section16_ASet_diff_msigma_zpow_unique_centralizer
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    {a : G}
    (ha : a ∈ section16ASet M U \ (section10Msigma M : Set G))
    {n : ℤ} {q : Nat.Primes}
    (hzorder : orderOf (a ^ n) = q.val)
    (hqcompl : q ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ)) :
    section9MaximalSubgroupsContaining
      (Subgroup.centralizer ({a ^ n} : Set G)) = {M} := by
  classical
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
      simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers, hzorder] using hp
    have hp_eq : p = q := by
      apply Subtype.ext
      exact (Nat.prime_dvd_prime_iff_eq p.property q.property).1 hpdiv
    simpa [hp_eq] using hqcompl
  have hzsigma' : section14IsPiElement (section10SigmaPrimes M)ᶜ (a ^ n) := by
    intro p hp hpσ
    exact hzsupport_compl hp (Or.inr hpσ)
  rcases corollary_14_3 (G := G) (M := M) hM hxSigma hxne hz_ne hzcentIn hzsigma' with
    hκ | hτ
  · have hqSupp : q ∈ section14ElementPrimeSupport (a ^ n) := by
      simp [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers, hzorder]
    exact False.elim (hzsupport_compl hqSupp (Or.inl (hκ.1 hqSupp)))
  · exact hτ.2.2

public theorem CFSG.section16_ASet_diff_msigma_conj_mem_of_mem_M
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    {m a : G} (hm : m ∈ M)
    (ha : a ∈ section16ASet M U \ (section10Msigma M : Set G)) :
    m * a * m⁻¹ ∈ section16ASet M U \ (section10Msigma M : Set G) := by
  classical
  rcases ha with ⟨haA, haNotSigma⟩
  rcases haA with ⟨haHat, haProd, hane⟩
  rcases haHat with ⟨haM, hcent_ne⟩
  have hUHall := hKU.2.2.2.1
  have hmNormSigma : m ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    section12_le_normalizer_msigma (M := M) hm
  have hminvNormSigma :
      m⁻¹ ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    Subgroup.inv_mem _ hmNormSigma
  have hconjM : m * a * m⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem hm haM) (M.inv_mem hm)
  have hcent_conj_ne :
      elementCentralizerIn (section10Msigma M) (m * a * m⁻¹) ≠ ⊥ := by
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hcent_ne with ⟨yC, hyCne⟩
    let y : G := yC
    let z : G := m * y * m⁻¹
    have hySigma : y ∈ section10Msigma M := yC.property.1
    have hyCent : y ∈ Subgroup.centralizer ({a} : Set G) := yC.property.2
    have hzSigma : z ∈ section10Msigma M :=
      (Subgroup.mem_normalizer_iff.mp hmNormSigma y).1 hySigma
    have hzCent : z ∈ Subgroup.centralizer ({m * a * m⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hyCent ⊢
      calc
        z * (m * a * m⁻¹) = m * (y * a) * m⁻¹ := by
          simp [z, mul_assoc]
        _ = m * (a * y) * m⁻¹ := by rw [hyCent]
        _ = (m * a * m⁻¹) * z := by
          simp [z, mul_assoc]
    let zC : elementCentralizerIn (section10Msigma M) (m * a * m⁻¹) :=
      ⟨z, hzSigma, hzCent⟩
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨zC, ?_⟩
    intro hzC_one
    have hz_one : z = 1 := congrArg Subtype.val hzC_one
    have hy_one : y = 1 := by
      have h := congrArg (fun t : G => m⁻¹ * t * m) hz_one
      simpa [z, mul_assoc] using h
    exact hyCne (Subtype.ext hy_one)
  have hU_norm_sigma :
      U ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hUHall.1.trans (section12_le_normalizer_msigma (M := M))
  have hProd :
      (((U ⊔ section10Msigma M : Subgroup G) : Set G)) =
        (U : Set G) * (section10Msigma M : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right U (section10Msigma M) hU_norm_sigma
  have haJoin : a ∈ (U ⊔ section10Msigma M : Subgroup G) := by
    change a ∈ (((U ⊔ section10Msigma M : Subgroup G) : Set G))
    rw [hProd]
    exact haProd
  have hJoinNorm :
      M ≤ Subgroup.normalizer ((U ⊔ section10Msigma M : Subgroup G) : Set G) :=
    section10_normalIn_le_normalizer (lemma_15_1_a hM hKU).1
  have hconjJoin : m * a * m⁻¹ ∈ (U ⊔ section10Msigma M : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp (hJoinNorm hm) a).1 haJoin
  have hconjProd :
      m * a * m⁻¹ ∈ (U : Set G) * (section10Msigma M : Set G) := by
    have hconjJoinSet :
        m * a * m⁻¹ ∈ (((U ⊔ section10Msigma M : Subgroup G) : Set G)) :=
      hconjJoin
    exact hProd ▸ hconjJoinSet
  have hconjNotSigma : m * a * m⁻¹ ∉ section10Msigma M := by
    intro hconjSigma
    have haSigma : a ∈ section10Msigma M := by
      have hback :
          m⁻¹ * (m * a * m⁻¹) * (m⁻¹)⁻¹ ∈ section10Msigma M :=
        (Subgroup.mem_normalizer_iff.mp hminvNormSigma (m * a * m⁻¹)).1 hconjSigma
      simpa [mul_assoc] using hback
    exact haNotSigma haSigma
  have hconjne : m * a * m⁻¹ ≠ 1 := by
    intro h
    exact hane (by
      have h' := congrArg (fun t : G => m⁻¹ * t * m) h
      simpa [mul_assoc] using h')
  exact ⟨⟨⟨hconjM, hcent_conj_ne⟩, hconjProd, hconjne⟩, hconjNotSigma⟩

public theorem CFSG.section16_ASet_diff_msigma_le_normalizer_of_M
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    M ≤ Subgroup.normalizer
      (section16ASet M U \ (section10Msigma M : Set G)) := by
  intro m hm
  change ∀ a : G,
    a ∈ section16ASet M U \ (section10Msigma M : Set G) ↔
      m * a * m⁻¹ ∈ section16ASet M U \ (section10Msigma M : Set G)
  intro a
  constructor
  · exact section16_ASet_diff_msigma_conj_mem_of_mem_M
      (G := G) (M := M) (K := K) (U := U) hM hKU hm
  · intro hconj
    have hback :=
      section16_ASet_diff_msigma_conj_mem_of_mem_M
        (G := G) (M := M) (K := K) (U := U) hM hKU (M.inv_mem hm) hconj
    simpa [mul_assoc] using hback

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_mem_normalizer_of_conjBy_eq
    {H : Subgroup G} {g : G} (hg : H.conjBy g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g :=
      Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
    simpa [hg] using hx'
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by
      simpa [hg] using hx
    rcases Subgroup.mem_map.mp hx' with ⟨y, hy, hyx⟩
    have hxy : x = y := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (g * y * g⁻¹) * g := by
          rw [show g * x * g⁻¹ = g * y * g⁻¹ by
            simpa [MulAut.conj_apply] using hyx.symm]
        _ = y := by group
    simpa [hxy] using hy

public theorem CFSG.section16_maximal_normalizer_eq_self
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    Subgroup.normalizer (M : Set G) = M := by
  classical
  have hMsigma_ne : section10Msigma M ≠ ⊥ := theorem_10_2_e (G := G) hM
  have hMsigmaSub_ne : section10MsigmaSubgroup M ≠ ⊥ := by
    intro hbot
    exact hMsigma_ne (by simp [section10Msigma, hbot])
  have hnorm :=
    section10_normalizer_map_subtype_eq_of_maximal_of_normal_ne_bot
      (G := G) hM (N := section10MsigmaSubgroup M) hMsigmaSub_ne
  have hnormSigma :
      Subgroup.normalizer (section10Msigma M : Set G) = M := by
    simpa [section10Msigma] using hnorm
  apply le_antisymm
  · intro g hgNormM
    have hle :
        Subgroup.normalizer (M : Set G) ≤
          Subgroup.normalizer
            (((section10MsigmaSubgroup M : Subgroup M).map M.subtype : Subgroup G) : Set G) :=
      section9_normalizer_le_normalizer_map_subtype_of_characteristic
        (G := G) (H := M) (K := section10MsigmaSubgroup M)
    have hgNormSigma : g ∈ Subgroup.normalizer (section10Msigma M : Set G) := by
      simpa [section10Msigma] using hle hgNormM
    simpa [hnormSigma] using hgNormSigma
  · exact Subgroup.le_normalizer


private theorem CFSG.section16_ASet_diff_msigma_TI
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    section16TISubset (section16ASet M U \ (section10Msigma M : Set G)) := by
  classical
  let T : Set G := section16ASet M U \ (section10Msigma M : Set G)
  have hMnormT : M ≤ Subgroup.normalizer T :=
    section16_ASet_diff_msigma_le_normalizer_of_M (G := G) hM hKU
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
    intro x hx
    rcases hx with ⟨hxT, hxConj⟩
    rcases hxConj with ⟨y, hyT, hxy⟩
    by_contra hxne_one
    have hxne : x ≠ 1 := hxne_one
    have hyne : y ≠ 1 := by
      intro hy
      exact hxne (by simpa [hy] using hxy)
    rcases section16_ASet_diff_msigma_exists_prime_compl_zpow
        (G := G) (M := M) (K := K) (U := U) hM hKU hxT with
      ⟨n, q, hxpow_order, hqcompl⟩
    let z : G := x ^ n
    let w : G := y ^ n
    have hz_eq : z = g * w * g⁻¹ := by
      dsimp [z, w]
      rw [hxy]
      exact conj_zpow (i := n) (a := g) (b := y)
    have hw_order : orderOf w = q.val := by
      have hconj_order : orderOf (g * w * g⁻¹) = orderOf w := by
        simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq w
      rw [← hconj_order, ← hz_eq]
      exact hxpow_order
    have huniq_z :
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({z} : Set G)) = {M} := by
      simpa [z] using
        section16_ASet_diff_msigma_zpow_unique_centralizer
          (G := G) (M := M) (K := K) (U := U) hM hxT hxpow_order hqcompl
    have huniq_w :
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({w} : Set G)) = {M} := by
      simpa [w] using
        section16_ASet_diff_msigma_zpow_unique_centralizer
          (G := G) (M := M) (K := K) (U := U) hM hyT hw_order hqcompl
    have hcent_w_le_M :
        Subgroup.centralizer ({w} : Set G) ≤ M := by
      have hMcont :
          M ∈ section9MaximalSubgroupsContaining
            (Subgroup.centralizer ({w} : Set G)) := by
        simp [huniq_w]
      exact hMcont.2
    have hMg_cont :
        M.conjBy g ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({z} : Set G)) := by
      refine ⟨section10_maximal_conjBy (G := G) hM g, ?_⟩
      intro c hcz
      have hc_w : g⁻¹ * c * g ∈ Subgroup.centralizer ({w} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hcz ⊢
        rw [hz_eq] at hcz
        calc
          (g⁻¹ * c * g) * w =
              g⁻¹ * (c * (g * w * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * w * g⁻¹) * c) * g := by rw [hcz]
          _ = w * (g⁻¹ * c * g) := by group
      rw [Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨g⁻¹ * c * g, hcent_w_le_M hc_w, ?_⟩
      simp [MulAut.conj_apply]
      group
    have hMg_eq_M : M.conjBy g = M := by
      have hsingle : M.conjBy g ∈ ({M} : Set (Subgroup G)) := by
        simpa [huniq_z] using hMg_cont
      simpa using hsingle
    have hgNormM : g ∈ Subgroup.normalizer (M : Set G) :=
      section16_mem_normalizer_of_conjBy_eq (G := G) hMg_eq_M
    exact hgM (by
      simpa [section16_maximal_normalizer_eq_self (G := G) hM] using hgNormM)

/-- Theorem B: the five assertions about `U`, `A(M)`, and `A_0(M)`. -/
@[expose] public def CFSG.section16TheoremBConclusions
    (M _K U : Subgroup G) : Prop :=
  section16HasAbelianSylowRankAtMostTwo U ∧
    section16SetCommutative ((U : Set G) ∩ section16HatMsigmaSet M) ∧
    (∃ U0 : Subgroup G, U0 ≤ U ∧ Monoid.exponent U0 = Monoid.exponent U ∧
      (U0 : Set G) ∩ section16HatMsigmaSet M = ({1} : Set G)) ∧
    (∀ X : Subgroup G, X ≤ U → X ≠ ⊥ →
      subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ →
        section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) ∧
    section16TISubset (section16ASet M U \ (section10Msigma M : Set G))

/-- Theorem B of Section 16. -/
public theorem CFSG.theorem_16_B
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (_hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U) :
    section16TheoremBConclusions M K U := by
  classical
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  exact ⟨
    section16_hasAbelianSylowRankAtMostTwo_of_section15 (G := G) hM hKU15,
    section16_setCommutative_hatMsigma_of_section15 (G := G) hM hKU15,
    section16_sameExponent_disjoint_hatMsigma_of_section15 (G := G) hM hKU15,
    section16_centralizer_unique_of_section15 (G := G) hM hKU15,
    section16_ASet_diff_msigma_TI (G := G) hM hKU15⟩

/-- Theorem C: the eleven assertions in the case `K != 1`. -/
@[expose] public def CFSG.section16TheoremCConclusions
    (M MF K U : Subgroup G) : Prop :=
  let Kstar := section16Kstar M K
  IsMulCommutative U ∧ ¬ Subgroup.normalizer (U : Set G) ≤ M ∧
    IsCyclic Kstar ∧ ⊥ < Kstar ∧ Kstar ≤ MF ∧ ¬ IsCyclic MF ∧
    ambientDerivedSubgroup M = U ⊔ section10Msigma M ∧
    Kstar ≤ section16SecondDerivedSubgroup M ∧
    ∃ Mstar : Subgroup G,
      section16MaximalTypeP Mstar ∧
        (∀ N : Subgroup G,
          section16MaximalTypeP N ∧
            K = subgroupCentralizerIn (section10Msigma N) Kstar ∧
            section12HallSubgroupIn (section16KappaPrimes N) Kstar N →
              N = Mstar) ∧
        K = subgroupCentralizerIn (section10Msigma Mstar) Kstar ∧
        section12HallSubgroupIn (section16KappaPrimes Mstar) Kstar Mstar ∧
        (∀ X : Subgroup G, section16PrimeOrderSubgroupOf X Kstar →
          section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) ∧
        (∀ Y : Subgroup G, section16PrimeOrderSubgroupOf Y K →
          section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {Mstar}) ∧
        M ⊓ Mstar = section16ZSubgroup K Kstar ∧
        section12InternalDirectProduct K Kstar (section16ZSubgroup K Kstar) ∧
        IsCyclic (section16ZSubgroup K Kstar) ∧
        (section16CaseP2 K U ∨ section16MaximalTypeP2 Mstar) ∧
        (∀ H : Subgroup G, section16MaximalTypeP H →
          (∃ g : G, H = M.conjBy g) ∨ ∃ g : G, H = Mstar.conjBy g) ∧
        section16TISubsetWithNormalizer (section16HatZ K Kstar) (section16ZSubgroup K Kstar) ∧
        section16ConjugatesOfSetBySet (section16HatZ K Kstar) (M : Set G) =
          section16AZeroSet M K \ section16ASet M U ∧
        section16TISubset (section16AZeroSet M K \ section16ASet M U) ∧
        (U ≠ ⊥ →
          section16HasPrimeOrder K ∧
            section16TISubset (section8FittingSubgroup M : Set G) ∧
              section10Msigma M ≤ section8FittingSubgroup M) ∧
        (U = ⊥ → section16HasPrimeOrder Kstar)

end MainResults
