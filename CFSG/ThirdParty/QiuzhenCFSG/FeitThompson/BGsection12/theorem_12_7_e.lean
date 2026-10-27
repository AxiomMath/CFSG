module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.theorem_12_7_d

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Theorem 12.7(e). -/
public theorem CFSG.theorem_12_7_e
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    ∃ E₀ : Subgroup G,
      section12ComplementIn E (subgroupCentralizerIn A (section10Msigma M)) E₀ ∧
        ∀ x : G, x ∈ section10Msigma M → x ≠ 1 →
          subgroupPrimeSet (elementCentralizerIn E₀ x) ⊆ section12Tau1Primes M := by
  classical
  obtain ⟨E₀, hE₀comp⟩ := theorem_12_7_d hM hE hp hA hSylow
  refine ⟨E₀, hE₀comp, ?_⟩
  intro x hxσ hxne q hqC
  have hE₀E : E₀ ≤ E := hE₀comp.2.1
  have hC_le_E₀ : elementCentralizerIn E₀ x ≤ E₀ := inf_le_left
  obtain ⟨z, hzC, hzne, hZq⟩ :=
    section12_exists_primeOrder_zpowers_of_prime_dvd_card_pre
      (B := elementCentralizerIn E₀ x) (q := q) hqC
  have hzE₀ : z ∈ E₀ := hC_le_E₀ hzC
  have hzE : z ∈ E := hE₀E hzE₀
  have hZ_E : Subgroup.zpowers z ∈ section10PrimeOrderSubgroupsIn q E := by
    rcases (show Subgroup.zpowers z ≤ elementCentralizerIn E₀ x ∧
        Nat.card (Subgroup.zpowers z) = q.val from hZq) with ⟨hZC, hZcard⟩
    exact ⟨hZC.trans (hC_le_E₀.trans hE₀E), hZcard⟩
  have hqτ :
      q ∈ section12Tau1Primes M ∪ section12Tau2Primes M ∪ section12Tau3Primes M := by
    have hqE : q ∈ subgroupPrimeSet E := by
      rcases (show Subgroup.zpowers z ≤ E ∧
          Nat.card (Subgroup.zpowers z) = q.val from hZ_E) with ⟨hZE, hZcard⟩
      have hqZ : q.val ∣ Nat.card (Subgroup.zpowers z) := by rw [hZcard]
      exact hqZ.trans (Subgroup.card_dvd_of_le hZE)
    exact section12_prime_mem_tau_union_of_mem_E hM hE.1 hqE
  rcases hqτ with hqτ12 | hqτ3
  · rcases hqτ12 with hqτ1 | hqτ2
    · exact hqτ1
    · have hτ2_single : section12Tau2Primes M = {p} :=
        theorem_12_7_a hM hE hp hA hSylow
      have hq_eq_p : q = p := by
        have hq_single : q ∈ ({p} : Set Nat.Primes) := by
          simpa [hτ2_single] using hqτ2
        simpa using hq_single
      have hZ_ne_A0 : Subgroup.zpowers z ≠ subgroupCentralizerIn A (section10Msigma M) := by
        intro hZ_eq_A0
        have hzA0 : z ∈ subgroupCentralizerIn A (section10Msigma M) := by
          rw [← hZ_eq_A0]
          exact Subgroup.mem_zpowers z
        have hzA : z ∈ A := hzA0.1
        have hzE₀' : z ∈ E₀ := hzE₀
        have hzbot : z ∈ (⊥ : Subgroup G) := by
          have hzinf : z ∈ subgroupCentralizerIn A (section10Msigma M) ⊓ E₀ :=
            ⟨hzA0, hzE₀'⟩
          simpa [hE₀comp.2.2.2.eq_bot] using hzinf
        exact hzne (by simpa using hzbot)
      have hZ_Msigma_bot :
          subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers z) = ⊥ :=
        (theorem_12_7_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
          hM hE hp hA hSylow (Subgroup.zpowers z)
          (by simpa [hq_eq_p] using hZ_E) hZ_ne_A0).1
      have hxCz : x ∈ subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers z) := by
        refine ⟨hxσ, ?_⟩
        have hzCentX : z ∈ Subgroup.centralizer ({x} : Set G) := hzC.2
        change x ∈ Subgroup.centralizer (Subgroup.zpowers z : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
        have hxz : x * z = z * x := by
          exact (Subgroup.mem_centralizer_iff.mp hzCentX) x (by simp)
        exact (Commute.zpow_right hxz n).eq.symm
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        simpa [hZ_Msigma_bot] using hxCz
      exact False.elim (hxne (by simpa using hxbot))
  · have hCx_bot :
        elementCentralizerIn (section10Msigma M) z = ⊥ :=
      corollary_12_6_d hM hE hp hA z ?_ hzne
    · have hxCz : x ∈ elementCentralizerIn (section10Msigma M) z := by
        refine ⟨hxσ, ?_⟩
        have hzCentX : z ∈ Subgroup.centralizer ({x} : Set G) := hzC.2
        change x ∈ Subgroup.centralizer ({z} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact ((Subgroup.mem_centralizer_iff.mp hzCentX) x (by simp)).symm
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        simpa [hCx_bot] using hxCz
      exact False.elim (hxne (by simpa using hxbot))
    · rcases (show Subgroup.zpowers z ≤ E ∧
          Nat.card (Subgroup.zpowers z) = q.val from hZ_E) with ⟨hZE, hZcard⟩
      have hzE3 : z ∈ E₃ := by
        have hqZ : q.val ∣ Nat.card (Subgroup.zpowers z) := by rw [hZcard]
        have hZp : IsPGroup q.val (Subgroup.zpowers z) := by
          refine IsPGroup.of_card (p := q.val) (G := Subgroup.zpowers z) (n := 1) ?_
          simpa [pow_one] using hZcard
        have hZsubE : (Subgroup.zpowers z).subgroupOf E ≤ E₃.subgroupOf E := by
          have hE3norm : section10NormalIn E₃ E := (lemma_12_1_b hM hE).2
          rcases hE with ⟨_hcomp, _hE12, _hE1, _hE2, hE3Hall⟩
          rcases hE3Hall with ⟨hE3E, hHallE3⟩
          have hZsub_p : IsPGroup q.val ((Subgroup.zpowers z).subgroupOf E) :=
            hZp.of_equiv
              (Subgroup.subgroupOfEquivOfLe (H := Subgroup.zpowers z) (K := E) hZE).symm
          haveI : (E₃.subgroupOf E).Normal := hE3norm.2
          exact section12_pSubgroup_le_normal_hall_of_prime_mem hHallE3 hqτ3 hZsub_p
        have hzsub : (⟨z, hzE⟩ : E) ∈ (Subgroup.zpowers z).subgroupOf E := by
          simp [Subgroup.mem_subgroupOf]
        exact hZsubE hzsub
      exact hzE3

public theorem CFSG.section12_E2_global_hall_of_abelian_sylow_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (_hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (_hAS : A ≤ (S : Subgroup G)) (hScomm : IsMulCommutative (S : Subgroup G)) :
    IsHallSubgroup (section12Tau2Primes M) E₂ := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  have hE2HallIn :
      section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
    section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
  rcases hE2HallIn with ⟨hE2E, hHallE2E⟩
  refine isHallSubgroup_of (G := G) (section12Tau2Primes M) E₂ ?_ ?_
  · intro q hqcard
    have hqcard_sub : q.val ∣ Nat.card (E₂.subgroupOf E) := by
      simpa [natCard_subgroupOf_eq _ _ hE2E] using hqcard
    exact hHallE2E.p_in_pi_of_p_dvd_card q hqcard_sub
  · intro q hqτ2 hqidx
    have hmul : E₂.relIndex E * E.index = E₂.index :=
      Subgroup.relIndex_mul_index hE2E
    have hprod : q.val ∣ E₂.relIndex E * E.index := by
      simpa [hmul] using hqidx
    rcases q.2.dvd_mul.mp hprod with hqrel | hqEidx
    · exact (hHallE2E.p_in_pi_of_p_dvd_index q
        (by simpa [Subgroup.relIndex] using hqrel)) hqτ2
    · obtain ⟨B, hB⟩ :=
        section12_exists_rankTwo_in_E_of_tau2
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) hM hE hqτ2
      haveI : Fact q.val.Prime := ⟨q.2⟩
      have hBq : IsPGroup q.val B := by
        have hElem := (section12_rankTwo_elementary hB).2
        haveI : IsElementaryAbelian q.val B := hElem
        exact IsElementaryAbelian.isPGroup q.val B
      obtain ⟨Q, hB_le_Q⟩ :=
        IsPGroup.exists_le_sylow (G := G) (p := q.val) hBq
      have hQcomm : IsMulCommutative (Q : Subgroup G) := by
        by_contra hQnoncomm
        have hτ2_single : section12Tau2Primes M = {q} :=
          theorem_12_7_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := B) (p := q)
            hM hE hqτ2 hB ⟨Q, hQnoncomm⟩
        have hpq : p = q := by
          have hp_single : p ∈ ({q} : Set Nat.Primes) := by
            simpa [hτ2_single] using hp
          simpa using hp_single
        have hq_eq_p : q = p := hpq.symm
        subst q
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
        have hconj_comm :
            IsMulCommutative ((g • S : Sylow p.val G) : Subgroup G) := by
          letI : IsMulCommutative (S : Subgroup G) := hScomm
          rw [Sylow.coe_subgroup_smul]
          exact Subgroup.map_isMulCommutative
            (f := (MulAut.conj g).toMonoidHom) (H := (S : Subgroup G))
        have hQcomm : IsMulCommutative (Q : Subgroup G) := by
          rw [← hg]
          exact hconj_comm
        exact hQnoncomm hQcomm
      have hQ_le_CB : (Q : Subgroup G) ≤ Subgroup.centralizer (B : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (setLike_mul_comm
          (s := (Q : Subgroup G)) hx (hB_le_Q hb)).symm
      have hCB_le_E : Subgroup.centralizer (B : Set G) ≤ E := by
        have h6B :=
          corollary_12_6_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := B) (p := q)
            hM hE hqτ2 hB
        simpa [h6B.2.1] using h6B.1
      have hQ_le_E : (Q : Subgroup G) ≤ E := hQ_le_CB.trans hCB_le_E
      exact Q.not_dvd_index
        (hqEidx.trans (Subgroup.index_dvd_of_le hQ_le_E))

public theorem CFSG.section12_tau2_sylow_comm_of_abelian_sylow_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p q : Nat.Primes}
    {S : Sylow p.val G} (Q : Sylow q.val G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (_hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (_hAS : A ≤ (S : Subgroup G)) (hScomm : IsMulCommutative (S : Subgroup G))
    (hq : q ∈ section12Tau2Primes M) :
    IsMulCommutative (Q : Subgroup G) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  by_contra hQnoncomm
  obtain ⟨B, hB⟩ :=
    section12_exists_rankTwo_in_E_of_tau2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hE hq
  have hτ2_single : section12Tau2Primes M = {q} :=
    theorem_12_7_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := B) (p := q)
      hM hE hq hB ⟨Q, hQnoncomm⟩
  have hpq : p = q := by
    have hp_single : p ∈ ({q} : Set Nat.Primes) := by
      simpa [hτ2_single] using hp
    simpa using hp_single
  have hq_eq_p : q = p := hpq.symm
  subst q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  have hconj_comm :
      IsMulCommutative ((g • S : Sylow p.val G) : Subgroup G) := by
    letI : IsMulCommutative (S : Subgroup G) := hScomm
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.map_isMulCommutative
      (f := (MulAut.conj g).toMonoidHom) (H := (S : Subgroup G))
  have hQcomm : IsMulCommutative (Q : Subgroup G) := by
    rw [← hg]
    exact hconj_comm
  exact hQnoncomm hQcomm


end Section12
