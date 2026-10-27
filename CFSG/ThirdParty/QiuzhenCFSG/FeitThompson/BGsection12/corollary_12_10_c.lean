module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_10_b

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# corollary_12_10_c
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_tau2_not_tau3
    {M : Subgroup G} {p : Nat.Primes}
    (hp : p ∈ section12Tau2Primes M) :
    p ∉ section12Tau3Primes M := by
  intro hp3
  have h2 : primeRank p.val M = 2 := hp.2
  have h1 : primeRank p.val M = 1 := hp3.2.2
  omega

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_subgroupCentralizerIn_normal_of_normal
    {E A : Subgroup G} (hAnorm : section10NormalIn A E) :
    section10NormalIn (subgroupCentralizerIn E A) E := by
  classical
  have hAE : A ≤ E := hAnorm.1
  haveI : (A.subgroupOf E).Normal := hAnorm.2
  have hC_le_E : subgroupCentralizerIn E A ≤ E := inf_le_left
  refine ⟨hC_le_E, ?_⟩
  have hCsub_eq :
      (subgroupCentralizerIn E A).subgroupOf E =
        Subgroup.centralizer ((A.subgroupOf E : Subgroup E) : Set E) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      apply Subtype.ext
      have hxC : (x : G) ∈ Subgroup.centralizer (A : Set G) := hx.2
      have haA : (a : G) ∈ A := by
        simpa [Subgroup.mem_subgroupOf] using ha
      exact Subgroup.mem_centralizer_iff.mp hxC (a : G) haA
    · intro hx
      refine ⟨x.property, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr (fun a ha => by
        let aE : E := ⟨a, hAE ha⟩
        have haSub : aE ∈ A.subgroupOf E := by
          simpa [aE, Subgroup.mem_subgroupOf] using ha
        have hcomm := Subgroup.mem_centralizer_iff.mp hx aE haSub
        exact congrArg Subtype.val hcomm)
  rw [hCsub_eq]
  exact Subgroup.normal_centralizer

omit [IsMinCE G] in
private theorem CFSG.section12_rankTwo_tau2_disjoint_E3_subgroupOf
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    A.subgroupOf E ⊓ E₃.subgroupOf E = ⊥ := by
  classical
  rcases hE with ⟨_hcomp, _hE12, _hE1, _hE2, hE3Hall⟩
  rcases hE3Hall with ⟨hE3E, hHallE3⟩
  have hAp : IsPGroup p.val (A.subgroupOf E) :=
    section12_rankTwo_subgroupOf_isPGroup hA
  have hp_not_tau3 : p ∉ section12Tau3Primes M :=
    section12_tau2_not_tau3 hp
  have hp_not_dvd_E3 : ¬ p.val ∣ Nat.card E₃ := by
    intro hpdiv
    have hpdiv_sub : p.val ∣ Nat.card (E₃.subgroupOf E) := by
      simpa [section12_card_subgroupOf_eq hE3E] using hpdiv
    exact hp_not_tau3 (hHallE3.p_in_pi_of_p_dvd_card p hpdiv_sub)
  apply Subgroup.card_eq_one.mp
  apply section12_card_eq_one_of_no_prime_dvd
  intro q hqdiv
  have hq_eq_p : q = p := by
    haveI : Fact p.val.Prime := ⟨p.2⟩
    have hqdiv_A : q.val ∣ Nat.card (A.subgroupOf E) :=
      hqdiv.trans (Subgroup.card_dvd_of_le (show
        (A.subgroupOf E) ⊓ (E₃.subgroupOf E) ≤ A.subgroupOf E from inf_le_left))
    rcases hAp.exists_card_eq with ⟨n, hn⟩
    have hq_dvd_p : q.val ∣ p.val := by
      exact q.2.dvd_of_dvd_pow (by simpa [hn] using hqdiv_A)
    exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hq_dvd_p)
  subst q
  have hpdiv_E3sub : p.val ∣ Nat.card (E₃.subgroupOf E) :=
    hqdiv.trans (Subgroup.card_dvd_of_le (show
      A.subgroupOf E ⊓ E₃.subgroupOf E ≤ E₃.subgroupOf E from inf_le_right))
  have hpdiv_E3 : p.val ∣ Nat.card E₃ := by
    simpa [section12_card_subgroupOf_eq hE3E] using hpdiv_E3sub
  exact hp_not_dvd_E3 hpdiv_E3

private theorem CFSG.section12_E3_le_centralizer_rankTwo_tau2
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    E₃ ≤ Subgroup.centralizer (A : Set G) := by
  classical
  have hAnorm : section10NormalIn A E :=
    (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA).1
  have hE3norm : section10NormalIn E₃ E :=
    (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2
  haveI : (A.subgroupOf E).Normal := hAnorm.2
  haveI : (E₃.subgroupOf E).Normal := hE3norm.2
  have hInfBot : A.subgroupOf E ⊓ E₃.subgroupOf E = ⊥ :=
    section12_rankTwo_tau2_disjoint_E3_subgroupOf
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hE hp hA
  have hcomm_bot : ⁅A.subgroupOf E, E₃.subgroupOf E⁆ = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxInf : x ∈ A.subgroupOf E ⊓ E₃.subgroupOf E :=
      Subgroup.commutator_le_inf (A.subgroupOf E) (E₃.subgroupOf E) hx
    simpa [hInfBot] using hxInf
  have hA_cent_E3 :
      A.subgroupOf E ≤ Subgroup.centralizer ((E₃.subgroupOf E : Subgroup E) : Set E) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hzE : z ∈ E := hE3norm.1 hz
  have haE : a ∈ E := section12_rankTwo_le hA ha
  let zE : E := ⟨z, hzE⟩
  let aE : E := ⟨a, haE⟩
  have hzSub : zE ∈ E₃.subgroupOf E := by
    simpa [zE, Subgroup.mem_subgroupOf] using hz
  have haSub : aE ∈ A.subgroupOf E := by
    simpa [aE, Subgroup.mem_subgroupOf] using ha
  have hcomm := Subgroup.mem_centralizer_iff.mp (hA_cent_E3 haSub) zE hzSub
  exact (congrArg Subtype.val hcomm).symm

private theorem CFSG.section12_E2_sup_E3_le_centralizer_rankTwo_tau2
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    E₂ ⊔ E₃ ≤ subgroupCentralizerIn E A := by
  classical
  have hA_le_E2 : A ≤ E₂ :=
    section12_rankTwo_tau2_le_E2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hM hE hp hA
  have hE2comm : IsMulCommutative E₂ :=
    (corollary_12_10_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).1
  have hE2_cent_A : E₂ ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (setLike_mul_comm
      (s := E₂) hx (hA_le_E2 ha)).symm
  have hE3_cent_A : E₃ ≤ Subgroup.centralizer (A : Set G) :=
    section12_E3_le_centralizer_rankTwo_tau2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hM hE hp hA
  have hKleE : E₂ ⊔ E₃ ≤ E :=
    (lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2.2.1.1
  have hKcent : E₂ ⊔ E₃ ≤ Subgroup.centralizer (A : Set G) :=
    sup_le hE2_cent_A hE3_cent_A
  intro x hx
  exact ⟨hKleE hx, hKcent hx⟩

/-- Corollary 12.10(c). -/
public theorem CFSG.corollary_12_10_c
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    E₂ ⊔ E₃ ≤ subgroupCentralizerIn E A ∧
      section10NormalIn (subgroupCentralizerIn E A) E ∧
        section12QuotientPrimeSet (subgroupCentralizerIn E A) E ⊆
          section12Tau1Primes M := by
  classical
  let C : Subgroup G := subgroupCentralizerIn E A
  let K : Subgroup G := E₂ ⊔ E₃
  have hKleC : K ≤ C :=
    section12_E2_sup_E3_le_centralizer_rankTwo_tau2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hM hE hp hA
  have hAnorm : section10NormalIn A E :=
    (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA).1
  have hCnorm : section10NormalIn C E :=
    section12_subgroupCentralizerIn_normal_of_normal (G := G) (E := E) (A := A) hAnorm
  have hE3norm : section10NormalIn E₃ E :=
    (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2
  have hKHallIn :
      section12HallSubgroupIn (section12Tau2Primes M ∪ section12Tau3Primes M)
        K E :=
    section12_E2_sup_E3_hall_in_E hE.2.1 hE.2.2.2.1 hE.2.2.2.2 hE3norm
  rcases hKHallIn with ⟨hKleE, hHallK⟩
  refine ⟨by simpa [K, C] using hKleC, by simpa [C] using hCnorm, ?_⟩
  intro q hqQuot
  rcases hqQuot with ⟨hCE, hqidx⟩
  have hKsub_le_Csub : K.subgroupOf E ≤ C.subgroupOf E := by
    intro x hx
    exact hKleC hx
  have hq_not_tau23 : q ∉ section12Tau2Primes M ∪ section12Tau3Primes M :=
    hHallK.p_in_pi_of_p_dvd_index q
      (hqidx.trans (Subgroup.index_dvd_of_le hKsub_le_Csub))
  have hqE : q ∈ subgroupPrimeSet E := by
    have hcardE :
        (C.subgroupOf E).index * Nat.card (C.subgroupOf E) = Nat.card E :=
      Subgroup.index_mul_card (H := C.subgroupOf E)
    have hq_card_E : q.val ∣ Nat.card E := by
      rw [← hcardE]
      exact dvd_mul_of_dvd_left hqidx _
    simpa [subgroupPrimeSet] using hq_card_E
  have hqτ :
      q ∈ section12Tau1Primes M ∪ section12Tau2Primes M ∪ section12Tau3Primes M :=
    section12_prime_mem_tau_union_of_mem_E hM hE.1 hqE
  rcases hqτ with hqτ12 | hqτ3
  · rcases hqτ12 with hqτ1 | hqτ2
    · exact hqτ1
    · exact False.elim (hq_not_tau23 (Or.inl hqτ2))
  · exact False.elim (hq_not_tau23 (Or.inr hqτ3))

end Section12
