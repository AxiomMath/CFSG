module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection13.theorem_13_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Data.Finset.NatDivisors
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Theorem 13 5 from BG Section 13 -/

section Section13

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_tau1_of_mem_E1_primeSet
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G} {p : Nat.Primes}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpE₁ : p ∈ subgroupPrimeSet E₁) :
    p ∈ section12Tau1Primes M := by
  classical
  rcases hE with ⟨_hcomp, hE₁₂, hE₁, _hE₂, _hE₃⟩
  rcases section12_E1_hall_in_E (G := G) hE₁₂ hE₁ with ⟨hE₁E, hHallE₁E⟩
  have hpE₁sub : p.val ∣ Nat.card (E₁.subgroupOf E) := by
    have hcard : Nat.card (E₁.subgroupOf E) = Nat.card E₁ :=
      natCard_subgroupOf_eq E₁ E hE₁E
    simpa [hcard, subgroupPrimeSet] using hpE₁
  exact hHallE₁E.p_in_pi_of_p_dvd_card p hpE₁sub

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_tau1_of_prime_order_le_E1
    {M E E₁₂ E₁ E₂ E₃ P : Subgroup G} {p : Nat.Primes}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁) :
    p ∈ section12Tau1Primes M := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hPE₁, hPcard⟩
  have hpE₁ : p ∈ subgroupPrimeSet E₁ := by
    have hpP : p.val ∣ Nat.card P := by
      rw [hPcard]
    have hpPsub : p.val ∣ Nat.card (P.subgroupOf E₁) := by
      have hcard : Nat.card (P.subgroupOf E₁) = Nat.card P :=
        natCard_subgroupOf_eq P E₁ hPE₁
      simpa [hcard] using hpP
    exact hpPsub.trans (Subgroup.card_subgroup_dvd_card (P.subgroupOf E₁))
  exact section13_tau1_of_mem_E1_primeSet (G := G) (M := M) (E := E)
    (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE hpE₁

omit [IsMinCE G] in
public theorem CFSG.section13_exists_prime_order_subgroup_le_ambient_sylow
    {A : Subgroup G} {q : Nat.Primes} (S : Sylow q.val A)
    (hSne : (S : Subgroup A) ≠ ⊥) :
    ∃ R : Subgroup G,
      R ≤ section10AmbientSylowSubgroup A S ∧ Nat.card R = q.val := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  obtain ⟨n, hncard⟩ := S.isPGroup'.exists_card_eq
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    have hcard_one : Nat.card (S : Subgroup A) = 1 := by
      simp [hncard, hn0]
    exact hSne ((Subgroup.eq_bot_iff_card (H := (S : Subgroup A))).2 hcard_one)
  have hqS : q.val ∣ Nat.card (S : Subgroup A) := by
    rcases Nat.exists_eq_succ_of_ne_zero hn_ne_zero with ⟨m, rfl⟩
    rw [hncard, Nat.pow_succ]
    exact dvd_mul_left q.val (q.val ^ m)
  obtain ⟨a, ha_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := (S : Subgroup A)) q.val hqS
  let R : Subgroup G := Subgroup.zpowers (((a : (S : Subgroup A)) : A) : G)
  have ha_mem_ambient :
      (((a : (S : Subgroup A)) : A) : G) ∈ section10AmbientSylowSubgroup A S := by
    exact Subgroup.mem_map_of_mem A.subtype a.property
  have hR_le : R ≤ section10AmbientSylowSubgroup A S := by
    exact Subgroup.zpowers_le.2 ha_mem_ambient
  have horderA : orderOf (((a : (S : Subgroup A)) : A)) = q.val := by
    simpa [Subgroup.orderOf_coe] using ha_order
  have horderG : orderOf ((((a : (S : Subgroup A)) : A) : G)) = q.val := by
    simpa [Subgroup.orderOf_coe] using horderA
  have hRcard : Nat.card R = q.val := by
    simp [R, Nat.card_zpowers, horderG]
  exact ⟨R, hR_le, hRcard⟩

omit [IsMinCE G] in
private theorem CFSG.section13_E1_sylow_as_E_sylow
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G} {q : Nat.Primes}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₁cyc : IsCyclic E₁) (hqE₁ : q ∈ subgroupPrimeSet E₁)
    (S : Sylow q.val E₁) :
    ∃ T : Sylow q.val E,
      section10AmbientSylowSubgroup E T = section10AmbientSylowSubgroup E₁ S ∧
        IsCyclic (T : Subgroup E) := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  rcases hE with ⟨_hcomp, hE₁₂, hE₁, _hE₂, _hE₃⟩
  rcases section12_E1_hall_in_E (G := G) hE₁₂ hE₁ with ⟨hE₁E, hHallE₁E⟩
  let f : E₁ →* E := E₁.subtype.codRestrict E (fun x => hE₁E x.property)
  let K : Subgroup E := (S : Subgroup E₁).map f
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : E => (z : G)) hxy
  have hKp : IsPGroup q.val K := by
    change IsPGroup q.val ((S : Subgroup E₁).map f)
    exact IsPGroup.map (p := q.val) (H := (S : Subgroup E₁))
      S.isPGroup' f
  have hqτ1 : q ∈ section12Tau1Primes M :=
    section13_tau1_of_mem_E1_primeSet (G := G) (M := M) (E := E)
      (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      ⟨_hcomp, hE₁₂, hE₁, _hE₂, _hE₃⟩ hqE₁
  have hK_not_index : ¬ q.val ∣ K.index := by
    intro hqKidx
    have hidx : K.index = (S : Subgroup E₁).index * f.range.index := by
      simpa [K] using (Subgroup.index_map_of_injective (H := (S : Subgroup E₁)) hf_inj)
    have hqprod : q.val ∣ (S : Subgroup E₁).index * f.range.index := by
      simpa [hidx] using hqKidx
    rcases q.property.dvd_mul.mp hqprod with hqSidx | hqrange
    · exact S.not_dvd_index hqSidx
    · have hrange_eq : f.range = E₁.subgroupOf E := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, _hy, rfl⟩
          exact y.property
        · intro hx
          exact ⟨⟨x, hx⟩, by simp [f]⟩
      exact (hHallE₁E.p_in_pi_of_p_dvd_index q (by simpa [hrange_eq] using hqrange)) hqτ1
  let T : Sylow q.val E := hKp.toSylow hK_not_index
  have hTcyc : IsCyclic (T : Subgroup E) := by
    haveI : IsCyclic E₁ := hE₁cyc
    have hScyc : IsCyclic (S : Subgroup E₁) := inferInstance
    have hKcyc : IsCyclic K :=
      (Subgroup.equivMapOfInjective (f := f) (S : Subgroup E₁) hf_inj).isCyclic.1 hScyc
    have hTK : (T : Subgroup E) = K := by
      simp [T, IsPGroup.toSylow_coe]
    rw [hTK]
    exact hKcyc
  refine ⟨T, ?_, hTcyc⟩
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨t, ht, rfl⟩
    change ((t : E) : G) ∈ section10AmbientSylowSubgroup E₁ S
    have htK : (t : E) ∈ K := by
      simpa [T, IsPGroup.toSylow_coe] using ht
    rcases Subgroup.mem_map.mp htK with ⟨s, hs, hs_eq⟩
    rw [← congrArg Subtype.val hs_eq]
    exact Subgroup.mem_map_of_mem E₁.subtype hs
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨s, hs, rfl⟩
    change ((s : E₁) : G) ∈ section10AmbientSylowSubgroup E T
    have hfs : f s ∈ (T : Subgroup E) := by
      simpa [T, K, IsPGroup.toSylow_coe] using Subgroup.mem_map_of_mem f hs
    rw [section10AmbientSylowSubgroup, Subgroup.mem_map]
    exact ⟨f s, hfs, by simp [f]⟩

private theorem CFSG.section13_E1_sylow_component_centralizes
    {M E E₁₂ E₁ E₂ E₃ P : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₁cyc : IsCyclic E₁)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁)
    (hqE₁ : q ∈ subgroupPrimeSet E₁) (S : Sylow q.val E₁) :
    section10AmbientSylowSubgroup E₁ S ≤
      Subgroup.centralizer (subgroupCentralizerIn (section10Msigma M) P : Set G) := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  rcases hE with ⟨hcomp, hE₁₂, hE₁, hE₂, hE₃⟩
  rcases section12_E1_hall_in_E (G := G) hE₁₂ hE₁ with ⟨hE₁E, _hHallE₁E⟩
  have hEdata : section12EData M E E₁₂ E₁ E₂ E₃ :=
    ⟨hcomp, hE₁₂, hE₁, hE₂, hE₃⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hPE₁, hPcard⟩
  have hpτ1 : p ∈ section12Tau1Primes M :=
    section13_tau1_of_prime_order_le_E1 (G := G) (M := M) (E := E)
      (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hEdata hP
  have hP_E : P ∈ section10PrimeOrderSubgroupsIn p E := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hPE₁.trans hE₁E, hPcard⟩
  have hqE : q ∈ subgroupPrimeSet E :=
    section8_subgroupPrimeSet_mono hE₁E hqE₁
  have hSne : (S : Subgroup E₁) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := E₁) S hqE₁
  rcases section13_exists_prime_order_subgroup_le_ambient_sylow
      (G := G) (A := E₁) S hSne with
    ⟨R, hR_le_S, hRcard⟩
  have hR_le_E₁ : R ≤ E₁ :=
    hR_le_S.trans (section13_ambient_sylow_le_base (G := G) E₁ S)
  have hR_cent_P : R ≤ Subgroup.centralizer (P : Set G) := by
    haveI : IsCyclic E₁ := hE₁cyc
    intro x hxR
    rw [Subgroup.mem_centralizer_iff]
    intro y hyP
    exact setLike_mul_comm (s := E₁) (hPE₁ hyP) (hR_le_E₁ hxR)
  have hR_prime_cent :
      R ∈ section10PrimeOrderSubgroupsIn q (subgroupCentralizerIn E P) := by
    have hR_le_cent : R ≤ subgroupCentralizerIn E P := by
      intro x hxR
      exact ⟨hE₁E (hR_le_E₁ hxR), hR_cent_P hxR⟩
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hR_le_cent, hRcard⟩
  have hCP_le_CR :
      subgroupCentralizerIn (section10Msigma M) P ≤
        subgroupCentralizerIn (section10Msigma M) R :=
    theorem_13_4 (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (R := R) (p := p) (r := q)
      hM hEdata hpτ1 hP_E hqE hR_prime_cent
  rcases section13_E1_sylow_as_E_sylow
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hEdata hE₁cyc hqE₁ S with
    ⟨T, hTamb_eq, hTcyc⟩
  have hTne : (T : Subgroup E) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := E) T hqE
  have hTacts :
      section13ActsPrimeManner
        (section10AmbientSylowSubgroup E T) (section10Msigma M) :=
    corollary_13_3_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hEdata q T hTne hTcyc
  have hR_le_Tamb : R ≤ section10AmbientSylowSubgroup E T := by
    simpa [hTamb_eq] using hR_le_S
  have hR_prime_Tamb :
      R ∈ section12PrimeOrderSubgroups (section10AmbientSylowSubgroup E T) := by
    simpa [section12PrimeOrderSubgroups] using ⟨hR_le_Tamb, ⟨q, hRcard⟩⟩
  have hCR_le_CT :
      subgroupCentralizerIn (section10Msigma M) R ≤
        subgroupCentralizerIn (section10Msigma M) (section10AmbientSylowSubgroup E T) :=
    hTacts.2 R hR_prime_Tamb
  have hCP_le_CT :
      subgroupCentralizerIn (section10Msigma M) P ≤
        subgroupCentralizerIn (section10Msigma M) (section10AmbientSylowSubgroup E T) :=
    hCP_le_CR.trans hCR_le_CT
  intro s hsS
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hsT : s ∈ section10AmbientSylowSubgroup E T := by
    simpa [hTamb_eq] using hsS
  exact (Subgroup.mem_centralizer_iff.mp (hCP_le_CT hy).2 s hsT).symm

/-- Theorem 13.5: if `E₁ ≠ 1`, then `E₁` acts in a prime manner on
`M_σ`. -/
public theorem CFSG.theorem_13_5
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (_hE₁ne : E₁ ≠ ⊥) :
    section13ActsPrimeManner E₁ (section10Msigma M) := by
  classical
  rcases hE with ⟨hcomp, hE₁₂, hE₁, hE₂, hE₃⟩
  rcases section12_E1_hall_in_E (G := G) hE₁₂ hE₁ with ⟨hE₁E, _hHallE₁E⟩
  have hEdata : section12EData M E E₁₂ E₁ E₂ E₃ :=
    ⟨hcomp, hE₁₂, hE₁, hE₂, hE₃⟩
  have hE₁cyc : IsCyclic E₁ := (lemma_12_1_d hM hEdata).1
  refine ⟨?_, ?_⟩
  · exact (hE₁E.trans hcomp.2.1).trans section13_le_normalizer_msigma
  · intro P hPprime
    rcases (by simpa [section12PrimeOrderSubgroups] using hPprime) with
      ⟨hPE₁, p, hPcard⟩
    have hP : P ∈ section10PrimeOrderSubgroupsIn p E₁ := by
      simpa [section10PrimeOrderSubgroupsIn] using ⟨hPE₁, hPcard⟩
    have hE₁_cent_CP :
        E₁ ≤ Subgroup.centralizer
          (subgroupCentralizerIn (section10Msigma M) P : Set G) :=
      section13_le_centralizer_of_exists_sylow_images
        (G := G) (K := subgroupCentralizerIn (section10Msigma M) P) (X := E₁) (by
          intro q hqE₁
          let S : Sylow q.val E₁ := default
          exact ⟨S,
            section13_E1_sylow_component_centralizes
              (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
              (E₂ := E₂) (E₃ := E₃) (P := P) (p := p) (q := q)
              hM hEdata hE₁cyc hP hqE₁ S⟩)
    intro y hy
    refine ⟨hy.1, ?_⟩
    change y ∈ Subgroup.centralizer (E₁ : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro e heE₁
    exact (Subgroup.mem_centralizer_iff.mp (hE₁_cent_CP heE₁) y hy).symm

end Section13
