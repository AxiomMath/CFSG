module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection13.lemma_13_8
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Data.Finset.NatDivisors
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Theorem 13 9 from BG Section 13 -/

section Section13

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
/-- A Section 12 data package exists for every maximal subgroup. -/
private theorem CFSG.section13_exists_EData
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    ∃ E E₁₂ E₁ E₂ E₃ : Subgroup G,
      section12EData M E E₁₂ E₁ E₂ E₃ := by
  classical
  have hbotπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ (⊥ : Subgroup G) := by
    intro q hq
    exact False.elim (q.property.not_dvd_one (by simpa using hq))
  rcases section13_exists_EData_containing_sigma_compl_piSubgroup
      (G := G) (M := M) (A := ⊥) hM bot_le hbotπ with
    ⟨E, E₁₂, E₁, E₂, E₃, hE, _hbot_le_E⟩
  exact ⟨E, E₁₂, E₁, E₂, E₃, hE⟩

/-- In Theorem 13.9, a common `σ` prime rules out `τ₂(M)` by
Corollary 12.6(f). -/
private theorem CFSG.section13_theorem_13_9_tau2_empty_of_common_sigma
    {M Mstar E E₁₂ E₁ E₂ E₃ : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hqM : q ∈ section10SigmaPrimes M)
    (hqMstar : q ∈ section10SigmaPrimes Mstar) :
    section12Tau2Primes M = ∅ := by
  classical
  ext p
  constructor
  · intro hpτ2
    rcases section12_exists_rankTwo_in_E_of_tau2
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hpτ2 with
      ⟨A, hA⟩
    have hdis :
        Disjoint (section10SigmaPrimes M) (section10SigmaPrimes Mstar) :=
      (corollary_12_6_f
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hpτ2 hA Mstar hMstar hnotconj).2
    exact False.elim ((Set.disjoint_left.mp hdis hqM) hqMstar)
  · intro hpempty
    cases hpempty

omit [IsMinCE G] in
/-- Once `E₁` is nontrivial, choose a prime-order subgroup of `E₁` and record
the corresponding `τ₁(M)` prime. -/
private theorem CFSG.section13_theorem_13_9_tau1_prime_order_choice
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₁ne : E₁ ≠ ⊥) :
    ∃ p : Nat.Primes, ∃ P : Subgroup G,
      p ∈ section12Tau1Primes M ∧
        P ∈ section10PrimeOrderSubgroupsIn p E₁ := by
  classical
  rcases section13_exists_prime_order_subgroup_le_of_ne_bot
      (G := G) (P := E₁) hE₁ne with
    ⟨p, P, hPE₁, hPcard⟩
  have hP : P ∈ section10PrimeOrderSubgroupsIn p E₁ := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hPE₁, hPcard⟩
  exact ⟨p, P,
    section13_tau1_of_prime_order_le_E1
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE hP,
    hP⟩

omit [IsMinCE G] in
private theorem CFSG.section13_conjBy_inv (H : Subgroup G) (a : G) :
    (H.conjBy a).conjBy a⁻¹ = H := by
  calc
    (H.conjBy a).conjBy a⁻¹ = H.conjBy (a⁻¹ * a) :=
      section8_conjBy_conjBy H a a⁻¹
    _ = H := by simpa using section8_conjBy_one (G := G) H


omit [IsMinCE G] in
private theorem CFSG.section13_mem_normalizer_of_conjBy_eq
    {H : Subgroup G} {g : G} (hg : H.conjBy g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx_conj : g * x * g⁻¹ ∈ H.conjBy g := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    simpa [hg] using hx_conj
  · intro hx
    have hginv : H.conjBy g⁻¹ = H := by
      calc
        H.conjBy g⁻¹ = (H.conjBy g).conjBy g⁻¹ := by rw [hg]
        _ = H := section13_conjBy_inv (G := G) H g
    have hx_inv_conj : x ∈ H.conjBy g⁻¹ := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨g * x * g⁻¹, hx, ?_⟩
      simp [mul_assoc]
    simpa [hginv] using hx_inv_conj


omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_maximal_conjBy
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) (a : G) :
    M.conjBy a ∈ section9MaximalSubgroups G := by
  have h_map : M.conjBy a = Subgroup.map ((MulAut.conj a : G ≃* G) : G →* G) M := rfl
  rw [h_map]
  exact ((MulAut.conj a : G ≃* G).mapSubgroup.isCoatom_iff M).mpr hM

omit [IsMinCE G] in
private theorem CFSG.section13_sigma_conjBy
    {M : Subgroup G} {p : Nat.Primes}
    (hpσ : p ∈ section10SigmaPrimes M) (a : G) :
    p ∈ section10SigmaPrimes (M.conjBy a) := by
  classical
  let _ : Fact p.val.Prime := ⟨p.property⟩
  rcases hpσ with ⟨hpM, P, hN⟩
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  let PGa : Subgroup G := PG.conjBy a
  have hPG_le_M : PG ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hPGa_le_Ma : PGa ≤ M.conjBy a := by
    intro x hx
    change x ∈ PG.conjBy a at hx
    rw [Subgroup.conjBy, Subgroup.mem_map] at hx
    rw [Subgroup.conjBy, Subgroup.mem_map]
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, hPG_le_M hy, rfl⟩
  have hPG_card : Nat.card PG = Nat.card (P : Subgroup M) := by
    simpa [PG, section10AmbientSylowSubgroup] using
      (Subgroup.card_map_of_injective
        (K := (P : Subgroup M)) (f := M.subtype) M.subtype_injective)
  let Psub : Subgroup (M.conjBy a) := PGa.subgroupOf (M.conjBy a)
  have hPsub_card :
      Nat.card Psub = p.val ^ (Nat.card (M.conjBy a)).factorization p.val := by
    calc
      Nat.card Psub = Nat.card PGa := by
        simpa [Psub] using natCard_subgroupOf_eq PGa (M.conjBy a) hPGa_le_Ma
      _ = Nat.card PG := by
        simpa [PGa] using section13_card_conjBy (G := G) PG a
      _ = Nat.card (P : Subgroup M) := by
        exact hPG_card
      _ = p.val ^ (Nat.card M).factorization p.val := Sylow.card_eq_multiplicity P
      _ = p.val ^ (Nat.card (M.conjBy a)).factorization p.val := by
        rw [section13_card_conjBy (G := G) M a]
  let P' : Sylow p.val (M.conjBy a) := Sylow.ofCard Psub hPsub_card
  have hP'_ambient : section10AmbientSylowSubgroup (M.conjBy a) P' = PGa := by
    calc
      section10AmbientSylowSubgroup (M.conjBy a) P' =
          (Psub.map (M.conjBy a).subtype : Subgroup G) := by
            simp [section10AmbientSylowSubgroup, P']
      _ = PGa ⊓ M.conjBy a := Subgroup.subgroupOf_map_subtype PGa (M.conjBy a)
      _ = PGa := inf_eq_left.mpr hPGa_le_Ma
  refine ⟨?_, P', ?_⟩
  · change p.val ∣ Nat.card (M.conjBy a)
    rw [section13_card_conjBy (G := G) M a]
    exact hpM
  · intro n hn
    have hnPGa : n ∈ Subgroup.normalizer (PGa : Set G) := by
      simpa [hP'_ambient] using hn
    have hPG_fix :
        PG.conjBy (a⁻¹ * n * a) = PG := by
      have hn_eq : PGa.conjBy n = PGa :=
        section13_conjBy_eq_of_mem_normalizer (G := G) (H := PGa) hnPGa
      have hna :
          PG.conjBy (n * a) = (PG.conjBy a).conjBy n := by
        exact (section8_conjBy_conjBy (G := G) PG a n).symm
      calc
        PG.conjBy (a⁻¹ * n * a) =
            (PG.conjBy (n * a)).conjBy a⁻¹ := by
              simpa [mul_assoc] using
                (section8_conjBy_conjBy (G := G) PG (n * a) a⁻¹).symm
        _ = ((PG.conjBy a).conjBy n).conjBy a⁻¹ := by
              rw [hna]
        _ = (PG.conjBy a).conjBy a⁻¹ := by
              rw [show (PG.conjBy a).conjBy n = PG.conjBy a by
                simpa [PGa] using hn_eq]
        _ = PG := section13_conjBy_inv (G := G) PG a
    have hconj :
        a⁻¹ * n * a ∈ Subgroup.normalizer (PG : Set G) :=
      section13_mem_normalizer_of_conjBy_eq (G := G) (H := PG) hPG_fix
    have hM : a⁻¹ * n * a ∈ M := hN hconj
    rw [Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨a⁻¹ * n * a, hM, by simp [mul_assoc]⟩

omit [IsMinCE G] in
private theorem CFSG.section13_notConjugate_conjBy_left
    {M Mstar : Subgroup G} (hnotconj : section12NotConjugate Mstar M) (a : G) :
    section12NotConjugate (Mstar.conjBy a) M := by
  intro g hg
  have hMstar_conj : Mstar.conjBy (g * a) = M := by
    calc
      Mstar.conjBy (g * a) = (Mstar.conjBy a).conjBy g :=
        (section8_conjBy_conjBy (G := G) Mstar a g).symm
      _ = M := hg
  exact hnotconj (g * a) hMstar_conj

private theorem CFSG.section13_exists_E_invariant_msigma_sylow
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hqσ : q ∈ section10SigmaPrimes M) :
    ∃ hEσ : Subgroup.Normalizes E (section10Msigma M),
      letI : Subgroup.Normalizes E (section10Msigma M) := hEσ
      ∃ S : Sylow q.val (section10Msigma M),
        IsInvariant (↥E) (↥(section10Msigma M))
          (S : Subgroup (section10Msigma M)) := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  have hE_le_M : E ≤ M := hE.1.2.1
  have hE_norm_msigma :
      E ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hE_le_M.trans section13_le_normalizer_msigma
  have hEσ : Subgroup.Normalizes E (section10Msigma M) := ⟨hE_norm_msigma⟩
  refine ⟨hEσ, ?_⟩
  let _ : Subgroup.Normalizes E (section10Msigma M) := hEσ
  have hMsigmaπsub : IsPiSubgroup (G := G) (section10SigmaPrimes M) (section10Msigma M) := by
    intro r hr
    exact ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card r hr
  have hMsigmaπ : IsPiGroup (section10SigmaPrimes M) (section10Msigma M) :=
    IsPiSubgroup.isPiGroup (section10Msigma M) hMsigmaπsub
  have hEπsub : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ E := by
    intro r hrE
    have hcard : Nat.card (E.subgroupOf M) = Nat.card E :=
      natCard_subgroupOf_eq E M hE_le_M
    have hrEsub : r.val ∣ Nat.card (E.subgroupOf M) := by
      simpa [hcard] using hrE
    exact (section12_msigma_complement_isHall_sigma_compl
      (G := G) hM hE.1).p_in_pi_of_p_dvd_card r hrEsub
  have hEπ : IsPiGroup (section10SigmaPrimes M)ᶜ E :=
    IsPiSubgroup.isPiGroup E hEπsub
  have hMsigma_le_M : section10Msigma M ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hMsigma_ne_top : section10Msigma M ≠ ⊤ := by
    intro htop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      intro x _hx
      exact hMsigma_le_M (by simp [htop])
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hMsigma_solv : Group.IsSolvable (section10Msigma M) :=
    IsMinCE.proper_subgroups_solvable (section10Msigma M)
      (lt_top_iff_ne_top.2 hMsigma_ne_top)
  have hq_eq : (⟨q.val, Fact.out⟩ : Nat.Primes) = q := by
    ext
    rfl
  exact
    exists_invariant_sylow_of_pi_complement_action
      (G := section10Msigma M) (A := E)
      (π := section10SigmaPrimes M) (p := q.val)
      hMsigmaπ hEπ hMsigma_solv (by rw [hq_eq]; exact hqσ)

public theorem CFSG.section13_exists_E_invariant_msigma_centralizer_sylow
    {M E E₁₂ E₁ E₂ E₃ Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE_norm_Q : E ≤ Subgroup.normalizer (Q : Set G))
    (hqC : q ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) Q)) :
    ∃ hEC : Subgroup.Normalizes E (subgroupCentralizerIn (section10Msigma M) Q),
      letI : Subgroup.Normalizes E (subgroupCentralizerIn (section10Msigma M) Q) := hEC
      ∃ S : Sylow q.val (subgroupCentralizerIn (section10Msigma M) Q),
        IsInvariant (↥E) (↥(subgroupCentralizerIn (section10Msigma M) Q))
          (S : Subgroup (subgroupCentralizerIn (section10Msigma M) Q)) := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  let C : Subgroup G := subgroupCentralizerIn (section10Msigma M) Q
  have hE_le_M : E ≤ M := hE.1.2.1
  have hE_norm_msigma :
      E ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hE_le_M.trans section13_le_normalizer_msigma
  have hE_norm_centQ :
      E ≤ Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) :=
    hE_norm_Q.trans (section13_normalizer_le_normalizer_centralizer (G := G) Q)
  have hE_norm_C : E ≤ Subgroup.normalizer (C : Set G) := by
    simpa [C, subgroupCentralizerIn] using
      section13_le_normalizer_inf
        (G := G) (A := E) (H := section10Msigma M)
        (K := Subgroup.centralizer (Q : Set G)) hE_norm_msigma hE_norm_centQ
  have hEC : Subgroup.Normalizes E C := ⟨hE_norm_C⟩
  refine ⟨by simpa [C] using hEC, ?_⟩
  let _ : Subgroup.Normalizes E C := hEC
  have hC_le_msigma : C ≤ section10Msigma M := by
    dsimp [C, subgroupCentralizerIn]
    exact inf_le_left
  have hCπsub : IsPiSubgroup (G := G) (section10SigmaPrimes M) C := by
    intro r hr
    exact ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card r
      (hr.trans (Subgroup.card_dvd_of_le hC_le_msigma))
  have hCπ : IsPiGroup (section10SigmaPrimes M) C :=
    IsPiSubgroup.isPiGroup C hCπsub
  have hEπsub : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ E := by
    intro r hrE
    have hcard : Nat.card (E.subgroupOf M) = Nat.card E :=
      natCard_subgroupOf_eq E M hE_le_M
    have hrEsub : r.val ∣ Nat.card (E.subgroupOf M) := by
      simpa [hcard] using hrE
    exact (section12_msigma_complement_isHall_sigma_compl
      (G := G) hM hE.1).p_in_pi_of_p_dvd_card r hrEsub
  have hEπ : IsPiGroup (section10SigmaPrimes M)ᶜ E :=
    IsPiSubgroup.isPiGroup E hEπsub
  have hMsigma_le_M : section10Msigma M ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hC_le_M : C ≤ M := hC_le_msigma.trans hMsigma_le_M
  have hC_ne_top : C ≠ ⊤ := by
    intro htop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [htop] using hC_le_M
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hCsolv : Group.IsSolvable C :=
    IsMinCE.proper_subgroups_solvable C (lt_top_iff_ne_top.2 hC_ne_top)
  have hqσ : q ∈ section10SigmaPrimes M :=
    section13_sigma_of_mem_centralizer_msigma (G := G) hM (P := Q) hqC
  have hq_eq : (⟨q.val, Fact.out⟩ : Nat.Primes) = q := by
    ext
    rfl
  simpa [C] using
    exists_invariant_sylow_of_pi_complement_action
      (G := C) (A := E) (π := section10SigmaPrimes M) (p := q.val)
      hCπ hEπ hCsolv (by rw [hq_eq]; exact hqσ)

omit [IsMinCE G] in
private theorem CFSG.section13_hall_sylow_map_to_overgroup_sylow
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes} {K : Subgroup H}
    (hKHall : IsHallSubgroup π K) {p : Nat.Primes} (hpπ : p ∈ π)
    (P : Sylow p.val K) :
    ∃ PH : Sylow p.val H, (PH : Subgroup H) = (P : Subgroup K).map K.subtype := by
  classical
  let _ : Fact p.val.Prime := ⟨p.property⟩
  let Psub : Subgroup H := (P : Subgroup K).map K.subtype
  have hPsubp : IsPGroup p.val Psub :=
    IsPGroup.map (p := p.val) (H := (P : Subgroup K)) P.isPGroup' K.subtype
  have hnot_index : ¬ p.val ∣ Psub.index := by
    intro hpidx
    have hidx : Psub.index = (P : Subgroup K).index * K.index := by
      simpa [Psub] using
        (Subgroup.index_map_subtype (H := K) (K := (P : Subgroup K)))
    have hp_prod : p.val ∣ (P : Subgroup K).index * K.index := by
      simpa [hidx] using hpidx
    rcases p.property.dvd_or_dvd hp_prod with hpPidx | hpKidx
    · exact P.not_dvd_index hpPidx
    · exact (hKHall.p_in_pi_of_p_dvd_index p hpKidx) hpπ
  let PH : Sylow p.val H := hPsubp.toSylow hnot_index
  exact ⟨PH, by simp [PH, Psub, IsPGroup.toSylow_coe]⟩

omit [IsMinCE G] in
public theorem CFSG.section13_sylowSubgroupIn_of_subgroup_sylow_with_ambient_sylow_le
    {K : Subgroup G} {C : Subgroup K} {q : Nat.Primes}
    (S : Sylow q.val C)
    (hfull : ∃ SK : Sylow q.val K, (SK : Subgroup K) ≤ C) :
    ∃ SK : Sylow q.val K,
      (SK : Subgroup K) = (S : Subgroup C).map C.subtype := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  let Smap : Subgroup K := (S : Subgroup C).map C.subtype
  have hSmap_p : IsPGroup q.val Smap :=
    IsPGroup.map (p := q.val) (H := (S : Subgroup C)) S.isPGroup' C.subtype
  rcases hfull with ⟨SK₀, hSK₀C⟩
  let SK₀C : Subgroup C := (SK₀ : Subgroup K).subgroupOf C
  have hSK₀_index :
      (SK₀ : Subgroup K).index = SK₀C.index * C.index := by
    have hmap : SK₀C.map C.subtype = (SK₀ : Subgroup K) := by
      simpa [SK₀C] using
        (Subgroup.map_subgroupOf_eq_of_le
          (H := (SK₀ : Subgroup K)) (K := C) hSK₀C)
    simpa [hmap] using
      (Subgroup.index_map_subtype (H := C) (K := SK₀C))
  have hq_not_C_index : ¬ q.val ∣ C.index := by
    intro hqC
    exact SK₀.not_dvd_index (by
      rw [hSK₀_index]
      exact dvd_mul_of_dvd_right hqC SK₀C.index)
  have hSmap_index :
      Smap.index = (S : Subgroup C).index * C.index := by
    simpa [Smap] using
      (Subgroup.index_map_subtype (H := C) (K := (S : Subgroup C)))
  have hSmap_not_index : ¬ q.val ∣ Smap.index := by
    intro hqSmap
    have hqprod : q.val ∣ (S : Subgroup C).index * C.index := by
      simpa [hSmap_index] using hqSmap
    rcases q.property.dvd_or_dvd hqprod with hqS | hqC
    · exact S.not_dvd_index hqS
    · exact hq_not_C_index hqC
  let SK : Sylow q.val K := hSmap_p.toSylow hSmap_not_index
  exact ⟨SK, by simp [SK, Smap, IsPGroup.toSylow_coe]⟩

public theorem CFSG.section13_msigma_sylowSubgroupIn_maximal
    {M : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hqσ : q ∈ section10SigmaPrimes M)
    (S : Sylow q.val (section10Msigma M)) :
    section12SylowSubgroupIn q
      (section10AmbientSylowSubgroup (section10Msigma M) S) M := by
  classical
  have hHallσ : IsHallSubgroup (section10SigmaPrimes M) (section10Msigma M) :=
    (theorem_10_2_b (G := G) hM).1
  rcases section13_hall_sylow_map_to_overgroup_sylow
      (H := G) (π := section10SigmaPrimes M) (K := section10Msigma M)
      hHallσ hqσ S with
    ⟨Sg, hSg⟩
  have hMsigma_le_M : section10Msigma M ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hQ_le_M :
      (Sg : Subgroup G) ≤ M := by
    intro x hx
    have hxQ : x ∈ section10AmbientSylowSubgroup (section10Msigma M) S := by
      simpa [section10AmbientSylowSubgroup, hSg] using hx
    exact hMsigma_le_M
      (section13_ambient_sylow_le_base (G := G) (section10Msigma M) S hxQ)
  let SM : Sylow q.val M := Sg.subtype hQ_le_M
  refine ⟨SM, ?_⟩
  calc
    section10AmbientSylowSubgroup M SM = (Sg : Subgroup G) := by
      change ((Sg : Subgroup G).subgroupOf M).map M.subtype = (Sg : Subgroup G)
      exact Subgroup.map_subgroupOf_eq_of_le (H := (Sg : Subgroup G)) (K := M) hQ_le_M
    _ = section10AmbientSylowSubgroup (section10Msigma M) S := by
      simpa [section10AmbientSylowSubgroup] using hSg

omit [IsMinCE G] in
public theorem CFSG.section13_normalizer_sylowSubgroupIn_le_of_sigma
    {M Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hqσ : q ∈ section10SigmaPrimes M)
    (hQ : section12SylowSubgroupIn q Q M) :
    Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  rcases hQ with ⟨S, hS⟩
  intro g hg
  refine theorem_10_1_d (G := G) (M := M) (p := q) hM hqσ S ?_
  rw [hS, section13_conjBy_eq_of_mem_normalizer (G := G) (H := Q) hg, ← hS]
  exact section13_ambient_sylow_le_base (G := G) M S

omit [IsMinCE G] in
public theorem CFSG.section13_commutator_eq_left_of_fixedpoint_free_pgroup
    {P Q H : Subgroup G} {p q : Nat.Primes}
    (hP : P ∈ section10PrimeOrderSubgroupsIn p H)
    (hQq : IsPGroup q.val Q)
    (hQne : Q ≠ ⊥)
    (hPinvQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥) :
    ⁅Q, P⁆ = Q := by
  classical
  let _ : Fact p.val.Prime := ⟨p.property⟩
  let _ : Fact q.val.Prime := ⟨q.property⟩
  have hq_ne_p : q ≠ p :=
    section13_ne_of_fixedpoint_free_p_sylow
      (G := G) (P := P) (Q := Q) (H := H) (p := p) (q := q)
      hP hQq hQne hPinvQ hCQ
  have hPp : IsPGroup p.val P :=
    section13_primeOrderSubgroupsIn_isPGroup (G := G) hP
  have hPπ : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) P :=
    section8_isPiSubgroup_singleton_of_isPGroup hPp
  have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q :=
    section8_isPiSubgroup_singleton_of_isPGroup hQq
  have hdis_pq : Disjoint ({p} : Set Nat.Primes) ({q} : Set Nat.Primes) := by
    rw [Set.disjoint_left]
    intro r hrp hrq
    have hrp_eq : r = p := by simpa using hrp
    have hrq_eq : r = q := by simpa using hrq
    exact hq_ne_p (hrq_eq.symm.trans hrp_eq)
  have hcop : Nat.Coprime (Nat.card P) (Nat.card Q) :=
    section13_coprime_card_of_isPiSubgroup_disjoint_primes
      (G := G) hPπ hQπ hdis_pq
  let _ : Subgroup.Normalizes P Q := ⟨hPinvQ⟩
  have hfixed_eq :
      fixedPointSubgroup (↥P) (↥Q) = (subgroupCentralizerIn Q P).subgroupOf Q := by
    simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Q P hPinvQ
  have hfix_bot : fixedPointSubgroup (↥P) (↥Q) = ⊥ := by
    rw [hfixed_eq]
    simpa using congrArg (fun S : Subgroup G => S.subgroupOf Q) hCQ
  have hQnil : Group.IsNilpotent Q :=
    IsPGroup.isNilpotent (p := q.val) (G := Q) hQq
  let _ : Group.IsNilpotent Q := hQnil
  have hsolvQ : Group.IsSolvable Q := inferInstance
  have hsup :
      fixedPointSubgroup (↥P) (↥Q) ⊔ commutatorAction (A := ↥P) (G := ↥Q) = ⊤ :=
    proposition_1_6_a (G := ↥Q) (A := ↥P) hsolvQ hcop
  have hcomm_top : commutatorAction (A := ↥P) (G := ↥Q) = ⊤ := by
    rw [hfix_bot, bot_sup_eq] at hsup
    exact hsup
  have hcomm_map :
      (commutatorAction (A := ↥P) (G := ↥Q)).map Q.subtype = ⁅Q, P⁆ := by
    simpa using commutatorAction_subgroup_conj_map_eq_commutator Q P hPinvQ
  have htop_map : (⊤ : Subgroup Q).map Q.subtype = Q := by
    ext x
    constructor
    · rintro ⟨y, _hy, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
  calc
    ⁅Q, P⁆ = (commutatorAction (A := ↥P) (G := ↥Q)).map Q.subtype := by
      exact hcomm_map.symm
    _ = (⊤ : Subgroup Q).map Q.subtype := by rw [hcomm_top]
    _ = Q := htop_map

/-- Core remaining configuration for Theorem 13.9: from a common `σ` prime
and a chosen `P ≤ E₁`, build the Lemma 13.8 hypotheses. -/
private theorem CFSG.section13_theorem_13_9_exists_lemma_13_8_data
    {M Mstar E E₁₂ E₁ E₂ E₃ P : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hqM : q ∈ section10SigmaPrimes M)
    (hqMstar : q ∈ section10SigmaPrimes Mstar)
    (_hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁) :
    ∃ Msharp Q : Subgroup G,
      Msharp ∈ section9MaximalSubgroups G ∧
        section12NotConjugate Msharp M ∧
          p ∈ section12Tau1Primes Msharp ∧
            P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Msharp) ∧
              section12SylowSubgroupIn q Q (M ⊓ Msharp) ∧
                P ≤ Subgroup.normalizer (Q : Set G) ∧
                  subgroupCentralizerIn Q P = ⊥ ∧
                    Subgroup.normalizer (Q : Set G) ≤ Msharp ∧
                      Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hP_E₁, hPcard⟩
  have hPne : P ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hPcard
  have hE₁_le_E : E₁ ≤ E :=
    (section12_E1_hall_in_E (G := G) hE.2.1 hE.2.2.1).1
  have hE_le_M : E ≤ M := hE.1.2.1
  have hP_M : P ≤ M := hP_E₁.trans (hE₁_le_E.trans hE_le_M)
  rcases section13_exists_E_invariant_msigma_sylow
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hqM with
    ⟨hEσ, S, hSinv⟩
  let Q : Subgroup G := section10AmbientSylowSubgroup (section10Msigma M) S
  have hE_norm_msigma :
      E ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hE_le_M.trans section13_le_normalizer_msigma
  let _ : Subgroup.Normalizes E (section10Msigma M) := hEσ
  have hE_norm_Q : E ≤ Subgroup.normalizer (Q : Set G) := by
    simpa [Q, section10AmbientSylowSubgroup] using
      section13_le_normalizer_map_of_isInvariant
        (G := G) (A := E) (H := section10Msigma M)
        (K := (S : Subgroup (section10Msigma M))) hE_norm_msigma hSinv
  have hPnormQ : P ≤ Subgroup.normalizer (Q : Set G) :=
    hP_E₁.trans (hE₁_le_E.trans hE_norm_Q)
  have hQ_M : section12SylowSubgroupIn q Q M :=
    section13_msigma_sylowSubgroupIn_maximal (G := G) hM hqM S
  have hQq : IsPGroup q.val Q :=
    section13_sylowSubgroupIn_isPGroup (G := G) hQ_M
  have hNQM : Subgroup.normalizer (Q : Set G) ≤ M :=
    section13_normalizer_sylowSubgroupIn_le_of_sigma (G := G) hM hqM hQ_M
  rcases section10_exists_conjBy_le_of_isPGroup_of_sigma
      (G := G) (M := Mstar) (Y := Q) (p := q) hqMstar hQq with
    ⟨a, hQ_le_Msharp⟩
  let Msharp : Subgroup G := Mstar.conjBy a
  have hMsharp : Msharp ∈ section9MaximalSubgroups G := by
    simpa [Msharp] using section13_maximal_conjBy (G := G) hMstar a
  have hnotconj_sharp : section12NotConjugate Msharp M := by
    simpa [Msharp] using section13_notConjugate_conjBy_left (G := G) hnotconj a
  have hqMsharp : q ∈ section10SigmaPrimes Msharp := by
    simpa [Msharp] using section13_sigma_conjBy (G := G) hqMstar a
  rcases hQ_M with ⟨SM, hSM⟩
  rcases section8SubgroupInAmbient_sylow_of_normalizer_le
      (G := G) (p := q.val) (M := M) SM (by
        intro g hg
        have hg' :
            g ∈ Subgroup.normalizer
              ((section10AmbientSylowSubgroup M SM : Subgroup G) : Set G) := by
          simpa [section10AmbientSylowSubgroup, section8SubgroupInAmbient] using hg
        exact hNQM (by simpa [hSM] using hg')) with
    ⟨Sg, hSgQ⟩
  have hSgQ' : (Sg : Subgroup G) = Q := by
    have hSg_ambient :
        (Sg : Subgroup G) = section10AmbientSylowSubgroup M SM := by
      simpa [section10AmbientSylowSubgroup, section8SubgroupInAmbient] using hSgQ
    exact hSg_ambient.trans hSM
  have hSg_le_Msharp : (Sg : Subgroup G) ≤ Msharp := by
    intro x hx
    exact hQ_le_Msharp (by simpa [hSgQ'] using hx)
  let Ssharp : Sylow q.val Msharp := Sg.subtype hSg_le_Msharp
  have hQ_Msharp : section12SylowSubgroupIn q Q Msharp := by
    refine ⟨Ssharp, ?_⟩
    calc
      section10AmbientSylowSubgroup Msharp Ssharp = (Sg : Subgroup G) := by
        change ((Sg : Subgroup G).subgroupOf Msharp).map Msharp.subtype = (Sg : Subgroup G)
        exact Subgroup.map_subgroupOf_eq_of_le (H := (Sg : Subgroup G)) (K := Msharp) hSg_le_Msharp
      _ = Q := hSgQ'
  have hNQsharp : Subgroup.normalizer (Q : Set G) ≤ Msharp :=
    section13_normalizer_sylowSubgroupIn_le_of_sigma (G := G) hMsharp hqMsharp hQ_Msharp
  have hP_Msharp : P ≤ Msharp := hPnormQ.trans hNQsharp
  have hPinf : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Msharp) := by
    simpa [section10PrimeOrderSubgroupsIn] using
      ⟨⟨hP_M, hP_Msharp⟩, hPcard⟩
  have hSg_le_inf : (Sg : Subgroup G) ≤ M ⊓ Msharp := by
    intro x hx
    exact ⟨hNQM (Subgroup.le_normalizer (by simpa [hSgQ'] using hx)), hSg_le_Msharp hx⟩
  let Sinf : Sylow q.val (M ⊓ Msharp : Subgroup G) := Sg.subtype hSg_le_inf
  have hQinf : section12SylowSubgroupIn q Q (M ⊓ Msharp) := by
    refine ⟨Sinf, ?_⟩
    calc
      section10AmbientSylowSubgroup (M ⊓ Msharp) Sinf = (Sg : Subgroup G) := by
        change ((Sg : Subgroup G).subgroupOf (M ⊓ Msharp)).map (M ⊓ Msharp).subtype = (Sg : Subgroup G)
        exact Subgroup.map_subgroupOf_eq_of_le
          (H := (Sg : Subgroup G)) (K := M ⊓ Msharp) hSg_le_inf
      _ = Q := hSgQ'
  have hCQ : subgroupCentralizerIn Q P = ⊥ := by
    by_contra hCne
    rcases section13_exists_prime_order_subgroup_le_of_ne_bot
        (G := G) (P := subgroupCentralizerIn Q P) hCne with
      ⟨r, X, hXleC, hXcard⟩
    have hX_le_Q : X ≤ Q := hXleC.trans inf_le_left
    have hXq : IsPGroup q.val X :=
      section13_isPGroup_of_le_pSubgroup (G := G) hQq hX_le_Q
    have hXne : X ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hXcard
    have hq_dvd_X : q.val ∣ Nat.card X := by
      rcases hXq.card_eq_or_dvd with hcard | hdiv
      · exact False.elim (hXne ((Subgroup.card_eq_one (H := X)).1 hcard))
      · exact hdiv
    have hq_dvd_r : q.val ∣ r.val := by
      simpa [hXcard] using hq_dvd_X
    have hqr_val : q.val = r.val :=
      (Nat.prime_dvd_prime_iff_eq q.property r.property).mp hq_dvd_r
    have hrq : r = q := Subtype.ext hqr_val.symm
    subst r
    have hQ_le_Msigma : Q ≤ section10Msigma M := by
      simpa [Q] using
        section13_ambient_sylow_le_base (G := G) (section10Msigma M) S
    have hX_prime :
        X ∈ section10PrimeOrderSubgroupsIn q
          (subgroupCentralizerIn (section10Msigma M) P) := by
      have hX_le_CMsigma :
          X ≤ subgroupCentralizerIn (section10Msigma M) P := by
        intro x hx
        exact ⟨hQ_le_Msigma ((hXleC hx).1), (hXleC hx).2⟩
      simpa [section10PrimeOrderSubgroupsIn] using ⟨hX_le_CMsigma, hXcard⟩
    have hUniqueQ :
        section9MaximalSubgroupsContaining
          (section10AmbientSylowSubgroup (section10Msigma M) S) = {M} :=
      (lemma_13_6
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
        (P := P) (X := X) (q := q) S hM hE hPne hP_E₁ hqM hX_prime).2
    have hMsharp_mem :
        Msharp ∈ section9MaximalSubgroupsContaining
          (section10AmbientSylowSubgroup (section10Msigma M) S) := by
      refine ⟨hMsharp, ?_⟩
      simpa [Q] using hQ_le_Msharp
    have hMsharp_eq_M : Msharp = M := by
      have hsingle : Msharp ∈ ({M} : Set (Subgroup G)) := by
        simpa [hUniqueQ] using hMsharp_mem
      simpa using hsingle
    exact hnotconj_sharp 1 (by
      simpa [hMsharp_eq_M] using section8_conjBy_one (G := G) Msharp)
  have hpτ1sharp : p ∈ section12Tau1Primes Msharp := by
    by_contra hp_notτ1sharp
    have hpE : p ∈ subgroupPrimeSet E := by
      have hp_dvd_P : p.val ∣ Nat.card P := by rw [hPcard]
      exact hp_dvd_P.trans (Subgroup.card_dvd_of_le (hP_E₁.trans hE₁_le_E))
    have hpMsharp : p ∈ subgroupPrimeSet Msharp := by
      have hp_dvd_P : p.val ∣ Nat.card P := by rw [hPcard]
      exact hp_dvd_P.trans (Subgroup.card_dvd_of_le hP_Msharp)
    have hQne : Q ≠ ⊥ :=
      section13_ne_bot_of_normalizer_le_maximal (G := G) hM hNQM
    have hQ_le_Msigma : Q ≤ section10Msigma M := by
      simpa [Q] using
        section13_ambient_sylow_le_base (G := G) (section10Msigma M) S
    let K : Subgroup G := section10Msigma M ⊓ Msharp
    let L : Subgroup G := M ⊓ Msharp
    have hQ_le_K : Q ≤ K := by
      intro x hx
      exact ⟨hQ_le_Msigma hx, hQ_le_Msharp hx⟩
    have hP_le_L : P ≤ L := by
      intro x hx
      exact ⟨hP_M hx, hP_Msharp hx⟩
    have hcommQP : ⁅Q, P⁆ = Q :=
      section13_commutator_eq_left_of_fixedpoint_free_pgroup
        (G := G) (P := P) (Q := Q) (H := M ⊓ Msharp)
        (p := p) (q := q) hPinf hQq hQne hPnormQ hCQ
    have hcomm_le : ⁅Q, P⁆ ≤ ⁅K, L⁆ :=
      Subgroup.commutator_mono hQ_le_K hP_le_L
    have hQ_le_comm : Q ≤ ⁅K, L⁆ := by
      rw [← hcommQP]
      exact hcomm_le
    have hcomm_ne : ⁅section10Msigma M ⊓ Msharp, M ⊓ Msharp⁆ ≠ ⊥ := by
      intro hbot
      have hQbot : Q ≤ (⊥ : Subgroup G) := by
        simpa [K, L, hbot] using hQ_le_comm
      exact hQne (le_bot_iff.mp hQbot)
    have hPp : IsPGroup p.val P :=
      section13_primeOrderSubgroupsIn_isPGroup (G := G) hPinf
    have hP_cent_K :
        P ≤ Subgroup.centralizer (section10Msigma M ⊓ Msharp : Set G) :=
      lemma_13_1_a
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
        (Mstar := Msharp) (p := p)
        hM hE hMsharp hpE hpMsharp hp_notτ1sharp hcomm_ne hnotconj_sharp
        P hP_le_L hPp
    have hK_cent_P :
        section10Msigma M ⊓ Msharp ≤ Subgroup.centralizer (P : Set G) :=
      (Subgroup.le_centralizer_iff
        (H := P) (K := section10Msigma M ⊓ Msharp)).mp hP_cent_K
    have hQ_le_C : Q ≤ subgroupCentralizerIn Q P := by
      intro x hx
      exact ⟨hx, hK_cent_P (hQ_le_K hx)⟩
    have hQbot : Q ≤ (⊥ : Subgroup G) := by
      simpa [hCQ] using hQ_le_C
    exact hQne (le_bot_iff.mp hQbot)
  exact ⟨Msharp, Q, hMsharp, hnotconj_sharp, hpτ1sharp, hPinf,
    hQinf, hPnormQ, hCQ, hNQsharp, hNQM⟩

/-- Applying the explicit Lemma 13.8 data gives the contradiction needed in
Theorem 13.9. -/
private theorem CFSG.section13_theorem_13_9_lemma_13_8_configuration
    {M Mstar E E₁₂ E₁ E₂ E₃ P : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hqM : q ∈ section10SigmaPrimes M)
    (hqMstar : q ∈ section10SigmaPrimes Mstar)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁) :
    False := by
  classical
  rcases section13_theorem_13_9_exists_lemma_13_8_data
      (G := G) (M := M) (Mstar := Mstar) (E := E)
      (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (P := P) (p := p) (q := q)
      hM hE hMstar hnotconj hqM hqMstar hpτ1 hP with
    ⟨Msharp, Q, hMsharp, hnotconj_sharp, hpτ1sharp, hPinf,
      hQ, hPnormQ, hCQ, hNQsharp, hNQM⟩
  exact
    lemma_13_8
      (G := G) (M := M) (Mstar := Msharp) (P := P) (Q := Q)
      (Qstar := Q) (p := p) (q := q) (qstar := q)
      hM hMsharp hnotconj_sharp hpτ1 hpτ1sharp hPinf hQ hQ
      hPnormQ hPnormQ hCQ hCQ hNQsharp hNQM

/-- Common `σ` primes are impossible in the Theorem 13.9 setup. -/
private theorem CFSG.section13_theorem_13_9_common_sigma_absurd
    {M Mstar : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hqM : q ∈ section10SigmaPrimes M)
    (hqMstar : q ∈ section10SigmaPrimes Mstar) :
    False := by
  classical
  rcases section13_exists_EData (G := G) (M := M) hM with
    ⟨E, E₁₂, E₁, E₂, E₃, hE⟩
  have hτ2empty : section12Tau2Primes M = ∅ :=
    section13_theorem_13_9_tau2_empty_of_common_sigma
      (G := G) (M := M) (Mstar := Mstar) (E := E)
      (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      hM hE hMstar hnotconj hqM hqMstar
  have hE₂bot : E₂ = ⊥ :=
    section13_E2_eq_bot_of_tau2_empty
      (G := G) (M := M) (E₁₂ := E₁₂) (E₂ := E₂)
      hE.2.2.2.1 hτ2empty
  have hE₁ne : E₁ ≠ ⊥ :=
    lemma_12_1_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hE₂bot
  rcases section13_theorem_13_9_tau1_prime_order_choice
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE hE₁ne with
    ⟨p, P, hpτ1, hP⟩
  exact
    section13_theorem_13_9_lemma_13_8_configuration
      (G := G) (M := M) (Mstar := Mstar) (E := E)
      (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (P := P) (p := p) (q := q)
      hM hE hMstar hnotconj hqM hqMstar hpτ1 hP

/-- Theorem 13.9: if `M* ∈ 𝓜` is not conjugate to `M`, then
`σ(M)` and `σ(M*)` are disjoint. -/
public theorem CFSG.theorem_13_9
    {M Mstar : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M) :
    Disjoint (section10SigmaPrimes M) (section10SigmaPrimes Mstar) := by
  classical
  rw [Set.disjoint_left]
  intro q hqM hqMstar
  exact
    section13_theorem_13_9_common_sigma_absurd
      (G := G) (M := M) (Mstar := Mstar)
      hM hMstar hnotconj hqM hqMstar

end Section13
