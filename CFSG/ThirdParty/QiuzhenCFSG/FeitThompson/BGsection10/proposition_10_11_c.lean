module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.proposition_10_11_b
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] in
private theorem CFSG.section10_coprime_card_of_hall_disjoint_primes
    {π ρ : Set Nat.Primes} {A B : Subgroup G}
    (hA : IsHallSubgroup π A) (hB : IsHallSubgroup ρ B)
    (hπρ : Disjoint π ρ) :
    Nat.Coprime (Nat.card A) (Nat.card B) := by
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hqA hqB
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hqπ : q' ∈ π := hA.p_in_pi_of_p_dvd_card q' hqA
  have hqρ : q' ∈ ρ := hB.p_in_pi_of_p_dvd_card q' hqB
  exact (Set.disjoint_left.mp hπρ hqπ) hqρ

omit [Finite G] in
public theorem CFSG.section10_disjoint_of_hall_disjoint_primes
    {π ρ : Set Nat.Primes} {A B : Subgroup G}
    (hA : IsHallSubgroup π A) (hB : IsHallSubgroup ρ B)
    (hπρ : Disjoint π ρ) :
    Disjoint A B := by
  rw [Subgroup.disjoint_def]
  intro x hxA hxB
  have hcop : Nat.Coprime (Nat.card A) (Nat.card B) :=
    section10_coprime_card_of_hall_disjoint_primes hA hB hπρ
  have hcop_order : Nat.Coprime (orderOf x) (Nat.card B) :=
    Nat.Coprime.of_dvd_left (Subgroup.orderOf_dvd_natCard A hxA) hcop
  have hx_order_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_order dvd_rfl
      (Subgroup.orderOf_dvd_natCard B hxB)
  exact orderOf_eq_one_iff.mp hx_order_one

omit [Finite G] in
public theorem CFSG.section10_coprime_card_of_isPiSubgroup_disjoint_primes
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

omit [Finite G] in
public theorem CFSG.section10_disjoint_of_isPiSubgroup_disjoint_primes
    {π ρ : Set Nat.Primes} {A B : Subgroup G}
    (hA : IsPiSubgroup π A) (hB : IsPiSubgroup ρ B)
    (hπρ : Disjoint π ρ) :
    Disjoint A B := by
  rw [Subgroup.disjoint_def]
  intro x hxA hxB
  have hcop : Nat.Coprime (Nat.card A) (Nat.card B) :=
    section10_coprime_card_of_isPiSubgroup_disjoint_primes hA hB hπρ
  have hcop_order : Nat.Coprime (orderOf x) (Nat.card B) :=
    Nat.Coprime.of_dvd_left (Subgroup.orderOf_dvd_natCard A hxA) hcop
  have hx_order_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_order dvd_rfl
      (Subgroup.orderOf_dvd_natCard B hxB)
  exact orderOf_eq_one_iff.mp hx_order_one

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_msigma_eq_piCoreIn (M : Subgroup G) :
    section10Msigma M = piCoreIn (section10SigmaPrimes M) M := by
  rfl

omit [IsMinCE G] in
private theorem CFSG.section10_piCoreIn_mono
    {π ρ : Set Nat.Primes} (H : Subgroup G) (hπρ : π ⊆ ρ) :
    piCoreIn π H ≤ piCoreIn ρ H := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact Subgroup.mem_map.mpr
    ⟨y, section10_piCore_mono (H := H) hπρ hy, rfl⟩

omit [IsMinCE G] in
public theorem CFSG.section10_le_normalizer_msigma
    {M : Subgroup G} :
    M ≤ Subgroup.normalizer (section10Msigma M : Set G) := by
  rw [section10_msigma_eq_piCoreIn]
  exact section8_le_normalizer_piCoreIn_of_le_normalizer
    (G := G) (π := section10SigmaPrimes M) (H := M) (P := M)
    (by
      intro x hx
      exact Subgroup.le_normalizer hx)

omit [Finite G] in
public theorem CFSG.section10_le_normalizer_fitting
    (M : Subgroup G) :
    M ≤ Subgroup.normalizer (section8FittingSubgroup M : Set G) := by
  have hFNorm : ((section8FittingSubgroup M).subgroupOf M).Normal :=
    section8FittingSubgroup_normal_in M
  letI : ((section8FittingSubgroup M).subgroupOf M).Normal := hFNorm
  exact Subgroup.le_normalizer_of_normal_subgroupOf (section8FittingSubgroup_le M)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_le_normalizer_sigma_compl_fitting_core
    (M : Subgroup G) :
    M ≤ Subgroup.normalizer
      (piCoreIn (section10SigmaPrimes M)ᶜ (section8FittingSubgroup M) : Set G) := by
  let F : Subgroup G := section8FittingSubgroup M
  let ZF : Subgroup F := piCore (section10SigmaPrimes M)ᶜ F
  have hnormFZ :
      Subgroup.normalizer (F : Set G) ≤
        Subgroup.normalizer ((ZF.map F.subtype : Subgroup G) : Set G) := by
    exact
      section10_normalizer_le_normalizer_map_subtype_of_characteristic_pre
        (G := G) F ZF
  exact (section10_le_normalizer_fitting (G := G) M).trans (by
    simpa [F, ZF, piCoreIn] using hnormFZ)

public theorem CFSG.section10_sigma_compl_fitting_core_le_centralizer_msigma
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    piCoreIn (section10SigmaPrimes M)ᶜ (section8FittingSubgroup M) ≤
      Subgroup.centralizer (section10Msigma M : Set G) := by
  classical
  let F : Subgroup G := section8FittingSubgroup M
  let Z : Subgroup G := piCoreIn (section10SigmaPrimes M)ᶜ F
  let S : Subgroup G := section10Msigma M
  have hZπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ Z := by
    simpa [Z, F] using piCoreIn_isPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ F
  have hSπ : IsPiSubgroup (G := G) (section10SigmaPrimes M) S := by
    exact (theorem_10_2_b (G := G) hM).1.p_in_pi_of_p_dvd_card
  have hπdisj : Disjoint (section10SigmaPrimes M)ᶜ (section10SigmaPrimes M) := by
    rw [Set.disjoint_left]
    intro p hp_compl hp
    exact hp_compl hp
  have hZSdisj : Disjoint Z S :=
    section10_disjoint_of_isPiSubgroup_disjoint_primes hZπ hSπ hπdisj
  have hSleM : S ≤ M := by
    intro x hx
    exact piCoreIn_le (G := G) (section10SigmaPrimes M) M
      (by simpa [S, section10_msigma_eq_piCoreIn] using hx)
  have hZleF : Z ≤ F := by
    simpa [Z, F] using
      piCoreIn_le (G := G) (section10SigmaPrimes M)ᶜ F
  have hMnormZ : M ≤ Subgroup.normalizer (Z : Set G) := by
    simpa [Z, F] using section10_le_normalizer_sigma_compl_fitting_core (G := G) M
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hs_norm_Z : s ∈ Subgroup.normalizer (Z : Set G) :=
    hMnormZ (hSleM hs)
  have hz_norm_S : z ∈ Subgroup.normalizer (S : Set G) :=
    section10_le_normalizer_msigma (G := G) (M := M)
      (section8FittingSubgroup_le M (hZleF hz))
  have hcommZ : ⁅z, s⁆ ∈ Z := by
    have hsz : s * z⁻¹ * s⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp hs_norm_Z z⁻¹).1 (Z.inv_mem hz)
    simpa [commutatorElement_def, mul_assoc] using Z.mul_mem hz hsz
  have hcommS : ⁅z, s⁆ ∈ S := by
    have hzs : z * s * z⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp hz_norm_S s).1 hs
    simpa [commutatorElement_def, mul_assoc] using S.mul_mem hzs (S.inv_mem hs)
  have hcomm_one : ⁅z, s⁆ = 1 :=
    Subgroup.disjoint_def.mp hZSdisj hcommZ hcommS
  exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm_one).symm

public theorem CFSG.section10_sigma_compl_fitting_core_isCyclic
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    IsCyclic ↥(piCoreIn (section10SigmaPrimes M)ᶜ (section8FittingSubgroup M)) := by
  classical
  let F : Subgroup G := section8FittingSubgroup M
  let Z : Subgroup G := piCoreIn (section10SigmaPrimes M)ᶜ F
  have hZπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ Z := by
    simpa [Z, F] using piCoreIn_isPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ F
  have hZleF : Z ≤ F := by
    simpa [Z, F] using
      piCoreIn_le (G := G) (section10SigmaPrimes M)ᶜ F
  have hZleM : Z ≤ M :=
    hZleF.trans (section8FittingSubgroup_le M)
  have hZcent :
      Z ≤ Subgroup.centralizer (section10Msigma M : Set G) := by
    simpa [Z, F] using
      section10_sigma_compl_fitting_core_le_centralizer_msigma (G := G) hM
  have hZleC : Z ≤ subgroupCentralizerIn Z (section10Msigma M) := by
    intro z hz
    exact ⟨hz, hZcent hz⟩
  have hZrank : groupRank Z ≤ 1 :=
    (section10_groupRank_le_of_le hZleC).trans
      (proposition_10_11_b (G := G) hM hZleM hZπ)
  have hZgroup : IsZGroup Z :=
    section10_isZGroup_of_subgroup_groupRank_le_one (G := G) Z hZrank
  have hZnil : Group.IsNilpotent Z := by
    have hFnil : Group.IsNilpotent F := section8FittingSubgroup_isNilpotent M
    letI : Group.IsNilpotent F := hFnil
    let ZF : Subgroup F := Z.subgroupOf F
    have hZF_nil : Group.IsNilpotent ZF := Subgroup.isNilpotent ZF
    let e : ZF ≃* Z := Subgroup.subgroupOfEquivOfLe (H := Z) (K := F) hZleF
    exact Group.nilpotent_of_mulEquiv (G := ZF) (G' := Z) e
  letI : IsZGroup Z := hZgroup
  letI : Group.IsNilpotent Z := hZnil
  infer_instance

omit [IsMinCE G] in
public theorem CFSG.section10_fitting_le_msigma_sup_sigma_compl_fitting_core
    (M : Subgroup G) :
    section8FittingSubgroup M ≤
      section10Msigma M ⊔
        piCoreIn (section10SigmaPrimes M)ᶜ (section8FittingSubgroup M) := by
  classical
  let F : Subgroup G := section8FittingSubgroup M
  let S : Subgroup G := section10Msigma M
  let Z : Subgroup G := piCoreIn (section10SigmaPrimes M)ᶜ F
  let K : Subgroup F := (S ⊔ Z).comap F.subtype
  have hFnil : Group.IsNilpotent F := by
    simpa [F] using section8FittingSubgroup_isNilpotent M
  letI : Group.IsNilpotent F := hFnil
  have htop_nil : Group.IsNilpotent (⊤ : Subgroup F) := by
    let e : F ≃* (⊤ : Subgroup F) :=
      (Subgroup.topEquiv : (⊤ : Subgroup F) ≃* F).symm
    exact Group.nilpotent_of_mulEquiv (G := F) (G' := (⊤ : Subgroup F)) e
  have htop_le_sup :
      (⊤ : Subgroup F) ≤
        ⨆ q : (Nat.card F).primeFactors.attach, pCore q.1.1 F :=
    normal_nilpotent_le_sup_pCore
      (G := F) (N := (⊤ : Subgroup F)) (hN := inferInstance) htop_nil
  have hMnormF : M ≤ Subgroup.normalizer (F : Set G) := by
    simpa [F] using section10_le_normalizer_fitting (G := G) M
  have hsup_le_K :
      (⨆ q : (Nat.card F).primeFactors.attach, pCore q.1.1 F) ≤ K := by
    refine iSup_le ?_
    intro q0
    let q : Nat.Primes := ⟨q0.1.1, Nat.prime_of_mem_primeFactors q0.1.2⟩
    haveI : Fact q.val.Prime := ⟨q.2⟩
    by_cases hqσ : q ∈ section10SigmaPrimes M
    · have hcore_le_S :
          (pCore q.val F).map F.subtype ≤ S := by
        have hsingle_le_FM :
            piCoreIn ({q} : Set Nat.Primes) F ≤ piCoreIn ({q} : Set Nat.Primes) M :=
          section8_piCoreIn_singleton_le_of_le_normalizer
            (G := G) (Y := F) (H := M)
            (by simpa [F] using section8FittingSubgroup_le M) hMnormF q
        have hsingle_le_sigma :
            piCoreIn ({q} : Set Nat.Primes) M ≤ piCoreIn (section10SigmaPrimes M) M :=
          section10_piCoreIn_mono (G := G) M (by
            intro r hr
            simpa using hr ▸ hqσ)
        intro x hx
        have hxsingle : x ∈ piCoreIn ({q} : Set Nat.Primes) F := by
          simpa [section8_piCoreIn_singleton_eq_pCore_map q F] using
            hx
        simpa [S, section10_msigma_eq_piCoreIn] using
          hsingle_le_sigma (hsingle_le_FM hxsingle)
      intro x hx
      exact Subgroup.mem_comap.mpr
        (Subgroup.mem_sup_left (hcore_le_S (by simpa [q] using hx)))
    · have hcore_le_Z :
          (pCore q.val F).map F.subtype ≤ Z := by
        have hsingle_le_compl :
            piCoreIn ({q} : Set Nat.Primes) F ≤
              piCoreIn (section10SigmaPrimes M)ᶜ F :=
          section10_piCoreIn_mono (G := G) F (by
            intro r hr
            simpa using hr ▸ hqσ)
        intro x hx
        have hxsingle : x ∈ piCoreIn ({q} : Set Nat.Primes) F := by
          simpa [section8_piCoreIn_singleton_eq_pCore_map q F] using
            hx
        exact hsingle_le_compl hxsingle
      intro x hx
      exact Subgroup.mem_comap.mpr
        (Subgroup.mem_sup_right (hcore_le_Z (by simpa [q] using hx)))
  intro x hxF
  let xF : F := ⟨x, hxF⟩
  have hxK : xF ∈ K :=
    hsup_le_K (htop_le_sup (Subgroup.mem_top xF))
  simpa [K, F, S, Z, Subgroup.mem_subgroupOf] using hxK

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_le_centralizer_sup_of_le_centralizers
    {R A B : Subgroup G}
    (hRA : R ≤ Subgroup.centralizer (A : Set G))
    (hRB : R ≤ Subgroup.centralizer (B : Set G)) :
    R ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro r hr
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  intro x hx
  rcases hx with hxA | hxB
  · exact Subgroup.mem_centralizer_iff.mp (hRA hr) x hxA
  · exact Subgroup.mem_centralizer_iff.mp (hRB hr) x hxB

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_le_centralizer_of_le_centralizer
    {A S : Subgroup G} (hSC : S ≤ Subgroup.centralizer (A : Set G)) :
    A ≤ Subgroup.centralizer (S : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact (Subgroup.mem_centralizer_iff.mp (hSC hs) a ha).symm

omit [IsMinCE G] in
private theorem CFSG.section10_pSubgroup_le_centralizer_piSubgroup_of_nilpotent_overgroup
    {π : Set Nat.Primes} {L P X : Subgroup G} {p : Nat.Primes}
    (hpπ : p ∉ π) (hLnil : Group.IsNilpotent L) (hPL : P ≤ L) (hXL : X ≤ L)
    (hPp : IsPGroup p.val P) (hXπ : IsPiSubgroup (G := G) π X) :
    P ≤ Subgroup.centralizer (X : Set G) := by
  classical
  have hXnil : Group.IsNilpotent X := by
    letI : Group.IsNilpotent L := hLnil
    let Xsub : Subgroup L := X.subgroupOf L
    have hXsub_nil : Group.IsNilpotent Xsub := by infer_instance
    let e : Xsub ≃* X := Subgroup.subgroupOfEquivOfLe (H := X) (K := L) hXL
    letI : Group.IsNilpotent Xsub := hXsub_nil
    exact Group.nilpotent_of_mulEquiv (G := Xsub) (G' := X) e
  letI : Group.IsNilpotent X := hXnil
  have htop_nil : Group.IsNilpotent (⊤ : Subgroup X) := by
    let e : X ≃* (⊤ : Subgroup X) :=
      (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).symm
    exact Group.nilpotent_of_mulEquiv (G := X) (G' := (⊤ : Subgroup X)) e
  have htop_le_sup :
      (⊤ : Subgroup X) ≤
        ⨆ q : (Nat.card X).primeFactors.attach, pCore q.1.1 X :=
    normal_nilpotent_le_sup_pCore
      (G := X) (N := (⊤ : Subgroup X)) (hN := inferInstance) htop_nil
  have hsup_le_cent :
      (⨆ q : (Nat.card X).primeFactors.attach, pCore q.1.1 X) ≤
        (Subgroup.centralizer (P : Set G)).comap X.subtype := by
    refine iSup_le ?_
    intro q0
    let q : Nat.Primes := ⟨q0.1.1, Nat.prime_of_mem_primeFactors q0.1.2⟩
    haveI : Fact q.val.Prime := ⟨q.2⟩
    have hqX : q.val ∣ Nat.card X := Nat.dvd_of_mem_primeFactors q0.1.2
    have hqπ : q ∈ π := hXπ q hqX
    have hpq : p ≠ q := by
      intro hpq
      exact hpπ (by simpa [hpq] using hqπ)
    let Q : Subgroup G := (pCore q.val X).map X.subtype
    have hQq : IsPGroup q.val Q := by
      exact IsPGroup.map (p := q.val) (H := pCore q.val X)
        (pCore_isPGroup (G := X) (p := q.val)) X.subtype
    have hQL : Q ≤ L := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨yX, _hyQ, rfl⟩
      exact hXL yX.2
    have hPcentQ : P ≤ Subgroup.centralizer (Q : Set G) :=
      section10_pSubgroup_le_centralizer_of_nilpotent_overgroup
        (G := G) hpq hLnil hPL hQL hPp hQq
    have hQcentP : Q ≤ Subgroup.centralizer (P : Set G) :=
      section10_le_centralizer_of_le_centralizer (G := G) hPcentQ
    intro x hx
    change ((x : X) : G) ∈ Subgroup.centralizer (P : Set G)
    exact hQcentP (Subgroup.mem_map_of_mem X.subtype (by simpa [q] using hx))
  have hXcentP : X ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    let xX : X := ⟨x, hx⟩
    have hxC : xX ∈ (Subgroup.centralizer (P : Set G)).comap X.subtype :=
      hsup_le_cent (htop_le_sup (Subgroup.mem_top xX))
    simpa [xX, Subgroup.mem_subgroupOf] using hxC
  exact section10_le_centralizer_of_le_centralizer (G := G) hXcentP

omit [IsMinCE G] in
public theorem CFSG.section10_isPiSubgroup_le_centralizer_of_nilpotent_disjoint
    {π ρ : Set Nat.Primes} {L A B : Subgroup G}
    (hπρ : Disjoint π ρ) (hLnil : Group.IsNilpotent L) (hAL : A ≤ L) (hBL : B ≤ L)
    (hAπ : IsPiSubgroup (G := G) π A) (hBρ : IsPiSubgroup (G := G) ρ B) :
    A ≤ Subgroup.centralizer (B : Set G) := by
  classical
  have hAnil : Group.IsNilpotent A := by
    letI : Group.IsNilpotent L := hLnil
    let Asub : Subgroup L := A.subgroupOf L
    have hAsub_nil : Group.IsNilpotent Asub := by infer_instance
    let e : Asub ≃* A := Subgroup.subgroupOfEquivOfLe (H := A) (K := L) hAL
    letI : Group.IsNilpotent Asub := hAsub_nil
    exact Group.nilpotent_of_mulEquiv (G := Asub) (G' := A) e
  letI : Group.IsNilpotent A := hAnil
  have htop_nil : Group.IsNilpotent (⊤ : Subgroup A) := by
    let e : A ≃* (⊤ : Subgroup A) :=
      (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).symm
    exact Group.nilpotent_of_mulEquiv (G := A) (G' := (⊤ : Subgroup A)) e
  have htop_le_sup :
      (⊤ : Subgroup A) ≤
        ⨆ q : (Nat.card A).primeFactors.attach, pCore q.1.1 A :=
    normal_nilpotent_le_sup_pCore
      (G := A) (N := (⊤ : Subgroup A)) (hN := inferInstance) htop_nil
  have hsup_le_cent :
      (⨆ q : (Nat.card A).primeFactors.attach, pCore q.1.1 A) ≤
        (Subgroup.centralizer (B : Set G)).comap A.subtype := by
    refine iSup_le ?_
    intro q0
    let q : Nat.Primes := ⟨q0.1.1, Nat.prime_of_mem_primeFactors q0.1.2⟩
    haveI : Fact q.val.Prime := ⟨q.2⟩
    have hqA : q.val ∣ Nat.card A := Nat.dvd_of_mem_primeFactors q0.1.2
    have hqπ : q ∈ π := hAπ q hqA
    have hqρ : q ∉ ρ := by
      rw [Set.disjoint_left] at hπρ
      exact hπρ hqπ
    let Q : Subgroup G := (pCore q.val A).map A.subtype
    have hQq : IsPGroup q.val Q := by
      exact IsPGroup.map (p := q.val) (H := pCore q.val A)
        (pCore_isPGroup (G := A) (p := q.val)) A.subtype
    have hQL : Q ≤ L := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨yA, _hyQ, rfl⟩
      exact hAL yA.2
    have hQcentB : Q ≤ Subgroup.centralizer (B : Set G) :=
      section10_pSubgroup_le_centralizer_piSubgroup_of_nilpotent_overgroup
        (G := G) hqρ hLnil hQL hBL hQq hBρ
    intro x hx
    change ((x : A) : G) ∈ Subgroup.centralizer (B : Set G)
    exact hQcentB (Subgroup.mem_map_of_mem A.subtype (by simpa [q] using hx))
  intro a ha
  let aA : A := ⟨a, ha⟩
  have haC : aA ∈ (Subgroup.centralizer (B : Set G)).comap A.subtype :=
    hsup_le_cent (htop_le_sup (Subgroup.mem_top aA))
  simpa [aA, Subgroup.mem_subgroupOf] using haC

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_ambientDerived_le_centralizer_of_cyclic_normal
    {M Z : Subgroup G} (hZleM : Z ≤ M)
    (hZnormM : (Z.subgroupOf M).Normal) (hZcyc : IsCyclic Z) :
    ambientDerivedSubgroup M ≤ Subgroup.centralizer (Z : Set G) := by
  classical
  let ZM : Subgroup M := Z.subgroupOf M
  haveI : ZM.Normal := hZnormM
  have hZMcyc : IsCyclic ZM :=
    (Subgroup.subgroupOfEquivOfLe (H := Z) (K := M) hZleM).isCyclic.2 hZcyc
  letI : IsCyclic ZM := hZMcyc
  let eAut : MulAut ZM ≃* (ZMod (Nat.card ZM))ˣ :=
    IsCyclic.mulAutMulEquiv (G := ZM)
  letI : CommGroup (MulAut ZM) :=
    MonoidHom.commGroupOfInjective eAut.toMonoidHom eAut.injective
  let φ : M →* MulAut ZM := MulAut.conjNormal (H := ZM)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rcases Subgroup.mem_map.mp hx with ⟨d, hd, rfl⟩
  let zM : M := ⟨z, hZleM hz⟩
  let zZM : ZM := ⟨zM, by simpa [ZM, zM, Subgroup.mem_subgroupOf] using hz⟩
  have hd_comm : (d : M) ∈ _root_.commutator M := by
    change (d : M) ∈ derivedSubgroup M
    exact hd
  have hd_ker : (d : M) ∈ φ.ker :=
    Abelianization.commutator_subset_ker φ hd_comm
  have hφd : φ d = 1 := by
    simpa [MonoidHom.mem_ker] using hd_ker
  have hfix : φ d zZM = zZM := by
    simp [hφd]
  have hconj : ((d : M) : G) * z * ((d : M) : G)⁻¹ = z := by
    have hval := congrArg (fun z : ZM => ((z : M) : G)) hfix
    simpa [φ, zZM, zM, ZM, MulAut.conjNormal_apply, MulAut.conj_apply,
      mul_assoc] using hval
  have hmul := congrArg (fun t : G => t * ((d : M) : G)) hconj
  simpa [mul_assoc] using hmul.symm

/-- Proposition 10.11(c). -/
public theorem CFSG.proposition_10_11_c
    {M K : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) (_hKle : K ≤ M)
    (hKσ : IsPiSubgroup (section10SigmaPrimes M)ᶜ K) :
    section10NormalIn
        ((subgroupCentralizerIn K (section10Msigma M)) ⊓ ambientDerivedSubgroup M) M ∧
      IsCyclic ↥((subgroupCentralizerIn K (section10Msigma M)) ⊓ ambientDerivedSubgroup M) := by
  classical
  let F : Subgroup G := section8FittingSubgroup M
  let Z : Subgroup G := piCoreIn (section10SigmaPrimes M)ᶜ F
  let C : Subgroup G := subgroupCentralizerIn K (section10Msigma M)
  let D : Subgroup G := C ⊓ ambientDerivedSubgroup M
  have hZleF : Z ≤ F := by
    simpa [Z, F] using
      piCoreIn_le (G := G) (section10SigmaPrimes M)ᶜ F
  have hZleM : Z ≤ M :=
    hZleF.trans (section8FittingSubgroup_le M)
  have hMnormZ : M ≤ Subgroup.normalizer (Z : Set G) := by
    simpa [Z, F] using section10_le_normalizer_sigma_compl_fitting_core (G := G) M
  have hZnormM : (Z.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZleM).mpr hMnormZ
  have hZcyc : IsCyclic Z := by
    simpa [Z, F] using section10_sigma_compl_fitting_core_isCyclic (G := G) hM
  have hDleC : D ≤ C := inf_le_left
  have hDleK : D ≤ K :=
    hDleC.trans (by intro x hx; exact hx.1)
  have hDleM : D ≤ M :=
    inf_le_right.trans section10_ambientDerivedSubgroup_le_base
  have hDπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ D := by
    intro p hp
    exact hKσ p (hp.trans (Subgroup.card_dvd_of_le hDleK))
  have hDcentS : D ≤ Subgroup.centralizer (section10Msigma M : Set G) := by
    intro x hx
    exact (hDleC hx).2
  have hDcentZ : D ≤ Subgroup.centralizer (Z : Set G) :=
    (inf_le_right : D ≤ ambientDerivedSubgroup M).trans <|
      section10_ambientDerived_le_centralizer_of_cyclic_normal
        (G := G) hZleM hZnormM hZcyc
  have hDcentSup :
      D ≤ Subgroup.centralizer ((section10Msigma M ⊔ Z : Subgroup G) : Set G) :=
    section10_le_centralizer_sup_of_le_centralizers hDcentS hDcentZ
  have hFleSup : F ≤ section10Msigma M ⊔ Z := by
    simpa [F, Z] using
      section10_fitting_le_msigma_sup_sigma_compl_fitting_core (G := G) M
  have hDcentF : D ≤ Subgroup.centralizer (F : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro f hfF
    exact Subgroup.mem_centralizer_iff.mp (hDcentSup hx) f (hFleSup hfF)
  have hDleF : D ≤ F := by
    have hMsolv : IsSolvable M :=
      IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
    intro x hxD
    let xM : M := ⟨x, hDleM hxD⟩
    have hxCentLocal : xM ∈ Subgroup.centralizer (fittingSubgroup M : Set M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have hfG : ((f : M) : G) ∈ F := by
        change ((f : M) : G) ∈ (fittingSubgroup M).map M.subtype
        exact Subgroup.mem_map_of_mem M.subtype hf
      have hcommG :=
        Subgroup.mem_centralizer_iff.mp (hDcentF hxD) ((f : M) : G) hfG
      exact Subtype.ext hcommG
    have hxFit : xM ∈ fittingSubgroup M :=
      centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
        (G := M) hMsolv hxCentLocal
    change x ∈ (fittingSubgroup M).map M.subtype
    exact Subgroup.mem_map.mpr ⟨xM, hxFit, rfl⟩
  have hF_norm_D : F ≤ Subgroup.normalizer (D : Set G) := by
    exact
      (section10_le_centralizer_of_le_centralizer hDcentF).trans
        (centralizer_le_normalizer D)
  have hDnormF : (D.subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDleF).mpr hF_norm_D
  have hDleZ : D ≤ Z :=
    section8_le_piCoreIn_of_normal_isPiSubgroup
      (G := G) (π := (section10SigmaPrimes M)ᶜ) (K := D) (H := F)
      hDleF hDnormF hDπ
  have hDcyc : IsCyclic D := by
    letI : IsCyclic Z := hZcyc
    exact Subgroup.isCyclic_of_le hDleZ
  have hDnormM : section10NormalIn D M := by
    let DZ : Subgroup Z := D.subgroupOf Z
    haveI : IsCyclic Z := hZcyc
    have hDZchar : DZ.Characteristic :=
      section10_characteristic_of_subgroup_of_isCyclic_pre (K := DZ)
    letI : DZ.Characteristic := hDZchar
    have hnormZ_le_normD :
        Subgroup.normalizer (Z : Set G) ≤ Subgroup.normalizer (D : Set G) := by
      have hnorm :=
        section10_normalizer_le_normalizer_map_subtype_of_characteristic_pre
          (G := G) Z DZ
      have hmap_eq : (DZ.map Z.subtype : Subgroup G) = D := by
        calc
          (DZ.map Z.subtype : Subgroup G) = D ⊓ Z := by
            simp [DZ]
          _ = D := inf_eq_left.mpr hDleZ
      simpa [hmap_eq] using hnorm
    exact section10_normalIn_of_le_normalizer (by simpa [D] using hDleM)
      (hMnormZ.trans hnormZ_le_normD)
  exact ⟨by simpa [D, C] using hDnormM, by simpa [D, C] using hDcyc⟩

end Section10
