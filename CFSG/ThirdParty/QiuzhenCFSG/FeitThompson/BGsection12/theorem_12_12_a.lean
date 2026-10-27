module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_11_c

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# theorem_12_12_a
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [IsMinCE G] in
public theorem CFSG.section12_piSubgroup_le_normal_hall
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes}
    {H A : Subgroup R} [H.Normal]
    (hHall : IsHallSubgroup π H) (hAπ : IsPiSubgroup (G := R) π A) :
    A ≤ H := by
  classical
  rw [← QuotientGroup.ker_mk' H]
  rw [← Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' H) (H := A)]
  apply Subgroup.card_eq_one.mp
  apply section12_card_eq_one_of_no_prime_dvd
  intro p hpdiv
  have hpmap : p ∈ subgroupPrimeSet (A.map (QuotientGroup.mk' H)) := hpdiv
  have hpπ : p ∈ π :=
    (section12_isPiSubgroup_map hAπ (QuotientGroup.mk' H)) p hpmap
  have hp_dvd_quot :
      p.val ∣ Nat.card (R ⧸ H) :=
    hpdiv.trans (Subgroup.card_subgroup_dvd_card (A.map (QuotientGroup.mk' H)))
  have hp_dvd_index : p.val ∣ H.index := by
    simpa [Subgroup.index_eq_card] using hp_dvd_quot
  exact (hHall.p_in_pi_of_p_dvd_index p hp_dvd_index) hpπ

public theorem CFSG.section12_exists_isCompl_isInvariant_of_elementaryAbelian_coprime
    {V A : Type*} [Group V] [Finite V] {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p V] [Group A] [Finite A] [MulDistribMulAction A V]
    (hcop : Nat.Coprime p (Nat.card A)) (B : Subgroup V) [IsInvariant A V B] :
    ∃ C : Subgroup V, IsCompl B C ∧ IsInvariant A V C := by
  classical
  letI : CommGroup V := IsMulCommutative.instCommGroup
  let ρ : Representation (ZMod p) A (Additive V) :=
    Theory.Representation.ofElementaryAbelianAction (A := A) (G := V) (p := p)
  let instAdd : AddCommGroup ρ.asModule := Representation.instAddCommGroupAsModule ρ
  letI : AddCommGroup ρ.asModule := instAdd
  let instMod : Module (MonoidAlgebra (ZMod p) A) ρ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule ρ
  letI : Module (MonoidAlgebra (ZMod p) A) ρ.asModule := instMod
  let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  have hBinv : η B ∈ ρ.invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    have hxB : Additive.toMul x ∈ B := by simpa [η] using hx
    simpa [ρ, η] using
      (IsInvariant.invariant (A := A) (G := V) (H := B) a (Additive.toMul x)).1 hxB
  let Bpack : ρ.invtSubmodule := ⟨η B, hBinv⟩
  haveI : Fintype A := Fintype.ofFinite A
  haveI : NeZero (Fintype.card A : ZMod p) := by
    constructor
    intro hzero
    have hdiv : p ∣ Fintype.card A :=
      (ZMod.natCast_eq_zero_iff (Fintype.card A) p).1 hzero
    have hnot : ¬ p ∣ Fintype.card A := by
      exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd).1
        (by simpa [Nat.card_eq_fintype_card] using hcop)
    exact hnot hdiv
  let Bmod : @Submodule (MonoidAlgebra (ZMod p) A) ρ.asModule _
      instAdd.toAddCommMonoid instMod :=
    ρ.mapSubmodule Bpack
  obtain ⟨Cmod, hBCmod⟩ := @MonoidAlgebra.Submodule.exists_isCompl'
    (ZMod p) inferInstance A inferInstance inferInstance ρ.asModule instAdd instMod inferInstance Bmod
  let Cpack : ρ.invtSubmodule := ρ.mapSubmodule.symm Cmod
  let C : Subgroup V := η.symm (Cpack : Submodule (ZMod p) (Additive V))
  have hCinv : IsInvariant A V C := by
    refine ⟨?_⟩
    intro a v
    constructor
    · intro hv
      have hvC : Additive.ofMul v ∈ (Cpack : Submodule (ZMod p) (Additive V)) := by
        simpa [C, η] using hv
      have hmem := (Representation.mem_invtSubmodule (ρ := ρ)).1 Cpack.2 a
      have hsmul :=
        (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (ρ a)).1 hmem
          (Additive.ofMul v) hvC
      simpa [ρ, C, η] using hsmul
    · intro hv
      have hvC : Additive.ofMul (a • v) ∈ (Cpack : Submodule (ZMod p) (Additive V)) := by
        simpa [C, η] using hv
      have hmem := (Representation.mem_invtSubmodule (ρ := ρ)).1 Cpack.2 a⁻¹
      have hsmul :=
        (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (ρ a⁻¹)).1 hmem
          (Additive.ofMul (a • v)) hvC
      simpa [ρ, C, η, inv_smul_smul] using hsmul
  refine ⟨C, ?_, hCinv⟩
  have hcompl_sub : IsCompl (η B) (η C) := by
    have hcompl_pack : IsCompl Bpack Cpack := by
      exact (ρ.mapSubmodule.isCompl_iff).2 (by simpa [Bmod, Cpack] using hBCmod)
    rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hcompl_pack ⊢
    constructor
    · simpa [Bpack, Cpack, C] using congrArg Subtype.val hcompl_pack.1
    · simpa [Bpack, Cpack, C] using congrArg Subtype.val hcompl_pack.2
  exact (OrderIso.isCompl_iff (f := η) (x := B) (y := C)).2 hcompl_sub

public theorem CFSG.section12_E2_isPGroup_of_tau2_singleton
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    IsPGroup p.val E₂ := by
  classical
  have hτ2_single : section12Tau2Primes M = {p} :=
    theorem_12_7_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  have hE2HallIn :
      section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
    section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
  rcases hE2HallIn with ⟨hE2E, hHallE2⟩
  apply section12_isPGroup_of_isPiSubgroup_singleton
  intro q hqdiv
  have hqdiv_sub : q.val ∣ Nat.card (E₂.subgroupOf E) := by
    simpa [section12_card_subgroupOf_eq hE2E] using hqdiv
  have hqτ2 : q ∈ section12Tau2Primes M :=
    hHallE2.p_in_pi_of_p_dvd_card q hqdiv_sub
  have hq_single : q ∈ ({p} : Set Nat.Primes) := by
    simpa [hτ2_single] using hqτ2
  simpa using hq_single

public theorem CFSG.section12_CA_msigma_le_E2_of_tau2
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    subgroupCentralizerIn A (section10Msigma M) ≤ E₂ :=
  inf_le_left.trans (section12_rankTwo_tau2_le_E2 hM hE hp hA)

private theorem CFSG.section12_E2_commutative_of_tau2_nonabelian
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    IsMulCommutative E₂ := by
  classical
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  have hE2_p : IsPGroup p.val E₂ :=
    section12_E2_isPGroup_of_tau2_singleton
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  have hE2HallIn :
      section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
    section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
  rcases hE2HallIn with ⟨hE2E, _hHallE2⟩
  let E₂sub : Subgroup M := E₂.subgroupOf M
  have hE2_le_M : E₂ ≤ M := hE2E.trans hE.1.2.1
  have hE2sub_p : IsPGroup p.val E₂sub :=
    hE2_p.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := E₂) (K := M) hE2_le_M).symm
  obtain ⟨T, hE2sub_le_T⟩ :=
    IsPGroup.exists_le_sylow (G := M) (p := p.val) hE2sub_p
  have hTcomm : IsMulCommutative (T : Subgroup M) :=
    (theorem_12_5_b hM hp hA_M).1 T
  have hTamb_comm : IsMulCommutative (section10AmbientSylowSubgroup M T) := by
    letI : IsMulCommutative (T : Subgroup M) := hTcomm
    change IsMulCommutative ((T : Subgroup M).map M.subtype)
    exact Subgroup.map_isMulCommutative
      (f := M.subtype) (H := (T : Subgroup M))
  have hE2_amb_le_T : E₂ ≤ section10AmbientSylowSubgroup M T := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hE2_le_M hx⟩,
        hE2sub_le_T (by simpa [E₂sub, Subgroup.mem_subgroupOf] using hx), rfl⟩
  refine ⟨⟨fun x y => ?_⟩⟩
  exact Subtype.ext <|
    setLike_mul_comm
      (s := section10AmbientSylowSubgroup M T)
      (hE2_amb_le_T x.property) (hE2_amb_le_T y.property)

public theorem CFSG.section12_E2_le_centralizer_rankTwo_tau2_of_theorem_12_7
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    E₂ ≤ Subgroup.centralizer (A : Set G) := by
  classical
  have hA_le_E2 : A ≤ E₂ :=
    section12_rankTwo_tau2_le_E2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hM hE hp hA
  have hE2comm : IsMulCommutative E₂ :=
    section12_E2_commutative_of_tau2_nonabelian
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hM hE hp hA hSylow
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (setLike_mul_comm
    (s := E₂) hx (hA_le_E2 ha)).symm

private theorem CFSG.section12_global_sylow_not_le_M_of_nonabelian
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    {S : Sylow p.val G} (hSnonab : ¬ IsMulCommutative (S : Subgroup G)) :
    ¬ (S : Subgroup G) ≤ M := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  intro hSleM
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  let Ssub : Subgroup M := (S : Subgroup G).subgroupOf M
  have hSsub_p : IsPGroup p.val Ssub :=
    S.isPGroup'.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := (S : Subgroup G)) (K := M) hSleM).symm
  have hp_not_dvd_Ssub_index : ¬ p.val ∣ Ssub.index := by
    have hmap_eq : Ssub.map M.subtype = (S : Subgroup G) := by
      simpa [Ssub] using Subgroup.map_subgroupOf_eq_of_le hSleM
    have hidx : (S : Subgroup G).index = Ssub.index * M.index := by
      rw [← hmap_eq]
      simpa [Ssub] using Subgroup.index_map_subtype (K := Ssub)
    intro hdiv
    exact S.not_dvd_index (by
      rw [hidx]
      exact dvd_mul_of_dvd_left hdiv _)
  let SM : Sylow p.val M := IsPGroup.toSylow (p := p.val) hSsub_p hp_not_dvd_Ssub_index
  have hSMcomm : IsMulCommutative (SM : Subgroup M) :=
    (theorem_12_5_b hM hp hA_M).1 SM
  have hScomm : IsMulCommutative (S : Subgroup G) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    have hxsub : (⟨(x : G), hSleM x.property⟩ : M) ∈ (SM : Subgroup M) := by
      simp [SM, Ssub, IsPGroup.toSylow_coe, Subgroup.mem_subgroupOf]
    have hysub : (⟨(y : G), hSleM y.property⟩ : M) ∈ (SM : Subgroup M) := by
      simp [SM, Ssub, IsPGroup.toSylow_coe, Subgroup.mem_subgroupOf]
    apply Subtype.ext
    exact congrArg (fun z : M => (z : G)) <|
      setLike_mul_comm
        (s := (SM : Subgroup M)) hxsub hysub
  exact hSnonab hScomm

omit [IsMinCE G] in
public theorem CFSG.section12_le_unique_maximal_of_le
    {Y X M : Subgroup G} (hYX : Y ≤ X) (hXproper : X ≠ ⊤)
    (hMuniq : section9MaximalSubgroupsContaining Y = {M}) :
    X ≤ M := by
  classical
  rcases eq_top_or_exists_le_coatom X with hXtop | ⟨N, hNcoatom, hXN⟩
  · exact False.elim (hXproper hXtop)
  have hNmax : N ∈ section9MaximalSubgroups G := hNcoatom
  have hNcont : N ∈ section9MaximalSubgroupsContaining Y := ⟨hNmax, hYX.trans hXN⟩
  have hNM : N = M := by
    have hNsingle : N ∈ ({M} : Set (Subgroup G)) := by
      simpa [hMuniq] using hNcont
    simpa using hNsingle
  simpa [hNM] using hXN

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_omegaOneCenter_centralizes
    {p : Nat.Primes} (P : Subgroup G) :
    section10OmegaOneCenter p P ≤ Subgroup.centralizer (P : Set G) := by
  intro z hz
  rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
  rcases Subgroup.mem_map.mp hy with ⟨c, _hc, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hxP
  simpa using congrArg Subtype.val ((Subgroup.mem_center_iff.mp c.property) ⟨x, hxP⟩)

private theorem CFSG.section12_centralizer_le_M_of_msigma_fixed_primeOrder_tau2
    {M E E₁₂ E₁ E₂ E₃ A X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A)
    (hCX : subgroupCentralizerIn (section10Msigma M) X ≠ ⊥) :
    Subgroup.centralizer (X : Set G) ≤ M := by
  classical
  have huniq :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} :=
    corollary_12_6_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA X hX hCX
  have hCproper : Subgroup.centralizer (X : Set G) ≠ ⊤ := by
    intro hCtop
    have htop_le_norm :
        (⊤ : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := by
      simpa [hCtop] using (centralizer_le_normalizer X)
    exact section12_normalizer_ne_top_of_ne_bot_ne_top
      (section12_primeOrder_ne_bot hX) (section12_primeOrder_ne_top hX)
      (top_le_iff.mp htop_le_norm)
  exact section12_le_unique_maximal_of_le (Y := Subgroup.centralizer (X : Set G))
    (X := Subgroup.centralizer (X : Set G)) (M := M) le_rfl hCproper huniq

private theorem CFSG.section12_CA_msigma_ne_omegaOneCenter_of_tau2
    {M E E₁₂ E₁ E₂ E₃ A P : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (_hPnonab : ¬ IsMulCommutative P)
    (hPnotM : ¬ P ≤ M)
    (hCcard : Nat.card (subgroupCentralizerIn A (section10Msigma M)) = p.val) :
    subgroupCentralizerIn A (section10Msigma M) ≠ section10OmegaOneCenter p P := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  have hCprime : C ∈ section10PrimeOrderSubgroupsIn p A := by
    exact ⟨inf_le_left, by simpa [C] using hCcard⟩
  have hσ_le_centC : section10Msigma M ≤ Subgroup.centralizer (C : Set G) := by
    simpa [C] using section12_subgroupCentralizerIn_commute A (section10Msigma M)
  have hCσ_ne_bot : subgroupCentralizerIn (section10Msigma M) C ≠ ⊥ := by
    intro hbot
    have hσ_le_bot : section10Msigma M ≤ ⊥ := by
      intro s hs
      have hsC : s ∈ subgroupCentralizerIn (section10Msigma M) C := ⟨hs, hσ_le_centC hs⟩
      simpa [hbot] using hsC
    exact (theorem_10_2_e (G := G) hM) (le_bot_iff.mp hσ_le_bot)
  intro hCeq
  have hP_le_centC : P ≤ Subgroup.centralizer (C : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcΩ : c ∈ section10OmegaOneCenter p P := by
      simpa [C, hCeq] using hc
    exact (Subgroup.mem_centralizer_iff.mp
      (section12_omegaOneCenter_centralizes (G := G) (p := p) P hcΩ) x hx).symm
  have hCentC_le_M :
      Subgroup.centralizer (C : Set G) ≤ M :=
    section12_centralizer_le_M_of_msigma_fixed_primeOrder_tau2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (X := C) (p := p)
      hM hE hp hA hCprime hCσ_ne_bot
  exact hPnotM (hP_le_centC.trans hCentC_le_M)

private theorem CFSG.section12_E1_le_normalizer_E2
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    E₁ ≤ Subgroup.normalizer (E₂ : Set G) := by
  classical
  have h12 := lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
    (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE
  have hE1_le_E12 : E₁ ≤ E₁₂ := hE.2.2.1.1
  have hE12_norm_E2 : E₁₂ ≤ Subgroup.normalizer (E₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h12.2.2.2.1).1 h12.2.2.2.2
  exact hE1_le_E12.trans hE12_norm_E2

private theorem CFSG.section12_isInvariant_map_quotient_local
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    {N : Subgroup G} [N.Normal] [IsInvariant A G N]
    (H : Subgroup G) [IsInvariant A G H] :
    letI : MulDistribMulAction A (G ⧸ N) :=
      quotientMulDistribMulAction (A := A) (G := G) N inferInstance
    IsInvariant A (G ⧸ N) (H.map (QuotientGroup.mk' N)) := by
  letI : MulDistribMulAction A (G ⧸ N) :=
    quotientMulDistribMulAction (A := A) (G := G) N inferInstance
  refine ⟨?_⟩
  intro a q
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨a • g, (IsInvariant.invariant (A := A) (G := G) (H := H) a g).1 hg, ?_⟩
    simp [MulAction.Quotient.smul_mk]
  · rintro ⟨g, hg, hq⟩
    refine ⟨a⁻¹ • g, (IsInvariant.invariant (A := A) (G := G) (H := H) a⁻¹ g).1 hg, ?_⟩
    have hsmul := congrArg (fun z : G ⧸ N => a⁻¹ • z) hq
    simpa [MulAction.Quotient.smul_mk, inv_smul_smul] using hsmul

private theorem CFSG.section12_isInvariant_comap_quotient_local
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    {N : Subgroup G} [N.Normal] [IsInvariant A G N]
    (H : Subgroup (G ⧸ N))
    [MulDistribMulAction A (G ⧸ N)] [IsInvariant A (G ⧸ N) H]
    (hq : ∀ a : A, ∀ g : G,
      a • ((QuotientGroup.mk' N) g) = (QuotientGroup.mk' N) (a • g)) :
    IsInvariant A G (H.comap (QuotientGroup.mk' N)) := by
  refine ⟨?_⟩
  intro a g
  constructor
  · intro hg
    change (QuotientGroup.mk' N) (a • g) ∈ H
    rw [← hq a g]
    exact (IsInvariant.invariant (A := A) (G := G ⧸ N) (H := H) a
      ((QuotientGroup.mk' N) g)).1 hg
  · intro hg
    change (QuotientGroup.mk' N) g ∈ H
    have hg' : a⁻¹ • ((QuotientGroup.mk' N) (a • g)) ∈ H :=
      (IsInvariant.invariant (A := A) (G := G ⧸ N) (H := H) a⁻¹
        ((QuotientGroup.mk' N) (a • g))).1 hg
    simpa [hq, inv_smul_smul] using hg'

public theorem CFSG.section12_CA_msigma_split_E2_cyclic_factor
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    ∃ Z : Subgroup G,
      Z ≤ E₂ ∧ IsCyclic Z ∧
        Disjoint (subgroupCentralizerIn A (section10Msigma M)) Z ∧
        E₂ = subgroupCentralizerIn A (section10Msigma M) ⊔ Z := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  haveI : Fact p.val.Prime := ⟨p.2⟩
  have hE₂p : IsPGroup p.val E₂ :=
    section12_E2_isPGroup_of_tau2_singleton
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  obtain ⟨S, hE₂S⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hE₂p
  have hSnonab : ¬ IsMulCommutative (S : Subgroup G) := by
    intro hScomm
    rcases hSylow with ⟨Sbad, hSbad_noncomm⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Sbad
    have hconj_comm : IsMulCommutative ((g • S : Sylow p.val G) : Subgroup G) := by
      letI : IsMulCommutative (S : Subgroup G) := hScomm
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.map_isMulCommutative
        (f := (MulAut.conj g).toMonoidHom) (H := (S : Subgroup G))
    have hSbad_comm : IsMulCommutative (Sbad : Subgroup G) := by
      rw [← hg]
      exact hconj_comm
    exact hSbad_noncomm hSbad_comm
  have hA_le_E₂ : A ≤ E₂ :=
    section12_rankTwo_tau2_le_E2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hM hE hp hA
  have hA_le_S : A ≤ (S : Subgroup G) := hA_le_E₂.trans hE₂S
  have hCcard : Nat.card C = p.val := by
    simpa [C] using (theorem_12_7_b
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow).1
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  have hAmaxG : A ∈ maximalElementaryAbelianSubgroups p.val G :=
    (lemma_12_1_g (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA_M).1
  have hA10 : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G := by
    simpa [section10RankTwoMaximalElementaryAbelianSubgroups] using
      (⟨section12_rankTwo_elementary hA, hAmaxG⟩ :
        A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G ∧
          A ∈ maximalElementaryAbelianSubgroups p.val G)
  have hpG : p ∈ subgroupPrimeSet (⊤ : Subgroup G) := by
    exact (section12_rankTwo_prime_mem hA).trans
      (Subgroup.card_dvd_of_le (show E ≤ (⊤ : Subgroup G) from le_top))
  have hCprime : C ∈ section10PrimeOrderSubgroupsIn p A := by
    exact ⟨inf_le_left, by simpa [C] using hCcard⟩
  have hSnotM : ¬ (S : Subgroup G) ≤ M :=
    section12_global_sylow_not_le_M_of_nonabelian
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSnonab
  have hCneOmega : C ≠ section10OmegaOneCenter p (S : Subgroup G) := by
    simpa [C] using
      section12_CA_msigma_ne_omegaOneCenter_of_tau2
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (P := (S : Subgroup G)) (p := p)
        hM hE hp hA hSnonab hSnotM hCcard
  obtain ⟨Z, _hΩZ, hZcyc, hCdisjZ, hCS_eq⟩ :=
    lemma_10_13_b (G := G) (p := p) (A := A) (P := (S : Subgroup G))
      (A₀ := C) hpG hA10 S.isPGroup' hSnonab hA_le_S hCprime hCneOmega
  have hE₂_le_centA : E₂ ≤ Subgroup.centralizer (A : Set G) :=
    section12_E2_le_centralizer_rankTwo_tau2_of_theorem_12_7
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  have hE₂_le_CS : E₂ ≤ subgroupCentralizerIn (S : Subgroup G) A := by
    intro x hx
    exact ⟨hE₂S hx, hE₂_le_centA hx⟩
  have hCS_le_E : subgroupCentralizerIn (S : Subgroup G) A ≤ E := by
    have h6 :=
      corollary_12_6_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA
    exact inf_le_right.trans (by simpa [h6.2.1] using h6.1)
  have hCS_le_E₂ : subgroupCentralizerIn (S : Subgroup G) A ≤ E₂ := by
    let K : Subgroup E := (subgroupCentralizerIn (S : Subgroup G) A).subgroupOf E
    have hCS_p : IsPGroup p.val (subgroupCentralizerIn (S : Subgroup G) A) :=
      IsPGroup.to_le S.isPGroup' inf_le_left
    have hKp : IsPGroup p.val K :=
      hCS_p.of_equiv
        (Subgroup.subgroupOfEquivOfLe
          (H := subgroupCentralizerIn (S : Subgroup G) A) (K := E) hCS_le_E).symm
    have hE2HallIn :
        section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
      section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
    rcases hE2HallIn with ⟨hE2E, hHallE2E⟩
    let E₂sub : Subgroup E := E₂.subgroupOf E
    have hE₂sub_p : IsPGroup p.val E₂sub :=
      hE₂p.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := E₂) (K := E) hE2E).symm
    have hp_not_dvd_E₂sub_index : ¬ p.val ∣ E₂sub.index := by
      intro hpidx
      exact (hHallE2E.p_in_pi_of_p_dvd_index p hpidx) hp
    let P : Sylow p.val E := IsPGroup.toSylow (p := p.val) hE₂sub_p hp_not_dvd_E₂sub_index
    have hP_eq_E₂sub : (P : Subgroup E) = E₂sub := by
      simp [P, E₂sub, IsPGroup.toSylow_coe]
    have hP_le_K : (P : Subgroup E) ≤ K := by
      rw [hP_eq_E₂sub]
      intro x hx
      change (x : G) ∈ subgroupCentralizerIn (S : Subgroup G) A
      exact hE₂_le_CS (by simpa [E₂sub, Subgroup.mem_subgroupOf] using hx)
    have hK_eq_P : K = (P : Subgroup E) :=
      P.is_maximal' hKp hP_le_K
    intro x hx
    have hxE : x ∈ E := hCS_le_E hx
    let xE : E := ⟨x, hxE⟩
    have hxK : xE ∈ K := by
      simpa [K, xE, Subgroup.mem_subgroupOf] using hx
    have hxE₂sub : xE ∈ E₂sub := by
      simpa [hK_eq_P, hP_eq_E₂sub] using hxK
    simpa [E₂sub, xE, Subgroup.mem_subgroupOf] using hxE₂sub
  have hCS_eq_E₂ : subgroupCentralizerIn (S : Subgroup G) A = E₂ :=
    le_antisymm hCS_le_E₂ hE₂_le_CS
  refine ⟨Z, ?_, hZcyc, by simpa [C] using hCdisjZ, ?_⟩
  · exact le_sup_right.trans (by
      rw [← hCS_eq, hCS_eq_E₂])
  · calc
      E₂ = subgroupCentralizerIn (S : Subgroup G) A := hCS_eq_E₂.symm
      _ = C ⊔ Z := hCS_eq
      _ = subgroupCentralizerIn A (section10Msigma M) ⊔ Z := by simp [C]

private theorem CFSG.section12_CA_msigma_not_le_frattini_E2
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    ¬ (subgroupCentralizerIn A (section10Msigma M)).subgroupOf E₂ ≤ frattini E₂ := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  intro hCΦ
  obtain ⟨Z, hZE₂, _hZcyc, hdisj, hE₂eq⟩ :=
    section12_CA_msigma_split_E2_cyclic_factor
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  have hCE₂ : C ≤ E₂ := by
    simpa [C] using
      section12_CA_msigma_le_E2_of_tau2
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA
  let C₂ : Subgroup E₂ := C.subgroupOf E₂
  let Z₂ : Subgroup E₂ := Z.subgroupOf E₂
  have hCZ_top : C₂ ⊔ Z₂ = ⊤ := by
    calc
      C₂ ⊔ Z₂ = (C ⊔ Z).subgroupOf E₂ := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := C) (A' := Z) (B := E₂) hCE₂ hZE₂
      _ = ⊤ := by
        apply Subgroup.subgroupOf_eq_top.2
        simpa [C] using le_of_eq hE₂eq
  have hZΦ_top : Z₂ ⊔ frattini E₂ = ⊤ := by
    apply le_antisymm le_top
    rw [← hCZ_top]
    exact sup_le
      (show C₂ ≤ Z₂ ⊔ frattini E₂ from
        (show C₂ ≤ frattini E₂ from by simpa [C₂, C] using hCΦ).trans le_sup_right)
      le_sup_left
  haveI : Fact p.val.Prime := ⟨p.2⟩
  have hE₂p : IsPGroup p.val E₂ :=
    section12_E2_isPGroup_of_tau2_singleton
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  haveI : Fact (IsPGroup p.val E₂) := ⟨hE₂p⟩
  have hZ₂top : Z₂ = ⊤ :=
    lemma_1_7_a (R := E₂) (p := p.val) (H := Z₂) hZΦ_top
  have hC_le_Z : C ≤ Z := by
    intro c hc
    have hcE₂ : c ∈ E₂ := hCE₂ hc
    let c₂ : E₂ := ⟨c, hcE₂⟩
    have hcZ₂ : c₂ ∈ Z₂ := by
      simp [hZ₂top]
    simpa [Z₂, c₂, Subgroup.mem_subgroupOf] using hcZ₂
  have hCbot : C = ⊥ := by
    apply le_bot_iff.mp
    intro c hc
    exact Subgroup.disjoint_def.mp hdisj hc (hC_le_Z hc)
  have hCcard := (theorem_12_7_b
    (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
    (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
    hM hE hp hA hSylow).1
  have hp_one : p.val = 1 := by
    simpa [C, hCbot] using hCcard.symm
  exact p.2.ne_one hp_one

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_coprime_card_E1_tau2
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (_hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (_hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    Nat.Coprime p.val (Nat.card E₁) := by
  classical
  rcases hE with ⟨_hcomp, _hE12, hE1, _hE2, _hE3⟩
  rcases hE1 with ⟨hE1E12, hHallE1⟩
  refine (p.property.coprime_iff_not_dvd).2 ?_
  intro hpdiv
  have hpdiv_sub : p.val ∣ Nat.card (E₁.subgroupOf E₁₂) := by
    simpa [section12_card_subgroupOf_eq hE1E12] using hpdiv
  have hpτ1 : p ∈ section12Tau1Primes M :=
    hHallE1.p_in_pi_of_p_dvd_card p hpdiv_sub
  have h1 : primeRank p.val M = 1 := hpτ1.2.2
  have h2 : primeRank p.val M = 2 := hp.2
  omega

private theorem CFSG.section12_E1_invariant_CA_msigma_subgroupOf_E2
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    letI : Subgroup.Normalizes E₁ E₂ :=
      ⟨section12_E1_le_normalizer_E2 (G := G) (M := M) hM hE⟩
    IsInvariant E₁ E₂
      ((subgroupCentralizerIn A (section10Msigma M)).subgroupOf E₂) := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  letI : Subgroup.Normalizes E₁ E₂ :=
    ⟨section12_E1_le_normalizer_E2 (G := G) (M := M) hM hE⟩
  have hAnorm : section10NormalIn A E :=
    (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA).1
  have hCnormE : section10NormalIn C E := by
    simpa [C] using
      section12_CA_msigma_normalIn_E (G := G) (M := M) (E := E)
        (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A)
        hE hAnorm
  have hE_norm_C : E ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCnormE.1).1 hCnormE.2
  have hE₁E : E₁ ≤ E := hE.2.2.1.1.trans hE.2.1.1
  refine ⟨?_⟩
  intro a x
  have ha_norm_C : (a : G) ∈ Subgroup.normalizer (C : Set G) :=
    hE_norm_C (hE₁E a.property)
  simpa [C, Subgroup.mem_subgroupOf,
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
      (Subgroup.mem_normalizer_iff.mp ha_norm_C (x : G))

public theorem CFSG.section12_CA_msigma_complement_in_E2
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    ∃ P₀ : Subgroup G,
      P₀ ≤ E₂ ∧
        E₂ = subgroupCentralizerIn A (section10Msigma M) ⊔ P₀ ∧
        Disjoint (subgroupCentralizerIn A (section10Msigma M)) P₀ ∧
        E₁ ≤ Subgroup.normalizer (P₀ : Set G) := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  have hCE₂ : C ≤ E₂ := by
    simpa [C] using
      section12_CA_msigma_le_E2_of_tau2
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA
  let C₂ : Subgroup E₂ := C.subgroupOf E₂
  let Φ : Subgroup E₂ := frattini E₂
  let q : E₂ →* E₂ ⧸ Φ := QuotientGroup.mk' Φ
  haveI : Fact p.val.Prime := ⟨p.2⟩
  have hE₂p : IsPGroup p.val E₂ :=
    section12_E2_isPGroup_of_tau2_singleton
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  haveI : Fact (IsPGroup p.val E₂) := ⟨hE₂p⟩
  letI : Subgroup.Normalizes E₁ E₂ :=
    ⟨section12_E1_le_normalizer_E2 (G := G) (M := M) hM hE⟩
  have hΦinv : IsInvariant E₁ E₂ Φ := by
    simpa [Φ] using isInvariant_of_characteristic (A := E₁) (G := E₂) (frattini E₂)
  letI : IsInvariant E₁ E₂ Φ := hΦinv
  haveI : Φ.Normal := by
    simpa [Φ] using (inferInstance : (frattini E₂).Normal)
  letI : MulDistribMulAction E₁ (E₂ ⧸ Φ) :=
    quotientMulDistribMulAction (A := E₁) (G := E₂) Φ hΦinv
  have hC₂inv : IsInvariant E₁ E₂ C₂ := by
    simpa [C₂, C] using
      section12_E1_invariant_CA_msigma_subgroupOf_E2
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA
  letI : IsInvariant E₁ E₂ C₂ := hC₂inv
  let B : Subgroup (E₂ ⧸ Φ) := C₂.map q
  have hBinv : IsInvariant E₁ (E₂ ⧸ Φ) B := by
    simpa [B, q] using
      section12_isInvariant_map_quotient_local
        (A := E₁) (G := E₂) (N := Φ) (H := C₂)
  letI : IsInvariant E₁ (E₂ ⧸ Φ) B := hBinv
  have hVelem : IsElementaryAbelian p.val (E₂ ⧸ Φ) := by
    simpa [Φ] using isElementaryAbelian_quotient_frattini (R := E₂) (p := p.val)
  letI : IsElementaryAbelian p.val (E₂ ⧸ Φ) := hVelem
  obtain ⟨Q, hBQ, hQinv⟩ :=
    section12_exists_isCompl_isInvariant_of_elementaryAbelian_coprime
      (V := E₂ ⧸ Φ) (A := E₁) (p := p.val)
      (section12_coprime_card_E1_tau2
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA) B
  let P₀sub : Subgroup E₂ := Q.comap q
  letI : IsInvariant E₁ (E₂ ⧸ Φ) Q := hQinv
  have hqcompat : ∀ a : E₁, ∀ g : E₂, a • q g = q (a • g) := by
    intro a g
    simp [q, MulAction.Quotient.smul_mk]
  have hP₀subInv : IsInvariant E₁ E₂ P₀sub := by
    simpa [P₀sub, q] using
      section12_isInvariant_comap_quotient_local
        (A := E₁) (G := E₂) (N := Φ) (H := Q) hqcompat
  let P₀ : Subgroup G := P₀sub.map E₂.subtype
  have hCcard : Nat.card C = p.val := by
    simpa [C] using (theorem_12_7_b
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow).1
  have hC₂card : Nat.card C₂ = p.val := by
    simpa [C₂, C, section12_card_subgroupOf_eq hCE₂] using hCcard
  have hC₂_not_le_Φ : ¬ C₂ ≤ Φ := by
    simpa [C₂, C, Φ] using
      section12_CA_msigma_not_le_frattini_E2
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA hSylow
  have hC₂Φdisj : Disjoint C₂ Φ := by
    rw [Subgroup.disjoint_def]
    intro x hxC₂ hxΦ
    let D : Subgroup C₂ := Φ.subgroupOf C₂
    have hD_ne_top : D ≠ ⊤ := by
      intro hDtop
      have hC₂_le_Φ : C₂ ≤ Φ := by
        intro y hy
        let yC : C₂ := ⟨y, hy⟩
        have hyD : yC ∈ D := by simp [hDtop]
        simpa [D, yC, Subgroup.mem_subgroupOf] using hyD
      exact hC₂_not_le_Φ hC₂_le_Φ
    haveI : Fact (Nat.card C₂).Prime := ⟨by simpa [hC₂card] using p.2⟩
    have hD_bot : D = ⊥ := by
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card D with hD | hD
      · exact hD
      · exact False.elim (hD_ne_top hD)
    let xC : C₂ := ⟨x, hxC₂⟩
    have hxD : xC ∈ D := by
      simpa [D, xC, Subgroup.mem_subgroupOf] using hxΦ
    have hxC_bot : xC ∈ (⊥ : Subgroup C₂) := by simpa [hD_bot] using hxD
    exact Subtype.ext_iff.mp (by simpa using hxC_bot)
  have hΦ_le_P₀sub : Φ ≤ P₀sub := by
    intro x hx
    change q x ∈ Q
    have hxq : q x = 1 := by
      simpa [q, Φ] using (QuotientGroup.eq_one_iff (N := Φ) (x := x)).2 hx
    simp [hxq]
  have hC₂P₀sub_top : C₂ ⊔ P₀sub = ⊤ := by
    have hcomap :
        (Φ ⊔ C₂) ⊔ P₀sub = ⊤ := by
      have hsup_comap :
          B.comap q ⊔ Q.comap q = (B ⊔ Q).comap q := by
        simpa using
          (Subgroup.comap_sup_eq (f := q) (H := B) (K := Q)
            (QuotientGroup.mk'_surjective Φ))
      calc
        (Φ ⊔ C₂) ⊔ P₀sub = B.comap q ⊔ Q.comap q := by
          simp [B, P₀sub, q, QuotientGroup.comap_map_mk']
        _ = (B ⊔ Q).comap q := hsup_comap
        _ = ⊤ := by
          simp [hBQ.sup_eq_top]
    apply le_antisymm le_top
    rw [← hcomap]
    exact sup_le
      (sup_le (hΦ_le_P₀sub.trans le_sup_right) le_sup_left)
      le_sup_right
  have hC₂P₀sub_disj : Disjoint C₂ P₀sub := by
    rw [Subgroup.disjoint_def]
    intro x hxC₂ hxP₀
    have hxB : q x ∈ B := by
      exact Subgroup.mem_map.mpr ⟨x, hxC₂, rfl⟩
    have hxQ : q x ∈ Q := by
      simpa [P₀sub] using hxP₀
    have hxBQ : q x ∈ B ⊓ Q := ⟨hxB, hxQ⟩
    have hxq_one : q x = 1 := by
      have hxbot : q x ∈ (⊥ : Subgroup (E₂ ⧸ Φ)) := by
        simpa [hBQ.inf_eq_bot] using hxBQ
      simpa using hxbot
    have hxΦ : x ∈ Φ := by
      simpa [q] using (QuotientGroup.eq_one_iff (N := Φ) (x := x)).1 hxq_one
    exact Subgroup.disjoint_def.mp hC₂Φdisj hxC₂ hxΦ
  refine ⟨P₀, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  · calc
      E₂ = (⊤ : Subgroup E₂).map E₂.subtype := by
        ext x
        constructor
        · intro hx
          exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩
        · intro hx
          rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
          exact y.property
      _ = (C₂ ⊔ P₀sub).map E₂.subtype := by rw [hC₂P₀sub_top]
      _ = C₂.map E₂.subtype ⊔ P₀ := by simp [P₀, Subgroup.map_sup]
      _ = C ⊔ P₀ := by
        have hC₂map : C₂.map E₂.subtype = C := by
          simpa [C₂, C] using Subgroup.map_subgroupOf_eq_of_le hCE₂
        simp [hC₂map, C]
      _ = subgroupCentralizerIn A (section10Msigma M) ⊔ P₀ := by simp [C]
  · rw [Subgroup.disjoint_def]
    intro x hxC hxP₀
    have hxE₂ : x ∈ E₂ := hCE₂ hxC
    let x₂ : E₂ := ⟨x, hxE₂⟩
    have hxC₂ : x₂ ∈ C₂ := by
      simpa [C₂, C, x₂, Subgroup.mem_subgroupOf] using hxC
    have hxP₀sub : x₂ ∈ P₀sub := by
      rcases Subgroup.mem_map.mp hxP₀ with ⟨y, hyP₀sub, hyx⟩
      have hy_eq : y = x₂ := Subtype.ext hyx
      simpa [hy_eq] using hyP₀sub
    exact congrArg (fun y : E₂ => (y : G))
      (Subgroup.disjoint_def.mp hC₂P₀sub_disj hxC₂ hxP₀sub)
  · have hforward (a : E₁) {x : G} (hx : x ∈ P₀) :
        (a : G) * x * (a : G)⁻¹ ∈ P₀ := by
      rcases Subgroup.mem_map.mp hx with ⟨y, hyP₀sub, rfl⟩
      refine Subgroup.mem_map.mpr ⟨a • y, ?_, ?_⟩
      · exact (IsInvariant.invariant (A := E₁) (G := E₂) (H := P₀sub) a y).1 hyP₀sub
      · simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    intro e he
    let e₁ : E₁ := ⟨e, he⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hforward e₁
    · intro hx
      have hx' := hforward (e₁⁻¹) hx
      simpa [e₁, mul_assoc] using hx'

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_coprime_card_E1_E2
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    Nat.Coprime (Nat.card E₁) (Nat.card E₂) := by
  classical
  rcases hE with ⟨_hcomp, _hE12, hE1, hE2, _hE3⟩
  rcases hE1 with ⟨hE1E12, hHallE1⟩
  rcases hE2 with ⟨hE2E12, hHallE2⟩
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hqE1 hqE2
  let r : Nat.Primes := ⟨q, hqprime⟩
  have hr1 : r ∈ section12Tau1Primes M :=
    hHallE1.p_in_pi_of_p_dvd_card r
      (by simpa [section12_card_subgroupOf_eq hE1E12, r] using hqE1)
  have hr2 : r ∈ section12Tau2Primes M :=
    hHallE2.p_in_pi_of_p_dvd_card r
      (by simpa [section12_card_subgroupOf_eq hE2E12, r] using hqE2)
  have h1 : primeRank r.val M = 1 := hr1.2.2
  have h2 : primeRank r.val M = 2 := hr2.2
  omega

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_coprime_card_E12_E3
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    Nat.Coprime (Nat.card E₁₂) (Nat.card E₃) := by
  classical
  rcases hE with ⟨_hcomp, hE12, _hE1, _hE2, hE3⟩
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE3 with ⟨hE3E, hHallE3⟩
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hqE12 hqE3
  let r : Nat.Primes := ⟨q, hqprime⟩
  have hr12 : r ∈ section12Tau1Primes M ∪ section12Tau2Primes M :=
    hHallE12.p_in_pi_of_p_dvd_card r
      (by simpa [section12_card_subgroupOf_eq hE12E, r] using hqE12)
  have hr3 : r ∈ section12Tau3Primes M :=
    hHallE3.p_in_pi_of_p_dvd_card r
      (by simpa [section12_card_subgroupOf_eq hE3E, r] using hqE3)
  rcases hr12 with hr1 | hr2
  · exact hr1.2.1 hr3.2.1
  · have h2 : primeRank r.val M = 2 := hr2.2
    have h3 : primeRank r.val M = 1 := hr3.2.2
    omega


/-- Theorem 12.12(a). -/
public theorem CFSG.theorem_12_12_a
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hcent :
      ∀ e : G, e ∈ E → e ≠ 1 →
        subgroupPrimeSet (Subgroup.zpowers e) ⊆
          section12Tau1Primes M ∪ section12Tau3Primes M →
            elementCentralizerIn (section10Msigma M) e = ⊥) :
    ∃ A₀ : Subgroup G, A₀ ≤ E ∧ IsMulCommutative A₀ ∧ section10NormalIn A₀ E ∧
      ∀ x : G, x ∈ section10Msigma M → x ≠ 1 → elementCentralizerIn E x ≤ A₀ := by
  classical
  by_cases hτ2empty : section12Tau2Primes M = ∅
  · have hE2HallIn :
        section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
      section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
    rcases hE2HallIn with ⟨hE2E, hHallE2⟩
    have hE2bot : E₂ = ⊥ := by
      apply Subgroup.card_eq_one.mp
      apply section12_card_eq_one_of_no_prime_dvd
      intro q hqdiv
      have hqdiv_sub : q.val ∣ Nat.card (E₂.subgroupOf E) := by
        simpa [section12_card_subgroupOf_eq hE2E] using hqdiv
      have hqτ2 : q ∈ section12Tau2Primes M :=
        hHallE2.p_in_pi_of_p_dvd_card q hqdiv_sub
      exact (show q ∉ section12Tau2Primes M from by simp [hτ2empty]) hqτ2
    refine ⟨⊥, bot_le, inferInstance, ⟨bot_le, inferInstance⟩, ?_⟩
    intro x hxσ hxne y hy
    have hyτ13 : subgroupPrimeSet (Subgroup.zpowers y) ⊆
        section12Tau1Primes M ∪ section12Tau3Primes M := by
      intro q hqY
      have hqE : q ∈ subgroupPrimeSet E :=
        section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hy.1) hqY
      have hqτ :
          q ∈ section12Tau1Primes M ∪ section12Tau2Primes M ∪ section12Tau3Primes M :=
        section12_prime_mem_tau_union_of_mem_E hM hE.1 hqE
      rcases hqτ with hq12 | hq3
      · rcases hq12 with hq1 | hq2
        · exact Or.inl hq1
        · exact False.elim ((show q ∉ section12Tau2Primes M from by simp [hτ2empty]) hq2)
      · exact Or.inr hq3
    have hxCy : x ∈ elementCentralizerIn (section10Msigma M) y := by
      refine ⟨hxσ, ?_⟩
      change x ∈ Subgroup.centralizer ({y} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz_eq : z = y := by simpa using hz
      subst z
      exact (Subgroup.mem_centralizer_iff.mp hy.2 x (by simp)).symm
    have hybot : y ∈ (⊥ : Subgroup G) := by
      by_contra hyne
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        simpa [hcent y hy.1 hyne hyτ13] using hxCy
      exact hxne (by simpa using hxbot)
    simpa using hybot
  · have hτ2nonempty : (section12Tau2Primes M).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hτ2empty
    rcases hτ2nonempty with ⟨p, hp⟩
    obtain ⟨A, hA⟩ := section12_exists_rankTwo_in_E_of_tau2 hM hE hp
    have hAnorm : section10NormalIn A E :=
      (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA).1
    by_cases hSylow : section12HasNonabelianSylowSubgroup p G
    · let A₀ : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
      obtain ⟨E₀, hE₀comp, hE₀tau1⟩ :=
        theorem_12_7_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
          hM hE hp hA hSylow
      have hAelem := (section12_rankTwo_elementary hA).2
      haveI : IsElementaryAbelian p.val A := hAelem
      have hA₀comm : IsMulCommutative A₀ := by
        refine ⟨⟨fun x y => ?_⟩⟩
        exact Subtype.ext <|
          setLike_mul_comm
            (s := A) x.property.1 y.property.1
      have hA₀norm : section10NormalIn A₀ E := by
        simpa [A₀] using
          section12_CA_msigma_normalIn_E
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A)
            hE hAnorm
      have hA₀comp' :
          (E₀.subgroupOf E).IsComplement' (A₀.subgroupOf E) :=
        section12_complementIn_of_normal_isComplement'
          (G := G) (H := E) (K := A₀) (L := E₀)
          (by simpa [A₀] using hE₀comp) hA₀norm
      have hE₀cent :
          ∀ x : G, x ∈ section10Msigma M → x ≠ 1 →
            elementCentralizerIn E₀ x = ⊥ := by
        intro x hxσ hxne
        apply le_bot_iff.mp
        intro z hz
        by_contra hzne
        have hzE : z ∈ E := hE₀comp.2.1 hz.1
        have hzτ13 :
            subgroupPrimeSet (Subgroup.zpowers z) ⊆
              section12Tau1Primes M ∪ section12Tau3Primes M := by
          intro q hqz
          exact Or.inl
            ((hE₀tau1 x hxσ hxne)
              (section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hz) hqz))
        have hxCz : x ∈ elementCentralizerIn (section10Msigma M) z := by
          refine ⟨hxσ, ?_⟩
          change x ∈ Subgroup.centralizer ({z} : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          have hwz : w = z := by simpa using hw
          subst w
          exact (Subgroup.mem_centralizer_iff.mp hz.2 x (by simp)).symm
        have hxbot : x ∈ (⊥ : Subgroup G) := by
          simpa [hcent z hzE hzne hzτ13] using hxCz
        exact hxne (by simpa using hxbot)
      refine ⟨A₀, hA₀norm.1, hA₀comm, hA₀norm, ?_⟩
      intro x hxσ hxne y hy
      let yE : E := ⟨y, hy.1⟩
      have hyTop : yE ∈ E₀.subgroupOf E ⊔ A₀.subgroupOf E := by
        rw [hA₀comp'.sup_eq_top]
        simp
      haveI : (A₀.subgroupOf E).Normal := hA₀norm.2
      rcases (Subgroup.mem_sup_of_normal_right
          (s := E₀.subgroupOf E) (t := A₀.subgroupOf E) (x := yE)).1 hyTop with
        ⟨e0, he0, a0, ha0, hmul⟩
      have ha0A₀ : (a0 : G) ∈ A₀ := by
        simpa [A₀, Subgroup.mem_subgroupOf] using ha0
      have ha0_cent : (a0 : G) ∈ Subgroup.centralizer ({x} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hwx : w = x := by simpa using hw
        subst w
        exact Subgroup.mem_centralizer_iff.mp ha0A₀.2 x hxσ
      have hmulG : (e0 : G) * a0 = y := by
        have hval := congrArg (fun z : E => (z : G)) hmul
        simpa [yE] using hval
      have he0_cent : (e0 : G) ∈ Subgroup.centralizer ({x} : Set G) := by
        have hy_cent : y ∈ Subgroup.centralizer ({x} : Set G) := hy.2
        have he0_eq : (e0 : G) = y * a0⁻¹ := by
          calc
            (e0 : G) = (e0 : G) * (a0 * a0⁻¹) := by simp
            _ = ((e0 : G) * a0) * a0⁻¹ := by simp [mul_assoc]
            _ = y * a0⁻¹ := by rw [hmulG]
        rw [he0_eq]
        exact (Subgroup.centralizer ({x} : Set G)).mul_mem hy_cent
          ((Subgroup.centralizer ({x} : Set G)).inv_mem ha0_cent)
      have he0Cx : (e0 : G) ∈ elementCentralizerIn E₀ x := ⟨by
        simpa [Subgroup.mem_subgroupOf] using he0, he0_cent⟩
      have he0bot : (e0 : G) ∈ (⊥ : Subgroup G) := by
        simpa [hE₀cent x hxσ hxne] using he0Cx
      have he0one : e0 = 1 := by
        apply Subtype.ext
        simpa using he0bot
      have hyA₀ : y ∈ A₀ := by
        have hy_eq_a0 : y = a0 := by simpa [he0one] using hmulG.symm
        simpa [hy_eq_a0, A₀, Subgroup.mem_subgroupOf] using ha0
      exact hyA₀
    · have hAp : IsPGroup p.val A := by
        have hElem := (section12_rankTwo_elementary hA).2
        haveI : IsElementaryAbelian p.val A := hElem
        exact IsElementaryAbelian.isPGroup p.val A
      obtain ⟨S, hAS⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hAp
      have hScomm : IsMulCommutative (S : Subgroup G) := by
        by_contra hSnoncomm
        exact hSylow ⟨S, hSnoncomm⟩
      have h8a :=
        lemma_12_8_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
          hM hE hp hA hAS hScomm
      have hE2comm : IsMulCommutative E₂ := h8a.1
      have hE2norm : section10NormalIn E₂ E := h8a.2
      have hE2HallIn :
          section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
        section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
      rcases hE2HallIn with ⟨hE2E, hHallE2E⟩
      haveI : (E₂.subgroupOf E).Normal := hE2norm.2
      refine ⟨E₂, hE2E, hE2comm, hE2norm, ?_⟩
      intro x hxσ hxne y hy
      let Y : Subgroup G := Subgroup.zpowers y
      have hYle : Y ≤ elementCentralizerIn E x := Subgroup.zpowers_le.2 hy
      have hYleE : Y ≤ E := hYle.trans inf_le_left
      have hYτ2 :
          subgroupPrimeSet Y ⊆ section12Tau2Primes M := by
        intro q hqY
        have hqE : q ∈ subgroupPrimeSet E :=
          section8_subgroupPrimeSet_mono hYleE hqY
        have hqτ :
            q ∈ section12Tau1Primes M ∪ section12Tau2Primes M ∪
              section12Tau3Primes M :=
          section12_prime_mem_tau_union_of_mem_E hM hE.1 hqE
        rcases hqτ with hq12 | hq3
        · rcases hq12 with hq1 | hq2
          · exfalso
            haveI : Fact q.val.Prime := ⟨q.2⟩
            obtain ⟨z0, hz0_order⟩ :=
              exists_prime_orderOf_dvd_card' (G := Y) q.val hqY
            let z : G := z0
            have hzY : z ∈ Y := z0.property
            have hz_order : orderOf z = q.val := by
              simpa [z, Subgroup.orderOf_coe] using hz0_order
            have hzE : z ∈ E := hYleE hzY
            have hzne : z ≠ 1 := by
              intro hz1
              have hq_one : q.val = 1 := by
                rw [← hz_order, hz1, orderOf_one]
              exact q.2.ne_one hq_one
            have hZτ13 :
                subgroupPrimeSet (Subgroup.zpowers z) ⊆
                  section12Tau1Primes M ∪ section12Tau3Primes M := by
              intro r hr
              have hrdiv : r.val ∣ Nat.card (Subgroup.zpowers z) := hr
              rw [Nat.card_zpowers, hz_order] at hrdiv
              have hr_eq_q : r = q := by
                exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.2 q.2).mp hrdiv)
              subst r
              exact Or.inl hq1
            have hzCent : z ∈ Subgroup.centralizer ({x} : Set G) :=
              (hYle hzY).2
            have hxCz : x ∈ elementCentralizerIn (section10Msigma M) z := by
              refine ⟨hxσ, ?_⟩
              change x ∈ Subgroup.centralizer ({z} : Set G)
              rw [Subgroup.mem_centralizer_iff]
              intro w hw
              have hwz : w = z := by simpa using hw
              subst w
              exact (Subgroup.mem_centralizer_iff.mp hzCent x (by simp)).symm
            have hxbot : x ∈ (⊥ : Subgroup G) := by
              simpa [hcent z hzE hzne hZτ13] using hxCz
            exact hxne (by simpa using hxbot)
          · exact hq2
        · exfalso
          haveI : Fact q.val.Prime := ⟨q.2⟩
          obtain ⟨z0, hz0_order⟩ :=
            exists_prime_orderOf_dvd_card' (G := Y) q.val hqY
          let z : G := z0
          have hzY : z ∈ Y := z0.property
          have hz_order : orderOf z = q.val := by
            simpa [z, Subgroup.orderOf_coe] using hz0_order
          have hzE : z ∈ E := hYleE hzY
          have hzne : z ≠ 1 := by
            intro hz1
            have hq_one : q.val = 1 := by
              rw [← hz_order, hz1, orderOf_one]
            exact q.2.ne_one hq_one
          have hZτ13 :
              subgroupPrimeSet (Subgroup.zpowers z) ⊆
                section12Tau1Primes M ∪ section12Tau3Primes M := by
            intro r hr
            have hrdiv : r.val ∣ Nat.card (Subgroup.zpowers z) := hr
            rw [Nat.card_zpowers, hz_order] at hrdiv
            have hr_eq_q : r = q := by
              exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.2 q.2).mp hrdiv)
            subst r
            exact Or.inr hq3
          have hzCent : z ∈ Subgroup.centralizer ({x} : Set G) :=
            (hYle hzY).2
          have hxCz : x ∈ elementCentralizerIn (section10Msigma M) z := by
            refine ⟨hxσ, ?_⟩
            change x ∈ Subgroup.centralizer ({z} : Set G)
            rw [Subgroup.mem_centralizer_iff]
            intro w hw
            have hwz : w = z := by simpa using hw
            subst w
            exact (Subgroup.mem_centralizer_iff.mp hzCent x (by simp)).symm
          have hxbot : x ∈ (⊥ : Subgroup G) := by
            simpa [hcent z hzE hzne hZτ13] using hxCz
          exact hxne (by simpa using hxbot)
      have hYπ : IsPiSubgroup (G := G) (section12Tau2Primes M) Y :=
        section8_isPiSubgroup_of_subgroupPrimeSet_subset hYτ2
      have hYsubπ : IsPiSubgroup (G := E) (section12Tau2Primes M) (Y.subgroupOf E) :=
        section12_isPiSubgroup_subgroupOf hYπ hYleE
      have hYsub_le_E2sub :
          Y.subgroupOf E ≤ E₂.subgroupOf E :=
        section12_piSubgroup_le_normal_hall
          (H := E₂.subgroupOf E) (A := Y.subgroupOf E) hHallE2E hYsubπ
      have hyYsub : (⟨y, hy.1⟩ : E) ∈ Y.subgroupOf E := by
        simp [Y, Subgroup.mem_subgroupOf]
      have hyE2sub : (⟨y, hy.1⟩ : E) ∈ E₂.subgroupOf E :=
        hYsub_le_E2sub hyYsub
      simpa [Subgroup.mem_subgroupOf] using hyE2sub

end Section12
