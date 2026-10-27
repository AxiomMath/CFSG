module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.theorem_12_7_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [IsMinCE G] in
public theorem CFSG.section12_exists_nontrivial_zpowers_fixedPoint_nonbot_pre
    {A H : Type*} [Group A] [Finite A] [Group H] [Finite H] [MulDistribMulAction A H]
    [Nontrivial H]
    (hSup : (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) H) = ⊤) :
    ∃ a : A, a ≠ 1 ∧ fixedPointSubgroup (↥(Subgroup.zpowers a)) H ≠ ⊥ := by
  by_contra h
  have hall :
      ∀ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) H = ⊥ := by
    intro a ha
    by_contra hi
    exact h ⟨a, ha, hi⟩
  have hle_bot :
      (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) H) ≤ ⊥ := by
    refine iSup_le ?_
    intro a
    refine iSup_le ?_
    intro ha
    simp [hall a ha]
  have hbot :
      (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) H) = ⊥ :=
    le_antisymm hle_bot bot_le
  exact top_ne_bot (hSup.symm.trans hbot)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_subgroupCentralizerIn_zpowers_eq_elementCentralizerIn_pre
    {Q : Subgroup G} (a : G) :
    subgroupCentralizerIn Q (Subgroup.zpowers a) = elementCentralizerIn Q a := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr <| by
      have hxcent : x ∈ Subgroup.centralizer ((Subgroup.zpowers a) : Set G) := hx.2
      have hcomm : a * x = x * a :=
        Subgroup.mem_centralizer_iff.mp hxcent a (Subgroup.mem_zpowers a)
      exact hcomm.symm
  · intro hx
    refine ⟨hx.1, ?_⟩
    change x ∈ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    have hcomm : Commute a x :=
      (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
    simpa using (hcomm.zpow_left n).eq

public theorem CFSG.section12_exists_primeOrder_centralizer_ne_bot_of_tau2_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    ∃ A₀ : Subgroup G, A₀ ∈ section10PrimeOrderSubgroupsIn p A ∧
      subgroupCentralizerIn (section10Msigma M) A₀ ≠ ⊥ := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  rcases (by simpa [section12Tau2Primes] using hp) with ⟨hpσ, _hprank⟩
  rcases section12_rankTwo_elementary hA with ⟨_hAcard, hAelem⟩
  let : IsElementaryAbelian p.val A := hAelem
  let : IsMulCommutative A := hAelem.toIsMulCommutative
  let : CommGroup A := IsMulCommutative.instCommGroup
  have : Fact (IsPGroup p.val A) := ⟨IsElementaryAbelian.isPGroup p.val A⟩
  have : Subgroup.Normalizes A (section10Msigma M) := by
    refine ⟨?_⟩
    exact (section12_rankTwo_le hA_M).trans section12_le_normalizer_msigma
  have hσ_p' : IsPiSubgroup (G := G) (section10PPrimeSet p) (section10Msigma M) :=
    section12_isPiSubgroup_pPrime_of_le_msigma_pre hM hpσ le_rfl
  have hcop : Nat.Coprime p.val (Nat.card (section10Msigma M)) :=
    section12_rankTwo_coprime_card_of_pPrime_pre hA_M hσ_p'
  have hσ_ne_bot : section10Msigma M ≠ ⊥ :=
    theorem_10_2_e (G := G) hM
  have : Nontrivial (section10Msigma M) :=
    (Subgroup.nontrivial_iff_ne_bot (section10Msigma M)).2 hσ_ne_bot
  have hsup :
      (⨆ (a : A) (_ : a ≠ 1),
          fixedPointSubgroup (↥(Subgroup.zpowers a)) (section10Msigma M)) = ⊤ :=
    proposition_1_16_a (G := section10Msigma M) (A := A) p.val hcop
      (section12_rankTwo_not_isCyclic_pre hA_M)
  obtain ⟨a, ha_ne, hfix_ne_bot⟩ :=
    section12_exists_nontrivial_zpowers_fixedPoint_nonbot_pre
      (A := A) (H := section10Msigma M) hsup
  have hfix_eq :
      fixedPointSubgroup (↥(Subgroup.zpowers a)) (section10Msigma M) =
        (elementCentralizerIn (section10Msigma M) (a : G)).subgroupOf (section10Msigma M) := by
    simpa using
      fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn
        (K := section10Msigma M) (R := A)
        ((section12_rankTwo_le hA_M).trans section12_le_normalizer_msigma) a
  refine ⟨Subgroup.zpowers (a : G),
    section12_zpowers_mem_primeOrderSubgroupsIn_of_rankTwo_pre hA a ha_ne, ?_⟩
  have hcent_sub_ne_bot :
      (elementCentralizerIn (section10Msigma M) (a : G)).subgroupOf (section10Msigma M) ≠ ⊥ := by
    simpa [hfix_eq] using hfix_ne_bot
  have hcent_ne_bot : elementCentralizerIn (section10Msigma M) (a : G) ≠ ⊥ := by
    intro hbot
    have hsub_bot :
        (elementCentralizerIn (section10Msigma M) (a : G)).subgroupOf
            (section10Msigma M) = ⊥ := by
      simp [hbot]
    exact hcent_sub_ne_bot hsub_bot
  simpa [section12_subgroupCentralizerIn_zpowers_eq_elementCentralizerIn_pre]
    using hcent_ne_bot

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_le_fittingSubgroupOf_of_normalIn_nilpotent
    {H N : Subgroup G} (hHN : N ≤ H)
    (hN_norm : (N.subgroupOf H).Normal) (hN_nil : Group.IsNilpotent N) :
    N ≤ fittingSubgroupOf (G := G) H := by
  classical
  have : Group.IsNilpotent (N.subgroupOf H) := by
    let e := (Subgroup.subgroupOfEquivOfLe (G := G) (H := N) (K := H) hHN).symm
    have : Group.IsNilpotent N := hN_nil
    exact Group.nilpotent_of_mulEquiv (G := N) (G' := N.subgroupOf H) e
  have hle_in_H : N.subgroupOf H ≤ fittingSubgroup H :=
    le_sSup ⟨hN_norm, (inferInstance : Group.IsNilpotent (N.subgroupOf H))⟩
  have hmap_le : (N.subgroupOf H).map H.subtype ≤ fittingSubgroupOf (G := G) H :=
    Subgroup.map_mono hle_in_H
  simpa [fittingSubgroupOf, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hHN]
    using hmap_le

public theorem CFSG.section12_msigma_le_fitting_of_tau2_pre
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    section10Msigma M ≤ section8FittingSubgroup M := by
  classical
  have hσM : section10Msigma M ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hσnorm : ((section10Msigma M).subgroupOf M).Normal := by
    simpa [section12Msigma_subgroupOf_eq] using
      section10MsigmaSubgroup_normal (M := M)
  have hσnil : Group.IsNilpotent (section10Msigma M) :=
    theorem_12_5_a hM hp hA
  simpa [section8FittingSubgroup] using
    section12_le_fittingSubgroupOf_of_normalIn_nilpotent
      (G := G) (H := M) (N := section10Msigma M) hσM hσnorm hσnil

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_subgroupCentralizerIn_commute_pre
    (A S : Subgroup G) :
    S ≤ Subgroup.centralizer (subgroupCentralizerIn A S : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  exact (Subgroup.mem_centralizer_iff.mp hc.2 s hs).symm

omit [IsMinCE G] in
public theorem CFSG.section12_subgroupCentralizerIn_le_fitting_of_card_prime_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hAnorm : section10NormalIn A E)
    (hCcard : Nat.card (subgroupCentralizerIn A (section10Msigma M)) = p.val) :
    subgroupCentralizerIn A (section10Msigma M) ≤ section8FittingSubgroup M := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  have hC_le_M : C ≤ M := by
    intro x hx
    exact hE.1.2.1 (hAnorm.1 hx.1)
  have hE_norm_A : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAnorm.1).mp hAnorm.2
  have hE_norm_σ : E ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hE.1.2.1.trans section12_le_normalizer_msigma
  have hE_norm_C : E ≤ Subgroup.normalizer (C : Set G) := by
    intro e he
    have he_norm_A : e ∈ Subgroup.normalizer (A : Set G) := hE_norm_A he
    have he_norm_σ : e ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
      hE_norm_σ he
    have he_inv_norm_A : e⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normalizer (A : Set G)).inv_mem he_norm_A
    have he_inv_norm_σ : e⁻¹ ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
      (Subgroup.normalizer (section10Msigma M : Set G)).inv_mem he_norm_σ
    have hconj_mem :
        ∀ {x : G}, x ∈ C → e * x * e⁻¹ ∈ C := by
      intro x hx
      refine ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp he_norm_A x).1 hx.1
      · change e * x * e⁻¹ ∈ Subgroup.centralizer (section10Msigma M : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hyσ
        have hy_conj : e⁻¹ * y * e ∈ section10Msigma M := by
          simpa using (Subgroup.mem_normalizer_iff.mp he_inv_norm_σ y).1 hyσ
        have hcomm :
            (e⁻¹ * y * e) * x = x * (e⁻¹ * y * e) :=
          Subgroup.mem_centralizer_iff.mp hx.2 (e⁻¹ * y * e) hy_conj
        calc
          y * (e * x * e⁻¹) = e * ((e⁻¹ * y * e) * x) * e⁻¹ := by group
          _ = e * (x * (e⁻¹ * y * e)) * e⁻¹ := by rw [hcomm]
          _ = (e * x * e⁻¹) * y := by group
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hconj_mem hx
    · intro hx
      have hx' : e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹ ∈ C := by
        refine ⟨?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp he_inv_norm_A (e * x * e⁻¹)).1 hx.1
        · change e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹ ∈
            Subgroup.centralizer (section10Msigma M : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro y hyσ
          have hy_conj : e * y * e⁻¹ ∈ section10Msigma M :=
            (Subgroup.mem_normalizer_iff.mp he_norm_σ y).1 hyσ
          have hcomm :
              (e * y * e⁻¹) * (e * x * e⁻¹) =
                (e * x * e⁻¹) * (e * y * e⁻¹) :=
            Subgroup.mem_centralizer_iff.mp hx.2 (e * y * e⁻¹) hy_conj
          calc
            y * (e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹) =
                e⁻¹ * ((e * y * e⁻¹) * (e * x * e⁻¹)) * e := by group
            _ = e⁻¹ * ((e * x * e⁻¹) * (e * y * e⁻¹)) * e := by rw [hcomm]
            _ = (e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹) * y := by group
      simpa [mul_assoc] using hx'
  have hσ_norm_C : section10Msigma M ≤ Subgroup.normalizer (C : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hcomm : s * x = x * s :=
        Subgroup.mem_centralizer_iff.mp hx.2 s hs
      have hsxs : s * x * s⁻¹ = x := by
        calc
          s * x * s⁻¹ = x * s * s⁻¹ := by rw [hcomm]
          _ = x := by simp [mul_assoc]
      simpa [hsxs] using hx
    · intro hx
      have hcomm : s * (s * x * s⁻¹) = (s * x * s⁻¹) * s :=
        Subgroup.mem_centralizer_iff.mp hx.2 s hs
      have hconj_eq : s * x * s⁻¹ = x := by
        calc
          s * x * s⁻¹ = s⁻¹ * (s * (s * x * s⁻¹)) := by group
          _ = s⁻¹ * ((s * x * s⁻¹) * s) := by rw [hcomm]
          _ = x := by group
      simpa [hconj_eq] using hx
  have hM_norm_C : M ≤ Subgroup.normalizer (C : Set G) := by
    rw [hE.1.2.2.1]
    exact sup_le hσ_norm_C hE_norm_C
  have hC_norm_M : (C.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hM_norm_C
  have hCp : IsPGroup p.val C := by
    refine IsPGroup.of_card (p := p.val) (G := C) (n := 1) ?_
    simpa [C, pow_one] using hCcard
  have hC_nil : Group.IsNilpotent C :=
    IsPGroup.isNilpotent (p := p.val) (G := C) hCp
  simpa [C, section8FittingSubgroup] using
    section12_le_fittingSubgroupOf_of_normalIn_nilpotent
      (G := G) (H := M) (N := C) hC_le_M hC_norm_M hC_nil


public theorem CFSG.section12_centralizer_le_M_of_msigma_fixed_primeOrder_tau2_pre
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
    exact section12_normalizer_ne_top_of_ne_bot_ne_top_pre
      (section12_primeOrder_ne_bot hX) (section12_primeOrder_ne_top_pre hX)
      (top_le_iff.mp htop_le_norm)
  exact section12_le_unique_maximal_of_le_pre (Y := Subgroup.centralizer (X : Set G))
    (X := Subgroup.centralizer (X : Set G)) (M := M) le_rfl hCproper huniq

public theorem CFSG.section12_msigma_fixed_eq_bot_of_not_centralizer_le_M_pre
    {M E E₁₂ E₁ E₂ E₃ A X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p E)
    (hnot : ¬ Subgroup.centralizer (X : Set G) ≤ M) :
    subgroupCentralizerIn (section10Msigma M) X = ⊥ := by
  classical
  have hX_A : X ∈ section10PrimeOrderSubgroupsIn p A := by
    have hEq :=
      (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA).2
    simpa [hEq] using hX
  by_contra hCne
  exact hnot <|
    section12_centralizer_le_M_of_msigma_fixed_primeOrder_tau2_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (X := X) (p := p)
      hM hE hp hA hX_A hCne

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_mem_normalizer_of_conjBy_eq_pre
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
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by simpa [hg] using hx
    rcases Subgroup.mem_map.mp hx' with ⟨y, hy, hyx⟩
    have hxy : x = y := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (g * y * g⁻¹) * g := by
          rw [show g * x * g⁻¹ = g * y * g⁻¹ by
            simpa [MulAut.conj_apply] using hyx.symm]
        _ = y := by group
    simpa [hxy] using hy


omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_le_conjBy_inv_of_conjBy_le_pre
    {H K : Subgroup G} {g : G} (hHK : H.conjBy g ≤ K) :
    H ≤ K.conjBy g⁻¹ := by
  intro x hx
  rw [Subgroup.conjBy, Subgroup.mem_map]
  refine ⟨g * x * g⁻¹, ?_, ?_⟩
  · apply hHK
    rw [Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  · simp
    group

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_conjBy_le_centralizer_conjBy_pre
    {C B : Subgroup G} (hCB : C ≤ Subgroup.centralizer (B : Set G)) (g : G) :
    C.conjBy g ≤ Subgroup.centralizer ((B.conjBy g) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Subgroup.conjBy, Subgroup.mem_map] at hx
  rcases hx with ⟨c, hc, hcx⟩
  change y ∈ B.conjBy g at hy
  rw [Subgroup.conjBy, Subgroup.mem_map] at hy
  rcases hy with ⟨b, hb, hby⟩
  have hcomm : b * c = c * b :=
    (Subgroup.mem_centralizer_iff.mp (hCB hc)) b hb
  rw [← hcx, ← hby]
  simpa [mul_assoc] using congrArg (fun t : G => t * g⁻¹) hcomm

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_maximal_conjBy_pre
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) (g : G) :
    M.conjBy g ∈ section9MaximalSubgroups G := by
  have h_map : M.conjBy g = Subgroup.map ((MulAut.conj g : G ≃* G) : G →* G) M := rfl
  rw [h_map]
  exact ((MulAut.conj g : G ≃* G).mapSubgroup.isCoatom_iff M).mpr hM

public theorem CFSG.section12_normalizer_le_self_of_maximal_pre
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    Subgroup.normalizer (M : Set G) ≤ M := by
  classical
  have hNproper : Subgroup.normalizer (M : Set G) ≠ ⊤ := by
    intro hNtop
    have hMnormal : M.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    let : IsSimpleGroup G := IsMinCE.simple
    rcases hMnormal.eq_bot_or_eq_top with hMbot | hMtop
    · have hσne : section10Msigma M ≠ ⊥ := theorem_10_2_e (G := G) hM
      have hσleM : section10Msigma M ≤ M := by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
        exact y.property
      have hσlebot : section10Msigma M ≤ ⊥ := by
        intro x hx
        have hxM : x ∈ M := hσleM hx
        simpa [hMbot] using hxM
      have hσbot : section10Msigma M = ⊥ := le_bot_iff.mp hσlebot
      exact hσne hσbot
    · exact hM.1 hMtop
  exact le_of_eq ((hM.le_iff_eq hNproper).mp Subgroup.le_normalizer)

omit [IsMinCE G] in
public theorem CFSG.section12_exists_nonabelian_sylow_containing_rankTwo_pre
    {E A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    ∃ S : Sylow p.val G, A ≤ (S : Subgroup G) ∧
      ¬ IsMulCommutative (S : Subgroup G) := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  have hAp : IsPGroup p.val A := by
    rcases section12_rankTwo_elementary hA with ⟨_hAcard, hAelem⟩
    have : IsElementaryAbelian p.val A := hAelem
    exact IsElementaryAbelian.isPGroup p.val A
  obtain ⟨S, hAS⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hAp
  refine ⟨S, hAS, ?_⟩
  by_contra hScomm
  rcases hSylow with ⟨Sbad, hSbad_noncomm⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Sbad
  have hSbad_comm : IsMulCommutative (Sbad : Subgroup G) := by
    have hconj_comm : IsMulCommutative ((g • S : Sylow p.val G) : Subgroup G) := by
      let : IsMulCommutative (S : Subgroup G) := hScomm
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.map_isMulCommutative
        (f := (MulAut.conj g).toMonoidHom) (H := (S : Subgroup G))
    rw [← hg]
    exact hconj_comm
  exact hSbad_noncomm hSbad_comm

public theorem CFSG.section12_global_sylow_not_le_M_of_nonabelian_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    {S : Sylow p.val G} (hSnonab : ¬ IsMulCommutative (S : Subgroup G)) :
    ¬ (S : Subgroup G) ≤ M := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
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

public theorem CFSG.section12_sylow_inf_M_isMulCommutative_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (S : Sylow p.val G) :
    IsMulCommutative ((S : Subgroup G) ⊓ M : Subgroup G) := by
  classical
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  let I : Subgroup G := (S : Subgroup G) ⊓ M
  have hI_le_M : I ≤ M := inf_le_right
  have hI_p : IsPGroup p.val I :=
    IsPGroup.to_le S.isPGroup' inf_le_left
  let Isub : Subgroup M := I.subgroupOf M
  have hIsub_p : IsPGroup p.val Isub :=
    hI_p.of_equiv (Subgroup.subgroupOfEquivOfLe (H := I) (K := M) hI_le_M).symm
  obtain ⟨T, hIsub_le_T⟩ := IsPGroup.exists_le_sylow (G := M) (p := p.val) hIsub_p
  have hTcomm : IsMulCommutative (T : Subgroup M) :=
    (theorem_12_5_b hM hp hA_M).1 T
  refine ⟨⟨fun x y => ?_⟩⟩
  have hxT : (⟨(x : G), hI_le_M x.property⟩ : M) ∈ (T : Subgroup M) := by
    apply hIsub_le_T
    change (⟨(x : G), hI_le_M x.property⟩ : M) ∈ I.subgroupOf M
    simp [Subgroup.mem_subgroupOf]
  have hyT : (⟨(y : G), hI_le_M y.property⟩ : M) ∈ (T : Subgroup M) := by
    apply hIsub_le_T
    change (⟨(y : G), hI_le_M y.property⟩ : M) ∈ I.subgroupOf M
    simp [Subgroup.mem_subgroupOf]
  apply Subtype.ext
  exact congrArg (fun z : M => (z : G)) <|
    setLike_mul_comm (s := (T : Subgroup M)) hxT hyT

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_conjBy_eq_self_of_le_abelian_pre
    {H X : Subgroup G} {g : G}
    (hHcomm : IsMulCommutative H) (hXH : X ≤ H) (hgH : g ∈ H) :
    X.conjBy g = X := by
  classical
  let : IsMulCommutative H := hHcomm
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyX, hyx⟩
    have hgy : g * y = y * g :=
      setLike_mul_comm (s := H) hgH (hXH hyX)
    have hx_eq_y : x = y := by
      rw [← hyx]
      simp [MulAut.conj_apply, hgy, mul_assoc]
    simpa [hx_eq_y] using hyX
  · intro hx
    refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
    have hgx : g * x = x * g :=
      setLike_mul_comm (s := H) hgH (hXH hx)
    simp [MulAut.conj_apply, hgx, mul_assoc]

public theorem CFSG.section12_not_centralizer_le_M_of_ne_fixed_primeOrder_tau2_pre
    {M E E₁₂ E₁ E₂ E₃ A A₀ X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hA₀ : A₀ ∈ section10PrimeOrderSubgroupsIn p A)
    (hCA₀ : subgroupCentralizerIn (section10Msigma M) A₀ ≠ ⊥)
    (hSylow : section12HasNonabelianSylowSubgroup p G)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p E)
    (hXne : X ≠ A₀) :
    ¬ Subgroup.centralizer (X : Set G) ≤ M := by
  classical
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
  obtain ⟨S, hAS, hSnonab⟩ :=
    section12_exists_nonabelian_sylow_containing_rankTwo_pre
      (G := G) (E := E) (A := A) (p := p) hA hSylow
  have hSnotM : ¬ (S : Subgroup G) ≤ M :=
    section12_global_sylow_not_le_M_of_nonabelian_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSnonab
  let Z : Subgroup G := section10OmegaOneCenter p (S : Subgroup G)
  have hS_le_centZ : (S : Subgroup G) ≤ Subgroup.centralizer (Z : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((Subgroup.mem_centralizer_iff.mp
      (section12_omegaOneCenter_centralizes_pre (p := p) (S : Subgroup G)
        (by simpa [Z] using hz))) s hs).symm
  have hA₀neZ : A₀ ≠ Z := by
    intro hA₀Z
    have hS_le_centA₀ : (S : Subgroup G) ≤ Subgroup.centralizer (A₀ : Set G) := by
      simpa [hA₀Z] using hS_le_centZ
    have hCentA₀_le_M :
        Subgroup.centralizer (A₀ : Set G) ≤ M :=
      section12_centralizer_le_M_of_msigma_fixed_primeOrder_tau2_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (X := A₀) (p := p)
        hM hE hp hA hA₀ hCA₀
    exact hSnotM (hS_le_centA₀.trans hCentA₀_le_M)
  have hX_A : X ∈ section10PrimeOrderSubgroupsIn p A := by
    have hEq :=
      (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA).2
    simpa [hEq] using hX
  by_cases hXZ : X = Z
  · intro hCentX_M
    have hS_le_centX : (S : Subgroup G) ≤ Subgroup.centralizer (X : Set G) := by
      simpa [hXZ] using hS_le_centZ
    exact hSnotM (hS_le_centX.trans hCentX_M)
  · have htrans :
        ConjugationActionTransitiveOn (subgroupNormalizerIn (S : Subgroup G) (A : Set G))
          {Y | Y ∈ section10PrimeOrderSubgroupsIn p A ∧ Y ≠ Z} := by
      simpa [Z] using
        lemma_10_13_c (G := G) (p := p) (A := A) (P := (S : Subgroup G))
          (A₀ := A₀) hpG hA10 S.isPGroup' hSnonab hAS hA₀
          (by simpa [Z] using hA₀neZ)
    obtain ⟨k, hkX⟩ := htrans A₀ ⟨hA₀, by simpa [Z] using hA₀neZ⟩
      X ⟨hX_A, by simpa [Z] using hXZ⟩
    have hkS : (k : G) ∈ (S : Subgroup G) := by
      have hk' :
          (k : G) ∈ Subgroup.normalizer (A : Set G) ⊓ (S : Subgroup G) := by
        exact k.property
      exact hk'.2
    have hk_not_M : (k : G) ∉ M := by
      intro hkM
      have hSintMcomm :
          IsMulCommutative ((S : Subgroup G) ⊓ M : Subgroup G) :=
        section12_sylow_inf_M_isMulCommutative_pre
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hM hE hp hA S
      have hA₀_le_inf : A₀ ≤ (S : Subgroup G) ⊓ M := by
        intro a ha
        exact ⟨hAS (hA₀.1 ha), (section12_rankTwo_le hA_M) (hA₀.1 ha)⟩
      have hk_inf : (k : G) ∈ (S : Subgroup G) ⊓ M := ⟨hkS, hkM⟩
      have hconjA₀ :
          A₀.conjBy (k : G) = A₀ :=
        section12_conjBy_eq_self_of_le_abelian_pre
          (G := G) hSintMcomm hA₀_le_inf hk_inf
      have hXA₀ : X = A₀ := by
        rw [hkX, hconjA₀]
      exact hXne hXA₀
    intro hCentX_M
    have hCentA₀_conj_le :
        (Subgroup.centralizer (A₀ : Set G)).conjBy (k : G) ≤
          Subgroup.centralizer (X : Set G) := by
      simpa [hkX] using
        section12_conjBy_le_centralizer_conjBy_pre
          (G := G) (C := Subgroup.centralizer (A₀ : Set G)) (B := A₀)
          (by intro y hy; exact hy) (k : G)
    have hCentA₀_le_Mconj :
        Subgroup.centralizer (A₀ : Set G) ≤ M.conjBy ((k : G)⁻¹) :=
      section12_le_conjBy_inv_of_conjBy_le_pre (G := G)
        (H := Subgroup.centralizer (A₀ : Set G)) (K := M) (g := (k : G))
        (hCentA₀_conj_le.trans hCentX_M)
    have huniqA₀ :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (A₀ : Set G)) = {M} :=
      corollary_12_6_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA A₀ hA₀ hCA₀
    have hMconj_mem :
        M.conjBy ((k : G)⁻¹) ∈
          section9MaximalSubgroupsContaining (Subgroup.centralizer (A₀ : Set G)) :=
      ⟨section12_maximal_conjBy_pre (G := G) hM ((k : G)⁻¹), hCentA₀_le_Mconj⟩
    have hMconj_eq_M : M.conjBy ((k : G)⁻¹) = M := by
      have hsingle :
          M.conjBy ((k : G)⁻¹) ∈ ({M} : Set (Subgroup G)) := by
        simpa [huniqA₀] using hMconj_mem
      simpa using hsingle
    have hkinv_norm : (k : G)⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
      section12_mem_normalizer_of_conjBy_eq_pre (G := G) hMconj_eq_M
    have hk_norm : (k : G) ∈ Subgroup.normalizer (M : Set G) :=
      by simpa using (Subgroup.normalizer (M : Set G)).inv_mem hkinv_norm
    have hkM : (k : G) ∈ M :=
      section12_normalizer_le_self_of_maximal_pre (G := G) hM hk_norm
    exact hk_not_M hkM

public theorem CFSG.section12_CA_msigma_eq_fixed_primeOrder_of_tau2_pre
    {M E E₁₂ E₁ E₂ E₃ A A₀ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hA₀ : A₀ ∈ section10PrimeOrderSubgroupsIn p A)
    (hCA₀ : subgroupCentralizerIn (section10Msigma M) A₀ ≠ ⊥)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    subgroupCentralizerIn A (section10Msigma M) = A₀ := by
  classical
  let K : Subgroup G := section10Msigma M
  have : Fact p.val.Prime := ⟨p.2⟩
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  rcases (by simpa [section12Tau2Primes] using hp) with ⟨hpσ, _hprank⟩
  rcases section12_rankTwo_elementary hA with ⟨_hAcard, hAelem⟩
  let : IsElementaryAbelian p.val A := hAelem
  let : IsMulCommutative A := hAelem.toIsMulCommutative
  let : CommGroup A := IsMulCommutative.instCommGroup
  have : Fact (IsPGroup p.val A) := ⟨IsElementaryAbelian.isPGroup p.val A⟩
  have hAKnorm : A ≤ Subgroup.normalizer (K : Set G) := by
    exact (section12_rankTwo_le hA_M).trans (by simpa [K] using section12_le_normalizer_msigma)
  have : Subgroup.Normalizes A K := ⟨hAKnorm⟩
  have hKp' : IsPiSubgroup (G := G) (section10PPrimeSet p) K := by
    simpa [K] using section12_isPiSubgroup_pPrime_of_le_msigma_pre hM hpσ le_rfl
  have hcop : Nat.Coprime p.val (Nat.card K) := by
    simpa [K] using section12_rankTwo_coprime_card_of_pPrime_pre hA_M hKp'
  have hsup :
      (⨆ (a : A) (_ : a ≠ 1),
          fixedPointSubgroup (↥(Subgroup.zpowers a)) K) = ⊤ :=
    proposition_1_16_a (G := K) (A := A) p.val hcop
      (section12_rankTwo_not_isCyclic_pre hA_M)
  have hfixed_map_le :
      ∀ a : A, ∀ ha_ne : a ≠ 1,
        (fixedPointSubgroup (↥(Subgroup.zpowers a)) K).map K.subtype ≤
          Subgroup.centralizer (A₀ : Set G) := by
    intro a ha_ne
    let X : Subgroup G := Subgroup.zpowers (a : G)
    have hX_A : X ∈ section10PrimeOrderSubgroupsIn p A := by
      simpa [X] using section12_zpowers_mem_primeOrderSubgroupsIn_of_rankTwo_pre hA a ha_ne
    have hX_E : X ∈ section10PrimeOrderSubgroupsIn p E := by
      rcases (show X ≤ A ∧ Nat.card X = p.val from hX_A) with ⟨hXA, hXcard⟩
      exact ⟨hXA.trans (section12_rankTwo_le hA), hXcard⟩
    have hfix_eq :
        fixedPointSubgroup (↥(Subgroup.zpowers a)) K =
          (elementCentralizerIn K (a : G)).subgroupOf K := by
      simpa [K] using
        fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn
          (K := K) (R := A) hAKnorm a
    have hfix_map :
        (fixedPointSubgroup (↥(Subgroup.zpowers a)) K).map K.subtype =
          elementCentralizerIn K (a : G) := by
      calc
        (fixedPointSubgroup (↥(Subgroup.zpowers a)) K).map K.subtype =
            ((elementCentralizerIn K (a : G)).subgroupOf K).map K.subtype := by
              rw [hfix_eq]
        _ = elementCentralizerIn K (a : G) ⊓ K := by
              rw [Subgroup.subgroupOf_map_subtype]
        _ = elementCentralizerIn K (a : G) := inf_eq_left.2 inf_le_left
    by_cases hXA₀ : X = A₀
    · rw [hfix_map]
      intro x hx
      rw [← hXA₀]
      exact section12_centralizer_singleton_le_centralizer_zpowers_pre (G := G)
        (a : G) hx.2
    · have hnot :
          ¬ Subgroup.centralizer (X : Set G) ≤ M :=
        section12_not_centralizer_le_M_of_ne_fixed_primeOrder_tau2_pre
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) (A := A) (A₀ := A₀) (X := X) (p := p)
          hM hE hp hA hA₀ hCA₀ hSylow hX_E hXA₀
      have hcent_bot : elementCentralizerIn K (a : G) = ⊥ := by
        have hbot :
            subgroupCentralizerIn (section10Msigma M) X = ⊥ :=
          section12_msigma_fixed_eq_bot_of_not_centralizer_le_M_pre
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
            (E₂ := E₂) (E₃ := E₃) (A := A) (X := X) (p := p)
            hM hE hp hA hX_E hnot
        simpa [K, X, section12_subgroupCentralizerIn_zpowers_eq_elementCentralizerIn_pre]
          using hbot
      rw [hfix_map, hcent_bot]
      intro x hx
      have hxone : x = 1 := by simpa using hx
      rw [hxone]
      simp
  have hK_le_centA₀ : K ≤ Subgroup.centralizer (A₀ : Set G) := by
    have htop_map_K : (⊤ : Subgroup K).map K.subtype = K := by
      simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := K))
    calc
      K = (⊤ : Subgroup K).map K.subtype := htop_map_K.symm
      _ =
          (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) K).map
            K.subtype := by
            simp [hsup]
      _ ≤ Subgroup.centralizer (A₀ : Set G) := by
            rw [Subgroup.map_iSup]
            refine iSup_le ?_
            intro a
            rw [Subgroup.map_iSup]
            refine iSup_le ?_
            intro ha_ne
            exact hfixed_map_le a ha_ne
  have hA₀_le_C : A₀ ≤ subgroupCentralizerIn A K := by
    intro a ha
    refine ⟨hA₀.1 ha, ?_⟩
    change a ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact ((Subgroup.mem_centralizer_iff.mp (hK_le_centA₀ hs)) a ha).symm
  have hC_le_A₀ : subgroupCentralizerIn A K ≤ A₀ := by
    intro c hc
    by_contra hcA₀
    have hc_ne : c ≠ 1 := by
      intro hc1
      exact hcA₀ (by simp [hc1])
    let X : Subgroup G := Subgroup.zpowers c
    have hX_A : X ∈ section10PrimeOrderSubgroupsIn p A := by
      simpa [X] using
        section12_zpowers_mem_primeOrderSubgroupsIn_of_rankTwo_pre hA ⟨c, hc.1⟩
          (by
            intro hsub
            exact hc_ne (by simpa using congrArg Subtype.val hsub))
    have hX_E : X ∈ section10PrimeOrderSubgroupsIn p E := by
      rcases (show X ≤ A ∧ Nat.card X = p.val from hX_A) with ⟨hXA, hXcard⟩
      exact ⟨hXA.trans (section12_rankTwo_le hA), hXcard⟩
    have hX_ne_A₀ : X ≠ A₀ := by
      intro hXeq
      exact hcA₀ (by
        have hcX : c ∈ X := by
          simp [X]
        simpa [hXeq] using hcX)
    have hnot :
        ¬ Subgroup.centralizer (X : Set G) ≤ M :=
      section12_not_centralizer_le_M_of_ne_fixed_primeOrder_tau2_pre
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (A₀ := A₀) (X := X) (p := p)
        hM hE hp hA hA₀ hCA₀ hSylow hX_E hX_ne_A₀
    have hbot :
        subgroupCentralizerIn K X = ⊥ := by
      simpa [K] using
        section12_msigma_fixed_eq_bot_of_not_centralizer_le_M_pre
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) (A := A) (X := X) (p := p)
          hM hE hp hA hX_E hnot
    have hK_le_centX : K ≤ Subgroup.centralizer (X : Set G) := by
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases Subgroup.mem_zpowers_iff.mp (by simpa [X] using hy) with ⟨n, rfl⟩
      have hcomm : Commute c s := by
        exact (Subgroup.mem_centralizer_iff.mp hc.2 s hs).symm
      simpa using (hcomm.zpow_left n).eq
    have hK_le_subcent : K ≤ subgroupCentralizerIn K X := by
      intro s hs
      exact ⟨hs, hK_le_centX hs⟩
    have hKbot : K = ⊥ := by
      exact le_bot_iff.mp (by
        intro s hs
        simpa [hbot] using hK_le_subcent hs)
    have hK_ne_bot : K ≠ ⊥ := by
      simpa [K] using theorem_10_2_e (G := G) hM
    exact hK_ne_bot hKbot
  exact le_antisymm (by simpa [K] using hC_le_A₀) (by simpa [K] using hA₀_le_C)

/-- Theorem 12.7(c). -/
public theorem CFSG.theorem_12_7_c
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    ∀ X : Subgroup G, X ∈ section10PrimeOrderSubgroupsIn p E →
      X ≠ subgroupCentralizerIn A (section10Msigma M) →
        subgroupCentralizerIn (section10Msigma M) X = ⊥ ∧
          ¬ Subgroup.centralizer (X : Set G) ≤ M := by
  classical
  obtain ⟨A₀, hA₀, hCA₀⟩ :=
    section12_exists_primeOrder_centralizer_ne_bot_of_tau2_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hM hE hp hA
  have hCA_eq_A₀ :
      subgroupCentralizerIn A (section10Msigma M) = A₀ :=
    section12_CA_msigma_eq_fixed_primeOrder_of_tau2_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (A₀ := A₀) (p := p)
      hM hE hp hA hA₀ hCA₀ hSylow
  intro X hX hXne
  have hXneA₀ : X ≠ A₀ := by
    intro hXA₀
    exact hXne (hXA₀.trans hCA_eq_A₀.symm)
  have hnot :
      ¬ Subgroup.centralizer (X : Set G) ≤ M :=
    section12_not_centralizer_le_M_of_ne_fixed_primeOrder_tau2_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (A₀ := A₀) (X := X) (p := p)
      hM hE hp hA hA₀ hCA₀ hSylow hX hXneA₀
  exact ⟨
    section12_msigma_fixed_eq_bot_of_not_centralizer_le_M_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (X := X) (p := p)
      hM hE hp hA hX hnot,
    hnot⟩


end Section12
