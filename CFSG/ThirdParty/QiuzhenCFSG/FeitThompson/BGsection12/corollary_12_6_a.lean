module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.theorem_12_5_f

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
/-- Corollary 12.6(a). -/
public theorem CFSG.section12_rankTwo_of_EData
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    A ∈ section12RankTwoElementaryAbelianIn p M := by
  rcases hE with ⟨hcomp, _hE12, _hE1, _hE2, _hE3⟩
  exact section12_rankTwo_mono hA hcomp.2.1

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_msigma_sup_rankTwo_inf_complement_eq_pre
    {M E A : Subgroup G} {p : Nat.Primes}
    (hcomp : section12ComplementToMsigma M E)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    (section10Msigma M ⊔ A) ⊓ E = A := by
  classical
  have hAE : A ≤ E := section12_rankTwo_le hA
  have hAM : A ≤ M := hAE.trans hcomp.2.1
  have hA_norm_sigma : A ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hAM.trans section12_le_normalizer_msigma
  have hσ_norm_sup : ((section10Msigma M).subgroupOf (A ⊔ section10Msigma M)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := A) (N := section10Msigma M)
      hA_norm_sigma
  apply le_antisymm
  · intro x hx
    have hx_sup' : x ∈ A ⊔ section10Msigma M := by
      simpa [sup_comm] using hx.1
    let L : Subgroup G := A ⊔ section10Msigma M
    let xL : L := ⟨x, hx_sup'⟩
    have hσ_norm_L : ((section10Msigma M).subgroupOf L).Normal := by
      simpa [L] using hσ_norm_sup
    have hL_sup :
        A.subgroupOf L ⊔ (section10Msigma M).subgroupOf L = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (A := A) (A' := section10Msigma M) (B := L)
        le_sup_left le_sup_right]
      simp [L]
    have hxL_sup : xL ∈ A.subgroupOf L ⊔ (section10Msigma M).subgroupOf L := by
      rw [hL_sup]
      exact trivial
    rcases (Subgroup.mem_sup_of_normal_right
        (s := A.subgroupOf L) (t := (section10Msigma M).subgroupOf L)
        (x := xL)).1 hxL_sup with ⟨aL, haA, sL, hsσ, hasL⟩
    let a : G := aL
    let s : G := sL
    have haA' : a ∈ A := haA
    have hsσ' : s ∈ section10Msigma M := hsσ
    have has : a * s = x := by
      simpa [a, s, xL] using congrArg Subtype.val hasL
    have hsE : s ∈ E := by
      have haE : a ∈ E := hAE haA'
      have hxE : x ∈ E := hx.2
      have hs_eq : s = a⁻¹ * x := by
        rw [← has]
        simp
      rw [hs_eq]
      exact E.mul_mem (E.inv_mem haE) hxE
    have hs_bot : s ∈ (⊥ : Subgroup G) := by
      have hsinf : s ∈ section10Msigma M ⊓ E := ⟨hsσ', hsE⟩
      simpa [hcomp.2.2.2.eq_bot] using hsinf
    have hs_one : s = 1 := by simpa using hs_bot
    have hx_eq_a : x = a := by
      rw [← has, hs_one, mul_one]
    simpa [hx_eq_a] using haA'
  · intro x hxA
    exact ⟨Subgroup.mem_sup_right hxA, hAE hxA⟩

public theorem CFSG.section12_rankTwo_normalIn_complement_of_tau2_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    section10NormalIn A E := by
  classical
  rcases hE with ⟨hcomp, hE12, hE1, hE2, hE3⟩
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData
      (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      ⟨hcomp, hE12, hE1, hE2, hE3⟩ hA
  have hSA_norm : section10NormalIn (section10Msigma M ⊔ A) M :=
    theorem_12_5_c hM hp hA_M
  rcases hSA_norm with ⟨hSA_M, hSA_sub_norm⟩
  have hM_le_norm_SA : M ≤ Subgroup.normalizer ((section10Msigma M ⊔ A : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSA_M).1 hSA_sub_norm
  have hSA_inf_E :
      (section10Msigma M ⊔ A) ⊓ E = A :=
    section12_msigma_sup_rankTwo_inf_complement_eq_pre hcomp hA
  refine ⟨section12_rankTwo_le hA, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (section12_rankTwo_le hA)]
  intro e heE
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro haA
    have heM : e ∈ M := hcomp.2.1 heE
    have hconj_SA : e * a * e⁻¹ ∈ section10Msigma M ⊔ A :=
      (Subgroup.mem_normalizer_iff.mp (hM_le_norm_SA heM) a).1
        (Subgroup.mem_sup_right haA)
    have hconj_E : e * a * e⁻¹ ∈ E :=
      E.mul_mem (E.mul_mem heE (section12_rankTwo_le hA haA)) (E.inv_mem heE)
    have hconj_inf : e * a * e⁻¹ ∈ (section10Msigma M ⊔ A) ⊓ E :=
      ⟨hconj_SA, hconj_E⟩
    simpa [hSA_inf_E] using hconj_inf
  · intro hconjA
    have heinvE : e⁻¹ ∈ E := E.inv_mem heE
    have heinvM : e⁻¹ ∈ M := hcomp.2.1 heinvE
    have hback_SA : e⁻¹ * (e * a * e⁻¹) * (e⁻¹)⁻¹ ∈ section10Msigma M ⊔ A :=
      (Subgroup.mem_normalizer_iff.mp (hM_le_norm_SA heinvM) (e * a * e⁻¹)).1
        (Subgroup.mem_sup_right hconjA)
    have hback_E : e⁻¹ * (e * a * e⁻¹) * (e⁻¹)⁻¹ ∈ E :=
      E.mul_mem (E.mul_mem heinvE (section12_rankTwo_le hA hconjA)) (E.inv_mem heinvE)
    have hback_inf :
        e⁻¹ * (e * a * e⁻¹) * (e⁻¹)⁻¹ ∈ (section10Msigma M ⊔ A) ⊓ E :=
      ⟨hback_SA, hback_E⟩
    have hbackA : e⁻¹ * (e * a * e⁻¹) * (e⁻¹)⁻¹ ∈ A := by
      simpa [hSA_inf_E] using hback_inf
    simpa [mul_assoc] using hbackA

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_mem_omegaOneSubgroup_of_mem_pow_eq_one_pre
    {H : Subgroup G} {p : Nat.Primes} {x : G}
    (hxH : x ∈ H) (hxp : x ^ p.val = 1) :
    x ∈ section12OmegaOneSubgroup p H := by
  let xH : H := ⟨x, hxH⟩
  have hxΩ : xH ∈ omega₁ (G := H) (p := p.val) := by
    rw [omega₁, omega]
    exact Subgroup.subset_closure (by simpa [xH] using hxp)
  exact Subgroup.mem_map.mpr ⟨xH, hxΩ, rfl⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_primeOrder_le_omegaOneSubgroup_of_le_pre
    {H X : Subgroup G} {p : Nat.Primes}
    (hX : X ∈ section10PrimeOrderSubgroupsIn p H) :
    X ≤ section12OmegaOneSubgroup p H := by
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXH, hXcard⟩
  intro x hxX
  have hxpowX : (⟨x, hxX⟩ : X) ^ Nat.card X = 1 := pow_card_eq_one'
  have hxpow : x ^ p.val = 1 := by
    simpa [hXcard] using congrArg Subtype.val hxpowX
  exact section12_mem_omegaOneSubgroup_of_mem_pow_eq_one_pre (hXH hxX) hxpow

public theorem CFSG.section12_primeOrderSubgroupsIn_E_eq_rankTwo_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAnorm : section10NormalIn A E) :
    section10PrimeOrderSubgroupsIn p E = section10PrimeOrderSubgroupsIn p A := by
  classical
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  rcases theorem_12_5_b hM hp hA_M with ⟨_hSylowAb, hOmega⟩
  ext X
  constructor
  · intro hX
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXE, hXcard⟩
    haveI : Fact p.val.Prime := ⟨p.2⟩
    have hAp : IsPGroup p.val A := by
      rcases section12_rankTwo_elementary hA with ⟨_hcard, hElem⟩
      haveI : IsElementaryAbelian p.val A := hElem
      exact IsElementaryAbelian.isPGroup p.val A
    have hXp : IsPGroup p.val X := by
      refine IsPGroup.of_card (p := p.val) (G := X) (n := 1) ?_
      simpa [pow_one] using hXcard
    have hX_norm_A : X ≤ Subgroup.normalizer (A : Set G) := by
      have hE_le_norm_A : E ≤ Subgroup.normalizer (A : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hAnorm.1).1 hAnorm.2
      exact hXE.trans hE_le_norm_A
    have hJoin_p : IsPGroup p.val (A ⊔ X : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hAp hXp hX_norm_A
    have hJoin_M : A ⊔ X ≤ M :=
      sup_le (section12_rankTwo_le hA_M) (hXE.trans hE.1.2.1)
    let Jsub : Subgroup M := (A ⊔ X).subgroupOf M
    have hJsub_p : IsPGroup p.val Jsub :=
      hJoin_p.of_equiv (Subgroup.subgroupOfEquivOfLe hJoin_M).symm
    obtain ⟨P, hJ_le_P⟩ := IsPGroup.exists_le_sylow (G := M) (p := p.val) hJsub_p
    have hA_le_Pamb : A ≤ section10AmbientSylowSubgroup M P := by
      intro a ha
      have haJ : (⟨a, hJoin_M (Subgroup.mem_sup_left ha)⟩ : M) ∈ Jsub :=
        Subgroup.mem_sup_left ha
      exact Subgroup.mem_map.mpr ⟨⟨a, hJoin_M (Subgroup.mem_sup_left ha)⟩, hJ_le_P haJ, rfl⟩
    have hOmega_eq :
        section12OmegaOneSubgroup p (section10AmbientSylowSubgroup M P) = A :=
      (hOmega P hA_le_Pamb).1
    have hX_le_Pamb : X ≤ section10AmbientSylowSubgroup M P := by
      intro x hx
      have hxJ : (⟨x, hJoin_M (Subgroup.mem_sup_right hx)⟩ : M) ∈ Jsub :=
        Subgroup.mem_sup_right hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hJoin_M (Subgroup.mem_sup_right hx)⟩, hJ_le_P hxJ, rfl⟩
    have hX_in_Pamb :
        X ∈ section10PrimeOrderSubgroupsIn p (section10AmbientSylowSubgroup M P) := by
      simpa [section10PrimeOrderSubgroupsIn] using ⟨hX_le_Pamb, hXcard⟩
    have hX_le_A : X ≤ A := by
      intro x hx
      have hxΩ : x ∈ section12OmegaOneSubgroup p (section10AmbientSylowSubgroup M P) :=
        section12_primeOrder_le_omegaOneSubgroup_of_le_pre hX_in_Pamb hx
      simpa [hOmega_eq] using hxΩ
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hX_le_A, hXcard⟩
  · intro hX
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXA, hXcard⟩
    have hAE : A ≤ E := section12_rankTwo_le hA
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hXA.trans hAE, hXcard⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_msigma_inf_normalizer_rankTwo_le_centralizer_pre
    {M E A : Subgroup G} {p : Nat.Primes}
    (hcomp : section12ComplementToMsigma M E)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    section10Msigma M ⊓ Subgroup.normalizer (A : Set G) ≤
      subgroupCentralizerIn (section10Msigma M) A := by
  classical
  have hAE : A ≤ E := section12_rankTwo_le hA
  have hAM : A ≤ M := hAE.trans hcomp.2.1
  have hA_norm_sigma : A ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hAM.trans section12_le_normalizer_msigma
  intro s hs
  refine ⟨hs.1, ?_⟩
  change s ∈ Subgroup.centralizer (A : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro a haA
  have hs_norm_A : s ∈ Subgroup.normalizer (A : Set G) := hs.2
  have hconjA : s * a * s⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hs_norm_A a).1 haA
  have hcommA : s * a * s⁻¹ * a⁻¹ ∈ A :=
    A.mul_mem hconjA (A.inv_mem haA)
  have ha_norm_sigma : a ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    hA_norm_sigma haA
  have hconj_sigma : a * s⁻¹ * a⁻¹ ∈ section10Msigma M :=
    (Subgroup.mem_normalizer_iff.mp ha_norm_sigma s⁻¹).1
      ((section10Msigma M).inv_mem hs.1)
  have hcomm_sigma : s * a * s⁻¹ * a⁻¹ ∈ section10Msigma M := by
    simpa [mul_assoc] using (section10Msigma M).mul_mem hs.1 hconj_sigma
  have hcomm_bot : s * a * s⁻¹ * a⁻¹ ∈ (⊥ : Subgroup G) := by
    have hcomm_inf : s * a * s⁻¹ * a⁻¹ ∈ section10Msigma M ⊓ E :=
      ⟨hcomm_sigma, hAE hcommA⟩
    simpa [hcomp.2.2.2.eq_bot] using hcomm_inf
  have hcomm_one : s * a * s⁻¹ * a⁻¹ = 1 := by simpa using hcomm_bot
  have hconj_eq : s * a * s⁻¹ = a := by
    exact mul_inv_eq_one.mp hcomm_one
  calc
    a * s = s * (s⁻¹ * a * s) := by group
    _ = s * a := by
      have hconj_inv : s⁻¹ * a * s = a := by
        calc
          s⁻¹ * a * s = s⁻¹ * (s * a * s⁻¹) * s := by rw [hconj_eq]
          _ = a := by group
      rw [hconj_inv]

public theorem CFSG.section12_normalizerIn_rankTwo_eq_complement_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAnorm : section10NormalIn A E) :
    subgroupNormalizerIn M (A : Set G) = E := by
  classical
  rcases hE with ⟨hcomp, _hE12, _hE1, _hE2, _hE3⟩
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) ⟨hcomp, _hE12, _hE1, _hE2, _hE3⟩ hA
  have hCbot : subgroupCentralizerIn (section10Msigma M) A = ⊥ :=
    theorem_12_5_d hM hp hA_M
  have hE_le_normA : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAnorm.1).1 hAnorm.2
  have hσ_norm_le_cent :
      section10Msigma M ⊓ Subgroup.normalizer (A : Set G) ≤
        subgroupCentralizerIn (section10Msigma M) A :=
    section12_msigma_inf_normalizer_rankTwo_le_centralizer_pre hcomp hA
  apply le_antisymm
  · intro x hx
    rcases (by simpa [subgroupNormalizerIn] using hx) with ⟨hxNormA, hxM⟩
    let S : Subgroup M := section10MsigmaSubgroup M
    let Ec : Subgroup M := E.subgroupOf M
    let xM : M := ⟨x, hxM⟩
    have hcomp' : Ec.IsComplement' S :=
      section12_complement_to_msigma_isComplement' (M := M) (E := E) hcomp
    have hx_top : xM ∈ (⊤ : Subgroup M) := trivial
    have hx_sup : xM ∈ Ec ⊔ S := by
      rw [hcomp'.sup_eq_top]
      exact hx_top
    have hS_norm : S.Normal := section10MsigmaSubgroup_normal (M := M)
    rcases (Subgroup.mem_sup_of_normal_right (s := Ec) (t := S) (x := xM)).1 hx_sup with
      ⟨eM, heE, sM, hsS, hes⟩
    let e : G := eM
    let s : G := sM
    have heE' : e ∈ E := heE
    have hsσ : s ∈ section10Msigma M := by
      change ((sM : M) : G) ∈ section10Msigma M
      change sM ∈ (section10Msigma M).subgroupOf M
      simpa [section12Msigma_subgroupOf_eq] using hsS
    have hx_eq : x = e * s := by
      simpa [e, s, xM] using congrArg Subtype.val hes.symm
    have heNormA : e ∈ Subgroup.normalizer (A : Set G) := hE_le_normA heE'
    have hsNormA : s ∈ Subgroup.normalizer (A : Set G) := by
      have hs_eq : s = e⁻¹ * x := by
        rw [hx_eq]
        simp
      rw [hs_eq]
      exact (Subgroup.normalizer (A : Set G)).mul_mem
        ((Subgroup.normalizer (A : Set G)).inv_mem heNormA) hxNormA
    have hsCent : s ∈ subgroupCentralizerIn (section10Msigma M) A :=
      hσ_norm_le_cent ⟨hsσ, hsNormA⟩
    have hsBot : s ∈ (⊥ : Subgroup G) := by
      simpa [hCbot] using hsCent
    have hs_one : s = 1 := by simpa using hsBot
    rw [hx_eq, hs_one, mul_one]
    exact heE'
  · intro x hxE
    exact ⟨hE_le_normA hxE, hcomp.2.1 hxE⟩

public theorem CFSG.section12_not_normalizer_rankTwo_le_M_pre
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    ¬ Subgroup.normalizer (A : Set G) ≤ M := by
  classical
  intro hNormA_M
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  rcases theorem_12_5_b hM hp hA_M with ⟨_hSylowAb, hOmega⟩
  have hAsub_p : IsPGroup p.val (A.subgroupOf M) :=
    section12_rankTwo_subgroupOf_isPGroup hA_M
  obtain ⟨P, hA_le_P⟩ := IsPGroup.exists_le_sylow (G := M) (p := p.val) hAsub_p
  have hA_le_Pamb : A ≤ section10AmbientSylowSubgroup M P := by
    intro a ha
    have haM : a ∈ M := section12_rankTwo_le hA_M ha
    exact Subgroup.mem_map.mpr ⟨⟨a, haM⟩, hA_le_P (by simpa [Subgroup.mem_subgroupOf] using ha), rfl⟩
  rcases hOmega P hA_le_Pamb with ⟨hOmega_eq, hNormP_not⟩
  have hNormP_le_NormA :
      Subgroup.normalizer ((section10AmbientSylowSubgroup M P : Subgroup G) : Set G) ≤
        Subgroup.normalizer (A : Set G) := by
    have hΩchar :
        (omega₁ (G := section10AmbientSylowSubgroup M P) (p := p.val)).Characteristic :=
      omega₁_characteristic (G := section10AmbientSylowSubgroup M P) (p := p.val)
    have hleΩ :
        Subgroup.normalizer ((section10AmbientSylowSubgroup M P : Subgroup G) : Set G) ≤
          Subgroup.normalizer
            (((omega₁ (G := section10AmbientSylowSubgroup M P) (p := p.val)).map
              (section10AmbientSylowSubgroup M P).subtype : Subgroup G) : Set G) :=
      section8_normalizer_map_subtype_le_of_characteristic
        (H := section10AmbientSylowSubgroup M P)
        (K := omega₁ (G := section10AmbientSylowSubgroup M P) (p := p.val))
    have hΩset_eq :
        (((omega₁ (G := section10AmbientSylowSubgroup M P) (p := p.val)).map
          (section10AmbientSylowSubgroup M P).subtype : Subgroup G) : Set G) = (A : Set G) := by
      simpa [section12OmegaOneSubgroup] using
        congrArg (fun K : Subgroup G => (K : Set G)) hOmega_eq
    simpa [hΩset_eq] using hleΩ
  exact hNormP_not (hNormP_le_NormA.trans hNormA_M)

public theorem CFSG.corollary_12_6_a
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    section10NormalIn A E ∧
      section10PrimeOrderSubgroupsIn p E = section10PrimeOrderSubgroupsIn p A := by
  classical
  have hAnorm : section10NormalIn A E :=
    section12_rankTwo_normalIn_complement_of_tau2_pre hM hE hp hA
  exact ⟨hAnorm, section12_primeOrderSubgroupsIn_E_eq_rankTwo_pre hM hE hp hA hAnorm⟩


end Section12
