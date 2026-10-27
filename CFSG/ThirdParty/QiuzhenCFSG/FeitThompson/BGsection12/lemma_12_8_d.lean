module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_8_c

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_normalizer_le_normalizer_centralizer_pre
    (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro a ha
    have ha' : n⁻¹ * a * n ∈ A :=
      (Subgroup.mem_normalizer_iff''.mp hn a).1 ha
    have hcomm : (n⁻¹ * a * n) * c = c * (n⁻¹ * a * n) := hc (n⁻¹ * a * n) ha'
    calc
      a * (n * c * n⁻¹) = n * ((n⁻¹ * a * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * a * n)) * n⁻¹ := by rw [hcomm]
      _ = (n * c * n⁻¹) * a := by group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro a ha
    have ha' : n * a * n⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hn a).1 ha
    have hcomm :
        (n * a * n⁻¹) * (n * c * n⁻¹) =
          (n * c * n⁻¹) * (n * a * n⁻¹) :=
      hc (n * a * n⁻¹) ha'
    calc
      a * c = n⁻¹ * ((n * a * n⁻¹) * (n * c * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * c * n⁻¹) * (n * a * n⁻¹)) * n := by rw [hcomm]
      _ = c * a := by group

omit [IsMinCE G] in
public theorem CFSG.section12_pSubgroup_le_piCoreIn_of_mem_of_nilpotent_pre
    {H A : Subgroup G} {π : Set Nat.Primes} {p : Nat.Primes}
    (hAH : A ≤ H) (hAp : IsPGroup p.val A) (hpπ : p ∈ π)
    (hnilH : Group.IsNilpotent H) :
    A ≤ piCoreIn π H := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  let A₀ : Subgroup H := A.subgroupOf H
  have hA₀p : IsPGroup p.val A₀ :=
    hAp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := A) (K := H) hAH).symm
  have hCoreHall : IsHallSubgroup π (piCore π H) :=
    section12_piCore_isHallSubgroup_of_nilpotent hnilH
  have hA₀_le_core : A₀ ≤ piCore π H :=
    section12_pSubgroup_le_normal_hall_of_prime_mem
      (R := H) (π := π) (H := piCore π H) (A := A₀)
      hCoreHall hpπ hA₀p
  intro x hx
  let xH : H := ⟨x, hAH hx⟩
  have hxA₀ : xH ∈ A₀ := by
    simpa [A₀, xH, Subgroup.mem_subgroupOf] using hx
  have hxCore : xH ∈ piCore π H := hA₀_le_core hxA₀
  have hxCoreSub : xH ∈ (piCoreIn π H).subgroupOf H := by
    simpa [piCore_map_subtype_subgroupOf] using hxCore
  simpa [xH, Subgroup.mem_subgroupOf] using hxCoreSub

omit [IsMinCE G] in
public theorem CFSG.section12_fitting_eq_fitting_centralizer_of_normal_pSubgroup_abelian_sylow_pre
    {H A : Subgroup G} {p : Nat.Primes}
    (hAnorm : section10NormalIn A H)
    (hCA_le_H : Subgroup.centralizer (A : Set G) ≤ H)
    (hAp : IsPGroup p.val A)
    (hSylow_comm : ∀ P : Sylow p.val G, IsMulCommutative (P : Subgroup G)) :
    section8FittingSubgroup H =
      section8FittingSubgroup (Subgroup.centralizer (A : Set G)) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  let FH : Subgroup G := section8FittingSubgroup H
  let FC : Subgroup G := section8FittingSubgroup C
  have hFH_le_C : FH ≤ C := by
    simpa [FH, C] using
      section12_fitting_le_centralizer_of_normal_pSubgroup_abelian_sylow_pre
        (G := G) (H := H) (A := A) (p := p) hAnorm hAp hSylow_comm
  have hFH_le_FC : FH ≤ FC := by
    have hH_norm_FH : H ≤ Subgroup.normalizer (FH : Set G) := by
      simpa [FH] using section10_le_normalizer_fitting (G := G) H
    have hC_norm_FH : C ≤ Subgroup.normalizer (FH : Set G) :=
      hCA_le_H.trans hH_norm_FH
    have hFH_norm_C : (FH.subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hFH_le_C).2 hC_norm_FH
    simpa [FH, FC, C, section8FittingSubgroup] using
      section12_le_fittingSubgroupOf_of_normalIn_nilpotent
        (G := G) (H := C) (N := FH) hFH_le_C hFH_norm_C
        (section8FittingSubgroup_isNilpotent H)
  have hFC_le_FH : FC ≤ FH := by
    have hH_le_norm_A : H ≤ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAnorm.1).1 hAnorm.2
    have hH_norm_C : H ≤ Subgroup.normalizer (C : Set G) :=
      hH_le_norm_A.trans (by simpa [C] using
        section12_normalizer_le_normalizer_centralizer_pre (G := G) A)
    have hNormC_FC :
        Subgroup.normalizer (C : Set G) ≤ Subgroup.normalizer (FC : Set G) := by
      have hnorm :=
        section8_normalizer_map_subtype_le_of_characteristic
          (G := G) (H := C) (K := fittingSubgroup C)
      simpa [FC, C, section8FittingSubgroup, fittingSubgroupOf] using hnorm
    have hH_norm_FC : H ≤ Subgroup.normalizer (FC : Set G) :=
      hH_norm_C.trans hNormC_FC
    have hFC_le_H : FC ≤ H :=
      (section8FittingSubgroup_le C).trans hCA_le_H
    have hFC_norm_H : (FC.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hFC_le_H).2 hH_norm_FC
    simpa [FH, FC] using
      section12_le_fittingSubgroupOf_of_normalIn_nilpotent
        (G := G) (H := H) (N := FC) hFC_le_H hFC_norm_H
        (section8FittingSubgroup_isNilpotent C)
  exact le_antisymm hFH_le_FC hFC_le_FH

/-- Lemma 12.8(d). -/
public theorem CFSG.lemma_12_8_d
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G)) (hScomm : IsMulCommutative (S : Subgroup G)) :
    Subgroup.normalizer (A : Set G) =
        Subgroup.normalizer ((S : Subgroup G) : Set G) ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
        Subgroup.normalizer (E₂ : Set G) ∧
      Subgroup.normalizer (E₂ : Set G) =
        Subgroup.normalizer (((E₂ ⊔ E₃ : Subgroup G) : Set G)) ∧
      Subgroup.normalizer (((E₂ ⊔ E₃ : Subgroup G) : Set G)) =
        Subgroup.normalizer (section8FittingSubgroup E : Set G) := by
  classical
  let F : Subgroup G := section8FittingSubgroup E
  let K : Subgroup G := E₂ ⊔ E₃
  let π₂ : Set Nat.Primes := section12Tau2Primes M
  let π₂₃ : Set Nat.Primes := section12Tau2Primes M ∪ section12Tau3Primes M
  let NA : Subgroup G := Subgroup.normalizer (A : Set G)
  have hAnormE : section10NormalIn A E :=
    (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA).1
  have hCA_le_E : Subgroup.centralizer (A : Set G) ≤ E := by
    have h6 :=
      corollary_12_6_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA
    intro x hx
    simpa [h6.2.1] using h6.1 hx
  have hAp : IsPGroup p.val A := by
    have hElem := (section12_rankTwo_elementary hA).2
    have : IsElementaryAbelian p.val A := hElem
    exact IsElementaryAbelian.isPGroup p.val A
  have hSylow_comm_all : ∀ P : Sylow p.val G, IsMulCommutative (P : Subgroup G) :=
    section12_all_sylow_comm_of_one_pre (G := G) (p := p) (S := S) hScomm
  have h8a :=
    lemma_12_8_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm
  have hE2comm : IsMulCommutative E₂ := h8a.1
  have hE2normE : section10NormalIn E₂ E := h8a.2
  have h8c :=
    lemma_12_8_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm
  have hS_le_F : (S : Subgroup G) ≤ F := by
    simpa [F] using h8c.1.trans h8c.2.1
  have hF_le_E : F ≤ E := by
    simpa [F] using section8FittingSubgroup_le E
  have hS_le_E : (S : Subgroup G) ≤ E := hS_le_F.trans hF_le_E
  have hS_le_M : (S : Subgroup G) ≤ M := hS_le_E.trans hE.1.2.1
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  let SM : Sylow p.val M := S.subtype hS_le_M
  have hSM_eq_S : section10AmbientSylowSubgroup M SM = (S : Subgroup G) := by
    simpa [SM, section10AmbientSylowSubgroup] using
      (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := (S : Subgroup G)) (K := M)
        hS_le_M)
  have hA_le_SM : A ≤ section10AmbientSylowSubgroup M SM := by
    simpa [hSM_eq_S] using hAS
  have hOmegaS :
      section12OmegaOneSubgroup p (S : Subgroup G) = A := by
    have hOmega :=
      (theorem_12_5_b (G := G) (M := M) (A := A) (p := p)
        hM hp hA_M).2 SM hA_le_SM
    simpa [hSM_eq_S] using hOmega.1
  have hNS_le_NA :
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
        Subgroup.normalizer (A : Set G) := by
    have hΩchar :
        (omega₁ (G := (S : Subgroup G)) (p := p.val)).Characteristic :=
      omega₁_characteristic (G := (S : Subgroup G)) (p := p.val)
    have hleΩ :
        Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
          Subgroup.normalizer
            (((omega₁ (G := (S : Subgroup G)) (p := p.val)).map
              (S : Subgroup G).subtype : Subgroup G) : Set G) :=
      section8_normalizer_map_subtype_le_of_characteristic
        (H := (S : Subgroup G))
        (K := omega₁ (G := (S : Subgroup G)) (p := p.val))
    have hΩset_eq :
        (((omega₁ (G := (S : Subgroup G)) (p := p.val)).map
          (S : Subgroup G).subtype : Subgroup G) : Set G) = (A : Set G) := by
      simpa [section12OmegaOneSubgroup] using
        congrArg (fun L : Subgroup G => (L : Set G)) hOmegaS
    simpa [hΩset_eq] using hleΩ
  have hA_le_NA : A ≤ NA := by
    simpa [NA] using (Subgroup.le_normalizer : A ≤ Subgroup.normalizer (A : Set G))
  have hAnormNA : section10NormalIn A NA := by
    refine ⟨hA_le_NA, ?_⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hA_le_NA).2 (by simp [NA])
  have hCA_le_NA : Subgroup.centralizer (A : Set G) ≤ NA := by
    simpa [NA] using centralizer_le_normalizer A
  have hFNA_eq_FC :
      section8FittingSubgroup NA =
        section8FittingSubgroup (Subgroup.centralizer (A : Set G)) :=
    section12_fitting_eq_fitting_centralizer_of_normal_pSubgroup_abelian_sylow_pre
      (G := G) (H := NA) (A := A) (p := p)
      hAnormNA hCA_le_NA hAp hSylow_comm_all
  have hFE_eq_FC :
      F = section8FittingSubgroup (Subgroup.centralizer (A : Set G)) := by
    simpa [F] using
      section12_fitting_eq_fitting_centralizer_of_normal_pSubgroup_abelian_sylow_pre
        (G := G) (H := E) (A := A) (p := p)
        hAnormE hCA_le_E hAp hSylow_comm_all
  have hFNA_eq_FE : section8FittingSubgroup NA = F :=
    hFNA_eq_FC.trans hFE_eq_FC.symm
  have hNA_le_NF : NA ≤ Subgroup.normalizer (F : Set G) := by
    have hNA_le_NFNA : NA ≤ Subgroup.normalizer (section8FittingSubgroup NA : Set G) :=
      section10_le_normalizer_fitting (G := G) NA
    simpa [hFNA_eq_FE] using hNA_le_NFNA
  have hE2_le_F : E₂ ≤ F := by
    have hcore_eq :
        piCoreIn π₂ F = E₂ := by
      simpa [π₂, F] using
        section12_tau2_core_fitting_eq_E2_of_abelian_sylow_pre
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A)
          (p := p) (S := S) hM hE hp hA hAS hScomm
    rw [← hcore_eq]
    exact piCoreIn_le (G := G) π₂ F
  have hDerE_le_F : ambientDerivedSubgroup E ≤ F := by
    have hDerNorm : section10NormalIn (ambientDerivedSubgroup E) E :=
      section12_normalIn_ambientDerivedSubgroup (G := G) (E := E)
    simpa [F, section8FittingSubgroup] using
      section12_le_fittingSubgroupOf_of_normalIn_nilpotent
        (G := G) (H := E) (N := ambientDerivedSubgroup E)
        hDerNorm.1 hDerNorm.2
        (lemma_12_1_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE)
  have hE3normE : section10NormalIn E₃ E :=
    (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2
  have hE3_le_F : E₃ ≤ F :=
    (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).1.trans hDerE_le_F
  have hK_le_F : K ≤ F := by
    simpa [K] using sup_le hE2_le_F hE3_le_F
  have hK_le_E : K ≤ E := hK_le_F.trans hF_le_E
  have hKnormE : section10NormalIn K E := by
    simpa [K] using
      (lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2.2.1
  have hS_le_E2 : (S : Subgroup G) ≤ E₂ := by
    have hS_le_core : (S : Subgroup G) ≤ piCoreIn π₂ F :=
      section12_pSubgroup_le_piCoreIn_of_mem_of_nilpotent_pre
        (G := G) (H := F) (A := (S : Subgroup G)) (π := π₂) (p := p)
        hS_le_F S.isPGroup' (by simpa [π₂] using hp)
        (by simpa [F] using section8FittingSubgroup_isNilpotent E)
    have hcore_eq :
        piCoreIn π₂ F = E₂ := by
      simpa [π₂, F] using
        section12_tau2_core_fitting_eq_E2_of_abelian_sylow_pre
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A)
          (p := p) (S := S) hM hE hp hA hAS hScomm
    simpa [hcore_eq] using hS_le_core
  have hNE2_le_NS :
      Subgroup.normalizer (E₂ : Set G) ≤
        Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    let SE2 : Sylow p.val E₂ := S.subtype hS_le_E2
    have hSE2_norm : (SE2 : Subgroup E₂).Normal := by
      let : IsMulCommutative E₂ := hE2comm
      infer_instance
    have : Fact p.val.Prime := ⟨p.2⟩
    have : (SE2 : Subgroup E₂).Characteristic :=
      Sylow.characteristic_of_normal SE2 hSE2_norm
    have hnorm :
        Subgroup.normalizer (E₂ : Set G) ≤
          Subgroup.normalizer (((SE2 : Subgroup E₂).map E₂.subtype : Subgroup G) : Set G) :=
      section8_normalizer_map_subtype_le_of_characteristic
        (H := E₂) (K := (SE2 : Subgroup E₂))
    have hmap :
        ((SE2 : Subgroup E₂).map E₂.subtype : Subgroup G) = (S : Subgroup G) := by
      change ((S : Subgroup G).subgroupOf E₂).map E₂.subtype = (S : Subgroup G)
      exact Subgroup.map_subgroupOf_eq_of_le (G := G) (H := (S : Subgroup G)) (K := E₂)
        hS_le_E2
    simpa [hmap] using hnorm
  have hE2HallE : section12HallSubgroupIn π₂ E₂ E := by
    simpa [π₂] using section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
  rcases hE2HallE with ⟨hE2E, hHallE2E⟩
  have hE2_le_K : E₂ ≤ K := by
    simp [K]
  have hE2HallK : IsHallSubgroup π₂ (E₂.subgroupOf K) := by
    refine isHallSubgroup_of (G := K) π₂ (E₂.subgroupOf K) ?_ ?_
    · intro q hqcard
      have hcardK : Nat.card (E₂.subgroupOf K) = Nat.card E₂ :=
        natCard_subgroupOf_eq _ _ hE2_le_K
      have hcardE : Nat.card (E₂.subgroupOf E) = Nat.card E₂ :=
        natCard_subgroupOf_eq _ _ hE2E
      exact hHallE2E.p_in_pi_of_p_dvd_card q
        (by simpa [hcardK, hcardE] using hqcard)
    · intro q hqπ hqidx
      have hidxK : q.val ∣ E₂.relIndex K := by
        simpa [Subgroup.relIndex] using hqidx
      have hmul : E₂.relIndex K * K.relIndex E = E₂.relIndex E :=
        Subgroup.relIndex_mul_relIndex E₂ K E hE2_le_K hK_le_E
      have hqErel : q.val ∣ E₂.relIndex E := by
        rw [← hmul]
        exact dvd_mul_of_dvd_left hidxK _
      exact (hHallE2E.p_in_pi_of_p_dvd_index q
        (by simpa [Subgroup.relIndex] using hqErel)) hqπ
  have hE_norm_E2 : E ≤ Subgroup.normalizer (E₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE2normE.1).1 hE2normE.2
  have hK_norm_E2 : K ≤ Subgroup.normalizer (E₂ : Set G) :=
    hK_le_E.trans hE_norm_E2
  have hE2normK : (E₂.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE2_le_K).2 hK_norm_E2
  have hE2_eq_coreK : piCoreIn π₂ K = E₂ := by
    let CoreK : Subgroup G := piCoreIn π₂ K
    have hCoreK_le_K : CoreK ≤ K := by
      simpa [CoreK] using piCoreIn_le (G := G) π₂ K
    have hCoreSub_eq : CoreK.subgroupOf K = piCore π₂ K := by
      simpa [CoreK] using piCore_map_subtype_subgroupOf (G := G) π₂ K
    have hCoreSubπ : IsPiSubgroup (G := K) π₂ (CoreK.subgroupOf K) := by
      rw [hCoreSub_eq]
      exact piCore_isPiSubgroup π₂
    have : (CoreK.subgroupOf K).Normal := by
      rw [hCoreSub_eq]
      infer_instance
    have hCore_le_E2 : CoreK ≤ E₂ := by
      have hCoreSub_le_E2Sub : CoreK.subgroupOf K ≤ E₂.subgroupOf K :=
        section12_normal_piSubgroup_le_hall
          (R := K) (π := π₂) (K := CoreK.subgroupOf K) (L := E₂.subgroupOf K)
          hCoreSubπ hE2HallK
      intro x hx
      let xK : K := ⟨x, hCoreK_le_K hx⟩
      have hxCoreSub : xK ∈ CoreK.subgroupOf K := by
        simpa [xK, Subgroup.mem_subgroupOf] using hx
      have hxE2Sub : xK ∈ E₂.subgroupOf K := hCoreSub_le_E2Sub hxCoreSub
      simpa [xK, Subgroup.mem_subgroupOf] using hxE2Sub
    have hE2_le_Core : E₂ ≤ CoreK := by
      have : (E₂.subgroupOf K).Normal := hE2normK
      have hE2Subπ : IsPiSubgroup (G := K) π₂ (E₂.subgroupOf K) :=
        section12_isPiSubgroup_of_hall hE2HallK
      have hE2Sub_le_coreLocal : E₂.subgroupOf K ≤ piCore π₂ K :=
        le_piCore_of_normal_isPiSubgroup (G := K) π₂ (E₂.subgroupOf K) hE2Subπ
      intro x hx
      let xK : K := ⟨x, hE2_le_K hx⟩
      have hxE2Sub : xK ∈ E₂.subgroupOf K := by
        simpa [xK, Subgroup.mem_subgroupOf] using hx
      have hxCoreLocal : xK ∈ piCore π₂ K := hE2Sub_le_coreLocal hxE2Sub
      have hxCoreSub : xK ∈ CoreK.subgroupOf K := by
        simpa [hCoreSub_eq] using hxCoreLocal
      simpa [CoreK, xK, Subgroup.mem_subgroupOf] using hxCoreSub
    exact le_antisymm hCore_le_E2 hE2_le_Core
  have hNK_le_NE2 :
      Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (E₂ : Set G) := by
    have hnorm :
        Subgroup.normalizer (K : Set G) ≤
          Subgroup.normalizer (piCoreIn π₂ K : Set G) :=
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (G := G) (π := π₂) (H := K) (P := Subgroup.normalizer (K : Set G))
        (by intro x hx; exact hx)
    simpa [hE2_eq_coreK] using hnorm
  have hKHallE : section12HallSubgroupIn π₂₃ K E := by
    simpa [π₂₃, K] using
      section12_E2_sup_E3_hall_in_E
        (M := M) (E := E) (E₁₂ := E₁₂) (E₂ := E₂) (E₃ := E₃)
        hE.2.1 hE.2.2.2.1 hE.2.2.2.2 hE3normE
  rcases hKHallE with ⟨_hKleE_hall, hHallKE⟩
  have hKHallF : IsHallSubgroup π₂₃ (K.subgroupOf F) := by
    refine isHallSubgroup_of (G := F) π₂₃ (K.subgroupOf F) ?_ ?_
    · intro q hqcard
      have hcardF : Nat.card (K.subgroupOf F) = Nat.card K :=
        natCard_subgroupOf_eq _ _ hK_le_F
      have hcardE : Nat.card (K.subgroupOf E) = Nat.card K :=
        natCard_subgroupOf_eq _ _ hK_le_E
      exact hHallKE.p_in_pi_of_p_dvd_card q
        (by simpa [hcardF, hcardE] using hqcard)
    · intro q hqπ hqidx
      have hidxF : q.val ∣ K.relIndex F := by
        simpa [Subgroup.relIndex] using hqidx
      have hmul : K.relIndex F * F.relIndex E = K.relIndex E :=
        Subgroup.relIndex_mul_relIndex K F E hK_le_F hF_le_E
      have hqErel : q.val ∣ K.relIndex E := by
        rw [← hmul]
        exact dvd_mul_of_dvd_left hidxF _
      exact (hHallKE.p_in_pi_of_p_dvd_index q
        (by simpa [Subgroup.relIndex] using hqErel)) hqπ
  have hE_norm_K : E ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKnormE.1).1 hKnormE.2
  have hF_norm_K : F ≤ Subgroup.normalizer (K : Set G) :=
    hF_le_E.trans hE_norm_K
  have hKnormF : (K.subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK_le_F).2 hF_norm_K
  have hK_eq_coreF : piCoreIn π₂₃ F = K := by
    let CoreF : Subgroup G := piCoreIn π₂₃ F
    have hCoreF_le_F : CoreF ≤ F := by
      simpa [CoreF] using piCoreIn_le (G := G) π₂₃ F
    have hCoreSub_eq : CoreF.subgroupOf F = piCore π₂₃ F := by
      simpa [CoreF] using piCore_map_subtype_subgroupOf (G := G) π₂₃ F
    have hCoreSubπ : IsPiSubgroup (G := F) π₂₃ (CoreF.subgroupOf F) := by
      rw [hCoreSub_eq]
      exact piCore_isPiSubgroup π₂₃
    have : (CoreF.subgroupOf F).Normal := by
      rw [hCoreSub_eq]
      infer_instance
    have hCore_le_K : CoreF ≤ K := by
      have hCoreSub_le_KSub : CoreF.subgroupOf F ≤ K.subgroupOf F :=
        section12_normal_piSubgroup_le_hall
          (R := F) (π := π₂₃) (K := CoreF.subgroupOf F) (L := K.subgroupOf F)
          hCoreSubπ hKHallF
      intro x hx
      let xF : F := ⟨x, hCoreF_le_F hx⟩
      have hxCoreSub : xF ∈ CoreF.subgroupOf F := by
        simpa [xF, Subgroup.mem_subgroupOf] using hx
      have hxKSub : xF ∈ K.subgroupOf F := hCoreSub_le_KSub hxCoreSub
      simpa [xF, Subgroup.mem_subgroupOf] using hxKSub
    have hK_le_Core : K ≤ CoreF := by
      have : (K.subgroupOf F).Normal := hKnormF
      have hKSubπ : IsPiSubgroup (G := F) π₂₃ (K.subgroupOf F) :=
        section12_isPiSubgroup_of_hall hKHallF
      have hKSub_le_coreLocal : K.subgroupOf F ≤ piCore π₂₃ F :=
        le_piCore_of_normal_isPiSubgroup (G := F) π₂₃ (K.subgroupOf F) hKSubπ
      intro x hx
      let xF : F := ⟨x, hK_le_F hx⟩
      have hxKSub : xF ∈ K.subgroupOf F := by
        simpa [xF, Subgroup.mem_subgroupOf] using hx
      have hxCoreLocal : xF ∈ piCore π₂₃ F := hKSub_le_coreLocal hxKSub
      have hxCoreSub : xF ∈ CoreF.subgroupOf F := by
        simpa [hCoreSub_eq] using hxCoreLocal
      simpa [CoreF, xF, Subgroup.mem_subgroupOf] using hxCoreSub
    exact le_antisymm hCore_le_K hK_le_Core
  have hNF_le_NK :
      Subgroup.normalizer (F : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    have hnorm :
        Subgroup.normalizer (F : Set G) ≤
          Subgroup.normalizer (piCoreIn π₂₃ F : Set G) :=
      section8_le_normalizer_piCoreIn_of_le_normalizer
        (G := G) (π := π₂₃) (H := F) (P := Subgroup.normalizer (F : Set G))
        (by intro x hx; exact hx)
    simpa [hK_eq_coreF] using hnorm
  have hNA_le_NK : NA ≤ Subgroup.normalizer (K : Set G) :=
    hNA_le_NF.trans hNF_le_NK
  have hNA_le_NE2 : NA ≤ Subgroup.normalizer (E₂ : Set G) :=
    hNA_le_NK.trans hNK_le_NE2
  have hNA_le_NS : NA ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    hNA_le_NE2.trans hNE2_le_NS
  have hNS_le_NE2 :
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
        Subgroup.normalizer (E₂ : Set G) :=
    hNS_le_NA.trans hNA_le_NE2
  have hNE2_le_NK :
      Subgroup.normalizer (E₂ : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    hNE2_le_NS.trans (hNS_le_NA.trans hNA_le_NK)
  have hNK_le_NF :
      Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (F : Set G) :=
    hNK_le_NE2.trans (hNE2_le_NS.trans (hNS_le_NA.trans hNA_le_NF))
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [NA] using le_antisymm hNA_le_NS hNS_le_NA
  · exact le_antisymm hNS_le_NE2 hNE2_le_NS
  · simpa [K] using le_antisymm hNE2_le_NK hNK_le_NE2
  · simpa [K, F] using le_antisymm hNK_le_NF hNF_le_NK

/- Lemma 12.8(e) is proved later, after the reusable commutator-control
infrastructure from Lemma 12.8(f) and Corollary 12.10(a). -/


end Section12
