module

public import CFSG.Milestones.ASVolI.F4TISets

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Syl

set_option linter.unusedSectionVars false


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem ronOdd5_sylow_E (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {T : Subgroup E}
    (hT : IsSylowTwoOf T (M₁ ⊓ M₂)) : IsSylowTwoOf T ⊤ := by
  haveI := hyp.finite
  obtain ⟨hS, -⟩ := burnsideF4j_sylow_data hyp
  refine CFSG.Quasithin.H13.F431.L3.isSylowTwoOf_of_max le_top hT.2.1 fun P hP hTP _ => ?_
  have hPG : P ⊓ Gp = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) :=
    burnsideF4j_eq_of_sylow_le hS (hP.to_le inf_le_left)
      (le_inf ((burnsideF4j_S_le_sylow hyp hT).trans hTP)
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)) inf_le_right
  have hPN : P ≤ Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E) := by
    intro x hx
    rw [← hPG, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyP, hyG⟩
      exact ⟨P.mul_mem (P.mul_mem hx hyP) (P.inv_mem hx), hyp.normal.conj_mem y hyG x⟩
    · rintro ⟨hyP, hyG⟩
      refine ⟨?_, ?_⟩
      · have := P.mul_mem (P.mul_mem (P.inv_mem hx) hyP) hx
        simpa [mul_assoc] using this
      · have := hyp.normal.conj_mem _ hyG x⁻¹
        simpa [mul_assoc] using this
  exact burnsideF4j_eq_of_sylow_le hT hP hTP (hPN.trans (burnsideF4j_normalizer_S_le hyp))

theorem ronOdd5_extremal (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {s : E} (hsM : s ∈ M₁ ⊓ M₂)
    (hs2 : s * s = 1) :
    ∃ Tb : Subgroup E, IsSylowTwoOf Tb (M₁ ⊓ M₂) ∧ ∃ fb : E, fb ∈ Tb ∧ fb * fb = 1 ∧
      (s ∉ Gp → fb ∉ Gp) ∧
      IsSylowTwoOf (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({fb} : Set E))
        (cenIn Gp fb) := by
  classical
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨T₀, hT₀c⟩ := burnsideF4j_exists_sylow (M₁ ⊓ M₂)
  have hT₀ : IsSylowTwoOf T₀ (M₁ ⊓ M₂) := hT₀c
  have hT₀E := ronOdd5_sylow_E hyp hT₀
  obtain ⟨R, hR⟩ := exists_isSylowTwoOf (Subgroup.centralizer ({s} : Set E))
  have hsC : s ∈ Subgroup.centralizer ({s} : Set E) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hsR : s ∈ R := by
    have hX : IsPGroup 2 (Subgroup.zpowers s) :=
      CFSG.Quasithin.H13.U4Par.isPGroup_zpowers_of_pow (k := 1) (by rw [pow_one, pow_two, hs2])
    have hc : ∀ r ∈ R, s * r * s⁻¹ = r := fun r hr => by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hR.1 hr)
      calc s * r * s⁻¹ = (r * s) * s⁻¹ := by rw [this]
        _ = r := by group
    have hc' : ∀ r ∈ R, s⁻¹ * r * s = r := fun r hr => by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hR.1 hr)
      calc s⁻¹ * r * s = s⁻¹ * (r * s) := by group
        _ = s⁻¹ * (s * r) := by rw [this]
        _ = r := by group
    have hXN : Subgroup.zpowers s ≤ Subgroup.normalizer (R : Set E) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [hc y hy]
        exact hy
      · intro hy
        have h1 : y = s * y * s⁻¹ := by
          calc y = s⁻¹ * (s * y * s⁻¹) * s := by group
            _ = s * y * s⁻¹ := hc' _ hy
        rw [h1]
        exact hy
    have hP : IsPGroup 2 (R ⊔ Subgroup.zpowers s : Subgroup E) :=
      IsPGroup.to_sup_of_normal_left' hR.2.1 hX hXN
    have hle : R ⊔ Subgroup.zpowers s ≤ Subgroup.centralizer ({s} : Set E) :=
      sup_le hR.1 ((Subgroup.zpowers_le (H := Subgroup.centralizer ({s} : Set E))).mpr hsC)
    have heq := hR.eq_of_le le_sup_left hle hP
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  obtain ⟨m, -, hle⟩ := F7.isSylowTwoOf_exists_conj_le hT₀E (le_top : R ≤ ⊤) hR.2.1
  have hfT : m⁻¹ * s * m ∈ T₀ := by
    have := hle hsR
    rwa [mem_conjSub] at this
  have hf2 : (m⁻¹ * s * m) * (m⁻¹ * s * m) = 1 := by
    calc (m⁻¹ * s * m) * (m⁻¹ * s * m) = m⁻¹ * (s * s) * m := by group
      _ = 1 := by rw [hs2]; group
  refine ⟨T₀, hT₀, m⁻¹ * s * m, hfT, hf2, ?_, ?_⟩
  · intro hsG hfG
    apply hsG
    have := hyp.normal.conj_mem _ hfG m
    simpa [mul_assoc] using this
  · set fb := m⁻¹ * s * m with hfb
    have hCC : conjSub m⁻¹ (Subgroup.centralizer ({s} : Set E)) =
        Subgroup.centralizer ({fb} : Set E) := by
      ext y
      rw [mem_conjSub, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_singleton_iff, inv_inv]
      constructor
      · intro h
        have := congrArg (fun w => m⁻¹ * w * m) h
        simp only [hfb]
        simpa [mul_assoc] using this
      · intro h
        have := congrArg (fun w => m * w * m⁻¹) h
        simp only [hfb] at this
        simpa [mul_assoc] using this
    have hRC : IsSylowTwoOf (conjSub m⁻¹ R) (Subgroup.centralizer ({fb} : Set E)) := by
      have := F7.isSylowTwoOf_conj hR m⁻¹
      rwa [hCC] at this
    have hRT : conjSub m⁻¹ R ≤ T₀ := (le_conjSub_iff m).mp hle
    have hPR : T₀ ⊓ Subgroup.centralizer ({fb} : Set E) = conjSub m⁻¹ R :=
      hRC.eq_of_le (le_inf hRT hRC.1) inf_le_right (hT₀.2.1.to_le inf_le_left)
    have hP : IsSylowTwoOf (T₀ ⊓ Subgroup.centralizer ({fb} : Set E))
        (Subgroup.centralizer ({fb} : Set E)) := by
      rw [hPR]
      exact hRC
    have hNn : (T₀ ⊓ Subgroup.centralizer ({fb} : Set E)) ≤
        Subgroup.normalizer ((cenIn Gp fb : Subgroup E) : Set E) := by
      intro x hx
      refine Subgroup.inf_normalizer_le_normalizer_inf (H := Gp)
        (K := Subgroup.centralizer ({fb} : Set E)) ⟨?_, Subgroup.le_normalizer hx.2⟩
      rw [Subgroup.normalizer_eq_top_iff.mpr hyp.normal]
      exact Subgroup.mem_top x
    have h1 : IsSylowTwoOf ((T₀ ⊓ Subgroup.centralizer ({fb} : Set E)) ⊓ cenIn Gp fb)
        (cenIn Gp fb) :=
      F7.isSylowTwoOf_inf_normal hP (inf_le_right : cenIn Gp fb ≤ _) hNn
    have hEq : (T₀ ⊓ Subgroup.centralizer ({fb} : Set E)) ⊓ cenIn Gp fb =
        pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({fb} : Set E) := by
      rw [← burnsideF4j_sylow_inf_Gp hyp hT₀]
      ext x
      simp only [cenIn, Subgroup.mem_inf]
      tauto
    rwa [hEq] at h1

end Syl

end CFSG.ASVolI
