module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Data

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
open scoped commutatorElement

private abbrev teNV_Aset : Set (Fin 4 → ℤ) := twE6A

private def teNV_Aroot : Fin 3 → (Fin 4 → ℤ) :=
  ![![1, 2, 4, 2], ![1, 3, 4, 2], ![2, 3, 4, 2]]

private def teNV_ArootT : Fin 3 → (Fin (Tag.rank .F4) → ℤ) :=
  ![![1, 2, 4, 2], ![1, 3, 4, 2], ![2, 3, 4, 2]]

private abbrev teNV_third : Fin (Tag.rank .F4) := ⟨2, by decide⟩

private abbrev teNV_lastD
    {k : Type} [Field k] (θ : k →+* k) : Fin (twistedDatum k θ).rank := twE6Last

private lemma teNV_Aset_mem {v : Fin 4 → ℤ} (h : v ∈ teNV_Aset) :
    v = ![1, 2, 4, 2] ∨ v = ![1, 3, 4, 2] ∨ v = ![2, 3, 4, 2] := by
  have h' : v ∈ (insert ![1, 2, 4, 2] (insert ![1, 3, 4, 2] {![2, 3, 4, 2]}) :
      Set (Fin 4 → ℤ)) := h
  rw [Set.mem_insert_iff] at h'
  rcases h' with h' | h'
  · exact Or.inl h'
  · rw [Set.mem_insert_iff] at h'
    rcases h' with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Set.mem_singleton_iff.mp h'))

private lemma teNV_Aset_iff_range {v : Fin 4 → ℤ} :
    v ∈ teNV_Aset ↔ ∃ t : Fin 3, teNV_Aroot t = v := by
  constructor
  · intro h
    rcases teNV_Aset_mem h with h | h | h
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, by rw [h]; rfl⟩
    · exact ⟨2, by rw [h]; rfl⟩
  · rintro ⟨t, rfl⟩
    have h' : teNV_Aroot t ∈ (insert ![1, 2, 4, 2] (insert ![1, 3, 4, 2] {![2, 3, 4, 2]}) :
        Set (Fin 4 → ℤ)) := by
      fin_cases t
      · exact Set.mem_insert_iff.2 (Or.inl rfl)
      · exact Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2 (Or.inl rfl)))
      · exact Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2 (Or.inr
          (Set.mem_singleton_iff.2 rfl))))
    exact h'

private lemma teNV_range_eq :
    twE6A = Set.range teNV_ArootT := by
  ext β
  constructor
  · intro hβ
    obtain ⟨t, ht⟩ := teNV_Aset_iff_range.1 hβ
    exact ⟨t, ht⟩
  · rintro ⟨t, rfl⟩
    exact teNV_Aset_iff_range.2 ⟨t, rfl⟩

private lemma teNV_ArootT_surj {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ twE6A) :
    ∃ t : Fin 3, teNV_ArootT t = γ := by
  obtain ⟨t, ht⟩ := teNV_Aset_iff_range.1 hγ
  exact ⟨t, ht⟩

private lemma teNV_ArootT_mem (t : Fin 3) : teNV_ArootT t ∈ twE6A :=
  teNV_Aset_iff_range.2 ⟨t, rfl⟩

private lemma teNV_memF4_iff
    (v : Fin (Tag.rank .F4) → ℤ) : memF4 v = true ↔ IsRoot .F4 v :=
  StringData.memDec_iff (Tag.rootCertificate_check .F4) (Tag.stringData_check .F4)

private lemma teNV_apply_nsmul_add {ι : Type} (i : ι) (a b : ℕ) (x y : ι → ℤ) :
    (a • x + b • y) i = (a : ℤ) * x i + (b : ℤ) * y i := by
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [nsmul_eq_mul, nsmul_eq_mul]

private lemma teNV_ArootT_isRoot
    (t : Fin 3) : IsRoot .F4 (teNV_ArootT t) := by
  fin_cases t <;> exact (teNV_memF4_iff _).1 (by decide +kernel)

private lemma teNV_ArootT_level (t : Fin 3) : teNV_ArootT t twE6Last = 2 := by
  fin_cases t <;> decide +kernel

private lemma teNV_ArootT_coord_ge_one (t : Fin 3) (j : Fin (Tag.rank .F4))
    (hj : j ≠ twE6Last) : 1 ≤ teNV_ArootT t j := by
  fin_cases t <;> fin_cases j <;> simp_all <;> decide +kernel

private lemma teNV_ArootT_third (t : Fin 3) : teNV_ArootT t teNV_third = 4 := by
  fin_cases t <;> decide +kernel

private lemma teNV_A_isRoot
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ twE6A) : IsRoot .F4 γ := by
  obtain ⟨t, rfl⟩ := teNV_ArootT_surj hγ
  exact teNV_ArootT_isRoot t

private lemma teNV_A_level {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ twE6A) :
    γ twE6Last = 2 := by
  obtain ⟨t, rfl⟩ := teNV_ArootT_surj hγ
  exact teNV_ArootT_level t

private lemma teNV_alpha_isRoot :
    IsRoot .F4 twE6Alpha :=
  (teNV_memF4_iff _).1 (by decide +kernel)

private lemma teNV_alpha_level : twE6Alpha twE6Last = 2 := by decide +kernel

private lemma teNV_alpha_third : twE6Alpha teNV_third = 3 := by decide +kernel

private lemma teNV_alpha_coord_ge_one (j : Fin (Tag.rank .F4)) (hj : j ≠ twE6Last) :
    1 ≤ twE6Alpha j := by
  fin_cases j <;> simp_all <;> decide +kernel

private lemma teNV_level_le_two_check :
    ((List.range (Tag.rootCertificate .F4).roots.length).all fun m =>
      decide (f4Root m twE6Last ≤ 2)) = true := by
  decide +kernel

private lemma teNV_pos_level_check :
    ((List.range (Tag.rootCertificate .F4).roots.length).all fun m =>
      decide (ht (f4Root m) ≤ 0) || decide (0 ≤ f4Root m twE6Last)) = true := by
  decide +kernel

private lemma teNV_coord_le_four_check :
    ((List.range (Tag.rootCertificate .F4).roots.length).all fun m =>
      (List.finRange (Tag.rank .F4)).all fun l =>
        decide (f4Root m l ≤ 4)) = true := by
  decide +kernel

private lemma teNV_level_le_two
    {δ : Fin (Tag.rank .F4) → ℤ} (hδ : IsRoot .F4 δ) : δ twE6Last ≤ 2 := by
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hδ
  have h := teNV_level_le_two_check
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h m hm

private lemma teNV_level_nonneg_of_ht_pos
    {δ : Fin (Tag.rank .F4) → ℤ} (hδ : IsRoot .F4 δ) (hδpos : 0 < ht δ) :
    0 ≤ δ twE6Last := by
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hδ
  have h := teNV_pos_level_check
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h m hm with hle | hge
  · exact absurd hδpos (not_lt.2 hle)
  · exact hge

private lemma teNV_coord_le_four
    {δ : Fin (Tag.rank .F4) → ℤ} (hδ : IsRoot .F4 δ) (l : Fin (Tag.rank .F4)) :
    δ l ≤ 4 := by
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hδ
  have h := teNV_coord_le_four_check
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, true_implies,
    decide_eq_true_eq] at h
  exact h m hm l

private def teNV_inA (v : Fin (Tag.rank .F4) → ℤ) : Bool :=
  (List.finRange 3).any fun t =>
    (List.finRange (Tag.rank .F4)).all fun j => decide (v j = teNV_ArootT t j)

private lemma teNV_inA_eq_true
    {v : Fin (Tag.rank .F4) → ℤ} (h : teNV_inA v = true) : v ∈ twE6A := by
  simp only [teNV_inA, List.any_eq_true, List.mem_finRange, List.all_eq_true, true_and,
    decide_eq_true_eq] at h
  obtain ⟨t, ht⟩ := h
  rw [teNV_range_eq]
  exact ⟨t, funext fun j => (ht j trivial).symm⟩

private lemma teNV_openCone_A_check :
    ((List.range (Tag.rootCertificate .F4).roots.length).all fun m =>
      decide (ht (f4Root m) ≤ 0) ||
        (List.range 8).all fun a =>
          (List.finRange 3).all fun t =>
            decide (memF4 (a • f4Root m + teNV_ArootT t) = false) ||
              decide (teNV_inA (a • f4Root m + teNV_ArootT t) = true)) = true := by
  decide +kernel

private lemma teNV_openCone_alpha_check :
    ((List.range (Tag.rootCertificate .F4).roots.length).all fun m =>
      decide (ht (f4Root m) ≤ 0) ||
        (List.range 8).all fun a =>
          decide (a = 0) ||
            decide (memF4 (a • f4Root m + twE6Alpha) = false) ||
              decide (teNV_inA (a • f4Root m + twE6Alpha) = true)) = true := by
  decide +kernel

private lemma teNV_openCone_A
    {δ γ : Fin (Tag.rank .F4) → ℤ}
    (hδroot : IsRoot .F4 δ) (hδpos : 0 < ht δ) (hγ : γ ∈ twE6A) :
    openCone {β : Fin (Tag.rank .F4) → ℤ | IsRoot .F4 β} δ γ ⊆ twE6A := by
  obtain ⟨t, hγt⟩ := teNV_ArootT_surj hγ
  rw [← hγt]
  have hδroot' := hδroot
  obtain ⟨m, hm, hδm⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hδroot
  rintro ε ⟨hεroot, a, b, ha, hb, rfl⟩
  have hδnn : ∀ j, 0 ≤ δ j := by
    rcases hδroot'.nonneg_or_nonpos with h | h
    · exact h
    · exfalso
      have hle : ht δ ≤ 0 := by
        rw [ht]
        exact Finset.sum_nonpos fun j _ => h j
      omega
  have hεle : (a • δ + b • teNV_ArootT t) twE6Last ≤ 2 := teNV_level_le_two hεroot
  have hlv := teNV_apply_nsmul_add twE6Last a b δ (teNV_ArootT t)
  rw [hlv, teNV_ArootT_level t] at hεle
  have hδge : 0 ≤ δ twE6Last := hδnn twE6Last
  have haZ : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
  have hb1 : b = 1 := by
    have hbZ : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
    have hle : (b : ℤ) * 2 ≤ 2 := by nlinarith
    omega
  have hδ0 : δ twE6Last = 0 := by
    have hbZ1 : (b : ℤ) = 1 := by exact_mod_cast hb1
    rw [hbZ1, one_mul] at hεle
    have h1 : (a : ℤ) * (δ twE6Last) ≤ 0 := by linarith
    have h2 : 0 ≤ (a : ℤ) * (δ twE6Last) := mul_nonneg (by positivity) hδge
    have h3 : (a : ℤ) * (δ twE6Last) = 0 := le_antisymm h1 h2
    exact (mul_eq_zero.mp h3).resolve_left (by omega)
  have ha3 : a ≤ 3 := by
    have hex : ∃ j : Fin (Tag.rank .F4), 0 < δ j := by
      by_contra h
      have h' : ∀ j, δ j ≤ 0 := fun j => by
        by_contra hj
        exact h ⟨j, not_le.mp hj⟩
      have hle : ht δ ≤ 0 := by
        rw [ht]
        exact Finset.sum_nonpos fun j _ => h' j
      omega
    obtain ⟨j, hj⟩ := hex
    have hjlast : j ≠ twE6Last := by
      intro h
      rw [h, hδ0] at hj
      omega
    have hγj : (1 : ℤ) ≤ teNV_ArootT t j := by
      exact_mod_cast teNV_ArootT_coord_ge_one t j hjlast
    have hεj : (a • δ + b • teNV_ArootT t) j ≤ 4 := teNV_coord_le_four hεroot j
    have hbZ1 : (b : ℤ) = 1 := by exact_mod_cast hb1
    have hcj := teNV_apply_nsmul_add j a b δ (teNV_ArootT t)
    rw [hcj, hbZ1, one_mul] at hεj
    have hδj1 : (1 : ℤ) ≤ δ j := by omega
    have : (a : ℤ) ≤ 3 := by nlinarith
    exact_mod_cast this
  have hεroot' : IsRoot .F4 (a • δ + teNV_ArootT t) := by simpa [hb1] using hεroot
  have hchk := teNV_openCone_A_check
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    List.mem_finRange, true_implies] at hchk
  rcases hchk m hm with hle | hrest
  · exfalso
    have hle' : ht δ ≤ 0 := by simpa [hδm] using hle
    exact absurd hδpos (not_lt.2 hle')
  · rcases hrest a (by omega) t with hnr | hina
    · exfalso
      have htrue : memF4 (a • f4Root m + teNV_ArootT t) = true :=
        (teNV_memF4_iff _).2 (by simpa [hδm] using hεroot')
      rw [hnr] at htrue
      exact Bool.false_ne_true htrue
    · have hmem := teNV_inA_eq_true hina
      simpa [hb1, hδm] using hmem

private lemma teNV_openCone_alpha
    {δ : Fin (Tag.rank .F4) → ℤ}
    (hδroot : IsRoot .F4 δ) (hδpos : 0 < ht δ) :
    openCone {β : Fin (Tag.rank .F4) → ℤ | IsRoot .F4 β} δ twE6Alpha ⊆ twE6A := by
  have hδroot' := hδroot
  obtain ⟨m, hm, hδm⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hδroot
  rintro ε ⟨hεroot, a, b, ha, hb, rfl⟩
  have hδnn : ∀ j, 0 ≤ δ j := by
    rcases hδroot'.nonneg_or_nonpos with h | h
    · exact h
    · exfalso
      have hle : ht δ ≤ 0 := by
        rw [ht]
        exact Finset.sum_nonpos fun j _ => h j
      omega
  have hεle : (a • δ + b • twE6Alpha) twE6Last ≤ 2 := teNV_level_le_two hεroot
  have hlv := teNV_apply_nsmul_add twE6Last a b δ twE6Alpha
  rw [hlv, teNV_alpha_level] at hεle
  have hδge : 0 ≤ δ twE6Last := hδnn twE6Last
  have haZ : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
  have hb1 : b = 1 := by
    have hbZ : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
    have hle : (b : ℤ) * 2 ≤ 2 := by nlinarith
    omega
  have hδ0 : δ twE6Last = 0 := by
    have hbZ1 : (b : ℤ) = 1 := by exact_mod_cast hb1
    rw [hbZ1, one_mul] at hεle
    have h1 : (a : ℤ) * (δ twE6Last) ≤ 0 := by linarith
    have h2 : 0 ≤ (a : ℤ) * (δ twE6Last) := mul_nonneg (by positivity) hδge
    have h3 : (a : ℤ) * (δ twE6Last) = 0 := le_antisymm h1 h2
    exact (mul_eq_zero.mp h3).resolve_left (by omega)
  have ha3 : a ≤ 3 := by
    have hex : ∃ j : Fin (Tag.rank .F4), 0 < δ j := by
      by_contra h
      have h' : ∀ j, δ j ≤ 0 := fun j => by
        by_contra hj
        exact h ⟨j, not_le.mp hj⟩
      have hle : ht δ ≤ 0 := by
        rw [ht]
        exact Finset.sum_nonpos fun j _ => h' j
      omega
    obtain ⟨j, hj⟩ := hex
    have hjlast : j ≠ twE6Last := by
      intro h
      rw [h, hδ0] at hj
      omega
    have hγj : (1 : ℤ) ≤ twE6Alpha j := by
      exact_mod_cast teNV_alpha_coord_ge_one j hjlast
    have hεj : (a • δ + b • twE6Alpha) j ≤ 4 := teNV_coord_le_four hεroot j
    have hbZ1 : (b : ℤ) = 1 := by exact_mod_cast hb1
    have hcj := teNV_apply_nsmul_add j a b δ twE6Alpha
    rw [hcj, hbZ1, one_mul] at hεj
    have hδj1 : (1 : ℤ) ≤ δ j := by omega
    have : (a : ℤ) ≤ 3 := by nlinarith
    exact_mod_cast this
  have hεroot' : IsRoot .F4 (a • δ + twE6Alpha) := by simpa [hb1] using hεroot
  have hchk := teNV_openCone_alpha_check
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hchk
  rcases hchk m hm with hle | hrest
  · exfalso
    have hle' : ht δ ≤ 0 := by simpa [hδm] using hle
    exact absurd hδpos (not_lt.2 hle')
  · rcases hrest a (by omega) with (hzero | hnr) | hina
    · omega
    · exfalso
      have htrue : memF4 (a • f4Root m + twE6Alpha) = true :=
        (teNV_memF4_iff _).2 (by simpa [hδm] using hεroot')
      rw [hnr] at htrue
      exact Bool.false_ne_true htrue
    · have hmem := teNV_inA_eq_true hina
      simpa [hb1, hδm] using hmem

private lemma teNV_openCone_eq_emptyD
    {k : Type} [Field k] (θ : k →+* k) {δ γ : Fin (twistedDatum k θ).rank → ℤ}
    (hδ : δ ∈ (twistedDatum k θ).roots) (hγ : γ ∈ (twistedDatum k θ).roots)
    (hsum : 3 ≤ δ (teNV_lastD θ) + γ (teNV_lastD θ)) :
    openCone (twistedDatum k θ).roots δ γ = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro ε ⟨hε, a, b, ha, hb, rfl⟩
  have hδroot : IsRoot .F4 δ := isRoot_of_mem_twistedDatum_roots θ hδ
  have hγroot : IsRoot .F4 γ := isRoot_of_mem_twistedDatum_roots θ hγ
  have hεroot : IsRoot .F4 (a • δ + b • γ) := isRoot_of_mem_twistedDatum_roots θ hε
  have hδle : δ (teNV_lastD θ) ≤ 2 := teNV_level_le_two hδroot
  have hγle : γ (teNV_lastD θ) ≤ 2 := teNV_level_le_two hγroot
  have hδ1 : (1 : ℤ) ≤ δ (teNV_lastD θ) := by omega
  have hγ1 : (1 : ℤ) ≤ γ (teNV_lastD θ) := by omega
  have hlv := teNV_apply_nsmul_add (teNV_lastD θ) a b δ γ
  have hge : 3 ≤ (a • δ + b • γ) (teNV_lastD θ) := by
    rw [hlv]
    have ha1 : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb1 : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  have hle := teNV_level_le_two hεroot
  rw [hlv] at hle
  omega

private lemma teNV_commute_of_level_sumD
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {δ γ : Fin (twistedDatum k θ).rank → ℤ}
    (hδ : δ ∈ (twistedDatum k θ).roots) (hγ : γ ∈ (twistedDatum k θ).roots)
    (hsum : 3 ≤ δ (teNV_lastD θ) + γ (teNV_lastD θ)) :
    ∀ x ∈ (twistedDatum k θ).rootGroup δ, ∀ y ∈ (twistedDatum k θ).rootGroup γ,
      Commute x y := by
  intro x hx y hy
  by_cases hδγ : δ = γ
  · have hx' : x ∈ (twistedDatum k θ).rootGroup γ := by rwa [hδγ] at hx
    have h2 : 2 • γ ∉ (twistedDatum k θ).roots :=
      CFSG.LieType.TitsSimplicity.two_smul_notMem_roots
        (show (twistedDatum k θ).divisible = ∅ from rfl) hγ
    have hmem : ⁅x, y⁆ ∈ ⁅(twistedDatum k θ).rootGroup γ, (twistedDatum k θ).rootGroup γ⁆ :=
      Subgroup.commutator_mem_commutator hx' hy
    rw [(twistedDatum_rootGroupCommutators θ).commutator_eq_bot γ hγ h2, Subgroup.mem_bot]
      at hmem
    exact commutatorElement_eq_one_iff_commute.1 hmem
  · have hδroot : IsRoot .F4 δ := isRoot_of_mem_twistedDatum_roots θ hδ
    have hγroot : IsRoot .F4 γ := isRoot_of_mem_twistedDatum_roots θ hγ
    have hlin : LinIndepPair δ γ := by
      by_contra hdep
      rcases TagRoots.eq_or_eq_neg_of_not_linIndepPair hδroot hγroot hdep with h | h
      · exact hδγ h
      · have hzero : δ (teNV_lastD θ) = -(γ (teNV_lastD θ)) := by rw [h]; rfl
        omega
    have hc := (twistedDatum_steinbergExtras θ hθ).commutator_mem δ hδ γ hγ hlin x hx y hy
    rw [teNV_openCone_eq_emptyD θ hδ hγ hsum] at hc
    simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at hc
    exact commutatorElement_eq_one_iff_commute.1 hc

private lemma teNV_mem_normalizer_ggSub_of_forall
    {k : Type} [Field k] (θ : k →+* k)
    (S : Set (Fin (Tag.rank .F4) → ℤ)) {u : fixedGroup k θ}
    (h : ∀ γ ∈ S, ∀ x ∈ twistedRootGroup k θ γ, u * x * u⁻¹ ∈ ggSub (twistedDatum k θ) S)
    (h' : ∀ γ ∈ S, ∀ x ∈ twistedRootGroup k θ γ, u⁻¹ * x * u ∈ ggSub (twistedDatum k θ) S) :
    u ∈ Subgroup.normalizer
      ((ggSub (twistedDatum k θ) S : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hm : (ggSub (twistedDatum k θ) S).map (MulAut.conj u).toMonoidHom ≤
        ggSub (twistedDatum k θ) S := by
      change (⨆ γ ∈ S, (twistedDatum k θ).rootGroup γ).map
        (MulAut.conj u).toMonoidHom ≤ ⨆ γ ∈ S, (twistedDatum k θ).rootGroup γ
      rw [Subgroup.map_iSup]
      refine iSup_le fun γ => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hγ => ?_
      rintro y ⟨z, hz, rfl⟩
      change u * z * u⁻¹ ∈ ggSub (twistedDatum k θ) S
      exact h γ hγ z hz
    exact hm ⟨x, hx, rfl⟩
  · intro hx
    have hm : (ggSub (twistedDatum k θ) S).map (MulAut.conj u⁻¹).toMonoidHom ≤
        ggSub (twistedDatum k θ) S := by
      change (⨆ γ ∈ S, (twistedDatum k θ).rootGroup γ).map
        (MulAut.conj u⁻¹).toMonoidHom ≤ ⨆ γ ∈ S, (twistedDatum k θ).rootGroup γ
      rw [Subgroup.map_iSup]
      refine iSup_le fun γ => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hγ => ?_
      rintro y ⟨z, hz, rfl⟩
      change u⁻¹ * z * u ∈ ggSub (twistedDatum k θ) S
      exact h' γ hγ z hz
    have hmem := hm ⟨u * x * u⁻¹, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hmem

private lemma teNV_hHat_mem_normalizer_ggSub
    {k : Type} [Field k] (θ : k →+* k) (S : Set (Fin (Tag.rank .F4) → ℤ))
    (hS : ∀ γ ∈ S, IsRoot .F4 γ) (i : Fin (Tag.rank .F4)) {h : fixedGroup k θ}
    (hh : h ∈ hHat k θ i) :
    h ∈ Subgroup.normalizer
      ((ggSub (twistedDatum k θ) S : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) := by
  apply teNV_mem_normalizer_ggSub_of_forall θ S
  · intro γ hγ x hx
    exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ S) => twistedRootGroup k θ γ) γ hγ le_rfl
      (hHat_conj_mem θ i (hS γ hγ) hh hx)
  · intro γ hγ x hx
    exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ S) => twistedRootGroup k θ γ) γ hγ le_rfl
      (by simpa only [inv_inv] using hHat_conj_mem θ i (hS γ hγ) (inv_mem hh) hx)

private lemma teNV_le_normalizer_of_comm {G : Type*} [Group G] {H K : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) : K ≤ Subgroup.normalizer (H : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : y * h * y⁻¹ = h := by rw [← hc h hh y hy, mul_inv_cancel_right]
    rw [this]
    exact hh
  · intro hh
    have h2 := hc _ hh y hy
    have : h = y * h * y⁻¹ := by
      calc h = y⁻¹ * ((y * h * y⁻¹) * y) := by group
        _ = y⁻¹ * (y * (y * h * y⁻¹)) := by rw [h2]
        _ = y * h * y⁻¹ := by group
    rw [this]
    exact hh

private lemma teNV_mem_sup_iff_of_le_normalizer {G : Type*} [Group G] {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G)) {g : G} :
    g ∈ H ⊔ K ↔ ∃ x ∈ H, ∃ y ∈ K, g = x * y := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left H K hK, Set.mem_mul]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨x, hx, y, hy, rfl⟩

private lemma teNV_A_isRootD
    {k : Type} [Field k] (θ : k →+* k) {γ : Fin (twistedDatum k θ).rank → ℤ}
    (hγ : γ ∈ twE6A) : IsRoot .F4 γ := teNV_A_isRoot hγ

private lemma teNV_A_levelD
    {k : Type} [Field k] (θ : k →+* k) {γ : Fin (twistedDatum k θ).rank → ℤ}
    (hγ : γ ∈ twE6A) : γ (teNV_lastD θ) = 2 := teNV_A_level hγ

private lemma teNV_alpha_levelD
    {k : Type} [Field k] (θ : k →+* k) : twE6Alpha (teNV_lastD θ) = 2 := teNV_alpha_level

private lemma teNV_posUnipotent_le_normalizer_V
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    posUnipotent (twistedDatum k θ) ≤
      Subgroup.normalizer (twE6V θ : Set (fixedGroup k θ)) := by
  refine iSup₂_le fun δ hδ => le_normalizer_iSup₂ fun x hx γ hγ y hy => ?_
  by_cases hδγ : δ = γ
  · have hx' : x ∈ (twistedDatum k θ).rootGroup γ := by rwa [hδγ] at hx
    exact le_iSup₂_of_le
      (f := fun γ (_ : γ ∈ twE6A) => (twistedDatum k θ).rootGroup γ) γ hγ le_rfl
      (mul_mem (mul_mem hx' hy) (inv_mem hx'))
  · have hδroot := isRoot_of_mem_twistedDatum_roots θ hδ.1
    have hγroot : IsRoot .F4 γ := teNV_A_isRootD θ hγ
    have hlin : LinIndepPair δ γ := by
      by_contra hdep
      rcases TagRoots.eq_or_eq_neg_of_not_linIndepPair hδroot hγroot hdep with h | h
      · exact hδγ h
      · have hlev : δ (teNV_lastD θ) = -(γ (teNV_lastD θ)) := by rw [h]; rfl
        have h0 : 0 ≤ δ (teNV_lastD θ) := teNV_level_nonneg_of_ht_pos hδroot hδ.2
        have h2 := teNV_A_levelD θ hγ
        rw [h2] at hlev
        omega
    have hc := (twistedDatum_steinbergExtras θ hθ).commutator_mem δ hδ.1 γ
      (by rw [twistedDatum_roots]; exact hγroot) hlin x hx y hy
    have hcl : ⁅x, y⁆ ∈ twE6V θ := by
      have hle : (⨆ ε ∈ openCone (twistedDatum k θ).roots δ γ,
          (twistedDatum k θ).rootGroup ε) ≤
          ⨆ ε ∈ twE6A, (twistedDatum k θ).rootGroup ε := by
        refine iSup₂_le fun ε hε => ?_
        rw [twistedDatum_roots] at hε
        exact le_iSup₂_of_le
          (f := fun γ (_ : γ ∈ twE6A) => (twistedDatum k θ).rootGroup γ) ε
          (teNV_openCone_A hδroot hδ.2 hγ hε) le_rfl
      exact hle hc
    have hyV : y ∈ twE6V θ :=
      le_iSup₂_of_le (f := fun γ (_ : γ ∈ twE6A) => (twistedDatum k θ).rootGroup γ)
        γ hγ le_rfl hy
    have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem hcl hyV

private lemma teNV_posUnipotent_le_normalizer_Va
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    posUnipotent (twistedDatum k θ) ≤
      Subgroup.normalizer (twE6Va θ : Set (fixedGroup k θ)) := by
  refine iSup₂_le fun δ hδ => le_normalizer_iSup₂ fun x hx γ hγ y hy => ?_
  have hδroot := isRoot_of_mem_twistedDatum_roots θ hδ.1
  rcases Set.mem_insert_iff.1 hγ with hγα | hγA
  · have hy' : y ∈ (twistedDatum k θ).rootGroup twE6Alpha := by rwa [hγα] at hy
    by_cases hδα : δ = twE6Alpha
    · have hx' : x ∈ (twistedDatum k θ).rootGroup twE6Alpha := by rwa [hδα] at hx
      exact le_iSup₂_of_le
        (f := fun γ (_ : γ ∈ insert twE6Alpha twE6A) => (twistedDatum k θ).rootGroup γ)
        twE6Alpha (Set.mem_insert_iff.2 (Or.inl rfl)) le_rfl
        (mul_mem (mul_mem hx' hy') (inv_mem hx'))
    · have hγroot : IsRoot .F4 twE6Alpha := teNV_alpha_isRoot
      have hlin : LinIndepPair δ twE6Alpha := by
        by_contra hdep
        rcases TagRoots.eq_or_eq_neg_of_not_linIndepPair hδroot hγroot hdep with h | h
        · exact hδα h
        · have hlev : δ (teNV_lastD θ) = -(twE6Alpha (teNV_lastD θ)) := by rw [h]; rfl
          have h0 : 0 ≤ δ (teNV_lastD θ) := teNV_level_nonneg_of_ht_pos hδroot hδ.2
          have h2 := teNV_alpha_levelD θ
          rw [h2] at hlev
          omega
      have hc := (twistedDatum_steinbergExtras θ hθ).commutator_mem δ hδ.1 twE6Alpha
        (by rw [twistedDatum_roots]; exact hγroot) hlin x hx y hy'
      have hcl : ⁅x, y⁆ ∈ twE6Va θ := by
        have hle : (⨆ ε ∈ openCone (twistedDatum k θ).roots δ twE6Alpha,
            (twistedDatum k θ).rootGroup ε) ≤
            ⨆ ε ∈ insert twE6Alpha twE6A, (twistedDatum k θ).rootGroup ε := by
          refine iSup₂_le fun ε hε => ?_
          rw [twistedDatum_roots] at hε
          exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ insert twE6Alpha twE6A) =>
              (twistedDatum k θ).rootGroup γ) ε
            (Set.mem_insert_of_mem _ (teNV_openCone_alpha hδroot hδ.2 hε)) le_rfl
        rw [twE6Va, ggSub]
        exact hle hc
      have hyV : y ∈ twE6Va θ := by
        rw [twE6Va, ggSub]
        exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ insert twE6Alpha twE6A) =>
          (twistedDatum k θ).rootGroup γ) twE6Alpha
          (Set.mem_insert_iff.2 (Or.inl rfl)) le_rfl hy'
      have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
      rw [e]
      exact mul_mem hcl hyV
  · by_cases hδγ : δ = γ
    · have hx' : x ∈ (twistedDatum k θ).rootGroup γ := by rwa [hδγ] at hx
      exact le_iSup₂_of_le
        (f := fun γ (_ : γ ∈ insert twE6Alpha twE6A) => (twistedDatum k θ).rootGroup γ)
        γ (Set.mem_insert_of_mem _ hγA) le_rfl
        (mul_mem (mul_mem hx' hy) (inv_mem hx'))
    · have hγroot : IsRoot .F4 γ := teNV_A_isRootD θ hγA
      have hlin : LinIndepPair δ γ := by
        by_contra hdep
        rcases TagRoots.eq_or_eq_neg_of_not_linIndepPair hδroot hγroot hdep with h | h
        · exact hδγ h
        · have hlev : δ (teNV_lastD θ) = -(γ (teNV_lastD θ)) := by rw [h]; rfl
          have h0 : 0 ≤ δ (teNV_lastD θ) := teNV_level_nonneg_of_ht_pos hδroot hδ.2
          have h2 := teNV_A_levelD θ hγA
          rw [h2] at hlev
          omega
      have hc := (twistedDatum_steinbergExtras θ hθ).commutator_mem δ hδ.1 γ
        (by rw [twistedDatum_roots]; exact hγroot) hlin x hx y hy
      have hcl : ⁅x, y⁆ ∈ twE6Va θ := by
        have hle : (⨆ ε ∈ openCone (twistedDatum k θ).roots δ γ,
            (twistedDatum k θ).rootGroup ε) ≤
            ⨆ ε ∈ insert twE6Alpha twE6A, (twistedDatum k θ).rootGroup ε := by
          refine iSup₂_le fun ε hε => ?_
          rw [twistedDatum_roots] at hε
          exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ insert twE6Alpha twE6A) =>
              (twistedDatum k θ).rootGroup γ) ε
            (Set.mem_insert_of_mem _ (teNV_openCone_A hδroot hδ.2 hγA hε)) le_rfl
        rw [twE6Va, ggSub]
        exact hle hc
      have hyV : y ∈ twE6Va θ := by
        rw [twE6Va, ggSub]
        exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ insert twE6Alpha twE6A) =>
          (twistedDatum k θ).rootGroup γ) γ (Set.mem_insert_of_mem _ hγA) le_rfl hy
      have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
      rw [e]
      exact mul_mem hcl hyV

private def teNV_L : List (Fin (Tag.rank .F4) → ℤ) :=
  [twE6Alpha, ![1, 2, 4, 2], ![1, 3, 4, 2], ![2, 3, 4, 2]]

private lemma teNV_L_nodup : teNV_L.Nodup := by decide +kernel

private lemma teNV_L_ht_check : teNV_L.all (fun β => decide (0 < ht β)) = true := by
  decide +kernel

private lemma teNV_ArootT_mem_L (t : Fin 3) : teNV_ArootT t ∈ teNV_L := by
  fin_cases t
  · change (![1, 2, 4, 2] : Fin (Tag.rank .F4) → ℤ) ∈ teNV_L
    rw [teNV_L]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · change (![1, 3, 4, 2] : Fin (Tag.rank .F4) → ℤ) ∈ teNV_L
    rw [teNV_L]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · change (![2, 3, 4, 2] : Fin (Tag.rank .F4) → ℤ) ∈ teNV_L
    rw [teNV_L]
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

private lemma teNV_L_mem_alpha : twE6Alpha ∈ teNV_L := by
  rw [teNV_L]; exact List.mem_cons_self

private lemma teNV_L_mem_iff {β : Fin (Tag.rank .F4) → ℤ} :
    β ∈ teNV_L ↔ β = twE6Alpha ∨ β ∈ twE6A := by
  constructor
  · intro hβ
    rw [teNV_L] at hβ
    rcases List.mem_cons.mp hβ with h | hβ
    · exact Or.inl h
    rcases List.mem_cons.mp hβ with h | hβ
    · exact Or.inr (by rw [h]; exact teNV_ArootT_mem 0)
    rcases List.mem_cons.mp hβ with h | hβ
    · exact Or.inr (by rw [h]; exact teNV_ArootT_mem 1)
    · rcases List.mem_cons.mp hβ with h | hβ
      · exact Or.inr (by rw [h]; exact teNV_ArootT_mem 2)
      · exact absurd hβ List.not_mem_nil
  · rintro (h | h)
    · rw [h]; exact teNV_L_mem_alpha
    · obtain ⟨t, ht⟩ := teNV_ArootT_surj h
      rw [← ht]
      exact teNV_ArootT_mem_L t

private lemma teNV_L_isRoot
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : β ∈ teNV_L) : IsRoot .F4 β := by
  rcases teNV_L_mem_iff.1 hβ with h | h
  · rw [h]; exact teNV_alpha_isRoot
  · exact teNV_A_isRoot h

private lemma teNV_L_ht_pos {β : Fin (Tag.rank .F4) → ℤ} (hβ : β ∈ teNV_L) : 0 < ht β := by
  have h := teNV_L_ht_check
  rw [List.all_eq_true] at h
  exact decide_eq_true_eq.mp (h β hβ)

private lemma teNV_L_sorted : teNV_L.Pairwise fun β δ => ht β ≤ ht δ := by decide +kernel

private lemma teNV_L_prodInjective
    {k : Type} [Field k] (θ : k →+* k) :
    ProdInjectiveFor (twistedRootGroup k θ) teNV_L :=
  prodInjective_twisted θ 1 teNV_L teNV_L_nodup
    (fun β hβ => ⟨teNV_L_isRoot hβ, by rw [one_mul]; exact teNV_L_ht_pos hβ⟩)
    (by simpa using teNV_L_sorted)

private lemma teNV_list_prod_single {M : Type*} [Group M] {α : Type} [DecidableEq α]
    {L : List α} (hL : L.Nodup) {a : α} (ha : a ∈ L) (x : M) :
    (L.map fun b => if b = a then x else 1).prod = x := by
  induction L with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons b L ih =>
    rw [List.nodup_cons] at hL
    obtain ⟨hbL, hL⟩ := hL
    rw [List.map_cons, List.prod_cons]
    by_cases hba : b = a
    · rw [if_pos hba]
      have hzero : ∀ c ∈ L, (if c = a then x else 1) = 1 := by
        intro c hc
        rw [if_neg]
        intro h
        exact hbL (by rw [hba, ← h]; exact hc)
      rw [List.prod_eq_one (fun y hy => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
        exact hzero c hc), mul_one]
    · rw [if_neg hba]
      have haL : a ∈ L := by
        rcases List.mem_cons.1 ha with h | h
        · exact absurd h.symm hba
        · exact h
      rw [ih hL haL, one_mul]

private lemma teNV_list_prod_pointwise_mul {M : Type*} [Group M] {α : Type} {L : List α}
    {f g : α → M} {s : Subgroup M} (hs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    (hf : ∀ a ∈ L, f a ∈ s) (hg : ∀ a ∈ L, g a ∈ s) :
    (L.map fun a => f a * g a).prod = (L.map f).prod * (L.map g).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.map_cons,
      List.prod_cons, ih (fun (b : α) hb => hf b (List.mem_cons_of_mem a hb))
        (fun (b : α) hb => hg b (List.mem_cons_of_mem a hb))]
    have hfL : (L.map f).prod ∈ s :=
      Subgroup.list_prod_mem _ fun y hy => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
        exact hf b (List.mem_cons_of_mem a hb)
    have hga : g a ∈ s := hg a (by simp)
    calc (f a * g a) * ((L.map f).prod * (L.map g).prod)
        = f a * (g a * (L.map f).prod) * (L.map g).prod := by group
      _ = f a * ((L.map f).prod * g a) * (L.map g).prod := by
            rw [hs (g a) hga ((L.map f).prod) hfL]
      _ = (f a * (L.map f).prod) * (g a * (L.map g).prod) := by group

private lemma teNV_V_comm_aux
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    ∀ x ∈ twE6V θ, ∀ y ∈ twE6V θ, Commute x y := by
  intro x hx
  refine CFSG.LieType.TitsSimplicity.iSup₂_induction
    (C := fun x => ∀ y ∈ twE6V θ, Commute x y) hx
    (fun γ hγ x hx' => ?_) (fun y hy => Commute.one_left y)
    (fun x z hx hz => fun y hy => (hx y hy).mul_left (hz y hy))
  intro y hy
  refine CFSG.LieType.TitsSimplicity.iSup₂_induction
    (C := fun y => Commute x y) hy
    (fun δ hδ y hy' => ?_) (Commute.one_right x)
    (fun y z hy hz => hy.mul_right hz)
  have hsum : 3 ≤ γ (teNV_lastD θ) + δ (teNV_lastD θ) := by
    rw [teNV_A_levelD θ hγ, teNV_A_levelD θ hδ]; norm_num
  exact teNV_commute_of_level_sumD θ hθ
    (by rw [twistedDatum_roots]; exact teNV_A_isRootD θ hγ)
    (by rw [twistedDatum_roots]; exact teNV_A_isRootD θ hδ) hsum x hx' y hy'

private lemma teNV_V_decomp
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {z : fixedGroup k θ}
    (hz : z ∈ twE6V θ) :
    ∃ f : (Fin (Tag.rank .F4) → ℤ) → fixedGroup k θ,
      (∀ β ∈ teNV_L, f β ∈ twistedRootGroup k θ β) ∧
        f twE6Alpha = 1 ∧ z = (teNV_L.map f).prod := by
  classical
  have hV : twE6V θ = ggSub (twistedDatum k θ) (Set.range teNV_ArootT) := by
    rw [twE6V, teNV_range_eq]
    rfl
  rw [hV] at hz
  refine CFSG.LieType.TitsSimplicity.iSup₂_induction
    (C := fun z => ∃ f : (Fin (Tag.rank .F4) → ℤ) → fixedGroup k θ,
      (∀ β ∈ teNV_L, f β ∈ twistedRootGroup k θ β) ∧
        f twE6Alpha = 1 ∧ z = (teNV_L.map f).prod) hz ?_ ?_ ?_
  · rintro γ ⟨t, rfl⟩ y hy
    have hγL : teNV_ArootT t ∈ teNV_L := teNV_ArootT_mem_L t
    have hαγ : twE6Alpha ≠ teNV_ArootT t := by
      intro h
      have h1 : twE6Alpha teNV_third = 4 := by rw [h]; exact teNV_ArootT_third t
      have h2 := teNV_alpha_third
      omega
    refine ⟨fun β => if β = teNV_ArootT t then y else 1, ?_, ?_, ?_⟩
    · intro β hβ
      by_cases h : β = teNV_ArootT t
      · dsimp only
        rw [h, if_pos rfl]
        exact show y ∈ twistedRootGroup k θ (teNV_ArootT t) from hy
      · dsimp only
        rw [if_neg h]; exact one_mem _
    · change (if twE6Alpha = teNV_ArootT t then y else 1) = 1
      rw [if_neg hαγ]
    · exact (teNV_list_prod_single teNV_L_nodup hγL y).symm
  · exact ⟨fun _ => 1, fun β hβ => one_mem _, rfl, by simp⟩
  · rintro x y ⟨f, hf, hfα, hfx⟩ ⟨g, hg, hgα, hgy⟩
    have hfV : ∀ β ∈ teNV_L, f β ∈ twE6V θ := by
      intro β hβ
      rcases teNV_L_mem_iff.1 hβ with h | h
      · rw [h, hfα]; exact one_mem _
      · exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ twE6A) => twistedRootGroup k θ γ) β h
          le_rfl (hf β hβ)
    have hgV : ∀ β ∈ teNV_L, g β ∈ twE6V θ := by
      intro β hβ
      rcases teNV_L_mem_iff.1 hβ with h | h
      · rw [h, hgα]; exact one_mem _
      · exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ twE6A) => twistedRootGroup k θ γ) β h
          le_rfl (hg β hβ)
    refine ⟨fun β => f β * g β, fun β hβ => mul_mem (hf β hβ) (hg β hβ), ?_, ?_⟩
    · change f twE6Alpha * g twE6Alpha = 1
      rw [hfα, hgα, one_mul]
    · change x * y = (teNV_L.map fun β => f β * g β).prod
      rw [hfx, hgy]
      exact (teNV_list_prod_pointwise_mul
        (fun a ha b hb => (teNV_V_comm_aux θ hθ a ha b hb).eq) hfV hgV).symm

theorem twE6V_comm
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {x y : fixedGroup k θ}
    (hx : x ∈ twE6V θ) (hy : y ∈ twE6V θ) : x * y = y * x := by
  exact (teNV_V_comm_aux θ hθ x hx y hy).eq

theorem twE6Alpha_comm_V
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {x y : fixedGroup k θ}
    (hx : x ∈ twE6RA θ) (hy : y ∈ twE6V θ) : x * y = y * x := by
  have hcomm : Commute x y := by
    refine CFSG.LieType.TitsSimplicity.iSup₂_induction (C := fun y => Commute x y) hy
      (fun γ hγ y hy' => ?_) (Commute.one_right x) (fun y z hy hz => hy.mul_right hz)
    have hsum : 3 ≤ twE6Alpha (teNV_lastD θ) + γ (teNV_lastD θ) := by
      rw [teNV_alpha_levelD θ, teNV_A_levelD θ hγ]; norm_num
    exact teNV_commute_of_level_sumD θ hθ
      (by rw [twistedDatum_roots]; exact teNV_alpha_isRoot)
      (by rw [twistedDatum_roots]; exact teNV_A_isRootD θ hγ) hsum x hx y hy'
  exact hcomm.eq

theorem twE6_borel_le_normalizer_V
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6Borel θ ≤ Subgroup.normalizer (twE6V θ : Set (fixedGroup k θ)) := by
  change (⨆ i, hHat k θ i) ⊔ posUnipotent (twistedDatum k θ) ≤
    Subgroup.normalizer (twE6V θ : Set (fixedGroup k θ))
  refine sup_le ?_ ?_
  · refine iSup_le fun i => ?_
    exact fun h hh => teNV_hHat_mem_normalizer_ggSub θ twE6A
      (fun γ hγ => teNV_A_isRoot hγ) i hh
  · exact teNV_posUnipotent_le_normalizer_V θ hθ

theorem twE6_borel_le_normalizer_Va
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6Borel θ ≤ Subgroup.normalizer (twE6Va θ : Set (fixedGroup k θ)) := by
  change (⨆ i, hHat k θ i) ⊔ posUnipotent (twistedDatum k θ) ≤
    Subgroup.normalizer (twE6Va θ : Set (fixedGroup k θ))
  refine sup_le ?_ ?_
  · refine iSup_le fun i => ?_
    exact fun h hh => teNV_hHat_mem_normalizer_ggSub θ (insert twE6Alpha twE6A)
      (fun γ hγ => (Set.mem_insert_iff.1 hγ).elim
        (fun h0 => by rw [h0]; exact teNV_alpha_isRoot) (fun h0 => teNV_A_isRoot h0)) i hh
  · exact teNV_posUnipotent_le_normalizer_Va θ hθ

theorem twE6Alpha_inf_V
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6RA θ ⊓ twE6V θ = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_inf] at hz
  obtain ⟨hzα, hzV⟩ := hz
  obtain ⟨f, hfmem, hfα, hfprod⟩ := teNV_V_decomp θ hθ hzV
  have hinj := teNV_L_prodInjective θ
  let g : (Fin (Tag.rank .F4) → ℤ) → fixedGroup k θ :=
    fun β => if β = twE6Alpha then z else 1
  have hgmem : ∀ β ∈ teNV_L, g β ∈ twistedRootGroup k θ β := by
    intro β hβ
    by_cases h : β = twE6Alpha
    · subst h
      exact show z ∈ twistedRootGroup k θ twE6Alpha from hzα
    · simp only [g, if_neg h]; exact one_mem _
  have hgα : g twE6Alpha = z := by simp [g]
  have hgprod : (teNV_L.map g).prod = z := by
    have h := teNV_list_prod_single teNV_L_nodup (teNV_L_mem_iff.2 (Or.inl rfl)) z
    simpa [g] using h
  have hp : (teNV_L.map f).prod = (teNV_L.map g).prod := by
    rw [← hfprod, hgprod]
  have h := hinj f g hfmem hgmem hp twE6Alpha (teNV_L_mem_iff.2 (Or.inl rfl))
  rw [hfα, hgα] at h
  exact Subgroup.mem_bot.2 h.symm

theorem mem_twE6Va_iff
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {x : fixedGroup k θ} :
    x ∈ twE6Va θ ↔ ∃ z ∈ twE6RA θ, ∃ v ∈ twE6V θ, x = z * v := by
  have hVa : twE6Va θ = twE6RA θ ⊔ twE6V θ := by
    change (⨆ γ ∈ insert twE6Alpha twE6A, (twistedDatum k θ).rootGroup γ) =
      (twistedDatum k θ).rootGroup twE6Alpha ⊔ ggSub (twistedDatum k θ) twE6A
    apply le_antisymm
    · refine iSup₂_le fun γ hγ => ?_
      rcases Set.mem_insert_iff.1 hγ with hγα | hγA
      · rw [hγα]; exact le_sup_of_le_left le_rfl
      · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun γ (_ : γ ∈ twE6A) =>
          (twistedDatum k θ).rootGroup γ) γ hγA le_rfl)
    · refine sup_le ?_ ?_
      · exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ insert twE6Alpha twE6A) =>
          (twistedDatum k θ).rootGroup γ) twE6Alpha
          (Set.mem_insert_iff.2 (Or.inl rfl)) le_rfl
      · refine iSup₂_le fun γ hγ => le_iSup₂_of_le
          (f := fun γ (_ : γ ∈ insert twE6Alpha twE6A) =>
            (twistedDatum k θ).rootGroup γ) γ (Set.mem_insert_of_mem _ hγ) le_rfl
  rw [hVa]
  refine teNV_mem_sup_iff_of_le_normalizer (H := twE6RA θ) (K := twE6V θ) ?_
  exact teNV_le_normalizer_of_comm (fun a ha b hb => twE6Alpha_comm_V θ hθ ha hb)

theorem twE6_conj_alpha_le_Va
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {b : fixedGroup k θ} (hb : b ∈ twE6Borel θ) :
    twE6Cj b (twE6RA θ) ≤ twE6Va θ := by
  have hB := twE6_borel_le_normalizer_Va θ hθ hb
  have hmap : (twE6Va θ).map (MulAut.conj b).toMonoidHom = twE6Va θ :=
    mem_normalizer_iff_map_conj.1 hB
  have hle : twE6RA θ ≤ twE6Va θ := by
    rw [twE6Va, ggSub]
    exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ insert twE6Alpha twE6A) =>
      twistedRootGroup k θ γ) twE6Alpha (Set.mem_insert_iff.2 (Or.inl rfl)) le_rfl
  calc twE6Cj b (twE6RA θ) = (twE6RA θ).map (MulAut.conj b).toMonoidHom := rfl
    _ ≤ (twE6Va θ).map (MulAut.conj b).toMonoidHom := Subgroup.map_mono hle
    _ = twE6Va θ := hmap

theorem twE6_conj_alpha_inf_V
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {b : fixedGroup k θ} (hb : b ∈ twE6Borel θ) :
    twE6Cj b (twE6RA θ) ⊓ twE6V θ = ⊥ := by
  have hB := twE6_borel_le_normalizer_V θ hθ hb
  have hmapV : (twE6V θ).map (MulAut.conj b).toMonoidHom = twE6V θ :=
    mem_normalizer_iff_map_conj.1 hB
  change ((twE6RA θ).map (MulAut.conj b).toMonoidHom) ⊓ twE6V θ = ⊥
  rw [← hmapV]
  rw [← Subgroup.map_inf (twE6RA θ) (twE6V θ) (MulAut.conj b).toMonoidHom
    (MulAut.conj b).injective]
  rw [twE6Alpha_inf_V θ hθ]
  simp

end CFSG.StandardType.LieKnownR2.Short
