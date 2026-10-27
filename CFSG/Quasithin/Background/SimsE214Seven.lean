module

public import CFSG.Quasithin.Background.SimsE214SevenMem

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank E214S

theorem e214_seven
    (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V)
    (hc : CharTwo H) (hTI : IsTISetIn V M) (I : Subgroup Γ) (g : Γ) (hI : IsInIHTV H T M V I)
    (hg : g ∈ I) (hIV : I = V ⊔ conjSubgroup V g) (hZ1 : V ⊓ conjSubgroup V g ≠ ⊥)
    (MI TI JI B A P Z : Subgroup Γ) (k : ℕ) (hMI : MI = M ⊓ I) (hTI' : TI = T ⊓ I)
    (hJI : JI = kerIn MI I) (hB : B = V ⊓ pCoreOf 2 I) (hA : A = conjSubgroup V g ⊓ pCoreOf 2 I)
    (hP : P = A ⊔ B) (hZ : Z = V ⊓ conjSubgroup V g)
    (hk : E1.nParam (⊤ : Subgroup (E2.StarQuot MI I)) = (k : ℕ∞))
    (h4 : (IsSz k (E2.StarQuot MI I) ∨ (1 ≤ k ∧ IsSp4Full k (E2.StarQuot MI I))) →
      ∀ Y₁ Y₂ : Subgroup Γ, Z ≤ Y₂ → Y₂ < Y₁ → Y₁ ≤ P → I ≤ Subgroup.normalizer (Y₁ : Set Γ) →
        I ≤ Subgroup.normalizer (Y₂ : Set Γ) →
        (∀ Y : Subgroup Γ, Y₂ ≤ Y → Y ≤ Y₁ → I ≤ Subgroup.normalizer (Y : Set Γ) →
          Y = Y₂ ∨ Y = Y₁) →
        4 * k ≤ E3.mQuot Y₁ Y₂) :
    rk ↥(autI h.elem A) ≤ 2 * k → ((1 : ℚ) : WithTop ℚ) < qOf (autI h.elem I) →
      ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
          Nonempty (E2.StarQuot MI I ≃* ↥(CFSG.Open.StatedSL 2 F))) ∨
        IsSz k (E2.StarQuot MI I) ∨ Nonempty (E2.StarQuot MI I ≃* DihedralGroup 5)) ∧
      rk ↥(autI h.elem A) = 2 * k ∧ E3.mQuot V Z = 3 * k ∧
      ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
          Nonempty (E2.StarQuot MI I ≃* ↥(CFSG.Open.StatedSL 2 F)) ∧
          IsSumOfNaturalSections 2 I P Z JI (CFSG.Open.StatedSL 2 F)) ∨
        (∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 1 ≤ a ∧ k = 2 * a + 1 ∧
          Nat.card F = 2 ^ k ∧ IsSz k (E2.StarQuot MI I) ∧
          IsNaturalSection I P Z JI (CFSG.Blueprint.suzukiGroup a F)) ∨
        (∃ (F : Type) (_ : Field F) (_ : Finite F)
            (S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)),
          Nat.card F = 4 ∧ S ≤ CFSG.Open.StatedSL 2 F ∧ Nonempty (↥S ≃* DihedralGroup 5) ∧
          Nonempty (E2.StarQuot MI I ≃* DihedralGroup 5) ∧ IsNaturalSection I P Z JI S)) := by
  intro hrk hq
  subst hMI hTI' hJI hB hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := E2P.finite_starQuot (M ⊓ I) I
  obtain ⟨hPZ, hVZ⟩ := numerics h hc hI hg hIV
  rw [← hP, ← hZ] at hPZ
  rw [← hZ] at hVZ
  have hmQ : ∀ m : ℕ, (V ⊓ pCoreOf 2 I).relIndex V = 2 ^ m →
      E3.mQuot V Z = m + rk ↥(autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I)) := by
    intro m hm
    rw [E3.mQuot, hVZ, hm, ← pow_add, padicValNat.prime_pow]
  obtain ⟨k', -, hcase⟩ := hI.2.2.2.2
  rcases hcase with ⟨hk1, hY | hY, -⟩ | ⟨rfl, p, a, hp, hp2, ha, ⟨e⟩⟩ | ⟨-, hk1, hY, -⟩
  ·
    have hkk : k = k' := eq_of_nParam_eq hk (nParam_eq_of_isPSL hY)
    subst hkk
    obtain ⟨F, _, _, hF, he, r, hr2, hrkr, hsum⟩ :=
      l2_case h hc hTI hI hg hIV hZ1 hP hZ hk (exists_statedSL_of_isPSL hY) hq
    have hVB := relIndex_V_of_psl_or_sz h hTI hI hg hIV hZ1 (by omega) (Or.inl hY)
    have hr : r = 2 := by
      have h1 : k * r ≤ k * 2 := by rw [← hrkr]; omega
      have := Nat.le_of_mul_le_mul_left h1 (by omega)
      omega
    subst hr
    have hrk2 : rk ↥(autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I)) = 2 * k := by
      rw [hrkr, mul_comm]
    refine ⟨Or.inl ⟨F, inferInstance, inferInstance, hF, he⟩, hrk2, ?_,
      Or.inl ⟨F, inferInstance, inferInstance, hF, he, hsum⟩⟩
    rw [hmQ k hVB, hrk2]
    ring
  ·
    have hkk : k = k' := eq_of_nParam_eq hk (nParam_eq_of_isSz hY)
    subst hkk
    obtain ⟨hrk2, a, F, _, _, ha, hka, hF, hnat⟩ :=
      sz_case h hc hI hg hIV hP hZ hY hrk (h4 (Or.inl hY))
    have hVB := relIndex_V_of_psl_or_sz h hTI hI hg hIV hZ1 (by omega) (Or.inr hY)
    refine ⟨Or.inr (Or.inl hY), hrk2, ?_,
      Or.inr (Or.inl ⟨a, F, inferInstance, inferInstance, ha, hka, hF, hY, hnat⟩)⟩
    rw [hmQ k hVB, hrk2]
    ring
  ·
    have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hk1 : k = 1 := eq_of_nParam_eq hk (j := 1) (by exact_mod_cast nParam_eq_of_dihedral e)
    subst hk1
    have hd := dihFour_holds Γ H T M V h hc I g hI hg hIV _ rfl p a hp hp2 ha ⟨e⟩
    have hpa := eq_three_or_five_of_dParamPrime_le hp hp2 ha (hd.trans (by omega))
    have hVB : (V ⊓ pCoreOf 2 I).relIndex V = 2 ^ 1 := by
      have hpr := E214E.pair_of_isInIHTV h hI hg hIV
      rw [pow_one, ← hpr.kerIn_inf_eq]
      exact hpr.relIndex_eq_two_of_dihedral (hp.odd_of_ne_two hp2).pow e
    rcases hpa with hpa | hpa
    ·
      rw [hpa] at e
      obtain ⟨F, _, _, hF, he, r, hr2, hrkr, hsum⟩ :=
        l2_case h hc hTI hI hg hIV hZ1 hP hZ hk (exists_statedSL_of_dihedral_three e) hq
      have hr : r = 2 := by omega
      subst hr
      have hrk2 : rk ↥(autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I)) = 2 * 1 := by omega
      refine ⟨Or.inl ⟨F, inferInstance, inferInstance, hF, he⟩, hrk2, ?_,
        Or.inl ⟨F, inferInstance, inferInstance, hF, he, hsum⟩⟩
      rw [hmQ 1 hVB, hrk2]
    ·
      rw [hpa] at e
      obtain ⟨hrk2, F, _, _, S, hF, hSSL, hSe, hnat⟩ :=
        dih5_case h hc hTI hI hg hIV hZ1 hP hZ e (by omega)
      refine ⟨Or.inr (Or.inr ⟨e⟩), by omega, ?_,
        Or.inr (Or.inr ⟨F, inferInstance, inferInstance, S, hF, hSSL, hSe, ⟨e⟩, hnat⟩)⟩
      rw [hmQ 1 hVB, hrk2]
  ·
    exfalso
    have hkk : k = k' := eq_of_nParam_eq hk (nParam_eq_of_isSp4Full hY)
    subst hkk
    have hrk2 := le_antisymm hrk ((e213_four_nondih H T M V h hc I g hI hg hIV _ rfl).2.2 k hk1 hY)
    rw [hrk2] at hPZ
    have hne : Z ≠ P := by
      intro hZP
      rw [hZP, Subgroup.relIndex_self] at hPZ
      have : 1 < 2 ^ (2 * (2 * k)) := Nat.one_lt_two_pow (by omega)
      omega
    exact sp4_false h hc hI hg hIV hP hZ hk1 hY (h4 (Or.inr ⟨hk1, hY⟩)) hne
      (by rw [hPZ]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)) hq

theorem e214_eight
    (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V)
    (hc : CharTwo H) (hTI : IsTISetIn V M) (I : Subgroup Γ) (g : Γ) (hI : IsInIHTV H T M V I)
    (hg : g ∈ I) (hIV : I = V ⊔ conjSubgroup V g) (hZ1 : V ⊓ conjSubgroup V g ≠ ⊥)
    (MI TI JI B A P Z : Subgroup Γ) (k : ℕ) (hMI : MI = M ⊓ I) (hTI' : TI = T ⊓ I)
    (hJI : JI = kerIn MI I) (hB : B = V ⊓ pCoreOf 2 I) (hA : A = conjSubgroup V g ⊓ pCoreOf 2 I)
    (hP : P = A ⊔ B) (hZ : Z = V ⊓ conjSubgroup V g)
    (hk : E1.nParam (⊤ : Subgroup (E2.StarQuot MI I)) = (k : ℕ∞))
    (h4 : (IsSz k (E2.StarQuot MI I) ∨ (1 ≤ k ∧ IsSp4Full k (E2.StarQuot MI I))) →
      ∀ Y₁ Y₂ : Subgroup Γ, Z ≤ Y₂ → Y₂ < Y₁ → Y₁ ≤ P → I ≤ Subgroup.normalizer (Y₁ : Set Γ) →
        I ≤ Subgroup.normalizer (Y₂ : Set Γ) →
        (∀ Y : Subgroup Γ, Y₂ ≤ Y → Y ≤ Y₁ → I ≤ Subgroup.normalizer (Y : Set Γ) →
          Y = Y₂ ∨ Y = Y₁) →
        4 * k ≤ E3.mQuot Y₁ Y₂) :
    k = 2 → rk ↥(autI h.elem A) ≤ 6 → ((1 : ℚ) : WithTop ℚ) < qOf (autI h.elem I) →
      IsPSL 2 2 2 (E2.StarQuot MI I) ∧
      ∃ s : ℕ, (s = 2 ∨ s = 3) ∧ rk ↥(autI h.elem A) = 2 * s ∧ E3.mQuot V Z = 2 * (s + 1) := by
  rintro rfl hrk hq
  subst hMI hTI' hJI hB hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := E2P.finite_starQuot (M ⊓ I) I
  obtain ⟨hPZ, hVZ⟩ := numerics h hc hI hg hIV
  rw [← hP, ← hZ] at hPZ
  rw [← hZ] at hVZ
  have hmQ : ∀ m : ℕ, (V ⊓ pCoreOf 2 I).relIndex V = 2 ^ m →
      E3.mQuot V Z = m + rk ↥(autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I)) := by
    intro m hm
    rw [E3.mQuot, hVZ, hm, ← pow_add, padicValNat.prime_pow]
  obtain ⟨k', -, hcase⟩ := hI.2.2.2.2
  rcases hcase with ⟨hk1, hY | hY, -⟩ | ⟨rfl, p, a, hp, hp2, ha, ⟨e⟩⟩ | ⟨-, hk1, hY, -⟩
  ·
    have hkk : 2 = k' := eq_of_nParam_eq hk (nParam_eq_of_isPSL hY)
    subst hkk
    obtain ⟨F, _, _, hF, he, r, hr2, hrkr, hsum⟩ :=
      l2_case h hc hTI hI hg hIV hZ1 hP hZ hk (exists_statedSL_of_isPSL hY) hq
    have hVB := relIndex_V_of_psl_or_sz h hTI hI hg hIV hZ1 le_rfl (Or.inl hY)
    refine ⟨hY, r, by omega, by omega, ?_⟩
    rw [hmQ 2 hVB, hrkr]
    ring
  ·
    exfalso
    have hkk : 2 = k' := eq_of_nParam_eq hk (nParam_eq_of_isSz hY)
    obtain ⟨-, a, -, -, -, -, hka, -⟩ := hY
    omega
  ·
    exfalso
    have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have := eq_of_nParam_eq hk (j := 1) (by exact_mod_cast nParam_eq_of_dihedral e)
    omega
  ·
    exfalso
    have hkk : 2 = k' := eq_of_nParam_eq hk (nParam_eq_of_isSp4Full hY)
    subst hkk
    have hrk4 := (e213_four_nondih H T M V h hc I g hI hg hIV _ rfl).2.2 2 hk1 hY
    have hne : Z ≠ P := by
      intro hZP
      rw [hZP, Subgroup.relIndex_self] at hPZ
      have : 1 < 2 ^ (2 * rk ↥(autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I))) :=
        Nat.one_lt_two_pow (by omega)
      omega
    exact sp4_false h hc hI hg hIV hP hZ hk1 hY (h4 (Or.inr ⟨hk1, hY⟩)) hne
      (by rw [hPZ]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)) hq

end CFSG.Quasithin.SimsE2
