module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveKBasic
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
public import CFSG.GF2Type.Aschbacher1976Full.HSGL3Simple
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (Thin8)

section Group

variable {Y : Type} [Group Y] [Finite Y]

abbrev F1Mat3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

def F1A3 : F1Mat3 := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

def F1T2 : F1Mat3 := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

theorem F1A3_cube : F1A3 ^ 3 = 1 := by decide +kernel

theorem F1A3_ne_one : F1A3 ≠ 1 := by decide +kernel

theorem F1T2_sq : F1T2 * F1T2 = 1 := by decide +kernel

theorem F1T2_conj_A3 : F1T2 * F1A3 * F1T2 = F1A3 ^ 2 := by decide +kernel

theorem F1centralizer_A3_mat : ∀ m : F1Mat3, m * F1A3 = F1A3 * m →
    ∀ n : F1Mat3, m * n = 1 → m = 1 ∨ m = F1A3 ∨ m = F1A3 ^ 2 := by
  decide +kernel

abbrev F1GL32 : Type := CFSG.QuasithinUnique.Setup.Family.GL32

def F1ga3 : F1GL32 := Matrix.GeneralLinearGroup.mkOfDetNeZero F1A3 (by decide)

def F1gt2 : F1GL32 := Matrix.GeneralLinearGroup.mkOfDetNeZero F1T2 (by decide)

theorem F1ga3_val : (F1ga3 : F1Mat3) = F1A3 := by
  unfold F1ga3 Matrix.GeneralLinearGroup.mkOfDetNeZero Matrix.GeneralLinearGroup.mk'
  rfl

theorem F1gt2_val : (F1gt2 : F1Mat3) = F1T2 := by
  unfold F1gt2 Matrix.GeneralLinearGroup.mkOfDetNeZero Matrix.GeneralLinearGroup.mk'
  rfl

theorem F1ga3_cube : F1ga3 ^ 3 = 1 := by
  apply Units.ext
  show ((F1ga3 ^ 3 : F1GL32) : F1Mat3) = ((1 : F1GL32) : F1Mat3)
  rw [show ((F1ga3 ^ 3 : F1GL32) : F1Mat3) = F1A3 ^ 3 by
    rw [show ((F1ga3 ^ 3 : F1GL32) : F1Mat3) = ((F1ga3 : F1GL32) : F1Mat3) ^ 3 by simp,
      F1ga3_val]]
  rw [show ((1 : F1GL32) : F1Mat3) = 1 by simp]
  exact F1A3_cube

theorem F1gt2_sq : F1gt2 * F1gt2 = 1 := by
  apply Units.ext
  show ((F1gt2 * F1gt2 : F1GL32) : F1Mat3) = ((1 : F1GL32) : F1Mat3)
  rw [show ((F1gt2 * F1gt2 : F1GL32) : F1Mat3) = F1T2 * F1T2 by
    rw [show ((F1gt2 * F1gt2 : F1GL32) : F1Mat3) =
      ((F1gt2 : F1GL32) : F1Mat3) * ((F1gt2 : F1GL32) : F1Mat3) by simp, F1gt2_val]]
  rw [show ((1 : F1GL32) : F1Mat3) = 1 by simp]
  exact F1T2_sq

theorem F1gt2_conj_ga3 : F1gt2 * F1ga3 * F1gt2⁻¹ = F1ga3 ^ 2 := by
  apply Units.ext
  rw [show ((F1gt2 * F1ga3 * F1gt2⁻¹ : F1GL32) : F1Mat3) =
      ((F1gt2 : F1GL32) : F1Mat3) * ((F1ga3 : F1GL32) : F1Mat3) *
        (((F1gt2⁻¹ : F1GL32) : F1Mat3)) by simp]
  have hinv : F1gt2⁻¹ = F1gt2 := inv_eq_of_mul_eq_one_right F1gt2_sq
  have hga3sq : ((F1ga3 ^ 2 : F1GL32) : F1Mat3) = F1A3 ^ 2 := by
    rw [show ((F1ga3 ^ 2 : F1GL32) : F1Mat3) = ((F1ga3 : F1GL32) : F1Mat3) ^ 2 by simp,
      F1ga3_val]
  rw [F1gt2_val, F1ga3_val, hinv, F1gt2_val, hga3sq]
  exact F1T2_conj_A3

theorem F1T2_ne_one : F1T2 ≠ 1 := by decide +kernel

theorem F1gt2_ne_one : F1gt2 ≠ 1 := by
  intro h
  have hmat : (F1gt2 : F1Mat3) = 1 := by rw [h]; rfl
  rw [F1gt2_val] at hmat
  exact F1T2_ne_one hmat

theorem F1ga3_ne_one : F1ga3 ≠ 1 := by
  intro h
  have hmat : (F1ga3 : F1Mat3) = 1 := by rw [h]; rfl
  rw [F1ga3_val] at hmat
  exact F1A3_ne_one hmat

theorem F1orderOf_ga3 : orderOf F1ga3 = 3 := orderOf_eq_prime F1ga3_cube F1ga3_ne_one

theorem F1orderOf_gt2 : orderOf F1gt2 = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact F1gt2_sq) F1gt2_ne_one

theorem F1mem_zpowers_ga3_iff (y : F1GL32) :
    y ∈ Subgroup.zpowers F1ga3 ↔ y = 1 ∨ y = F1ga3 ∨ y = F1ga3 ^ 2 := by
  constructor
  · intro hy
    rw [Subgroup.mem_zpowers_iff] at hy
    obtain ⟨k, hk⟩ := hy
    have h3z : F1ga3 ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, F1ga3_cube]
    have hmod : F1ga3 ^ k = F1ga3 ^ (k % (3 : ℤ)) := zpow_eq_zpow_emod k h3z
    have hk' : F1ga3 ^ (k % (3 : ℤ)) = y := by rw [← hmod, hk]
    have hbound1 : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by norm_num)
    have hbound2 : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
    have hcases : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · left; rw [h0, zpow_zero] at hk'; exact hk'.symm
    · right; left; rw [h1] at hk'; simpa using hk'.symm
    · right; right; rw [h2] at hk'; simpa using hk'.symm
  · rintro (rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers F1ga3
    · exact Subgroup.zpow_mem_zpowers F1ga3 (2 : ℤ)

theorem F1centralizer_zpowers_ga3 :
    Subgroup.centralizer (Subgroup.zpowers F1ga3 : Set F1GL32) = Subgroup.zpowers F1ga3 := by
  apply le_antisymm
  · intro g hg
    have hcomm := (Subgroup.mem_centralizer_iff.mp hg) F1ga3 (Subgroup.mem_zpowers F1ga3)
    have hmat : (g : F1Mat3) * F1A3 = F1A3 * (g : F1Mat3) := by
      have h := congrArg (fun u : F1GL32 => (u : F1Mat3)) hcomm
      rw [show ((F1ga3 * g : F1GL32) : F1Mat3) =
            ((F1ga3 : F1GL32) : F1Mat3) * ((g : F1GL32) : F1Mat3) by simp,
        show ((g * F1ga3 : F1GL32) : F1Mat3) =
            ((g : F1GL32) : F1Mat3) * ((F1ga3 : F1GL32) : F1Mat3) by simp,
        F1ga3_val] at h
      exact h.symm
    have hmn : (g : F1Mat3) * ((g⁻¹ : F1GL32) : F1Mat3) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [F1mem_zpowers_ga3_iff]
    rcases F1centralizer_A3_mat (g : F1Mat3) hmat ((g⁻¹ : F1GL32) : F1Mat3) hmn with
      h1 | h2 | h3
    · left; exact Units.ext h1
    · right; left; exact Units.ext (h2.trans F1ga3_val.symm)
    · right; right
      have hsq : ((F1ga3 ^ 2 : F1GL32) : F1Mat3) = F1A3 ^ 2 := by
        rw [show ((F1ga3 ^ 2 : F1GL32) : F1Mat3) =
          ((F1ga3 : F1GL32) : F1Mat3) ^ 2 by simp, F1ga3_val]
      exact Units.ext (h3.trans hsq.symm)
  · exact Subgroup.le_centralizer (H := Subgroup.zpowers F1ga3)

theorem F1gt2_mem_normalizer :
    F1gt2 ∈ Subgroup.normalizer (Subgroup.zpowers F1ga3 : Set F1GL32) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  have hconj : MulAut.conj F1gt2 F1ga3 = F1ga3⁻¹ := by
    have h : F1ga3 ^ 2 = F1ga3⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      exact F1ga3_cube
    calc MulAut.conj F1gt2 F1ga3 = F1gt2 * F1ga3 * F1gt2⁻¹ := rfl
      _ = F1ga3 ^ 2 := F1gt2_conj_ga3
      _ = F1ga3⁻¹ := h
  change Subgroup.zpowers ((MulAut.conj F1gt2) F1ga3) = Subgroup.zpowers F1ga3
  rw [hconj, Subgroup.zpowers_inv]

theorem F1exists_inverting_zpowers_ga3 :
    ∃ t ∈ Subgroup.normalizer (Subgroup.zpowers F1ga3 : Set F1GL32),
      orderOf t = 2 ∧ ∀ x ∈ Subgroup.zpowers F1ga3, t * x * t⁻¹ = x⁻¹ :=
  ⟨F1gt2, F1gt2_mem_normalizer, F1orderOf_gt2, fun x hx => by
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    have h2 : F1ga3 ^ 2 = F1ga3⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      exact F1ga3_cube
    have hconj : F1gt2 * F1ga3 * F1gt2⁻¹ = F1ga3⁻¹ := by rw [F1gt2_conj_ga3, h2]
    calc F1gt2 * F1ga3 ^ k * F1gt2⁻¹ = (F1gt2 * F1ga3 * F1gt2⁻¹) ^ k := conj_zpow.symm
      _ = (F1ga3⁻¹) ^ k := by rw [hconj]
      _ = (F1ga3 ^ k)⁻¹ := inv_zpow F1ga3 k⟩

theorem F1exists_conj_zpowers_of_card_three (Q : Subgroup F1GL32) (hQ : Nat.card Q = 3) :
    ∃ g : F1GL32, Q = (Subgroup.zpowers F1ga3).map (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card F1GL32).factorization 3 = 1 := by
    rw [show Nat.card F1GL32 = 168 from CFSG.ComponentClassification.GHarris.card_GL32_gh]
    decide +kernel
  have hZcard : Nat.card (Subgroup.zpowers F1ga3) = 3 := by
    rw [Nat.card_zpowers, F1orderOf_ga3]
  let SZ : Sylow 3 F1GL32 := Sylow.ofCard (Subgroup.zpowers F1ga3) (by rw [hZcard, hfac]; norm_num)
  let SQ : Sylow 3 F1GL32 := Sylow.ofCard Q (by rw [hQ, hfac]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq F1GL32 SZ SQ
  refine ⟨g, ?_⟩
  have hQcoe : (SQ : Subgroup F1GL32) = Q := Sylow.coe_ofCard Q _
  have hZcoe : (SZ : Subgroup F1GL32) = Subgroup.zpowers F1ga3 := Sylow.coe_ofCard _ _
  have h1 : (SQ : Subgroup F1GL32) = (g • SZ : Sylow 3 F1GL32) :=
    congrArg (fun S : Sylow 3 F1GL32 => (S : Subgroup F1GL32)) hg.symm
  rw [← hQcoe, h1, Sylow.coe_subgroup_smul, hZcoe, Subgroup.pointwise_smul_def]
  rfl

theorem F1map_centralizer_equiv {A B : Type} [Group A] [Group B] (f : A ≃* B)
    (H : Subgroup A) :
    (Subgroup.centralizer H).map f.toMonoidHom =
      Subgroup.centralizer (H.map f.toMonoidHom) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx w hw]
  · intro y hy
    refine Subgroup.mem_map.mpr ⟨f.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    apply f.injective
    rw [map_mul, map_mul, f.apply_symm_apply]
    exact hy (f z) (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)

theorem F1exists_inverting_of_card_three_GL32 (Q : Subgroup F1GL32) (hQ : Nat.card Q = 3) :
    ∃ t ∈ Subgroup.normalizer (Q : Set F1GL32),
      orderOf t = 2 ∧ ∀ x ∈ Q, t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨g, rfl⟩ := F1exists_conj_zpowers_of_card_three Q hQ
  obtain ⟨t, htN, ht2, htin⟩ := F1exists_inverting_zpowers_ga3
  refine ⟨g * t * g⁻¹, ?_, ?_, ?_⟩
  · have hm : MulAut.conj g t ∈
        (Subgroup.normalizer (Subgroup.zpowers F1ga3 : Set F1GL32)).map
          (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨t, htN, rfl⟩
    rwa [Subgroup.map_equiv_normalizer_eq] at hm
  · have hord : orderOf ((MulAut.conj g) t) = 2 := by
      rw [MulEquiv.orderOf_eq, ht2]
    simpa using hord
  · rintro x ⟨z, hz, rfl⟩
    calc (g * t * g⁻¹) * (g * z * g⁻¹) * (g * t * g⁻¹)⁻¹
        = g * (t * z * t⁻¹) * g⁻¹ := by group
      _ = g * z⁻¹ * g⁻¹ := by rw [htin z hz]
      _ = (g * z * g⁻¹)⁻¹ := by group

theorem F1centralizer_eq_of_card_three_GL32 (Q : Subgroup F1GL32) (hQ : Nat.card Q = 3) :
    Subgroup.centralizer (Q : Set F1GL32) = Q := by
  obtain ⟨g, rfl⟩ := F1exists_conj_zpowers_of_card_three Q hQ
  rw [← F1map_centralizer_equiv (MulAut.conj g) (Subgroup.zpowers F1ga3),
    F1centralizer_zpowers_ga3]

theorem F1centralizer_eq_via (e : Y ≃* F1GL32) {P : Subgroup Y} (hP : Nat.card P = 3) :
    Subgroup.centralizer (P : Set Y) = P := by
  let Q : Subgroup F1GL32 := P.map e.toMonoidHom
  have hQ : Nat.card Q = 3 := by
    rw [show Q = P.map e.toMonoidHom from rfl,
      Subgroup.card_map_of_injective e.injective, hP]
  have hmap : (Subgroup.centralizer (P : Set Y)).map e.toMonoidHom = P.map e.toMonoidHom := by
    rw [F1map_centralizer_equiv]
    exact F1centralizer_eq_of_card_three_GL32 Q hQ
  exact le_antisymm ((Subgroup.map_le_map_iff_of_injective e.injective).mp hmap.le)
    ((Subgroup.map_le_map_iff_of_injective e.injective).mp hmap.ge)

theorem F1exists_inverting_via (e : Y ≃* F1GL32) {P : Subgroup Y} (hP : Nat.card P = 3) :
    ∃ t ∈ Subgroup.normalizer (P : Set Y),
      orderOf t = 2 ∧ ∀ x ∈ P, t * x * t⁻¹ = x⁻¹ := by
  let Q : Subgroup F1GL32 := P.map e.toMonoidHom
  have hQ : Nat.card Q = 3 := by
    rw [show Q = P.map e.toMonoidHom from rfl,
      Subgroup.card_map_of_injective e.injective, hP]
  obtain ⟨t, htN, ht2, htin⟩ := F1exists_inverting_of_card_three_GL32 Q hQ
  refine ⟨e.symm t, ?_, ?_, ?_⟩
  · exact (Subgroup.mem_map_equiv (f := e)
      (K := Subgroup.normalizer (P : Set Y))).mp
      (by rw [Subgroup.map_equiv_normalizer_eq]; exact htN)
  · rw [← e.orderOf_eq (e.symm t)]
    simpa using ht2
  · intro x hx
    apply e.injective
    simp only [map_mul, map_inv, e.apply_symm_apply]
    exact htin (e x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

theorem card_eq_of_isL3 (h : IsL3 Y 1) : Nat.card Y = 168 :=
  CFSG.SeitzReduction.LinearPilot.card_of_lieModel_PSL_three_two h

theorem isSimpleGroup_of_isL3 (h : IsL3 Y 1) : IsSimpleGroup Y := by
  obtain ⟨e⟩ := CFSG.SeitzReduction.LinearPilot.nonempty_equiv_GL32_of_lieModel h
  haveI : IsSimpleGroup F1GL32 := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  exact e.isSimpleGroup

theorem center_eq_bot_of_isL3 (h : IsL3 Y 1) : Subgroup.center Y = ⊥ := by
  haveI hs : IsSimpleGroup Y := isSimpleGroup_of_isL3 h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with hc | hc
  · exact hc
  · exfalso
    haveI : IsMulCommutative Y := Subgroup.center_eq_top_iff.mp hc
    have hp : (Nat.card Y).Prime := Group.is_simple_iff_prime_card.mp hs
    rw [card_eq_of_isL3 h] at hp
    norm_num at hp

theorem card_pGroup_dvd_of_isL3 (h : IsL3 Y 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup Y} (hP : IsPGroup p P) : Nat.card P ∣ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : p ^ k ∣ 168 := by
    have hcard := Subgroup.card_subgroup_dvd_card P
    rw [card_eq_of_isL3 h] at hcard
    rwa [← hk]
  have hp2not : ¬ p ^ 2 ∣ 168 := by
    intro h2
    have hle168 : p ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) h2
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hle12 : p ≤ 12 := by nlinarith
    interval_cases p <;> norm_num at h2
  have hk1 : k ≤ 1 := by
    by_contra hk'
    have h2k : 2 ≤ k := by omega
    exact hp2not (pow_dvd_pow p h2k |>.trans hdvd)
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with rfl | rfl
  · rw [hk, pow_zero]; exact one_dvd p
  · rw [hk, pow_one]

theorem card_sylow_three_of_isL3 (h : IsL3 Y 1) (P : Sylow 3 Y) : Nat.card P = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [P.card_eq_multiplicity, card_eq_of_isL3 h]
  decide +kernel

theorem exists_inverting_of_isL3 (h : IsL3 Y 1) {P : Subgroup Y} (hP : Nat.card P = 3) :
    ∃ t ∈ normalizer (P : Set Y), orderOf t = 2 ∧ ∀ x ∈ P, t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨e⟩ := CFSG.SeitzReduction.LinearPilot.nonempty_equiv_GL32_of_lieModel h
  exact F1exists_inverting_via e hP

theorem centralizer_eq_of_isL3 (h : IsL3 Y 1) {P : Subgroup Y} (hP : Nat.card P = 3) :
    centralizer (P : Set Y) = P := by
  obtain ⟨e⟩ := CFSG.SeitzReduction.LinearPilot.nonempty_equiv_GL32_of_lieModel h
  exact F1centralizer_eq_via e hP

theorem card_normalizer_seven_of_isL3 (h : IsL3 Y 1) {P : Subgroup Y} (hP : Nat.card P = 7) :
    Nat.card (normalizer (P : Set Y)) = 21 := by
  haveI := isSimpleGroup_of_isL3 h
  exact CFSG.GF2Type.Aschbacher1976Full.HS.card_normalizer_of_card_seven_simple168
    (card_eq_of_isL3 h) P hP

theorem centralizer_eq_of_isL3_seven (h : IsL3 Y 1) {P : Subgroup Y} (hP : Nat.card P = 7) :
    centralizer (P : Set Y) = P := by
  haveI hs : IsSimpleGroup Y := isSimpleGroup_of_isL3 h
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hN := card_normalizer_seven_of_isL3 h hP
  have hle : P ≤ centralizer (P : Set Y) := by
    haveI : IsCyclic P := isCyclic_of_prime_card (p := 7) hP
    exact Subgroup.le_centralizer (H := P)
  have hCN : centralizer (P : Set Y) ≤ normalizer (P : Set Y) :=
    Subgroup.centralizer_le_normalizer _
  have hdvd : Nat.card (centralizer (P : Set Y)) ∣ 21 :=
    (Subgroup.card_dvd_of_le hCN).trans (by rw [hN])
  have h7 : 7 ∣ Nat.card (centralizer (P : Set Y)) := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hP] at this
  have hc : Nat.card (centralizer (P : Set Y)) = 7 ∨
      Nat.card (centralizer (P : Set Y)) = 21 := by
    obtain ⟨m, hm⟩ := h7
    have hm3 : m ∣ 3 := by
      rw [hm] at hdvd
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 7)).mp hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with h1 | h3
    · left; rw [hm, h1, mul_one]
    · right; rw [hm, h3]
  rcases hc with hcard7 | hcard21
  · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard7, hP])).symm
  · exfalso
    have hNC : normalizer (P : Set Y) ≤ centralizer (P : Set Y) := by
      have heq : centralizer (P : Set Y) = normalizer (P : Set Y) :=
        Subgroup.eq_of_le_of_card_ge hCN (by rw [hN, hcard21])
      exact heq.ge
    let S : Sylow 7 Y := Sylow.ofCard P (by
      rw [hP, show (Nat.card Y).factorization 7 = 1 by rw [card_eq_of_isL3 h]; decide +kernel]
      norm_num)
    have hS : (S : Subgroup Y) = P := Sylow.coe_ofCard _ _
    have hburn : normalizer (S : Set Y) ≤ centralizer (S : Set Y) := by
      have heqS : (S : Set Y) = (P : Set Y) :=
        congrArg (fun H : Subgroup Y => (H : Set Y)) hS
      rw [heqS]
      exact hNC
    let K := (MonoidHom.transferSylow S hburn).ker
    have hKcard : Nat.card K = 24 := by
      have hc := (MonoidHom.ker_transferSylow_isComplement' S hburn).card_mul_card
      rw [card_eq_of_isL3 h] at hc
      have hScard : Nat.card (S : Subgroup Y) = 7 := by rw [hS, hP]
      rw [hScard, show (168 : ℕ) = 24 * 7 by norm_num] at hc
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) hc
    rcases hs.eq_bot_or_eq_top_of_normal K with hbot | htop
    · rw [hbot, Subgroup.card_bot] at hKcard; omega
    · rw [htop, Subgroup.card_top, card_eq_of_isL3 h] at hKcard; omega

theorem card_mulAut_dvd_of_isL3 (h : IsL3 Y 1) : Nat.card (MulAut Y) ∣ 336 := by
  rw [CFSG.SeitzReduction.LinearPilot.card_mulAut_of_lieModel_PSL_three_two h]

end Group

section Component

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_of_isElemAbelian {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hA : IsElemAbelian p A) : IsPGroup p A := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [IsPGroup.iff_orderOf]
  intro x
  have hx : x ^ p = 1 := Subtype.ext (hA.2 x.1 x.2)
  have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hx
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

theorem pRank_le_one_of_isL3 {L : Subgroup G} (h : IsL3 (Bar2 L) 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : Open.pRank p L ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E hEL hE
  have hE_p : IsPGroup p E := isPGroup_of_isElemAbelian hp hE
  have hE'p : IsPGroup p (E.subgroupOf L) := hE_p.comap_subtype
  have hpc : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  have hdisj : Disjoint (E.subgroupOf L) (CFSG.pCore 2 ↥L) :=
    IsPGroup.disjoint_of_ne p 2 hp2 _ _ hE'p hpc
  have hcardmap : Nat.card ((E.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) =
      Nat.card (E.subgroupOf L) := by
    have hinj : Function.Injective
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (E.subgroupOf L).subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      apply Subtype.ext
      have hxker : (x : ↥L) ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := hx
      rw [QuotientGroup.ker_mk'] at hxker
      have hmem : (x : ↥L) ∈ (E.subgroupOf L) ⊓ (CFSG.pCore 2 ↥L) := ⟨x.2, hxker⟩
      rw [disjoint_iff.mp hdisj] at hmem
      simpa using hmem
    have h := Subgroup.card_map_of_injective (K := ⊤) hinj
    rw [Subgroup.card_top] at h
    have htop : (E.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
        (⊤ : Subgroup (E.subgroupOf L)).map
          ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (E.subgroupOf L).subtype) := by
      rw [← Subgroup.map_map]
      congr 1
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [htop, h]
  have hmapp : IsPGroup p ((E.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :=
    hE'p.map _
  have hdiv : Nat.card ((E.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ∣ p :=
    card_pGroup_dvd_of_isL3 h hp hp2 hmapp
  have hle : Nat.card E ≤ p := by
    calc Nat.card E = Nat.card (E.subgroupOf L) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv).symm
      _ = Nat.card ((E.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :=
          hcardmap.symm
      _ ≤ p := Nat.le_of_dvd hp.pos hdiv
  simpa using hle

theorem card_sylow_three_of_isL3_bar2 {L P : Subgroup G} (h : IsL3 (Bar2 L) 1)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P L) : Nat.card P = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [hP.card_eq]
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  have hcardL : Nat.card L = 2 ^ k * 168 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L), hk,
      card_eq_of_isL3 h, mul_comm]
  have hfac : (Nat.card L).factorization 3 = 1 := by
    have h3pow : (2 ^ k).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h => by
        exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num))
    rw [hcardL, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      h3pow, show (168 : ℕ).factorization 3 = 1 by decide +kernel]
  rw [hfac, pow_one]

theorem pRank_three_of_isL3 {L : Subgroup G} (h : IsL3 (Bar2 L) 1) : Open.pRank 3 L = 1 := by
  apply le_antisymm
  · exact pRank_le_one_of_isL3 h Nat.prime_three (by norm_num)
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
    have hPcard : Nat.card P = 3 := card_sylow_three_of_isL3_bar2 h hP
    have hle : P ≤ L := hP.le
    haveI : IsCyclic P := isCyclic_of_prime_card (p := 3) hPcard
    have hE : IsElemAbelian 3 P := by
      refine ⟨inferInstance, ?_⟩
      intro x hx
      have h1 : orderOf (⟨x, hx⟩ : P) ∣ 3 := by
        have := orderOf_dvd_natCard (⟨x, hx⟩ : P)
        rwa [hPcard] at this
      have h2 : (⟨x, hx⟩ : P) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
      simpa using congrArg Subtype.val h2
    have hk : Nat.card P = 3 ^ 1 := by rw [hPcard, pow_one]
    exact CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hle hE hk

theorem thin8_of_isL3 {L : Subgroup G} (h : IsL3 (Bar2 L) 1) : Thin8 L :=
  fun p hp hp2 => pRank_le_one_of_isL3 h hp hp2

end Component

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
