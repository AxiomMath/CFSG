module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofOuter
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofClassical
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Item223CensusProof

theorem linearAutGroup_eq_range (n : ℕ) (K : Type) [Field K] :
    linearAutGroup n K = (conjAut n K).range :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup_eq_range

theorem isInnerAut_conjAut_of_det_eq_pow {n : ℕ} {K : Type} [Field K] (_hn : 1 ≤ n)
    {A : GL (Fin n) K} {u : Kˣ} (hu : Matrix.GeneralLinearGroup.det A = u ^ n) :
    IsInnerAut (conjAut n K A) :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_mem_range_conj_of_det_eq_pow hu

theorem eq_zpow_bezout {M : Type*} [CommGroup M] (x : M) {a b : ℤ} {m n : ℕ}
    (hab : a * m + b * n = 1) : x = (x ^ m) ^ a * (x ^ n) ^ b := by
  rw [← zpow_natCast x m, ← zpow_natCast x n, ← zpow_mul, ← zpow_mul, ← zpow_add,
    mul_comm (m : ℤ), mul_comm (n : ℤ), hab, zpow_one]

theorem pow_zpow_comm {M : Type*} [Group M] (x : M) (n : ℕ) (a : ℤ) :
    (x ^ n) ^ a = (x ^ a) ^ n := by
  rw [← zpow_natCast x n, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]

theorem isCoprime_three_of_not_dvd {n : ℕ} (h : ¬ 3 ∣ n) : IsCoprime ((3 : ℕ) : ℤ) (n : ℤ) :=
  Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h)

theorem exists_eq_pow_of_pow_three_eq_pow {K : Type} [Field K] [Finite K] {n : ℕ}
    (h3 : ¬ (3 ∣ n ∧ 3 ∣ Nat.card K - 1)) {d c : Kˣ} (h : d ^ 3 = c ^ n) :
    ∃ u : Kˣ, d = u ^ n := by
  by_cases h3n : 3 ∣ n
  · have hN : ¬ 3 ∣ Nat.card Kˣ := by
      rw [Nat.card_units]
      exact fun h' => h3 ⟨h3n, h'⟩
    obtain ⟨a, b, hab⟩ := isCoprime_three_of_not_dvd hN
    refine ⟨c ^ a, ?_⟩
    have hd : d ^ (Nat.card Kˣ) = 1 := pow_card_eq_one'
    rw [eq_zpow_bezout d hab, h, hd, one_zpow, mul_one, pow_zpow_comm]
  · obtain ⟨a, b, hab⟩ := isCoprime_three_of_not_dvd h3n
    refine ⟨c ^ a * d ^ b, ?_⟩
    conv_lhs => rw [eq_zpow_bezout d hab]
    rw [h, pow_zpow_comm, pow_zpow_comm, mul_pow]

theorem isInnerAut_of_mem_linearAutGroup_of_pow_three {n : ℕ} {K : Type} [Field K] [Finite K]
    (hn : 3 ≤ n) (h3 : ¬ (3 ∣ n ∧ 3 ∣ Nat.card K - 1)) {τ : MulAut (projectiveSL n K)}
    (hτ : τ ∈ linearAutGroup n K) (hτ3 : τ ^ 3 = 1) : IsInnerAut τ := by
  rw [linearAutGroup_eq_range] at hτ
  obtain ⟨A, rfl⟩ := hτ
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn (A ^ 3) 1
    (by rw [map_one, mul_one, map_pow, hτ3])
  have hdet : Matrix.GeneralLinearGroup.det A ^ 3 = c ^ n := by
    have h1 := congrArg Matrix.GeneralLinearGroup.det hc
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow] at h1
    exact h1.symm
  obtain ⟨u, hu⟩ := exists_eq_pow_of_pow_three_eq_pow h3 hdet
  exact isInnerAut_conjAut_of_det_eq_pow (by omega) hu

theorem isInnerAut_psuConj_of_not_dvd {p f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData p f K} (h3 : ¬ 3 ∣ p ^ f + 1) (A : unitaryIsom3 h) :
    IsInnerAut (psuConj h A) := by
  have := h.finite
  set q := p ^ f with hqdef
  set d : Kˣ := Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K) with hddef
  have hd : d ^ (q + 1) = 1 := by
    have hA := mem_unitaryIsom3.mp A.2
    have h1 := congrArg Matrix.det hA
    have hbar : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar).det =
        h.bar ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det :=
      (RingHom.map_det h.bar _).symm
    rw [Matrix.det_mul, Matrix.det_transpose, hbar, Matrix.det_one,
      UnitaryFieldData.bar_apply] at h1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ]
    exact h1
  obtain ⟨a, b, hab⟩ := isCoprime_three_of_not_dvd h3
  set l : Kˣ := d ^ a with hldef
  have hl3 : l ^ 3 = d := by
    rw [hldef, ← pow_zpow_comm]
    conv_rhs => rw [eq_zpow_bezout d hab, hd, one_zpow, mul_one]
  have hlq : l ^ (q + 1) = 1 := by
    rw [hldef, ← pow_zpow_comm, hd, one_zpow]
  have hnorm : h.bar (l : K) * (l : K) = 1 := by
    rw [UnitaryFieldData.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, hlq, Units.val_one]
  have hs : Matrix.GeneralLinearGroup.scalar (Fin 3) l ∈ unitaryIsom3 h := by
    rw [mem_unitaryIsom3, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, hnorm]
    · simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, hij]
  set S : unitaryIsom3 h := ⟨_, hs⟩ with hSdef
  have hS1 : psuConj h S = 1 := (Sec4.psuConj_eq_one_iff S).mpr ⟨l, rfl⟩
  have hB : ((S⁻¹ * A : unitaryIsom3 h) : GL (Fin 3) K) ∈ unitarySU p f K 3 := by
    refine (mem_unitarySU_iff h).mpr ⟨?_, (S⁻¹ * A).2⟩
    have h1 : Matrix.GeneralLinearGroup.det ((S⁻¹ * A : unitaryIsom3 h) : GL (Fin 3) K) = 1 := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hSdef,
        Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hl3, ← hddef, inv_mul_cancel]
    have h2 := congrArg (fun v : Kˣ => (v : K)) h1
    simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using h2
  have hAeq : A = S * ⟨((S⁻¹ * A : unitaryIsom3 h) : GL (Fin 3) K),
      unitarySU_le_unitaryIsom3 hB⟩ := by
    apply Subtype.ext
    simp
  rw [hAeq, map_mul, hS1, one_mul]
  exact ⟨_, conj_mk_eq_psuConj ⟨_, hB⟩⟩

variable {G : Type} [Group G] [Finite G]

theorem false_of_forall_mem {X A : Subgroup G} {M : Type*} [Group M]
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hA81 : Nat.card A = 3 ^ 4)
    (hAN : A ≤ Subgroup.normalizer (X : Set G))
    (hAC : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3)
    (φ : MulAut (X ⧸ aschbacherSolvableCore 3 X) →* MulAut M) (hφ : Function.Injective φ)
    (N : Subgroup (MulAut M))
    (hN : ∀ F : Subgroup (MulAut M), CFSG.Assembly.IsElemAbelian 3 F → F ≤ N → Nat.card F ≤ 9)
    (hmem : ∀ a (ha : a ∈ A), φ (Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨a, hAN ha⟩)) ∈ N) :
    False := by
  set ρ := φ.comp (Sec4.thetaAct hAN)
  have hρ : CFSG.Assembly.IsElemAbelian 3 ρ.range := by
    rw [MonoidHom.range_comp]
    exact Sec4.isElemAbelian_map φ (Sec4.isElemAbelian_range_thetaAct hAN hAe)
  have h1 := hN ρ.range hρ (by
    rintro _ ⟨a, rfl⟩
    exact hmem a a.2)
  have h2 : Nat.card ρ.range = 3 ^ 3 := by
    rw [MonoidHom.range_comp, Subgroup.card_map_of_injective hφ]
    have h := card_range_thetaAct hAN
    rw [hAC, hA81] at h
    omega
  rw [h2] at h1
  norm_num at h1

theorem isInnerAut_inducedAutHom_of_not {X : Subgroup G} {M : Type*} [Group M]
    (e : X ⧸ aschbacherSolvableCore 3 X ≃* M) {a : G} (ha : a ∈ Subgroup.normalizer (X : Set G))
    (hin : ¬ Sec4.InducesOuterTheta a X) : IsInnerAut (inducedAutHom X e ⟨a, ha⟩) := by
  by_contra hni
  exact hin ((not_isInnerAut_inducedAutHom_iff X e ha).mp hni)

theorem three_ne_zero_of_dvd_card_sub_one {K : Type} [Field K] [Finite K]
    (h : 3 ∣ Nat.card K - 1) : (3 : K) ≠ 0 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, f, hp, hK⟩ := FiniteField.card' K
  rw [← Nat.card_eq_fintype_card] at hK
  refine Sec4.three_ne_zero_of_card hp (fun hp3 => ?_) hK
  subst hp3
  rw [hK] at h
  have h3 : 3 ∣ 3 ^ (f : ℕ) := dvd_pow_self 3 f.ne_zero
  have h1 : 1 ≤ 3 ^ (f : ℕ) := Nat.one_le_pow _ _ (by norm_num)
  have h5 : 3 ^ (f : ℕ) - 1 + 1 = 3 ^ (f : ℕ) := Nat.sub_add_cancel h1
  have h4 := (Nat.dvd_add_right h).mp (h5 ▸ h3)
  norm_num at h4

theorem three_ne_zero_of_dvd_add_one {p f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData p f K)
    (h : 3 ∣ p ^ f + 1) : (3 : K) ≠ 0 := by
  have := hK.finite
  refine Sec4.three_ne_zero_of_card hK.prime (fun hp3 => ?_) hK.card
  subst hp3
  have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := hK.one_le; omega)
  have h4 := (Nat.dvd_add_right h3).mp h
  norm_num at h4

end Item223CensusProof

open Item223CensusProof


@[expose] def Outer223High : Prop :=
  ∀ (Y : Type) [Group Y], Sec4.IsList46 Y →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K], 4 ≤ n → 3 ∣ n → 3 ∣ Nat.card K - 1 →
      IsEmpty (Y ≃* projectiveSL n K) ∧ IsEmpty (Y ≃* Matrix.SpecialLinearGroup (Fin n) K)

@[expose] def Outer223Cross : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G) (y : G),
    Sec4.IsList46 (X ⧸ aschbacherSolvableCore 3 X) → y ^ 3 = 1 →
    KFacts.InducesStdKind X y .diagonal →
    (∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K - 1 →
      ∀ (e : X ⧸ aschbacherSolvableCore 3 X ≃* projectiveSL 3 K)
        (hy : y ∈ Subgroup.normalizer (X : Set G)),
        inducedAutHom X e ⟨y, hy⟩ ∈ linearAutGroup 3 K) ∧
    (∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K - 1 →
      ∀ (e : X ⧸ aschbacherSolvableCore 3 X ≃* Matrix.SpecialLinearGroup (Fin 3) K)
        (hy : y ∈ Subgroup.normalizer (X : Set G)),
        descendAut 3 K (inducedAutHom X e ⟨y, hy⟩) ∈ linearAutGroup 3 K) ∧
    (∀ (p f : ℕ) (K : Type) [Field K] (hK : UnitaryFieldData p f K), 3 ∣ p ^ f + 1 →
      ∀ (e : X ⧸ aschbacherSolvableCore 3 X ≃* unitaryPSU hK 3)
        (hy : y ∈ Subgroup.normalizer (X : Set G)),
        inducedAutHom X e ⟨y, hy⟩ ∈ (psuConj hK).range) ∧
    ∀ (p f : ℕ) (K : Type) [Field K] (hK : UnitaryFieldData p f K) (hq : 2 < p ^ f),
      3 ∣ p ^ f + 1 →
      ∀ (e : X ⧸ aschbacherSolvableCore 3 X ≃* unitarySU p f K 3)
        (hy : y ∈ Subgroup.normalizer (X : Set G)),
        MulAut.congr (suCenterEquiv hK hq)
          (centerDescend _ (inducedAutHom X e ⟨y, hy⟩)) ∈ (psuConj hK).range

theorem outer223Linear_of (hHigh : Outer223High) (hCross : Outer223Cross) : Outer223Linear := by
  intro G _ _ X A hL hAe hA81 hAN hAC hdiag x hxA hout
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hcr := fun a (ha : a ∈ A) (houta : Sec4.InducesOuterTheta a X) =>
    hCross G X a hL (hAe.2 a ha) (hdiag a ha houta)
  refine ⟨fun n K _ _ hn => ⟨fun h => ?_, fun h => ?_⟩,
    fun p f K _ hK hq => ⟨fun h => ?_, fun h => ?_⟩⟩
  ·
    obtain ⟨e, hx, hτ, hni⟩ := h
    by_cases h3 : 3 ∣ n ∧ 3 ∣ Nat.card K - 1
    · rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
      · have hK3 := three_ne_zero_of_dvd_card_sub_one h3.2
        refine false_of_forall_mem hAe hA81 hAN hAC (MulAut.congr e).toMonoidHom
          (MulAut.congr e).injective (linearAutGroup 3 K) (fun F hF hFN => ?_) (fun a ha => ?_)
        · have h9 := Sec4.card_inf_linearAutGroup_three_le hK3 hF
          rwa [inf_eq_left.mpr hFN] at h9
        · change inducedAutHom X e ⟨a, hAN ha⟩ ∈ linearAutGroup 3 K
          by_cases houta : Sec4.InducesOuterTheta a X
          · exact (hcr a ha houta).1 K h3.2 e (hAN ha)
          · obtain ⟨y, hy⟩ := isInnerAut_inducedAutHom_of_not e (hAN ha) houta
            rw [← hy]
            exact innAut_le_linearAutGroup 3 K ⟨y, rfl⟩
      · exact (hHigh _ hL n K hn4 h3.1 h3.2).1.false e
    · exact hni (isInnerAut_of_mem_linearAutGroup_of_pow_three hn h3 hτ
        (inducedAutHom_pow_eq_one X e hx hx3))
  ·
    obtain ⟨e, hx, hτ, hni⟩ := h
    by_cases h3 : 3 ∣ n ∧ 3 ∣ Nat.card K - 1
    · rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
      · have hK3 := three_ne_zero_of_dvd_card_sub_one h3.2
        refine false_of_forall_mem hAe hA81 hAN hAC
          ((descendAut 3 K).comp (MulAut.congr e).toMonoidHom)
          (Sec4.descendAut_three_injective.comp (MulAut.congr e).injective) (linearAutGroup 3 K)
          (fun F hF hFN => ?_) (fun a ha => ?_)
        · have h9 := Sec4.card_inf_linearAutGroup_three_le hK3 hF
          rwa [inf_eq_left.mpr hFN] at h9
        · change descendAut 3 K (inducedAutHom X e ⟨a, hAN ha⟩) ∈ linearAutGroup 3 K
          by_cases houta : Sec4.InducesOuterTheta a X
          · exact (hcr a ha houta).2.1 K h3.2 e (hAN ha)
          · obtain ⟨y, hy⟩ := isInnerAut_inducedAutHom_of_not e (hAN ha) houta
            rw [← hy, descendAut_conj]
            exact innAut_le_linearAutGroup 3 K ⟨_, rfl⟩
      · exact (hHigh _ hL n K hn4 h3.1 h3.2).2.false e
    · exact hni (isInnerAut_of_mem_linearAutGroup_of_pow_three hn h3 hτ
        (by rw [← map_pow, inducedAutHom_pow_eq_one X e hx hx3, map_one]))
  ·
    obtain ⟨e, hx, hτ, hni⟩ := h
    by_cases h3 : 3 ∣ p ^ f + 1
    · have := hK.finite
      have hK3 := three_ne_zero_of_dvd_add_one hK h3
      refine false_of_forall_mem hAe hA81 hAN hAC (MulAut.congr e).toMonoidHom
        (MulAut.congr e).injective (psuConj hK).range
        (fun F hF hFN => card_le_nine_of_le_psuConj_range hK3 F hF hFN) (fun a ha => ?_)
      change inducedAutHom X e ⟨a, hAN ha⟩ ∈ (psuConj hK).range
      by_cases houta : Sec4.InducesOuterTheta a X
      · exact (hcr a ha houta).2.2.1 p f K hK h3 e (hAN ha)
      · obtain ⟨y, hy⟩ := isInnerAut_inducedAutHom_of_not e (hAN ha) houta
        rw [← hy]
        exact (stdPinnedPSU3 hK).inn_le ⟨y, rfl⟩
    · obtain ⟨B, hB⟩ := hτ
      rw [← hB] at hni
      exact hni (isInnerAut_psuConj_of_not_dvd h3 B)
  ·
    obtain ⟨e, hx, hτ, hni⟩ := h
    by_cases h3 : 3 ∣ p ^ f + 1
    · have := hK.finite
      have hK3 := three_ne_zero_of_dvd_add_one hK h3
      refine false_of_forall_mem hAe hA81 hAN hAC
        ((MulAut.congr (suCenterEquiv hK hq)).toMonoidHom.comp
          ((centerDescend (unitarySU p f K 3)).comp (MulAut.congr e).toMonoidHom))
        ((MulAut.congr (suCenterEquiv hK hq)).injective.comp
          ((centerDescend_injective_unitarySU hK hq).comp (MulAut.congr e).injective))
        (psuConj hK).range
        (fun F hF hFN => card_le_nine_of_le_psuConj_range hK3 F hF hFN) (fun a ha => ?_)
      change MulAut.congr (suCenterEquiv hK hq)
        (centerDescend _ (inducedAutHom X e ⟨a, hAN ha⟩)) ∈ (psuConj hK).range
      by_cases houta : Sec4.InducesOuterTheta a X
      · exact (hcr a ha houta).2.2.2 p f K hK hq h3 e (hAN ha)
      · obtain ⟨y, hy⟩ := isInnerAut_inducedAutHom_of_not e (hAN ha) houta
        rw [← hy, centerDescend_conj, congr_mulAutConj]
        exact (stdPinnedPSU3 hK).inn_le ⟨_, rfl⟩
    · obtain ⟨B, hB⟩ := hτ
      rw [← hB] at hni
      exact hni (isInnerAut_psuConj_of_not_dvd h3 B)

end CFSG.RankThree.PartTwo.Sec21
