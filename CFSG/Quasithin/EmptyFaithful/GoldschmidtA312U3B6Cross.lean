module

public import CFSG.RankThree.SubgroupLists.LinearTwoFamily

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.Assembly.LowTwoRank CFSG.RepresentationTheory CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

theorem exists_unit_sq_natCast {F : Type} [Field F] [Finite F] {r : ℕ} [Fact r.Prime]
    [CharP F r] (hr2 : r ≠ 2) (hF : Nat.card F = r ^ 2) {k : ℕ} (hk1 : 1 ≤ k) (hkr : k < r) :
    ∃ a : Fˣ, (k : F) = (a : F) ^ 2 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F r]; exact hr2
  have hcard : Fintype.card F = r ^ 2 := by rw [← Nat.card_eq_fintype_card, hF]
  have hk0 : (k : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F r]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hfermat : (k : F) ^ r = (k : F) := by
    exact (frobenius_def (R := F) (p := r) (k : F)).symm.trans (map_natCast (frobenius F r) k)
  have hpow1 : (k : F) ^ (r - 1) = 1 := by
    have hr1 : 1 ≤ r := (Fact.out : r.Prime).one_lt.le
    have h : (k : F) ^ (r - 1) * (k : F) = 1 * (k : F) := by
      rw [← pow_succ, Nat.sub_add_cancel hr1, hfermat, one_mul]
    exact mul_right_cancel₀ hk0 h
  obtain ⟨m, hm⟩ := (Fact.out : r.Prime).odd_of_ne_two hr2
  have hdiv : r ^ 2 / 2 = (r - 1) * (m + 1) := by
    have h : r ^ 2 = 2 * ((r - 1) * (m + 1)) + 1 := by
      rw [hm]
      simp only [Nat.add_sub_cancel]
      ring
    generalize r ^ 2 = N at h ⊢
    omega
  have hpow : (k : F) ^ (Fintype.card F / 2) = 1 := by
    rw [hcard, hdiv, pow_mul, hpow1, one_pow]
  obtain ⟨b, hb⟩ := (FiniteField.isSquare_iff hchar hk0).mpr hpow
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact hk0 hb
  exact ⟨Units.mk0 b hb0, by rw [Units.val_mk0, hb, sq]⟩

theorem linear_two_cross_f {K : Type} [Field K] [Finite K] {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hrK : (r : K) ≠ 0) (hf : 1 ≤ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = r ^ f) (e : (H ⧸ Subgroup.center H) ≃* StatedProj (StatedSL 2 F)) :
    f = 1 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : CharP F r := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow hr hF
  have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
    pow_three_eq_one_of_mem_center hZ hz
  have hr3' : Nat.Coprime r 3 := (Nat.coprime_primes hr Nat.prime_three).mpr hr3
  have hr5 : 5 ≤ r := hr.five_le_of_ne_two_of_ne_three hr2 hr3
  set e' := toPSL2 e with he'
  set u := e'.symm (rootPSL2 F) with hudef
  have hu1 : u ≠ 1 := fun h =>
    rootPSL2_ne_one (e'.symm.injective (by rw [← hudef, h, map_one]))
  have hur : u ^ r = 1 := by
    rw [hudef, ← map_pow, rootGroupPSL2_pow rootPSL2_mem_rootGroupPSL2, map_one]
  obtain ⟨x, hxu, hxr⟩ := exists_lift_pow_eq_one le_rfl hZ3 hr3' u hur
  set X : GL (Fin 3) K := (x : GL (Fin 3) K) with hXdef
  have hX1 : X ≠ 1 := fun h => hu1 (by
    rw [← hxu, show x = 1 from Subtype.ext h, QuotientGroup.mk_one])
  have hXr : X ^ r = 1 := by rw [hXdef, ← Subgroup.coe_pow, hxr, Subgroup.coe_one]
  have hconj : ∀ k : ℕ, (∃ a : Fˣ, (k : F) = (a : F) ^ 2) →
      IsConj X (X ^ (k : ZMod r).val) := by
    rintro k ⟨a, ha⟩
    have hS : IsConj u (u ^ k) := by
      obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_rootPSL2_pow (F := F) ha)
      exact isConj_iff.mpr ⟨e'.symm c, by
        rw [hudef, ← map_pow, ← map_inv, ← map_mul, ← map_mul, hc]⟩
    have hH : IsConj x (x ^ k) := isConj_of_isConj_mk le_rfl hZ3 hr3' hxr
      (by rw [← pow_mul, mul_comm, pow_mul, hxr, one_pow])
      (by rw [QuotientGroup.mk_pow, hxu]; exact hS)
    have hval : X ^ (k : ZMod r).val = X ^ k := by
      rw [ZMod.val_natCast]
      conv_rhs => rw [← Nat.div_add_mod k r, pow_add, pow_mul, hXr, one_pow, one_mul]
    rw [hval, hXdef, ← Subgroup.coe_pow]
    exact H.subtype.map_isConj hH
  set π := QuotientGroup.mk' (Subgroup.center H) with hπ
  set U := (rootGroupPSL2 F).map e'.symm.toMonoidHom with hUdef
  have hUcomm : ∀ y ∈ U, ∀ z ∈ U, y * z = z * y := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, rootGroupPSL2_comm hy hz]
  have hUexp : ∀ y ∈ U, y ^ r = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, rootGroupPSL2_pow hy, map_one]
  have hUp : IsPGroup r U := fun y =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, hUexp _ y.2, Subgroup.coe_one])⟩
  have hcen : π.ker ≤ Subgroup.center H := by rw [hπ, QuotientGroup.ker_mk']
  have hC : ¬ r ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    intro h
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (h.trans hZ))
  let eU := CFSG.LieType.CentralExt.liftSubgroupEquiv (QuotientGroup.mk'_surjective _) hcen hC hUp
  set E := (CFSG.LieType.CentralExt.liftSubgroup r π U).map H.subtype with hE
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : eU (⟨a, ha⟩ * ⟨b, hb⟩) = eU (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext (hUcomm _ (eU ⟨a, ha⟩).2 _ (eU ⟨b, hb⟩).2)
    have h3 : a * b = b * a := congrArg Subtype.val (eU.injective h1)
    exact congrArg Subtype.val h3
  have hEexp : ∀ a ∈ E, a ^ r = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : eU (⟨a, ha⟩ ^ r) = eU 1 := by
      rw [map_pow, map_one]
      exact Subtype.ext (by rw [Subgroup.coe_pow, hUexp _ (eU ⟨a, ha⟩).2, Subgroup.coe_one])
    have h3 : a ^ r = 1 := congrArg Subtype.val (eU.injective h1)
    change (a : GL (Fin 3) K) ^ r = 1
    rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
  have hEdet : ∀ a ∈ E, (a : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rintro _ ⟨a, -, rfl⟩
    exact hdet _ a.2
  have hEcard : Nat.card E = r ^ f := by
    rw [hE, Subgroup.card_map_of_injective H.subtype_injective, Nat.card_congr eU.toEquiv, hUdef,
      Subgroup.card_map_of_injective e'.symm.injective, card_rootGroupPSL2, hF]
  have hf2 : f ≤ 2 := by
    have := card_le_sq_of_elementary hrK E hEcomm hEexp hEdet
    rw [hEcard] at this
    exact (Nat.pow_le_pow_iff_right hr.one_lt).mp this
  rcases (by omega : f = 1 ∨ f = 2) with h | h
  · exact h
  exfalso
  subst h
  set Q := (Finset.Icc 1 4).image (fun m : ℕ => ((m : ℕ) : ZMod r)) with hQdef
  have hQcard : Q.card = 4 := by
    rw [hQdef, Finset.card_image_of_injOn]
    · simp
    · intro m₁ hm₁ m₂ hm₂ h
      simp only [Finset.coe_Icc, Set.mem_Icc] at hm₁ hm₂
      have h' : (m₁ : ZMod r) = m₂ := h
      rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at h'
  have hQ : ∀ k ∈ Q, k ≠ 0 ∧ IsConj X (X ^ k.val) := by
    intro k hk
    rw [hQdef, Finset.mem_image] at hk
    obtain ⟨m, hm, rfl⟩ := hk
    simp only [Finset.mem_Icc] at hm
    refine ⟨?_, hconj m (exists_unit_sq_natCast hr2 hF hm.1 (by omega))⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have := card_le_three_of_isConj_pow hrK hXr hX1 Q hQ
  omega

end CFSG.Quasithin.A312U3
