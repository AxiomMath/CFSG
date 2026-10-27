module

public import CFSG.Quasithin.Vol2.Ch9Sec3FactsLie
public import CFSG.CharacterTheory.SteinbergBYFieldFour
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.CharacterTheory.SteinbergBY
open scoped commutatorElement

namespace SL3Four

@[expose] def h0Mat : Matrix (Fin 3) (Fin 3) FieldFour := !![0, 1, 0; 1, FieldFour.ω, 0; 0, 0, 1]

theorem h0Mat_det : h0Mat.det = 1 := by
  rw [Matrix.det_fin_three]
  decide

@[expose] def h0 : Matrix.SpecialLinearGroup (Fin 3) FieldFour := ⟨h0Mat, h0Mat_det⟩

theorem orderOf_h0 : orderOf h0 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    show h0Mat ^ 5 = 1
    decide
  · intro h
    exact (by decide : h0Mat ≠ 1) (congrArg Subtype.val h)

theorem eq_scalar_of_commute (M : Matrix (Fin 3) (Fin 3) FieldFour) (hc : M * h0Mat = h0Mat * M)
    (h3 : M ^ 3 = 1) (hdet : M.det = 1) : M = Matrix.scalar (Fin 3) (M 0 0) := by
  have e : ∀ i j, (M * h0Mat) i j = (h0Mat * M) i j := fun i j => by rw [hc]
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  simp only [Matrix.mul_apply, Fin.sum_univ_three, h0Mat, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const, mul_zero,
    zero_mul, mul_one, one_mul, add_zero, zero_add] at e00 e01 e02 e12 e20 e21
  have h02 : M 0 2 = 0 ∧ M 1 2 = 0 := by
    revert e02 e12
    generalize M 0 2 = x
    generalize M 1 2 = y
    revert x y
    decide
  have h20 : M 2 0 = 0 ∧ M 2 1 = 0 := by
    revert e20 e21
    generalize M 2 0 = x
    generalize M 2 1 = y
    revert x y
    decide
  have h10 : M 1 0 = M 0 1 := by
    revert e00
    generalize M 0 1 = x
    generalize M 1 0 = y
    revert x y
    decide
  have h11 : M 1 1 = M 0 0 + FieldFour.ω * M 0 1 := by
    revert e01
    generalize M 0 0 = x
    generalize M 0 1 = y
    generalize M 1 1 = z
    revert x y z
    decide
  have hM : M = !![M 0 0, M 0 1, 0; M 0 1, M 0 0 + FieldFour.ω * M 0 1, 0; 0, 0, M 2 2] := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [h02.1, h02.2, h20.1, h20.2, h10, h11]
  have key : ∀ a b r : FieldFour,
      (!![a, b, 0; b, a + FieldFour.ω * b, 0; 0, 0, r] : Matrix (Fin 3) (Fin 3) FieldFour) ^ 3 = 1 →
      (!![a, b, 0; b, a + FieldFour.ω * b, 0; 0, 0, r] : Matrix (Fin 3) (Fin 3) FieldFour).det = 1 →
      b = 0 ∧ r = a := by
    intro a b r h3' hd'
    rw [Matrix.det_fin_three] at hd'
    revert h3' hd'
    revert a b r
    decide
  rw [hM] at h3 hdet
  obtain ⟨hb, hr⟩ := key _ _ _ h3 hdet
  rw [hM]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [hb, hr]

theorem card_SL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) FieldFour) = 60480 := by
  rw [Matrix.card_SL_field, FieldFour.card_eq]
  simp [Fin.prod_univ_three]

theorem mem_center_of_commute_h0 (g : Matrix.SpecialLinearGroup (Fin 3) FieldFour) (h3 : g ^ 3 = 1)
    (hc : g * h0 = h0 * g) : g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) FieldFour) := by
  have h3' : (g : Matrix (Fin 3) (Fin 3) FieldFour) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, h3, Matrix.SpecialLinearGroup.coe_one]
  have hM := eq_scalar_of_commute (g : Matrix (Fin 3) (Fin 3) FieldFour)
    (congrArg Subtype.val hc) h3'
    g.2
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨(g : Matrix (Fin 3) (Fin 3) FieldFour) 0 0, ?_, hM.symm⟩
  have hdet := g.2
  rw [hM, Matrix.det_fin_three] at hdet
  rw [Fintype.card_fin]
  revert hdet
  generalize (g : Matrix (Fin 3) (Fin 3) FieldFour) 0 0 = r
  revert r
  decide

theorem exists_conj_mem_zpowers_h0 (h : Matrix.SpecialLinearGroup (Fin 3) FieldFour)
    (hh : orderOf h = 5) :
    ∃ x : Matrix.SpecialLinearGroup (Fin 3) FieldFour, x * h * x⁻¹ ∈ Subgroup.zpowers h0 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hidx : ∀ y : Matrix.SpecialLinearGroup (Fin 3) FieldFour, orderOf y = 5 →
      ¬ 5 ∣ (Subgroup.zpowers y).index := by
    intro y hy h5
    have h1 := (Subgroup.zpowers y).card_mul_index
    rw [Nat.card_zpowers, hy, card_SL] at h1
    omega
  have hp : ∀ y : Matrix.SpecialLinearGroup (Fin 3) FieldFour, orderOf y = 5 →
      IsPGroup 5 (Subgroup.zpowers y) := fun y hy =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 3) FieldFour)
    ((hp h hh).toSylow (hidx h hh)) ((hp h0 orderOf_h0).toSylow (hidx h0 orderOf_h0))
  refine ⟨x, ?_⟩
  have h1 := congrArg (fun P : Sylow 5 (Matrix.SpecialLinearGroup (Fin 3) FieldFour) =>
    (P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) FieldFour))) hx
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
  rw [← h1]
  have h2 := Subgroup.smul_mem_pointwise_smul h (MulAut.conj x) _ (Subgroup.mem_zpowers h)
  simpa [MulAut.smul_def, MulAut.conj_apply] using h2

theorem mem_center_of_commute (g h : Matrix.SpecialLinearGroup (Fin 3) FieldFour) (h3 : g ^ 3 = 1)
    (hh : orderOf h = 5) (hc : g * h = h * g) :
    g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) FieldFour) := by
  obtain ⟨x, hx⟩ := exists_conj_mem_zpowers_h0 h hh
  have hord : orderOf (x * h * x⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hh]
  have hz : Subgroup.zpowers (x * h * x⁻¹) = Subgroup.zpowers h0 :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, orderOf_h0])
  have hcomm : Commute (x * g * x⁻¹) (x * h * x⁻¹) := by
    have := (Commute.map (show Commute g h from hc) (MulAut.conj x))
    simpa [MulAut.conj_apply] using this
  have hh0 : h0 ∈ Subgroup.zpowers (x * h * x⁻¹) := by
    rw [hz]
    exact Subgroup.mem_zpowers h0
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh0
  have hc0 : (x * g * x⁻¹) * h0 = h0 * (x * g * x⁻¹) := by
    rw [← hk]
    exact (hcomm.zpow_right k).eq
  have hg3 : (x * g * x⁻¹) ^ 3 = 1 := by
    rw [← MulAut.conj_apply, ← map_pow, h3, map_one]
  have hcen := mem_center_of_commute_h0 _ hg3 hc0
  have hgx : x * g * x⁻¹ = g := by
    have h1 := Subgroup.mem_center_iff.mp hcen x
    calc x * g * x⁻¹ = x⁻¹ * (x * (x * g * x⁻¹)) := by group
      _ = x⁻¹ * ((x * g * x⁻¹) * x) := by rw [h1]
      _ = g := by group
  rw [← hgx]
  exact hcen

theorem mem_center_of_commute' {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (g h : Matrix.SpecialLinearGroup (Fin 3) K) (h3 : g ^ 3 = 1) (hh : orderOf h = 5)
    (hc : g * h = h * g) : g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
  have := Fintype.ofFinite K
  set φ : K ≃+* FieldFour :=
    FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hK, FieldFour.card_eq])
    with hφ
  set Φ : Matrix.SpecialLinearGroup (Fin 3) K ≃* Matrix.SpecialLinearGroup (Fin 3) FieldFour :=
    MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map φ.toRingHom)
      (Matrix.SpecialLinearGroup.map φ.symm.toRingHom)
      (by
        ext A : 1
        apply Subtype.ext
        refine Matrix.ext fun i j => ?_
        simp [Matrix.SpecialLinearGroup.map_apply_coe])
      (by
        ext A : 1
        apply Subtype.ext
        refine Matrix.ext fun i j => ?_
        simp [Matrix.SpecialLinearGroup.map_apply_coe])
    with hΦ
  have hcen := mem_center_of_commute (Φ g) (Φ h) (by rw [← map_pow, h3, map_one])
    (by rw [MulEquiv.orderOf_eq, hh]) (by rw [← map_mul, hc, map_mul])
  rw [Subgroup.mem_center_iff] at hcen ⊢
  intro y
  apply Φ.injective
  rw [map_mul, map_mul]
  exact hcen (Φ y)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCoreOf_iff {L : Subgroup G} (x : ↥L) :
    (x : G) ∈ pCoreOf 2 L ↔ x ∈ CFSG.pCore 2 ↥L := CFSG.mem_openPCoreOf_iff x

omit [Finite G] in
theorem not_mem_of_orderOf_five {P : Subgroup G} (hP : IsPGroup 2 P) {y : G} (hy : orderOf y = 5)
    (hyP : y ∈ P) : False := by
  obtain ⟨k, hk⟩ := hP ⟨y, hyP⟩
  have h1 : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hy] at h2
  have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
    ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h2))
  omega

omit [Finite G] in
theorem exists_pow_five_mem {L : Subgroup G} (hA5 : Nonempty (O2Q L ≃* alternatingGroup (Fin 5))) :
    ∃ x ∈ L, x ^ 5 ∈ pCoreOf 2 L ∧ x ∉ pCoreOf 2 L := by
  obtain ⟨ψ⟩ := hA5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set σ : alternatingGroup (Fin 5) :=
    ⟨finRotate 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ with hσ
  have hσ5 : σ ^ 5 = 1 := by
    apply Subtype.ext
    decide
  have hσ1 : σ ≠ 1 := by
    intro h
    have := congrArg Subtype.val h
    exact (by decide : finRotate 5 ≠ 1) this
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (ψ.symm σ)
  refine ⟨x, x.2, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, mem_pCoreOf_iff (x ^ 5), ← QuotientGroup.eq_one_iff,
      QuotientGroup.mk_pow, hx, ← map_pow, hσ5, map_one]
  · rw [mem_pCoreOf_iff x, ← QuotientGroup.eq_one_iff, hx]
    intro h
    apply hσ1
    rw [← ψ.apply_symm_apply σ, h, map_one]

theorem exists_orderOf_five_commute {L : Subgroup G} {d : G} (hd3 : orderOf d = 3)
    (hdL : d ∈ Subgroup.normalizer (L : Set G))
    (hLd : ⁅L, Subgroup.zpowers d⁆ ≤ pCoreOf 2 L)
    (hA5 : Nonempty (O2Q L ≃* alternatingGroup (Fin 5))) :
    ∃ e ∈ L, orderOf e = 5 ∧ e * d = d * e := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hxL, hx5, hxQ⟩ := exists_pow_five_mem hA5
  set H := Subgroup.normalizer (L : Set G) with hH
  set Q := pCoreOf 2 L with hQ
  have hQL : Q ≤ L := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L
  have hLH : L ≤ H := Subgroup.le_normalizer
  have hQH : Q ≤ H := hQL.trans hLH
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 L
  set N : Subgroup ↥H := Q.subgroupOf H with hNdef
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hHQ
  have hQ2 : IsPGroup 2 Q := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L
  have hN3 : ¬ 3 ∣ Nat.card N := by
    have hNQ : Nat.card N = Nat.card Q := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hQ2)
    rw [hNQ, hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h3))
    omega
  set d' : ↥H := ⟨d, hdL⟩ with hd'
  set A : Subgroup ↥H := Subgroup.zpowers d' with hA
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk, hd3])
  have hmapC := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 N hN3 A hA3
  set x' : ↥H := ⟨x, hLH hxL⟩ with hx'
  have hxC : QuotientGroup.mk' N x' ∈
      Subgroup.centralizer ((A.map (QuotientGroup.mk' N) : Subgroup (↥H ⧸ N)) : Set (↥H ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hc : ⁅x⁻¹, (d ^ i)⁻¹⁆ ∈ Q :=
      hLd (Subgroup.commutator_mem_commutator (L.inv_mem hxL)
        (Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers d i)))
    convert hc using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, hd', hx',
      commutatorElement_def, inv_inv, mul_inv_rev]
    group
  rw [← hmapC] at hxC
  obtain ⟨c', hc'C, hc'x⟩ := hxC
  have hcd : c' * d' = d' * c' :=
    (Subgroup.mem_centralizer_iff.mp hc'C d' (Subgroup.mem_zpowers d')).symm
  have hcx : c'⁻¹ * x' ∈ N := QuotientGroup.eq.mp hc'x
  set c : G := (c' : G) with hc
  have hcxQ : c⁻¹ * x ∈ Q := hcx
  have hcL : c ∈ L := by
    have h1 : c = x * (c⁻¹ * x)⁻¹ := by group
    rw [h1]
    exact L.mul_mem hxL (L.inv_mem (hQL hcxQ))
  have hcQ : c ∉ Q := fun h => hxQ (by
    have h1 : x = c * (c⁻¹ * x) := by group
    rw [h1]
    exact Q.mul_mem h hcxQ)
  have hc5 : c ^ 5 ∈ Q := by
    have h1 : QuotientGroup.mk' N (c' ^ 5) = QuotientGroup.mk' N (x' ^ 5) := by
      rw [map_pow, map_pow, hc'x]
    have h2 : x' ^ 5 ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      simpa [hx'] using hx5
    have h3 : c' ^ 5 ∈ N := by
      rw [← QuotientGroup.eq_one_iff] at h2 ⊢
      rw [QuotientGroup.mk'_apply] at h1
      rw [h1]
      exact h2
    rw [Subgroup.mem_subgroupOf] at h3
    simpa [hc] using h3
  set m := Nat.card Q with hm
  have hcd' : c * d = d * c := by
    have := congrArg Subtype.val hcd
    simpa [hc, hd'] using this
  refine ⟨c ^ m, L.pow_mem hcL m, ?_, (Commute.pow_left hcd' m).eq⟩
  apply orderOf_eq_prime
  · rw [← pow_mul, mul_comm, pow_mul]
    have h := congrArg Subtype.val (pow_card_eq_one' (G := ↥Q) (x := ⟨c ^ 5, hc5⟩))
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h
    exact h
  · intro h1
    apply hcQ
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hQ2)
    rw [hm, hk] at h1
    have hg : Nat.gcd 5 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    have hbez := Nat.gcd_eq_gcd_ab 5 (2 ^ k)
    rw [hg] at hbez
    have h2 : c = (c ^ (5 : ℤ)) ^ (Nat.gcdA 5 (2 ^ k)) *
        (c ^ ((2 ^ k : ℕ) : ℤ)) ^ (Nat.gcdB 5 (2 ^ k)) := by
      rw [← zpow_mul, ← zpow_mul, ← zpow_add]
      push_cast at hbez ⊢
      rw [← hbez, zpow_one]
    rw [h2, zpow_natCast, h1, one_zpow, mul_one]
    exact Q.zpow_mem (by exact_mod_cast hc5) _

end SL3Four

theorem sl3FourTorusFact_holds : SL3FourTorusFact := by
  intro G _ _ X S L K d hX _ hLX hKX _ _ _ _ hA5 _ _ hdX hd3 hdL hdK hLd
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e, heL, he5, hed⟩ := SL3Four.exists_orderOf_five_commute hd3 hdL hLd hA5
  obtain ⟨F, _, _, hF, ⟨ψ⟩⟩ := hX
  set Θ : O2Q X ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    ψ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm with hΘ
  set π : ↥X →* O2Q X := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  set d' : ↥X := ⟨d, hdX⟩ with hd'
  set e' : ↥X := ⟨e, hLX heL⟩ with he'
  have hd'3 : d' ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hd3]
    exact pow_orderOf_eq_one d
  have he'5 : orderOf e' = 5 := by
    rw [hd', Subgroup.orderOf_mk] at *
    exact he5
  have hg3 : (Θ (π d')) ^ 3 = 1 := by rw [← map_pow, ← map_pow, hd'3, map_one, map_one]
  have hh5 : orderOf (Θ (π e')) = 5 := by
    rw [MulEquiv.orderOf_eq]
    apply orderOf_eq_prime
    · rw [← map_pow, ← he'5, pow_orderOf_eq_one, map_one]
    · intro h1
      have h2 : e' ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff e').mp h1
      exact SL3Four.not_mem_of_orderOf_five
        (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2) he'5 h2
  have hc : Θ (π d') * Θ (π e') = Θ (π e') * Θ (π d') := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext hed.symm
  have hcen := SL3Four.mem_center_of_commute' hF _ _ hg3 hh5 hc
  have hcen' : ∀ y : O2Q X, y * π d' = π d' * y := by
    intro y
    apply Θ.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hcen (Θ y)
  have hKQ : K ⊓ pCoreOf 2 X ≤ pCoreOf 2 K := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ K inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk => ?_)
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X).to_le inf_le_right)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hkn := Subgroup.le_normalizer hk
    have hkX := CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X
      (hKX hk)
    rw [Subgroup.mem_normalizer_iff] at hkn hkX
    simp only [Subgroup.mem_inf]
    rw [hkn y, hkX y]
  rw [Subgroup.commutator_le]
  intro k hk a ha
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  apply hKQ
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    have hdi : d ^ i ∈ Subgroup.normalizer (K : Set G) := Subgroup.zpow_mem _ hdK i
    have h1 : d ^ i * k⁻¹ * (d ^ i)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hdi _).mp
      (K.inv_mem hk)
    have h2 : k * d ^ i * k⁻¹ * (d ^ i)⁻¹ = k * (d ^ i * k⁻¹ * (d ^ i)⁻¹) := by group
    rw [h2]
    exact K.mul_mem hk h1
  · set k' : ↥X := ⟨k, hKX hk⟩ with hk'
    have h1 : π (k' * d' ^ i * k'⁻¹ * (d' ^ i)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_zpow]
      have h2 : π k' * π d' ^ i = π d' ^ i * π k' :=
        (Commute.zpow_right (show Commute (π k') (π d') from hcen' (π k')) i).eq
      rw [h2]
      group
    have h3 : k' * d' ^ i * k'⁻¹ * (d' ^ i)⁻¹ ∈ CFSG.pCore 2 ↥X :=
      (QuotientGroup.eq_one_iff _).mp h1
    have h4 := (SL3Four.mem_pCoreOf_iff (k' * d' ^ i * k'⁻¹ * (d' ^ i)⁻¹)).mpr h3
    simpa [commutatorElement_def, hk', hd'] using h4

end CFSG.Quasithin.H13.Ch9
