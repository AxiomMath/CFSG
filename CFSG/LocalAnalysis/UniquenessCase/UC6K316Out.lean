module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Shape
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316L34
public import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
public import CFSG.RankThree.PartTwo.KFacts.KS18OuterCore
public import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.RankThree.PartTwo.KFacts.KS18Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
open CFSG.ASVolI.ChIJK (IsGraphFieldAut F4 graphFieldPSL3)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL proj scalars)
open scoped MatrixGroups

section Model

theorem orderOf_dvd_of_fixed_graphField {c : projectiveSL 3 F4}
    (hcc : MulAut.conj c * L34.betaAut (frobeniusEquiv F4 2) *
      (MulAut.conj c * L34.betaAut (frobeniusEquiv F4 2)) = 1)
    {y : projectiveSL 3 F4} (hy : (MulAut.conj c * L34.betaAut (frobeniusEquiv F4 2)) y = y) :
    orderOf y ∣ 72 := by
  have hk : Nat.card F4 = 4 := L34.card_galoisField_two_two
  have hσ : ∀ a : F4, frobeniusEquiv F4 2 a = a ^ 2 := fun a => frobeniusEquiv_apply F4 2 a
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 F4 c
  rw [← LinearFlag.conjAut_toGL] at hcc hy
  set A := Matrix.SpecialLinearGroup.toGL g with hA
  have hα : (LinearFlag.conjAut 3 F4 A * LinearFlag.fieldAut 3 F4 (frobeniusEquiv F4 2) *
      LinearFlag.dualAut 3 F4) ^ 2 = 1 := by
    rw [sq, mul_assoc (LinearFlag.conjAut 3 F4 A)]
    exact hcc
  obtain ⟨-, -, H, hH⟩ := LinearFlag.odd_linear_graph_field_involution_conjugacy Nat.prime_two (f := 2)
    (by norm_num) (by rw [hk]; norm_num) le_rfl A _ (LinearThreeFourOuter.sigma_ne_one hσ hk) hα
  have hH' : LinearFlag.conjAut 3 F4 A * L34.betaAut (frobeniusEquiv F4 2) =
      LinearFlag.conjAut 3 F4 H * L34.betaAut (frobeniusEquiv F4 2) * (LinearFlag.conjAut 3 F4 H)⁻¹ := by
    rw [← hH, mul_assoc]
  have hcard : Nat.card (GL3TwoFixedModel.autFixed
      (LinearFlag.conjAut 3 F4 A * L34.betaAut (frobeniusEquiv F4 2))) = 72 := by
    rw [hH', L34.card_autFixed_conj, L34.card_autFixed_betaAut hk hσ]
  have hmem : y ∈ GL3TwoFixedModel.autFixed (LinearFlag.conjAut 3 F4 A * L34.betaAut (frobeniusEquiv F4 2)) :=
    GL3TwoFixedModel.mem_autFixed.2 hy
  rw [← hcard, ← Subgroup.orderOf_mk y hmem]
  exact _root_.orderOf_dvd_natCard _

theorem exists_fixed_of_commute {x w : GL (Fin 3) F4} {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3)
    (hw : w ∈ StatedSL 3 F4) (hwx : x * w = w * x) (hwr : orderOf w = r) :
    ∃ y : projectiveSL 3 F4, LinearFlag.conjAut 3 F4 x y = y ∧ orderOf y = r := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hk : Nat.card F4 = 4 := L34.card_galoisField_two_two
  have hdet : (w : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
    rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker] at hw
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hw, Units.val_one]
  set w' : SL(3, F4) := ⟨w, hdet⟩ with hw'
  have hw'w : Matrix.SpecialLinearGroup.toGL w' = w := Units.ext rfl
  refine ⟨proj 3 F4 w', ?_, ?_⟩
  · rw [LinearFlag.conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [LinearFlag.coe_slConjugation]
    have h1 : x * w * x⁻¹ = w := by rw [hwx, mul_inv_cancel_right]
    have h2 := congrArg Units.val h1
    rw [Units.val_mul, Units.val_mul] at h2
    exact h2
  · have hord' : orderOf w' = r := by
      rw [← hwr, ← hw'w]
      exact (orderOf_injective _ Matrix.SpecialLinearGroup.toGL_injective w').symm
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hord', pow_orderOf_eq_one, map_one]
    · intro h1
      have hmem : w' ∈ scalars 3 F4 := by
        rw [← LinearFlag.ker_proj]
        exact h1
      have hS : Nat.card (scalars 3 F4) ∣ 3 := by
        have := LinearFlag.card_scalars_dvd (K := F4) (n := 3) (by norm_num)
        rwa [hk] at this
      have h3 : w' ^ 3 = 1 := by
        have h2 : (⟨w', hmem⟩ : scalars 3 F4) ^ 3 = 1 :=
          orderOf_dvd_iff_pow_eq_one.1 ((_root_.orderOf_dvd_natCard _).trans hS)
        have := congrArg Subtype.val h2
        simpa using this
      have hdvd : orderOf w' ∣ 3 := orderOf_dvd_of_pow_eq_one h3
      rw [hord'] at hdvd
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact hr.one_lt.ne' h
      · exact hr3 h

theorem exists_fixed_of_pow_three {ε : MulAut (projectiveSL 3 F4)} (hε : ε * ε * ε = 1)
    (hout : ∀ g : projectiveSL 3 F4, ε ≠ MulAut.conj g) :
    ∃ y : projectiveSL 3 F4, ε y = y ∧ (orderOf y = 5 ∨ orderOf y = 7) := by
  classical
  have hk : Nat.card F4 = 4 := L34.card_galoisField_two_two
  have hσ : ∀ a : F4, frobeniusEquiv F4 2 a = a ^ 2 := fun a => frobeniusEquiv_apply F4 2 a
  have hD : ε ∈ LinearFlag.linearAutGroup 3 F4 := by
    by_contra hD
    obtain ⟨σ', hσ'3, -⟩ := linear_order_three_field_descent le_rfl ε (by rw [pow_three']; exact hε) hD
    rcases LinearThreeFourOuter.ringEquiv_eq_one_or hσ hk σ' with h1 | h1
    · rw [h1, orderOf_one] at hσ'3
      norm_num at hσ'3
    · have h2 : σ' ^ 2 = 1 := by
        rw [h1, sq]
        exact LinearThreeFourOuter.sigma_mul_self hσ hk
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hσ'3] at h3
      norm_num at h3
  have hrange : LinearFlag.linearAutGroup 3 F4 = (LinearFlag.conjAut 3 F4).range := by
    rw [LinearFlag.linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
  rw [hrange] at hD
  obtain ⟨x, rfl⟩ := hD
  have hdet : Matrix.GeneralLinearGroup.det x ≠ 1 := fun h1 => by
    obtain ⟨g, hg⟩ := (LinearThreeFourOuter.conjAut_mem_range_conj_iff hk x).2 h1
    exact hout g hg.symm
  obtain ⟨u, hu⟩ := L34.exists_units_ne_one hk
  have hω3 : (u : F4) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, LinearThreeFourOuter.units_pow_three hk, Units.val_one]
  have hω1 : (u : F4) ≠ 1 := fun h => hu (Units.ext h)
  have hK : Sec4.PiField true 2 2 F4 := ⟨Nat.prime_two, by norm_num, by rw [hk]; rfl⟩
  have hq : Sec4.ModThree true (2 ^ 2) := by
    change 2 ^ 2 % 3 = 1
    norm_num
  have hZ : Sec4.zPi true 3 (2 ^ 2) F4 = Sec4.glPi true 3 (2 ^ 2) F4 ⊓ StatedScalars (Fin 3) F4 :=
    Sec4.zPi_eq (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hω3 hω1
  have hxH : x ∈ Sec4.glPi true 3 (2 ^ 2) F4 := Subgroup.mem_top x
  have hxZ : x ∉ Sec4.zPi true 3 (2 ^ 2) F4 := by
    rw [hZ]
    intro hx
    obtain ⟨c, hc⟩ := (Subgroup.mem_inf.1 hx).2
    apply hout 1
    rw [map_one, ← hc, LinearFlag.conjAut_scalar]
  have hx3 : x ^ 3 ∈ Sec4.zPi true 3 (2 ^ 2) F4 := by
    rw [hZ]
    have h1 : LinearFlag.conjAut 3 F4 (x ^ 3) * LinearFlag.fieldAut 3 F4 1 = 1 := by
      rw [map_one, mul_one, map_pow, pow_three']
      exact hε
    obtain ⟨-, c, hc⟩ := LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl _ _ h1
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, MonoidHom.mem_range.2 ⟨c, hc⟩⟩
  obtain ⟨y, ⟨z, hz, rfl⟩, hcases⟩ := Sec4.rank3II_4_10_one hK hq hω3 hω1 hxH hxZ hx3
  rw [hZ] at hz
  obtain ⟨c, hc⟩ := (Subgroup.mem_inf.1 hz).2
  have hzc : ∀ w : GL (Fin 3) F4, z * w = w * z := fun w => by
    rw [← hc]
    exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c w).symm.eq
  have hdetz : Matrix.GeneralLinearGroup.det z = 1 := by
    rw [← hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, LinearThreeFourOuter.units_pow_three hk]
  have hcomm : ∀ w : GL (Fin 3) F4, w * (x * z) = x * z * w → x * w = w * x := by
    intro w hw
    have h1 : w * x * z = x * w * z := by
      calc w * x * z = w * (x * z) := by rw [mul_assoc]
        _ = x * z * w := hw
        _ = x * (z * w) := by rw [mul_assoc]
        _ = x * (w * z) := by rw [hzc w]
        _ = x * w * z := by rw [mul_assoc]
    exact (mul_right_cancel h1).symm
  have key : ∀ r : ℕ, r.Prime → r ≠ 3 →
      r ∣ Nat.card ↥(Sec4.slPi true 3 (2 ^ 2) F4 ⊓ Subgroup.centralizer {x * z}) →
      ∃ y : projectiveSL 3 F4, LinearFlag.conjAut 3 F4 x y = y ∧ orderOf y = r := by
    intro r hr hr3 hrC
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' r hrC
    have hmem := Subgroup.mem_inf.1 w.2
    exact exists_fixed_of_commute hr hr3 hmem.1
      (hcomm _ (Subgroup.mem_centralizer_singleton_iff.1 hmem.2)) (by rw [Subgroup.orderOf_coe, hw])
  rcases hcases with ⟨⟨g, -, hg⟩, -, -⟩ | ⟨-, ⟨eC⟩, -⟩ | ⟨-, -, -, -, hcard, -⟩
  ·
    exfalso
    apply hdet
    have h1 := congrArg Matrix.GeneralLinearGroup.det hg
    have h2 : Matrix.GeneralLinearGroup.det (Sec4.diagTau hω3) = 1 := by
      have := Sec4.diagTau_mem_slPi (p := 2) (f := 2) (fun h => absurd h (by decide))
        (fun h => absurd h (by decide)) (π := true) hω3
      change Sec4.diagTau hω3 ∈ StatedSL 3 F4 at this
      rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker] at this
      exact this
    rw [h2, map_mul, map_mul, map_mul, map_inv, hdetz, mul_one, mul_comm, ← mul_assoc, mul_inv_cancel,
      one_mul] at h1
    exact h1
  ·
    haveI : Fintype F4 := Fintype.ofFinite F4
    obtain ⟨y, hy, hy5⟩ := key 5 (by norm_num) (by norm_num) (by
      rw [Nat.card_congr eC.toEquiv]
      change 5 ∣ Nat.card ↥(⊤ : Subgroup (GL (Fin 2) F4))
      rw [Subgroup.card_top, Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hk]
      decide)
    exact ⟨y, hy, Or.inl hy5⟩
  ·
    obtain ⟨y, hy, hy7⟩ := key 7 (by norm_num) (by norm_num) (by
      rw [hcard]
      decide)
    exact ⟨y, hy, Or.inr hy7⟩

theorem exists_eq_conj_of_projectiveSL {c : projectiveSL 3 F4} {ε : MulAut (projectiveSL 3 F4)}
    (hcc : MulAut.conj c * L34.betaAut (frobeniusEquiv F4 2) *
      (MulAut.conj c * L34.betaAut (frobeniusEquiv F4 2)) = 1)
    (hε : ε * ε * ε = 1)
    (hfix : ∀ y : projectiveSL 3 F4, ε y = y → (orderOf y = 5 ∨ orderOf y = 7) →
      (MulAut.conj c * L34.betaAut (frobeniusEquiv F4 2)) y = y) :
    ∃ g : projectiveSL 3 F4, ε = MulAut.conj g := by
  by_contra hne
  push Not at hne
  obtain ⟨y, hy, hord⟩ := exists_fixed_of_pow_three hε hne
  have hdvd := orderOf_dvd_of_fixed_graphField hcc (hfix y hy hord)
  rcases hord with h | h <;> rw [h] at hdvd <;> norm_num at hdvd

end Model

section Cover

theorem exists_eq_conj_of_isGraphFieldAut {K : Type} [Group K] [Finite K] (hKp : commutator K = ⊤)
    (hZ3 : Nat.card (Subgroup.center K) ∣ 3) {τ ε : MulAut K} (hgf : IsGraphFieldAut τ) (hττ : τ * τ = 1)
    (hε : ε * ε * ε = 1) (hfix : ∀ k : K, ε k = k → τ k = k) : ∃ g : K, ∀ x : K, ε x = g * x * g⁻¹ := by
  classical
  obtain ⟨e, c, he⟩ := hgf
  set Z := Subgroup.center K with hZdef
  set ψ : K ⧸ Z ≃* projectiveSL 3 F4 := e.trans pslEquiv with hψ
  set τb := centerDescend K τ with hτb
  set εb := centerDescend K ε with hεb
  set τ' := MulAut.congr ψ τb with hτ'
  set ε' := MulAut.congr ψ εb with hε'
  have hcong : ∀ (f : MulAut (K ⧸ Z)) (q : K ⧸ Z), MulAut.congr ψ f (ψ q) = ψ (f q) := fun f q => by
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hz3 : ∀ z ∈ Z, z ^ 3 = 1 := by
    intro z hz
    have h2 : (⟨z, hz⟩ : Z) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 ((_root_.orderOf_dvd_natCard _).trans hZ3)
    have := congrArg Subtype.val h2
    simpa using this
  have hτ'eq : τ' = MulAut.conj (pslEquiv c) * L34.betaAut (frobeniusEquiv F4 2) := by
    ext y
    obtain ⟨q, rfl⟩ := ψ.surjective y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hτ', hcong, hτb, centerDescend_mk, MulAut.mul_apply, MulAut.conj_apply, hψ, MulEquiv.trans_apply,
      MulEquiv.trans_apply, he k, map_mul, map_mul, map_inv, pslEquiv_graphField]
  have hτ'2 : τ' * τ' = 1 := by
    rw [hτ', ← map_mul, hτb, ← map_mul, hττ, map_one, map_one]
  have hε'3 : ε' * ε' * ε' = 1 := by
    rw [hε', ← map_mul, ← map_mul, hεb, ← map_mul, ← map_mul, hε, map_one, map_one]
  have hlift : ∀ y : projectiveSL 3 F4, ε' y = y → (orderOf y = 5 ∨ orderOf y = 7) → τ' y = y := by
    intro y hy hord
    obtain ⟨q, rfl⟩ := ψ.surjective y
    obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective q
    have hy' : εb (k₀ : K ⧸ Z) = k₀ := by
      rw [hε', hcong] at hy
      exact ψ.injective hy
    have hordq : orderOf (k₀ : K ⧸ Z) = orderOf (ψ k₀) :=
      (orderOf_injective ψ.toMonoidHom ψ.injective _).symm
    obtain ⟨r, m, hr, hr3, hrm, hord'⟩ : ∃ r m : ℕ, r.Prime ∧ r ≠ 3 ∧ (3 * m) % r = 1 ∧
        orderOf (k₀ : K ⧸ Z) = r := by
      rcases hord with h | h
      · exact ⟨5, 2, by norm_num, by norm_num, by norm_num, hordq.trans h⟩
      · exact ⟨7, 5, by norm_num, by norm_num, by norm_num, hordq.trans h⟩
    set k := k₀ ^ (3 * m) with hk
    have hkq : (k : K ⧸ Z) = k₀ := by
      rw [hk, QuotientGroup.mk_pow, ← pow_mod_orderOf, hord', hrm, pow_one]
    have hkr : k ^ r = 1 := by
      have h1 : (k₀ : K ⧸ Z) ^ r = 1 := by rw [← hord']; exact pow_orderOf_eq_one _
      have h2 : k₀ ^ r ∈ Z := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
        exact h1
      rw [hk, ← pow_mul, show 3 * m * r = r * 3 * m by ring, pow_mul, pow_mul, hz3 _ h2, one_pow]
    have hεk : ε k = k := by
      have h1 : ((ε k : K) : K ⧸ Z) = (k : K ⧸ Z) := by
        rw [← centerDescend_mk, ← hεb, hkq, hy']
      rw [QuotientGroup.eq] at h1
      set z := (ε k)⁻¹ * k with hz
      have hkz : k = ε k * z := by rw [hz, mul_inv_cancel_left]
      have hzr : z ^ r = 1 := by
        have hεkr : (ε k) ^ r = 1 := by rw [← map_pow, hkr, map_one]
        have hcomm : Commute (ε k) z := Subgroup.mem_center_iff.1 h1 (ε k)
        have h3 := congrArg (· ^ r) hkz
        rw [hcomm.mul_pow, hεkr, one_mul, hkr] at h3
        exact h3.symm
      have hz1 : z = 1 := by
        have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzr) (orderOf_dvd_of_pow_eq_one (hz3 z h1))
        rw [Nat.Coprime.gcd_eq_one ((Nat.coprime_primes hr Nat.prime_three).2 hr3)] at hd
        exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
      rw [hz1, mul_one] at hkz
      exact hkz.symm
    rw [hτ', hcong, ← hkq, hτb, centerDescend_mk, hfix k hεk]
  obtain ⟨g', hg'⟩ := exists_eq_conj_of_projectiveSL (c := pslEquiv c) (by rw [← hτ'eq]; exact hτ'2) hε'3
    (fun y hy hord => by rw [← hτ'eq]; exact hlift y hy hord)
  obtain ⟨q, hq⟩ := ψ.surjective g'
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, ?_⟩
  have hbar : ∀ l : K, ((ε l : K) : K ⧸ Z) = ((g * l * g⁻¹ : K) : K ⧸ Z) := by
    intro l
    have h1 := congrArg (fun α : MulAut (projectiveSL 3 F4) => α (ψ (l : K ⧸ Z))) hg'
    rw [hε', hcong, MulAut.conj_apply, ← hq, ← map_inv, ← map_mul, ← map_mul] at h1
    have h2 := ψ.injective h1
    rw [hεb, centerDescend_mk] at h2
    rw [h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  let α : MulAut K := ε * (MulAut.conj g)⁻¹
  have hαapp : ∀ l : K, α l = ε (g⁻¹ * l * g) := fun l => by
    change ε ((MulAut.conj g)⁻¹ l) = _
    rw [MulAut.conj_inv_apply]
  have hα : ∀ l : K, α l * l⁻¹ ∈ Subgroup.center K := by
    intro l
    have h1 := hbar (g⁻¹ * l * g)
    rw [show g * (g⁻¹ * l * g) * g⁻¹ = l by group, ← hαapp] at h1
    rw [← div_eq_mul_inv]
    exact QuotientGroup.eq_iff_div_mem.1 h1
  refine fun x => ?_
  have h1 := KS18.eq_of_mul_inv_mem_center hKp α hα (g * x * g⁻¹)
  rw [hαapp, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1
  exact h1

end Cover

theorem l34OuterFree : L34OuterFree := by
  intro K _ _ hK τ ε hgf hττ hε _ hfix
  have hk : Nat.card F4 = 4 := L34.card_galoisField_two_two
  haveI hSL : Group.IsPerfect SL(3, F4) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  rcases hK with hK | hK
  · obtain ⟨eK⟩ := hK
    have h1 : Nat.card (Subgroup.center K) = 1 := by
      rw [Nat.card_congr (Subgroup.centerCongr (eK.trans pslEquiv)).toEquiv,
        LinearThreeFourOuter.center_projectiveSL_three_eq_bot hk, Subgroup.card_bot]
    refine exists_eq_conj_of_isGraphFieldAut ?_ (by rw [h1]; exact one_dvd 3) hgf hττ hε hfix
    exact (Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective).commutator_eq_top
  · obtain ⟨eK⟩ := hK
    have h1 : Nat.card (Subgroup.center K) = 3 := by
      rw [Nat.card_congr (Subgroup.centerCongr eK).toEquiv,
        CFSG.OrderReductions.LinearOrders.card_specialLinear_center F4 3 (by norm_num), hk]
      decide
    refine exists_eq_conj_of_isGraphFieldAut ?_ (by rw [h1]) hgf hττ hε hfix
    exact (Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective).commutator_eq_top

end CFSG.LocalAnalysis.UniquenessCase.UCK
