module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Determinant
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public noncomputable section

namespace CFSG.Quasithin.SteinbergBT

open Module Finset Polynomial Subgroup

variable {k : Type*} [Field k]

theorem mul_self_eq_trace_smul_sub_one_of_det (M : Matrix (Fin 2) (Fin 2) k) (hM : M.det = 1) :
    M * M = M.trace • M - 1 := by
  have h := Matrix.aeval_self_charpoly M
  rw [Matrix.charpoly_fin_two, hM] at h
  simp only [map_add, map_sub, map_mul, aeval_X_pow, aeval_C, aeval_X, map_one,
    Algebra.algebraMap_eq_smul_one] at h
  rw [← sub_eq_zero, ← h, sq, smul_mul_assoc, one_mul]
  abel

theorem geom_sum_eq_zero_of_det_eq_one_fin_two {p : ℕ} (hpk : (p : k) ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) k} (hdet : M.det = 1) (hMp : M ^ p = 1) (hM1 : M ≠ 1) :
    ∑ i ∈ range p, M ^ i = 0 := by
  have hCH : M * M = M.trace • M - 1 := mul_self_eq_trace_smul_sub_one_of_det M hdet
  have hgeom : (∑ i ∈ range p, M ^ i) * (M - 1) = 0 := by rw [geom_sum_mul, hMp, sub_self]
  by_cases ht : M.trace = 2
  · exfalso
    set N := M - 1 with hN
    have hMN : M = 1 + N := by rw [hN]; abel
    have hN2 : N * N = 0 := by
      have h : N * N = M * M - 2 • M + 1 := by
        rw [hN, sub_mul, mul_sub, mul_sub, mul_one, one_mul, mul_one, two_nsmul]
        abel
      rw [h, hCH, ht, two_smul, two_nsmul]
      abel
    have hpow : ∀ n : ℕ, M ^ n = 1 + (n : k) • N := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, ih, hMN]
        have e : (1 + (n : k) • N) * (1 + N) = 1 + ((n : k) + 1) • N + (n : k) • (N * N) := by
          rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, smul_mul_assoc, add_smul,
            one_smul]
          abel
        rw [e, hN2, smul_zero, add_zero]
        push_cast
        rfl
    have h1 := hpow p
    rw [hMp] at h1
    have h2 : (p : k) • N = 0 := by
      have := congrArg (fun X => X - 1) h1
      simpa using this.symm
    have hN0 : N = 0 := (smul_eq_zero.1 h2).resolve_left hpk
    exact hM1 (by rw [hMN, hN0, add_zero])
  · have hdetN : (M - 1).det ≠ 0 := by
      have e : (M - 1).det = 2 - M.trace := by
        have h0 := hdet
        rw [Matrix.det_fin_two] at h0
        rw [Matrix.det_fin_two, Matrix.trace_fin_two]
        simp only [Matrix.sub_apply, Matrix.one_apply_eq,
          Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
          Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero]
        linear_combination h0
      rw [e, sub_ne_zero]
      exact Ne.symm ht
    have hunit : IsUnit (M - 1) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdetN)
    exact hunit.mul_left_eq_zero.1 hgeom

variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem eq_one_of_det_eq_one_of_finrank_eq_one (h : finrank k V = 1) {f : V →ₗ[k] V}
    (hdet : LinearMap.det f = 1) : f = 1 := by
  set b := Module.finBasisOfFinrankEq k V h
  have hM : LinearMap.toMatrix b b f = 1 := by
    have hd := LinearMap.det_toMatrix b f
    rw [hdet, Matrix.det_unique] at hd
    ext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default, hd, Matrix.one_apply_eq]
  apply (LinearMap.toMatrix b b).injective
  rw [hM, LinearMap.toMatrix_one]

theorem geom_sum_eq_zero_of_det_eq_one {p : ℕ} (hpk : (p : k) ≠ 0) (hV : finrank k V ≤ 2)
    {f : V →ₗ[k] V} (hdet : LinearMap.det f = 1) (hfp : f ^ p = 1) (hf1 : f ≠ 1) :
    ∑ i ∈ range p, f ^ i = 0 := by
  rcases (show finrank k V = 0 ∨ finrank k V = 1 ∨ finrank k V = 2 by omega) with h | h | h
  · exfalso
    have : Subsingleton V := Module.finrank_zero_iff.1 h
    exact hf1 (LinearMap.ext fun v => Subsingleton.elim _ _)
  · exact absurd (eq_one_of_det_eq_one_of_finrank_eq_one h hdet) hf1
  · set b := Module.finBasisOfFinrankEq k V h
    set e := LinearMap.toMatrixAlgEquiv b with he
    have hef : e f = LinearMap.toMatrix b b f := by
      ext i j
      rw [he, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
    have hdet' : (e f).det = 1 := by rw [hef, LinearMap.det_toMatrix, hdet]
    have hp' : e f ^ p = 1 := by rw [← map_pow, hfp, map_one]
    have h1' : e f ≠ 1 := fun h' => hf1 (e.injective (h'.trans (map_one e).symm))
    have hsum := geom_sum_eq_zero_of_det_eq_one_fin_two hpk hdet' hp' h1'
    apply e.injective
    rw [map_sum, map_zero]
    simpa only [map_pow] using hsum

theorem natCast_eq_zero_of_geom_sums {R : Type*} [Ring R] {p : ℕ} {a b : R} (hab : Commute a b)
    (h1 : ∀ j < p, ∑ i ∈ range p, (a * b ^ j) ^ i = 0)
    (h2 : ∀ i < p, i ≠ 0 → ∑ j ∈ range p, (b ^ i) ^ j = 0) : (p : R) = 0 := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · rw [hp0, Nat.cast_zero]
  calc (p : R) = ∑ i ∈ range p, a ^ i * ∑ j ∈ range p, (b ^ i) ^ j := by
        rw [Finset.sum_eq_single 0]
        · simp
        · intro i hi hi0
          rw [h2 i (mem_range.1 hi) hi0, mul_zero]
        · intro h
          exact absurd (mem_range.2 hp0) h
    _ = ∑ i ∈ range p, ∑ j ∈ range p, (a * b ^ j) ^ i := by
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        rw [(hab.pow_right j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i j]
    _ = ∑ j ∈ range p, ∑ i ∈ range p, (a * b ^ j) ^ i := sum_comm
    _ = 0 := sum_eq_zero fun j hj => h1 j (mem_range.1 hj)

theorem coprime_two_space_exponent_prime_determinant_bound {p : ℕ} (hp : p.Prime)
    (hk : ringChar k ≠ p) (hV : finrank k V ≤ 2)
    (A : Subgroup (LinearMap.GeneralLinearGroup k V)) [Finite A] (hA : IsPGroup p A)
    (hexp : ∀ a ∈ A, a ^ p = 1) :
    Nat.card ↥(A ⊓ (Units.map (LinearMap.det : (V →ₗ[k] V) →* k)).ker) ≤ p ∧
    Nat.card ↥(A.map (Units.map (LinearMap.det : (V →ₗ[k] V) →* k))) ≤ p ∧
    Nat.card A ≤ p ^ 2 ∧ CFSG.IsElementaryAbelian p A ∧
    (Nat.card A = p ^ 2 → finrank k V = 2 ∧
      Nat.card ↥(A ⊓ (Units.map (LinearMap.det : (V →ₗ[k] V) →* k)).ker) = p ∧
      Nat.card ↥(A.map (Units.map (LinearMap.det : (V →ₗ[k] V) →* k))) = p ∧
      ∀ g ∈ Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)),
        ∀ x ∈ A ⊓ (Units.map (LinearMap.det : (V →ₗ[k] V) →* k)).ker,
          g * x * g⁻¹ ∈ A ⊓ (Units.map (LinearMap.det : (V →ₗ[k] V) →* k)).ker) ∧
    (finrank k V = 0 → ∀ g : LinearMap.GeneralLinearGroup k V,
      Units.map (LinearMap.det : (V →ₗ[k] V) →* k) g = 1) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set det : LinearMap.GeneralLinearGroup k V →* kˣ :=
    Units.map (LinearMap.det : (V →ₗ[k] V) →* k) with hdetdef
  have hdet_apply : ∀ g, ((det g : kˣ) : k) = LinearMap.det (g : V →ₗ[k] V) := fun g => rfl
  have hpk : (p : k) ≠ 0 := by
    intro h
    rcases (Nat.dvd_prime hp).1 ((ringChar.spec k p).1 h) with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · exact hk h1
  set S := A ⊓ det.ker with hSdef
  have hSA : S ≤ A := inf_le_left
  have : Finite S := Finite.of_injective (Subgroup.inclusion hSA) (Subgroup.inclusion_injective _)
  have hSp : IsPGroup p S := hA.to_le hSA
  have hgeom : ∀ a ∈ S, a ≠ 1 → ∑ i ∈ range p, (a : V →ₗ[k] V) ^ i = 0 := by
    intro a ha ha1
    refine geom_sum_eq_zero_of_det_eq_one hpk hV ?_ ?_ ?_
    · have h := congrArg Units.val (MonoidHom.mem_ker.1 ha.2)
      rwa [hdet_apply, Units.val_one] at h
    · rw [← Units.val_pow_eq_pow_val, hexp a ha.1, Units.val_one]
    · exact fun h => ha1 (Units.ext h)
  have hS : Nat.card S ≤ p := by
    by_cases hS1 : S = ⊥
    · rw [hS1, card_bot]
      exact hp.one_lt.le
    have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hS1
    have := hSp.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center S)
    set a : LinearMap.GeneralLinearGroup k V := ((z : S) : LinearMap.GeneralLinearGroup k V)
      with ha
    have haS : a ∈ S := (z : S).2
    have ha1 : a ≠ 1 := fun h => hz (Subtype.ext (Subtype.ext h))
    have hacomm : ∀ b ∈ S, a * b = b * a := fun b hb =>
      congrArg Subtype.val ((Subgroup.mem_center_iff.1 z.2 ⟨b, hb⟩).symm)
    have haord : orderOf a = p := orderOf_eq_prime (hexp a haS.1) ha1
    have hSz : ∀ b ∈ S, b ∈ Subgroup.zpowers a := by
      intro b hb
      by_contra hbz
      have hb1 : b ≠ 1 := fun h => hbz (h ▸ one_mem _)
      have hbord : orderOf b = p := orderOf_eq_prime (hexp b hb.1) hb1
      have hcomm' : Commute (a : V →ₗ[k] V) (b : V →ₗ[k] V) := by
        change (a : V →ₗ[k] V) * b = b * a
        rw [← Units.val_mul, ← Units.val_mul, hacomm b hb]
      have h0 := natCast_eq_zero_of_geom_sums hcomm' (p := p)
        (fun j _ => by
          have hmem : a * b ^ j ∈ S := mul_mem haS (pow_mem hb j)
          have hne : a * b ^ j ≠ 1 := by
            intro h
            have h' : a = (b ^ j)⁻¹ := eq_inv_of_mul_eq_one_left h
            apply hbz
            have haz : a ∈ Subgroup.zpowers b := h' ▸ inv_mem (pow_mem (mem_zpowers b) j)
            have hle : Subgroup.zpowers a ≤ Subgroup.zpowers b := zpowers_le.2 haz
            have : Finite (Subgroup.zpowers b) :=
              Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hbord]; exact hp.ne_zero)
            have heq : Subgroup.zpowers a = Subgroup.zpowers b := by
              refine eq_of_le_of_card_ge hle ?_
              rw [Nat.card_zpowers, Nat.card_zpowers, haord, hbord]
            rw [heq]
            exact mem_zpowers b
          have h := hgeom _ hmem hne
          simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using h)
        (fun i hi hi0 => by
          have hmem : b ^ i ∈ S := pow_mem hb i
          have hne : b ^ i ≠ 1 := pow_ne_one_of_lt_orderOf hi0 (hbord ▸ hi)
          have h := hgeom _ hmem hne
          simpa only [Units.val_pow_eq_pow_val] using h)
      have hV0 : Nontrivial V := by
        by_contra hV0
        rw [not_nontrivial_iff_subsingleton] at hV0
        exact ha1 (Units.ext (LinearMap.ext fun v => Subsingleton.elim _ _))
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have h1 := congrArg (fun F : V →ₗ[k] V => F v) h0
      simp only [Module.End.natCast_apply, LinearMap.zero_apply] at h1
      rw [← Nat.cast_smul_eq_nsmul k] at h1
      exact hv ((smul_eq_zero.1 h1).resolve_left hpk)
    have : Finite (Subgroup.zpowers a) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, haord]; exact hp.ne_zero)
    calc Nat.card S ≤ Nat.card (Subgroup.zpowers a) := by
          refine Nat.card_le_card_of_injective (fun b : S => (⟨b, hSz b b.2⟩ : Subgroup.zpowers a))
            fun b b' hbb' => ?_
          have h := congrArg Subtype.val hbb'
          exact Subtype.ext h
      _ = p := by rw [Nat.card_zpowers, haord]
  have hD : Nat.card (A.map det) ≤ p := by
    have : NeZero p := ⟨hp.ne_zero⟩
    have hle : A.map det ≤ rootsOfUnity p k := by
      rintro _ ⟨a, ha, rfl⟩
      rw [mem_rootsOfUnity, ← map_pow, hexp a ha, map_one]
    exact (card_le_of_le hle).trans (card_rootsOfUnity k p)
  have hcardA : Nat.card A = Nat.card S * Nat.card (A.map det) := by
    set f : A →* kˣ := det.comp A.subtype with hf
    have hfr : f.range = A.map det := by rw [hf, MonoidHom.range_comp, range_subtype]
    have hfk : Nat.card f.ker = Nat.card S := Nat.card_congr
      { toFun := fun x => ⟨x.1, x.1.2, MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 x.2)⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 y.2.2)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    rw [← card_mul_index f.ker, index_ker, hfr, hfk]
  have hA2 : Nat.card A ≤ p ^ 2 := by
    rw [hcardA, sq]
    exact Nat.mul_le_mul hS hD
  have hAcomm : IsMulCommutative A := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hA
    have hn2 : n ≤ 2 := by
      rw [hn] at hA2
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hA2
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl
    · have : Subsingleton A := (Nat.card_eq_one_iff_unique.1 (by rw [hn, pow_zero])).1
      exact ⟨⟨fun x y => Subsingleton.elim _ _⟩⟩
    · have : IsCyclic A := isCyclic_of_prime_card (by rw [hn, pow_one])
      exact IsCyclic.isMulCommutative
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hn
  have hAe : CFSG.IsElementaryAbelian p A :=
    { toIsMulCommutative := hAcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext (by
        rw [Subgroup.coe_pow, hexp a a.2, Subgroup.coe_one]) }
  refine ⟨hS, hD, hA2, hAe, fun hA2' => ?_, fun h0 g => ?_⟩
  ·
    have hp0 : 0 < p := hp.pos
    have hmul : Nat.card S * Nat.card (A.map det) = p * p := by rw [← hcardA, hA2', sq]
    have hSeq : Nat.card S = p := by
      refine le_antisymm hS ?_
      by_contra hlt
      push Not at hlt
      have : Nat.card S * Nat.card (A.map det) < p * p :=
        calc Nat.card S * Nat.card (A.map det) ≤ Nat.card S * p := Nat.mul_le_mul_left _ hD
          _ < p * p := Nat.mul_lt_mul_of_pos_right hlt hp0
      omega
    have hDeq : Nat.card (A.map det) = p := by
      rw [hSeq] at hmul
      exact Nat.eq_of_mul_eq_mul_left hp0 hmul
    refine ⟨?_, hSeq, hDeq, fun g hg x hx => ?_⟩
    ·
      rcases (show finrank k V = 0 ∨ finrank k V = 1 ∨ finrank k V = 2 by omega) with h | h | h
      · exfalso
        have : Subsingleton V := Module.finrank_zero_iff.1 h
        have hsub : Subsingleton S := ⟨fun x y => Subtype.ext (Units.ext
          (LinearMap.ext fun v => Subsingleton.elim _ _))⟩
        have := Finite.card_le_one_iff_subsingleton.2 hsub
        have := hp.two_le
        omega
      · exfalso
        have hsub : Subsingleton S := ⟨fun x y => by
          have hx := eq_one_of_det_eq_one_of_finrank_eq_one h
            (f := ((x : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V)) (by
            have := congrArg Units.val (MonoidHom.mem_ker.1 x.2.2)
            rwa [hdet_apply, Units.val_one] at this)
          have hy := eq_one_of_det_eq_one_of_finrank_eq_one h
            (f := ((y : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V)) (by
            have := congrArg Units.val (MonoidHom.mem_ker.1 y.2.2)
            rwa [hdet_apply, Units.val_one] at this)
          exact Subtype.ext (Units.ext (hx.trans hy.symm))⟩
        have := Finite.card_le_one_iff_subsingleton.2 hsub
        have := hp.two_le
        omega
      · exact h
    · refine ⟨(mem_normalizer_iff.1 hg x).1 hx.1, MonoidHom.mem_ker.2 ?_⟩
      rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.1 hx.2, mul_one, mul_inv_cancel]
  · exact Units.ext (by rw [hdet_apply, LinearMap.det_eq_one_of_finrank_eq_zero h0, Units.val_one])

end CFSG.Quasithin.SteinbergBT
