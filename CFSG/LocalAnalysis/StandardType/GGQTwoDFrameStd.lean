module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEven

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def dSgn (ε : Bool) : ZMod 3 := if ε then -1 else 1

@[expose] noncomputable def dRootAB (m : ℕ) (ε : Bool) (a b : Fin m) : DVec m :=
  dBasis m a - dSgn ε • dBasis m b

@[expose] noncomputable def dFormAB (m : ℕ) (ε : Bool) (a b : Fin m) :
    Module.Dual (ZMod 3) (DVec m) :=
  LinearMap.proj a - dSgn ε • LinearMap.proj b

@[expose] noncomputable def dRoot (m : ℕ) (t : Fin m) : DVec m :=
  dRootAB m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)

@[expose] noncomputable def dRootForm (m : ℕ) (t : Fin m) : Module.Dual (ZMod 3) (DVec m) :=
  dFormAB m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)

private lemma plq_dSgn_false : dSgn false = (1 : ZMod 3) := by decide

private lemma plq_dSgn_true : dSgn true = (-1 : ZMod 3) := by decide

private lemma plq_dSgn_mul_self (ε : Bool) : dSgn ε * dSgn ε = 1 := by cases ε <;> decide

private lemma plq_dRootAB_apply (m : ℕ) (ε : Bool) (a b i : Fin m) :
    dRootAB m ε a b i = (if i = a then 1 else 0) - dSgn ε * (if i = b then 1 else 0) := by
  simp only [dRootAB, dBasis, Pi.basisFun_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul]

private lemma plq_dFormAB_dRootAB (m : ℕ) (ε ε' : Bool) (a b c d : Fin m) :
    dFormAB m ε a b (dRootAB m ε' c d) =
      (if a = c then 1 else 0) - dSgn ε' * (if a = d then 1 else 0)
        - dSgn ε * ((if b = c then 1 else 0) - dSgn ε' * (if b = d then 1 else 0)) := by
  simp only [dFormAB, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul, plq_dRootAB_apply]

private def plq_dval (m : ℕ) (t j : Fin m) : ZMod 3 :=
  if t = j then 2
  else if t.val + 1 = j.val ∧ j.val + 2 < m then -1
  else if j.val + 1 = t.val ∧ t.val + 2 < m then -1
  else if t.val + 3 = m ∧ (j.val + 2 = m ∨ j.val + 1 = m) then -1
  else if j.val + 3 = m ∧ (t.val + 2 = m ∨ t.val + 1 = m) then -1
  else 0

private lemma plq_dval_eq_cartan (m : ℕ) (hm : 4 ≤ m) (t j : Fin m) :
    plq_dval m t j = ((CartanMatrix.D m t j : ℤ) : ZMod 3) := by
  rw [plq_dval, CartanMatrix.D, Matrix.of_apply]
  push_cast
  by_cases hij : t = j
  · simp [hij]
  · rw [if_neg hij, if_neg (show ¬ (m ≤ 2) by omega)]
    split_ifs <;> norm_num

theorem dFormAB_apply (m : ℕ) (ε : Bool) (a b : Fin m) (v : DVec m) :
    dFormAB m ε a b v = v a - dSgn ε * v b := by
  simp [dFormAB, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

theorem dFormAB_dRootAB (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) :
    dFormAB m ε a b (dRootAB m ε a b) = 2 := by
  rw [dFormAB_apply]
  have h1 : dRootAB m ε a b a = 1 := by
    rw [plq_dRootAB_apply]; simp [hab]
  have h2 : dRootAB m ε a b b = -dSgn ε := by
    rw [plq_dRootAB_apply]; simp [hab.symm]
  rw [h1, h2]
  have hs : dSgn ε * dSgn ε = 1 := plq_dSgn_mul_self ε
  calc
    1 - dSgn ε * (-dSgn ε) = 1 + dSgn ε * dSgn ε := by ring
    _ = 1 + 1 := by rw [hs]
    _ = 2 := by decide

theorem dRootAB_ne_zero (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) :
    dRootAB m ε a b ≠ 0 := by
  intro h
  have h1 : dRootAB m ε a b a = 1 := by
    rw [plq_dRootAB_apply]; simp [hab]
  have h2 := congrFun h a
  rw [h1, Pi.zero_apply] at h2
  exact one_ne_zero h2

theorem dTau_apply_vec (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) (v : DVec m) :
    dTau m ε a b v = v - dFormAB m ε a b v • dRootAB m ε a b := by
  have hLR : (dTau m ε a b : DVec m →ₗ[ZMod 3] DVec m) =
      Module.preReflection (dRootAB m ε a b) (dFormAB m ε a b) := by
    refine (dBasis m).ext fun i => ?_
    rw [Module.preReflection_apply]
    change dTau m ε a b (dBasis m i) =
      dBasis m i - dFormAB m ε a b (dBasis m i) • dRootAB m ε a b
    by_cases hia : i = a
    · rw [hia]
      rw [dTau_apply_left m ε hab]
      have hfa : dFormAB m ε a b (dBasis m a) = 1 := by
        rw [dFormAB_apply]
        simp [dBasis, Pi.basisFun_apply, Pi.single_apply, hab]
      rw [hfa]
      change dSgn ε • dBasis m b = dBasis m a - 1 • dRootAB m ε a b
      rw [dRootAB]
      simp only [one_smul]
      abel
    · by_cases hib : i = b
      · rw [hib]
        rw [dTau_apply_right m ε hab]
        have hfb : dFormAB m ε a b (dBasis m b) = -dSgn ε := by
          rw [dFormAB_apply]
          simp [dBasis, Pi.basisFun_apply, Pi.single_apply, hab.symm]
        rw [hfb]
        change dSgn ε • dBasis m a = dBasis m b - (-dSgn ε) • dRootAB m ε a b
        rw [dRootAB]
        have hs : dSgn ε * dSgn ε = 1 := plq_dSgn_mul_self ε
        rw [neg_smul, smul_sub, smul_smul, hs, one_smul, neg_sub]
        abel
      · rw [dTau_apply_of_ne m ε hia hib]
        have hfi : dFormAB m ε a b (dBasis m i) = 0 := by
          rw [dFormAB_apply]
          simp [dBasis, Pi.basisFun_apply, Pi.single_apply, hia, hib]
        rw [hfi, zero_smul, sub_zero]
  have h := congrArg (fun L : DVec m →ₗ[ZMod 3] DVec m => L v) hLR
  rwa [Module.preReflection_apply] at h

theorem dTau_apply_eq_self_iff (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) (v : DVec m) :
    dTau m ε a b v = v ↔ v a = dSgn ε * v b := by
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  rw [dTau_apply_vec m ε hab v, sub_eq_self, smul_eq_zero]
  constructor
  · rintro (h | h)
    · rw [dFormAB_apply] at h
      exact sub_eq_zero.mp h
    · exact absurd h (dRootAB_ne_zero m ε hab)
  · intro h
    left
    rw [dFormAB_apply, sub_eq_zero]
    exact h

private lemma plq_dTau_fixes_basis (m : ℕ) (ε : Bool) {a b i : Fin m} (hab : a ≠ b) :
    dTau m ε a b (dBasis m i) = dBasis m i ↔ i ≠ a ∧ i ≠ b := by
  constructor
  · rintro h
    refine ⟨?_, ?_⟩
    · intro hia
      subst hia
      rw [dTau_apply_left m ε hab] at h
      have hb : (if ε then (-1 : ZMod 3) else 1) = 0 := by
        have := congrFun h b
        simpa [dBasis, Pi.basisFun_apply, Pi.single_apply, hab.symm] using this
      cases ε <;> exact absurd hb (by decide)
    · intro hib
      subst hib
      rw [dTau_apply_right m ε hab] at h
      have ha : (if ε then (-1 : ZMod 3) else 1) = 0 := by
        have := congrFun h a
        simpa [dBasis, Pi.basisFun_apply, Pi.single_apply, hab] using this
      cases ε <;> exact absurd ha (by decide)
  · rintro ⟨hia, hib⟩
    exact dTau_apply_of_ne m ε hia hib

theorem dTau_injOn (m : ℕ) {ε ε' : Bool} {a b a' b' : Fin m} (hab : a < b) (hab' : a' < b')
    (h : dTau m ε a b = dTau m ε' a' b') : ε = ε' ∧ a = a' ∧ b = b' := by
  have habne : a ≠ b := hab.ne
  have hab'ne : a' ≠ b' := hab'.ne
  have hiff : ∀ i : Fin m, (i ≠ a ∧ i ≠ b) ↔ (i ≠ a' ∧ i ≠ b') := by
    intro i
    have key : (dTau m ε a b (dBasis m i) = dBasis m i) ↔
        (dTau m ε' a' b' (dBasis m i) = dBasis m i) := iff_of_eq (by rw [h])
    rwa [plq_dTau_fixes_basis m ε habne, plq_dTau_fixes_basis m ε' hab'ne] at key
  have ha : a = a' ∨ a = b' := by
    by_contra hc
    push Not at hc
    exact ((hiff a).mpr ⟨hc.1, hc.2⟩).1 rfl
  have hb : b = a' ∨ b = b' := by
    by_contra hc
    push Not at hc
    exact ((hiff b).mpr ⟨hc.1, hc.2⟩).2 rfl
  have h1 : a.val = a'.val := by
    have ha' := ha.imp (congrArg Fin.val) (congrArg Fin.val)
    have hb' := hb.imp (congrArg Fin.val) (congrArg Fin.val)
    omega
  have h2 : b.val = b'.val := by
    have ha' := ha.imp (congrArg Fin.val) (congrArg Fin.val)
    have hb' := hb.imp (congrArg Fin.val) (congrArg Fin.val)
    omega
  have hae : a = a' := Fin.ext h1
  have hbe : b = b' := Fin.ext h2
  have hε : ε = ε' := by
    have hh : dTau m ε a b (dBasis m a) = dTau m ε' a b (dBasis m a) := by
      have := congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m => T (dBasis m a)) h
      rwa [← hae, ← hbe] at this
    rw [dTau_apply_left m ε habne, dTau_apply_left m ε' habne] at hh
    have hcoeff : (if ε then (-1 : ZMod 3) else 1) =
        (if ε' then (-1 : ZMod 3) else 1) := by
      have := congrFun hh b
      simpa [dBasis, Pi.basisFun_apply, Pi.single_apply] using this
    cases ε <;> cases ε' <;> first | rfl | exact absurd hcoeff (by decide)
  exact ⟨hε, hae, hbe⟩

theorem dTau_simple_apply (m : ℕ) (hm : 4 ≤ m) (t : Fin m) (v : DVec m) :
    dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t) v =
      v - dRootForm m t v • dRoot m t := by
  exact dTau_apply_vec m (decide (t.val + 1 = m))
    (OrthTorus.simpleLo_ne_simpleHi (by omega) t) v

private lemma plq_dRootForm_dRoot_dval (m : ℕ) (hm : 4 ≤ m) (t j : Fin m) :
    dRootForm m t (dRoot m j) = plq_dval m t j := by
  rw [dRootForm, dRoot, plq_dval]
  by_cases hij : t = j
  · subst hij
    rw [dFormAB_dRootAB m (decide (t.val + 1 = m))
      (OrthTorus.simpleLo_ne_simpleHi (by omega) t)]
    simp
  · have hijv : t.val ≠ j.val := fun h => hij (Fin.ext h)
    rw [plq_dFormAB_dRootAB]
    rcases lt_or_eq_of_le (show t.val + 1 ≤ m by omega) with ht | ht
    · rcases lt_or_eq_of_le (show j.val + 1 ≤ m by omega) with hj | hj
      · have hdt : decide (t.val + 1 = m) = false := by
          rw [decide_eq_false_iff_not]; omega
        have hdj : decide (j.val + 1 = m) = false := by
          rw [decide_eq_false_iff_not]; omega
        rw [show OrthTorus.simpleLo t = t from Fin.ext (OrthTorus.simpleLo_of_lt ht),
            show OrthTorus.simpleHi t = ⟨t.val + 1, ht⟩ from
              Fin.ext (OrthTorus.simpleHi_of_lt ht),
            show OrthTorus.simpleLo j = j from Fin.ext (OrthTorus.simpleLo_of_lt hj),
            show OrthTorus.simpleHi j = ⟨j.val + 1, hj⟩ from
              Fin.ext (OrthTorus.simpleHi_of_lt hj),
            hdt, hdj, plq_dSgn_false]
        simp only [Fin.ext_iff, Fin.val_mk, hijv]
        split_ifs <;> (try norm_num) <;> first | omega | contradiction | decide
      · have hdt : decide (t.val + 1 = m) = false := by
          rw [decide_eq_false_iff_not]; omega
        have hdj : decide (j.val + 1 = m) = true := by
          rw [decide_eq_true_eq]; omega
        rw [show OrthTorus.simpleLo t = t from Fin.ext (OrthTorus.simpleLo_of_lt ht),
            show OrthTorus.simpleHi t = ⟨t.val + 1, ht⟩ from
              Fin.ext (OrthTorus.simpleHi_of_lt ht),
            show OrthTorus.simpleLo j = ⟨m - 2, by omega⟩ from
              Fin.ext (OrthTorus.simpleLo_of_last hj),
            show OrthTorus.simpleHi j = ⟨m - 1, by omega⟩ from
              Fin.ext (OrthTorus.simpleHi_of_last hj),
            hdt, hdj, plq_dSgn_false, plq_dSgn_true]
        simp only [Fin.ext_iff, Fin.val_mk]
        split_ifs <;> (try norm_num) <;> first | omega | contradiction | decide
    · rcases lt_or_eq_of_le (show j.val + 1 ≤ m by omega) with hj | hj
      · have hdt : decide (t.val + 1 = m) = true := by
          rw [decide_eq_true_eq]; omega
        have hdj : decide (j.val + 1 = m) = false := by
          rw [decide_eq_false_iff_not]; omega
        rw [show OrthTorus.simpleLo t = ⟨m - 2, by omega⟩ from
              Fin.ext (OrthTorus.simpleLo_of_last ht),
            show OrthTorus.simpleHi t = ⟨m - 1, by omega⟩ from
              Fin.ext (OrthTorus.simpleHi_of_last ht),
            show OrthTorus.simpleLo j = j from Fin.ext (OrthTorus.simpleLo_of_lt hj),
            show OrthTorus.simpleHi j = ⟨j.val + 1, hj⟩ from
              Fin.ext (OrthTorus.simpleHi_of_lt hj),
            hdt, hdj, plq_dSgn_true, plq_dSgn_false]
        simp only [Fin.ext_iff, Fin.val_mk]
        split_ifs <;> (try norm_num) <;> first | omega | contradiction | decide
      · exact absurd (Fin.ext (by omega : t.val = j.val)) hij

theorem dRootForm_dRoot (m : ℕ) (hm : 4 ≤ m) (t j : Fin m) :
    dRootForm m t (dRoot m j) = ((CartanMatrix.D m t j : ℤ) : ZMod 3) := by
  rw [plq_dRootForm_dRoot_dval m hm t j, plq_dval_eq_cartan m hm t j]

theorem dRoot_linearIndependent (m : ℕ) (hm : 4 ≤ m) :
    LinearIndependent (ZMod 3) (dRoot m) := by
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let A : Matrix (Fin m) (Fin m) (ZMod 3) :=
    (CartanMatrix.D m).map (Int.castRingHom (ZMod 3))
  have hA : Matrix.mulVec A g = 0 := by
    funext t
    have h := congrArg (dRootForm m t) hg
    simp only [map_sum, map_smul, map_zero] at h
    rw [Matrix.mulVec_apply_eq_sum]
    calc
      ∑ i, A t i * g i = ∑ i, g i * dRootForm m t (dRoot m i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hA' : A t i = ((CartanMatrix.D m t i : ℤ) : ZMod 3) := by
          simp [A, Matrix.map_apply]
        rw [hA', dRootForm_dRoot m hm t i]
        ring
      _ = 0 := by simpa only [smul_eq_mul] using h
  have hdet : A.det ≠ 0 := by
    have hmap := RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.D m)
    rw [CartanMatrix.D_det (by omega)] at hmap
    have hAeq : A = (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.D m) := rfl
    rw [hAeq, ← hmap]
    have hfour : ((4 : ℤ) : ZMod 3) ≠ 0 := by
      intro h
      exact absurd ((ZMod.intCast_zmod_eq_zero_iff_dvd 4 3).mp h) (by norm_num)
    exact hfour
  have hg0 : g = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hA
  intro i
  rw [hg0]
  rfl

theorem eq_zero_of_dRootForm_eq_zero (m : ℕ) (hm : 4 ≤ m) (v : DVec m)
    (hv : ∀ t, dRootForm m t v = 0) : v = 0 := by
  let w : ℕ → ZMod 3 := fun k => if hk : k < m then v ⟨k, hk⟩ else 0
  have hw : ∀ (k : ℕ) (hk : k < m), w k = v ⟨k, hk⟩ := by
    intro k hk; simp only [w, dif_pos hk]
  have hw_eq : ∀ i : Fin m, v i = w i.val := by
    intro i
    rw [hw i.val i.isLt]
  have hwstep : ∀ (k : ℕ) (hk : k + 1 < m), w k = w (k + 1) := by
    intro k hk
    have hk' : k < m := by omega
    have hlt : (⟨k, hk'⟩ : Fin m).val + 1 < m := by simpa using hk
    have hdec : decide ((⟨k, hk'⟩ : Fin m).val + 1 = m) = false := by
      simp only [Fin.val_mk, decide_eq_false_iff_not]; omega
    have hv' := hv ⟨k, hk'⟩
    rw [dRootForm, dFormAB_apply] at hv'
    rw [hdec] at hv'
    rw [hw_eq (OrthTorus.simpleLo ⟨k, hk'⟩), hw_eq (OrthTorus.simpleHi ⟨k, hk'⟩),
        OrthTorus.simpleLo_of_lt hlt, OrthTorus.simpleHi_of_lt hlt] at hv'
    simp only [plq_dSgn_false, one_mul, Fin.val_mk] at hv'
    exact sub_eq_zero.mp hv'
  have hconst : ∀ k, k < m → w k = w 0 := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
        intro hk
        rw [← hwstep k hk]
        exact ih (by omega)
  have hlast : w (m - 2) + w (m - 1) = 0 := by
    have htlast : (⟨m - 1, by omega⟩ : Fin m).val + 1 = m := by
      simp only [Fin.val_mk]
      omega
    have hdec : decide ((⟨m - 1, by omega⟩ : Fin m).val + 1 = m) = true := by
      simp [htlast]
    have h := hv ⟨m - 1, by omega⟩
    rw [dRootForm, dFormAB_apply] at h
    rw [hdec] at h
    rw [hw_eq (OrthTorus.simpleLo ⟨m - 1, by omega⟩),
        hw_eq (OrthTorus.simpleHi ⟨m - 1, by omega⟩)] at h
    rw [OrthTorus.simpleLo_of_last htlast, OrthTorus.simpleHi_of_last htlast] at h
    simp only [plq_dSgn_true, Fin.val_mk] at h
    ring_nf at h
    exact h
  have hw0 : w 0 = 0 := by
    rw [hconst (m - 2) (by omega), hconst (m - 1) (by omega)] at hlast
    rw [← two_mul] at hlast
    exact (mul_eq_zero.mp hlast).resolve_left (by decide)
  funext i
  rw [hw_eq i, hconst i.val i.isLt]
  exact hw0

theorem dEven_conj_dTau (m : ℕ) {h : DVec m ≃ₗ[ZMod 3] DVec m} (hh : h ∈ dEven m) (ε : Bool)
    {a b : Fin m} (hab : a ≠ b) :
    ∃ (ε' : Bool) (a' b' : Fin m), a' ≠ b' ∧ h * dTau m ε a b * h⁻¹ = dTau m ε' a' b' := by
  obtain ⟨σ, c, hc, _, hact⟩ := hh
  have hσab : σ a ≠ σ b := fun hh => hab (σ.injective hh)
  have hsq : ∀ i, c i * c i = 1 := by
    intro i
    rcases hc i with h | h <;> rw [h] <;> decide
  have hinv : ∀ i, h⁻¹ (dBasis m (σ i)) = c i • dBasis m i := by
    intro i
    have h1 : h (c i • dBasis m i) = dBasis m (σ i) := by
      rw [map_smul, hact i, smul_smul, hsq i, one_smul]
    rw [← h1]
    exact h.symm_apply_apply _
  have hval : c a * c b * dSgn ε = 1 ∨ c a * c b * dSgn ε = -1 := by
    rcases hc a with ha | ha <;> rcases hc b with hb | hb <;> cases ε <;>
      rw [ha, hb] <;> norm_num [dSgn]
  have hact' : ∀ (ε' : Bool), dSgn ε' = c a * c b * dSgn ε →
      h * dTau m ε a b * h⁻¹ = dTau m ε' (σ a) (σ b) := by
    intro ε' hε'
    refine (dBasis m).ext' fun k => ?_
    obtain ⟨i, rfl⟩ := σ.surjective k
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv i]
    by_cases hia : i = a
    · rw [hia]
      rw [dTau_apply_left m ε' hσab,
        show (if ε' then (-1 : ZMod 3) else 1) = dSgn ε' from rfl]
      have hcoeff : c a * (if ε then (-1 : ZMod 3) else 1) * c b = dSgn ε' := by
        rw [hε']
        show c a * (if ε then (-1 : ZMod 3) else 1) * c b =
          c a * c b * (if ε then (-1 : ZMod 3) else 1)
        ring
      calc
        h (dTau m ε a b (c a • dBasis m a))
            = h (c a • dTau m ε a b (dBasis m a)) := by rw [map_smul]
        _ = h (c a • ((if ε then (-1 : ZMod 3) else 1) • dBasis m b)) := by
              rw [dTau_apply_left m ε hab]
        _ = h ((c a * (if ε then (-1 : ZMod 3) else 1)) • dBasis m b) := by
              rw [smul_smul]
        _ = (c a * (if ε then (-1 : ZMod 3) else 1)) • h (dBasis m b) := by
              rw [map_smul]
        _ = (c a * (if ε then (-1 : ZMod 3) else 1)) • (c b • dBasis m (σ b)) := by
              rw [hact b]
        _ = (c a * (if ε then (-1 : ZMod 3) else 1) * c b) • dBasis m (σ b) := by
              rw [smul_smul]
        _ = dSgn ε' • dBasis m (σ b) := by rw [hcoeff]
    · by_cases hib : i = b
      · rw [hib]
        rw [dTau_apply_right m ε' hσab,
          show (if ε' then (-1 : ZMod 3) else 1) = dSgn ε' from rfl]
        have hcoeff : c b * (if ε then (-1 : ZMod 3) else 1) * c a = dSgn ε' := by
          rw [hε']
          show c b * (if ε then (-1 : ZMod 3) else 1) * c a =
            c a * c b * (if ε then (-1 : ZMod 3) else 1)
          ring
        calc
          h (dTau m ε a b (c b • dBasis m b))
              = h (c b • dTau m ε a b (dBasis m b)) := by rw [map_smul]
          _ = h (c b • ((if ε then (-1 : ZMod 3) else 1) • dBasis m a)) := by
                rw [dTau_apply_right m ε hab]
          _ = h ((c b * (if ε then (-1 : ZMod 3) else 1)) • dBasis m a) := by
                rw [smul_smul]
          _ = (c b * (if ε then (-1 : ZMod 3) else 1)) • h (dBasis m a) := by
                rw [map_smul]
          _ = (c b * (if ε then (-1 : ZMod 3) else 1)) • (c a • dBasis m (σ a)) := by
                rw [hact a]
          _ = (c b * (if ε then (-1 : ZMod 3) else 1) * c a) • dBasis m (σ a) := by
                rw [smul_smul]
          _ = dSgn ε' • dBasis m (σ a) := by rw [hcoeff]
      · rw [dTau_apply_of_ne m ε' (fun hh => hia (σ.injective hh))
            (fun hh => hib (σ.injective hh))]
        simp only [map_smul, dTau_apply_of_ne m ε hia hib, hact i, smul_smul, hsq i,
          one_smul]
  rcases hval with hv | hv
  · refine ⟨false, σ a, σ b, hσab, hact' false ?_⟩
    rw [show dSgn false = (1 : ZMod 3) from plq_dSgn_false, hv]
  · refine ⟨true, σ a, σ b, hσab, hact' true ?_⟩
    rw [show dSgn true = (-1 : ZMod 3) from plq_dSgn_true, hv]

end CFSG.StandardType.QTwo

end
