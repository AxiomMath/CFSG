module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IDefs

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.RCKSmall (RCKSmallTag)


section

variable {G : Type*} [CommGroup G]

private lemma rckK1Ib_closure_pair_eq {a b : G}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    (Subgroup.closure ({a, b} : Set G) : Set G) = {1, a, b, a * b} := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨m, n, rfl⟩ := Subgroup.mem_closure_pair.mp hz
    have ham : a ^ m = 1 ∨ a ^ m = a := by
      rw [zpow_eq_zpow_emod m (n := (2 : ℤ)) (by simpa using ha)]
      rcases Int.emod_two_eq_zero_or_one m with h | h <;> rw [h] <;> simp
    have hbn : b ^ n = 1 ∨ b ^ n = b := by
      rw [zpow_eq_zpow_emod n (n := (2 : ℤ)) (by simpa using hb)]
      rcases Int.emod_two_eq_zero_or_one n with h | h <;> rw [h] <;> simp
    rcases ham with h | h <;> rcases hbn with h' | h' <;> rw [h, h'] <;> simp
  · intro z hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

private lemma rckK1Ib_card_closure_pair {a b : G}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) = 4 := by
  classical
  have hb' : b * b = 1 := by rw [← pow_two]; exact hb
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    exact mul_right_cancel (show a * b = b * b by rw [h, hb'])
  have hba1 : a * b ≠ a := by
    intro h
    apply hb1
    exact mul_left_cancel (show a * b = a * 1 by rw [h, mul_one])
  have hbb1 : a * b ≠ b := by
    intro h
    apply ha1
    exact mul_right_cancel (show a * b = 1 * b by rw [h, one_mul])
  rw [show Nat.card (Subgroup.closure ({a, b} : Set G)) =
      (Subgroup.closure ({a, b} : Set G) : Set G).ncard from Nat.card_coe_set_eq _]
  rw [rckK1Ib_closure_pair_eq ha hb ha1 hb1 hab]
  rw [Set.ncard_insert_of_notMem (by
        simp [ha1, hb1, hab1, Ne.symm ha1, Ne.symm hb1, Ne.symm hab1]),
      Set.ncard_insert_of_notMem (by simp [hab, hba1, Ne.symm hab, Ne.symm hba1]),
      Set.ncard_insert_of_notMem (by simp [hbb1, Ne.symm hbb1]),
      Set.ncard_singleton]


end

private noncomputable def rckK1Ib_phiR {X : Type*} [Group X] {R : Subgroup X} (φ : MulAut X)
    (hRmap : R.map φ.toMonoidHom = R) : R →* R where
  toFun x := ⟨φ (x : X), by
    have hx : φ (x : X) ∈ R.map φ.toMonoidHom := Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
    rwa [hRmap] at hx⟩
  map_one' := Subtype.ext (map_one (φ : X →* X))
  map_mul' x y := Subtype.ext (map_mul (φ : X →* X) (x : X) (y : X))

private noncomputable def rckK1Ib_psiFun {X : Type*} [Group X] {R : Subgroup X} {Fq : Type}
    [Field Fq] (ε : Multiplicative Fq ≃* R) (φ : MulAut X)
    (hRmap : R.map φ.toMonoidHom = R) : Fq → Fq :=
  fun t => (ε.symm (rckK1Ib_phiR φ hRmap (ε (Multiplicative.ofAdd t)))).toAdd

private lemma rckK1Ib_psiFun_zero {X : Type*} [Group X] {R : Subgroup X} {Fq : Type}
    [Field Fq] (ε : Multiplicative Fq ≃* R) (φ : MulAut X)
    (hRmap : R.map φ.toMonoidHom = R) :
    rckK1Ib_psiFun ε φ hRmap 0 = 0 := by
  simp [rckK1Ib_psiFun, rckK1Ib_phiR]

private lemma rckK1Ib_psiFun_one {X : Type*} [Group X] {R : Subgroup X} {Fq : Type}
    [Field Fq] (ε : Multiplicative Fq ≃* R) (φ : MulAut X)
    (hRmap : R.map φ.toMonoidHom = R)
    (hfix : φ (ε (Multiplicative.ofAdd 1) : X) = ε (Multiplicative.ofAdd 1)) :
    rckK1Ib_psiFun ε φ hRmap 1 = 1 := by
  simp [rckK1Ib_psiFun, rckK1Ib_phiR, hfix]

private lemma rckK1Ib_psiFun_add {X : Type*} [Group X] {R : Subgroup X} {Fq : Type}
    [Field Fq] (ε : Multiplicative Fq ≃* R) (φ : MulAut X)
    (hRmap : R.map φ.toMonoidHom = R) (s t : Fq) :
    rckK1Ib_psiFun ε φ hRmap (s + t) =
      rckK1Ib_psiFun ε φ hRmap s + rckK1Ib_psiFun ε φ hRmap t := by
  simp only [rckK1Ib_psiFun]
  rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul]

private lemma rckK1Ib_psiFun_mul {X : Type*} [Group X] {R : Subgroup X} {Fq : Type}
    [Field Fq] [CharP Fq 2] (ε : Multiplicative Fq ≃* R) (hRF : RCKRootFieldExact R Fq ε)
    (φ : MulAut X) (hRmap : R.map φ.toMonoidHom = R)
    (hfix : φ (ε (Multiplicative.ofAdd 1) : X) = ε (Multiplicative.ofAdd 1))
    (l t : Fq) :
    rckK1Ib_psiFun ε φ hRmap (l * t) =
      rckK1Ib_psiFun ε φ hRmap l * rckK1Ib_psiFun ε φ hRmap t := by
  classical
  by_cases hl : l = 0
  · subst hl
    rw [zero_mul, rckK1Ib_psiFun_zero, zero_mul]
  · obtain ⟨h, hh⟩ := hRF.1 l hl
    have hmem : h ∈ Subgroup.normalizer (R : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        obtain ⟨u, hu⟩ := ε.surjective ⟨x, hx⟩
        rw [show x = (ε u : X) from (congrArg Subtype.val hu).symm]
        rw [← ofAdd_toAdd u, hh (Multiplicative.toAdd u)]
        exact (ε (Multiplicative.ofAdd (l * Multiplicative.toAdd u))).2
      · intro hx
        obtain ⟨u, hu⟩ := ε.surjective ⟨h * x * h⁻¹, hx⟩
        have hu' : (ε u : X) = h * x * h⁻¹ := congrArg Subtype.val hu
        have hx' : x = h⁻¹ * (ε u) * h := by rw [hu']; group
        rw [hx']
        have hh_inv : h⁻¹ * ε u * h =
            ε (Multiplicative.ofAdd (l⁻¹ * Multiplicative.toAdd u)) := by
          have h1 : h * ε (Multiplicative.ofAdd (l⁻¹ * Multiplicative.toAdd u)) * h⁻¹ = ε u := by
            have hh1 := hh (l⁻¹ * Multiplicative.toAdd u)
            rw [mul_inv_cancel_left₀ hl, ofAdd_toAdd] at hh1
            exact hh1
          rw [← h1]; group
        rw [hh_inv]
        exact (ε (Multiplicative.ofAdd (l⁻¹ * Multiplicative.toAdd u))).2
    have hRinv : R.map φ⁻¹.toMonoidHom = R := by
      have hh2 := congrArg (fun S : Subgroup X => S.map φ⁻¹.toMonoidHom) hRmap
      rw [Subgroup.map_map] at hh2
      have hcomp : φ⁻¹.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id X := by
        ext x; simp
      rw [hcomp, Subgroup.map_id] at hh2
      exact hh2.symm
    have hmemφ : φ h ∈ Subgroup.normalizer (R : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hx' : x ∈ R.map φ.toMonoidHom := by rwa [hRmap]
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
        rw [← hyx]
        have hconj : φ h * (MulEquiv.toMonoidHom φ) y * (φ h)⁻¹ = φ (h * y * h⁻¹) := by
          simp only [map_mul, map_inv]
          rfl
        rw [hconj]
        have hy' : h * y * h⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hmem y).mp hy
        have hfin : φ (h * y * h⁻¹) ∈ R.map φ.toMonoidHom :=
          Subgroup.mem_map.mpr ⟨h * y * h⁻¹, hy', rfl⟩
        rwa [hRmap] at hfin
      · intro hx
        have hmemR : φ⁻¹ (φ h * x * (φ h)⁻¹) ∈ R := by
          have : φ⁻¹ (φ h * x * (φ h)⁻¹) ∈ R.map φ⁻¹.toMonoidHom :=
            Subgroup.mem_map.mpr ⟨φ h * x * (φ h)⁻¹, hx, rfl⟩
          rwa [hRinv] at this
        have h1 : h * φ⁻¹ x * h⁻¹ = φ⁻¹ (φ h * x * (φ h)⁻¹) := by
          simp [map_mul, map_inv]
        have h2 : h * φ⁻¹ x * h⁻¹ ∈ R := by rw [h1]; exact hmemR
        have h3 : φ⁻¹ x ∈ R := (Subgroup.mem_normalizer_iff.mp hmem (φ⁻¹ x)).mpr h2
        have hfin : x ∈ R.map φ.toMonoidHom :=
          Subgroup.mem_map.mpr ⟨φ⁻¹ x, h3, by simp⟩
        rwa [hRmap] at hfin
    obtain ⟨l', hl', hh'⟩ := hRF.2 (φ h) hmemφ
    have key : ∀ u, rckK1Ib_psiFun ε φ hRmap (l * u) =
        l' * rckK1Ib_psiFun ε φ hRmap u := by
      intro u
      have hφ : φ (ε (Multiplicative.ofAdd (l * u))) =
          ε (Multiplicative.ofAdd (l' * rckK1Ib_psiFun ε φ hRmap u)) := by
        calc φ (ε (Multiplicative.ofAdd (l * u)))
            = φ (h * ε (Multiplicative.ofAdd u) * h⁻¹) := by rw [hh u]
            _ = φ h * φ (ε (Multiplicative.ofAdd u)) * (φ h)⁻¹ := by
                  rw [map_mul, map_mul, map_inv]
            _ = φ h * ε (Multiplicative.ofAdd (rckK1Ib_psiFun ε φ hRmap u)) *
                  (φ h)⁻¹ := by
                  congr 1
                  simp [rckK1Ib_psiFun, rckK1Ib_phiR]
            _ = ε (Multiplicative.ofAdd (l' * rckK1Ib_psiFun ε φ hRmap u)) := hh' _
      have : rckK1Ib_phiR φ hRmap (ε (Multiplicative.ofAdd (l * u))) =
          ε (Multiplicative.ofAdd (l' * rckK1Ib_psiFun ε φ hRmap u)) :=
        Subtype.ext hφ
      rw [rckK1Ib_psiFun, this]
      simp
    have hψ1 : rckK1Ib_psiFun ε φ hRmap 1 = 1 := rckK1Ib_psiFun_one ε φ hRmap hfix
    have hψl : rckK1Ib_psiFun ε φ hRmap l = l' := by
      have hkey := key 1
      rwa [mul_one, hψ1, mul_one] at hkey
    rw [key t, hψl]

private noncomputable def rckK1Ib_psi {X : Type*} [Group X] {R : Subgroup X} {Fq : Type}
    [Field Fq] [CharP Fq 2] (ε : Multiplicative Fq ≃* R) (hRF : RCKRootFieldExact R Fq ε)
    (φ : MulAut X) (hRmap : R.map φ.toMonoidHom = R)
    (hfix : φ (ε (Multiplicative.ofAdd 1) : X) = ε (Multiplicative.ofAdd 1)) : Fq →+* Fq where
  toFun := rckK1Ib_psiFun ε φ hRmap
  map_one' := rckK1Ib_psiFun_one ε φ hRmap hfix
  map_zero' := rckK1Ib_psiFun_zero ε φ hRmap
  map_add' := rckK1Ib_psiFun_add ε φ hRmap
  map_mul' := rckK1Ib_psiFun_mul ε hRF φ hRmap hfix

private lemma rckK1Ib_psi_apply {X : Type*} [Group X] {R : Subgroup X} {Fq : Type}
    [Field Fq] [CharP Fq 2] (ε : Multiplicative Fq ≃* R) (hRF : RCKRootFieldExact R Fq ε)
    (φ : MulAut X) (hRmap : R.map φ.toMonoidHom = R)
    (hfix : φ (ε (Multiplicative.ofAdd 1) : X) = ε (Multiplicative.ofAdd 1)) (t : Fq) :
    rckK1Ib_psi ε hRF φ hRmap hfix t = rckK1Ib_psiFun ε φ hRmap t := rfl

private noncomputable def rckK1Ib_psiRingEquiv {X : Type*} [Group X] {R : Subgroup X} {Fq : Type}
    [Field Fq] [Finite Fq] [CharP Fq 2] (ε : Multiplicative Fq ≃* R)
    (hRF : RCKRootFieldExact R Fq ε) (φ : MulAut X) (hRmap : R.map φ.toMonoidHom = R)
    (hfix : φ (ε (Multiplicative.ofAdd 1) : X) = ε (Multiplicative.ofAdd 1)) : Fq ≃+* Fq :=
  RingEquiv.ofBijective (rckK1Ib_psi ε hRF φ hRmap hfix)
    ⟨RingHom.injective _, Finite.surjective_of_injective (RingHom.injective _)⟩

private lemma rckK1Ib_psiRingEquiv_apply {X : Type*} [Group X] {R : Subgroup X} {Fq : Type}
    [Field Fq] [Finite Fq] [CharP Fq 2] (ε : Multiplicative Fq ≃* R)
    (hRF : RCKRootFieldExact R Fq ε) (φ : MulAut X) (hRmap : R.map φ.toMonoidHom = R)
    (hfix : φ (ε (Multiplicative.ofAdd 1) : X) = ε (Multiplicative.ofAdd 1)) (t : Fq) :
    rckK1Ib_psiRingEquiv ε hRF φ hRmap hfix t = rckK1Ib_psiFun ε φ hRmap t := rfl

private lemma rckK1Ib_phiR_iterate {X : Type*} [Group X] {R : Subgroup X} (φ : MulAut X)
    (hRmap : R.map φ.toMonoidHom = R) (m : ℕ) (x : R) :
    ((((rckK1Ib_phiR φ hRmap : R → R) ^[m]) x : R) : X) = (φ ^ m) (x : X) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    change (φ ((((rckK1Ib_phiR φ hRmap : R → R) ^[m]) x : R) : X)) = (φ ^ (m + 1)) (x : X)
    rw [ih, pow_succ']
    rfl

private lemma rckK1Ib_psiFun_iterate {X : Type*} [Group X] {R : Subgroup X} {Fq : Type}
    [Field Fq] [CharP Fq 2] (ε : Multiplicative Fq ≃* R) (φ : MulAut X)
    (hRmap : R.map φ.toMonoidHom = R) (m : ℕ) (t : Fq) :
    (rckK1Ib_psiFun ε φ hRmap) ^[m] t =
      (ε.symm (((rckK1Ib_phiR φ hRmap : R → R) ^[m])
        (ε (Multiplicative.ofAdd t)))).toAdd := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, rckK1Ib_psiFun, ofAdd_toAdd]
    simp only [MulEquiv.apply_symm_apply]
    rw [Function.iterate_succ_apply']

private lemma rckK1Ib_psiFun_iterate_eq_id {X : Type*} [Group X] {R : Subgroup X} {Fq : Type}
    [Field Fq] [CharP Fq 2] (ε : Multiplicative Fq ≃* R) (φ : MulAut X)
    (hRmap : R.map φ.toMonoidHom = R) {m : ℕ} (hφ : φ ^ m = 1) :
    (rckK1Ib_psiFun ε φ hRmap) ^[m] = id := by
  funext t
  rw [rckK1Ib_psiFun_iterate]
  have hx : ((((rckK1Ib_phiR φ hRmap : R → R) ^[m]) (ε (Multiplicative.ofAdd t)) : R) : X) =
      (ε (Multiplicative.ofAdd t) : X) := by
    rw [rckK1Ib_phiR_iterate, hφ]
    rfl
  have hx' : (((rckK1Ib_phiR φ hRmap : R → R) ^[m]) (ε (Multiplicative.ofAdd t)) : R) =
      ε (Multiplicative.ofAdd t) := Subtype.ext hx
  rw [hx']
  simp

private lemma rckK1Ib_odd_log_card_of_no_cube {Fq : Type} [Field Fq] [Finite Fq] [CharP Fq 2]
    (hno : ¬ ∃ ω : Fq, ω ^ 2 + ω + 1 = 0) {n : ℕ} (hn : Nat.card Fq = 2 ^ n) : Odd n := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  apply hno
  have h3 : 3 ∣ 2 ^ n - 1 := by
    obtain ⟨d, hd⟩ := heven
    rw [hd, ← two_mul, pow_mul]
    norm_num
    have hme : Nat.ModEq 3 (4 ^ d) 1 := by
      have h41 : Nat.ModEq 3 4 1 := by decide
      simpa using h41.pow d
    have hle : 1 ≤ 4 ^ d := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 4)
    exact (Nat.modEq_iff_dvd' hle).mp hme.symm
  have h3' : 3 ∣ Nat.card Fq - 1 := by rw [hn]; exact h3
  rw [← Nat.card_units] at h3'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3'
  have hx3u : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx3 : (x : Fq) ^ 3 = 1 := by
    simpa using congrArg (fun u : Fqˣ => (u : Fq)) hx3u
  have hx1 : (x : Fq) ≠ 1 := by
    intro h
    have hxone : x = 1 := Units.ext h
    rw [hxone, orderOf_one] at hx
    exact absurd hx (by norm_num)
  refine ⟨(x : Fq), ?_⟩
  have h : ((x : Fq) - 1) * ((x : Fq) ^ 2 + (x : Fq) + 1) = 0 := by
    rw [show ((x : Fq) - 1) * ((x : Fq) ^ 2 + (x : Fq) + 1) = (x : Fq) ^ 3 - 1 by ring,
      hx3, sub_self]
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd (sub_eq_zero.mp h') hx1
  · exact h'

private lemma rckK1Ib_eq_one_of_no_cube {Fq : Type} [Field Fq] [Finite Fq] [CharP Fq 2]
    (hno : ¬ ∃ ω : Fq, ω ^ 2 + ω + 1 = 0)
    (ψ : Fq ≃+* Fq) (h2 : ∃ k : ℕ, (ψ : Fq → Fq) ^[2 ^ k] = id) : ψ = 1 := by
  classical
  haveI : Algebra (ZMod 2) Fq := ZMod.algebra Fq 2
  let ψa : Fq ≃ₐ[ZMod 2] Fq :=
    AlgEquiv.ofRingEquiv (f := ψ) (fun x => by
      have h : (ψ : Fq →+* Fq).comp (algebraMap (ZMod 2) Fq) =
          (algebraMap (ZMod 2) Fq) := Subsingleton.elim _ _
      simpa using DFunLike.congr_fun h x)
  haveI : Module.Finite (ZMod 2) Fq := (Module.finite_iff_finite (R := ZMod 2)).mpr ‹Finite Fq›
  have hcard : Nat.card (Fq ≃ₐ[ZMod 2] Fq) = Module.finrank (ZMod 2) Fq :=
    IsGalois.card_aut_eq_finrank (ZMod 2) Fq
  have hdvd : orderOf ψa ∣ Module.finrank (ZMod 2) Fq := by
    rw [← hcard]
    exact orderOf_dvd_natCard ψa
  obtain ⟨k, hk⟩ := h2
  have hdvd2 : orderOf ψa ∣ 2 ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one]
    ext x
    rw [AlgEquiv.coe_pow]
    change (ψ : Fq → Fq) ^[2 ^ k] x = x
    rw [hk]
    rfl
  have hcard2 : Nat.card Fq = 2 ^ Module.finrank (ZMod 2) Fq := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Fq), Nat.card_eq_fintype_card,
      ZMod.card]
  have hnodd : Odd (Module.finrank (ZMod 2) Fq) :=
    rckK1Ib_odd_log_card_of_no_cube hno hcard2
  have hcop : Nat.Coprime (Module.finrank (ZMod 2) Fq) (2 ^ k) :=
    hnodd.coprime_two_right.pow_right k
  have hg : orderOf ψa ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hdvd hdvd2
  have hψa1 : ψa = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  ext x
  exact congrFun (congrArg DFunLike.coe hψa1) x

private lemma rckK1Ib_sq_eq_one {Fq : Type} [Field Fq] [CharP Fq 2]
    (z : Multiplicative Fq) : z ^ 2 = 1 := by
  have hz : z = Multiplicative.ofAdd (Multiplicative.toAdd z) := (ofAdd_toAdd z).symm
  rw [hz, pow_two, ← ofAdd_add]
  have ht : Multiplicative.toAdd z + Multiplicative.toAdd z = 0 :=
    CharTwo.add_self_eq_zero (Multiplicative.toAdd z)
  rw [ht, ofAdd_zero]

private lemma rckK1Ib_conj_eq {X : Type*} [Group X] {R : Subgroup X} {Fq : Type}
    [Field Fq] [CharP Fq 2] (ε : Multiplicative Fq ≃* R) (φ : MulAut X)
    (hRmap : R.map φ.toMonoidHom = R) (z : Multiplicative Fq) :
    φ ((R.subtype.comp ε.toMonoidHom) z) * (((R.subtype.comp ε.toMonoidHom) z))⁻¹ =
      ((ε (Multiplicative.ofAdd (rckK1Ib_psiFun ε φ hRmap (Multiplicative.toAdd z) -
        Multiplicative.toAdd z)) : R) : X) := by
  have hphi : rckK1Ib_phiR φ hRmap (ε z) =
      ε (Multiplicative.ofAdd (rckK1Ib_psiFun ε φ hRmap (Multiplicative.toAdd z))) := by
    rw [← ofAdd_toAdd z]
    simp [rckK1Ib_psiFun, rckK1Ib_phiR]
  change (((rckK1Ib_phiR φ hRmap (ε z) * (ε z)⁻¹ : R) : X)) = _
  rw [hphi, ← map_inv, ← map_mul]
  congr 1
  rw [← ofAdd_toAdd z]
  simp [ofAdd_add, ofAdd_neg, toAdd_ofAdd, sub_eq_add_neg]

private lemma rckK1Ib_map_isElemAbelian {G H : Type*} [Group G] [Group H] {p : ℕ}
    {K : Subgroup G} (f : G →* H) (h : CFSG.Open.IsElemAbelian p K) :
    CFSG.Open.IsElemAbelian p (K.map f) := by
  constructor
  · refine IsMulCommutative.of_comm ?_
    intro x y
    obtain ⟨a, ha, hx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨b, hb, hy⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    have hab : a * b = b * a := by
      haveI : IsMulCommutative K := h.1
      exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : K) (⟨b, hb⟩ : K))
    simp only [Subgroup.coe_mul]
    rw [show x.val = f a from hx.symm, show y.val = f b from hy.symm]
    rw [← map_mul, ← map_mul, hab]
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    show f a ^ p = 1
    rw [← map_pow, h.2 a ha, map_one]

private lemma rckK1Ib_data_of_scalar {X : Type*} [Group X] [Finite X] {R : Subgroup X}
    {Fq : Type} [Field Fq] [Finite Fq] [CharP Fq 2]
    (hq : 4 ≤ Nat.card Fq) (ε : Multiplicative Fq ≃* R) (hRF : RCKRootFieldExact R Fq ε)
    (hA : ∀ α : MulAut X, α (ε (Multiplicative.ofAdd 1) : X) = ε (Multiplicative.ofAdd 1) →
      R.map α.toMonoidHom = R)
    {b0 : Fq} (hb0 : b0 ≠ 0) (hb0' : b0 ≠ 1)
    (hscalar : ∀ (φ : MulAut X) (hfix : φ (ε (Multiplicative.ofAdd 1) : X) =
        ε (Multiplicative.ofAdd 1)), (∃ k : ℕ, φ ^ (2 ^ k) = 1) →
      rckK1Ib_psiFun ε φ (hA φ hfix) b0 - b0 = 0 ∨
        rckK1Ib_psiFun ε φ (hA φ hfix) b0 - b0 = 1) :
    ∃ Vb : Subgroup X, Vb ≤ R ∧
      RCKK1Data (ε (Multiplicative.ofAdd 1) : X) Vb := by
  classical
  let a : Multiplicative Fq := Multiplicative.ofAdd (1 : Fq)
  let bF : Multiplicative Fq := Multiplicative.ofAdd b0
  let Wb : Subgroup (Multiplicative Fq) := Subgroup.closure ({a, bF} : Set (Multiplicative Fq))
  let Vb : Subgroup X := Wb.map (R.subtype.comp ε.toMonoidHom)
  have ha2 : a ^ 2 = 1 := rckK1Ib_sq_eq_one a
  have hb2 : bF ^ 2 = 1 := rckK1Ib_sq_eq_one bF
  have ha1 : a ≠ 1 := by
    intro h
    have : (1 : Fq) = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa [a] using this
    exact one_ne_zero this
  have hb1 : bF ≠ 1 := by
    intro h
    apply hb0
    have := congrArg Multiplicative.toAdd h
    simpa [bF] using this
  have hab : a ≠ bF := by
    intro h
    apply hb0'
    have := congrArg Multiplicative.toAdd h
    simpa [a, bF] using this.symm
  have hWb : (Wb : Set (Multiplicative Fq)) = {1, a, bF, a * bF} :=
    rckK1Ib_closure_pair_eq ha2 hb2 ha1 hb1 hab
  have hcardWb : Nat.card Wb = 4 := rckK1Ib_card_closure_pair ha2 hb2 ha1 hb1 hab
  have hmemWb : ∀ z, z ∈ Wb ↔ z ∈ ({1, a, bF, a * bF} : Set (Multiplicative Fq)) := by
    intro z
    change z ∈ (Wb : Set (Multiplicative Fq)) ↔ _
    rw [hWb]
  refine ⟨Vb, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    exact (ε z).2
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨a, Subgroup.subset_closure (by simp [a]), rfl⟩
    · intro h
      have h' : (ε (Multiplicative.ofAdd (1 : Fq)) : R) = 1 := Subtype.ext h
      rw [← map_one ε] at h'
      have h'' : Multiplicative.ofAdd (1 : Fq) = 1 := ε.injective h'
      have : (1 : Fq) = 0 := by
        have := congrArg Multiplicative.toAdd h''
        simpa using this
      exact one_ne_zero this
    · have hEAWb : CFSG.Open.IsElemAbelian 2 Wb := by
        constructor
        · exact IsMulCommutative.of_comm (fun x y => Subtype.ext (mul_comm _ _))
        · intro x hx
          exact rckK1Ib_sq_eq_one x
      exact rckK1Ib_map_isElemAbelian (R.subtype.comp ε.toMonoidHom) hEAWb
    · rw [show Nat.card Vb = Nat.card Wb from
        Subgroup.card_map_of_injective (K := Wb) (f := R.subtype.comp ε.toMonoidHom) ?_,
        hcardWb]
      intro x y h
      exact ε.injective (Subtype.ext h)
    · intro v hv hv1
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hv
      have hz' : z ∈ ({1, a, bF, a * bF} : Set (Multiplicative Fq)) := (hmemWb z).mp hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
      rcases hz' with hz1 | hza | hzb | hzab
      · rw [hz1] at hv1
        exact absurd (by simp : (R.subtype.comp ε.toMonoidHom) 1 = 1) hv1
      · rw [hza]
        exact ⟨1, by simp [a]⟩
      · rw [hzb]
        obtain ⟨h, hh⟩ := hRF.1 b0 hb0
        exact ⟨h, by simpa [bF, mul_one] using (hh 1).symm⟩
      · rw [hzab]
        have h1b0 : (1 : Fq) + b0 ≠ 0 := by
          intro hc
          apply hb0'
          have hneg : (-1 : Fq) = 1 := by
            rw [neg_eq_iff_add_eq_zero]
            exact CharTwo.add_self_eq_zero 1
          have h2 : b0 = -1 := eq_neg_of_add_eq_zero_right hc
          rwa [hneg] at h2
        obtain ⟨h, hh⟩ := hRF.1 (1 + b0) h1b0
        exact ⟨h, by simpa [a, bF, ofAdd_add, mul_one] using (hh 1).symm⟩
    · intro Y hY hfixY hnorm v hv φ hφ
      have hfix : φ (ε (Multiplicative.ofAdd 1) : X) = ε (Multiplicative.ofAdd 1) := hfixY φ hφ
      have hRmap : R.map φ.toMonoidHom = R := hA φ hfix
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hv
      have hz' : z ∈ ({1, a, bF, a * bF} : Set (Multiplicative Fq)) := (hmemWb z).mp hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
      have h2φ : ∃ k : ℕ, φ ^ (2 ^ k) = 1 := by
        obtain ⟨k, hk⟩ := hY.exists_pow_pow_eq_one (⟨φ, hφ⟩ : Y)
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      have hsc := hscalar φ hfix h2φ
      have key : ∀ t : Fq, (rckK1Ib_psiFun ε φ hRmap t - t = 0 ∨
          rckK1Ib_psiFun ε φ hRmap t - t = 1) →
          φ ((R.subtype.comp ε.toMonoidHom) (Multiplicative.ofAdd t)) *
            (((R.subtype.comp ε.toMonoidHom) (Multiplicative.ofAdd t)))⁻¹ ∈
            Subgroup.zpowers (ε (Multiplicative.ofAdd 1) : X) := by
        intro t ht
        rw [rckK1Ib_conj_eq ε φ hRmap (Multiplicative.ofAdd t)]
        simp only [toAdd_ofAdd]
        rcases ht with h | h
        · rw [h, ofAdd_zero]
          simp
        · rw [h]
          exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
      rcases hz' with hz1 | hza | hzb | hzab
      · rw [hz1]
        exact key 0 (Or.inl (by simp [rckK1Ib_psiFun_zero]))
      · rw [hza]
        have h1 : rckK1Ib_psiFun ε φ hRmap 1 = 1 := rckK1Ib_psiFun_one ε φ hRmap hfix
        exact key 1 (Or.inl (by rw [h1, sub_self]))
      · rw [hzb]
        exact key b0 (by simpa [bF] using hsc)
      · rw [hzab]
        have hψ : rckK1Ib_psiFun ε φ hRmap (1 + b0) =
            1 + rckK1Ib_psiFun ε φ hRmap b0 := by
          rw [rckK1Ib_psiFun_add, rckK1Ib_psiFun_one ε φ hRmap hfix]
        have hsub : rckK1Ib_psiFun ε φ hRmap (1 + b0) - (1 + b0) =
            rckK1Ib_psiFun ε φ hRmap b0 - b0 := by
          rw [hψ]; ring
        exact key (1 + b0) (by rw [hsub]; exact hsc)


theorem rckK1I_K1b {X : Type} [Group X] [Finite X] {R : Subgroup X} {Fq : Type} [Field Fq] [Finite Fq]
    [CharP Fq 2] (hq : 4 ≤ Nat.card Fq) (ε : Multiplicative Fq ≃* R) (hRF : RCKRootFieldExact R Fq ε)
    (hA : ∀ α : MulAut X, α (ε (Multiplicative.ofAdd 1) : X) = ε (Multiplicative.ofAdd 1) →
      R.map α.toMonoidHom = R) :
    ∃ Vb : Subgroup X, Vb ≤ R ∧ RCKK1Data (ε (Multiplicative.ofAdd 1) : X) Vb := by
  classical
  by_cases hcube : ∃ ω : Fq, ω ^ 2 + ω + 1 = 0
  · obtain ⟨ω, hω⟩ := hcube
    have hω1 : ω ≠ 1 := by
      intro h
      rw [h] at hω
      simp only [one_pow, CharTwo.add_self_eq_zero, zero_add] at hω
      exact one_ne_zero hω
    have hω0 : ω ≠ 0 := by
      intro h
      rw [h] at hω
      norm_num at hω
    refine rckK1Ib_data_of_scalar hq ε hRF hA hω0 hω1 ?_
    intro φ hfix _
    have hRmap : R.map φ.toMonoidHom = R := hA φ hfix
    have hroot : (rckK1Ib_psiFun ε φ hRmap ω) ^ 2 + rckK1Ib_psiFun ε φ hRmap ω + 1 = 0 := by
      have hmap : (rckK1Ib_psi ε hRF φ hRmap hfix ω) ^ 2 +
          (rckK1Ib_psi ε hRF φ hRmap hfix ω) + 1 = 0 := by
        rw [← map_pow, ← map_one (rckK1Ib_psi ε hRF φ hRmap hfix), ← map_add, ← map_add,
          hω, map_zero]
      simpa only [rckK1Ib_psi_apply] using hmap
    have hωsum : ω ^ 2 + ω = 1 := CharTwo.add_eq_zero.mp hω
    have hδ : (rckK1Ib_psiFun ε φ hRmap ω + ω) ^ 2 +
        (rckK1Ib_psiFun ε φ hRmap ω + ω) = 0 := by
      have h1 : (rckK1Ib_psiFun ε φ hRmap ω) ^ 2 + rckK1Ib_psiFun ε φ hRmap ω = 1 :=
        CharTwo.add_eq_zero.mp hroot
      calc (rckK1Ib_psiFun ε φ hRmap ω + ω) ^ 2 +
            (rckK1Ib_psiFun ε φ hRmap ω + ω)
          = ((rckK1Ib_psiFun ε φ hRmap ω) ^ 2 + rckK1Ib_psiFun ε φ hRmap ω) +
              (ω ^ 2 + ω) := by rw [CharTwo.add_sq]; ring
        _ = 1 + 1 := by rw [h1, hωsum]
        _ = 0 := CharTwo.add_self_eq_zero 1
    have hδ' : (rckK1Ib_psiFun ε φ hRmap ω - ω) *
        ((rckK1Ib_psiFun ε φ hRmap ω - ω) + 1) = 0 := by
      rw [CharTwo.sub_eq_add]
      have : (rckK1Ib_psiFun ε φ hRmap ω + ω) *
          ((rckK1Ib_psiFun ε φ hRmap ω + ω) + 1) =
          (rckK1Ib_psiFun ε φ hRmap ω + ω) ^ 2 +
            (rckK1Ib_psiFun ε φ hRmap ω + ω) := by ring
      rw [this, hδ]
    rcases mul_eq_zero.mp hδ' with h | h
    · left; exact h
    · right; exact CharTwo.add_eq_zero.mp h
  ·
    obtain ⟨c, hc⟩ : ∃ c : Fq, c ≠ 0 ∧ c ≠ 1 := by
      haveI : Fintype Fq := Fintype.ofFinite Fq
      have h2 : ({0, 1} : Finset Fq).card < (Finset.univ : Finset Fq).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        have h01 : ({0, 1} : Finset Fq).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
        rw [h01]; omega
      obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card h2
      exact ⟨e, by simpa [Finset.mem_insert, Finset.mem_singleton] using he⟩
    refine rckK1Ib_data_of_scalar hq ε hRF hA hc.1 hc.2 ?_
    intro φ hfix h2φ
    have hRmap : R.map φ.toMonoidHom = R := hA φ hfix
    have hψ1 : rckK1Ib_psiRingEquiv ε hRF φ hRmap hfix = 1 := by
      refine rckK1Ib_eq_one_of_no_cube hcube _ ?_
      obtain ⟨k, hk⟩ := h2φ
      exact ⟨k, rckK1Ib_psiFun_iterate_eq_id ε φ hRmap hk⟩
    left
    have : rckK1Ib_psiFun ε φ hRmap c = c := by
      rw [← rckK1Ib_psiRingEquiv_apply ε hRF φ hRmap hfix c, hψ1]
      rfl
    rw [this, sub_self]

end CFSG.StandardType.RCKK1I
