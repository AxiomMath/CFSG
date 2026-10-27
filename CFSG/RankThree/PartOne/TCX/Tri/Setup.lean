module

public import CFSG.RankThree.PartOne.TCX.Tri.Graph
public import CFSG.RankThree.PartOne.TCX.Tri.Twist
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.RankThree.PartOne.KLCE.Descent
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KLCE
open CFSG.RankThree.PartOne.TCX

section Defs

variable (L : Type) [Field L]

@[expose] noncomputable def triG (p : ℕ) : ModGL TwistTag.D4.tag L :=
  if p % 3 = 1 then 1 else triN L

@[expose] noncomputable def triF0 [CharP L 2] (f₀ : ℕ) :
    ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L :=
  twistHom TwistTag.D4 L (iterateFrobenius L 2 f₀)

@[expose] noncomputable def triPhi [CharP L 2] (p f₀ : ℕ) :
    ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L :=
  twPhi (triP L ^ p) (iterateFrobenius L 2 (f₀ * p))

variable {L}

theorem triF0_apply [CharP L 2] (f₀ : ℕ) (u : ModGL TwistTag.D4.tag L) :
    triF0 L f₀ u = triP L * Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) u * (triP L)⁻¹ :=
  rfl

theorem triPhi_apply [CharP L 2] (p f₀ : ℕ) (u : ModGL TwistTag.D4.tag L) :
    triPhi L p f₀ u =
      triP L ^ p * Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p))) u * (triP L ^ p)⁻¹ :=
  twPhi_apply _ _ _

theorem triF0_iterate [CharP L 2] (f₀ m : ℕ) (u : ModGL TwistTag.D4.tag L) :
    (⇑(triF0 L f₀))^[m] u =
      triP L ^ m * Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * m))) u * (triP L ^ m)⁻¹ := by
  induction m generalizing u with
  | zero =>
    rw [Nat.mul_zero, iterateFrobenius_zero, Function.iterate_zero, id_eq, pow_zero, inv_one,
      one_mul, mul_one]
    exact (Units.ext (entrywise_id _)).symm
  | succ m ih =>
    have hP : ∀ σ : L →+* L, Units.map (entrywiseHom σ) (triP L) = triP L := fun σ =>
      units_map_entrywiseHom_diagramMap (t := TwistTag.D4) σ
    have hcomp : ∀ (a b : L →+* L) (g : ModGL TwistTag.D4.tag L),
        Units.map (entrywiseHom a) (Units.map (entrywiseHom b) g) =
          Units.map (entrywiseHom (a.comp b)) g := fun a b g =>
      units_map_entrywiseHom_comp (t := TwistTag.D4) a b g
    rw [Function.iterate_succ_apply', ih, triF0_apply, map_mul, map_mul, map_inv, map_pow, hP,
      hcomp, show f₀ * (m + 1) = f₀ + f₀ * m by ring, iterateFrobenius_add, pow_succ']
    group

theorem triPhi_eq_iterate [CharP L 2] (p f₀ : ℕ) (u : ModGL TwistTag.D4.tag L) :
    triPhi L p f₀ u = (⇑(triF0 L f₀))^[p] u := by
  rw [triPhi_apply, triF0_iterate]

theorem triG_eq_one {p : ℕ} (hp : p % 3 = 1) : triG L p = 1 := by
  simp [triG, hp]

theorem triG_eq_triN {p : ℕ} (hp : ¬ p % 3 = 1) : triG L p = triN L := by
  simp [triG, hp]

theorem triP_pow_cube : triP L ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  exact triP_cube L

theorem triP_pow_prime (p : ℕ) : triP L ^ p = triP L ^ (p % 3) := by
  conv_lhs => rw [← Nat.div_add_mod p 3, pow_add, pow_mul, triP_pow_cube, one_pow, one_mul]

theorem triG_conj_triP {p : ℕ} (hp3 : p % 3 = 1 ∨ p % 3 = 2) :
    triG L p * triP L * (triG L p)⁻¹ = triP L ^ p := by
  rw [triP_pow_prime]
  rcases hp3 with h | h
  · rw [triG_eq_one h, h, inv_one, one_mul, mul_one, pow_one]
  · rw [triG_eq_triN (by omega), h, pow_two, triN_conj_triP, triP_sq]

theorem triPow_mul_triG {p : ℕ} (hp3 : p % 3 = 1 ∨ p % 3 = 2) :
    triP L ^ p * triG L p = triG L p * triP L := by
  rw [← triG_conj_triP hp3]
  group

theorem triP_mul_triG_inv {p : ℕ} (hp3 : p % 3 = 1 ∨ p % 3 = 2) :
    triP L * (triG L p)⁻¹ = (triG L p)⁻¹ * triP L ^ p := by
  rw [← triG_conj_triP hp3]
  group

theorem units_map_triG [CharP L 2] (p : ℕ) (σ : L →+* L) :
    Units.map (entrywiseHom σ) (triG L p) = triG L p := by
  by_cases h : p % 3 = 1
  · rw [triG_eq_one h, map_one]
  · rw [triG_eq_triN h]
    exact units_map_entrywiseHom_permModuleMap triSwap_cartan L σ

theorem triN_inv : (triN L)⁻¹ = triN L := inv_eq_of_mul_eq_one_right (triN_mul_self L)

theorem triG_inv_mul_mem_adjoint {p : ℕ} (u : ModGL TwistTag.D4.tag L)
    (hu : u ∈ adjointGroup TwistTag.D4.tag L) :
    triG L p * u * (triG L p)⁻¹ ∈ adjointGroup TwistTag.D4.tag L ∧
      (triG L p)⁻¹ * u * triG L p ∈ adjointGroup TwistTag.D4.tag L := by
  by_cases h : p % 3 = 1
  · rw [triG_eq_one h]
    simpa using hu
  · rw [triG_eq_triN h]
    have h1 : triN L * u * (triN L)⁻¹ ∈ adjointGroup TwistTag.D4.tag L := by
      have := Subgroup.mem_map_of_mem (MulAut.conj (permModuleMap triSwap_cartan L)).toMonoidHom hu
      rw [map_conj_permModuleMap_adjointGroup] at this
      simpa [MulAut.conj_apply, triN] using this
    refine ⟨h1, ?_⟩
    rw [triN_inv]
    simpa [triN_inv] using h1

theorem triP_mul_triN_mul_inv : triP L * triN L * (triP L)⁻¹ = triN L * triP L := by
  have h1 : triN L * triP L = (triP L)⁻¹ * triN L := triN_mul_triP L
  have h5 : triP L * triN L * (triP L * triN L) = 1 := by
    calc triP L * triN L * (triP L * triN L) = triP L * (triN L * triP L) * triN L := by group
      _ = triP L * ((triP L)⁻¹ * triN L) * triN L := by rw [h1]
      _ = triN L * triN L := by group
      _ = 1 := triN_mul_self L
  have h2 : triP L * triN L = triN L * (triP L)⁻¹ := by
    rw [eq_inv_of_mul_eq_one_left h5, mul_inv_rev, triN_inv]
  rw [h2]
  have h4 : (triP L)⁻¹ * (triP L)⁻¹ = triP L := by
    rw [← mul_inv_rev, triP_sq, inv_inv]
  calc triN L * (triP L)⁻¹ * (triP L)⁻¹ = triN L * ((triP L)⁻¹ * (triP L)⁻¹) := by
        rw [mul_assoc]
    _ = triN L * triP L := by rw [h4]

end Defs

section Embed

variable {K : Type} [Field K] [Finite K] (L : Type) [Field L] [Algebra K L]

@[expose] noncomputable def triIota (p : ℕ) (σ : K ≃+* K) :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* ModGL TwistTag.D4.tag L :=
  (MulAut.conj (triG L p)).toMonoidHom.comp (triEmb K σ L)

variable {L}

omit [Finite K] in
theorem triIota_apply (p : ℕ) (σ : K ≃+* K) (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    triIota L p σ y = triG L p * triEmb K σ L y * (triG L p)⁻¹ := by
  simp only [triIota, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

omit [Finite K] in
theorem triIota_injective (p : ℕ) (σ : K ≃+* K) : Function.Injective (triIota L p σ) :=
  (MulAut.conj (triG L p)).injective.comp triEmb_injective

omit [Finite K] in
theorem triIota_mem_adjoint (p : ℕ) (σ : K ≃+* K)
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    triIota L p σ y ∈ adjointGroup TwistTag.D4.tag L := by
  rw [triIota_apply]
  exact (triG_inv_mul_mem_adjoint _ (triEmb_mem_adjointGroup y)).1

omit [Finite K] in
theorem triFr_apply [CharP L 2] (p f₀ : ℕ) (c : L) :
    iterateFrobenius L 2 (f₀ * p) c = c ^ 2 ^ (p * f₀) := by
  rw [mul_comm p f₀]
  exact iterateFrobenius_def 2 (f₀ * p) c

omit [Finite K] in
theorem triFr_comm [CharP L 2] {p f₀ : ℕ} (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ (p * f₀)) :
    (algebraMap K L).comp σ.toRingHom =
      (iterateFrobenius L 2 (f₀ * p)).comp (algebraMap K L) :=
  RingHom.ext fun c => by
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [hσ, map_pow, triFr_apply]

omit [Finite K] in
theorem triPhi_triIota [CharP L 2] {p f₀ : ℕ} (hp3 : p % 3 = 1 ∨ p % 3 = 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ (p * f₀))
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    triPhi L p f₀ (triIota L p σ y) = triIota L p σ y := by
  have hfix := triEmb_fixed (K := K) (σ := σ) (L := L) (iterateFrobenius L 2 (f₀ * p))
    (triFr_comm σ hσ) y
  set w := triEmb K σ L y with hw
  have hw' : Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p))) w =
      (triP L)⁻¹ * w * triP L := by
    have h1 : triP L * Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p))) w *
        (triP L)⁻¹ = w := hfix
    calc _ = (triP L)⁻¹ * (triP L * Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p))) w *
          (triP L)⁻¹) * triP L := by group
      _ = _ := by rw [h1]
  rw [triIota_apply, triPhi_apply, map_mul, map_mul, map_inv, units_map_triG, hw']
  have hg := triPow_mul_triG (L := L) hp3
  calc triP L ^ p * (triG L p * ((triP L)⁻¹ * w * triP L) * (triG L p)⁻¹) * (triP L ^ p)⁻¹
      = (triP L ^ p * triG L p) * ((triP L)⁻¹ * w * triP L) * (triP L ^ p * triG L p)⁻¹ := by
        group
    _ = (triG L p * triP L) * ((triP L)⁻¹ * w * triP L) * (triG L p * triP L)⁻¹ := by rw [hg]
    _ = triG L p * w * (triG L p)⁻¹ := by group

omit [Finite K] in
theorem triIota_range [CharP L 2] [IsAlgClosure K L] {p f₀ : ℕ} (hp3 : p % 3 = 1 ∨ p % 3 = 2)
    (hf : 1 ≤ p * f₀) (hK : Nat.card K = (2 ^ (p * f₀)) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ (p * f₀)) {u : ModGL TwistTag.D4.tag L}
    (hu : u ∈ adjointGroup TwistTag.D4.tag L) (hΦ : triPhi L p f₀ u = u) :
    u ∈ (triIota L p σ).range := by
  have hwA : (triG L p)⁻¹ * u * triG L p ∈ adjointGroup TwistTag.D4.tag L := (triG_inv_mul_mem_adjoint u hu).2
  have hwF : twistHom TwistTag.D4 L (iterateFrobenius L 2 (f₀ * p))
      ((triG L p)⁻¹ * u * triG L p) = (triG L p)⁻¹ * u * triG L p := by
    rw [twistHom_apply, map_mul, map_mul, map_inv, units_map_triG]
    have e1 := triP_mul_triG_inv (L := L) hp3
    have hΦ' := hΦ
    rw [triPhi_apply] at hΦ'
    calc triP L * ((triG L p)⁻¹ * Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p))) u *
          triG L p) * (triP L)⁻¹
        = (triP L * (triG L p)⁻¹) * Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p))) u *
          (triP L * (triG L p)⁻¹)⁻¹ := by group
      _ = ((triG L p)⁻¹ * triP L ^ p) *
          Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p))) u *
          ((triG L p)⁻¹ * triP L ^ p)⁻¹ := by rw [e1]
      _ = (triG L p)⁻¹ * (triP L ^ p *
          Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p))) u * (triP L ^ p)⁻¹) *
          triG L p := by group
      _ = (triG L p)⁻¹ * u * triG L p := by rw [hΦ']
  have hmem : (triG L p)⁻¹ * u * triG L p ∈ (triEmb K σ L).range := by
    rw [triEmb_range (ℓ := 2) (f := p * f₀) Nat.prime_two hf hK hσ
      (iterateFrobenius L 2 (f₀ * p)) (triFr_apply p f₀)]
    exact Subgroup.mem_inf.2 ⟨hwA, hwF⟩
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, ?_⟩
  rw [triIota_apply, hy]
  group

end Embed

section Actor

variable {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L] [CharP L 2]

theorem triF0_triIota {p f₀ : ℕ} (hp3 : p % 3 = 1 ∨ p % 3 = 2) (σ ψ ε : K ≃+* K)
    (hψ : (algebraMap K L).comp ψ.toRingHom = (iterateFrobenius L 2 f₀).comp (algebraMap K L))
    (hεψ : ε * σ ^ (if p % 3 = 1 then 1 else 2) = ψ)
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    triF0 L f₀ (triIota L p σ y) =
      triIota L p σ (fieldActor (t := TwistTag.D4) σ ε y) := by
  have hyK : twistHom TwistTag.D4 K σ.toRingHom (y : ModGL TwistTag.D4.tag K) = y :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ y.2)).2
  set yK : ModGL TwistTag.D4.tag K := (y : ModGL TwistTag.D4.tag K) with hyKdef
  set PK : ModGL TwistTag.D4.tag K := diagramMap TwistTag.D4 K with hPK
  have hσy : Units.map (entrywiseHom σ.toRingHom) yK = PK⁻¹ * yK * PK := by
    have h1 : PK * Units.map (entrywiseHom σ.toRingHom) yK * PK⁻¹ = yK := hyK
    calc _ = PK⁻¹ * (PK * Units.map (entrywiseHom σ.toRingHom) yK * PK⁻¹) * PK := by group
      _ = _ := by rw [h1]
  have hPfix : ∀ τ' : K →+* K, Units.map (entrywiseHom τ') PK = PK := fun τ' =>
    units_map_entrywiseHom_diagramMap (t := TwistTag.D4) τ'
  have hcomp : ∀ (a b : K →+* K) (g : ModGL TwistTag.D4.tag K),
      Units.map (entrywiseHom a) (Units.map (entrywiseHom b) g) =
        Units.map (entrywiseHom (a.comp b)) g := fun a b g =>
    units_map_entrywiseHom_comp (t := TwistTag.D4) a b g
  have hact : ((fieldActor (t := TwistTag.D4) σ ε y :
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
        Units.map (entrywiseHom ε.toRingHom) yK := coe_fieldActor σ ε y
  have hEeq : triEmb K σ L (fieldActor (t := TwistTag.D4) σ ε y) =
      baseChangeGL (algebraMap K L) (Units.map (entrywiseHom ε.toRingHom) yK) := by
    rw [triEmb_apply, hact]
  have hF0 : ∀ g : ModGL TwistTag.D4.tag K, triF0 L f₀ (baseChangeGL (algebraMap K L) g) =
      baseChangeGL (algebraMap K L) (twistHom TwistTag.D4 K ψ.toRingHom g) := fun g =>
    twistHom_baseChangeGL (algebraMap K L) hψ g
  have hPL : baseChangeGL (algebraMap K L) PK = triP L := baseChangeGL_diagramMap (algebraMap K L) TwistTag.D4
  have hεy : Units.map (entrywiseHom ε.toRingHom) (PK⁻¹ * yK * PK) =
      PK⁻¹ * Units.map (entrywiseHom ε.toRingHom) yK * PK := by
    rw [map_mul, map_mul, map_inv, hPfix]
  rcases hp3 with h | h
  ·
    have hj : (if p % 3 = 1 then 1 else 2) = 1 := by simp [h]
    rw [hj] at hεψ
    have hψc : ∀ c, ψ c = ε (σ c) := fun c => by
      rw [← hεψ, pow_one, RingAut.mul_apply]
    have hψeq : ψ.toRingHom = ε.toRingHom.comp σ.toRingHom := RingHom.ext hψc
    have hT : twistHom TwistTag.D4 K ψ.toRingHom yK = Units.map (entrywiseHom ε.toRingHom) yK := by
      rw [twistHom_apply, hψeq, ← hcomp, hσy, hεy]
      change PK * (PK⁻¹ * Units.map (entrywiseHom ε.toRingHom) yK * PK) * PK⁻¹ = _
      group
    rw [triIota_apply, triIota_apply, triG_eq_one h, hEeq, inv_one, one_mul, mul_one, one_mul,
      mul_one, triEmb_apply, hF0, hT]
  ·
    have hj : (if p % 3 = 1 then 1 else 2) = 2 := by simp [show ¬ p % 3 = 1 by omega]
    rw [hj] at hεψ
    have hψc : ∀ c, ψ c = ε (σ (σ c)) := fun c => by
      rw [← hεψ, pow_two, RingAut.mul_apply, RingAut.mul_apply]
    have hψeq : ψ.toRingHom = ε.toRingHom.comp (σ.toRingHom.comp σ.toRingHom) :=
      RingHom.ext hψc
    have hσσ : Units.map (entrywiseHom σ.toRingHom) (Units.map (entrywiseHom σ.toRingHom) yK) =
        PK⁻¹ * (PK⁻¹ * yK * PK) * PK := by
      rw [hσy, map_mul, map_mul, map_inv, hPfix, hσy]
    have hT : twistHom TwistTag.D4 K ψ.toRingHom yK =
        PK⁻¹ * Units.map (entrywiseHom ε.toRingHom) yK * PK := by
      rw [twistHom_apply, hψeq, ← hcomp, ← hcomp, hσσ, map_mul, map_mul, map_inv, hPfix]
      have h2 : Units.map (entrywiseHom ε.toRingHom) (PK⁻¹ * yK * PK) =
          PK⁻¹ * Units.map (entrywiseHom ε.toRingHom) yK * PK := hεy
      rw [h2, ← hPK]
      group
    have hg : triG L p = triN L := triG_eq_triN (by omega)
    have hFN : triF0 L f₀ (triN L) = triN L * triP L := by
      rw [triF0_apply, ← hg, units_map_triG, hg]
      exact triP_mul_triN_mul_inv
    rw [triIota_apply, triIota_apply, hg, hEeq, map_mul, map_mul, map_inv, hFN, triEmb_apply,
      hF0, hT, map_mul, map_mul, map_inv, hPL]
    group

end Actor

section Main

theorem zpowers_eq_of_eq_pow {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {a b : G}
    (hb : b ^ p = 1) {m : ℕ} (hm : ¬ p ∣ m) (h : a = b ^ m) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  apply le_antisymm
  · rw [Subgroup.zpowers_le, h]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b) m
  · rw [Subgroup.zpowers_le]
    obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm hp.one_lt
    have hbt : b = a ^ t := by
      have h1 : b ^ (m * t) = b := by
        calc b ^ (m * t) = b ^ (m * t % p + p * (m * t / p)) := by rw [Nat.mod_add_div]
          _ = b ^ (m * t % p) * (b ^ p) ^ (m * t / p) := by rw [pow_add, pow_mul]
          _ = b := by rw [hb, one_pow, mul_one, ht, pow_one]
      rw [h, ← pow_mul]
      exact h1.symm
    rw [hbt]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) t

theorem tri_eps_data {p : ℕ} (hp : p.Prime) (f₀ : ℕ) (hp3 : p % 3 = 1 ∨ p % 3 = 2) :
    ∃ e m : ℕ, e + p * f₀ * (if p % 3 = 1 then 1 else 2) = f₀ + 3 * (p * f₀) ∧
      e = 3 * f₀ * m ∧ ¬ p ∣ m := by
  have hnd : ∀ m k : ℕ, 3 * m = k * p + 1 → ¬ p ∣ m := by
    intro m k hmk hpm
    have h1 : p ∣ 3 * m := Dvd.dvd.mul_left hpm 3
    rw [hmk] at h1
    have h2 : p ∣ 1 := (Nat.dvd_add_right (Dvd.intro_left k rfl)).1 h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  rcases hp3 with h | h
  · obtain ⟨m, hm⟩ : ∃ m, 3 * m = 2 * p + 1 := ⟨(2 * p + 1) / 3, by omega⟩
    refine ⟨3 * f₀ * m, m, ?_, rfl, hnd m 2 (by omega)⟩
    have : (if p % 3 = 1 then 1 else 2) = 1 := by simp [h]
    rw [this]
    nlinarith
  · obtain ⟨m, hm⟩ : ∃ m, 3 * m = 1 * p + 1 := ⟨(p + 1) / 3, by omega⟩
    refine ⟨3 * f₀ * m, m, ?_, rfl, hnd m 1 hm⟩
    have : (if p % 3 = 1 then 1 else 2) = 2 := by simp [show ¬ p % 3 = 1 by omega]
    rw [this]
    nlinarith


theorem tri_setup {p f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ (p * f₀)) ^ 3) (σ δ₀ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ (p * f₀)) (hδ₀ : ∀ c, δ₀ c = c ^ 2 ^ (3 * f₀))
    (hδ₀ord : orderOf δ₀ = p) (L : Type) [Field L] [Algebra K L] [CharP L 2] :
    ∃ ε : K ≃+* K,
      (∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        triF0 L f₀ (triIota L p σ y) =
          triIota L p σ (fieldActor (t := TwistTag.D4) σ ε y)) ∧
      fieldActor (t := TwistTag.D4) σ ε ^ p = 1 ∧
      Subgroup.zpowers (fieldActor (t := TwistTag.D4) σ ε) =
        Subgroup.zpowers (fieldActor (t := TwistTag.D4) σ δ₀) := by
  have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3 : ¬ 3 ∣ p := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
      omega
    omega
  have hpf : 1 ≤ 3 * (p * f₀) := Nat.succ_le_of_lt (Nat.mul_pos (by norm_num)
    (Nat.mul_pos hp.pos hf₀))
  obtain ⟨fr, hfr, hord, -, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := K) Nat.prime_two hpf (by rw [hK, ← pow_mul, mul_comm])
  have hfrpow : ∀ m c, (fr ^ m) c = c ^ 2 ^ m := fun m c =>
    ringAut_pow_apply_of_frobenius hfr m c
  have hσfr : σ = fr ^ (p * f₀) := RingEquiv.ext fun c => by rw [hσ, hfrpow]
  have hδfr : δ₀ = fr ^ (3 * f₀) := RingEquiv.ext fun c => by rw [hδ₀, hfrpow]
  have hfr1 : fr ^ (3 * (p * f₀)) = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one fr
  obtain ⟨e, m, hsum, he, hm⟩ := tri_eps_data hp f₀ hp3
  set ψ : K ≃+* K := fr ^ f₀ with hψdef
  have hψ : (algebraMap K L).comp ψ.toRingHom =
      (iterateFrobenius L 2 f₀).comp (algebraMap K L) :=
    RingHom.ext fun c => by
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      rw [hψdef, hfrpow, map_pow, iterateFrobenius_def]
  set ε : K ≃+* K := fr ^ e with hεdef
  have hεψ : ε * σ ^ (if p % 3 = 1 then 1 else 2) = ψ := by
    rw [hσfr, ← pow_mul, hεdef, ← pow_add, hsum, pow_add, hfr1, mul_one]
  refine ⟨ε, fun y => triF0_triIota hp3 σ ψ ε hψ hεψ y, ?_, ?_⟩
  · have hεp : ε ^ p = 1 := by
      rw [hεdef, ← pow_mul, he, show 3 * f₀ * m * p = 3 * (p * f₀) * m by ring, pow_mul, hfr1,
        one_pow]
    have h1 := map_pow (fieldActorHom (t := TwistTag.D4) σ) ε p
    rw [hεp, map_one] at h1
    exact h1.symm
  · have hεδ : ε = δ₀ ^ m := by
      rw [hεdef, hδfr, ← pow_mul, he]
    have hb : fieldActor (t := TwistTag.D4) σ δ₀ ^ p = 1 := by
      have h1 := map_pow (fieldActorHom (t := TwistTag.D4) σ) δ₀ p
      rw [← hδ₀ord, pow_orderOf_eq_one, map_one] at h1
      rw [hδ₀ord] at h1
      exact h1.symm
    refine zpowers_eq_of_eq_pow hp hb hm ?_
    have h1 := map_pow (fieldActorHom (t := TwistTag.D4) σ) δ₀ m
    rw [← hεδ] at h1
    exact h1

end Main

end CFSG.RankThree.PartOne.TCX.Tri
