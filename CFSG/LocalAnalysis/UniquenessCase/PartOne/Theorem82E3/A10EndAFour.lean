module

public import CFSG.Open.LocalVocabulary
import CFSG.Walter.Cited.HuppertBasic
import CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen

open scoped commutatorElement
open CFSG.Walter.Huppert

variable {G : Type} [Group G] [Finite G]

private lemma mulAut_apply_congr {E : Type*} [Group E] {f g : MulAut E} (h : f = g) (x : E) :
    f x = g x :=
  congrArg (fun φ : MulAut E => φ x) h

private structure KleinMul {E : Type*} [Group E] (σ₁ σ₂ : MulAut E) : Prop where
  mul1 : σ₁ * σ₁ = 1
  mul2 : σ₂ * σ₂ = 1
  mul13 : σ₁ * (σ₁ * σ₂) = σ₂
  mul21 : σ₂ * σ₁ = σ₁ * σ₂
  mul23 : σ₂ * (σ₁ * σ₂) = σ₁
  mul31 : (σ₁ * σ₂) * σ₁ = σ₂
  mul32 : (σ₁ * σ₂) * σ₂ = σ₁
  mul33 : (σ₁ * σ₂) * (σ₁ * σ₂) = 1

private structure KleinRules {E : Type*} [Group E] (σ₁ σ₂ : MulAut E) : Prop where
  sq1 : ∀ x : E, σ₁ (σ₁ x) = x
  sq2 : ∀ x : E, σ₂ (σ₂ x) = x
  cross12 : ∀ x : E, σ₁ (σ₂ x) = (σ₁ * σ₂) x
  cross21 : ∀ x : E, σ₂ (σ₁ x) = (σ₁ * σ₂) x
  cross13 : ∀ x : E, σ₁ ((σ₁ * σ₂) x) = σ₂ x
  cross23 : ∀ x : E, σ₂ ((σ₁ * σ₂) x) = σ₁ x
  cross31 : ∀ x : E, (σ₁ * σ₂) (σ₁ x) = σ₂ x
  cross32 : ∀ x : E, (σ₁ * σ₂) (σ₂ x) = σ₁ x
  cross33 : ∀ x : E, (σ₁ * σ₂) ((σ₁ * σ₂) x) = x

private structure CycleMul {E : Type*} [Group E] (σ₁ σ₂ ε : MulAut E) : Prop where
  m2ε : σ₂ * ε = ε * σ₁
  m1ε : σ₁ * ε = ε * (σ₁ * σ₂)
  m3ε : (σ₁ * σ₂) * ε = ε * σ₂
  m2ε2 : σ₂ * ε ^ 2 = ε ^ 2 * (σ₁ * σ₂)
  m3ε2 : (σ₁ * σ₂) * ε ^ 2 = ε ^ 2 * σ₁

private structure CycleRules {E : Type*} [Group E] (σ₁ σ₂ ε : MulAut E) : Prop where
  e_sq2 : ∀ x : E, σ₂ (ε x) = ε (σ₁ x)
  e_sq1 : ∀ x : E, σ₁ (ε x) = ε ((σ₁ * σ₂) x)
  e_sq3 : ∀ x : E, (σ₁ * σ₂) (ε x) = ε (σ₂ x)
  e2_sq2 : ∀ x : E, σ₂ ((ε ^ 2) x) = (ε ^ 2) ((σ₁ * σ₂) x)
  e2_sq3 : ∀ x : E, (σ₁ * σ₂) ((ε ^ 2) x) = (ε ^ 2) (σ₁ x)

private lemma kleinMul {E : Type*} [Group E] {σ₁ σ₂ : MulAut E} (h1 : σ₁ ^ 2 = 1)
    (h2 : σ₂ ^ 2 = 1) (hc : σ₁ * σ₂ = σ₂ * σ₁) : KleinMul σ₁ σ₂ := by
  have hσ₁σ₁ : σ₁ * σ₁ = 1 := by rw [← pow_two, h1]
  have hσ₂σ₂ : σ₂ * σ₂ = 1 := by rw [← pow_two, h2]
  have hσ₁σ₃ : σ₁ * (σ₁ * σ₂) = σ₂ := by rw [← mul_assoc, hσ₁σ₁, one_mul]
  have hσ₂σ₃ : σ₂ * (σ₁ * σ₂) = σ₁ := by
    rw [← mul_assoc, ← hc, mul_assoc, hσ₂σ₂, mul_one]
  have hσ₃σ₁ : (σ₁ * σ₂) * σ₁ = σ₂ := by
    rw [mul_assoc, ← hc, ← mul_assoc, hσ₁σ₁, one_mul]
  have hσ₃σ₂ : (σ₁ * σ₂) * σ₂ = σ₁ := by rw [mul_assoc, hσ₂σ₂, mul_one]
  have hσ₃σ₃ : (σ₁ * σ₂) * (σ₁ * σ₂) = 1 := by
    calc (σ₁ * σ₂) * (σ₁ * σ₂) = σ₁ * (σ₂ * σ₁) * σ₂ := by group
      _ = σ₁ * (σ₁ * σ₂) * σ₂ := by rw [hc]
      _ = (σ₁ * σ₁) * (σ₂ * σ₂) := by group
      _ = 1 := by rw [hσ₁σ₁, hσ₂σ₂, mul_one]
  exact ⟨hσ₁σ₁, hσ₂σ₂, hσ₁σ₃, hc.symm, hσ₂σ₃, hσ₃σ₁, hσ₃σ₂, hσ₃σ₃⟩

private lemma kleinRules {E : Type*} [Group E] {σ₁ σ₂ : MulAut E} (K : KleinMul σ₁ σ₂) :
    KleinRules σ₁ σ₂ where
  sq1 := fun x => by
    simpa only [MulAut.mul_apply, MulAut.one_apply] using mulAut_apply_congr K.mul1 x
  sq2 := fun x => by
    simpa only [MulAut.mul_apply, MulAut.one_apply] using mulAut_apply_congr K.mul2 x
  cross12 := fun x => rfl
  cross21 := fun x => by
    simpa only [MulAut.mul_apply] using mulAut_apply_congr K.mul21 x
  cross13 := fun x => by
    simpa only [MulAut.mul_apply] using mulAut_apply_congr K.mul13 x
  cross23 := fun x => by
    simpa only [MulAut.mul_apply] using mulAut_apply_congr K.mul23 x
  cross31 := fun x => by
    simpa only [MulAut.mul_apply] using mulAut_apply_congr K.mul31 x
  cross32 := fun x => by
    simpa only [MulAut.mul_apply] using mulAut_apply_congr K.mul32 x
  cross33 := fun x => by
    simpa only [MulAut.mul_apply, MulAut.one_apply] using mulAut_apply_congr K.mul33 x

private lemma cycleMul {E : Type*} [Group E] {σ₁ σ₂ ε : MulAut E} (K : KleinMul σ₁ σ₂)
    (he1 : ε * σ₁ * ε⁻¹ = σ₂) (he2 : ε * σ₂ * ε⁻¹ = σ₁ * σ₂) (he3 : ε ^ 3 = 1) :
    CycleMul σ₁ σ₂ ε := by
  have hm2ε : σ₂ * ε = ε * σ₁ := by
    have h := congrArg (fun f : MulAut E => f * ε) he1
    rw [mul_assoc, inv_mul_cancel, mul_one] at h
    exact h.symm
  have heσ₃ : ε * (σ₁ * σ₂) * ε⁻¹ = σ₁ := by
    have h : ε * (σ₁ * σ₂) * ε⁻¹ = (ε * σ₁ * ε⁻¹) * (ε * σ₂ * ε⁻¹) := by group
    rw [h, he1, he2, K.mul23]
  have hm1ε : σ₁ * ε = ε * (σ₁ * σ₂) := by
    have h := congrArg (fun f : MulAut E => f * ε) heσ₃
    rw [mul_assoc, inv_mul_cancel, mul_one] at h
    exact h.symm
  have hm3ε : (σ₁ * σ₂) * ε = ε * σ₂ := by
    have h := congrArg (fun f : MulAut E => f * ε) he2
    rw [mul_assoc, inv_mul_cancel, mul_one] at h
    exact h.symm
  have hm2ε2 : σ₂ * ε ^ 2 = ε ^ 2 * (σ₁ * σ₂) := by
    rw [pow_two]
    calc σ₂ * (ε * ε) = (σ₂ * ε) * ε := (mul_assoc _ _ _).symm
      _ = (ε * σ₁) * ε := by rw [hm2ε]
      _ = ε * (σ₁ * ε) := mul_assoc _ _ _
      _ = ε * (ε * (σ₁ * σ₂)) := by rw [hm1ε]
      _ = (ε * ε) * (σ₁ * σ₂) := (mul_assoc _ _ _).symm
  have hm3ε2 : (σ₁ * σ₂) * ε ^ 2 = ε ^ 2 * σ₁ := by
    rw [pow_two]
    calc (σ₁ * σ₂) * (ε * ε) = ((σ₁ * σ₂) * ε) * ε := (mul_assoc _ _ _).symm
      _ = (ε * σ₂) * ε := by rw [hm3ε]
      _ = ε * (σ₂ * ε) := mul_assoc _ _ _
      _ = ε * (ε * σ₁) := by rw [hm2ε]
      _ = (ε * ε) * σ₁ := (mul_assoc _ _ _).symm
  exact ⟨hm2ε, hm1ε, hm3ε, hm2ε2, hm3ε2⟩

private lemma cycleRules {E : Type*} [Group E] {σ₁ σ₂ ε : MulAut E} (C : CycleMul σ₁ σ₂ ε) :
    CycleRules σ₁ σ₂ ε where
  e_sq2 := fun x => by
    simpa only [MulAut.mul_apply] using mulAut_apply_congr C.m2ε x
  e_sq1 := fun x => by
    simpa only [MulAut.mul_apply] using mulAut_apply_congr C.m1ε x
  e_sq3 := fun x => by
    simpa only [MulAut.mul_apply] using mulAut_apply_congr C.m3ε x
  e2_sq2 := fun x => by
    simpa only [MulAut.mul_apply] using mulAut_apply_congr C.m2ε2 x
  e2_sq3 := fun x => by
    simpa only [MulAut.mul_apply] using mulAut_apply_congr C.m3ε2 x

private lemma cycle_norm_fixed {E : Type*} [Group E] (hcomm : ∀ x y : E, x * y = y * x)
    {ε : MulAut E} (he3 : ε ^ 3 = 1) (b : E) :
    ε (b * (ε b) * ((ε ^ 2) b)) = b * (ε b) * ((ε ^ 2) b) := by
  letI : CommGroup E := { ‹Group E› with mul_comm := hcomm }
  have hε2 : ε (ε b) = (ε ^ 2) b := by
    have h : (ε * ε) b = (ε ^ 2) b := by rw [pow_two]
    rwa [MulAut.mul_apply] at h
  have hε3' : ε ((ε ^ 2) b) = b := by
    have h : (ε * ε ^ 2) b = (1 : MulAut E) b := by
      rw [show ε * ε ^ 2 = ε ^ 3 by group, he3]
    rwa [MulAut.mul_apply, MulAut.one_apply] at h
  simp only [map_mul, hε2, hε3']
  ac_rfl

private lemma cycle_fix_two {E : Type*} [Group E] {σ₁ σ₂ ε : MulAut E}
    (hm1 : ε * σ₁ * ε⁻¹ = σ₂) (hfix : ∀ x : E, ε x = x → σ₁ x = x) :
    ∀ n : E, ε n = n → σ₂ n = n := by
  intro n hn
  have hinv : ε⁻¹ n = n := by
    have h := congrArg (fun x => ε⁻¹ x) hn
    rw [MulAut.inv_apply_self] at h
    exact h.symm
  rw [show σ₂ = ε * σ₁ * ε⁻¹ from hm1.symm]
  change ε (σ₁ (ε⁻¹ n)) = n
  rw [hinv, hfix n hn, hn]

private lemma cycle_fix_three {E : Type*} [Group E] {σ₁ σ₂ ε : MulAut E}
    (hm2 : ε * σ₂ * ε⁻¹ = σ₁ * σ₂) (hfix2 : ∀ n : E, ε n = n → σ₂ n = n) :
    ∀ n : E, ε n = n → (σ₁ * σ₂) n = n := by
  intro n hn
  have hinv : ε⁻¹ n = n := by
    have h := congrArg (fun x => ε⁻¹ x) hn
    rw [MulAut.inv_apply_self] at h
    exact h.symm
  rw [show σ₁ * σ₂ = ε * σ₂ * ε⁻¹ from hm2.symm]
  change ε (σ₂ (ε⁻¹ n)) = n
  rw [hinv, hfix2 n hn, hn]

private lemma odd_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Type*} [Group E]
    [Finite E] (hE : IsPGroup p E) : ∀ t : E, t * t = 1 → t = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro t ht
  have h2' : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hE) t
  have hcop : Nat.Coprime 2 (p ^ k) :=
    (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm |>.pow_right k
  rw [← hk] at hcop
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2' dvd_rfl)

private lemma norm_step_two {E : Type*} [Group E] (hcomm : ∀ x y : E, x * y = y * x)
    {σ₁ σ₂ ε : MulAut E} (R : CycleRules σ₁ σ₂ ε)
    (hεnorm : ∀ b : E, ε (b * (ε b) * ((ε ^ 2) b)) = b * (ε b) * ((ε ^ 2) b))
    (h2n : ∀ n : E, ε n = n → σ₂ n = n) (hodd : ∀ t : E, t * t = 1 → t = 1) {b : E}
    (hb2 : σ₂ b = b) (hb1 : σ₁ b = b⁻¹) (hb3 : (σ₁ * σ₂) b = b⁻¹) :
    b * (ε b) * ((ε ^ 2) b) = b := by
  letI : CommGroup E := { ‹Group E› with mul_comm := hcomm }
  have hfixn : σ₂ (b * (ε b) * ((ε ^ 2) b)) = b * (ε b) * ((ε ^ 2) b) :=
    h2n _ (hεnorm b)
  have hcalc : σ₂ (b * (ε b) * ((ε ^ 2) b)) = b * (ε b)⁻¹ * ((ε ^ 2) b)⁻¹ := by
    simp only [map_mul, R.e_sq2 b, R.e2_sq2 b, hb1, hb2, hb3, map_inv]
  rw [hcalc] at hfixn
  have hX : (ε b)⁻¹ * ((ε ^ 2) b)⁻¹ = (ε b) * ((ε ^ 2) b) := by
    have h : b * ((ε b)⁻¹ * ((ε ^ 2) b)⁻¹) = b * ((ε b) * ((ε ^ 2) b)) := by
      simp only [mul_assoc] at hfixn
      exact hfixn
    exact mul_left_cancel h
  have hsq : ((ε b) * ((ε ^ 2) b)) * ((ε b) * ((ε ^ 2) b)) = 1 := by
    have h2' : ((ε b) * ((ε ^ 2) b))⁻¹ = (ε b) * ((ε ^ 2) b) := by
      rw [mul_inv_rev, mul_comm ((ε ^ 2) b)⁻¹ (ε b)⁻¹]
      exact hX
    have h3 := congrArg (fun x => x * ((ε b) * ((ε ^ 2) b))) h2'
    rw [inv_mul_cancel] at h3
    exact h3.symm
  have h5 : (ε b) * ((ε ^ 2) b) = 1 := hodd _ hsq
  calc b * (ε b) * ((ε ^ 2) b) = b * ((ε b) * ((ε ^ 2) b)) := mul_assoc _ _ _
    _ = b := by rw [h5, mul_one]

private lemma norm_step_three {E : Type*} [Group E] (hcomm : ∀ x y : E, x * y = y * x)
    {σ₁ σ₂ ε : MulAut E} (R : CycleRules σ₁ σ₂ ε)
    (hεnorm : ∀ b : E, ε (b * (ε b) * ((ε ^ 2) b)) = b * (ε b) * ((ε ^ 2) b))
    (h3n : ∀ n : E, ε n = n → (σ₁ * σ₂) n = n) (hodd : ∀ t : E, t * t = 1 → t = 1) {b : E}
    (hb3 : (σ₁ * σ₂) b = b) (hb2 : σ₂ b = b⁻¹) (hb1 : σ₁ b = b⁻¹) :
    b * (ε b) * ((ε ^ 2) b) = b := by
  letI : CommGroup E := { ‹Group E› with mul_comm := hcomm }
  have hfixn : (σ₁ * σ₂) (b * (ε b) * ((ε ^ 2) b)) = b * (ε b) * ((ε ^ 2) b) :=
    h3n _ (hεnorm b)
  have hcalc : (σ₁ * σ₂) (b * (ε b) * ((ε ^ 2) b)) = b * (ε b)⁻¹ * ((ε ^ 2) b)⁻¹ := by
    simp only [map_mul, R.e_sq3 b, R.e2_sq3 b, hb1, hb2, hb3, map_inv]
  rw [hcalc] at hfixn
  have hX : (ε b)⁻¹ * ((ε ^ 2) b)⁻¹ = (ε b) * ((ε ^ 2) b) := by
    have h : b * ((ε b)⁻¹ * ((ε ^ 2) b)⁻¹) = b * ((ε b) * ((ε ^ 2) b)) := by
      simp only [mul_assoc] at hfixn
      exact hfixn
    exact mul_left_cancel h
  have hsq : ((ε b) * ((ε ^ 2) b)) * ((ε b) * ((ε ^ 2) b)) = 1 := by
    have h2' : ((ε b) * ((ε ^ 2) b))⁻¹ = (ε b) * ((ε ^ 2) b) := by
      rw [mul_inv_rev, mul_comm ((ε ^ 2) b)⁻¹ (ε b)⁻¹]
      exact hX
    have h3 := congrArg (fun x => x * ((ε b) * ((ε ^ 2) b))) h2'
    rw [inv_mul_cancel] at h3
    exact h3.symm
  have h5 : (ε b) * ((ε ^ 2) b) = 1 := hodd _ hsq
  calc b * (ε b) * ((ε ^ 2) b) = b * ((ε b) * ((ε ^ 2) b)) := mul_assoc _ _ _
    _ = b := by rw [h5, mul_one]

private lemma eq_one_of_eigenspace {E : Type*} [Group E] (hcomm : ∀ x y : E, x * y = y * x)
    {σ₁ σ₂ ε : MulAut E} (R : CycleRules σ₁ σ₂ ε)
    (hεnorm : ∀ b : E, ε (b * (ε b) * ((ε ^ 2) b)) = b * (ε b) * ((ε ^ 2) b))
    (h2n : ∀ n : E, ε n = n → σ₂ n = n) (hfix : ∀ x : E, ε x = x → σ₁ x = x)
    (hodd : ∀ t : E, t * t = 1 → t = 1) {b : E} (hb1 : σ₁ b = b⁻¹) (hb2 : σ₂ b = b)
    (hb3 : (σ₁ * σ₂) b = b⁻¹) : b = 1 := by
  have hnb : b * (ε b) * ((ε ^ 2) b) = b := norm_step_two hcomm R hεnorm h2n hodd hb2 hb1 hb3
  have hεb : ε b = b := by
    have h := hεnorm b
    rw [hnb] at h
    exact h
  have hbb : b = b⁻¹ := (hfix b hεb).symm.trans hb1
  have h2' : b * b⁻¹ = 1 := mul_inv_cancel b
  rw [← hbb] at h2'
  exact hodd b h2'

private lemma eq_one_of_eigenspace' {E : Type*} [Group E] (hcomm : ∀ x y : E, x * y = y * x)
    {σ₁ σ₂ ε : MulAut E} (R : CycleRules σ₁ σ₂ ε)
    (hεnorm : ∀ b : E, ε (b * (ε b) * ((ε ^ 2) b)) = b * (ε b) * ((ε ^ 2) b))
    (h3n : ∀ n : E, ε n = n → (σ₁ * σ₂) n = n) (hfix : ∀ x : E, ε x = x → σ₁ x = x)
    (hodd : ∀ t : E, t * t = 1 → t = 1) {b : E} (hb1 : σ₁ b = b⁻¹) (hb2 : σ₂ b = b⁻¹)
    (hb3 : (σ₁ * σ₂) b = b) : b = 1 := by
  have hnb : b * (ε b) * ((ε ^ 2) b) = b := norm_step_three hcomm R hεnorm h3n hodd hb3 hb2 hb1
  have hεb : ε b = b := by
    have h := hεnorm b
    rw [hnb] at h
    exact h
  have hbb : b = b⁻¹ := (hfix b hεb).symm.trans hb1
  have h2' : b * b⁻¹ = 1 := mul_inv_cancel b
  rw [← hbb] at h2'
  exact hodd b h2'

private lemma eigenspace_proj_one {E : Type*} [Group E] (hcomm : ∀ x y : E, x * y = y * x)
    {σ₁ σ₂ ε : MulAut E} (K : KleinRules σ₁ σ₂) (R : CycleRules σ₁ σ₂ ε)
    (hεnorm : ∀ b : E, ε (b * (ε b) * ((ε ^ 2) b)) = b * (ε b) * ((ε ^ 2) b))
    (h2n : ∀ n : E, ε n = n → σ₂ n = n) (hfix : ∀ x : E, ε x = x → σ₁ x = x)
    (hodd : ∀ t : E, t * t = 1 → t = 1) (a : E) :
    a * (σ₁ a)⁻¹ * (σ₂ a) * ((σ₁ * σ₂) a)⁻¹ = 1 := by
  letI : CommGroup E := { ‹Group E› with mul_comm := hcomm }
  refine eq_one_of_eigenspace hcomm R hεnorm h2n hfix hodd ?_ ?_ ?_
  · simp only [map_mul, map_inv, K.sq1, K.cross12, K.cross13, mul_inv_rev, inv_inv]
    ac_rfl
  · simp only [map_mul, map_inv, K.sq2, K.cross21, K.cross23, mul_inv_rev, inv_inv]
    ac_rfl
  · simp only [map_mul, map_inv, K.cross31, K.cross32, K.cross33, mul_inv_rev, inv_inv]
    ac_rfl

private lemma eigenspace_proj_two {E : Type*} [Group E] (hcomm : ∀ x y : E, x * y = y * x)
    {σ₁ σ₂ ε : MulAut E} (K : KleinRules σ₁ σ₂) (R : CycleRules σ₁ σ₂ ε)
    (hεnorm : ∀ b : E, ε (b * (ε b) * ((ε ^ 2) b)) = b * (ε b) * ((ε ^ 2) b))
    (h3n : ∀ n : E, ε n = n → (σ₁ * σ₂) n = n) (hfix : ∀ x : E, ε x = x → σ₁ x = x)
    (hodd : ∀ t : E, t * t = 1 → t = 1) (a : E) :
    a * (σ₁ a)⁻¹ * (σ₂ a)⁻¹ * ((σ₁ * σ₂) a) = 1 := by
  letI : CommGroup E := { ‹Group E› with mul_comm := hcomm }
  refine eq_one_of_eigenspace' hcomm R hεnorm h3n hfix hodd ?_ ?_ ?_
  · simp only [map_mul, map_inv, K.sq1, K.cross12, K.cross13, mul_inv_rev, inv_inv]
    ac_rfl
  · simp only [map_mul, map_inv, K.sq2, K.cross21, K.cross23, mul_inv_rev, inv_inv]
    ac_rfl
  · simp only [map_mul, map_inv, K.cross31, K.cross32, K.cross33, mul_inv_rev, inv_inv]
    ac_rfl

private lemma eq_one_of_projections {E : Type*} [Group E] (hcomm : ∀ x y : E, x * y = y * x)
    {σ₁ σ₂ : MulAut E} (hodd : ∀ t : E, t * t = 1 → t = 1)
    (h1' : ∀ a : E, a * (σ₁ a)⁻¹ * (σ₂ a) * ((σ₁ * σ₂) a)⁻¹ = 1)
    (h2' : ∀ a : E, a * (σ₁ a)⁻¹ * (σ₂ a)⁻¹ * ((σ₁ * σ₂) a) = 1) : σ₁ = 1 := by
  letI : CommGroup E := { ‹Group E› with mul_comm := hcomm }
  refine MulEquiv.ext fun a => ?_
  have hf1 : a * (σ₁ a)⁻¹ * (σ₂ a) = (σ₁ * σ₂) a := mul_inv_eq_one.mp (h1' a)
  have hf2 : a * (σ₁ a)⁻¹ * (σ₂ a)⁻¹ = ((σ₁ * σ₂) a)⁻¹ := by
    have h : ((σ₁ * σ₂) a) * (a * (σ₁ a)⁻¹ * (σ₂ a)⁻¹) = 1 := by
      rw [mul_comm]
      exact h2' a
    exact eq_inv_of_mul_eq_one_right h
  have hC : a * (σ₁ a)⁻¹ = ((σ₁ * σ₂) a)⁻¹ * (σ₂ a) := by
    have h := congrArg (fun x => x * (σ₂ a)) hf2
    rwa [mul_assoc, inv_mul_cancel, mul_one] at h
  have hD : a * (σ₁ a)⁻¹ = (σ₁ * σ₂) a * (σ₂ a)⁻¹ := by
    have h := congrArg (fun x => x * (σ₂ a)⁻¹) hf1
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h
  have hsq : (a * (σ₁ a)⁻¹) * (a * (σ₁ a)⁻¹) = 1 := by
    nth_rewrite 2 [hC]
    rw [hD]
    rw [show ((σ₁ * σ₂) a * (σ₂ a)⁻¹) * (((σ₁ * σ₂) a)⁻¹ * (σ₂ a))
        = ((σ₁ * σ₂) a * ((σ₁ * σ₂) a)⁻¹) * ((σ₂ a)⁻¹ * (σ₂ a)) by ac_rfl]
    rw [mul_inv_cancel, one_mul, inv_mul_cancel]
  have hfin : a * (σ₁ a)⁻¹ = 1 := hodd _ hsq
  rw [mul_inv_eq_one] at hfin
  exact hfin.symm

theorem a4_aut_eq_one_of_commutative {E : Type*} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hE : IsPGroup p E) (hcomm : ∀ x y : E, x * y = y * x)
    {σ₁ σ₂ ε : MulAut E} (h1 : σ₁ ^ 2 = 1) (h2 : σ₂ ^ 2 = 1) (hc : σ₁ * σ₂ = σ₂ * σ₁)
    (he1 : ε * σ₁ * ε⁻¹ = σ₂) (he2 : ε * σ₂ * ε⁻¹ = σ₁ * σ₂) (he3 : ε ^ 3 = 1)
    (hfix : ∀ x : E, ε x = x → σ₁ x = x) : σ₁ = 1 := by
  have KM := kleinMul h1 h2 hc
  have K := kleinRules KM
  have R := cycleRules (cycleMul KM he1 he2 he3)
  have hεnorm := cycle_norm_fixed hcomm he3
  have h2n := cycle_fix_two he1 hfix
  have hodd := odd_of_isPGroup hp hp2 hE
  exact eq_one_of_projections hcomm hodd
    (eigenspace_proj_one hcomm K R hεnorm h2n hfix hodd)
    (eigenspace_proj_two hcomm K R hεnorm (cycle_fix_three he2 h2n) hfix hodd)

private lemma frattini_lift_fixed {E : Type*} [Group E] [Finite E] {σ₁ σ₂ ε : MulAut E}
    (he3 : ε ^ 3 = 1) (hΦinv : ∀ n ∈ frattini E, ε n ∈ frattini E)
    (hΦ3 : ¬ 3 ∣ Nat.card ↥(frattini E))
    (hfix : ∀ x : E, ε x = x → σ₁ x = x ∧ σ₂ x = x) :
    ∀ z : E ⧸ frattini E, frattiniAut E ε z = z → frattiniAut E σ₁ z = z := by
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini E) z
  have hmem : x⁻¹ * (ε x) ∈ frattini E := by
    simp only [QuotientGroup.mk'_apply, frattiniAut_mk] at hz
    have h : (x : E ⧸ frattini E) = ((ε x : E) : E ⧸ frattini E) := hz.symm
    exact (QuotientGroup.eq (s := frattini E)).mp h
  have hx : ε x * x⁻¹ ∈ frattini E := by
    have hconj := Subgroup.Normal.conj_mem (inferInstance : (frattini E).Normal)
      (x⁻¹ * ε x) hmem x
    have e : x * (x⁻¹ * ε x) * x⁻¹ = ε x * x⁻¹ := by group
    rwa [e] at hconj
  obtain ⟨y, hyx, hεy⟩ :=
    CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.fixed_lift
      ε he3 (frattini E) inferInstance hΦinv hΦ3 x hx
  have hzy : (y : E ⧸ frattini E) = (x : E ⧸ frattini E) := by
    have hmem2 : x⁻¹ * y ∈ frattini E := by
      have h := Subgroup.Normal.conj_mem (inferInstance : (frattini E).Normal)
        (y * x⁻¹) hyx x⁻¹
      have e : x⁻¹ * (y * x⁻¹) * (x⁻¹)⁻¹ = x⁻¹ * y := by group
      rwa [e] at h
    exact (QuotientGroup.eq (s := frattini E)).mpr (by
      have h := (frattini E).inv_mem hmem2
      rwa [mul_inv_rev, inv_inv] at h)
  calc frattiniAut E σ₁ (x : E ⧸ frattini E) = frattiniAut E σ₁ (y : E ⧸ frattini E) := by
        rw [hzy]
    _ = ((σ₁ y : E) : E ⧸ frattini E) := frattiniAut_mk σ₁ y
    _ = (y : E ⧸ frattini E) := by rw [(hfix y hεy).1]
    _ = (x : E ⧸ frattini E) := hzy

theorem a4_aut_eq_one {E : Type*} [Group E] [Finite E] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hE : IsPGroup p E)
    {σ₁ σ₂ ε : MulAut E} (h1 : σ₁ ^ 2 = 1) (h2 : σ₂ ^ 2 = 1) (hc : σ₁ * σ₂ = σ₂ * σ₁)
    (he1 : ε * σ₁ * ε⁻¹ = σ₂) (he2 : ε * σ₂ * ε⁻¹ = σ₁ * σ₂) (he3 : ε ^ 3 = 1)
    (hfix : ∀ x : E, ε x = x → σ₁ x = x ∧ σ₂ x = x) : σ₁ = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hchar : (frattini E).Characteristic := inferInstance
  have hΦinv : ∀ n ∈ frattini E, ε n ∈ frattini E := by
    intro n hn
    have h := Subgroup.characteristic_iff_map_eq.mp hchar ε
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hn
  have hΦ3 : ¬ 3 ∣ Nat.card ↥(frattini E) := by
    obtain ⟨k, hk⟩ := (hE.to_subgroup (frattini E)).exists_card_eq
    rw [hk]
    intro h
    have h3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow h
    rcases (Nat.dvd_prime hp).mp h3 with h1 | h1
    · norm_num at h1
    · exact hp3 h1.symm
  have hcomm : ∀ a b : E ⧸ frattini E, a * b = b * a :=
    (CFSG.Walter.Huppert.frattini_quotient_facts hE).1
  have hlift := frattini_lift_fixed he3 hΦinv hΦ3 hfix
  have hq : frattiniAut E σ₁ = 1 :=
    a4_aut_eq_one_of_commutative (E := E ⧸ frattini E) (p := p)
      (hp := hp) (hp2 := hp2) (hE := hE.to_quotient (frattini E)) (hcomm := hcomm)
      (σ₁ := frattiniAut E σ₁) (σ₂ := frattiniAut E σ₂) (ε := frattiniAut E ε)
      (h1 := by rw [← map_pow, h1, map_one])
      (h2 := by rw [← map_pow, h2, map_one])
      (hc := by rw [← map_mul, ← map_mul, hc])
      (he1 := by rw [← map_mul, ← map_inv, ← map_mul, he1])
      (he2 := by rw [← map_mul, ← map_inv, ← map_mul, he2, map_mul])
      (he3 := by rw [← map_pow, he3, map_one])
      (hfix := hlift)
  have hcop : Nat.Coprime p (orderOf σ₁) := by
    have h2' : orderOf σ₁ ∣ 2 := orderOf_dvd_of_pow_eq_one h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h2' with h | h
    · rw [h]; exact Nat.coprime_one_right p
    · rw [h]; exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  exact eq_one_of_frattiniAut_eq_one hE hcop hq

private structure A4Aut {E : Type*} [Group E] (σ₁ σ₂ ε : MulAut E) : Prop where
  h1 : σ₁ ^ 2 = 1
  h2 : σ₂ ^ 2 = 1
  hc : σ₁ * σ₂ = σ₂ * σ₁
  he1 : ε * σ₁ * ε⁻¹ = σ₂
  he2 : ε * σ₂ * ε⁻¹ = σ₁ * σ₂
  he3 : ε ^ 3 = 1

private structure NormalizerData (X : Subgroup G) (k₁ k₂ e : G)
    (hk₁ : k₁ ∈ Subgroup.normalizer (X : Set G)) (hk₂ : k₂ ∈ Subgroup.normalizer (X : Set G))
    (heX : e ∈ Subgroup.normalizer (X : Set G)) : Prop where
  m1 : (⟨k₁, hk₁⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 2 = 1
  m2 : (⟨k₂, hk₂⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 2 = 1
  m12 : (⟨k₁, hk₁⟩ : ↥(Subgroup.normalizer (X : Set G))) * ⟨k₂, hk₂⟩ =
    ⟨k₂, hk₂⟩ * ⟨k₁, hk₁⟩
  me1 : (⟨e, heX⟩ : ↥(Subgroup.normalizer (X : Set G))) * ⟨k₁, hk₁⟩ *
    (⟨e, heX⟩ : ↥(Subgroup.normalizer (X : Set G)))⁻¹ = ⟨k₂, hk₂⟩
  me2 : (⟨e, heX⟩ : ↥(Subgroup.normalizer (X : Set G))) * ⟨k₂, hk₂⟩ *
    (⟨e, heX⟩ : ↥(Subgroup.normalizer (X : Set G)))⁻¹ = ⟨k₁, hk₁⟩ * ⟨k₂, hk₂⟩
  me3 : (⟨e, heX⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 3 = 1

private lemma normalizerData {X : Subgroup G} {k₁ k₂ e : G}
    (hk₁ : k₁ ∈ Subgroup.normalizer (X : Set G)) (hk₂ : k₂ ∈ Subgroup.normalizer (X : Set G))
    (heX : e ∈ Subgroup.normalizer (X : Set G))
    (hk1 : k₁ ^ 2 = 1) (hk2 : k₂ ^ 2 = 1) (hcomm : k₁ * k₂ = k₂ * k₁)
    (he1 : e * k₁ * e⁻¹ = k₂) (he2 : e * k₂ * e⁻¹ = k₁ * k₂) (he3 : e ^ 3 = 1) :
    NormalizerData X k₁ k₂ e hk₁ hk₂ heX := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, hk1]
    rfl
  · apply Subtype.ext
    rw [Subgroup.coe_pow, hk2]
    rfl
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcomm]
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, he1]
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, he2]
  · apply Subtype.ext
    rw [Subgroup.coe_pow, he3]
    rfl

private lemma conjData {X : Subgroup G} {k₁ k₂ e : G}
    (hk₁ : k₁ ∈ Subgroup.normalizer (X : Set G)) (hk₂ : k₂ ∈ Subgroup.normalizer (X : Set G))
    (heX : e ∈ Subgroup.normalizer (X : Set G)) (N : NormalizerData X k₁ k₂ e hk₁ hk₂ heX) :
    A4Aut ((Subgroup.normalizerMonoidHom X) ⟨k₁, hk₁⟩)
      ((Subgroup.normalizerMonoidHom X) ⟨k₂, hk₂⟩)
      ((Subgroup.normalizerMonoidHom X) ⟨e, heX⟩) where
  h1 := by rw [← map_pow, N.m1, map_one]
  h2 := by rw [← map_pow, N.m2, map_one]
  hc := by rw [← map_mul, ← map_mul, N.m12]
  he1 := by rw [← map_mul, ← map_inv, ← map_mul, N.me1]
  he2 := by rw [← map_mul, ← map_inv, ← map_mul, N.me2, map_mul]
  he3 := by rw [← map_pow, N.me3, map_one]

private lemma conjData_fixed {X : Subgroup G} {k₁ k₂ e : G} {σ₁ σ₂ ε : MulAut ↥X}
    (hσ₁ : ∀ x : ↥X, ((σ₁ x : ↥X) : G) = k₁ * (x : G) * k₁⁻¹)
    (hσ₂ : ∀ x : ↥X, ((σ₂ x : ↥X) : G) = k₂ * (x : G) * k₂⁻¹)
    (hε : ∀ x : ↥X, ((ε x : ↥X) : G) = e * (x : G) * e⁻¹)
    (hfix : X ⊓ Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.centralizer ({k₁, k₂} : Set G)) :
    ∀ x : ↥X, ε x = x → σ₁ x = x ∧ σ₂ x = x := by
  intro x hx
  have hxG : e * (x : G) * e⁻¹ = (x : G) := by
    have h := congrArg (fun y : ↥X => (y : G)) hx
    rwa [hε] at h
  have hxmem : (x : G) ∈ X ⊓ Subgroup.centralizer ({e} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [mul_inv_eq_iff_eq_mul] at hxG
    exact hxG.symm
  have hcen := hfix hxmem
  have hx1 : k₁ * (x : G) = (x : G) * k₁ :=
    Subgroup.mem_centralizer_iff.mp hcen k₁ (by simp)
  have hx2 : k₂ * (x : G) = (x : G) * k₂ :=
    Subgroup.mem_centralizer_iff.mp hcen k₂ (by simp)
  constructor
  · apply Subtype.ext
    rw [hσ₁, hx1, mul_assoc, mul_inv_cancel, mul_one]
  · apply Subtype.ext
    rw [hσ₂, hx2, mul_assoc, mul_inv_cancel, mul_one]

theorem centralizes_of_a4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {X : Subgroup G} {k₁ k₂ e : G} (hX : IsPGroup p X)
    (hk₁ : k₁ ∈ Subgroup.normalizer (X : Set G)) (hk₂ : k₂ ∈ Subgroup.normalizer (X : Set G))
    (heX : e ∈ Subgroup.normalizer (X : Set G))
    (hk1 : k₁ ^ 2 = 1) (hk2 : k₂ ^ 2 = 1) (hcomm : k₁ * k₂ = k₂ * k₁)
    (he1 : e * k₁ * e⁻¹ = k₂) (he2 : e * k₂ * e⁻¹ = k₁ * k₂) (he3 : e ^ 3 = 1)
    (hfix : X ⊓ Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.centralizer ({k₁, k₂} : Set G)) :
    k₁ ∈ Subgroup.centralizer (X : Set G) := by
  classical
  let σ₁ : MulAut ↥X := (Subgroup.normalizerMonoidHom X) ⟨k₁, hk₁⟩
  let σ₂ : MulAut ↥X := (Subgroup.normalizerMonoidHom X) ⟨k₂, hk₂⟩
  let ε : MulAut ↥X := (Subgroup.normalizerMonoidHom X) ⟨e, heX⟩
  have hσ₁ : ∀ x : ↥X, ((σ₁ x : ↥X) : G) = k₁ * (x : G) * k₁⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨k₁, hk₁⟩ x
  have hσ₂ : ∀ x : ↥X, ((σ₂ x : ↥X) : G) = k₂ * (x : G) * k₂⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨k₂, hk₂⟩ x
  have hε : ∀ x : ↥X, ((ε x : ↥X) : G) = e * (x : G) * e⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨e, heX⟩ x
  have R := conjData hk₁ hk₂ heX (normalizerData hk₁ hk₂ heX hk1 hk2 hcomm he1 he2 he3)
  have hσ : σ₁ = 1 := a4_aut_eq_one hp hp2 hp3 hX R.h1 R.h2 R.hc R.he1 R.he2 R.he3
    (conjData_fixed hσ₁ hσ₂ hε hfix)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hpt : σ₁ ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hσ, MulAut.one_apply]
  have h' := congrArg (fun y : ↥X => (y : G)) hpt
  rw [hσ₁] at h'
  rw [mul_inv_eq_iff_eq_mul] at h'
  exact h'.symm

private lemma isElemAbelian_comm {W : Subgroup G} (hW : CFSG.Open.IsElemAbelian 2 W) :
    ∀ x y : ↥W, x * y = y * x :=
  hW.1.is_comm.comm

private lemma norm_fixed_sigma {M : Type*} [Group M] (hcomm : ∀ x y : M, x * y = y * x)
    {σ : MulAut M} (hσ3 : σ ^ 3 = 1) (x : M) :
    x * σ x * (σ ^ 2) x = σ x * σ (σ x) * (σ ^ 2) (σ x) := by
  letI : CommGroup M := { ‹Group M› with mul_comm := hcomm }
  have h1 : σ (σ x) = (σ ^ 2) x := by
    have h : (σ * σ) x = (σ ^ 2) x := by rw [pow_two]
    rwa [MulAut.mul_apply] at h
  have h2 : (σ ^ 2) (σ x) = x := by
    have h : (σ * σ ^ 2) x = (1 : MulAut M) x := by
      rw [show σ * σ ^ 2 = σ ^ 3 by group, hσ3]
    rwa [MulAut.mul_apply, MulAut.one_apply] at h
  rw [h1, h2]
  ac_rfl

private lemma norm_fixed_sigma_sq {M : Type*} [Group M] (hcomm : ∀ x y : M, x * y = y * x)
    {σ : MulAut M} (hσ3 : σ ^ 3 = 1) (x : M) :
    x * σ x * (σ ^ 2) x = (σ ^ 2) x * σ ((σ ^ 2) x) * (σ ^ 2) ((σ ^ 2) x) := by
  letI : CommGroup M := { ‹Group M› with mul_comm := hcomm }
  have h1 : σ ((σ ^ 2) x) = x := by
    have h : (σ * σ ^ 2) x = (1 : MulAut M) x := by
      rw [show σ * σ ^ 2 = σ ^ 3 by group, hσ3]
    rwa [MulAut.mul_apply, MulAut.one_apply] at h
  have h2 : (σ ^ 2) ((σ ^ 2) x) = σ x := by
    have h4 : σ ^ 2 * σ ^ 2 = σ ^ 3 * σ := by group
    calc (σ ^ 2) ((σ ^ 2) x) = (σ ^ 2 * σ ^ 2) x := rfl
      _ = (σ ^ 3 * σ) x := by rw [h4]
      _ = (σ ^ 3) (σ x) := rfl
      _ = σ x := by rw [hσ3, MulAut.one_apply]
  rw [h1, h2]
  ac_rfl

private noncomputable def normHom (W : Subgroup G) (e : G)
    (heW : e ∈ Subgroup.normalizer (W : Set G))
    (hcomm : ∀ x y : ↥W, x * y = y * x) : ↥W →* ↥W := by
  letI : CommGroup ↥W := { (inferInstance : Group ↥W) with mul_comm := hcomm }
  refine
    { toFun := fun x => x * ((Subgroup.normalizerMonoidHom W) ⟨e, heW⟩ x) *
        (((Subgroup.normalizerMonoidHom W) ⟨e, heW⟩) ^ 2) x
      map_one' := by simp
      map_mul' := fun x y => by simp only [map_mul]; ac_rfl }

private lemma normHom_apply {W : Subgroup G} {e : G} (heW : e ∈ Subgroup.normalizer (W : Set G))
    (hcomm : ∀ x y : ↥W, x * y = y * x) (x : ↥W) :
    normHom W e heW hcomm x = x * ((Subgroup.normalizerMonoidHom W) ⟨e, heW⟩ x) *
      (((Subgroup.normalizerMonoidHom W) ⟨e, heW⟩) ^ 2) x :=
  rfl

private lemma normalizerConj_pow_three {W : Subgroup G} {e : G}
    (heW : e ∈ Subgroup.normalizer (W : Set G)) (he : e ^ 3 = 1) :
    ((Subgroup.normalizerMonoidHom W) ⟨e, heW⟩) ^ 3 = 1 := by
  have h : (⟨e, heW⟩ : ↥(Subgroup.normalizer (W : Set G))) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, he]
    rfl
  rw [← map_pow, h, map_one]

private lemma normalizerConj_pow_two_apply {W : Subgroup G} {e : G}
    (heW : e ∈ Subgroup.normalizer (W : Set G)) (x : ↥W) :
    ((((Subgroup.normalizerMonoidHom W) ⟨e, heW⟩) ^ 2) x : G) = e ^ 2 * (x : G) * (e ^ 2)⁻¹ := by
  have h : ((Subgroup.normalizerMonoidHom W) ⟨e, heW⟩) ^ 2 =
      (Subgroup.normalizerMonoidHom W)
        ((⟨e, heW⟩ : ↥(Subgroup.normalizer (W : Set G))) ^ 2) := by
    rw [map_pow]
  rw [h, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_pow]

private lemma normHom_sigma {W : Subgroup G} {e : G} (heW : e ∈ Subgroup.normalizer (W : Set G))
    (hcomm : ∀ x y : ↥W, x * y = y * x) (he : e ^ 3 = 1) (x : ↥W) :
    normHom W e heW hcomm (((Subgroup.normalizerMonoidHom W) ⟨e, heW⟩) x) =
      normHom W e heW hcomm x := by
  rw [normHom_apply heW hcomm (((Subgroup.normalizerMonoidHom W) ⟨e, heW⟩) x),
    normHom_apply heW hcomm x]
  exact (norm_fixed_sigma hcomm (normalizerConj_pow_three heW he) x).symm

private lemma normHom_sigma_sq {W : Subgroup G} {e : G} (heW : e ∈ Subgroup.normalizer (W : Set G))
    (hcomm : ∀ x y : ↥W, x * y = y * x) (he : e ^ 3 = 1) (x : ↥W) :
    normHom W e heW hcomm ((((Subgroup.normalizerMonoidHom W) ⟨e, heW⟩) ^ 2) x) =
      normHom W e heW hcomm x := by
  rw [normHom_apply heW hcomm ((((Subgroup.normalizerMonoidHom W) ⟨e, heW⟩) ^ 2) x),
    normHom_apply heW hcomm x]
  exact (norm_fixed_sigma_sq hcomm (normalizerConj_pow_three heW he) x).symm

private lemma norm_commutator_one {W : Subgroup G} {e : G}
    (hW : CFSG.Open.IsElemAbelian 2 W) (heW : e ∈ Subgroup.normalizer (W : Set G))
    (he : e ^ 3 = 1) {w : G} (hw : w ∈ W) :
    ⁅w, e⁆ ∈ (normHom W e heW (isElemAbelian_comm hW)).ker.map W.subtype := by
  have hcomm := isElemAbelian_comm hW
  have hσw : e * w * e⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp heW w).mp hw
  have hmem : ⁅w, e⁆ ∈ W := by
    rw [commutatorElement_def, show w * e * w⁻¹ * e⁻¹ = w * (e * w * e⁻¹)⁻¹ by group]
    exact W.mul_mem hw (W.inv_mem hσw)
  refine Subgroup.mem_map.mpr ⟨⟨⁅w, e⁆, hmem⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker]
  have h1 : (⟨⁅w, e⁆, hmem⟩ : ↥W) =
      ⟨w, hw⟩ * (((Subgroup.normalizerMonoidHom W) ⟨e, heW⟩) ⟨w, hw⟩)⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe]
    show ⁅w, e⁆ = w * (e * w * e⁻¹)⁻¹
    rw [commutatorElement_def]
    group
  rw [h1, map_mul, map_inv, normHom_sigma heW hcomm he ⟨w, hw⟩]
  exact mul_inv_cancel _

private lemma norm_commutator_two {W : Subgroup G} {e : G}
    (hW : CFSG.Open.IsElemAbelian 2 W) (heW : e ∈ Subgroup.normalizer (W : Set G))
    (he : e ^ 3 = 1) {w : G} (hw : w ∈ W) :
    ⁅w, e ^ 2⁆ ∈ (normHom W e heW (isElemAbelian_comm hW)).ker.map W.subtype := by
  have hcomm := isElemAbelian_comm hW
  have hσ2w : e ^ 2 * w * (e ^ 2)⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (W : Set G)).pow_mem heW 2) w).mp hw
  have hmem : ⁅w, e ^ 2⁆ ∈ W := by
    rw [commutatorElement_def, show w * e ^ 2 * w⁻¹ * (e ^ 2)⁻¹ =
      w * (e ^ 2 * w * (e ^ 2)⁻¹)⁻¹ by group]
    exact W.mul_mem hw (W.inv_mem hσ2w)
  refine Subgroup.mem_map.mpr ⟨⟨⁅w, e ^ 2⁆, hmem⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker]
  have h1 : (⟨⁅w, e ^ 2⁆, hmem⟩ : ↥W) =
      ⟨w, hw⟩ * ((((Subgroup.normalizerMonoidHom W) ⟨e, heW⟩) ^ 2) ⟨w, hw⟩)⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, normalizerConj_pow_two_apply heW]
    show ⁅w, e ^ 2⁆ = w * (e ^ 2 * w * (e ^ 2)⁻¹)⁻¹
    rw [commutatorElement_def]
    group
  rw [h1, map_mul, map_inv, normHom_sigma_sq heW hcomm he ⟨w, hw⟩]
  exact mul_inv_cancel _

private lemma norm_commutator_le {W : Subgroup G} {e : G}
    (hW : CFSG.Open.IsElemAbelian 2 W) (heW : e ∈ Subgroup.normalizer (W : Set G))
    (he : e ^ 3 = 1) :
    ⁅W, Subgroup.zpowers e⁆ ≤ (normHom W e heW (isElemAbelian_comm hW)).ker.map W.subtype := by
  rw [Subgroup.commutator_le]
  intro w hw b hb
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have h1 : e ^ j = e ^ (j % 3) := zpow_eq_zpow_emod' j he
  rw [h1]
  have h2 : 0 ≤ j % 3 := Int.emod_nonneg j (by norm_num)
  have h3 : j % 3 < 3 := Int.emod_lt_of_pos j (by norm_num)
  have h4 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases h4 with h | h | h
  · rw [h, zpow_zero, commutatorElement_one_right]
    exact Subgroup.one_mem _
  · rw [h, zpow_one]
    exact norm_commutator_one hW heW he hw
  · rw [h, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact norm_commutator_two hW heW he hw

private lemma norm_eq_one_of_mem {W : Subgroup G} {e : G}
    (hW : CFSG.Open.IsElemAbelian 2 W) (heW : e ∈ Subgroup.normalizer (W : Set G))
    (he : e ^ 3 = 1) {k : G} (hk : k ∈ ⁅W, Subgroup.zpowers e⁆) :
    k * (e * k * e⁻¹) * (e ^ 2 * k * (e ^ 2)⁻¹) = 1 := by
  have hcomm := isElemAbelian_comm hW
  have hkT : k ∈ (normHom W e heW hcomm).ker.map W.subtype := norm_commutator_le hW heW he hk
  obtain ⟨x, hxker, hxeq⟩ := Subgroup.mem_map.mp hkT
  have hxnorm : normHom W e heW hcomm x = 1 := by rwa [MonoidHom.mem_ker] at hxker
  have h := congrArg (fun y : ↥W => (y : G)) hxnorm
  simp only [normHom_apply, Subgroup.coe_mul, Subgroup.normalizerMonoidHom_apply_apply_coe,
    normalizerConj_pow_two_apply heW, Subgroup.coe_one] at h
  rw [show (x : G) = k from hxeq] at h
  exact h

private lemma centralizes_of_mem_commutator {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {X W : Subgroup G} {e : G} (hX : IsPGroup p X) (hW : CFSG.Open.IsElemAbelian 2 W)
    (he : e ^ 3 = 1) (heW : e ∈ Subgroup.normalizer (W : Set G))
    (heX : e ∈ Subgroup.normalizer (X : Set G)) (hWX : W ≤ Subgroup.normalizer (X : Set G))
    (hfix : X ⊓ Subgroup.centralizer ({e} : Set G) ≤ Subgroup.centralizer (W : Set G))
    {k : G} (hk : k ∈ ⁅W, Subgroup.zpowers e⁆) : k ∈ Subgroup.centralizer (X : Set G) := by
  have hKW : ⁅W, Subgroup.zpowers e⁆ ≤ W := by
    rw [← Subgroup.le_normalizer_iff_commutator_le_left]
    exact Subgroup.zpowers_le.mpr heW
  have hkW : k ∈ W := hKW hk
  have hnorm := norm_eq_one_of_mem hW heW he hk
  have hksq : k ^ 2 = 1 := hW.2 k hkW
  have hk2 : e * k * e⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp heW k).mp hkW
  have hk2sq : (e * k * e⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hksq, mul_one, mul_inv_cancel]
  have hkk2 : k * (e * k * e⁻¹) = (e * k * e⁻¹) * k := by
    have hc : (⟨k, hkW⟩ : ↥W) * ⟨e * k * e⁻¹, hk2⟩ = ⟨e * k * e⁻¹, hk2⟩ * ⟨k, hkW⟩ :=
      hW.1.is_comm.comm _ _
    exact congrArg (fun y : ↥W => (y : G)) hc
  have hkk2sq : (k * (e * k * e⁻¹)) ^ 2 = 1 := by
    have hc : Commute k (e * k * e⁻¹) := hkk2
    calc (k * (e * k * e⁻¹)) ^ 2 = k ^ 2 * (e * k * e⁻¹) ^ 2 := hc.mul_pow 2
      _ = 1 := by rw [hksq, hk2sq, mul_one]
  have hk3eq : e * (e * k * e⁻¹) * e⁻¹ = k * (e * k * e⁻¹) := by
    have h1 : e * (e * k * e⁻¹) * e⁻¹ = e ^ 2 * k * (e ^ 2)⁻¹ := by
      rw [show e ^ 2 = e * e from pow_two e, show (e * e)⁻¹ = e⁻¹ * e⁻¹ from mul_inv_rev e e]
      group
    rw [h1]
    have h2 : e ^ 2 * k * (e ^ 2)⁻¹ = (k * (e * k * e⁻¹))⁻¹ :=
      eq_inv_of_mul_eq_one_right hnorm
    have hsq' : k * (e * k * e⁻¹) * (k * (e * k * e⁻¹)) = 1 := by
      rw [← pow_two]
      exact hkk2sq
    rw [h2, inv_eq_of_mul_eq_one_right hsq']
  have hfix2 : X ⊓ Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.centralizer ({k, e * k * e⁻¹} : Set G) := by
    intro y hy
    have hyW := hfix hy
    rw [Subgroup.mem_centralizer_iff] at hyW ⊢
    intro z hz
    rcases (by simpa using hz : z = k ∨ z = e * k * e⁻¹) with h | h
    · rw [h]; exact hyW k hkW
    · rw [h]; exact hyW _ hk2
  have hk1N : k ∈ Subgroup.normalizer (X : Set G) := hWX hkW
  have hk2N : e * k * e⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normalizer (X : Set G)).mul_mem
      ((Subgroup.normalizer (X : Set G)).mul_mem heX hk1N)
      ((Subgroup.normalizer (X : Set G)).inv_mem heX)
  exact centralizes_of_a4 (k₁ := k) (k₂ := e * k * e⁻¹) hp hp2 hp3 hX hk1N hk2N heX
    hksq hk2sq hkk2 rfl hk3eq he hfix2

theorem commutator_zpowers_le_centralizer {p : ℕ} [Fact p.Prime] (hp : Nat.Coprime p 6)
    {X W : Subgroup G} {e : G} (hX : IsPGroup p X) (hW : CFSG.Open.IsElemAbelian 2 W)
    (he : e ^ 3 = 1) (heW : e ∈ Subgroup.normalizer (W : Set G))
    (heX : e ∈ Subgroup.normalizer (X : Set G)) (hWX : W ≤ Subgroup.normalizer (X : Set G))
    (hfix : X ⊓ Subgroup.centralizer ({e} : Set G) ≤ Subgroup.centralizer (W : Set G)) :
    ⁅W, Subgroup.zpowers e⁆ ≤ Subgroup.centralizer (X : Set G) := by
  classical
  have hpp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    have := hp
    norm_num at this
  have hp3 : p ≠ 3 := by
    rintro rfl
    have := hp
    norm_num at this
  intro k hk
  exact centralizes_of_mem_commutator hpp hp2 hp3 hX hW he heW heX hWX hfix hk

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen
