module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS10
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev B2M4 := Matrix (Fin 4) (Fin 4) (ZMod 3)

@[expose] def b2Pairing : B2M4 :=
  !![2, -2, -1, 0; -1, 2, 0, -1; -1, 0, 2, 1; 0, -1, 2, 2]

def b2ReflMat (k : Fin 4) : B2M4 :=
  fun i j => (if i = j then 1 else 0) - if i = k then b2Pairing j k else 0

@[expose] def b2TA {G : Type*} [Group G] (r : Fin 4 → G) : G := r 3 * r 2 * r 3

@[expose] def b2TB {G : Type*} [Group G] (r : Fin 4 → G) : G :=
  r 2 * r 0 * r 1 * r 3 * r 1 * r 0 * r 2

def b2WordA {G : Type*} [Group G] (r : Fin 4 → G) : G := r 0 * b2TA r * r 0 * b2TA r

def b2WordB {G : Type*} [Group G] (r : Fin 4 → G) : G := r 1 * b2TB r * r 1 * b2TB r

@[expose] def b2TAMat (R : Fin 4 → B2M4) : B2M4 := R 3 * R 2 * R 3

@[expose] def b2TBMat (R : Fin 4 → B2M4) : B2M4 :=
  R 2 * R 0 * R 1 * R 3 * R 1 * R 0 * R 2

def b2AMat (R : Fin 4 → B2M4) : B2M4 := R 0 * b2TAMat R * R 0 * b2TAMat R

def b2BMat (R : Fin 4 → B2M4) : B2M4 := R 1 * b2TBMat R * R 1 * b2TBMat R

theorem b2TAMat_mul_self : b2TAMat b2ReflMat * b2TAMat b2ReflMat = 1 := by
  decide +kernel

theorem b2TBMat_mul_self : b2TBMat b2ReflMat * b2TBMat b2ReflMat = 1 := by
  decide +kernel

theorem b2AMat_pow_three : b2AMat b2ReflMat ^ 3 = 1 := by
  decide +kernel

theorem b2BMat_pow_three : b2BMat b2ReflMat ^ 3 = 1 := by
  decide +kernel

theorem b2AMat_comm :
    b2AMat b2ReflMat * b2BMat b2ReflMat = b2BMat b2ReflMat * b2AMat b2ReflMat := by
  decide +kernel

theorem b2AMat_ne_one : b2AMat b2ReflMat ≠ 1 := by
  decide +kernel

theorem b2BMat_ne_one : b2BMat b2ReflMat ≠ 1 := by
  decide +kernel

theorem b2BMat_ne_a : b2BMat b2ReflMat ≠ b2AMat b2ReflMat := by
  decide +kernel

theorem b2BMat_ne_a_two : b2BMat b2ReflMat ≠ b2AMat b2ReflMat ^ 2 := by
  decide +kernel

@[expose] def b2ZVec : Fin 4 → ZMod 3 := ![1, 0, 2, 1]

theorem b2TAMat_mulVec_z : Matrix.mulVec (b2TAMat b2ReflMat) b2ZVec = b2ZVec := by
  decide +kernel

theorem b2TBMat_mulVec_z : Matrix.mulVec (b2TBMat b2ReflMat) b2ZVec = b2ZVec := by
  decide +kernel

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

private theorem toMatrix_mul_lin (h : Module.Basis (Fin 4) (ZMod 3) V)
    (e f : V ≃ₗ[ZMod 3] V) :
    LinearMap.toMatrix h h ((e * f).toLinearMap) =
      LinearMap.toMatrix h h e.toLinearMap * LinearMap.toMatrix h h f.toLinearMap := by
  change (LinearMap.toMatrixAlgEquiv h) ((e * f).toLinearMap) =
    (LinearMap.toMatrixAlgEquiv h) e.toLinearMap * (LinearMap.toMatrixAlgEquiv h) f.toLinearMap
  rw [show (e * f).toLinearMap = e.toLinearMap * f.toLinearMap by
      exact map_mul LinearEquiv.automorphismGroup.toLinearMapMonoidHom e f,
    LinearMap.toMatrixAlgEquiv_mul]

private theorem toMatrix_one_lin (h : Module.Basis (Fin 4) (ZMod 3) V) :
    LinearMap.toMatrix h h ((1 : V ≃ₗ[ZMod 3] V).toLinearMap) = 1 := by
  change (LinearMap.toMatrixAlgEquiv h) ((1 : V ≃ₗ[ZMod 3] V).toLinearMap) = 1
  rw [show (1 : V ≃ₗ[ZMod 3] V).toLinearMap = 1 by
      simpa [LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply] using
        map_one LinearEquiv.automorphismGroup.toLinearMapMonoidHom,
    map_one (LinearMap.toMatrixAlgEquiv h)]

private theorem toMatrix_pow_lin (h : Module.Basis (Fin 4) (ZMod 3) V)
    (e : V ≃ₗ[ZMod 3] V) (n : ℕ) :
    LinearMap.toMatrix h h ((e ^ n).toLinearMap) =
      (LinearMap.toMatrix h h e.toLinearMap) ^ n := by
  change (LinearMap.toMatrixAlgEquiv h) ((e ^ n).toLinearMap) =
    ((LinearMap.toMatrixAlgEquiv h) e.toLinearMap) ^ n
  rw [show (e ^ n).toLinearMap = (e.toLinearMap) ^ n by
      simpa [LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply] using
        map_pow LinearEquiv.automorphismGroup.toLinearMapMonoidHom e n]
  exact map_pow (LinearMap.toMatrixAlgEquiv h) e.toLinearMap n

theorem toMatrix_b2TA (h : Module.Basis (Fin 4) (ZMod 3) V)
    (r : Fin 4 → V ≃ₗ[ZMod 3] V)
    (hR : ∀ k, LinearMap.toMatrix h h (r k).toLinearMap = b2ReflMat k) :
    LinearMap.toMatrix h h (b2TA r).toLinearMap = b2TAMat b2ReflMat := by
  simp [b2TA, b2TAMat, LinearMap.toMatrix_mul, hR]

theorem toMatrix_b2TB (h : Module.Basis (Fin 4) (ZMod 3) V)
    (r : Fin 4 → V ≃ₗ[ZMod 3] V)
    (hR : ∀ k, LinearMap.toMatrix h h (r k).toLinearMap = b2ReflMat k) :
    LinearMap.toMatrix h h (b2TB r).toLinearMap = b2TBMat b2ReflMat := by
  simp [b2TB, b2TBMat, LinearMap.toMatrix_mul, hR]

theorem toMatrix_b2WordA (h : Module.Basis (Fin 4) (ZMod 3) V)
    (r : Fin 4 → V ≃ₗ[ZMod 3] V)
    (hR : ∀ k, LinearMap.toMatrix h h (r k).toLinearMap = b2ReflMat k) :
    LinearMap.toMatrix h h (b2WordA r).toLinearMap = b2AMat b2ReflMat := by
  simp [b2WordA, b2AMat, LinearMap.toMatrix_mul, toMatrix_b2TA h r hR, hR]

theorem toMatrix_b2WordB (h : Module.Basis (Fin 4) (ZMod 3) V)
    (r : Fin 4 → V ≃ₗ[ZMod 3] V)
    (hR : ∀ k, LinearMap.toMatrix h h (r k).toLinearMap = b2ReflMat k) :
    LinearMap.toMatrix h h (b2WordB r).toLinearMap = b2BMat b2ReflMat := by
  simp [b2WordB, b2BMat, LinearMap.toMatrix_mul, toMatrix_b2TB h r hR, hR]

theorem toMatrix_of_b2_reflection (h : Module.Basis (Fin 4) (ZMod 3) V)
    (α : Fin 4 → V →ₗ[ZMod 3] ZMod 3) (r : Fin 4 → V ≃ₗ[ZMod 3] V)
    (hα : ∀ i j, α i (h j) = b2Pairing j i)
    (hlin : ∀ k v, r k v = v - α k v • h k) (k : Fin 4) :
    LinearMap.toMatrix h h (r k).toLinearMap = b2ReflMat k := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (h.repr (r k (h j))) i = b2ReflMat k i j
  rw [hlin k (h j), hα k j, map_sub, map_smul]
  change (h.repr (h j)) i - b2Pairing j k * (h.repr (h k)) i = b2ReflMat k i j
  rw [Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]
  simp only [b2ReflMat]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

theorem b2TA_mul_self_of_reflection (h : Module.Basis (Fin 4) (ZMod 3) V)
    (α : Fin 4 → V →ₗ[ZMod 3] ZMod 3) (r : Fin 4 → V ≃ₗ[ZMod 3] V)
    (hα : ∀ i j, α i (h j) = b2Pairing j i)
    (hlin : ∀ k v, r k v = v - α k v • h k) :
    b2TA r * b2TA r = 1 := by
  have hR : ∀ k, LinearMap.toMatrix h h (r k).toLinearMap = b2ReflMat k :=
    fun k => toMatrix_of_b2_reflection h α r hα hlin k
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrix h h).injective
  rw [toMatrix_mul_lin, toMatrix_b2TA h r hR, b2TAMat_mul_self, toMatrix_one_lin]

theorem b2TB_mul_self_of_reflection (h : Module.Basis (Fin 4) (ZMod 3) V)
    (α : Fin 4 → V →ₗ[ZMod 3] ZMod 3) (r : Fin 4 → V ≃ₗ[ZMod 3] V)
    (hα : ∀ i j, α i (h j) = b2Pairing j i)
    (hlin : ∀ k v, r k v = v - α k v • h k) :
    b2TB r * b2TB r = 1 := by
  have hR : ∀ k, LinearMap.toMatrix h h (r k).toLinearMap = b2ReflMat k :=
    fun k => toMatrix_of_b2_reflection h α r hα hlin k
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrix h h).injective
  rw [toMatrix_mul_lin, toMatrix_b2TB h r hR, b2TBMat_mul_self, toMatrix_one_lin]

theorem b2WordA_pow_three_of_reflection (h : Module.Basis (Fin 4) (ZMod 3) V)
    (α : Fin 4 → V →ₗ[ZMod 3] ZMod 3) (r : Fin 4 → V ≃ₗ[ZMod 3] V)
    (hα : ∀ i j, α i (h j) = b2Pairing j i)
    (hlin : ∀ k v, r k v = v - α k v • h k) :
    b2WordA r ^ 3 = 1 := by
  have hR : ∀ k, LinearMap.toMatrix h h (r k).toLinearMap = b2ReflMat k :=
    fun k => toMatrix_of_b2_reflection h α r hα hlin k
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrix h h).injective
  rw [toMatrix_pow_lin, toMatrix_b2WordA h r hR, b2AMat_pow_three, toMatrix_one_lin h]

theorem b2WordB_pow_three_of_reflection (h : Module.Basis (Fin 4) (ZMod 3) V)
    (α : Fin 4 → V →ₗ[ZMod 3] ZMod 3) (r : Fin 4 → V ≃ₗ[ZMod 3] V)
    (hα : ∀ i j, α i (h j) = b2Pairing j i)
    (hlin : ∀ k v, r k v = v - α k v • h k) :
    b2WordB r ^ 3 = 1 := by
  have hR : ∀ k, LinearMap.toMatrix h h (r k).toLinearMap = b2ReflMat k :=
    fun k => toMatrix_of_b2_reflection h α r hα hlin k
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrix h h).injective
  rw [toMatrix_pow_lin, toMatrix_b2WordB h r hR, b2BMat_pow_three, toMatrix_one_lin h]

theorem b2WordA_comm_b2WordB_of_reflection (h : Module.Basis (Fin 4) (ZMod 3) V)
    (α : Fin 4 → V →ₗ[ZMod 3] ZMod 3) (r : Fin 4 → V ≃ₗ[ZMod 3] V)
    (hα : ∀ i j, α i (h j) = b2Pairing j i)
    (hlin : ∀ k v, r k v = v - α k v • h k) :
    b2WordA r * b2WordB r = b2WordB r * b2WordA r := by
  have hR : ∀ k, LinearMap.toMatrix h h (r k).toLinearMap = b2ReflMat k :=
    fun k => toMatrix_of_b2_reflection h α r hα hlin k
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrix h h).injective
  rw [toMatrix_mul_lin, toMatrix_mul_lin, toMatrix_b2WordA h r hR,
    toMatrix_b2WordB h r hR, b2AMat_comm]

theorem b2WordA_ne_one_of_reflection (h : Module.Basis (Fin 4) (ZMod 3) V)
    (α : Fin 4 → V →ₗ[ZMod 3] ZMod 3) (r : Fin 4 → V ≃ₗ[ZMod 3] V)
    (hα : ∀ i j, α i (h j) = b2Pairing j i)
    (hlin : ∀ k v, r k v = v - α k v • h k) :
    b2WordA r ≠ 1 := by
  have hR : ∀ k, LinearMap.toMatrix h h (r k).toLinearMap = b2ReflMat k :=
    fun k => toMatrix_of_b2_reflection h α r hα hlin k
  intro ha
  have hmat := congrArg (fun e : V ≃ₗ[ZMod 3] V => LinearMap.toMatrix h h e.toLinearMap) ha
  rw [toMatrix_b2WordA h r hR, toMatrix_one_lin h] at hmat
  exact b2AMat_ne_one hmat

theorem b2WordB_ne_one_of_reflection (h : Module.Basis (Fin 4) (ZMod 3) V)
    (α : Fin 4 → V →ₗ[ZMod 3] ZMod 3) (r : Fin 4 → V ≃ₗ[ZMod 3] V)
    (hα : ∀ i j, α i (h j) = b2Pairing j i)
    (hlin : ∀ k v, r k v = v - α k v • h k) :
    b2WordB r ≠ 1 := by
  have hR : ∀ k, LinearMap.toMatrix h h (r k).toLinearMap = b2ReflMat k :=
    fun k => toMatrix_of_b2_reflection h α r hα hlin k
  intro hb
  have hmat := congrArg (fun e : V ≃ₗ[ZMod 3] V => LinearMap.toMatrix h h e.toLinearMap) hb
  rw [toMatrix_b2WordB h r hR, toMatrix_one_lin h] at hmat
  exact b2BMat_ne_one hmat

theorem b2WordB_ne_b2WordA_of_reflection (h : Module.Basis (Fin 4) (ZMod 3) V)
    (α : Fin 4 → V →ₗ[ZMod 3] ZMod 3) (r : Fin 4 → V ≃ₗ[ZMod 3] V)
    (hα : ∀ i j, α i (h j) = b2Pairing j i)
    (hlin : ∀ k v, r k v = v - α k v • h k) :
    b2WordB r ≠ b2WordA r := by
  have hR : ∀ k, LinearMap.toMatrix h h (r k).toLinearMap = b2ReflMat k :=
    fun k => toMatrix_of_b2_reflection h α r hα hlin k
  intro hb
  have hmat := congrArg (fun e : V ≃ₗ[ZMod 3] V => LinearMap.toMatrix h h e.toLinearMap) hb
  rw [toMatrix_b2WordB h r hR, toMatrix_b2WordA h r hR] at hmat
  exact b2BMat_ne_a hmat

theorem b2WordB_ne_b2WordA_sq_of_reflection (h : Module.Basis (Fin 4) (ZMod 3) V)
    (α : Fin 4 → V →ₗ[ZMod 3] ZMod 3) (r : Fin 4 → V ≃ₗ[ZMod 3] V)
    (hα : ∀ i j, α i (h j) = b2Pairing j i)
    (hlin : ∀ k v, r k v = v - α k v • h k) :
    b2WordB r ≠ b2WordA r ^ 2 := by
  have hR : ∀ k, LinearMap.toMatrix h h (r k).toLinearMap = b2ReflMat k :=
    fun k => toMatrix_of_b2_reflection h α r hα hlin k
  intro hb
  have hmat := congrArg (fun e : V ≃ₗ[ZMod 3] V => LinearMap.toMatrix h h e.toLinearMap) hb
  rw [toMatrix_b2WordB h r hR, toMatrix_pow_lin, toMatrix_b2WordA h r hR] at hmat
  exact b2BMat_ne_a_two hmat

theorem qTwoBTwoForced_nine_dvd {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Module.Basis (Fin 4) (ZMod 3) V)
    (α : Fin 4 → V →ₗ[ZMod 3] ZMod 3) (r : Fin 4 → V ≃ₗ[ZMod 3] V)
    (hα : ∀ i j, α i (h j) = b2Pairing j i)
    (hlin : ∀ k v, r k v = v - α k v • h k)
    (Q : Subgroup (V ≃ₗ[ZMod 3] V))
    (hr0 : r 0 ∈ Q) (hr1 : r 1 ∈ Q)
    (htA : b2TA r ∈ Subgroup.normalizer (Q : Set (V ≃ₗ[ZMod 3] V)))
    (htB : b2TB r ∈ Subgroup.normalizer (Q : Set (V ≃ₗ[ZMod 3] V))) :
    9 ∣ Nat.card Q := by
  classical
  let : Finite V := Finite.of_equiv (Fin 4 → ZMod 3) h.equivFun.symm
  let : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V)) (by
      intro e f hef
      ext v
      exact congrFun hef v)
  have htA2 := b2TA_mul_self_of_reflection h α r hα hlin
  have htB2 := b2TB_mul_self_of_reflection h α r hα hlin
  have ha3 := b2WordA_pow_three_of_reflection h α r hα hlin
  have hb3 := b2WordB_pow_three_of_reflection h α r hα hlin
  have hcomm := b2WordA_comm_b2WordB_of_reflection h α r hα hlin
  have ha1 := b2WordA_ne_one_of_reflection h α r hα hlin
  have hb1 := b2WordB_ne_one_of_reflection h α r hα hlin
  have hba := b2WordB_ne_b2WordA_of_reflection h α r hα hlin
  have hba2 := b2WordB_ne_b2WordA_sq_of_reflection h α r hα hlin
  have haQ : b2WordA r ∈ Q := by
    have hconj : b2TA r * r 0 * (b2TA r)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp htA (r 0)).mp hr0
    have hTAinv : (b2TA r)⁻¹ = b2TA r := inv_eq_of_mul_eq_one_right htA2
    have heq : b2WordA r = r 0 * (b2TA r * r 0 * (b2TA r)⁻¹) := by
      simp only [b2WordA, hTAinv, mul_assoc]
    rw [heq]
    exact Q.mul_mem hr0 hconj
  have hbQ : b2WordB r ∈ Q := by
    have hconj : b2TB r * r 1 * (b2TB r)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp htB (r 1)).mp hr1
    have hTBinv : (b2TB r)⁻¹ = b2TB r := inv_eq_of_mul_eq_one_right htB2
    have heq : b2WordB r = r 1 * (b2TB r * r 1 * (b2TB r)⁻¹) := by
      simp only [b2WordB, hTBinv, mul_assoc]
    rw [heq]
    exact Q.mul_mem hr1 hconj
  have hsub : Subgroup.zpowers (b2WordA r) ⊔ Subgroup.zpowers (b2WordB r) ≤ Q :=
    sup_le (Subgroup.zpowers_le.mpr haQ) (Subgroup.zpowers_le.mpr hbQ)
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have horda : orderOf (b2WordA r) = 3 := orderOf_eq_prime ha3 ha1
  have hordb : orderOf (b2WordB r) = 3 := orderOf_eq_prime hb3 hb1
  have hbnot : b2WordB r ∉ Subgroup.zpowers (b2WordA r) := by
    intro hbzp
    rw [mem_zpowers_iff_mem_range_orderOf, horda] at hbzp
    obtain ⟨k, hk, hk_eq⟩ := Finset.mem_image.mp hbzp
    have hk3 : k < 3 := Finset.mem_range.mp hk
    interval_cases k
    · simp only [pow_zero] at hk_eq
      exact hb1 hk_eq.symm
    · simpa using hba hk_eq.symm
    · simpa using hba2 hk_eq.symm
  have h9 := CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F.nine_dvd_card_sup
    (G := V ≃ₗ[ZMod 3] V) (a := b2WordA r) (b := b2WordB r) horda hordb hcomm hbnot
  exact h9.trans (Subgroup.card_dvd_of_le hsub)

theorem qTwoBTwoForced_nine_dvd_mulAut {E : Type} [Group E]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive E ≃+ V) (h : Module.Basis (Fin 4) (ZMod 3) V)
    (α : Fin 4 → V →ₗ[ZMod 3] ZMod 3) (φ : Fin 4 → MulAut E)
    (hφ : ∀ k v, ggLin (p := 3) ι (φ k) v = v - α k v • h k)
    (hα : ∀ i j, α i (h j) = b2Pairing j i)
    (Q : Subgroup (MulAut E))
    (hr0 : φ 0 ∈ Q) (hr1 : φ 1 ∈ Q)
    (htA : b2TA φ ∈ Subgroup.normalizer (Q : Set (MulAut E)))
    (htB : b2TB φ ∈ Subgroup.normalizer (Q : Set (MulAut E))) :
    9 ∣ Nat.card Q := by
  let r : Fin 4 → V ≃ₗ[ZMod 3] V := fun k => ggLin (p := 3) ι (φ k)
  let Q' : Subgroup (V ≃ₗ[ZMod 3] V) := Q.map (ggLin (p := 3) ι)
  have hcard : Nat.card Q' = Nat.card Q :=
    Subgroup.card_map_of_injective (ggLin_injective (p := 3) ι)
  have hmap_norm : ∀ {x : MulAut E}, x ∈ Subgroup.normalizer (Q : Set (MulAut E)) →
      ggLin (p := 3) ι x ∈ Subgroup.normalizer (Q' : Set (V ≃ₗ[ZMod 3] V)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨x * q * x⁻¹, (hx q).mp hq, by simp [map_mul]⟩
    · rintro ⟨q, hq, hqeq⟩
      have hxinv : x⁻¹ ∈ Subgroup.normalizer (Q : Set (MulAut E)) := Subgroup.inv_mem _ hx
      have hq' : x⁻¹ * q * x ∈ Q := (Subgroup.mem_normalizer_iff.mp hxinv q).mp hq
      have hy : y = (ggLin (p := 3) ι x)⁻¹ * ggLin (p := 3) ι q * ggLin (p := 3) ι x := by
        rw [hqeq]
        group
      refine ⟨x⁻¹ * q * x, hq', ?_⟩
      rw [hy]
      simp [map_mul]
  have hr0' : r 0 ∈ Q' := Subgroup.mem_map_of_mem (ggLin (p := 3) ι) hr0
  have hr1' : r 1 ∈ Q' := Subgroup.mem_map_of_mem (ggLin (p := 3) ι) hr1
  have hTAimage : b2TA r = ggLin (p := 3) ι (b2TA φ) := by
    simp [b2TA, map_mul, r]
  have hTBimage : b2TB r = ggLin (p := 3) ι (b2TB φ) := by
    simp [b2TB, map_mul, r]
  have h9 := qTwoBTwoForced_nine_dvd (V := V) h α r hα hφ Q' hr0' hr1'
    (hTAimage ▸ hmap_norm htA) (hTBimage ▸ hmap_norm htB)
  simpa [hcard] using h9

end CFSG.StandardType

end
