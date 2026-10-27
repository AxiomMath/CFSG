module

public import CFSG.Sporadic.Co1.Cover.Section
public import CFSG.Sporadic.Co1.Cover.Cocycle
public import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.Sporadic.Co1.Cover

open Matrix CFSG.Monster.Schur SemidirectProduct

@[expose] def phiOf {n : ℕ} {P : Type*} [Group P]
    (ρ : P →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))) :
    P →* MulAut (Multiplicative (Fin n → ZMod 2)) where
  toFun p := (ρ p).toAddEquiv.toMultiplicative
  map_one' := MulEquiv.ext fun v => by
    show Multiplicative.ofAdd (ρ 1 (Multiplicative.toAdd v)) = v
    rw [map_one]
    rfl
  map_mul' p q := MulEquiv.ext fun v => by
    show Multiplicative.ofAdd (ρ (p * q) (Multiplicative.toAdd v)) =
      Multiplicative.ofAdd (ρ p (ρ q (Multiplicative.toAdd v)))
    rw [map_mul]
    rfl

theorem phiOf_apply {n : ℕ} {P : Type*} [Group P]
    (ρ : P →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))) (p : P)
    (v : Multiplicative (Fin n → ZMod 2)) :
    phiOf ρ p v = Multiplicative.ofAdd (ρ p (Multiplicative.toAdd v)) := rfl

section Main

variable {n : ℕ} {P : Type} [Group P]
  (ρ : P →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)))
  {X : Type} [Group X] (ψ : X →* Multiplicative (Fin n → ZMod 2) ⋊[phiOf ρ] P)

theorem exists_P_section [Group.IsPerfect P] (hND : NoPerfectDoubleCover P)
    (hψ : Function.Surjective ψ) (z : X) (hz2 : z * z = 1) (hzne : z ≠ 1)
    (hker : ψ.ker = Subgroup.zpowers z) :
    ∃ σ : P →* X, ∀ p, ψ (σ p) = inr p := by
  let XP : Subgroup X :=
    Subgroup.comap ψ (inr : P →* Multiplicative (Fin n → ZMod 2) ⋊[phiOf ρ] P).range
  let g : XP →* P := rightHom.comp (ψ.comp XP.subtype)
  have hg : Function.Surjective g := by
    intro p
    obtain ⟨x, hx⟩ := hψ (inr p)
    exact ⟨⟨x, ⟨p, hx.symm⟩⟩, by simp [g, hx]⟩
  have hψz : ψ z = 1 := by
    have : z ∈ ψ.ker := hker ▸ Subgroup.mem_zpowers z
    exact MonoidHom.mem_ker.1 this
  have hzXP : z ∈ XP := ⟨1, by rw [map_one, hψz]⟩
  let zP : XP := ⟨z, hzXP⟩
  have hgx : ∀ x : XP, g x = 1 ↔ ψ x.1 = 1 := by
    intro x
    obtain ⟨q, hq⟩ := x.2
    have h1 : g x = q := by
      show rightHom (ψ x.1) = q
      rw [← hq, rightHom_inr]
    rw [h1, ← hq]
    constructor
    · rintro rfl
      exact map_one _
    · intro h
      exact inr_injective (h.trans (map_one inr).symm)
  have hmem : ∀ x : XP, x ∈ Subgroup.zpowers zP ↔ x.1 ∈ Subgroup.zpowers z := by
    intro x
    simp only [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, by simp [zP]⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa [zP] using hk)⟩
  have hgker : g.ker = Subgroup.zpowers zP := by
    ext x
    rw [MonoidHom.mem_ker, hgx, hmem, ← hker, MonoidHom.mem_ker]
  have hord : orderOf zP = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simp [zP, pow_two, hz2])
    · intro h
      exact hzne (congrArg Subtype.val h)
  have hk : Nat.card g.ker = 2 := by rw [hgker, Nat.card_zpowers, hord]
  obtain ⟨σ', hσ'⟩ := exists_section_of_noPerfectDoubleCover hND g hg hk
  refine ⟨XP.subtype.comp σ', fun p => ?_⟩
  obtain ⟨q, hq⟩ := (σ' p).2
  have h1 : q = p := by
    have h2 : g (σ' p) = p := hσ' p
    have h3 : g (σ' p) = q := by
      show rightHom (ψ (σ' p).1) = q
      rw [← hq, rightHom_inr]
    rw [← h3, h2]
  show ψ (σ' p).1 = inr p
  rw [← hq, h1]

@[expose] def preV : Subgroup X := (rightHom.comp ψ).ker

instance preV_normal : (preV ρ ψ).Normal := MonoidHom.normal_ker _

theorem right_of_mem_preV {x : X} (hx : x ∈ preV ρ ψ) : (ψ x).right = 1 := hx

theorem psi_preV (t : preV ρ ψ) : ψ t.1 = inl (ψ t.1).left := by
  have h : (ψ t.1).right = 1 := t.2
  ext
  · simp
  · simp [h]

@[expose] def projV : preV ρ ψ →* Multiplicative (Fin n → ZMod 2) where
  toFun t := (ψ t.1).left
  map_one' := by simp
  map_mul' t t' := by
    have h : (ψ t.1).right = 1 := t.2
    show (ψ (t.1 * t'.1)).left = (ψ t.1).left * (ψ t'.1).left
    rw [map_mul, mul_left, h]
    simp

theorem projV_apply (t : preV ρ ψ) : projV ρ ψ t = (ψ t.1).left := rfl

theorem psi_z {z : X} (hker : ψ.ker = Subgroup.zpowers z) : ψ z = 1 := by
  have : z ∈ ψ.ker := hker ▸ Subgroup.mem_zpowers z
  exact MonoidHom.mem_ker.1 this

theorem z_mem_preV {z : X} (hker : ψ.ker = Subgroup.zpowers z) : z ∈ preV ρ ψ := by
  show rightHom (ψ z) = 1
  rw [psi_z ρ ψ hker, map_one]

section CentralExtension

variable (hψ : Function.Surjective ψ) {z : X} (hzc : ∀ x, z * x = x * z) (hz2 : z * z = 1)
  (hzne : z ≠ 1) (hker : ψ.ker = Subgroup.zpowers z)
include hψ hzc hz2 hzne hker

noncomputable def centralExtOf : CentralExt n (preV ρ ψ) where
  ψ := projV ρ ψ
  surj := by
    intro v
    obtain ⟨x, hx⟩ := hψ (inl v)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show rightHom (ψ x) = 1
      rw [hx, rightHom_inl]
    · show (ψ x).left = v
      rw [hx]
      rfl
  z := ⟨z, z_mem_preV ρ ψ hker⟩
  central := fun t => Subtype.ext (hzc t.1)
  sq := Subtype.ext hz2
  ne_one := fun h => hzne (congrArg Subtype.val h)
  ker_eq := by
    ext t
    have h1 : t ∈ (projV ρ ψ).ker ↔ ψ t.1 = 1 := by
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        rw [psi_preV ρ ψ t]
        show inl (ψ t.1).left = 1
        rw [show (ψ t.1).left = 1 from h, map_one]
      · intro h
        show (ψ t.1).left = 1
        rw [h]
        rfl
    rw [h1, ← MonoidHom.mem_ker, hker]
    simp only [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end CentralExtension

theorem projV_conj (σ : P →* X) (hσ : ∀ p, ψ (σ p) = inr p) (p : P) (t : preV ρ ψ) :
    projV ρ ψ (MulAut.conjNormal (σ p) t) =
      Multiplicative.ofAdd (ρ p (Multiplicative.toAdd (projV ρ ψ t))) := by
  show (ψ (MulAut.conjNormal (σ p) t).1).left = _
  rw [MulAut.conjNormal_apply, map_mul, map_mul, map_inv, hσ, psi_preV ρ ψ t,
    ← map_inv, ← inl_aut]
  rfl

theorem zpow_mul_self_eq_one {z : X} (hz2 : z * z = 1) (m : ℤ) : z ^ m * z ^ m = 1 := by
  rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hz2, one_zpow]

theorem psi_s (E : CentralExt n (preV ρ ψ)) (hE : E.ψ = projV ρ ψ)
    (s : Multiplicative (Fin n → ZMod 2) →* preV ρ ψ) (hs : ∀ v, E.ψ (s v) = v)
    (v : Multiplicative (Fin n → ZMod 2)) : ψ (s v).1 = inl v := by
  rw [psi_preV ρ ψ (s v)]
  have := hs v
  rw [hE] at this
  rw [← projV_apply]
  rw [this]

theorem exists_hom_section [Group.IsPerfect P] (hND : NoPerfectDoubleCover P)
    (a b : P) (hgen : Subgroup.closure ({a, b} : Set P) = ⊤)
    (A B : Matrix (Fin n) (Fin n) (ZMod 2)) (hA : ∀ v, ρ a v = A *ᵥ v)
    (hB : ∀ v, ρ b v = B *ᵥ v)
    (hC : ∀ c : Matrix (Fin n) (Fin n) (ZMod 2), cᵀ = c → (∀ i, c i i = 0) →
      Aᵀ * c * A = c → Bᵀ * c * B = c → c = 0)
    (hl : ∀ l : Fin n → ZMod 2, Aᵀ *ᵥ l = l → Bᵀ *ᵥ l = l → l = 0)
    (x₀ : Fin n → ZMod 2) (hx₀ : ρ a x₀ = x₀) (ha2 : a * a = 1)
    (hfox : ∀ l : P → (Fin n → ZMod 2),
      (∀ p q x, l (p * q) ⬝ᵥ x = l p ⬝ᵥ ρ q x + l q ⬝ᵥ x) → l a ⬝ᵥ x₀ = 0 →
        ∃ φ : Fin n → ZMod 2, (∀ x, l a ⬝ᵥ x = φ ⬝ᵥ ρ a x + φ ⬝ᵥ x) ∧
          (∀ x, l b ⬝ᵥ x = φ ⬝ᵥ ρ b x + φ ⬝ᵥ x))
    (hψ : Function.Surjective ψ) {z : X} (hzc : ∀ x, z * x = x * z) (hz2 : z * z = 1)
    (hzne : z ≠ 1) (hker : ψ.ker = Subgroup.zpowers z)
    (x₁ : X) (hx₁ : x₁ * x₁ = 1)
    (hψx₁ : ψ x₁ = inl (Multiplicative.ofAdd x₀) * inr a) :
    ∃ τ : Multiplicative (Fin n → ZMod 2) ⋊[phiOf ρ] P →* X, ∀ s, ψ (τ s) = s := by
  obtain ⟨σ, hσ⟩ := exists_P_section ρ ψ hND hψ z hz2 hzne hker
  let E := centralExtOf ρ ψ hψ hzc hz2 hzne hker
  have hE : E.ψ = projV ρ ψ := rfl
  have hfixz : ∀ p, MulAut.conjNormal (σ p) E.z = E.z := fun p =>
    Subtype.ext (by
      show σ p * z * (σ p)⁻¹ = z
      rw [← hzc (σ p), mul_assoc, mul_inv_cancel, mul_one])
  let actA : E.Act A :=
    { γ := (MulAut.conjNormal (σ a)).toMonoidHom
      fix_z := hfixz a
      act := fun t => by
        show projV ρ ψ (MulAut.conjNormal (σ a) t) = _
        rw [projV_conj ρ ψ σ hσ, hA]
        rfl }
  let actB : E.Act B :=
    { γ := (MulAut.conjNormal (σ b)).toMonoidHom
      fix_z := hfixz b
      act := fun t => by
        show projV ρ ψ (MulAut.conjNormal (σ b) t) = _
        rw [projV_conj ρ ψ σ hσ, hB]
        rfl }
  obtain ⟨s₀, hs₀⟩ := E.exists_section_of_forms actA actB hC hl
  let Q : EquivSection E ρ :=
    { γ := (MulAut.conjNormal : X →* MulAut (preV ρ ψ)).comp σ
      fix_z := fun p => hfixz p
      act := fun p t => by
        show projV ρ ψ (MulAut.conjNormal (σ p) t) = _
        rw [projV_conj ρ ψ σ hσ]
        rfl
      s₀ := s₀
      sec := hs₀ }
  have hfix : Q.γ a (Q.s₀ (Multiplicative.ofAdd x₀)) = Q.s₀ (Multiplicative.ofAdd x₀) := by
    set sx : preV ρ ψ := s₀ (Multiplicative.ofAdd x₀) with hsx
    have hψs : ψ sx.1 = inl (Multiplicative.ofAdd x₀) := psi_s ρ ψ E hE s₀ hs₀ _
    let c₀ : X := sx.1 * σ a
    have hψc₀ : ψ c₀ = ψ x₁ := by
      show ψ (sx.1 * σ a) = _
      rw [map_mul, hψs, hσ, hψx₁]
    have hmem : c₀⁻¹ * x₁ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψc₀, inv_mul_cancel]
    have hmem' : c₀⁻¹ * x₁ ∈ Subgroup.zpowers z := by rw [← hker]; exact hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem'
    have hx₁c : x₁ = c₀ * z ^ m := by rw [hm]; group
    have hzcomm : Commute z c₀ := hzc c₀
    have hcomm : Commute (z ^ m) c₀ := hzcomm.zpow_left m
    have hsq : c₀ * c₀ = 1 := by
      have : x₁ * x₁ = c₀ * c₀ * (z ^ m * z ^ m) := by
        rw [hx₁c]
        calc c₀ * z ^ m * (c₀ * z ^ m) = c₀ * (z ^ m * c₀) * z ^ m := by simp only [mul_assoc]
          _ = c₀ * (c₀ * z ^ m) * z ^ m := by rw [hcomm.eq]
          _ = c₀ * c₀ * (z ^ m * z ^ m) := by simp only [mul_assoc]
      rw [zpow_mul_self_eq_one hz2, mul_one] at this
      rw [← this, hx₁]
    have hcc : c₀ * c₀ = sx.1 * (MulAut.conjNormal (σ a) sx).1 := by
      rw [MulAut.conjNormal_apply]
      have : σ a * σ a = 1 := by rw [← map_mul, ha2, map_one]
      calc c₀ * c₀ = sx.1 * σ a * (sx.1 * σ a) := rfl
        _ = sx.1 * (σ a * sx.1 * (σ a)⁻¹) * (σ a * σ a) := by group
        _ = sx.1 * (σ a * sx.1 * (σ a)⁻¹) := by rw [this, mul_one]
    have h1 : sx.1 * (MulAut.conjNormal (σ a) sx).1 = 1 := by rw [← hcc, hsq]
    have h2 : (MulAut.conjNormal (σ a) sx).1 = sx.1⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : sx.1⁻¹ = sx.1 := by
      have : (sx * sx : preV ρ ψ) = 1 := by
        rw [hsx, ← map_mul]
        have : Multiplicative.ofAdd x₀ * Multiplicative.ofAdd x₀ =
            (1 : Multiplicative (Fin n → ZMod 2)) :=
          CentralExt.mul_self_multiplicative _
        rw [this, map_one]
      have h4 : (sx⁻¹ : preV ρ ψ) = sx := inv_eq_of_mul_eq_one_right this
      exact congrArg Subtype.val h4
    exact Subtype.ext (h2.trans h3)
  obtain ⟨s', hs'ψ, hs'eq⟩ :=
    exists_equivariant_section Q a b hgen x₀ hx₀ hfix hfox
  let fn : Multiplicative (Fin n → ZMod 2) →* X := (preV ρ ψ).subtype.comp s'
  have hcompat : ∀ p, fn.comp (phiOf ρ p).toMonoidHom =
      (MulAut.conj (σ p)).toMonoidHom.comp fn := by
    intro p
    refine MonoidHom.ext fun v => ?_
    show (s' (phiOf ρ p v)).1 = σ p * (s' v).1 * (σ p)⁻¹
    have := hs'eq p v
    rw [phiOf_apply, ← this]
    exact MulAut.conjNormal_apply (σ p) (s' v)
  refine ⟨SemidirectProduct.lift fn σ hcompat, fun s => ?_⟩
  have key : ψ.comp (SemidirectProduct.lift fn σ hcompat) = MonoidHom.id _ := by
    apply SemidirectProduct.hom_ext
    · refine MonoidHom.ext fun v => ?_
      show ψ (SemidirectProduct.lift fn σ hcompat (inl v)) = inl v
      rw [lift_inl]
      exact psi_s ρ ψ E hE s' hs'ψ v
    · refine MonoidHom.ext fun p => ?_
      show ψ (SemidirectProduct.lift fn σ hcompat (inr p)) = inr p
      rw [lift_inr]
      exact hσ p
  exact DFunLike.congr_fun key s

end Main

end CFSG.Sporadic.Co1.Cover
