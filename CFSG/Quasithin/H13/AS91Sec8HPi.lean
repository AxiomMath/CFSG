module

public import CFSG.Quasithin.H13.AS91Sec4DefsB
public import CFSG.Quasithin.Background.HatM22DoubleCover

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin.HatM22
open CFSG.CharacterTheory.SteinbergBY (FieldFour)

theorem eq_one_or_of_mem_zpowers_of_orderOf_eq_two {H : Type*} [Group H] {t : H}
    (ht : orderOf t = 2) {x : H} (hx : x ∈ Subgroup.zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have ht2 : t ^ ((2 : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← ht, pow_orderOf_eq_one]
  have hmod := zpow_eq_zpow_emod (x := t) (m := n) (n := ((2 : ℕ) : ℤ)) ht2
  norm_num at hmod
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [hmod, h]; simp
  · right; rw [hmod, h]; simp

namespace Loc41

variable {G : Type} [Group G] [Finite G] {z : G}

theorem z_orderOf (c : Loc41 G z) : orderOf z = 2 := by
  rw [← c.S_z, c.S.orderOf_z]

abbrev CX (c : Loc41 G z) : Subgroup G := H z ⊓ centralizer (c.X : Set G)

abbrev NX (c : Loc41 G z) : Subgroup G := H z ⊓ normalizer (c.X : Set G)

theorem z_mem_CX (c : Loc41 G z) : z ∈ c.CX := by
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, ?_⟩
  change z ∈ centralizer (c.X : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (c.X_le hx)

theorem X_le_CX (c : Loc41 G z) : c.X ≤ c.CX := by
  intro x hx
  refine ⟨c.X_le hx, ?_⟩
  change x ∈ centralizer (c.X : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hcyc : IsCyclic ↥c.X := isCyclic_of_prime_card (p := 3) (by rw [c.card_X])
  have hcomm := isMulCommutative_iff.mp (IsCyclic.isMulCommutative (α := ↥c.X)) ⟨y, hy⟩ ⟨x, hx⟩
  simpa using congrArg Subtype.val hcomm

theorem SM_eq (c : Loc41 G z) : c.S.M = H z := by
  rw [Setting.M, H, c.S_z]

abbrev toSM (c : Loc41 G z) (h : ↥c.CX) : ↥c.S.M :=
  ⟨(h : G), c.SM_eq.symm ▸ h.2.1⟩

@[simp]
theorem coe_toSM (c : Loc41 G z) (h : ↥c.CX) : ((c.toSM h : c.S.M) : G) = (h : G) := rfl

theorem toSM_mem_centralizer (c : Loc41 G z) (h : ↥c.CX) :
    ((c.toSM h : c.S.M) : G) ∈ centralizer (c.X : Set G) :=
  h.2.2

noncomputable def piCMat (c : Loc41 G z) (h : ↥c.CX) :
    Matrix.GeneralLinearGroup (Fin 6) FieldFour :=
  Classical.choose (c.acts (c.toSM h) (c.toSM_mem_centralizer h))

theorem piCMat_mem (c : Loc41 G z) (h : ↥c.CX) : c.piCMat h ∈ hatM22Γ₀ :=
  (Classical.choose_spec (c.acts (c.toSM h) (c.toSM_mem_centralizer h))).1

theorem piCMat_spec (c : Loc41 G z) (h : ↥c.CX) (v : c.S.Qt) :
    c.ψ ((c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v) =
      ((c.piCMat h : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour).mulVec (c.ψ v) :=
  (Classical.choose_spec (c.acts (c.toSM h) (c.toSM_mem_centralizer h))).2 v

theorem eq_of_mulVec_ψ_eq (c : Loc41 G z)
    {A B : Matrix (Fin 6) (Fin 6) FieldFour}
    (h : ∀ v : c.S.Qt, A.mulVec (c.ψ v) = B.mulVec (c.ψ v)) : A = B := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := c.ψ.surjective w
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact h v

noncomputable def piC (c : Loc41 G z) : ↥c.CX →* ↥hatM22Γ₀ where
  toFun h := ⟨c.piCMat h, c.piCMat_mem h⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    apply c.eq_of_mulVec_ψ_eq
    intro v
    rw [← c.piCMat_spec, show c.toSM (1 : ↥c.CX) = 1 from Subtype.ext rfl, map_one]
    simp
  map_mul' h₁ h₂ := by
    apply Subtype.ext
    apply Units.ext
    apply c.eq_of_mulVec_ψ_eq
    intro v
    rw [← c.piCMat_spec,
      show c.toSM (h₁ * h₂) = c.toSM h₁ * c.toSM h₂ from Subtype.ext rfl, map_mul,
      Subgroup.coe_mul, LinearEquiv.mul_apply,
      c.piCMat_spec h₁ ((c.S.ρ (c.toSM h₂) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v),
      c.piCMat_spec h₂ v, Matrix.mulVec_mulVec]
    rw [Subgroup.coe_mul, Units.val_mul]

theorem piC_spec (c : Loc41 G z) (h : ↥c.CX) (v : c.S.Qt) :
    c.ψ ((c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v) =
      (((c.piC h : ↥hatM22Γ₀) :
          Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour).mulVec (c.ψ v) :=
  c.piCMat_spec h v

theorem piC_unique (c : Loc41 G z) (h : ↥c.CX) (γ : ↥hatM22Γ₀)
    (hγ : ∀ v : c.S.Qt, c.ψ ((c.S.ρ (c.toSM h) : c.S.Qt ≃ₗ[ZMod 2] c.S.Qt) v) =
      (((γ : ↥hatM22Γ₀) : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour).mulVec (c.ψ v)) :
    c.piC h = γ := by
  apply Subtype.ext
  apply Units.ext
  apply c.eq_of_mulVec_ψ_eq
  intro v
  rw [← c.piC_spec h v, hγ v]

theorem piC_surjective (c : Loc41 G z) : Function.Surjective c.piC := by
  intro γ
  obtain ⟨m, hmX, hm⟩ := c.onto γ γ.2
  have hmH : (m : G) ∈ H z := c.SM_eq ▸ m.2
  let h : ↥c.CX := ⟨(m : G), ⟨hmH, hmX⟩⟩
  refine ⟨h, ?_⟩
  apply c.piC_unique h γ
  intro v
  rw [show c.toSM h = m from Subtype.ext rfl]
  exact hm v

theorem z_mem_Q (c : Loc41 G z) : z ∈ Q z := by
  have h := c.S.z_mem_QG
  rwa [c.S_z, c.S_QG] at h

theorem toSM_z (c : Loc41 G z) :
    c.toSM ⟨z, c.z_mem_CX⟩ = c.S.zM := by
  apply Subtype.ext
  rw [coe_toSM, Setting.coe_zM, c.S_z]

theorem piC_eq_one_of_mem_Q (c : Loc41 G z) (h : ↥c.CX) (hQ : c.toSM h ∈ c.S.Q) :
    c.piC h = 1 := by
  apply c.piC_unique h 1
  intro v
  rw [c.S.ρ_eq_one_of_mem_Q hQ]
  simp

theorem mem_ker_piC_iff (c : Loc41 G z) (h : ↥c.CX) :
    h ∈ c.piC.ker ↔ (h : G) = 1 ∨ (h : G) = z := by
  constructor
  · intro hk
    rw [MonoidHom.mem_ker] at hk
    have hρ : c.S.ρ (c.toSM h) = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      have hspec := c.piC_spec h v
      rw [hk] at hspec
      apply c.ψ.injective
      rw [hspec]
      simp
    have hQ : c.toSM h ∈ c.S.Q := by
      rw [← c.S.ker_ρ]
      exact hρ
    have hQG : (h : G) ∈ c.S.QG := c.S.mem_QG_iff.mpr ⟨(c.toSM h).2, hQ⟩
    have hQz : (h : G) ∈ Q z := by rwa [c.S_QG] at hQG
    have hmem : (h : G) ∈ Q z ⊓ centralizer (c.X : Set G) := ⟨hQz, h.2.2⟩
    rw [c.inf_centralizer] at hmem
    exact eq_one_or_of_mem_zpowers_of_orderOf_eq_two c.z_orderOf hmem
  · rintro (h1 | hz)
    · have hh : h = 1 := Subtype.ext h1
      rw [hh, MonoidHom.mem_ker, map_one]
    · have hh : h = ⟨z, c.z_mem_CX⟩ := Subtype.ext hz
      rw [hh, MonoidHom.mem_ker]
      apply c.piC_eq_one_of_mem_Q
      rw [c.toSM_z]
      exact c.S.zM_mem_Q

theorem ker_piC_le_center (c : Loc41 G z) : c.piC.ker ≤ Subgroup.center ↥c.CX := by
  intro h hk
  rw [Subgroup.mem_center_iff]
  intro y
  rcases (c.mem_ker_piC_iff h).1 hk with h1 | hz
  · have hh : h = 1 := Subtype.ext h1
    rw [hh, mul_one, one_mul]
  · apply Subtype.ext
    have hcomm : (y : G) * z = z * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp y.2.1
    simpa [Subgroup.coe_mul, hz] using hcomm

theorem card_ker_piC (c : Loc41 G z) : Nat.card c.piC.ker = 2 := by
  let g : ↥c.CX := ⟨z, c.z_mem_CX⟩
  have hg2 : orderOf g = 2 := by
    have h : ((g : ↥c.CX) : G) = z := rfl
    rw [← Subgroup.orderOf_coe g, h, c.z_orderOf]
  have hker : c.piC.ker = Subgroup.zpowers g := by
    apply le_antisymm
    · intro h hk
      rcases (c.mem_ker_piC_iff h).1 hk with h1 | hz
      · rw [show h = 1 from Subtype.ext h1]
        exact Subgroup.one_mem _
      · rw [show h = g from Subtype.ext hz]
        exact Subgroup.mem_zpowers g
    · intro h hh
      rw [MonoidHom.mem_ker]
      rcases eq_one_or_of_mem_zpowers_of_orderOf_eq_two hg2 hh with h1 | hgz
      · rw [h1, map_one]
      · rw [hgz]
        apply c.piC_eq_one_of_mem_Q
        rw [c.toSM_z]
        exact c.S.zM_mem_Q
  rw [hker, Nat.card_zpowers, hg2]

theorem piC_of_mem_X
    (c : Loc41 G z) {x : G} (hx : x ∈ c.X) (hx1 : x ≠ 1) :
    c.piC ⟨x, c.X_le_CX hx⟩ = hatM22Z ∨ c.piC ⟨x, c.X_le_CX hx⟩ = hatM22Z ^ 2 := by
  let g : ↥c.CX := ⟨x, c.X_le_CX hx⟩
  have hxcent : g ∈ Subgroup.center ↥c.CX := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hy : (y : G) ∈ centralizer (c.X : Set G) := y.2.2
    have hxy : x * (y : G) = (y : G) * x := Subgroup.mem_centralizer_iff.mp hy x hx
    simpa [g] using hxy.symm
  have hcent : c.piC g ∈ Subgroup.center ↥hatM22Γ₀ :=
    Subgroup.map_center_le_center (f := c.piC) c.piC_surjective
      (Subgroup.mem_map_of_mem c.piC hxcent)
  rw [center_hatM22Γ₀] at hcent
  rcases (mem_ker_hatM22Act_iff (c.piC g)).1 hcent with h1 | hZ | hZ2
  · exfalso
    have hk : g ∈ c.piC.ker := by rwa [MonoidHom.mem_ker]
    rcases (c.mem_ker_piC_iff g).1 hk with hx1' | hz
    · exact hx1 hx1'
    · have hdvd : orderOf x ∣ 3 := by
        have := Subgroup.orderOf_dvd_natCard c.X hx
        rwa [c.card_X] at this
      have hordx : orderOf x = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hx1
        · exact h
      have hxz : x = z := by simpa [g] using hz
      have h32 : (3 : ℕ) = 2 := by rw [← hordx, hxz, c.z_orderOf]
      norm_num at h32
  · exact Or.inl hZ
  · exact Or.inr hZ2

theorem Q_normal_H (c : Loc41 G z) :
    ∀ h ∈ H z, ∀ q ∈ Q z, h * q * h⁻¹ ∈ Q z := by
  intro h hh q hq
  obtain ⟨hqM, hqQ⟩ := c.S.mem_QG_iff.mp (by rwa [← c.S_QG] at hq)
  let hS : c.S.M := ⟨h, c.SM_eq.symm ▸ hh⟩
  have hconj : hS * (⟨q, hqM⟩ : c.S.M) * hS⁻¹ ∈ c.S.Q :=
    c.S.normal.conj_mem (⟨q, hqM⟩ : c.S.M) hqQ hS
  have hmem : h * q * h⁻¹ ∈ c.S.QG := ⟨_, hconj, rfl⟩
  rwa [c.S_QG] at hmem

theorem Q_inf_X_eq_bot (c : Loc41 G z) : Q z ⊓ c.X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  by_contra hx1
  have hxX : x ∈ c.X := hx.2
  have hdvd : orderOf x ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard c.X hxX
    rwa [c.card_X] at this
  have hordx : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hQ2 : IsPGroup 2 (Q z) := by
    rw [← c.S_QG]
    exact IsPGroup.map c.S.extraspecial.1 c.S.M.subtype
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ2) ⟨x, hx.1⟩
  have hk' : orderOf x = 2 ^ k := by simpa using hk
  have h3eq : 3 = 2 ^ k := by rw [← hordx, hk']
  have h3dvd : 3 ∣ 2 ^ k := h3eq ▸ dvd_refl 3
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3dvd
  norm_num at h32

theorem z_mem_NX (c : Loc41 G z) : z ∈ c.NX := by
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, ?_⟩
  change z ∈ normalizer (c.X : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp (c.X_le hx)
    have hzx : z * x * z⁻¹ = x := by
      calc z * x * z⁻¹ = x * z * z⁻¹ := by rw [← hxz]
        _ = x := by group
    rwa [hzx]
  · intro hx
    have hcommy : (z * x * z⁻¹) * z = z * (z * x * z⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp (c.X_le hx)
    have hy : z⁻¹ * (z * x * z⁻¹) * z = z * x * z⁻¹ := by
      calc z⁻¹ * (z * x * z⁻¹) * z = z⁻¹ * ((z * x * z⁻¹) * z) := by group
        _ = z⁻¹ * (z * (z * x * z⁻¹)) := by rw [hcommy]
        _ = z * x * z⁻¹ := by group
    have hx' : x = z * x * z⁻¹ := by
      calc x = z⁻¹ * (z * x * z⁻¹) * z := by group
        _ = z * x * z⁻¹ := hy
    rwa [hx']

theorem CX_le_NX (c : Loc41 G z) : c.CX ≤ c.NX := by
  intro h hh
  exact ⟨hh.1, Subgroup.centralizer_le_normalizer (c.X : Set G) hh.2⟩

theorem CX_normal_NX (c : Loc41 G z) : (c.CX.subgroupOf c.NX).Normal := by
  rw [Subgroup.normal_subgroupOf_iff c.CX_le_NX]
  intro h k hh hk
  refine ⟨(H z).mul_mem ((H z).mul_mem hk.1 hh.1) ((H z).inv_mem hk.1), ?_⟩
  change k * h * k⁻¹ ∈ centralizer (c.X : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hk'inv : k⁻¹ ∈ normalizer (c.X : Set G) :=
    (normalizer (c.X : Set G)).inv_mem hk.2
  have hx' : k⁻¹ * x * k ∈ c.X := by
    simpa using (Subgroup.mem_normalizer_iff.mp hk'inv x).mp hx
  have hcomm : (k⁻¹ * x * k) * h = h * (k⁻¹ * x * k) :=
    Subgroup.mem_centralizer_iff.mp hh.2 _ hx'
  calc x * (k * h * k⁻¹) = k * ((k⁻¹ * x * k) * h) * k⁻¹ := by group
    _ = k * (h * (k⁻¹ * x * k)) * k⁻¹ := by rw [← hcomm]
    _ = (k * h * k⁻¹) * x := by group

theorem X_le_NX (c : Loc41 G z) : c.X ≤ c.NX := by
  intro x hx
  exact ⟨c.X_le hx, Subgroup.le_normalizer hx⟩

theorem X_normal_NX (c : Loc41 G z) : (c.X.subgroupOf c.NX).Normal := by
  rw [Subgroup.normal_subgroupOf_iff c.X_le_NX]
  intro h k hh hk
  exact (Subgroup.mem_normalizer_iff.mp hk.2 h).mp hh

noncomputable abbrev qC (c : Loc41 G z) : ↥c.CX →* CFSG.Blueprint.NativeSporadic.M22 :=
  CFSG.Quasithin.HM22.hatM22Q.comp c.piC

theorem qC_surjective (c : Loc41 G z) : Function.Surjective c.qC :=
  CFSG.Quasithin.HM22.hatM22Q_surjective.comp c.piC_surjective

theorem H_eq_sup_NX (c : Loc41 G z) : H z = Q z ⊔ c.NX :=
  c.eq_sup_normalizer

theorem self_centralizing_NX (c : Loc41 G z) {g : G} (hg : g ∈ c.NX)
    (hcomm : ∀ y ∈ c.CX, g * y = y * g) : g ∈ c.CX := by
  refine ⟨hg.1, ?_⟩
  change g ∈ centralizer (c.X : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (hcomm x (c.X_le_CX hx)).symm

theorem inf_Q_NX (c : Loc41 G z) : Q z ⊓ c.NX = Subgroup.zpowers z := by
  apply le_antisymm
  · intro q hq
    have hqQ : q ∈ Q z := hq.1
    have hqN : q ∈ normalizer (c.X : Set G) := hq.2.2
    have hqcent : q ∈ centralizer (c.X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hconjX : q * x * q⁻¹ ∈ c.X :=
        (Subgroup.mem_normalizer_iff.mp hqN x).mp hx
      have hQ1 : x * q * x⁻¹ ∈ Q z := c.Q_normal_H x (c.X_le hx) q hqQ
      have hQ2 : x * q * x⁻¹ * q⁻¹ ∈ Q z :=
        (Q z).mul_mem hQ1 ((Q z).inv_mem hqQ)
      have hcommQ : q * x * q⁻¹ * x⁻¹ ∈ Q z := by
        have := (Q z).inv_mem hQ2
        simpa [mul_assoc] using this
      have hcommX : q * x * q⁻¹ * x⁻¹ ∈ c.X :=
        c.X.mul_mem hconjX (c.X.inv_mem hx)
      have hbot : q * x * q⁻¹ * x⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← c.Q_inf_X_eq_bot]
        exact ⟨hcommQ, hcommX⟩
      rw [Subgroup.mem_bot] at hbot
      have hqx : q * x * q⁻¹ = x := mul_inv_eq_one.mp hbot
      calc x * q = (q * x * q⁻¹) * q := by rw [hqx]
        _ = q * x := by group
    have hmem : q ∈ Q z ⊓ centralizer (c.X : Set G) := ⟨hqQ, hqcent⟩
    rwa [c.inf_centralizer] at hmem
  · rw [Subgroup.zpowers_le]
    exact ⟨c.z_mem_Q, c.z_mem_NX⟩

noncomputable def conjNX (c : Loc41 G z) : ↥c.NX →* MulAut ↥c.X :=
  (conjNormalizer c.X).comp
    { toFun := fun n => ⟨(n : G), n.2.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }

theorem conjNX_apply (c : Loc41 G z) (n : ↥c.NX) (x : ↥c.X) :
    ((c.conjNX n x : ↥c.X) : G) = (n : G) * (x : G) * (n : G)⁻¹ :=
  conjNormalizer_apply c.X ⟨(n : G), n.2.2⟩ x

theorem conjNX_eq_one_iff (c : Loc41 G z) (n : ↥c.NX) :
    c.conjNX n = 1 ↔ (n : G) ∈ centralizer (c.X : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : c.conjNX n ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [h]; rfl
    have hcoe := congrArg (fun e : ↥c.X => (e : G)) hx'
    rw [c.conjNX_apply] at hcoe
    calc x * (n : G) = ((n : G) * x * (n : G)⁻¹) * (n : G) := by rw [hcoe]
      _ = (n : G) * x := by group
  · intro h
    apply DFunLike.ext
    intro x
    apply Subtype.ext
    rw [c.conjNX_apply]
    have hcomm : (x : G) * (n : G) = (n : G) * (x : G) :=
      Subgroup.mem_centralizer_iff.mp h (x : G) x.2
    calc (n : G) * (x : G) * (n : G)⁻¹ = (x : G) * (n : G) * (n : G)⁻¹ := by rw [← hcomm]
      _ = (x : G) := by group

end Loc41

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G}

theorem isPerfect_CX (c : Loc49 G z) : Group.IsPerfect ↥c.CX :=
  c.quasisimple.1

theorem exists_t (c : Loc49 G z) :
    ∃ t ∈ c.NX, t ∉ c.CX ∧ t * t = 1 ∧
      (∀ x ∈ c.X, t * x * t⁻¹ = x⁻¹) ∧
      c.NX = c.CX ⊔ Subgroup.zpowers t := by
  obtain ⟨t, htH, ht2, htinv⟩ := c.inv_X
  have ht_inv : t⁻¹ = t := by
    calc t⁻¹ = t⁻¹ * 1 := by rw [mul_one]
      _ = t⁻¹ * (t * t) := by rw [ht2]
      _ = (t⁻¹ * t) * t := by rw [mul_assoc]
      _ = t := by rw [inv_mul_cancel, one_mul]
  have htN : t ∈ c.NX := by
    refine ⟨htH, ?_⟩
    change t ∈ normalizer (c.X : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [htinv x hx]
      exact c.X.inv_mem hx
    · intro hx
      have hy : t⁻¹ * (t * x * t⁻¹) * t = (t * x * t⁻¹)⁻¹ := by
        rw [ht_inv]
        simpa [ht_inv] using htinv (t * x * t⁻¹) hx
      have hx' : x = (t * x * t⁻¹)⁻¹ := by
        calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
          _ = (t * x * t⁻¹)⁻¹ := hy
      rw [hx']
      exact c.X.inv_mem hx
  have htnotCX : t ∉ c.CX := by
    intro htCX
    have hXnt : Nontrivial ↥c.X := by
      rw [← Finite.one_lt_card_iff_nontrivial, c.card_X]
      norm_num
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥c.X)
    have hxmem : (x : G) ∈ c.X := x.2
    have hcomm : t * (x : G) = (x : G) * t :=
      (Subgroup.mem_centralizer_iff.mp htCX.2 (x : G) hxmem).symm
    have hinv := htinv (x : G) hxmem
    have hxeq : (x : G) = (x : G)⁻¹ := by
      calc (x : G) = t * (x : G) * t⁻¹ := by rw [hcomm]; group
        _ = (x : G)⁻¹ := hinv
    have hx2 : (x : G) * (x : G) = 1 := by
      calc (x : G) * (x : G) = (x : G)⁻¹ * (x : G) := by
            nth_rewrite 1 [hxeq]
            rfl
        _ = 1 := inv_mul_cancel (x : G)
    have hdvd3 : orderOf (x : G) ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard c.X x.2
      rwa [c.card_X] at this
    have hdvd2 : orderOf (x : G) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hx2
    have hone : orderOf (x : G) = 1 := by
      have hdvd : orderOf (x : G) ∣ Nat.gcd 3 2 := Nat.dvd_gcd hdvd3 hdvd2
      have hdvd1 : orderOf (x : G) ∣ 1 := by simpa using hdvd
      exact Nat.dvd_one.mp hdvd1
    exact hx1 (Subtype.ext (orderOf_eq_one_iff.mp hone))
  let tNX : ↥c.NX := ⟨t, htN⟩
  have hφt_ne : c.conjNX tNX ≠ 1 := by
    intro h
    exact htnotCX ⟨htN.1, (c.conjNX_eq_one_iff tNX).1 h⟩
  have hφt_sq : c.conjNX tNX ^ 2 = 1 := by
    rw [← map_pow, show tNX ^ 2 = 1 from Subtype.ext (by simpa [tNX, pow_two] using ht2), map_one]
  have horder : orderOf (c.conjNX tNX) = 2 :=
    orderOf_eq_prime hφt_sq hφt_ne
  haveI : IsCyclic ↥c.X := isCyclic_of_prime_card (p := 3) (by rw [c.card_X])
  have hcardAut : Nat.card (MulAut ↥c.X) = 2 := by
    rw [IsCyclic.card_mulAut ↥c.X, c.card_X, Nat.totient_prime (by norm_num)]
  have hzp_top : Subgroup.zpowers (c.conjNX tNX) = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Nat.card_zpowers, horder, Subgroup.card_top, hcardAut]
  refine ⟨t, htN, htnotCX, ht2, htinv, ?_⟩
  apply le_antisymm
  · intro g hg
    have hmem : c.conjNX ⟨g, hg⟩ ∈ Subgroup.zpowers (c.conjNX tNX) := by
      rw [hzp_top]
      exact Subgroup.mem_top _
    rcases eq_one_or_of_mem_zpowers_of_orderOf_eq_two horder hmem with hφg | hφg
    · have hgcent : g ∈ centralizer (c.X : Set G) := (c.conjNX_eq_one_iff ⟨g, hg⟩).1 hφg
      exact Subgroup.mem_sup_left ⟨hg.1, hgcent⟩
    · have hgt : (g * t⁻¹) ∈ c.NX := c.NX.mul_mem hg (c.NX.inv_mem htN)
      have hφgt : c.conjNX ⟨g * t⁻¹, hgt⟩ = 1 := by
        have hprod : c.conjNX ⟨g * t⁻¹, hgt⟩ =
            c.conjNX ⟨g, hg⟩ * (c.conjNX tNX)⁻¹ := by
          rw [show (⟨g * t⁻¹, hgt⟩ : ↥c.NX) = ⟨g, hg⟩ * tNX⁻¹ from
            Subtype.ext (by simp [tNX])]
          rw [map_mul, map_inv]
        rw [hprod, hφg, mul_inv_cancel]
      have hgcent : (g * t⁻¹) ∈ centralizer (c.X : Set G) :=
        (c.conjNX_eq_one_iff ⟨g * t⁻¹, hgt⟩).1 hφgt
      have hgCX : (g * t⁻¹) ∈ c.CX := ⟨hgt.1, hgcent⟩
      have hg_eq : g = (g * t⁻¹) * t := by group
      rw [hg_eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgCX)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  · apply sup_le
    · exact c.CX_le_NX
    · rw [Subgroup.zpowers_le]
      exact htN

theorem hatM22Q_hatM22Z :
    CFSG.Quasithin.HM22.hatM22Q hatM22Z = 1 := by
  rw [← MonoidHom.mem_ker, CFSG.Quasithin.HM22.hatM22Q_ker]
  exact hatM22Z_mem_center

theorem hatM22Q_hatM22Z_sq :
    CFSG.Quasithin.HM22.hatM22Q (hatM22Z ^ 2) = 1 := by
  rw [← MonoidHom.mem_ker, CFSG.Quasithin.HM22.hatM22Q_ker]
  exact Subgroup.pow_mem _ hatM22Z_mem_center 2

theorem qC_of_mem_X_ne
    (c : Loc49 G z) {x : G} (hx : x ∈ c.X) (hx1 : x ≠ 1) :
    c.qC ⟨x, c.X_le_CX hx⟩ = 1 := by
  change CFSG.Quasithin.HM22.hatM22Q (c.piC ⟨x, c.X_le_CX hx⟩) = 1
  rcases c.piC_of_mem_X hx hx1 with h | h
  · rw [h]
    exact hatM22Q_hatM22Z
  · rw [h]
    exact hatM22Q_hatM22Z_sq

theorem qC_of_mem_X
    (c : Loc49 G z) {x : G} (hx : x ∈ c.X) :
    c.qC ⟨x, c.X_le_CX hx⟩ = 1 := by
  by_cases hx1 : x = 1
  · have hh : (⟨x, c.X_le_CX hx⟩ : ↥c.CX) = 1 := Subtype.ext hx1
    rw [hh, map_one]
  · exact qC_of_mem_X_ne c hx hx1

theorem qC_ker
    (c : Loc49 G z) : c.qC.ker = Subgroup.center ↥c.CX := by
  have hqC : c.qC.ker = (Subgroup.center ↥hatM22Γ₀).comap c.piC := by
    rw [← MonoidHom.comap_ker, CFSG.Quasithin.HM22.hatM22Q_ker]
  rw [hqC, CFSG.LocalCores.comap_center_eq_of_perfect c.isPerfect_CX c.piC
    c.piC_surjective c.ker_piC_le_center]

theorem card_center_CX
    (c : Loc49 G z) : Nat.card (Subgroup.center ↥c.CX) = 6 := by
  have hcenter := CFSG.LocalCores.comap_center_eq_of_perfect c.isPerfect_CX c.piC
    c.piC_surjective c.ker_piC_le_center
  rw [← hcenter]
  have h1 := Subgroup.card_mul_index ((Subgroup.center ↥hatM22Γ₀).comap c.piC)
  rw [Subgroup.index_comap_of_surjective _ c.piC_surjective] at h1
  have h2 := Subgroup.card_ker_mul_card_range c.piC
  rw [MonoidHom.range_eq_top.mpr c.piC_surjective, Subgroup.card_top,
    c.card_ker_piC] at h2
  have h3 := Subgroup.card_mul_index (Subgroup.center ↥hatM22Γ₀)
  have hZcard : Nat.card (Subgroup.center ↥hatM22Γ₀) = 3 := card_center_hatM22Γ₀
  have hpos : 0 < (Subgroup.center ↥hatM22Γ₀).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have step : (2 * Nat.card (Subgroup.center ↥hatM22Γ₀)) *
      (Subgroup.center ↥hatM22Γ₀).index =
      Nat.card ((Subgroup.center ↥hatM22Γ₀).comap c.piC) *
        (Subgroup.center ↥hatM22Γ₀).index := by
    rw [show (2 * Nat.card (Subgroup.center ↥hatM22Γ₀)) *
        (Subgroup.center ↥hatM22Γ₀).index =
        2 * (Nat.card (Subgroup.center ↥hatM22Γ₀) *
          (Subgroup.center ↥hatM22Γ₀).index) by ring]
    calc 2 * (Nat.card (Subgroup.center ↥hatM22Γ₀) *
          (Subgroup.center ↥hatM22Γ₀).index) = 2 * Nat.card ↥hatM22Γ₀ := by rw [h3]
      _ = Nat.card ↥c.CX := h2
      _ = Nat.card ((Subgroup.center ↥hatM22Γ₀).comap c.piC) *
            (Subgroup.center ↥hatM22Γ₀).index := h1.symm
  have hC : Nat.card ((Subgroup.center ↥hatM22Γ₀).comap c.piC) =
      2 * Nat.card (Subgroup.center ↥hatM22Γ₀) :=
    (Nat.eq_of_mul_eq_mul_right hpos step).symm
  rw [hC, hZcard]

theorem qC_ker_le_center
    (c : Loc49 G z) : c.qC.ker ≤ Subgroup.center ↥c.CX := by
  rw [c.qC_ker]

theorem card_qC_ker
    (c : Loc49 G z) : Nat.card c.qC.ker = 6 := by
  rw [c.qC_ker, c.card_center_CX]

theorem exists_mulEquiv_CX
    {G' : Type} [Group G'] [Finite G'] {z' : G'}
    (c : Loc49 G z) (c' : Loc49 G' z') :
    ∃ θ : ↥c.CX ≃* ↥c'.CX, ∀ h, c'.piC (θ h) = c.piC h :=
  exists_mulEquiv_over_hatM22Γ₀ c.isPerfect_CX c'.isPerfect_CX c.piC c'.piC
    c.piC_surjective c'.piC_surjective c.ker_piC_le_center c'.ker_piC_le_center
    c.card_ker_piC c'.card_ker_piC

theorem mulEquiv_CX_maps_z {G' : Type} [Group G'] [Finite G'] {z' : G'}
    (c : Loc49 G z) (c' : Loc49 G' z') (θ : ↥c.CX ≃* ↥c'.CX)
    (hθ : ∀ h, c'.piC (θ h) = c.piC h) :
    θ ⟨z, c.z_mem_CX⟩ = ⟨z', c'.z_mem_CX⟩ := by
  have hzker : (⟨z, c.z_mem_CX⟩ : ↥c.CX) ∈ c.piC.ker := by
    rw [c.mem_ker_piC_iff]
    exact Or.inr rfl
  have hz'ker : θ ⟨z, c.z_mem_CX⟩ ∈ c'.piC.ker := by
    rw [MonoidHom.mem_ker, hθ]
    exact hzker
  rcases (c'.mem_ker_piC_iff (θ ⟨z, c.z_mem_CX⟩)).1 hz'ker with h1 | hz
  · exfalso
    have hz1 : (⟨z, c.z_mem_CX⟩ : ↥c.CX) = 1 := by
      apply θ.injective
      rw [show θ ⟨z, c.z_mem_CX⟩ = 1 from Subtype.ext h1, map_one]
    have hzG : z = 1 := congrArg Subtype.val hz1
    exact c.S.z_ne_one (by rw [c.S_z]; exact hzG)
  · exact Subtype.ext hz

end Loc49

end CFSG.Quasithin.H13.AS91
