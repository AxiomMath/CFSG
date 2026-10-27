module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.OddTranspositions

open Equiv

set_option maxRecDepth 20000 in
theorem perm_outer_facts : ∀ π : Perm (Fin 5), π * π = 1 → Perm.sign π ≠ 1 →
    ∀ k : alternatingGroup (Fin 5), k * k = 1 → k ≠ 1 → π * (k : Perm (Fin 5)) = k * π →
      (∃ k' : alternatingGroup (Fin 5), k' * k' = 1 ∧ π * (k' : Perm (Fin 5)) = k' * π ∧
        (k * k') ^ 3 = 1 ∧ k * k' ≠ 1) ∧
      ∃ h : alternatingGroup (Fin 5),
        π * (h : Perm (Fin 5)) * π⁻¹ = ((h * k : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
  decide

variable {G : Type} [Group G]

theorem exists_pair_and_twist_of_outer {K₁ : Subgroup G} (e : K₁ ≃* alternatingGroup (Fin 5))
    {a : G} (ha2 : a * a = 1) (haK : a ∈ Subgroup.normalizer (K₁ : Set G))
    (hout : ¬ ∃ k ∈ K₁, ∀ x ∈ K₁, a * x * a⁻¹ = k * x * k⁻¹)
    {k : G} (hkK : k ∈ K₁) (hkk : k * k = 1) (hk1 : k ≠ 1) (hak : Commute a k) :
    (∃ k' ∈ K₁, k' * k' = 1 ∧ Commute a k' ∧ orderOf (k * k') = 3) ∧
      ∃ h ∈ K₁, h * (a * k) * h⁻¹ = a := by
  classical
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hmem : ∀ x : G, x ∈ K₁ → a * x * a⁻¹ ∈ K₁ := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp haK x).mp hx
  have hback : ∀ x : G, a * (a * x * a⁻¹) * a⁻¹ = x := fun x => by
    rw [hainv, show a * (a * x * a) * a = (a * a) * x * (a * a) by group, ha2]; group
  let φ : K₁ ≃* K₁ :=
    { toFun := fun x => ⟨a * x * a⁻¹, hmem x x.2⟩
      invFun := fun x => ⟨a * x * a⁻¹, hmem x x.2⟩
      left_inv := fun x => Subtype.ext (hback x)
      right_inv := fun x => Subtype.ext (hback x)
      map_mul' := fun x y => Subtype.ext (by
        change a * ((x : G) * y) * a⁻¹ = a * x * a⁻¹ * (a * y * a⁻¹)
        group) }
  have hφ : ∀ x : K₁, (φ x : G) = a * x * a⁻¹ := fun x => rfl
  have hφφ : ∀ x : K₁, φ (φ x) = x := fun x => Subtype.ext (hback x)
  let ψ : MulAut (alternatingGroup (Fin 5)) := (e.symm.trans φ).trans e
  have hψ : ∀ y, ψ y = e (φ (e.symm y)) := fun y => rfl
  have hψ' : ∀ y, e.symm (ψ y) = φ (e.symm y) := fun y => by
    rw [hψ, MulEquiv.symm_apply_apply]
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)
  obtain ⟨π, hπ⟩ := hbij.2 ψ
  have key : ∀ y : alternatingGroup (Fin 5),
      ((ψ y : alternatingGroup (Fin 5)) : Perm (Fin 5)) = π * y * π⁻¹ := fun y => by
    rw [← hπ, MulAut.conjNormal_apply]
  have hππ : π * π = 1 := by
    apply hbij.1
    rw [map_mul, hπ, map_one]
    exact MulEquiv.ext fun y => by
      rw [MulAut.mul_apply, MulAut.one_apply, hψ, hψ, MulEquiv.symm_apply_apply, hφφ,
        MulEquiv.apply_symm_apply]
  have hψfix : ∀ y : alternatingGroup (Fin 5), π * (y : Perm (Fin 5)) = y * π → ψ y = y :=
    fun y h => Subtype.ext (by
      rw [key, h, mul_inv_cancel_right])
  have hπodd : Perm.sign π ≠ 1 := by
    intro hsign
    have hπA : π ∈ alternatingGroup (Fin 5) := Perm.mem_alternatingGroup.mpr hsign
    apply hout
    refine ⟨e.symm ⟨π, hπA⟩, (e.symm ⟨π, hπA⟩).2, fun x hx => ?_⟩
    have h1 : ψ (e ⟨x, hx⟩) = ⟨π, hπA⟩ * e ⟨x, hx⟩ * (⟨π, hπA⟩ : alternatingGroup (Fin 5))⁻¹ :=
      Subtype.ext (by rw [key]; rfl)
    have h2 := congrArg Subtype.val (hψ' (e ⟨x, hx⟩))
    rw [h1, MulEquiv.symm_apply_apply, hφ, map_mul, map_mul, map_inv,
      MulEquiv.symm_apply_apply] at h2
    simpa using h2.symm
  set k₀ := e ⟨k, hkK⟩ with hk₀def
  have hkK' : e.symm k₀ = ⟨k, hkK⟩ := by rw [hk₀def, MulEquiv.symm_apply_apply]
  have hk₀ : k₀ * k₀ = 1 := by
    rw [hk₀def, ← map_mul, show (⟨k, hkK⟩ : K₁) * ⟨k, hkK⟩ = 1 from Subtype.ext hkk, map_one]
  have hk₀1 : k₀ ≠ 1 := fun h => hk1 (by
    have := congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
    simpa using this)
  have hψk : ψ k₀ = k₀ := by
    rw [hψ, hkK']
    congr 1
    exact Subtype.ext (by rw [hφ]; change a * k * a⁻¹ = k; rw [hak.eq, mul_inv_cancel_right])
  have hπk : π * (k₀ : Perm (Fin 5)) = k₀ * π := by
    have h := key k₀
    rw [hψk] at h
    calc π * (k₀ : Perm (Fin 5)) = π * k₀ * π⁻¹ * π := by group
      _ = k₀ * π := by rw [← h]
  obtain ⟨⟨k₀', hk₀'2, hπk', hcube, hne⟩, h₀, hh₀⟩ :=
    perm_outer_facts π hππ hπodd k₀ hk₀ hk₀1 hπk
  refine ⟨⟨e.symm k₀', (e.symm k₀').2, ?_, ?_, ?_⟩, e.symm h₀, (e.symm h₀).2, ?_⟩
  · have := congrArg Subtype.val (show e.symm k₀' * e.symm k₀' = 1 by
      rw [← map_mul, hk₀'2, map_one])
    simpa using this
  · have h := congrArg Subtype.val (hψ' k₀')
    rw [hψfix k₀' hπk', hφ] at h
    change a * _ = _ * a
    calc a * ((e.symm k₀' : K₁) : G) = a * (e.symm k₀' : K₁) * a⁻¹ * a := by group
      _ = ((e.symm k₀' : K₁) : G) * a := by rw [← h]
  · have hval : k * ((e.symm k₀' : K₁) : G) = ((e.symm (k₀ * k₀') : K₁) : G) := by
      rw [map_mul, hkK']; rfl
    have h3 : (k * ((e.symm k₀' : K₁) : G)) ^ 3 = 1 := by
      rw [hval, ← Subgroup.coe_pow, ← map_pow, hcube, map_one, Subgroup.coe_one]
    have h1 : k * ((e.symm k₀' : K₁) : G) ≠ 1 := by
      rw [hval]
      intro h
      apply hne
      have : e.symm (k₀ * k₀') = 1 := Subtype.ext h
      simpa using congrArg e this
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime h3 h1
  ·
    have hψh : ψ h₀ = h₀ * k₀ := Subtype.ext (by rw [key, hh₀])
    have h := congrArg Subtype.val (hψ' h₀)
    rw [hψh, hφ, map_mul, hkK'] at h
    set hG : G := ((e.symm h₀ : K₁) : G) with hhG
    have hah : a * hG = hG * k * a := by
      calc a * hG = a * hG * a⁻¹ * a := by group
        _ = hG * k * a := by rw [← h]; rfl
    calc hG * (a * k) * hG⁻¹ = hG * (k * a) * hG⁻¹ := by rw [hak.eq]
      _ = (hG * k * a) * hG⁻¹ := by group
      _ = a := by rw [← hah, mul_inv_cancel_right]

end CFSG.OddTranspositions

end
