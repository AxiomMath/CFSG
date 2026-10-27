module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.H13.KGInspOdd

open scoped commutatorElement

variable {X : Type*} [Group X]

theorem centralizes_of_card_le_four {K A : Subgroup X} [Finite A] (hK : ⁅K, K⁆ = K)
    (hKA : K ≤ Subgroup.normalizer (A : Set X)) (hA : Nat.card A ≤ 4) :
    ∀ k ∈ K, ∀ a ∈ A, k * a = a * k := by
  have hmem : ∀ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ ∈ A := fun k hk a ha =>
    (Subgroup.mem_normalizer_iff.mp (hKA hk) a).mp ha
  have hmem' : ∀ k ∈ K, ∀ a ∈ A, k⁻¹ * a * k ∈ A := fun k hk a ha => by
    have := hmem k⁻¹ (K.inv_mem hk) a ha
    rwa [inv_inv] at this
  let ψ : ↥K →* Equiv.Perm ↥A :=
    { toFun := fun k =>
        { toFun := fun a => ⟨k * a * k⁻¹, hmem k k.2 a a.2⟩
          invFun := fun a => ⟨k⁻¹ * a * k, hmem' k k.2 a a.2⟩
          left_inv := fun a => Subtype.ext (by simp [mul_assoc])
          right_inv := fun a => Subtype.ext (by simp [mul_assoc]) }
      map_one' := by
        ext a
        simp
      map_mul' := fun k l => by
        ext a
        simp [mul_assoc] }
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  have hsolv : Group.IsSolvable ψ.range := by
    have : Group.IsSolvable (Equiv.Perm ↥A) := Equiv.Perm.isSolvable hA
    infer_instance
  have hperf : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have htriv : ψ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ψ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable ψ.range hsolv
  intro k hk a ha
  have h1 : ψ ⟨k, hk⟩ = 1 := by
    have : ψ ⟨k, hk⟩ ∈ ψ.range := ⟨⟨k, hk⟩, rfl⟩
    rw [htriv, Subgroup.mem_bot] at this
    exact this
  have h2 := congrArg (fun σ : Equiv.Perm ↥A => ((σ ⟨a, ha⟩ : ↥A) : X)) h1
  simp only [ψ, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, Equiv.Perm.coe_one, id_eq,
    Subgroup.coe_inv] at h2
  calc k * a = k * a * k⁻¹ * k := by group
    _ = a * k := by rw [h2]

@[expose] def omegaZ (R : Subgroup X) : Subgroup X where
  carrier := {r | r ∈ R ∧ (∀ s ∈ R, r * s = s * r) ∧ r ^ 2 = 1}
  one_mem' := ⟨R.one_mem, fun s _ => by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hac, ha2⟩ ⟨hb, hbc, hb2⟩
    refine ⟨R.mul_mem ha hb, fun s hs => ?_, ?_⟩
    · rw [mul_assoc, hbc s hs, ← mul_assoc, hac s hs, mul_assoc]
    · rw [sq, mul_assoc, ← mul_assoc b, ← hac b hb, mul_assoc, ← mul_assoc, ← sq, ← sq, ha2, hb2,
        one_mul]
  inv_mem' := by
    rintro a ⟨ha, hac, ha2⟩
    refine ⟨R.inv_mem ha, fun s hs => ?_, by rw [inv_pow, ha2, inv_one]⟩
    have := hac s hs
    calc a⁻¹ * s = a⁻¹ * (s * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * s) * a⁻¹ := by rw [this]
      _ = s * a⁻¹ := by group

theorem omegaZ_le (R : Subgroup X) : omegaZ R ≤ R := fun _ h => h.1

theorem isElemAbelian_omegaZ (R : Subgroup X) : CFSG.Open.IsElemAbelian 2 (omegaZ R) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hx.2.2⟩
  exact a.2.2.1 b b.2.1

theorem exists_involution_centralized [Finite X] {K R : Subgroup X} (hK : ⁅K, K⁆ = K)
    (hKR : K ≤ Subgroup.normalizer (R : Set X)) (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hrank : ∀ E : Subgroup X, E ≤ R → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 4) :
    ∃ z ∈ R, orderOf z = 2 ∧ (∀ s ∈ R, z * s = s * z) ∧ ∀ k ∈ K, k * z = z * k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKΩ : K ≤ Subgroup.normalizer ((omegaZ R : Subgroup X) : Set X) := by
    intro k hk
    have hkR := hKR hk
    rw [Subgroup.mem_normalizer_iff]
    have hconj : ∀ g ∈ Subgroup.normalizer (R : Set X), ∀ y, y ∈ omegaZ R →
        g * y * g⁻¹ ∈ omegaZ R := by
      rintro g hg y ⟨hy, hyc, hy2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hy, fun s hs => ?_, ?_⟩
      · have hs' : g⁻¹ * s * g ∈ R := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) s).mp hs
          rwa [inv_inv] at this
        have := hyc _ hs'
        calc g * y * g⁻¹ * s = g * (y * (g⁻¹ * s * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * s * g) * y) * g⁻¹ := by rw [this]
          _ = s * (g * y * g⁻¹) := by group
      · rw [conj_pow, hy2, mul_one, mul_inv_cancel]
    intro y
    constructor
    · exact hconj k hkR y
    · intro h
      have := hconj k⁻¹ (Subgroup.inv_mem _ hkR) _ h
      simpa [mul_assoc] using this
  have hcard : Nat.card (omegaZ R) ≤ 4 := hrank _ (omegaZ_le R) (isElemAbelian_omegaZ R)
  have hcent := centralizes_of_card_le_four hK hKΩ hcard
  have hne : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR
  have hZ : Nontrivial (Subgroup.center ↥R) := hR2.center_nontrivial
  obtain ⟨m, -, hm⟩ := (hR2.to_le (le_refl R)).nontrivial_iff_card.mp hne
  have h2 : 2 ∣ Nat.card (Subgroup.center ↥R) := by
    obtain ⟨k, hk0, hk⟩ := (hR2.to_subgroup (Subgroup.center ↥R)).nontrivial_iff_card.mp hZ
    rw [hk]
    exact dvd_pow_self 2 hk0.ne'
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥R)) 2 h2
  set z : X := ((c : ↥R) : X) with hzdef
  have hzR : z ∈ R := (c : ↥R).2
  have hzo : orderOf z = 2 := by
    rw [hzdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  have hzc : ∀ s ∈ R, z * s = s * z := by
    intro s hs
    have := Subgroup.mem_center_iff.mp c.2 ⟨s, hs⟩
    exact (congrArg Subtype.val this).symm
  have hzΩ : z ∈ omegaZ R := ⟨hzR, hzc, by rw [← hzo, pow_orderOf_eq_one]⟩
  exact ⟨z, hzR, hzo, hzc, fun k hk => hcent k hk z hzΩ⟩

theorem commutator_central_mul_left {a b c : X} (hca : Commute c a) (hcb : Commute c b) :
    ⁅c * a, b⁆ = ⁅a, b⁆ := by
  have h : Commute c (a * b * a⁻¹) := (hca.mul_right hcb).mul_right hca.inv_right
  simp only [commutatorElement_def, mul_inv_rev]
  calc c * a * b * (a⁻¹ * c⁻¹) * b⁻¹ = (c * (a * b * a⁻¹)) * c⁻¹ * b⁻¹ := by group
    _ = (a * b * a⁻¹ * c) * c⁻¹ * b⁻¹ := by rw [h.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutator_central_mul_right {a b d : X} (hda : Commute d a) (hdb : Commute d b) :
    ⁅a, d * b⁆ = ⁅a, b⁆ := by
  have h : Commute d (a * b * a⁻¹ * b⁻¹) :=
    ((hda.mul_right hdb).mul_right hda.inv_right).mul_right hdb.inv_right
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * (d * b) * a⁻¹ * (b⁻¹ * d⁻¹) = (a * d) * b * a⁻¹ * b⁻¹ * d⁻¹ := by group
    _ = (d * a) * b * a⁻¹ * b⁻¹ * d⁻¹ := by rw [hda.eq]
    _ = (d * (a * b * a⁻¹ * b⁻¹)) * d⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹ * d) * d⁻¹ := by rw [h.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem centralizes_of_commutator_mem {K Z : Subgroup X} (hK : ⁅K, K⁆ = K) {x : X} (hZK : Z ≤ K)
    (hZ : ∀ c ∈ Z, ∀ k ∈ K, c * k = k * c) (hx : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ Z) :
    ∀ k ∈ K, x * k = k * x := by
  have hxk : ∀ k ∈ K, x * k * x⁻¹ = (x * k * x⁻¹ * k⁻¹) * k := fun k _ => by group
  let H : Subgroup X :=
    { carrier := {k | k ∈ K ∧ x * k = k * x}
      one_mem' := ⟨K.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨K.mul_mem ha hb, ?_⟩
        rw [← mul_assoc, ha', mul_assoc, hb', ← mul_assoc]
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨K.inv_mem ha, ?_⟩
        calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
          _ = a⁻¹ * (x * a) * a⁻¹ := by rw [ha']
          _ = a⁻¹ * x := by group }
  have hKH : ⁅K, K⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
    · set ca := x * a * x⁻¹ * a⁻¹ with hca
      set cb := x * b * x⁻¹ * b⁻¹ with hcb
      have hcaZ := hx a ha
      have hcbZ := hx b hb
      have e1 : x * ⁅a, b⁆ * x⁻¹ = ⁅x * a * x⁻¹, x * b * x⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      have hxa : x * a * x⁻¹ = ca * a := by rw [hca]; group
      have hxb : x * b * x⁻¹ = cb * b := by rw [hcb]; group
      have hcab : ca * b = b * ca := hZ ca hcaZ b hb
      have hcaa : ca * a = a * ca := hZ ca hcaZ a ha
      have hcbb : cb * b = b * cb := hZ cb hcbZ b hb
      have hcba : cb * a = a * cb := hZ cb hcbZ a ha
      have hcacb : ca * cb = cb * ca := hZ ca hcaZ cb (hZK hcbZ)
      have e2 : ⁅ca * a, cb * b⁆ = ⁅a, b⁆ := by
        have h1 : Commute ca a := hcaa
        have h2 : Commute ca (cb * b) :=
          Commute.mul_right (show Commute ca cb from hcacb) (show Commute ca b from hcab)
        rw [commutator_central_mul_left h1 h2]
        exact commutator_central_mul_right hcba hcbb
      have e3 : x * ⁅a, b⁆ * x⁻¹ = ⁅a, b⁆ := by rw [e1, hxa, hxb, e2]
      calc x * ⁅a, b⁆ = x * ⁅a, b⁆ * x⁻¹ * x := by group
        _ = ⁅a, b⁆ * x := by rw [e3]
  intro k hk
  exact (hKH (hK.symm ▸ hk)).2

end CFSG.Quasithin.H13.KGInspOdd
