module

public import CFSG.Quasithin.EmptyFaithful.SzN31CntGrpB
public import CFSG.Quasithin.EmptyFaithful.SzN31CntLinA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11 CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem card_linearEquiv_four (hV : Module.finrank (ZMod 2) V = 4) :
    Nat.card (V ≃ₗ[ZMod 2] V) = 20160 := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let bV := Module.finBasisOfFinrankEq (ZMod 2) V hV
  have h1 : Nat.card (V ≃ₗ[ZMod 2] V) =
      Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :=
    (Nat.card_congr ((Matrix.GeneralLinearGroup.toLin' bV).toEquiv.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toEquiv)).symm
  rw [h1, Matrix.card_GL_field, ZMod.card]
  decide

theorem card_eq_sixteen (hV : Module.finrank (ZMod 2) V = 4) : Nat.card V = 16 := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hV]
  norm_num

theorem card_linearEquiv_two (hV : Module.finrank (ZMod 2) V = 2) :
    Nat.card (V ≃ₗ[ZMod 2] V) = 6 := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let bV := Module.finBasisOfFinrankEq (ZMod 2) V hV
  have h1 : Nat.card (V ≃ₗ[ZMod 2] V) =
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) :=
    (Nat.card_congr ((Matrix.GeneralLinearGroup.toLin' bV).toEquiv.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toEquiv)).symm
  rw [h1, Matrix.card_GL_field, ZMod.card]
  decide

omit [Finite V] in
theorem mem_fixedSpace_zpowers_iff {h : V ≃ₗ[ZMod 2] V} {v : V} :
    v ∈ fixedSpace (Subgroup.zpowers h) ↔ h v = v := by
  refine ⟨fun hv => hv h (Subgroup.mem_zpowers h), fun hv k hk => ?_⟩
  have hinv : h⁻¹ v = v := by
    calc h⁻¹ v = h⁻¹ (h v) := by rw [hv]
      _ = v := CntLin.inv_apply_apply h v
  have key : ∀ n : ℤ, (h ^ n) v = v := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ i ih => rw [zpow_add_one, LinearEquiv.mul_apply, hv, ih]
    | pred i ih => rw [zpow_sub_one, LinearEquiv.mul_apply, hinv, ih]
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  exact key n

theorem fixed_modEq {q : ℕ} (hq : q.Prime) (P : Subgroup (V ≃ₗ[ZMod 2] V)) (hP : IsPGroup q P)
    (T : Submodule (ZMod 2) V) (hT : ∀ g ∈ P, ∀ v ∈ T, g v ∈ T) :
    2 ^ Module.finrank (ZMod 2) T ≡ 2 ^ Module.finrank (ZMod 2) ↥(T ⊓ fixedSpace P) [MOD q] := by
  have : Fact q.Prime := ⟨hq⟩
  let T' : SubMulAction P V := ⟨(T : Set V), fun g v hv => hT g g.2 v hv⟩
  have hmod := hP.card_modEq_card_fixedPoints T'
  have hfix : Nat.card (MulAction.fixedPoints P T') = Nat.card ↥(T ⊓ fixedSpace P) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨(a.1 : V), a.1.2, fun g hg => congrArg Subtype.val (a.2 ⟨g, hg⟩)⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, fun g => Subtype.ext (b.2.2 g g.2)⟩
        left_inv := fun a => rfl
        right_inv := fun b => rfl }
  have hcard : Nat.card T' = 2 ^ Module.finrank (ZMod 2) T := by
    have : Module.Finite (ZMod 2) T := Module.Finite.of_finite
    rw [show Nat.card T' = Nat.card T from Nat.card_congr (Equiv.refl _),
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcard' : Nat.card ↥(T ⊓ fixedSpace P) =
      2 ^ Module.finrank (ZMod 2) ↥(T ⊓ fixedSpace P) := by
    have : Module.Finite (ZMod 2) ↥(T ⊓ fixedSpace P) := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hfix, hcard, hcard'] at hmod
  exact hmod

theorem two_pow_mod_three (n : ℕ) : 2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs <;> omega

theorem three_group_finrank_mod_two (P : Subgroup (V ≃ₗ[ZMod 2] V)) (hP : IsPGroup 3 P)
    (T : Submodule (ZMod 2) V) (hT : ∀ g ∈ P, ∀ v ∈ T, g v ∈ T) :
    Module.finrank (ZMod 2) T % 2 = Module.finrank (ZMod 2) ↥(T ⊓ fixedSpace P) % 2 := by
  have h := fixed_modEq Nat.prime_three P hP T hT
  unfold Nat.ModEq at h
  rw [two_pow_mod_three, two_pow_mod_three] at h
  split_ifs at h <;> omega

theorem card_dvd_of_free (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hfree : ∀ h ∈ H, h ≠ 1 → ∀ v : V, h v = v → v = 0) : Nat.card H ∣ Nat.card V - 1 := by
  classical
  have : Fintype H := Fintype.ofFinite _
  have : Fintype V := Fintype.ofFinite _
  have : ∀ g : H, Fintype (MulAction.fixedBy V g) := fun g => Fintype.ofFinite _
  have : Fintype (MulAction.orbitRel.Quotient H V) := Fintype.ofFinite _
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H V
  have hterm : ∀ g : H, Fintype.card (MulAction.fixedBy V g) =
      1 + (if g = 1 then Fintype.card V - 1 else 0) := by
    intro g
    rw [← Nat.card_eq_fintype_card]
    by_cases hg : g = 1
    · subst hg
      have hset : MulAction.fixedBy V (1 : H) = Set.univ := by
        ext v
        simp
      rw [hset, Nat.card_univ, Nat.card_eq_fintype_card]
      have : 0 < Fintype.card V := Fintype.card_pos
      simp only [↓reduceIte]
      omega
    · have hset : MulAction.fixedBy V g = {0} := by
        ext v
        simp only [MulAction.mem_fixedBy, Set.mem_singleton_iff]
        constructor
        · intro hv
          exact hfree (g : V ≃ₗ[ZMod 2] V) g.2 (fun h => hg (Subtype.ext h)) v hv
        · rintro rfl
          exact smul_zero g
      rw [hset]
      simp [hg]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, smul_eq_mul, mul_one] at hburn
  have h1 : Nat.card H = Fintype.card H := Nat.card_eq_fintype_card
  have h2 : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  rw [h1, h2]
  have hd : Fintype.card H ∣ Fintype.card H + (Fintype.card V - 1) :=
    ⟨Fintype.card (MulAction.orbitRel.Quotient H V), by rw [hburn]; ring⟩
  exact (Nat.dvd_add_right (dvd_refl _)).1 hd

theorem card_dvd_nine_of_isPGroup_three (hV : Module.finrank (ZMod 2) V = 4)
    {Q : Subgroup (V ≃ₗ[ZMod 2] V)} (hQ : IsPGroup 3 Q) : Nat.card Q ∣ 9 := by
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : Nat.card Q ∣ 20160 :=
    (card_linearEquiv_four hV) ▸ Subgroup.card_subgroup_dvd_card Q
  rw [hk] at hdvd ⊢
  by_cases hk2 : k ≤ 2
  · exact (pow_dvd_pow 3 hk2).trans (by norm_num)
  · have h3 : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    exact absurd (h3.trans hdvd) (by norm_num)

theorem card_dvd_five_of_isPGroup_five (hV : Module.finrank (ZMod 2) V = 4)
    {Q : Subgroup (V ≃ₗ[ZMod 2] V)} (hQ : IsPGroup 5 Q) : Nat.card Q ∣ 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : Nat.card Q ∣ 20160 :=
    (card_linearEquiv_four hV) ▸ Subgroup.card_subgroup_dvd_card Q
  rw [hk] at hdvd ⊢
  by_cases hk1 : k ≤ 1
  · exact (pow_dvd_pow 5 hk1).trans (by norm_num)
  · have h5 : 5 ^ 2 ∣ 5 ^ k := pow_dvd_pow 5 (by omega)
    exact absurd (h5.trans hdvd) (by norm_num)

theorem prime_three_or_five_of_pCoreOf_ne_bot {Γ A : Subgroup (GLV V)} {m : ℕ}
    (hyp : G94Hyp Γ A m) (hV : Module.finrank (ZMod 2) V = 4) {p : ℕ} (hp : p.Prime)
    (hne : pCoreOf p Γ ≠ ⊥) : p = 3 ∨ p = 5 := by
  have hfix := g94_fixedSpace_pCoreOf_eq_bot hyp hne
  have hdvd := pgroup_dvd_two_pow hp (pCoreOf p Γ) (isPGroup_pCoreOf p Γ) ⊤
    (fun _ _ _ _ => Submodule.mem_top) (fun v _ hv => by
      have hv' : v ∈ fixedSpace (pCoreOf p Γ) := hv
      rw [hfix] at hv'
      simpa using hv')
  rw [finrank_top, hV] at hdvd
  have h15 : p ∣ 3 * 5 := by norm_num at hdvd ⊢; exact hdvd
  rcases (Nat.Prime.dvd_mul hp).1 h15 with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h)

end CFSG.Quasithin.SzN31
