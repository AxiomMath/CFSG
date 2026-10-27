module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.G112A2

open Module

theorem not_dvd_card_GL {k : ℕ} (hk : k ≤ 5) : ¬ 27 ∣ Nat.card (GL (Fin k) (ZMod 2)) := by
  rw [Matrix.card_GL_field, ZMod.card]
  interval_cases k <;> norm_num [Fin.prod_univ_succ]

theorem card_linearEquiv {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] :
    Nat.card (W ≃ₗ[ZMod 2] W) = Nat.card (GL (Fin (finrank (ZMod 2) W)) (ZMod 2)) := by
  have e : W ≃ₗ[ZMod 2] (Fin (finrank (ZMod 2) W) → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simp)
  rw [Nat.card_congr (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)).toEquiv]
  apply Nat.card_congr
  exact { toFun := fun f => (e.symm.trans f).trans e
          invFun := fun g => (e.trans g).trans e.symm
          left_inv := fun f => by ext x; simp
          right_inv := fun g => by ext x; simp }

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

abbrev commW (z : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V :=
  LinearMap.range (z.toLinearMap - LinearMap.id)

theorem map_commW {z p : V ≃ₗ[ZMod 2] V} (h : p * z = z * p) :
    (commW z).map (p : V →ₗ[ZMod 2] V) = commW z := by
  have hle : (commW z).map (p : V →ₗ[ZMod 2] V) ≤ commW z := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨p x, ?_⟩
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f x) h
    simp only [LinearEquiv.mul_apply] at this
    simp [this]
  exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq p _)

theorem two_smul_zero (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem fix_eq_zero {P : Type} [Group P] [Finite P] (hP : Nat.card P = 27)
    (ι : P →* (V ≃ₗ[ZMod 2] V)) (hι : Function.Injective ι) (hV : finrank (ZMod 2) V ≤ 6)
    {c : P} (hc : c ∈ Subgroup.center P) (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1)
    (hcen : ∀ d ∈ Subgroup.center P, d = 1 ∨ d = c ∨ d = c ^ 2) :
    ∀ v, ι c v = v → v = 0 := by
  classical
  set z := ι c with hz
  have hz3 : z ^ 3 = 1 := by rw [hz, ← map_pow, hc3, map_one]
  have hzc : ∀ p : P, ι p * z = z * ι p := fun p => by
    rw [hz, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hc p)]
  have hz3' : ∀ x, z (z (z x)) = x := fun x => by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f x) hz3
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  intro v hv
  by_contra hv0
  have hdim : finrank (ZMod 2) (commW z) ≤ 5 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (z.toLinearMap - LinearMap.id)
    have hk : 1 ≤ finrank (ZMod 2) (LinearMap.ker (z.toLinearMap - LinearMap.id)) := by
      rw [Submodule.one_le_finrank_iff, Submodule.ne_bot_iff]
      exact ⟨v, by simp [hv], hv0⟩
    have : finrank (ZMod 2) (commW z) =
        finrank (ZMod 2) (LinearMap.range (z.toLinearMap - LinearMap.id)) := rfl
    omega
  let ρ : P →* (commW z ≃ₗ[ZMod 2] commW z) :=
    { toFun := fun p => LinearEquiv.ofSubmodules (ι p) (commW z) (commW z) (map_commW (hzc p))
      map_one' := by ext x; simp
      map_mul' := fun p q => by ext x; simp }
  have hρ : ∀ (p : P) (w : commW z), ((ρ p w : commW z) : V) = ι p w := fun _ _ => rfl
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    by_contra hne
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hpg : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
    haveI := hpg.isNilpotent
    obtain ⟨⟨d, hd⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    have hdk := (Subgroup.mem_inf.mp hd).1
    have hdc := (Subgroup.mem_inf.mp hd).2
    have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
    have hzW : ∀ w ∈ commW z, z w = w := by
      intro w hw
      have hdw : ι d w = w := by
        have := congrArg (fun f : commW z ≃ₗ[ZMod 2] commW z => ((f ⟨w, hw⟩ : commW z) : V))
          (MonoidHom.mem_ker.mp hdk)
        simpa [hρ] using this
      rcases hcen d hdc with h | h | h
      · exact absurd h hd1'
      · rwa [h] at hdw
      · rw [h, map_pow, pow_two, LinearEquiv.mul_apply] at hdw
        calc z w = z (z (z w)) := by rw [hdw]
          _ = w := hz3' w
    apply hc1
    apply hι
    rw [map_one, ← hz]
    ext x
    have h1 : z (z x - x) = z x - x := hzW _ ⟨x, by simp⟩
    rw [map_sub] at h1
    have h2 : z (z x) = x := by
      have h3 : z (z x) - z x + z x = z x - x + z x := by rw [h1]
      rw [sub_add_cancel, sub_add_eq_add_sub, two_smul_zero, zero_sub] at h3
      rw [h3]
      exact neg_eq_of_add_eq_zero_right (two_smul_zero x)
    have h3 := hz3' x
    rw [h2] at h3
    exact h3
  have hdvd := Subgroup.card_dvd_of_injective ρ hinj
  rw [hP, card_linearEquiv] at hdvd
  exact not_dvd_card_GL hdim hdvd

theorem exists_center_three {P : Type} [Group P] (h : Nat.card (Subgroup.center P) = 3) :
    ∃ c ∈ Subgroup.center P, c ≠ 1 ∧ c ^ 3 = 1 ∧
      ∀ d ∈ Subgroup.center P, d = 1 ∨ d = c ∨ d = c ^ 2 := by
  classical
  haveI : Finite (Subgroup.center P) := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  haveI : Nontrivial (Subgroup.center P) := Finite.one_lt_card_iff_nontrivial.mp (by rw [h]; norm_num)
  obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center P)
  have hord : orderOf c = 3 := by
    have hd : orderOf c ∣ 3 := h ▸ orderOf_dvd_natCard c
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hc1
    · exact h1
  have htop : Subgroup.zpowers c = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, h])
  refine ⟨c, c.2, fun h1 => hc1 (Subtype.ext h1), ?_, fun d hd => ?_⟩
  · have := pow_orderOf_eq_one c
    rw [hord] at this
    exact congrArg Subtype.val this
  · have hm : (⟨d, hd⟩ : Subgroup.center P) ∈ Subgroup.zpowers c := htop ▸ Subgroup.mem_top _
    rw [mem_zpowers_iff_mem_range_orderOf, hord] at hm
    simp only [Finset.mem_image, Finset.mem_range] at hm
    obtain ⟨k, hk, hkd⟩ := hm
    interval_cases k
    · left; have := congrArg Subtype.val hkd; simpa using this.symm
    · right; left; have := congrArg Subtype.val hkd; simpa using this.symm
    · right; right; have := congrArg Subtype.val hkd; simpa using this.symm


theorem g112ConclA2_concl3 (B : LinearMap.BilinForm (ZMod 2) V)
    (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V) (W : Submodule (ZMod 2) V)
    (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)) (hH : G111Hyp B Γ v₁ W X X₀) (h3 : G112Concl3Partial Γ) :
    ∀ t ∈ X, Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2 →
      v₁ ∈ LinearMap.range (t.toLinearMap - LinearMap.id) → (∀ v, B v (t v) = 0) →
      ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
        γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁ := by
  classical
  obtain ⟨hV, P, hPn, hPe, hP27, -, -, -⟩ := h3
  haveI : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hP27]; norm_num)
  obtain ⟨c, hc, hc1, hc3, hcen⟩ := exists_center_three hPe.center_order_p
  let ι : ↥P →* (V ≃ₗ[ZMod 2] V) := Γ.subtype.comp P.subtype
  have hι : Function.Injective ι := Γ.subtype_injective.comp P.subtype_injective
  set z := ι c with hz
  have hfix := fix_eq_zero hP27 ι hι hV.le hc hc1 hc3 hcen
  have hz3 : z ^ 3 = 1 := by rw [hz, ← map_pow, hc3, map_one]
  have hz3' : ∀ x, z (z (z x)) = x := fun x => by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f x) hz3
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  intro t ht hr _ _
  set tΓ : ↥Γ := ⟨t, hH.X_le ht⟩
  have hdP : tΓ * (c : ↥Γ) * tΓ⁻¹ ∈ P := hPn.conj_mem _ c.2 tΓ
  set d : ↥P := ⟨_, hdP⟩
  have hdc : d ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro p
    have hp' : tΓ⁻¹ * (p : ↥Γ) * tΓ⁻¹⁻¹ ∈ P := hPn.conj_mem _ p.2 tΓ⁻¹
    have hcp := Subgroup.mem_center_iff.mp hc ⟨_, hp'⟩
    have hcp' := congrArg (fun q : ↥P => (q : ↥Γ)) hcp
    simp only [Subgroup.coe_mul, inv_inv] at hcp'
    apply Subtype.ext
    simp only [d, Subgroup.coe_mul]
    calc (p : ↥Γ) * (tΓ * ↑c * tΓ⁻¹) = tΓ * ((tΓ⁻¹ * ↑p * tΓ) * ↑c) * tΓ⁻¹ := by group
      _ = tΓ * (↑c * (tΓ⁻¹ * ↑p * tΓ)) * tΓ⁻¹ := by rw [hcp']
      _ = tΓ * ↑c * tΓ⁻¹ * ↑p := by group
  have hd1 : d ≠ 1 := by
    intro h
    apply hc1
    have := congrArg (fun q : ↥P => (q : ↥Γ)) h
    simp only [d, OneMemClass.coe_one] at this
    have h2 : (c : ↥Γ) = 1 := by
      calc (c : ↥Γ) = tΓ⁻¹ * (tΓ * ↑c * tΓ⁻¹) * tΓ := by group
        _ = 1 := by rw [this]; group
    exact Subtype.ext h2
  have hdι : ι d = t * z * t⁻¹ := rfl
  rcases hcen d hdc with h | h | h
  · exact absurd h hd1
  ·
    have htz : t * z = z * t := by
      have := hdι
      rw [h, ← hz] at this
      calc t * z = (t * z * t⁻¹) * t := by group
        _ = z * t := by rw [← this]
    refine ⟨z, (c : ↥Γ).2, ?_, fun h1 => hH.point (hfix v₁ h1)⟩
    rintro w ⟨x, rfl⟩
    refine ⟨z x, ?_⟩
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f x) htz
    simp only [LinearEquiv.mul_apply] at this
    simp [this]
  ·
    exfalso
    have htz : ∀ x, t (z x) = z (z (t x)) := by
      intro x
      have := hdι
      rw [h, map_pow, ← hz] at this
      have h2 : t * z = z ^ 2 * t := by
        calc t * z = (t * z * t⁻¹) * t := by group
          _ = z ^ 2 * t := by rw [← this]
      have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f x) h2
      simpa [pow_two, LinearEquiv.mul_apply] using this
    set K := LinearMap.ker (t.toLinearMap - LinearMap.id) with hK
    have hmemK : ∀ x, x ∈ K ↔ t x = x := fun x => by
      simp [hK, sub_eq_zero]
    have hinf : K ⊓ K.map (z : V →ₗ[ZMod 2] V) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro y ⟨hyK, x, hxK, rfl⟩
      have hx : t x = x := (hmemK x).mp hxK
      have hy : t (z x) = z x := (hmemK _).mp hyK
      rw [htz, hx] at hy
      have hzx : z x = x := by
        calc z x = z (z (z (z x))) := by rw [hz3']
          _ = z (z (z x)) := congrArg (fun y => z (z y)) hy
          _ = x := hz3' x
      simp [hfix x hzx]
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq K (K.map (z : V →ₗ[ZMod 2] V))
    rw [hinf, finrank_bot, add_zero, LinearEquiv.finrank_map_eq] at hsum
    have hle : finrank (ZMod 2) ↥(K ⊔ K.map (z : V →ₗ[ZMod 2] V)) ≤ 6 :=
      hV ▸ Submodule.finrank_le _
    have hrn := LinearMap.finrank_range_add_finrank_ker (t.toLinearMap - LinearMap.id)
    rw [hV, ← hK, hr] at hrn
    omega

end CFSG.Quasithin.G112A2
