module

public import CFSG.Quasithin.Background.SzG11TwoCommonForm

public section

namespace CFSG.Quasithin.G11.SzG11S.Two

open CFSG.Quasithin CFSG.Quasithin.SzG11NC CFSG.QuasithinUnique

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ X X₀ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V}

theorem sp4_abstract [Finite V] (hyp : G111Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)}
    (hirr : IsIrr H ⊤) (hHΓ : H ≤ Γ) (hnorm : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hE : Nat.card (CommF H hirr) = 4) (hV : Nat.card V = 256)
    (J : LinearMap.BilinForm (CommF H hirr) V) (hJalt : ∀ v, J v v = 0)
    (hJnd : J.Nondegenerate) (hJinv : ∀ h ∈ H, ∀ u v, J (h u) (h v) = J u v)
    (htv : ∀ (u : V) (t : CommF H hirr), ∃ h ∈ H, ∀ v, h v = v + (t * J v u) • u)
    (hex : ∃ x ∈ X, ∃ f ∈ endCommutant H, ∃ v, x (f v) ≠ f (x v)) : False := by
  classical
  have h2 : (2 : CommF H hirr) = 0 := two_eq_zero_of_card_four hE
  have hchar : CharP (CommF H hirr) 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨ℓ, hℓ⟩ := exists_nonzero_addHom (E := CommF H hirr)
  obtain ⟨c, hc0, hBc⟩ := exists_scalar_form hyp.toG101Hyp hirr hHΓ J hJnd hJinv ℓ hℓ
  have hiso : ∀ κ : CommF H hirr, B v₁ (κ • v₁) = 0 := by
    intro κ
    rw [hBc, map_smul, smul_eq_mul, hJalt, mul_zero, mul_zero, map_zero]
  have hYker : Ysp (CommF H hirr) B v₁ = LinearMap.ker (J v₁) := Ysp_eq_ker J ℓ hℓ hc0 hBc v₁
  have hMcard := card_Mq (E := CommF H hirr) (B := B) (v₁ := v₁) hE hyp.nondegenerate hyp.point
    hiso
  have hYcard : Nat.card (Ysp (CommF H hirr) B v₁) = 64 := by
    have := card_eq_four_mul_Ysp (E := CommF H hirr) (B := B) (v₁ := v₁) hE hyp.nondegenerate
      hyp.point
    omega
  obtain ⟨P, hP, n, hn, hdvd⟩ := rho_card_dvd hyp hirr hHΓ hnorm hE hex
  have hM16 : Nat.card (Mq (CommF H hirr) B v₁) = 16 := by omega
  have hn4 : n = 4 := by
    have : n ^ 2 = 4 ^ 2 := by rw [← hn, hM16]; norm_num
    exact Nat.pow_left_injective (by norm_num) this
  subst hn4
  have hfinV : Module.finrank (CommF H hirr) V = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := CommF H hirr) (V := V)
    rw [hE, hV] at h
    have : (4 : ℕ) ^ Module.finrank (CommF H hirr) V = 4 ^ 4 := by rw [← h]; norm_num
    exact Nat.pow_right_injective (by norm_num) this
  have hfinY : Module.finrank (CommF H hirr) (Ysp (CommF H hirr) B v₁) = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := CommF H hirr)
      (V := Ysp (CommF H hirr) B v₁)
    rw [hE, hYcard] at h
    have : (4 : ℕ) ^ Module.finrank (CommF H hirr) (Ysp (CommF H hirr) B v₁) = 4 ^ 3 := by
      rw [← h]; norm_num
    exact Nat.pow_right_injective (by norm_num) this
  have hA : ∃ u ∈ Ysp (CommF H hirr) B v₁, (∀ a : CommF H hirr, u ≠ a • v₁) ∧
      ∃ y ∈ Ysp (CommF H hirr) B v₁, J u y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hiso' : ∀ u ∈ Ysp (CommF H hirr) B v₁, ∀ y ∈ Ysp (CommF H hirr) B v₁, J u y = 0 := by
      intro u hu y hy
      by_cases hline : ∃ a : CommF H hirr, u = a • v₁
      · obtain ⟨a, rfl⟩ := hline
        have hy0 : J v₁ y = 0 := by
          rw [← LinearMap.mem_ker, ← hYker]
          exact hy
        rw [map_smul, LinearMap.smul_apply, hy0, smul_zero]
      · push Not at hline
        exact hcon u hu hline y hy
    have hle : Ysp (CommF H hirr) B v₁ ≤ J.orthogonal (Ysp (CommF H hirr) B v₁) := by
      intro y hy
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      exact hiso' u hu y hy
    have h1 := Submodule.finrank_mono hle
    rw [LinearMap.BilinForm.finrank_orthogonal hJnd, hfinV, hfinY] at h1
    omega
  obtain ⟨u, huY, hunot, y, hyY, hJuy⟩ := hA
  have hJv1u : J v₁ u = 0 := by
    rw [← LinearMap.mem_ker, ← hYker]
    exact huY
  have hJyu : J y u ≠ 0 := by
    intro h0
    apply hJuy
    have h := hJalt (y + u)
    simp only [map_add, LinearMap.add_apply, hJalt, zero_add, add_zero] at h
    simpa [h0] using h
  choose tv htvH htvapp using htv u
  have hJuu : J u u = 0 := hJalt u
  have htvC : ∀ t, tv t ∈ H ⊓ MulAction.stabilizer (GLV V) v₁ := by
    intro t
    refine ⟨htvH t, ?_⟩
    show tv t v₁ = v₁
    rw [htvapp, hJv1u, mul_zero, zero_smul, add_zero]
  have htv0 : tv 0 = 1 := by
    apply LinearEquiv.ext
    intro v
    rw [htvapp, zero_mul, zero_smul, add_zero]
    rfl
  have hmul : ∀ t t', tv (t + t') = tv t * tv t' := by
    intro t t'
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, htvapp, htvapp, htvapp, map_add, LinearMap.add_apply, map_smul,
      LinearMap.smul_apply, hJuu]
    simp only [smul_eq_mul, mul_zero, add_zero]
    rw [add_mul, add_smul]
    abel
  let τ : Multiplicative (CommF H hirr) →* ↥(H ⊓ MulAction.stabilizer (GLV V) v₁) :=
    { toFun := fun t => ⟨tv (Multiplicative.toAdd t), htvC _⟩
      map_one' := Subtype.ext htv0
      map_mul' := fun a b => Subtype.ext (hmul _ _) }
  let ρ := rhoStab hyp.toG101Hyp hirr hHΓ
  have hρmk : ∀ (c : ↥(H ⊓ MulAction.stabilizer (GLV V) v₁))
      (y' : Ysp (CommF H hirr) B v₁), ρ c (Submodule.Quotient.mk y') =
      Submodule.Quotient.mk ⟨(c : GLV V) y',
        (stab_prop hyp.toG101Hyp hirr hHΓ c c.2).2.2 y' y'.2⟩ :=
    fun c y' => rhoStab_mk hyp.toG101Hyp hirr hHΓ c y'
  have hinj : Function.Injective (ρ.comp τ) := by
    refine (injective_iff_map_eq_one _).2 fun t ht => ?_
    by_contra hne
    have ht0 : Multiplicative.toAdd t ≠ 0 := fun h => hne (toAdd_eq_zero.1 h)
    have h1 : ρ (τ t) (Submodule.Quotient.mk ⟨y, hyY⟩) = Submodule.Quotient.mk ⟨y, hyY⟩ := by
      have := congrArg (fun f => f (Submodule.Quotient.mk ⟨y, hyY⟩)) ht
      simpa using this
    rw [hρmk, Submodule.Quotient.eq] at h1
    obtain ⟨a, ha⟩ := mem_Nsp.1 h1
    have hτy : ((τ t : ↥(H ⊓ MulAction.stabilizer (GLV V) v₁)) : GLV V) y =
        y + (Multiplicative.toAdd t * J y u) • u := htvapp _ y
    have ha' : a • v₁ = (Multiplicative.toAdd t * J y u) • u := by
      rw [ha]
      simp only [AddSubgroupClass.coe_sub]
      rw [hτy]
      abel
    have hne0 : Multiplicative.toAdd t * J y u ≠ 0 := mul_ne_zero ht0 hJyu
    apply hunot ((Multiplicative.toAdd t * J y u)⁻¹ * a)
    rw [mul_smul, ha', smul_smul, inv_mul_cancel₀ hne0, one_smul]
  have hcard4 : Nat.card (MonoidHom.range (ρ.comp τ)) = 4 := by
    rw [← hE]
    exact ((Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans
      (Nat.card_congr Multiplicative.ofAdd).symm)
  have hdvd4 : 4 ∣ Nat.card ρ.range := by
    have hle : (ρ.comp τ).range ≤ ρ.range := by
      rintro _ ⟨t, rfl⟩
      exact ⟨τ t, rfl⟩
    have := Subgroup.card_dvd_of_le hle
    rwa [hcard4] at this
  let Q := A4.toSylow hP
  have hlow : 2 ^ 2 ≤ Nat.card (Subgroup.map ρ (Q : Subgroup _)) :=
    pow_le_card_map_sylow ρ Q (k := 2) (by simpa using hdvd4)
  have hQcoe : (Q : Subgroup ↥(H ⊓ MulAction.stabilizer (GLV V) v₁)) =
      P.subgroupOf (H ⊓ MulAction.stabilizer (GLV V) v₁) := A4.toSylow_coe hP
  have hpg : IsPGroup 2 ↥(Subgroup.map ρ (Q : Subgroup _)) := Q.isPGroup'.map ρ
  have : Finite ↥(Subgroup.map ρ (Q : Subgroup ↥(H ⊓ MulAction.stabilizer (GLV V) v₁))) := by
    have hQfin : Finite ↥(Q : Subgroup ↥(H ⊓ MulAction.stabilizer (GLV V) v₁)) := inferInstance
    exact Finite.of_surjective
      (fun x : ↥(Q : Subgroup ↥(H ⊓ MulAction.stabilizer (GLV V) v₁)) =>
        (⟨ρ x, Subgroup.mem_map_of_mem ρ x.2⟩ :
          ↥(Subgroup.map ρ (Q : Subgroup ↥(H ⊓ MulAction.stabilizer (GLV V) v₁)))))
      (by
        rintro ⟨_, ⟨x, hx, rfl⟩⟩
        exact ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨m, hm⟩ := hpg.exists_card_eq
  rw [hQcoe] at hm hlow
  rw [hm] at hlow hdvd
  have hm2 : 2 ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).1 hlow
  have h4 : 2 ^ 2 ∣ Nat.factorial (4 - 1) := (pow_dvd_pow 2 hm2).trans hdvd
  norm_num [Nat.factorial] at h4

end CFSG.Quasithin.G11.SzG11S.Two
