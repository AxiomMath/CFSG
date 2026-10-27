module

public import CFSG.Quasithin.Background.SzG11TwoCommonForm

public section

namespace CFSG.Quasithin.G11.SzG11S.Two

open CFSG.Quasithin CFSG.Quasithin.SzG11NC CFSG.QuasithinUnique

theorem card_linearEquiv_sixteen (L : Type) [AddCommGroup L] [Module (ZMod 2) L] [Finite L]
    (hL : Nat.card L = 16) : Nat.card (L ≃ₗ[ZMod 2] L) = 20160 := by
  have hfin : Module.finrank (ZMod 2) L = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := L)
    rw [hL, Nat.card_zmod] at h
    have : (2 : ℕ) ^ Module.finrank (ZMod 2) L = 2 ^ 4 := by rw [← h]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  let b : Module.Basis (Fin 4) (ZMod 2) L := Module.finBasisOfFinrankEq (ZMod 2) L hfin
  let e : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) ≃* (L ≃ₗ[ZMod 2] L) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) L)
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  simp [Fin.prod_univ_four, ZMod.card]

section

variable {E : Type} [Field E] {M : Type} [AddCommGroup M] [Module E M]

@[expose] def addAutFix (x : M →+ M) (a : M ≃ₗ[E] M) (ha : ∀ m, a (x m) = x (a m)) :
    fixAdd x ≃+ fixAdd x :=
  { permFix x a ha with map_add' := fun l l' => Subtype.ext (map_add a l.1 l'.1) }

theorem card_centralizer_dvd_gl [Finite E] [Finite M] (hE : Nat.card E = 4) (x : M →+ M)
    (hx : ∀ (e : E) (m : M), x (e • m) = e ^ 2 • x m) (hxx : ∀ m, x (x m) = m)
    (hM : Nat.card M = 256) (A : Subgroup (M ≃ₗ[E] M))
    (hA : ∀ a ∈ A, ∀ m, a (x m) = x (a m)) : Nat.card A ∣ 20160 := by
  obtain ⟨ω, -, -, -, hdec⟩ := frob_decomp hE x hx hxx
  have h2 : (2 : E) = 0 := two_eq_zero_of_card_four hE
  have hL16 : Nat.card (fixAdd x) = 16 := by
    have h1 := card_eq_sq hE x hx hxx
    have : Nat.card (fixAdd x) ^ 2 = 16 ^ 2 := by rw [← h1, hM]; norm_num
    exact Nat.pow_left_injective (by norm_num) this
  have hll : ∀ l : fixAdd x, 2 • l = 0 := by
    intro l
    apply Subtype.ext
    show 2 • (l : M) = 0
    rw [← Nat.cast_smul_eq_nsmul E, Nat.cast_ofNat, h2, zero_smul]
  let _ : Module (ZMod 2) (fixAdd x) := AddCommGroup.zmodModule hll
  let f : A →* (fixAdd x ≃ₗ[ZMod 2] fixAdd x) :=
    { toFun := fun a =>
        { addAutFix x a.1 (hA a.1 a.2) with
          map_smul' := fun c l => ZMod.map_smul (addAutFix x a.1 (hA a.1 a.2)) c l }
      map_one' := by
        ext l
        rfl
      map_mul' := fun a b => by
        ext l
        rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply LinearEquiv.ext
    intro m
    obtain ⟨l₁, h₁, l₂, h₂, rfl⟩ := hdec m
    have e : ∀ (l : M) (hl : l ∈ fixAdd x), a.1 l = b.1 l := fun l hl =>
      congrArg (fun g : fixAdd x ≃ₗ[ZMod 2] fixAdd x => ((g ⟨l, hl⟩ : fixAdd x) : M)) hab
    rw [map_add, map_add, map_smul, map_smul, e l₁ h₁, e l₂ h₂]
  have hdvd := Subgroup.card_dvd_of_injective f hf
  rwa [card_linearEquiv_sixteen _ hL16] at hdvd

end

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ X X₀ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V}

theorem rho_card_dvd_gl [Finite V] (hyp : G111Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)}
    (hirr : IsIrr H ⊤) (hHΓ : H ≤ Γ) (hnorm : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hE : Nat.card (CommF H hirr) = 4) (hM : Nat.card (Mq (CommF H hirr) B v₁) = 256)
    (hex : ∃ x ∈ X, ∃ f ∈ endCommutant H, ∃ v, x (f v) ≠ f (x v)) :
    ∃ P : Subgroup (GLV V), IsSylowTwoOf P (H ⊓ MulAction.stabilizer (GLV V) v₁) ∧
      Nat.card (Subgroup.map (rhoStab hyp.toG101Hyp hirr hHΓ)
        (P.subgroupOf (H ⊓ MulAction.stabilizer (GLV V) v₁))) ∣ 20160 := by
  obtain ⟨P, hP, x, hx, hxx, hcomm⟩ := exists_xbar_commuting hyp hirr hHΓ hnorm hE hex
  have : Finite (Mq (CommF H hirr) B v₁) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  refine ⟨P, hP, ?_⟩
  refine card_centralizer_dvd_gl hE x hx hxx hM _ ?_
  rintro a ⟨p, hp, rfl⟩ m
  exact hcomm p (Subgroup.mem_subgroupOf.1 hp) m

theorem g2_abstract [Finite V] (hyp : G111Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)}
    (hirr : IsIrr H ⊤) (hHΓ : H ≤ Γ) (hnorm : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hE : Nat.card (CommF H hirr) = 4) (hV : Nat.card V = 4096)
    (J : LinearMap.BilinForm (CommF H hirr) V) (hJalt : ∀ v, J v v = 0)
    (hJnd : J.Nondegenerate) (hJinv : ∀ h ∈ H, ∀ u v, J (h u) (h v) = J u v)
    (hlow : Ysp (CommF H hirr) B v₁ = LinearMap.ker (J v₁) →
      2 ^ 7 ∣ Nat.card (rhoStab hyp.toG101Hyp hirr hHΓ).range)
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
  have hM : Nat.card (Mq (CommF H hirr) B v₁) = 256 := by omega
  obtain ⟨P, hP, hdvd⟩ := rho_card_dvd_gl hyp hirr hHΓ hnorm hE hM hex
  let ρ := rhoStab hyp.toG101Hyp hirr hHΓ
  let Q := A4.toSylow hP
  have hlow7 : 2 ^ 7 ≤ Nat.card (Subgroup.map ρ (Q : Subgroup _)) :=
    pow_le_card_map_sylow ρ Q (k := 7) (hlow hYker)
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
  rw [hQcoe] at hm hlow7
  rw [hm] at hlow7 hdvd
  have hm7 : 7 ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).1 hlow7
  have h7 : 2 ^ 7 ∣ 20160 := (pow_dvd_pow 2 hm7).trans hdvd
  norm_num at h7

end CFSG.Quasithin.G11.SzG11S.Two
