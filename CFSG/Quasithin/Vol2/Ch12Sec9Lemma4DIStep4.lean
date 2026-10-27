module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep3

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

section Card

theorem card_GL_four {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (h : Module.finrank (ZMod 2) M = 4) : Nat.card (M ≃ₗ[ZMod 2] M) = 20160 := by
  classical
  haveI : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  let b := Module.finBasisOfFinrankEq (ZMod 2) M h
  let e : (M ≃ₗ[ZMod 2] M) ≃* GL (Fin 4) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) M).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, ZMod.card]
  decide

end Card

section Act

variable {G : Type} [Group G] [Finite G]

theorem linAct_eq_one_iff {I : Subgroup G} [IsMulCommutative ↥I]
    [Module (ZMod 2) (Additive ↥I)] (g : Subgroup.normalizer (I : Set G)) :
    linAct (V := I) g = 1 ↔ (g : G) ∈ Subgroup.centralizer (I : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hv : linAct (V := I) g (Additive.ofMul (⟨x, hx⟩ : ↥I)) = Additive.ofMul (⟨x, hx⟩ : ↥I) := by
      rw [h]
      rfl
    have hc := congrArg (fun y : Additive ↥I => ((Additive.toMul y : ↥I) : G)) hv
    rw [coe_linAct] at hc
    simp only [toMul_ofMul] at hc
    exact (mul_inv_eq_iff_eq_mul.1 hc).symm
  · intro h
    apply LinearEquiv.ext
    intro v
    show linAct (V := I) g v = v
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [coe_linAct]
    have hcm := Subgroup.mem_centralizer_iff.1 h ((Additive.toMul v : ↥I) : G) (Additive.toMul v).2
    show _ = ((Additive.toMul v : ↥I) : G)
    rw [← hcm]
    group

end Act

section Kappa

variable {G : Type} [Group G] [Finite G]

theorem exists_kappa {K₁ I V V₁ : Subgroup G} [IsMulCommutative ↥I]
    [Module (ZMod 2) (Additive ↥I)]
    (D : HatModelU (u128 V V₁)) (hK₁U : K₁ ≤ Subgroup.normalizer (u128 V V₁ : Set G))
    (hKI : K₁ ≤ Subgroup.normalizer (I : Set G))
    (hker : ∀ k : G, ∀ hk : k ∈ K₁, ∀ hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      D.ρ ⟨k, hkN⟩ = 1 ↔ k ∈ pCoreOf 2 K₁)
    (hkerI : K₁ ⊓ Subgroup.centralizer (I : Set G) = pCoreOf 2 K₁) :
    ∃ κ : ↥(D.img K₁) →* (Additive ↥I ≃ₗ[ZMod 2] Additive ↥I),
      ∀ k : G, ∀ hk : k ∈ K₁, ∀ hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G),
        ∀ hmem : D.ρ ⟨k, hkN⟩ ∈ D.img K₁,
          κ ⟨D.ρ ⟨k, hkN⟩, hmem⟩ = linAct (V := I) ⟨k, hKI hk⟩ := by
  let ρK : ↥K₁ →* (D.V ≃ₗ[ZMod 2] D.V) := D.ρ.comp (Subgroup.inclusion hK₁U)
  let aK : ↥K₁ →* (Additive ↥I ≃ₗ[ZMod 2] Additive ↥I) :=
    (linAct (V := I)).comp (Subgroup.inclusion hKI)
  have hrange : ρK.range = D.img K₁ := (L1294.img_eq_range D hK₁U).symm
  have hle : ρK.ker ≤ aK.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxK : (x : G) ∈ K₁ := x.2
    have hxN : (x : G) ∈ Subgroup.normalizer (u128 V V₁ : Set G) := hK₁U hxK
    have h1 : D.ρ ⟨(x : G), hxN⟩ = 1 := hx
    have h2 := (hker (x : G) hxK hxN).1 h1
    have h3 : (x : G) ∈ K₁ ⊓ Subgroup.centralizer (I : Set G) := by
      rw [hkerI]
      exact h2
    show linAct (V := I) ⟨(x : G), hKI hxK⟩ = 1
    exact (linAct_eq_one_iff _).2 h3.2
  let κ0 : ↥ρK.range →* (Additive ↥I ≃ₗ[ZMod 2] Additive ↥I) :=
    (QuotientGroup.lift ρK.ker aK hle).comp
      (QuotientGroup.quotientKerEquivRange ρK).symm.toMonoidHom
  refine ⟨κ0.comp (MulEquiv.subgroupCongr hrange.symm).toMonoidHom, ?_⟩
  intro k hk hkN hmem
  have e1 : (MulEquiv.subgroupCongr hrange.symm) ⟨D.ρ ⟨k, hkN⟩, hmem⟩ =
      ⟨ρK ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩⟩ := rfl
  have e2 : (QuotientGroup.quotientKerEquivRange ρK).symm ⟨ρK ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩⟩ =
      ((⟨k, hk⟩ : ↥K₁) : ↥K₁ ⧸ ρK.ker) := by
    apply (QuotientGroup.quotientKerEquivRange ρK).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  show κ0 (MulEquiv.subgroupCongr hrange.symm ⟨D.ρ ⟨k, hkN⟩, hmem⟩) = _
  rw [e1]
  show (QuotientGroup.lift ρK.ker aK hle)
      ((QuotientGroup.quotientKerEquivRange ρK).symm ⟨ρK ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩⟩) = _
  rw [e2, QuotientGroup.lift_mk]
  rfl


end Kappa

section Bij

variable {G : Type} [Group G] [Finite G]

theorem kappa_bijective {K₁ I V V₁ : Subgroup G} [IsMulCommutative ↥I]
    [Module (ZMod 2) (Additive ↥I)]
    (D : HatModelU (u128 V V₁)) (hK₁U : K₁ ≤ Subgroup.normalizer (u128 V V₁ : Set G))
    (hKI : K₁ ≤ Subgroup.normalizer (I : Set G))
    (hker : ∀ k : G, ∀ hk : k ∈ K₁, ∀ hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      D.ρ ⟨k, hkN⟩ = 1 ↔ k ∈ pCoreOf 2 K₁)
    (hkerI : K₁ ⊓ Subgroup.centralizer (I : Set G) = pCoreOf 2 K₁)
    {κ : ↥(D.img K₁) →* (Additive ↥I ≃ₗ[ZMod 2] Additive ↥I)}
    (hκ : ∀ k : G, ∀ hk : k ∈ K₁, ∀ hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      ∀ hmem : D.ρ ⟨k, hkN⟩ ∈ D.img K₁, κ ⟨D.ρ ⟨k, hkN⟩, hmem⟩ = linAct (V := I) ⟨k, hKI hk⟩)
    (hcardΩ : Nat.card (D.img K₁) = 20160)
    (hcardI : Nat.card (Additive ↥I ≃ₗ[ZMod 2] Additive ↥I) = 20160) :
    Function.Bijective κ := by
  have hinj : Function.Injective κ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    obtain ⟨γ, hγ⟩ := x
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).1 hγ
    have hx' := hκ k hk hkN hγ
    rw [hx'] at hx
    have h1 : k ∈ Subgroup.centralizer (I : Set G) :=
      (linAct_eq_one_iff ⟨k, hKI hk⟩).1 hx
    have h2 : k ∈ K₁ ⊓ Subgroup.centralizer (I : Set G) := ⟨hk, h1⟩
    rw [hkerI] at h2
    have h3 := (hker k hk hkN).2 h2
    apply Subtype.ext
    exact h3
  haveI : Finite (Additive ↥I ≃ₗ[ZMod 2] Additive ↥I) :=
    Finite.of_injective (fun f : Additive ↥I ≃ₗ[ZMod 2] Additive ↥I =>
      (f : Additive ↥I → Additive ↥I)) DFunLike.coe_injective
  exact (Nat.bijective_iff_injective_and_card κ).2 ⟨hinj, by rw [hcardΩ, hcardI]⟩

theorem linAct_eq_kappa {K₁ I V V₁ : Subgroup G} [IsMulCommutative ↥I]
    [Module (ZMod 2) (Additive ↥I)] (F0 : FactF0) (hI16 : Nat.card I = 16)
    (D : HatModelU (u128 V V₁)) (hK₁U : K₁ ≤ Subgroup.normalizer (u128 V V₁ : Set G))
    (hK₁H : K₁ ≤ Subgroup.normalizer (V₁ : Set G))
    (hKI : K₁ ≤ Subgroup.normalizer (I : Set G))
    (hker : ∀ k : G, ∀ hk : k ∈ K₁, ∀ hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      D.ρ ⟨k, hkN⟩ = 1 ↔ k ∈ pCoreOf 2 K₁)
    (hkerI : K₁ ⊓ Subgroup.centralizer (I : Set G) = pCoreOf 2 K₁)
    (hnormH : ∀ h ∈ Subgroup.normalizer (V₁ : Set G), ∀ k ∈ K₁, h * k * h⁻¹ ∈ K₁)
    {κ : ↥(D.img K₁) →* (Additive ↥I ≃ₗ[ZMod 2] Additive ↥I)}
    (hκ : ∀ k : G, ∀ hk : k ∈ K₁, ∀ hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      ∀ hmem : D.ρ ⟨k, hkN⟩ ∈ D.img K₁, κ ⟨D.ρ ⟨k, hkN⟩, hmem⟩ = linAct (V := I) ⟨k, hKI hk⟩)
    (hκbij : Function.Bijective κ)
    (x : G) (hxU : x ∈ Subgroup.normalizer (u128 V V₁ : Set G))
    (hxI : x ∈ Subgroup.normalizer (I : Set G)) (hxH : x ∈ Subgroup.normalizer (V₁ : Set G))
    (hxΩ : D.ρ ⟨x, hxU⟩ ∈ D.img K₁) :
    linAct (V := I) ⟨x, hxI⟩ = κ ⟨D.ρ ⟨x, hxU⟩, hxΩ⟩ := by
  obtain ⟨k, hk, hkN, hkρ⟩ := (L128A.HatU.mem_img D).1 hxΩ
  set c : G := k⁻¹ * x with hc
  have hcU : c ∈ Subgroup.normalizer (u128 V V₁ : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) hxU
  have hcI : c ∈ Subgroup.normalizer (I : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKI hk)) hxI
  have hcH : c ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hK₁H hk)) hxH
  have hρc : D.ρ ⟨c, hcU⟩ = 1 := by
    have e : (⟨c, hcU⟩ : Subgroup.normalizer (u128 V V₁ : Set G)) =
        ⟨k, hkN⟩⁻¹ * ⟨x, hxU⟩ := Subtype.ext (by simp [hc])
    rw [e, map_mul, map_inv, hkρ, inv_mul_cancel]
  set C : Additive ↥I ≃ₗ[ZMod 2] Additive ↥I := linAct (V := I) ⟨c, hcI⟩ with hCdef
  have hcomm : ∀ k' : G, ∀ hk' : k' ∈ K₁, ∀ hk'N : k' ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      C * linAct (V := I) ⟨k', hKI hk'⟩ = linAct (V := I) ⟨k', hKI hk'⟩ * C := by
    intro k' hk' hk'N
    have hmK : c * k' * c⁻¹ ∈ K₁ := hnormH c hcH k' hk'
    have hnK : c * k' * c⁻¹ * k'⁻¹ ∈ K₁ := Subgroup.mul_mem _ hmK (Subgroup.inv_mem _ hk')
    have hnN : c * k' * c⁻¹ * k'⁻¹ ∈ Subgroup.normalizer (u128 V V₁ : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hcU hk'N)
        (Subgroup.inv_mem _ hcU)) (Subgroup.inv_mem _ hk'N)
    have hρn : D.ρ ⟨c * k' * c⁻¹ * k'⁻¹, hnN⟩ = 1 := by
      have e : (⟨c * k' * c⁻¹ * k'⁻¹, hnN⟩ : Subgroup.normalizer (u128 V V₁ : Set G)) =
          ⟨c, hcU⟩ * ⟨k', hk'N⟩ * ⟨c, hcU⟩⁻¹ * ⟨k', hk'N⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hρc]
      simp
    have hn1 : linAct (V := I) ⟨c * k' * c⁻¹ * k'⁻¹, hKI hnK⟩ = 1 := by
      apply (linAct_eq_one_iff _).2
      have h2 : c * k' * c⁻¹ * k'⁻¹ ∈ K₁ ⊓ Subgroup.centralizer (I : Set G) := by
        rw [hkerI]
        exact (hker _ hnK hnN).1 hρn
      exact h2.2
    have hcI' : c * k' * c⁻¹ ∈ Subgroup.normalizer (I : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hcI (hKI hk')) (Subgroup.inv_mem _ hcI)
    have hm : linAct (V := I) ⟨c * k' * c⁻¹, hcI'⟩ = linAct (V := I) ⟨k', hKI hk'⟩ := by
      have e : (⟨c * k' * c⁻¹, hcI'⟩ : Subgroup.normalizer (I : Set G)) =
          ⟨c * k' * c⁻¹ * k'⁻¹, hKI hnK⟩ * ⟨k', hKI hk'⟩ := Subtype.ext (by simp)
      rw [e, map_mul, hn1, one_mul]
    have hconj : linAct (V := I) ⟨c * k' * c⁻¹, hcI'⟩ = C * linAct (V := I) ⟨k', hKI hk'⟩ * C⁻¹ := by
      have e : (⟨c * k' * c⁻¹, hcI'⟩ : Subgroup.normalizer (I : Set G)) =
          ⟨c, hcI⟩ * ⟨k', hKI hk'⟩ * ⟨c, hcI⟩⁻¹ := Subtype.ext (by simp)
      rw [e, map_mul, map_mul, map_inv]
    rw [hm] at hconj
    calc C * linAct (V := I) ⟨k', hKI hk'⟩
        = (C * linAct (V := I) ⟨k', hKI hk'⟩ * C⁻¹) * C := by group
      _ = linAct (V := I) ⟨k', hKI hk'⟩ * C := by rw [← hconj]
  have hgall : ∀ g : Additive ↥I ≃ₗ[ZMod 2] Additive ↥I, C * g = g * C := by
    intro g
    obtain ⟨a, ha⟩ := hκbij.2 g
    obtain ⟨a', ha'⟩ := a
    obtain ⟨k', hk', hk'N, hk'ρ⟩ := (L128A.HatU.mem_img D).1 ha'
    have hsub : (⟨a', ha'⟩ : ↥(D.img K₁)) = ⟨D.ρ ⟨k', hk'N⟩, L128A.HatU.rho_mem_img D hk' hk'N⟩ :=
      Subtype.ext hk'ρ.symm
    rw [← ha, hsub, hκ k' hk' hk'N _]
    exact hcomm k' hk' hk'N
  have hfin : Module.finrank (ZMod 2) (Additive ↥I) = 4 :=
    finrank_of_natCard (n := 4) (by rw [show Nat.card (Additive ↥I) = Nat.card ↥I from rfl, hI16]; norm_num)
  have hF0 := F0 (Additive ↥I) hfin C.toLinearMap (fun g v => by
    have := LinearEquiv.congr_fun (hgall g) v
    simpa using this)
  rcases hF0 with h0 | hid
  · exfalso
    haveI : Nontrivial (Additive ↥I) := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      show 1 < Nat.card ↥I
      rw [hI16]
      norm_num
    obtain ⟨v, hv⟩ := exists_ne (0 : Additive ↥I)
    have h1 : C v = 0 := LinearMap.congr_fun h0 v
    have h2 : C v = C 0 := by rw [h1, map_zero]
    exact hv (C.injective h2)
  · have hC1 : C = 1 := by
      apply LinearEquiv.ext
      intro v
      exact LinearMap.congr_fun hid v
    have hxk : (⟨x, hxI⟩ : Subgroup.normalizer (I : Set G)) =
        ⟨k, hKI hk⟩ * ⟨c, hcI⟩ := Subtype.ext (by simp [hc])
    rw [hxk, map_mul]
    have hCc : linAct (V := I) ⟨c, hcI⟩ = 1 := hC1
    rw [hCc, mul_one]
    have hfinal : κ ⟨D.ρ ⟨x, hxU⟩, hxΩ⟩ = κ ⟨D.ρ ⟨k, hkN⟩, L128A.HatU.rho_mem_img D hk hkN⟩ :=
      congrArg κ (Subtype.ext hkρ.symm)
    rw [hfinal, hκ k hk hkN _]

end Bij

end CFSG.Quasithin.H13.C1294
