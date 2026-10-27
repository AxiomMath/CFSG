module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Front
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairHyp
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45R24Lin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement
open scoped Pointwise

variable {p : ℕ} {G : Type} [Group G] [Finite G] {D : Subgroup G}

private noncomputable abbrev singletonZX (x : ↥(Xof G)) : Subgroup G :=
  Subgroup.closure ({(x : G)} : Set G) ⊔ ZXof G

private noncomputable def uc45_alt5_equiv (c : Ctx45 p G D)
    (hker : Wker G = CFSG.pPrimeCore 3 G) :
    (G ⧸ Wker G) ≃* ↥(alternatingGroup (Fin 5)) :=
  (QuotientGroup.quotientMulEquivOfEq hker).trans c.alt5.some

private theorem uc45_singletonZX_abelian (c : Pre45 p G D) (x : ↥(Xof G)) :
    IsMulCommutative ↥(singletonZX x) := by
  have hxcent : (x : G) ∈ Subgroup.centralizer
      (Subgroup.closure ({(x : G)} : Set G) : Set G) := by
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_singleton_iff]
  have hxcentY : (x : G) ∈ Subgroup.centralizer (singletonZX x : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    change y ∈ Subgroup.closure ({(x : G)} : Set G) ⊔ ZXof G at hy
    have hmem : y ∈ (Subgroup.closure ({(x : G)} : Set G) : Set G) * (ZXof G : Set G) := by
      rw [← Subgroup.mul_normal]
      exact hy
    rw [Set.mem_mul] at hmem
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem
    obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.mp ha
    have h1 : (x : G) ^ n * x = x * (x : G) ^ n :=
      Subgroup.mem_centralizer_iff.mp hxcent ((x : G) ^ n)
        ((Subgroup.closure ({(x : G)} : Set G)).zpow_mem
          (Subgroup.mem_closure_singleton_self (x : G)) n)
    have h2 : b * (x : G) = (x : G) * b :=
      (Subgroup.mem_center_iff.mp (c.ZX_le hb) (x : G)).symm
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  refine Subgroup.le_centralizer_iff_isMulCommutative.mp ?_
  change Subgroup.closure ({(x : G)} : Set G) ⊔ ZXof G ≤
    Subgroup.centralizer (singletonZX x : Set G)
  refine sup_le ?_ ?_
  · rw [Subgroup.closure_le, Set.singleton_subset_iff]
    exact hxcentY
  · intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact Subgroup.mem_center_iff.mp (c.ZX_le hz) y

private theorem uc45_singletonZX_normal (x : ↥(Xof G))
    (hxfix : ∀ g : G, MulAut.conjNormal g x * x⁻¹ ∈ Subgroup.center ↥(Xof G)) :
    (singletonZX x).Normal := by
  refine ⟨fun y hy g => ?_⟩
  change y ∈ Subgroup.closure ({(x : G)} : Set G) ⊔ ZXof G at hy
  have hmem : y ∈ (Subgroup.closure ({(x : G)} : Set G) : Set G) * (ZXof G : Set G) := by
    rw [← Subgroup.mul_normal]
    exact hy
  rw [Set.mem_mul] at hmem
  obtain ⟨a, ha, b, hb, rfl⟩ := hmem
  obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.mp ha
  have hzx : ((MulAut.conjNormal g x * x⁻¹ : ↥(Xof G)) : G) ∈ ZXof G :=
    Subgroup.mem_map.mpr ⟨_, hxfix g, rfl⟩
  have hgx : g * (x : G) * g⁻¹ ∈ singletonZX x := by
    have he : g * (x : G) * g⁻¹ =
        ((MulAut.conjNormal g x * x⁻¹ : ↥(Xof G)) : G) * (x : G) := by
      simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [he]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hzx)
      (Subgroup.mem_sup_left (Subgroup.mem_closure_singleton_self (x : G)))
  have he : g * ((x : G) ^ n * b) * g⁻¹ =
      (g * (x : G) * g⁻¹) ^ n * (g * b * g⁻¹) := by
    calc g * ((x : G) ^ n * b) * g⁻¹
        = (g * (x : G) ^ n * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (g * (x : G) * g⁻¹) ^ n * (g * b * g⁻¹) := by
          rw [← conj_zpow (a := g) (b := (x : G)) (i := n)]
  rw [he]
  change (g * (x : G) * g⁻¹) ^ n * (g * b * g⁻¹) ∈
    Subgroup.closure ({(x : G)} : Set G) ⊔ ZXof G
  exact Subgroup.mul_mem _ ((singletonZX x).zpow_mem hgx n)
    (Subgroup.mem_sup_right ((zxof_normal (G := G)).conj_mem b hb g))

private theorem uc45_fixed_vector_eq_zero
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (φ : (G ⧸ Wker G) →* (W ≃ₗ[ZMod 2] W)) (π : ↥(Xof G) →* Multiplicative W)
    (hπsurj : Function.Surjective π) (hπker : π.ker = Subgroup.center ↥(Xof G))
    (hequiv : ∀ (g : G) (x : ↥(Xof G)), π (MulAut.conjNormal g x) =
      Multiplicative.ofAdd (φ (QuotientGroup.mk g) (Multiplicative.toAdd (π x))))
    (c : Pre45 p G D) :
    ∀ w : W, (∀ γ : G ⧸ Wker G, φ γ w = w) → w = 0 := by
  intro w₀ hw₀
  obtain ⟨x, hx⟩ := hπsurj (Multiplicative.ofAdd w₀)
  have hxfix : ∀ g : G, MulAut.conjNormal g x * x⁻¹ ∈ Subgroup.center ↥(Xof G) := by
    intro g
    have hconj : π (MulAut.conjNormal g x) = π x := by
      rw [hequiv g x, hx]
      simp only [toAdd_ofAdd]
      rw [hw₀]
    rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hconj, mul_inv_cancel]
  haveI : (singletonZX x).Normal := uc45_singletonZX_normal x hxfix
  have hleX : singletonZX x ≤ Xof G := by
    change Subgroup.closure ({(x : G)} : Set G) ⊔ ZXof G ≤ Xof G
    refine sup_le ?_ ?_
    · rw [Subgroup.closure_le, Set.singleton_subset_iff]
      exact x.2
    · exact Subgroup.map_subtype_le _
  have hY2 : IsPGroup 2 (singletonZX x) := (xof_isPGroup (G := G)).to_le hleX
  have hcenter : singletonZX x ≤ Subgroup.center G :=
    uc45_normal_abelian_le_center c.toBase45 (singletonZX x) hY2
      (uc45_singletonZX_abelian c x)
  have hxY : (x : G) ∈ singletonZX x :=
    Subgroup.mem_sup_left (Subgroup.mem_closure_singleton_self (x : G))
  have hxcentG : (x : G) ∈ Subgroup.center G := hcenter hxY
  have hxcentX : x ∈ Subgroup.center ↥(Xof G) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxcentG (y : G)
  have hx1 : π x = 1 := by
    rw [← MonoidHom.mem_ker, hπker]
    exact hxcentX
  have hof : (Multiplicative.ofAdd w₀ : Multiplicative W) = 1 := by rw [← hx, hx1]
  simpa using congrArg Multiplicative.toAdd hof

private theorem uc45_commSpace_finrank_generator (c : Ctx45 p G D)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (φ : (G ⧸ Wker G) →* (W ≃ₗ[ZMod 2] W))
    (hcard : ∀ g : G, Nat.card ↥(⁅Xof G, Subgroup.zpowers g⁆ ⊔ ZXof G) =
      Nat.card ↥(ZXof G) * 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.range
        ((φ (QuotientGroup.mk g) : W →ₗ[ZMod 2] W) - LinearMap.id)))
    {d : G} (hd : Subgroup.zpowers d = D) :
    Module.finrank (ZMod 2) ↥(LinearMap.range
      ((φ (QuotientGroup.mk d) : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2 := by
  have hZXpos : 0 < Nat.card ↥(ZXof G) := by
    haveI : Nonempty ↥(ZXof G) := ⟨1, by simp⟩
    exact Nat.card_pos
  have hcardd := hcard d
  rw [uc45_card_commutator_zpowers c.toPre45 hd] at hcardd
  have hmul : Nat.card ↥(ZXof G) * 4 = Nat.card ↥(ZXof G) *
      2 ^ Module.finrank (ZMod 2) ↥(LinearMap.range
        ((φ (QuotientGroup.mk d) : W →ₗ[ZMod 2] W) - LinearMap.id)) := by
    rw [mul_comm (Nat.card ↥(ZXof G)) 4]
    exact hcardd
  have hpow : 4 = 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.range
      ((φ (QuotientGroup.mk d) : W →ₗ[ZMod 2] W) - LinearMap.id)) :=
    Nat.mul_left_cancel hZXpos hmul
  have h2 : (2 : ℕ) ^ (2 : ℕ) = 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.range
      ((φ (QuotientGroup.mk d) : W →ₗ[ZMod 2] W) - LinearMap.id)) := by
    rw [← hpow]
    norm_num
  exact (Nat.pow_right_injective (le_refl 2) h2).symm

private theorem uc45_range_conj_sub_one
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (e f g' : W ≃ₗ[ZMod 2] W) (hg : g' = e * f * e⁻¹) :
    LinearMap.range ((g' : W →ₗ[ZMod 2] W) - LinearMap.id) =
      (LinearMap.range ((f : W →ₗ[ZMod 2] W) - LinearMap.id)).map e.toLinearMap := by
  apply le_antisymm
  · rintro w ⟨y, hy⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply] at hy
    refine Submodule.mem_map.mpr ⟨(f : W →ₗ[ZMod 2] W) (e.symm y) - e.symm y,
      ⟨e.symm y, rfl⟩, ?_⟩
    rw [map_sub]
    rw [show (e : W →ₗ[ZMod 2] W) (e.symm y) = y from LinearEquiv.apply_symm_apply e y]
    have h1 : (e : W →ₗ[ZMod 2] W) ((f : W →ₗ[ZMod 2] W) (e.symm y)) =
        (g' : W →ₗ[ZMod 2] W) y := by
      rw [hg]; simp
    rw [h1, hy]
  · rintro w ⟨z, ⟨y, rfl⟩, rfl⟩
    refine ⟨(e : W ≃ₗ[ZMod 2] W) y, ?_⟩
    change (g' : W →ₗ[ZMod 2] W) ((e : W ≃ₗ[ZMod 2] W) y) - (e : W ≃ₗ[ZMod 2] W) y =
      (e : W →ₗ[ZMod 2] W) ((f : W →ₗ[ZMod 2] W) y - y)
    rw [map_sub]
    have h1 : (e : W →ₗ[ZMod 2] W) ((f : W →ₗ[ZMod 2] W) y) =
        (g' : W →ₗ[ZMod 2] W) ((e : W ≃ₗ[ZMod 2] W) y) := by
      rw [hg]; simp
    rw [h1]
    rfl

private theorem uc45_commSpace_finrank (c : Ctx45 p G D)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (φ : (G ⧸ Wker G) →* (W ≃ₗ[ZMod 2] W))
    (hcard : ∀ g : G, Nat.card ↥(⁅Xof G, Subgroup.zpowers g⁆ ⊔ ZXof G) =
      Nat.card ↥(ZXof G) * 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.range
        ((φ (QuotientGroup.mk g) : W →ₗ[ZMod 2] W) - LinearMap.id)))
    (ι : (G ⧸ Wker G) ≃* ↥(alternatingGroup (Fin 5))) :
    ∀ g : ↥(alternatingGroup (Fin 5)), orderOf g = 3 →
      Module.finrank (ZMod 2) ↥(LinearMap.range
        (((φ.comp ι.symm.toMonoidHom) g : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2 := by
  let ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W) := φ.comp ι.symm.toMonoidHom
  change ∀ g : ↥(alternatingGroup (Fin 5)), orderOf g = 3 →
    Module.finrank (ZMod 2) ↥(LinearMap.range ((ρ g : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨d, hd⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top D).mp
    (isCyclic_of_prime_card c.card_three)
  have hιd : orderOf (ι (QuotientGroup.mk d : G ⧸ Wker G)) = 3 :=
    (MulEquiv.orderOf_eq ι _).trans (uc45_orderOf_mk_of_zpowers c.toPre45 hd)
  have hdimD := uc45_commSpace_finrank_generator c φ hcard hd
  intro g hg
  obtain ⟨u, hu⟩ := a5_order_three_conj (ι (QuotientGroup.mk d)) g hιd hg
  have hρι : ρ (ι (QuotientGroup.mk d)) = φ (QuotientGroup.mk d) := by simp [ρ]
  have hρg : ρ g = ρ u * φ (QuotientGroup.mk d) * (ρ u)⁻¹ := by
    rw [← hu, map_mul, map_mul, map_inv, hρι]
  rw [uc45_range_conj_sub_one (ρ u) (φ (QuotientGroup.mk d)) (ρ g) hρg,
    LinearEquiv.finrank_map_eq]
  exact hdimD

theorem r24_module (hSymp : SympData) (c : Ctx45 p G D)
    (hker : Wker G = CFSG.pPrimeCore 3 G) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (φ : (G ⧸ Wker G) →* (W ≃ₗ[ZMod 2] W)) (π : ↥(Xof G) →* Multiplicative W),
      Nat.card W = 16 ∧ Function.Injective φ ∧ Function.Surjective π ∧
      π.ker = Subgroup.center ↥(Xof G) ∧
      (∀ (g : G) (x : ↥(Xof G)), π (MulAut.conjNormal g x) =
        Multiplicative.ofAdd (φ (QuotientGroup.mk g) (Multiplicative.toAdd (π x)))) ∧
      (∀ w : W, (∀ γ, φ γ w = w) → w = 0) ∧
      (∀ γ : G ⧸ Wker G, orderOf γ = 3 → Nat.card {w : W // φ γ w = w} = 4) := by
  obtain ⟨W, hWadd, hWmod, hWfin, B, φ, π, hB, hAlt, hφinj, hiso, hπsurj, hπker, hequiv,
    hBform, hpre, hcard⟩ :=
    hSymp G (Xof G) (Wker G) (xof_isPGroup (G := G)) c.class_two.1 c.class_two.2
      (uc45_center_Xof_isCyclic c.toPre45) (fun g => mem_wker (G := G) (g := g))
  letI := hWadd
  letI := hWmod
  letI := hWfin
  have h0φ := uc45_fixed_vector_eq_zero φ π hπsurj hπker hequiv c.toPre45
  let ι : (G ⧸ Wker G) ≃* ↥(alternatingGroup (Fin 5)) := uc45_alt5_equiv c hker
  let ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W) := φ.comp ι.symm.toMonoidHom
  have hρ : Function.Injective ρ := fun a b hab => ι.symm.injective (hφinj hab)
  have hisoρ : ∀ g x y, B (ρ g x) (ρ g y) = B x y := fun g => hiso (ι.symm g)
  have h0ρ : ∀ w : W, (∀ g, ρ g w = w) → w = 0 := by
    intro w hw
    exact h0φ w fun γ => by
      have h := hw (ι γ)
      rwa [show ρ (ι γ) = φ γ from by simp [ρ]] at h
  have hdim := uc45_commSpace_finrank c φ hcard ι
  obtain ⟨hcardW, hfixed⟩ := a5_module_card_sixteen W B hB hAlt ρ hρ hisoρ h0ρ hdim
  refine ⟨W, hWadd, hWmod, hWfin, φ, π, hcardW, hφinj, hπsurj, hπker, hequiv, h0φ, ?_⟩
  intro γ hγ
  have hιγ : orderOf (ι γ) = 3 := (MulEquiv.orderOf_eq ι γ).trans hγ
  have h := hfixed (ι γ) hιγ
  rwa [show ρ (ι γ) = φ γ from by simp [ρ]] at h

theorem r2_card_X (hSymp : SympData) (c : Ctx45 p G D)
    (hker : Wker G = CFSG.pPrimeCore 3 G) :
    Nat.card ↥(Xof G) = 16 * Nat.card ↥(Subgroup.center ↥(Xof G)) := by
  obtain ⟨W, hWadd, hWmod, hWfin, φ, π, hcardW, -, hπsurj, hπker, -, -, -⟩ :=
    r24_module hSymp c hker
  letI := hWadd
  letI := hWmod
  letI := hWfin
  have h1 : Nat.card ↥(Xof G) =
      Nat.card (↥(Xof G) ⧸ π.ker) * Nat.card ↥(π.ker) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  have h2 : Nat.card (↥(Xof G) ⧸ π.ker) = Nat.card W := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπsurj).toEquiv]
    exact (Nat.card_congr Multiplicative.ofAdd).symm
  rw [h2, hcardW] at h1
  rw [hπker] at h1
  exact h1

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
