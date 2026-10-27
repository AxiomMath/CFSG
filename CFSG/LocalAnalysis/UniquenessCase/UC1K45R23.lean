module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Normal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {G : Type} [Group G] [Finite G] {D : Subgroup G}

private theorem orderOf_eq_two_of_sq_eq_one_of_ne_one {A : Type*} [Group A] {u : A}
    (hu : u ^ 2 = 1) (hu1 : u ≠ 1) : orderOf u = 2 := by
  have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hu
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hu1
  · exact h

private theorem mem_zpowers_iff_of_orderOf_eq_two {A : Type*} [Group A] {g x : A}
    (hg : orderOf g = 2) : x ∈ Subgroup.zpowers g ↔ x = 1 ∨ x = g := by
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf g k, hg, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem eq_of_sq_eq_one_of_ne_one {A : Type*} [Group A] [Finite A] [IsCyclic A] {u v : A}
    (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) : u = v := by
  have hu2 := orderOf_eq_two_of_sq_eq_one_of_ne_one hu hu1
  have hv2 := orderOf_eq_two_of_sq_eq_one_of_ne_one hv hv1
  have hzu : Subgroup.zpowers u = Subgroup.zpowers v := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hu2, hv2]
  have hmem : u ∈ Subgroup.zpowers v := hzu ▸ Subgroup.mem_zpowers u
  rcases (mem_zpowers_iff_of_orderOf_eq_two hv2).mp hmem with h | h
  · exact absurd h hu1
  · exact h

theorem eq_of_sq_eq_one_of_iff_eq_one {A : Type*} [Group A] [Finite A] [IsCyclic A] {u v : A}
    (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (h : u = 1 ↔ v = 1) : u = v := by
  by_cases h1 : u = 1
  · rw [h1, h.mp h1]
  · exact eq_of_sq_eq_one_of_ne_one hu hv h1 (fun hv1 => h1 (h.mpr hv1))

@[expose] noncomputable def epsTwo {A : Type*} [Group A] (z : A) : ZMod 2 := by
  classical
  exact if z = 1 then 0 else 1

theorem epsTwo_one {A : Type*} [Group A] : epsTwo (1 : A) = 0 := by
  simp [epsTwo]

theorem epsTwo_eq_zero_iff {A : Type*} [Group A] [Finite A] [IsCyclic A] {z : A}
    (hz : z ^ 2 = 1) : epsTwo z = 0 ↔ z = 1 := by
  by_cases h : z = 1
  · simp [epsTwo, h]
  · simp [epsTwo, h]

theorem epsTwo_mul {A : Type*} [Group A] [Finite A] [IsCyclic A] {u v : A}
    (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) : epsTwo (u * v) = epsTwo u + epsTwo v := by
  by_cases hu1 : u = 1
  · subst hu1; rw [one_mul]; simp [epsTwo]
  by_cases hv1 : v = 1
  · subst hv1; rw [mul_one]; simp [epsTwo]
  have huv : u = v := eq_of_sq_eq_one_of_ne_one hu hv hu1 hv1
  subst huv
  have huv1 : u * u = 1 := by rw [← pow_two, hu]
  have hε : epsTwo u = 1 := by simp [epsTwo, hu1]
  rw [huv1, epsTwo_one, hε]
  decide

theorem xof_le_pPrimeCore (c : Front45 p G D) : Xof G ≤ CFSG.pPrimeCore 3 G := by
  rw [← c.K_eq]
  change ⁅CFSG.pPrimeCore 3 G, (⊤ : Subgroup G)⁆ ≤ CFSG.pPrimeCore 3 G
  exact Subgroup.commutator_le_left (H₁ := CFSG.pPrimeCore 3 G) (H₂ := ⊤)

theorem center_le_pPrimeCore (c : Front45 p G D) : Subgroup.center G ≤ CFSG.pPrimeCore 3 G :=
  proper_normal_le_pPrimeCore c.card_three c.gen c.rank (Subgroup.center G)
    (center_ne_top c.card_three c.perfect)

theorem sup_le_pPrimeCore (c : Front45 p G D) :
    Xof G ⊔ Subgroup.center G ≤ CFSG.pPrimeCore 3 G :=
  sup_le (xof_le_pPrimeCore c) (center_le_pPrimeCore c)

theorem zxof_cyclic (c : Front45 p G D) : IsCyclic ↥(ZXof G) := by
  haveI : IsCyclic ↥(Subgroup.center G) := c.center_cyclic
  exact Subgroup.isCyclic_of_le c.ZX_le

theorem center_xof_cyclic (c : Front45 p G D) : IsCyclic ↥(Subgroup.center ↥(Xof G)) := by
  haveI hZX : IsCyclic ↥(ZXof G) := zxof_cyclic c
  let e : ↥(Subgroup.center ↥(Xof G)) ≃* ↥(ZXof G) :=
    Subgroup.equivMapOfInjective (Subgroup.center ↥(Xof G)) (Xof G).subtype
      (Xof G).subtype_injective
  exact (MulEquiv.isCyclic e).mpr hZX

theorem commutator_sq_eq_one (c : Front45 p G D) (a : G)
    (ha : ∀ y ∈ Xof G, ⁅a, y⁆ ∈ ZXof G) (x : ↥(Xof G)) : ⁅a, x.1⁆ ^ 2 = 1 := by
  have hz : ⁅a, x.1⁆ ∈ Subgroup.center G := c.ZX_le (ha x.1 x.2)
  have hcomm : Commute x.1 ⁅a, x.1⁆ := (Subgroup.mem_center_iff.mp hz) x.1
  rw [Commute.commutatorElement_pow_right hcomm 2]
  have hx2 : x.1 ^ 2 ∈ Subgroup.center G :=
    c.ZX_le (Subgroup.mem_map.mpr ⟨x ^ 2, c.class_two.2 x, by simp⟩)
  exact Commute.commutator_eq ((Subgroup.mem_center_iff.mp hx2) a)

@[expose] noncomputable def wkerCommutatorHom (c : Front45 p G D) (g : G)
    (hgW : ∀ x ∈ Xof G, ⁅g, x⁆ ∈ ZXof G) : ↥(Xof G) →* ↥(ZXof G) where
  toFun x := ⟨⁅g, x.1⁆, hgW x.1 x.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' := by
    intro x y
    apply Subtype.ext
    change ⁅g, x.1 * y.1⁆ = ⁅g, x.1⁆ * ⁅g, y.1⁆
    have hz : x.1 * ⁅g, y.1⁆ * x.1⁻¹ = ⁅g, y.1⁆ := by
      rw [Subgroup.mem_center_iff.mp (c.ZX_le (hgW y.1 y.2)) x.1]
      group
    calc ⁅g, x.1 * y.1⁆ = ⁅g, x.1⁆ * x.1 * ⁅g, y.1⁆ * x.1⁻¹ :=
          commutatorElement_mul_right_eq_mul_conj g x.1 y.1
      _ = ⁅g, x.1⁆ * ⁅g, y.1⁆ := by
          rw [show ⁅g, x.1⁆ * x.1 * ⁅g, y.1⁆ * x.1⁻¹ =
            ⁅g, x.1⁆ * (x.1 * ⁅g, y.1⁆ * x.1⁻¹) by group, hz]

@[simp] theorem wkerCommutatorHom_apply (c : Front45 p G D) (g : G)
    (hgW : ∀ x ∈ Xof G, ⁅g, x⁆ ∈ ZXof G) (x : ↥(Xof G)) :
    wkerCommutatorHom c g hgW x = ⟨⁅g, x.1⁆, hgW x.1 x.2⟩ := rfl

theorem wkerCommutatorHom_sq (c : Front45 p G D) (g : G)
    (hgW : ∀ x ∈ Xof G, ⁅g, x⁆ ∈ ZXof G) (x : ↥(Xof G)) :
    wkerCommutatorHom c g hgW x ^ 2 = 1 := by
  apply Subtype.ext
  change ⁅g, x.1⁆ ^ 2 = 1
  exact commutator_sq_eq_one c g hgW x

theorem wkerCommutatorHom_eq_one_of_mem_center (c : Front45 p G D) (g : G)
    (hgW : ∀ x ∈ Xof G, ⁅g, x⁆ ∈ ZXof G) {x : ↥(Xof G)}
    (hx : x ∈ Subgroup.center ↥(Xof G)) : wkerCommutatorHom c g hgW x = 1 := by
  apply Subtype.ext
  change ⁅g, x.1⁆ = 1
  have hzx : x.1 ∈ ZXof G := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  exact Commute.commutator_eq ((Subgroup.mem_center_iff.mp (c.ZX_le hzx)) g)

@[expose] noncomputable def wkerZModHom (c : Front45 p G D) (g : G)
    (hgW : ∀ x ∈ Xof G, ⁅g, x⁆ ∈ ZXof G) [IsCyclic ↥(ZXof G)] :
    ↥(Xof G) →* Multiplicative (ZMod 2) := by
  classical
  refine
    { toFun := fun x => Multiplicative.ofAdd (epsTwo (wkerCommutatorHom c g hgW x))
      map_one' := ?_
      map_mul' := ?_ }
  · rw [map_one, epsTwo_one]
    rfl
  · intro x y
    rw [map_mul]
    rw [epsTwo_mul (wkerCommutatorHom_sq c g hgW x) (wkerCommutatorHom_sq c g hgW y)]
    rfl

theorem wkerZModHom_eq_one_of_mem_center (c : Front45 p G D) (g : G)
    (hgW : ∀ x ∈ Xof G, ⁅g, x⁆ ∈ ZXof G) [IsCyclic ↥(ZXof G)] {x : ↥(Xof G)}
    (hx : x ∈ Subgroup.center ↥(Xof G)) : wkerZModHom c g hgW x = 1 := by
  have hφ : wkerCommutatorHom c g hgW x = 1 := wkerCommutatorHom_eq_one_of_mem_center c g hgW hx
  change Multiplicative.ofAdd (epsTwo (wkerCommutatorHom c g hgW x)) = 1
  rw [hφ, epsTwo_one]
  rfl

theorem exists_addHom_factor {X W : Type*} [Group X] [AddCommGroup W]
    (π : X →* Multiplicative W) (hπ : Function.Surjective π)
    (f : X →* Multiplicative (ZMod 2)) (hf : π.ker ≤ f.ker) :
    ∃ ℓ : W →+ ZMod 2, ∀ x : X,
      ℓ (Multiplicative.toAdd (π x)) = Multiplicative.toAdd (f x) := by
  classical
  let e : X ⧸ π.ker ≃* Multiplicative W := QuotientGroup.liftEquiv π.ker hπ rfl
  let fbar : X ⧸ π.ker →* Multiplicative (ZMod 2) := QuotientGroup.lift π.ker f hf
  let ℓm : Multiplicative W →* Multiplicative (ZMod 2) := fbar.comp e.symm.toMonoidHom
  let ℓ : W →+ ZMod 2 := (AddMonoidHom.toMultiplicative (α := W) (β := ZMod 2)).symm ℓm
  refine ⟨ℓ, fun x => ?_⟩
  have h1 : ℓm (π x) = f x := by
    have hmk : e (QuotientGroup.mk x) = π x := QuotientGroup.liftEquiv_mk π.ker hπ rfl x
    have hsymm : e.symm (π x) = QuotientGroup.mk x := by rw [← hmk, MulEquiv.symm_apply_apply]
    show fbar (e.symm (π x)) = f x
    rw [hsymm]
    exact QuotientGroup.lift_mk π.ker hf x
  have h2 : (AddMonoidHom.toMultiplicative ℓ) = ℓm := by simp [ℓ]
  have h3 : Multiplicative.ofAdd (ℓ (Multiplicative.toAdd (π x))) = f x := by
    have := congrArg (fun g : Multiplicative W →* Multiplicative (ZMod 2) => g (π x)) h2
    rw [h1] at this
    simpa only [AddMonoidHom.coe_toMultiplicative, Function.comp_apply] using this
  have := congrArg Multiplicative.toAdd h3
  simpa using this

private theorem exists_riesz_local {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (β : LinearMap.BilinForm K V) (hβ : β.Nondegenerate)
    (f : Module.Dual K V) : ∃ w : V, ∀ v, β w v = f v :=
  ⟨(LinearMap.BilinForm.toDual β hβ).symm f,
    fun v => LinearMap.BilinForm.apply_toDual_symm_apply f v⟩

theorem commutator_subtype_eq_one_iff (x₀ x : ↥(Xof G)) :
    ⁅x₀, x⁆ = 1 ↔ ⁅x₀.1, x.1⁆ = 1 := by
  have h : ((⁅x₀, x⁆ : ↥(Xof G)) : G) = ⁅x₀.1, x.1⁆ :=
    map_commutatorElement (Subgroup.subtype (Xof G)) x₀ x
  rw [← h]
  exact Subtype.ext_iff

theorem commutator_eq_of_form_eq_eps (c : Front45 p G D) (g : G)
    (hgW : ∀ x ∈ Xof G, ⁅g, x⁆ ∈ ZXof G)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (B : LinearMap.BilinForm (ZMod 2) W) (π : ↥(Xof G) →* Multiplicative W)
    (hform : ∀ x y : ↥(Xof G),
      B (Multiplicative.toAdd (π x)) (Multiplicative.toAdd (π y)) = 0 ↔ ⁅x, y⁆ = 1)
    (x₀ : ↥(Xof G))
    (hBx : ∀ x : ↥(Xof G), B (Multiplicative.toAdd (π x₀))
      (Multiplicative.toAdd (π x)) = epsTwo (wkerCommutatorHom c g hgW x)) :
    ∀ x : ↥(Xof G), ⁅x₀.1, x.1⁆ = ⁅g, x.1⁆ := by
  haveI hZX : IsCyclic ↥(ZXof G) := zxof_cyclic c
  intro x
  have hφsq : (wkerCommutatorHom c g hgW x) ^ 2 = 1 := wkerCommutatorHom_sq c g hgW x
  have ha₀ : ∀ y ∈ Xof G, ⁅x₀.1, y⁆ ∈ ZXof G := by
    intro y hy
    let y' : ↥(Xof G) := ⟨y, hy⟩
    refine Subgroup.mem_map.mpr ⟨(⁅x₀, y'⁆ : ↥(Xof G)), ?_, ?_⟩
    · exact c.class_two.1 (Subgroup.commutator_mem_commutator (Subgroup.mem_top x₀)
        (Subgroup.mem_top y'))
    · exact map_commutatorElement (Subgroup.subtype (Xof G)) x₀ y'
  have hmem : ⁅x₀.1, x.1⁆ ∈ ZXof G := ha₀ x.1 x.2
  let u : ↥(ZXof G) := ⟨⁅x₀.1, x.1⁆, hmem⟩
  have husq : u ^ 2 = 1 := by
    have := commutator_sq_eq_one c x₀.1 ha₀ x
    simpa [u] using this
  have hiff : u = 1 ↔ wkerCommutatorHom c g hgW x = 1 := by
    have h1 : u = 1 ↔ ⁅x₀, x⁆ = 1 := by
      rw [Subtype.ext_iff]
      change ⁅x₀.1, x.1⁆ = 1 ↔ ⁅x₀, x⁆ = 1
      rw [commutator_subtype_eq_one_iff]
    have h2 : ⁅x₀, x⁆ = 1 ↔ B (Multiplicative.toAdd (π x₀))
        (Multiplicative.toAdd (π x)) = 0 := (hform x₀ x).symm
    have h3 : B (Multiplicative.toAdd (π x₀)) (Multiplicative.toAdd (π x)) = 0 ↔
        wkerCommutatorHom c g hgW x = 1 := by
      rw [hBx x]
      exact epsTwo_eq_zero_iff hφsq
    exact h1.trans (h2.trans h3)
  have hux : u = wkerCommutatorHom c g hgW x :=
    eq_of_sq_eq_one_of_iff_eq_one husq hφsq hiff
  have := congrArg Subtype.val hux
  simpa [u] using this

theorem exists_x0_commutator_eq (hForm : SympForm) (c : Front45 p G D) (g : G)
    (hgW : ∀ x ∈ Xof G, ⁅g, x⁆ ∈ ZXof G) :
    ∃ x₀ : ↥(Xof G), ∀ x : ↥(Xof G), ⁅x₀.1, x.1⁆ = ⁅g, x.1⁆ := by
  haveI hcyc : IsCyclic ↥(Subgroup.center ↥(Xof G)) := center_xof_cyclic c
  obtain ⟨W, _, _, hWfin, B, π, hB, _hAlt, hπ, hker, hform⟩ :=
    hForm ↥(Xof G) (xof_isPGroup (G := G)) c.class_two.1 c.class_two.2 hcyc
  haveI : Finite W := hWfin
  haveI hZXcyc : IsCyclic ↥(ZXof G) := zxof_cyclic c
  haveI : FiniteDimensional (ZMod 2) W := (Module.finite_iff_finite (R := ZMod 2)).mpr hWfin
  let f : ↥(Xof G) →* Multiplicative (ZMod 2) := wkerZModHom c g hgW
  have hfker : π.ker ≤ f.ker := by
    intro x hx
    have hx' : x ∈ Subgroup.center ↥(Xof G) := by rwa [hker] at hx
    exact wkerZModHom_eq_one_of_mem_center c g hgW hx'
  obtain ⟨ℓ, hℓ⟩ := exists_addHom_factor π hπ f hfker
  let ℓlin : W →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun w => ℓ w
      map_add' := fun a b => map_add ℓ a b
      map_smul' := fun c w => by
        fin_cases c
        · show ℓ (0 • w) = (0 : ZMod 2) * ℓ w
          rw [zero_smul, map_zero, zero_mul]
        · show ℓ (1 • w) = (1 : ZMod 2) * ℓ w
          rw [one_smul, one_mul] }
  obtain ⟨w₀, hw₀⟩ := exists_riesz_local (K := ZMod 2) (V := W) B hB ℓlin
  obtain ⟨x₀, hx₀⟩ := hπ (Multiplicative.ofAdd w₀)
  refine ⟨x₀, commutator_eq_of_form_eq_eps c g hgW B π hform x₀ ?_⟩
  intro x
  rw [hx₀]
  change B w₀ (Multiplicative.toAdd (π x)) = epsTwo (wkerCommutatorHom c g hgW x)
  rw [hw₀]
  change ℓ (Multiplicative.toAdd (π x)) = epsTwo (wkerCommutatorHom c g hgW x)
  rw [hℓ x]
  rfl

theorem inv_mul_mem_centralizer (c : Front45 p G D) {x₀ g : G}
    (hx₀ : ∀ x : ↥(Xof G), ⁅x₀, x.1⁆ = ⁅g, x.1⁆)
    (hgW : ∀ x ∈ Xof G, ⁅g, x⁆ ∈ ZXof G) :
    x₀⁻¹ * g ∈ Subgroup.centralizer (Xof G : Set G) := by
  rw [Subgroup.mem_centralizer_iff_commutator_eq_one']
  intro x hx
  have hx0x : ⁅x₀, x⁆ = ⁅g, x⁆ := hx₀ ⟨x, hx⟩
  have hgx : ⁅g, x⁆ ∈ Subgroup.center G := c.ZX_le (hgW x hx)
  have hh : x₀⁻¹ * ⁅g, x⁆ * x₀ = ⁅g, x⁆ := by
    rw [Subgroup.mem_center_iff.mp hgx x₀⁻¹]
    group
  have hc : ⁅x₀, x⁆ ∈ Subgroup.center G := by rw [hx0x]; exact hgx
  calc ⁅x₀⁻¹ * g, x⁆ = x₀⁻¹ * ⁅g, x⁆ * (x₀⁻¹)⁻¹ * ⁅x₀⁻¹, x⁆ :=
        commutatorElement_mul_left_eq_conj_mul x₀⁻¹ g x
    _ = ⁅g, x⁆ * ⁅x₀⁻¹, x⁆ := by rw [inv_inv, hh]
    _ = ⁅g, x⁆ * ⁅x₀, x⁆⁻¹ := by
        rw [commutatorElement_inv_left, commutatorElement_inv]
        have hci : ⁅x, x₀⁆ ∈ Subgroup.center G := by
          rw [← commutatorElement_inv]
          exact (Subgroup.center G).inv_mem hc
        rw [show x₀⁻¹ * ⁅x, x₀⁆ * x₀ = ⁅x, x₀⁆ by
          rw [Subgroup.mem_center_iff.mp hci x₀⁻¹]; group]
    _ = 1 := by rw [hx0x, mul_inv_cancel]

theorem pPrimeCore_le_sup (hForm : SympForm) (c : Front45 p G D)
    (hHW : CFSG.pPrimeCore 3 G ≤ Wker G)
    (hcent : Subgroup.centralizer (Xof G : Set G) = Subgroup.center G) :
    CFSG.pPrimeCore 3 G ≤ Xof G ⊔ Subgroup.center G := by
  intro g hg
  have hgW : ∀ x ∈ Xof G, ⁅g, x⁆ ∈ ZXof G := mem_wker.mp (hHW hg)
  obtain ⟨x₀, hx₀⟩ := exists_x0_commutator_eq hForm c g hgW
  have hmem : x₀.1⁻¹ * g ∈ Subgroup.centralizer (Xof G : Set G) :=
    inv_mul_mem_centralizer c hx₀ hgW
  rw [hcent] at hmem
  have hg_eq : g = x₀.1 * (x₀.1⁻¹ * g) := by group
  rw [hg_eq]
  exact Subgroup.mul_mem_sup x₀.2 hmem

theorem r2_H_eq_XZ (hForm : SympForm) (c : Front45 p G D)
    (hHW : CFSG.pPrimeCore 3 G ≤ Wker G)
    (hcent : Subgroup.centralizer (Xof G : Set G) = Subgroup.center G) :
    CFSG.pPrimeCore 3 G = Xof G ⊔ Subgroup.center G :=
  le_antisymm (pPrimeCore_le_sup hForm c hHW hcent) (sup_le_pPrimeCore c)

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
