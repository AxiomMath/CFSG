module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Normal
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairHyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {G : Type} [Group G] [Finite G] {D : Subgroup G}

private theorem matrix_two_cube_of_sq_add_self_add_one
    (A C : Matrix (Fin 2) (Fin 2) (ZMod 2)) (hA : A ^ 2 + A + 1 = 0)
    (hAC : C * A = A * C) (hC : C ≠ 0) : C ^ 3 = 1 := by
  revert A C
  decide

private theorem endo_two_cube_of_sq_add_self_add_one {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (h2 : Module.finrank (ZMod 2) V = 2) {T C : V →ₗ[ZMod 2] V}
    (hT : T ^ 2 + T + 1 = 0) (hTC : C * T = T * C) (hC : C ≠ 0) : C ^ 3 = 1 := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) V h2
  let ψ := LinearMap.toMatrixAlgEquiv b
  let A := ψ T
  let C' := ψ C
  have hA : A ^ 2 + A + 1 = 0 := by
    have hψ : A ^ 2 + A + 1 = ψ (T ^ 2 + T + 1) := by
      show (ψ T) ^ 2 + ψ T + 1 = ψ (T ^ 2 + T + 1)
      rw [map_add, map_add, map_pow, map_one]
    rw [hψ, hT, map_zero]
  have hAC : C' * A = A * C' := by
    show ψ C * ψ T = ψ T * ψ C
    rw [← map_mul, ← map_mul, hTC]
  have hC' : C' ≠ 0 := by
    intro h
    have h' : ψ C = 0 := h
    exact hC (ψ.injective (by rw [h', map_zero]))
  have hres := matrix_two_cube_of_sq_add_self_add_one A C' hA hAC hC'
  apply ψ.injective
  rw [map_pow, hres, map_one]

private theorem restrict_pow_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {p : Submodule (ZMod 2) V} {f : V →ₗ[ZMod 2] V} (hf : ∀ x ∈ p, f x ∈ p) (n : ℕ) :
    ∀ x : p, ((f.restrict hf ^ n) x : V) = (f ^ n) x.1 := by
  induction n with
  | zero => intro x; simp
  | succ n ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, LinearMap.coe_restrict_apply, pow_succ,
        Module.End.mul_apply]

private theorem restrict_ne_zero {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {p : Submodule (ZMod 2) V} {f : V →ₗ[ZMod 2] V} (hf : ∀ x ∈ p, f x ∈ p)
    (hinj : Function.Injective f) (hp : p ≠ ⊥) : f.restrict hf ≠ 0 := by
  intro h
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  have : ((f.restrict hf) ⟨x, hx⟩ : V) = 0 := by rw [h]; rfl
  rw [LinearMap.coe_restrict_apply] at this
  exact hx0 (hinj (by simpa using this))

private theorem xof_le_wker (c : Pre45 p G D) : Xof G ≤ Wker G := by
  intro x hx
  rw [mem_wker]
  intro y hy
  have hmem : ⁅(⟨x, hx⟩ : ↥(Xof G)), (⟨y, hy⟩ : ↥(Xof G))⁆ ∈ Subgroup.center ↥(Xof G) :=
    c.class_two.1 (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  exact Subgroup.mem_map.mpr ⟨_, hmem,
    map_commutatorElement (Subgroup.subtype (Xof G)) _ _⟩

private theorem inf_centralizer_X_eq_zxof :
    Xof G ⊓ Subgroup.centralizer (Xof G : Set G) = ZXof G := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxX⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y.1 y.2)
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy (⟨z, hz⟩ : ↥(Xof G)))

private theorem centralizer_X_ne_top (c : Front45 p G D) :
    Subgroup.centralizer (Xof G : Set G) ≠ ⊤ := by
  intro htop
  have hXZ : Xof G ≤ Subgroup.center G := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (Xof G : Set G) := by
      rw [htop]; exact Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg x hx).symm
  have hcenter_comm : ⁅Subgroup.center G, D⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro d _
    exact Subgroup.mem_center_iff.mp hx d
  have hTle : Tof G D ≤ Subgroup.center G := by
    calc Tof G D = ⁅Xof G, D⁆ := rfl
      _ ≤ ⁅Subgroup.center G, D⁆ := Subgroup.commutator_mono hXZ le_rfl
      _ = ⊥ := hcenter_comm
      _ ≤ Subgroup.center G := bot_le
  have hcommT : IsMulCommutative ↥(Tof G D) :=
    IsMulCommutative.of_comm fun a b => Subtype.ext
      (Subgroup.mem_center_iff.mp (hTle a.2) (b : G)).symm
  obtain ⟨eQ⟩ := c.Q8
  refine quaternionGroup_two_not_isMulCommutative ?_
  refine IsMulCommutative.of_comm fun u v => ?_
  have h := hcommT.is_comm.comm (eQ.symm u) (eQ.symm v)
  have h2 := congrArg (fun t : ↥(Tof G D) => eQ t) h
  simpa using h2

private theorem commutator_centralizer_le_zxof (c : Front45 p G D)
    (hCne : Subgroup.centralizer (Xof G : Set G) ≠ ⊤) :
    ⁅Subgroup.centralizer (Xof G : Set G), (⊤ : Subgroup G)⁆ ≤ ZXof G := by
  have hCleH : Subgroup.centralizer (Xof G : Set G) ≤ CFSG.pPrimeCore 3 G :=
    proper_normal_le_pPrimeCore c.card_three c.gen c.rank _ hCne
  have h1 : ⁅Subgroup.centralizer (Xof G : Set G), (⊤ : Subgroup G)⁆ ≤ Xof G := by
    calc ⁅Subgroup.centralizer (Xof G : Set G), (⊤ : Subgroup G)⁆
        ≤ ⁅CFSG.pPrimeCore 3 G, (⊤ : Subgroup G)⁆ :=
          Subgroup.commutator_mono hCleH le_rfl
      _ = Kof G := rfl
      _ = Xof G := c.K_eq
  have h2 : ⁅Subgroup.centralizer (Xof G : Set G), (⊤ : Subgroup G)⁆
      ≤ Subgroup.centralizer (Xof G : Set G) :=
    Subgroup.commutator_le_left (H₁ := _) (H₂ := ⊤)
  rw [← inf_centralizer_X_eq_zxof]
  exact le_inf h1 h2

theorem r2_centralizer_X (c : Front45 p G D) :
    Subgroup.centralizer (Xof G : Set G) = Subgroup.center G := by
  let C : Subgroup G := Subgroup.centralizer (Xof G : Set G)
  have hCnorm : C.Normal := Subgroup.normal_centralizer (H := Xof G)
  haveI : C.Normal := hCnorm
  have hZXle : Subgroup.center G ≤ C := Subgroup.center_le_centralizer _
  have hCne : C ≠ ⊤ := centralizer_X_ne_top c
  have hCleH : C ≤ CFSG.pPrimeCore 3 G :=
    proper_normal_le_pPrimeCore c.card_three c.gen c.rank C hCne
  have hcommC : ⁅C, (⊤ : Subgroup G)⁆ ≤ ZXof G := commutator_centralizer_le_zxof c hCne
  have hcommD : ⁅C, D⁆ ≤ Subgroup.center G :=
    (Subgroup.commutator_mono le_rfl le_top).trans (hcommC.trans c.ZX_le)
  have hbot : ⁅⁅C, D⁆, D⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro d _
    exact Subgroup.mem_center_iff.mp (hcommD hx) d
  have hcop : Nat.Coprime (Nat.card D) (Nat.card C) := by
    rw [c.card_three]
    exact (CFSG.pPrimeCore_coprime_card (p := 3) (G := G)).coprime_dvd_right
      (Subgroup.card_dvd_of_le hCleH)
  have hidem :=
    CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime C D hcop
      (Subgroup.le_normalizer_of_normal)
  have hCDbot : ⁅C, D⁆ = ⊥ := by rw [← hidem]; exact hbot
  have hDCbot : ⁅D, C⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hCDbot
  have hDle : D ≤ Subgroup.centralizer (C : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hDCbot
  have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer (C : Set G) := by
    haveI : (Subgroup.centralizer (C : Set G)).Normal := Subgroup.normal_centralizer (H := C)
    rw [← c.gen]
    exact Subgroup.normalClosure_le_normal hDle
  have hCleZ : C ≤ Subgroup.center G := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.mp (htop (Subgroup.mem_top g)) x hx).symm
  exact le_antisymm hCleZ hZXle

private theorem range_sub_one_invariant {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (a : V ≃ₗ[ZMod 2] V) :
    ∀ x ∈ LinearMap.range ((a : V →ₗ[ZMod 2] V) - 1),
      (a : V →ₗ[ZMod 2] V) x ∈ LinearMap.range ((a : V →ₗ[ZMod 2] V) - 1) := by
  intro x hx
  obtain ⟨v, rfl⟩ := hx
  refine ⟨(a : V →ₗ[ZMod 2] V) v, ?_⟩
  simp only [LinearMap.sub_apply, map_sub, Module.End.one_apply, LinearMap.id_apply]

private theorem sq_add_self_add_one_mul_sub_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a : V →ₗ[ZMod 2] V} (ha3 : a ^ 3 = 1) : (a ^ 2 + a + 1) * (a - 1) = 0 := by
  have h : (a ^ 2 + a + 1) * (a - 1) = a ^ 3 - 1 := by noncomm_ring
  rw [h, ha3, sub_self]

private theorem sq_add_self_add_one_apply_of_mem_range_sub_one {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {a : V →ₗ[ZMod 2] V} (hcomp : (a ^ 2 + a + 1) * (a - 1) = 0) :
    ∀ x ∈ LinearMap.range (a - 1), (a ^ 2 + a + (1 : V →ₗ[ZMod 2] V)) x = 0 := by
  intro x hx
  obtain ⟨v, rfl⟩ := hx
  have h := congrFun (congrArg (fun f : Module.End (ZMod 2) V => (f : V → V)) hcomp) v
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply, LinearMap.id_apply] using h

private theorem restrict_range_sub_one_sq_add_self_add_one {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] (a : V ≃ₗ[ZMod 2] V) (ha3 : a ^ 3 = 1)
    (haP : ∀ x ∈ LinearMap.range ((a : V →ₗ[ZMod 2] V) - 1),
      (a : V →ₗ[ZMod 2] V) x ∈ LinearMap.range ((a : V →ₗ[ZMod 2] V) - 1)) :
    ((a : V →ₗ[ZMod 2] V).restrict haP) ^ 2 + (a : V →ₗ[ZMod 2] V).restrict haP + 1 = 0 := by
  have haL3 : (a : V →ₗ[ZMod 2] V) ^ 3 = 1 := by
    change (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := V)) a ^ 3 = 1
    rw [← map_pow, ha3]
    exact map_one _
  have hx_apply := sq_add_self_add_one_apply_of_mem_range_sub_one
    (sq_add_self_add_one_mul_sub_one haL3)
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hx := hx_apply x.1 x.2
  have h1 : ((((a : V →ₗ[ZMod 2] V).restrict haP) ^ 2) x : V) =
      ((a : V →ₗ[ZMod 2] V) ^ 2) x.1 := restrict_pow_apply haP 2 x
  have h2 : ((a : V →ₗ[ZMod 2] V).restrict haP x : V) =
      (a : V →ₗ[ZMod 2] V) x.1 := LinearMap.coe_restrict_apply haP x
  simp only [LinearMap.add_apply, Module.End.one_apply, Submodule.coe_add, Submodule.coe_zero,
    LinearMap.id_apply]
  rw [h1, h2]
  simpa only [LinearMap.add_apply, Module.End.one_apply, LinearMap.id_apply, LinearMap.zero_apply,
    Submodule.coe_zero] using hx

private theorem commute_preserves_range_sub_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a ch : V →ₗ[ZMod 2] V} (h : Commute ch a) :
    ∀ x ∈ LinearMap.range (a - 1), ch x ∈ LinearMap.range (a - 1) := by
  intro x hx
  obtain ⟨v, rfl⟩ := hx
  refine ⟨ch v, ?_⟩
  have hcommv := congrFun (congrArg (fun f : Module.End (ZMod 2) V => (f : V → V))
    (show ch * a = a * ch from h)) v
  simp only [Module.End.mul_apply] at hcommv
  simp only [LinearMap.sub_apply, map_sub, Module.End.one_apply, LinearMap.id_apply]
  rw [hcommv]

private theorem restrict_cube_eq_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {P : Submodule (ZMod 2) V} {a ch : V →ₗ[ZMod 2] V}
    (haP : ∀ x ∈ P, a x ∈ P) (hchP : ∀ x ∈ P, ch x ∈ P)
    (hcomm : Commute ch a) (hinj : Function.Injective ch)
    (ha : (a.restrict haP) ^ 2 + a.restrict haP + 1 = 0)
    (hrank : Module.finrank (ZMod 2) P = 2) :
    (ch.restrict hchP) ^ 3 = 1 := by
  have hTC : (ch.restrict hchP) * (a.restrict haP) = (a.restrict haP) * (ch.restrict hchP) :=
    LinearMap.restrict_commute hcomm hchP haP
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hrank
    exact (by norm_num : (0 : ℕ) ≠ 2) hrank
  have hne : ch.restrict hchP ≠ 0 := restrict_ne_zero hchP hinj hPne
  exact endo_two_cube_of_sq_add_self_add_one hrank ha hTC hne

private theorem restrict_cube_fixes {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {P : Submodule (ZMod 2) V} {ch : V →ₗ[ZMod 2] V} (hchP : ∀ x ∈ P, ch x ∈ P)
    (h3 : (ch.restrict hchP) ^ 3 = 1) : ∀ u ∈ P, ch (ch (ch u)) = u := by
  intro u hu
  have h1 : (((ch.restrict hchP) ^ 3) ⟨u, hu⟩ : V) = u := by rw [h3]; rfl
  rw [restrict_pow_apply hchP 3 ⟨u, hu⟩] at h1
  have h2 : (ch ^ 3) u = ch (ch (ch u)) := by rw [Module.End.pow_apply]; rfl
  rwa [h2] at h1

private theorem range_sub_one_restrict_cube {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (a : V ≃ₗ[ZMod 2] V) (ha3 : a ^ 3 = 1)
    (ch : V →ₗ[ZMod 2] V) (hcomm : Commute ch a) (hinj : Function.Injective ch)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range ((a : V →ₗ[ZMod 2] V) - 1)) = 2) :
    ∀ u ∈ LinearMap.range ((a : V →ₗ[ZMod 2] V) - 1), ch (ch (ch u)) = u := by
  have haP : ∀ x ∈ LinearMap.range ((a : V →ₗ[ZMod 2] V) - 1),
      (a : V →ₗ[ZMod 2] V) x ∈ LinearMap.range ((a : V →ₗ[ZMod 2] V) - 1) :=
    range_sub_one_invariant a
  have haPres := restrict_range_sub_one_sq_add_self_add_one a ha3 haP
  have hchP : ∀ x ∈ LinearMap.range ((a : V →ₗ[ZMod 2] V) - 1),
      ch x ∈ LinearMap.range ((a : V →ₗ[ZMod 2] V) - 1) :=
    commute_preserves_range_sub_one hcomm
  have h3 := restrict_cube_eq_one haP hchP hcomm hinj haPres hrank
  exact restrict_cube_fixes hchP h3

private theorem linearMap_cube_eq_one_of_fixes_span {H V : Type*} [Group H]
    [AddCommGroup V] [Module (ZMod 2) V]
    (chL : V →ₗ[ZMod 2] V) (P : Submodule (ZMod 2) V)
    (φ : H →* (V ≃ₗ[ZMod 2] V)) (W₀ : Submodule (ZMod 2) V)
    (hW₀ : W₀ = ⨆ γ : H, P.map (φ γ).toLinearMap) (hW₀top : W₀ = ⊤)
    (hchφ : ∀ γ u, chL (φ γ u) = φ γ (chL u))
    (hfixP : ∀ u ∈ P, chL (chL (chL u)) = u) :
    chL ^ 3 = 1 := by
  have hker : W₀ ≤ LinearMap.ker (chL ^ 3 - 1) := by
    rw [hW₀]
    refine iSup_le fun γ => ?_
    intro v hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply]
    change chL (chL (chL (φ γ u))) - φ γ u = 0
    rw [hchφ γ u, hchφ γ (chL u), hchφ γ (chL (chL u)), hfixP u hu, sub_self]
  have htop : LinearMap.ker (chL ^ 3 - 1) = ⊤ := by
    rw [← hW₀top]
    exact le_antisymm (le_top.trans (le_of_eq hW₀top.symm)) hker
  ext v
  have hv : (chL ^ 3) v = v := by
    have hmem : v ∈ LinearMap.ker (chL ^ 3 - 1) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hmem
    exact hmem
  simpa only [Module.End.one_apply] using hv

private theorem orderOf_toLinearMap_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (e : V ≃ₗ[ZMod 2] V) : orderOf (e : V →ₗ[ZMod 2] V) = orderOf e := by
  have hinj : Function.Injective
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := V)) :=
    fun e₁ e₂ h => LinearEquiv.ext fun x => congrFun
      (congrArg (fun f : V →ₗ[ZMod 2] V => (f : V → V)) h) x
  have h := orderOf_injective
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := V)) hinj e
  simpa using h

private def preimageSubmodule {X : Type*} [Group X] {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] (π : X →* Multiplicative W) (W₀ : Submodule (ZMod 2) W) :
    Subgroup X where
  carrier := {x | Multiplicative.toAdd (π x) ∈ W₀}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change Multiplicative.toAdd (π (x * y)) ∈ W₀
    have hxy : Multiplicative.toAdd (π (x * y)) =
        Multiplicative.toAdd (π x) + Multiplicative.toAdd (π y) := by
      rw [map_mul]
      rfl
    rw [hxy]
    exact W₀.add_mem hx hy
  inv_mem' := by
    intro x hx
    change Multiplicative.toAdd (π x⁻¹) ∈ W₀
    have hx' : Multiplicative.toAdd (π x⁻¹) = -Multiplicative.toAdd (π x) := by
      rw [map_inv]
      rfl
    rw [hx']
    exact W₀.neg_mem hx

private theorem preimageSubmodule_conj_mem {H : Subgroup G} [H.Normal] {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W]
    (φ : (G ⧸ Wker G) →* (W ≃ₗ[ZMod 2] W))
    (π : ↥H →* Multiplicative W) (W₀ : Submodule (ZMod 2) W)
    (hW₀_inv : ∀ γ : G ⧸ Wker G, W₀.map ((φ γ).toLinearMap) ≤ W₀)
    (hequiv : ∀ (g : G) (x : ↥H), π (MulAut.conjNormal g x) =
      Multiplicative.ofAdd (φ (QuotientGroup.mk g) (Multiplicative.toAdd (π x))))
    (g : G) (x : preimageSubmodule π W₀) :
    MulAut.conjNormal g (x : ↥H) ∈ preimageSubmodule π W₀ := by
  change Multiplicative.toAdd (π (MulAut.conjNormal g (x : ↥H))) ∈ W₀
  have hx : Multiplicative.toAdd (π (x : ↥H)) ∈ W₀ := x.2
  have heq : Multiplicative.toAdd (π (MulAut.conjNormal g (x : ↥H))) =
      (φ (QuotientGroup.mk g)) (Multiplicative.toAdd (π (x : ↥H))) := by
    rw [hequiv g (x : ↥H)]
    rfl
  rw [heq]
  exact hW₀_inv (QuotientGroup.mk g) ⟨_, hx, rfl⟩

private theorem le_iSup_map {H M : Type*} [Group H] [AddCommGroup M] [Module (ZMod 2) M]
    (φ : H →* (M ≃ₗ[ZMod 2] M)) (P : Submodule (ZMod 2) M) :
    P ≤ ⨆ γ : H, P.map (φ γ).toLinearMap := by
  have h1 : P.map ((φ 1).toLinearMap) = P := by
    rw [map_one]
    exact Submodule.map_id P
  exact h1.symm.le.trans (le_iSup (fun γ => P.map (φ γ).toLinearMap) 1)

private theorem iSup_map_le_iSup {H M : Type*} [Group H] [AddCommGroup M] [Module (ZMod 2) M]
    (φ : H →* (M ≃ₗ[ZMod 2] M)) (P : Submodule (ZMod 2) M) (γ' : H) :
    (⨆ γ : H, P.map (φ γ).toLinearMap).map ((φ γ').toLinearMap) ≤
      ⨆ γ : H, P.map (φ γ).toLinearMap := by
  rw [Submodule.map_iSup]
  refine iSup_le fun γ => ?_
  have h1 : (P.map (φ γ).toLinearMap).map ((φ γ').toLinearMap) =
      P.map (φ (γ' * γ)).toLinearMap := by
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap_mul, Module.End.mul_apply,
      map_mul]
  rw [h1]
  exact le_iSup (fun γ'' => P.map (φ γ'').toLinearMap) (γ' * γ)

private structure R21Data (p : ℕ) (G : Type) [Group G] [Finite G] (D : Subgroup G)
    (W : Type) [AddCommGroup W] [Module (ZMod 2) W] where
  φ : (G ⧸ Wker G) →* (W ≃ₗ[ZMod 2] W)
  π : ↥(Xof G) →* Multiplicative W
  hφinj : Function.Injective φ
  hπsurj : Function.Surjective π
  hequiv : ∀ (g : G) (x : ↥(Xof G)),
    π (MulAut.conjNormal g x) =
      Multiplicative.ofAdd (φ (QuotientGroup.mk g) (Multiplicative.toAdd (π x)))
  hmem : ∀ (g : G) (x : ↥(Xof G)),
    (x : G) ∈ ⁅Xof G, Subgroup.zpowers g⁆ ⊔ ZXof G ↔
      Multiplicative.toAdd (π x) ∈ LinearMap.range
        ((φ (QuotientGroup.mk g) : W →ₗ[ZMod 2] W) - LinearMap.id)
  horder : ∀ g : G, Nat.card ↥(⁅Xof G, Subgroup.zpowers g⁆ ⊔ ZXof G) =
    Nat.card ↥(ZXof G) * 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.range
      ((φ (QuotientGroup.mk g) : W →ₗ[ZMod 2] W) - LinearMap.id))
  d : G
  hd : Subgroup.zpowers d = D

private theorem preimageSubmodule_normal {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (S : R21Data p G D W) (W₀ : Submodule (ZMod 2) W)
    (hW₀_inv : ∀ γ : G ⧸ Wker G, W₀.map ((S.φ γ).toLinearMap) ≤ W₀) :
    ((preimageSubmodule S.π W₀).map (Xof G).subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  rw [← hyx]
  refine Subgroup.mem_map.mpr ⟨MulAut.conjNormal g y,
    preimageSubmodule_conj_mem S.φ S.π W₀ hW₀_inv S.hequiv g ⟨y, hy⟩, ?_⟩
  exact MulAut.conjNormal_apply g y

private theorem tof_le_preimageSubmodule {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (S : R21Data p G D W) (W₀ : Submodule (ZMod 2) W)
    (hP : LinearMap.range ((S.φ (QuotientGroup.mk S.d) : W →ₗ[ZMod 2] W) - LinearMap.id) ≤ W₀) :
    Tof G D ≤ (preimageSubmodule S.π W₀).map (Xof G).subtype := by
  intro x hxT
  have hxX : x ∈ Xof G := Subgroup.commutator_le_left (H₁ := Xof G) (H₂ := D) hxT
  refine Subgroup.mem_map.mpr ⟨⟨x, hxX⟩, ?_, rfl⟩
  have hxT' : x ∈ ⁅Xof G, Subgroup.zpowers S.d⁆ := by rw [S.hd]; exact hxT
  have hxsup : x ∈ ⁅Xof G, Subgroup.zpowers S.d⁆ ⊔ ZXof G := Subgroup.mem_sup_left hxT'
  exact hP ((S.hmem S.d ⟨x, hxX⟩).mp hxsup)

private theorem preimageSubmodule_eq_top (c : Front45 p G D) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (S : R21Data p G D W) (W₀ : Submodule (ZMod 2) W)
    (hY_normal : ((preimageSubmodule S.π W₀).map (Xof G).subtype).Normal)
    (hT : Tof G D ≤ (preimageSubmodule S.π W₀).map (Xof G).subtype) :
    W₀ = ⊤ := by
  have hX_le_Y : Xof G ≤ (preimageSubmodule S.π W₀).map (Xof G).subtype := by
    haveI : ((preimageSubmodule S.π W₀).map (Xof G).subtype).Normal := hY_normal
    have := Subgroup.normalClosure_le_normal hT
    rwa [c.X_gen] at this
  have hYeq : (preimageSubmodule S.π W₀).map (Xof G).subtype = Xof G :=
    le_antisymm (Subgroup.map_subtype_le _) hX_le_Y
  have hπmem : ∀ x : ↥(Xof G), Multiplicative.toAdd (S.π x) ∈ W₀ := by
    intro x
    have hx : (x : G) ∈ (preimageSubmodule S.π W₀).map (Xof G).subtype := by
      rw [hYeq]; exact x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  rw [eq_top_iff]
  intro w _
  obtain ⟨x, hx⟩ := S.hπsurj (Multiplicative.ofAdd w)
  have := hπmem x
  rwa [hx] at this

private theorem r21_finrank_range (c : Front45 p G D) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (S : R21Data p G D W) :
    Module.finrank (ZMod 2) ↥(LinearMap.range
      ((S.φ (QuotientGroup.mk S.d) : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2 := by
  have h1 := S.horder S.d
  rw [S.hd, uc45_card_TZ c.toPre45] at h1
  have h1' : Nat.card ↥(ZXof G) * 4 = Nat.card ↥(ZXof G) *
      2 ^ Module.finrank (ZMod 2) ↥(LinearMap.range
        ((S.φ (QuotientGroup.mk S.d) : W →ₗ[ZMod 2] W) - LinearMap.id)) := by
    rw [mul_comm (Nat.card ↥(ZXof G)) 4]
    exact h1
  have h2 : 4 = 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.range
      ((S.φ (QuotientGroup.mk S.d) : W →ₗ[ZMod 2] W) - LinearMap.id)) :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos h1'
  have h3 : (2 : ℕ) ^ Module.finrank (ZMod 2) ↥(LinearMap.range
      ((S.φ (QuotientGroup.mk S.d) : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2 ^ 2 := by
    rw [← h2]; norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h3

private theorem r21_span_eq_top (c : Front45 p G D) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (S : R21Data p G D W) (P : Submodule (ZMod 2) W)
    (hP : P = LinearMap.range ((S.φ (QuotientGroup.mk S.d) : W →ₗ[ZMod 2] W) - LinearMap.id))
    (hPle : P ≤ ⨆ γ : G ⧸ Wker G, P.map (S.φ γ).toLinearMap) :
    (⨆ γ : G ⧸ Wker G, P.map (S.φ γ).toLinearMap) = ⊤ := by
  let W₀ : Submodule (ZMod 2) W := ⨆ γ : G ⧸ Wker G, P.map (S.φ γ).toLinearMap
  have hinv : ∀ γ' : G ⧸ Wker G, W₀.map ((S.φ γ').toLinearMap) ≤ W₀ :=
    fun γ' => iSup_map_le_iSup S.φ P γ'
  have hY_normal : ((preimageSubmodule S.π W₀).map (Xof G).subtype).Normal :=
    preimageSubmodule_normal S W₀ hinv
  have hrange : LinearMap.range
      ((S.φ (QuotientGroup.mk S.d) : W →ₗ[ZMod 2] W) - LinearMap.id) ≤ W₀ := by
    rw [← hP]
    exact hPle
  have hT : Tof G D ≤ (preimageSubmodule S.π W₀).map (Xof G).subtype :=
    tof_le_preimageSubmodule S W₀ hrange
  exact preimageSubmodule_eq_top c S W₀ hY_normal hT

private theorem phi_mk_comm (c : Front45 p G D) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (S : R21Data p G D W) {h : G} (hh : h ∈ CFSG.pPrimeCore 3 G) (g : G) :
    S.φ (QuotientGroup.mk h) * S.φ (QuotientGroup.mk g) =
      S.φ (QuotientGroup.mk g) * S.φ (QuotientGroup.mk h) := by
  have hcomm : (QuotientGroup.mk h : G ⧸ Wker G) * QuotientGroup.mk g =
      QuotientGroup.mk g * QuotientGroup.mk h := by
    have hmemX : ⁅h, g⁆ ∈ Xof G := by
      have hmem' := Subgroup.commutator_mem_commutator (H₁ := CFSG.pPrimeCore 3 G)
        (H₂ := ⊤) hh (Subgroup.mem_top g)
      rwa [show ⁅CFSG.pPrimeCore 3 G, (⊤ : Subgroup G)⁆ = Kof G from rfl, c.K_eq] at hmem'
    have hmemW : ⁅h, g⁆ ∈ Wker G := xof_le_wker c.toPre45 hmemX
    rw [← commutatorElement_eq_one_iff_mul_comm]
    have hmap : QuotientGroup.mk ⁅h, g⁆ =
        ⁅(QuotientGroup.mk h : G ⧸ Wker G), (QuotientGroup.mk g : G ⧸ Wker G)⁆ := by
      simpa only [QuotientGroup.mk'_apply] using
        map_commutatorElement (QuotientGroup.mk' (Wker G)) h g
    rw [← hmap]
    exact (QuotientGroup.eq_one_iff (N := Wker G) ⁅h, g⁆).mpr hmemW
  rw [← map_mul, ← map_mul, hcomm]

private theorem phi_linearMap_comm (c : Front45 p G D) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (S : R21Data p G D W) {h : G}
    (hh : h ∈ CFSG.pPrimeCore 3 G) (g : G) :
    (S.φ (QuotientGroup.mk h)).toLinearMap * (S.φ (QuotientGroup.mk g)).toLinearMap =
      (S.φ (QuotientGroup.mk g)).toLinearMap * (S.φ (QuotientGroup.mk h)).toLinearMap := by
  have hcomm := phi_mk_comm c S hh g
  rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul]
  exact congrArg (fun e : W ≃ₗ[ZMod 2] W => (e : W →ₗ[ZMod 2] W)) hcomm

private theorem r21_action_cube (c : Front45 p G D) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (S : R21Data p G D W) {h : G}
    (hh : h ∈ CFSG.pPrimeCore 3 G) :
    (S.φ (QuotientGroup.mk h)).toLinearMap ^ 3 = 1 := by
  let a : W ≃ₗ[ZMod 2] W := S.φ (QuotientGroup.mk S.d)
  let P : Submodule (ZMod 2) W := LinearMap.range ((a : W →ₗ[ZMod 2] W) - LinearMap.id)
  have hrankP : Module.finrank (ZMod 2) P = 2 := r21_finrank_range c S
  let W₀ : Submodule (ZMod 2) W := ⨆ γ : G ⧸ Wker G, P.map (S.φ γ).toLinearMap
  have hW₀top : W₀ = ⊤ := r21_span_eq_top c S P rfl (le_iSup_map S.φ P)
  have ha3 : a ^ 3 = 1 := by
    show (S.φ (QuotientGroup.mk S.d)) ^ 3 = 1
    rw [← map_pow, show (QuotientGroup.mk S.d : G ⧸ Wker G) ^ 3 = 1 from
      orderOf_dvd_iff_pow_eq_one.mp (by rw [uc45_orderOf_mk_of_zpowers c.toPre45 S.hd]), map_one]
  let ch : W ≃ₗ[ZMod 2] W := S.φ (QuotientGroup.mk h)
  let chL : Module.End (ZMod 2) W := ch.toLinearMap
  have hchφ : ∀ γ : G ⧸ Wker G, ∀ u : W, chL (S.φ γ u) = S.φ γ (chL u) := by
    intro γ u
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    exact congrFun (congrArg (fun f : Module.End (ZMod 2) W => (f : W → W))
      (phi_linearMap_comm c S hh g)) u
  have hcomm : Commute chL (a : W →ₗ[ZMod 2] W) := by
    show chL * (a : W →ₗ[ZMod 2] W) = (a : W →ₗ[ZMod 2] W) * chL
    ext u
    exact hchφ (QuotientGroup.mk S.d) u
  have hfixP : ∀ u ∈ P, chL (chL (chL u)) = u :=
    range_sub_one_restrict_cube a ha3 chL hcomm ch.injective hrankP
  exact linearMap_cube_eq_one_of_fixes_span chL P S.φ W₀ rfl hW₀top hchφ hfixP

private theorem r21_action_eq_one {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (S : R21Data p G D W) {h : G} (hh : h ∈ CFSG.pPrimeCore 3 G)
    (h3 : (S.φ (QuotientGroup.mk h)).toLinearMap ^ 3 = 1) : h ∈ Wker G := by
  have hchorder : orderOf (S.φ (QuotientGroup.mk h)).toLinearMap =
      orderOf (S.φ (QuotientGroup.mk h)) := orderOf_toLinearMap_eq _
  have hdvd : orderOf (S.φ (QuotientGroup.mk h)) ∣ 3 := by
    rw [← hchorder]
    exact orderOf_dvd_iff_pow_eq_one.mpr h3
  have hcop : Nat.Coprime 3 (orderOf (S.φ (QuotientGroup.mk h))) := by
    have hcopH : Nat.Coprime 3 (Nat.card ↥(CFSG.pPrimeCore 3 G)) := CFSG.pPrimeCore_coprime_card
    have horderH : orderOf h ∣ Nat.card ↥(CFSG.pPrimeCore 3 G) := Subgroup.orderOf_dvd_natCard _ hh
    have hcoph : Nat.Coprime 3 (orderOf h) := hcopH.coprime_dvd_right horderH
    have horder_mk : orderOf (QuotientGroup.mk h : G ⧸ Wker G) ∣ orderOf h :=
      orderOf_map_dvd (QuotientGroup.mk' (Wker G)) h
    have horder_ch : orderOf (S.φ (QuotientGroup.mk h)) =
        orderOf (QuotientGroup.mk h : G ⧸ Wker G) := orderOf_injective S.φ S.hφinj _
    rw [horder_ch]
    exact hcoph.coprime_dvd_right horder_mk
  have hone : orderOf (S.φ (QuotientGroup.mk h)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hdvd dvd_rfl
  have hch1 : S.φ (QuotientGroup.mk h) = 1 := orderOf_eq_one_iff.mp hone
  have hmk : QuotientGroup.mk h = 1 := S.hφinj (by rw [hch1, map_one])
  exact (QuotientGroup.eq_one_iff (N := Wker G) h).mp hmk

theorem r2_H_le_wker (hSymp : SympData) (c : Front45 p G D) :
    CFSG.pPrimeCore 3 G ≤ Wker G := by
  haveI hcyc : IsCyclic ↥(Subgroup.center ↥(Xof G)) := uc45_center_Xof_isCyclic c.toPre45
  obtain ⟨W, _, _, hWfin, _, φ, π, _, _, hφinj, _, hπsurj, _, hequiv, _, hmem, horder⟩ :=
    hSymp G (Xof G) (Wker G) (xof_isPGroup (G := G)) c.class_two.1
      c.class_two.2 hcyc (fun g => mem_wker (G := G) (g := g))
  haveI : Finite W := hWfin
  have hcycD : IsCyclic ↥D := isCyclic_of_prime_card c.card_three
  obtain ⟨d, hd⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top D).mp hcycD
  let S : R21Data p G D W :=
    { φ := φ, π := π, hφinj := hφinj, hπsurj := hπsurj, hequiv := hequiv,
      hmem := hmem, horder := horder, d := d, hd := hd }
  intro h hh
  exact r21_action_eq_one S hh (r21_action_cube c S hh)

theorem r2_wker_eq (hSymp : SympData) (c : Front45 p G D) :
    Wker G = CFSG.pPrimeCore 3 G := by
  have hle : Wker G ≤ CFSG.pPrimeCore 3 G := by
    refine proper_normal_le_pPrimeCore c.card_three c.gen c.rank (Wker G) ?_
    intro htop
    have hDle : D ≤ Wker G := htop ▸ le_top
    have hDbot : D = ⊥ := by
      rw [← inf_eq_left.mpr hDle, uc45_D_inf_wker c.toPre45]
    have hcard : Nat.card ↥D = 1 := by rw [hDbot, Subgroup.card_bot]
    rw [c.card_three] at hcard
    exact (by decide : (3 : ℕ) ≠ 1) hcard
  exact le_antisymm hle (r2_H_le_wker hSymp c)

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
