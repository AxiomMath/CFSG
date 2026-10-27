module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Basic
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUReduceUAuxAbs

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7A3ReduceMAux_H_le_kerAug {p m : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}
    {H A : Subgroup (V ≃ₗ[ZMod p] V)} (hD : A3LinData p m V θ z H A)
    (hM : ∀ r ∈ H, GGLinRefl r → ggLinMove r ≤ (a3Aug p m).map θ) :
    H ≤ hdRo7SUReduceUAux_kerAug p ((a3Aug p m).map θ) := by
  obtain ⟨S, hS, hHS, -⟩ := hD.hgen
  intro g hg
  rw [hHS] at hg
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
      intro v
      have hmove : s v - v ∈ ggLinMove s := by
        exact ⟨v, rfl⟩
      exact hM s (hS s hs).1 (hS s hs).2 hmove
  | one =>
      intro v
      simp
  | mul g h _ _ hgh hgh' =>
      intro v
      have heq : (g * h) v - v = (g (h v) - h v) + (h v - v) := by
        rw [LinearEquiv.mul_apply]; abel
      rw [heq]
      exact Submodule.add_mem _ (hgh (h v)) (hgh' v)
  | inv g _ hgh =>
      intro v
      have heq : g⁻¹ v - v = -(g (g⁻¹ v) - g⁻¹ v) := by
        rw [show g (g⁻¹ v) = v from LinearEquiv.apply_symm_apply g v]
        abel
      rw [heq]
      exact Submodule.neg_mem _ (hgh (g⁻¹ v))

private theorem hdRo7A3ReduceMAux_sup_span_z {p m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}
    (hfr : A3Frame p m θ z) :
    (a3Aug p m).map θ ⊔ Submodule.span (ZMod p) {z} = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  obtain ⟨u, hu, c, rfl⟩ := hfr.2.1 v
  exact Submodule.mem_sup.mpr ⟨θ u, Submodule.mem_map.mpr ⟨u, hu, rfl⟩, c • z,
    Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton z)), rfl⟩

private theorem hdRo7A3ReduceMAux_transv_of_fixes {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (U : Submodule (ZMod p) V) (z : V)
    (hsup : U ⊔ Submodule.span (ZMod p) {z} = ⊤) (g : V ≃ₗ[ZMod p] V)
    (hg : g ∈ hdRo7SUReduceUAux_kerAug p U) (hfix : ∀ u ∈ U, g u = u) (hne : g ≠ 1) :
    C2Transv p g := by
  have hz : g z - z ∈ U := hg z
  have hz0 : g z - z ≠ 0 := by
    intro h0
    apply hne
    ext v
    have hgz : g z = z := sub_eq_zero.mp h0
    have hv : v ∈ U ⊔ Submodule.span (ZMod p) {z} := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
    calc g v = g (u + w) := by rw [huw]
      _ = g u + g w := map_add g u w
      _ = u + c • g z := by rw [hfix u hu, ← hc, map_smul]
      _ = u + c • z := by rw [hgz]
      _ = u + w := by rw [hc]
      _ = v := huw
  have hmove : ggLinMove g = Submodule.span (ZMod p) {g z - z} := by
    apply le_antisymm
    · rintro y ⟨v, rfl⟩
      change g v - v ∈ Submodule.span (ZMod p) {g z - z}
      have hv : v ∈ U ⊔ Submodule.span (ZMod p) {z} := by rw [hsup]; exact Submodule.mem_top
      obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hv
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
      have heq : g v - v = c • (g z - z) := by
        calc g v - v = g (u + w) - (u + w) := by rw [huw]
          _ = (g u + g w) - (u + w) := by rw [map_add]
          _ = (g u + c • g z) - (u + c • z) := by rw [← hc, map_smul]
          _ = c • (g z - z) := by rw [hfix u hu]; module
      rw [heq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨z, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hmove, finrank_span_singleton hz0]
  · intro w
    have hw : g w - w ∈ U := hg w
    rw [hfix _ hw]

private theorem hdRo7A3ReduceMAux_res_injective {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (U : Submodule (ZMod p) V) (z : V)
    (hsup : U ⊔ Submodule.span (ZMod p) {z} = ⊤)
    (H A : Subgroup (V ≃ₗ[ZMod p] V)) (hHK : H ≤ hdRo7SUReduceUAux_kerAug p U)
    (hHA : H ≤ A) (hNoT : ∀ a ∈ A, ¬ C2Transv p a) :
    Function.Injective (hdRo7SUReduceUAux_res U H hHK) := by
  have key : ∀ g : ↥H, hdRo7SUReduceUAux_res U H hHK g = 1 → g = 1 := by
    intro g hg
    by_contra hne
    have hg1 : (g : V ≃ₗ[ZMod p] V) ≠ 1 := fun h => hne (Subtype.ext h)
    have hfix : ∀ u ∈ U, (g : V ≃ₗ[ZMod p] V) u = u := by
      intro u hu
      have happ := congrArg (fun (e : U ≃ₗ[ZMod p] U) => (e ⟨u, hu⟩ : V)) hg
      exact happ
    exact hNoT g.1 (hHA g.2)
      (hdRo7A3ReduceMAux_transv_of_fixes U z hsup g.1 (hHK g.2) hfix hg1)
  intro g h hgh
  have h1 : g * h⁻¹ = 1 := by
    apply key
    rw [map_mul, map_inv, hgh, mul_inv_cancel]
  exact mul_inv_eq_one.mp h1

private theorem hdRo7A3ReduceMAux_range_eq_closure {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (U : Submodule (ZMod p) V)
    {H : Subgroup (V ≃ₗ[ZMod p] V)}
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p U)
    (S : Set (V ≃ₗ[ZMod p] V)) (hS : ∀ s ∈ S, s ∈ H ∧ GGLinRefl s)
    (hScl : H = Subgroup.closure S)
    (h2 : (2 : ZMod p) ≠ 0) :
    (hdRo7SUReduceUAux_res U H hHK).range =
      Subgroup.closure {r | r ∈ (hdRo7SUReduceUAux_res U H hHK).range ∧
        GGLinRefl r} := by
  let res := hdRo7SUReduceUAux_res U H hHK
  let S' : Set ↥H := {g | (g : V ≃ₗ[ZMod p] V) ∈ S}
  have hS'img : H.subtype '' S' = S := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hx
      exact ⟨⟨x, (hS x hx).1⟩, hx, rfl⟩
  have hmap : Subgroup.map H.subtype (Subgroup.closure S') = H := by
    rw [MonoidHom.map_closure, hS'img, hScl]
  have hS'gen : Subgroup.closure S' = ⊤ := by
    apply le_antisymm le_top
    intro g _
    have hg : (g : V ≃ₗ[ZMod p] V) ∈ Subgroup.map H.subtype (Subgroup.closure S') := by
      rw [hmap]; exact g.2
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg
    have hkg' : k = g := Subtype.ext hkg
    rwa [hkg'] at hk
  have hrange : res.range = Subgroup.closure (res '' S') := by
    rw [MonoidHom.range_eq_map, ← hS'gen, MonoidHom.map_closure]
  have himage : res '' S' ⊆ {r | r ∈ res.range ∧ GGLinRefl r} := by
    rintro r ⟨g, hgS, rfl⟩
    refine ⟨⟨g, rfl⟩, ?_⟩
    have hrefl : GGLinRefl (g : V ≃ₗ[ZMod p] V) := (hS (g : V ≃ₗ[ZMod p] V) hgS).2
    have hthis := hdRo7SUReduceUAux_refl_restrict U g.1 (hHK g.2)
      (by simpa using hrefl.1) h2 hrefl.2
    change GGLinRefl (hdRo7SUReduceUAux_restrict U g.1 (hHK g.2))
    exact hthis
  rw [hrange] at himage
  apply le_antisymm
  · rw [hrange]
    exact Subgroup.closure_mono himage
  · exact (Subgroup.closure_le _).mpr (fun r hr => hr.1)

private theorem hdRo7A3ReduceMAux_card_range {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (U : Submodule (ZMod p) V)
    {H : Subgroup (V ≃ₗ[ZMod p] V)}
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p U)
    (hresinj : Function.Injective (hdRo7SUReduceUAux_res U H hHK)) :
    Nat.card ↥(hdRo7SUReduceUAux_res U H hHK).range = Nat.card ↥H := by
  let res := hdRo7SUReduceUAux_res U H hHK
  let f : ↥H → ↥res.range := fun g => ⟨res g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply hresinj
      exact congrArg Subtype.val hab
    · rintro ⟨r, hr⟩
      obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hr
      exact ⟨g, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

private theorem hdRo7A3ReduceMAux_linWeyl_lift {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (U : Submodule (ZMod p) V)
    {H : Subgroup (V ≃ₗ[ZMod p] V)}
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p U)
    (h2 : (2 : ZMod p) ≠ 0)
    (hresinj : Function.Injective (hdRo7SUReduceUAux_res U H hHK)) :
    ZS.LinWeyl p (hdRo7SUReduceUAux_res U H hHK).range → ZS.LinWeyl p H := by
  intro hR
  obtain ⟨ι, M, hM, f, hf⟩ := hR
  let res := hdRo7SUReduceUAux_res U H hHK
  let eHom : ↥H →* ↥res.range :=
    { toFun := fun g => ⟨res g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
      map_one' := by ext; rfl
      map_mul' := by intro a b; ext; rfl }
  have heHom : Function.Bijective eHom := by
    constructor
    · intro a b hab
      apply hresinj
      exact congrArg Subtype.val hab
    · rintro ⟨r, hr⟩
      obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hr
      exact ⟨g, rfl⟩
  let e : ↥H ≃* ↥res.range := MulEquiv.ofBijective eHom heHom
  refine ⟨ι, M, hM, f.trans e.symm, ?_⟩
  intro i
  let gH : ↥H := e.symm (f (M.simple i))
  let gV : V ≃ₗ[ZMod p] V := gH
  have hres_e : res gH = (f (M.simple i)).1 :=
    congrArg Subtype.val (MulEquiv.apply_symm_apply e (f (M.simple i)))
  have hsq : gH * gH = 1 := by
    apply hresinj
    rw [map_mul, map_one, hres_e]
    exact (hf i).1
  have hsqV : gV * gV = 1 := by
    change (gH : V ≃ₗ[ZMod p] V) * (gH : V ≃ₗ[ZMod p] V) = 1
    simpa using congrArg Subtype.val hsq
  have hfr : Module.finrank (ZMod p) (ggLinMove gV) = 1 := by
    have hmap := hdRo7SUReduceUAux_move_map_restrict U gV (hHK gH.2) hsqV h2
    rw [← hmap, Submodule.finrank_map_subtype_eq]
    change Module.finrank (ZMod p) (ggLinMove (res gH)) = 1
    rw [hres_e]
    exact (hf i).2
  have : ZS.IsRefl p gV := ⟨hsqV, hfr⟩
  simpa [gV, gH] using this

private theorem hdRo7A3ReduceMAux_arith_bound (d : ℕ) (hd : 10 ≤ d) :
    2 * (d + 1) * (d + 2) ≤ 2 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hle : (k + 2) * (k + 3) ≤ 2 * ((k + 1) * (k + 2)) := by
        nlinarith
      have h2 : 2 * ((k + 2) * (k + 3)) ≤ 2 * (2 * ((k + 1) * (k + 2))) := by
        exact Nat.mul_le_mul_left 2 hle
      have h3 : 2 * ((k + 1) * (k + 2)) ≤ 2 ^ k := by
        rw [← Nat.mul_assoc]
        exact ih
      calc 2 * (k + 2) * (k + 3) = 2 * ((k + 2) * (k + 3)) := by ring
        _ ≤ 2 * (2 * ((k + 1) * (k + 2))) := h2
        _ ≤ 2 * (2 ^ k) := Nat.mul_le_mul_left 2 h3
        _ = 2 ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]

private theorem hdRo7A3ReduceMAux_stabilizer_card {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (H : Subgroup (V ≃ₗ[ZMod p] V)) (z : V) :
    Nat.card (MulAction.stabilizer H z) = Nat.card {a : V ≃ₗ[ZMod p] V // a ∈ H ∧ a z = z} := by
  let e : MulAction.stabilizer H z ≃ {a : V ≃ₗ[ZMod p] V // a ∈ H ∧ a z = z} :=
    { toFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
      invFun := fun a => ⟨⟨a.1, a.2.1⟩, a.2.2⟩
      left_inv := fun g => by ext; rfl
      right_inv := fun a => by ext; rfl }
  exact Nat.card_congr e

private theorem hdRo7A3ReduceMAux_orbit_card_le {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] (M : Submodule (ZMod p) V) (z : V)
    (H : Subgroup (V ≃ₗ[ZMod p] V)) (hHK : H ≤ hdRo7SUReduceUAux_kerAug p M) :
    Nat.card (MulAction.orbit H z) ≤ Nat.card M := by
  let f : MulAction.orbit H z → M := fun v =>
    ⟨(v : V) - z, by
      obtain ⟨a, ha⟩ := v.2
      rw [← ha]
      exact hHK a.2 z⟩
  have hf_inj : Function.Injective f := by
    intro v w hvw
    have h : (v : V) - z = (w : V) - z := congrArg Subtype.val hvw
    have h2 : (v : V) = w := by
      have := congrArg (fun x => x + z) h
      simpa using this
    exact Subtype.ext h2
  exact Nat.card_le_card_of_injective f hf_inj

private theorem hdRo7A3ReduceMAux_factorial_bound {m : ℕ} (hm : 12 ≤ m) :
    3 ^ (m - 2) * (2 * m.factorial) ≤ 6 ^ (m - 2) * (m - 2).factorial := by
  have hd : 10 ≤ m - 2 := by omega
  have harith := hdRo7A3ReduceMAux_arith_bound (m - 2) hd
  have hm2 : 2 ≤ m := by omega
  have hfact : m.factorial = m * (m - 1) * (m - 2).factorial := by
    have h1 : m = (m - 1) + 1 := by omega
    have h2 : m - 1 = (m - 2) + 1 := by omega
    calc m.factorial = ((m - 1) + 1).factorial := by rw [← h1]
      _ = ((m - 1) + 1) * (m - 1).factorial := Nat.factorial_succ (m - 1)
      _ = ((m - 1) + 1) * (((m - 2) + 1).factorial) := by rw [← h2]
      _ = ((m - 1) + 1) * (((m - 2) + 1) * (m - 2).factorial) := by rw [Nat.factorial_succ (m - 2)]
      _ = m * (m - 1) * (m - 2).factorial := by
        rw [show m - 1 + 1 = m by omega, show m - 2 + 1 = m - 1 by omega]
        ring
  have hpow6 : 6 ^ (m - 2) = 2 ^ (m - 2) * 3 ^ (m - 2) := by
    rw [← Nat.mul_pow]
  rw [hfact, hpow6]
  have hle : 2 * m * (m - 1) ≤ 2 ^ (m - 2) := by
    have h1 : m - 2 + 1 = m - 1 := by omega
    have h2 : m - 2 + 2 = m := by omega
    rw [h1, h2] at harith
    calc 2 * m * (m - 1) = 2 * (m - 1) * m := by ring
      _ ≤ 2 ^ (m - 2) := harith
  calc 3 ^ (m - 2) * (2 * (m * (m - 1) * (m - 2).factorial))
      = 3 ^ (m - 2) * (2 * m * (m - 1)) * (m - 2).factorial := by ring
    _ ≤ 3 ^ (m - 2) * (2 ^ (m - 2)) * (m - 2).factorial := by
        have h1 : 3 ^ (m - 2) * (2 * m * (m - 1)) ≤ 3 ^ (m - 2) * 2 ^ (m - 2) :=
          Nat.mul_le_mul_left _ hle
        exact Nat.mul_le_mul_right _ h1
    _ = 2 ^ (m - 2) * 3 ^ (m - 2) * (m - 2).factorial := by ring

section Abs

variable {p m : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}

private theorem hdRo7A3ReduceMAux_mem_map {u : Fin m → ZMod p} (hu : u ∈ a3Aug p m) :
    θ u ∈ (a3Aug p m).map θ :=
  Submodule.mem_map.mpr ⟨u, hu, rfl⟩

private noncomputable def hdRo7A3ReduceMAux_root (i j : Fin m) :
    ↥((a3Aug p m).map θ) :=
  ⟨θ (Pi.single i 1 - Pi.single j 1),
    hdRo7A3ReduceMAux_mem_map (a3_single_sub_mem i j)⟩

private theorem hdRo7A3ReduceMAux_root_self (i : Fin m) :
    hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i i = 0 := by
  apply Subtype.ext
  simp [hdRo7A3ReduceMAux_root]

private theorem hdRo7A3ReduceMAux_aug_decomp {u : Fin m → ZMod p}
    (hu : u ∈ a3Aug p m) (i0 : Fin m) :
    u = ∑ k, u k • (Pi.single k (1 : ZMod p) - Pi.single i0 (1 : ZMod p)) := by
  have hsub : (∑ k, u k • (Pi.single k (1 : ZMod p) - Pi.single i0 (1 : ZMod p)))
      = (∑ k, u k • Pi.single k (1 : ZMod p)) -
        (∑ k, u k • Pi.single i0 (1 : ZMod p)) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
  have hsingle : (∑ k, u k • Pi.single k (1 : ZMod p)) = u := by
    have h := (Pi.basisFun (ZMod p) (Fin m)).sum_repr u
    simpa [Pi.basisFun_repr, Pi.basisFun_apply] using h
  have hconst : (∑ k, u k • Pi.single i0 (1 : ZMod p)) = 0 := by
    rw [← Finset.sum_smul]
    have hsum : (∑ k, u k) = 0 := hu
    rw [hsum, zero_smul]
  rw [hsub, hsingle, hconst, sub_zero]

private theorem hdRo7A3ReduceMAux_two_ne_zero (hp : p = 3) : (2 : ZMod p) ≠ 0 := by
  apply two_ne_zero_zmod
  omega

private theorem hdRo7A3ReduceMAux_transp {H A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hD : A3LinData p m V θ z H A) {i j : Fin m} (hij : i ≠ j) :
    ∃ (t : V ≃ₗ[ZMod p] V) (ψ : Module.Dual (ZMod p) V),
      t ∈ H ∧ A3P p m θ z t ∧ GGLinRefl t ∧ t z = z ∧
      (∀ u ∈ a3Aug p m, ψ (θ u) = u i - u j) ∧ ψ z = 0 ∧
      (∀ v, t v = v - ψ v • θ (Pi.single i 1 - Pi.single j 1)) := by
  obtain ⟨t, ψ, ht, htz, hψ, hψz, hform, hrefl⟩ :=
    a3_transp hD.hp hD.hfr (by rw [hD.hp]; exact hD.h3)
      (by have := hD.hm; omega) hij
  have htP : A3P p m θ z t := ⟨Equiv.swap i j, ht, htz⟩
  exact ⟨t, ψ, hD.hPH t htP, htP, hrefl, htz, hψ, hψz, hform⟩

private theorem hdRo7A3ReduceMAux_exists_P {H A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hD : A3LinData p m V θ z H A) (σ : Equiv.Perm (Fin m)) :
    ∃ a : V ≃ₗ[ZMod p] V, a ∈ H ∧ A3P p m θ z a ∧
      (∀ u ∈ a3Aug p m, a (θ u) = θ (fun i => u (σ.symm i))) ∧ a z = z := by
  obtain ⟨a, hact, haz⟩ :=
    a3_exists_perm hD.hfr (by rw [hD.hp]; exact hD.h3) σ
  exact ⟨a, hD.hPH a ⟨σ, hact, haz⟩, ⟨σ, hact, haz⟩, hact, haz⟩

private theorem hdRo7A3ReduceMAux_P_root {H : Subgroup (V ≃ₗ[ZMod p] V)}
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p ((a3Aug p m).map θ))
    {σ : Equiv.Perm (Fin m)} {a : V ≃ₗ[ZMod p] V} (haH : a ∈ H)
    (hact : ∀ u ∈ a3Aug p m, a (θ u) = θ (fun i => u (σ.symm i))) (i j : Fin m) :
    (hdRo7SUReduceUAux_res ((a3Aug p m).map θ) H hHK ⟨a, haH⟩)
        (hdRo7A3ReduceMAux_root i j) =
      hdRo7A3ReduceMAux_root (σ i) (σ j) := by
  apply Subtype.ext
  change a (θ (Pi.single i 1 - Pi.single j 1)) =
    θ (Pi.single (σ i) 1 - Pi.single (σ j) 1)
  rw [hact _ (a3_single_sub_mem i j)]
  congr 1
  funext q
  simp only [Pi.sub_apply, Pi.single_apply, Equiv.symm_apply_eq]

private theorem hdRo7A3ReduceMAux_psi_root (hp : p = 3) {i j : Fin m}
    {ψ : Module.Dual (ZMod p) V}
    (hψ : ∀ u ∈ a3Aug p m, ψ (θ u) = u i - u j) (hij : i ≠ j) :
    ψ (θ (Pi.single i 1 - Pi.single j 1)) = 2 := by
  subst hp
  rw [hψ _ (a3_single_sub_mem i j)]
  have h2 : ((Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) -
        (Pi.single j (1 : ZMod 3) : Fin m → ZMod 3)) i -
        ((Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) -
        (Pi.single j (1 : ZMod 3) : Fin m → ZMod 3)) j = 2 := by
    simp [Pi.sub_apply, hij]
    ring
  exact h2

private theorem hdRo7A3ReduceMAux_val_self {a b : Fin m} (h : a ≠ b) :
    ((Pi.single a 1 - Pi.single b 1 : Fin m → ZMod p) a) = 1 := by
  simp [Pi.sub_apply, h]

private theorem hdRo7A3ReduceMAux_val_snd {a b : Fin m} (h : a ≠ b) :
    ((Pi.single a 1 - Pi.single b 1 : Fin m → ZMod p) b) = -1 := by
  simp [Pi.sub_apply, Ne.symm h]

private theorem hdRo7A3ReduceMAux_val_other {a b q : Fin m} (h1 : q ≠ a) (h2 : q ≠ b) :
    ((Pi.single a 1 - Pi.single b 1 : Fin m → ZMod p) q) = 0 := by
  simp [Pi.sub_apply, h1, h2]

private theorem hdRo7A3ReduceMAux_roots_span {i₀ : Fin m}
    (W : Submodule (ZMod p) ↥((a3Aug p m).map θ))
    (hW : ∀ k l : Fin m, hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) k l ∈ W) :
    W = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  obtain ⟨u, hu, hux⟩ := Submodule.mem_map.mp x.2
  have hx : x = ∑ k, u k • hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) k i₀ := by
    apply Subtype.ext
    have hsum : ((∑ k, u k • hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) k i₀ :
        ↥((a3Aug p m).map θ)) : V) =
        θ (∑ k, u k • (Pi.single k (1 : ZMod p) - Pi.single i₀ 1)) := by
      simp [hdRo7A3ReduceMAux_root, map_sum, map_smul]
    rw [hsum, ← hux]
    congr 1
    exact hdRo7A3ReduceMAux_aug_decomp hu i₀
  rw [hx]
  exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (hW k i₀))

private theorem hdRo7A3ReduceMAux_perm_pair {i j k l : Fin m} (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ σ : Equiv.Perm (Fin m), σ i = k ∧ σ j = l := by
  have hne : Equiv.swap i k j ≠ k := by
    intro h
    have h' : Equiv.swap i k j = Equiv.swap i k i := by rw [h, Equiv.swap_apply_left]
    exact hij ((Equiv.swap i k).injective h').symm
  refine ⟨Equiv.swap l (Equiv.swap i k j) * Equiv.swap i k, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hkl (Ne.symm hne)
  · rw [Equiv.Perm.mul_apply]
    exact Equiv.swap_apply_right l (Equiv.swap i k j)

private theorem hdRo7A3ReduceMAux_exists_fourth {m : ℕ} (hm : 4 ≤ m) (i j k : Fin m) :
    ∃ ℓ : Fin m, ℓ ≠ i ∧ ℓ ≠ j ∧ ℓ ≠ k := by
  have hlt : ({i, j, k} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have h1 : ({i, j, k} : Finset (Fin m)).card ≤ 3 := by
      have ha : ({i, j, k} : Finset (Fin m)).card ≤ ({j, k} : Finset (Fin m)).card + 1 :=
        Finset.card_insert_le i {j, k}
      have hb : ({j, k} : Finset (Fin m)).card ≤ ({k} : Finset (Fin m)).card + 1 :=
        Finset.card_insert_le j {k}
      have hc : ({k} : Finset (Fin m)).card = 1 := Finset.card_singleton k
      omega
    omega
  obtain ⟨ℓ, -, hℓ⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hℓ
  exact ⟨ℓ, hℓ.1, hℓ.2.1, hℓ.2.2⟩

private theorem hdRo7A3ReduceMAux_root_mem_of_ne_zero {H A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hD : A3LinData p m V θ z H A) (hM1 : θ (fun _ => 1) = 0)
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p ((a3Aug p m).map θ))
    {W : Submodule (ZMod p) ↥((a3Aug p m).map θ)}
    (hW : ∀ a ∈ (hdRo7SUReduceUAux_res ((a3Aug p m).map θ) H hHK).range,
      ∀ w ∈ W, a w ∈ W)
    {w : ↥((a3Aug p m).map θ)} (hw : w ∈ W) (hw0 : w ≠ 0) :
    ∃ i j : Fin m, i ≠ j ∧ hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i j ∈ W := by
  obtain ⟨u, hu, hux⟩ := Submodule.mem_map.mp w.2
  have hwv : θ u ≠ 0 := by
    intro h0
    apply hw0
    apply Subtype.ext
    rw [← hux, h0]
    rfl
  let i₀ : Fin m := ⟨0, by have := hD.hm; omega⟩
  have hex : ∃ i : Fin m, u i ≠ u i₀ := by
    by_contra h
    push Not at h
    apply hwv
    have huconst : u = fun _ => u i₀ := funext h
    rw [huconst]
    rw [show (fun _ : Fin m => u i₀) = u i₀ • (fun _ => (1 : ZMod p)) by
      funext q; simp]
    rw [map_smul, hM1, smul_zero]
  obtain ⟨i, hi⟩ := hex
  have hij : i ≠ i₀ := fun h => hi (by rw [h])
  obtain ⟨t, ψ, htH, -, -, -, hψ, -, hform⟩ := hdRo7A3ReduceMAux_transp hD hij
  let a : ↥H := ⟨t, htH⟩
  let res := hdRo7SUReduceUAux_res ((a3Aug p m).map θ) H hHK
  have hsR : res a ∈ res.range := MonoidHom.mem_range.mpr ⟨a, rfl⟩
  have hsw : res a w ∈ W := hW (res a) hsR w hw
  have hdiff : res a w - w =
      -(u i - u i₀) • hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i i₀ := by
    apply Subtype.ext
    change ((res a w : ↥((a3Aug p m).map θ)) : V) - w.1 =
      -((u i - u i₀)) • θ (Pi.single i 1 - Pi.single i₀ 1)
    have hsval : ((res a w : ↥((a3Aug p m).map θ)) : V) = t w.1 := rfl
    rw [hsval, ← hux, hform (θ u), hψ u hu]
    module
  have hmem : -(u i - u i₀) • hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i i₀ ∈ W := by
    rw [← hdiff]
    exact Submodule.sub_mem _ hsw hw
  have hc : -(u i - u i₀) ≠ 0 := neg_ne_zero.mpr (sub_ne_zero.mpr hi)
  refine ⟨i, i₀, hij, ?_⟩
  have hroot : hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i i₀ =
      (-(u i - u i₀))⁻¹ • (-(u i - u i₀) •
        hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i i₀) := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hroot]
  exact Submodule.smul_mem _ _ hmem

private theorem hdRo7A3ReduceMAux_irred {H A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hD : A3LinData p m V θ z H A) (hM1 : θ (fun _ => 1) = 0)
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p ((a3Aug p m).map θ)) :
    ∀ W : Submodule (ZMod p) ↥((a3Aug p m).map θ),
      (∀ a ∈ (hdRo7SUReduceUAux_res ((a3Aug p m).map θ) H hHK).range,
        ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨i, j, hij, hroot⟩ :=
      hdRo7A3ReduceMAux_root_mem_of_ne_zero hD hM1 hHK hW hwW hw0
    have hall : ∀ k l : Fin m, hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) k l ∈ W := by
      intro k l
      by_cases hkl : k = l
      · rw [hkl, hdRo7A3ReduceMAux_root_self]
        exact W.zero_mem
      · obtain ⟨σ, hσi, hσj⟩ := hdRo7A3ReduceMAux_perm_pair hij hkl
        obtain ⟨a, haH, -, hact, -⟩ := hdRo7A3ReduceMAux_exists_P hD σ
        have hmem := hW (hdRo7SUReduceUAux_res ((a3Aug p m).map θ) H hHK ⟨a, haH⟩)
          (MonoidHom.mem_range.mpr ⟨⟨a, haH⟩, rfl⟩)
          (hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i j) hroot
        rw [hdRo7A3ReduceMAux_P_root hHK haH hact i j, hσi, hσj] at hmem
        exact hmem
    rw [hdRo7A3ReduceMAux_roots_span (p := p) (m := m) (θ := θ) (i₀ := i) W hall]

private theorem hdRo7A3ReduceMAux_root_eigen {H A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hD : A3LinData p m V θ z H A)
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p ((a3Aug p m).map θ))
    {T : Module.End (ZMod p) ↥((a3Aug p m).map θ)}
    (hT : ∀ a ∈ (hdRo7SUReduceUAux_res ((a3Aug p m).map θ) H hHK).range,
      T ∘ₗ (a : ↥((a3Aug p m).map θ) →ₗ[ZMod p] ↥((a3Aug p m).map θ)) =
        (a : ↥((a3Aug p m).map θ) →ₗ[ZMod p] ↥((a3Aug p m).map θ)) ∘ₗ T)
    {i j : Fin m} (hij : i ≠ j) :
    ∃ α : ZMod p, T (hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i j) =
      α • hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i j := by
  obtain ⟨t, ψ, htH, -, -, -, hψ, -, hform⟩ := hdRo7A3ReduceMAux_transp hD hij
  let a : ↥H := ⟨t, htH⟩
  let res := hdRo7SUReduceUAux_res ((a3Aug p m).map θ) H hHK
  let s : ↥((a3Aug p m).map θ) →ₗ[ZMod p] ↥((a3Aug p m).map θ) :=
    (res a : ↥((a3Aug p m).map θ) ≃ₗ[ZMod p] ↥((a3Aug p m).map θ))
  let r := hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i j
  have hsR : res a ∈ res.range := MonoidHom.mem_range.mpr ⟨a, rfl⟩
  have hψr : ψ (r : V) = 2 := by
    change ψ (θ (Pi.single i 1 - Pi.single j 1)) = 2
    exact hdRo7A3ReduceMAux_psi_root hD.hp hψ hij
  have hsform : ∀ x : ↥((a3Aug p m).map θ), s x = x - ψ (x : V) • r := by
    intro x
    change ((res a) x : ↥((a3Aug p m).map θ)) = x - ψ (x : V) • r
    apply Subtype.ext
    change ((res a x : ↥((a3Aug p m).map θ)) : V) =
      x.1 - ψ x.1 • θ (Pi.single i 1 - Pi.single j 1)
    have hsval : ((res a x : ↥((a3Aug p m).map θ)) : V) = t x.1 := rfl
    rw [hsval, hform x.1]
  have hroot : s r = -r := by
    rw [hsform, hψr]
    module
  have hcomm : T (s r) = s (T r) := by
    have h := congrArg (fun (f : ↥((a3Aug p m).map θ) →ₗ[ZMod p] ↥((a3Aug p m).map θ)) =>
      f r) (hT (res a) hsR)
    simpa only [LinearMap.comp_apply, s] using h
  rw [hroot, map_neg, hsform (T r)] at hcomm
  have h2 : (2 : ZMod p) • T r = ψ (T r).1 • r := by
    have h3 : -T r + ψ (T r).1 • r = T r := (eq_sub_iff_add_eq).mp hcomm
    have h4 : ψ (T r).1 • r = T r + T r := by
      rw [← sub_neg_eq_add, eq_sub_iff_add_eq, add_comm]
      exact h3
    rw [two_smul]
    exact h4.symm
  refine ⟨(2 : ZMod p)⁻¹ * ψ (T r).1, ?_⟩
  calc T r = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • T r) := by
        rw [smul_smul, inv_mul_cancel₀ (hdRo7A3ReduceMAux_two_ne_zero hD.hp), one_smul]
    _ = (2 : ZMod p)⁻¹ • (ψ (T r).1 • r) := by rw [h2]
    _ = ((2 : ZMod p)⁻¹ * ψ (T r).1) • r := by rw [smul_smul]

private theorem hdRo7A3ReduceMAux_root_indep {H A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hD : A3LinData p m V θ z H A)
    {i j k ℓ : Fin m} (hiℓ : ℓ ≠ i) (hjℓ : ℓ ≠ j) (hkℓ : ℓ ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {a b : ZMod p}
    (h : a • hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i j +
      b • hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i k = 0) :
    a = 0 ∧ b = 0 := by
  have hv : θ (a • (Pi.single i 1 - Pi.single j 1) +
      b • (Pi.single i 1 - Pi.single k 1)) = 0 := by
    rw [map_add, map_smul, map_smul]
    simpa [hdRo7A3ReduceMAux_root] using congrArg Subtype.val h
  have hmem : a • (Pi.single i 1 - Pi.single j 1) +
      b • (Pi.single i 1 - Pi.single k 1) ∈ a3Aug p m :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (a3_single_sub_mem i j))
      (Submodule.smul_mem _ _ (a3_single_sub_mem i k))
  obtain ⟨c, hc⟩ := hD.hfr.1 _ hmem hv
  have hℓ0 : (a • (Pi.single i 1 - Pi.single j 1) +
      b • (Pi.single i 1 - Pi.single k 1) : Fin m → ZMod p) ℓ = 0 := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      hdRo7A3ReduceMAux_val_other hiℓ hjℓ, hdRo7A3ReduceMAux_val_other hiℓ hkℓ]
    ring
  have hc0 : c = 0 := by rw [← congrFun hc ℓ, hℓ0]
  have hi0 : (a • (Pi.single i 1 - Pi.single j 1) +
      b • (Pi.single i 1 - Pi.single k 1) : Fin m → ZMod p) i = a + b := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      hdRo7A3ReduceMAux_val_self hij, hdRo7A3ReduceMAux_val_self hik]
    ring
  have hj0 : (a • (Pi.single i 1 - Pi.single j 1) +
      b • (Pi.single i 1 - Pi.single k 1) : Fin m → ZMod p) j = -a := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      hdRo7A3ReduceMAux_val_snd hij, hdRo7A3ReduceMAux_val_other (Ne.symm hij) hjk]
    ring
  have hai : a + b = 0 := by rw [← hi0, congrFun hc i, hc0]
  have haj : a = 0 := by rw [← neg_eq_zero, ← hj0, congrFun hc j, hc0]
  refine ⟨haj, ?_⟩
  rw [haj, zero_add] at hai
  exact hai

private theorem hdRo7A3ReduceMAux_commutant {H A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hD : A3LinData p m V θ z H A)
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p ((a3Aug p m).map θ))
    {T : Module.End (ZMod p) ↥((a3Aug p m).map θ)}
    (hT : ∀ a ∈ (hdRo7SUReduceUAux_res ((a3Aug p m).map θ) H hHK).range,
      T ∘ₗ (a : ↥((a3Aug p m).map θ) →ₗ[ZMod p] ↥((a3Aug p m).map θ)) =
        (a : ↥((a3Aug p m).map θ) →ₗ[ZMod p] ↥((a3Aug p m).map θ)) ∘ₗ T) :
    ∃ c : ZMod p, T = c • LinearMap.id := by
  classical
  let i0 : Fin m := ⟨0, by have := hD.hm; omega⟩
  let j0 : Fin m := ⟨1, by have := hD.hm; omega⟩
  have hj0 : j0 ≠ i0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [i0, j0] at hv
  have hm4 : 4 ≤ m := by have := hD.hm; omega
  have heig : ∀ (i j : Fin m), i ≠ j → ∃ α : ZMod p,
      T (hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i j) =
        α • hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i j :=
    fun i j hij => hdRo7A3ReduceMAux_root_eigen hD hHK hT hij
  obtain ⟨α, hα⟩ := heig i0 j0 (Ne.symm hj0)
  have hsame : ∀ (j k : Fin m), j ≠ i0 → k ≠ i0 → j ≠ k → ∀ α β : ZMod p,
      T (hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i0 j) =
        α • hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i0 j →
      T (hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i0 k) =
        β • hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i0 k →
      α = β := by
    intro j k hj hk hjk β γ hβ hγ
    obtain ⟨ℓ, hℓi, hℓj, hℓk⟩ := hdRo7A3ReduceMAux_exists_fourth hm4 i0 j k
    obtain ⟨lam, hlam⟩ := heig k j (Ne.symm hjk)
    set xj : ↥((a3Aug p m).map θ) :=
      hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i0 j with hxj
    set xk : ↥((a3Aug p m).map θ) :=
      hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i0 k with hxk
    have hx : xj - xk = hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) k j := by
      apply Subtype.ext
      change θ (Pi.single i0 1 - Pi.single j 1) - θ (Pi.single i0 1 - Pi.single k 1) =
        θ (Pi.single k 1 - Pi.single j 1)
      rw [← map_sub]
      congr 1
      funext q
      simp only [Pi.sub_apply]
      ring
    have hTeq : T (xj - xk) = β • xj - γ • xk := by rw [map_sub, hβ, hγ]
    have hTeq2 : T (xj - xk) = lam • (xj - xk) := by rw [hx, hlam]
    have h4' : β • xj - γ • xk = lam • xj - lam • xk := by
      rw [← hTeq, hTeq2, smul_sub]
    have h5 : (β - lam) • xj + (lam - γ) • xk = 0 := by
      have h6 : (β - lam) • xj + (lam - γ) • xk =
          (β • xj - γ • xk) - (lam • xj - lam • xk) := by
        rw [sub_smul, sub_smul]
        abel
      rw [h6, h4', sub_self]
    have hji : i0 ≠ j := Ne.symm hj
    have hki : i0 ≠ k := Ne.symm hk
    obtain ⟨h1, h2⟩ :=
      hdRo7A3ReduceMAux_root_indep hD hℓi hℓj hℓk hji hki hjk h5
    rw [sub_eq_zero] at h1 h2
    rw [h1, h2]
  have hαj : ∀ (j : Fin m) (hj : j ≠ i0),
      T (hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i0 j) =
        α • hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i0 j := by
    intro j hj
    rcases eq_or_ne j j0 with rfl | hne
    · exact hα
    · obtain ⟨β, hβ⟩ := heig i0 j (Ne.symm hj)
      have hβα : β = α := hsame j j0 hj hj0 (fun h => hne h) β α hβ hα
      rw [hβα] at hβ
      exact hβ
  let W : Submodule (ZMod p) ↥((a3Aug p m).map θ) := LinearMap.ker (T - α • LinearMap.id)
  have hW : ∀ k l : Fin m,
      hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) k l ∈ W := by
    intro k l
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hroot_eq : hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) k l =
        hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) k i0 -
          hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) l i0 := by
      apply Subtype.ext
      change θ (Pi.single k 1 - Pi.single l 1) =
        θ (Pi.single k 1 - Pi.single i0 1) - θ (Pi.single l 1 - Pi.single i0 1)
      rw [← map_sub]
      congr 1
      funext q
      simp only [Pi.sub_apply]
      ring
    have hTi : ∀ (u : Fin m),
        T (hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) u i0) =
          α • hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) u i0 := by
      intro u
      by_cases hu : u = i0
      · subst hu
        rw [hdRo7A3ReduceMAux_root_self, map_zero, smul_zero]
      · have hneg : hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) u i0 =
            -hdRo7A3ReduceMAux_root (p := p) (m := m) (θ := θ) i0 u := by
          apply Subtype.ext
          change θ (Pi.single u 1 - Pi.single i0 1) =
            -θ (Pi.single i0 1 - Pi.single u 1)
          rw [← map_neg]
          congr 1
          funext q
          simp only [Pi.sub_apply, Pi.neg_apply]
          ring
        rw [hneg, map_neg, hαj u hu, smul_neg]
    rw [hroot_eq, map_sub, hTi k, hTi l, smul_sub, sub_self]
  have hWtop : W = ⊤ :=
    hdRo7A3ReduceMAux_roots_span (p := p) (m := m) (θ := θ) (i₀ := i0) W hW
  have hzero : T - α • LinearMap.id = 0 := (LinearMap.ker_eq_top).mp hWtop
  exact ⟨α, sub_eq_zero.mp hzero⟩

end Abs

theorem a3_reduceM_holds : A3ReduceMLeaf := by
  intro hSC hN p hpFact m V instAC instMod θ z H A hD hM h12 hroot
  set M : Submodule (ZMod p) V := (a3Aug p m).map θ with hM_def
  have hsup : M ⊔ Submodule.span (ZMod p) {z} = ⊤ :=
    hdRo7A3ReduceMAux_sup_span_z hD.hfr
  have hHK : H ≤ hdRo7SUReduceUAux_kerAug p M :=
    hdRo7A3ReduceMAux_H_le_kerAug hD hroot
  have hresinj : Function.Injective (hdRo7SUReduceUAux_res M H hHK) :=
    hdRo7A3ReduceMAux_res_injective M z hsup H A hHK hD.hHA hD.hNoT
  obtain ⟨S, hS, hScl, -⟩ := hD.hgen
  have h2 : (2 : ZMod p) ≠ 0 := by
    apply two_ne_zero_zmod
    have hp3 : p = 3 := hD.hp
    omega
  have hRgen : (hdRo7SUReduceUAux_res M H hHK).range =
      Subgroup.closure {r | r ∈ (hdRo7SUReduceUAux_res M H hHK).range ∧ GGLinRefl r} :=
    hdRo7A3ReduceMAux_range_eq_closure M hHK S hS hScl h2
  have habs : ZS.AbsIrred p (hdRo7SUReduceUAux_res M H hHK).range := by
    refine ⟨?_, ?_⟩
    · exact hdRo7A3ReduceMAux_irred hD hM hHK
    · intro T hT
      exact hdRo7A3ReduceMAux_commutant hD hHK hT
  have hcardR :
      Nat.card ↥(hdRo7SUReduceUAux_res M H hHK).range ≤
        6 ^ (m - 2) * (m - 2).factorial := by
    have hcard_eq : Nat.card ↥(hdRo7SUReduceUAux_res M H hHK).range = Nat.card H :=
      hdRo7A3ReduceMAux_card_range M hHK hresinj
    rw [hcard_eq]
    have : Finite V := a3_finite hD.hfr
    have : Fintype V := Fintype.ofFinite V
    have : Fintype (V → V) := Fintype.ofFinite (V → V)
    have : Fintype (V ≃ₗ[ZMod p] V) :=
      Fintype.ofInjective (fun e : V ≃ₗ[ZMod p] V => (e : V → V))
        (fun a b h => LinearEquiv.ext (fun v => congrArg (fun f : V → V => f v) h))
    have : Finite H := Subtype.finite
    have : Fintype H := Fintype.ofFinite H
    have : Finite M := Subtype.finite
    have : Fintype M := Fintype.ofFinite M
    have : Fintype (MulAction.orbit H z) := Fintype.ofFinite _
    have : Fintype (MulAction.stabilizer H z) := Fintype.ofFinite _
    have horbit_stab :
        Nat.card (MulAction.orbit H z) * Nat.card (MulAction.stabilizer H z) = Nat.card H := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group H z
    have hstab_card : Nat.card (MulAction.stabilizer H z) ≤ 2 * m.factorial := by
      rw [hdRo7A3ReduceMAux_stabilizer_card]
      exact hSC hN p m V θ z H A hD
    have horbit_card : Nat.card (MulAction.orbit H z) ≤ Nat.card M :=
      hdRo7A3ReduceMAux_orbit_card_le M z H hHK
    have hH_le : Nat.card H ≤ Nat.card M * (2 * m.factorial) := by
      rw [← horbit_stab]
      exact Nat.mul_le_mul horbit_card hstab_card
    have hM_card : Nat.card M = 3 ^ (m - 2) := by
      have hfin : Module.finrank (ZMod p) ((a3Aug p m).map θ) = m - 2 :=
        a3_finrank_M hD.hfr (by rw [hD.hp]; exact hD.h3) (by omega) hM
      have hcard : Nat.card ((a3Aug p m).map θ) = 3 ^ (m - 2) := by
        rw [← hfin]
        rw [← FiniteField.pow_finrank_eq_natCard (p := p)]
        congr 1
        exact hD.hp
      exact hcard
    calc Nat.card H ≤ Nat.card M * (2 * m.factorial) := hH_le
      _ = 3 ^ (m - 2) * (2 * m.factorial) := by rw [hM_card]
      _ ≤ 6 ^ (m - 2) * (m - 2).factorial := hdRo7A3ReduceMAux_factorial_bound h12
  have hlift : ZS.LinWeyl p (hdRo7SUReduceUAux_res M H hHK).range → ZS.LinWeyl p H :=
    hdRo7A3ReduceMAux_linWeyl_lift M hHK h2 hresinj
  exact ⟨M, inferInstance, inferInstance, (hdRo7SUReduceUAux_res M H hHK).range,
    a3_finrank_M hD.hfr (by rw [hD.hp]; exact hD.h3) (by omega) hM, habs, hRgen, hcardR, hlift⟩
end CFSG.StandardType.HdRo7A3
