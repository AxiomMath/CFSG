module

public import CFSG.RankThree.GF2n.Parrott.Section2Transfer
public import CFSG.RankThree.GF2n.Parrott.OThreeH
public import CFSG.RankThree.GF2n.Parrott.HeisenbergFour

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)
variable (h : Tim79a.ParrottHyp z)

theorem Wsub_eq_range :
    Wsub h (sigma1Nine (z := z) D) = (VComplementHom h (sigma1Nine (z := z) D)).range := by
  rw [show Wsub h (sigma1Nine (z := z) D) =
    commutatorV h (sigma1Nine (z := z) D) from rfl]
  exact commutatorV_eq_range (z := z) h (sigma1Nine_order (z := z) D)

theorem conjVLinearMap_mul (x y : ↥(H z)) :
    conjVLinearMap h (x * y) =
      conjVLinearMap h x * conjVLinearMap h y := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  ext v
  simp [conjVLinearMap_apply, map_mul, MulAut.mul_apply, Module.End.mul_apply]

theorem conjVLinearMap_one :
    conjVLinearMap h (1 : ↥(H z)) = 1 := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  ext v
  simp [conjVLinearMap_apply]

theorem conjVLinearMap_pow (x : ↥(H z)) (n : ℕ) :
    conjVLinearMap h x ^ n = conjVLinearMap h (x ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, conjVLinearMap_one]
  | succ n ih => rw [pow_succ, ih, pow_succ, conjVLinearMap_mul]

theorem conjVLinearMap_sigma1Nine_pow_three :
    conjVLinearMap h (sigma1Nine (z := z) D) ^ 3 = 1 := by
  rw [conjVLinearMap_pow, ← sigma1Nine_order (z := z) D, pow_orderOf_eq_one,
    conjVLinearMap_one]

@[simp] theorem mem_WsubModule_iff (v : Additive (QuotientV.V z)) :
    v ∈ WsubModule (z := z) (D := D) h ↔
      Additive.toMul v ∈ Wsub h (sigma1Nine (z := z) D) :=
  Iff.rfl

@[simp] theorem mem_FsubModule_iff (v : Additive (QuotientV.V z)) :
    v ∈ FsubModule (z := z) (D := D) h ↔
      Additive.toMul v ∈ Fsub (z := z) (sigma1Nine (z := z) D) :=
  Iff.rfl

theorem conjV_comm_of_mem_O3H (u : ↥(O3H D)) :
    conjV h (u : ↥(H z)) * conjV h (sigma1Nine (z := z) D) =
      conjV h (sigma1Nine (z := z) D) * conjV h (u : ↥(H z)) := by
  have hcommH : (u : ↥(H z)) * sigma1Nine (z := z) D =
      sigma1Nine (z := z) D * (u : ↥(H z)) :=
    Subgroup.mem_centralizer_singleton_iff.mp (O3H_le_K (z := z) D u.2)
  rw [← map_mul, ← map_mul, hcommH]

theorem conjVLinearMap_mem_WsubModule (u : ↥(O3H D)) :
    ∀ v ∈ WsubModule (z := z) (D := D) h,
      conjVLinearMap h (u : ↥(H z)) v ∈ WsubModule (z := z) (D := D) h := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  intro v hv
  have hcomm := conjV_comm_of_mem_O3H (z := z) (D := D) h u
  have hvW : Additive.toMul v ∈ Wsub h (sigma1Nine (z := z) D) := by
    rwa [mem_WsubModule_iff] at hv
  rw [mem_WsubModule_iff, conjVLinearMap_apply]
  simpa using conjV_mem_Wsub_of_commute (z := z) (D := D) h hcomm (Additive.toMul v) hvW

@[expose] noncomputable def Wact (u : ↥(O3H D)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    WsubModule (z := z) (D := D) h →ₗ[ZMod 2] WsubModule (z := z) (D := D) h := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  exact (conjVLinearMap h (u : ↥(H z))).restrict
    (conjVLinearMap_mem_WsubModule (z := z) (D := D) h u)

@[simp] theorem Wact_apply (u : ↥(O3H D))
    (v : WsubModule (z := z) (D := D) h) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    ((Wact (z := z) (D := D) h u v : WsubModule (z := z) (D := D) h) :
        Additive (QuotientV.V z)) =
      conjVLinearMap h (u : ↥(H z)) v := rfl

theorem Wact_one :
    Wact (z := z) (D := D) h (1 : ↥(O3H D)) = 1 := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [Wact_apply]
  simp [conjVLinearMap_one]

theorem Wact_mul (u v : ↥(O3H D)) :
    Wact (z := z) (D := D) h (u * v) =
      Wact (z := z) (D := D) h u * Wact (z := z) (D := D) h v := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  rw [Module.End.mul_apply, Wact_apply, Wact_apply]
  rw [show (↑(u * v) : ↥(H z)) = (u : ↥(H z)) * (v : ↥(H z)) from rfl,
    conjVLinearMap_mul]
  rfl

@[expose] noncomputable def rhoO3H :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    ↥(O3H D) →* (WsubModule (z := z) (D := D) h →ₗ[ZMod 2]
      WsubModule (z := z) (D := D) h) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  exact
    { toFun := Wact (z := z) (D := D) h
      map_one' := Wact_one (z := z) (D := D) h
      map_mul' := Wact_mul (z := z) (D := D) h }

@[simp] theorem rhoO3H_apply (u : ↥(O3H D)) :
    rhoO3H (z := z) (D := D) h u = Wact (z := z) (D := D) h u := rfl

theorem card_Wsub :
    Nat.card (Wsub h (sigma1Nine (z := z) D)) = 2 ^ 6 := by
  have hEq := Subgroup.card_ker_mul_card_range (VComplementHom h (sigma1Nine (z := z) D))
  rw [ker_VComplementHom_eq_autFixedSubgroup (z := z) h (sigma1Nine_order (z := z) D),
    card_fix h (sigma1Nine (z := z) D),
    fixDimV_sigma1Nine (z := z) (D := D) h, QuotientV.card_V h] at hEq
  have hrange : Nat.card (VComplementHom h (sigma1Nine (z := z) D)).range = 2 ^ 6 := by
    have hEq' : 4 * Nat.card (VComplementHom h (sigma1Nine (z := z) D)).range =
        4 * 2 ^ 6 := by
      have h := hEq
      norm_num at h ⊢
      exact h
    exact Nat.mul_left_cancel (by norm_num) hEq'
  rw [Wsub_eq_range (z := z) (D := D) h]
  exact hrange

theorem finrank_WsubModule :
    Module.finrank (ZMod 2) (WsubModule (z := z) (D := D) h) = 6 := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have hcard : Nat.card ↥(WsubModule (z := z) (D := D) h) = 2 ^ 6 := by
    rw [← card_Wsub (z := z) (D := D) h]
    refine Nat.card_congr ?_
    exact
      { toFun := fun v => ⟨Additive.toMul v.1, v.2⟩
        invFun := fun w => ⟨Additive.ofMul w.1, w.2⟩
        left_inv := by intro v; ext; simp
        right_inv := by intro w; ext; simp }
  have hdim := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := ↥(WsubModule (z := z) (D := D) h))
  rw [Nat.card_zmod, hcard] at hdim
  exact (Nat.pow_right_injective (by norm_num) hdim).symm

theorem WsubModule_eq_range_add_one :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    WsubModule (z := z) (D := D) h =
      LinearMap.range (conjVLinearMap h (sigma1Nine (z := z) D) + 1) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  ext v
  rw [mem_WsubModule_iff]
  constructor
  · intro hv
    rw [Wsub_eq_range (z := z) (D := D) h] at hv
    obtain ⟨u, hu⟩ := hv
    refine ⟨Additive.ofMul u, ?_⟩
    rw [LinearMap.add_apply, Module.End.one_apply, conjVLinearMap_apply, ← ofMul_mul]
    calc Additive.ofMul (((conjV h) (sigma1Nine (z := z) D)) u * u)
        = Additive.ofMul (u * ((conjV h) (sigma1Nine (z := z) D)) u) := by rw [mul_comm]
      _ = Additive.ofMul ((VComplementHom h (sigma1Nine (z := z) D)) u) := rfl
      _ = Additive.ofMul (Additive.toMul v) := by rw [hu]
      _ = v := rfl
  · rintro ⟨u, rfl⟩
    rw [Wsub_eq_range (z := z) (D := D) h]
    rw [LinearMap.add_apply, Module.End.one_apply, conjVLinearMap_apply]
    refine ⟨Additive.toMul u, ?_⟩
    change (VComplementHom h (sigma1Nine (z := z) D)) (Additive.toMul u) =
      ((conjV h) (sigma1Nine (z := z) D)) u * Additive.toMul u
    rw [VComplementHom_apply, mul_comm]
    rfl

theorem rhoO3H_omega_apply (u : Additive (QuotientV.V z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    conjVLinearMap h (sigma1Nine (z := z) D)
        (conjVLinearMap h (sigma1Nine (z := z) D)
          (conjVLinearMap h (sigma1Nine (z := z) D) u + u)) +
      conjVLinearMap h (sigma1Nine (z := z) D)
        (conjVLinearMap h (sigma1Nine (z := z) D) u + u) +
      (conjVLinearMap h (sigma1Nine (z := z) D) u + u) = 0 := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have h2 : ∀ x : Additive (QuotientV.V z), x + x = 0 := by
    intro x
    rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 by decide, zero_smul]
  have hC3 : conjVLinearMap h (sigma1Nine (z := z) D) ^ 3 = 1 :=
    conjVLinearMap_sigma1Nine_pow_three (z := z) (D := D) h
  have hC3u : conjVLinearMap h (sigma1Nine (z := z) D)
      (conjVLinearMap h (sigma1Nine (z := z) D)
        (conjVLinearMap h (sigma1Nine (z := z) D) u)) = u := by
    calc conjVLinearMap h (sigma1Nine (z := z) D)
          (conjVLinearMap h (sigma1Nine (z := z) D)
            (conjVLinearMap h (sigma1Nine (z := z) D) u))
        = (conjVLinearMap h (sigma1Nine (z := z) D) ^ 3) u := by
          rw [show conjVLinearMap h (sigma1Nine (z := z) D) ^ 3 =
            conjVLinearMap h (sigma1Nine (z := z) D) *
              conjVLinearMap h (sigma1Nine (z := z) D) *
              conjVLinearMap h (sigma1Nine (z := z) D) by noncomm_ring]
          rfl
      _ = u := by
          have h := LinearMap.congr_fun hC3 u
          rwa [Module.End.one_apply] at h
  have h2' : ∀ x y : Additive (QuotientV.V z), (x + y) + (y + x) = 0 := by
    intro x y
    rw [show (x + y) + (y + x) = (x + x) + (y + y) by abel]
    rw [h2 x, h2 y, zero_add]
  simp only [map_add]
  rw [hC3u]
  have h1 : (u + conjVLinearMap h (sigma1Nine (z := z) D)
        (conjVLinearMap h (sigma1Nine (z := z) D) u)) +
      (conjVLinearMap h (sigma1Nine (z := z) D)
        (conjVLinearMap h (sigma1Nine (z := z) D) u) +
        conjVLinearMap h (sigma1Nine (z := z) D) u) =
      u + conjVLinearMap h (sigma1Nine (z := z) D) u := by
    calc (u + conjVLinearMap h (sigma1Nine (z := z) D)
            (conjVLinearMap h (sigma1Nine (z := z) D) u)) +
          (conjVLinearMap h (sigma1Nine (z := z) D)
            (conjVLinearMap h (sigma1Nine (z := z) D) u) +
            conjVLinearMap h (sigma1Nine (z := z) D) u)
        = u + (conjVLinearMap h (sigma1Nine (z := z) D)
            (conjVLinearMap h (sigma1Nine (z := z) D) u) +
            (conjVLinearMap h (sigma1Nine (z := z) D)
              (conjVLinearMap h (sigma1Nine (z := z) D) u) +
              conjVLinearMap h (sigma1Nine (z := z) D) u)) := add_assoc _ _ _
      _ = u + ((conjVLinearMap h (sigma1Nine (z := z) D)
              (conjVLinearMap h (sigma1Nine (z := z) D) u) +
            conjVLinearMap h (sigma1Nine (z := z) D)
              (conjVLinearMap h (sigma1Nine (z := z) D) u)) +
            conjVLinearMap h (sigma1Nine (z := z) D) u) := by
          rw [add_assoc]
      _ = u + (0 + conjVLinearMap h (sigma1Nine (z := z) D) u) := by
          rw [h2]
      _ = u + conjVLinearMap h (sigma1Nine (z := z) D) u := by rw [zero_add]
  calc (u + conjVLinearMap h (sigma1Nine (z := z) D)
          (conjVLinearMap h (sigma1Nine (z := z) D) u)) +
        (conjVLinearMap h (sigma1Nine (z := z) D)
          (conjVLinearMap h (sigma1Nine (z := z) D) u) +
          conjVLinearMap h (sigma1Nine (z := z) D) u) +
        (conjVLinearMap h (sigma1Nine (z := z) D) u + u)
      = (u + conjVLinearMap h (sigma1Nine (z := z) D) u) +
          (conjVLinearMap h (sigma1Nine (z := z) D) u + u) := by rw [h1]
    _ = 0 := h2' u (conjVLinearMap h (sigma1Nine (z := z) D) u)

theorem rhoO3H_omega :
    let c : ↥(O3H D) := ⟨sigma1Nine (z := z) D, sigma1Nine_mem_O3H (z := z) D⟩
    rhoO3H (z := z) (D := D) h c * rhoO3H (z := z) (D := D) h c +
        rhoO3H (z := z) (D := D) h c + 1 = 0 := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  let c : ↥(O3H D) := ⟨sigma1Nine (z := z) D, sigma1Nine_mem_O3H (z := z) D⟩
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.mul_apply,
    Module.End.one_apply, rhoO3H_apply]
  change ((Wact (z := z) (D := D) h c
        (Wact (z := z) (D := D) h c w) : WsubModule (z := z) (D := D) h) :
      Additive (QuotientV.V z)) +
      ((Wact (z := z) (D := D) h c w : WsubModule (z := z) (D := D) h) :
        Additive (QuotientV.V z)) + (w : Additive (QuotientV.V z)) = 0
  rw [Wact_apply, Wact_apply]
  have hw : (w : Additive (QuotientV.V z)) ∈
      LinearMap.range (conjVLinearMap h (sigma1Nine (z := z) D) + 1) := by
    rw [← WsubModule_eq_range_add_one (z := z) (D := D) h]
    exact w.2
  obtain ⟨u, hu⟩ := hw
  rw [← hu]
  exact rhoO3H_omega_apply (z := z) (D := D) h u

theorem fixW_eq_map_ker (x : ↥(O3H D)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    fixW (z := z) (D := D) h (x : ↥(H z)) =
      (LinearMap.ker (rhoO3H (z := z) (D := D) h x - 1)).map
        (WsubModule (z := z) (D := D) h).subtype := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  ext v
  rw [show fixW (z := z) (D := D) h (x : ↥(H z)) =
    fixSubmodule h (x : ↥(H z)) ⊓ WsubModule (z := z) (D := D) h from rfl]
  rw [Submodule.mem_inf, Submodule.mem_map]
  constructor
  · rintro ⟨hvfix, hvW⟩
    refine ⟨⟨v, hvW⟩, ?_, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    apply Subtype.ext
    rw [rhoO3H_apply, Wact_apply, conjVLinearMap_apply]
    rw [mem_fixSubmodule_iff, mem_autFixedSubgroup] at hvfix
    rw [hvfix]
    rfl
  · rintro ⟨w, hw, hwv⟩
    have hfix : (w : Additive (QuotientV.V z)) ∈ fixSubmodule h (x : ↥(H z)) := by
      rw [mem_fixSubmodule_iff, mem_autFixedSubgroup]
      have h := hw
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
      have h' := congrArg Subtype.val h
      rw [rhoO3H_apply, Wact_apply, conjVLinearMap_apply] at h'
      exact congrArg Additive.toMul h'
    rw [← hwv]
    exact ⟨hfix, w.2⟩

theorem finrank_fixW_eq_two (x : ↥(O3H D))
    (hx : x ∉ Subgroup.zpowers
      (⟨sigma1Nine (z := z) D, sigma1Nine_mem_O3H (z := z) D⟩ : ↥(O3H D))) :
    Module.finrank (ZMod 2) (fixW (z := z) (D := D) h (x : ↥(H z))) = 2 := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  let c : ↥(O3H D) := ⟨sigma1Nine (z := z) D, sigma1Nine_mem_O3H (z := z) D⟩
  have hker := finrank_ker_heisenbergFour (ρ := rhoO3H (z := z) (D := D) h)
    (c := c) (card_O3H (z := z) h D) (isHeisenberg_O3H (z := z) h D).1
    (center_O3H (z := z) h D) (rhoO3H_omega (z := z) (D := D) h)
    (finrank_WsubModule (z := z) (D := D) h) hx
  rw [fixW_eq_map_ker (z := z) (D := D) h x, Submodule.finrank_map_subtype_eq]
  exact hker

end CFSG.RankThree.GF2n.Parrott

