module

public import Certificates.Data.ParrottSpin
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Parrott

private lemma V_add_self (v : V) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private lemma q_zero : q (0 : V) = 0 := by
  unfold q
  simp only [Pi.zero_apply, mul_zero, ite_self, Finset.sum_const_zero]

private lemma kappa_one {G : Type*} [Group G] {J : Subgroup G} {κ : G → V}
    (hadd : ∀ j ∈ J, ∀ k ∈ J, κ (j * k) = κ j + κ k) : κ 1 = 0 := by
  have h := hadd 1 (one_mem J) 1 (one_mem J)
  rw [mul_one] at h
  have h' : κ 1 + κ 1 = κ 1 + 0 := by simpa using h.symm
  exact add_left_cancel h'

private lemma kappa_inv {G : Type*} [Group G] {J : Subgroup G} {κ : G → V}
    (hadd : ∀ j ∈ J, ∀ k ∈ J, κ (j * k) = κ j + κ k) {j : G} (hj : j ∈ J) :
    κ j⁻¹ = κ j := by
  have h1 : κ 1 = 0 := kappa_one hadd
  have h2 := hadd j hj j⁻¹ (J.inv_mem hj)
  rw [mul_inv_cancel, h1] at h2
  have h3 : κ j + κ j = 0 := V_add_self (κ j)
  exact add_left_cancel (h2.symm.trans h3.symm)

private lemma kappa_z {G : Type*} [Group G] {J : Subgroup G} {z : G} {κ : G → V}
    (hzJ : z ∈ J) (hker : ∀ j ∈ J, κ j = 0 ↔ (j = 1 ∨ j = z)) : κ z = 0 :=
  (hker z hzJ).mpr (Or.inr rfl)

private lemma z_sq {G : Type*} [Group G] {J : Subgroup G} {z : G} {κ : G → V}
    (hzJ : z ∈ J) (hsq : ∀ j ∈ J, j * j = if q (κ j) = 0 then 1 else z)
    (hκz : κ z = 0) : z * z = 1 := by
  have h := hsq z hzJ
  have hq : q (κ z) = 0 := by rw [hκz, q_zero]
  rw [if_pos hq] at h
  exact h

private lemma b_comm (v w : V) : b v w = b w v := by
  unfold b
  rw [add_comm w v]
  calc q (v + w) + q v + q w = q (v + w) + (q v + q w) := add_assoc _ _ _
    _ = q (v + w) + (q w + q v) := by rw [add_comm (q v) (q w)]
    _ = q (v + w) + q w + q v := (add_assoc _ _ _).symm

private lemma kappa_commutator {G : Type*} [Group G] {J : Subgroup G} {a : G} {κ : G → V}
    {σ : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hadd : ∀ j ∈ J, ∀ k ∈ J, κ (j * k) = κ j + κ k)
    (haJ : ∀ j ∈ J, a * j * a⁻¹ ∈ J)
    (haκ : ∀ j ∈ J, κ (a * j * a⁻¹) = σ *ᵥ κ j) {j : G} (hj : j ∈ J) :
    κ (a * j * a⁻¹ * j⁻¹) = σ *ᵥ κ j + κ j := by
  have hmem : a * j * a⁻¹ ∈ J := haJ j hj
  have h := hadd (a * j * a⁻¹) hmem j⁻¹ (J.inv_mem hj)
  rw [haκ j hj, kappa_inv hadd hj] at h
  exact h

private lemma eq_or_eq_mul_z_of_kappa_eq {G : Type*} [Group G] {J : Subgroup G} {z : G}
    {κ : G → V}
    (hadd : ∀ j ∈ J, ∀ k ∈ J, κ (j * k) = κ j + κ k)
    (hker : ∀ j ∈ J, κ j = 0 ↔ (j = 1 ∨ j = z))
    {j k : G} (hj : j ∈ J) (hk : k ∈ J) (hκ : κ j = κ k) :
    k = j ∨ k = j * z := by
  have hmem : j⁻¹ * k ∈ J := J.mul_mem (J.inv_mem hj) hk
  have hκ0 : κ (j⁻¹ * k) = 0 := by
    rw [hadd j⁻¹ (J.inv_mem hj) k hk, kappa_inv hadd hj, hκ]
    exact V_add_self (κ k)
  rcases (hker (j⁻¹ * k) hmem).mp hκ0 with h | h
  · left
    have := congrArg (fun t => j * t) h
    simpa using this
  · right
    have := congrArg (fun t => j * t) h
    simpa [mul_assoc] using this

private lemma conj_commutator_commute {G : Type*} [Group G] {J : Subgroup G} {z a : G}
    {κ : G → V} {σ : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (ha2 : a * a = 1) (hadd : ∀ j ∈ J, ∀ k ∈ J, κ (j * k) = κ j + κ k)
    (haJ : ∀ j ∈ J, a * j * a⁻¹ ∈ J)
    (haκ : ∀ j ∈ J, κ (a * j * a⁻¹) = σ *ᵥ κ j) (hσ2 : σ * σ = 1)
    (hF1 : ∀ w : V, σ *ᵥ w = w → q w = 0)
    (hsq : ∀ j ∈ J, j * j = if q (κ j) = 0 then 1 else z) {j : G} (hj : j ∈ J) :
    a * (a * j * a⁻¹ * j⁻¹) = (a * j * a⁻¹ * j⁻¹) * a := by
  let c := a * j * a⁻¹ * j⁻¹
  have hcJ : c ∈ J := by
    simpa [c] using J.mul_mem (haJ j hj) (J.inv_mem hj)
  have hcκ : κ c = σ *ᵥ κ j + κ j := by
    simpa [c] using kappa_commutator hadd haJ haκ hj
  have hfix : σ *ᵥ (κ c) = κ c := by
    rw [hcκ, Matrix.mulVec_add, Matrix.mulVec_mulVec, hσ2, Matrix.one_mulVec,
      add_comm]
  have hq : q (κ c) = 0 := hF1 (κ c) hfix
  have hcc : c * c = 1 := by
    have h := hsq c hcJ
    rw [if_pos hq] at h
    exact h
  have ha_inv : a⁻¹ = a := (eq_inv_of_mul_eq_one_left ha2).symm
  have hconj : a * c * a⁻¹ = c⁻¹ := by
    change a * (a * j * a⁻¹ * j⁻¹) * a⁻¹ = (a * j * a⁻¹ * j⁻¹)⁻¹
    rw [ha_inv]
    calc a * (a * j * a * j⁻¹) * a = (a * a) * j * a * j⁻¹ * a := by group
      _ = j * a * j⁻¹ * a := by rw [ha2, one_mul]
      _ = (a * j * a * j⁻¹)⁻¹ := by simp only [mul_inv_rev, ha_inv, inv_inv]; group
  have hconj' : a * c * a⁻¹ = c := by
    rw [hconj, inv_eq_of_mul_eq_one_right hcc]
  calc a * c = (a * c * a⁻¹) * a := by group
    _ = c * a := by rw [hconj']

private lemma commute_iff_aux {G : Type*} [Group G] {J : Subgroup G} {z a : G}
    {κ : G → V} {σ : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hza : z * a = a * z)
    (hadd : ∀ j ∈ J, ∀ k ∈ J, κ (j * k) = κ j + κ k)
    (hsurj : ∀ w : V, ∃ j ∈ J, κ j = w)
    (hker : ∀ j ∈ J, κ j = 0 ↔ (j = 1 ∨ j = z))
    (hsq : ∀ j ∈ J, j * j = if q (κ j) = 0 then 1 else z)
    (ha2 : a * a = 1) (haJ : ∀ j ∈ J, a * j * a⁻¹ ∈ J)
    (haκ : ∀ j ∈ J, κ (a * j * a⁻¹) = σ *ᵥ κ j) (hσ2 : σ * σ = 1)
    (hF1 : ∀ w : V, σ *ᵥ w = w → q w = 0)
    (hF2 : ∀ w : V, σ *ᵥ w = w → ∃ u : V, σ *ᵥ u + u = w) :
    ∀ j ∈ J, a * j = j * a ↔ σ *ᵥ κ j = κ j := by
  intro j hj
  constructor
  · intro h
    have hconj : a * j * a⁻¹ = j := by
      calc a * j * a⁻¹ = (j * a) * a⁻¹ := by rw [h]
        _ = j := by group
    rw [← haκ j hj, hconj]
  · intro hfix
    obtain ⟨u, hu⟩ := hF2 (κ j) hfix
    obtain ⟨k, hkJ, hκk⟩ := hsurj u
    have hcJ : a * k * a⁻¹ * k⁻¹ ∈ J :=
      J.mul_mem (haJ k hkJ) (J.inv_mem hkJ)
    have hcκ : κ (a * k * a⁻¹ * k⁻¹) = κ j := by
      rw [kappa_commutator hadd haJ haκ hkJ, hκk]
      exact hu
    have hcz : j = a * k * a⁻¹ * k⁻¹ ∨ j = a * k * a⁻¹ * k⁻¹ * z :=
      eq_or_eq_mul_z_of_kappa_eq (j := a * k * a⁻¹ * k⁻¹) (k := j) hadd hker hcJ hj hcκ
    have hc_comm : a * (a * k * a⁻¹ * k⁻¹) = (a * k * a⁻¹ * k⁻¹) * a :=
      conj_commutator_commute ha2 hadd haJ haκ hσ2 hF1 hsq hkJ
    rcases hcz with h | h
    · rw [h]
      exact hc_comm
    · rw [h]
      calc a * ((a * k * a⁻¹ * k⁻¹) * z)
          = (a * (a * k * a⁻¹ * k⁻¹)) * z := by group
        _ = ((a * k * a⁻¹ * k⁻¹) * a) * z := by rw [hc_comm]
        _ = (a * k * a⁻¹ * k⁻¹) * (a * z) := by group
        _ = (a * k * a⁻¹ * k⁻¹) * (z * a) := by rw [hza]
        _ = ((a * k * a⁻¹ * k⁻¹) * z) * a := by group

private lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  have hx0 : x.val ≠ 0 := by rwa [ZMod.val_ne_zero]
  have hxle : x.val ≤ 1 := by
    have h := ZMod.val_lt x
    simpa using h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hxle with h0 | h1
  · exact absurd h0 hx0
  · exact ZMod.val_injective 2 (by rw [h1, ZMod.val_one])

private lemma commutator_mul_z {G : Type*} [Group G] {a z j : G}
    (hza : z * a = a * z) (hz2 : z * z = 1) :
    a * (j * z) * a⁻¹ * (j * z)⁻¹ = a * j * a⁻¹ * j⁻¹ := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hza' : a⁻¹ * z = z * a⁻¹ := by
    calc a⁻¹ * z = a⁻¹ * z⁻¹ := by rw [hzi]
      _ = (z * a)⁻¹ := by rw [mul_inv_rev]
      _ = (a * z)⁻¹ := by rw [hza]
      _ = z⁻¹ * a⁻¹ := by rw [mul_inv_rev]
      _ = z * a⁻¹ := by rw [hzi]
  rw [mul_inv_rev, hzi]
  simp only [hza'.symm, mul_assoc]
  rw [← mul_assoc z z, hz2, one_mul]

private lemma commutator_commute_a {G : Type*} [Group G] {a r c : G}
    (hra : r * a = a * r) (hac : a * c = c * a) :
    a * (r * c * r⁻¹ * c⁻¹) = (r * c * r⁻¹ * c⁻¹) * a := by
  have har_inv : a * r⁻¹ = r⁻¹ * a := by
    calc a * r⁻¹ = r⁻¹ * (r * a) * r⁻¹ := by group
      _ = r⁻¹ * (a * r) * r⁻¹ := by rw [hra]
      _ = r⁻¹ * a := by group
  have hac_inv : a * c⁻¹ = c⁻¹ * a := by
    calc a * c⁻¹ = c⁻¹ * (c * a) * c⁻¹ := by group
      _ = c⁻¹ * (a * c) * c⁻¹ := by rw [hac]
      _ = c⁻¹ * a := by group
  have hrc : a * (r * c * r⁻¹) = (r * c * r⁻¹) * a := by
    calc a * (r * c * r⁻¹) = (a * r) * c * r⁻¹ := by group
      _ = (r * a) * c * r⁻¹ := by rw [hra.symm]
      _ = r * (a * c) * r⁻¹ := by group
      _ = r * (c * a) * r⁻¹ := by rw [hac]
      _ = r * c * a * r⁻¹ := by group
      _ = r * c * (a * r⁻¹) := by group
      _ = r * c * (r⁻¹ * a) := by rw [har_inv]
      _ = (r * c * r⁻¹) * a := by group
  calc a * (r * c * r⁻¹ * c⁻¹) = (a * (r * c * r⁻¹)) * c⁻¹ := by group
    _ = ((r * c * r⁻¹) * a) * c⁻¹ := by rw [hrc]
    _ = (r * c * r⁻¹) * (a * c⁻¹) := by group
    _ = (r * c * r⁻¹) * (c⁻¹ * a) := by rw [hac_inv]
    _ = (r * c * r⁻¹ * c⁻¹) * a := by group

private lemma exists_char_separating {G : Type*} [Group G] {C N : Subgroup G}
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hexp : ∀ x ∈ C, x * x = 1) {z : G} (hzC : z ∈ C) (hzN : z ∉ N) :
    ∃ χ : C →* Multiplicative (ZMod 2),
      (χ ⟨z, hzC⟩ = Multiplicative.ofAdd 1) ∧
      (∀ x : C, (x : G) ∈ N → χ x = 1) := by
  classical
  let _ : CommGroup C := CommGroup.mk fun x y => Subtype.ext (hcomm x x.2 y y.2)
  let A := Additive C
  let _ : Module (ZMod 2) A := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    calc x + x = Additive.ofMul x.toMul + Additive.ofMul x.toMul := by rw [ofMul_toMul]
      _ = Additive.ofMul (x.toMul * x.toMul) := (ofMul_mul _ _).symm
      _ = Additive.ofMul (1 : C) := by
        rw [show x.toMul * x.toMul = 1 from Subtype.ext (hexp x.toMul x.toMul.2)]
      _ = 0 := ofMul_one
  let S : Submodule (ZMod 2) A :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (N.subgroupOf C))
  let v : A := Additive.ofMul (⟨z, hzC⟩ : C)
  have hv : v ∉ S := by
    intro hvS
    have hmem : Additive.ofMul (⟨z, hzC⟩ : C) ∈
        Subgroup.toAddSubgroup (N.subgroupOf C) := by
      rw [AddSubgroup.mem_toZModSubmodule] at hvS
      exact hvS
    have hmem2 : (⟨z, hzC⟩ : C) ∈ N.subgroupOf C := hmem
    exact hzN (Subgroup.mem_subgroupOf.mp hmem2)
  obtain ⟨f, hfz, hfS⟩ := Submodule.exists_le_ker_of_notMem (K := ZMod 2) (V := A)
    (p := S) (v := v) hv
  refine ⟨MonoidHom.mk' (fun x : C => Multiplicative.ofAdd (f (Additive.ofMul x))) ?_, ?_, ?_⟩
  · intro x y
    rw [ofMul_mul, map_add, ofAdd_add]
  · have hf1 : f v = 1 := zmod2_eq_one_of_ne_zero hfz
    exact congrArg Multiplicative.ofAdd hf1
  · intro x hx
    have hxS : Additive.ofMul x ∈ S := by
      rw [AddSubgroup.mem_toZModSubmodule]
      exact Subgroup.mem_subgroupOf.mpr hx
    have hfx : f (Additive.ofMul x) = 0 := LinearMap.mem_ker.mp (hfS hxS)
    change Multiplicative.ofAdd (f (Additive.ofMul x)) = 1
    rw [hfx, ofAdd_zero]

private lemma toAdd_chi_if {G : Type*} [Group G] {C : Subgroup G} {z : G} (hzC : z ∈ C)
    (χ : C →* Multiplicative (ZMod 2)) (hχz : χ ⟨z, hzC⟩ = Multiplicative.ofAdd 1)
    (β : ZMod 2) :
    Multiplicative.toAdd (χ (if β = 0 then 1 else ⟨z, hzC⟩)) = β := by
  by_cases hβ : β = 0
  · rw [if_pos hβ, map_one, hβ, toAdd_one]
  · rw [if_neg hβ, hχz, zmod2_eq_one_of_ne_zero hβ, toAdd_ofAdd]

theorem spinCoord_mul_self_of_commute {G : Type*} [Group G] {J : Subgroup G} {z a : G}
    {κ : G → V} {σ : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hza : z * a = a * z)
    (hadd : ∀ j ∈ J, ∀ k ∈ J, κ (j * k) = κ j + κ k)
    (hsurj : ∀ w : V, ∃ j ∈ J, κ j = w)
    (hker : ∀ j ∈ J, κ j = 0 ↔ (j = 1 ∨ j = z))
    (hsq : ∀ j ∈ J, j * j = if q (κ j) = 0 then 1 else z)
    (ha2 : a * a = 1) (haJ : ∀ j ∈ J, a * j * a⁻¹ ∈ J)
    (haκ : ∀ j ∈ J, κ (a * j * a⁻¹) = σ *ᵥ κ j) (hσ2 : σ * σ = 1)
    (hF1 : ∀ w : V, σ *ᵥ w = w → q w = 0)
    (hF2 : ∀ w : V, σ *ᵥ w = w → ∃ u : V, σ *ᵥ u + u = w) :
    ∀ j ∈ J, a * j = j * a → j * j = 1 := by
  intro j hj h
  have hfix : σ *ᵥ κ j = κ j :=
    (commute_iff_aux hza hadd hsurj hker hsq ha2 haJ haκ hσ2 hF1 hF2 j hj).mp h
  have hq : q (κ j) = 0 := hF1 (κ j) hfix
  have hsqj := hsq j hj
  rw [if_pos hq] at hsqj
  exact hsqj

theorem spinCoord_commute_of_commute {G : Type*} [Group G] {J : Subgroup G} {z a : G}
    {κ : G → V} {σ : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hza : z * a = a * z)
    (hadd : ∀ j ∈ J, ∀ k ∈ J, κ (j * k) = κ j + κ k)
    (hsurj : ∀ w : V, ∃ j ∈ J, κ j = w)
    (hker : ∀ j ∈ J, κ j = 0 ↔ (j = 1 ∨ j = z))
    (hsq : ∀ j ∈ J, j * j = if q (κ j) = 0 then 1 else z)
    (hcomm : ∀ j ∈ J, ∀ k ∈ J, j * k * j⁻¹ * k⁻¹ = if b (κ j) (κ k) = 0 then 1 else z)
    (ha2 : a * a = 1) (haJ : ∀ j ∈ J, a * j * a⁻¹ ∈ J)
    (haκ : ∀ j ∈ J, κ (a * j * a⁻¹) = σ *ᵥ κ j) (hσ2 : σ * σ = 1)
    (hF1 : ∀ w : V, σ *ᵥ w = w → q w = 0)
    (hF2 : ∀ w : V, σ *ᵥ w = w → ∃ u : V, σ *ᵥ u + u = w) :
    ∀ j ∈ J, ∀ k ∈ J, a * j = j * a → a * k = k * a → j * k = k * j := by
  intro j hj k hk hja hka
  have hfixj : σ *ᵥ κ j = κ j :=
    (commute_iff_aux hza hadd hsurj hker hsq ha2 haJ haκ hσ2 hF1 hF2 j hj).mp hja
  have hfixk : σ *ᵥ κ k = κ k :=
    (commute_iff_aux hza hadd hsurj hker hsq ha2 haJ haκ hσ2 hF1 hF2 k hk).mp hka
  have hfixjk : σ *ᵥ (κ j + κ k) = κ j + κ k := by
    rw [Matrix.mulVec_add, hfixj, hfixk]
  have hqj : q (κ j) = 0 := hF1 (κ j) hfixj
  have hqk : q (κ k) = 0 := hF1 (κ k) hfixk
  have hqjk : q (κ j + κ k) = 0 := hF1 (κ j + κ k) hfixjk
  have hb : b (κ j) (κ k) = 0 := by
    unfold b
    rw [hqjk, hqj, hqk, zero_add, zero_add]
  have hc := hcomm j hj k hk
  rw [if_pos hb] at hc
  have hc' : (j * k) * (k * j)⁻¹ = 1 := by
    simpa [mul_inv_rev, mul_assoc] using hc
  exact mul_inv_eq_one.mp hc'

theorem spinCoord_two_classes {G : Type*} [Group G] {J : Subgroup G} {z a : G}
    {κ : G → V} {σ : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hzJ : z ∈ J) (hzc : ∀ j ∈ J, z * j = j * z) (hza : z * a = a * z)
    (hadd : ∀ j ∈ J, ∀ k ∈ J, κ (j * k) = κ j + κ k)
    (hsurj : ∀ w : V, ∃ j ∈ J, κ j = w)
    (hker : ∀ j ∈ J, κ j = 0 ↔ (j = 1 ∨ j = z))
    (hsq : ∀ j ∈ J, j * j = if q (κ j) = 0 then 1 else z)
    (ha2 : a * a = 1) (haJ : ∀ j ∈ J, a * j * a⁻¹ ∈ J)
    (haκ : ∀ j ∈ J, κ (a * j * a⁻¹) = σ *ᵥ κ j)
    (hF2 : ∀ w : V, σ *ᵥ w = w → ∃ u : V, σ *ᵥ u + u = w) :
    ∀ x : G, a⁻¹ * x ∈ J → x * x = 1 →
      ∃ k ∈ J, x = k * a * k⁻¹ ∨ x = k * (a * z) * k⁻¹ := by
  intro x hxJ hx2
  let m := a⁻¹ * x
  have hmJ : m ∈ J := hxJ
  have hx_eq : x = a * m := by
    change x = a * (a⁻¹ * x)
    group
  let j' := a * m * a⁻¹
  have hj'J : j' ∈ J := haJ m hmJ
  have hx_eq2 : x = j' * a := by
    rw [hx_eq]
    simp [j', mul_assoc]
  have hx_sq : (a * m) * (a * m) = 1 := by
    rw [← hx_eq]
    exact hx2
  have ha_inv : a⁻¹ = a := (eq_inv_of_mul_eq_one_left ha2).symm
  have hconj : a * m * a⁻¹ = m⁻¹ := by
    have h1 : (a * m * a) * m = 1 := by
      calc (a * m * a) * m = (a * m) * (a * m) := by group
        _ = 1 := hx_sq
    have h2 : a * m * a = m⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [ha_inv]
    exact h2
  have hj'_κ : κ j' = κ m := by
    change κ (a * m * a⁻¹) = κ m
    rw [hconj, kappa_inv hadd hmJ]
  have hσm : σ *ᵥ κ m = κ m := by
    have h := haκ m hmJ
    rw [hconj, kappa_inv hadd hmJ] at h
    exact h.symm
  have hj'_fix : σ *ᵥ κ j' = κ j' := by
    rw [hj'_κ]
    exact hσm
  obtain ⟨u, hu⟩ := hF2 (κ j') hj'_fix
  obtain ⟨k, hkJ, hκk⟩ := hsurj u
  let c' := k * a * k⁻¹ * a⁻¹
  have hc'J : c' ∈ J := by
    have h1 : a * k * a⁻¹ ∈ J := haJ k hkJ
    have h2 : k * (a * k * a⁻¹)⁻¹ ∈ J := J.mul_mem hkJ (J.inv_mem h1)
    simpa [c', mul_inv_rev, mul_assoc] using h2
  have hc'κ : κ c' = κ j' := by
    have hdJ : a * k * a⁻¹ * k⁻¹ ∈ J := J.mul_mem (haJ k hkJ) (J.inv_mem hkJ)
    have hdκ : κ (a * k * a⁻¹ * k⁻¹) = σ *ᵥ κ k + κ k :=
      kappa_commutator hadd haJ haκ hkJ
    have hinv : c' = (a * k * a⁻¹ * k⁻¹)⁻¹ := by
      change k * a * k⁻¹ * a⁻¹ = (a * k * a⁻¹ * k⁻¹)⁻¹
      group
    rw [hinv, kappa_inv hadd hdJ, hdκ, hκk]
    exact hu
  have hcase : j' = c' ∨ j' = c' * z :=
    eq_or_eq_mul_z_of_kappa_eq hadd hker hc'J hj'J hc'κ
  have hz2 : z * z = 1 := z_sq hzJ hsq (kappa_z hzJ hker)
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzc_inv : ∀ y ∈ J, z * y⁻¹ = y⁻¹ * z := by
    intro y hy
    have hzy : z * y = y * z := hzc y hy
    calc z * y⁻¹ = (y * z)⁻¹ := by rw [mul_inv_rev, hzi]
      _ = (z * y)⁻¹ := by rw [hzy]
      _ = y⁻¹ * z := by rw [mul_inv_rev, hzi]
  rcases hcase with h | h
  · refine ⟨k, hkJ, Or.inl ?_⟩
    calc x = j' * a := hx_eq2
      _ = c' * a := by rw [h]
      _ = k * a * k⁻¹ := by simp [c', mul_assoc]
  · refine ⟨k, hkJ, Or.inr ?_⟩
    calc x = j' * a := hx_eq2
      _ = (c' * z) * a := by rw [h]
      _ = c' * (z * a) := by group
      _ = c' * (a * z) := by rw [hza]
      _ = (k * a * k⁻¹ * a⁻¹) * (a * z) := rfl
      _ = k * a * k⁻¹ * z := by group
      _ = k * a * (k⁻¹ * z) := by group
      _ = k * a * (z * k⁻¹) := by rw [← hzc_inv k hkJ]
      _ = k * (a * z) * k⁻¹ := by group

theorem spinCoord_z_mem_closure {G : Type*} [Group G] {J : Subgroup G} {z a : G}
    {κ : G → V} {σ : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hzJ : z ∈ J) (hza : z * a = a * z)
    (hadd : ∀ j ∈ J, ∀ k ∈ J, κ (j * k) = κ j + κ k)
    (hsurj : ∀ w : V, ∃ j ∈ J, κ j = w)
    (hker : ∀ j ∈ J, κ j = 0 ↔ (j = 1 ∨ j = z))
    (hsq : ∀ j ∈ J, j * j = if q (κ j) = 0 then 1 else z)
    (hcomm : ∀ j ∈ J, ∀ k ∈ J, j * k * j⁻¹ * k⁻¹ = if b (κ j) (κ k) = 0 then 1 else z)
    (ha2 : a * a = 1) (haJ : ∀ j ∈ J, a * j * a⁻¹ ∈ J)
    (haκ : ∀ j ∈ J, κ (a * j * a⁻¹) = σ *ᵥ κ j) (hσ2 : σ * σ = 1)
    (hF1 : ∀ w : V, σ *ᵥ w = w → q w = 0)
    (hF2 : ∀ w : V, σ *ᵥ w = w → ∃ u : V, σ *ᵥ u + u = w)
    {r₁ r₂ : G} {M₁ M₂ : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hr₁a : r₁ * a = a * r₁) (hr₂a : r₂ * a = a * r₂)
    (hr₁J : ∀ j ∈ J, r₁ * j * r₁⁻¹ ∈ J) (hr₂J : ∀ j ∈ J, r₂ * j * r₂⁻¹ ∈ J)
    (hr₁κ : ∀ j ∈ J, κ (r₁ * j * r₁⁻¹) = M₁ *ᵥ κ j)
    (hr₂κ : ∀ j ∈ J, κ (r₂ * j * r₂⁻¹) = M₂ *ᵥ κ j)
    (hF3 : ¬ ∃ ψ : V → ZMod 2,
      (∀ v w, ψ (v + w) = ψ v + ψ w + b v ((σ + 1) *ᵥ w)) ∧
      (∀ v, ψ (M₁ *ᵥ v) = ψ v) ∧ (∀ v, ψ (M₂ *ᵥ v) = ψ v)) :
    z ∈ Subgroup.closure {x : G | ∃ c ∈ J, a * c = c * a ∧
      (x = r₁ * c * r₁⁻¹ * c⁻¹ ∨ x = r₂ * c * r₂⁻¹ * c⁻¹)} := by
  classical
  let C : Subgroup G := J ⊓ Subgroup.centralizer ({a} : Set G)
  let N : Subgroup G := Subgroup.closure {x : G | ∃ c ∈ J, a * c = c * a ∧
      (x = r₁ * c * r₁⁻¹ * c⁻¹ ∨ x = r₂ * c * r₂⁻¹ * c⁻¹)}
  have hmemC : ∀ x : G, x ∈ C ↔ x ∈ J ∧ a * x = x * a := by
    intro x
    rw [show C = J ⊓ Subgroup.centralizer ({a} : Set G) from rfl, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hxJ, hx⟩
      exact ⟨hxJ, by simpa using hx a (by simp)⟩
    · rintro ⟨hxJ, hx⟩
      exact ⟨hxJ, by intro y hy; rw [Set.mem_singleton_iff] at hy; subst y; exact hx⟩
  have hzC : z ∈ C := (hmemC z).mpr ⟨hzJ, hza.symm⟩
  have hNle : N ≤ C := by
    rw [Subgroup.closure_le]
    rintro x ⟨c, hcJ, hac, hx | hx⟩
    · rw [hx]
      exact (hmemC _).mpr ⟨J.mul_mem (hr₁J c hcJ) (J.inv_mem hcJ),
        commutator_commute_a hr₁a hac⟩
    · rw [hx]
      exact (hmemC _).mpr ⟨J.mul_mem (hr₂J c hcJ) (J.inv_mem hcJ),
        commutator_commute_a hr₂a hac⟩
  have hCcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
    intro x hx y hy
    have hx' := (hmemC x).mp hx
    have hy' := (hmemC y).mp hy
    exact spinCoord_commute_of_commute hza hadd hsurj hker hsq hcomm ha2 haJ haκ
      hσ2 hF1 hF2 x hx'.1 y hy'.1 hx'.2 hy'.2
  have hCexp : ∀ x ∈ C, x * x = 1 := by
    intro x hx
    have hx' := (hmemC x).mp hx
    exact spinCoord_mul_self_of_commute hza hadd hsurj hker hsq ha2 haJ
      haκ hσ2 hF1 hF2 x hx'.1 hx'.2
  by_contra hzN
  obtain ⟨χ, hχz, hχN⟩ := exists_char_separating hCcomm hCexp hzC hzN
  have hdC : ∀ j ∈ J, a * j * a⁻¹ * j⁻¹ ∈ C := by
    intro j hj
    exact (hmemC _).mpr ⟨J.mul_mem (haJ j hj) (J.inv_mem hj),
      conj_commutator_commute ha2 hadd haJ haκ hσ2 hF1 hsq hj⟩
  let jOf : V → G := fun w => Classical.choose (hsurj w)
  have hjOf_mem : ∀ w : V, jOf w ∈ J := fun w => (Classical.choose_spec (hsurj w)).1
  have hκjOf : ∀ w : V, κ (jOf w) = w := fun w => (Classical.choose_spec (hsurj w)).2
  let ψ : V → ZMod 2 := fun w =>
    Multiplicative.toAdd (χ ⟨a * jOf w * a⁻¹ * (jOf w)⁻¹, hdC (jOf w) (hjOf_mem w)⟩)
  have hz2 : z * z = 1 := z_sq hzJ hsq (kappa_z hzJ hker)
  have hψκ : ∀ (j : G) (hj : j ∈ J), ψ (κ j) =
      Multiplicative.toAdd (χ ⟨a * j * a⁻¹ * j⁻¹, hdC j hj⟩) := by
    intro j hj
    let j0 := jOf (κ j)
    have hκj0 : κ j0 = κ j := hκjOf (κ j)
    have hcase : j = j0 ∨ j = j0 * z :=
      eq_or_eq_mul_z_of_kappa_eq hadd hker (hjOf_mem (κ j)) hj hκj0
    dsimp only [ψ]
    change Multiplicative.toAdd
        (χ ⟨a * j0 * a⁻¹ * j0⁻¹, hdC j0 (hjOf_mem (κ j))⟩) =
      Multiplicative.toAdd (χ ⟨a * j * a⁻¹ * j⁻¹, hdC j hj⟩)
    rcases hcase with h | h
    · have hx : (⟨a * j0 * a⁻¹ * j0⁻¹, hdC j0 (hjOf_mem (κ j))⟩ : C) =
          ⟨a * j * a⁻¹ * j⁻¹, hdC j hj⟩ := by
        apply Subtype.ext
        change a * j0 * a⁻¹ * j0⁻¹ = a * j * a⁻¹ * j⁻¹
        rw [h]
      rw [hx]
    · have hd : a * j * a⁻¹ * j⁻¹ = a * j0 * a⁻¹ * j0⁻¹ := by
        rw [h]
        exact commutator_mul_z (j := j0) hza hz2
      have hx : (⟨a * j0 * a⁻¹ * j0⁻¹, hdC j0 (hjOf_mem (κ j))⟩ : C) =
          ⟨a * j * a⁻¹ * j⁻¹, hdC j hj⟩ := Subtype.ext hd.symm
      rw [hx]
  have hψadd : ∀ v w : V, ψ (v + w) = ψ v + ψ w + b v ((σ + 1) *ᵥ w) := by
    intro v w
    obtain ⟨j₁, hj₁J, hκ₁⟩ := hsurj v
    obtain ⟨j₂, hj₂J, hκ₂⟩ := hsurj w
    have hsum : κ (j₁ * j₂) = v + w := by rw [hadd j₁ hj₁J j₂ hj₂J, hκ₁, hκ₂]
    rw [← hsum, ← hκ₁, ← hκ₂, hψκ (j₁ * j₂) (J.mul_mem hj₁J hj₂J), hψκ j₁ hj₁J,
      hψκ j₂ hj₂J]
    let d1 : C := ⟨a * j₁ * a⁻¹ * j₁⁻¹, hdC j₁ hj₁J⟩
    let d2 : C := ⟨a * j₂ * a⁻¹ * j₂⁻¹, hdC j₂ hj₂J⟩
    let d2G : G := a * j₂ * a⁻¹ * j₂⁻¹
    have hd2J : d2G ∈ J := J.mul_mem (haJ j₂ hj₂J) (J.inv_mem hj₂J)
    let g0 : G := d2G⁻¹ * j₁ * d2G * j₁⁻¹
    have hg0J : g0 ∈ J :=
      J.mul_mem (J.mul_mem (J.mul_mem (J.inv_mem hd2J) hj₁J) hd2J) (J.inv_mem hj₁J)
    have hd2κ : κ d2G = σ *ᵥ κ j₂ + κ j₂ := kappa_commutator hadd haJ haκ hj₂J
    have hb : b (κ (d2G⁻¹)) (κ j₁) = b (κ j₁) ((σ + 1) *ᵥ κ j₂) := by
      have h1 : κ (d2G⁻¹) = σ *ᵥ κ j₂ + κ j₂ := by
        rw [kappa_inv hadd hd2J, hd2κ]
      have h2 : (σ + 1) *ᵥ κ j₂ = σ *ᵥ κ j₂ + κ j₂ := by
        rw [Matrix.add_mulVec, Matrix.one_mulVec]
      rw [h1, h2, b_comm]
    have hg0def : g0 = if b (κ j₁) ((σ + 1) *ᵥ κ j₂) = 0 then 1 else z := by
      have h := hcomm (d2G⁻¹) (J.inv_mem hd2J) j₁ hj₁J
      simpa [g0, hb, inv_inv] using h
    have hg0C : g0 ∈ C := by
      by_cases hb0 : b (κ j₁) ((σ + 1) *ᵥ κ j₂) = 0
      · rw [hg0def, if_pos hb0]
        exact C.one_mem
      · rw [hg0def, if_neg hb0]
        exact hzC
    let zC : C := ⟨z, hzC⟩
    let gC : C := if b (κ j₁) ((σ + 1) *ᵥ κ j₂) = 0 then 1 else zC
    have hgval : Multiplicative.toAdd (χ gC) = b (κ j₁) ((σ + 1) *ᵥ κ j₂) := by
      dsimp [gC]
      exact toAdd_chi_if hzC χ hχz _
    have hgC_eq : gC = ⟨g0, hg0C⟩ := by
      apply Subtype.ext
      dsimp [gC, zC]
      rw [hg0def]
      split <;> rfl
    have hd12 : (⟨a * (j₁ * j₂) * a⁻¹ * (j₁ * j₂)⁻¹,
        hdC (j₁ * j₂) (J.mul_mem hj₁J hj₂J)⟩ : C) = d1 * d2 * gC := by
      rw [hgC_eq]
      apply Subtype.ext
      dsimp [d1, d2, g0, d2G]
      group
    have hLHS : Multiplicative.toAdd (χ (d1 * d2 * gC)) =
        Multiplicative.toAdd (χ d1) + Multiplicative.toAdd (χ d2) +
          Multiplicative.toAdd (χ gC) := by
      calc Multiplicative.toAdd (χ (d1 * d2 * gC))
          = Multiplicative.toAdd (χ (d1 * d2) * χ gC) := by rw [map_mul]
        _ = Multiplicative.toAdd (χ (d1 * d2)) + Multiplicative.toAdd (χ gC) := by
            rw [toAdd_mul]
        _ = (Multiplicative.toAdd (χ d1) + Multiplicative.toAdd (χ d2)) +
              Multiplicative.toAdd (χ gC) := by rw [map_mul, toAdd_mul]
        _ = Multiplicative.toAdd (χ d1) + Multiplicative.toAdd (χ d2) +
              Multiplicative.toAdd (χ gC) := by rw [add_assoc]
    rw [hd12, hLHS, hgval]
  have hψM : ∀ (r : G) (M : Matrix (Fin 8) (Fin 8) (ZMod 2)),
      r * a = a * r → (∀ j ∈ J, r * j * r⁻¹ ∈ J) →
      (∀ j ∈ J, κ (r * j * r⁻¹) = M *ᵥ κ j) →
      (∀ c ∈ J, a * c = c * a → r * c * r⁻¹ * c⁻¹ ∈ N) →
      ∀ v : V, ψ (M *ᵥ v) = ψ v := by
    intro r M hra hrJ hrκ hgenN v
    obtain ⟨j, hjJ, hκj⟩ := hsurj v
    rw [← hκj, ← hrκ j hjJ, hψκ (r * j * r⁻¹) (hrJ j hjJ), hψκ j hjJ]
    let d : G := a * j * a⁻¹ * j⁻¹
    have hdJ : d ∈ J := by
      dsimp [d]
      exact J.mul_mem (haJ j hjJ) (J.inv_mem hjJ)
    have hdCj : d ∈ C := by
      dsimp [d]
      exact hdC j hjJ
    have hdcomm : a * d = d * a := ((hmemC d).mp hdCj).2
    have hgN : r * d * r⁻¹ * d⁻¹ ∈ N := hgenN d hdJ hdcomm
    have hgC : r * d * r⁻¹ * d⁻¹ ∈ C := hNle hgN
    have hχg : χ ⟨r * d * r⁻¹ * d⁻¹, hgC⟩ = 1 := hχN _ hgN
    have har : a * r = r * a := hra.symm
    have har_inv : a⁻¹ * r⁻¹ = r⁻¹ * a⁻¹ := by
      simpa [mul_inv_rev] using congrArg Inv.inv hra
    have hconv : (⟨a * (r * j * r⁻¹) * a⁻¹ * (r * j * r⁻¹)⁻¹,
        hdC (r * j * r⁻¹) (hrJ j hjJ)⟩ : C) =
        ⟨r * d * r⁻¹ * d⁻¹, hgC⟩ * ⟨d, hdCj⟩ := by
      apply Subtype.ext
      dsimp [d]
      calc a * (r * j * r⁻¹) * a⁻¹ * (r * j * r⁻¹)⁻¹
          = (a * r) * j * (r⁻¹ * a⁻¹) * (r * j⁻¹ * r⁻¹) := by group
        _ = (r * a) * j * (a⁻¹ * r⁻¹) * (r * j⁻¹ * r⁻¹) := by rw [har, har_inv]
        _ = r * (a * j * a⁻¹ * j⁻¹) * r⁻¹ := by group
        _ = (r * (a * j * a⁻¹ * j⁻¹) * r⁻¹ * (a * j * a⁻¹ * j⁻¹)⁻¹) *
            (a * j * a⁻¹ * j⁻¹) := by group
    rw [hconv, map_mul, toAdd_mul, hχg, toAdd_one, zero_add]
  have hgenN₁ : ∀ c ∈ J, a * c = c * a → r₁ * c * r₁⁻¹ * c⁻¹ ∈ N := by
    intro c hcJ hac
    exact Subgroup.subset_closure ⟨c, hcJ, hac, Or.inl rfl⟩
  have hgenN₂ : ∀ c ∈ J, a * c = c * a → r₂ * c * r₂⁻¹ * c⁻¹ ∈ N := by
    intro c hcJ hac
    exact Subgroup.subset_closure ⟨c, hcJ, hac, Or.inr rfl⟩
  exact hF3 ⟨ψ, hψadd, hψM r₁ M₁ hr₁a hr₁J hr₁κ hgenN₁,
    hψM r₂ M₂ hr₂a hr₂J hr₂κ hgenN₂⟩

end CFSG.RankThree.GF2n.Parrott
