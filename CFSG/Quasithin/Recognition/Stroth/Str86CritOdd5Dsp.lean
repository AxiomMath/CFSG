module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Stroth

variable {G : Type} [Group G] [Finite G]

private noncomputable def dspConj (U : Subgroup G) (a : G)
    (ha : a ∈ Subgroup.normalizer (U : Set G)) : U →* U :=
  ((Subgroup.normalizerMonoidHom U) ⟨a, ha⟩).toMonoidHom

private theorem dspConj_coe (U : Subgroup G) (a : G)
    (ha : a ∈ Subgroup.normalizer (U : Set G)) (u : U) :
    ((dspConj U a ha u : U) : G) = a * (u : G) * a⁻¹ := by
  simpa [dspConj] using Subgroup.normalizerMonoidHom_apply_apply_coe U ⟨a, ha⟩ u

private noncomputable def dspPhi (U : Subgroup G) (a : G)
    (hU : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u)
    (ha : a ∈ Subgroup.normalizer (U : Set G)) : U →* U where
  toFun u := u * (dspConj U a ha u)⁻¹
  map_one' := by
    show (1 : U) * (dspConj U a ha 1)⁻¹ = 1
    rw [map_one, inv_one, mul_one]
  map_mul' u v := by
    letI : IsMulCommutative U :=
      IsMulCommutative.mk ⟨fun x y => Subtype.ext (hU x.1 x.2 y.1 y.2)⟩
    letI : CommGroup U := IsMulCommutative.instCommGroup
    show u * v * (dspConj U a ha (u * v))⁻¹ =
      (u * (dspConj U a ha u)⁻¹) * (v * (dspConj U a ha v)⁻¹)
    rw [map_mul (dspConj U a ha) u v, mul_inv_rev]
    ac_rfl

private theorem dspPhi_ker (U : Subgroup G) (a : G)
    (hU : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u)
    (ha : a ∈ Subgroup.normalizer (U : Set G)) :
    (dspPhi U a hU ha).ker =
      (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)).subgroupOf U := by
  ext u
  have hcent : Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) =
      Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hcent,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : u * (dspConj U a ha u)⁻¹ = 1 := h
    have hu : u = dspConj U a ha u := mul_inv_eq_one.mp h'
    have hcoe : (u : G) = a * (u : G) * a⁻¹ := by
      simpa only [dspConj_coe] using congrArg (fun x : U => (x : G)) hu
    calc (u : G) * a = (a * (u : G) * a⁻¹) * a := congrArg (fun x => x * a) hcoe
      _ = a * (u : G) := by group
  · intro hua
    have hσ : dspConj U a ha u = u := by
      apply Subtype.ext
      rw [dspConj_coe]
      calc a * (u : G) * a⁻¹ = ((u : G) * a) * a⁻¹ := by rw [← hua]
        _ = (u : G) := by group
    show u * (dspConj U a ha u)⁻¹ = 1
    rw [hσ, mul_inv_cancel]

theorem relIndex_centralizer_le_mul_card {U U₀ Z : Subgroup G}
    (hU : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {a : G} (ha : a ∈ Subgroup.normalizer (U : Set G))
    (hU₀ : U₀ ≤ U) (hZ : ∀ u ∈ U₀, u * a * u⁻¹ * a⁻¹ ∈ Z) :
    (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)).relIndex U ≤
      U₀.relIndex U * Nat.card Z := by
  classical
  let φ := dspPhi U a hU ha
  let K := U₀.subgroupOf U
  let ψ : K →* U := φ.comp K.subtype
  have hker : φ.ker =
      (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)).subgroupOf U :=
    dspPhi_ker U a hU ha
  have hcardN : Nat.card ↥φ.ker * Nat.card ↥φ.range = Nat.card ↥U :=
    Subgroup.card_ker_mul_card_range φ
  have hcardU : K.index * Nat.card ↥K = Nat.card ↥U := Subgroup.index_mul_card K
  have hrange : ψ.range = K.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardK : Nat.card ↥ψ.ker * Nat.card ↥(K.map φ) = Nat.card ↥K := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rwa [hrange] at h
  have hmapleZ : K.map φ ≤ Z.subgroupOf U := by
    rintro y ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hcoe : ((φ x : U) : G) = (x : G) * a * (x : G)⁻¹ * a⁻¹ := by
      show (((x : U) * (dspConj U a ha x)⁻¹ : U) : G) = (x : G) * a * (x : G)⁻¹ * a⁻¹
      rw [Subgroup.coe_mul, Subgroup.coe_inv, dspConj_coe]
      group
    rw [hcoe]
    exact hZ (x : G) (Subgroup.mem_subgroupOf.mp hx)
  have hcardZ : Nat.card ↥(K.map φ) ≤ Nat.card Z := by
    have hZmap : Subgroup.map U.subtype (Z.subgroupOf U) ≤ Z := by
      rintro y ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hx
    calc Nat.card ↥(K.map φ) ≤ Nat.card ↥(Z.subgroupOf U) := Subgroup.card_le_of_le hmapleZ
      _ = Nat.card ↥(Subgroup.map U.subtype (Z.subgroupOf U)) :=
        (Subgroup.card_subtype U (Z.subgroupOf U)).symm
      _ ≤ Nat.card ↥Z := Subgroup.card_le_of_le hZmap
  have hmapker : Subgroup.map K.subtype ψ.ker ≤ φ.ker := by
    rintro y ⟨x, hx, rfl⟩
    change φ (K.subtype x) = 1
    change ψ x = 1 at hx
    exact hx
  have hcardKN_le : Nat.card ↥ψ.ker ≤ Nat.card ↥φ.ker := by
    calc Nat.card ↥ψ.ker = Nat.card ↥(Subgroup.map K.subtype ψ.ker) :=
        (Subgroup.card_subtype K ψ.ker).symm
      _ ≤ Nat.card ↥φ.ker := Subgroup.card_le_of_le hmapker
  have hposN : 0 < Nat.card ↥φ.ker := Nat.card_pos
  have hmul1 : Nat.card ↥φ.range * Nat.card ↥φ.ker = Nat.card ↥U := by
    rw [mul_comm]
    exact hcardN
  have hmul3 : Nat.card ↥K = Nat.card ↥(K.map φ) * Nat.card ↥ψ.ker := by
    rw [mul_comm]
    exact hcardK.symm
  have hmain : Nat.card ↥φ.range * Nat.card ↥φ.ker ≤
      K.index * Nat.card Z * Nat.card ↥φ.ker := by
    calc Nat.card ↥φ.range * Nat.card ↥φ.ker = Nat.card ↥U := hmul1
      _ = K.index * Nat.card ↥K := hcardU.symm
      _ = K.index * (Nat.card ↥(K.map φ) * Nat.card ↥ψ.ker) := by rw [hmul3]
      _ ≤ K.index * (Nat.card Z * Nat.card ↥φ.ker) := by
            exact Nat.mul_le_mul_left K.index (Nat.mul_le_mul hcardZ hcardKN_le)
      _ = K.index * Nat.card Z * Nat.card ↥φ.ker := by rw [mul_assoc]
  have hcancel : Nat.card ↥φ.range ≤ K.index * Nat.card Z :=
    Nat.le_of_mul_le_mul_right hmain hposN
  have hgoal : (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)).relIndex U =
      Nat.card ↥φ.range := by
    change ((Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)).subgroupOf U).index =
      Nat.card ↥φ.range
    rw [← hker, Subgroup.index_ker φ]
  rw [hgoal]
  exact hcancel

end CFSG.Quasithin.Stroth

end
