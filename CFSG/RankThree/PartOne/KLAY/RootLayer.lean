module

public import CFSG.RankThree.PartOne.KLAY.Core

public section

namespace CFSG.RankThree.PartOne.KLAY

open CFSG CFSG.RankThree.PartOne.KFU CFSG.LieType.Chevalley

@[expose] def RootLayer (Γ : Type) [Group Γ] (p : ℕ) (u : Γ) (n : ℕ) : Prop :=
  ∃ R : Subgroup Γ, R ≤ Subgroup.centralizer ({u} : Set Γ) ∧
    (R.subgroupOf (Subgroup.centralizer ({u} : Set Γ))).Normal ∧ IsSimpleGroup ↥R ∧
    Group.IsPerfect ↥R ∧ (∃ x ∈ R, orderOf x = p) ∧ Nat.card ↥R = n ∧
    ∀ P : Subgroup Γ, P ≤ Subgroup.centralizer ({u} : Set Γ) → Group.IsPerfect ↥P → P ≤ R

theorem RootLayer.of_layerD {Γ : Type} [Group Γ] [Finite Γ] {p n : ℕ} (hp : p.Prime) {u : Γ}
    {R : Subgroup Γ} (hD : layerD u = R) (hs : IsSimpleGroup ↥R) (hn : Nat.card ↥R = n)
    (hpn : p ∣ n) : RootLayer Γ p u n := by
  classical
  set C : Subgroup Γ := Subgroup.centralizer ({u} : Set Γ) with hC
  have hperf : Group.IsPerfect ↥R := hD ▸ isPerfect_inSubgroup_perfectResidual _
  have hRC : R ≤ C := by
    rw [← hD]
    exact Subgroup.map_subtype_le _
  refine ⟨R, hRC, ?_, hs, hperf, ?_, hn, ?_⟩
  · have h1 : R.subgroupOf C = perfectResidual ↥C := by
      rw [← hD]
      change ((perfectResidual ↥C).map C.subtype).subgroupOf C = _
      exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
    rw [h1]
    have := (perfect_residual_characterization (G := ↥C)).2.1
    infer_instance
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) p (by rw [hn]; exact hpn)
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  · intro P hPC hP
    have hP' : Group.IsPerfect ↥(P.subgroupOf C) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPC).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hPC).symm.surjective
    have h2 := (perfect_residual_transport (MonoidHom.id ↥C)).2.2 _ hP'
    rw [← hD]
    calc P = (P.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hPC).symm
      _ ≤ (perfectResidual ↥C).map C.subtype := Subgroup.map_mono h2

theorem RootLayer.of_SL2Torus {M : Type} [Group M] [Finite M] {k : Type} [Field k] [Finite k]
    [CharP k 2] {p n : ℕ} {φ : SL2 k →* M} {T₀ : Subgroup M} (h : SL2Torus p φ T₀)
    (hp : p.Prime) (h4 : 4 ≤ Nat.card k) (hpq : p ∣ Nat.card k - 1) {u : M}
    (hD : layerD u = φ.range) (hn : n = Nat.card k * (Nat.card k ^ 2 - 1)) :
    RootLayer M p u n := by
  refine RootLayer.of_layerD hp hD (h.isSimpleGroup_range h4) (h.card_range.trans hn.symm) ?_
  rw [hn]
  have h1 : Nat.card k - 1 ∣ Nat.card k ^ 2 - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow (Nat.card k) 1 2
  exact Dvd.dvd.mul_left (hpq.trans h1) _

end CFSG.RankThree.PartOne.KLAY
