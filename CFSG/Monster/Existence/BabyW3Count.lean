module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.Monster.Existence

theorem ncard_conj_mul_natCard_inf_centralizer {G : Type*} [Group G] (H : Subgroup G) (t : G) :
    {u : G | ∃ g ∈ H, u = g⁻¹ * t * g}.ncard * Nat.card ↥(H ⊓ Subgroup.centralizer {t}) =
      Nat.card H := by
  let _ : MulAction H G := MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp H.subtype)
  have hsmul : ∀ h : H, h • t = (h : G) * t * (h : G)⁻¹ := fun h => ConjAct.toConjAct_smul _ _
  have hclass : {u : G | ∃ g ∈ H, u = g⁻¹ * t * g} = MulAction.orbit H t := by
    ext u
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g⁻¹, H.inv_mem hg⟩, ?_⟩
      show (⟨g⁻¹, H.inv_mem hg⟩ : H) • t = _
      rw [hsmul]
      simp
    · rintro ⟨h, rfl⟩
      refine ⟨(h : G)⁻¹, H.inv_mem h.2, ?_⟩
      show h • t = _
      rw [hsmul, inv_inv]
  have h1 : (MulAction.stabilizer H t).index = Nat.card (MulAction.orbit H t) :=
    MulAction.index_stabilizer H t
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer H t)
  have h3 : Nat.card (MulAction.stabilizer H t) = Nat.card ↥(H ⊓ Subgroup.centralizer {t}) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.1.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have hx := MulAction.mem_stabilizer_iff.1 x.2
      rw [hsmul] at hx
      calc (x.1 : G) * t = (x.1 : G) * t * (x.1 : G)⁻¹ * (x.1 : G) := by group
        _ = t * (x.1 : G) := by rw [hx]
    · rw [MulAction.mem_stabilizer_iff, hsmul]
      have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2
      calc (y.1 : G) * t * (y.1 : G)⁻¹ = t * (y.1 : G) * (y.1 : G)⁻¹ := by rw [hc]
        _ = t := by group
  rw [hclass, ← h3, ← Nat.card_coe_set_eq, ← h1, mul_comm]
  exact h2

theorem natCard_centralizer_eq_image {G H : Type*} [Group G] [Group H] (e : G ≃* H) (a : G) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) =
      Nat.card (Subgroup.centralizer ({e a} : Set H)) :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    simp only [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      show e x * e a = e a * e x
      rw [← map_mul, ← map_mul, h]
    · intro h
      apply e.injective
      rw [map_mul, map_mul]
      exact h)

theorem val_mapEquiv_submonoidCongr {M : Type*} [Monoid M] {S T : Submonoid M} (h : S = T)
    (u : Sˣ) : (((Units.mapEquiv (MulEquiv.submonoidCongr h) u : Tˣ) : T) : M) = ((u : S) : M) := by
  subst h
  rfl

end CFSG.Monster.Existence
