module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Finset.Attr
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

@[expose] def commProdHom {X : Type*} [Group X] {U V : Subgroup X}
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) : ↥U × ↥V →* X where
  toFun p := (p.1 : X) * (p.2 : X)
  map_one' := by simp
  map_mul' p q := by
    have hc : (q.1 : X) * (p.2 : X) = (p.2 : X) * (q.1 : X) := hUV (q.1 : X) q.1.2 (p.2 : X) p.2.2
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    calc (p.1 : X) * (q.1 : X) * ((p.2 : X) * (q.2 : X))
        = (p.1 : X) * ((q.1 : X) * (p.2 : X)) * (q.2 : X) := by simp only [mul_assoc]
      _ = (p.1 : X) * ((p.2 : X) * (q.1 : X)) * (q.2 : X) := by rw [hc]
      _ = (p.1 : X) * (p.2 : X) * ((q.1 : X) * (q.2 : X)) := by simp only [mul_assoc]

theorem commProdHom_apply {X : Type*} [Group X] {U V : Subgroup X}
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (p : ↥U × ↥V) :
    commProdHom hUV p = (p.1 : X) * (p.2 : X) :=
  rfl

theorem commProdHom_range {X : Type*} [Group X] {U V : Subgroup X}
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) : (commProdHom hUV).range = U ⊔ V := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨p, rfl⟩ := MonoidHom.mem_range.1 hx
    rw [commProdHom_apply]
    exact Subgroup.mul_mem_sup p.1.2 p.2.2
  · refine sup_le ?_ ?_
    · intro u hu
      exact MonoidHom.mem_range.2 ⟨(⟨u, hu⟩, 1), by rw [commProdHom_apply]; simp⟩
    · intro v hv
      exact MonoidHom.mem_range.2 ⟨(1, ⟨v, hv⟩), by rw [commProdHom_apply]; simp⟩

theorem commProdHom_injective {X : Type*} [Group X] {U V : Subgroup X}
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hint : U ⊓ V = ⊥) :
    Function.Injective (commProdHom hUV) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨u, v⟩ h
  simp only [commProdHom_apply] at h
  have hu : (u : X) ∈ V := by
    rw [eq_inv_of_mul_eq_one_left h]
    exact V.inv_mem v.2
  have hu1 : (u : X) = 1 := by
    have hmem : (u : X) ∈ U ⊓ V := Subgroup.mem_inf.2 ⟨u.2, hu⟩
    rw [hint, Subgroup.mem_bot] at hmem
    exact hmem
  have hv1 : (v : X) = 1 := by
    rw [hu1, one_mul] at h
    exact h
  exact Prod.ext (Subtype.ext hu1) (Subtype.ext hv1)

theorem nonempty_mulEquiv_prod_of_commute {X : Type*} [Group X] {U V : Subgroup X}
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hint : U ⊓ V = ⊥) :
    Nonempty (↥(U ⊔ V) ≃* ↥U × ↥V) :=
  ⟨((MonoidHom.ofInjective (commProdHom_injective hUV hint)).trans
    (MulEquiv.subgroupCongr (commProdHom_range hUV))).symm⟩

theorem nonempty_mulEquiv_prod_of_commute_of_eq {X : Type*} [Group X] {U V W : Subgroup X}
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hint : U ⊓ V = ⊥) (hW : W = U ⊔ V) :
    Nonempty (↥W ≃* ↥U × ↥V) := by
  subst hW
  exact nonempty_mulEquiv_prod_of_commute hUV hint

theorem nonempty_mulEquiv_prod_of_commute_of_equiv {X : Type*} [Group X] {U V W : Subgroup X}
    {U' V' : Type*} [Group U'] [Group V']
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hint : U ⊓ V = ⊥) (hW : W = U ⊔ V)
    (eU : ↥U ≃* U') (eV : ↥V ≃* V') :
    Nonempty (↥W ≃* U' × V') := by
  obtain ⟨e⟩ := nonempty_mulEquiv_prod_of_commute_of_eq hUV hint hW
  exact ⟨e.trans (MulEquiv.prodCongr eU eV)⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
