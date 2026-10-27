module

public import CFSG.Monster.B.TwoA.Amalgam.DiameterThreeCore
public import CFSG.Monster.B.TwoA.Amalgam.GlobalTypeCore
public import CFSG.Monster.B.E6.FieldInvF4
public import CFSG.Monster.B.GSide.RonanThreeStd

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open SimpleGraph CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

theorem b3tri_of
    (hloc : DistThreeLocalOrbits) :
    ∀ v x y : CVert, cgraph.dist v x = 3 → cgraph.dist v y = 3 → cgraph.Adj x y →
      ∃ h, cgraph.dist v h = 2 ∧ cgraph.Adj h x ∧ cgraph.Adj h y := by
  intro v x y hvx hvy hxy
  have hy : y ∈ cgraph.neighborSet x \ sphereFour v := ⟨hxy, fun h => by
    have h2 := h.1
    rw [hvy] at h2
    exact absurd h2 (by decide)⟩
  obtain ⟨h, hh, hyh⟩ := exists_adj_mem_X hloc hvx hy
  exact ⟨h, hh.2.1, cgraph.adj_symm hh.1, cgraph.adj_symm hyh⟩

@[expose] def DistThreeFieldCoords :
    Prop :=
  ∀ v u : CVert, cgraph.dist v u = 3 →
    ∃ (hc : clabelS v ∈ vStab u) (ρ : vStab u →* GStar) (iu : cgraph.neighborSet u ≃ rootClass),
      IsLocalLabel ρ iu ∧ ρ ⟨clabelS v, hc⟩ = betaStarElt ∧
      ∀ z : cgraph.neighborSet u, ((z : CVert) ∈ sphereFour v ↔ cvMul z (clabelS v) ≠ z)

theorem betaStarElt_inv :
    betaStarElt⁻¹ = betaStarElt := by
  rw [inv_eq_iff_mul_eq_one, ← sq, ← CFSG.Monster.B.E6.FieldInvF4.orderOf_betaStarElt,
    pow_orderOf_eq_one]

theorem inv_betaStarElt_mul_inl_mul
    (x : stdGroup) :
    (betaStarElt⁻¹ * SemidirectProduct.inl x * betaStarElt : GStar) =
      SemidirectProduct.inl (betaG x) := by
  have h := SemidirectProduct.inl_aut (φ := betaGroup.subtype)
    (⟨betaG, Subgroup.mem_zpowers _⟩ : betaGroup) x
  rw [map_inv] at h
  change SemidirectProduct.inl (betaG x) = betaStarElt * SemidirectProduct.inl x * betaStarElt⁻¹
    at h
  rw [h, betaStarElt_inv]

theorem b3con_of
    (hcoord : DistThreeFieldCoords) (hloc : DistThreeLocalOrbits) :
    ∀ v u : CVert, cgraph.dist v u = 3 →
      (cgraph.induce (cgraph.neighborSet u ∩ sphereFour v)).Connected := by
  intro v u hvu
  obtain ⟨hc, ρ, iu, hL, hβ, hfix⟩ := hcoord v u hvu
  have hXcard := (hloc v u hvu).2.2.2.2.1
  have hX : ∀ z : cgraph.neighborSet u,
      (z : CVert) ∈ sphereFour v ↔ betaG (iu z : stdGroup) ≠ iu z := by
    intro z
    have e : (iu (stabAct ⟨clabelS v, hc⟩ z) : stdGroup) = betaG (iu z) := by
      have h := hL.1 ⟨clabelS v, hc⟩ z
      rw [hβ, inv_betaStarElt_mul_inl_mul] at h
      exact SemidirectProduct.inl_injective h
    rw [hfix z]
    constructor
    · intro hne heq
      apply hne
      have h1 : stabAct ⟨clabelS v, hc⟩ z = z := iu.injective (Subtype.ext (e.trans heq))
      exact congrArg Subtype.val h1
    · intro hne heq
      apply hne
      rw [← e]
      have h1 : stabAct ⟨clabelS v, hc⟩ z = z := Subtype.ext heq
      rw [h1]
  let φ : ↥(cgraph.neighborSet u ∩ sphereFour v) ≃ nonFixedRoots :=
    { toFun := fun z => ⟨iu ⟨z, z.2.1⟩, (hX ⟨z, z.2.1⟩).1 z.2.2⟩
      invFun := fun p => ⟨iu.symm p, (iu.symm p).2,
        (hX (iu.symm p)).2 (by rw [iu.apply_symm_apply]; exact p.2)⟩
      left_inv := fun z => Subtype.ext (by simp)
      right_inv := fun p => Subtype.ext (by simp) }
  let e : cgraph.induce (cgraph.neighborSet u ∩ sphereFour v) ≃g nonFixedGraph :=
    { toEquiv := φ
      map_rel_iff' := fun {a b} => by
        change nonFixedGraph.Adj (φ a) (φ b) ↔ cgraph.Adj a b
        rw [nonFixedGraph, SimpleGraph.fromRel_adj]
        have hne : (φ a ≠ φ b) ↔ (⟨a, a.2.1⟩ : cgraph.neighborSet u) ≠ ⟨b, b.2.1⟩ :=
          ⟨fun h e' => h (Subtype.ext (congrArg iu e')),
            fun h e' => h (iu.injective (congrArg Subtype.val e'))⟩
        constructor
        · rintro ⟨hab, hc' | hc'⟩
          · exact (hL.2.1 _ _ (hne.1 hab)).2 hc'
          · exact (hL.2.1 _ _ (hne.1 hab)).2 hc'.symm
        · intro hab
          have hab' : (⟨a, a.2.1⟩ : cgraph.neighborSet u) ≠ ⟨b, b.2.1⟩ := fun e' =>
            hab.ne (congrArg (fun z : cgraph.neighborSet u => (z : CVert)) e')
          exact ⟨hne.2 hab', Or.inl ((hL.2.1 _ _ hab').1 hab)⟩ }
  have hA : nonFixedRoots.ncard = 3898440 := by
    rw [← hXcard, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact (Nat.card_congr φ).symm
  exact e.connected_iff.2 (nonFixedGraph_connected (by rw [hA]; norm_num))

end CFSG.Monster.B.GSide
