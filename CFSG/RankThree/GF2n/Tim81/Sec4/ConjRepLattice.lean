module

public import CFSG.RankThree.GF2n.Tim81.Sec4.ConjRep
public import CFSG.RankThree.GF2n.Tim81.Setting
public import CFSG.RankThree.GF2n.Tim81.Overgroups

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X7

variable {G : Type} [Group G] {M V H : Subgroup G}

theorem subW_sup {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {E F : Subgroup G} (hE : E ≤ Tim79a.xOf V H) (hF : F ≤ Tim79a.xOf V H) :
    subW hW (E ⊔ F) = subW hW E ⊔ subW hW F := by
  have hcomm : ∀ a ∈ E, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hW.1.is_comm.comm ⟨a, hE ha⟩ ⟨b, hF hb⟩)
  ext x
  constructor
  · intro hx
    change (toW hW x : G) ∈ E ⊔ F at hx
    obtain ⟨e, he, f, hf, hef⟩ := exists_mul_of_mem_sup
      (V := E) (U := F) (le_normalizer_of_comm fun b hb a ha => (hcomm a ha b hb).symm) hx
    have hsum : ofW hW ⟨e, hE he⟩ + ofW hW ⟨f, hF hf⟩ = x := by
      have h1 : toW hW (ofW hW ⟨e, hE he⟩ + ofW hW ⟨f, hF hf⟩) = toW hW x := by
        rw [toW_add, toW_ofW, toW_ofW]
        exact Subtype.ext hef.symm
      rw [← ofW_mul]
      simpa using congrArg (ofW hW) h1
    rw [← hsum]
    exact Submodule.add_mem_sup ((mem_subW_iff _).mpr he) ((mem_subW_iff _).mpr hf)
  · intro hx
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
    rw [← huv]
    have hu' : (toW hW u : G) ∈ E := by
      have h' := hu
      rw [← ofW_toW hW u] at h'
      exact (mem_subW_iff _).mp h'
    have hv' : (toW hW v : G) ∈ F := by
      have h' := hv
      rw [← ofW_toW hW v] at h'
      exact (mem_subW_iff _).mp h'
    change (toW hW (u + v) : G) ∈ E ⊔ F
    rw [toW_add]
    exact Subgroup.mul_mem_sup hu' hv'

theorem subW_le_subW_iff {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {E F : Subgroup G} (hE : E ≤ Tim79a.xOf V H) :
    subW hW E ≤ subW hW F ↔ E ≤ F := by
  constructor
  · intro hle x hx
    have hmem : ofW hW ⟨x, hE hx⟩ ∈ subW hW E := (mem_subW_iff _).mpr hx
    exact (mem_subW_iff _).mp (hle hmem)
  · intro hEF
    exact subW_mono hEF

theorem subW_inj {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {E F : Subgroup G} (hE : E ≤ Tim79a.xOf V H) (hF : F ≤ Tim79a.xOf V H) :
    subW hW E = subW hW F ↔ E = F := by
  constructor
  · intro h
    exact le_antisymm ((subW_le_subW_iff hE).mp (le_of_eq h))
      ((subW_le_subW_iff hF).mp (le_of_eq h.symm))
  · rintro rfl
    rfl

theorem natCard_fixedSub_subRepW {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {X : Type} [Group X] (ψ : HBar V H ≃* X)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) {S : Subgroup G} (hS : S ≤ H) :
    Nat.card (fixedSub (subRepW hW ψ hW₀ hN) ((imgK V H S).map ψ)) =
      Nat.card ↥(W₀ ⊓ Subgroup.centralizer (S : Set G)) := by
  have hmap := fixedSub_subRepW hW ψ hW₀ hN hS
  rw [Nat.card_congr (Submodule.equivMapOfInjective (subW hW W₀).subtype
      (Submodule.subtype_injective (subW hW W₀))
      (fixedSub (subRepW hW ψ hW₀ hN) ((imgK V H S).map ψ))).toEquiv,
    hmap, natCard_subW _ (inf_le_left.trans hW₀)]

namespace RootHyp

variable [Finite G]

theorem inf_centralizer_Pc_eq_inf (h : RootHyp M V) {W₀ : Subgroup G} :
    W₀ ⊓ Subgroup.centralizer (Pc M V : Set G) = V ⊓ W₀ := by
  rw [Hyp.centralizer_Pc h.toHyp, inf_comm]

theorem inf_centralizer_conj_Pc_eq_inf (h : RootHyp M V) {y : G} {W₀ : Subgroup G} :
    W₀ ⊓ Subgroup.centralizer (conjSubgroup y (Pc M V) : Set G) = conjSubgroup y V ⊓ W₀ := by
  rw [Hyp.centralizer_conj_Pc h.toHyp y, inf_comm]

end RootHyp

end CFSG.RankThree.GF2n.Tim81

end
