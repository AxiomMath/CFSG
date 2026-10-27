module

public import CFSG.RankThree.GF2n.Stroth78.QuadraticForm
public import CFSG.RankThree.GF2n.Stroth78.Sec2Centralizer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

private abbrev mkQ (S : Setting z E F) : ↥(Q z) →* QbarOf S :=
  QuotientGroup.mk' ((ZQ z).subgroupOf (Q z))

private noncomputable abbrev Wbar (S : Setting z E F) (W : Subgroup G) :
    Submodule (ZMod 2) (Additive (QbarOf S)) :=
  AddSubgroup.toZModSubmodule 2
    (Subgroup.map (mkQ S) (W.subgroupOf (Q z))).toAddSubgroup

private theorem mem_Wbar_iff (S : Setting z E F) (W : Subgroup G)
    {v : Additive (QbarOf S)} :
    v ∈ Wbar S W ↔ ∃ y : ↥(Q z), (y : G) ∈ W ∧ mkQ S y = Additive.toMul v := by
  simp only [Wbar, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup,
    Subgroup.mem_map, Subgroup.mem_subgroupOf, Additive.toMul]

private theorem mem_orth_iff (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] (W : Subgroup G) (hWQ : W ≤ Q z)
    (x : ↥(Q z)) :
    Additive.ofMul (mkQ S x) ∈ LinearMap.BilinForm.orthogonal ((q S).polarBilin) (Wbar S W) ↔
      (x : G) ∈ Subgroup.centralizer (W : Set G) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwbar : Additive.ofMul (mkQ S ⟨w, hWQ hw⟩) ∈ Wbar S W := by
      rw [mem_Wbar_iff]
      exact ⟨⟨w, hWQ hw⟩, hw, rfl⟩
    have h0 := h _ hwbar
    have h0' : QuadraticMap.polar (q S) (QuotientGroup.mk ⟨w, hWQ hw⟩)
        (QuotientGroup.mk x) = 0 := h0
    exact (polar_q_eq_zero_iff S ⟨w, hWQ hw⟩ x).mp h0' 
  · intro hx v hv
    rw [mem_Wbar_iff] at hv
    obtain ⟨y, hy, hvy⟩ := hv
    have hv' : v = Additive.ofMul (mkQ S y) := by
      change Additive.toMul v = mkQ S y
      exact hvy.symm
    rw [hv']
    exact (polar_q_eq_zero_iff S y x).mpr (hx y hy)

private theorem map_centralizer_eq_orthogonal (S : Setting z E F)
    [Module (ZMod 2) (Additive (Abelianization F))] (W : Subgroup G) (hWQ : W ≤ Q z) :
    (Subgroup.map (mkQ S)
        ((Subgroup.centralizer (W : Set G) ⊓ Q z).subgroupOf (Q z))).toAddSubgroup =
      (LinearMap.BilinForm.orthogonal ((q S).polarBilin) (Wbar S W)).toAddSubgroup := by
  ext v
  rw [Additive.mem_toAddSubgroup, Submodule.mem_toAddSubgroup]
  constructor
  · rintro ⟨x, hx, hxv⟩
    have hv : v = Additive.ofMul (mkQ S x) := by
      change Additive.toMul v = mkQ S x
      exact hxv.symm
    rw [hv]
    have hxC : (x : G) ∈ Subgroup.centralizer (W : Set G) ⊓ Q z := by
      simpa using (Subgroup.mem_subgroupOf.mp hx)
    exact (mem_orth_iff S W hWQ x).mpr (Subgroup.mem_inf.mp hxC).1
  · intro hv
    obtain ⟨x, hx⟩ :=
      QuotientGroup.mk'_surjective ((ZQ z).subgroupOf (Q z)) (Additive.toMul v)
    have hv' : v = Additive.ofMul (mkQ S x) := by
      change Additive.toMul v = mkQ S x
      exact hx.symm
    rw [hv'] at hv ⊢
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨(mem_orth_iff S W hWQ x).mp hv, x.2⟩

theorem commutatorOrthogonality (S : Setting z E F) : CommutatorOrthogonality S := by
  classical
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  intro W hZW hWQ
  set C : Subgroup G := Subgroup.centralizer (W : Set G) ⊓ Q z with hCdef
  have hCQ : C ≤ Q z := by rw [hCdef]; exact inf_le_right
  have hZC : ZQ z ≤ C := by
    rw [hCdef]
    intro x hx
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.centralizer_le hWQ (Subgroup.mem_inf.mp hx).2, (Subgroup.mem_inf.mp hx).1⟩
  have hcardC : Nat.card ↥C = Nat.card (ZQ z) *
      Nat.card ↥(Subgroup.map (mkQ S) (C.subgroupOf (Q z))) := by
    have h := Subgroup.card_ker_mul_card_range
      ((mkQ S).comp (Subgroup.inclusion hCQ))
    have hker : ((mkQ S).comp (Subgroup.inclusion hCQ)).ker = (ZQ z).subgroupOf C := by
      ext c
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply,
        mkQ, QuotientGroup.mk'_apply, Subgroup.coe_inclusion]
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rw [Subgroup.coe_inclusion]
    have hrange : ((mkQ S).comp (Subgroup.inclusion hCQ)).range =
        Subgroup.map (mkQ S) (C.subgroupOf (Q z)) := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rw [hker, hrange] at h
    rw [h.symm, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv]
  have hcardW : Nat.card W = Nat.card (ZQ z) *
      Nat.card ↥(Subgroup.map (mkQ S) (W.subgroupOf (Q z))) := by
    have h := Subgroup.card_ker_mul_card_range
      ((mkQ S).comp (Subgroup.inclusion hWQ))
    have hker : ((mkQ S).comp (Subgroup.inclusion hWQ)).ker = (ZQ z).subgroupOf W := by
      ext c
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply,
        mkQ, QuotientGroup.mk'_apply, Subgroup.coe_inclusion]
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rw [Subgroup.coe_inclusion]
    have hrange : ((mkQ S).comp (Subgroup.inclusion hWQ)).range =
        Subgroup.map (mkQ S) (W.subgroupOf (Q z)) := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rw [hker, hrange] at h
    rw [h.symm, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv]
  have hcardQ : Nat.card (Q z) = Nat.card (ZQ z) * Nat.card (QbarOf S) := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := mkQ S)
      (QuotientGroup.mk'_surjective ((ZQ z).subgroupOf (Q z)))
    have hker : (mkQ S).ker = (ZQ z).subgroupOf (Q z) := by
      ext x
      simp only [MonoidHom.mem_ker, mkQ, QuotientGroup.mk'_apply]
      exact QuotientGroup.eq_one_iff x
    rw [hker] at h
    rw [h.symm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show ZQ z ≤ Q z from inf_le_left)).toEquiv]
  have hcardOrth : Nat.card ↥(Subgroup.map (mkQ S) (C.subgroupOf (Q z))) =
      Nat.card ↥(LinearMap.BilinForm.orthogonal ((q S).polarBilin) (Wbar S W)) :=
    congrArg (fun A : AddSubgroup (Additive (QbarOf S)) => Nat.card ↥A)
      (map_centralizer_eq_orthogonal S W hWQ)
  have hcardWbar : Nat.card ↥(Wbar S W) =
      Nat.card ↥(Subgroup.map (mkQ S) (W.subgroupOf (Q z))) := rfl
  have hVcard : Nat.card (QbarOf S) = 2 ^ finrank (ZMod 2) (Additive (QbarOf S)) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (QbarOf S))
    rw [Nat.card_zmod] at h
    exact h
  have hWbarcard : Nat.card ↥(Wbar S W) = 2 ^ finrank (ZMod 2) (Wbar S W) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Wbar S W)
    rw [Nat.card_zmod] at h
    exact h
  have hOrthcard : Nat.card ↥(LinearMap.BilinForm.orthogonal ((q S).polarBilin) (Wbar S W)) =
      2 ^ finrank (ZMod 2) (LinearMap.BilinForm.orthogonal ((q S).polarBilin) (Wbar S W)) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := LinearMap.BilinForm.orthogonal ((q S).polarBilin) (Wbar S W))
    rw [Nat.card_zmod] at h
    exact h
  have horthdim : finrank (ZMod 2) (LinearMap.BilinForm.orthogonal ((q S).polarBilin) (Wbar S W)) =
      finrank (ZMod 2) (Additive (QbarOf S)) - finrank (ZMod 2) (Wbar S W) :=
    LinearMap.BilinForm.finrank_orthogonal (q_nondegenerate S) (Wbar S W)
  have hd : finrank (ZMod 2) (Wbar S W) ≤ finrank (ZMod 2) (Additive (QbarOf S)) :=
    Submodule.finrank_le _
  have harith : ∀ a n d : ℕ, d ≤ n → (a * 2 ^ (n - d)) * (a * 2 ^ d) = (a * 2 ^ n) * a := by
    intro a n d hdn
    calc
      (a * 2 ^ (n - d)) * (a * 2 ^ d) = a * (2 ^ (n - d) * 2 ^ d) * a := by ring
      _ = a * 2 ^ n * a := by rw [← pow_add, Nat.sub_add_cancel hdn]
      _ = (a * 2 ^ n) * a := by ring
  calc
    Nat.card ↥C * Nat.card W =
        (Nat.card (ZQ z) * Nat.card ↥(Subgroup.map (mkQ S) (C.subgroupOf (Q z)))) *
          (Nat.card (ZQ z) * Nat.card ↥(Subgroup.map (mkQ S) (W.subgroupOf (Q z)))) := by
      rw [hcardC, hcardW]
    _ = (Nat.card (ZQ z) * Nat.card ↥(LinearMap.BilinForm.orthogonal ((q S).polarBilin) (Wbar S W))) *
          (Nat.card (ZQ z) * Nat.card ↥(Wbar S W)) := by
      rw [hcardOrth, hcardWbar]
    _ = (Nat.card (ZQ z) * 2 ^ (finrank (ZMod 2) (Additive (QbarOf S)) -
            finrank (ZMod 2) (Wbar S W))) *
          (Nat.card (ZQ z) * 2 ^ finrank (ZMod 2) (Wbar S W)) := by
      rw [hOrthcard, horthdim, hWbarcard]
    _ = (Nat.card (ZQ z) * 2 ^ finrank (ZMod 2) (Additive (QbarOf S))) *
          Nat.card (ZQ z) :=
      harith _ _ _ hd
    _ = Nat.card (Q z) * Nat.card (ZQ z) := by rw [hcardQ, hVcard]

end CFSG.RankThree.GF2n.Stroth78

