module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413Defs
public import CFSG.LocalAnalysis.WeakClosure81.W18T189FourBridge
import CFSG.RankThree.GF2n.Stroth80.Sec7TailFStarSimple

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem br4_false_one_comp (h : Asch5_14_13Prime) {Y L A : Subgroup (LGL 2 V)} (hLY : L ≤ Y)
    (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L) (hLs : IsSimpleGroup ↥L)
    (hLab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a)
    (hLc : ∀ y ∈ Y, (∀ l ∈ L, y * l = l * y) → y = 1) (hshape : Shape1413Prime ↥L)
    (hAY : A ≤ Y) (hAe : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card ↥A)
    (hq : CFSG.Quasithin.G11.commSpace A (commSub A) = ⊥) : False := by
  classical
  let S : Subgroup ↥Y := L.subgroupOf Y
  have hYle : Y ≤ Subgroup.normalizer L := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      exact hLn y hy l hl
    · intro hl
      have h' := hLn y⁻¹ (Y.inv_mem hy) (y * l * y⁻¹) hl
      have h'' : y⁻¹ * (y * l * y⁻¹) * y⁻¹⁻¹ = l := by group
      rwa [h''] at h'
  have hSnormal : S.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mpr hYle
  haveI : S.Normal := hSnormal
  let e : S ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLY
  haveI : IsSimpleGroup ↥L := hLs
  haveI hSsimple : IsSimpleGroup ↥S := e.isSimpleGroup
  have hnabS : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hLab
    refine ⟨⟨a, hLY ha⟩, ha, ⟨b, hLY hb⟩, hb, fun hcon => hab ?_⟩
    simpa using congrArg Subtype.val hcon
  have hnabSs : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnabS
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun hcon => hab (by simpa using congrArg Subtype.val hcon)⟩
  have hC : ∀ c : ↥Y, (∀ s ∈ S, c * s = s * c) → c = 1 := by
    intro c hcen
    refine Subtype.ext ?_
    refine hLc (c : LGL 2 V) c.2 ?_
    intro l hl
    have hmem : (⟨l, hLY hl⟩ : ↥Y) ∈ S := by
      rw [Subgroup.mem_subgroupOf]
      exact hl
    have hh := hcen ⟨l, hLY hl⟩ hmem
    simpa using congrArg Subtype.val hh
  have hEvenS : Even (Nat.card ↥S) := by
    by_contra hodd
    have hsolv : Group.IsSolvable ↥S :=
      CFSG.Milestones.odd_order_solvable (Nat.not_even_iff_odd.mp hodd)
    obtain ⟨a, b, hab⟩ := hnabSs
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolv a b)
  have hbot_case : ∀ P : Subgroup ↥Y, P.Normal → (P ⊓ S).subgroupOf S = ⊥ → P = ⊥ := by
    intro P hPn hbot
    haveI : P.Normal := hPn
    have hdisj : Disjoint (P ⊓ S) S := Subgroup.subgroupOf_eq_bot.mp hbot
    have hPS : P ⊓ S = ⊥ := by
      rw [disjoint_iff, inf_assoc, inf_idem] at hdisj
      exact hdisj
    have hcomm : ⁅P, S⁆ = ⊥ := by
      apply le_bot_iff.mp
      rw [← hPS]
      exact le_inf (Subgroup.commutator_le_left (H₁ := P) (H₂ := S))
        (Subgroup.commutator_le_right (H₁ := P) (H₂ := S))
    have hcent : P ≤ Subgroup.centralizer (S : Set ↥Y) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    rw [eq_bot_iff]
    intro p hp
    have hp1 : p = 1 :=
      hC p fun s hs => (Subgroup.mem_centralizer_iff.mp (hcent hp) s hs).symm
    simpa using hp1
  have hO2 : ∀ P : Subgroup ↥Y, P.Normal → IsPGroup 2 P → P = ⊥ := by
    intro P hPn hP2
    haveI : P.Normal := hPn
    rcases Subgroup.Normal.eq_bot_or_eq_top ((P ⊓ S).subgroupOf S) with hbot | htop
    · exact hbot_case P hPn hbot
    · have hSP : S ≤ P := (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_left
      have hSP2 : IsPGroup 2 ↥S :=
        hP2.of_injective (Subgroup.inclusion hSP) (Subgroup.inclusion_injective hSP)
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI hnil : Group.IsNilpotent ↥S := hSP2.isNilpotent
      obtain ⟨a, b, hab⟩ := hnabSs
      exact (hab ((IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance a b)).elim
  have hO : ∀ P : Subgroup ↥Y, P.Normal → Odd (Nat.card P) → P = ⊥ := by
    intro P hPn hPodd
    haveI : P.Normal := hPn
    rcases Subgroup.Normal.eq_bot_or_eq_top ((P ⊓ S).subgroupOf S) with hbot | htop
    · exact hbot_case P hPn hbot
    · have hSP : S ≤ P := (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_left
      have hdvd : Nat.card ↥(S.subgroupOf P) ∣ Nat.card ↥P :=
        ⟨(S.subgroupOf P).index, (Subgroup.card_mul_index (S.subgroupOf P)).symm⟩
      have hcard : Nat.card ↥(S.subgroupOf P) = Nat.card ↥S :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv
      have hEvenP : Even (Nat.card ↥P) := (hcard.symm ▸ hEvenS).trans_dvd hdvd
      exact absurd hEvenP (Nat.not_even_iff_odd.mpr hPodd)
  have hgf : generalizedFitting ↥Y = S :=
    CFSG.RankThree.GF2n.Stroth80.fstar_eq_of_simple hSsimple hnabS hC hO2 hO
  have hFstar : genFittingFStar ↥Y = S :=
    (CFSG.Adapters.genFittingFStar_eq_foundations ↥Y).trans hgf
  have hAe' : IsElemAbelian 2 (A.subgroupOf Y) := hAe.subgroupOf Y
  have hcardA : Nat.card ↥(A.subgroupOf Y) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv
  obtain ⟨B, hBA, hB4⟩ :=
    exists_subgroup_card_four (X := ↥Y) hAe'.isPGroup (hcardA.symm ▸ hA4)
  have hBe : IsElemAbelian 2 B := hAe'.mono hBA
  have hBq : IsQuadraticOn (repOf Y) B := (isQuadraticOn_lglRep (Y := Y) hq).mono hBA
  have hShapeS : Shape1413Prime ↥S := by
    rcases hshape with hh | ⟨p, hp, hgt, hlm⟩
    · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hh)
    · exact Or.inr ⟨p, hp, hgt, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hlm⟩
  exact h ↥Y (Multiplicative V) (multiplicative_sq_eq_one (W := V)) (repOf Y)
    (repOf_injective Y) S B hFstar hShapeS hB4 hBe hBq

end CFSG.LocalAnalysis.WeakClosure81

end
