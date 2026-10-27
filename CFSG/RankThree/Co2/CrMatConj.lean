module

public import CFSG.RankThree.Co2.CrMat
public import CFSG.RankThree.Co2.CmWords
public import CFSG.RankThree.Co2.CrBridge
public import CFSG.RankThree.Co2.ClassesM

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Co2Inv CFSG.KC.Co2Syl

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem map_subW_eq {ws : Array (List ℕ)} (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42) :
    (subW ws).toSubmonoid.map crMat = matGrp ws :=
  le_antisymm (map_subW_le hws) (matGrp_le_map hws)

theorem mem_subW_iff_crMat {ws : Array (List ℕ)} (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42) {y : Cr} :
    y ∈ subW ws ↔ crMat y ∈ matGrp ws := by
  rw [← map_subW_eq hws]
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y', hy', e⟩
    rwa [← crMat_injective e]

theorem card_subW_crMat {ws : Array (List ℕ)} (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42) (P : M22 → Prop) :
    Nat.card {j : subW ws // P (crMat (j : Cr))} = Nat.card {x // x ∈ matGrp ws ∧ P x} := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun j => ⟨crMat (j : Cr), (mem_subW_iff_crMat hws).1 j.1.2, j.2⟩) ⟨?_, ?_⟩)
  · intro a b h
    exact Subtype.ext (Subtype.ext (crMat_injective (congrArg Subtype.val h)))
  · rintro ⟨x, hx, hP⟩
    rw [← map_subW_eq hws] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨⟨y, hy⟩, hP⟩, rfl⟩

theorem closure_toSubmonoid_eq {G : Type*} [Group G] [Finite G] (S : Set G) :
    (Subgroup.closure S).toSubmonoid = Submonoid.closure S := by
  apply le_antisymm
  · let H : Subgroup G :=
      { Submonoid.closure S with
        inv_mem' := fun {a} ha => by
          have hn : orderOf a ≠ 0 := (orderOf_pos a).ne'
          have e : a ^ (orderOf a - 1) = a⁻¹ :=
            eq_inv_of_mul_eq_one_left (by rw [pow_sub_one_mul hn, pow_orderOf_eq_one])
          change a⁻¹ ∈ Submonoid.closure S
          rw [← e]
          exact Submonoid.pow_mem _ ha _ }
    have hle : Subgroup.closure S ≤ H := (Subgroup.closure_le H).2 Submonoid.subset_closure
    exact fun x hx => hle hx
  · exact Submonoid.closure_le.2 Subgroup.subset_closure

theorem isConj_rCr_iff {y : Cr} :
    IsConj rCr y ↔ y = rCr := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := isConj_iff.1 h
    rw [← hg, Subgroup.mem_center_iff.1 rCr_mem_center g, mul_inv_cancel_right]
  · rintro rfl
    exact IsConj.refl _

theorem isConj_rep_zero_iff {y : Cr} : IsConj (rep 0) y ↔ y = rCr := by
  rw [rep_zero, isConj_rCr_iff]

theorem not_isConj_rep_rCr {c : ℕ} (hc : c < 10) (h1 : classSizes[c]! ≠ 1) : ¬ IsConj (rep c) rCr := by
  intro h
  have e : rep c = rCr := isConj_rCr_iff.1 h.symm
  have hC : Subgroup.centralizer ({rep c} : Set Cr) = ⊤ := by
    rw [e, eq_top_iff]
    intro x _
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_center_iff.1 rCr_mem_center x
  have hcard := card_centralizer_rep hc
  rw [hC, Subgroup.card_top, natCard_Cr] at hcard
  omega

end CFSG.RankThree.Co2

end
