module

public import CFSG.RankThree.GF2n.Tim77Prop24Core
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

theorem commute_commutator_of_sq_eq_one {G : Type*} [Group G] {t v : G} (ht : t * t = 1)
    (hu : (t * v * t⁻¹ * v⁻¹) * (t * v * t⁻¹ * v⁻¹) = 1) :
    (t * v * t⁻¹ * v⁻¹) * t = t * (t * v * t⁻¹ * v⁻¹) := by
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hu' : (t * v * t⁻¹ * v⁻¹)⁻¹ = t * v * t⁻¹ * v⁻¹ := inv_eq_of_mul_eq_one_right hu
  have h1 : t * v * t⁻¹ * v⁻¹ = v * t * v⁻¹ * t := by
    calc t * v * t⁻¹ * v⁻¹ = (t * v * t⁻¹ * v⁻¹)⁻¹ := hu'.symm
      _ = v * t * v⁻¹ * t⁻¹ := by group
      _ = v * t * v⁻¹ * t := by rw [hinv]
  calc (t * v * t⁻¹ * v⁻¹) * t = t * v * t * v⁻¹ * t := by rw [hinv]
    _ = t * (v * t * v⁻¹ * t) := by group
    _ = t * (t * v * t⁻¹ * v⁻¹) := by rw [h1]

theorem card_le_card_inf_normalizer {G : Type*} [Group G] [Finite G] {U V : Subgroup G}
    (hV : Assembly.IsElemAbelian 2 V) (hU : Assembly.IsElemAbelian 2 U) (hUTI : IsTI U)
    (hUN : U ≤ Subgroup.normalizer (V : Set G)) {v : G} (hv : v ∈ V)
    (hvN : v ∉ Subgroup.normalizer (U : Set G)) :
    Nat.card U ≤ Nat.card (V ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) := by
  have hmem : ∀ t : U, (t : G) * v * (t : G)⁻¹ * v⁻¹ ∈ V ⊓ Subgroup.normalizer (U : Set G) := by
    intro t
    have hconj : (t : G) * v * (t : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hUN t.2) v).mp hv
    have hcV : (t : G) * v * (t : G)⁻¹ * v⁻¹ ∈ V := V.mul_mem hconj (V.inv_mem hv)
    refine Subgroup.mem_inf.mpr ⟨hcV, ?_⟩
    by_cases ht1 : (t : G) = 1
    · rw [ht1, inv_one, one_mul, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · refine Tim77.mem_normalizer_of_commute_of_isTI hUTI t.2 ht1 ?_
      exact commute_commutator_of_sq_eq_one (hU.mul_self_eq_one t.2) (hV.mul_self_eq_one hcV)
  refine Nat.card_le_card_of_injective (fun t => ⟨(t : G) * v * (t : G)⁻¹ * v⁻¹, hmem t⟩) ?_
  intro t t' h
  have h' : (t : G) * v * (t : G)⁻¹ * v⁻¹ = (t' : G) * v * (t' : G)⁻¹ * v⁻¹ :=
    congrArg Subtype.val h
  have h2 : (t : G) * v * (t : G)⁻¹ = (t' : G) * v * (t' : G)⁻¹ := mul_right_cancel h'
  have hcomm : v * ((t' : G)⁻¹ * t) = ((t' : G)⁻¹ * t) * v := by
    calc v * ((t' : G)⁻¹ * t) = (t' : G)⁻¹ * ((t' : G) * v * (t' : G)⁻¹) * t := by group
      _ = (t' : G)⁻¹ * ((t : G) * v * (t : G)⁻¹) * t := by rw [h2]
      _ = ((t' : G)⁻¹ * t) * v := by group
  by_contra hne
  have hs1 : (t' : G)⁻¹ * t ≠ 1 := fun h1 => hne (Subtype.ext (inv_mul_eq_one.mp h1).symm)
  exact hvN (Tim77.mem_normalizer_of_commute_of_isTI hUTI (U.mul_mem (U.inv_mem t'.2) t.2) hs1
    hcomm)

theorem weaklyClosedIn_normalizer_of_centralizer_eq {G : Type} [Group G] [Finite G]
    {V : Subgroup G} (hel : Assembly.IsElemAbelian 2 V) (hTI : IsTI V)
    (hC : Subgroup.centralizer (V : Set G) = V) :
    WeaklyClosedIn V (Subgroup.normalizer (V : Set G)) := by
  refine ⟨Subgroup.le_normalizer, fun g hgN => ?_⟩
  by_contra hne
  have hUel : Assembly.IsElemAbelian 2 (conjSubgroup g V) := hel.map (MulAut.conj g).toMonoidHom
  have hUTI : IsTI (conjSubgroup g V) := isTI_conjSubgroup hTI g
  have hcard : Nat.card (conjSubgroup g V) = Nat.card V := card_conjSubgroup g V
  have hbot : V ⊓ conjSubgroup g V = ⊥ := inf_conjSubgroup_eq_bot_of_isTI hTI hne
  by_cases hVU : V ≤ Subgroup.normalizer ((conjSubgroup g V : Subgroup G) : Set G)
  · have hUV : conjSubgroup g V ≤ V := by
      intro t ht
      rw [← hC, Subgroup.mem_centralizer_iff]
      intro v hv
      have hcU : v * t * v⁻¹ * t⁻¹ ∈ conjSubgroup g V :=
        (conjSubgroup g V).mul_mem ((Subgroup.mem_normalizer_iff.mp (hVU hv) t).mp ht)
          ((conjSubgroup g V).inv_mem ht)
      have hcV : v * t * v⁻¹ * t⁻¹ ∈ V := by
        rw [mul_assoc v, mul_assoc v]
        exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hgN ht) v⁻¹).mp (V.inv_mem hv))
      have h0 : v * t * v⁻¹ * t⁻¹ ∈ V ⊓ conjSubgroup g V := Subgroup.mem_inf.mpr ⟨hcV, hcU⟩
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h0
      exact h0
    exact hne (Subgroup.eq_of_le_of_card_ge hUV hcard.ge)
  · obtain ⟨v, hv, hvN⟩ := SetLike.not_le_iff_exists.mp hVU
    have hle := card_le_card_inf_normalizer hel hUel hUTI hgN hv hvN
    have hVL : V ⊓ Subgroup.normalizer ((conjSubgroup g V : Subgroup G) : Set G) = V :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (hcard.symm.le.trans hle)
    have hvL : v ∈ V ⊓ Subgroup.normalizer ((conjSubgroup g V : Subgroup G) : Set G) := by
      rw [hVL]
      exact hv
    exact hvN (Subgroup.mem_inf.mp hvL).2

end CFSG.RankThree.GF2n.Tim79a
