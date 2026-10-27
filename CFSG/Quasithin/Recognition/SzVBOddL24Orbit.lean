module

public import CFSG.Quasithin.Recognition.SzVBOdd

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem orbit_of_comm [Finite G] {P S V : Subgroup G} {z : G}
    (hK : KleinData P V z) (hW : IsElemAbelian 2 (conjClosure V P))
    (hS_le : S ≤ P) (hS : IsPGroup 2 S) (hSV : S ≤ Subgroup.normalizer (V : Set G))
    (hS_trans : ∀ U U' : ConjSet P V, U ≠ ConjSet.base P V → U' ≠ ConjSet.base P V →
      ∃ s : ↥P, (s : G) ∈ S ∧ s • U = U')
    (hodd : Odd (Nat.card (ConjSet P V))) (hfive : 5 ≤ Nat.card (ConjSet P V))
    {e e' : ↥P}
    (hcomm : ∀ w ∈ conjClosure V P, (e' : G) * ((e : G) * w * (e : G)⁻¹ * w⁻¹) * (e' : G)⁻¹ =
      (e : G) * w * (e : G)⁻¹ * w⁻¹) :
    ∀ U : ConjSet P V, e • U = U ∨ e' • U = U ∨ e • U = e' • U := by
  classical
  obtain ⟨t, ht⟩ := exists_tDataG hK
  have hPN := le_normalizer_conjClosure V P
  generalize conjClosure V P = W at hW hcomm ht hPN
  have : Fintype (ConjSet P V) := Fintype.ofFinite _
  let _ : CommGroup ↥W := commGroupOfElemAbelian hW
  have hmul : ∀ a b : ↥W, ((a * b : ↥W) : G) = (a : G) * (b : G) := fun a b => rfl
  have hinvW : ∀ a : ↥W, ((a⁻¹ : ↥W) : G) = (a : G)⁻¹ := fun a => rfl
  have honeW : ((1 : ↥W) : G) = 1 := rfl
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥P →* MulAut ↥W,
      ∀ (x : ↥P) (a : ↥W), ((ρ x a : ↥W) : G) = x * a * (x : G)⁻¹ :=
    ⟨(conjAct W).comp (Subgroup.inclusion hPN),
      fun x a => OddAux.conjAct_coe W (Subgroup.inclusion hPN x) a⟩
  obtain ⟨tW, htW⟩ : ∃ tW : ConjSet P V → ↥W, ∀ a, ((tW a : ↥W) : G) = t a :=
    ⟨fun a => ⟨t a, ht.t_mem a⟩, fun a => rfl⟩
  obtain ⟨zW, hzW⟩ : ∃ zW : ↥W, (zW : G) = z := ⟨⟨z, ht.z_mem⟩, rfl⟩
  have hT : TData ρ tW zW := by
    refine ⟨fun a => Subtype.ext ?_, Subtype.ext ?_, fun h => ht.z_ne_one ?_,
      fun x => Subtype.ext ?_, fun x a => ?_, fun a b hab => ?_⟩
    · rw [hmul, htW, honeW]
      exact ht.t_sq a
    · rw [hmul, hzW, honeW]
      exact ht.z_sq
    · rw [← hzW, h, honeW]
    · rw [hρ, hzW]
      calc (x : G) * z * (x : G)⁻¹ = z * x * (x : G)⁻¹ := by rw [ht.z_cent x x.2]
        _ = z := mul_inv_cancel_right _ _
    · rcases ht.act x a with h | h
      · refine Or.inl (Subtype.ext ?_)
        rw [hρ, htW, htW]
        exact h
      · refine Or.inr (Subtype.ext ?_)
        rw [hρ, hmul, htW, htW, hzW]
        exact h
    · refine ⟨fun h => (ht.distinct a b hab).1 ?_, fun h => (ht.distinct a b hab).2 ?_⟩
      · have := congrArg Subtype.val h
        rwa [hmul, htW, htW, honeW] at this
      · have := congrArg Subtype.val h
        rwa [hmul, htW, htW, hzW] at this
  have hΩ5 : 5 ≤ Fintype.card (ConjSet P V) := by
    rw [← Nat.card_eq_fintype_card]
    exact hfive
  have hker : KerProp tW zW := by
    refine kerProp_of_tData hT (OddAux.conjSet_isPretransitive P V) (S.subgroupOf P)
      (hS.of_equiv (Subgroup.subgroupOfEquivOfLe hS_le).symm) (ConjSet.base P V) ?_ ?_ ?_
    · intro r hr
      exact Subtype.ext
        (OddAux.conjSub_eq_of_mem_normalizer' (hSV (Subgroup.mem_subgroupOf.mp hr)))
    · intro a b ha hb
      obtain ⟨s, hs, h⟩ := hS_trans a b ha hb
      exact ⟨s, Subgroup.mem_subgroupOf.mpr hs, h⟩
    · rw [← Nat.card_eq_fintype_card]
      exact hodd
  have hcomm_coe : ∀ (s : ↥P) (a : ↥W), ((commMap ρ s a : ↥W) : G) =
      (s : G) * a * (s : G)⁻¹ * (a : G)⁻¹ := by
    intro s a
    rw [commMap_apply, hmul, hinvW, hρ]
  intro U
  refine orbit_le_two_of_quadratic hT hker hΩ5 e e' U (Or.inl ?_)
  apply Subtype.ext
  rw [hcomm_coe, hcomm_coe, htW, honeW, hcomm (t U) (ht.t_mem U)]
  exact mul_inv_cancel _

end CFSG.Quasithin.SzVB
