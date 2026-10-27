module

public import CFSG.Quasithin.EmptyFaithful.S151S9P2
public import CFSG.Quasithin.EmptyFaithful.S151S9P3A

public section

namespace CFSG.Quasithin

namespace HSRuLoc

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G]

theorem lift_excl [Finite G] {L S : Subgroup G} {H : Type} [Group H] [Finite H] {π : ↥L →* H}
    {P Kb Rb : Subgroup H} {e : ℕ} (c : LiftCtx L S π P Kb Rb e) :
    ExclHyp (liftK L π Kb) S e := by
  have hSK : S ≤ Subgroup.normalizer (liftK L π Kb : Set G) := (lift_struct c).2.1
  have hz : π.ker ≤ Subgroup.center ↥L := ker_le_center c
  have hcore : pCoreOf 2 (liftK L π Kb) = liftR L π Kb Rb := pCoreOf_liftK c
  have hmapK := map_liftK c
  obtain ⟨C, hC⟩ : ∃ C : Subgroup ↥L, C = ⁅Kb.comap π, Kb.comap π⁆ := ⟨_, rfl⟩
  have hK : liftK L π Kb = C.map L.subtype := by rw [hC]; rfl
  have hR : liftR L π Kb Rb = (C ⊓ Rb.comap π).map L.subtype := by
    show liftK L π Kb ⊓ _ = _
    rw [Subgroup.map_inf_eq _ _ _ L.subtype_injective, hK]
  have hmapC : C.map π = Kb := by
    have h : (liftK L π Kb).subgroupOf L = C := by
      rw [hK]; exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective C
    rwa [h] at hmapK
  have hmapRc : (C ⊓ Rb.comap π).map π = Rb := by
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨x, hx, rfl⟩ := hy
      exact hx.2
    · obtain ⟨x, hxC, rfl⟩ : y ∈ C.map π := hmapC ▸ c.hm.R_le hy
      exact ⟨x, ⟨hxC, hy⟩, rfl⟩
  have hmapQc : (⁅C ⊓ Rb.comap π, C⁆).map π = Rb := by
    rw [Subgroup.map_commutator, hmapRc, hmapC]
    exact c.hm.R_comm
  have hQcK : (⁅C ⊓ Rb.comap π, C⁆).map L.subtype ≤
      ⁅pCoreOf 2 (liftK L π Kb), liftK L π Kb⁆ := by
    rw [Subgroup.map_commutator, ← hK, ← hR, ← hcore]
  have hQR : ⁅pCoreOf 2 (liftK L π Kb ⊔ S), liftK L π Kb⁆ ≤ (C ⊓ Rb.comap π).map L.subtype := by
    rw [← hR, ← hcore]
    exact Excl.commutator_pCoreOf_sup_le hSK
  have hRQ : (⁅C ⊓ Rb.comap π, C⁆).map L.subtype ≤
      ⁅pCoreOf 2 (liftK L π Kb ⊔ S), liftK L π Kb⁆ :=
    hQcK.trans (Subgroup.commutator_mono (Excl.pCoreOf_le_pCoreOf_sup hSK) le_rfl)
  have hQL : ⁅pCoreOf 2 (liftK L π Kb ⊔ S), liftK L π Kb⁆ ≤ L :=
    hQR.trans (Subgroup.map_subtype_le _)
  have hB : ∀ y, y ∈ Rb ↔ ∃ q : G, ∃ hq : q ∈ ⁅pCoreOf 2 (liftK L π Kb ⊔ S), liftK L π Kb⁆,
      π ⟨q, hQL hq⟩ = y := by
    intro y
    constructor
    · intro hy
      have hy' : y ∈ (⁅C ⊓ Rb.comap π, C⁆).map π := by rw [hmapQc]; exact hy
      obtain ⟨x, hx, rfl⟩ := hy'
      exact ⟨(x : G), hRQ ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨x, hx, hxq⟩ := hQR hq
      subst hxq
      exact hx.2
  obtain ⟨T, hTQ, hT, hcard⟩ := Excl.exists_card_ker hQL π Rb hB
  refine ⟨?_, ⟨T, ?_, ?_, ?_⟩, c.hm.R_he⟩
  · obtain ⟨x, hxR, hx2⟩ := c.hm.R_order4
    obtain ⟨q, hq, hπq⟩ := (hB x).mp hxR
    refine ⟨q, hq, fun h => hx2 ?_⟩
    rw [← hπq, ← map_pow]
    have h1 : (⟨q, hQL hq⟩ : ↥L) ^ 2 = 1 := Subtype.ext (by simpa using h)
    rw [h1, map_one]
  · exact le_inf hTQ fun t ht => Subgroup.mem_centralizer_iff.mpr fun k hk =>
      Excl.commute_of_exists_ker hz (hT t ht) (liftK_le c hk)
  · exact le_inf hTQ fun t ht => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Excl.commute_of_exists_ker hz (hT t ht) (hQL hy)
  · exact hcard.trans (by rw [c.hm.R_card])

end HSRuLoc

end CFSG.Quasithin
