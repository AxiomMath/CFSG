module

public import CFSG.Sporadic.Co1Block.TwoACheck
public import CFSG.Sporadic.Co1Block.CentQ
public import CFSG.Sporadic.Co1Block.CentGA
public import CFSG.Sporadic.Co1Block.Co1Equiv
public import CFSG.Sporadic.Co1.Module.Involutions

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative Matrix

abbrev aG : GL24 := (iotaA : GL24)

abbrev twoAE : Subgroup GL24 := brayE aG twoAD1 twoABray

abbrev twoAQg : ℕ → GL24 := fun k => (iotaQ k : GL24)

abbrev twoAQ : Subgroup GL24 := qSub twoAQg twoAQRows.length

theorem twoAQRows_length : twoAQRows.length = 8 := by simp [twoAQRows]

theorem qRep_twoA :
    QRep twoAQRows twoAQg := by
  intro l hl
  rw [twoAQRows_length] at hl
  rw [twoAQRows, List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
    List.getElem_range]
  exact rep_iotaQ l

theorem twoA_misc_parts :
    (gtBFS twoAQRows.toArray 512).pts.contains iotaARows = true ∧
    (∀ q ∈ twoAQRows, CFSG.Sporadic.Co1Schreier.Native.mul q iotaARows =
      CFSG.Sporadic.Co1Schreier.Native.mul iotaARows q) ∧
    fixCount (transposeRows 24 iotaARows) = 65536 ∧ (gtBFS twoAQRows.toArray 512).pts.size = 512 ∧
    CFSG.Sporadic.Co1Schreier.Native.mul iotaARows iotaARows =
      CFSG.Sporadic.Co1Schreier.Native.one ∧ validRows iotaARows = true ∧
    iotaARows ≠ CFSG.Sporadic.Co1Schreier.Native.one := by
  have h := twoA_misc_check
  simp only [twoAMiscOf, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem twoAE_le :
    twoAE ≤ GA ⊓ Subgroup.centralizer {aG} :=
  brayE_le rep_iotaA iotaA_mem_GA twoA_cent_check

theorem card_twoAE_ge :
    89181388800 ≤ Nat.card twoAE := by
  have h := card_brayE_ge rep_iotaA twoA_cent_check
  have hp : ∏ i ∈ Finset.range twoAVBase.length, twoAVSizes.getD i 0 = 89181388800 := by
    simp only [twoAVBase, twoAVSizes, List.length_cons, List.length_nil, Finset.prod_range_succ,
      Finset.prod_range_zero]
    rfl
  rw [hp] at h
  exact h

theorem aG_sq :
    aG * aG = 1 := by
  have h := rep_iotaA.mul rep_iotaA
  rw [twoA_misc_parts.2.2.2.2.1] at h
  exact h.eq MRep.one

theorem aG_ne_one :
    aG ≠ 1 := by
  intro h
  have h1 : MRep iotaARows aG := rep_iotaA
  rw [h] at h1
  apply twoA_misc_parts.2.2.2.2.2.2
  refine CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid twoA_misc_parts.2.2.2.2.2.1
    validRows_one ?_
  rw [h1]
  exact MRep.one.symm

theorem orderOf_aG :
    orderOf aG = 2 :=
  orderOf_eq_prime (by rw [sq]; exact aG_sq) aG_ne_one

theorem card_cent_aG_le :
    Nat.card (GA ⊓ Subgroup.centralizer {aG} : Subgroup GL24) ≤
    89181388800 := by
  set s : CFSG.Blueprint.NativeSporadic.Co1 := co1MatEquiv.symm ⟨aG, iotaA_mem_GA⟩
  have hsv : s.val.val = (aG : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
    rw [← co1MatEquiv_val, MulEquiv.apply_symm_apply]
  have key : ∀ (g : GL24) (hg : g ∈ GA), orderOf g = 2 →
      orderOf (co1MatEquiv.symm ⟨g, hg⟩) = 2 := by
    intro g hg h
    rw [orderOf_co1MatEquiv_symm, Subgroup.orderOf_mk, h]
  have hs2 : orderOf s = 2 := key aG iotaA_mem_GA orderOf_aG
  have hfix : (CFSG.Monster.GMS.co1Fix s).ncard = 2 ^ 16 := by
    rw [CFSG.Monster.GMS.co1Inv_fix_eq]
    have e : {v : Vec24 | CFSG.Sporadic.Co1.Module.co1Act s v = v} =
        {v : Vec24 | rowsMatrix 24 iotaARows *ᵥ v = v} := by
      ext v
      simp only [Set.mem_ofPred_eq, CFSG.Sporadic.Co1.Module.co1Act_eq_mulVec]
      rw [show CFSG.Sporadic.Co1.Module.matHom s = rowsMatrix 24 iotaARows by
        rw [rep_iotaA]; exact hsv]
    rw [e, CFSG.Sporadic.Co1.Module.ncard_fix, twoA_misc_parts.2.2.1]
    norm_num
  have hb := (CFSG.Monster.GMS.co1InvolutionFacts.1 s hs2).1
  rw [hfix] at hb
  have hc : Nat.card (Subgroup.centralizer ({s} : Set CFSG.Blueprint.NativeSporadic.Co1)) =
      Nat.card (GA ⊓ Subgroup.centralizer {aG} : Subgroup GL24) := by
    rw [card_centralizer_co1 s, MulEquiv.apply_symm_apply, card_centralizer_GA]
  rw [← hc]
  omega

theorem twoAE_eq :
    twoAE = GA ⊓ Subgroup.centralizer {aG} :=
  Subgroup.eq_of_le_of_card_ge twoAE_le (card_cent_aG_le.trans card_twoAE_ge)

theorem card_cent_aG :
    Nat.card (GA ⊓ Subgroup.centralizer {aG} : Subgroup GL24) =
    89181388800 :=
  le_antisymm card_cent_aG_le (twoAE_eq ▸ card_twoAE_ge)

theorem card_twoAQ :
    Nat.card twoAQ = 512 := by
  rw [card_Q qRep_twoA twoA_q_check, twoA_misc_parts.2.2.2.1]

theorem twoAQg_comm
    (k : ℕ) (hk : k < 8) : twoAQg k * aG = aG * twoAQg k := by
  have hq : iotaQRows k ∈ twoAQRows := by
    rw [twoAQRows]
    exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩
  have e := twoA_misc_parts.2.1 _ hq
  exact ((rep_iotaQ k).mul rep_iotaA).eq (by rw [e]; exact rep_iotaA.mul (rep_iotaQ k))

theorem twoAQ_le :
    twoAQ ≤ GA ⊓ Subgroup.centralizer {aG} := by
  show Subgroup.closure (twoAQg '' {l | l < twoAQRows.length}) ≤ _
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  rw [twoAQRows_length] at hk
  exact Subgroup.mem_inf.2 ⟨iotaQ_mem_GA k,
    Subgroup.mem_centralizer_singleton_iff.2 (twoAQg_comm k hk)⟩

theorem aG_mem_twoAQ :
    aG ∈ twoAQ :=
  mem_Q_of_contains qRep_twoA twoA_q_check twoA_misc_parts.1 rep_iotaA

theorem twoAQ_normal :
    ∀ g ∈ GA ⊓ Subgroup.centralizer {aG}, ∀ q ∈ twoAQ, g * q * g⁻¹ ∈ twoAQ := by
  rw [← twoAE_eq]
  exact brayE_conj_mem_Q rep_iotaA twoA_cent_check qRep_twoA twoA_q_check

theorem twoARoots_length : twoARoots.length = 8 := rfl

theorem twoA_tower_prod : ∏ i ∈ Finset.range twoARoots.length, twoACSizes.getD i 0 =
    44590694400 := by
  simp only [twoARoots_length, twoACSizes, Finset.prod_range_succ, Finset.prod_range_zero]
  rfl

theorem twoA_selfCentralizing :
    ∀ g ∈ GA ⊓ Subgroup.centralizer {aG},
    (∀ q ∈ twoAQ, g * q = q * g) → g ∈ twoAQ := by
  obtain ⟨b, hb⟩ := exists_roots qRep_twoA twoA_q_check
  have hT := card_mul_card_towerStab_brayE_le rep_iotaA twoA_cent_check twoA_q_check
    (fun i hi => (hb i hi).2)
  have hE : brayE aG twoAD1 twoABray = GA ⊓ Subgroup.centralizer {aG} := twoAE_eq
  rw [twoA_tower_prod, hE, card_cent_aG] at hT
  set T := towerStab (GA ⊓ Subgroup.centralizer {aG}) b twoARoots.length
  have hT2 : Nat.card T ≤ 2 := by omega
  have hmemT : ∀ g ∈ GA ⊓ Subgroup.centralizer {aG}, (∀ q ∈ twoAQ, g * q = q * g) → g ∈ T :=
    fun g hg hq => mem_towerStab_of_lt hg _ fun i hi => hq (b i) (hb i hi).1
  intro g hg hq
  have hgT := hmemT g hg hq
  have h1T : (1 : GL24) ∈ T := T.one_mem
  have haT : aG ∈ T := hmemT aG (Subgroup.mem_inf.2 ⟨iotaA_mem_GA,
    Subgroup.mem_centralizer_singleton_iff.2 rfl⟩) fun q hq =>
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (twoAQ_le hq)).2).symm
  by_contra hgQ
  have hg1 : g ≠ 1 := fun h => hgQ (h ▸ twoAQ.one_mem)
  have hga : g ≠ aG := fun h => hgQ (h ▸ aG_mem_twoAQ)
  have hsub : ({1, aG, g} : Set GL24) ⊆ (T : Set GL24) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [h1T, haT, hgT]
  have hcard3 : ({1, aG, g} : Set GL24).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [aG_ne_one.symm, hg1.symm]),
      Set.ncard_pair hga.symm]
  have h3 : 3 ≤ Nat.card T := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [hcard3, ← Nat.card_coe_set_eq] at this
  omega

end CFSG.Sporadic.Co1Block
