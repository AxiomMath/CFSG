module

public import CFSG.Quasithin.Background.F1Borel
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

@[expose] noncomputable def spCh6 {G : Type} [Group G] (L K S : Subgroup G) : Subgroup G :=
  pCoreOf 2 (bigB L K S)

variable {G : Type} [Group G] [Finite G] {L K S : Subgroup G}

theorem spCh6_le (hS : IsSylowTwoOf S (bigB L K S)) : spCh6 L K S ≤ S :=
  F7.isSylowTwoOf_pCoreOf_le hS

theorem inf_le_spCh6_left (h : Hyp111R L K S) : S ⊓ L ≤ spCh6 L K S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← F1.pCoreOf_borelOf h.hyp.h1.sylow]
  refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans ?_) ?_ (pCoreOf_isPGroup 2 _)
  · exact le_sup_left.trans le_sup_left
  · exact (F1.bigB_le_normalizer_borelOf h).1.trans (normalizer_le_normalizer_pCoreOf 2 _)

theorem inf_le_spCh6_right (h : Hyp111R L K S) : S ⊓ K ≤ spCh6 L K S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← F1.pCoreOf_borelOf h.hyp.h2.sylow]
  refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans ?_) ?_ (pCoreOf_isPGroup 2 _)
  · exact le_sup_right.trans le_sup_left
  · exact (F1.bigB_le_normalizer_borelOf h).2.trans (normalizer_le_normalizer_pCoreOf 2 _)

theorem spCh6_inf_left (h : Hyp111R L K S) (hS : IsSylowTwoOf S (bigB L K S)) :
    spCh6 L K S ⊓ L = S ⊓ L :=
  le_antisymm (fun _ hx => ⟨spCh6_le hS hx.1, hx.2⟩) (le_inf (inf_le_spCh6_left h) inf_le_right)

theorem spCh6_inf_right (h : Hyp111R L K S) (hS : IsSylowTwoOf S (bigB L K S)) :
    spCh6 L K S ⊓ K = S ⊓ K :=
  le_antisymm (fun _ hx => ⟨spCh6_le hS hx.1, hx.2⟩) (le_inf (inf_le_spCh6_right h) inf_le_right)

theorem borelOf_spCh6_left (h : Hyp111R L K S) (hS : IsSylowTwoOf S (bigB L K S)) :
    borelOf L (spCh6 L K S) = borelOf L S := by
  unfold borelOf
  rw [spCh6_inf_left h hS]

theorem borelOf_spCh6_right (h : Hyp111R L K S) (hS : IsSylowTwoOf S (bigB L K S)) :
    borelOf K (spCh6 L K S) = borelOf K S := by
  unfold borelOf
  rw [spCh6_inf_right h hS]

omit [Finite G] in
theorem le_normalizer_spCh6 (L K S : Subgroup G) :
    S ≤ Subgroup.normalizer (spCh6 L K S : Set G) :=
  (le_sup_right : S ≤ bigB L K S).trans (le_normalizer_pCoreOf 2 _)

omit [Finite G] in
theorem spCh6_comm (L K S : Subgroup G) : spCh6 K L S = spCh6 L K S := by
  unfold spCh6
  rw [bigB_comm]

theorem le_normalizer_spCh6_sup (h : Hyp111R L K S) :
    L ⊔ S ⊔ borelOf K S ≤ Subgroup.normalizer ((L ⊔ spCh6 L K S ⊔ borelOf K S : Subgroup G) :
      Set G) := by
  have hSn : S ≤ Subgroup.normalizer ((L ⊔ spCh6 L K S ⊔ borelOf K S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (F1.le_normalizer_sup h.hyp.h1.normalizes (le_normalizer_spCh6 L K S))
      ((le_sup_right : S ≤ bigB L K S).trans (F1.bigB_le_normalizer_borelOf h).2)
  exact sup_le (sup_le ((le_sup_left.trans le_sup_left).trans Subgroup.le_normalizer) hSn)
    (le_sup_right.trans Subgroup.le_normalizer)

theorem charTwo_spCh6_left (h : Hyp111R L K S) (hS : IsSylowTwoOf S (bigB L K S)) :
    CharTwo (L ⊔ spCh6 L K S ⊔ borelOf K S) := by
  have hle : L ⊔ spCh6 L K S ⊔ borelOf K S ≤ L ⊔ S ⊔ borelOf K S :=
    sup_le_sup (sup_le_sup le_rfl (spCh6_le hS)) le_rfl
  exact CharTwo.of_normal h.hyp.h1.charTwo hle
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (le_normalizer_spCh6_sup h))

theorem hyp111_spCh6 (h : Hyp111R L K S) (hS : IsSylowTwoOf S (bigB L K S)) :
    Hyp111 L K (spCh6 L K S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite ↥(spCh6 L K S) := inferInstance
  have hp : IsPGroup 2 ↥(spCh6 L K S) := pCoreOf_isPGroup 2 _
  have hBL := F1.bigB_le_normalizer_left h
  have hS' : IsSylowTwoOf S (bigB K L S) := by rwa [bigB_comm]
  have h1 : Hyp111At L K (spCh6 L K S) := by
    refine ⟨hfin, hp, (pCoreOf_le 2 _).trans hBL.1, ?_, h.hyp.h1.listed, ?_, ?_⟩
    · rw [spCh6_inf_left h hS]
      exact h.hyp.h1.sylow
    · rw [borelOf_spCh6_right h hS]
      exact h.hyp.h1.borel_le
    · rw [borelOf_spCh6_right h hS]
      exact charTwo_spCh6_left h hS
  have h2 : Hyp111At K L (spCh6 L K S) := by
    refine ⟨hfin, hp, (pCoreOf_le 2 _).trans hBL.2, ?_, h.hyp.h2.listed, ?_, ?_⟩
    · rw [spCh6_inf_right h hS]
      exact h.hyp.h2.sylow
    · rw [borelOf_spCh6_left h hS]
      exact h.hyp.h2.borel_le
    · rw [borelOf_spCh6_left h hS]
      have := charTwo_spCh6_left h.symm hS'
      rwa [spCh6_comm] at this
  have ho2 : pCoreOf 2 (L ⊔ K ⊔ spCh6 L K S) = ⊥ := by
    set Y := L ⊔ K ⊔ spCh6 L K S with hY
    have hSY : S ≤ Subgroup.normalizer (Y : Set G) :=
      F1.le_normalizer_sup (F1.le_normalizer_sup h.hyp.h1.normalizes h.hyp.h2.normalizes)
        (le_normalizer_spCh6 L K S)
    have hle : pCoreOf 2 Y ≤ pCoreOf 2 (L ⊔ K ⊔ S) := by
      refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans
        (sup_le_sup le_rfl (spCh6_le hS))) ?_ (pCoreOf_isPGroup 2 Y)
      have hYN := le_normalizer_pCoreOf 2 Y
      refine sup_le (sup_le ((le_sup_left.trans le_sup_left).trans hYN)
        ((le_sup_right.trans le_sup_left).trans hYN)) ?_
      exact hSY.trans (normalizer_le_normalizer_pCoreOf 2 Y)
    rw [h.hyp.o2] at hle
    exact le_bot_iff.mp hle
  exact ⟨h1, h2, ho2⟩

theorem spCh6_normal_left (h : Hyp111R L K S) (hS : IsSylowTwoOf S (bigB L K S)) :
    ((spCh6 L K S).subgroupOf (spCh6 L K S ⊔ borelOf L (spCh6 L K S))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left, borelOf_spCh6_left h hS]
  exact sup_le Subgroup.le_normalizer
    ((le_sup_left.trans le_sup_left : borelOf L S ≤ bigB L K S).trans (le_normalizer_pCoreOf 2 _))

end CFSG.Quasithin.H13
