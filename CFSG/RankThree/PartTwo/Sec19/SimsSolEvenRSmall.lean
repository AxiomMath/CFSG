module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmallOmega

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}

theorem card_Rc_le_two_of_tight (C : Cfg G M X n) (D : C.PiData) (hn : 8 ≤ n)
    (htight : Subgroup.centralizer (X : Set G) = ⊥ ∨
      (Rc X ≠ ⊥ ∧
        (∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X) ∧
        ((IsCyclic ↥(Rc X) ∧ Nat.card ↥(Rc X) = 4) ∨ CFSG.Open.IsElemAbelian 2 (Rc X)) ∧
        ∃ g : G, conjSubgroup g (Rc X) ≤ M ∧ conjSubgroup g (Rc X) ≠ Rc X)) :
    Nat.card ↥(Rc X) ≤ 2 := by
  rcases htight with hC | ⟨-, hRsyl, hab, g, hTM, hne⟩
  · have hR : Rc X = ⊥ := by
      apply le_bot_iff.1
      rw [← hC]
      exact CFSG.CGT.PushingUpLit.SolK.pCoreOf_le_self _
    rw [hR, Subgroup.card_bot]
    omega
  · by_contra hcard
    push Not at hcard
    have hW : Nonempty C.UIso ∨ Function.Injective C.β := by
      have h2 := C.card_blockZ_le_two
      have h1 : 0 < Nat.card ↥(blockZ X) := Nat.card_pos
      rcases (show Nat.card ↥(blockZ X) = 1 ∨ Nat.card ↥(blockZ X) = 2 by omega) with h | h
      · exact Or.inr (C.beta_injective_of_card h)
      · exact Or.inl (C.nonempty_uIso h)
    have hRab : ∀ r ∈ Rc X, ∀ r' ∈ Rc X, r * r' = r' * r := by
      intro r hr r' hr'
      rcases hab with ⟨hcyc, -⟩ | hel
      · exact congrArg Subtype.val
          ((IsCyclic.isMulCommutative (α := ↥(Rc X))).is_comm.comm ⟨r, hr⟩ ⟨r', hr'⟩)
      · exact congrArg Subtype.val (hel.1.is_comm.comm ⟨r, hr⟩ ⟨r', hr'⟩)
    have hgM : g ∉ M := by
      intro hg
      apply hne
      exact Setting.map_conj_eq_of_normalized (fun x hx => RSmall.R_normalized C.S hg hx)
        (fun x hx => RSmall.R_normalized C.S (M.inv_mem hg) hx)
    exact RSmall.false_of_three_le C D hn hW hRsyl hRab hgM hTM (by omega)

theorem card_Rc_le_two
    (C : Cfg G M X n) (D : C.PiData) (hn : n = 10)
    (hST : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight)
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement) :
    CFSG.Assembly.InCatalog G ∨ Nat.card ↥(Rc X) ≤ 2 := by
  rcases C.S.inCatalog_or_tight hNode hST with h | h
  · exact Or.inl h
  · exact Or.inr (card_Rc_le_two_of_tight C D (by omega) h)

theorem card_Rc_le_two_eight
    (C : Cfg G M X n) (D : C.PiData) (hn : n = 8)
    (hST : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight)
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement) :
    CFSG.Assembly.InCatalog G ∨ Nat.card ↥(Rc X) ≤ 2 := by
  rcases C.S.inCatalog_or_tight hNode hST with h | h
  · exact Or.inl h
  · exact Or.inr (card_Rc_le_two_of_tight C D (by omega) h)

end Cfg

end CFSG.RankThree.PartTwo.Sec19.SolEven
