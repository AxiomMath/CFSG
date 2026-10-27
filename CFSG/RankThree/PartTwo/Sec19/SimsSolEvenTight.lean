module

public import CFSG.CGT.Hall82.Tight
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo

abbrev Rc {G : Type} [Group G] (X : Subgroup G) : Subgroup G :=
  CFSG.Open.pCoreOf 2 (Subgroup.centralizer (X : Set G))

namespace Setting

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : Setting G M X n)
include S

theorem card_blockU_ge : 2 ^ (n - 2) ≤ Nat.card ↥(blockU X) := by
  obtain ⟨-, -, -, β, hβ, -, -⟩ := S.type
  have h1 : Nat.card (Multiplicative (altHeart n)) ≤ Nat.card ↥(blockU X) :=
    Nat.card_le_card_of_surjective β hβ
  have hn : 2 ≤ n ∧ Even n := by
    rcases S.n_mem with rfl | rfl | rfl <;> exact ⟨by norm_num, by decide⟩
  have h2 : Nat.card (Multiplicative (altHeart n)) = 2 ^ (n - 2) :=
    (Nat.card_congr Multiplicative.toAdd).trans
      (CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.card_altHeart_even hn.1 hn.2)
  omega

theorem sixteen_le_card_blockU : 16 ≤ Nat.card ↥(blockU X) := by
  have h := S.card_blockU_ge
  rcases S.n_mem with rfl | rfl | rfl <;> norm_num at h ⊢ <;> omega

theorem R_eq_inf : Rc X = CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (X : Set G) :=
  CFSG.CGT.Hall82.pCoreOf_centralizer_eq_inf S.normalizer_eq

theorem isTI_R : CFSG.CGT.Timmesfeld75.IsTI (Rc X) :=
  CFSG.CGT.Hall82.isTI_pCoreOf_centralizer S.maxLocal S.normalizer_eq S.uniq

theorem normalizer_R (hR : Rc X ≠ ⊥) : Subgroup.normalizer ((Rc X : Subgroup G) : Set G) = M :=
  CFSG.CGT.Hall82.normalizer_pCoreOf_centralizer_eq S.normalizer_eq S.uniq hR

theorem centralizer_le_of_mem_R {r : G} (hr : r ∈ Rc X) (hr1 : r ≠ 1) :
    Subgroup.centralizer ({r} : Set G) ≤ M :=
  CFSG.CGT.Hall82.centralizer_le_of_mem_pCoreOf S.uniq hr hr1

theorem mem_of_conj_le {g : G} (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ M) : g ∈ M :=
  CFSG.CGT.Hall82.mem_of_conj_le_of_isMaximalTwoLocal S.maxLocal S.uniq hg

theorem inCatalog_or_tight
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hSTT : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight) :
    CFSG.Assembly.InCatalog G ∨ Subgroup.centralizer (X : Set G) = ⊥ ∨
      (Rc X ≠ ⊥ ∧
        (∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (X : Set G) → P ≤ Rc X) ∧
        ((IsCyclic ↥(Rc X) ∧ Nat.card ↥(Rc X) = 4) ∨ CFSG.Open.IsElemAbelian 2 (Rc X)) ∧
        ∃ g : G, CFSG.CGT.Timmesfeld75.conjSubgroup g (Rc X) ≤ M ∧
          CFSG.CGT.Timmesfeld75.conjSubgroup g (Rc X) ≠ Rc X) :=
  CFSG.CGT.Hall82.inCatalog_or_tight hNode hSTT S.simple S.nonab S.kProper S.charTwo S.maxLocal
    S.normalizer_eq S.uniq S.elemU (by have := S.sixteen_le_card_blockU; omega)

end Setting

end CFSG.RankThree.PartTwo.Sec19.SolEven
