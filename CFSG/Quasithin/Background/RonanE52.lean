module

public import CFSG.Quasithin.Background.RonanE52Member
public import CFSG.Quasithin.Background.RonanE52FrattiniMain
public import CFSG.Quasithin.Background.E1Param

public section

namespace CFSG.Quasithin.RonanE52

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem e5_2 {P : Subgroup G} {i j : ℕ} (hj : 0 < j) (hP : IsSylowIn 2 P ⊤)
    (hn : E1.nParam (⊤ : Subgroup G) = (j : ℕ∞)) (hlt : i + j < CFSG.Open.twoRank G)
    {D : Subgroup G} (hD : D = omegaOneCenterOf (thompsonJi P (i + j))) :
    Subgroup.normalizer (thompsonJi P i : Set G) ⊔
      (⨆ (D₁ : Subgroup G) (_ : D₁ ≤ D ∧ E3.mQuot D D₁ ≤ i + j),
        thompsonJi (Subgroup.centralizer (D₁ : Set G)) i) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrk : CFSG.Open.pRank 2 P = CFSG.Open.pRank 2 (⊤ : Subgroup G) :=
    pRank_eq_top_of_isSylow hP
  have hnm : i + j < CFSG.Open.pRank 2 P := by
    rw [hrk]
    exact hlt
  have him : i < CFSG.Open.pRank 2 P := lt_of_le_of_lt (Nat.le_add_right i j) hnm
  have hJeq : thompsonJi P (i + j) = H13.thompsonJk (i + j) P :=
    VolI.E54.thompsonJi_eq_thompsonJk hnm
  have hDeq : D = omegaOneCenterOf (H13.thompsonJk (i + j) P) := by rw [hD, hJeq]
  set G₀ : Subgroup G := Subgroup.normalizer (thompsonJi P i : Set G) ⊔
    (⨆ (D₁ : Subgroup G) (_ : D₁ ≤ D ∧ E3.mQuot D D₁ ≤ i + j),
      thompsonJi (Subgroup.centralizer (D₁ : Set G)) i) with hG₀
  have hPG : P ≤ G₀ := by
    have h1 : thompsonJi P i = H13.thompsonJk i P := VolI.E54.thompsonJi_eq_thompsonJk him
    have h2 : P ≤ Subgroup.normalizer (thompsonJi P i : Set G) := by
      rw [h1]
      exact E5.le_normalizer_thompsonJk i P
    exact h2.trans le_sup_left
  have hcent : ∀ D₁ : Subgroup G, D₁ ≤ omegaOneCenterOf (H13.thompsonJk (i + j) P) →
      Nat.card ↥(omegaOneCenterOf (H13.thompsonJk (i + j) P)) ≤ 2 ^ (i + j) * Nat.card ↥D₁ →
      Subgroup.centralizer (D₁ : Set G) ≤ G₀ := by
    intro D₁ hD₁ hcard
    have hD₁' : D₁ ≤ D := hDeq ▸ hD₁
    have hmQ : E3.mQuot D D₁ ≤ i + j := mQuot_le_of_card_le hD₁' (hDeq ▸ hcard)
    have hJC : thompsonJi P i ≤ Subgroup.centralizer (D₁ : Set G) := by
      have h1 : thompsonJi P i ≤ thompsonJi P (i + j) := thompsonJi_mono (Nat.le_add_right i j) hnm
      rw [hJeq] at h1
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact (mem_centralizer_of_mem_omegaOneCenterOf (hD₁ hd) (h1 hx)).symm
    have h1 := le_normalizer_sup_thompsonJi hP him hJC
    exact h1.trans (sup_le_sup_left (le_iSup₂_of_le
      (f := fun D₁ (_ : D₁ ≤ D ∧ E3.mQuot D D₁ ≤ i + j) =>
        thompsonJi (Subgroup.centralizer (D₁ : Set G)) i) D₁ ⟨hD₁', hmQ⟩ le_rfl) _)
  have hinE : E1.InE j (⊤ : Subgroup G) := (E1.nParam_le_iff hj).1 hn.le
  have hinFor : E1.InEFor j (⊤ : Subgroup G) P := hinE P hP
  set Ω : Set (Subgroup G) := {A | IsElemAbelianCorank (⊤ : Subgroup G) i A} with hΩdef
  have hΩ : E1.IsInvColl (⊤ : Subgroup G) Ω :=
    { le := fun A _ => le_top
      isElemAbelian := fun A hA => hA.2.1
      conj := fun A hA h _ => ⟨le_top, isElemAbelian_cjSub hA.2.1, by
        show Nat.card (cjSub h A) * 2 ^ i = _
        rw [card_cjSub]
        exact hA.2.2⟩ }
  have hwc : E1.weakClosure P Ω = thompsonJi P i := by
    unfold E1.weakClosure thompsonJi
    refine le_antisymm (iSup₂_le fun A hA => iSup_le fun hAP => ?_) (iSup₂_le fun A hA => ?_)
    · exact le_iSup₂_of_le A ⟨hAP, hA.2.1, by rw [hrk]; exact hA.2.2⟩ le_rfl
    · exact le_iSup₂_of_le A ⟨le_top, hA.2.1, by rw [← hrk]; exact hA.2.2⟩
        (le_iSup_of_le hA.1 le_rfl)
  have hEF := hinFor Ω hΩ
  rw [hwc] at hEF
  refine eq_top_iff.2 (hEF.ge.trans (sup_le ?_ (inf_le_right.trans le_sup_left)))
  refine iSup₂_le fun A hA => iSup_le fun hAP => iSup₂_le fun K hK => ?_
  have hA' : IsElemAbelianCorank P i A := ⟨hAP, hA.2.1, by rw [hrk]; exact hA.2.2⟩
  exact le_of_mem_E hP hA' hK hPG hcent

end CFSG.Quasithin.RonanE52
