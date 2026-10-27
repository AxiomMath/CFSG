module

public import CFSG.Quasithin.Recognition.F112Crit.Setting
public import CFSG.Quasithin.Recognition.F112Crit.SmallVertex
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem centerOf_le_pCoreOf_of_charTwo {X : Subgroup G} (hX : CharTwo X) :
    centerOf X ≤ pCoreOf 2 X := fun _ hz =>
  hX ⟨hz.1, Subgroup.centralizer_le (Subgroup.map_subtype_le _) hz.2⟩

private theorem omegaOneOf_ne_bot_of_isPGroup {Y : Subgroup G} (hY : IsPGroup 2 Y) (hne : Y ≠ ⊥) :
    omegaOneOf Y ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hY.exists_card_eq
  have h2 : 2 ∣ Nat.card Y := by
    rcases n with _ | n
    · exact absurd (Subgroup.eq_bot_of_card_eq Y (by simpa using hn)) hne
    · rw [hn, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hy2' : (y : G) ^ 2 = 1 := by simpa using congrArg Subtype.val hy2
  intro hbot
  have hmem : (y : G) ∈ omegaOneOf Y := Subgroup.subset_closure ⟨y.2, hy2'⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have hy1 : y = 1 := Subtype.ext hmem
  rw [hy1, orderOf_one] at hy
  exact absurd hy (by norm_num)

theorem le_centralizer_omegaOneCenterOf (X : Subgroup G) :
    X ≤ Subgroup.centralizer (omegaOneCenterOf X : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz' : z ∈ centerOf X := A4.omegaOneCenterOf_le_centerOf _ hz
  exact (Subgroup.mem_centralizer_iff.mp hz'.2 x hx).symm

theorem P₂_swap_eq (L1 L2 S : Subgroup G) : P₂ L2 L1 S = L1 ⊔ S ⊔ borelOf L2 S := by
  simp only [P₂, bigB]
  apply le_antisymm
  · exact sup_le (le_sup_left.trans le_sup_left) (sup_le (sup_le le_sup_right
      ((F1.borelOf_le L1 S).trans (le_sup_left.trans le_sup_left))) (le_sup_right.trans le_sup_left))
  · exact sup_le (sup_le le_sup_left (le_sup_right.trans le_sup_right))
      (le_sup_left.trans (le_sup_left.trans le_sup_right))

theorem setting_of_fdBig (hH : F112Hyp L1 L2 S) (hFD : VFD L2)
    (hc : centerOf (L1 ⊔ S ⊔ borelOf L2 S) ≠ ⊥) (hS : S ≤ L2) :
    Setting L2 L1 S (omegaOneCenterOf (L1 ⊔ S ⊔ borelOf L2 S)) := by
  have hR : Hyp111R L2 L1 S := Hyp111R.of_hyp111 rankOneListedFacts hH.1.symm
  have hP : P₂ L2 L1 S = L1 ⊔ S ⊔ borelOf L2 S := P₂_swap_eq L1 L2 S
  have hSyl : IsSylowTwoOf S (L1 ⊔ S ⊔ borelOf L2 S) := by
    rw [← hP]
    exact F112W.isSylowTwoOf_parabolic' hR
  have hZS : centerOf (L1 ⊔ S ⊔ borelOf L2 S) ≤ S :=
    (centerOf_le_pCoreOf_of_charTwo hH.1.h1.charTwo).trans
      (pCoreOf_two_le_of_isSylowTwoOf hSyl)
  have hcard := card_oTwoQuot_of_vFD hFD
  exact
    { hyp := hR
      S_le := hS
      ne_bot := omegaOneOf_ne_bot_of_isPGroup (hH.1.h1.pgroup.to_le hZS) hc
      isElemAbelian := ⟨⟨⟨fun x y => Subtype.ext (A4.mul_comm_of_mem_omegaOneCenterOf x.2 y.2)⟩⟩,
        fun _ hx => A4.sq_eq_one_of_mem_omegaOneCenterOf hx⟩
      le_S := (A4.omegaOneCenterOf_le_centerOf _).trans hZS
      centralizes := hP ▸ le_centralizer_omegaOneCenterOf _
      prime := by rw [relIndex_borelOf_eq_five hR hcard]; norm_num
      cyclic := isCyclic_of_vFD hFD }

end CFSG.Quasithin.F112Crit

end
