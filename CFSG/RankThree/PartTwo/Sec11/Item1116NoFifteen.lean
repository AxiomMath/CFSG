module

public import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Main

@[expose] def Item11131 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g →
      KFacts.InducesStdKind Y c .field →
        Subgroup.zpowers c = Subgroup.zpowers s ⊓ Subgroup.centralizer {a}

namespace Item1116NoFifteen

variable {G : Type} [Group G] [Finite G]

theorem R_eq_of_closure_eq {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G}
    {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) :
    R = Subgroup.closure {a, x, s} := by
  rw [h.R_eq]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy <;> rw [hy]
    · have hr : r ∈ Subgroup.closure ({a, s} : Set G) := by
        rw [← hrs]
        exact Subgroup.subset_closure (by simp)
      refine (Subgroup.closure_le _).mpr ?_ hr
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz <;> rw [hz] <;> exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy <;> rw [hy]
    · have ha : a ∈ Subgroup.closure ({r, s} : Set G) := by
        rw [hrs]
        exact Subgroup.subset_closure (by simp)
      refine (Subgroup.closure_le _).mpr ?_ ha
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz <;> rw [hz] <;> exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

theorem commute_s_a_of_closure_eq (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) : s * a = a * s := by
  by_contra hsa
  have h₂ : Sec11Data G A c L a R Y d x s a g :=
    { h with
      R_eq := R_eq_of_closure_eq h hrs
      a_mem_closure := Subgroup.subset_closure (by simp) }
  have hag : a * g = g * a :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y h.g_mem.1)).symm
  exact Item1115Proof.false_of_mem_zpowers h45 h113 h117 h₂ (Subgroup.mem_zpowers a) hag hsa

theorem lt_orderOf_x_of_ne_zpowers (h45 : Sec4.Item4_5) (h118 : Item118) (h119 : Item119)
    (hCB : CentBound119) {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G}
    {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (h1131 : KFacts.InducesStdKind Y c .field →
      Subgroup.zpowers c = Subgroup.zpowers s ⊓ Subgroup.centralizer {a})
    (hsc : Subgroup.zpowers s ≠ Subgroup.zpowers c) (hsa : s * a = a * s) : 9 < orderOf x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnf : ¬ KFacts.InducesStdKind Y c .field := by
    intro hf
    apply hsc
    rw [h1131 hf, inf_of_le_left (Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr hsa))]
  have hbar := Item1116Proof.exists_isList119_of_not_field h45 h119 h hnf
  obtain ⟨hRc, hRL⟩ := Item1116Proof.le_centralizer_and_normalizer h45 h
  have hsR : s ∈ R := (Item1116Proof.mem_R h).2.2
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp h.mem_partTwoF.1 h.a_mem
      h.a_ne_one Y h.mem_thetaComponentsAt_Y
  obtain ⟨-, -, hd1⟩ := h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq
  have hdK := h.toSec11Std.d_mem_sec11K h.inf_eq
  have hK1 : sec11K L a ≠ ⊥ := fun hb => hd1 (by rw [hb, Subgroup.mem_bot] at hdK; exact hdK)
  have hsY : s ∈ Subgroup.normalizer (Y : Set G) :=
    h.toSec11Std.mem_normalizer_Y hK1 (hRL hsR) hsa
  have hsC : s ∈ Sec4.thetaQuotCentralizer L := by
    have h1 : s ∈ Subgroup.zpowers s := Subgroup.mem_zpowers s
    rw [← h.inf_centralizer_eq] at h1
    exact h1.2
  have hm := hCB G Y (sec11K L a) c s hbar (hAY h.mem_A) (h.mem_partTwoF.1.2 c h.mem_A)
    (mem_thetaComponentsIn_sec11K_inf h.toSec11Std)
    (kType119 G A c L a R Y h.toSec11Std d h.inf_eq h.closure_eq) hsY
    (Item1116Proof.exists_pow_eq_one_of_mem h hsR)
    (Subgroup.mem_centralizer_singleton_iff.mp (hRc hsR))
    (Item1116Proof.commutator_mem_theta_sec11K (hRL hsR) hsa hsC)
  have hs1 := Item1116Proof.eq_one_of_mem_zpowers_s_of_not_mem h
    (Item1116Proof.c_not_mem_thetaQuotCentralizer h118 h)
    (Subgroup.pow_mem _ (Subgroup.mem_zpowers s) _) hm
  have hle : orderOf s ≤ 3 ^ (Nat.card (sec11K L a)).factorization 3 :=
    Nat.le_of_dvd (by positivity) (orderOf_dvd_of_pow_eq_one hs1)
  exact lt_of_le_of_lt ((Item1116Proof.nine_le_orderOf_s h hsc).trans hle)
    (Item1116Proof.ordProj_card_sec11K_lt h)

end Item1116NoFifteen

theorem item1116_of_item11131 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h11131 : Item11131) (h118 : Item118) (h119 : Item119) (hCB : CentBound119) : Item1116 := by
  intro G _ _ A c L a R Y d x s r g h hor
  by_cases hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}
  · have hsc : Subgroup.zpowers s ≠ Subgroup.zpowers c := by
      rcases hor with hsc | hrs'
      · exact hsc
      · exact absurd hrs hrs'
    exact Item1116NoFifteen.lt_orderOf_x_of_ne_zpowers h45 h118 h119 hCB h
      (h11131 G A c L a R Y d x s r g h) hsc
      (Item1116NoFifteen.commute_s_a_of_closure_eq h45 h113 h117 h hrs)
  · exact item1116_of_ne_closure h45 G A c L a R Y d x s r g h hrs

end Main

end CFSG.RankThree.PartTwo.Sec11
