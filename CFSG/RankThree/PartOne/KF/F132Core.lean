module

public import CFSG.RankThree.PartOne.KF.F132Gen
public import CFSG.RankThree.PartOne.KF.LayerFrame

public section

namespace CFSG.RankThree.PartOne

theorem Sec12Hyp.L_le_centralizer {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) : L ≤ Subgroup.centralizer ({c} : Set G) := by
  obtain ⟨L', -, hL'⟩ := h.L_mem.2
  rw [← hL']
  exact Subgroup.map_subtype_le _

end CFSG.RankThree.PartOne

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.RankThree.PartOne CFSG.Assembly.LowTwoRank

theorem exists_reflection_of_core
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hEA : E = A) (hcL : c ∉ L) {b : G} {K : Subgroup G}
    (hd : LayerCore p A L b K) {g : ℕ} (hg3 : 3 ≤ g)
    (hmodel : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSL 2 2 g) :
    ∃ t : MulAut E, t ∈ torusImage E L ∧ IsAutReflection p E t ∧
      (∀ hbE : b ∈ E, ((t ⟨b, hbE⟩ : E) : G) = b) ∧ KFAt p E g t ∧ kZero p E t = K := by
  obtain ⟨hbA, hbL, hb1⟩ := hd.b_mem
  have hbE : b ∈ E := hEA ▸ hbA
  have hK := hd.K_eq
  subst hK
  have hZ : Subgroup.center ↥(kLayer L b) = ⊥ :=
    psl2EvenCenterTrivial_of_multipliers hGA hg3 hd.K_qs hmodel
  have hAK : Nat.card ↥(E ⊓ kLayer L b) = p := by rw [hEA]; exact hd.A_K
  have hE3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  obtain ⟨t, htL, hrefl, hfix, -, hKF, hKz⟩ := exists_reflection_of_layer h hE3
    h.L_le_centralizer hcL hbE hbL hb1 hAK hmodel hZ
  exact ⟨t, htL, hrefl, fun _ => hfix, hKF, hKz⟩

end CFSG.RankThree.PartOne.KF132
