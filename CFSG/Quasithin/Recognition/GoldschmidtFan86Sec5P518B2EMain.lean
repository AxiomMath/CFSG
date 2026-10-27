module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2ESwap
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Set

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem eBallStab_le_nbr_inf {v β : V} (hβ : Γ.Adj v β) :
    ballStab Γ G 2 v ≤ nbrStab Γ G v ⊓ nbrStab Γ G β := by
  intro g hg
  refine ⟨fun w hw => hg w ?_, fun w hw => hg w (eDist_le_two hβ hw)⟩
  have h1 : Γ.dist v w ≤ 1 := (SimpleGraph.dist_eq_one_iff_adj.2 hw).le
  show Γ.dist v w ≤ 2
  omega

theorem eExists_nbrStab_inf_not_ballStab (S : B2Set F L T a) {v β : V} (hβ : Γ.Adj v β)
    {x : G} (hx : x ∈ MulAction.stabilizer G v) (hxo : orderOf x = valence Γ v) :
    ∃ q ∈ nbrStab Γ G v ⊓ nbrStab Γ G β, q ∉ ballStab Γ G 2 v := by
  obtain ⟨h1, h2, h3⟩ := S.h33 v β hβ x hx hxo
  have hnp : ¬ SingLe Γ G 3 := (singGe_succ_iff 3).1 S.h40
  have hpc : ¬ PClosed Γ G v := fun hpc => hnp (h3 hpc)
  have hne : ¬ (nbrStab Γ G v ⊓ nbrStab Γ G β = ballStab Γ G 2 v) :=
    fun h => hpc (h2.1 (h1.1 h))
  by_cases hcase : nbrStab Γ G v ⊓ nbrStab Γ G β ≤ ballStab Γ G 2 v
  · exact absurd (le_antisymm hcase (eBallStab_le_nbr_inf hβ)) hne
  · exact IsConcreteLE.not_le_iff_exists.1 hcase

theorem eLayer (S : B2Set F L T a) {x : G} (hx : x ∈ MulAction.stabilizer G (xv T a 6))
    (hxo : orderOf x = 5) :
    ∃ q ∈ nbrStab Γ G (xv T a 6), x * q * x⁻¹ * q⁻¹ ∉ ballStab Γ G 2 (xv T a 6) := by
  have hv : valence Γ (xv T a 6) = 5 := by simpa using S.val_even 3
  have hxv : x • xv T a 6 = xv T a 6 := MulAction.mem_stabilizer_iff.1 hx
  obtain ⟨β, hβ⟩ := F.exists_adj (xv T a 6)
  obtain ⟨q, hq, hqn⟩ := eExists_nbrStab_inf_not_ballStab S hβ hx (by rw [hxo, hv])
  refine ⟨q, hq.1, fun hmem => ?_⟩
  have hqfix : q • xv T a 6 = xv T a 6 := F.nbrStab_le_stabilizer _ hq.1
  have hmv : ∃ w, Γ.dist (xv T a 6) w ≤ 2 ∧ q • w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact hqn (fun w hw => hcon w hw)
  obtain ⟨w, hw2, hqw⟩ := hmv
  have hβ' : ∃ β', Γ.Adj (xv T a 6) β' ∧ EMoves Γ q (xv T a 6) β' := by
    have hcases : Γ.dist (xv T a 6) w = 0 ∨ Γ.dist (xv T a 6) w = 1 ∨
        Γ.dist (xv T a 6) w = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · exfalso
      have : xv T a 6 = w := (F.isTree.connected.dist_eq_zero_iff).1 h0
      subst this
      exact hqw hqfix
    · exfalso
      exact hqw (hq.1 w (SimpleGraph.dist_eq_one_iff_adj.1 h1))
    · obtain ⟨u, hu1, hu2⟩ := eExists_mid F h2
      refine ⟨u, hu1, w, hu2, ?_, hqw⟩
      rintro rfl
      simp at h2
  obtain ⟨β', hβ'adj, hβ'm⟩ := hβ'
  obtain ⟨n, hn⟩ := eExists_pow_nbr F hv hx hxo hβ'adj hβ
  have hm := eMoves_pow F hxv hβ'adj hmem hβ'm n
  rw [hn] at hm
  obtain ⟨w', hw'adj, -, hw'q⟩ := hm
  exact hw'q (hq.2 w' hw'adj)

end P518

end CFSG.Quasithin.Fan86
