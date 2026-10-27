module

public import CFSG.Milestones.ASVolI.F45.ExcDefs
public import CFSG.Milestones.ASVolI.F45.Lie
public import CFSG.Milestones.ASVolI.F45.TitsModel

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF CFSG.Quasithin.F7

section OPPrime

variable {G : Type} [Group G]

theorem burnsideF45_oPPrime_le (p : ℕ) (H : Subgroup G) : oPPrime p H ≤ H :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem burnsideF45_le_oPPrime {p : ℕ} (hp : p.Prime) {H : Subgroup G} (hH : IsPGroup p H) :
    H ≤ oPPrime p H := by
  intro x hx
  apply Subgroup.subset_closure
  refine ⟨hx, ?_⟩
  obtain ⟨k, hk⟩ := hH ⟨x, hx⟩
  have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk')
  exact ⟨j, hj⟩

end OPPrime


theorem burnsideF45_excKind_Tits : burnsideF45_ExcKind .Tits := by
  intro p f E _ Gp M₁ M₂ hyp
  have T := burnsideF45_titsData hyp
  obtain ⟨hp2, hf1, -⟩ := hyp.model
  subst hp2
  subst hf1
  have hGp : Gp = ⊤ := hyp.canonical (Or.inr rfl)
  haveI : Finite E := hyp.finite
  have hp : Nat.Prime 2 := Nat.prime_two
  have hm : 3 ≤ GLKind.Tits.m := burnsideF45_three_le_m _
  have hP := burnsideF45_parabolics hyp.toHypF_4_4g
  have hN : (burnsideF45_setting hyp hp hm).N = ⊤ := by
    show Gp.comap (toE (incl M₁ M₂)) = ⊤
    rw [hGp, Subgroup.comap_top]
  have hQb : ∀ u, (burnsideF45_setting hyp hp hm).Qbar u = pCoreOf 2 (stv (incl M₁ M₂) u) := by
    intro u
    show pCoreOf 2 ((burnsideF45_setting hyp hp hm).N ⊓ stv (incl M₁ M₂) u) = _
    rw [hN, top_inf_eq]
  have hQ : ∀ u, Qu 2 Gp (incl M₁ M₂) u = pCoreOf 2 (stv (incl M₁ M₂) u) := fun u =>
    (burnsideF45_Qu_eq_Qbar hyp hp hm u).trans (hQb u)
  have hxl : (incl M₁ M₂).graph.Adj (incl M₁ M₂).xv (incl M₁ M₂).lv := CosetGeom.adj_γ₀_γ₁
  have hpB : IsPGroup 2 ↥(stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) (incl M₁ M₂).lv) :=
    T.isPGroup_borel
  have hpB' :
      IsPGroup 2 ↥(stv (incl M₁ M₂) (incl M₁ M₂).lv ⊓ stv (incl M₁ M₂) (incl M₁ M₂).xv) := by
    rw [inf_comm]
    exact hpB
  refine ⟨?_, ?_, ?_⟩
  ·
    have hx : burnsideF45_C6cd 2 Gp M₁ M₂ (incl M₁ M₂).xv (incl M₁ M₂).lv := by
      refine ⟨fun w₁ hw₁ w₂ hw₂ => ?_, fun g hg w hw hgw => ?_⟩
      · obtain ⟨g, hg, hgw⟩ := T.six_x_trans hw₁.1 hw₁.2 hw₂.1 hw₂.2
        exact ⟨g, burnsideF45_le_oPPrime hp hpB hg, hgw⟩
      · rw [hQ]
        exact T.six_x_free (burnsideF45_oPPrime_le 2 _ hg) hw.1 hw.2 hgw
    have hl : burnsideF45_C6cd 2 Gp M₁ M₂ (incl M₁ M₂).lv (incl M₁ M₂).xv := by
      refine ⟨fun w₁ hw₁ w₂ hw₂ => ?_, fun g hg w hw hgw => ?_⟩
      · obtain ⟨g, hg, hgw⟩ := T.six_l_trans hw₁.1 hw₁.2 hw₂.1 hw₂.2
        exact ⟨g, burnsideF45_le_oPPrime hp hpB' hg, hgw⟩
      · rw [hQ]
        exact T.six_l_free (burnsideF45_oPPrime_le 2 _ hg) hw.1 hw.2 hgw
    exact fun u v huv => burnsideF45_C6_of_base hyp hp hm hP hx hl huv
  ·
    refine ⟨T.transX, T.transL, T.line_orbits, ?_⟩
    intro v hv q₁ hq₁ hq₁v q₂ hq₂ hq₂v hne r₁ hr₁ hr₁v r₂ hr₂ hr₂v hne'
    exact T.line_two_trans_paths hv hq₁ hq₁v hq₂ hq₂v hne hr₁ hr₁v hr₂ hr₂v hne'
  ·
    intro u v huv
    refine ⟨fun hu => ?_, fun hu => Or.inl (T.nine_point huv hu)⟩
    rw [hQ]
    exact T.nine_line (fun w hw q hq =>
      (burnsideF45_C6_abe hyp hp hm hP hxl.symm).2.1 w hw q (by rwa [hQ])) huv hu

end CFSG.ASVolI
