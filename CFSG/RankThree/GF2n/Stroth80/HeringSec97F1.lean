module

public import CFSG.RankThree.GF2n.Stroth80.CarterSec97Good
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RTwo

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

@[expose] def FourBase (M Q B Y : Subgroup G) : Prop :=
  ∀ F : Subgroup G, IsConjB M B F → F ≤ QB B → GoodPt M Q B Y F

theorem conj_inv_eq_of_conj_eq {g : G} {Y : Subgroup G} (h : conjSubgroup g Y = Y) :
    conjSubgroup g⁻¹ Y = Y := by
  calc conjSubgroup g⁻¹ Y = conjSubgroup g⁻¹ (conjSubgroup g Y) := by rw [h]
    _ = conjSubgroup (g⁻¹ * g) Y := (conjSubgroup_mul _ _ _).symm
    _ = Y := by rw [inv_mul_cancel, conjSubgroup_one]

theorem conj_Y_eq_of_goodPt (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y) (h1 : OneConcl hc X Y) {s : G} (hsM : s ∈ M)
    (hgood : GoodPt M Q B Y (conjSubgroup s B)) : conjSubgroup s Y = Y := by
  obtain ⟨g, hg, hgY, hgL⟩ := hgood
  have hQ : ∀ m ∈ M, conjSubgroup m Q = Q := fun m hm => hc.conj_Q_eq hm
  rw [LB_conjSubgroup M Q B hQ hsM] at hgL
  have hn : conjSubgroup (s⁻¹ * g) (LB M Q B) = LB M Q B := by
    rw [conjSubgroup_mul, hgL, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hnM : s⁻¹ * g ∈ M := M.mul_mem (M.inv_mem hsM) hg
  have hnY := conj_Y_eq_of_normalizes_LB h34 hc hs hsplit h4 h1 hnM hn
  have hnY' : conjSubgroup (s⁻¹ * g)⁻¹ Y = Y := conj_inv_eq_of_conj_eq hnY
  calc conjSubgroup s Y = conjSubgroup (g * (s⁻¹ * g)⁻¹) Y := by
        rw [show g * (s⁻¹ * g)⁻¹ = s by group]
    _ = conjSubgroup g (conjSubgroup (s⁻¹ * g)⁻¹ Y) := conjSubgroup_mul _ _ _
    _ = Y := by rw [hnY', hgY]

theorem fourConcl_of_base (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y) (h1 : OneConcl hc X Y) (hbase : FourBase M Q B Y) :
    FourConcl M Q B Y := by
  intro S F hS hF hgoodS hFS
  have hQ : ∀ m ∈ M, conjSubgroup m Q = Q := fun m hm => hc.conj_Q_eq hm
  obtain ⟨s, hsM, rfl⟩ := hS
  obtain ⟨f, hfM, rfl⟩ := hF
  have hsY := conj_Y_eq_of_goodPt h34 hc hs hsplit h4 h1 hsM hgoodS
  have hF'conj : IsConjB M B (conjSubgroup (s⁻¹ * f) B) :=
    ⟨s⁻¹ * f, M.mul_mem (M.inv_mem hsM) hfM, rfl⟩
  have hF'le : conjSubgroup (s⁻¹ * f) B ≤ QB B := by
    have h1' : conjSubgroup s⁻¹ (conjSubgroup f B) ≤
        conjSubgroup s⁻¹ (conjSubgroup s (QB B)) := by
      rw [← QB_conj]
      exact Subgroup.map_mono hFS
    have e : conjSubgroup s⁻¹ (conjSubgroup s (QB B)) = QB B := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    rw [e, ← conjSubgroup_mul] at h1'
    exact h1'
  obtain ⟨g', hg', hg'Y, hg'L⟩ := hbase _ hF'conj hF'le
  refine ⟨s * g', M.mul_mem hsM hg', ?_, ?_⟩
  · rw [conjSubgroup_mul, hg'Y, hsY]
  · have hF : conjSubgroup f B = conjSubgroup s (conjSubgroup (s⁻¹ * f) B) := by
      rw [← conjSubgroup_mul, mul_inv_cancel_left]
    rw [conjSubgroup_mul, hg'L, hF, LB_conjSubgroup M Q _ hQ hsM]

theorem goodPt_of_conj_mem_LB (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) (h1 : OneConcl hc X Y)
    {h : G} (hh : h ∈ M) {x : G} (hx : x ∈ LB M Q B ⊓ X) (hxQ : x ∉ Q)
    (hhx : h * x * h⁻¹ ∈ LB M Q B) : GoodPt M Q B Y (conjSubgroup h B) :=
  goodPt_conj_of_mem M Q B Y (fun m hm => hc.conj_Q_eq hm) hh
    (conj_Y_eq_of_conj_mem_LB h34 h311a hc hs hsplit h4 h1 hx hxQ hh hhx)

theorem goodPt_of_mem_conj_LB (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) (h1 : OneConcl hc X Y)
    {h : G} (hh : h ∈ M) {x : G} (hx : x ∈ LB M Q B ⊓ X) (hxQ : x ∉ Q)
    (hxh : x ∈ conjSubgroup h (LB M Q B)) : GoodPt M Q B Y (conjSubgroup h B) := by
  have hmem : h⁻¹ * x * h⁻¹⁻¹ ∈ LB M Q B := by
    rw [inv_inv]
    exact mem_conjSubgroup.mp hxh
  have hY := conj_Y_eq_of_conj_mem_LB h34 h311a hc hs hsplit h4 h1 hx hxQ (M.inv_mem hh) hmem
  exact goodPt_conj_of_mem M Q B Y (fun m hm => hc.conj_Q_eq hm) hh
    (by
      have := conj_inv_eq_of_conj_eq hY
      rwa [inv_inv] at this)

end HS9

@[expose] def Sec97FourHardStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
      HS9.OneConcl hc X Y → HS9.TwoConcl M Q B X → HS9.ThreeConcl M Q B X →
      ∀ h ∈ M, conjSubgroup h B ≤ QB B →
        (∀ x ∈ LB M Q B ⊓ X, x ∉ Q →
          h * x * h⁻¹ ∉ LB M Q B ∧ x ∉ conjSubgroup h (LB M Q B)) → False

theorem sec97Four_of_hard (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hHard : Sec97FourHardStatement) : Sec97FourStatement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit h4 h1 h2 h3
  refine HS9.fourConcl_of_base h34 hc hs hsplit h4 h1 ?_
  rintro F ⟨h, hh, rfl⟩ hFB
  by_cases hex : ∃ x ∈ LB M Q B ⊓ X, x ∉ Q ∧
      (h * x * h⁻¹ ∈ LB M Q B ∨ x ∈ conjSubgroup h (LB M Q B))
  · obtain ⟨x, hx, hxQ, hor⟩ := hex
    rcases hor with hxh | hxh
    · exact HS9.goodPt_of_conj_mem_LB h34 h311a hc hs hsplit h4 h1 hh hx hxQ hxh
    · exact HS9.goodPt_of_mem_conj_LB h34 h311a hc hs hsplit h4 h1 hh hx hxQ hxh
  · push Not at hex
    exact (hHard G M Q Z B hc n t hs X Y hsplit h4 h1 h2 h3 h hh hFB
      fun x hx hxQ => hex x hx hxQ).elim

end CFSG.RankThree.GF2n.Stroth80
