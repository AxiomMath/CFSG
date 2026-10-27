module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93AC2
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93AC1
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93XH

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix MatrixGroups

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

omit [Finite G] in
theorem exists_sl2_hom {X F : Subgroup G} {q : ℕ} (hq : QuotSat X F (IsSLModel 2 q)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (π : ↥X →* SL(2, K)),
      Nat.card K = q ∧ Function.Surjective π ∧ ∀ x : ↥X, π x = 1 ↔ (x : G) ∈ F := by
  obtain ⟨hN, K, hKF, hKFin, hKcard, ⟨e⟩⟩ := hq
  haveI := hN
  let e' : (↥X ⧸ F.subgroupOf X) ≃* SL(2, K) :=
    e.trans (specialLinearGroupEquivStatedSL 2 K).symm
  refine ⟨K, hKF, hKFin, e'.toMonoidHom.comp (QuotientGroup.mk' (F.subgroupOf X)), hKcard, ?_, ?_⟩
  · exact e'.surjective.comp (QuotientGroup.mk'_surjective _)
  · intro x
    show e' (QuotientGroup.mk' (F.subgroupOf X) x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]

theorem exists_cover_of_line (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {h : G} (hh : h ∈ M)
    (hne : LB M Q B ≠ conjSubgroup h (LB M Q B)) (hline : LineGeom M Q Z B h) :
    ∃ w ∈ Xhat M Q B h, conjSubgroup w (LB M Q B) = conjSubgroup h (LB M Q B) ∧
      ∀ y ∈ Xhat M Q B h, y ∈ Subgroup.normalizer (LB M Q B : Set G) ∨
        ∃ ε ∈ LB M Q B, (ε * w)⁻¹ * y ∈ Subgroup.normalizer (LB M Q B : Set G) := by
  obtain ⟨w, hwX, hw⟩ := exists_swap_of_line h34 hs hh hne hline
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  refine ⟨w, hwX, hw, fun y hy => ?_⟩
  have hy' : y ∈ LB M Q B ⊔ LB M Q (conjSubgroup h B) := by
    rw [hLconj]
    exact hy
  rcases line_orbit_of_geom hc hh hline y hy' with h1 | ⟨ε, hε, h2⟩
  · exact Or.inl (conjSubgroup_eq_self_iff.mp h1)
  · right
    refine ⟨ε, hε, ?_⟩
    rw [hLconj, ← hw, ← conjSubgroup_mul] at h2
    exact conjSubgroup_eq_conjSubgroup_iff.mp h2.symm

theorem normalizer_inf_le_Fhat_and_relIndex (h34 : Stroth34Statement) {hc : Ctx M Q Z B}
    {n : ℕ} {t r : G} {Z0 : Subgroup G} {h : G} (cfg : Cfg93c hc n t r Z0 h)
    (hq : QuotSat (Xhat M Q B h) (Fhat M Q B h) (IsSLModel 2 (Nat.card Z)))
    (hline : LineGeom M Q Z B h) :
    (∀ y ∈ LB M Q B, y ∈ Subgroup.normalizer (conjSubgroup h (LB M Q B) : Set G) →
        y ∈ Fhat M Q B h) ∧
      (Fhat M Q B h).relIndex (LB M Q B) = Nat.card Z := by
  classical
  have hh := cfg.hh
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  obtain ⟨K, hKF, hKFin, π, hKcard, hsurj, hker⟩ := exists_sl2_hom hq
  letI := hKF
  letI := hKFin
  obtain ⟨⟨e, he⟩, hq4⟩ := card_Z_facts hc
  have hKe : Nat.card K = 2 ^ e := hKcard.trans he
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow hKe
  have h4K : 4 ≤ Nat.card K := by rw [hKcard]; exact hq4
  obtain ⟨w, hwX, -, hcov⟩ := exists_cover_of_line h34 cfg.hs.toSec5 hh cfg.hne hline
  have hL2 : IsPGroup 2 ↥(LB M Q B) := isPGroup_LB_of_ctx hc
  have hL'2 : IsPGroup 2 ↥(conjSubgroup h (LB M Q B)) := by
    have := isPGroup_LB_of_ctx hc'
    rwa [hLconj] at this
  obtain ⟨h1, h2⟩ := sl2_bridge (L := LB M Q B) (L' := conjSubgroup h (LB M Q B))
    (F := Fhat M Q B h) (X := Xhat M Q B h) rfl h4K ⟨e, hKe⟩ hL2 hL'2 π hsurj hker hwX hcov
  refine ⟨h1, le_antisymm (relIndex_Fhat_le hc hq) ?_⟩
  rwa [hKcard] at h2

theorem card_LB_sup_Fhat_eq (h34 : Stroth34Statement) {hc : Ctx M Q Z B}
    {n : ℕ} {t r : G} {Z0 : Subgroup G} {h : G} (cfg : Cfg93c hc n t r Z0 h)
    (hq : QuotSat (Xhat M Q B h) (Fhat M Q B h) (IsSLModel 2 (Nat.card Z)))
    (hline : LineGeom M Q Z B h) :
    Nat.card ↥(LB M Q B ⊔ Fhat M Q B h) = Nat.card ↥(Fhat M Q B h) * Nat.card Z := by
  have hrel := (normalizer_inf_le_Fhat_and_relIndex h34 cfg hq hline).2
  have hLn : LB M Q B ≤ Subgroup.normalizer (Fhat M Q B h : Set G) :=
    (le_sup_left : LB M Q B ≤ Xhat M Q B h).trans (le_normalizer_pCoreIn _)
  have h1 := relIndex_mul_card_eq_card_sup hLn
  rw [hrel] at h1
  rw [← h1]
  ring

end HS9

end CFSG.RankThree.GF2n.Stroth80
