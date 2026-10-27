module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec97F1

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

@[expose] def LineGeom (M Q Z B : Subgroup G) (h : G) : Prop :=
  (∀ x ∈ LB M Q B ⊔ LB M Q (conjSubgroup h B),
      conjSubgroup x (Z ⊔ B ⊔ conjSubgroup h B) = Z ⊔ B ⊔ conjSubgroup h B) ∧
    ∀ P : Subgroup G, IsConjB M B P → P ≤ Z ⊔ B ⊔ conjSubgroup h B →
      LB M Q P = LB M Q B ∨
        ∃ ε ∈ LB M Q B, LB M Q P = conjSubgroup ε (LB M Q (conjSubgroup h B))

theorem line_orbit_of_geom (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M) (hline : LineGeom M Q Z B h) :
    ∀ x ∈ LB M Q B ⊔ LB M Q (conjSubgroup h B),
      conjSubgroup x (LB M Q B) = LB M Q B ∨
        ∃ ε ∈ LB M Q B,
          conjSubgroup x (LB M Q B) = conjSubgroup ε (LB M Q (conjSubgroup h B)) := by
  intro x hx
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hxM : x ∈ M := (sup_le hc.LB_le_M hc'.LB_le_M) hx
  have hP : conjSubgroup x B ≤ Z ⊔ B ⊔ conjSubgroup h B := by
    calc conjSubgroup x B ≤ conjSubgroup x (Z ⊔ B ⊔ conjSubgroup h B) :=
          Subgroup.map_mono (le_sup_right.trans le_sup_left)
      _ = Z ⊔ B ⊔ conjSubgroup h B := hline.1 x hx
  have hLP : LB M Q (conjSubgroup x B) = conjSubgroup x (LB M Q B) := hc.LB_conj hxM
  have := hline.2 (conjSubgroup x B) ⟨x, hxM, rfl⟩ hP
  rw [hLP] at this
  exact this

theorem conj_E_eq_of_normalizes_LB {X : Subgroup G} (h2 : TwoConcl M Q B X) {n : G} (hn : n ∈ M)
    (hL : conjSubgroup n (LB M Q B) = LB M Q B) :
    conjSubgroup n (LB M Q B ⊓ X) = LB M Q B ⊓ X := by
  have hle : conjSubgroup n (LB M Q B ⊓ X) ≤ LB M Q B ⊓ X := by
    intro y hy
    have hx : n⁻¹ * y * n ∈ LB M Q B ⊓ X := mem_conjSubgroup.mp hy
    have hyL : y ∈ conjSubgroup n (LB M Q B) := by
      rw [mem_conjSubgroup]
      exact hx.1
    rw [hL] at hyL
    have e : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
    have hmem : n * (n⁻¹ * y * n) * n⁻¹ ∈ LB M Q B := by rw [e]; exact hyL
    have := h2 _ hx n hn hmem
    rwa [e] at this
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])

theorem isTIMod_of_line (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h2 : TwoConcl M Q B X) {h : G} (hh : h ∈ M)
    (hhard : ∀ x ∈ LB M Q B ⊓ X, x ∉ Q → h * x * h⁻¹ ∉ LB M Q B)
    (hline : LineGeom M Q Z B h) :
    IsTIMod (LB M Q B ⊔ LB M Q (conjSubgroup h B)) Q (LB M Q B ⊓ X) := by
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hQ : ∀ m ∈ M, conjSubgroup m Q = Q := fun m hm => hc.conj_Q_eq hm
  have hQX : Q ≤ X := hsplit.1.1
  have hQE : Q ≤ LB M Q B ⊓ X := le_inf le_sup_left hQX
  intro x hx
  have hxM : x ∈ M := (sup_le hc.LB_le_M hc'.LB_le_M) hx
  rcases line_orbit_of_geom hc hh hline x hx with hxL | ⟨ε, hε, hxε⟩
  · right
    rw [conj_E_eq_of_normalizes_LB h2 hxM hxL, inf_idem]
  · left
    have hεM : ε ∈ M := hc.LB_le_M hε
    have hεh : ε * h ∈ M := M.mul_mem hεM hh
    have hLF : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
    rw [hLF, ← conjSubgroup_mul] at hxε
    have hn : conjSubgroup ((ε * h)⁻¹ * x) (LB M Q B) = LB M Q B := by
      rw [conjSubgroup_mul, hxε, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    have hEn := conj_E_eq_of_normalizes_LB h2 (M.mul_mem (M.inv_mem hεh) hxM) hn
    have hEx : conjSubgroup x (LB M Q B ⊓ X) = conjSubgroup (ε * h) (LB M Q B ⊓ X) := by
      calc conjSubgroup x (LB M Q B ⊓ X)
          = conjSubgroup ((ε * h) * ((ε * h)⁻¹ * x)) (LB M Q B ⊓ X) := by
            rw [mul_inv_cancel_left]
        _ = conjSubgroup (ε * h) (conjSubgroup ((ε * h)⁻¹ * x) (LB M Q B ⊓ X)) :=
            conjSubgroup_mul _ _ _
        _ = conjSubgroup (ε * h) (LB M Q B ⊓ X) := by rw [hEn]
    rw [hEx]
    refine le_antisymm (fun y hy => ?_) (le_inf hQE (by
      calc Q = conjSubgroup (ε * h) Q := (hQ _ hεh).symm
        _ ≤ conjSubgroup (ε * h) (LB M Q B ⊓ X) := Subgroup.map_mono hQE))
    obtain ⟨hyE, hyc⟩ := Subgroup.mem_inf.mp hy
    by_contra hyQ
    have he : (ε * h)⁻¹ * y * (ε * h) ∈ LB M Q B ⊓ X := mem_conjSubgroup.mp hyc
    have heQ : (ε * h)⁻¹ * y * (ε * h) ∉ Q := by
      intro heQ
      apply hyQ
      have : y ∈ conjSubgroup (ε * h) Q := by
        rw [mem_conjSubgroup]
        exact heQ
      rwa [hQ _ hεh] at this
    have hεE : conjSubgroup ε (LB M Q B ⊓ X) = LB M Q B ⊓ X :=
      conj_E_eq_of_normalizes_LB h2 hεM (conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hε))
    have hy' : ε⁻¹ * y * ε ∈ LB M Q B ⊓ X := by
      have : y ∈ conjSubgroup ε (LB M Q B ⊓ X) := by rw [hεE]; exact hyE
      exact mem_conjSubgroup.mp this
    have e : h * ((ε * h)⁻¹ * y * (ε * h)) * h⁻¹ = ε⁻¹ * y * ε := by group
    exact hhard _ he heQ (by rw [e]; exact hy'.1)

end HS9

@[expose] def Sec97FourLineStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ h ∈ M, conjSubgroup h B ≤ QB B → HS9.LineGeom M Q Z B h

@[expose] def Sec97FourCoreStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
      HS9.OneConcl hc X Y → HS9.TwoConcl M Q B X → HS9.ThreeConcl M Q B X →
      ∀ h ∈ M, conjSubgroup h B ≤ QB B →
        (∀ x ∈ LB M Q B ⊓ X, x ∉ Q →
          h * x * h⁻¹ ∉ LB M Q B ∧ x ∉ conjSubgroup h (LB M Q B)) →
        HS9.LineGeom M Q Z B h →
        IsTIMod (LB M Q B ⊔ LB M Q (conjSubgroup h B)) Q (LB M Q B ⊓ X) → False

theorem sec97FourHard_of_line_core (hLine : Sec97FourLineStatement)
    (hCore : Sec97FourCoreStatement) : Sec97FourHardStatement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit h4 h1 h2 h3 h hh hFB hhard
  have hline := hLine G M Q Z B hc n t hs h hh hFB
  exact hCore G M Q Z B hc n t hs X Y hsplit h4 h1 h2 h3 h hh hFB hhard hline
    (HS9.isTIMod_of_line hc hsplit h2 hh (fun x hx hxQ => (hhard x hx hxQ).1) hline)

theorem sec97Four_of_line_core (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hLine : Sec97FourLineStatement) (hCore : Sec97FourCoreStatement) : Sec97FourStatement :=
  sec97Four_of_hard h34 h311a (sec97FourHard_of_line_core hLine hCore)

end CFSG.RankThree.GF2n.Stroth80
