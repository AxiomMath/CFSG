module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S37
public import CFSG.LocalAnalysis.UniquenessCase.UC6Close

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.Yardstones.Mf4cdcdf2e013 (TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (calNOf)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem Z_le_normalizer_L : m.Z ≤ normalizer (m.L : Set G) := fun z hz =>
  (Subgroup.centralizer_le_normalizer (m.L : Set G))
    (mem_centralizer_iff.2 fun l hl => (m.Z_comm_L hz hl).symm)

theorem Z_le_X : m.Z ≤ m.K ⊓ normalizer (m.L : Set G) := le_inf m.Z_le_K m.Z_le_normalizer_L

theorem V_ne_bot : m.V ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal Dat.maxLocal.1

theorem M_le_normalizer_V : m.M ≤ normalizer (m.V : Set G) := le_normalizer_pCoreOf 2 m.M

theorem false_of_claims (h67 : R6_7 Dat) (h619 : m.C619) (h620 : m.C620)
    (h624 : m.C624) (h629 : m.C629) (h632 : m.C632) (h635 : m.C635) (h636 : m.C636) : False := by
  classical
  set X : Subgroup G := m.K ⊓ normalizer (m.L : Set G) with hX
  have hXK : X ≤ m.K := inf_le_left
  have hXV : X ≤ normalizer (m.V : Set G) := fun x hx => m.M_le_normalizer_V (m.K_le_M hx.1)
  have hX1 : X ≠ ⊥ := by
    intro h
    exact m.Z_ne_bot (le_bot_iff.1 (h ▸ m.Z_le_X))
  have hreg := m.semiregular h67 h619 h620 h632 h635 h636
  have hZp : (Nat.card m.Z).Prime := by rw [m.card_Z]; exact m.hr
  obtain ⟨q, Q, Y, hq, hQ, hQcyc, hYQ, hYcard, hYZ, hQnot⟩ :=
    exists_regular_zgroup_data hXV m.V_ne_bot hX1 h636.1 hreg m.Z_le_X hZp
  have hYX : Y ≤ X := hYQ.trans hQ.le
  have hY1 : Y ≠ ⊥ := by
    intro h
    have : q = 1 := by rw [← hYcard, h]; exact Subgroup.card_bot
    exact hq.ne_one this
  have hcontrol : normalizer (Y : Set G) ⊓ m.K ≤ X := by
    have hYL : ∀ y ∈ Y, ∀ l ∈ m.L, y * l = l * y := fun y hy l hl =>
      (mem_centralizer_iff.1 (h636.2 (hYX hy)) l hl).symm
    have hALY : m.A ⊔ m.L ≤ centralizer (Y : Set G) := by
      have hZLY : m.Z ⊔ m.L ≤ centralizer (Y : Set G) := by
        refine sup_le (fun z hz => mem_centralizer_iff.2 fun y hy => (hYZ y hy z hz)) ?_
        exact fun l hl => mem_centralizer_iff.2 fun y hy => (hYL y hy l hl)
      exact sup_le (h620.1.trans hZLY) (le_sup_right.trans hZLY)
    have hNtop : normalizer (Y : Set G) ≠ ⊤ := by
      intro h
      haveI : (Y).Normal := Subgroup.normalizer_eq_top_iff.1 h
      rcases Dat.standing.simple.eq_bot_or_eq_top_of_normal Y with hb | ht
      · exact hY1 hb
      · have hYM : Y ≤ m.M := hYX.trans (hXK.trans m.K_le_M)
        rw [ht] at hYM
        exact m.M_ne_top (eq_top_iff.2 hYM)
    obtain ⟨N', hN', hle⟩ : ∃ N', IsCoatom N' ∧ normalizer (Y : Set G) ≤ N' := by
      rcases eq_top_or_exists_le_coatom (normalizer (Y : Set G)) with h | h
      · exact absurd h hNtop
      · exact h
    have hN'mem : N' ∈ calNOf (m.A ⊔ m.L) :=
      ⟨hN', hALY.trans ((Subgroup.centralizer_le_normalizer (Y : Set G)).trans hle)⟩
    have hr3 : m.r ≠ 3 := by have : 3 < m.r := h635; omega
    have hN'eq : N' = normalizer (m.L : Set G) := by
      have := h624 hr3
      rw [this] at hN'mem
      exact hN'mem
    exact fun g hg => ⟨hg.2, hN'eq ▸ hle hg.1⟩
  exact false_of_zgroup_control hq hXK hQ hQcyc hYQ hYcard hcontrol hQnot
    (fun N _ hN => m.K_no_pgroup_quotient h629 hq N hN)

end Mz614

structure UC6Inputs {G : Type} [Group G] [Finite G] (Dat : Data G) : Prop where
  r67 : TheoremCAt Dat.M → R6_7 Dat
  c619 : ∀ m : Mz614 Dat, m.C619
  c620 : ∀ m : Mz614 Dat, m.C620
  c624 : ∀ m : Mz614 Dat, m.C624
  c629 : ∀ m : Mz614 Dat, m.C629
  c632 : ∀ m : Mz614 Dat, m.C632
  c635 : ∀ m : Mz614 Dat, m.C635
  c636 : ∀ m : Mz614 Dat, m.C636

theorem r6_14_of_inputs {G : Type} [Group G] [Finite G] {Dat : Data G} (hk : Hooks Dat)
    (hC : TheoremCAt Dat.M) (h : UC6Inputs Dat) : R6_14 Dat := by
  intro hσ1 r hr hr2 hrσ R hR E hE hEel hEcard hΓ
  by_contra hns
  let c : Mc614 Dat :=
    { hk := hk, hC := hC, hσ1 := hσ1, r := r, R := R, E := E,
      d := { maxLocal := Dat.maxLocal, prime := hr, odd := hr2, sylow := hR, E_le := hE,
             E_el := hEel, E_card := hEcard, E_gamma := hΓ },
      hrσ := hrσ, hns := hns }
  obtain ⟨Z, hZle, hZcard, hZnot⟩ := c.exists_Z
  let m : Mz614 Dat := { toMc614 := c, Z := Z, hZ := ⟨hZle, hZcard, hZnot⟩ }
  exact m.false_of_claims (h.r67 hC) (h.c619 m) (h.c620 m) (h.c624 m) (h.c629 m)
    (h.c632 m) (h.c635 m) (h.c636 m)

end CFSG.LocalAnalysis.UniquenessCase.UC6G
