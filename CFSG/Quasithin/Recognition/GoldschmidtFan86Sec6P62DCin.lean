module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalFrob
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Defs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P62

theorem exists_mid (F : FanTree Γ G) {l d : V} (h : Γ.dist l d = 2) :
    ∃ ν, Γ.Adj l ν ∧ Γ.Adj ν d := by
  obtain ⟨p, hp⟩ := F.isTree.connected.exists_walk_length_eq_dist l d
  rw [h] at hp
  cases p with
  | nil => simp at hp
  | cons h1 p1 =>
    cases p1 with
    | nil => simp at hp
    | cons h2 p2 =>
      cases p2 with
      | nil => exact ⟨_, h1, h2⟩
      | cons h3 p3 =>
        simp only [SimpleGraph.Walk.length_cons] at hp
        omega

theorem cinv_mem_nbrStab (F : FanTree Γ G) {v : V} {w : G} (hw : w ∈ Cinv G v) :
    w ∈ nbrStab Γ G v := by
  obtain ⟨-, hw2, hwst, hwc⟩ := hw
  have hfin : Finite (Γ.neighborSet v) := F.finite_neighborSet v
  let _ : Fintype (Γ.neighborSet v) := Fintype.ofFinite _
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ Fintype.card (Γ.neighborSet v) := by
    rw [Fintype.card_eq_nat_card]
    rcases F.valence v with h | h <;> omega
  have e : (⟨w, hwst⟩ : MulAction.stabilizer G v) * ⟨w, hwst⟩ = 1 := Subtype.ext hw2
  have hσ : F.localHom v ⟨w, hwst⟩ ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq, ← map_mul, e, map_one]
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime hodd hσ
  have hwa : w • (a : V) = a := congrArg Subtype.val ha
  intro b hb
  obtain ⟨g, hg, hgb⟩ := F.loc_trans v a b a.2 hb
  have hcomm : g * w = w * g := hwc g hg
  calc w • b = w • g • (a : V) := by rw [hgb]
    _ = g • w • (a : V) := by rw [← mul_smul, ← hcomm, mul_smul]
    _ = b := by rw [hwa, hgb]

theorem le_normalizer_zpowers {H : Subgroup G} {w : G} (h : ∀ g ∈ H, g * w = w * g) :
    H ≤ Subgroup.normalizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  exact (Commute.zpow_left (show Commute w g from (h g hg).symm) n).eq

theorem lemmaD_two (F : FanTree Γ G) {l d : V} (hld : l ≠ d) (hdist : Γ.dist l d = 2) {w : G}
    (hl : w ∈ Cinv G l) (hd : w ∈ Cinv G d) : False := by
  obtain ⟨ν, hlν, hνd⟩ := exists_mid F hdist
  have hKl := cinv_mem_nbrStab F hl
  set H : Subgroup G :=
    Subgroup.closure ((MulAction.stabilizer G l : Set G) ∪ MulAction.stabilizer G d) with hH
  have hl_le : MulAction.stabilizer G l ≤ H := fun g hg => Subgroup.subset_closure (Or.inl hg)
  have hd_le : MulAction.stabilizer G d ≤ H := fun g hg => Subgroup.subset_closure (Or.inr hg)
  have hcomm : ∀ g ∈ H, g * w = w * g := by
    intro g hg
    have : H ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [hH, Subgroup.closure_le]
      rintro g (hg | hg)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact (hl.2.2.2 g hg).symm
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact (hd.2.2.2 g hg).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (this hg)
  have hU : ∀ u ∈ Subgroup.zpowers w, u • l = l ∧ u • ν = ν := by
    have hle : Subgroup.zpowers w ≤ MulAction.stabilizer G l ⊓ MulAction.stabilizer G ν :=
      Subgroup.zpowers_le.2 (F.nbrStab_le_edge l hlν hKl)
    intro u hu
    exact ⟨MulAction.mem_stabilizer_iff.1 (hle hu).1, MulAction.mem_stabilizer_iff.1 (hle hu).2⟩
  have hα : ∀ a b, Γ.Adj l a → Γ.Adj l b → ∃ h ∈ H, h • l = l ∧ h • a = b := by
    intro a b ha hb
    obtain ⟨g, hg, hga⟩ := F.loc_trans l a b ha hb
    exact ⟨g, hl_le hg, MulAction.mem_stabilizer_iff.1 hg, hga⟩
  have hβ : ∀ a b, Γ.Adj ν a → Γ.Adj ν b → ∃ h ∈ H, h • ν = ν ∧ h • a = b := by
    obtain ⟨g₁, hg₁, hg₁l, c₁, hc₁, hg₁c⟩ := F.frobenius_nonreg ν l hlν.symm
    obtain ⟨g₂, hg₂, hg₂d, c₂, hc₂, hg₂c⟩ := F.frobenius_nonreg ν d hνd
    have h₁d : g₁ • d ≠ d := fun h =>
      hg₁c (F.frobenius_two ν l d hlν.symm hνd hld g₁ hg₁ hg₁l h c₁ hc₁)
    have h₂l : g₂ • l ≠ l := fun h =>
      hg₂c (F.frobenius_two ν d l hνd hlν.symm hld.symm g₂ hg₂ hg₂d h c₂ hc₂)
    intro a b ha hb
    obtain ⟨m, hm, hmν, hma⟩ := F.transitive_of_two_fixers hlν.symm hνd hld hg₁ hg₂ hg₁l h₁d
      hg₂d h₂l ha hb
    have hle : Subgroup.closure ({g₁, g₂} : Set G) ≤ H := by
      rw [Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact hl_le (MulAction.mem_stabilizer_iff.2 hg₁l)
      · exact hd_le (MulAction.mem_stabilizer_iff.2 hg₂d)
    exact ⟨m, hle hm, hmν, hma⟩
  have hbot := F.eq_bot_of_locTrans H hlν hU (le_normalizer_zpowers hcomm) hα hβ
  exact hl.1 (Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_zpowers w))

end P62

end CFSG.Quasithin.Fan86
