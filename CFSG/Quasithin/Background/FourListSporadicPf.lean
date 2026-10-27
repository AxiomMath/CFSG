module

public import CFSG.Quasithin.Background.FourListSporadic
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.GH74.Orders.LieType
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersSporadic
public import CFSG.RankThree.OddKernel.SporadicKernelTh

public section

namespace CFSG.Quasithin.FourListSporadic

open CFSG.Open CFSG.Timmesfeld.Orders

@[expose] def fourOrd (N : ℕ) : Prop :=
  (∃ n, 1 ≤ n ∧ (N = ordA 1 (2 ^ n) ∨ N = ordSuzuki (2 ^ n) ∨ N = ordTwistedA 2 (2 ^ n) ∨
    N = ordA 2 (2 ^ n) ∨ N = ordBC 2 (2 ^ n) ∨ N = ordG2 (2 ^ n))) ∨
  N = 360 ∨ N = 2520 ∨ N = 6048 ∨ N = ordA 3 (2 ^ 1) ∨ N = ordA 4 (2 ^ 1)

@[expose] def fourCheck (N : ℕ) : Bool :=
  (List.range 47).all (fun n => ordA 1 (2 ^ n) != N && ordSuzuki (2 ^ n) != N &&
    ordTwistedA 2 (2 ^ n) != N && ordA 2 (2 ^ n) != N && ordBC 2 (2 ^ n) != N &&
    ordG2 (2 ^ n) != N) &&
  N != 360 && N != 2520 && N != 6048 && N != ordA 3 (2 ^ 1) && N != ordA 4 (2 ^ 1)

theorem two_pow_dvd_of_eq {m n k r : ℕ} (hk : 1 ≤ k) (hm : m = 2 ^ (n * k) * r) : 2 ^ n ∣ m :=
  hm ▸ (Nat.pow_dvd_pow 2 (Nat.le_mul_of_pos_right n hk)).trans (Dvd.intro r rfl)

theorem two_pow_dvd_of_fourOrd {N n : ℕ} (hn : 1 ≤ n)
    (h : N = ordA 1 (2 ^ n) ∨ N = ordSuzuki (2 ^ n) ∨ N = ordTwistedA 2 (2 ^ n) ∨
      N = ordA 2 (2 ^ n) ∨ N = ordBC 2 (2 ^ n) ∨ N = ordG2 (2 ^ n)) : 2 ^ n ∣ N := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨r, -, hr⟩ := (profile_ordA (n := 1) le_rfl hn).two
    exact two_pow_dvd_of_eq (k := 1 * (1 + 1) / 2) (by norm_num) hr
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _) _
  · obtain ⟨r, -, hr⟩ := (profile_ordTwistedA (n := 2) le_rfl hn).two
    exact two_pow_dvd_of_eq (k := 2 * (2 + 1) / 2) (by norm_num) hr
  · obtain ⟨r, -, hr⟩ := (profile_ordA (n := 2) (by norm_num) hn).two
    exact two_pow_dvd_of_eq (k := 2 * (2 + 1) / 2) (by norm_num) hr
  · obtain ⟨r, -, hr⟩ := (profile_ordBC (n := 2) hn).two
    exact two_pow_dvd_of_eq (k := 2 * 2) (by norm_num) hr
  · obtain ⟨r, -, hr⟩ := (profile_ordG2 hn).two
    exact two_pow_dvd_of_eq (k := 6) (by norm_num) hr

theorem not_fourOrd {N : ℕ} (h47 : ¬ 2 ^ 47 ∣ N) (hc : fourCheck N = true) : ¬ fourOrd N := by
  simp only [fourCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, bne_iff_ne,
    ne_eq] at hc
  obtain ⟨⟨⟨⟨⟨hF, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  rintro (⟨n, hn, h⟩ | h | h | h | h | h)
  · have hlt : n < 47 := by
      by_contra hge
      exact h47 ((Nat.pow_dvd_pow 2 (not_lt.1 hge)).trans (two_pow_dvd_of_fourOrd hn h))
    obtain ⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩ := hF n hlt
    rcases h with h | h | h | h | h | h
    · exact g1 h.symm
    · exact g2 h.symm
    · exact g3 h.symm
    · exact g4 h.symm
    · exact g5 h.symm
    · exact g6 h.symm
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 h
  · exact h5 h

section Lie

theorem card_mem_fourOrd {X : Type} [Group X] (h : FourList X) :
    IsSporadic .M22 X ∨ fourOrd (Nat.card X) := by
  have alt : ∀ n, 2 ≤ n → IsAlt n X → Nat.card X = n.factorial / 2 := by
    rintro n hn ⟨e⟩
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rcases h with ⟨n, hn, h | h | h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h | ⟨n, hn, h⟩ | h | h | h | h | h
  · exact .inr (.inl ⟨n, by omega, .inl ((CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl)⟩)
  · obtain ⟨-, -, -, -, hc⟩ := CFSG.GH74.card_of_suzukiModel h
    exact .inr (.inl ⟨n, by omega, .inr (.inl hc)⟩)
  · exact .inr (.inl ⟨n, by omega,
      .inr (.inr (.inl ((CFSG.Timmesfeld.card_statedClassicalModel_two h).2.1 rfl)))⟩)
  · exact .inr (.inl ⟨n, hn,
      .inr (.inr (.inr (.inl ((CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl))))⟩)
  · exact .inr (.inl ⟨n, by omega, .inr (.inr (.inr (.inr (.inl
      ((CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl)))))⟩)
  · exact .inr (.inr (.inl ((alt 6 (by norm_num) h).trans (by decide))))
  · exact .inr (.inl ⟨n, by omega, .inr (.inr (.inr (.inr (.inr
      (CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h)))))⟩)
  · exact .inr (.inr (.inr (.inr (.inl (CFSG.QuasithinUnique.Id2519.card_psu_three_three h)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl
      ((CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr
      ((CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl))))))
  · exact .inr (.inr (.inr (.inl ((alt 7 (by norm_num) h).trans (by decide)))))
  · exact .inl h

end Lie

section Spor

theorem not_fourOrd_card_carrier
    (hM : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M) =
      808017424794512875886459904961710757005754368000000000)
    {s : TauCeti.SporadicName} (hs : s ≠ .M22) :
    ¬ fourOrd (Nat.card (CFSG.Blueprint.NativeSporadic.Carrier s)) := by
  have gen : ∀ N : ℕ, Nat.card (CFSG.Blueprint.NativeSporadic.Carrier s) = N →
      ¬ 2 ^ 47 ∣ N → fourCheck N = true →
        ¬ fourOrd (Nat.card (CFSG.Blueprint.NativeSporadic.Carrier s)) :=
    fun N hN h47 hc => hN ▸ not_fourOrd h47 hc
  cases s
  case M11 => exact gen _ CFSG.Sporadic.Mathieu.card_M11 (by decide) (by decide +kernel)
  case M12 => exact gen _ CFSG.Sporadic.Mathieu.card_M12 (by decide) (by decide +kernel)
  case M22 => exact absurd rfl hs
  case M23 =>
    exact gen _ CFSG.EvenSmallLie.CatalogOrders.card_M23 (by decide) (by decide +kernel)
  case M24 => exact gen _ CFSG.Sporadic.Mathieu.card_M24 (by decide) (by decide +kernel)
  case J1 => exact gen _ CFSG.Sporadic.J1.card_J1 (by decide) (by decide +kernel)
  case J2 => exact gen _ CFSG.Sporadic.J2.card_J2 (by decide) (by decide +kernel)
  case J3 => exact gen _ CFSG.Sporadic.J3.card_J3 (by decide) (by decide +kernel)
  case J4 => exact gen _ CFSG.Sporadic.J4.card_J4 (by decide) (by decide +kernel)
  case HS => exact gen _ CFSG.Sporadic.HS.card_HS (by decide) (by decide +kernel)
  case McL => exact gen _ CFSG.Sporadic.McL.card_McL (by decide) (by decide +kernel)
  case He => exact gen _ CFSG.Sporadic.He.fam_he_order.1 (by decide) (by decide +kernel)
  case Ru => exact gen _ CFSG.Sporadic.Ru.card_Ru (by decide) (by decide +kernel)
  case Suz => exact gen _ CFSG.Sporadic.Suz.card_Suz (by decide) (by decide +kernel)
  case ONan => exact gen _ CFSG.Sporadic.ON.card_ON (by decide) (by decide +kernel)
  case Co1 => exact gen _ CFSG.Sporadic.Co1.card_Co1 (by decide) (by decide +kernel)
  case Co2 => exact gen _ CFSG.Sporadic.Co2.card_Co2 (by decide) (by decide +kernel)
  case Co3 => exact gen _ CFSG.Sporadic.Co3.card_Co3 (by decide) (by decide +kernel)
  case Fi22 => exact gen _ CFSG.Sporadic.Fi22.card_Fi22 (by decide) (by decide +kernel)
  case Fi23 => exact gen _ CFSG.Sporadic.Fi23.card_Fi23 (by decide) (by decide +kernel)
  case Fi24Prime =>
    exact gen _ CFSG.Sporadic.Fi24.card_Fi24prime (by decide) (by decide +kernel)
  case HN => exact gen _ CFSG.Sporadic.HN.card_HN (by decide) (by decide +kernel)
  case Ly => exact gen _ CFSG.Sporadic.Ly.card_Ly (by decide) (by decide +kernel)
  case Th => exact gen _ CFSG.RankThree.OddKernel.card_Th_eq (by decide) (by decide +kernel)
  case B => exact gen _ CFSG.Monster.Existence.card_nativeB (by decide) (by decide +kernel)
  case M => exact gen _ hM (by decide) (by decide +kernel)

end Spor

section Main

theorem sporadicFourListDisjoint_of_card_monster
    (hM : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M) =
      808017424794512875886459904961710757005754368000000000) :
    SporadicFourListDisjoint := by
  intro X _ s hs hF
  by_cases hs22 : s = .M22
  · exact hs22 ▸ hs
  rcases card_mem_fourOrd hF with h | h
  · exact h
  obtain ⟨e⟩ := hs
  rw [Nat.card_congr e.toEquiv] at h
  exact absurd h (not_fourOrd_card_carrier hM hs22)

end Main

end CFSG.Quasithin.FourListSporadic
