module

public import CFSG.Assembly.Defs
import CFSG.LocalAnalysis.ZStar.BrauerSuzukiShortcut
import TauCeti.GroupTheory.DerivedCentralQuotient

public section

namespace CFSG.Walter

theorem two_le_twoRank (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (heven : Even (Nat.card G)) :
    2 ≤ Assembly.twoRank G := by
  classical
  let := Fintype.ofFinite G
  by_contra hlt
  push Not at hlt
  have hbdd : BddAbove
      {k | ∃ E : Subgroup G, E ≤ ⊤ ∧ Assembly.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} :=
    ⟨Nat.card G, fun k ⟨E, _, _, hk⟩ => (Nat.lt_two_pow_self).le.trans
      (hk ▸ Subgroup.card_le_card_group E)⟩
  have hrank : ∀ E : Subgroup G, Assembly.IsElemAbelian 2 E → ∀ k, Nat.card E = 2 ^ k → k ≤ 1 :=
    fun E hE k hk => by
      have : k ≤ Assembly.twoRank G := le_csSup hbdd ⟨E, le_top, hE, hk⟩
      omega
  obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hPne : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card (even_iff_two_dvd.mp heven)
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot _).mpr hPne
  have hZ := P.isPGroup'.center_nontrivial
  obtain ⟨k, hk, hkcard⟩ :=
    ((P.isPGroup'.to_subgroup (Subgroup.center P)).nontrivial_iff_card).mp hZ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 2
    (hkcard ▸ dvd_pow_self 2 hk.ne')
  set t : G := ((z : P) : G)
  have htP : t ∈ (P : Subgroup G) := (z : P).2
  have htord : orderOf t = 2 := by
    have h1 : orderOf (z : P) = 2 :=
      (orderOf_injective (Subgroup.center P).subtype Subtype.val_injective z).trans hz
    exact (orderOf_injective (P : Subgroup G).subtype Subtype.val_injective (z : P)).trans h1
  have ht1 : t ≠ 1 := by
    intro h; rw [h, orderOf_one] at htord; omega
  have ht2 : t * t = 1 := by
    rw [← sq, ← htord, pow_orderOf_eq_one]
  have huniq : ZStar.UniqueInvolutionIn (P : Subgroup G) t := by
    intro s hsP hs1 hs2
    by_contra hst
    have hcomm : ({s, t} : Set G).Pairwise Commute := by
      have hst' : Commute s t := by
        have := Subgroup.mem_center_iff.mp z.2 ⟨s, hsP⟩
        show s * t = t * s
        simpa [t] using congrArg Subtype.val this
      intro a ha b hb hab
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact hst'
      · exact hst'.symm
      · exact (hab rfl).elim
    let E := Subgroup.closure ({s, t} : Set G)
    have hEcomm : IsMulCommutative E := Subgroup.isMulCommutative_closure hcomm
    have hEsq : ∀ x ∈ E, x ^ 2 = 1 := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with rfl | rfl
        · rw [sq, hs2]
        · rw [sq, ht2]
      | one => exact one_pow 2
      | mul x y hx hy hx2 hy2 =>
        have hxy : Commute x y := by
          have := hEcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
          exact congrArg Subtype.val this
        rw [hxy.mul_pow, hx2, hy2, one_mul]
      | inv x hx hx2 => rw [inv_pow, hx2, inv_one]
    have hEP : E ≤ (P : Subgroup G) := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hsP
      · exact htP
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp (P.isPGroup'.to_le hEP))
    have hk1 := hrank E ⟨hEcomm, hEsq⟩ k hk
    have hfour : 4 ≤ Nat.card E := by
      have hsub : (({1, s, t, s * t} : Finset G) : Set G) ⊆ E := by
        intro x hx
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact E.one_mem
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact E.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      have hcard : ({1, s, t, s * t} : Finset G).card = 4 := by
        have hst1 : s * t ≠ 1 := fun h => hst (by
          have := eq_inv_of_mul_eq_one_left h
          rwa [inv_eq_of_mul_eq_one_right ht2] at this)
        have hsts : s * t ≠ s := fun h => ht1 (by simpa using h)
        have hstt : s * t ≠ t := fun h => hs1 (by simpa using h)
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_pair hstt.symm]
        · simp [hst, hsts.symm]
        · simp [hs1.symm, ht1.symm, hst1.symm]
      calc 4 = ({1, s, t, s * t} : Finset G).card := hcard.symm
        _ = Set.ncard ((({1, s, t, s * t} : Finset G)) : Set G) := (Set.ncard_coe_finset _).symm
        _ ≤ Set.ncard (E : Set G) := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = Nat.card E := Nat.card_coe_set_eq _ |>.symm
    interval_cases k <;> simp_all
  have hperfect : commutator G = ⊤ := by
    have hnc : ¬ IsMulCommutative G := by
      rintro ⟨hc⟩
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (hc.comm a b)
    have := TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc
    exact Group.IsPerfect.commutator_eq_top
  obtain ⟨N, hN, hNodd, hc⟩ :=
    ZStar.BrauerSuzukiShortcut.zStarConclusion_of_perfect_uniqueInvolution_brauerSuzuki
      ht1 ht2 P htP huniq hperfect
  rcases hN.eq_bot_or_eq_top with rfl | rfl
  · have htc : t ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
      have := hc g
      rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
      exact this
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
    · exact ht1 (by rwa [h, Subgroup.mem_bot] at htc)
    · obtain ⟨a, b, hab⟩ := hnonab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  · rw [Subgroup.card_top] at hNodd
    exact (Nat.not_even_iff_odd.mpr hNodd) heven

end CFSG.Walter
