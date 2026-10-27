module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Blocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3PStarA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gCase153

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

private theorem s168e3_seven_comm_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : ∀ a b : X, a * b = b * a := by
  obtain ⟨e⟩ := h
  intro a b
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

theorem s168e3_seven_deltaSym {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} {r : ℕ} (hr : 2 ≤ r) (hE : IsElemAbelianOfRank 7 r ↥L)
    (hW : Conc4_136W A t L) :
    ⁅L, Subgroup.zpowers t⁆ ≠ ⊥ ∧ DeltaSym A t (commSub (⊤ : Subgroup W) L) r 3 := by
  have hcomm := s168e3_seven_comm_of_elem hE
  have hcard : Nat.card ↥L = 7 ^ r := A38.card_eq_of_isElemAbelianOfRank (by norm_num) hE
  have h27 : 27 ≤ 7 ^ r :=
    calc 27 ≤ 7 ^ 2 := by norm_num
      _ ≤ 7 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  obtain ⟨-, -, h⟩ := hW
  rcases h with h133 | ⟨K, hK, g, hg, hKne, hLK, htens⟩ | ⟨hcomp, -, -⟩ | ⟨-, -, hcomp, -⟩
  · obtain ⟨p', hp'p, -, hLt, -, halt⟩ := h133
    rcases halt with ⟨hcyc, h | h | h⟩ | ⟨hcyc, h⟩ | ⟨h1p2, h⟩ | ⟨hEA, h8, -⟩ |
      ⟨hcyc, h | h⟩ | ⟨r', m', hpm, hr2, hEAr, hrk', hDelta⟩ | ⟨hEA, h6, hinv⟩
    · exfalso; have := hcyc.2; omega
    · exfalso; have := hcyc.2; omega
    · exfalso; have := hcyc.2; omega
    · exfalso; have := hcyc.2; omega
    · exact (r1613g_not_isPOnePlusTwo_of_comm hcomm h1p2).elim
    · exfalso
      have hc9 : Nat.card ↥L = 9 := by
        have h9' := A38.card_eq_of_isElemAbelianOfRank (by norm_num : Nat.Prime 3) hEA
        simpa using h9'
      omega
    · exfalso; have := hcyc.2; omega
    · exfalso; have := hcyc.2; omega
    · have hp'pr : p'.Prime := hp'p
      have hcard' : Nat.card ↥L = p' ^ r' := A38.card_eq_of_isElemAbelianOfRank hp'pr hEAr
      have hpow : 7 ^ r = p' ^ r' := hcard.symm.trans hcard'
      obtain ⟨hpp', hrr'⟩ :=
        Nat.Prime.pow_inj' (by norm_num : Nat.Prime 7) hp'pr (by omega) (by omega) hpow
      subst hrr'
      have hm3 : m' = 3 := by
        have hp'7 : p' = 7 := hpp'.symm
        rcases hpm with ⟨h3, -⟩ | ⟨-, h3⟩
        · rw [hp'7] at h3
          exact absurd h3 (by norm_num)
        · exact h3
      rw [hm3] at hDelta
      exact ⟨hLt, hDelta⟩
    · exfalso
      have hc9 : Nat.card ↥L = 9 := by
        have h9' := A38.card_eq_of_isElemAbelianOfRank (by norm_num : Nat.Prime 3) hEA
        simpa using h9'
      omega
  · exfalso
    have hKL : K ≤ L := hLK ▸ le_sup_left
    exact r1613g_not_isQuasisimple_of_comm
      (fun a b => Subtype.ext (by
        have h := congrArg (fun x : ↥L => (x : MulAut W))
          (hcomm ⟨a.1, hKL a.2⟩ ⟨b.1, hKL b.2⟩)
        exact h)) hK.2.2
  · exact (r1613g_not_isQuasisimple_of_comm hcomm hcomp.2.2).elim
  · exact (r1613g_not_isQuasisimple_of_comm hcomm hcomp.2.2).elim

variable {G : Type} [Group G] [Finite G]

theorem s168e3_seven_le_commutator {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) {r : ℕ} (hr : 2 ≤ r)
    (hE : IsElemAbelianOfRank 7 r ↥(lBar V₀ V hV L)) :
    lBar V₀ V hV L ≤ ⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆ := by
  obtain ⟨t, -, ht2, -, htrk, hW⟩ := c.conc
  obtain ⟨hLt, hD⟩ := s168e3_seven_deltaSym hr hE hW
  exact s16h_bl_le_commutator_of_deltaSym (s15_Infra_vtil_sq_eq_one V₀ V hV) hW ht2 htrk
    (by norm_num) (by norm_num) (Or.inr ⟨rfl, rfl⟩) hr (by omega)
    (barSub_mono V₀ V hV c.setting.hyp151.le) hE hLt hD

theorem s168e3_seven_exists_xbar {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) {r : ℕ} (hr : 2 ≤ r)
    (hE : IsElemAbelianOfRank 7 r ↥(lBar V₀ V hV L))
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    ∃ Xbar : Subgroup (F11.MBar11 D.M V₀ V), Xbar.Normal ∧ IsElemAbelian 7 Xbar ∧
      Nat.card Xbar = 7 ^ r ∧ Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ ∧
      barSub V₀ V hV (F11.barPreimage11 D.M V₀ V Xbar) ≤ lBar V₀ V hV L := by
  have hXn : ∀ q ∈ Mbar D.M V₀ V hV, ∀ x ∈ lBar V₀ V hV L, q * x * q⁻¹ ∈ lBar V₀ V hV L := by
    intro q hq x hx
    have h := lBar_conj_eq_of_s15_eq_one hs hq
    have hm : (MulAut.conj q).toMonoidHom x ∈ (lBar V₀ V hV L).map (MulAut.conj q).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [h] at hm
    simpa [MulAut.conj_apply] using hm
  exact s16h_z3_exists_xbar_of_bar c.setting.hyp16 hXn (s16h_bl_isElemAbelian hE)
    (s168e3_seven_le_commutator c hr hE)
    (A38.card_eq_of_isElemAbelianOfRank (by norm_num) hE)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
