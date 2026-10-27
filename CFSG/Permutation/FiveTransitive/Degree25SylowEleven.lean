module

public import CFSG.Permutation.FiveTransitive.Degree25Eleven
public import Mathlib.CategoryTheory.Action.Concrete

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

theorem eleven_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬11 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  change ¬11 ∣ h
  intro heleven
  have hh : h ≠ 0 := Nat.ne_of_gt Nat.card_pos
  let Y := SubMulAction.ofFixingSubgroup P s
  have hYcard : Nat.card Y = 20 := by
    change Nat.card ↥(sᶜ : Set X) = 20
    rw [Nat.card_coe_set_eq]
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card, hcard, hs] at htotal
    omega
  have hfaithful :
      Function.Injective (MulAction.toPermHom H Y) := by
    intro a b hab
    apply Subtype.ext
    apply P.subtype_injective
    ext x
    by_cases hx : x ∈ s
    · have ha :=
        (mem_fixingSubgroup_iff P).mp a.prop x hx
      have hb :=
        (mem_fixingSubgroup_iff P).mp b.prop x hx
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using
        ha.trans hb.symm
    · let y : Y := ⟨x, hx⟩
      have hy :=
        congrArg (fun q : Equiv.Perm Y => q y) hab
      have hy' := congrArg Subtype.val hy
      simpa [y, Subgroup.smul_def, Equiv.Perm.smul_def] using
        hy'
  have hdiv : h ∣ (20 : ℕ).factorial := by
    change Nat.card H ∣ (20 : ℕ).factorial
    have hdvd :=
      Subgroup.card_dvd_of_injective
        (MulAction.toPermHom H Y) hfaithful
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hYcard] at hdvd
    exact hdvd
  have hnotElevenSq : ¬11 ^ 2 ∣ h := by
    intro hdvd
    have : 11 ^ 2 ∣ (20 : ℕ).factorial :=
      hdvd.trans hdiv
    norm_num [Nat.factorial] at this
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 6375600 := by
    change (fixingSubgroup P s).index = 6375600
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 6375600 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hElevenSqDvdP : 11 ^ 2 ∣ Nat.card P := by
    rw [hPcard]
    have hindexEleven : 11 ∣ 6375600 := by norm_num
    simpa [pow_two] using Nat.mul_dvd_mul hindexEleven heleven
  have hnotElevenCubeP : ¬11 ^ 3 ∣ Nat.card P := by
    intro hcube
    have hcube' :
        11 * 121 ∣ 11 * (579600 * h) := by
      rw [hPcard] at hcube
      simpa only
        [show 11 ^ 3 = 11 * 121 by norm_num,
          show 6375600 * h = 11 * (579600 * h) by ring]
        using hcube
    have h121Product : 121 ∣ 579600 * h :=
      (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 11)).mp hcube'
    have h121h : 121 ∣ h :=
      (show Nat.Coprime 121 579600 by norm_num).dvd_of_dvd_mul_left
        h121Product
    exact hnotElevenSq (by
      norm_num at h121h ⊢
      exact h121h)
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let S : Sylow 11 P := Sylow.nonempty.some
  have hPfactorization : (Nat.card P).factorization 11 = 2 := by
    have hge :
        2 ≤ (Nat.card P).factorization 11 :=
      (show Nat.Prime 11 by norm_num).pow_dvd_iff_le_factorization
        (Nat.ne_of_gt Nat.card_pos) |>.mp hElevenSqDvdP
    have hlt :
        (Nat.card P).factorization 11 < 3 := by
      rw [← not_le]
      intro hthree
      apply hnotElevenCubeP
      exact
        (show Nat.Prime 11 by norm_num).pow_dvd_iff_le_factorization
          (Nat.ne_of_gt Nat.card_pos) |>.mpr hthree
    omega
  have hScard : Nat.card S = 121 := by
    rw [S.card_eq_multiplicity, hPfactorization]
    norm_num
  letI : IsMulCommutative S :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq
      (p := 11) (by
        rw [hScard]
        norm_num)
  have hSnontrivial : Nontrivial S :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hScard]
      norm_num)
  letI : Nontrivial S := hSnontrivial
  have hfixedPointsNe :
      MulAction.fixedPoints S X ≠ Set.univ := by
    obtain ⟨u, hu⟩ := exists_ne (1 : S)
    intro hfixed
    have huFixed : MulAction.fixedBy X u = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      have hx : x ∈ MulAction.fixedPoints S X := by
        rw [hfixed]
        trivial
      exact hx u
    exact hu
      ((MulAction.fixedBy_eq_univ_iff_eq_one
        (M := S) (α := X)).mp huFixed)
  obtain ⟨x, hx⟩ :
      ∃ x, x ∉ MulAction.fixedPoints S X := by
    by_contra h
    push Not at h
    exact hfixedPointsNe (Set.eq_univ_of_forall h)
  let O : Set X := MulAction.orbit S x
  let R : Subgroup S := MulAction.stabilizer S x
  have hOcardNe : Fintype.card O ≠ 1 := by
    intro hone
    apply hx
    apply MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr
    simpa only [O] using hone
  have hOcardPos : 0 < Fintype.card O :=
    Fintype.card_pos_iff.mpr
      ⟨⟨x, MulAction.mem_orbit_self x⟩⟩
  have hOcardGt : 1 < Fintype.card O := by omega
  have hOcardLe : Fintype.card O ≤ 25 := by
    calc
      Fintype.card O ≤ Fintype.card X :=
        Fintype.card_le_of_injective
          (fun y : O => (y : X)) Subtype.val_injective
      _ = 25 := hcard
  have horbit :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      S x
  have hScardF : Fintype.card S = 121 := by
    rw [← Nat.card_eq_fintype_card, hScard]
  have horbit' :
      Fintype.card O * Fintype.card R = 121 := by
    rw [hScardF] at horbit
    simpa only [O, R] using horbit
  have hOdvd : Fintype.card O ∣ 121 :=
    ⟨Fintype.card R, horbit'.symm⟩
  have hOcard : Fintype.card O = 11 := by
    interval_cases Fintype.card O
    all_goals try norm_num at hOdvd
    all_goals omega
  have hRcard : Nat.card R = 11 := by
    rw [Nat.card_eq_fintype_card]
    rw [hOcard] at horbit'
    omega
  have hElevenDvdR : 11 ∣ Nat.card R := by
    rw [hRcard]
  obtain ⟨v, hvorder⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := R) 11 hElevenDvdR
  let vS : S := v
  let vP : P := vS
  let w : Equiv.Perm X := vP
  have hworder : orderOf w = 11 := by
    calc
      orderOf w = orderOf vP := Subgroup.orderOf_coe _
      _ = orderOf vS := Subgroup.orderOf_coe _
      _ = orderOf v := Subgroup.orderOf_coe _
      _ = 11 := hvorder
  have hvfix : vS • x = x :=
    MulAction.mem_stabilizer_iff.mp v.prop
  have hfixOrbit {y : X} (hy : y ∈ O) : w y = y := by
    obtain ⟨t, rfl⟩ :=
      MulAction.mem_orbit_iff.mp hy
    change vS • (t • x) = t • x
    calc
      vS • (t • x) = (vS * t) • x :=
        (mul_smul _ _ _).symm
      _ = (t * vS) • x := by rw [mul_comm' vS t]
      _ = t • (vS • x) := mul_smul _ _ _
      _ = t • x := by rw [hvfix]
  have hsuppSubset : (w.support : Set X) ⊆ Oᶜ := by
    intro y hy
    rw [Set.mem_compl_iff]
    intro hyO
    exact Equiv.Perm.mem_support.mp hy (hfixOrbit hyO)
  have hOncard : O.ncard = 11 := by
    rw [← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card]
    exact hOcard
  have hOcomplCard : Oᶜ.ncard = 14 := by
    have htotal := Set.ncard_add_ncard_compl O
    rw [Nat.card_eq_fintype_card, hcard, hOncard] at htotal
    omega
  have hsuppCard : w.support.card ≤ 14 := by
    rw [← Set.ncard_coe_finset]
    exact
      (Set.ncard_le_ncard hsuppSubset).trans_eq hOcomplCard
  have hwprime : (orderOf w).Prime := by
    rw [hworder]
    norm_num
  have hwcycle : w.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order hwprime (by omega)
  have hwsupport : w.support.card = 11 := by
    rw [← hwcycle.orderOf, hworder]
  exact hnotAlt
    (alternatingGroup_le_of_elevenCycle
      X P hcard h5 vP.prop hwcycle hwsupport)

end FiveTransitive.Degree25

end CFSG
