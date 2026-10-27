module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.RankThree.PartOne.AUTSL.Interface
import CFSG.RankThree.PartTwo.KFacts.L34Sylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKAutL34Cent
import CFSG.Permutation.FiveTransitive.OrbitComplementCardBound
import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.PCycleJordan
import CFSG.Permutation.FiveTransitive.LargePrimeCyclePrimitive
import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

private theorem no_order_fifteen_of_lieModel_psl_three_two {L : Type} [Group L]
    (hL : CFSG.Blueprint.LieModel L .PSL 3 2 2) : ¬ ∃ x : L, orderOf x = 15 := by
  rintro ⟨x, hx⟩
  have hx5 : orderOf (x ^ 5) = 3 := by
    rw [orderOf_pow' x (by norm_num), hx]
    norm_num
  have hmem : x ∈ Subgroup.centralizer ({x ^ 5} : Set L) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Commute.refl x).pow_right 5).eq
  have hdvd : orderOf x ∣ Nat.card (Subgroup.centralizer ({x ^ 5} : Set L)) := by
    have := orderOf_dvd_natCard (⟨x, hmem⟩ : Subgroup.centralizer ({x ^ 5} : Set L))
    rwa [Subgroup.orderOf_mk] at this
  rw [card_centralizer_of_orderOf_three_psl_three_four hL hx5, hx] at hdvd
  norm_num at hdvd

private def a8c3 : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 1 2

private def a8c5 : Equiv.Perm (Fin 8) :=
  Equiv.swap 3 4 * Equiv.swap 4 5 * Equiv.swap 5 6 * Equiv.swap 6 7

private def a8c35 : Equiv.Perm (Fin 8) := a8c3 * a8c5

private theorem a8c3_order : orderOf a8c3 = 3 := by
  apply orderOf_eq_prime (p := 3) (hp := ⟨by norm_num⟩)
  · ext i; fin_cases i <;> decide
  · intro h; exact absurd (congrArg (fun f : Equiv.Perm (Fin 8) => f 0) h) (by decide)

private theorem a8c5_order : orderOf a8c5 = 5 := by
  apply orderOf_eq_prime (p := 5) (hp := ⟨by norm_num⟩)
  · ext i; fin_cases i <;> decide
  · intro h; exact absurd (congrArg (fun f : Equiv.Perm (Fin 8) => f 3) h) (by decide)

private theorem a8c35_order : orderOf a8c35 = 15 := by
  have h : Commute a8c3 a8c5 := by rw [commute_iff_eq]; ext i; fin_cases i <;> decide
  have hcop : Nat.Coprime (orderOf a8c3) (orderOf a8c5) := by
    rw [a8c3_order, a8c5_order]; norm_num
  rw [a8c35, h.orderOf_mul_eq_mul_orderOf_of_coprime hcop, a8c3_order, a8c5_order]

private theorem a8c35_mem : a8c35 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  show Equiv.Perm.sign a8c35 = 1
  rw [a8c35, map_mul, show Equiv.Perm.sign a8c3 = 1 by decide,
    show Equiv.Perm.sign a8c5 = 1 by decide]
  norm_num

private theorem exists_orderOf_fifteen_alt_of_card_eight
    {Y : Type} [Fintype Y] [DecidableEq Y] (hY : Nat.card Y = 8) :
    ∃ g : alternatingGroup Y, orderOf g = 15 := by
  have hcard : Fintype.card Y = 8 := by rw [← Nat.card_eq_fintype_card]; exact hY
  let e : Y ≃ Fin 8 := Fintype.equivFinOfCardEq hcard
  refine ⟨(Equiv.altCongrHom e).symm ⟨a8c35, a8c35_mem⟩, ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  exact a8c35_order

private theorem symmetric_or_alternating_of_card
    {X : Type} [Fintype X] [DecidableEq X] (hn : 2 ≤ Nat.card X)
    (P : Subgroup (Equiv.Perm X))
    (hP : Nat.card P = (Fintype.card X).factorial ∨
      Nat.card P = (Fintype.card X).factorial / 2) :
    P = ⊤ ∨ P = alternatingGroup X := by
  have hperm : Nat.card (Equiv.Perm X) = (Fintype.card X).factorial := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card]
  rcases hP with htop | halt
  · exact Or.inl (Subgroup.eq_top_of_card_eq P (htop.trans hperm.symm))
  · right
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := P))
    rw [P.index_mul_card, hperm, halt]
    symm
    apply Nat.mul_div_cancel'
    have h := Nat.factorial_dvd_factorial hn
    simpa only [Nat.card_eq_fintype_card, Nat.factorial_two] using h

private theorem not_section_psu_three_eight {L : Type} [Group L]
    (hL : CFSG.Blueprint.LieModel L .PSU 3 2 3)
    (D : Subgroup (Equiv.Perm (Fin 9))) (N : Subgroup D) [N.Normal]
    (e : (D ⧸ N) ≃* L) : False := by
  obtain ⟨-, K, _, _, hKcard, ⟨eL⟩⟩ := hL.statedClassicalModel_of_ne_zero (by norm_num)
  have hcard : Nat.card L = 5515776 := by
    have hgcd := CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd (K := K)
      Nat.prime_two (by norm_num) hKcard
    have hSt : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ 3) K)) = 5515776 := by
      norm_num at hgcd ⊢
      omega
    exact (Nat.card_congr eL.toEquiv).trans hSt
  have hqcard : Nat.card (D ⧸ N) = 5515776 := (Nat.card_congr e.toEquiv).trans hcard
  have hle1 : Nat.card (D ⧸ N) ≤ Nat.card D :=
    Nat.le_of_dvd (Nat.card_pos (α := D)) (Subgroup.card_quotient_dvd_card N)
  have hle2 : Nat.card D ≤ Nat.card (Equiv.Perm (Fin 9)) :=
    Nat.card_le_card_of_injective D.subtype D.subtype_injective
  have h9 : Nat.card (Equiv.Perm (Fin 9)) = 362880 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  omega

private theorem not_section_alt9
    (D : Subgroup (Equiv.Perm (Fin 9))) (N : Subgroup D) [N.Normal]
    (x : D) (hc : (x : Equiv.Perm (Fin 9)).IsCycle)
    (hsupp : (x : Equiv.Perm (Fin 9)).support.card = 5)
    (htrans : MulAction.IsPretransitive D (Fin 9))
    (hQcard : Nat.card (D ⧸ N) = 20160) (hDle : Nat.card D ≤ 362880)
    (hDmul : Nat.card D = 20160 * Nat.card N) : False := by
  let _ : MulAction.IsPretransitive D (Fin 9) := htrans
  have hprim : MulAction.IsPreprimitive D (Fin 9) :=
    CFSG.FiveTransitive.LargePrimeCyclePrimitive.isPreprimitive D x.2 hc
      (by rw [hsupp]; norm_num) (by rw [hsupp]; simp)
  have hAlt : alternatingGroup (Fin 9) ≤ D :=
    CFSG.FiveTransitive.OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
      hprim (by norm_num : Nat.Prime 5) (by simp) hc hsupp x.2
  let q : alternatingGroup (Fin 9) →* (D ⧸ N) :=
    (QuotientGroup.mk' N).comp (Subgroup.inclusion hAlt)
  let _ : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  have hA9 : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hNle : Nat.card N ≤ 18 := by
    rw [hDmul] at hDle
    omega
  rcases (inferInstance : q.ker.Normal).eq_bot_or_eq_top with h | h
  · have hinj : Function.Injective q := MonoidHom.ker_eq_bot_iff q |>.mp h
    have hle : Nat.card (alternatingGroup (Fin 9)) ≤ Nat.card (D ⧸ N) :=
      Nat.card_le_card_of_injective q hinj
    rw [hA9, hQcard] at hle
    norm_num at hle
  · have hmem (a : alternatingGroup (Fin 9)) : (Subgroup.inclusion hAlt a : D) ∈ N := by
      have hq1 : q a = 1 := by
        have hmem : a ∈ q.ker := by rw [h]; trivial
        exact hmem
      have hq1' : (QuotientGroup.mk' N) (Subgroup.inclusion hAlt a) = 1 := hq1
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      exact hq1'
    have hinj : Function.Injective (Subgroup.inclusion hAlt) := by
      intro a b hab
      apply Subtype.ext
      have h2 := congrArg (fun z : D => (z : Equiv.Perm (Fin 9))) hab
      simpa using h2
    have hcardle : Nat.card (alternatingGroup (Fin 9)) ≤ Nat.card N := by
      let f : alternatingGroup (Fin 9) →* N :=
        { toFun := fun a => ⟨Subgroup.inclusion hAlt a, hmem a⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' := fun a b => Subtype.ext (map_mul _ a b) }
      exact Nat.card_le_card_of_injective f (fun a b hab => hinj (Subtype.ext_iff.mp hab))
    rw [hA9] at hcardle
    omega

private theorem not_section_eight_orbit {L : Type} [Group L]
    (hL : CFSG.Blueprint.LieModel L .PSL 3 2 2)
    (D : Subgroup (Equiv.Perm (Fin 9))) (N : Subgroup D) [N.Normal]
    (e : (D ⧸ N) ≃* L) (p : Fin 9)
    (hOncard : (MulAction.orbit D p).ncard = 8)
    (hDcard : Nat.card D = 20160 ∨ Nat.card D = 40320)
    (hNle : Nat.card N ≤ 2) : False := by
  have hcompl : ((MulAction.orbit D p)ᶜ : Set (Fin 9)).ncard = 1 := by
    rw [Set.ncard_compl, hOncard]; simp
  have hne : ((MulAction.orbit D p)ᶜ : Set (Fin 9)).ncard ≠ 0 := by rw [hcompl]; norm_num
  obtain ⟨p', hp'⟩ := Set.nonempty_of_ncard_ne_zero hne
  have hp'not : p' ∉ MulAction.orbit D p := hp'
  have hcompl' : (MulAction.orbit D p)ᶜ = ({p'} : Set (Fin 9)) := by
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hcompl
    rw [ha] at hp' ⊢
    rw [Set.mem_singleton_iff] at hp'
    rw [← hp']
  have hfix (d : D) : (d : Equiv.Perm (Fin 9)) p' = p' := by
    have hmem : (d : Equiv.Perm (Fin 9)) p' ∈ (MulAction.orbit D p)ᶜ := by
      rw [Set.mem_compl_iff]
      intro hcon
      have h1 : ((d⁻¹ : D) : Equiv.Perm (Fin 9)) ((d : Equiv.Perm (Fin 9)) p') ∈
          MulAction.orbit D p := MulAction.mem_orbit_of_mem_orbit (d⁻¹) hcon
      have h2 : ((d⁻¹ : D) : Equiv.Perm (Fin 9)) ((d : Equiv.Perm (Fin 9)) p') = p' := by
        simp
      rw [h2] at h1
      exact hp'not h1
    rw [hcompl'] at hmem
    exact Set.mem_singleton_iff.mp hmem
  let Y := {q : Fin 9 // q ≠ p'}
  have hYcard : Nat.card Y = 8 := by
    change Nat.card ↑({p'}ᶜ : Set (Fin 9)) = 8
    rw [Nat.card_coe_set_eq, Set.ncard_compl]
    simp
  have hfixY (d : D) : ∀ q : Fin 9, q ≠ p' → (d : Equiv.Perm (Fin 9)) q ≠ p' := by
    intro q hq hqd
    have h2 : (d : Equiv.Perm (Fin 9)).symm p' = p' :=
      ((Equiv.symm_apply_eq (e := (d : Equiv.Perm (Fin 9))))).mpr (hfix d).symm
    have h3 : (d : Equiv.Perm (Fin 9)).symm ((d : Equiv.Perm (Fin 9)) q) =
        (d : Equiv.Perm (Fin 9)).symm p' := by rw [hqd]
    rw [Equiv.symm_apply_apply, h2] at h3
    exact hq h3
  let φ : D →* Equiv.Perm Y :=
    { toFun := fun d => Equiv.Perm.subtypePermOfFintype (d : Equiv.Perm (Fin 9)) (hfixY d)
      map_one' := by ext q; rfl
      map_mul' := by intro a b; ext q; rfl }
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply Equiv.ext
    intro q
    by_cases hq : q = p'
    · subst hq; rw [hfix a, hfix b]
    · have h3 := congrArg (fun f : Equiv.Perm Y => f ⟨q, hq⟩) hab
      rw [show φ a ⟨q, hq⟩ = ⟨(a : Equiv.Perm (Fin 9)) q, hfixY a q hq⟩ from rfl,
        show φ b ⟨q, hq⟩ = ⟨(b : Equiv.Perm (Fin 9)) q, hfixY b q hq⟩ from rfl] at h3
      simpa using congrArg Subtype.val h3
  let P : Subgroup (Equiv.Perm Y) := φ.range
  have hPcard : Nat.card P = Nat.card D := Nat.card_range_of_injective hφinj
  have hYfcard : Fintype.card Y = 8 := by rw [← Nat.card_eq_fintype_card]; exact hYcard
  have hPcase : P = ⊤ ∨ P = alternatingGroup Y := by
    apply symmetric_or_alternating_of_card
    · rw [hYcard]; norm_num
    · rw [hPcard, hYfcard]
      rcases hDcard with h | h <;> rw [h] <;> norm_num [Nat.factorial]
  have hAltY : alternatingGroup Y ≤ P := by
    rcases hPcase with h | h
    · rw [h]; exact le_top
    · rw [h]
  obtain ⟨g, hg⟩ := exists_orderOf_fifteen_alt_of_card_eight hYcard
  have hgP : (g : Equiv.Perm Y) ∈ P := hAltY g.2
  obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hgP
  have hdord : orderOf d = 15 := by
    have h1 : orderOf (φ d) = 15 := by
      rw [hd, ← Subgroup.orderOf_mk (g : Equiv.Perm Y) g.2]
      exact hg
    exact (orderOf_injective φ hφinj d).symm.trans h1
  have hm_dvd : orderOf (QuotientGroup.mk' N d) ∣ 15 := by
    rw [orderOf_dvd_iff_pow_eq_one, ← map_pow]
    rw [show d ^ 15 = 1 by rw [← hdord]; exact pow_orderOf_eq_one d, map_one]
  have hdvds : orderOf (QuotientGroup.mk' N d) ∈ Nat.divisors 15 :=
    Nat.mem_divisors.mpr ⟨hm_dvd, by norm_num⟩
  rw [show Nat.divisors 15 = {1, 3, 5, 15} by decide] at hdvds
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdvds
  have hy15 : orderOf (QuotientGroup.mk' N d) = 15 := by
    rcases hdvds with h | h | h | h
    · exfalso
      have hy1 : QuotientGroup.mk' N d = 1 := orderOf_eq_one_iff.mp h
      have hdN : d ∈ N := by
        rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
        exact hy1
      have hdvd : orderOf d ∣ Nat.card N := by
        have := orderOf_dvd_natCard (⟨d, hdN⟩ : N)
        rwa [Subgroup.orderOf_mk] at this
      rw [hdord] at hdvd
      have := Nat.le_of_dvd (Nat.card_pos (α := N)) hdvd
      omega
    · exfalso
      have hp3 : (QuotientGroup.mk' N d) ^ 3 = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (by rw [h])
      have hdN : d ^ 3 ∈ N := by
        rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
        simpa only [map_pow] using hp3
      have hdvd : orderOf (d ^ 3) ∣ Nat.card N := by
        have := orderOf_dvd_natCard (⟨d ^ 3, hdN⟩ : N)
        rwa [Subgroup.orderOf_mk] at this
      have h3 : orderOf (d ^ 3) = 5 := by
        rw [orderOf_pow' d (by norm_num), hdord]
        norm_num
      rw [h3] at hdvd
      have := Nat.le_of_dvd (Nat.card_pos (α := N)) hdvd
      omega
    · exfalso
      have hp5 : (QuotientGroup.mk' N d) ^ 5 = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (by rw [h])
      have hdN : d ^ 5 ∈ N := by
        rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
        simpa only [map_pow] using hp5
      have hdvd : orderOf (d ^ 5) ∣ Nat.card N := by
        have := orderOf_dvd_natCard (⟨d ^ 5, hdN⟩ : N)
        rwa [Subgroup.orderOf_mk] at this
      have h3 : orderOf (d ^ 5) = 3 := by
        rw [orderOf_pow' d (by norm_num), hdord]
        norm_num
      rw [h3] at hdvd
      have := Nat.le_of_dvd (Nat.card_pos (α := N)) hdvd
      omega
    · exact h
  exact no_order_fifteen_of_lieModel_psl_three_two hL
    ⟨e (QuotientGroup.mk' N d), (MulEquiv.orderOf_eq e (QuotientGroup.mk' N d)).trans hy15⟩

theorem not_nonempty_mulEquiv_quotient_perm_fin_nine_L34_or_U38 {L : Type} [Group L]
    (hL : CFSG.Blueprint.LieModel L .PSL 3 2 2 ∨ CFSG.Blueprint.LieModel L .PSU 3 2 3)
    (D : Subgroup (Equiv.Perm (Fin 9))) (N : Subgroup D) [N.Normal] :
    ¬ Nonempty ((D ⧸ N) ≃* L) := by
  rintro ⟨e⟩
  rcases hL with hL | hL
  · obtain ⟨K, _, _, hK, ⟨φL⟩⟩ :=
      CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
    have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
    have hLcard : Nat.card L = 20160 :=
      (Nat.card_congr φL.toEquiv).trans (CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL hK4)
    have hno15 := no_order_fifteen_of_lieModel_psl_three_two hL
    have hqcard : Nat.card (D ⧸ N) = 20160 := (Nat.card_congr e.toEquiv).trans hLcard
    have h20160dvd : 20160 ∣ Nat.card D := by
      rw [← hqcard]
      exact Subgroup.card_quotient_dvd_card N
    have hDle : Nat.card D ≤ 362880 := by
      have h := Nat.card_le_card_of_injective D.subtype D.subtype_injective
      have h9 : Nat.card (Equiv.Perm (Fin 9)) = 362880 := by
        rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      rwa [h9] at h
    have hDmul : Nat.card D = 20160 * Nat.card N := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hqcard]
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D) 5 (hp := ⟨by norm_num⟩)
      ((by norm_num : 5 ∣ 20160).trans h20160dvd)
    have hg : orderOf (x : Equiv.Perm (Fin 9)) = 5 := (Subgroup.orderOf_coe x).trans hx
    have hc : (x : Equiv.Perm (Fin 9)).IsCycle := by
      apply Equiv.Perm.isCycle_of_prime_order
      · rw [hg]; norm_num
      · rw [hg]
        have h9 : (x : Equiv.Perm (Fin 9)).support.card ≤ 9 := by
          simpa using Finset.card_le_univ (x : Equiv.Perm (Fin 9)).support
        omega
    have hsupp : (x : Equiv.Perm (Fin 9)).support.card = 5 := hc.orderOf.symm.trans hg
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [hsupp]; norm_num)
    set o : ℕ := Nat.card (MulAction.orbit D p) with ho_def
    have hle : Nat.card D ≤ Nat.factorial o * Nat.factorial (9 - o) := by
      have hthis := CFSG.FiveTransitive.OrbitComplementCardBound.card_le_factorials D p
      simpa [← ho_def, Nat.card_fin] using hthis
    have hsub : ((x : Equiv.Perm (Fin 9)).support : Set (Fin 9)) ⊆ MulAction.orbit D p := by
      intro q hq
      have hp' : (x : Equiv.Perm (Fin 9)) p ≠ p := Equiv.Perm.mem_support.mp hp
      have hq' : (x : Equiv.Perm (Fin 9)) q ≠ q := Equiv.Perm.mem_support.mp hq
      obtain ⟨i, hi⟩ := hc.exists_pow_eq hp' hq'
      rw [← hi]
      exact MulAction.mem_orbit_iff.mpr ⟨(x : D) ^ i, rfl⟩
    have hOge5 : 5 ≤ o := by
      have h1 : ((x : Equiv.Perm (Fin 9)).support : Set (Fin 9)).ncard ≤
          (MulAction.orbit D p).ncard := Set.ncard_le_ncard hsub
      rw [Set.ncard_coe_finset, hsupp] at h1
      have h2 : o = (MulAction.orbit D p).ncard := by rw [ho_def, Nat.card_coe_set_eq]
      omega
    by_cases hO9 : o = 9
    · have htrans : MulAction.IsPretransitive D (Fin 9) := by
        rw [MulAction.isPretransitive_iff_orbit_eq_univ p]
        rw [Set.eq_univ_iff_ncard]
        rw [← Nat.card_coe_set_eq, ← ho_def, hO9, Nat.card_fin]
      exact not_section_alt9 D N x hc hsupp htrans hqcard hDle hDmul
    · have ho_le8 : o ≤ 8 := by
        have h9 : Nat.card (MulAction.orbit D p) ≤ 9 := by
          simpa [Nat.card_fin] using Nat.card_le_card_of_injective
            (fun z : ↑(MulAction.orbit D p) => z.val) Subtype.val_injective
        rw [← ho_def] at h9
        omega
      have ho8 : o = 8 := by
        by_contra hne
        have h7 : o ≤ 7 := by omega
        have harith : Nat.factorial o * Nat.factorial (9 - o) ≤ 10080 := by
          interval_cases o <;> decide
        have hbd : Nat.card D ≤ 10080 := by
          calc Nat.card D ≤ Nat.factorial o * Nat.factorial (9 - o) := hle
            _ ≤ 10080 := harith
        have hge : 20160 ≤ Nat.card D :=
          Nat.le_of_dvd (Nat.card_pos (α := D)) h20160dvd
        omega
      have hOncard : (MulAction.orbit D p).ncard = 8 := by
        rw [← Nat.card_coe_set_eq, ← ho_def]
        exact ho8
      have hDle40320 : Nat.card D ≤ 40320 := by
        have h40320 : Nat.factorial 8 * Nat.factorial (9 - 8) = 40320 := by decide
        calc Nat.card D ≤ Nat.factorial o * Nat.factorial (9 - o) := hle
          _ = 40320 := by rw [ho8]; exact h40320
      have hDcard : Nat.card D = 20160 ∨ Nat.card D = 40320 := by
        obtain ⟨k, hk⟩ := h20160dvd
        have hkpos : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with h0 | hpos
          · rw [h0, mul_zero] at hk
            have : 0 < Nat.card D := Nat.card_pos
            omega
          · exact hpos
        omega
      have hNle : Nat.card N ≤ 2 := by
        rw [hDmul] at hDle40320
        omega
      exact not_section_eight_orbit hL D N e p hOncard hDcard hNle
  · exact not_section_psu_three_eight hL D N e

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
