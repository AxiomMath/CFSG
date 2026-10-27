module

public import CFSG.Permutation.FiveTransitive.Degree24SevenTransferCases
public import CFSG.Permutation.FiveTransitive.Degree19CoprimeComplement

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction Subgroup
open scoped Pointwise

private theorem small_divisor_eq_of_mod_seven
    (n d : ℕ)
    (hn : n = 5 ∨ n = 9 ∨ n = 25 ∨ n = 81)
    (hd : d ∣ n)
    (hmod : n % 7 = d % 7) :
    d = n := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    have hdle : d ≤ _ :=
      Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *

private theorem seven_group_action_on_selected_group_is_trivial
    (T R : Type) [Group T] [Group R]
    [Fintype T] [Fintype R]
    [MulDistribMulAction T R]
    (hT : IsPGroup 7 T)
    (hRcard :
      Nat.card R = 5 ∨ Nat.card R = 9 ∨
        Nat.card R = 25 ∨ Nat.card R = 81) :
    ∀ t : T, ∀ r : R, t • r = r := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let F : Subgroup R :=
    Degree19.fixedPointsSubgroup T R
  have hFset :
      (F : Set R) = MulAction.fixedPoints T R :=
    rfl
  let eF :
      F ≃ MulAction.fixedPoints T R :=
    Set.equivOfEq hFset
  have hmod :
      Nat.card R % 7 = Nat.card F % 7 := by
    have h :=
      hT.card_modEq_card_fixedPoints R
    change
      Nat.card R % 7 =
        Nat.card (MulAction.fixedPoints T R) % 7 at h
    calc
      Nat.card R % 7 =
          Nat.card (MulAction.fixedPoints T R) % 7 :=
        h
      _ = Nat.card F % 7 :=
        congrArg (fun n => n % 7)
          (Nat.card_congr eF).symm
  have hdiv : Nat.card F ∣ Nat.card R :=
    Subgroup.card_subgroup_dvd_card F
  have hFcard : Nat.card F = Nat.card R :=
    small_divisor_eq_of_mod_seven
      (Nat.card R) (Nat.card F) hRcard hdiv hmod
  have hFtop : F = ⊤ :=
    Subgroup.eq_top_of_card_eq F hFcard
  intro t r
  have hr : r ∈ F := by
    rw [hFtop]
    exact Subgroup.mem_top r
  exact hr t

private theorem exists_fixed_point_of_seven_group_action
    (T α : Type) [Group T] [Fintype T]
    [Fintype α] [MulAction T α]
    (hT : IsPGroup 7 T)
    (hnotSeven : ¬7 ∣ Nat.card α) :
    ∃ a : α, ∀ t : T, t • a = a := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ :=
    hT.nonempty_fixed_point_of_prime_not_dvd_card
      α hnotSeven
  exact ⟨a, ha⟩

private theorem fixed_selected_sylow_under_seven_action_is_trivial
    (T Q : Type) [Group T] [Group Q]
    [Fintype T] [Fintype Q]
    [MulDistribMulAction T Q]
    (hT : IsPGroup 7 T)
    {p : ℕ} [Fact p.Prime]
    (R : Sylow p Q)
    (hRfixed : ∀ t : T, t • R = R)
    (hRcard :
      Nat.card R = 5 ∨ Nat.card R = 9 ∨
        Nat.card R = 25 ∨ Nat.card R = 81) :
    ∀ t : T, ∀ r : R, t • (r : Q) = r := by
  classical
  let rsmul : SMul T R :=
    { smul := fun t r =>
        (⟨t • (r : Q), by
          have hr :
              t • (r : Q) ∈
                (t • R : Sylow p Q) := by
            exact Subgroup.smul_mem_pointwise_smul
              (r : Q) t (R : Subgroup Q) r.prop
          rwa [hRfixed t] at hr⟩ : R) }
  letI : SMul T R := rsmul
  letI : MulDistribMulAction T R :=
    Subtype.coe_injective.mulDistribMulAction
      (R : Subgroup Q).subtype (fun _ _ => rfl)
  have htr :=
    seven_group_action_on_selected_group_is_trivial
      T R hT hRcard
  intro t r
  exact congrArg Subtype.val (htr t r)

private theorem fixed_sylow_card_dvd_centralizer
    {H : Type} [Group H] [Fintype H]
    (S : Sylow 7 H)
    (Q : Subgroup H) [Q.Normal]
    [MulDistribMulAction S Q]
    {p : ℕ} [Fact p.Prime]
    (R : Sylow p Q)
    (hsmul :
      ∀ t : S, ∀ q : Q,
        Q.subtype (t • q) =
          (t : H) * (q : H) * (t : H)⁻¹)
    (hRtrivial :
      ∀ t : S, ∀ r : R, t • (r : Q) = r) :
    Nat.card R ∣
      Nat.card
        (Subgroup.centralizer (S : Set H)) := by
  let C : Subgroup H :=
    Subgroup.centralizer (S : Set H)
  let inclusion : R →* C := {
    toFun := fun r =>
      ⟨((r : Q) : H), by
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        let tS : S := ⟨t, ht⟩
        have hfixQ := hRtrivial tS r
        have hfixH := congrArg Q.subtype hfixQ
        rw [hsmul] at hfixH
        change
          (tS : H) * ((r : Q) : H) * (tS : H)⁻¹ =
            ((r : Q) : H) at hfixH
        calc
          t * ((r : Q) : H) =
              (t * ((r : Q) : H) * t⁻¹) * t := by
            group
          _ = ((r : Q) : H) * t := by
            simpa only [tS] using
              congrArg (fun y : H => y * t) hfixH⟩
    map_one' := by
      apply Subtype.ext
      rfl
    map_mul' := by
      intro a b
      apply Subtype.ext
      rfl }
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    apply Q.subtype_injective
    exact congrArg
      (fun c : C => (c : H)) hab
  exact
    Subgroup.card_dvd_of_injective
      inclusion hinclusion

theorem five_point_stabilizer_card_ne_two_thousand_sixteen_and_ne_one_million_eighty_eight_thousand_six_hundred_forty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ≠ 2016 ∧
      Nat.card (fixingSubgroup P s) ≠ 1088640 := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  have hFalse
      (hCases :
        Nat.card H = 2016 ∨
          Nat.card H = 1088640) :
      False := by
    let S : Sylow 7 H := Sylow.nonempty.some
    have hScard : Nat.card S = 7 := by
      rcases hCases with hH | hH
      · exact
          sylow_card_eq_prime_of_card_eq_prime_mul
            H 7 288 (by norm_num) (by norm_num)
              (by simpa using hH) S
      · exact
          sylow_card_eq_prime_of_card_eq_prime_mul
            H 7 155520 (by norm_num) (by norm_num)
              (by simpa using hH) S
    have hnormalizer :
        Subgroup.normalizer (S : Set H) ≤
          Subgroup.centralizer (S : Set H) := by
      apply
        selected_sylowSeven_normalizer_le_centralizer
          X P hcard h5 hnotAlt s hs
      simpa only [H] using hCases
    let transfer : H →* S :=
      MonoidHom.transferSylow S hnormalizer
    let Q : Subgroup H := transfer.ker
    letI : Q.Normal := by
      dsimp only [Q, transfer]
      infer_instance
    have hcomplement : IsComplement' Q S := by
      simpa only [Q, transfer] using
        MonoidHom.ker_transferSylow_isComplement'
          S hnormalizer
    have hQcard :
        Nat.card Q = 288 ∨
          Nat.card Q = 155520 := by
      have hcardMul := hcomplement.card_mul
      rcases hCases with hH | hH
      · left
        rw [hScard, hH] at hcardMul
        nlinarith
      · right
        rw [hScard, hH] at hcardMul
        nlinarith
    letI : MulDistribMulAction S Q :=
      MulDistribMulAction.compHom Q
        ((MulAut.conjNormal (H := Q)).comp
          (S : Subgroup H).subtype)
    have hCdvd :
        Nat.card
            (Subgroup.centralizer (S : Set H)) ∣
          98 := by
      simpa only [H] using
        sylowSeven_centralizer_card_dvd_ninety_eight
          X P hcard h5 hnotAlt s hs S hScard
    rcases hQcard with hQcard | hQcard
    · letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      let R₀ : Sylow 3 Q := Sylow.nonempty.some
      have hR₀card : Nat.card R₀ = 9 := by
        rw [R₀.card_eq_multiplicity, hQcard]
        rw [show 288 = 2 ^ 5 * 3 ^ 2 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num),
          Finsupp.add_apply,
          (show Nat.Prime 2 by norm_num).factorization_pow,
          (show Nat.Prime 3 by norm_num).factorization_pow]
        norm_num
      have hR₀index : R₀.index = 32 := by
        have hproduct := R₀.index_mul_card
        rw [hR₀card, hQcard] at hproduct
        omega
      have hSylowDvd :
          Nat.card (Sylow 3 Q) ∣ 32 := by
        rw [← hR₀index]
        exact R₀.card_dvd_index
      have hSevenNotDvd :
          ¬7 ∣ Nat.card (Sylow 3 Q) := by
        intro hSeven
        have := hSeven.trans hSylowDvd
        norm_num at this
      obtain ⟨R, hRfixed⟩ :=
        exists_fixed_point_of_seven_group_action
          S (Sylow 3 Q) S.2 hSevenNotDvd
      have hRcard : Nat.card R = 9 := by
        calc
          Nat.card R = Nat.card R₀ :=
            Nat.card_congr (Sylow.equiv R R₀).toEquiv
          _ = 9 := hR₀card
      have hRtrivial :
          ∀ t : S, ∀ r : R,
            t • (r : Q) = (r : Q) :=
        fixed_selected_sylow_under_seven_action_is_trivial
          S Q S.2 R hRfixed
            (Or.inr (Or.inl hRcard))
      have hNineDvd :
          9 ∣
            Nat.card
              (Subgroup.centralizer (S : Set H)) := by
        rw [← hRcard]
        exact
          fixed_sylow_card_dvd_centralizer
            S Q R (by
              intro t q
              rfl) hRtrivial
      have := hNineDvd.trans hCdvd
      norm_num at this
    · letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      let R₀ : Sylow 5 Q := Sylow.nonempty.some
      have hR₀card : Nat.card R₀ = 5 := by
        rw [R₀.card_eq_multiplicity, hQcard]
        rw [show 155520 =
              2 ^ 7 * (3 ^ 5 * 5 ^ 1) by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num),
          Finsupp.add_apply,
          Nat.factorization_mul (by norm_num) (by norm_num),
          Finsupp.add_apply,
          (show Nat.Prime 2 by norm_num).factorization_pow,
          (show Nat.Prime 3 by norm_num).factorization_pow,
          (show Nat.Prime 5 by norm_num).factorization_pow]
        norm_num
      have hR₀index : R₀.index = 31104 := by
        have hproduct := R₀.index_mul_card
        rw [hR₀card, hQcard] at hproduct
        omega
      have hSylowDvd :
          Nat.card (Sylow 5 Q) ∣ 31104 := by
        rw [← hR₀index]
        exact R₀.card_dvd_index
      have hSevenNotDvd :
          ¬7 ∣ Nat.card (Sylow 5 Q) := by
        intro hSeven
        have := hSeven.trans hSylowDvd
        norm_num at this
      obtain ⟨R, hRfixed⟩ :=
        exists_fixed_point_of_seven_group_action
          S (Sylow 5 Q) S.2 hSevenNotDvd
      have hRcard : Nat.card R = 5 := by
        calc
          Nat.card R = Nat.card R₀ :=
            Nat.card_congr (Sylow.equiv R R₀).toEquiv
          _ = 5 := hR₀card
      have hRtrivial :
          ∀ t : S, ∀ r : R,
            t • (r : Q) = (r : Q) :=
        fixed_selected_sylow_under_seven_action_is_trivial
          S Q S.2 R hRfixed (Or.inl hRcard)
      have hFiveDvd :
          5 ∣
            Nat.card
              (Subgroup.centralizer (S : Set H)) := by
        rw [← hRcard]
        exact
          fixed_sylow_card_dvd_centralizer
            S Q R (by
              intro t q
              rfl) hRtrivial
      have := hFiveDvd.trans hCdvd
      norm_num at this
  constructor
  · intro hH
    exact hFalse (Or.inl (by simpa only [H] using hH))
  · intro hH
    exact hFalse (Or.inr (by simpa only [H] using hH))

end FiveTransitive.Degree24

end CFSG
