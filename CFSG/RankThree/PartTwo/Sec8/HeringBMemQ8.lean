module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringBMem

open scoped commutatorElement

theorem card_modEq_filter_fix {H : Type*} [DecidableEq H] (p : ℕ) [hp : Fact p.Prime]
    (f : H → H) (S : Finset H) (hS : ∀ x ∈ S, f x ∈ S) (hinj : Function.Injective f)
    (hper : ∀ x, f^[p] x = x) :
    S.card ≡ (S.filter (fun x => f x = x)).card [MOD p] := by
  let g : S → S := fun x => ⟨f x.1, hS x.1 x.2⟩
  have hg : Function.Injective g := fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab))
  let σ : Equiv.Perm S := Equiv.ofBijective g ⟨hg, Finite.injective_iff_surjective.mp hg⟩
  have hiter : ∀ (k : ℕ) (x : S), ((σ ^ k) x : H) = f^[k] x.1 := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, Function.iterate_succ_apply']
      exact congrArg f (ih x)
  have hσ : σ ^ p ^ 1 = 1 := by
    rw [pow_one]
    ext x
    rw [hiter p x, hper]
    rfl
  have h1 := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) hσ
  have h2 : σ.supportᶜ.card = (S.filter (fun x => f x = x)).card := by
    apply Finset.card_bij (fun a _ => a.1)
    · intro a ha
      have hfix : σ a = a := by
        have h := ha
        rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at h
        exact h
      rw [Finset.mem_filter]
      exact ⟨a.2, congrArg Subtype.val hfix⟩
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro b hb
      obtain ⟨hbS, hfb⟩ := Finset.mem_filter.mp hb
      refine ⟨⟨b, hbS⟩, ?_, rfl⟩
      rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      exact Subtype.ext hfb
  rw [Fintype.card_coe, h2] at h1
  exact h1.symm

theorem not_comm_of_gen {H : Type*} [Group H] (φ : H →* H) (hφ : ∀ x, φ (φ (φ x)) = x)
    (hgen : ∀ K : Subgroup H, (∀ x, x * φ x⁻¹ ∈ K) → K = ⊤)
    (hcomm : ∀ a b : H, a * b = b * a) {z : H} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hzf : φ z = z) : False := by
  have hlc : ∀ a b c : H, a * (b * c) = b * (a * c) := fun a b c => by
    rw [← mul_assoc, hcomm a b, mul_assoc]
  have ac4 : ∀ a b c d : H, a * b * (c * d) = a * c * (b * d) := fun a b c d => by
    rw [mul_assoc, hlc b c d, ← mul_assoc]
  let N : H →* H := MonoidHom.mk' (fun x => x * φ x * φ (φ x)) (fun a b => by
    show (a * b) * φ (a * b) * φ (φ (a * b)) = (a * φ a * φ (φ a)) * (b * φ b * φ (φ b))
    simp only [map_mul]
    rw [ac4 a b (φ a) (φ b), ac4 (a * φ a) (b * φ b) (φ (φ a)) (φ (φ b))])
  have hNφ : ∀ x, N (φ x) = N x := by
    intro x
    show φ x * φ (φ x) * φ (φ (φ x)) = x * φ x * φ (φ x)
    rw [hφ x, mul_assoc x]
    exact hcomm _ x
  have hker : N.ker = ⊤ := by
    apply hgen
    intro x
    simp only [MonoidHom.mem_ker, map_mul, map_inv, hNφ, mul_inv_cancel]
  have hz : z ∈ N.ker := by
    rw [hker]
    exact Subgroup.mem_top z
  rw [MonoidHom.mem_ker] at hz
  change z * φ z * φ (φ z) = 1 at hz
  rw [hzf, hzf] at hz
  rw [mul_assoc, ← sq, hz2, mul_one] at hz
  exact hz1 hz

theorem exists_unique_involution_of_card_eight {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    (hH : Fintype.card H = 8) (φ : H →* H) (hφ : ∀ x, φ (φ (φ x)) = x)
    (hgen : ∀ K : Subgroup H, (∀ x, x * φ x⁻¹ ∈ K) → K = ⊤) :
    ∃ z : H, z ≠ 1 ∧ ∀ x : H, x ≠ 1 → x = z ∨ x ^ 2 = z := by
  have hinj : Function.Injective φ := by
    intro a b hab
    calc a = φ (φ (φ a)) := (hφ a).symm
      _ = φ (φ (φ b)) := by rw [hab]
      _ = b := hφ b
  have hper3 : ∀ x, (⇑φ)^[3] x = x := hφ
  have hC3 : (Finset.univ : Finset H).card ≡
      ((Finset.univ : Finset H).filter (fun x => φ x = x)).card [MOD 3] :=
    card_modEq_filter_fix 3 (⇑φ) Finset.univ (fun x _ => Finset.mem_univ _) hinj hper3
  rw [Finset.card_univ, hH] at hC3
  let C : Subgroup H :=
    { carrier := {x | φ x = x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        exact map_one φ
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha] }
  have hCcard' : Nat.card C = Nat.card {x : H // φ x = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  have hCcard : Nat.card C = ((Finset.univ : Finset H).filter (fun x => φ x = x)).card := by
    rw [hCcard', Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hdvd : ((Finset.univ : Finset H).filter (fun x => φ x = x)).card ∣ 8 := by
    have h := Subgroup.card_subgroup_dvd_card C
    rw [hCcard, Nat.card_eq_fintype_card, hH] at h
    exact h
  have hc8 : ((Finset.univ : Finset H).filter (fun x => φ x = x)).card ≠ 8 := by
    intro h8
    have hall : ∀ x : H, φ x = x := by
      intro x
      have hfull : (Finset.univ : Finset H).filter (fun x => φ x = x) = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [h8, hH])
      have hx : x ∈ (Finset.univ : Finset H).filter (fun x => φ x = x) := by
        rw [hfull]
        exact Finset.mem_univ x
      exact (Finset.mem_filter.mp hx).2
    obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card (by rw [hH]; norm_num) (1 : H)
    have hbot : (⊥ : Subgroup H) = ⊤ := hgen ⊥ fun y => by
      rw [map_inv, hall y, mul_inv_cancel]
      exact Subgroup.one_mem _
    have hxmem : x ∈ (⊥ : Subgroup H) := by
      rw [hbot]
      exact Subgroup.mem_top x
    exact hx (Subgroup.mem_bot.mp hxmem)
  have hcpos : 0 < ((Finset.univ : Finset H).filter (fun x => φ x = x)).card :=
    Finset.card_pos.mpr ⟨1, by simp [map_one]⟩
  have hc2 : ((Finset.univ : Finset H).filter (fun x => φ x = x)).card = 2 := by
    generalize ((Finset.univ : Finset H).filter (fun x => φ x = x)).card = c at hC3 hdvd hc8 hcpos ⊢
    have hle : c ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    unfold Nat.ModEq at hC3
    interval_cases c <;> omega
  obtain ⟨z, hzmem, hz1⟩ : ∃ z ∈ (Finset.univ : Finset H).filter (fun x => φ x = x), z ≠ 1 := by
    have h1lt : 1 < ((Finset.univ : Finset H).filter (fun x => φ x = x)).card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1lt
    by_cases ha1 : a = 1
    · exact ⟨b, hb, fun hb1 => hab (ha1.trans hb1.symm)⟩
    · exact ⟨a, ha, ha1⟩
  have hzf : φ z = z := (Finset.mem_filter.mp hzmem).2
  have hpair : ({1, z} : Finset H) = (Finset.univ : Finset H).filter (fun x => φ x = x) := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      rcases Finset.mem_insert.mp hy with h | h
      · rw [h]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, map_one φ⟩
      · rw [Finset.mem_singleton.mp h]
        exact hzmem
    · exact le_of_eq (by rw [hc2, Finset.card_pair_eq_two_iff.mpr (Ne.symm hz1)])
  have hstar : ∀ x : H, φ x = x → x = 1 ∨ x = z := by
    intro x hx
    have hxmem : x ∈ ({1, z} : Finset H) := by
      rw [hpair]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
    rcases Finset.mem_insert.mp hxmem with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  have hz2 : z ^ 2 = 1 := by
    rcases hstar (z ^ 2) (by rw [map_pow, hzf]) with h | h
    · exact h
    · exfalso
      apply hz1
      have h' : z * z = z * 1 := by rw [mul_one, ← sq, h]
      exact mul_left_cancel h'
  obtain ⟨A, hAdef⟩ : ∃ A : Finset H, A = (Finset.univ : Finset H).filter (fun x => x ≠ 1) :=
    ⟨_, rfl⟩
  have hmemA : ∀ x, x ∈ A ↔ x ≠ 1 := by
    intro x
    rw [hAdef, Finset.mem_filter]
    simp
  have hAcard : A.card = 7 := by
    rw [hAdef, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hH]
  have hsplit : (A.filter (fun x => x ^ 2 = 1)).card +
      (A.filter (fun x => ¬ x ^ 2 = 1)).card = 7 := by
    rw [← hAcard]
    exact Finset.card_filter_add_card_filter_not _
  have hI_stable : ∀ x ∈ A.filter (fun x : H => x ^ 2 = 1),
      φ x ∈ A.filter (fun x : H => x ^ 2 = 1) := by
    intro x hx
    obtain ⟨hxA, hx2⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨(hmemA _).mpr fun h => ?_, ?_⟩
    · exact (hmemA x).mp hxA ((map_eq_one_iff φ hinj).mp h)
    · rw [← map_pow, hx2, map_one]
  have hIfix : ((A.filter (fun x : H => x ^ 2 = 1)).filter (fun x => φ x = x)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨z, ?_⟩
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_singleton, hmemA]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hfx⟩
      rcases hstar x hfx with h | h
      · exact absurd h hx1
      · exact h
    · rintro rfl
      exact ⟨⟨hz1, hz2⟩, hzf⟩
  have hI3 : (A.filter (fun x : H => x ^ 2 = 1)).card ≡
      ((A.filter (fun x : H => x ^ 2 = 1)).filter (fun x => φ x = x)).card [MOD 3] :=
    card_modEq_filter_fix 3 (⇑φ) _ hI_stable hinj hper3
  rw [hIfix] at hI3
  have hN_stable : ∀ x ∈ A.filter (fun x : H => ¬ x ^ 2 = 1),
      x⁻¹ ∈ A.filter (fun x : H => ¬ x ^ 2 = 1) := by
    intro x hx
    obtain ⟨hxA, hx2⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨(hmemA _).mpr (inv_ne_one.mpr ((hmemA x).mp hxA)), ?_⟩
    rw [inv_pow, inv_eq_one]
    exact hx2
  have hN2 : (A.filter (fun x : H => ¬ x ^ 2 = 1)).card ≡
      ((A.filter (fun x : H => ¬ x ^ 2 = 1)).filter (fun x => x⁻¹ = x)).card [MOD 2] :=
    card_modEq_filter_fix 2 (fun x : H => x⁻¹) _ hN_stable inv_injective
      (fun x => by show x⁻¹⁻¹ = x; exact inv_inv x)
  have hN2fix : (A.filter (fun x : H => ¬ x ^ 2 = 1)).filter (fun x => x⁻¹ = x) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx hxinv
    obtain ⟨_, hx2⟩ := Finset.mem_filter.mp hx
    apply hx2
    rw [sq]
    calc x * x = x * x⁻¹ := by rw [hxinv]
      _ = 1 := mul_inv_cancel x
  rw [hN2fix, Finset.card_empty] at hN2
  have hI_odd : (A.filter (fun x : H => x ^ 2 = 1)).card = 1 ∨
      (A.filter (fun x : H => x ^ 2 = 1)).card = 7 := by
    unfold Nat.ModEq at hI3 hN2
    omega
  by_cases h7 : (A.filter (fun x : H => x ^ 2 = 1)).card = 7
  ·
    exfalso
    have hIA : A.filter (fun x : H => x ^ 2 = 1) = A :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hsq : ∀ x : H, x ^ 2 = 1 := by
      intro x
      by_cases hx : x = 1
      · rw [hx, one_pow]
      · have hxA : x ∈ A := (hmemA x).mpr hx
        rw [← hIA] at hxA
        exact (Finset.mem_filter.mp hxA).2
    have hinv : ∀ x : H, x⁻¹ = x := fun x =>
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq x)
    have hcomm : ∀ a b : H, a * b = b * a := by
      intro a b
      have h1 : (a * b)⁻¹ = a * b :=
        inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq (a * b))
      rw [mul_inv_rev, hinv, hinv] at h1
      exact h1.symm
    exact not_comm_of_gen φ hφ hgen hcomm hz1 hz2 hzf
  ·
    have hI1 : (A.filter (fun x : H => x ^ 2 = 1)).card = 1 := by omega
    have hzI : z ∈ A.filter (fun x : H => x ^ 2 = 1) :=
      Finset.mem_filter.mpr ⟨(hmemA z).mpr hz1, hz2⟩
    have huniq : ∀ y ∈ A.filter (fun x : H => x ^ 2 = 1), y = z := fun y hy =>
      Finset.card_le_one.mp (by omega) y hy z hzI
    refine ⟨z, hz1, fun x hx => ?_⟩
    by_cases hx2 : x ^ 2 = 1
    · exact Or.inl (huniq x (Finset.mem_filter.mpr ⟨(hmemA x).mpr hx, hx2⟩))
    · by_cases h4 : (x ^ 2) ^ 2 = 1
      · exact Or.inr (huniq (x ^ 2) (Finset.mem_filter.mpr ⟨(hmemA _).mpr hx2, h4⟩))
      · exfalso
        have hdvd8 : orderOf x ∣ 8 := by
          have h := orderOf_dvd_natCard x
          rwa [Nat.card_eq_fintype_card, hH] at h
        have hnd4 : ¬ orderOf x ∣ 4 := by
          intro h
          apply h4
          rw [← pow_mul]
          exact orderOf_dvd_iff_pow_eq_one.mp h
        have hord : orderOf x = 8 := by
          generalize orderOf x = n at hdvd8 hnd4 ⊢
          have hle : n ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd8
          interval_cases n <;> omega
        have hzp : Subgroup.zpowers x = ⊤ := by
          apply Subgroup.eq_top_of_card_eq
          rw [Nat.card_zpowers, hord, Nat.card_eq_fintype_card, hH]
        have hcommx : ∀ a b : H, a * b = b * a := by
          intro a b
          have ha : a ∈ Subgroup.zpowers x := by
            rw [hzp]
            exact Subgroup.mem_top a
          have hb : b ∈ Subgroup.zpowers x := by
            rw [hzp]
            exact Subgroup.mem_top b
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          exact ((Commute.refl x).zpow_zpow m n).eq
        exact not_comm_of_gen φ hφ hgen hcommx hz1 hz2 hzf

open scoped commutatorElement in
theorem quatLike_of_commutator {G : Type*} [Group G] {Q : Subgroup G} {u : G}
    (hQ : Nat.card Q = 8) (hu3 : u ^ 3 = 1) (hn : ∀ q ∈ Q, u * q * u⁻¹ ∈ Q)
    (hc : ⁅Q, Subgroup.zpowers u⁆ = Q) :
    ∃ z ∈ Q, z ≠ 1 ∧ ∀ x ∈ Q, x ≠ 1 → x = z ∨ x ^ 2 = z := by
  classical
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  letI : Fintype Q := Fintype.ofFinite Q
  have hH : Fintype.card Q = 8 := by
    rw [← Nat.card_eq_fintype_card]
    exact hQ
  let φ : Q →* Q :=
    { toFun := fun q => ⟨u * (q : G) * u⁻¹, hn _ q.2⟩
      map_one' := by
        ext
        simp
      map_mul' := fun a b => by
        ext
        simp [mul_assoc] }
  have hφ : ∀ x : Q, φ (φ (φ x)) = x := by
    intro x
    apply Subtype.ext
    show u * (u * (u * (x : G) * u⁻¹) * u⁻¹) * u⁻¹ = (x : G)
    have huuu : u * (u * u) = 1 := by
      rw [← pow_three]
      exact hu3
    have h : u * (u * (u * (x : G) * u⁻¹) * u⁻¹) * u⁻¹ =
        (u * (u * u)) * (x : G) * (u * (u * u))⁻¹ := by
      group
    rw [h, huuu, inv_one, mul_one, one_mul]
  have hgen : ∀ K : Subgroup Q, (∀ x, x * φ x⁻¹ ∈ K) → K = ⊤ := by
    intro K hK
    let K' : Subgroup G := K.map Q.subtype
    have key1 : ∀ g ∈ Q, ⁅g, u⁆ ∈ K' := by
      intro g hg
      refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * φ ⟨g, hg⟩⁻¹, hK _, ?_⟩
      simp [φ, commutatorElement_def, mul_assoc]
    have key2 : ∀ g ∈ Q, ⁅g, u * u⁆ ∈ K' := by
      intro g hg
      have h : ⁅g, u * u⁆ = ⁅g, u⁆ * ⁅u * g * u⁻¹, u⁆ := by
        simp only [commutatorElement_def]
        group
      rw [h]
      exact K'.mul_mem (key1 g hg) (key1 _ (hn g hg))
    have hzpow : ∀ k : ℤ, u ^ k = u ^ (k % 3) := by
      intro k
      conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
      have h3 : u ^ (3 : ℤ) = 1 := by
        rw [zpow_ofNat]
        exact hu3
      rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
    have hyK : ∀ g ∈ Q, ∀ y ∈ Subgroup.zpowers u, ⁅g, y⁆ ∈ K' := by
      intro g hg y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [hzpow k]
      rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
      · rw [h, zpow_zero, commutatorElement_one_right]
        exact K'.one_mem
      · rw [h, zpow_one]
        exact key1 g hg
      · rw [h, zpow_two]
        exact key2 g hg
    have hle' : ⁅Q, Subgroup.zpowers u⁆ ≤ K' :=
      Subgroup.commutator_le.mpr fun g hg y hy => hyK g hg y hy
    rw [hc] at hle'
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨y, hyK', hy⟩ := Subgroup.mem_map.mp (hle' x.2)
    have hyx : y = x := Subtype.ext hy
    rw [← hyx]
    exact hyK'
  obtain ⟨z, hz1, hz⟩ := exists_unique_involution_of_card_eight hH φ hφ hgen
  refine ⟨(z : G), z.2, fun h => hz1 (Subtype.ext h), fun x hx hx1 => ?_⟩
  rcases hz ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h)) with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (by simpa using congrArg Subtype.val h)

end CFSG.RankThree.PartTwo.Sec8.HeringBMem
