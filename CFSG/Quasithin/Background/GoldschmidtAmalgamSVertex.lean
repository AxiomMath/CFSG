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

public section

namespace CFSG.Quasithin.F6.GoldAmS

open Equiv

theorem card_modEq_fixed {G : Type*} [Group G] (Q : Subgroup G) [Q.Normal] [Finite Q] (x : G)
    (hx : x ^ 3 = 1) :
    Nat.card Q ≡ Nat.card {q : Q // x * (q : G) * x⁻¹ = q} [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fintype Q := Fintype.ofFinite Q
  let σ : Perm Q := MulAut.toPerm Q (MulAut.conjNormal x)
  have hσ : σ ^ 3 ^ 1 = 1 := by
    rw [pow_one, ← map_pow, ← map_pow, hx, map_one, map_one]
  have key := Equiv.Perm.card_compl_support_modEq hσ
  have h2 : Nat.card {q : Q // x * (q : G) * x⁻¹ = q} = ((Equiv.Perm.support σ)ᶜ).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun q => by
      simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      change x * (q : G) * x⁻¹ = q ↔ MulAut.conjNormal x q = q
      rw [Subtype.ext_iff, MulAut.conjNormal_apply])
  rw [h2, Nat.card_eq_fintype_card]
  exact key.symm


theorem fixed_eq_one_of_card_four {G : Type*} [Group G] (Q : Subgroup G) [Q.Normal] [Finite Q]
    (hQ : Nat.card Q = 4) (x : G) (hx : x ^ 3 = 1) (hnc : ∃ q ∈ Q, x * q * x⁻¹ ≠ q) :
    ∀ q ∈ Q, x * q * x⁻¹ = q → q = 1 := by
  let C : Subgroup Q := MonoidHom.eqLocus (MulAut.conjNormal x : MulAut Q).toMonoidHom
    (MonoidHom.id Q)
  have hC : Nat.card C = Nat.card {q : Q // x * (q : G) * x⁻¹ = q} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun q => by
      change MulAut.conjNormal x q = q ↔ _
      rw [Subtype.ext_iff, MulAut.conjNormal_apply])
  have h1 := card_modEq_fixed Q x hx
  rw [← hC, hQ] at h1
  have h2 : Nat.card C ∣ 4 := by
    have := Subgroup.card_subgroup_dvd_card C
    rwa [hQ] at this
  have h3 : Nat.card C = 1 := by
    have h4 : Nat.card C ≤ 4 := Nat.le_of_dvd (by norm_num) h2
    have h5 : 0 < Nat.card C := Nat.card_pos
    unfold Nat.ModEq at h1
    interval_cases hc : Nat.card C <;> first | rfl | omega | skip
    · exfalso
      have hCtop : C = ⊤ := by
        rw [← Subgroup.card_eq_iff_eq_top]
        omega
      obtain ⟨q, hq, hne⟩ := hnc
      have hmem : (⟨q, hq⟩ : Q) ∈ C := by rw [hCtop]; exact Subgroup.mem_top _
      have h6 : MulAut.conjNormal x ⟨q, hq⟩ = ⟨q, hq⟩ := hmem
      have h7 := congrArg Subtype.val h6
      rw [MulAut.conjNormal_apply] at h7
      exact hne h7
  intro q hq hfix
  have hbot : C = ⊥ := (Subgroup.card_eq_one).1 h3
  have hmem : (⟨q, hq⟩ : Q) ∈ C := by
    change MulAut.conjNormal x ⟨q, hq⟩ = ⟨q, hq⟩
    rw [Subtype.ext_iff, MulAut.conjNormal_apply]
    exact hfix
  rw [hbot] at hmem
  exact congrArg Subtype.val ((Subgroup.mem_bot).1 hmem)


@[expose] def V4Fin : Finset (Perm (Fin 4)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

@[expose] def V4 : Subgroup (Perm (Fin 4)) where
  carrier := ↑V4Fin
  one_mem' := by decide
  mul_mem' := by
    intro a b ha hb
    simp only [Finset.mem_coe] at ha hb ⊢
    revert a b
    decide
  inv_mem' := by
    intro a ha
    simp only [Finset.mem_coe] at ha ⊢
    revert a
    decide

theorem card_V4 : Nat.card V4 = 4 := by
  show Nat.card (↥(V4Fin : Set (Perm (Fin 4)))) = 4
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

theorem mem_V4_of_sq_eq_one (σ : Perm (Fin 4)) (h2 : σ * σ = 1) (hfix : ∀ i, σ i ≠ i) :
    σ ∈ V4 := by
  show σ ∈ (V4Fin : Set (Perm (Fin 4)))
  simp only [Finset.mem_coe]
  revert σ
  decide


section Vertex

variable {G : Type*} [Group G] [Finite G] (Q : Subgroup G) [Q.Normal]

omit [Finite G] [Q.Normal] in
theorem exists_not_comm {hQe : ∀ q ∈ Q, q * q = 1}
    (hC : ∀ g : G, (∀ q ∈ Q, g * q = q * g) → g ∈ Q) (y : G) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∃ q ∈ Q, y * q * y⁻¹ ≠ q := by
  by_contra hcon
  push Not at hcon
  have hyQ : y ∈ Q := hC y fun q hq => by
    have := hcon q hq
    calc y * q = y * q * y⁻¹ * y := by group
      _ = q * y := by rw [this]
  have h2 := hQe y hyQ
  apply hy1
  calc y = y ^ 3 * (y * y)⁻¹ := by group
    _ = 1 := by rw [hy3, h2]; simp

theorem eq_one_of_normalizes (hQ : Nat.card Q = 4) (hQe : ∀ q ∈ Q, q * q = 1)
    (hC : ∀ g : G, (∀ q ∈ Q, g * q = q * g) → g ∈ Q) (y : G) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (q : G) (hq : q ∈ Q) (hqn : q * y * q⁻¹ ∈ Subgroup.zpowers y) : q = 1 := by
  have hfix := fixed_eq_one_of_card_four Q hQ y hy3 (exists_not_comm Q (hQe := hQe) hC y hy3 hy1)
  have hc1 : q * y * q⁻¹ * y⁻¹ ∈ Subgroup.zpowers y :=
    Subgroup.mul_mem _ hqn (Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
  have hc2 : q * y * q⁻¹ * y⁻¹ ∈ Q := by
    have h1 : y * q⁻¹ * y⁻¹ ∈ Q := (inferInstance : Q.Normal).conj_mem _ (Q.inv_mem hq) y
    have h2 : q * (y * q⁻¹ * y⁻¹) ∈ Q := Q.mul_mem hq h1
    have : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
    rwa [this]
  have hc3 : q * y * q⁻¹ * y⁻¹ = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc1
    have h3 : (q * y * q⁻¹ * y⁻¹) ^ 3 = 1 := by
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [hy3]
    have h2 := hQe _ hc2
    have key : ∀ c : G, c ^ 3 = 1 → c * c = 1 → c = 1 := fun c h3 h2 => by
      calc c = c ^ 3 * (c * c)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; simp
    exact key _ h3 h2
  have hcomm : y * q * y⁻¹ = q := by
    have : q * y = y * q := by
      have h := congrArg (· * y) hc3
      simp only [one_mul] at h
      calc q * y = q * y * q⁻¹ * y⁻¹ * y * q := by group
        _ = y * q := by rw [hc3]; group
    calc y * q * y⁻¹ = q * y * y⁻¹ := by rw [this]
      _ = q := by group
  exact hfix q hq hcomm

theorem factorization_24 : (24 : ℕ).factorization 3 = 1 := by
  have h := Nat.factorization_mul (show (3 : ℕ) ≠ 0 by norm_num) (show (8 : ℕ) ≠ 0 by norm_num)
  rw [show (24 : ℕ) = 3 * 8 by norm_num, h, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem vertex_four (hQ : Nat.card Q = 4) (hQe : ∀ q ∈ Q, q * q = 1)
    (hC : ∀ g : G, (∀ q ∈ Q, g * q = q * g) → g ∈ Q) (hG : Nat.card G = 24) :
    ∃ ψ : G ≃* Perm (Fin 4), ∀ q ∈ Q, ψ q ∈ V4 := by
  classical
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard3 : ∀ P : Sylow 3 G, Nat.card P = 3 := by
    intro P
    rw [Sylow.card_eq_multiplicity, hG, factorization_24, pow_one]
  obtain ⟨P₀⟩ : Nonempty (Sylow 3 G) := inferInstance
  have hgen : ∀ P : Sylow 3 G, ∃ y : G, y ^ 3 = 1 ∧ y ≠ 1 ∧
      (P : Subgroup G) = Subgroup.zpowers y := by
    intro P
    have hP3 : Nat.card (P : Subgroup G) = 3 := hcard3 P
    have : Nontrivial (P : Subgroup G) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hP3]; norm_num
    obtain ⟨y, hy1⟩ := exists_ne (1 : (P : Subgroup G))
    have hy3 : y ^ 3 = 1 := by
      have h := pow_card_eq_one' (x := y)
      rwa [hP3] at h
    have hy3' : (y : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
    have hy1' : (y : G) ≠ 1 := fun h => hy1 (Subtype.ext (by simpa using h))
    have hyord : orderOf (y : G) = 3 := orderOf_eq_prime hy3' hy1'
    refine ⟨y, hy3', hy1', ?_⟩
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact y.2
    · rw [Nat.card_zpowers, hyord, hP3]
  have hnormQ : ∀ P : Sylow 3 G, ∀ q ∈ Q, q ∈ Subgroup.normalizer (P : Set G) → q = 1 := by
    intro P q hq hqn
    obtain ⟨y, hy3, hy1, hPy⟩ := hgen P
    have hy : y ∈ (P : Subgroup G) := hPy ▸ Subgroup.mem_zpowers y
    have h1 := (Subgroup.mem_normalizer_iff.1 hqn y).1 hy
    exact eq_one_of_normalizes Q hQ hQe hC y hy3 hy1 q hq (hPy ▸ h1)
  have hn : Nat.card (Sylow 3 G) = 4 := by
    have hn1 : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
    have hidx : (P₀ : Subgroup G).index = 8 := by
      have h := (P₀ : Subgroup G).card_mul_index
      rw [hcard3 P₀, hG] at h
      omega
    have hndvd : Nat.card (Sylow 3 G) ∣ 8 := by
      have := Sylow.card_dvd_index P₀
      rwa [hidx] at this
    have hle : Nat.card (Sylow 3 G) ≤ 8 := Nat.le_of_dvd (by norm_num) hndvd
    have hpos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
    unfold Nat.ModEq at hn1
    have h14 : Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 := by
      interval_cases hc : Nat.card (Sylow 3 G) <;> omega
    rcases h14 with h1 | h4
    · exfalso
      have hsub : Subsingleton (Sylow 3 G) := by
        rw [← Finite.card_le_one_iff_subsingleton]; omega
      have hnorm : (P₀ : Subgroup G).Normal := Sylow.normal_of_subsingleton P₀
      have hQ1 : ∀ q ∈ Q, q = 1 := fun q hq =>
        hnormQ P₀ q hq (Sylow.smul_eq_iff_mem_normalizer.1 (Subsingleton.elim _ _))
      have : Nat.card Q = 1 := by
        rw [Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]; exact hQ1
      omega
    · exact h4
  let α : G →* Perm (Sylow 3 G) := MulAction.toPermHom G (Sylow 3 G)
  have hαP : ∀ g P, α g P = g • P := fun _ _ => rfl
  have hKQ : ∀ q ∈ Q, α q = 1 → q = 1 := by
    intro q hq hq1
    apply hnormQ P₀ q hq
    rw [← Sylow.smul_eq_iff_mem_normalizer, ← hαP, hq1]
    rfl
  have hinj : Function.Injective α := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hcomm : ∀ q ∈ Q, k * q = q * k := by
      intro q hq
      have h1 : k * q * k⁻¹ * q⁻¹ ∈ Q :=
        Q.mul_mem ((inferInstance : Q.Normal).conj_mem q hq k) (Q.inv_mem hq)
      have h2 : α (k * q * k⁻¹ * q⁻¹) = 1 := by simp [map_mul, map_inv, hk]
      have h3 := hKQ _ h1 h2
      calc k * q = k * q * k⁻¹ * q⁻¹ * q * k := by group
        _ = q * k := by rw [h3]; group
    exact hKQ k (hC k hcomm) hk
  have hbij : Function.Bijective α := by
    apply Function.Injective.bijective_of_nat_card_le hinj
    rw [Nat.card_perm, hn, hG]
    decide
  let e2 : Sylow 3 G ≃ Fin 4 := Finite.equivFinOfCardEq hn
  refine ⟨(MulEquiv.ofBijective α hbij).trans (Equiv.permCongrHom e2), fun q hq => ?_⟩
  by_cases hq1 : q = 1
  · subst hq1
    simp only [map_one]
    exact V4.one_mem
  · apply mem_V4_of_sq_eq_one
    · rw [← map_mul, hQe q hq, map_one]
    · intro i hi
      apply hq1
      apply hnormQ (e2.symm i) q hq
      rw [← Sylow.smul_eq_iff_mem_normalizer]
      have h1 : e2 (α q (e2.symm i)) = i := hi
      have := congrArg e2.symm h1
      simpa [hαP] using this

end Vertex


section Exponent

variable {G : Type*} [Group G] [Finite G] (Q : Subgroup G) [Q.Normal]

omit [Finite G] [Q.Normal] in
theorem exists_not_comm' (hQ : Nat.card Q = 4)
    (hC : ∀ g : G, (∀ q ∈ Q, g * q = q * g) → g ∈ Q) (y : G) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∃ q ∈ Q, y * q * y⁻¹ ≠ q := by
  by_contra hcon
  push Not at hcon
  have hyQ : y ∈ Q := hC y fun q hq => by
    have := hcon q hq
    calc y * q = y * q * y⁻¹ * y := by group
      _ = q * y := by rw [this]
  have h4 : y ^ 4 = 1 := by
    have h := pow_card_eq_one' (G := Q) (x := ⟨y, hyQ⟩)
    rw [hQ] at h
    simpa using congrArg Subtype.val h
  apply hy1
  calc y = y ^ 4 * (y ^ 3)⁻¹ := by group
    _ = 1 := by rw [h4, hy3]; simp

theorem exp_two_of_card_four (hQ : Nat.card Q = 4) (hG3 : 3 ∣ Nat.card G)
    (hC : ∀ g : G, (∀ q ∈ Q, g * q = q * g) → g ∈ Q) : ∀ q ∈ Q, q * q = 1 := by
  classical
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := G) 3
    (by rw [← Nat.card_eq_fintype_card]; exact hG3)
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; omega
  have hfix := fixed_eq_one_of_card_four Q hQ x hx3 (exists_not_comm' Q hQ hC x hx3 hx1)
  by_contra hcon
  push Not at hcon
  obtain ⟨q, hq, hq2⟩ := hcon
  have hq4 : q ^ 4 = 1 := by
    have h := pow_card_eq_one' (G := Q) (x := ⟨q, hq⟩)
    rw [hQ] at h
    simpa using congrArg Subtype.val h
  have hord : orderOf q = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := q)
      (by simpa [pow_two] using hq2) (by simpa using hq4)
    simpa using this
  have hzQ : Subgroup.zpowers q = Q := by
    have hle : Subgroup.zpowers q ≤ Q := by rw [Subgroup.zpowers_le]; exact hq
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord, hQ])
  have hinv : ∀ v ∈ Q, v * v = 1 → v = 1 ∨ v = q * q := by
    intro v hv hv2
    rw [← hzQ, mem_zpowers_iff_mem_range_orderOf] at hv
    simp only [Finset.mem_image, Finset.mem_range, hord] at hv
    obtain ⟨n, hn, rfl⟩ := hv
    interval_cases n
    · left; simp
    · exfalso; exact hq2 (by simpa [pow_two] using hv2)
    · right; simp [pow_two]
    · exfalso
      apply hq2
      have : q ^ 3 * q ^ 3 = q ^ 2 := by
        calc q ^ 3 * q ^ 3 = q ^ 4 * q ^ 2 := by group
          _ = q ^ 2 := by rw [hq4]; simp
      rw [this] at hv2
      simpa [pow_two] using hv2
  set u := q * q with hu
  have huQ : u ∈ Q := Q.mul_mem hq hq
  have hu1 : u ≠ 1 := hq2
  have huu : u * u = 1 := by
    have : q * q * (q * q) = q ^ 4 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [hu, this, hq4]
  have hcQ : x * u * x⁻¹ ∈ Q := (inferInstance : Q.Normal).conj_mem u huQ x
  have hcc : (x * u * x⁻¹) * (x * u * x⁻¹) = 1 := by
    calc (x * u * x⁻¹) * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
      _ = 1 := by rw [huu]; group
  have hcu : x * u * x⁻¹ = u := by
    rcases hinv _ hcQ hcc with h1 | h1
    · exfalso
      apply hu1
      calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  exact hu1 (hfix u huQ hcu)

end Exponent

theorem eq_of_card_le_two {G : Type*} [Group G] [Finite G] (hG : Nat.card G ≤ 2) {a b : G}
    (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  classical
  by_contra hab
  have : Fintype G := Fintype.ofFinite G
  have h3 : ({1, a, b} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => ha h.symm, fun h => hb h.symm⟩
  have h4 : ({1, a, b} : Finset G).card ≤ Nat.card G := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  omega

end CFSG.Quasithin.F6.GoldAmS
