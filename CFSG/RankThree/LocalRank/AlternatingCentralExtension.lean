module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
import CFSG.LocalAnalysis.LyonsUnitaryFour.CentralHall
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
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

namespace CFSG.RankThree.LocalRank

open Equiv CFSG.ComponentClassification.PresentationLocal

section CubeLifts

variable {E A : Type*} [Group E] [Group A] (π : E →* A)

theorem exists_unique_cube_lift (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (h3 : Nat.Coprime (Nat.card π.ker) 3) {a : A} (ha : a ^ 3 = 1) :
    ∃! x : E, π x = a ∧ x ^ 3 = 1 := by
  obtain ⟨y, rfl⟩ := hπ a
  have hy : y ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, ha]
  have hbij := Nat.Coprime.pow_left_bijective h3
  obtain ⟨d, hd⟩ := hbij.2 (⟨(y ^ 3)⁻¹, inv_mem hy⟩ : π.ker)
  have hd' : (d : E) ^ 3 = (y ^ 3)⁻¹ := congrArg Subtype.val hd
  have hcomm : Commute y (d : E) := Subgroup.mem_center_iff.mp (hC d.2) y
  have hdker : π (d : E) = 1 := d.2
  refine ⟨y * d, ⟨by rw [map_mul, hdker, mul_one], ?_⟩, ?_⟩
  · rw [hcomm.mul_pow, hd', mul_inv_cancel]
  · rintro x ⟨hx, hx3⟩
    set u := (y * d)⁻¹ * x with hu
    have huker : u ∈ π.ker := by
      rw [MonoidHom.mem_ker, hu, map_mul, map_inv, map_mul, hdker, mul_one, hx, inv_mul_cancel]
    have hxu : x = y * d * u := by rw [hu, mul_inv_cancel_left]
    have hcomm' : Commute (y * d) u := Subgroup.mem_center_iff.mp (hC huker) (y * d)
    have hyd3 : (y * d) ^ 3 = 1 := by rw [hcomm.mul_pow, hd', mul_inv_cancel]
    have hu3 : u ^ 3 = 1 := by
      have h := hx3
      rw [hxu, hcomm'.mul_pow, hyd3, one_mul] at h
      exact h
    have hu1 : (⟨u, huker⟩ : π.ker) = 1 :=
      hbij.1 (Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one, hu3, one_pow]))
    have hu1' : u = 1 := congrArg Subtype.val hu1
    rw [hxu, hu1', mul_one]

end CubeLifts

section Alternating

variable {n : ℕ} {E : Type*} [Group E] [Finite E] (π : E →* alternatingGroup (Fin n))

theorem carmichaelCycle_ne_one (k : CarmichaelIndex n) : carmichaelCycle k ≠ 1 := by
  intro h
  exact (carmichaelPerm_isThreeCycle k).ne_one (congrArg Subtype.val h)

theorem orderOf_carmichaelCycle (k : CarmichaelIndex n) : orderOf (carmichaelCycle k) = 3 :=
  orderOf_eq_prime (carmichaelCycle_pow_three k) (carmichaelCycle_ne_one k)

theorem card_closure_pair_carmichaelCycle_dvd {i j : CarmichaelIndex n} (hij : i ≠ j) :
    Nat.card (Subgroup.closure (Set.range ![carmichaelCycle i, carmichaelCycle j])) ∣ 36 := by
  set Q := Subgroup.closure (Set.range ![carmichaelCycle i, carmichaelCycle j]) with hQ
  have hle : Nat.card Q ≤ 12 := by
    have h := (finite_closure_and_card_le_of_carmichael 2 ![carmichaelCycle i, carmichaelCycle j]
      (by
        intro k
        fin_cases k
        · exact carmichaelCycle_pow_three i
        · exact carmichaelCycle_pow_three j)
      (by
        intro k l hkl
        fin_cases k <;> fin_cases l
        · exact absurd rfl hkl
        · exact carmichaelCycle_mul_sq i j hij
        · exact carmichaelCycle_mul_sq j i (Ne.symm hij)
        · exact absurd rfl hkl)).2
    exact h.trans (by decide)
  have hmem : carmichaelCycle i ∈ Q := Subgroup.subset_closure ⟨0, rfl⟩
  have h3 : 3 ∣ Nat.card Q := by
    have h := orderOf_dvd_natCard (⟨carmichaelCycle i, hmem⟩ : Q)
    rwa [Subgroup.orderOf_mk, orderOf_carmichaelCycle] at h
  obtain ⟨m, hm⟩ := h3
  have hpos : 0 < Nat.card Q := Nat.card_pos
  rw [hm] at hle hpos ⊢
  have hm4 : m ≤ 4 := by omega
  interval_cases m <;> omega

omit [Finite E] in
theorem coprime_of_dvd_thirtySix (h6 : Nat.Coprime (Nat.card π.ker) 6) {m : ℕ} (hm : m ∣ 36) :
    Nat.Coprime (Nat.card π.ker) m :=
  Nat.Coprime.coprime_dvd_right hm (by simpa using Nat.Coprime.pow_right 2 h6)

theorem lift_mul_sq_eq_one (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (h6 : Nat.Coprime (Nat.card π.ker) 6) {i j : CarmichaelIndex n} (hij : i ≠ j) {x y : E}
    (hx : π x = carmichaelCycle i) (hx3 : x ^ 3 = 1) (hy : π y = carmichaelCycle j)
    (hy3 : y ^ 3 = 1) : (x * y) ^ 2 = 1 := by
  set Q := Subgroup.closure (Set.range ![carmichaelCycle i, carmichaelCycle j]) with hQ
  have hQ36 := card_closure_pair_carmichaelCycle_dvd hij
  set F := Q.comap π with hF
  have hkerF : π.ker ≤ F := fun k hk => by
    rw [hF, Subgroup.mem_comap, (MonoidHom.mem_ker).mp hk]
    exact Q.one_mem
  set A := π.ker.subgroupOf F with hA
  set ψ : F →* alternatingGroup (Fin n) := π.comp F.subtype with hψ
  have hψker : ψ.ker = A := by
    ext g
    simp only [hψ, hA, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Subgroup.mem_subgroupOf]
  have hψrange : ψ.range = Q := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype, hF,
      Subgroup.map_comap_eq_self_of_surjective hπ]
  have hindex : A.index = Nat.card Q := by
    rw [← hψker, Subgroup.index_ker, hψrange]
  have hcardA : Nat.card A = Nat.card π.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerF).toEquiv
  have hcop : Nat.Coprime (Nat.card A) A.index := by
    rw [hcardA, hindex]
    exact coprime_of_dvd_thirtySix π h6 hQ36
  have hcentral : A ≤ Subgroup.center F := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hC (Subgroup.mem_subgroupOf.mp hg)) h)
  obtain ⟨K, -, -, -, hKmem, -, -⟩ :=
    CFSG.LyonsUnitaryFour.central_hall_direct_complement A hcentral hcop
  have hxF : x ∈ F := by
    rw [hF, Subgroup.mem_comap, hx]
    exact Subgroup.subset_closure ⟨0, rfl⟩
  have hyF : y ∈ F := by
    rw [hF, Subgroup.mem_comap, hy]
    exact Subgroup.subset_closure ⟨1, rfl⟩
  have h3 : 3 ∣ A.index := by
    rw [hindex]
    have hmem : carmichaelCycle i ∈ Q := Subgroup.subset_closure ⟨0, rfl⟩
    have h := orderOf_dvd_natCard (⟨carmichaelCycle i, hmem⟩ : Q)
    rwa [Subgroup.orderOf_mk, orderOf_carmichaelCycle] at h
  obtain ⟨m, hm⟩ := h3
  have hpowx : (⟨x, hxF⟩ : F) ^ A.index = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, hm, pow_mul, hx3, one_pow, Subgroup.coe_one])
  have hpowy : (⟨y, hyF⟩ : F) ^ A.index = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, hm, pow_mul, hy3, one_pow, Subgroup.coe_one])
  have hxyK := K.mul_mem ((hKmem _).mpr hpowx) ((hKmem _).mpr hpowy)
  have hpow : (x * y) ^ A.index = 1 := congrArg Subtype.val ((hKmem _).mp hxyK)
  have hz : (x * y) ^ 2 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, map_mul, hx, hy, carmichaelCycle_mul_sq i j hij]
  have hzidx : ((x * y) ^ 2) ^ A.index = 1 := by rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow]
  have h1 : orderOf ((x * y) ^ 2) ∣ A.index := orderOf_dvd_of_pow_eq_one hzidx
  have h2 : orderOf ((x * y) ^ 2) ∣ Nat.card π.ker := by
    rw [← Subgroup.orderOf_mk _ hz]
    exact orderOf_dvd_natCard _
  have hcop' : Nat.Coprime (Nat.card π.ker) A.index := by
    rw [hindex]
    exact coprime_of_dvd_thirtySix π h6 hQ36
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop' h2 h1)

theorem alternating_central_prime_to_six_extension_splitting (hn : 3 ≤ n)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (h6 : Nat.Coprime (Nat.card π.ker) 6) :
    (∃ s : alternatingGroup (Fin n) →* E, π.comp s = MonoidHom.id _ ∧
      (∀ s' : alternatingGroup (Fin n) →* E, π.comp s' = MonoidHom.id _ → s' = s) ∧
      (∀ k : CarmichaelIndex n, orderOf (s (carmichaelCycle k)) = 3 ∧
        ∀ y : E, π y = carmichaelCycle k → orderOf y = 3 → y = s (carmichaelCycle k)) ∧
      π.ker ⊔ s.range = ⊤ ∧ π.ker ⊓ s.range = ⊥ ∧
      ∃ e : π.ker × alternatingGroup (Fin n) ≃* E, ∀ c a, e (c, a) = (c : E) * s a) ∧
    (Group.IsPerfect E → π.ker = ⊥) := by
  have h3 : Nat.Coprime (Nat.card π.ker) 3 :=
    Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) h6
  have hlift := fun k : CarmichaelIndex n =>
    exists_unique_cube_lift π hπ hC h3 (carmichaelCycle_pow_three k)
  choose x hx using fun k => (hlift k).exists
  have hxx : ∀ i j, i ≠ j → (x i * x j) ^ 2 = 1 := fun i j hij =>
    lift_mul_sq_eq_one π hπ hC h6 hij (hx i).1 (hx i).2 (hx j).1 (hx j).2
  obtain ⟨s, hs⟩ := exists_hom_carmichaelCycle hn x (fun k => (hx k).2) hxx
  have hsection : π.comp s = MonoidHom.id _ := hom_ext_carmichaelCycle hn fun k => by
    rw [MonoidHom.comp_apply, hs, (hx k).1, MonoidHom.id_apply]
  have hπs : ∀ a, π (s a) = a := fun a => DFunLike.congr_fun hsection a
  have hord : ∀ k : CarmichaelIndex n, orderOf (s (carmichaelCycle k)) = 3 ∧
      ∀ y : E, π y = carmichaelCycle k → orderOf y = 3 → y = s (carmichaelCycle k) := by
    intro k
    refine ⟨?_, fun y hy hy3 => ?_⟩
    · apply orderOf_eq_prime
      · rw [← map_pow, carmichaelCycle_pow_three, map_one]
      · intro h1
        apply carmichaelCycle_ne_one k
        rw [← hπs (carmichaelCycle k), h1, map_one]
    · rw [hs]
      exact (hlift k).unique ⟨hy, hy3 ▸ pow_orderOf_eq_one y⟩ (hx k)
  have huniq : ∀ s' : alternatingGroup (Fin n) →* E, π.comp s' = MonoidHom.id _ → s' = s := by
    intro s' hs'
    apply hom_ext_carmichaelCycle hn
    intro k
    have h1 : π (s' (carmichaelCycle k)) = carmichaelCycle k := DFunLike.congr_fun hs' _
    rw [hs]
    exact (hlift k).unique ⟨h1, by rw [← map_pow, carmichaelCycle_pow_three, map_one]⟩ (hx k)
  have hdecomp : ∀ g : E, g * (s (π g))⁻¹ ∈ π.ker := fun g => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπs, mul_inv_cancel]
  have hsup : π.ker ⊔ s.range = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hmem : s (π g) ∈ s.range := MonoidHom.mem_range.mpr ⟨π g, rfl⟩
    have h := Subgroup.mul_mem_sup (hdecomp g) hmem
    rwa [inv_mul_cancel_right] at h
  have hinf : π.ker ⊓ s.range = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgker, ⟨a, rfl⟩⟩
    rw [Subgroup.mem_bot]
    have ha : a = 1 := by
      rw [← hπs a]
      exact hgker
    rw [ha, map_one]
  let f : π.ker × alternatingGroup (Fin n) →* E :=
    { toFun := fun ca => (ca.1 : E) * s ca.2
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul, mul_assoc]
        congr 1
        rw [← mul_assoc, ← mul_assoc]
        congr 1
        exact (Subgroup.mem_center_iff.mp (hC b.1.2) (s a.2)).symm }
  have hf : ∀ c a, f (c, a) = (c : E) * s a := fun _ _ => rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨c, a⟩ h1
    rw [hf] at h1
    have ha : a = 1 := by
      have h := congrArg π h1
      rwa [map_mul, (MonoidHom.mem_ker).mp c.2, one_mul, hπs, map_one] at h
    rw [ha, map_one, mul_one] at h1
    rw [ha]
    exact Prod.ext (Subtype.ext h1) rfl
  have hfsurj : Function.Surjective f := fun g =>
    ⟨(⟨g * (s (π g))⁻¹, hdecomp g⟩, π g), by rw [hf, inv_mul_cancel_right]⟩
  refine ⟨⟨s, hsection, huniq, hord, hsup, hinf, MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩,
    fun c a => rfl⟩, fun hperf => ?_⟩
  set e := MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩ with he
  let φ : E →* π.ker := (MonoidHom.fst _ _).comp e.symm.toMonoidHom
  have hφ : Function.Surjective φ := fun c =>
    ⟨e (c, 1), by simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, MonoidHom.coe_fst]⟩
  have : Group.IsPerfect E := hperf
  have : Group.IsPerfect π.ker := Group.IsPerfect.ofSurjective hφ
  have : IsMulCommutative π.ker :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hC b.2) a)⟩⟩
  have : Subsingleton π.ker := Group.IsPerfect.subsingleton_of_isMulCommutative
  rw [eq_bot_iff]
  intro c hc
  exact congrArg Subtype.val (Subsingleton.elim (⟨c, hc⟩ : π.ker) 1)

theorem perfect_central_prime_extension_alternating_ker_eq_bot (hn : 5 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) [Group.IsPerfect E] (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) : π.ker = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpk
  have h6 : Nat.Coprime (Nat.card π.ker) 6 := by
    rw [hk]
    apply Nat.Coprime.pow_left
    rw [hp.coprime_iff_not_dvd]
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 * 3 from h) with h2 | h3
    · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) h3) (by omega)
  exact (alternating_central_prime_to_six_extension_splitting π (by omega) hπ hC h6).2
    inferInstance

end Alternating

end CFSG.RankThree.LocalRank
