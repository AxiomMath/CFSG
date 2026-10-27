module

public import CFSG.RankThree.GF2n.Parrott.HPrimeJ1
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Certificates.Certificate946017
import CFSG.RankThree.GF2n.Parrott.DerivedInterJEqBranch
import CFSG.RankThree.GF2n.Parrott.MemJOfIndexTwo
import CFSG.RankThree.GF2n.Parrott.WAction
import CFSG.RankThree.GF2n.Parrott.QA45SylowFacts
import CFSG.RankThree.GF2n.Parrott.OrderNineLift
import Mathlib.GroupTheory.Transfer
public import CFSG.Blueprint.SourceGeckCorrespondence
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.FixedFreeThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.RankThree.GF2n.Parrott.FixDimConj
public import CFSG.RankThree.GF2n.Parrott.Section2J0NormalFinal

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

private theorem card_modEq_one_of_pow_five {Y : Type*} [Group Y] [Finite Y] {b : Y}
    (hb : b ^ 5 = 1) {U : Subgroup Y} (hU : ∀ u ∈ U, b * u * b⁻¹ ∈ U)
    (hfix : ∀ u ∈ U, b * u = u * b → u = 1) : Nat.card U ≡ 1 [MOD 5] := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fintype ↥U := Fintype.ofFinite _
  let f : Function.End ↥U := fun u => ⟨b * u * b⁻¹, hU u u.2⟩
  have hpow : ∀ (n : ℕ) (u : ↥U), (((f ^ n) u : ↥U) : Y) = b ^ n * u * (b ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
        intro u
        simp only [pow_zero, one_mul, inv_one, mul_one]
        rfl
    | succ n ih =>
        intro u
        rw [pow_succ]
        change ((f ^ n) (f u) : Y) = _
        rw [ih]
        change b ^ n * (b * u * b⁻¹) * (b ^ n)⁻¹ = _
        rw [pow_succ]
        group
  have hf : f ^ 5 ^ 1 = 1 := by
    funext u
    apply Subtype.ext
    rw [pow_one, hpow, hb]
    simp only [one_mul, inv_one, mul_one]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) hf
  have hfp : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, Subtype.ext (by simp [f])⟩, ?_⟩
    rintro ⟨u, hu⟩
    apply Subtype.ext
    apply Subtype.ext
    have hu' : b * (u : Y) * b⁻¹ = (u : Y) := congrArg Subtype.val hu
    have hcomm : b * (u : Y) = (u : Y) * b := by
      calc b * (u : Y) = b * (u : Y) * b⁻¹ * b := by group
        _ = (u : Y) * b := by rw [hu']
    exact hfix u u.2 hcomm
  rw [hfp, ← Nat.card_eq_fintype_card] at hmod
  exact hmod

private theorem eq_one_or_eq_81_of_dvd_of_modEq {n : ℕ} (hn : n ∣ 81) (h5 : n ≡ 1 [MOD 5]) :
    n = 1 ∨ n = 81 := by
  have hn' : n ∈ Nat.divisors 81 := Nat.mem_divisors.mpr ⟨hn, by norm_num⟩
  have hdiv : Nat.divisors 81 = {1, 3, 9, 27, 81} := by decide
  rw [hdiv] at hn'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn'
  rcases hn' with rfl | rfl | rfl | rfl | rfl <;> simp_all [Nat.ModEq]

private theorem false_of_card_eq_405 {Y : Type*} [Group Y] [Finite Y] (hY : Nat.card Y = 405)
    (hC : ∀ b t : Y, orderOf b = 5 → t ^ 81 = 1 → b * t = t * b → t = 1)
    (h9 : ∀ T : Subgroup Y, Nat.card T = 81 → ∃ t ∈ T, orderOf t = 9) : False := by
  classical
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 Y) := inferInstance
  have hfact3 : (Nat.card Y).factorization 3 = 4 := by
    rw [hY, show (405 : ℕ) = 3 ^ 4 * 5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 5)]
  have hT : Nat.card (T : Subgroup Y) = 81 := by
    rw [Sylow.card_eq_multiplicity, hfact3]
    norm_num
  have hTidx : (T : Subgroup Y).index = 5 := by
    have h := Subgroup.card_mul_index (T : Subgroup Y)
    rw [hT, hY] at h
    omega
  have hn3 : Nat.card (Sylow 3 Y) = 1 := by
    have hmod := card_sylow_modEq_one 3 Y
    have hdvd := Sylow.card_dvd_index T
    rw [hTidx] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card (Sylow 3 Y) <;> simp_all [Nat.ModEq]
  have hTn : (T : Subgroup Y).Normal := by
    have hidx := Sylow.card_eq_index_normalizer T
    rw [hn3] at hidx
    rw [← Subgroup.normalizer_eq_top_iff]
    exact Subgroup.index_eq_one.mp hidx.symm
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := Y) 5 (by rw [hY]; norm_num)
  have hb5 : b ^ 5 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hT81 : ∀ t ∈ (T : Subgroup Y), t ^ 81 = 1 := by
    intro t ht
    have h := pow_card_eq_one' (G := (T : Subgroup Y)) (x := ⟨t, ht⟩)
    rw [hT] at h
    exact congrArg Subtype.val h
  let Z : Subgroup Y := (Subgroup.center (T : Subgroup Y)).map (T : Subgroup Y).subtype
  have hZT : Z ≤ (T : Subgroup Y) := Subgroup.map_subtype_le _
  have hmemZ : ∀ x : Y, x ∈ Z ↔ x ∈ (T : Subgroup Y) ∧ ∀ t ∈ (T : Subgroup Y), t * x = x * t := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun t ht => ?_⟩
      have := Subgroup.mem_center_iff.mp hy ⟨t, ht⟩
      exact congrArg Subtype.val this
    · rintro ⟨hxT, hx⟩
      refine ⟨⟨x, hxT⟩, Subgroup.mem_center_iff.mpr fun t => Subtype.ext (hx t t.2), rfl⟩
  have hZb : ∀ u ∈ Z, b * u * b⁻¹ ∈ Z := by
    intro u hu
    obtain ⟨huT, hu⟩ := (hmemZ u).mp hu
    refine (hmemZ _).mpr ⟨hTn.conj_mem u huT b, fun t ht => ?_⟩
    have ht' : b⁻¹ * t * b ∈ (T : Subgroup Y) := by
      have := hTn.conj_mem t ht b⁻¹
      simpa using this
    have hc := hu _ ht'
    calc t * (b * u * b⁻¹) = b * ((b⁻¹ * t * b) * u) * b⁻¹ := by group
      _ = b * (u * (b⁻¹ * t * b)) * b⁻¹ := by rw [hc]
      _ = b * u * b⁻¹ * t := by group
  have hZmod := card_modEq_one_of_pow_five hb5 hZb
    (fun u hu hc => hC b u hb (hT81 u (hZT hu)) hc)
  have hZdvd : Nat.card Z ∣ 81 := hT ▸ Subgroup.card_dvd_of_le hZT
  have hZne : Nat.card Z ≠ 1 := by
    intro h1
    have hnt : Nontrivial (Subgroup.center (T : Subgroup Y)) := by
      have : Nontrivial (T : Subgroup Y) :=
        Finite.one_lt_card_iff_nontrivial.mp (by rw [hT]; norm_num)
      exact (T.isPGroup').center_nontrivial
    have hc1 : Nat.card (Subgroup.center (T : Subgroup Y)) = 1 := by
      rwa [Subgroup.card_map_of_injective (T : Subgroup Y).subtype_injective] at h1
    exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' hc1
  have hZ81 : Nat.card Z = 81 :=
    (eq_one_or_eq_81_of_dvd_of_modEq hZdvd hZmod).resolve_left hZne
  have hZeq : Z = (T : Subgroup Y) := Subgroup.eq_of_le_of_card_ge hZT (by rw [hZ81, hT])
  have hTab : ∀ x ∈ (T : Subgroup Y), ∀ y ∈ (T : Subgroup Y), x * y = y * x := by
    intro x hx y hy
    have hx' : x ∈ Z := by
      rw [hZeq]
      exact hx
    exact (((hmemZ x).mp hx').2 y hy).symm
  let U : Subgroup Y :=
    { carrier := {x | ∃ t ∈ (T : Subgroup Y), t ^ 3 = x}
      one_mem' := ⟨1, Subgroup.one_mem _, one_pow 3⟩
      mul_mem' := by
        rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
        refine ⟨s * t, Subgroup.mul_mem _ hs ht, ?_⟩
        exact ((show Commute s t from hTab s hs t ht).mul_pow 3)
      inv_mem' := by
        rintro _ ⟨t, ht, rfl⟩
        exact ⟨t⁻¹, Subgroup.inv_mem _ ht, inv_pow t 3⟩ }
  have hUT : U ≤ (T : Subgroup Y) := by
    rintro _ ⟨t, ht, rfl⟩
    exact Subgroup.pow_mem _ ht 3
  have hUb : ∀ u ∈ U, b * u * b⁻¹ ∈ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨b * t * b⁻¹, hTn.conj_mem t ht b, by simp [conj_pow]⟩
  have hUmod := card_modEq_one_of_pow_five hb5 hUb
    (fun u hu hc => hC b u hb (hT81 u (hUT hu)) hc)
  have hUdvd : Nat.card U ∣ 81 := hT ▸ Subgroup.card_dvd_of_le hUT
  obtain ⟨t, htT, ht9⟩ := h9 (T : Subgroup Y) hT
  rcases eq_one_or_eq_81_of_dvd_of_modEq hUdvd hUmod with hU1 | hU81
  ·
    have hbot : U = ⊥ := (Subgroup.card_eq_one).mp hU1
    have ht3 : t ^ 3 = 1 := by
      have hmem : t ^ 3 ∈ U := ⟨t, htT, rfl⟩
      rw [hbot] at hmem
      exact (Subgroup.mem_bot).mp hmem
    have h9dvd : orderOf t ∣ 3 := orderOf_dvd_of_pow_eq_one ht3
    rw [ht9] at h9dvd
    norm_num at h9dvd
  ·
    have hUeq : U = (T : Subgroup Y) := Subgroup.eq_of_le_of_card_ge hUT (by rw [hU81, hT])
    let φ : ↥(T : Subgroup Y) → ↥(T : Subgroup Y) := fun s =>
      ⟨(s : Y) ^ 3, Subgroup.pow_mem _ s.2 3⟩
    have hφs : Function.Surjective φ := by
      intro s
      have hs : (s : Y) ∈ U := by
        rw [hUeq]
        exact s.2
      obtain ⟨r, hr, hrs⟩ := hs
      exact ⟨⟨r, hr⟩, Subtype.ext hrs⟩
    have hφi : Function.Injective φ := Finite.injective_iff_surjective.mpr hφs
    have ht3T : t ^ 3 ∈ (T : Subgroup Y) := Subgroup.pow_mem _ htT 3
    have h1 : φ ⟨t ^ 3, ht3T⟩ = φ 1 := by
      apply Subtype.ext
      change (t ^ 3) ^ 3 = (1 : Y) ^ 3
      rw [← pow_mul, one_pow]
      have := pow_orderOf_eq_one t
      rwa [ht9] at this
    have h2 := congrArg Subtype.val (hφi h1)
    change t ^ 3 = 1 at h2
    have h9dvd : orderOf t ∣ 3 := orderOf_dvd_of_pow_eq_one h2
    rw [ht9] at h9dvd
    norm_num at h9dvd

private theorem false_of_card_eq_270 {Y : Type*} [Group Y] [Finite Y] (hY : Nat.card Y = 270)
    (hN : ∀ B : Subgroup Y, Nat.card B = 5 → Nat.card (Subgroup.normalizer (B : Set Y)) ∣ 40) :
    False := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 Y) := inferInstance
  have hfact5 : (Nat.card Y).factorization 5 = 1 := by
    rw [hY, show (270 : ℕ) = 54 * 5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 54),
      Nat.Prime.factorization_self (Fact.out : Nat.Prime 5)]
  have hP : Nat.card (P : Subgroup Y) = 5 := by
    rw [Sylow.card_eq_multiplicity, hfact5, pow_one]
  have h40 := hN P hP
  have h270 : Nat.card (Subgroup.normalizer ((P : Subgroup Y) : Set Y)) ∣ 270 := by
    rw [← hY]
    exact Subgroup.card_subgroup_dvd_card _
  have h5N : 5 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup Y) : Set Y)) := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := (P : Subgroup Y)))
    rwa [hP] at this
  have h10 : Nat.card (Subgroup.normalizer ((P : Subgroup Y) : Set Y)) ∣ 10 := by
    have := Nat.dvd_gcd h40 h270
    rwa [show Nat.gcd 40 270 = 10 by norm_num] at this
  have hmul := Subgroup.card_mul_index (Subgroup.normalizer ((P : Subgroup Y) : Set Y))
  have hmod := card_sylow_modEq_one 5 Y
  have hidx : Nat.card (Sylow 5 Y) =
      (Subgroup.normalizer ((P : Subgroup Y) : Set Y)).index := Sylow.card_eq_index_normalizer P
  rw [hidx] at hmod
  have hle := Nat.le_of_dvd (by norm_num) h10
  rw [hY] at hmul
  unfold Nat.ModEq at hmod
  interval_cases hc : Nat.card (Subgroup.normalizer ((P : Subgroup Y) : Set Y)) <;> omega

private theorem false_of_card_eq_810 {Y : Type*} [Group Y] [Finite Y] (hY : Nat.card Y = 810)
    (hC : ∀ b t : Y, orderOf b = 5 → t ^ 81 = 1 → b * t = t * b → t = 1)
    (h9 : ∀ T : Subgroup Y, Nat.card T = 81 → ∃ t ∈ T, orderOf t = 9) : False := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 Y) := inferInstance
  have hfact2 : (Nat.card Y).factorization 2 = 1 := by
    rw [hY, show (810 : ℕ) = 405 * 2 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 405),
      Nat.Prime.factorization_self Nat.prime_two]
  have hP : Nat.card (P : Subgroup Y) = 2 := by
    rw [Sylow.card_eq_multiplicity, hfact2, pow_one]
  have hcyc : IsCyclic (P : Subgroup Y) := isCyclic_of_prime_card hP
  have hmin : (Nat.card Y).minFac = 2 := by
    rw [hY]
    norm_num
  have hcompl := IsCyclic.isComplement' hmin hcyc
  set N := (MonoidHom.transferSylow P (hcyc.normalizer_le_centralizer hmin)).ker with hNdef
  have hNcard : Nat.card N = 405 := by
    have h := hcompl.card_mul
    rw [hP, hY] at h
    omega
  refine false_of_card_eq_405 (Y := ↥N) hNcard (fun b t hb ht hbt => ?_) (fun T hT => ?_)
  · have hb' : orderOf (b : Y) = 5 := by rw [Subgroup.orderOf_coe, hb]
    have ht' : (t : Y) ^ 81 = 1 := by
      have := congrArg Subtype.val ht
      simpa using this
    have hbt' : (b : Y) * t = t * b := congrArg Subtype.val hbt
    exact Subtype.ext (hC b t hb' ht' hbt')
  · obtain ⟨t, htT, ht9⟩ := h9 (T.map N.subtype)
      (by rw [Subgroup.card_map_of_injective N.subtype_injective, hT])
    obtain ⟨t', ht'T, rfl⟩ := Subgroup.mem_map.mp htT
    exact ⟨t', ht'T, by rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe] at ht9⟩

private theorem card_le_card_inf_centralizer_mul_card {X : Type*} [Group X] [Finite X]
    (P S : Subgroup X) (g : X) (hS : ∀ p ∈ P, ⁅p, g⁆ ∈ S) :
    Nat.card P ≤ Nat.card ↥(Subgroup.centralizer ({g} : Set X) ⊓ P) * Nat.card S := by
  let C : Subgroup P := (Subgroup.centralizer ({g} : Set X)).subgroupOf P
  have hCcard : Nat.card C = Nat.card ↥(Subgroup.centralizer ({g} : Set X) ⊓ P) := by
    change Nat.card ↥((Subgroup.centralizer ({g} : Set X)).subgroupOf P) = _
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hkey : ∀ a b : P, (⁅(a : X), g⁆ = ⁅(b : X), g⁆ ↔ a⁻¹ * b ∈ C) := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_mul,
      Subgroup.coe_inv, commutatorElement_def, commutatorElement_def]
    constructor
    · intro hab
      have h1 : (a : X) * g * (a : X)⁻¹ = (b : X) * g * (b : X)⁻¹ := mul_right_cancel hab
      calc (a : X)⁻¹ * b * g = (a : X)⁻¹ * ((b : X) * g * (b : X)⁻¹) * b := by group
        _ = (a : X)⁻¹ * ((a : X) * g * (a : X)⁻¹) * b := by rw [h1]
        _ = g * ((a : X)⁻¹ * b) := by group
    · intro hab
      have h1 : (a : X) * g * (a : X)⁻¹ = (b : X) * g * (b : X)⁻¹ := by
        calc (a : X) * g * (a : X)⁻¹ = (a : X) * (g * ((a : X)⁻¹ * b)) * (b : X)⁻¹ := by group
          _ = (a : X) * ((a : X)⁻¹ * b * g) * (b : X)⁻¹ := by rw [hab]
          _ = (b : X) * g * (b : X)⁻¹ := by group
      rw [h1]
  let F : P ⧸ C → S := fun q => Quotient.liftOn' q (fun p : P => (⟨⁅(p : X), g⁆, hS p p.2⟩ : S))
    (fun a b hab => Subtype.ext ((hkey a b).mpr (QuotientGroup.leftRel_apply.mp hab)))
  have hF : Function.Injective F := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.mpr ((hkey a b).mp (congrArg Subtype.val hxy))
  have hle : Nat.card (P ⧸ C) ≤ Nat.card S := Nat.card_le_card_of_injective F hF
  have hmul := Subgroup.card_mul_index C
  rw [hCcard] at hmul
  rw [← hmul, Subgroup.index]
  exact Nat.mul_le_mul_left _ hle

private theorem commute_inv_mul_of_conj {X : Type*} [Group X] {k x y c e : X}
    (hy : k * x * k⁻¹ = y) (hkc : k * c * k⁻¹ = e * c) (hec : Commute e c) (hey : Commute e y)
    (hk : Commute k ⁅x, c⁆) : Commute c (x⁻¹ * y) := by
  have hcomm : Commute e (y * c * y⁻¹ * c⁻¹) :=
    ((hey.mul_right hec).mul_right hey.inv_right).mul_right hec.inv_right
  have h1 : ⁅x, c⁆ = y * c * y⁻¹ * c⁻¹ := by
    calc ⁅x, c⁆ = k * ⁅x, c⁆ * k⁻¹ := by rw [hk.eq, mul_inv_cancel_right]
      _ = (k * x * k⁻¹) * (k * c * k⁻¹) * (k * x * k⁻¹)⁻¹ * (k * c * k⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      _ = y * (e * c) * y⁻¹ * (e * c)⁻¹ := by rw [hy, hkc]
      _ = (y * e) * (c * y⁻¹ * c⁻¹ * e⁻¹) := by group
      _ = (e * y) * (c * y⁻¹ * c⁻¹ * e⁻¹) := by rw [← hey.eq]
      _ = e * (y * c * y⁻¹ * c⁻¹) * e⁻¹ := by group
      _ = (y * c * y⁻¹ * c⁻¹) * e * e⁻¹ := by rw [hcomm.eq]
      _ = y * c * y⁻¹ * c⁻¹ := by group
  rw [commutatorElement_def] at h1
  have h2 : x * c * x⁻¹ = y * c * y⁻¹ := mul_right_cancel h1
  show c * (x⁻¹ * y) = x⁻¹ * y * c
  calc c * (x⁻¹ * y) = x⁻¹ * (x * c * x⁻¹) * y := by group
    _ = x⁻¹ * (y * c * y⁻¹) * y := by rw [h2]
    _ = x⁻¹ * y * c := by group

section QA45

open scoped Pointwise
open CFSG.ComponentClassification.CatFactsSmall.PSp43


private theorem qa45_eq_one_of_commute_orderOf_five
    (b t : ↥QA45.originalSubgroup) (hb : orderOf b = 5) (ht : t ^ 81 = 1) (hbt : b * t = t * b) :
    t = 1 := by
  obtain ⟨-, hC10, -⟩ := qa45_sylowFive (Subgroup.zpowers b) (by rw [Nat.card_zpowers, hb])
  have htC : t ∈ Subgroup.centralizer
      ((Subgroup.zpowers b : Subgroup ↥QA45.originalSubgroup) : Set ↥QA45.originalSubgroup) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (show Commute b t from hbt) k).eq
  have h10 : orderOf t ∣ 10 := hC10 ▸ Subgroup.orderOf_dvd_natCard _ htC
  have h81 : orderOf t ∣ 81 := orderOf_dvd_of_pow_eq_one ht
  have h1 : orderOf t ∣ Nat.gcd 10 81 := Nat.dvd_gcd h10 h81
  rw [show Nat.gcd 10 81 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

private theorem qa45_exists_orderOf_nine
    (T : Subgroup ↥QA45.originalSubgroup) (hT : Nat.card T = 81) : ∃ t ∈ T, orderOf t = 9 := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfact : (Nat.card ↥QA45.originalSubgroup).factorization 3 = 4 := by
    rw [card_QA45, show (51840 : ℕ) = 3 ^ 4 * 640 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 640)]
  let TS : Sylow 3 ↥QA45.originalSubgroup := Sylow.ofCard T (by rw [hT, hfact]; norm_num)
  let e : ↥QA45.originalSubgroup := ⟨e9, e9_mem_A⟩
  have he : orderOf e = 9 := by rw [Subgroup.orderOf_mk, orderOf_e9]
  have hp : IsPGroup 3 (Subgroup.zpowers e) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, he]; norm_num)
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥QA45.originalSubgroup S TS
  refine ⟨g * e * g⁻¹, ?_, ?_⟩
  · have hmem : MulAut.conj g • e ∈ MulAut.conj g • (S : Subgroup ↥QA45.originalSubgroup) :=
      Subgroup.smul_mem_pointwise_smul e (MulAut.conj g) (S : Subgroup ↥QA45.originalSubgroup)
        (hS (Subgroup.mem_zpowers e))
    have hgS : ((g • S : Sylow 3 ↥QA45.originalSubgroup) : Subgroup ↥QA45.originalSubgroup) =
        MulAut.conj g • (S : Subgroup ↥QA45.originalSubgroup) :=
      Sylow.coe_subgroup_smul
    rw [← hgS, hg] at hmem
    simpa [TS, Sylow.coe_ofCard, MulAut.smul_def, MulAut.conj_apply] using hmem
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, he]

private theorem four_dvd_card_of_le_QP45
    {Q : Subgroup ↥QA45.originalSubgroup}
    (hQ : Q ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    (hbig : 25920 ≤ 128 * Nat.card Q) : 4 ∣ Nat.card Q := by
  by_contra h4
  obtain ⟨m, hm⟩ : Nat.card Q ∣ 25920 := by
    rw [← card_QP45_subgroupOf]
    exact Subgroup.card_dvd_of_le hQ
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have hm128 : m ≤ 128 := by
    by_contra hlt
    have : Nat.card Q * 129 ≤ Nat.card Q * m := Nat.mul_le_mul_left _ (by omega)
    omega
  have hcases : Nat.card Q = 270 ∨ Nat.card Q = 405 ∨ Nat.card Q = 810 := by
    interval_cases m <;> omega
  have hC : ∀ b t : ↥Q, orderOf b = 5 → t ^ 81 = 1 → b * t = t * b → t = 1 := by
    intro b t hb ht hbt
    have hb' : orderOf (b : ↥QA45.originalSubgroup) = 5 := by rw [Subgroup.orderOf_coe, hb]
    have ht' : (t : ↥QA45.originalSubgroup) ^ 81 = 1 := by
      have := congrArg Subtype.val ht
      simpa using this
    exact Subtype.ext (qa45_eq_one_of_commute_orderOf_five b t hb' ht'
      (congrArg Subtype.val hbt))
  have h9 : ∀ T : Subgroup ↥Q, Nat.card T = 81 → ∃ t ∈ T, orderOf t = 9 := by
    intro T hT
    obtain ⟨t, htT, ht9⟩ := qa45_exists_orderOf_nine (T.map Q.subtype)
      (by rw [Subgroup.card_map_of_injective Q.subtype_injective, hT])
    obtain ⟨t', ht'T, rfl⟩ := Subgroup.mem_map.mp htT
    exact ⟨t', ht'T, by rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe] at ht9⟩
  rcases hcases with h | h | h
  · refine false_of_card_eq_270 (Y := ↥Q) h fun B hB => ?_
    obtain ⟨hN40, -⟩ := qa45_sylowFive (B.map Q.subtype)
      (by rw [Subgroup.card_map_of_injective Q.subtype_injective, hB])
    have hle := Subgroup.le_normalizer_map (H := B) Q.subtype
    have hdvd := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective Q.subtype_injective, hN40] at hdvd
  · exact false_of_card_eq_405 (Y := ↥Q) h hC h9
  · exact false_of_card_eq_810 (Y := ↥Q) h hC h9

end QA45

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

section Steps

open CFSG.ComponentClassification.CatFactsSmall.PSp43

private theorem card_J1sub (h : Tim79a.ParrottHyp z) :
    Nat.card (J1sub (z := z) (D := D) h) = 2 ^ 8 := by
  let _ : CommGroup (QuotientV.V z) := commGroupV h
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  let C : Subgroup (J z) :=
    Subgroup.centralizer (centralizerJ (sigma1Nine (z := z) D) : Set (J z))
  have hCim : C.map (QuotientV.pi z) = commutatorV h (sigma1Nine (z := z) D) := by
    apply Subgroup.toAddSubgroup.injective
    have h' := congrArg Submodule.toAddSubgroup
      (centralizerCentralizerJ_image_eq (z := z) (D := D) (h := h))
    simpa [Cimage, commutatorVSubmodule, C, Subgroup.toAddSubgroup,
      AddSubgroup.toZModSubmodule] using h'
  have hW : Nat.card (C.map (QuotientV.pi z)) = 2 ^ 6 := by
    rw [hCim]
    exact card_Wsub (z := z) (D := D) h
  have hZC : Subgroup.center (J z) ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro c _
    exact Subgroup.mem_center_iff.mp hx c
  let φ : C →* QuotientV.V z := (QuotientV.pi z).comp C.subtype
  have hrange : φ.range = C.map (QuotientV.pi z) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker = (Subgroup.center (J z)).subgroupOf C := by
    ext c
    change QuotientV.pi z (c : J z) = 1 ↔ (c : J z) ∈ Subgroup.center (J z)
    rw [← MonoidHom.mem_ker, QuotientV.pi_ker, QuotientV.centerIn_subgroupOf_eq_center]
  have hkercard : Nat.card φ.ker = 4 := by
    rw [hker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv).trans
      (card_center_subgroupOf_J (z := z) h)
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hkercard, hrange, hW] at hcard
  rw [← centralizer_centralizerJ_eq_J1sub (z := z) (D := D) h,
    Subgroup.card_map_of_injective (J z).subtype_injective]
  change Nat.card C = 2 ^ 8
  rw [← hcard]
  norm_num

private theorem commutator_P_H_J_le_J1sub (h : Tim79a.ParrottHyp z)
    (hJ0 : (J0sub (z := z) (D := D)).Normal) :
    ⁅(P_H (z := z) D).map (H z).subtype, J z⁆ ≤ J1sub (z := z) (D := D) h := by
  have hCJ : CJ z (sigma1Nine (z := z) D : G) ≤ J z := inf_le_right
  have hPH : (P_H (z := z) D).map (H z).subtype ≤ H z := Subgroup.map_subtype_le _
  have h1 : ⁅⁅J z, CJ z (sigma1Nine (z := z) D : G)⁆, (P_H (z := z) D).map (H z).subtype⁆ =
      ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    calc ⁅J z, CJ z (sigma1Nine (z := z) D : G)⁆ ≤ ⁅J z, J z⁆ :=
          Subgroup.commutator_mono le_rfl hCJ
      _ = Subgroup.zpowers z := h.2.2.1
      _ ≤ Subgroup.centralizer (((P_H (z := z) D).map (H z).subtype : Subgroup G) : Set G) :=
          Subgroup.zpowers_le.mpr (Subgroup.centralizer_le hPH (z_centralizes_H (z := z) h))
  have h2 : ⁅⁅CJ z (sigma1Nine (z := z) D : G), (P_H (z := z) D).map (H z).subtype⁆, J z⁆ =
      ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact (P_H_commutator_CJ_le_center (z := z) D h hJ0).trans
      (centerIn_le_centralizer_J (z := z))
  have hcent : ⁅(P_H (z := z) D).map (H z).subtype, J z⁆ ≤
      Subgroup.centralizer (CJ z (sigma1Nine (z := z) D : G) : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp
      (Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2)
  have hPJ : ⁅(P_H (z := z) D).map (H z).subtype, J z⁆ ≤ J z := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨a, -, rfl⟩ b hb
    have hconj : (a : G) * b * (a : G)⁻¹ ∈ J z := by
      have hmem := hN.conj_mem (⟨b, J_le_H (z := z) hb⟩ : ↥(H z))
        (Subgroup.mem_subgroupOf.mpr hb) a
      exact Subgroup.mem_subgroupOf.mp hmem
    rw [Subgroup.coe_subtype, commutatorElement_def]
    exact (J z).mul_mem hconj ((J z).inv_mem hb)
  intro x hx
  have hxJ : x ∈ J z := hPJ hx
  have hxc : x ∈ Subgroup.centralizer (CJ z (sigma1Nine (z := z) D : G) : Set G) := hcent hx
  rw [← centralizer_centralizerJ_eq_J1sub (z := z) (D := D) h]
  refine Subgroup.mem_map.mpr ⟨⟨x, hxJ⟩, ?_, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have hcC : (c : G) ∈ CJ z (sigma1Nine (z := z) D : G) :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (mem_centralizerJ_iff.mp hc), c.2⟩
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc (c : G) hcC)

private theorem card_P_H (h : Tim79a.ParrottHyp z) :
    Nat.card (P_H (z := z) D) = 2 ^ 10 * 25920 := by
  have hH : Nat.card ↥(H z) = 2 ^ 10 * 51840 := by
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup ((J z).subgroupOf (H z))
    rw [Nat.card_congr (D.toQA45 (z := z) (hN := hN)).toEquiv, card_QA45,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (J_le_H (z := z))).toEquiv, card_J h] at hq
    rw [hq]
    ring
  have hmul := Subgroup.card_mul_index (P_H (z := z) D)
  rw [index_P_H, hH] at hmul
  norm_num at hmul ⊢
  omega

private theorem two_pow_eleven_dvd_card (h : Tim79a.ParrottHyp z)
    (hJ0 : (J0sub (z := z) (D := D)).Normal) {j : J z} (hjZ : j ∉ Subgroup.center (J z)) :
    2 ^ 11 ∣ Nat.card ↥(Subgroup.centralizer
      ({Subgroup.inclusion (J_le_H (z := z)) j} : Set ↥(H z)) ⊓ P_H (z := z) D) := by
  let jH : ↥(H z) := Subgroup.inclusion (J_le_H (z := z)) j
  let N : Subgroup ↥(H z) := Subgroup.centralizer ({jH} : Set ↥(H z)) ⊓ P_H (z := z) D
  change 2 ^ 11 ∣ Nat.card N
  have hS : ∀ p ∈ P_H (z := z) D, ⁅p, jH⁆ ∈ (J1sub (z := z) (D := D) h).subgroupOf (H z) := by
    intro p hp
    rw [Subgroup.mem_subgroupOf]
    exact commutator_P_H_J_le_J1sub (z := z) (D := D) h hJ0
      (Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem (H z).subtype hp) j.2)
  have hle := card_le_card_inf_centralizer_mul_card (P_H (z := z) D) _ jH hS
  have hS8 : Nat.card ↥((J1sub (z := z) (D := D) h).subgroupOf (H z)) = 2 ^ 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((J1sub_le_J (z := z) (D := D) h).trans (J_le_H (z := z)))).toEquiv]
    exact card_J1sub (z := z) (D := D) h
  rw [hS8, card_P_H (z := z) D h] at hle
  let f : N →* QA45.originalSubgroup := (qH (z := z) D).comp N.subtype
  have hmemJ : ∀ x : f.ker, (((x : N) : ↥(H z)) : G) ∈ J z := by
    intro x
    have hx : qH (z := z) D ((x : N) : ↥(H z)) = 1 := MonoidHom.mem_ker.mp x.2
    exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr hx)
  have hmemC : ∀ x : f.ker, (⟨(((x : N) : ↥(H z)) : G), hmemJ x⟩ : J z) ∈
      Subgroup.centralizer ({j} : Set (J z)) := by
    intro x
    have hc : ((x : N) : ↥(H z)) * jH = jH * ((x : N) : ↥(H z)) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (x : N).2).1
    have hval : (((x : N) : ↥(H z)) : G) * (j : G) = (j : G) * (((x : N) : ↥(H z)) : G) :=
      congrArg Subtype.val hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hval
  have hmemN : ∀ c : Subgroup.centralizer ({j} : Set (J z)),
      (⟨(c : G), J_le_H (z := z) (c : J z).2⟩ : ↥(H z)) ∈ N := by
    intro c
    have hc : (c : J z) * j = j * (c : J z) := Subgroup.mem_centralizer_singleton_iff.mp c.2
    have hval : (c : G) * (j : G) = (j : G) * (c : G) := congrArg Subtype.val hc
    refine Subgroup.mem_inf.mpr ⟨?_, J_le_P_H D (Subgroup.mem_subgroupOf.mpr (c : J z).2)⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hval
  have hmemK : ∀ c : Subgroup.centralizer ({j} : Set (J z)),
      (⟨⟨(c : G), J_le_H (z := z) (c : J z).2⟩, hmemN c⟩ : N) ∈ f.ker := by
    intro c
    exact MonoidHom.mem_ker.mpr ((J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr (c : J z).2))
  have hker : Nat.card f.ker = 2 ^ 9 := by
    rw [← card_centralizerJ_eq_two_pow_nine_of_notMem_center h hjZ]
    exact Nat.card_congr
      { toFun := fun x => ⟨⟨_, hmemJ x⟩, hmemC x⟩
        invFun := fun c => ⟨⟨⟨(c : G), J_le_H (z := z) (c : J z).2⟩, hmemN c⟩, hmemK c⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hrange : f.range = N.map (qH (z := z) D) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardN := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange] at hcardN
  have hQle : N.map (qH (z := z) D) ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_P_H_iff (z := z) D x).mp hx.2
  have hbig : 25920 ≤ 128 * Nat.card (N.map (qH (z := z) D)) := by
    rw [← hcardN] at hle
    have h1 : (2 : ℕ) ^ 10 * 25920 = 1024 * 25920 := by norm_num
    have h2 : 2 ^ 9 * Nat.card (N.map (qH (z := z) D)) * 2 ^ 8 =
        1024 * (128 * Nat.card (N.map (qH (z := z) D))) := by ring
    rw [h1, h2] at hle
    exact Nat.le_of_mul_le_mul_left hle (by norm_num)
  obtain ⟨m, hm⟩ := four_dvd_card_of_le_QP45 hQle hbig
  rw [← hcardN, hm]
  exact ⟨m, by ring⟩

private theorem exists_commutator_notMem_center (h : Tim79a.ParrottHyp z) {j : J z}
    (hjZ : j ∉ Subgroup.center (J z)) {K₀ : Subgroup ↥(H z)} (hK₀P : K₀ ≤ P_H (z := z) D)
    (hK₀C : K₀ ≤ Subgroup.centralizer ({Subgroup.inclusion (J_le_H (z := z)) j} : Set ↥(H z)))
    (hK₀ : 2 ^ 11 ≤ Nat.card K₀) :
    ∃ k ∈ K₀, ∃ c ∈ Subgroup.centralizer ({j} : Set (J z)),
      ⁅((k : ↥(H z)) : G), (c : G)⁆ ∉ centerIn (J z) := by
  by_contra hcon
  push Not at hcon
  have hCidx := index_centralizerJ_eq_two h hjZ
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : J z, x₀ ∉ Subgroup.centralizer ({j} : Set (J z)) := by
    by_contra hall
    push Not at hall
    have htop : Subgroup.centralizer ({j} : Set (J z)) = ⊤ :=
      eq_top_iff.mpr fun x _ => hall x
    rw [htop, Subgroup.index_top] at hCidx
    exact absurd hCidx (by norm_num)
  have hfix : ∀ k ∈ K₀, ∀ c ∈ Subgroup.centralizer ({j} : Set (J z)),
      conjV h k (QuotientV.pi z c) = QuotientV.pi z c := by
    intro k hk c hc
    rw [conjV_mk]
    have hmem : conjJ' z k c * c⁻¹ ∈ (QuotientV.pi z).ker := by
      rw [QuotientV.pi_ker, Subgroup.mem_subgroupOf]
      have hval : ((conjJ' z k c * c⁻¹ : J z) : G) = ⁅(k : G), (c : G)⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, conjJ'_apply_coe, commutatorElement_def]
      rw [hval]
      exact hcon k hk c hc
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hmem
    exact hmem
  have hmove : ∀ k ∈ K₀, (QuotientV.pi z x₀)⁻¹ * conjV h k (QuotientV.pi z x₀) ∈
      Subgroup.zpowers (QuotientV.pi z j) := by
    intro k hk
    have hbC : x₀⁻¹ * conjJ' z k x₀ ∈
        Subgroup.centralizer (Subgroup.centralizer ({j} : Set (J z)) : Set (J z)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have he := hcon k hk c hc
      have hzk : Commute (k : G) ⁅(x₀ : G), (c : G)⁆ := by
        have ht : ⁅(x₀ : G), (c : G)⁆ ∈ Subgroup.zpowers z := by
          rw [← h.2.2.1]
          exact Subgroup.commutator_mem_commutator x₀.2 c.2
        exact Subgroup.mem_centralizer_iff.mp
          (Subgroup.zpowers_le.mpr (z_centralizes_H (z := z) h) ht) (k : G) k.2
      have hcomm := commute_inv_mul_of_conj (k := (k : G)) (x := (x₀ : G))
        (y := ((conjJ' z k x₀ : J z) : G)) (c := (c : G)) (e := ⁅(k : G), (c : G)⁆)
        (conjJ'_apply_coe k x₀).symm (by rw [commutatorElement_def]; group)
        (Subgroup.mem_centralizer_iff.mp he.2 (c : G) c.2).symm
        (Subgroup.mem_centralizer_iff.mp he.2 _ (conjJ' z k x₀).2).symm hzk
      exact Subtype.ext hcomm.eq
    rw [centralizer_centralizer_eq_sup_center h] at hbC
    have hπb := Subgroup.mem_map_of_mem (QuotientV.pi z) hbC
    have hZker : (Subgroup.center (J z)).map (QuotientV.pi z) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientV.pi_ker, QuotientV.centerIn_subgroupOf_eq_center]
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hZker, sup_bot_eq, map_mul, map_inv,
      ← conjV_mk] at hπb
    exact hπb
  have hdet : ∀ k₁ ∈ K₀, ∀ k₂ ∈ K₀,
      conjV h k₁ (QuotientV.pi z x₀) = conjV h k₂ (QuotientV.pi z x₀) →
        conjV h k₁ = conjV h k₂ := by
    intro k₁ hk₁ k₂ hk₂ h12
    refine MulEquiv.ext fun v => ?_
    obtain ⟨x, rfl⟩ := QuotientV.pi_surjective z v
    by_cases hx : x ∈ Subgroup.centralizer ({j} : Set (J z))
    · rw [hfix k₁ hk₁ x hx, hfix k₂ hk₂ x hx]
    · have hu : x₀⁻¹ * x ∈ Subgroup.centralizer ({j} : Set (J z)) := by
        rw [Subgroup.mul_mem_iff_of_index_two hCidx, Subgroup.inv_mem_iff]
        exact iff_of_false hx₀ hx
      obtain ⟨u, hu', rfl⟩ : ∃ u ∈ Subgroup.centralizer ({j} : Set (J z)), x = x₀ * u :=
        ⟨x₀⁻¹ * x, hu, by group⟩
      rw [map_mul, map_mul, map_mul, h12, hfix k₁ hk₁ u hu', hfix k₂ hk₂ u hu']
  let ψ : ↥K₀ →* MulAut (QuotientV.V z) := (conjV h).comp K₀.subtype
  have hkJ : ∀ k : ψ.ker, (((k : ↥K₀) : ↥(H z)) : G) ∈ J z := by
    intro k
    have hV : conjV h ((k : ↥K₀) : ↥(H z)) = 1 := MonoidHom.mem_ker.mp k.2
    have hq := (mem_P_H_iff (z := z) D _).mp (hK₀P (k : ↥K₀).2)
    exact mem_J_of_conjZ_eq_one_of_conjV_eq_one h
      (conjZ_eq_one_of_qH_mem_QP45 (z := z) D h _ (Subgroup.mem_subgroupOf.mp hq)) hV
  have hkC : ∀ k : ψ.ker, (⟨(((k : ↥K₀) : ↥(H z)) : G), hkJ k⟩ : J z) ∈
      Subgroup.centralizer ({j} : Set (J z)) := by
    intro k
    have hc : ((k : ↥K₀) : ↥(H z)) * Subgroup.inclusion (J_le_H (z := z)) j =
        Subgroup.inclusion (J_le_H (z := z)) j * ((k : ↥K₀) : ↥(H z)) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hK₀C (k : ↥K₀).2)
    have hval : (((k : ↥K₀) : ↥(H z)) : G) * (j : G) = (j : G) * (((k : ↥K₀) : ↥(H z)) : G) :=
      congrArg Subtype.val hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hval
  have hkerle : Nat.card ψ.ker ≤ 2 ^ 9 := by
    rw [← card_centralizerJ_eq_two_pow_nine_of_notMem_center h hjZ]
    refine Nat.card_le_card_of_injective (fun k => (⟨⟨_, hkJ k⟩, hkC k⟩ :
      Subgroup.centralizer ({j} : Set (J z)))) ?_
    intro a b hab
    have hval : (((a : ↥K₀) : ↥(H z)) : G) = (((b : ↥K₀) : ↥(H z)) : G) :=
      congrArg (fun x : Subgroup.centralizer ({j} : Set (J z)) => ((x : J z) : G)) hab
    exact Subtype.ext (Subtype.ext (Subtype.ext hval))
  have hmoveR : ∀ φ ∈ ψ.range, (QuotientV.pi z x₀)⁻¹ * φ (QuotientV.pi z x₀) ∈
      Subgroup.zpowers (QuotientV.pi z j) := by
    rintro _ ⟨k, rfl⟩
    exact hmove k k.2
  have hzp : Nat.card (Subgroup.zpowers (QuotientV.pi z j)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num)
      (orderOf_dvd_of_pow_eq_one (QuotientV.pow_two_eq_one_V h _))
  have hrangele : Nat.card ψ.range ≤ 2 := by
    refine le_trans (Nat.card_le_card_of_injective (fun φ =>
      (⟨_, hmoveR φ φ.2⟩ : Subgroup.zpowers (QuotientV.pi z j))) ?_) hzp
    intro φ₁ φ₂ h12
    have h12' := mul_left_cancel (congrArg Subtype.val h12)
    obtain ⟨⟨k₁, hk₁⟩, hφ₁⟩ := φ₁.2
    obtain ⟨⟨k₂, hk₂⟩, hφ₂⟩ := φ₂.2
    apply Subtype.ext
    rw [← hφ₁, ← hφ₂] at h12' ⊢
    exact hdet k₁ hk₁ k₂ hk₂ h12'
  have hcard := Subgroup.card_ker_mul_card_range ψ
  have hle : Nat.card K₀ ≤ 2 ^ 9 * 2 := by
    rw [← hcard]
    exact Nat.mul_le_mul hkerle hrangele
  norm_num at hle hK₀
  omega

end Steps

theorem zpowers_le_commutator_derived_of_equalityBranch (h : Tim79a.ParrottHyp z)
    (hEq : ParrottEqualityBranch (z := z) (D := D) h) {j : J z}
    (hjZ : j ∉ Subgroup.center (J z)) (hj1 : (j : G) ∉ J1sub (z := z) (D := D) h)
    {K : Subgroup ↥(H z)}
    (hCK : (Subgroup.centralizer ({j} : Set (J z))).map
      (Subgroup.inclusion (J_le_H (z := z))) ≤ K)
    (hKS : IsSylowOf 2 (K.map (H z).subtype)
      (H z ⊓ Subgroup.centralizer ({(j : G)} : Set G))) :
    Subgroup.zpowers z ≤ ⁅K, ⁅K, K⁆⁆.map (H z).subtype := by
  obtain ⟨σ₂, hs₂, hq₂, hCJ⟩ := hEq
  have hJ0 := J0sub_normal (z := z) (D := D) h hCJ hs₂ hq₂
  have hmapC : (Subgroup.centralizer
      ({Subgroup.inclusion (J_le_H (z := z)) j} : Set ↥(H z))).map (H z).subtype =
      H z ⊓ Subgroup.centralizer ({(j : G)} : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hy' : y * Subgroup.inclusion (J_le_H (z := z)) j =
          Subgroup.inclusion (J_le_H (z := z)) j * y :=
        Subgroup.mem_centralizer_singleton_iff.mp hy
      have hval : (y : G) * (j : G) = (j : G) * (y : G) := congrArg Subtype.val hy'
      exact Subgroup.mem_inf.mpr ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr hval⟩
    · intro hx
      obtain ⟨hxH, hxc⟩ := Subgroup.mem_inf.mp hx
      have hval : x * (j : G) = (j : G) * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
      have hy : (⟨x, hxH⟩ : ↥(H z)) * Subgroup.inclusion (J_le_H (z := z)) j =
          Subgroup.inclusion (J_le_H (z := z)) j * ⟨x, hxH⟩ := Subtype.ext hval
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hxH⟩, Subgroup.mem_centralizer_singleton_iff.mpr hy, rfl⟩
  rw [← hmapC] at hKS
  have hKS' := (isSylowOf_map_subtype_iff (H z)).mp hKS
  have hPn : (P_H (z := z) D).Normal := P_H_normal (z := z) D
  have hnorm : Subgroup.centralizer ({Subgroup.inclusion (J_le_H (z := z)) j} : Set ↥(H z)) ≤
      Subgroup.normalizer ((Subgroup.centralizer
        ({Subgroup.inclusion (J_le_H (z := z)) j} : Set ↥(H z)) ⊓ P_H (z := z) D :
          Subgroup ↥(H z)) : Set ↥(H z)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hx1) (Subgroup.inv_mem _ hg),
        hPn.conj_mem x hx2 g⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨?_, ?_⟩
      · have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hx1) hg
        simpa [mul_assoc] using this
      · have := hPn.conj_mem _ hx2 g⁻¹
        simpa [mul_assoc] using this
  have hK0S := hKS'.inf_of_le_normalizer inf_le_left hnorm
  have hK0 : 2 ^ 11 ≤ Nat.card ↥(K ⊓ (Subgroup.centralizer
      ({Subgroup.inclusion (J_le_H (z := z)) j} : Set ↥(H z)) ⊓ P_H (z := z) D)) := by
    have hdvdN := two_pow_eleven_dvd_card (z := z) D h hJ0 hjZ
    have hne : Nat.card ↥(Subgroup.centralizer
        ({Subgroup.inclusion (J_le_H (z := z)) j} : Set ↥(H z)) ⊓ P_H (z := z) D) ≠ 0 :=
      Nat.card_pos.ne'
    have hdvd : 2 ^ 11 ∣ Nat.card ↥(K ⊓ (Subgroup.centralizer
        ({Subgroup.inclusion (J_le_H (z := z)) j} : Set ↥(H z)) ⊓ P_H (z := z) D)) := by
      rw [hK0S.card_eq]
      exact pow_dvd_pow 2 ((Nat.prime_two.pow_dvd_iff_le_factorization hne).mp hdvdN)
    exact Nat.le_of_dvd Nat.card_pos hdvd
  obtain ⟨k, hk, c, hc, hkc⟩ := exists_commutator_notMem_center (z := z) D h hjZ
    (K₀ := K ⊓ (Subgroup.centralizer
      ({Subgroup.inclusion (J_le_H (z := z)) j} : Set ↥(H z)) ⊓ P_H (z := z) D))
    (fun _ hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).2)
    (fun _ hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).1) hK0
  have hkK : k ∈ K := (Subgroup.mem_inf.mp hk).1
  have hkP : k ∈ P_H (z := z) D := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hk).2).2
  have hyJ1 : ⁅((k : ↥(H z)) : G), (c : G)⁆ ∈ J1sub (z := z) (D := D) h :=
    commutator_P_H_J_le_J1sub (z := z) (D := D) h hJ0
      (Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem (H z).subtype hkP) c.2)
  have hyJ : ⁅((k : ↥(H z)) : G), (c : G)⁆ ∈ J z := J1sub_le_J (z := z) (D := D) h hyJ1
  have hyC : (⟨⁅((k : ↥(H z)) : G), (c : G)⁆, hyJ⟩ : J z) ∉
      Subgroup.centralizer (Subgroup.centralizer ({j} : Set (J z)) : Set (J z)) := by
    rw [centralizer_centralizer_eq_sup_center h]
    intro hy
    have hy' := Subgroup.mem_map_of_mem (J z).subtype hy
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← centerIn_eq_map_center] at hy'
    have hy'' : ⁅((k : ↥(H z)) : G), (c : G)⁆ ∈ Subgroup.zpowers (j : G) ⊔ centerIn (J z) := hy'
    have hmem : ⁅((k : ↥(H z)) : G), (c : G)⁆ ∈
        (Subgroup.zpowers (j : G) ⊔ centerIn (J z)) ⊓ J1sub (z := z) (D := D) h :=
      Subgroup.mem_inf.mpr ⟨hy'', hyJ1⟩
    rw [sup_zpowers_center_inf_J1sub (z := z) (D := D) h hj1] at hmem
    exact hkc hmem
  rw [Subgroup.mem_centralizer_iff] at hyC
  push Not at hyC
  obtain ⟨a, ha, hay⟩ := hyC
  have haz : ⁅(a : G), ⁅((k : ↥(H z)) : G), (c : G)⁆⁆ = z := by
    have hmem : ⁅(a : G), ⁅((k : ↥(H z)) : G), (c : G)⁆⁆ ∈ Subgroup.zpowers z := by
      rw [← h.2.2.1]
      exact Subgroup.commutator_mem_commutator a.2 hyJ
    rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two h.1 hmem with h1 | h1
    · exfalso
      apply hay
      apply Subtype.ext
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · exact h1
  have haK : Subgroup.inclusion (J_le_H (z := z)) a ∈ K := hCK (Subgroup.mem_map_of_mem _ ha)
  have hcK : Subgroup.inclusion (J_le_H (z := z)) c ∈ K := hCK (Subgroup.mem_map_of_mem _ hc)
  have hzK : ⁅(a : G), ⁅((k : ↥(H z)) : G), (c : G)⁆⁆ ∈ ⁅K, ⁅K, K⁆⁆.map (H z).subtype :=
    Subgroup.mem_map.mpr ⟨_, Subgroup.commutator_mem_commutator haK
      (Subgroup.commutator_mem_commutator hkK hcK), by simp [commutatorElement_def]⟩
  rw [haz] at hzK
  exact Subgroup.zpowers_le.mpr hzK

end CFSG.RankThree.GF2n.Parrott
