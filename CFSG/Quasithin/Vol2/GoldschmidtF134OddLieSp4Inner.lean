module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Basic

public section

namespace CFSG.Quasithin.H13.NQCore.Psp4

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Lin2.Five (frobAut frobAut_apply tauAut tauAut_mul_self)

theorem conj_eq_of_conjNormal_eq_conj_odd {A : Type*} [Group A] [Finite A] {L U P : Subgroup A}
    [L.Normal] (hZ : Subgroup.center L = ⊥) (hU : IsSylowTwoOf U L) (hPL : P ≤ L) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hP : IsPGroup p P)
    (hPU : ∀ y ∈ P, ∀ u ∈ U, y * u * y⁻¹ ∈ U) {t : A}
    (ht2 : IsPGroup 2 (Subgroup.zpowers t)) (htU : t ∈ Subgroup.normalizer (U : Set A))
    (htP : t ∈ Subgroup.normalizer (P : Set A)) {x : L}
    (htx : MulAut.conjNormal t = MulAut.conj x) {y : A} (hy : y ∈ P) :
    t * y * t⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ l : L, t * (l : A) * t⁻¹ = (x : A) * l * (x : A)⁻¹ := by
    intro l
    have h := congrArg (fun α : MulAut L => ((α l : L) : A)) htx
    simpa [MulAut.conjNormal_apply] using h
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp ht2) ⟨t, Subgroup.mem_zpowers t⟩
  have hta : t ^ 2 ^ a = 1 := by
    have := pow_orderOf_eq_one (⟨t, Subgroup.mem_zpowers t⟩ : Subgroup.zpowers t)
    rw [ha] at this
    exact congrArg Subtype.val this
  have hxa : x ^ 2 ^ a = 1 := by
    have h1 : MulAut.conj (x ^ 2 ^ a) = 1 := by
      rw [map_pow, ← htx, ← map_pow, hta, map_one]
    have hmem : x ^ 2 ^ a ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      have := congrArg (fun α : MulAut L => α l) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc l * x ^ 2 ^ a = x ^ 2 ^ a * l * (x ^ 2 ^ a)⁻¹ * x ^ 2 ^ a := by rw [this]
        _ = x ^ 2 ^ a * l := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hxU : (x : A) ∈ Subgroup.normalizer (U : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hconj ⟨h, hU.1 hh⟩]
      exact (Subgroup.mem_normalizer_iff.mp htU h).mp hh
    · intro hh
      have hL : h ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem x.2) (hU.1 hh)) x.2
        rwa [show (x : A)⁻¹ * ((x : A) * h * (x : A)⁻¹) * x = h by group] at this
      rw [← hconj ⟨h, hL⟩] at hh
      exact (Subgroup.mem_normalizer_iff.mp htU h).mpr hh
  have hx2 : IsPGroup 2 (Subgroup.zpowers (x : A)) := by
    have hxa' : (x : A) ^ 2 ^ a = 1 := by
      rw [← SubgroupClass.coe_pow, hxa, OneMemClass.coe_one]
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxa')
    exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb])
  have hsup := CFSG.Quasithin.P134.le_of_isSylowTwoOf hU le_sup_right
    (sup_le (Subgroup.zpowers_le.mpr x.2) hU.1)
    (hx2.to_sup_of_normal_right' hU.2.1 (Subgroup.zpowers_le.mpr hxU))
  have hxU' : (x : A) ∈ U := hsup (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hyL : y ∈ L := hPL hy
  have hc1 : (x : A) * y * (x : A)⁻¹ * y⁻¹ ∈ P := by
    rw [← hconj ⟨y, hyL⟩]
    exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp htP y).mp hy) (P.inv_mem hy)
  have hc2 : (x : A) * y * (x : A)⁻¹ * y⁻¹ ∈ U := by
    rw [show (x : A) * y * (x : A)⁻¹ * y⁻¹ = x * (y * (x : A)⁻¹ * y⁻¹) by group]
    exact U.mul_mem hxU' (hPU y hy _ (U.inv_mem hxU'))
  have hdisj := IsPGroup.disjoint_of_ne p 2 hp2 P U hP hU.2.1
  have hc : (x : A) * y * (x : A)⁻¹ * y⁻¹ = 1 :=
    Subgroup.disjoint_def.mp hdisj hc1 hc2
  rw [hconj ⟨y, hyL⟩]
  calc (x : A) * y * (x : A)⁻¹ = (x : A) * y * (x : A)⁻¹ * y⁻¹ * y := by group
    _ = y := by rw [hc, one_mul]

theorem frobAut_pow_apply {F : Type} [Field F] [Finite F] [CharP F 2] (i : ℕ) (x : F) :
    (frobAut F ^ i) x = x ^ 2 ^ i := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    rw [pow_succ' (frobAut F)]
    change frobAut F ((frobAut F ^ i) x) = _
    rw [frobAut_apply, ih, ← pow_mul, pow_succ]

theorem frobAut_pow_card {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : Nat.card F = 2 ^ n) : frobAut F ^ n = 1 := by
  have := Fintype.ofFinite F
  refine RingEquiv.ext fun x => ?_
  rw [frobAut_pow_apply]
  change x ^ 2 ^ n = x
  have h := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, hn] at h

end CFSG.Quasithin.H13.NQCore.Psp4
