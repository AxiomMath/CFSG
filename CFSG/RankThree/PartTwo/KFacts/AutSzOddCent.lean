module

public import CFSG.RankThree.PartTwo.KFacts.AutSzTwoPower
import CFSG.Mathlib.FieldTheory.Finite.FixedUnits
import CFSG.GroupTheory.CoprimeCosetFixed
import CFSG.LocalAnalysis.SectionRank.SuzukiCover
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.AutTransport
open CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega
open CFSG.ComponentClassification.AschbacherToolkit.Bender.SuzukiAut
open CFSG.Open
open CFSG.BenderSuzuki CFSG.BenderSuzuki.External CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Pointwise

section

variable (m : ℕ)

local notation "F" => BinaryGaloisField (2 * m + 1)

private theorem pow_torus_mul_mem (y : Fˣ) {n : SuzukiMatrixGroup m}
    (hn : n ∈ rootSub m) :
    ∀ k : ℕ, ∃ n' ∈ rootSub m, (torus m y * n) ^ k = torus m (y ^ k) * n' := by
  intro k
  induction k with
  | zero =>
    exact ⟨1, (rootSub m).one_mem, by rw [pow_zero, pow_zero, torus_one m, one_mul]⟩
  | succ k ih =>
    obtain ⟨n', hn', hpow⟩ := ih
    have hyN : torus m y ∈ Subgroup.normalizer
        ((rootSub m : Subgroup (SuzukiMatrixGroup m)) : Set _) :=
      torusSub_le_normalizer m (torus_mem m y)
    have hinv : (torus m y)⁻¹ * n' * torus m y ∈ rootSub m :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hyN) n').mp hn'
    refine ⟨(torus m y)⁻¹ * n' * torus m y * n, (rootSub m).mul_mem hinv hn, ?_⟩
    rw [pow_succ, hpow, pow_succ, ← torus_mul]
    group

private theorem pow_torus_mul_mem_rootSub_iff (hm : 0 < m) (y : Fˣ)
    {n : SuzukiMatrixGroup m} (hn : n ∈ rootSub m) (k : ℕ) :
    (torus m y * n) ^ k ∈ rootSub m ↔ y ^ k = 1 := by
  constructor
  · intro hmem
    obtain ⟨n', hn', hpow⟩ := pow_torus_mul_mem m y hn k
    rw [hpow] at hmem
    have htor : torus m (y ^ k) ∈ rootSub m := by
      simpa using (rootSub m).mul_mem hmem ((rootSub m).inv_mem hn')
    exact (torus_mem_rootSub_iff m hm (y ^ k)).mp htor
  · intro hy
    obtain ⟨n', hn', hpow⟩ := pow_torus_mul_mem m y hn k
    rw [hpow, hy, torus_one m, one_mul]
    exact hn'

private theorem orderOf_pow_card_torus_mul (hm : 0 < m) (y : Fˣ)
    {n : SuzukiMatrixGroup m} (hn : n ∈ rootSub m)
    (hcop : Nat.Coprime (orderOf y) (Nat.card (rootSub m))) :
    orderOf ((torus m y * n) ^ Nat.card (rootSub m)) = orderOf y := by
  have hmem : (torus m y * n) ^ orderOf y ∈ rootSub m :=
    (pow_torus_mul_mem_rootSub_iff m hm y hn (orderOf y)).mpr (pow_orderOf_eq_one y)
  have hdvd : orderOf ((torus m y * n) ^ Nat.card (rootSub m)) ∣ orderOf y := by
    rw [orderOf_dvd_iff_pow_eq_one]
    calc
      ((torus m y * n) ^ Nat.card (rootSub m)) ^ orderOf y =
          (torus m y * n) ^ (Nat.card (rootSub m) * orderOf y) :=
        (pow_mul _ _ _).symm
      _ = (torus m y * n) ^ (orderOf y * Nat.card (rootSub m)) := by
        congr 1
        exact Nat.mul_comm _ _
      _ = ((torus m y * n) ^ orderOf y) ^ Nat.card (rootSub m) := pow_mul _ _ _
      _ = 1 := orderOf_dvd_iff_pow_eq_one.mp
        (Subgroup.orderOf_dvd_natCard (rootSub m) hmem)
  refine Nat.dvd_antisymm hdvd ?_
  set j := orderOf ((torus m y * n) ^ Nat.card (rootSub m)) with hj
  have hpow : (torus m y * n) ^ (Nat.card (rootSub m) * j) = 1 := by
    rw [pow_mul]
    exact pow_orderOf_eq_one _
  have hmemj : (torus m y * n) ^ (Nat.card (rootSub m) * j) ∈ rootSub m := by
    rw [hpow]
    exact (rootSub m).one_mem
  have hy : y ^ (Nat.card (rootSub m) * j) = 1 :=
    (pow_torus_mul_mem_rootSub_iff m hm y hn _).mp hmemj
  have hdvd' : orderOf y ∣ j * Nat.card (rootSub m) := by
    rw [show j * Nat.card (rootSub m) = Nat.card (rootSub m) * j from
      Nat.mul_comm _ _]
    exact orderOf_dvd_of_pow_eq_one hy
  exact hcop.dvd_of_dvd_mul_right hdvd'

private theorem theta_torus_mul_inv_mem (θ : MulAut (SuzukiMatrixGroup m))
    {r : SuzukiMatrixGroup m} {z : Fˣ} (hr : r ∈ rootSub m)
    (hR : ∀ r ∈ rootSub m, θ r ∈ rootSub m)
    (hxR : θ (r * torus m z) * (r * torus m z)⁻¹ ∈ rootSub m) :
    θ (torus m z) * (torus m z)⁻¹ ∈ rootSub m := by
  have h1 : (θ r)⁻¹ * (θ (r * torus m z) * (r * torus m z)⁻¹) * r ∈ rootSub m :=
    (rootSub m).mul_mem
      ((rootSub m).mul_mem ((rootSub m).inv_mem (hR r hr)) hxR) hr
  have heq : (θ r)⁻¹ * (θ (r * torus m z) * (r * torus m z)⁻¹) * r =
      θ (torus m z) * (torus m z)⁻¹ := by
    simp only [map_mul]
    group
  rwa [heq] at h1

private theorem tau_fixed_eq_one_of_s_eq_one (τ : F ≃+* F) {s : ℕ} {y : Fˣ}
    (hyord : orderOf y = 2 ^ s - 1)
    (hgen : ∀ z : Fˣ, τ (z : F) = (z : F) → z ∈ Subgroup.zpowers y)
    (hs1 : s = 1) : ∀ z : Fˣ, τ (z : F) = (z : F) → z = 1 := by
  have hy1 : y = 1 := by
    apply orderOf_eq_one_iff.mp
    rw [hyord, hs1]
    norm_num
  intro z hz
  have hzmem := hgen z hz
  rw [hy1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hzmem
  exact hzmem

private theorem mem_rootSub_of_normalizer_of_tau_fixed_trivial (hm : 0 < m)
    (θ : MulAut (SuzukiMatrixGroup m)) (τ : F ≃+* F)
    (hτ : ∀ x : Fˣ,
      (torus m (Units.map (τ : F →* F) x))⁻¹ * θ (torus m x) ∈ rootSub m)
    (hR : ∀ r ∈ rootSub m, θ r ∈ rootSub m)
    (hfix : ∀ z : Fˣ, τ (z : F) = (z : F) → z = 1)
    {x : SuzukiMatrixGroup m}
    (hxN : x ∈ Subgroup.normalizer ((rootSub m : Subgroup (SuzukiMatrixGroup m)) : Set _))
    (hxR : θ x * x⁻¹ ∈ rootSub m) : x ∈ rootSub m := by
  obtain ⟨r, hr, h, hh, rfl⟩ := (normalizer_and_card_sylow m hm).1 x hxN
  obtain ⟨z, rfl⟩ := (mem_torusSub m hm).mp hh
  have hzN : torus m z ∈ Subgroup.normalizer
      ((rootSub m : Subgroup (SuzukiMatrixGroup m)) : Set _) :=
    torusSub_le_normalizer m (torus_mem m z)
  set u : Fˣ := Units.map (τ : F →* F) z with hu
  set s : SuzukiMatrixGroup m := (torus m u)⁻¹ * θ (torus m z) with hs
  have hsR : s ∈ rootSub m := hτ z
  have hD : θ (torus m z) * (torus m z)⁻¹ ∈ rootSub m :=
    theta_torus_mul_inv_mem m θ hr hR hxR
  have hconj : torus m z * s * (torus m z)⁻¹ ∈ rootSub m :=
    (Subgroup.mem_normalizer_iff.mp hzN s).mp hsR
  have hθhz : θ (torus m z) = torus m u * s := by
    rw [hs]
    group
  have hE : torus m (u * z⁻¹) ∈ rootSub m := by
    have heq : θ (torus m z) * (torus m z)⁻¹ =
        torus m u * (torus m z)⁻¹ * (torus m z * s * (torus m z)⁻¹) := by
      rw [hθhz]
      group
    have htor : torus m u * (torus m z)⁻¹ = torus m (u * z⁻¹) := by
      rw [torus_inv, torus_mul]
    rw [heq, htor] at hD
    have hEq : torus m (u * z⁻¹) =
        (torus m (u * z⁻¹) * (torus m z * s * (torus m z)⁻¹)) *
          (torus m z * s * (torus m z)⁻¹)⁻¹ := by group
    rw [hEq]
    exact (rootSub m).mul_mem hD ((rootSub m).inv_mem hconj)
  have huz : u * z⁻¹ = 1 := (torus_mem_rootSub_iff m hm (u * z⁻¹)).mp hE
  have huz' : u = z := mul_inv_eq_one.mp huz
  have hτz : τ (z : F) = (z : F) := by
    have := congrArg Units.val huz'
    simpa [hu, Units.coe_map] using this
  have hz1 : z = 1 := hfix z hτz
  rw [hz1, torus_one m, mul_one]
  exact hr

theorem exists_fixed_of_odd_normalizes_rootSub (hm : 0 < m) (θ : MulAut (SuzukiMatrixGroup m))
    (hθ : Odd (orderOf θ)) (hR : ∀ r ∈ rootSub m, θ r ∈ rootSub m) :
    ∃ s : ℕ, s ∣ 2 * m + 1 ∧ (2 * m + 1) / s ∣ orderOf θ ∧
      (∃ x : SuzukiMatrixGroup m, orderOf x = 2 ^ s - 1 ∧ θ x = x) ∧
      (s = 1 → ∀ x ∈ Subgroup.normalizer
          ((rootSub m : Subgroup (SuzukiMatrixGroup m)) : Set _),
        θ x * x⁻¹ ∈ rootSub m → x ∈ rootSub m) := by
  classical
  obtain ⟨τ, _, _, hτmem⟩ := exists_ringEquiv_root_zero_torus m hm θ hR
  have hτpow : τ ^ orderOf θ = 1 :=
    pow_eq_one_of_mul_torus_mem m hm θ τ hR hτmem (pow_orderOf_eq_one θ)
  have hτdvd : orderOf τ ∣ orderOf θ := orderOf_dvd_of_pow_eq_one hτpow
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hsa, hsdiv, y, hyord, hyfix, hygen⟩ :=
    CFSG.exists_zpowers_eq_fixed_units (p := 2) (a := 2 * m + 1)
      (CFSG.SectionRank.natCard_binaryGaloisField m) τ
  have hs_pos : 0 < s := Nat.pos_of_dvd_of_pos hsa (by omega)
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootSub m hm
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card (rootSub m) = 2 ^ k := by
    have hp : IsPGroup 2 (rootSub m) := by
      rw [← hS]
      exact Sylow.isPGroup' S
    exact (IsPGroup.iff_card).mp hp
  have hy_units : Units.map (τ : F →* F) y = y := by
    ext
    simpa using hyfix
  have hcoset : (torus m y)⁻¹ * θ (torus m y) ∈ rootSub m := by
    simpa [hy_units] using hτmem y
  have hodd_y : Odd (orderOf y) := by
    rw [hyord]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.mpr ⟨even_two, hs_pos.ne'⟩) odd_one
  have hcop : Nat.Coprime (orderOf y) (Nat.card (rootSub m)) := by
    rw [hk]
    exact ((hodd_y.coprime_two_left).pow_left k).symm
  obtain ⟨n, hnR, hfixn⟩ :=
    CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime_mulAut (rootSub m) θ hR hcoset (by
      rw [hk]
      exact ((hθ.coprime_two_left).pow_left k).symm)
  refine ⟨s, hsa, ?_, ⟨(torus m y * n) ^ Nat.card (rootSub m), ?_, ?_⟩, ?_⟩
  · rw [hsdiv]
    exact hτdvd
  · rw [orderOf_pow_card_torus_mul m hm y hnR hcop, hyord]
  · rw [map_pow, hfixn]
  · intro hs1 x hxN hxR
    exact mem_rootSub_of_normalizer_of_tau_fixed_trivial m hm θ τ hτmem hR
      (tau_fixed_eq_one_of_s_eq_one m τ hyord hygen hs1) hxN hxR

private theorem exists_fixed_of_odd_of_map_equiv {X Y : Type*} [Group X] [Group Y]
    (ψ : X ≃* Y) (S : Subgroup X) (S' : Subgroup Y)
    (hSS' : S.map ψ.toMonoidHom = S') (θ : MulAut X) (a : ℕ)
    (h : ∃ s : ℕ, s ∣ a ∧ a / s ∣ orderOf (MulAut.congr ψ θ) ∧
      (∃ y : Y, orderOf y = 2 ^ s - 1 ∧ MulAut.congr ψ θ y = y) ∧
      (s = 1 → ∀ y ∈ Subgroup.normalizer (S' : Set Y),
        MulAut.congr ψ θ y * y⁻¹ ∈ S' → y ∈ S')) :
    ∃ s : ℕ, s ∣ a ∧ a / s ∣ orderOf θ ∧
      (∃ x : X, orderOf x = 2 ^ s - 1 ∧ θ x = x) ∧
      (s = 1 → ∀ x ∈ Subgroup.normalizer (S : Set X),
        θ x * x⁻¹ ∈ S → x ∈ S) := by
  obtain ⟨s, hsa, hsd, ⟨y, hyord, hyfix⟩, hclause⟩ := h
  have hcongr : orderOf (MulAut.congr ψ θ) = orderOf θ :=
    MulEquiv.orderOf_eq (MulAut.congr ψ) θ
  refine ⟨s, hsa, ?_, ⟨ψ.symm y, ?_, ?_⟩, ?_⟩
  · rwa [hcongr] at hsd
  · rw [MulEquiv.orderOf_eq ψ.symm y, hyord]
  · have := congrArg ψ.symm hyfix
    simpa [MulAut.congr_apply] using this
  · intro hs1 x hxN hxR
    have hyN : ψ x ∈ Subgroup.normalizer (S' : Set Y) := by
      have hmem : ψ x ∈ (Subgroup.normalizer (S : Set X)).map ψ.toMonoidHom :=
        Subgroup.mem_map_of_mem _ hxN
      rwa [Subgroup.map_equiv_normalizer_eq, hSS'] at hmem
    have hyR : MulAut.congr ψ θ (ψ x) * (ψ x)⁻¹ ∈ S' := by
      rw [← hSS']
      refine Subgroup.mem_map.mpr ⟨θ x * x⁻¹, hxR, ?_⟩
      simp [MulAut.congr_apply, map_mul, map_inv]
    have hyS' : ψ x ∈ S' := hclause hs1 (ψ x) hyN hyR
    have hxS : ψ.symm (ψ x) ∈ S := by
      rw [← hSS'] at hyS'
      exact (Subgroup.mem_map_equiv (f := ψ) (K := S)).mp hyS'
    simpa using hxS

theorem exists_fixed_of_odd_normalizes_sylow {X : Type*} [Group X] [Finite X] (hm : 0 < m)
    (e : X ≃* SuzukiMatrixGroup m) (S : Sylow 2 X) (θ : MulAut X) (hθ : Odd (orderOf θ))
    (hS : ∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) :
    ∃ s : ℕ, s ∣ 2 * m + 1 ∧ (2 * m + 1) / s ∣ orderOf θ ∧
      (∃ x : X, orderOf x = 2 ^ s - 1 ∧ θ x = x) ∧
      (s = 1 → ∀ x ∈ Subgroup.normalizer ((S : Subgroup X) : Set X),
        θ x * x⁻¹ ∈ (S : Subgroup X) → x ∈ (S : Subgroup X)) := by
  classical
  let S' : Sylow 2 (SuzukiMatrixGroup m) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S
  obtain ⟨g, hg⟩ := exists_eq_map_conj_rootSub m hm S'
  have hScoe : (S' : Subgroup (SuzukiMatrixGroup m)) =
      (S : Subgroup X).map e.toMonoidHom := rfl
  let ψ : X ≃* SuzukiMatrixGroup m := e.trans (MulAut.conj g).symm
  have hSψ : (S : Subgroup X).map ψ.toMonoidHom = rootSub m := by
    have h1 : (S : Subgroup X).map ψ.toMonoidHom =
        ((S : Subgroup X).map e.toMonoidHom).map
          (MulAut.conj g).symm.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [h1, ← hScoe, hg, Subgroup.map_map]
    have hcomp : (MulEquiv.symm (MulAut.conj g)).toMonoidHom.comp
        (MulEquiv.toMonoidHom (MulAut.conj g)) = MonoidHom.id _ := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  let θ' : MulAut (SuzukiMatrixGroup m) := MulAut.congr ψ θ
  have hθ' : Odd (orderOf θ') := by
    rw [show orderOf θ' = orderOf θ from MulEquiv.orderOf_eq (MulAut.congr ψ) θ]
    exact hθ
  have hR' : ∀ r ∈ rootSub m, θ' r ∈ rootSub m := by
    intro r hr
    rw [← hSψ] at hr ⊢
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hr
    refine Subgroup.mem_map.mpr ⟨θ x, hS x hx, ?_⟩
    simp [θ', MulAut.congr_apply]
  have hmain := exists_fixed_of_odd_normalizes_rootSub m hm θ' hθ' hR'
  exact exists_fixed_of_odd_of_map_equiv ψ (S : Subgroup X) (rootSub m) hSψ θ (2 * m + 1)
    (by simpa [θ'] using hmain)

end

end CFSG.RankThree.PartTwo.KFacts

end
