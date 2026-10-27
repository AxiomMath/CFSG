module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelOvergroup
public import CFSG.Quasithin.Vol2.KGNatSp4BorelOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender
public import CFSG.LargeExtraspecial.S8CBFSmall
public import CFSG.Quasithin.Vol2.Ch9KGFFSpConj
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QDiag
public import CFSG.Quasithin.Background.F918Z8Op4d
public import CFSG.Quasithin.Vol2.Ch1EightFourNum
public import CFSG.Adapters.LieModelSimple
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import TauCeti.GroupTheory.PGroup
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusFour
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartTwo.Sec4.Census (odd_two_pow_add_one)

theorem prod_le_normalizer_of_bender {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    [IsSimpleGroup A] [IsSimpleGroup B]
    (hbA : fusionIsBenderGroup A) (hbB : fusionIsBenderGroup B)
    (UA : Sylow 2 A) (UB : Sylow 2 B) (Y : Subgroup (A × B))
    (hUY : ((UA : Subgroup A).prod (UB : Subgroup B)) ≤ Y) {D dA dB : ℕ}
    (hYdvd : Nat.card Y ∣ Nat.card ((UA : Subgroup A).prod (UB : Subgroup B)) * D)
    (hdA : dA ∣ Nat.card A) (hdA1 : 1 < dA) (hoddA : Odd dA)
    (hcopDA : Nat.Coprime dA D)
    (hdB : dB ∣ Nat.card B) (hdB1 : 1 < dB) (hoddB : Odd dB)
    (hcopDB : Nat.Coprime dB D) :
    Y ≤ Subgroup.normalizer (((UA : Subgroup A).prod (UB : Subgroup B) :
      Subgroup (A × B)) : Set (A × B)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set YA : Subgroup A := Y.map (MonoidHom.fst A B) with hYAdef
  set YB : Subgroup B := Y.map (MonoidHom.snd A B) with hYBdef
  have hUA_le : (UA : Subgroup A) ≤ YA := by
    intro a ha
    exact Subgroup.mem_map.mpr
      ⟨(a, 1), hUY (Subgroup.mem_prod.mpr ⟨ha, Subgroup.one_mem (UB : Subgroup B)⟩), rfl⟩
  have hUB_le : (UB : Subgroup B) ≤ YB := by
    intro b hb
    exact Subgroup.mem_map.mpr
      ⟨(1, b), hUY (Subgroup.mem_prod.mpr ⟨Subgroup.one_mem (UA : Subgroup A), hb⟩), rfl⟩
  have hcopA : Nat.Coprime dA (Nat.card UA * Nat.card UB * D) := by
    obtain ⟨i, hi⟩ := UA.isPGroup'.exists_card_eq
    obtain ⟨j, hj⟩ := UB.isPGroup'.exists_card_eq
    rw [hi, hj]
    exact Nat.Coprime.mul_right
      (Nat.Coprime.mul_right (Nat.Coprime.pow_right i (Nat.coprime_two_right.mpr hoddA))
        (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hoddA))) hcopDA
  have hcopB : Nat.Coprime dB (Nat.card UA * Nat.card UB * D) := by
    obtain ⟨i, hi⟩ := UA.isPGroup'.exists_card_eq
    obtain ⟨j, hj⟩ := UB.isPGroup'.exists_card_eq
    rw [hi, hj]
    exact Nat.Coprime.mul_right
      (Nat.Coprime.mul_right (Nat.Coprime.pow_right i (Nat.coprime_two_right.mpr hoddB))
        (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hoddB))) hcopDB
  have hYA_ne : YA ≠ ⊤ := by
    intro htop
    have hdvdY : dA ∣ Nat.card Y := by
      have h1 : dA ∣ Nat.card YA := by rw [htop, Subgroup.card_top]; exact hdA
      exact h1.trans (Subgroup.card_map_dvd Y (MonoidHom.fst A B))
    have h2 : dA ∣ Nat.card ((UA : Subgroup A).prod (UB : Subgroup B)) * D :=
      hdvdY.trans hYdvd
    rw [CFSG.LocalAnalysis.EvenBN.Common.card_prod_subgroup] at h2
    have h3 : dA ∣ 1 := by
      have h4 : dA ∣ Nat.gcd dA (Nat.card UA * Nat.card UB * D) :=
        Nat.dvd_gcd (dvd_refl dA) h2
      rwa [hcopA] at h4
    have h1 : dA = 1 := Nat.dvd_one.mp h3
    omega
  have hYB_ne : YB ≠ ⊤ := by
    intro htop
    have hdvdY : dB ∣ Nat.card Y := by
      have h1 : dB ∣ Nat.card YB := by rw [htop, Subgroup.card_top]; exact hdB
      exact h1.trans (Subgroup.card_map_dvd Y (MonoidHom.snd A B))
    have h2 : dB ∣ Nat.card ((UA : Subgroup A).prod (UB : Subgroup B)) * D :=
      hdvdY.trans hYdvd
    rw [CFSG.LocalAnalysis.EvenBN.Common.card_prod_subgroup] at h2
    have h3 : dB ∣ 1 := by
      have h4 : dB ∣ Nat.gcd dB (Nat.card UA * Nat.card UB * D) :=
        Nat.dvd_gcd (dvd_refl dB) h2
      rwa [hcopB] at h4
    have h1 : dB = 1 := Nat.dvd_one.mp h3
    omega
  have hYA_le : YA ≤ Subgroup.normalizer (UA : Set A) :=
    CFSG.QuasithinUnique.Bridge.Over.le_normalizer_of_bender hbA UA hUA_le hYA_ne
  have hYB_le : YB ≤ Subgroup.normalizer (UB : Set B) :=
    CFSG.QuasithinUnique.Bridge.Over.le_normalizer_of_bender hbB UB hUB_le hYB_ne
  have hYle : Y ≤ YA.prod YB := by
    rintro ⟨a, b⟩ hab
    exact Subgroup.mem_prod.mpr
      ⟨Subgroup.mem_map.mpr ⟨(a, b), hab, rfl⟩,
        Subgroup.mem_map.mpr ⟨(a, b), hab, rfl⟩⟩
  exact hYle.trans (CFSG.LocalAnalysis.EvenBN.Common.prod_le_normalizer_prod hYA_le hYB_le)

theorem statedSp_le_normalizer {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    (hK : Nat.card K = 2 ^ n) (U : Sylow 2 (StatedSp 2 K)) (Y : Subgroup (StatedSp 2 K))
    (hUY : (U : Subgroup (StatedSp 2 K)) ≤ Y)
    (hYdvd : Nat.card Y ∣ Nat.card U * (Nat.card K - 1) ^ 2) :
    Y ≤ Subgroup.normalizer ((U : Subgroup (StatedSp 2 K)) : Set (StatedSp 2 K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  obtain ⟨P₀, hP₀⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_unipotent (K := K) 2 2
  obtain ⟨g, hg⟩ := CFSG.CGT.Timmesfeld75.exists_conjSubgroup_eq_of_sylow P₀ U
  rw [hP₀] at hg
  set Y' := Y.comap (MulAut.conj g).toMonoidHom with hY'
  have hmemY' : ∀ z, z ∈ Y' ↔ g * z * g⁻¹ ∈ Y := fun z => Iff.rfl
  have hUY' : unipotent 2 K ≤ Y' := by
    intro u hu
    rw [hmemY']
    refine hUY (hg ▸ CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr ?_)
    rw [show g⁻¹ * (g * u * g⁻¹) * g = u by group]
    exact hu
  have key : ∀ k : Fin 2, weylRep K k ∉ Y' := by
    intro k hk
    obtain ⟨φ, hφ, hφY⟩ :=
      CFSG.Quasithin.Vol2.KGNat.exists_SL2_le_of_weylRep_mem (F := K) hUY' k hk
    obtain ⟨x, p, hp, hx, hpq⟩ :=
      CFSG.Quasithin.Vol2.KGNat.exists_prime_order_dvd_succ (F := K)
    have hy : g * φ x * g⁻¹ ∈ Y := (hmemY' _).mp (hφY x)
    have hord : orderOf (g * φ x * g⁻¹) = p := by
      rw [show g * φ x * g⁻¹ = (MulAut.conj g).toMonoidHom (φ x) from rfl,
        orderOf_injective _ (MulAut.conj g).injective, orderOf_injective φ hφ, hx]
    have hpY : p ∣ Nat.card Y := by
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard Y hy
    have hpYdvd : p ∣ Nat.card U * (Nat.card K - 1) ^ 2 := hpY.trans hYdvd
    have hp2 : p ≠ 2 := by
      rintro rfl
      rw [hK] at hpq
      have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      omega
    have hpU : ¬ p ∣ Nat.card U := by
      obtain ⟨j, hj⟩ := U.isPGroup'.exists_card_eq
      rw [hj]
      intro h
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    have hq1 : p ∣ 2 ^ n - 1 := by
      have hsq : p ∣ (2 ^ n - 1) ^ 2 := by
        rcases hp.dvd_mul.mp (by rwa [hK] at hpYdvd) with h | h
        · exact absurd h hpU
        · exact h
      exact hp.dvd_of_dvd_pow hsq
    have hq2 : p ∣ 2 ^ n + 1 := by rwa [hK] at hpq
    have h3 : p ∣ 2 := by
      have h5 := Nat.dvd_sub hq2 hq1
      rwa [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by
        have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega] at h5
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  have hcuts : CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.borelCuts K Y' = {1, 2} := by
    ext i
    constructor
    · rintro ⟨k, rfl, -⟩
      rcases CFSG.QuasithinUnique.Vol2Native.A312L.fin_two_cases k with rfl | rfl <;> simp
    · intro hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with rfl | rfl
      · exact ⟨0, rfl, key 0⟩
      · exact ⟨1, rfl, key 1⟩
  have hY'B : Y' ≤ CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.borelSubgroup 2 K := by
    have h1 :=
      ((CFSG.QuasithinUnique.Setup.X7a.symplectic_unitriangular_overgroup_subflag_containment
        (r := 2) (K := K)).1 Y' hUY').1
    rwa [hcuts, ← CFSG.QuasithinUnique.Setup.X7a.borelSubgroup_eq_flagStabilizer] at h1
  intro y hy
  rw [← hg, CFSG.Quasithin.Vol2.KGNat.mem_normalizer_conjSubgroup,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.normalizer_unipotent]
  exact hY'B ((hmemY' _).mpr (by rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]))

theorem isSp4_le_normalizer {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n)
    (hX : IsSp4 X n) (U : Sylow 2 X) (Y : Subgroup X)
    (hUY : (U : Subgroup X) ≤ Y)
    (hYdvd : Nat.card Y ∣ Nat.card U * (2 ^ n - 1) ^ 2) :
    Y ≤ Subgroup.normalizer ((U : Subgroup X) : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ :=
    (show StatedClassicalModel X .PSp 2 2 n from
      CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
  have hchar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  let e' : X ≃* StatedSp 2 K :=
    e.trans (CFSG.Quasithin.H13.Ch9.KGFF.projEquiv (K := K)).symm
  let U' : Sylow 2 (StatedSp 2 K) :=
    Sylow.mapSurjective (p := 2) (f := e'.toMonoidHom) e'.surjective U
  let Y' : Subgroup (StatedSp 2 K) := Y.map e'.toMonoidHom
  have hU'coe : (U' : Subgroup (StatedSp 2 K)) = (U : Subgroup X).map e'.toMonoidHom :=
    Sylow.coe_mapSurjective (p := 2) (f := e'.toMonoidHom) e'.surjective U
  have hU'Y' : (U' : Subgroup (StatedSp 2 K)) ≤ Y' := by
    rw [hU'coe]
    exact Subgroup.map_mono hUY
  have hY'card : Nat.card Y' = Nat.card Y :=
    Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective
  have hU'card : Nat.card U' = Nat.card U := by
    rw [hU'coe]
    exact Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective
  have hYdvd' : Nat.card Y' ∣ Nat.card U' * (Nat.card K - 1) ^ 2 := by
    rw [hY'card, hU'card, hKcard]
    exact hYdvd
  have hres : Y' ≤ Subgroup.normalizer ((U' : Subgroup (StatedSp 2 K)) :
      Set (StatedSp 2 K)) := statedSp_le_normalizer hn hKcard U' Y' hU'Y' hYdvd'
  have hYcomap : Y ≤ (Subgroup.normalizer ((U' : Subgroup (StatedSp 2 K)) :
      Set (StatedSp 2 K))).comap e'.toMonoidHom := by
    intro y hy
    exact hres (Subgroup.mem_map_of_mem (f := e'.toMonoidHom) hy)
  rw [Subgroup.comap_normalizer_eq_of_surjective (U' : Subgroup (StatedSp 2 K)) e'.surjective,
    hU'coe, Subgroup.comap_map_eq_self_of_injective e'.injective (U : Subgroup X)] at hYcomap
  exact hYcomap

theorem odd_two_pow_sq_add_one {n : ℕ} (hn : 1 ≤ n) : Odd ((2 ^ n) ^ 2 + 1) := by
  have hq : Even (2 ^ n) := (Nat.even_pow).mpr ⟨by norm_num, by omega⟩
  exact ((Nat.even_pow).mpr ⟨hq, by norm_num⟩).add_one

theorem coprime_two_pow_add_one_sub_one_sq {n : ℕ} (hn : 1 ≤ n) :
    Nat.Coprime (2 ^ n + 1) ((2 ^ n - 1) ^ 2) :=
  (uc22pwsu3_coprime_two_pow hn).symm.pow_right 2

theorem coprime_two_pow_sq_add_one_sub_one_sq {n : ℕ} (hn : 1 ≤ n) :
    Nat.Coprime ((2 ^ n) ^ 2 + 1) ((2 ^ n - 1) ^ 2) := by
  have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hqeven : Even (2 ^ n) := (Nat.even_pow).mpr ⟨by norm_num, by omega⟩
  have hodd : Odd ((2 ^ n) ^ 2 + 1) := odd_two_pow_sq_add_one hn
  have hcop : Nat.Coprime ((2 ^ n) ^ 2 + 1) (2 ^ n - 1) := by
    have hdvd : Nat.gcd ((2 ^ n) ^ 2 + 1) (2 ^ n - 1) ∣ 2 := by
      have h1 : Nat.gcd ((2 ^ n) ^ 2 + 1) (2 ^ n - 1) ∣ (2 ^ n) ^ 2 + 1 :=
        Nat.gcd_dvd_left _ _
      have h2 : Nat.gcd ((2 ^ n) ^ 2 + 1) (2 ^ n - 1) ∣ (2 ^ n) ^ 2 - 1 := by
        rw [CFSG.Quasithin.Ch1Four.sq_sub_one_eq]
        exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
      have h3 := Nat.dvd_sub h1 h2
      rwa [show (2 ^ n) ^ 2 + 1 - ((2 ^ n) ^ 2 - 1) = 2 by
        have : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ hq
        omega] at h3
    have hoddg : Odd (Nat.gcd ((2 ^ n) ^ 2 + 1) (2 ^ n - 1)) :=
      Odd.of_dvd_nat hodd (Nat.gcd_dvd_left _ _)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hoddg
      exact absurd hoddg (by decide)
  exact hcop.pow_right 2

theorem one_lt_div_gcd_three {q : ℕ} (hq : 9 ≤ q + 1) :
    1 < (q + 1) / Nat.gcd 3 (q + 1) := by
  have hgle : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left (q + 1) (by norm_num)
  have h1 : (q + 1) / 3 ≤ (q + 1) / Nat.gcd 3 (q + 1) :=
    Nat.div_le_div_left hgle (Nat.gcd_pos_of_pos_right 3 (by omega))
  have h2 : 3 ≤ (q + 1) / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : (0 : ℕ) < 3)]
    omega
  omega

theorem div_gcd_three_dvd {q : ℕ} (hq : 1 ≤ q) :
    (q + 1) / Nat.gcd 3 (q + 1) ∣
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) := by
  have hg : Nat.gcd 3 (q + 1) ∣ q + 1 := Nat.gcd_dvd_right 3 (q + 1)
  have hq3 : q + 1 ∣ q ^ 3 + 1 := by
    rw [CFSG.Quasithin.Ch1Four.cube_add_one_eq hq]
    exact dvd_mul_right (q + 1) (q ^ 2 - q + 1)
  have hgN : Nat.gcd 3 (q + 1) ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (hg.trans hq3) (q ^ 2 - 1)) (q ^ 3)
  rw [Nat.dvd_div_iff_mul_dvd hgN, Nat.mul_div_cancel' hg]
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hq3 (q ^ 2 - 1)) (q ^ 3)

theorem two_pow_add_one_dvd_card_of_isL2_psl_two {A : Type} [Group A] {n : ℕ} (h : IsL2 A n) :
    2 ^ n + 1 ∣ Nat.card A := by
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
      (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)),
    CFSG.Quasithin.Ch1Four.sq_sub_one_eq]
  exact dvd_mul_of_dvd_right (dvd_mul_right (2 ^ n + 1) (2 ^ n - 1)) (2 ^ n)

theorem card_of_isU3 {B : Type} [Group B] {n : ℕ} (h : IsU3 B n) :
    Nat.card B = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) /
      Nat.gcd 3 (2 ^ n + 1) := by
  have hmodel : StatedClassicalModel B .PSU 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  have h1 : Nat.card B = ordTwistedA 2 (2 ^ n) := by
    simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.1 rfl
  rw [h1, CFSG.Quasithin.H13.ordTwistedA_two_eq (2 ^ n) (Nat.one_le_two_pow)]

theorem card_of_isSz_two_pow {A : Type} [Group A] {n : ℕ} (h : IsSz A n) :
    Nat.card A = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) := by
  obtain ⟨-, a, ha, K, hKf, hKfin, hf, hKcard, ⟨e⟩⟩ :=
    (CFSG.Blueprint.LieModel.suzukiModel h).2
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hKcard, hf]
  have hcard : Nat.card A = Nat.card (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) := by
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup
        (a := a) hK').toEquiv]
  rw [hcard, CFSG.Quasithin.opq4d_card_suzukiMatrixGroup (m := a) (by omega), ← hf]
  ring

theorem prodShape_le_normalizer {X A B : Type} [Group X] [Finite X]
    [Group A] [Group B] [Finite A] [Finite B]
    [IsSimpleGroup A] [IsSimpleGroup B]
    (e : X ≃* A × B) (U : Sylow 2 X) (Y : Subgroup X)
    (hUY : (U : Subgroup X) ≤ Y)
    (hbA : fusionIsBenderGroup A) (hbB : fusionIsBenderGroup B)
    {D dA dB : ℕ} (hYdvd : Nat.card Y ∣ Nat.card U * D)
    (hdA : dA ∣ Nat.card A) (hdA1 : 1 < dA) (hoddA : Odd dA) (hcopDA : Nat.Coprime dA D)
    (hdB : dB ∣ Nat.card B) (hdB1 : 1 < dB) (hoddB : Odd dB) (hcopDB : Nat.Coprime dB D) :
    Y ≤ Subgroup.normalizer ((U : Subgroup X) : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U' : Sylow 2 (A × B) :=
    Sylow.mapSurjective (p := 2) (f := e.toMonoidHom) e.surjective U
  let Y' : Subgroup (A × B) := Y.map e.toMonoidHom
  have hU'coe : (U' : Subgroup (A × B)) = (U : Subgroup X).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (p := 2) (f := e.toMonoidHom) e.surjective U
  have hU'Y' : (U' : Subgroup (A × B)) ≤ Y' := by
    rw [hU'coe]
    exact Subgroup.map_mono hUY
  have hY'card : Nat.card Y' = Nat.card Y :=
    Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
  have hU'card : Nat.card U' = Nat.card U := by
    rw [hU'coe]
    exact Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
  have hYdvd' : Nat.card Y' ∣ Nat.card U' * D := by
    rw [hY'card, hU'card]
    exact hYdvd
  let UA : Sylow 2 A :=
    Sylow.mapSurjective (p := 2) (f := MonoidHom.fst A B) Prod.fst_surjective U'
  let UB : Sylow 2 B :=
    Sylow.mapSurjective (p := 2) (f := MonoidHom.snd A B) Prod.snd_surjective U'
  have hUAcoe : (UA : Subgroup A) = (U' : Subgroup (A × B)).map (MonoidHom.fst A B) :=
    Sylow.coe_mapSurjective (p := 2) (f := MonoidHom.fst A B) Prod.fst_surjective U'
  have hUBcoe : (UB : Subgroup B) = (U' : Subgroup (A × B)).map (MonoidHom.snd A B) :=
    Sylow.coe_mapSurjective (p := 2) (f := MonoidHom.snd A B) Prod.snd_surjective U'
  have hUle : (U' : Subgroup (A × B)) ≤ (UA : Subgroup A).prod (UB : Subgroup B) := by
    intro u hu
    rw [Subgroup.mem_prod, hUAcoe, hUBcoe]
    exact ⟨Subgroup.mem_map.mpr ⟨u, hu, rfl⟩, Subgroup.mem_map.mpr ⟨u, hu, rfl⟩⟩
  have hprod2 : IsPGroup 2 ((UA : Subgroup A).prod (UB : Subgroup B)) :=
    (IsPGroup.prod UA.isPGroup' UB.isPGroup').of_equiv (Subgroup.prodEquiv _ _).symm
  have hUeq : ((UA : Subgroup A).prod (UB : Subgroup B)) = (U' : Subgroup (A × B)) :=
    U'.is_maximal' hprod2 hUle
  have hU0Y : ((UA : Subgroup A).prod (UB : Subgroup B)) ≤ Y' := by
    rw [hUeq]
    exact hU'Y'
  have hYdvd0 : Nat.card Y' ∣
      Nat.card ((UA : Subgroup A).prod (UB : Subgroup B)) * D := by
    rw [hUeq]
    exact hYdvd'
  have hres := prod_le_normalizer_of_bender hbA hbB UA UB Y' hU0Y hYdvd0
    hdA hdA1 hoddA hcopDA hdB hdB1 hoddB hcopDB
  have hY'le : Y' ≤ Subgroup.normalizer ((U' : Subgroup (A × B)) : Set (A × B)) := by
    rw [← hUeq]
    exact hres
  have hYcomap : Y ≤ (Subgroup.normalizer ((U' : Subgroup (A × B)) :
      Set (A × B))).comap e.toMonoidHom := by
    intro y hy
    exact hY'le (Subgroup.mem_map_of_mem (f := e.toMonoidHom) hy)
  rw [Subgroup.comap_normalizer_eq_of_surjective (U' : Subgroup (A × B)) e.surjective,
    hU'coe, Subgroup.comap_map_eq_self_of_injective e.injective (U : Subgroup X)] at hYcomap
  exact hYcomap

theorem isL2Square_le_normalizer {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n)
    (hX : IsL2Square X n) (U : Sylow 2 X) (Y : Subgroup X)
    (hUY : (U : Subgroup X) ≤ Y)
    (hYdvd : Nat.card Y ∣ Nat.card U * (2 ^ n - 1) ^ 2) :
    Y ≤ Subgroup.normalizer ((U : Subgroup X) : Set X) := by
  classical
  obtain ⟨A, B, hAg, hBg, ⟨e⟩, hA, hB⟩ := hX
  have : Finite (A × B) := Finite.of_equiv X e.toEquiv
  have : Finite A := Finite.of_injective (fun a : A => ((a, 1) : A × B))
    (by intro a b h; simpa using h)
  have : Finite B := Finite.of_injective (fun b : B => ((1, b) : A × B))
    (by intro a b h; simpa using h)
  have : IsSimpleGroup A :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA
  have : IsSimpleGroup B :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB
  exact prodShape_le_normalizer e U Y hUY
    (CFSG.LargeExtraspecial.S8.fusionIsBenderGroup_of_lieModel_psl_two hA)
    (CFSG.LargeExtraspecial.S8.fusionIsBenderGroup_of_lieModel_psl_two hB)
    hYdvd (two_pow_add_one_dvd_card_of_isL2_psl_two hA)
    (by have : 1 ≤ 2 ^ n := Nat.one_le_two_pow; omega)
    (odd_two_pow_add_one (by omega)) (coprime_two_pow_add_one_sub_one_sq (by omega))
    (two_pow_add_one_dvd_card_of_isL2_psl_two hB)
    (by have : 1 ≤ 2 ^ n := Nat.one_le_two_pow; omega)
    (odd_two_pow_add_one (by omega)) (coprime_two_pow_add_one_sub_one_sq (by omega))

theorem isL2U3_le_normalizer {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n)
    (hX : S17.IsL2U3Product X n) (U : Sylow 2 X) (Y : Subgroup X)
    (hUY : (U : Subgroup X) ≤ Y)
    (hYdvd : Nat.card Y ∣ Nat.card U * (2 ^ n - 1) ^ 2) :
    Y ≤ Subgroup.normalizer ((U : Subgroup X) : Set X) := by
  classical
  obtain ⟨A, B, hAg, hBg, ⟨e⟩, hA, hB⟩ := hX
  have : Finite (A × B) := Finite.of_equiv X e.toEquiv
  have : Finite A := Finite.of_injective (fun a : A => ((a, 1) : A × B))
    (by intro a b h; simpa using h)
  have : Finite B := Finite.of_injective (fun b : B => ((1, b) : A × B))
    (by intro a b h; simpa using h)
  have : IsSimpleGroup A :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA
  have : IsSimpleGroup B :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB
  have hdA : 2 ^ n + 1 ∣ Nat.card A := two_pow_add_one_dvd_card_of_isL2_psl_two hA
  have hdB : (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) ∣ Nat.card B := by
    rw [card_of_isU3 hB]
    exact div_gcd_three_dvd (q := 2 ^ n) Nat.one_le_two_pow
  have hg : Nat.gcd 3 (2 ^ n + 1) ∣ 2 ^ n + 1 := Nat.gcd_dvd_right 3 (2 ^ n + 1)
  exact prodShape_le_normalizer e U Y hUY
    (CFSG.LargeExtraspecial.S8.fusionIsBenderGroup_of_lieModel_psl_two hA)
    (CFSG.LargeExtraspecial.S8.fusionIsBenderGroup_of_lieModel_psu_three hB)
    hYdvd hdA (by have : 1 ≤ 2 ^ n := Nat.one_le_two_pow; omega)
    (odd_two_pow_add_one (by omega)) (coprime_two_pow_add_one_sub_one_sq (by omega))
    hdB (one_lt_div_gcd_three (q := 2 ^ n) (by
      have h8 : 8 ≤ 2 ^ n := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega))
    (Odd.of_dvd_nat (odd_two_pow_add_one (by omega)) (Nat.div_dvd_of_dvd hg))
    ((Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd hg)
      (uc22pwsu3_coprime_two_pow (n := n) (by omega)).symm).pow_right 2)

theorem isSzSquare_le_normalizer {X : Type} [Group X] [Finite X]
    {n : ℕ} (hn : 3 ≤ n) (hX : IsSzSquare X n) (U : Sylow 2 X) (Y : Subgroup X)
    (hUY : (U : Subgroup X) ≤ Y)
    (hYdvd : Nat.card Y ∣ Nat.card U * (2 ^ n - 1) ^ 2) :
    Y ≤ Subgroup.normalizer ((U : Subgroup X) : Set X) := by
  classical
  obtain ⟨A, B, hAg, hBg, ⟨e⟩, hA, hB⟩ := hX
  have : Finite (A × B) := Finite.of_equiv X e.toEquiv
  have : Finite A := Finite.of_injective (fun a : A => ((a, 1) : A × B))
    (by intro a b h; simpa using h)
  have : Finite B := Finite.of_injective (fun b : B => ((1, b) : A × B))
    (by intro a b h; simpa using h)
  have : IsSimpleGroup A :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hA
  have : IsSimpleGroup B :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hB
  have hdA : (2 ^ n) ^ 2 + 1 ∣ Nat.card A := by
    rw [card_of_isSz_two_pow hA]
    exact dvd_mul_left _ _
  have hdB : (2 ^ n) ^ 2 + 1 ∣ Nat.card B := by
    rw [card_of_isSz_two_pow hB]
    exact dvd_mul_left _ _
  exact prodShape_le_normalizer e U Y hUY
    (CFSG.LargeExtraspecial.S8.fusionIsBenderGroup_of_lieModel_twistedB2 hA)
    (CFSG.LargeExtraspecial.S8.fusionIsBenderGroup_of_lieModel_twistedB2 hB)
    hYdvd hdA (by
      have : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ Nat.one_le_two_pow
      omega)
    (odd_two_pow_sq_add_one (by omega)) (coprime_two_pow_sq_add_one_sub_one_sq (by omega))
    hdB (by
      have : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ Nat.one_le_two_pow
      omega)
    (odd_two_pow_sq_add_one (by omega)) (coprime_two_pow_sq_add_one_sub_one_sq (by omega))

theorem k_BorelOvergroup_holds : K_BorelOvergroup := by
  intro X _ _ n hn hshape U Y hUY hYdvd
  rcases hshape with h | h | h | h
  · exact isSp4_le_normalizer hn h U Y hUY hYdvd
  · exact isL2Square_le_normalizer hn h U Y hUY hYdvd
  · exact isL2U3_le_normalizer hn h U Y hUY hYdvd
  · exact isSzSquare_le_normalizer hn h U Y hUY hYdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
