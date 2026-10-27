module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4Inner
import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofE27
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
import CFSG.RankThree.PartOne.KF.R9Perm
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Card
import CFSG.RankThree.PartOne.TCX.Plane

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement
open CFSG.RankThree.PartOne.KFU (diagU diagU_val torusSU torusVec mem_torusSU_iff permGL
  permGL_conj_diagU permGL_mem_unitarySU exists_diag_iso_le_of_iso)
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Item419Res3
open CFSG.RankThree.PartTwo.Sec21.U4OddLines (dvecD0 phiD0 ker_phiD0 blkSU2 blkGL2 blk2
  nonempty_blkSU2_mulEquiv blkSU2_le_centralizer coe_blkGL2)
open CFSG.RankThree.PartTwo.Sec21.Item2130Res4Proof (blk3SU blk3SUEquiv commutator_mem_blk3SU
  blk3SU_le_uS blk3SU_le_centralizer mem_blk3SU_diagonal statedSU_eq_uS)
open CFSG.Assembly.RankThreeEven (projSU)

theorem two_pow_mod_five {n : ℕ} (hn : Odd n) : 2 ^ n % 5 = 2 ∨ 2 ^ n % 5 = 3 := by
  obtain ⟨m, rfl⟩ := hn
  have h4 : ∀ m : ℕ, 4 ^ m % 5 = 1 ∨ 4 ^ m % 5 = 4 := by
    intro m
    induction m with
    | zero => left; norm_num
    | succ m ih =>
      rw [pow_succ]
      rcases ih with h | h <;> omega
  have : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [this]
  rcases h4 m with h | h <;> omega

theorem not_five_dvd_orders {n : ℕ} (hn : Odd n) :
    ¬ 5 ∣ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) ∧
      ¬ 5 ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hq := two_pow_mod_five hn
  generalize 2 ^ n = q at hq ⊢
  have hq2 : q ^ 2 % 5 = 4 := by
    rcases hq with h | h <;> simp [Nat.pow_mod, h]
  have hq3 : q ^ 3 % 5 = 3 ∨ q ^ 3 % 5 = 2 := by
    rcases hq with h | h <;> simp [Nat.pow_mod, h]
  have hqpos : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h5q : ¬ 5 ∣ q := by omega
  have h5q3 : ¬ 5 ∣ q ^ 3 := fun h => h5q ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h))
  have h5a : ¬ 5 ∣ q ^ 2 - 1 := by omega
  have h5b : ¬ 5 ∣ q ^ 3 + 1 := by omega
  have hp : Nat.Prime 5 := by norm_num
  constructor
  · intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h <;> contradiction
    · contradiction
  · intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact h5q h
    · contradiction

section Types

variable {K : Type} [Field K] {f : ℕ}

theorem not_five_dvd_typeA (h : UnitaryFieldData 2 f K) (hf : Odd f) {ω : Kˣ} (hω1 : ω ≠ 1)
    {J : Subgroup (GL (Fin 4) K)}
    (hJC : J ≤ unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU ![ω, ω, ω, 1]})
    (hJ : Group.IsPerfect J) : ¬ 5 ∣ Nat.card J := by
  have := h.finite
  set D : GL (Fin 4) K := diagU ![ω, ω, ω, 1] with hDdef
  have hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal ![(ω : K), ω, ω, 1] := by
    rw [hDdef, diagU_val]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hω1' : (ω : K) ≠ 1 := fun h1 => hω1 (Units.ext h1)
  have hS : unitarySU 2 f K 4 = CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof.uS h 4 :=
    statedSU_eq_uS h 4
  set C := unitarySU 2 f K 4 ⊓ Subgroup.centralizer {D} with hC
  have hCe : C = CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof.uS h 4 ⊓
      Subgroup.centralizer {D} := by rw [hC, hS]
  have hcomm : ⁅C, C⁆ ≤ blk3SU h := by
    rw [Subgroup.commutator_le]
    intro g hg k hk
    rw [hCe] at hg hk
    exact commutator_mem_blk3SU h hω1' hD hg hk
  have hperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ
  have hJN : J ≤ blk3SU h := hperf ▸ (Subgroup.commutator_mono hJC hJC).trans hcomm
  have hU3 : CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof.uS h 3 = unitarySU 2 f K 3 :=
    (statedSU_eq_uS h 3).symm
  have hcard : Nat.card (blk3SU h) = Nat.card (unitarySU 2 f K 3) :=
    Nat.card_congr ((blk3SUEquiv h).trans (MulEquiv.subgroupCongr hU3)).toEquiv
  intro h5
  rw [CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_unitarySU_three h] at hcard
  exact (not_five_dvd_orders hf).1 (hcard ▸ h5.trans (Subgroup.card_dvd_of_le hJN))

theorem not_five_dvd_typeB (h : UnitaryFieldData 2 f K) (hf : Odd f) {ω : Kˣ} (h1 : ω ≠ 1)
    (h2 : ω ≠ ω⁻¹) {J : Subgroup (GL (Fin 4) K)}
    (hJC : J ≤ unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)})
    (hJ : Group.IsPerfect J) : ¬ 5 ∣ Nat.card J := by
  have := h.finite
  set C := unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)} with hC
  have hcomm : ⁅C, C⁆ ≤ blkSU2 f K := by
    rw [Subgroup.commutator_le]
    intro g hg k hk
    have hmem : (⟨g, hg⟩ * ⟨k, hk⟩ * ⟨g, hg⟩⁻¹ * ⟨k, hk⟩⁻¹ : C) ∈ (phiD0 h h1 h2).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm
        (phiD0 h h1 h2 ⟨g, hg⟩) (phiD0 h h1 h2 ⟨k, hk⟩)]
      group
    rw [ker_phiD0 h h1 h2, Subgroup.mem_subgroupOf] at hmem
    rw [commutatorElement_def]
    exact hmem
  have hperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ
  have hJN : J ≤ blkSU2 f K := hperf ▸ (Subgroup.commutator_mono hJC hJC).trans hcomm
  obtain ⟨φ⟩ := nonempty_blkSU2_mulEquiv h
  have hcard : Nat.card (blkSU2 f K) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr φ.toEquiv, CFSG.RankThree.PartOne.TCX.card_SL2', h.card_fixedField]
  intro h5
  exact (not_five_dvd_orders hf).2 (hcard ▸ h5.trans (Subgroup.card_dvd_of_le hJN))

theorem blkGL2_commute_blkGL2L (X Y : GL (Fin 2) K) :
    blkGL2 X * blkGL2L Y = blkGL2L Y * blkGL2 X := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_blkGL2, coe_blkGL2L]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2, blk2L, Matrix.mul_apply, Fin.sum_univ_four]

theorem not_five_dvd_typeC (h : UnitaryFieldData 2 f K) (hf : Odd f) {ω : Kˣ} (hω : ω ≠ ω⁻¹)
    {J : Subgroup (GL (Fin 4) K)} (hJC : J ≤ centC f K ω) (hJ : Group.IsPerfect J) :
    ¬ 5 ∣ Nat.card J := by
  have := h.finite
  have hperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ
  have hJN : J ≤ blkSU2 f K ⊔ blkSU2L f K :=
    hperf ▸ (Subgroup.commutator_mono hJC hJC).trans (commutator_centC_le h hω)
  obtain ⟨φ₁⟩ := nonempty_blkSU2_mulEquiv h
  obtain ⟨φ₂⟩ := nonempty_blkSU2L_mulEquiv h
  have hcard₁ : Nat.card (blkSU2 f K) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr φ₁.toEquiv, CFSG.RankThree.PartOne.TCX.card_SL2', h.card_fixedField]
  have hcard₂ : Nat.card (blkSU2L f K) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr φ₂.toEquiv, CFSG.RankThree.PartOne.TCX.card_SL2', h.card_fixedField]
  have hcomm : ∀ (a : blkSU2 f K) (b : blkSU2L f K),
      Commute ((blkSU2 f K).subtype a) ((blkSU2L f K).subtype b) := by
    rintro ⟨_, X, -, rfl⟩ ⟨_, Y, -, rfl⟩
    exact blkGL2_commute_blkGL2L X Y
  set Φ := MonoidHom.noncommCoprod (blkSU2 f K).subtype (blkSU2L f K).subtype hcomm with hΦ
  have hrange : Φ.range = blkSU2 f K ⊔ blkSU2L f K := by
    rw [hΦ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hdvd : Nat.card (blkSU2 f K ⊔ blkSU2L f K : Subgroup (GL (Fin 4) K)) ∣
      2 ^ f * ((2 ^ f) ^ 2 - 1) * (2 ^ f * ((2 ^ f) ^ 2 - 1)) := by
    rw [← hrange]
    refine (Subgroup.card_range_dvd Φ).trans ?_
    rw [Nat.card_prod, hcard₁, hcard₂]
  intro h5
  have h5' := h5.trans ((Subgroup.card_dvd_of_le hJN).trans hdvd)
  have hp : Nat.Prime 5 := by norm_num
  rcases (Nat.Prime.dvd_mul hp).mp h5' with h5'' | h5'' <;> exact (not_five_dvd_orders hf).2 h5''

theorem not_five_dvd_of_diag (h : UnitaryFieldData 2 f K) (hf : Odd f) (h3 : 3 ∣ 2 ^ f + 1)
    {v : Fin 4 → Kˣ} (hv3 : ∀ i, v i ^ 3 = 1) (hvp : ∏ i, v i = 1) (hv1 : v ≠ 1)
    {J : Subgroup (GL (Fin 4) K)}
    (hJC : J ≤ unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU v}) (hJ : Group.IsPerfect J) :
    ¬ 5 ∣ Nat.card J := by
  have := h.finite
  have hdvd : 3 ∣ Nat.card K - 1 := by
    rw [h.card]
    have h4 := Res419Two.three_dvd_two_pow_sq_sub_one f
    rwa [← pow_mul, mul_comm] at h4
  obtain ⟨ζ, hζ⟩ := Res417Six.exists_primitiveRoot_three hdvd
  obtain ⟨σ, ω, hω3, hω1, hnf⟩ := exists_perm_normal_form hζ hv3 hvp hv1
  set P : GL (Fin 4) K := permGL σ with hP
  have hPU : P ∈ unitarySU 2 f K 4 := permGL_mem_unitarySU h σ
  set ι : GL (Fin 4) K →* GL (Fin 4) K := (MulAut.conj P).toMonoidHom with hι
  have hιinj : Function.Injective ι := (MulAut.conj P).injective
  have hmapS : (unitarySU 2 f K 4).map ι = unitarySU 2 f K 4 := by
    ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact mul_mem (mul_mem hPU hg') (inv_mem hPU)
    · intro hg
      refine ⟨P⁻¹ * g * P, mul_mem (mul_mem (inv_mem hPU) hg) hPU, ?_⟩
      change P * (P⁻¹ * g * P) * P⁻¹ = g
      group
  have hmapC : (Subgroup.centralizer ({diagU v} : Set (GL (Fin 4) K))).map ι =
      Subgroup.centralizer {diagU (v ∘ σ.symm)} := by
    rw [hι, map_centralizer_singleton]
    congr 2
    change P * diagU v * P⁻¹ = diagU (v ∘ σ.symm)
    exact permGL_conj_diagU σ v
  set C := unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU v} with hC
  have hmap : C.map ι = unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (v ∘ σ.symm)} := by
    rw [hC, Subgroup.map_inf_eq _ _ ι hιinj, hmapS, hmapC]
  have hJC' : J.map ι ≤ unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (v ∘ σ.symm)} :=
    hmap ▸ Subgroup.map_mono hJC
  set eJ : J ≃* J.map ι := J.equivMapOfInjective ι hιinj
  have hJ' : Group.IsPerfect (J.map ι) :=
    Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  rw [Nat.card_congr eJ.toEquiv]
  have hω2 : ω ≠ ω⁻¹ := by
    intro hh
    apply hω1
    have h2' : ω ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [hh]; exact mul_inv_cancel ω
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
      _ = 1 := by rw [hω3, h2', inv_one, one_mul]
  rcases hnf with hA | hB | hC'
  · rw [hA] at hJC'
    exact not_five_dvd_typeA h hf hω1 hJC' hJ'
  · rw [hB] at hJC'
    exact not_five_dvd_typeB h hf hω1 hω2 hJC' hJ'
  · rw [hC'] at hJC'
    exact not_five_dvd_typeC h hf hω2 hJC' hJ'

end Types

theorem not_five_dvd_of_perfect_le_centralizer {n : ℕ} (hn : Odd n) {x : projSU 4 2 n}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {P : Subgroup (projSU 4 2 n)} (hP : Group.IsPerfect P)
    (hPC : P ≤ Subgroup.centralizer ({x} : Set (projSU 4 2 n))) : ¬ 5 ∣ Nat.card P := by
  have hn1 : 1 ≤ n := hn.pos
  set K := GaloisField 2 (2 * n) with hKdef
  have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn1, GaloisField.card 2 (2 * n) (by omega)⟩
  have := hU.finite
  have h3 : 3 ∣ 2 ^ n + 1 := Res417Six.three_dvd_two_pow_add_one hn
  set ψ₀ := Res417Six.unitarySUEquivProjSU hn1
  have hFexp : ∀ y ∈ Subgroup.zpowers x, y ^ 3 = 1 := by
    rintro _ ⟨i, rfl⟩
    show (x ^ i) ^ 3 = 1
    calc (x ^ i) ^ 3 = (x ^ i) ^ ((3 : ℕ) : ℤ) := (zpow_natCast _ 3).symm
      _ = x ^ (i * 3) := (_root_.zpow_mul x i 3).symm
      _ = x ^ (3 * i) := congrArg (x ^ ·) (mul_comm i 3)
      _ = (x ^ (3 : ℤ)) ^ i := _root_.zpow_mul x 3 i
      _ = 1 := by
        rw [show x ^ (3 : ℤ) = 1 from (zpow_natCast x 3).trans hx3, _root_.one_zpow]
  have hFcomm : ∀ y ∈ Subgroup.zpowers x, ∀ z ∈ Subgroup.zpowers x, y * z = z * y := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.zpow_zpow_self x i j).eq
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU Nat.prime_three h3 ψ₀ (Subgroup.zpowers x)
    hFexp hFcomm
  set s := ψ.symm x with hs
  have hsT : (s : GL (Fin 4) K) ∈ torusSU 3 4 K :=
    hψ s (by rw [hs, MulEquiv.apply_symm_apply]; exact Subgroup.mem_zpowers x)
  obtain ⟨v, hv3, hvp, hvs⟩ := mem_torusSU_iff.mp hsT
  have hv1 : v ≠ 1 := by
    rintro rfl
    apply hx1
    have h1 : (s : GL (Fin 4) K) = 1 := by rw [← hvs]; exact CFSG.RankThree.PartOne.KFU.diagU_one
    have h2 : s = 1 := Subtype.ext h1
    rw [← ψ.apply_symm_apply x, ← hs, h2, map_one]
  set P₁ : Subgroup (unitarySU 2 n K 4) := P.map ψ.symm.toMonoidHom with hP₁
  set P₂ : Subgroup (GL (Fin 4) K) := P₁.map (unitarySU 2 n K 4).subtype with hP₂
  have hP₁C : P₁ ≤ Subgroup.centralizer ({s} : Set (unitarySU 2 n K 4)) := by
    have := Subgroup.map_mono (f := ψ.symm.toMonoidHom) hPC
    rwa [map_centralizer_singleton] at this
  have hP₂C : P₂ ≤ unitarySU 2 n K 4 ⊓ Subgroup.centralizer {diagU v} := by
    have h1 : P₂ ≤ (Subgroup.centralizer ({s} : Set (unitarySU 2 n K 4))).map
        (unitarySU 2 n K 4).subtype := Subgroup.map_mono hP₁C
    rw [map_subtype_centralizer_singleton, ← hvs] at h1
    exact h1
  set e₂ : P ≃* P₂ := (P.equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective).trans
    (P₁.equivMapOfInjective (unitarySU 2 n K 4).subtype (unitarySU 2 n K 4).subtype_injective)
  have hP₂perf : Group.IsPerfect P₂ :=
    Group.IsPerfect.ofSurjective (f := e₂.toMonoidHom) e₂.surjective
  rw [Nat.card_congr e₂.toEquiv]
  exact not_five_dvd_of_diag hU hn h3 hv3 hvp hv1 hP₂C hP₂perf

end CFSG.RankThree.PartTwo.Sec8.Hering611
