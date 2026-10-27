module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4Blocks
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofU4
import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofE27
import CFSG.RankThree.PartOne.KF.R9Perm
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofUniFix
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res4ProofU4Cent
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res4ProofU4Wt

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item419Res3

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement
open CFSG.RankThree.PartOne.KFU (diagU diagU_val torusSU torusVec mem_torusSU_iff permGL
  permGL_conj_diagU permGL_mem_unitarySU exists_diag_iso_le_of_iso)
open CFSG.RankThree.PartTwo.Sec21.U4OddLines (dvecD0)
open CFSG.RankThree.PartTwo.Sec21.Item2130Res4Proof (blk3SU blk3SUEquiv commutator_mem_blk3SU
  commutator_blk3SU blk3SU_le_uS blk3SU_le_centralizer mem_blk3SU_diagonal statedSU_eq_uS)
open CFSG.Assembly.RankThreeEven (projSU)

section Transport

variable {Y Y' : Type*} [Group Y] [Group Y']

theorem isComponent_subgroupOf_map (ι : Y →* Y') (hι : Function.Injective ι) {C K : Subgroup Y}
    (hK : IsComponent (K.subgroupOf C)) : IsComponent ((K.map ι).subgroupOf (C.map ι)) :=
  isComponent_subgroupOf_of_mulEquiv (C.equivMapOfInjective ι hι)
    (fun _ => (Subgroup.mem_map_iff_mem hι).symm) hK

theorem map_centralizer_singleton (e : Y ≃* Y') (x : Y) :
    (Subgroup.centralizer ({x} : Set Y)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set Y') := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hz]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy

theorem map_subtype_centralizer_singleton (S : Subgroup Y) (s : S) :
    (Subgroup.centralizer ({s} : Set S)).map S.subtype =
      S ⊓ Subgroup.centralizer ({(s : Y)} : Set Y) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, congrArg Subtype.val hz⟩
  · rintro ⟨hyS, hy⟩
    exact ⟨⟨y, hyS⟩, Subtype.ext hy, rfl⟩

end Transport

@[expose] def permList : List (Equiv.Perm (Fin 4)) :=
  [1, Equiv.swap 0 3, Equiv.swap 1 3, Equiv.swap 2 3, Equiv.swap 1 2, Equiv.swap 0 2,
    Equiv.swap 0 2 * Equiv.swap 1 3]

set_option maxRecDepth 10000 in
theorem nf_exp : ∀ e : Fin 4 → ZMod 3, e 0 + e 1 + e 2 + e 3 = 0 → e ≠ 0 →
    ∃ σ ∈ permList, ∃ c : ZMod 3, c ≠ 0 ∧
      (e ∘ σ.symm = ![c, c, c, 0] ∨ e ∘ σ.symm = ![0, 0, c, -c] ∨
        e ∘ σ.symm = ![c, c, -c, -c]) := by
  decide

variable {K : Type} [Field K]

theorem pow_val_neg {ζ : Kˣ} (hζ3 : ζ ^ 3 = 1) (c : ZMod 3) :
    ζ ^ (-c).val = (ζ ^ c.val)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_add]
  have h : (3 : ℕ) ∣ (-c).val + c.val := by
    fin_cases c <;> decide
  obtain ⟨k, hk⟩ := h
  rw [hk, pow_mul, hζ3, one_pow]

theorem exists_perm_normal_form {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) {v : Fin 4 → Kˣ}
    (hv3 : ∀ i, v i ^ 3 = 1) (hvp : ∏ i, v i = 1) (hv1 : v ≠ 1) :
    ∃ σ : Equiv.Perm (Fin 4), ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧
      (v ∘ σ.symm = ![ω, ω, ω, 1] ∨ v ∘ σ.symm = dvecD0 ω ∨ v ∘ σ.symm = dvecC ω) := by
  have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hk : ∀ i, ∃ k < 3, ζ ^ k = v i := fun i =>
    hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 3 (v i)).mpr (hv3 i))
  choose k hk3 hkv using hk
  set e : Fin 4 → ZMod 3 := fun i => (k i : ZMod 3) with he
  have hval : ∀ i, (e i).val = k i := fun i => ZMod.val_cast_of_lt (hk3 i)
  have hvi : ∀ i, v i = ζ ^ (e i).val := fun i => by rw [hval, hkv]
  have hsum : e 0 + e 1 + e 2 + e 3 = 0 := by
    have hp : ζ ^ (k 0 + k 1 + k 2 + k 3) = 1 := by
      rw [pow_add, pow_add, pow_add, hkv, hkv, hkv, hkv, ← hvp, Fin.prod_univ_four]
    have hd := (hζ.pow_eq_one_iff_dvd _).mp hp
    have : ((k 0 + k 1 + k 2 + k 3 : ℕ) : ZMod 3) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hd
    simpa [he] using this
  have he0 : e ≠ 0 := by
    intro h0
    apply hv1
    funext i
    rw [hvi i, show e i = 0 from congrFun h0 i, ZMod.val_zero, pow_zero, Pi.one_apply]
  obtain ⟨σ, -, c, hc, hpat⟩ := nf_exp e hsum he0
  have hcv : ∀ i, v (σ.symm i) = ζ ^ ((e ∘ σ.symm) i).val := fun i => hvi _
  set ω := ζ ^ c.val with hω
  have hω3 : ω ^ 3 = 1 := by rw [hω, ← pow_mul, mul_comm, pow_mul, hζ3, one_pow]
  have hω1 : ω ≠ 1 := by
    rw [hω]
    exact hζ.pow_ne_one_of_pos_of_lt (by rwa [Ne, ZMod.val_eq_zero]) (ZMod.val_lt c)
  have hneg : ζ ^ (-c).val = ω⁻¹ := pow_val_neg hζ3 c
  refine ⟨σ, ω, hω3, hω1, ?_⟩
  rcases hpat with h | h | h
  · left
    funext i
    rw [Function.comp_apply, hcv, h]
    fin_cases i <;> simp [hω]
  · right; left
    funext i
    rw [Function.comp_apply, hcv, h]
    fin_cases i <;> simp [dvecD0, hω, hneg]
  · right; right
    funext i
    rw [Function.comp_apply, hcv, h]
    fin_cases i <;> simp [dvecC, hω, hneg]

theorem component_of_typeA {f : ℕ} (h : UnitaryFieldData 2 f K) {ω : Kˣ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (h3 : 3 ∣ 2 ^ f + 1) {J : Subgroup (GL (Fin 4) K)}
    (hJC : J ≤ unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU ![ω, ω, ω, 1]})
    (hJ : IsComponent (J.subgroupOf
      (unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU ![ω, ω, ω, 1]}))) :
    Subgroup.center J ≠ ⊥ := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : GL (Fin 4) K := diagU ![ω, ω, ω, 1] with hDdef
  have hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal ![(ω : K), ω, ω, 1] := by
    rw [hDdef, diagU_val]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hω1' : (ω : K) ≠ 1 := fun h1 => hω1 (Units.ext h1)
  have hω3' : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hωbar : h.bar (ω : K) * ω = 1 := by
    exact CFSG.RankThree.PartOne.KCUnitaryPlane.bar_eq_inv_of_pow_eq_one h h3 hω3'
  have hS : unitarySU 2 f K 4 = CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof.uS h 4 :=
    statedSU_eq_uS h 4
  set C := unitarySU 2 f K 4 ⊓ Subgroup.centralizer {D} with hC
  have hCe : C = CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof.uS h 4 ⊓
      Subgroup.centralizer {D} := by rw [hC, hS]
  have hNC : blk3SU h ≤ C := by
    rw [hCe]
    exact le_inf (blk3SU_le_uS h) (blk3SU_le_centralizer h hD)
  have hperf := commutator_eq_of_isComponent_subgroupOf hJ hJC
  have hcomm : ⁅C, C⁆ ≤ blk3SU h := by
    rw [Subgroup.commutator_le]
    intro g hg k hk
    rw [hCe] at hg hk
    exact commutator_mem_blk3SU h hω1' hD hg hk
  have hJN : J ≤ blk3SU h := hperf ▸ (Subgroup.commutator_mono hJC hJC).trans hcomm
  have hf := h.one_le
  have hU3 : CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof.uS h 3 = unitarySU 2 f K 3 :=
    (statedSU_eq_uS h 3).symm
  rcases (show f = 1 ∨ 2 ≤ f by omega) with hf1 | hf2
  · exfalso
    have hsol : Group.IsSolvable (unitarySU 2 f K 3) :=
      Item424Res3.isSolvable_unitarySU_two h (by rw [hf1]; norm_num)
    have hsol' : Group.IsSolvable (blk3SU h) := by
      have e := (blk3SUEquiv h).trans (MulEquiv.subgroupCongr hU3)
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact false_of_isComponent_subgroupOf_le hJ hNC hJN hsol'
  · have hcard : Nat.card K = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
    have hq : IsQuasisimple (unitarySU 2 f K 3) :=
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard le_rfl (by
        intro hh
        simp only [Prod.mk.injEq, true_and] at hh
        have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
        omega)).1
    have hq' : IsQuasisimple (blk3SU h) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((blk3SUEquiv h).trans (MulEquiv.subgroupCongr hU3)).symm hq
    have hJeq := eq_of_isComponent_subgroupOf_le hJ hJC hNC hJN hq'
    have hDJ : D ∈ J := hJeq ▸ mem_blk3SU_diagonal h hω3' hωbar hD
    have hDZ : (⟨D, hDJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.mp (hJC y.2).2
      exact this
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hDZ
    have hD1 : D = 1 := congrArg Subtype.val hDZ
    apply hω1
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 4) K =>
      (g : Matrix (Fin 4) (Fin 4) K)) hD1) 0) 0
    simp only [hD, Units.val_one, Matrix.one_apply_eq, Matrix.diagonal_apply_eq] at this
    exact Units.ext this

theorem component_of_diag {f : ℕ} (h : UnitaryFieldData 2 f K) (h3 : 3 ∣ 2 ^ f + 1)
    {v : Fin 4 → Kˣ} (hv3 : ∀ i, v i ^ 3 = 1) (hvp : ∏ i, v i = 1) (hv1 : v ≠ 1)
    {J : Subgroup (GL (Fin 4) K)}
    (hJC : J ≤ unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU v})
    (hJ : IsComponent (J.subgroupOf (unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU v}))) :
    Subgroup.center J ≠ ⊥ ∨ Nat.card J = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
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
  have hJ' := isComponent_subgroupOf_map ι hιinj hJ
  rw [hmap] at hJ'
  have hJC' : J.map ι ≤ unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (v ∘ σ.symm)} :=
    hmap ▸ Subgroup.map_mono hJC
  set eJ : J ≃* J.map ι := J.equivMapOfInjective ι hιinj
  rcases hnf with hA | hB | hC'
  · left
    rw [hA] at hJ' hJC'
    have hZ := component_of_typeA h hω3 hω1 h3 hJC' hJ'
    intro hbot
    apply hZ
    rw [← Subgroup.map_center_eq eJ, hbot, Subgroup.map_bot]
  · right
    rw [hB] at hJ' hJC'
    have h2 : ω ≠ ω⁻¹ := by
      intro hh
      apply hω1
      have h2' : ω ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [hh]; exact mul_inv_cancel ω
      calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
        _ = 1 := by rw [hω3, h2', inv_one, one_mul]
    rw [Nat.card_congr eJ.toEquiv]
    exact component_of_typeB h hω1 h2 hJC' hJ'
  · right
    rw [hC'] at hJ' hJC'
    have h2 : ω ≠ ω⁻¹ := by
      intro hh
      apply hω1
      have h2' : ω ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [hh]; exact mul_inv_cancel ω
      calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
        _ = 1 := by rw [hω3, h2', inv_one, one_mul]
    rw [Nat.card_congr eJ.toEquiv]
    exact component_of_typeC h h2 hJC' hJ'

theorem inner_case {n : ℕ} (hn : Odd n) {x : projSU 4 2 n} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {J : Subgroup (projSU 4 2 n)} (hJC : J ≤ Subgroup.centralizer ({x} : Set (projSU 4 2 n)))
    (hJ : IsComponent (J.subgroupOf (Subgroup.centralizer ({x} : Set (projSU 4 2 n))))) :
    Subgroup.center J ≠ ⊥ ∨ Nat.card J = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
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
  have hJ₁ := isComponent_subgroupOf_map ψ.symm.toMonoidHom ψ.symm.injective hJ
  rw [map_centralizer_singleton] at hJ₁
  have hJ₂ := isComponent_subgroupOf_map (unitarySU 2 n K 4).subtype
    (unitarySU 2 n K 4).subtype_injective hJ₁
  rw [map_subtype_centralizer_singleton, ← hs, ← hvs] at hJ₂
  set J₂ := (J.map ψ.symm.toMonoidHom).map (unitarySU 2 n K 4).subtype with hJ₂def
  have hJ₂C : J₂ ≤ unitarySU 2 n K 4 ⊓ Subgroup.centralizer {diagU v} := by
    rw [hvs, hs, ← map_subtype_centralizer_singleton, ← map_centralizer_singleton]
    exact Subgroup.map_mono (Subgroup.map_mono hJC)
  set e₂ : J ≃* J₂ := (J.equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective).trans
    ((J.map ψ.symm.toMonoidHom).equivMapOfInjective (unitarySU 2 n K 4).subtype
      (unitarySU 2 n K 4).subtype_injective)
  rcases component_of_diag hU h3 hv3 hvp hv1 hJ₂C hJ₂ with hZ | hc
  · left
    intro hbot
    apply hZ
    rw [← Subgroup.map_center_eq e₂, hbot, Subgroup.map_bot]
  · right
    rw [Nat.card_congr e₂.toEquiv]
    exact hc

end CFSG.RankThree.PartTwo.Sec4.Item419Res3
