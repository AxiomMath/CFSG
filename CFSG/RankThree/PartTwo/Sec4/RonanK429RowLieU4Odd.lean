module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieU4
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieU4OddDiag
import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4Inner
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofE27

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFU (diagU diagU_one torusSU mem_torusSU_iff permGL permGL_conj_diagU
  permGL_mem_unitarySU exists_diag_iso_le_of_iso)
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSU)

section Inner


theorem u4OddInner429 : U4OddInner429 := by
  intro n hn S _ _ hS σ hin hσ3 hσ1 K hKfix hKperf _hsub htype
  obtain ⟨eS⟩ := hS
  haveI := hKperf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := hn.pos
  obtain ⟨x, rfl⟩ := hin
  have hZ : Subgroup.center S = ⊥ :=
    center_eq_bot_of_mulEquiv eS (Sec4.RonanK432.center_projSU_four_two_eq_bot hn1)
  have hx3 : x ^ 3 = 1 := by
    have h1 : MulAut.conj (x ^ 3) = 1 := by rw [map_pow]; exact hσ3
    have hc : x ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := congrArg (fun φ : MulAut S => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * x ^ 3 = x ^ 3 * g * (x ^ 3)⁻¹ * x ^ 3 := by rw [h2]
        _ = x ^ 3 * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hσ1 (map_one _)
  have hxK : ∀ k ∈ K, x * k = k * x := by
    intro k hk
    have h1 : MulAut.conj x k = k := Sec4.mem_autFix.mp (hKfix hk)
    rw [MulAut.conj_apply] at h1
    calc x * k = x * k * x⁻¹ * x := by group
      _ = k * x := by rw [h1]
  have hxKc : ∀ k ∈ K, Commute x k := hxK
  obtain ⟨E, hEK, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_type429 htype
  have hNCP : NoCommNormalPair3 K := by
    haveI : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
    obtain ⟨k₀, hk₀E, hk₀1, hk₀3⟩ := exists_ne_one_pow_three hE3 hE9
    haveI : Nontrivial (K ⧸ CFSG.pCore 2 K) := by
      refine ⟨⟨QuotientGroup.mk (⟨k₀, hEK hk₀E⟩ : K), 1, fun h => ?_⟩⟩
      rw [QuotientGroup.eq_one_iff] at h
      exact hk₀1 (congrArg Subtype.val (eq_one_of_isPGroup_two_of_pow_three CFSG.pCore_isPGroup h
        (Subtype.ext (by simpa using hk₀3))))
    exact noCommNormalPair3_of_simple (isSimpleGroup_of_isType429 htype)
  have hxE : ∀ a ∈ E, ∀ i : ℤ, a * x ^ i = x ^ i * a := fun a ha i =>
    ((hxKc a (hEK ha)).zpow_left i).symm.eq
  have hxi3 : ∀ i : ℤ, (x ^ i) ^ 3 = 1 := by
    intro i
    calc (x ^ i) ^ 3 = (x ^ i) ^ ((3 : ℕ) : ℤ) := (zpow_natCast _ 3).symm
      _ = x ^ (i * 3) := (_root_.zpow_mul x i 3).symm
      _ = x ^ (3 * i) := congrArg (x ^ ·) (mul_comm i 3)
      _ = (x ^ (3 : ℤ)) ^ i := _root_.zpow_mul x 3 i
      _ = 1 := by
        rw [show x ^ (3 : ℤ) = 1 from (zpow_natCast x 3).trans hx3, _root_.one_zpow]
  have hcomm : ∀ (a : E) (b : Subgroup.zpowers x),
      Commute (E.subtype a) ((Subgroup.zpowers x).subtype b) := by
    rintro ⟨a, ha⟩ ⟨_, i, rfl⟩
    exact ((hxKc a (hEK ha)).zpow_left i).symm
  set F : Subgroup S := (E.subtype.noncommCoprod (Subgroup.zpowers x).subtype hcomm).range
    with hF
  have hFmem : ∀ y ∈ F, ∃ a ∈ E, ∃ i : ℤ, a * x ^ i = y := by
    rintro y ⟨⟨⟨a, ha⟩, ⟨_, i, rfl⟩⟩, rfl⟩
    exact ⟨a, ha, i, rfl⟩
  have hEF : E ≤ F := fun a ha => ⟨(⟨a, ha⟩, 1), by simp⟩
  have hxF : x ∈ F := ⟨(1, ⟨x, Subgroup.mem_zpowers x⟩), by simp⟩
  have hFexp : ∀ y ∈ F, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨a, ha, i, rfl⟩ := hFmem y hy
    rw [((hxKc a (hEK ha)).zpow_left i).symm.mul_pow, hE3 a ha, hxi3 i, one_mul]
  have hFcomm : ∀ y ∈ F, ∀ z ∈ F, y * z = z * y := by
    intro y hy z hz
    obtain ⟨a, ha, i, rfl⟩ := hFmem y hy
    obtain ⟨b, hb, j, rfl⟩ := hFmem z hz
    have h1 : x ^ i * b = b * x ^ i := (hxE b hb i).symm
    have h2 : x ^ j * a = a * x ^ j := (hxE a ha j).symm
    have h3 : a * b = b * a := hEc a ha b hb
    have h4 : x ^ i * x ^ j = x ^ j * x ^ i := (Commute.zpow_zpow_self x i j).eq
    calc a * x ^ i * (b * x ^ j) = a * (x ^ i * b) * x ^ j := by group
      _ = a * b * (x ^ i * x ^ j) := by rw [h1]; group
      _ = b * a * (x ^ j * x ^ i) := by rw [h3, h4]
      _ = b * (x ^ j * a) * x ^ i := by rw [h2]; group
      _ = b * x ^ j * (a * x ^ i) := by group
  set Lf := GaloisField 2 (2 * n) with hLf
  have hU : UnitaryFieldData 2 n Lf := ⟨Nat.prime_two, hn1, GaloisField.card 2 (2 * n) (by omega)⟩
  have := hU.finite
  have h3 : 3 ∣ 2 ^ n + 1 := Res417Six.three_dvd_two_pow_add_one hn
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU Nat.prime_three h3
    ((Res417Six.unitarySUEquivProjSU hn1).trans eS.symm) F hFexp hFcomm
  have hFT : ∀ y ∈ F, ((ψ.symm y : unitarySU 2 n Lf 4) : GL (Fin 4) Lf) ∈ torusSU 3 4 Lf :=
    fun y hy => hψ _ (by rw [MulEquiv.apply_symm_apply]; exact hy)
  obtain ⟨v, hv3, hvp, hvx⟩ := mem_torusSU_iff.mp (hFT x hxF)
  have hv1 : v ≠ 1 := by
    rintro rfl
    apply hx1
    have h1 : ψ.symm x = 1 := Subtype.ext (by rw [← hvx, diagU_one]; rfl)
    rw [← ψ.apply_symm_apply x, h1, map_one]
  have hdvd : 3 ∣ Nat.card Lf - 1 := by
    rw [hU.card]
    have h4 := Res419Two.three_dvd_two_pow_sq_sub_one n
    rwa [← pow_mul, mul_comm] at h4
  obtain ⟨ζ, hζ⟩ := Res417Six.exists_primitiveRoot_three hdvd
  obtain ⟨π, ω, hω3, hω1, hnf⟩ := Item419Res3.exists_perm_normal_form hζ hv3 hvp hv1
  have hω2 : ω ≠ ω⁻¹ := by
    intro hh
    apply hω1
    have h2' : ω ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [hh]; exact mul_inv_cancel ω
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
      _ = 1 := by rw [hω3, h2', inv_one, one_mul]
  set P : GL (Fin 4) Lf := permGL π with hP
  have hPU : P ∈ unitarySU 2 n Lf 4 := permGL_mem_unitarySU hU π
  set ρ : S →* GL (Fin 4) Lf := (MulAut.conj P).toMonoidHom.comp
    ((unitarySU 2 n Lf 4).subtype.comp ψ.symm.toMonoidHom) with hρ
  have hρapp : ∀ y, ρ y = P * ((ψ.symm y : unitarySU 2 n Lf 4) : GL (Fin 4) Lf) * P⁻¹ :=
    fun y => rfl
  have hρinj : Function.Injective ρ := by
    intro y z h
    rw [hρapp, hρapp] at h
    exact ψ.symm.injective (Subtype.ext (mul_left_cancel (mul_right_cancel h)))
  have hρU : ∀ y, ρ y ∈ unitarySU 2 n Lf 4 := fun y =>
    mul_mem (mul_mem hPU (ψ.symm y).2) (inv_mem hPU)
  have hρx : ρ x = diagU (v ∘ π.symm) := by
    rw [hρapp, ← hvx]
    exact permGL_conj_diagU π v
  have hρT : ∀ y ∈ F, ρ y ∈ torusSU 3 4 Lf := by
    intro y hy
    obtain ⟨d, hd3, hdp, hdy⟩ := mem_torusSU_iff.mp (hFT y hy)
    refine mem_torusSU_iff.mpr ⟨d ∘ π.symm, fun i => hd3 _, ?_, ?_⟩
    · rw [← hdp]
      exact Equiv.prod_comp π.symm d
    · rw [hρapp, ← hdy]
      exact (permGL_conj_diagU π d).symm
  set K₂ : Subgroup (GL (Fin 4) Lf) := K.map ρ with hK₂
  set E₂ : Subgroup (GL (Fin 4) Lf) := E.map ρ with hE₂
  have hK₂U : K₂ ≤ unitarySU 2 n Lf 4 := by
    rintro _ ⟨k, -, rfl⟩
    exact hρU k
  have hK₂C : K₂ ≤ Subgroup.centralizer {ρ x} := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxK k hk]
  have hK₂p : ⁅K₂, K₂⁆ = K₂ := by
    rw [hK₂, ← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  have hE₂K : E₂ ≤ K₂ := Subgroup.map_mono hEK
  have hE₂9 : Nat.card E₂ = 9 := by rw [hE₂, Subgroup.card_map_of_injective hρinj, hE9]
  have hE₂T : E₂ ≤ torusSU 3 4 Lf := by
    rintro _ ⟨e, he, rfl⟩
    exact hρT e (hEF he)
  have hE₂Z : ∀ z ∈ E₂, (∀ k ∈ K₂, z * k = k * z) → z = 1 := by
    rintro _ ⟨e, he, rfl⟩ hc
    have : e = 1 := hEZ e he (fun k hk => hρinj (by
      rw [map_mul, map_mul]
      exact hc _ ⟨k, hk, rfl⟩))
    rw [this, map_one]
  have hNCP₂ : NoCommNormalPair3 K₂ :=
    noCommNormalPair3_of_mulEquiv (K.equivMapOfInjective ρ hρinj) hNCP
  rw [hρx] at hK₂C
  rcases hnf with hA | hB | hC
  · rw [hA] at hK₂C
    exact falseA hω3 hω1 hK₂C hK₂p hE₂K hE₂9 hE₂T hE₂Z
  · rw [hB] at hK₂C
    exact falseB hω1 hω2 hK₂C hK₂p hE₂K hE₂9 hE₂T
  · rw [hC] at hK₂C
    exact falseC hU hω2 (le_inf hK₂U hK₂C) hK₂p hE₂K hE₂9 hE₂T hNCP₂

end Inner

section Row


theorem seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowSOf429 (projSU 4 2 n) :=
  seven_SU4_of u4OddInner429

end Row

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
