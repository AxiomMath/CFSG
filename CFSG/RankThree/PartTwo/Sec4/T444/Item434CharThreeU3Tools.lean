module

public import CFSG.LocalAnalysis.SectionRank.OddCover.UnitaryThree
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434CharThree

open CFSG Matrix
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.ComponentClassification.OuterAutomorphisms (equivalence Outer)
open CFSG.Assembly.LowTwoRank (StatedSU StatedScalars StatedProj)

section Heis

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

noncomputable abbrev heisU : Subgroup (SU σ 3) :=
  heisenbergSubgroup σ hσ (i := (0 : Fin 3)) (k := 1) (by decide) (by decide) (by decide)

@[expose] def ent01 (g : SU σ 3) : F := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1

omit [Field F] in
theorem heisenbergMatrix_apply01 {F : Type} [Field F] (σ : F ≃+* F) (a b : F) :
    heisenbergMatrix σ (0 : Fin 3) 1 a b 0 1 = a := by
  rw [CFSG.LieType.Steinberg.heisenbergMatrix_three]
  simp

omit [Field F] in
theorem heisenbergMatrix_apply02 {F : Type} [Field F] (σ : F ≃+* F) (a b : F) :
    heisenbergMatrix σ (0 : Fin 3) 1 a b 0 2 = b := by
  rw [CFSG.LieType.Steinberg.heisenbergMatrix_three]
  simp

variable {hσ}

theorem ent01_mul {g g' : SU σ 3} (hg : g ∈ heisU hσ) (hg' : g' ∈ heisU hσ) :
    ent01 (g * g') = ent01 g + ent01 g' := by
  obtain ⟨a, b, -, hm⟩ := hg
  obtain ⟨a', b', -, hm'⟩ := hg'
  rw [ent01, ent01, ent01, Subgroup.coe_mul, Units.val_mul, hm, hm',
    heisenbergMatrix_mul σ (by decide) (by decide) (by decide), heisenbergMatrix_apply01,
    heisenbergMatrix_apply01, heisenbergMatrix_apply01]

theorem ent01_inv {g : SU σ 3} (hg : g ∈ heisU hσ) : ent01 g⁻¹ = -ent01 g := by
  have h := ent01_mul hg ((heisU hσ).inv_mem hg)
  rw [mul_inv_cancel] at h
  have h1 : ent01 (1 : SU σ 3) = 0 := by simp [ent01]
  rw [h1] at h
  linear_combination -h

theorem commute_iff_of_mem_heisU {g g' : SU σ 3} (hg : g ∈ heisU hσ) (hg' : g' ∈ heisU hσ) :
    g * g' = g' * g ↔ ent01 g * σ (ent01 g') = ent01 g' * σ (ent01 g) := by
  obtain ⟨a, b, hab, hm⟩ := hg
  obtain ⟨a', b', hab', hm'⟩ := hg'
  have hga : ent01 g = a := by rw [ent01, hm, heisenbergMatrix_apply01]
  have hga' : ent01 g' = a' := by rw [ent01, hm', heisenbergMatrix_apply01]
  rw [hga, hga']
  have hprod : ∀ x y : SU σ 3, x * y = y * x ↔
      ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((y : GL (Fin 3) F) : Matrix _ _ F) =
        ((y : GL (Fin 3) F) : Matrix _ _ F) * ((x : GL (Fin 3) F) : Matrix _ _ F) := by
    intro x y
    constructor
    · intro h
      have := congrArg (fun z : SU σ 3 => ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
      simpa using this
    · intro h
      exact Subtype.ext (Units.ext (by simpa using h))
  rw [hprod, hm, hm', heisenbergMatrix_mul σ (by decide) (by decide) (by decide),
    heisenbergMatrix_mul σ (by decide) (by decide) (by decide)]
  constructor
  · intro h
    have h2 := congrFun (congrFun h 0) 2
    rw [heisenbergMatrix_apply02, heisenbergMatrix_apply02] at h2
    linear_combination -h2
  · intro h
    have e1 : a + a' = a' + a := add_comm _ _
    have e2 : b + b' - a * σ a' = b' + b - a' * σ a := by linear_combination -h
    rw [e1, e2]

theorem pow_three_eq_one_of_mem_heisU [CharP F 3] {g : SU σ 3} (hg : g ∈ heisU hσ) :
    g ^ 3 = 1 := by
  obtain ⟨a, b, -, hm⟩ := hg
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  apply Subtype.ext
  apply Units.ext
  rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, hm,
    CFSG.SectionRank.OddCover.heis_pow]
  have e3 : ((3 : ℕ) : F) = 0 := by exact_mod_cast h3
  have hc : ((Nat.choose 3 2 : ℕ) : F) = 0 := by
    rw [show Nat.choose 3 2 = 3 by decide]
    exact e3
  rw [e3, hc, zero_mul, zero_mul, zero_mul, sub_zero, heisenbergMatrix_zero]
  rfl

variable (hσ) in
@[expose] noncomputable def lineU (a₀ : F) : Subgroup (SU σ 3) where
  carrier := {g | g ∈ heisU hσ ∧ ∃ s : F, σ s = s ∧ ent01 g = s * a₀}
  mul_mem' := by
    rintro g g' ⟨hg, s, hs, hgs⟩ ⟨hg', t, ht, hgt⟩
    refine ⟨(heisU hσ).mul_mem hg hg', s + t, by rw [map_add, hs, ht], ?_⟩
    rw [ent01_mul hg hg', hgs, hgt]
    ring
  one_mem' := ⟨(heisU hσ).one_mem, 0, map_zero σ, by simp [ent01]⟩
  inv_mem' := by
    rintro g ⟨hg, s, hs, hgs⟩
    refine ⟨(heisU hσ).inv_mem hg, -s, by rw [map_neg, hs], ?_⟩
    rw [ent01_inv hg, hgs]
    ring

theorem lineU_le_heisU (a₀ : F) : lineU hσ a₀ ≤ heisU hσ := fun _ hg => hg.1

theorem lineU_commute {a₀ : F} {g g' : SU σ 3} (hg : g ∈ lineU hσ a₀) (hg' : g' ∈ lineU hσ a₀) :
    g * g' = g' * g := by
  obtain ⟨hgU, s, hs, hgs⟩ := hg
  obtain ⟨hgU', t, ht, hgt⟩ := hg'
  rw [commute_iff_of_mem_heisU hgU hgU', hgs, hgt, map_mul, map_mul, hs, ht]
  ring

theorem isElemAbelian_lineU [CharP F 3] (a₀ : F) :
    CFSG.Assembly.IsElemAbelian 3 (lineU hσ a₀) :=
  ⟨⟨⟨fun x y => Subtype.ext (lineU_commute x.2 y.2)⟩⟩,
    fun _ hx => pow_three_eq_one_of_mem_heisU hx.1⟩

theorem exists_le_lineU {P : Subgroup (SU σ 3)} (hP : P ≤ heisU hσ)
    (hc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) : ∃ a₀ : F, a₀ ≠ 0 ∧ P ≤ lineU hσ a₀ := by
  by_cases hZ : ∀ x ∈ P, ent01 x = 0
  · exact ⟨1, one_ne_zero, fun x hx => ⟨hP hx, 0, map_zero σ, by rw [hZ x hx, zero_mul]⟩⟩
  push Not at hZ
  obtain ⟨x, hxP, hx0⟩ := hZ
  refine ⟨ent01 x, hx0, fun y hy => ⟨hP hy, ent01 y / ent01 x, ?_, ?_⟩⟩
  · have hcomm := (commute_iff_of_mem_heisU (hP hxP) (hP hy)).mp (hc x hxP y hy)
    have hσx : σ (ent01 x) ≠ 0 := (map_ne_zero σ).mpr hx0
    rw [map_div₀, div_eq_div_iff hσx hx0]
    linear_combination hcomm
  · exact (div_mul_cancel₀ _ hx0).symm

end Heis

section Finite

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

include hF

theorem card_heisU :
    Nat.card (heisU (unitaryInvolution_involutive hF)) = (p ^ f) ^ 3 := by
  rw [heisU, ← CFSG.LieType.Steinberg.rootGroup_three_eq_heisenbergSubgroup]
  exact CFSG.LieType.Steinberg.card_rootGroup_three hF

theorem card_lineU_ge {a₀ : F} (ha₀ : a₀ ≠ 0) :
    (p ^ f) ^ 2 ≤ Nat.card (lineU (unitaryInvolution_involutive hF) a₀) := by
  set σ := unitaryInvolution F p f with hσdef
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  have htr : ∀ a : F, ∃ c : F, c + σ c = -(σ a * a) := fun a =>
    exists_add_unitaryInvolution_eq hF (by rw [map_neg, map_mul, hσ, mul_comm])
  choose c hc using htr
  have hmem : ∀ (s : CFSG.LieType.Steinberg.fixedSubfield F p f)
      (z : traceZero σ), (c (s * a₀) + z) + σ (c (s * a₀) + z) + σ (s * a₀) * (s * a₀) = 0 := by
    intro s z
    have hz := (mem_traceZero σ).mp z.2
    rw [map_add]
    linear_combination hc (s * a₀) + hz
  let φ : CFSG.LieType.Steinberg.fixedSubfield F p f × traceZero σ →
      lineU (unitaryInvolution_involutive hF) a₀ := fun v =>
    ⟨CFSG.SectionRank.OddCover.heisSU hσ (v.1 * a₀) (c (v.1 * a₀) + v.2) (hmem v.1 v.2),
      ⟨⟨_, _, hmem v.1 v.2, rfl⟩, v.1, v.1.2, by
        rw [ent01, CFSG.SectionRank.OddCover.coe_heisSU, heisenbergMatrix_apply01]⟩⟩
  have hφ : Function.Injective φ := by
    rintro ⟨s, z⟩ ⟨s', z'⟩ h
    have h' := congrArg (fun g : lineU (unitaryInvolution_involutive hF) a₀ =>
      (((g : SU σ 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
    simp only [φ, CFSG.SectionRank.OddCover.coe_heisSU] at h'
    have h1 := congrFun (congrFun h' 0) 1
    have h2 := congrFun (congrFun h' 0) 2
    rw [heisenbergMatrix_apply01, heisenbergMatrix_apply01] at h1
    rw [heisenbergMatrix_apply02, heisenbergMatrix_apply02] at h2
    have hs : (s : F) = s' := mul_right_cancel₀ ha₀ h1
    have hs' : s = s' := Subtype.ext hs
    subst hs'
    have hz : (z : F) = z' := by linear_combination h2
    rw [Subtype.ext hz]
  have h := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_prod, CFSG.LieType.Steinberg.card_fixedSubfield hF,
    CFSG.LieType.Steinberg.card_traceZero hF, ← sq] at h

end Finite

section Galois

variable {e : ℕ}

theorem card_galois_two_mul (he : e ≠ 0) : Nat.card (GaloisField 3 (2 * e)) = (3 ^ e) ^ 2 := by
  rw [GaloisField.card 3 (2 * e) (by omega), ← pow_mul, mul_comm]

theorem factorization_card_SU_three (he : e ≠ 0) :
    (Nat.card (SU (unitaryInvolution (GaloisField 3 (2 * e)) 3 e) 3)).factorization 3 = 3 * e := by
  rw [CFSG.LieType.Steinberg.card_SU_three (card_galois_two_mul he)]
  set m := ((3 ^ e) ^ 2 - 1) * ((3 ^ e) ^ 3 + 1) with hm_def
  have hm : ¬ 3 ∣ m := by
    intro h3
    have h1 : 3 ∣ (3 ^ e) ^ 2 := dvd_pow (dvd_pow_self 3 he) two_ne_zero
    have h1' : 3 ∣ (3 ^ e) ^ 3 := dvd_pow (dvd_pow_self 3 he) (by norm_num)
    have h2 : 1 ≤ (3 ^ e) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h <;> omega
  rw [mul_assoc, show (3 ^ e) ^ 3 * m = 3 ^ (3 * e) * m by rw [← pow_mul, mul_comm e 3]]
  exact Item434AltPerm.factorization_three_pow_mul (3 * e) hm

theorem statedScalars_subgroupOf_statedSU_eq_bot {K : Type} [Field K] [CharP K 3] (q : ℕ) :
    (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 q K) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨x, hxSU⟩ hx
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hx
  obtain ⟨c, hc⟩ := hx
  have hc' : Matrix.GeneralLinearGroup.scalar (Fin 3) c = x := hc
  have hdet : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    det_eq_one_of_mem_statedSU hxSU
  rw [← hc'] at hdet
  have hc3 : (c : K) ^ 3 = 1 := by
    simpa [Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_three] using hdet
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have hc1 : (c : K) = 1 := by
    have h : ((c : K) - 1) ^ 3 = 0 := by linear_combination hc3 - ((c : K) ^ 2 - c) * h3
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  change x = 1
  rw [← hc', show c = 1 from Units.ext hc1, map_one]

@[expose] noncomputable def suEquivProjSU (he : e ≠ 0) :
    SU (unitaryInvolution (GaloisField 3 (2 * e)) 3 e) 3 ≃*
      CFSG.Assembly.RankThreeEven.projSU 3 3 e :=
  ((equivStatedSU (card_galois_two_mul he) 3).trans
    ((QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedSU_eq_bot (3 ^ e))).trans
      QuotientGroup.quotientBot).symm).trans (Sec4.projSUEquivStatedProj 3 3 e).symm

theorem card_outer_SU_three_dvd (he : 1 ≤ e) :
    Nat.card (Outer (SU (unitaryInvolution (GaloisField 3 (2 * e)) 3 e) 3)) ∣
      2 * e * (3 ^ e + 1) := by
  rw [Nat.card_congr (equivalence (suEquivProjSU (by omega : e ≠ 0))).toEquiv]
  refine Sec4.card_outer_projSU_dvd 3 3 e he le_rfl ?_
  rintro ⟨-, h2⟩
  have : 3 ^ 1 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
  omega

end Galois

end CFSG.RankThree.PartTwo.Sec4.Item434CharThree
