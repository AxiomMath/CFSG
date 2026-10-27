module

public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HDefs
public import CFSG.RankThree.PartTwo.Sec12.Hering129LSL3
public import CFSG.RankThree.PartTwo.Sec12.Item122
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129D4H

open CFSG CFSG.RankThree.PartTwo.Sec19
open CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof (sl2Three)
open CFSG.LieType.Chevalley (fixSubfield)

theorem sl2Three_eq_commutator (k : Type) [Field k] [CharP k 2] :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) k, sl2Three k = a * b * a⁻¹ * b⁻¹ := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hn : (-1 : k) = 1 := CharTwo.neg_eq 1
  let a : Matrix.SpecialLinearGroup (Fin 2) k := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let b : Matrix.SpecialLinearGroup (Fin 2) k :=
    ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, hn]⟩
  refine ⟨a, b, ?_⟩
  have key : a * b = sl2Three k * b * a := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    change (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) k) * !![0, 1; 1, 0] =
      (!![0, 1; -1, -1] * !![0, 1; 1, 0]) * !![1, 1; 0, 1]
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hn] <;>
      first | linear_combination (0 : k) * h2 | linear_combination (-1 : k) * h2 |
        linear_combination (1 : k) * h2
  exact ((mul_inv_eq_iff_eq_mul.2 (mul_inv_eq_iff_eq_mul.2 key))).symm

theorem sl2Three_ne_one (k : Type) [Field k] : sl2Three k ≠ 1 := by
  intro h
  have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) k =>
    (M : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp [sl2Three] at this

section Std

variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X} (P : D4Par n X σ)

theorem zStd_mem : zStd P ∈ Asub σ := (asubEquiv P _).2

theorem tStd_mem : tStd P ∈ Bsub σ := (bsubEquiv P _).2

theorem zStd_pow_three : zStd P ^ 3 = 1 := by
  rw [zStd, ← Subgroup.coe_pow, ← map_pow,
    CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.sl2Three_pow_three, map_one, Subgroup.coe_one]

theorem tStd_pow_three : tStd P ^ 3 = 1 := by
  rw [tStd, ← Subgroup.coe_pow, ← map_pow,
    CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.sl2Three_pow_three, map_one, Subgroup.coe_one]

theorem zStd_ne_one : zStd P ≠ 1 := by
  intro h
  have h1 : (asubEquiv P (sl2Three X) : Asub σ) = 1 :=
    Subtype.ext (h.trans (Subgroup.coe_one _).symm)
  exact sl2Three_ne_one X ((asubEquiv P).injective (by rw [h1, map_one]))

theorem tStd_ne_one : tStd P ≠ 1 := by
  intro h
  have h1 : (bsubEquiv P (sl2Three (fixSubfield σ)) : Bsub σ) = 1 :=
    Subtype.ext (h.trans (Subgroup.coe_one _).symm)
  exact sl2Three_ne_one (fixSubfield σ) ((bsubEquiv P).injective (by rw [h1, map_one]))

theorem tStd_not_mem_zpowers : tStd P ∉ Subgroup.zpowers (zStd P) := by
  intro h
  have hA : tStd P ∈ Asub σ := (Subgroup.zpowers_le.2 (zStd_mem P)) h
  have : tStd P ∈ Asub σ ⊓ Bsub σ := ⟨hA, tStd_mem P⟩
  rw [Asub_inf_Bsub P, Subgroup.mem_bot] at this
  exact tStd_ne_one P this

theorem tStd_mem_commutator :
    tStd P ∈ ⁅Subgroup.centralizer ({zStd P} : Set (C0 σ)),
      Subgroup.centralizer ({zStd P} : Set (C0 σ))⁆ := by
  haveI := P.charP
  haveI : CharP ↥(fixSubfield σ) 2 := inferInstance
  obtain ⟨a, b, hab⟩ := sl2Three_eq_commutator (fixSubfield σ)
  have hcent : ∀ u : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ),
      ((bsubEquiv P u : Bsub σ) : C0 σ) ∈ Subgroup.centralizer ({zStd P} : Set (C0 σ)) := by
    intro u
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Asub_Bsub_commute (zStd_mem P) (bsubEquiv P u).2).symm
  have h := Subgroup.commutator_mem_commutator (hcent a) (hcent b)
  convert h using 1
  rw [tStd, hab]
  simp [commutatorElement_def]

theorem exists_conj_std_of_R {c y : C0 σ} {R : Subgroup (C0 σ)}
    (hR : Sec4.IsSLThreePiAt ↥R (2 ^ n)) (hcR : c ∈ R) (hRc : ∀ r ∈ R, r * c = c * r)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hyR : y ∈ R) (hy3 : y ^ 3 = 1)
    (hyc : y ∉ Subgroup.zpowers c) {γ₀ : C0 σ} (hγ₀ : γ₀ * c * γ₀⁻¹ = zStd P)
    (htR : γ₀⁻¹ * tStd P * γ₀ ∈ R) :
    ∃ γ : C0 σ, γ * c * γ⁻¹ = zStd P ∧ γ * y * γ⁻¹ = tStd P := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set c' : ↥R := ⟨c, hcR⟩ with hc'
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hc'1 : c' ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hcen : c' ∈ Subgroup.center ↥R :=
    Subgroup.mem_center_iff.2 fun r => Subtype.ext (hRc r r.2)
  have hZcard : Nat.card (Subgroup.center ↥R) = 3 :=
    card_center_eq_three_of_isSLThreePi ⟨_, hR⟩
  have hord : orderOf c' = 3 := orderOf_eq_prime hc'3 hc'1
  have hZ : Subgroup.zpowers c' = Subgroup.center ↥R :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hcen)
      (by rw [Nat.card_zpowers, hord, hZcard])
  set ŷ : C0 σ := γ₀⁻¹ * tStd P * γ₀ with hŷ
  have hŷ3 : ŷ ^ 3 = 1 := by
    have : ŷ = γ₀⁻¹ * tStd P * γ₀⁻¹⁻¹ := by rw [inv_inv]
    rw [this, conj_pow, tStd_pow_three]
    group
  have hy' : (⟨y, hyR⟩ : ↥R) ∉ Subgroup.center ↥R := by
    intro h
    rw [← hZ] at h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    apply hyc
    exact ⟨k, by simpa [hc'] using congrArg Subtype.val hk⟩
  have hŷ' : (⟨ŷ, htR⟩ : ↥R) ∉ Subgroup.center ↥R := by
    intro h
    rw [← hZ] at h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    have hk' : c ^ k = ŷ := by simpa [hc'] using congrArg Subtype.val hk
    apply tStd_not_mem_zpowers P
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have : tStd P = γ₀ * ŷ * γ₀⁻¹ := by rw [hŷ]; group
    rw [← hγ₀, conj_zpow, hk', this]
  let r : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, P.one_le⟩
  have hR' : Sec4.IsSLThreePiAt ↥R r.card := by
    rw [TauCeti.PrimePower.card_def]
    exact hR
  obtain ⟨g, hg⟩ := Hering129L.exists_conj_of_isSLThreePiAt (r := r) hR'
    (a := ⟨y, hyR⟩) (b := ⟨ŷ, htR⟩) (Subtype.ext (by simpa using hy3))
    (Subtype.ext (by simpa using hŷ3)) hy' hŷ'
  have hg' : (g : C0 σ) * y * (g : C0 σ)⁻¹ = ŷ := congrArg Subtype.val hg
  refine ⟨γ₀ * (g : C0 σ), ?_, ?_⟩
  · have hgc := hRc g g.2
    calc γ₀ * (g : C0 σ) * c * (γ₀ * (g : C0 σ))⁻¹
        = γ₀ * ((g : C0 σ) * c * (g : C0 σ)⁻¹) * γ₀⁻¹ := by group
      _ = zStd P := by rw [hgc, mul_inv_cancel_right, hγ₀]
  · calc γ₀ * (g : C0 σ) * y * (γ₀ * (g : C0 σ))⁻¹
        = γ₀ * ((g : C0 σ) * y * (g : C0 σ)⁻¹) * γ₀⁻¹ := by group
      _ = tStd P := by rw [hg', hŷ]; group

end Std

end Hering129D4H

end CFSG.RankThree.PartTwo.Sec12
