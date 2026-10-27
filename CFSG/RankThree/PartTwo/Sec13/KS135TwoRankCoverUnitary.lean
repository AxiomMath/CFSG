module

public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleTwoRank
public import CFSG.RankThree.PartTwo.Census.TransitiveLift
import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverRanks

public section

namespace CFSG.RankThree.PartTwo.Sec13.KS135Cover

open CFSG CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem three_le_pRank_of_commuting_lifts {J X : Type*} [Group J] [Finite J] [Group X]
    {φ : J →* X} (hφ : Function.Surjective φ) {W : Subgroup X}
    (hW2 : ∀ w ∈ W, w * w = 1) (hW8 : 8 ≤ Nat.card W)
    (hW : ∀ y y' : J, φ y ∈ W → φ y' ∈ W → y * y' = y' * y) : 3 ≤ CFSG.pRank 2 J := by
  classical
  set A := W.comap φ with hA
  let sqHom : A →* J :=
    { toFun := fun a => (a : J) * a
      map_one' := by simp
      map_mul' := fun a b => by
        have hab : (a : J) * b = b * a := hW a b a.2 b.2
        simp only [Subgroup.coe_mul]
        calc (a : J) * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hab]
          _ = a * a * (b * b) := by group }
  have hsq : ∀ a : A, sqHom a = (a : J) * a := fun a => rfl
  have hsq_ker : sqHom.range ≤ φ.ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker, hsq, map_mul]
    exact hW2 _ a.2
  set ψ : A →* X := φ.comp A.subtype with hψ
  have hψrange : ψ.range = W := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype, hA,
      Subgroup.map_comap_eq_self_of_surjective hφ]
  have hle : φ.ker ≤ A := fun k hk => by
    rw [hA, Subgroup.mem_comap, (MonoidHom.mem_ker).mp hk]
    exact W.one_mem
  have hψker : Nat.card ψ.ker = Nat.card φ.ker := by
    have e : ψ.ker = φ.ker.subgroupOf A := by
      ext a
      simp only [hψ, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
        Subgroup.mem_subgroupOf]
    rw [e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h1 := Subgroup.card_ker_mul_card_range ψ
  rw [hψker, hψrange] at h1
  have h2 := Subgroup.card_ker_mul_card_range sqHom
  have h3 : Nat.card sqHom.range ≤ Nat.card φ.ker := Subgroup.card_le_of_le hsq_ker
  have h4 : Nat.card W ≤ Nat.card sqHom.ker := by
    have hpos : 0 < Nat.card φ.ker := Nat.card_pos
    by_contra h
    push Not at h
    have h5 : Nat.card sqHom.ker * Nat.card sqHom.range < Nat.card W * Nat.card φ.ker :=
      calc Nat.card sqHom.ker * Nat.card sqHom.range ≤ Nat.card sqHom.ker * Nat.card φ.ker :=
            Nat.mul_le_mul_left _ h3
        _ < Nat.card W * Nat.card φ.ker := Nat.mul_lt_mul_of_pos_right h hpos
    rw [h2, ← h1, mul_comm] at h5
    exact lt_irrefl _ h5
  have h6 : Nat.card sqHom.ker ≤ Nat.card (Sec4.Census.TransitiveLift.involutionLift hW) := by
    refine Nat.card_le_card_of_injective
      (fun k => (⟨((k : A) : J), (k : A).2, ?_⟩ :
        Sec4.Census.TransitiveLift.involutionLift hW)) ?_
    · have hk := (MonoidHom.mem_ker).mp k.2
      rw [hsq] at hk
      rw [sq]
      exact hk
    · intro k k' h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
  exact Sec4.Census.TransitiveLift.le_pRank_of_card
    (Sec4.Census.TransitiveLift.isElementaryAbelian_involutionLift hW) (k := 3)
    (by norm_num; omega)

section Eichler

open Matrix
open CFSG.Assembly.RankThreeEven (projSU)

variable (f : ℕ)

@[expose] noncomputable def eichMat (a γ : GaloisField 2 (2 * f)) :
    Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f)) :=
  !![1 + γ, γ, a ^ 2 ^ f; γ, 1 + γ, a ^ 2 ^ f; a, a, 1]

theorem frob_add (x y : GaloisField 2 (2 * f)) :
    (x + y) ^ 2 ^ f = x ^ 2 ^ f + y ^ 2 ^ f := by
  rw [add_pow_char_pow]

theorem eichMat_mul (a γ b δ : GaloisField 2 (2 * f)) :
    eichMat f a γ * eichMat f b δ = eichMat f (a + b) (γ + δ + b * a ^ 2 ^ f) := by
  have h2 : (2 : GaloisField 2 (2 * f)) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eichMat, mul_apply, Fin.sum_univ_three, frob_add] <;> ring_nf <;> simp [h2]

theorem det_eichMat (a γ : GaloisField 2 (2 * f)) : (eichMat f a γ).det = 1 := by
  have h2 : (2 : GaloisField 2 (2 * f)) = 0 := CharTwo.two_eq_zero
  rw [det_fin_three]
  simp [eichMat]
  linear_combination (γ - a * a ^ 2 ^ f) * h2

theorem unitary_eichMat (hf : 1 ≤ f) {a γ : GaloisField 2 (2 * f)}
    (hγ : γ + γ ^ 2 ^ f = a * a ^ 2 ^ f) :
    ((eichMat f a γ).map (· ^ 2 ^ f))ᵀ * eichMat f a γ = 1 := by
  have h2 : (2 : GaloisField 2 (2 * f)) = 0 := CharTwo.two_eq_zero
  have haa : (a ^ 2 ^ f) ^ 2 ^ f = a := Sec4.Census.frobQ_frobQ hf a
  have h1γ : (1 + γ) ^ 2 ^ f = 1 + γ ^ 2 ^ f := by rw [frob_add, one_pow]
  have hmap : (eichMat f a γ).map (· ^ 2 ^ f) =
      !![1 + γ ^ 2 ^ f, γ ^ 2 ^ f, a; γ ^ 2 ^ f, 1 + γ ^ 2 ^ f, a; a ^ 2 ^ f, a ^ 2 ^ f, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [eichMat, haa, h1γ]
  rw [hmap]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eichMat, mul_apply, Fin.sum_univ_three] <;>
    first
    | linear_combination hγ + (γ * γ ^ 2 ^ f + a * a ^ 2 ^ f) * h2
    | linear_combination (a ^ 2 ^ f + γ ^ 2 ^ f * a ^ 2 ^ f) * h2
    | linear_combination (a + a * γ) * h2
    | linear_combination (a * a ^ 2 ^ f) * h2

theorem eichMat_zero (c : (traceQ2 f).ker) :
    eichMat f 0 c = 1 + radU3 f c := by
  have h0 : (0 : GaloisField 2 (2 * f)) ^ 2 ^ f = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eichMat, radU3, isoLineMat, h0]

@[expose] noncomputable def eichGL (a γ : GaloisField 2 (2 * f)) :
    GL (Fin 3) (GaloisField 2 (2 * f)) :=
  GeneralLinearGroup.mkOfDetNeZero (eichMat f a γ) (by rw [det_eichMat]; exact one_ne_zero)

theorem coe_eichGL (a γ : GaloisField 2 (2 * f)) :
    ((eichGL f a γ : GL (Fin 3) (GaloisField 2 (2 * f))) : Matrix (Fin 3) (Fin 3) _) =
      eichMat f a γ :=
  rfl

theorem eichGL_mul (a γ b δ : GaloisField 2 (2 * f)) :
    eichGL f a γ * eichGL f b δ = eichGL f (a + b) (γ + δ + b * a ^ 2 ^ f) :=
  Units.ext (by rw [Units.val_mul, coe_eichGL, coe_eichGL, coe_eichGL, eichMat_mul])

theorem eichGL_zero (c : (traceQ2 f).ker) :
    eichGL f 0 c = Sec4.Census.sqZeroUnit (radU3 f) (radU3_mul f) c :=
  Units.ext (by rw [coe_eichGL, eichMat_zero]; rfl)

theorem eichGL_comm_zero (a γ c : GaloisField 2 (2 * f)) :
    eichGL f a γ * eichGL f 0 c = eichGL f 0 c * eichGL f a γ := by
  have h0 : (0 : GaloisField 2 (2 * f)) ^ 2 ^ f = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  rw [eichGL_mul, eichGL_mul]
  congr 1
  · ring
  · rw [h0]
    ring

theorem commutatorElement_eichGL (a γ b δ : GaloisField 2 (2 * f)) :
    ⁅eichGL f a γ, eichGL f b δ⁆ = eichGL f 0 (b * a ^ 2 ^ f + a * b ^ 2 ^ f) := by
  have h2 : (2 : GaloisField 2 (2 * f)) = 0 := CharTwo.two_eq_zero
  set c := b * a ^ 2 ^ f + a * b ^ 2 ^ f with hc
  have key : eichGL f a γ * eichGL f b δ = eichGL f b δ * eichGL f a γ * eichGL f 0 c := by
    rw [eichGL_mul, eichGL_mul, eichGL_mul]
    congr 1
    · ring
    · rw [hc]
      linear_combination (-(a * b ^ 2 ^ f)) * h2
  rw [commutatorElement_def, key]
  have hT1 := eichGL_comm_zero f a γ c
  have hT2 := eichGL_comm_zero f b δ c
  calc eichGL f b δ * eichGL f a γ * eichGL f 0 c * (eichGL f a γ)⁻¹ * (eichGL f b δ)⁻¹ =
      eichGL f b δ * (eichGL f a γ * eichGL f 0 c) * (eichGL f a γ)⁻¹ * (eichGL f b δ)⁻¹ := by
        group
    _ = eichGL f b δ * (eichGL f 0 c * eichGL f a γ) * (eichGL f a γ)⁻¹ * (eichGL f b δ)⁻¹ := by
        rw [hT1]
    _ = (eichGL f b δ * eichGL f 0 c) * (eichGL f b δ)⁻¹ := by group
    _ = (eichGL f 0 c * eichGL f b δ) * (eichGL f b δ)⁻¹ := by rw [hT2]
    _ = eichGL f 0 c := by group

variable [Fact (Nat.Prime 2)]

theorem mk_eichGL_mem (hf : 1 ≤ f) {a γ : GaloisField 2 (2 * f)}
    (hγ : γ + γ ^ 2 ^ f = a * a ^ 2 ^ f) :
    ProjGenLinGroup.mk (eichGL f a γ) ∈ projSU 3 2 f := by
  refine ⟨eichGL f a γ, Subgroup.subset_closure ⟨?_, ?_⟩, rfl⟩
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Units.val_one, coe_eichGL, det_eichMat]
  · rw [coe_eichGL]
    exact unitary_eichMat f hf hγ

theorem mk_sqZeroUnit_mem (c : (traceQ2 f).ker) :
    ProjGenLinGroup.mk (Sec4.Census.sqZeroUnit (radU3 f) (radU3_mul f) c) ∈ projSU 3 2 f := by
  refine ⟨Sec4.Census.sqZeroUnit (radU3 f) (radU3_mul f) c, Subgroup.subset_closure ⟨?_, ?_⟩,
    rfl⟩
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Units.val_one]
    exact det_one_add_radU3 f c
  · exact unitary_one_add_radU3 f c

@[expose] noncomputable def tHom : Multiplicative (traceQ2 f).ker →* projSU 3 2 f :=
  (ProjGenLinGroup.mk.comp (Sec4.Census.sqZeroHom (radU3 f) (radU3_mul f))).codRestrict _
    fun c => mk_sqZeroUnit_mem f (Multiplicative.toAdd c)

theorem coe_tHom (c : Multiplicative (traceQ2 f).ker) :
    ((tHom f c : projSU 3 2 f) : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * f))) =
      ProjGenLinGroup.mk (Sec4.Census.sqZeroUnit (radU3 f) (radU3_mul f)
        (Multiplicative.toAdd c)) :=
  rfl

theorem tHom_injective : Function.Injective (tHom f) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have h1 := congrArg Subtype.val hc
  rw [coe_tHom, Subgroup.coe_one] at h1
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
  obtain ⟨u, hu⟩ := h1
  have h01 := congrArg (fun g : GL (Fin 3) (GaloisField 2 (2 * f)) =>
    (g : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f))) 0 1) hu
  simp [Sec4.Census.sqZeroUnit, radU3, isoLineMat] at h01
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  exact Subtype.ext h01.symm

end Eichler

section Cover

open Matrix
open CFSG.Assembly.RankThreeEven (projSU)

theorem three_le_pRank_of_projSU_cover {J : Type*} [Group J] [Finite J] {f : ℕ} (hf : 3 ≤ f)
    (h3 : 2 ^ f % 3 = 2) {φ : J →* projSU 3 2 f} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center J) : 3 ≤ CFSG.pRank 2 J := by
  classical
  have hf1 : 1 ≤ f := by omega
  set K := GaloisField 2 (2 * f) with hK
  have hKpi : Sec4.PiField false 2 f K := piField_galoisField_two 2 f hf1
  have hq3 : Sec4.ModThree false (2 ^ f) := h3
  obtain ⟨τ, hτ3, hτ1⟩ := Sec4.exists_tau hKpi hq3
  have hsum : 1 + τ + τ ^ 2 = 0 := Sec4.one_add_tau_add_sq hτ3 hτ1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hττ : τ + τ ^ 2 = 1 := by linear_combination hsum - h2
  have hτq : τ ^ 2 ^ f = τ ^ 2 := by
    have h := Sec4.pow_succ_eq_one_of_modThree hq3 hτ3
    calc τ ^ 2 ^ f = τ ^ 2 ^ f * τ ^ 3 := by rw [hτ3, mul_one]
      _ = τ ^ (2 ^ f + 1) * τ ^ 2 := by ring
      _ = τ ^ 2 := by rw [h, one_mul]
  have h1q : (1 : K) ^ 2 ^ f = 1 := one_pow _
  have hγ1 : τ + τ ^ 2 ^ f = 1 * 1 ^ 2 ^ f := by rw [hτq, h1q, mul_one, hττ]
  have hγ2 : ∀ c : K, c ^ 2 ^ f = c →
      c ^ 2 * τ + (c ^ 2 * τ) ^ 2 ^ f = c * τ * (c * τ) ^ 2 ^ f := by
    intro c hc
    rw [mul_pow, mul_pow, hτq, ← pow_mul, mul_comm 2 (2 ^ f), pow_mul, hc]
    linear_combination c ^ 2 * hττ - c ^ 2 * hτ3
  set W := (tHom f).range with hW
  have hW2 : ∀ w ∈ W, w * w = 1 := by
    rintro _ ⟨c, rfl⟩
    rw [← map_mul]
    have hcc : c * c = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      exact Subtype.ext (by
        rw [AddSubgroup.coe_add, AddSubgroup.coe_zero]
        exact CharTwo.add_self_eq_zero _)
    rw [hcc, map_one]
  have hW8 : 8 ≤ Nat.card W := by
    have hcard : Nat.card W = Nat.card (traceQ2 f).ker := by
      rw [hW, ← Nat.card_congr (MonoidHom.ofInjective (tHom_injective f)).toEquiv]
      exact Nat.card_congr Multiplicative.toAdd
    rw [hcard]
    have h := le_card_ker_traceQ2 f hf1
    have h8 : 8 ≤ 2 ^ f := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hcomm : ∀ y y' : J, φ y ∈ W → φ y' ∈ W → y * y' = y' * y := by
    intro y y' hy hy'
    obtain ⟨c₁, hc₁⟩ := hy
    obtain ⟨c₂, hc₂⟩ := hy'
    set c : K := ((Multiplicative.toAdd c₂ : (traceQ2 f).ker) : K) with hcdef
    have hc : c ^ 2 ^ f = c := (mem_ker_traceQ2 f).mp (Multiplicative.toAdd c₂).2
    set e₁ : projSU 3 2 f := ⟨_, mk_eichGL_mem f hf1 hγ1⟩ with he₁
    set e₂ : projSU 3 2 f := ⟨_, mk_eichGL_mem f hf1 (hγ2 c hc)⟩ with he₂
    obtain ⟨p, hp⟩ := hφ e₁
    obtain ⟨q, hq⟩ := hφ e₂
    have hcommE : ∀ (a γ : K) (h : ProjGenLinGroup.mk (eichGL f a γ) ∈ projSU 3 2 f),
        Commute (tHom f c₁) ⟨_, h⟩ := by
      intro a γ h
      apply Subtype.ext
      change ProjGenLinGroup.mk (Sec4.Census.sqZeroUnit (radU3 f) (radU3_mul f)
          (Multiplicative.toAdd c₁)) * ProjGenLinGroup.mk (eichGL f a γ) =
        ProjGenLinGroup.mk (eichGL f a γ) * ProjGenLinGroup.mk (Sec4.Census.sqZeroUnit
          (radU3 f) (radU3_mul f) (Multiplicative.toAdd c₁))
      rw [← eichGL_zero, ← map_mul, ← map_mul, eichGL_comm_zero]
    refine Sec4.Census.TransitiveLift.commute_of_map_eq_commutatorElement hker (p := p) (q := q)
      ?_ ?_ ?_
    · rw [← hc₁, hp]
      exact hcommE 1 τ _
    · rw [← hc₁, hq]
      exact hcommE _ _ _
    · rw [← hc₂, map_commutatorElement, hp, hq]
      apply Subtype.ext
      change ProjGenLinGroup.mk (Sec4.Census.sqZeroUnit (radU3 f) (radU3_mul f)
          (Multiplicative.toAdd c₂)) = ⁅ProjGenLinGroup.mk (eichGL f 1 τ),
        ProjGenLinGroup.mk (eichGL f (c * τ) (c ^ 2 * τ))⁆
      rw [← map_commutatorElement, commutatorElement_eichGL, ← eichGL_zero]
      congr 2
      rw [← hcdef, h1q, mul_one, one_mul, mul_pow, hτq, hc]
      linear_combination (-c) * hττ
  exact three_le_pRank_of_commuting_lifts hφ hW2 hW8 hcomm

end Cover

end CFSG.RankThree.PartTwo.Sec13.KS135Cover
