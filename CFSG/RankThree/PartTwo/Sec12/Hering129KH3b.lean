module

import CFSG.RankThree.PartTwo.Sec12.Hering129KH3
public import CFSG.RankThree.PartTwo.Sec12.Hering129KE1
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.DicksonNonLocal

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open CFSG.Open (StatedScalars)
open Matrix (ProjGenLinGroup)
open scoped Pointwise


namespace Hering129KH3b

variable {P : Type} [Group P] [Finite P] {Yh Bh : Subgroup P} {xh bh ch : P}
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem h3b_card_sup_le_nine {x y : P} (hx : ∀ g : P, x * g = g * x) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤ 9 := by
  have hN : (Subgroup.zpowers x).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : x ^ k * g = g * x ^ k := Commute.zpow_left (show Commute x g from hx g) k
    rw [← hc, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  have hset : ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup P) : Set P) =
      (Subgroup.zpowers x : Set P) * (Subgroup.zpowers y : Set P) :=
    Subgroup.normal_mul _ _
  have h1 : Nat.card (Subgroup.zpowers x) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx3)
  have h2 : Nat.card (Subgroup.zpowers y) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hy3)
  calc Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y)
      = Nat.card ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup P) : Set P) := rfl
    _ = Nat.card ((Subgroup.zpowers x : Set P) * (Subgroup.zpowers y : Set P)) := by
        rw [hset]
    _ ≤ Nat.card (Subgroup.zpowers x : Set P) * Nat.card (Subgroup.zpowers y : Set P) :=
        Set.natCard_mul_le
    _ ≤ 3 * 3 := Nat.mul_le_mul h1 h2
    _ = 9 := by norm_num

theorem h3b_not_isSolvable_projSL_two {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    ¬ Group.IsSolvable ↥(projSL 2 F) := by
  intro hs
  exact (CFSG.SignalizerFunctorTheorem.CatalogBridge.psl2_simple_not_isSolvable h4).2
    (Group.isSolvable_of_surjective (f := (Sec4.projSLEquivPSL F).toMonoidHom)
      (MulEquiv.surjective _))

theorem h3b_isSolvable_slPi_false (hK : Sec4.PiField false p f K) (h2 : p ^ f = 2) :
    Group.IsSolvable ↥(Sec4.slPi false 3 (p ^ f) K) := by
  have hcard : Nat.card K = (2 ^ 1) ^ 2 := by
    rw [hK.card]
    norm_num [Sec4.piCard, h2]
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_rfl, by rw [hcard]; norm_num⟩
  have hc : Nat.card (CFSG.Open.StatedSU 3 (2 ^ 1) K) = 216 :=
    CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
  have hfin : Finite ↥(CFSG.Open.StatedSU 3 (2 ^ 1) K) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have := Fintype.ofFinite ↥(CFSG.Open.StatedSU 3 (2 ^ 1) K)
  have hsolv : Group.IsSolvable ↥(CFSG.Open.StatedSU 3 (2 ^ 1) K) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hc]; norm_num)
  have heq : Sec4.slPi false 3 (p ^ f) K = CFSG.Open.StatedSU 3 (2 ^ 1) K := by
    show CFSG.Open.StatedSU 3 (p ^ f) K = _
    simp only [h2, pow_one]
  rw [heq]
  exact hsolv

theorem h3b_two_lt_of_not_isSolvable {Xh : Subgroup P}
    (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    (e : ↥Yh ≃* projImage (Sec4.slPi π 3 (p ^ f) K)) (hXY : Xh ≤ Yh)
    (hXns : ¬ Group.IsSolvable ↥Xh) : 2 < p ^ f := by
  by_contra hle
  have hp : p.Prime := hK.prime
  have hf : 1 ≤ f := hK.one_le
  have h2le : 2 ≤ p ^ f := by
    have h1 : p ^ 1 ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
    rw [pow_one] at h1
    exact le_trans hp.two_le h1
  have h2 : p ^ f = 2 := by omega
  have hπ : π = false := by
    cases π with
    | false => rfl
    | true =>
      exfalso
      simp [Sec4.ModThree, h2] at hq
  subst hπ
  haveI : Group.IsSolvable ↥(Sec4.slPi false 3 (p ^ f) K) :=
    h3b_isSolvable_slPi_false hK h2
  haveI : Group.IsSolvable ↥(projImage (Sec4.slPi false 3 (p ^ f) K)) :=
    Group.isSolvable_of_surjective (Sec4.projOf_surjective _)
  have hχ : Function.Injective
      (e.toMonoidHom.comp (Subgroup.inclusion hXY) :
        Xh →* ↥(projImage (Sec4.slPi false 3 (p ^ f) K))) :=
    e.injective.comp (Subgroup.inclusion_injective hXY)
  exact hXns (Group.isSolvable_of_isSolvable_injective hχ)

theorem hess_to_pgl [Yh.Normal] (hD : HessData Yh Bh xh bh ch) (hK : Sec4.PiField π p f K)
    (hq : Sec4.ModThree π (p ^ f)) (e : ↥Yh ≃* projImage (Sec4.slPi π 3 (p ^ f) K))
    {y : GL (Fin 3) K} (hy : Sec4.IsPGLAtP e bh y) :
    y ∉ StatedScalars (Fin 3) K ∧ y ^ 3 ∈ StatedScalars (Fin 3) K ∧
    ((e ⟨ch, hD.cY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) ≠ 1 ∧
    ((e ⟨ch, hD.cY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) ^ 3 = 1 ∧
    ProjGenLinGroup.mk y *
      ((e ⟨ch, hD.cY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
    ((e ⟨ch, hD.cY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) *
      ProjGenLinGroup.mk y ∧
    ∃ Xm : Subgroup (ProjGenLinGroup (Fin 3) K), Xm ≤ projImage (Sec4.slPi π 3 (p ^ f) K) ∧
      Xm ≤ Subgroup.centralizer ({ProjGenLinGroup.mk y} : Set (ProjGenLinGroup (Fin 3) K)) ∧
      Group.IsPerfect Xm ∧ ¬ Group.IsSolvable Xm ∧
      ((e ⟨ch, hD.cY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) ∈ Xm := by
  have hBcomm : ∀ a ∈ Bh, ∀ b ∈ Bh, a * b = b * a := by
    haveI := hD.elem.1
    exact fun a ha b hb => setLike_mul_comm ha hb
  have hBexp : ∀ a ∈ Bh, a ^ 3 = 1 := fun a ha => hD.elem.2 a ha
  have hxB : xh ∈ Bh := by
    rw [hD.gen]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers xh))
  have hbB : bh ∈ Bh := by
    rw [hD.gen]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers bh))
  have hcB : ch ∈ Bh := by
    rw [hD.gen]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ch)
  have hxcent : ∀ g : P, xh * g = g * xh := hD.xcent
  have hbA : bh ∉ Subgroup.zpowers xh := by
    intro hb
    have hB : Bh = Subgroup.zpowers xh ⊔ Subgroup.zpowers ch := by
      rw [hD.gen, sup_eq_left.mpr (Subgroup.zpowers_le.mpr hb)]
    have hle := h3b_card_sup_le_nine hxcent (hBexp xh hxB) (hBexp ch hcB)
    rw [← hB, hD.card] at hle
    omega
  have hchne : ch ≠ 1 := by
    intro h1
    have hB : Bh = Subgroup.zpowers xh ⊔ Subgroup.zpowers bh := by
      rw [hD.gen, h1, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
    have hle := h3b_card_sup_le_nine hxcent (hBexp xh hxB) (hBexp bh hbB)
    rw [← hB, hD.card] at hle
    omega
  have hy1 : y ∉ StatedScalars (Fin 3) K := by
    intro hys
    have hcen := Sec4.mem_centralizer_of_isPGLAtP_scalar hy hys
    have hmem : bh ∈ Bh ⊓ Subgroup.centralizer (Yh : Set P) :=
      Subgroup.mem_inf.mpr ⟨hbB, hcen⟩
    rw [hD.cent] at hmem
    exact hbA hmem
  obtain ⟨Xh, hXY, hXC, hXp, -, hchX, p₁, n₁, hp₁, h4, φ, hφ⟩ := hD.comp
  have hXns : ¬ Group.IsSolvable ↥Xh := by
    intro hs
    have hn1 : n₁ ≠ 0 := by
      rintro rfl
      simp at h4
    have h4' : 4 ≤ Nat.card (GaloisField p₁ n₁) := by
      rw [GaloisField.card p₁ n₁ hn1]
      exact h4
    exact h3b_not_isSolvable_projSL_two h4' (Group.isSolvable_of_surjective hφ)
  have hq2 : 2 < p ^ f := h3b_two_lt_of_not_isSolvable hK hq e hXY hXns
  haveI : Group.IsPerfect ↥(projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    CFSG.RankThree.PartTwo.Sec13.isPerfect_projImage_slPi hK hq2
  have hy3 : y ^ 3 ∈ StatedScalars (Fin 3) K := by
    have h3 := Sec4.isPGLAtP_pow hy 3
    rw [hBexp bh hbB] at h3
    have h1 : Sec4.IsPGLAtP e 1 1 := Sec4.isPGLAtP_of_mem_centralizer e (Subgroup.one_mem _)
    have h5 := Sec4.isPGLAtP_inv_mul_mem hK hq h1 h3
    simpa using h5
  have hcommY : ∀ {x : P} (hx : x ∈ Yh), bh * x = x * bh →
      ProjGenLinGroup.mk y * ((e ⟨x, hx⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) =
      ((e ⟨x, hx⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) *
        ProjGenLinGroup.mk y := by
    intro x hx hc
    have h := Hering129KH3.conj_compat e hy hx
    have hconj : bh * x * bh⁻¹ = x := by rw [hc, mul_inv_cancel_right]
    have he : e ⟨bh * x * bh⁻¹, Subgroup.Normal.conj_mem ‹_› x hx bh⟩ = e ⟨x, hx⟩ :=
      congrArg e (Subtype.ext hconj)
    rw [he] at h
    exact (eq_mul_inv_iff_mul_eq.mp h).symm
  have hcomm₀ := hcommY hD.cY (hBcomm bh hbB ch hcB)
  have hm₀ne : ((e ⟨ch, hD.cY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) ≠ 1 := by
    intro h
    have h1 : e ⟨ch, hD.cY⟩ = 1 := Subtype.ext h
    have h2 : (⟨ch, hD.cY⟩ : Yh) = 1 := e.injective (by rw [h1, map_one])
    exact hchne (congrArg Subtype.val h2)
  have hm₀pow : ((e ⟨ch, hD.cY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) ^ 3 = 1 := by
    have h3 : (⟨ch, hD.cY⟩ : Yh) ^ 3 = 1 := Subtype.ext (by simpa using hBexp ch hcB)
    have h4 : (e ⟨ch, hD.cY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) ^ 3 = 1 := by
      rw [← map_pow, h3, map_one]
    simpa using congrArg Subtype.val h4
  let χ : Xh →* ↥(projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    e.toMonoidHom.comp (Subgroup.inclusion hXY)
  have hχ : Function.Injective χ := e.injective.comp (Subgroup.inclusion_injective hXY)
  let ψ : Xh →* ProjGenLinGroup (Fin 3) K :=
    (projImage (Sec4.slPi π 3 (p ^ f) K)).subtype.comp χ
  have hψ : Function.Injective ψ := (Subgroup.subtype_injective _).comp hχ
  refine ⟨hy1, hy3, hm₀ne, hm₀pow, hcomm₀, ψ.range, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (χ x).2
  · rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx : bh * (x : P) = (x : P) * bh :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hXC x.2)).symm
    exact (hcommY (hXY x.2) hx).symm
  · exact Group.IsPerfect.range ψ
  · intro hs
    apply hXns
    have hinj : Function.Injective ψ.rangeRestrict := by
      intro a b hab
      apply hψ
      have h := congrArg Subtype.val hab
      exact h
    exact Group.isSolvable_of_isSolvable_injective (f := ψ.rangeRestrict) hinj
  · exact MonoidHom.mem_range.mpr ⟨⟨ch, hchX⟩, rfl⟩

end Hering129KH3b

end CFSG.RankThree.PartTwo.Sec12
