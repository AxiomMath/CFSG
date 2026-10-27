module

public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnLift
public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnCenter
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13a
public import CFSG.RankThree.PartTwo.Sec21.FF79KFacts13
import CFSG.RankThree.PartTwo.Sec21.HeringFFLInner

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.TLn

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

private theorem sylowOf_card {G : Type} [Group G] [Finite G] {H P : Subgroup G}
    (h : IsSylowOf 3 P H) : Nat.card P = 3 ^ (Nat.card H).factorization 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hle, hp, hcop⟩ := h
  obtain ⟨a, ha⟩ := hp.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card P H
  rw [inf_of_le_left hle, ha] at h1
  have hne : P.relIndex H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  have hf : (P.relIndex H).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop)
  rw [← h1, Nat.factorization_mul hne (by positivity), Finsupp.add_apply, hf,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same, zero_add, ha]

theorem liftData_of_equiv {G : Type} [Group G] [Finite G] {J P : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥J) (hP : IsSylowOf 3 P J)
    (hcop : Nat.Coprime 3 (Nat.card ↥(Subgroup.center ↥J)))
    {S : Type} [Group S] [Finite S] (e : (↥J ⧸ Subgroup.center ↥J) ≃* S) {R : Subgroup S}
    (hsyl : Nat.card R = 3 ^ (Nat.card S).factorization 3) :
    Nonempty (LiftData J P S R) ∧ Nat.card P = 3 ^ (Nat.card S).factorization 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.center ↥J with hZ
  let ϕ₀ : ↥J →* S := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hϕ₀ : ∀ x, ϕ₀ x = e (QuotientGroup.mk x) := fun _ => rfl
  have hker : ∀ x : ↥J, ϕ₀ x = 1 ↔ x ∈ Z := by
    intro x
    rw [hϕ₀, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hPcard : Nat.card P = 3 ^ (Nat.card S).factorization 3 := by
    rw [sylowOf_card hP]
    have hJ : Nat.card ↥J = Nat.card S * Nat.card Z := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z, Nat.card_congr e.toEquiv]
    have hZ0 : (Nat.card Z).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop)
    rw [hJ, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hZ0,
      add_zero]
  let Pj : Subgroup ↥J := P.subgroupOf J
  have hPj3 : IsPGroup 3 Pj := hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  have hPjcard : Nat.card Pj = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv
  have hPj3' : ∀ x : ↥J, x ∈ Pj → ∃ k : ℕ, x ^ (3 ^ k) = 1 := fun x hx => hPj3 ⟨x, hx⟩ |>.imp
    fun k hk => by simpa using congrArg Subtype.val hk
  have hinj : ∀ x y : ↥J, x ∈ Pj → y ∈ Pj → ϕ₀ x = ϕ₀ y → x = y := by
    intro x y hx hy hxy
    exact eq_of_inv_mul_mem_center hcop
      ((hker _).mp (by rw [map_mul, map_inv, hxy, inv_mul_cancel])) (hPj3' x hx) (hPj3' y hy)
  let Q : Subgroup S := Pj.map ϕ₀
  have hQcard : Nat.card Q = 3 ^ (Nat.card S).factorization 3 := by
    rw [← hPcard, ← hPjcard]
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun x : Pj => (⟨ϕ₀ x, x, x.2, rfl⟩ : Q))
      ⟨fun x y hxy => Subtype.ext (hinj x y x.2 y.2 (congrArg Subtype.val hxy)), ?_⟩)
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨s, hs⟩ := exists_conj_of_card hsyl hQcard
  refine ⟨⟨{ e := e.trans (MulAut.conj s⁻¹),
              ϕ := (MulAut.conj s⁻¹).toMonoidHom.comp ϕ₀,
              ϕ_eq := fun j => rfl,
              perf := Subgroup.isPerfect_iff.mp hq.1,
              surj := ?_,
              ker_eq := ?_,
              cop := hcop,
              pgrp := hP.2.1,
              le := hP.1,
              img := ?_ }⟩, hPcard⟩
  · intro x
    obtain ⟨q, hq'⟩ := e.surjective (s * x * s⁻¹)
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨j, ?_⟩
    show s⁻¹ * ϕ₀ j * s⁻¹⁻¹ = x
    rw [hϕ₀, hq']
    group
  · ext x
    rw [MonoidHom.mem_ker]
    show (MulAut.conj s⁻¹) (ϕ₀ x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact hker x
  · intro x
    constructor
    · intro hx
      have h1 : s * x * s⁻¹ ∈ Q := (hs _).mpr (by
        rw [show s⁻¹ * (s * x * s⁻¹) * s = x by group]; exact hx)
      obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.mp h1
      refine ⟨p, hp, ?_⟩
      show s⁻¹ * ϕ₀ p * s⁻¹⁻¹ = x
      rw [hpe]
      group
    · rintro ⟨p, hp, rfl⟩
      have := (hs (ϕ₀ p)).mp ⟨p, hp, rfl⟩
      show s⁻¹ * ϕ₀ p * s⁻¹⁻¹ ∈ R
      rwa [inv_inv]

theorem exists_liftData
    {G : Type} [Group G] [Finite G] {n : ℕ}
    (hn : n = 4 ∨ n = 5) {J P : Subgroup G} (hq : CFSG.IsQuasisimple ↥J)
    (hm : IsTypeLnq n 2 1 J) (hP : IsSylowOf 3 P J) :
    ∃ (S : Type) (_ : Group S) (R : Subgroup S), TModel S R ∧
      Nat.card R = 3 ^ (Nat.card S).factorization 3 ∧ Nat.card P = 9 ∧
      Nonempty (LiftData J P S R) ∧
      (CentAlphaS (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
          (TLn.R Hering214.sA4 Hering214.sB4) 4 →
        CentAlphaS (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
          (TLn.R Hering214.sA5 Hering214.sB5) 5 →
        CentAlphaS S R n) := by
  have hZ := FF79.card_center_dvd_two_of_typeLn hq hn hm
  have hcop : Nat.Coprime 3 (Nat.card ↥(Subgroup.center ↥J)) :=
    Nat.Coprime.coprime_dvd_right hZ (by norm_num)
  obtain ⟨e'⟩ : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃*
      Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := Hering214.exists_mulEquiv_projectiveSL_of_psl_two_one hm
    haveI := Hering214.charP_two_of_natCard_eq_two hK
    exact ⟨e.trans (MulEquiv.ofBijective (Hering214.embedTwo K n)
      (embedTwo_bijective hK hn)).symm⟩
  rcases hn with rfl | rfl
  · obtain ⟨hL, hc⟩ := liftData_of_equiv hq hP hcop e' card_R_sylow4
    refine ⟨_, inferInstance, _, tModel4, card_R_sylow4, ?_, hL, fun h4 _ => h4⟩
    rw [hc, ← card_R_sylow4, tModel4.card]
  · obtain ⟨hL, hc⟩ := liftData_of_equiv hq hP hcop e' card_R_sylow5
    refine ⟨_, inferInstance, _, tModel5, card_R_sylow5, ?_, hL, fun _ h5 => h5⟩
    rw [hc, ← card_R_sylow5, tModel5.card]

end CFSG.RankThree.PartTwo.Sec21.FF79.TLn

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21 TLn

theorem ff79KTypeLn_holds :
    FF79KTypeLn := by
  intro G _ _ n J hn hq hm
  have hZ := card_center_dvd_two_of_typeLn hq hn hm
  refine ⟨Nat.Coprime.coprime_dvd_right hZ (by norm_num), ?_, ?_⟩
  · intro P'
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hQ : IsSylowOf 3 ((P' : Subgroup ↥J).map J.subtype) J := by
      refine ⟨Subgroup.map_subtype_le _, P'.isPGroup'.map J.subtype, ?_⟩
      rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective J.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr P'.not_dvd_index
    obtain ⟨S, _, R, M, -, hc, ⟨L⟩, -⟩ := exists_liftData hn hq hm hQ
    have hcomm : IsMulCommutative ↥((P' : Subgroup ↥J).map J.subtype) :=
      IsMulCommutative.of_comm fun a b => Subtype.ext (L.comm_P M a.2 b.2)
    have hexp : Monoid.exponent ↥((P' : Subgroup ↥J).map J.subtype) ∣ 3 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => Subtype.ext (L.cube_P M x.2)
    refine ⟨{ toIsMulCommutative := hcomm, exponent_dvd_p := hexp }, ?_⟩
    rw [hc]
    norm_num
  · intro x hx ⟨k, hk⟩
    obtain ⟨j, hj, hc⟩ := exists_mem_inv_mul_mem_centralizer_of_odd hq hn hm hx
      (m := 3 ^ k) (Odd.pow (by decide)) hk
    refine ⟨j, hj, fun y hy => ?_⟩
    have hcy := Subgroup.mem_centralizer_iff.mp hc y hy
    calc x * y * x⁻¹ = j * ((j⁻¹ * x) * y) * (j⁻¹ * x)⁻¹ * j⁻¹ := by group
      _ = j * (y * (j⁻¹ * x)) * (j⁻¹ * x)⁻¹ * j⁻¹ := by rw [hcy]
      _ = j * y * j⁻¹ := by group

theorem ff79KTypeLnNorm_holds :
    FF79KTypeLnNorm := by
  intro G _ _ n J P hn hq hm _ hP
  obtain ⟨S, _, R, M, -, -, ⟨L⟩, -⟩ := exists_liftData hn hq hm hP
  refine ⟨L.tau_lift M, L.count_lift M, L.noncomm_lift M, fun g hg hgP => ?_⟩
  obtain ⟨j, hj, h⟩ := L.nor_act_lift M hg hgP
  exact ⟨j, j.2, hj, h⟩

theorem ff79KAutCentP_holds :
    FF79KAutCentP := by
  intro G _ _ n J P hn hq hm hP
  obtain ⟨S, _, R, M, hsyl, -, ⟨L⟩, -⟩ := exists_liftData hn hq hm hP
  refine ⟨L.relIndex_le_two M, fun g hg => ?_⟩
  obtain ⟨j, hj⟩ := L.exists_cent_lift M hsyl hg
  exact ⟨j, j.2, hj⟩

end CFSG.RankThree.PartTwo.Sec21.FF79

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21 TLn

theorem ff79KCentAlpha_of_finite
    (h4 : CentAlphaS (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
      (TLn.R Hering214.sA4 Hering214.sB4) 4)
    (h5 : CentAlphaS (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
      (TLn.R Hering214.sA5 Hering214.sB5) 5) :
    FF79KCentAlpha := by
  intro G _ _ n J P hn hq hm hP α hα hα3 Y hY1 hY2 hcop hnorm
  obtain ⟨S, _, R, M, -, -, ⟨L⟩, hS⟩ := exists_liftData hn hq hm hP
  exact L.centAlpha_lift M (hS h4 h5) hα hα3 hY1 hY2 hcop hnorm

end CFSG.RankThree.PartTwo.Sec21.FF79
