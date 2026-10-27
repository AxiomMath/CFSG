module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveCStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InnerTorusFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

private theorem isMetacyclic_of_isPGroup_subgroup_mulAut {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥)
    (hcyc : ∀ S : Subgroup X, IsPGroup 3 S → IsCyclic S)
    (hOut : IsCyclic (Outer X))
    (R : Subgroup (MulAut X)) (hR : IsPGroup 3 ↥R) :
    CFSG.IsMetacyclic ↥R ∧ (¬ 3 ∣ Nat.card (Outer X) → IsCyclic ↥R) := by
  classical
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := congrArg (fun f : MulAut X => f x) hab
      simp only [MulAut.conj_apply] at h1
      calc x * (a⁻¹ * b) = a⁻¹ * (a * x * a⁻¹) * b := by group
        _ = a⁻¹ * (b * x * b⁻¹) * b := by rw [h1]
        _ = a⁻¹ * b * x := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc
  let I : Subgroup (MulAut X) := CFSG.ComponentClassification.OuterAutomorphisms.inner X
  haveI hIn : I.Normal := inferInstance
  let N : Subgroup ↥R := I.subgroupOf R
  haveI hNn : N.Normal := inferInstance
  have hNcyc : IsCyclic ↥N := by
    have hN3 : IsPGroup 3 ↥N := hR.to_subgroup N
    let B : Subgroup (MulAut X) := N.map (Subgroup.subtype R)
    have hBle : B ≤ I := by
      rintro b ⟨n, hn, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hn
    let A : Subgroup X := B.comap (MulAut.conj : X →* MulAut X)
    have hB3 : IsPGroup 3 ↥B := hN3.map (Subgroup.subtype R)
    have hA3 : IsPGroup 3 ↥A :=
      hB3.comap_of_injective (MulAut.conj : X →* MulAut X) hinj
    have hAcyc : IsCyclic ↥A := hcyc A hA3
    have hBA : A.map (MulAut.conj : X →* MulAut X) = B := Subgroup.map_comap_eq_self hBle
    have hBcyc : IsCyclic ↥B := by
      rw [← hBA]
      exact isCyclic_of_surjective ((MulAut.conj : X →* MulAut X).subgroupMap A)
        ((MulAut.conj : X →* MulAut X).subgroupMap_surjective A)
    exact (N.equivMapOfInjective (Subgroup.subtype R) Subtype.val_injective).isCyclic.mpr hBcyc
  have hquotcyc : IsCyclic (↥R ⧸ N) := by
    haveI : IsCyclic (Outer X) := hOut
    let g : ↥R →* Outer X := (QuotientGroup.mk' I).comp (Subgroup.subtype R)
    have hker : g.ker = N := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
      exact QuotientGroup.eq_one_iff (x : MulAut X)
    have hcyc_ker : IsCyclic (↥R ⧸ g.ker) :=
      isCyclic_of_injective (QuotientGroup.kerLift g) (QuotientGroup.kerLift_injective g)
    exact (QuotientGroup.quotientMulEquivOfEq hker).isCyclic.mp hcyc_ker
  refine ⟨⟨N, hNn, hNcyc, hquotcyc⟩, fun h3out => ?_⟩
  have hRI : R ≤ I := by
    intro r hr
    let rr : ↥R := ⟨r, hr⟩
    let g : ↥R →* Outer X := (QuotientGroup.mk' I).comp (Subgroup.subtype R)
    obtain ⟨k, hk⟩ := hR rr
    have hpow : g rr ^ 3 ^ k = 1 := by rw [← map_pow, hk, map_one]
    have hd1 : orderOf (g rr) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hpow
    have hd2 : orderOf (g rr) ∣ Nat.card (Outer X) := orderOf_dvd_natCard _
    have hcop : Nat.Coprime (3 ^ k) (Nat.card (Outer X)) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3out)
    have hone : orderOf (g rr) = 1 :=
      Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hd1 hd2)
    have hg1 : g rr = 1 := orderOf_eq_one_iff.1 hone
    exact (QuotientGroup.eq_one_iff (rr : MulAut X)).1 hg1
  let A : Subgroup X := R.comap (MulAut.conj : X →* MulAut X)
  have hA3 : IsPGroup 3 ↥A := hR.comap_of_injective _ hinj
  have hAcyc : IsCyclic ↥A := hcyc A hA3
  have hRA : A.map (MulAut.conj : X →* MulAut X) = R := Subgroup.map_comap_eq_self hRI
  haveI := hAcyc
  rw [← hRA]
  exact isCyclic_of_surjective ((MulAut.conj : X →* MulAut X).subgroupMap A)
    ((MulAut.conj : X →* MulAut X).subgroupMap_surjective A)

theorem exists_metacyclic_hom_of_isL2 {D : Data G} (h82 : F08.R82 D)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {L : Subgroup G} {n : ℕ} (hL : L ∈ calC D.M)
    (hL2 : IsL2 (Bar2 L) n) {P : Subgroup G} (hP : IsPGroup 3 ↥P) (hPM : P ≤ D.M) :
    ∃ (Q : Type) (_ : Group Q) (φ : ↥P →* Q), CFSG.IsMetacyclic Q ∧ (¬ 3 ∣ n → IsCyclic Q) ∧
      ∀ x : ↥P, (x : G) ∈ L → φ x = 1 → x = 1 := by
  classical
  have h3rank : CFSG.Open.pRank 3 L = 1 := pRank_three_eq_one_of_isL2 hL2
  have hodd : ∀ x ∈ P, Odd (orderOf x) := fun x hx => by
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    have hpow : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hpow)
  have hPN : P ≤ normalizer (L : Set G) := fun x hx =>
    R8107Odd.mem_normalizer_of_odd h82 hnsp hL h3rank (hPM hx) (hodd x hx)
  let f : ↥P →* MulAut (Bar2 L) := (UC6S846.rhoL L).comp (Subgroup.inclusion hPN)
  have hsimple : IsSimpleGroup (Bar2 L) :=
    isSimpleGroup_bar2_of_isL2_or_isSz (Or.inl hL2)
  have hZ : Subgroup.center (Bar2 L) = ⊥ := by
    haveI := hsimple
    exact uc22p21k_center_eq_bot hL.2.2
  have hEv : IsL2Ev (Bar2 L) n := (P22fin.isL2Ev_of_isL2 hL2).1
  have hcyc : ∀ S : Subgroup (Bar2 L), IsPGroup 3 S → IsCyclic S := fun S hS =>
    P22y.isCyclic_of_isPGroup_of_isL2Ev hEv Nat.prime_three (by norm_num) S hS
  have hOut : IsCyclic (Outer (Bar2 L)) := (outer_finite_isCyclic_1755 hL2).2
  have hR : IsPGroup 3 ↥f.range :=
    hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨hmeta, hcycimg⟩ :=
    isMetacyclic_of_isPGroup_subgroup_mulAut hZ hcyc hOut f.range hR
  have hOutdvd : Nat.card (Outer (Bar2 L)) ∣ n := card_outer_dvd_of_isL2 hL2
  refine ⟨↥f.range, inferInstance, f.rangeRestrict, hmeta,
    fun h3n => hcycimg (fun h3out => h3n (h3out.trans hOutdvd)), ?_⟩
  intro x hxL hx1
  have hx1' : f x = 1 := by simpa using congrArg Subtype.val hx1
  have hf : f x = UC6S846.rhoL L ⟨x, hPN x.2⟩ := rfl
  rw [hf, UC6S846.rhoL_inner L x hxL] at hx1'
  have hcen : (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) ∈ Subgroup.center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := DFunLike.congr_fun hx1' g
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L)
        = ((QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) * g *
            (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L)⁻¹) *
          (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) := by rw [h]
      _ = (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) * g := by group
  rw [hZ, Subgroup.mem_bot] at hcen
  have h2 : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).1 hcen
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨⟨x, hxL⟩, h2⟩
  obtain ⟨b, hb⟩ := hP x
  have h2pow : (x : G) ^ 2 ^ a = 1 := by
    simpa using congrArg (fun y : ↥(CFSG.pCore 2 ↥L) => ((y : ↥L) : G)) ha
  have h3pow : (x : G) ^ 3 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2pow) (orderOf_dvd_of_pow_eq_one h3pow)
  rw [(Nat.Coprime.pow a b (by norm_num : Nat.Coprime 2 3)).gcd_eq_one] at hd
  exact Subtype.ext (orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
