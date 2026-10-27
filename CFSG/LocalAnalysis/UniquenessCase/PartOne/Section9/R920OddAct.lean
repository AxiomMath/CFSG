module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddPair
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

private theorem finite_mulAut (X : Type) [Group X] [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem map_conj_eq_of_le (h82 : F08.R82 D) (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D)
    (h76 : F07.R76Sig D) (hKF7 : KF7Use D) (S : SliceCore D L D₃ Y H)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {E P : Subgroup G} (hEX : E ≤ Opp 3 Y)
    (hE3 : Nat.card E = 3) (hEU : E ∈ uniqueSet D.M) (hP : IsPGroup 3 ↥P) (hPM : P ≤ D.M)
    (hEP : E ≤ P) {h : G} (hh : h ∈ H) (hhP : E.map (MulAut.conj h).toMonoidHom ≤ P) :
    E.map (MulAut.conj h).toMonoidHom = E := by
  by_contra hne
  exact S.false_of_map_conj_ne h82 hSg h614 h76 hKF7 hnsp hEX hE3 hEU hP hPM hEP hh hhP hne

theorem isCyclic_of_isPGroup_mulAut_bar2 (S : SliceCore D L D₃ Y H)
    {R : Subgroup (MulAut (Bar2 L))} (hR : IsPGroup 3 ↥R) : IsCyclic ↥R := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_mulAut (Bar2 L)
  have hZ : Subgroup.center (Bar2 L) = ⊥ :=
    haveI := S.facts_L.simple
    uc22p21k_center_eq_bot S.L_mem.2.2
  let e : Bar2 L →* MulAut (Bar2 L) := MulAut.conj
  have hinj : Function.Injective e := by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center (Bar2 L) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 : a * x * a⁻¹ = b * x * b⁻¹ := by
        simpa [e, MulAut.conj_apply] using DFunLike.congr_fun hab x
      calc x * (a⁻¹ * b) = a⁻¹ * (a * x * a⁻¹) * b := by group
        _ = a⁻¹ * (b * x * b⁻¹) * b := by rw [h1]
        _ = (a⁻¹ * b) * x := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc
  have hrange : Nat.card e.range = Nat.card (Bar2 L) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hdvd : e.range.index ∣ 2 := by
    have h := e.range.index_mul_card
    rw [hrange] at h
    have hA := S.facts_L.card_mulAut_dvd
    rw [← h] at hA
    exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hA
  have hle : R ≤ e.range := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with hindex | hindex
    · rw [Subgroup.index_eq_one.1 hindex]
      exact le_top
    haveI : e.range.Normal := Subgroup.normal_of_index_eq_two hindex
    have hq2 : Nat.card (MulAut (Bar2 L) ⧸ e.range) = 2 := by
      rw [← Subgroup.index_eq_card]
      exact hindex
    intro r hr
    obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
    have hpow : r ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf (QuotientGroup.mk' e.range r) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hpow, map_one])
    have h2 : orderOf (QuotientGroup.mk' e.range r) ∣ 2 := by
      have := orderOf_dvd_natCard (QuotientGroup.mk' e.range r)
      rwa [hq2] at this
    have h3 := Nat.dvd_gcd h1 h2
    rw [(Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 3 2)).gcd_eq_one] at h3
    exact (QuotientGroup.eq_one_iff r).1 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3))
  have hR₀p : IsPGroup 3 ↥(R.comap e) := hR.comap_of_injective e hinj
  have hrank : CFSG.Open.pRank 3 (R.comap e) ≤ 1 := by
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = CFSG.Open.pRank 3 L :=
      PartTwo.s13_pRank_bar_top Nat.prime_three (by norm_num) L
    have h2 : CFSG.Open.pRank 3 L ≤ 1 := S.thin_L 3 Nat.prime_three (by norm_num)
    exact (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans (h1 ▸ h2)
  have hcyc : IsCyclic ↥(R.comap e) :=
    UCK.K31.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) hR₀p hrank
  have hmap : (R.comap e).map e = R := by
    rw [Subgroup.map_comap_eq]
    first
      | exact inf_eq_right.2 hle
      | exact inf_eq_left.2 hle
  have hcyc' := ((R.comap e).equivMapOfInjective e hinj).isCyclic.1 hcyc
  rwa [hmap] at hcyc'

theorem exists_cyclic_hom_of_isPGroup (h82 : F08.R82 D) (S : SliceCore D L D₃ Y H)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {P : Subgroup G} (hP : IsPGroup 3 ↥P) (hPM : P ≤ D.M) :
    ∃ (Q : Type) (_ : Group Q) (φ : ↥P →* Q), IsCyclic Q ∧
      ∀ x : ↥P, (x : G) ∈ L → φ x = 1 → x = 1 := by
  classical
  have hodd : ∀ x ∈ P, Odd (orderOf x) := fun x hx => by
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    have hpow : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hpow)
  have hPN : P ≤ normalizer (L : Set G) := fun x hx =>
    S.mem_normalizer_L_of_odd h82 hnsp (hPM hx) (hodd x hx)
  let f : ↥P →* MulAut (Bar2 L) := (UC6S846.rhoL L).comp (Subgroup.inclusion hPN)
  refine ⟨↥f.range, inferInstance, f.rangeRestrict,
    S.isCyclic_of_isPGroup_mulAut_bar2 (hP.of_surjective f.rangeRestrict
      f.rangeRestrict_surjective), fun x hxL hx1 => ?_⟩
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
  have hZ : Subgroup.center (Bar2 L) = ⊥ :=
    haveI := S.facts_L.simple
    uc22p21k_center_eq_bot S.L_mem.2.2
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

end SliceCore

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
