module

public import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJCore
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofGL
public import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
public import CFSG.RankThree.PartTwo.KFacts.K412TripleCover
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionLifting
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
open CFSG.RankThree.PartTwo.Sec4.Census (CriticalAt)

noncomputable def sigmaOfTripleCover {T : Type} [Group T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) :
    T →* alternatingGroup (Fin 6) :=
  hT.2.some.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center T))

theorem sigmaOfTripleCover_surjective {T : Type} [Group T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) :
    Function.Surjective (sigmaOfTripleCover hT) :=
  hT.2.some.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center T))

theorem sigmaOfTripleCover_ker {T : Type} [Group T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) :
    (sigmaOfTripleCover hT).ker = Subgroup.center T := by
  ext x
  rw [MonoidHom.mem_ker]
  change hT.2.some (QuotientGroup.mk x) = 1 ↔ x ∈ Subgroup.center T
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

private theorem ker_comp_sigma_isSolvable {Y T : Type} [Group Y] [Group T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) (π : Y →* T)
    (hK : Group.IsSolvable π.ker) :
    Group.IsSolvable ((sigmaOfTripleCover hT).comp π).ker := by
  haveI : Group.IsSolvable π.ker := hK
  set N : Subgroup Y := (Subgroup.center T).comap π
  have hker : ((sigmaOfTripleCover hT).comp π).ker = N := by
    rw [← MonoidHom.comap_ker (sigmaOfTripleCover hT) π, sigmaOfTripleCover_ker]
  have hle : π.ker ≤ N := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact Subgroup.one_mem _
  rw [hker]
  let f : π.ker →* N := Subgroup.inclusion hle
  let g : N →* Subgroup.center T := (π.comp N.subtype).codRestrict _ fun x => x.2
  have hfg : g.ker ≤ f.range := by
    intro x hx
    have h1 : π (x : Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact ⟨⟨(x : Y), h1⟩, rfl⟩
  exact Group.isSolvable_of_ker_le_range f g hfg

private theorem isSimpleGroup_quotient_ker_comp {Y T : Type} [Group Y] [Group T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) (π : Y →* T)
    (hπ : Function.Surjective π) :
    IsSimpleGroup (Y ⧸ ((sigmaOfTripleCover hT).comp π).ker) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact MulEquiv.isSimpleGroup
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((sigmaOfTripleCover_surjective hT).comp hπ))

private theorem ker_comp_sigma_ne_top {Y T : Type} [Group Y] [Group T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) (π : Y →* T)
    (hπ : Function.Surjective π) :
    ((sigmaOfTripleCover hT).comp π).ker ≠ ⊤ := by
  haveI hs : IsSimpleGroup (Y ⧸ ((sigmaOfTripleCover hT).comp π).ker) :=
    isSimpleGroup_quotient_ker_comp hT π hπ
  exact QuotientGroup.nontrivial_iff.mp hs.toNontrivial

private theorem not_sq_dvd_1080 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ^ 2 ∣ 1080 := by
  intro h
  have hpdvd : p ∣ 1080 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans h
  have hfac : (1080 : ℕ) = 2 ^ 3 * 3 ^ 3 * 5 := by norm_num
  rw [hfac] at hpdvd
  have h2 : ¬ p ∣ 2 := fun hd => by
    have h' := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
    omega
  have h3 : ¬ p ∣ 3 := fun hd => by
    have h' := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd
    omega
  have hp5dvd : p ∣ 5 := by
    rcases hp.dvd_mul.mp hpdvd with h' | h'
    · rcases hp.dvd_mul.mp h' with h'' | h''
      · exact absurd (hp.dvd_of_dvd_pow h'') h2
      · exact absurd (hp.dvd_of_dvd_pow h'') h3
    · exact h'
  have hple : p ≤ 5 := Nat.le_of_dvd (by norm_num) hp5dvd
  rcases hp.eq_two_or_odd' with h2' | hodd
  · exact absurd h2' hp2
  · obtain ⟨k, hk⟩ := hodd
    have hp_eq : p = 5 := by
      have := hp.two_le
      omega
    subst hp_eq
    norm_num at h

private theorem ker_le_center_of_isQuasisimple {Y T : Type} [Group Y] [Group T]
    (hq : IsQuasisimple Y) (π : Y →* T) (hK : Group.IsSolvable π.ker) :
    π.ker ≤ Subgroup.center Y := by
  obtain ⟨-, hZs, a, b, hab⟩ := hq
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hZs
  haveI : Group.IsSolvable π.ker := hK
  have hn : (π.ker.map (QuotientGroup.mk' (Subgroup.center Y))).Normal :=
    (MonoidHom.normal_ker π).map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (π.ker.map (QuotientGroup.mk' (Subgroup.center Y))) with h | h
  · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · have hsurj : Function.Surjective
        ((QuotientGroup.mk' (Subgroup.center Y)).comp π.ker.subtype) := by
      intro x
      have hx : x ∈ π.ker.map (QuotientGroup.mk' (Subgroup.center Y)) := by
        rw [h]
        trivial
      obtain ⟨k, hk, rfl⟩ := hx
      exact ⟨⟨k, hk⟩, rfl⟩
    have hsol : Group.IsSolvable (Y ⧸ Subgroup.center Y) :=
      Group.isSolvable_of_surjective hsurj
    exact absurd ((IsSimpleGroup.comm_iff_isSolvable).mpr hsol a b) hab

private theorem ker_eq_bot_of_isQuasisimple {Y T : Type} [Group Y] [Finite Y]
    [Group.IsPerfect Y] [Group T] (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hq : IsQuasisimple Y) (π : Y →* T) (hπ : Function.Surjective π)
    (hK : Group.IsSolvable π.ker) (h3 : ¬ 3 ∣ Nat.card π.ker)
    (hO2 : CFSG.pCore 2 Y = ⊥) : π.ker = ⊥ := by
  have hKZ : π.ker ≤ Subgroup.center Y := ker_le_center_of_isQuasisimple hq π hK
  have h2 : ¬ 2 ∣ Nat.card π.ker := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) 2 h2
    have ht' : orderOf (t : Y) = 2 := by rw [Subgroup.orderOf_coe, ht]
    have hnorm : (Subgroup.zpowers (t : Y)).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr (hKZ t.2))
    have hpg : IsPGroup 2 (Subgroup.zpowers (t : Y)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
    have hle : Subgroup.zpowers (t : Y) ≤ CFSG.pCore 2 Y := le_sSup ⟨hnorm, hpg⟩
    rw [hO2, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
    rw [hle, orderOf_one] at ht'
    exact absurd ht' (by norm_num)
  refine CFSG.RankThree.PartTwo.KFacts.KS14.eq_bot_of_isPerfect_of_not_sq_dvd hKZ ?_
  intro p hp hpdvd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h2 hpdvd
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact h3 hpdvd
  have hcard : Nat.card (Y ⧸ π.ker) = 1080 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv,
      CFSG.RankThree.PartTwo.Sec13.card_eq_of_isTripleCover_six hT]
  rw [hcard]
  exact not_sq_dvd_1080 hp hp2 hp3

private theorem pCore_three_inf_ker {Y T : Type} [Group Y] [Finite Y] [Group T]
    (π : Y →* T) (h3 : ¬ 3 ∣ Nat.card π.ker) : CFSG.pCore 3 Y ⊓ π.ker = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 3) (G := Y)).to_le inf_le_left |>.exists_card_eq
  have hdvd : 3 ^ k ∣ Nat.card π.ker := hk ▸ Subgroup.card_dvd_of_le inf_le_right
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  · exact absurd ((dvd_pow_self 3 hk0.ne').trans hdvd) h3

private theorem pCore_three_image_sigma_eq_bot {Y T : Type} [Group Y] [Group T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) (π : Y →* T)
    (hπ : Function.Surjective π) :
    ((CFSG.pCore 3 Y).map π).map (sigmaOfTripleCover hT) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnorm : ((CFSG.pCore 3 Y).map π).Normal :=
    (pCore_normal (p := 3) (G := Y)).map π hπ
  have hnorm' : (((CFSG.pCore 3 Y).map π).map (sigmaOfTripleCover hT)).Normal :=
    hnorm.map _ (sigmaOfTripleCover_surjective hT)
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (((CFSG.pCore 3 Y).map π).map (sigmaOfTripleCover hT)) with h | h
  · exact h
  · exfalso
    haveI hperf : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    have hsol : Group.IsSolvable
        (((CFSG.pCore 3 Y).map π).map (sigmaOfTripleCover hT)) := by
      have hpg : IsPGroup 3
          (((CFSG.pCore 3 Y).map π).map (sigmaOfTripleCover hT)) :=
        ((pCore_isPGroup (p := 3) (G := Y)).map π).map (sigmaOfTripleCover hT)
      haveI : Group.IsNilpotent
          (((CFSG.pCore 3 Y).map π).map (sigmaOfTripleCover hT)) := hpg.isNilpotent
      infer_instance
    haveI : Group.IsSolvable (⊤ : Subgroup (alternatingGroup (Fin 6))) := h ▸ hsol
    have hsolA : Group.IsSolvable (alternatingGroup (Fin 6)) :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv (G := alternatingGroup (Fin 6))).toMonoidHom)
        (Subgroup.topEquiv (G := alternatingGroup (Fin 6))).surjective
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6)) hsolA

private theorem pCore_three_map_le_center {Y T : Type} [Group Y] [Group T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) (π : Y →* T)
    (hπ : Function.Surjective π) :
    (CFSG.pCore 3 Y).map π ≤ Subgroup.center T := by
  have hbot := pCore_three_image_sigma_eq_bot hT π hπ
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : (sigmaOfTripleCover hT) (π x) = 1 := by
    have hx' : (sigmaOfTripleCover hT) (π x) ∈
        ((CFSG.pCore 3 Y).map π).map (sigmaOfTripleCover hT) :=
      ⟨π x, ⟨x, hx, rfl⟩, rfl⟩
    rw [hbot] at hx'
    simpa using hx'
  rw [← sigmaOfTripleCover_ker hT, MonoidHom.mem_ker]
  exact hx1

private theorem pCore_three_le_center {Y T : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    [Group T] (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) (π : Y →* T)
    (hπ : Function.Surjective π) (h3 : ¬ 3 ∣ Nat.card π.ker) :
    CFSG.pCore 3 Y ≤ Subgroup.center Y := by
  have himg := pCore_three_map_le_center hT π hπ
  have hinf := pCore_three_inf_ker π h3
  have hinj : ∀ x y : CFSG.pCore 3 Y, π (x : Y) = π (y : Y) → x = y := by
    intro x y hxy
    have h1 : ((x : Y) * (y : Y)⁻¹) ∈ CFSG.pCore 3 Y :=
      (CFSG.pCore 3 Y).mul_mem x.2 (Subgroup.inv_mem _ y.2)
    have h2 : ((x : Y) * (y : Y)⁻¹) ∈ π.ker :=
      MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
    have hmem : ((x : Y) * (y : Y)⁻¹) ∈ CFSG.pCore 3 Y ⊓ π.ker :=
      Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact Subtype.ext (mul_inv_eq_one.mp hmem)
  have hcarddvd : Nat.card (CFSG.pCore 3 Y) ∣ 3 := by
    have h1 : Nat.card ((CFSG.pCore 3 Y).map π) ∣ Nat.card (Subgroup.center T) :=
      Subgroup.card_dvd_of_le (H := (CFSG.pCore 3 Y).map π) (K := Subgroup.center T) himg
    rw [hT.1] at h1
    have hbij : Function.Bijective (fun x : CFSG.pCore 3 Y =>
        (⟨π (x : Y), ⟨x, x.2, rfl⟩⟩ : (CFSG.pCore 3 Y).map π)) := by
      refine ⟨fun x y hxy => ?_, fun y => ?_⟩
      · exact hinj x y (congrArg Subtype.val hxy)
      · obtain ⟨x, hx, hxy⟩ := y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    have heq : Nat.card (CFSG.pCore 3 Y) = Nat.card ((CFSG.pCore 3 Y).map π) :=
      Nat.card_congr (Equiv.ofBijective _ hbij)
    rwa [heq]
  haveI : IsCyclic ↥(CFSG.pCore 3 Y) := isCyclic_of_card_dvd_prime hcarddvd
  exact CFSG.RankThree.PartTwo.KFacts.K412.le_center_of_isCyclic
    (Group.IsPerfect.commutator_eq_top (G := Y))

private theorem exists_critical_of_not_isQuasisimple {Y T : Type} [Group Y] [Finite Y]
    [Group.IsPerfect Y] [Group T] [Finite T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) (π : Y →* T)
    (hπ : Function.Surjective π) (hK : Group.IsSolvable π.ker)
    (h3 : ¬ 3 ∣ Nat.card π.ker) (hO2 : CFSG.pCore 2 Y = ⊥) (hq : ¬ IsQuasisimple Y) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ D : Subgroup Y, ∃ hD : CriticalAt p D,
      hD.frattiniKer ≤ ((sigmaOfTripleCover hT).comp π).ker := by
  set ψ := (sigmaOfTripleCover hT).comp π
  have hK'sol : Group.IsSolvable ψ.ker := ker_comp_sigma_isSolvable hT π hK
  haveI hsimple : IsSimpleGroup (Y ⧸ ψ.ker) := isSimpleGroup_quotient_ker_comp hT π hπ
  have htop : ψ.ker ≠ ⊤ := ker_comp_sigma_ne_top hT π hπ
  obtain ⟨p, hp, hpS⟩ := Sec4.Census.exists_centralizer_pCore_le (K := ψ.ker) hK'sol hq
  haveI : Fact p.Prime := ⟨hp⟩
  have hPne : CFSG.pCore p Y ≠ ⊥ := by
    intro h
    apply htop
    refine top_le_iff.mp (le_trans (fun g _ => ?_) hpS)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [h, SetLike.mem_coe, Subgroup.mem_bot] at hx
    rw [hx, one_mul, mul_one]
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hPne hO2
  have hp3 : p ≠ 3 := by
    rintro rfl
    exfalso
    have hcen := pCore_three_le_center hT π hπ h3
    have hcent : Subgroup.centralizer (CFSG.pCore 3 Y : Set Y) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_center_iff.mp (hcen hx) y).symm
    exact htop (by rw [← top_le_iff, ← hcent]; exact hpS)
  obtain ⟨D, hD⟩ := Sec4.Census.exists_criticalAt hp2 hPne
  exact ⟨p, hp, by have := hp.two_le; omega, D, hD, hD.frattiniKer_le hK'sol hpS⟩

private theorem exists_critical {Y T : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    [Group T] [Finite T] (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (π : Y →* T) (hπ : Function.Surjective π) (hK : Group.IsSolvable π.ker)
    (h3 : ¬ 3 ∣ Nat.card π.ker) (hO2 : CFSG.pCore 2 Y = ⊥) (hne : π.ker ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ D : Subgroup Y, ∃ hD : CriticalAt p D,
      hD.frattiniKer ≤ ((sigmaOfTripleCover hT).comp π).ker := by
  by_cases hq : IsQuasisimple Y
  · exact absurd (ker_eq_bot_of_isQuasisimple hT hq π hπ hK h3 hO2) hne
  · exact exists_critical_of_not_isQuasisimple hT π hπ hK h3 hO2 hq

private theorem false_of_pRank_le_two {Y T : Type} [Group Y]
    [Finite Y] [Group T] [Finite T] (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (π : Y →* T) (hπ : Function.Surjective π) {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p)
    {D : Subgroup Y} (hD : CriticalAt p D)
    (hDK : hD.frattiniKer ≤ ((sigmaOfTripleCover hT).comp π).ker)
    (hrank : CFSG.pRank p D ≤ 2) : False := by
  obtain ⟨V, _, _, _, ρ, hρ, hdim, -⟩ :=
    CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ.exists_frattiniModule
      (by omega : p ≠ 2) hD
  have hDp : IsPGroup p D := (pCore_isPGroup (p := p) (G := Y)).to_le hD.le
  have hexp : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, hD.exp x x.2, Subgroup.coe_one])
  have h1 := (class_two_small_rank_order_bounds hDp hexp hD.commutator_le_center).1 hrank
  have hfc := frattini_eq_commutator hDp hexp
  have h2 : CFSG.pRank p (D ⧸ frattini D) ≤ 2 := by
    rw [pRank_congr_mulEquiv hp.out.one_lt (QuotientGroup.quotientMulEquivOfEq hfc)]
    exact h1
  have hdim2 : Module.finrank (ZMod p) V ≤ 2 := by
    rw [← hdim]
    exact h2
  have hp5 : 5 ≤ p := by
    rcases hp.out.eq_two_or_odd' with h2' | hodd
    · omega
    · obtain ⟨k, hk⟩ := hodd
      omega
  have hψ : Function.Surjective ((sigmaOfTripleCover hT).comp π) :=
    (sigmaOfTripleCover_surjective hT).comp hπ
  refine CFSG.RankThree.PartTwo.Sec13.Res7Proof.false_of_rep_one (V := V) hp5 ρ ⊤ ?_
    (fun _ _ _ => Submodule.mem_top) CFSG.RankThree.PartTwo.Sec13.Res7Proof.altTarget_six
    ((sigmaOfTripleCover hT).comp π) hψ ?_
  · rw [finrank_top]
    exact hdim2
  · intro y hy
    have hρ1 : ρ y = 1 := by
      ext w
      simpa using hy w Submodule.mem_top
    exact MonoidHom.mem_ker.mp (hDK (hρ y hρ1))

private theorem ker_eq_bot_of_pRank_le_two {Y T : Type}
    [Group Y] [Finite Y] [Group.IsPerfect Y] [Group T] [Finite T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) (π : Y →* T)
    (hπ : Function.Surjective π) (hK : Group.IsSolvable π.ker) (h3 : ¬ 3 ∣ Nat.card π.ker)
    (hO2 : CFSG.pCore 2 Y = ⊥)
    (hrank : ∀ p : ℕ, p.Prime → 3 < p → CFSG.pRank p Y ≤ 2) : π.ker = ⊥ := by
  by_contra hne
  obtain ⟨p, hp, hp3, D, hD, hDK⟩ := exists_critical hT π hπ hK h3 hO2 hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hDr : CFSG.pRank p D ≤ 2 := by
    have h1 := Sec4.Census.pRank_le_pRank_top hp D
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h1
    exact h1.trans (hrank p hp hp3)
  exact false_of_pRank_le_two hT π hπ hp3 hD hDK hDr

theorem ker_le_pCore_two_of_pRank_le_two {Y : Type} [Group Y]
    [Finite Y] [Group.IsPerfect Y] {T : Type} [Group T] [Finite T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) (π : Y →* T)
    (hπ : Function.Surjective π) (hK : Group.IsSolvable π.ker) (h3 : ¬ 3 ∣ Nat.card π.ker)
    (hrank : ∀ p : ℕ, p.Prime → 3 < p → CFSG.pRank p Y ≤ 2) : π.ker ≤ CFSG.pCore 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pCore 2 Y
  haveI : Q.Normal := pCore_normal
  haveI hsimple : IsSimpleGroup (Y ⧸ ((sigmaOfTripleCover hT).comp π).ker) :=
    isSimpleGroup_quotient_ker_comp hT π hπ
  have hQψ : Q ≤ ((sigmaOfTripleCover hT).comp π).ker := Sec4.Census.pCore_le 2
  have hQK : Q ≤ π.ker := by
    intro x hx
    have hxψ : x ∈ ((sigmaOfTripleCover hT).comp π).ker := hQψ hx
    have hxZ : π (x : Y) ∈ Subgroup.center T := by
      rw [← sigmaOfTripleCover_ker hT]
      exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hxψ)
    have h3Z : (π (x : Y)) ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := Subgroup.center T) (x := ⟨π (x : Y), hxZ⟩)
      rw [hT.1] at h
      simpa using congrArg Subtype.val h
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := Y) : IsPGroup 2 Q) ⟨x, hx⟩
    have hk' : (x : Y) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have h2Z : (π (x : Y)) ^ 2 ^ k = 1 := by
      rw [← map_pow, hk', map_one]
    refine MonoidHom.mem_ker.mpr ?_
    have hdvd2 : orderOf (π (x : Y)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2Z
    have hdvd3 : orderOf (π (x : Y)) ∣ 3 := orderOf_dvd_of_pow_eq_one h3Z
    have hgcd : orderOf (π (x : Y)) ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd hdvd2 hdvd3
    have hcop : Nat.Coprime (2 ^ k) 3 := (by norm_num : Nat.Coprime 2 3).pow_left k
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hgcd
    exact hgcd
  set π' : Y ⧸ Q →* T := QuotientGroup.lift Q π hQK
  have hπ' : Function.Surjective π' := by
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hker' : π'.ker = π.ker.map (QuotientGroup.mk' Q) := QuotientGroup.ker_lift Q π hQK
  have hK' : Group.IsSolvable π'.ker := by
    rw [hker']
    exact Group.isSolvable_of_surjective ((QuotientGroup.mk' Q).subgroupMap_surjective π.ker)
  have h3' : ¬ 3 ∣ Nat.card π'.ker := by
    rw [hker']
    exact fun h => h3 (h.trans (Subgroup.card_map_dvd _ _))
  have hO2' : CFSG.pCore 2 (Y ⧸ Q) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hrank' : ∀ p : ℕ, p.Prime → 3 < p → CFSG.pRank p (Y ⧸ Q) ≤ 2 := by
    intro p hp hp3
    have : Fact p.Prime := ⟨hp⟩
    have hQp : ¬ p ∣ Nat.card Q := by
      obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup 2 Q).exists_card_eq
      rw [hk]
      intro h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      omega
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_quotient_eq Q hQp,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hrank p hp hp3
  have hbot := ker_eq_bot_of_pRank_le_two hT π' hπ' hK' h3' hO2' hrank'
  rw [hker', Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

theorem aschbacherSolvableCore_eq_pCore_two {X : Type} [Group X]
    [Finite X] (hX : SectionFourHyp X) [Group.IsPerfect X]
    (hT : Sec4.IsTripleCover (X ⧸ aschbacherSolvableCore 3 X) (alternatingGroup (Fin 6)))
    (hO2 : CFSG.pCore 2 X ≠ ⊥) : aschbacherSolvableCore 3 X = CFSG.pCore 2 X := by
  set θ := aschbacherSolvableCore 3 X
  obtain ⟨hθsol, -, hθ3, -, -, -, hθO⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  let π : X →* (X ⧸ θ) := QuotientGroup.mk' θ
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective θ
  have hker : π.ker = θ := QuotientGroup.ker_mk' θ
  have hK : Group.IsSolvable π.ker := by
    rw [hker]
    exact hθsol
  have h3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hker]
    exact hθ3
  have hθ2 : θ ≤ CFSG.pCore 2 X := by
    rw [← hker]
    refine ker_le_pCore_two_of_pRank_le_two hT π hπ hK h3 fun p hp hp3 => ?_
    have h1 := CFSG.RankThree.PartOne.OddCore37.pRank_le_localRank_of_le_normalizer hp hO2
      pCore_isPGroup (D := ⊤) (Subgroup.normalizer_eq_top (CFSG.pCore 2 X)).ge
    rw [pRank_congr_mulEquiv hp.one_lt Subgroup.topEquiv] at h1
    have h2 := hX.localRank_lt p hp hp3
    omega
  exact le_antisymm hθ2 (hθO 2 Nat.prime_two (by norm_num))

end CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6
