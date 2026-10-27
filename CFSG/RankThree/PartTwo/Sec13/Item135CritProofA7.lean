module

public import CFSG.RankThree.PartTwo.Sec13.Item135CritProofSetup
public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec4.T444.Step452
import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA7
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec21.Item222KLeProof
import CFSG.RankThree.PartTwo.Sec3.AlternatingSLTwoLocalRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.RankThree.PartTwo.Sec13.CritProof

open CFSG Subgroup CFSG.SectionRank.Ccomm CFSG.RankThree CFSG.RankThree.LocalRank
open CFSG.RankThree.PartTwo

section General

variable {X : Type} [Group X] [Finite X]

theorem mul_comm_of_mem_pCore_three (hbar : IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X)) :
    ∀ y ∈ pCore 3 X, ∀ x : X, y * x = x * y := by
  intro y hy x
  set θ := aschbacherSolvableCore 3 X with hθdef
  have hθ := solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hθ3 : ¬ 3 ∣ Nat.card θ := hθ.2.2.1
  set π := QuotientGroup.mk' θ with hπ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 (pCore 3 X) := pCore_isPGroup
  have hN : ((pCore 3 X).map π).Normal :=
    (CFSG.pCore_normal (p := 3) (G := X)).map _ (QuotientGroup.mk'_surjective θ)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hbar hN with htop | hcen
  · exfalso
    have hpg : IsPGroup 3 ((pCore 3 X).map π) := hP3.map π
    rw [htop] at hpg
    have hpg' : IsPGroup 3 (X ⧸ θ) := hpg.of_equiv Subgroup.topEquiv
    have : Nontrivial (X ⧸ θ) := CFSG.LocalCores.isQuasisimple_nontrivial hbar
    have : Group.IsPerfect (X ⧸ θ) := hbar.1
    have : Group.IsNilpotent (X ⧸ θ) := hpg'.isNilpotent
    exact Group.IsPerfect.not_isSolvable (X ⧸ θ) inferInstance
  · have hyc : π y ∈ center (X ⧸ θ) := hcen ⟨y, hy, rfl⟩
    set z := y * x * y⁻¹ * x⁻¹ with hz
    have hzθ : z ∈ θ := by
      rw [← QuotientGroup.eq_one_iff]
      have h1 := mem_center_iff.mp hyc (π x)
      change ((y * x * y⁻¹ * x⁻¹ : X) : X ⧸ θ) = 1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv]
      change π y * π x * (π y)⁻¹ * (π x)⁻¹ = 1
      rw [← h1]
      group
    have hzP : z ∈ pCore 3 X := by
      have h1 : x * y⁻¹ * x⁻¹ ∈ pCore 3 X :=
        (CFSG.pCore_normal (p := 3) (G := X)).conj_mem _ (inv_mem hy) x
      have : z = y * (x * y⁻¹ * x⁻¹) := by rw [hz]; group
      rw [this]
      exact mul_mem hy h1
    obtain ⟨n, hn⟩ := hP3 ⟨z, hzP⟩
    have hzn : z ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hd1 : orderOf z ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hzn
    have hd2 : orderOf z ∣ Nat.card θ := by
      rw [← Subgroup.orderOf_mk _ hzθ]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (3 ^ n) (Nat.card θ) :=
      Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
    have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
    calc y * x = z * (x * y) := by rw [hz]; group
      _ = x * y := by rw [hz1, one_mul]

theorem surj_alt7_of_equiv (e : X ⧸ aschbacherSolvableCore 3 X ≃* alternatingGroup (Fin 7)) :
    ∃ φ : X →* alternatingGroup (Fin 7), Function.Surjective φ ∧ Group.IsSolvable φ.ker ∧
      φ.ker = aschbacherSolvableCore 3 X := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _), e.surjective.comp
    (QuotientGroup.mk'_surjective _), ?_, ?_⟩
  · have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 X))).ker =
        aschbacherSolvableCore 3 X := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [hker]
    exact (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).1
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem surj_alt7_of_tripleCover
    (h : Sec4.IsTripleCover (X ⧸ aschbacherSolvableCore 3 X) (alternatingGroup (Fin 7))) :
    ∃ φ : X →* alternatingGroup (Fin 7), Function.Surjective φ ∧ Group.IsSolvable φ.ker ∧
      φ.ker = (center (X ⧸ aschbacherSolvableCore 3 X)).comap
        (QuotientGroup.mk' (aschbacherSolvableCore 3 X)) := by
  obtain ⟨-, ⟨e⟩⟩ := h
  set θ := aschbacherSolvableCore 3 X
  set ψ : X →* alternatingGroup (Fin 7) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (center (X ⧸ θ))).comp (QuotientGroup.mk' θ))
  have hψ : Function.Surjective ψ :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hker : ψ.ker = (center (X ⧸ θ)).comap (QuotientGroup.mk' θ) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    change e (QuotientGroup.mk' (center (X ⧸ θ)) (QuotientGroup.mk' θ x)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨ψ, hψ, ?_, hker⟩
  rw [hker]
  have hθs : Group.IsSolvable θ :=
    (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).1
  have hZs : Group.IsSolvable (center (X ⧸ θ)) := Group.isSolvable_of_comm fun a b =>
    Subtype.ext ((mem_center_iff.mp a.2) b).symm
  exact Sec4.isSolvable_comap_mk' hθs hZs

theorem exists_critical_of_alt7 [Group.IsPerfect X]
    (hq : ¬ IsQuasisimple X) (hO2 : pCore 2 X = ⊥)
    (hO3 : ∀ y ∈ pCore 3 X, ∀ x : X, y * x = x * y)
    (φ : X →* alternatingGroup (Fin 7)) (hφ : Function.Surjective φ)
    (hK : Group.IsSolvable φ.ker) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ (_ : Fact p.Prime) (C : Subgroup (pCore p X)),
      IsThompsonCritical C ∧ C ≠ ⊥ ∧
      Sec4.Census.CriticalAt p (omegaOneCore p C) ∧ (omegaOneCore p C).Characteristic ∧
      (∃ y ∈ pCore p X, ∃ x : X, y * x ≠ x * y) ∧
      centralizer (pCore p X : Set X) ≤ φ.ker ∧ 3 ≤ CFSG.pRank p (omegaOneCore p C) := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  set e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have : IsSimpleGroup (X ⧸ φ.ker) := e.isSimpleGroup
  set E : Subgroup (X ⧸ φ.ker) := Sec4.Res423Two.eNine7.map e.symm.toMonoidHom with hEdef
  have hE9 : Nat.card E = 9 := by
    rw [hEdef, Subgroup.card_map_of_injective e.symm.injective]
    exact Sec4.Res423Two.card_eNine7
  have hE : Monoid.exponent E ∣ 3 := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp g.2
    obtain ⟨i, j, hij⟩ : ((x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ∈
        KFacts.KP2.eNine := Subgroup.mem_subgroupOf.mp hx
    have hx3 : x ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hij, KFacts.KP2.eNineF_pow_three i j]
      rfl
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hxg, ← map_pow, hx3, map_one]
    rfl
  exact exists_critical_rank_three hK hq hO2 hO3 hE hE9

end General

section Center

variable {X : Type} [Group X] [Finite X]

theorem not_dvd_card_center_quotient_oddCore {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2) :
    ¬ q ∣ Nat.card (center (X ⧸ CFSG.oddCore X)) := by
  intro hdvd
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := center (X ⧸ CFSG.oddCore X)) q hdvd
  set O := CFSG.oddCore X with hOdef
  set π := QuotientGroup.mk' O with hπ
  have hwq : orderOf (w : X ⧸ O) = q := by rw [Subgroup.orderOf_coe]; exact hw
  set N : Subgroup X := (Subgroup.zpowers (w : X ⧸ O)).comap π with hNdef
  have hZn : (Subgroup.zpowers (w : X ⧸ O)).Normal := by
    constructor
    intro n hn g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hcomm : g * (w : X ⧸ O) ^ k = (w : X ⧸ O) ^ k * g :=
      (Commute.zpow_right ((mem_center_iff.mp w.2 g)) k).eq
    rw [hcomm, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k
  have hNn : N.Normal := hZn.comap π
  have hO : Odd (Nat.card O) := CFSG.ABGDGroups.odd_card_oddCore X
  have hNodd : Odd (Nat.card N) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 (even_iff_two_dvd.mp hev)
    have hn2 : orderOf (n : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hn
    have hnZ : π n ∈ Subgroup.zpowers (w : X ⧸ O) := n.2
    have hd1 : orderOf (π n) ∣ 2 := by
      rw [← hn2]
      exact orderOf_map_dvd π (n : X)
    have hd2 : orderOf (π n) ∣ q := by
      rw [← hwq, ← Nat.card_zpowers (w : X ⧸ O)]
      rw [← Subgroup.orderOf_mk _ hnZ]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime 2 q :=
      (Nat.coprime_primes Nat.prime_two hq.out).mpr (Ne.symm hq2)
    have h1 : π n = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
    have hnO : (n : X) ∈ O := (QuotientGroup.eq_one_iff _).mp h1
    have hd3 : orderOf (n : X) ∣ Nat.card O := by
      rw [← Subgroup.orderOf_mk _ hnO]
      exact orderOf_dvd_natCard _
    rw [hn2] at hd3
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr hd3)
  have hNO : N ≤ O := le_sSup ⟨hNn, hNodd⟩
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective O (w : X ⧸ O)
  have hxN : x ∈ N := by
    rw [hNdef, Subgroup.mem_comap, hx]
    exact Subgroup.mem_zpowers _
  have hw1 : (w : X ⧸ O) = 1 := by
    rw [← hx]
    exact (QuotientGroup.eq_one_iff x).mpr (hNO hxN)
  rw [hw1, orderOf_one] at hwq
  exact hq.out.one_lt.ne hwq

theorem center_quotient_oddCore_of_alt7 [Group.IsPerfect X]
    (hO : IsQuasisimple (X ⧸ CFSG.oddCore X)) (φ : X →* alternatingGroup (Fin 7))
    (hφ : Function.Surjective φ) (hK : Group.IsSolvable φ.ker) :
    (center (X ⧸ CFSG.oddCore X)).comap (QuotientGroup.mk' (CFSG.oddCore X)) = φ.ker ∧
      Nonempty ((X ⧸ CFSG.oddCore X) ⧸ center (X ⧸ CFSG.oddCore X) ≃*
        alternatingGroup (Fin 7)) ∧
      Nat.card (center (X ⧸ CFSG.oddCore X)) ≤ 2 := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  set e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have : IsSimpleGroup (X ⧸ φ.ker) := e.isSimpleGroup
  set O := CFSG.oddCore X with hOdef
  set π := QuotientGroup.mk' O with hπ
  set Z := (center (X ⧸ O)).comap π with hZdef
  have hOK : O ≤ φ.ker := by
    have hmap : (O.map (QuotientGroup.mk' φ.ker)).Normal :=
      (inferInstance : O.Normal).map _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.map (QuotientGroup.mk' φ.ker)) with
      h | h
    · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    · exfalso
      have hdvd : Nat.card (O.map (QuotientGroup.mk' φ.ker)) ∣ Nat.card O :=
        Subgroup.card_dvd_of_surjective ((QuotientGroup.mk' φ.ker).subgroupMap_surjective O)
      rw [h, Subgroup.card_top, Nat.card_congr e.toEquiv] at hdvd
      have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
        rw [CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin]
        decide
      rw [h7] at hdvd
      have hO' : Odd (Nat.card O) := CFSG.ABGDGroups.odd_card_oddCore X
      exact (Nat.not_even_iff_odd.mpr (hO'.of_dvd_nat hdvd)) (by decide)
  have hOs : Group.IsSolvable O :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hOK)
  have hZs : Group.IsSolvable (center (X ⧸ O)) := Group.isSolvable_of_comm fun a b =>
    Subtype.ext ((mem_center_iff.mp a.2) b).symm
  have hZsol : Group.IsSolvable Z := Sec4.isSolvable_comap_mk' hOs hZs
  have hZn : Z.Normal := (inferInstance : (center (X ⧸ O)).Normal).comap π
  have hZK : Z ≤ φ.ker := Sec4.Census.le_of_isSolvable_of_normal hZn hZsol
  have hKZ : φ.ker ≤ Z := by
    have hmap : (φ.ker.map π).Normal :=
      (inferInstance : φ.ker.Normal).map _ (QuotientGroup.mk'_surjective _)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hO hmap with h | h
    · exfalso
      have hs : Group.IsSolvable (φ.ker.map π) :=
        Group.isSolvable_of_surjective (π.subgroupMap_surjective φ.ker)
      rw [h] at hs
      have hsol : Group.IsSolvable (X ⧸ O) :=
        Group.isSolvable_of_surjective
          (f := ((Subgroup.topEquiv : (⊤ : Subgroup (X ⧸ O)) ≃* (X ⧸ O)) :
            (⊤ : Subgroup (X ⧸ O)) →* (X ⧸ O))) Subgroup.topEquiv.surjective
      have : Nontrivial (X ⧸ O) := CFSG.LocalCores.isQuasisimple_nontrivial hO
      have : Group.IsPerfect (X ⧸ O) := hO.1
      exact Group.IsPerfect.not_isSolvable (X ⧸ O) hsol
    · intro x hx
      exact h ⟨x, hx, rfl⟩
  have hZeq : Z = φ.ker := le_antisymm hZK hKZ
  have hOZ : O ≤ Z := hOK.trans hKZ
  have hmapZ : Z.map π = center (X ⧸ O) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O) _
  have e' : (X ⧸ O) ⧸ center (X ⧸ O) ≃* alternatingGroup (Fin 7) :=
    ((QuotientGroup.quotientMulEquivOfEq hmapZ.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient O Z hOZ)).trans
      ((QuotientGroup.quotientMulEquivOfEq hZeq).trans e)
  refine ⟨hZeq, ⟨e'⟩, ?_⟩
  have h6 := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hO e'
  rw [(CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_seven).2] at h6
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := not_dvd_card_center_quotient_oddCore (X := X) (q := 3) (by norm_num)
  have hpos : 0 < Nat.card (center (X ⧸ O)) := Nat.card_pos
  have hle : Nat.card (center (X ⧸ O)) ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  interval_cases h : Nat.card (center (X ⧸ O)) <;> simp_all

end Center

section Sec13

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

omit [Finite G] in
theorem not_isQuasisimple_of_pCore_two (hnq : ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L))
    (hO2 : CFSG.pCore 2 L = ⊥) : ¬ IsQuasisimple L := fun hq =>
  hnq (CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientBot (G := L)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hO2).symm) hq)

theorem pRank_map_subtype {p : ℕ} (hp : 1 < p) (D : Subgroup L) :
    CFSG.pRank p (D.map L.subtype) = CFSG.pRank p D := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp
    (D.equivMapOfInjective _ L.subtype_injective).symm

omit [Finite G] in
theorem centralizer_le_subgroupOf (D : Subgroup L) :
    centralizer (D : Set L) ≤
      (centralizer ((D.map L.subtype : Subgroup G) : Set G)).subgroupOf L := by
  intro x hx
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  rintro _ ⟨d, hd, rfl⟩
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx d hd)

omit [Finite G] in
theorem mem_normalizer_map_of_characteristic {D : Subgroup L} [hD : D.Characteristic] {g : G}
    (hg : g ∈ normalizer (L : Set G)) :
    g ∈ normalizer ((D.map L.subtype : Subgroup G) : Set G) := by
  set σ : MulAut L := L.normalizerMonoidHom ⟨g, hg⟩ with hσ
  have hσD : D.map σ.toMonoidHom = D := (characteristic_iff_map_eq.mp hD) σ
  have hσapp : ∀ y : L, ((σ y : L) : G) = g * y * g⁻¹ := fun y => rfl
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨d, hd, rfl⟩
    have h1 : σ d ∈ D := by
      rw [← hσD]
      exact ⟨d, hd, rfl⟩
    exact ⟨σ d, h1, by rw [Subgroup.subtype_apply, hσapp]; rfl⟩
  · rintro ⟨d, hd, hdh⟩
    have h1 : σ.symm d ∈ D := by
      have := (characteristic_iff_map_eq.mp hD) σ.symm
      rw [← this]
      exact ⟨d, hd, rfl⟩
    refine ⟨σ.symm d, h1, ?_⟩
    have h2 : ((σ (σ.symm d) : L) : G) = g * ((σ.symm d : L) : G) * g⁻¹ := hσapp _
    rw [MulEquiv.apply_symm_apply] at h2
    rw [Subgroup.subtype_apply] at hdh ⊢
    have h3 : g * ((σ.symm d : L) : G) * g⁻¹ = g * h * g⁻¹ := by rw [← h2, hdh]
    have h4 := congrArg (fun y => g⁻¹ * y * g) h3
    simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using h4

theorem exists_critical_sec13 (hD : Sec13Data G A c L)
    (hnq : ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L)) (hO2 : CFSG.pCore 2 L = ⊥)
    (φ : L →* alternatingGroup (Fin 7)) (hφ : Function.Surjective φ)
    (hK : Group.IsSolvable φ.ker) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ (_ : Fact p.Prime) (C : Subgroup (pCore p L)),
      IsThompsonCritical C ∧ C ≠ ⊥ ∧
      Sec4.Census.CriticalAt p (omegaOneCore p C) ∧ (omegaOneCore p C).Characteristic ∧
      (∃ y ∈ pCore p L, ∃ x : L, y * x ≠ x * y) ∧ 3 ≤ CFSG.pRank p (omegaOneCore p C) ∧
      Odd (Nat.card (centralizer (((omegaOneCore p C).map L.subtype : Subgroup G) : Set G))) ∧
      centralizer ((omegaOneCore p C : Subgroup L) : Set L) ≤ CFSG.oddCore L := by
  have hLc := hD.mem_thetaComponentsAt
  have hperf : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hbar : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  have hnq' : ¬ IsQuasisimple L := not_isQuasisimple_of_pCore_two hnq hO2
  obtain ⟨p, hp, hp3, hpF, C, hC, hCne, hDc, hDch, hmove, -, hrank⟩ :=
    exists_critical_of_alt7 hnq' hO2 (mul_comm_of_mem_pCore_three hbar) φ hφ hK
  have hrankG : 3 ≤ CFSG.pRank p ((omegaOneCore p C).map L.subtype) := by
    rw [pRank_map_subtype hp.one_lt]
    exact hrank
  have hodd := odd_card_centralizer_of_three_le_pRank hp (by omega)
    (hD.localRank_lt p hp hp3) hrankG
  refine ⟨p, hp, hp3, hpF, C, hC, hCne, hDc, hDch, hmove, hrank, hodd, ?_⟩
  have hle := centralizer_subgroupOf_le_oddCore (Y := L) (fun l hl =>
    mem_normalizer_map_of_characteristic (hD := hDch) (Subgroup.le_normalizer hl)) hodd
  exact (centralizer_le_subgroupOf _).trans hle

end Sec13

end CFSG.RankThree.PartTwo.Sec13.CritProof

namespace CFSG.RankThree.PartTwo.Sec13.CritProof

open CFSG Subgroup CFSG.SectionRank.Ccomm CFSG.RankThree CFSG.RankThree.LocalRank
open CFSG.RankThree.PartTwo

structure Crit135 {G : Type} [Group G] [Finite G] (L : Subgroup G) (p : ℕ)
    (C : Subgroup (CFSG.pCore p L)) : Prop where
  prime : p.Prime
  three_lt : 3 < p
  isThompsonCritical : IsThompsonCritical C
  ne_bot : C ≠ ⊥
  criticalAt : Sec4.Census.CriticalAt p (omegaOneCore p C)
  characteristic : (omegaOneCore p C).Characteristic
  not_commute : ∃ y ∈ CFSG.pCore p L, ∃ x : L, y * x ≠ x * y
  three_le_pRank : 3 ≤ CFSG.pRank p (omegaOneCore p C)
  odd_card_centralizer :
    Odd (Nat.card (centralizer (((omegaOneCore p C).map L.subtype : Subgroup G) : Set G)))
  centralizer_le_oddCore :
    centralizer ((omegaOneCore p C : Subgroup L) : Set L) ≤ CFSG.oddCore L
  pRank_inf_centralizer_le : ∀ u : G, u ≠ 1 → (∃ k : ℕ, u ^ 2 ^ k = 1) →
    CFSG.pRank p ((omegaOneCore p C).map L.subtype ⊓ centralizer {u} : Subgroup G) ≤ 2
  card_le_eight : ∀ E : Subgroup G,
    E ≤ normalizer ((((omegaOneCore p C).map L.subtype : Subgroup G)) : Set G) →
    CFSG.Assembly.IsElemAbelian 2 E → Nat.card E ≤ 8
  not_faithful_A4SL23 : ∀ X : Subgroup G,
    X ≤ normalizer ((((omegaOneCore p C).map L.subtype : Subgroup G)) : Set G) →
    Nonempty (X ≃* alternatingGroup (Fin 4) × Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) →
    X ⊓ centralizer ((((omegaOneCore p C).map L.subtype : Subgroup G)) : Set G) ≠ ⊥

structure OddCoreAlt7 {G : Type} [Group G] (L : Subgroup G) (Z : Subgroup L) : Prop where
  isQuasisimple : IsQuasisimple (L ⧸ CFSG.oddCore L)
  comap_center : (center (L ⧸ CFSG.oddCore L)).comap (QuotientGroup.mk' (CFSG.oddCore L)) = Z
  quotient_center :
    Nonempty ((L ⧸ CFSG.oddCore L) ⧸ center (L ⧸ CFSG.oddCore L) ≃* alternatingGroup (Fin 7))
  card_center_le : Nat.card (center (L ⧸ CFSG.oddCore L)) ≤ 2

structure Crit135K {G : Type} [Group G] [Finite G] (c : G) (L K D : Subgroup G) : Prop where
  ne : K ≠ L
  le_normalizer_left : K ≤ normalizer (L : Set G)
  le_normalizer_right : L ≤ normalizer (K : Set G)
  commutator_mem_theta : ∀ x ∈ K, ∀ y ∈ L, x * y * x⁻¹ * y⁻¹ ∈
    inSubgroup (aschbacherSolvableCore 3) (centralizer ({c} : Set G))
  commutator_le_oddCore : ⁅K, L⁆ ≤ (CFSG.oddCore L).map L.subtype
  sup_le_normalizer : K ⊔ L ≤ normalizer (D : Set G)
  centralizer_le_oddCore : (centralizer (D : Set G)).subgroupOf (K ⊔ L) ≤ CFSG.oddCore ↥(K ⊔ L)

section Bundle

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

omit [Finite G] in
theorem exists_pow_orderOf_eq_two {u : G} (hu : u ≠ 1) (hk : ∃ k : ℕ, u ^ 2 ^ k = 1) :
    ∃ n : ℕ, orderOf (u ^ n) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (exists_orderOf_eq_prime_pow_iff (p := 2)).mpr hk
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hm
    exact hu hm
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine ⟨2 ^ m', orderOf_eq_prime ?_ ?_⟩
  · rw [← pow_mul, ← pow_succ, ← hm, pow_orderOf_eq_one]
  · intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hm] at this
    have h2 := Nat.le_of_dvd (by positivity) this
    rw [pow_succ] at h2
    have : 0 < 2 ^ m' := by positivity
    omega

theorem pRank_inf_centralizer_le_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hloc : CFSG.Assembly.RankThreeEven.localRank p G < 3) (D : Subgroup G) {u : G}
    (hu : u ≠ 1) (hk : ∃ k : ℕ, u ^ 2 ^ k = 1) :
    CFSG.pRank p (D ⊓ centralizer {u} : Subgroup G) ≤ 2 := by
  obtain ⟨n, hn⟩ := exists_pow_orderOf_eq_two hu hk
  have hcomm : ∀ h ∈ (D ⊓ centralizer {u} : Subgroup G), h * u ^ n = u ^ n * h := by
    intro h hh
    have h1 : Commute h u := Subgroup.mem_centralizer_singleton_iff.mp hh.2
    exact (Commute.pow_right h1 n).eq
  have := Sec4.Census.pRank_le_localRank_of_centralizes hp hp2 hn hcomm
  omega

theorem exists_crit135 (hD : Sec13Data G A c L)
    (hnq : ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L)) (hO2 : CFSG.pCore 2 L = ⊥)
    (φ : L →* alternatingGroup (Fin 7)) (hφ : Function.Surjective φ)
    (hK : Group.IsSolvable φ.ker) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (C : Subgroup (CFSG.pCore p L)), Crit135 L p C := by
  obtain ⟨p, hp, hp3, hpF, C, hC, hCne, hDc, hDch, hmove, hrank, hodd, hcen⟩ :=
    exists_critical_sec13 hD hnq hO2 φ hφ hK
  have hloc : ∀ u : G, u ≠ 1 → (∃ k : ℕ, u ^ 2 ^ k = 1) →
      CFSG.pRank p ((omegaOneCore p C).map L.subtype ⊓ centralizer {u} : Subgroup G) ≤ 2 :=
    fun u hu hk => pRank_inf_centralizer_le_two hp (by omega) (hD.localRank_lt p hp hp3) _ hu hk
  have hDp : IsPGroup p ((omegaOneCore p C).map L.subtype) :=
    ((CFSG.pCore_isPGroup (p := p) (G := L)).to_le hDc.le).map L.subtype
  have hexp : ∀ x ∈ (omegaOneCore p C).map L.subtype, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.subtype_apply, ← Subgroup.coe_pow, hDc.exp x hx, Subgroup.coe_one]
  have hcl : ∀ a ∈ (omegaOneCore p C).map L.subtype, ∀ b ∈ (omegaOneCore p C).map L.subtype,
      ∀ d ∈ (omegaOneCore p C).map L.subtype,
        a * b * a⁻¹ * b⁻¹ * d = d * (a * b * a⁻¹ * b⁻¹) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩
    have h := (hDc.comm a ha b (hDc.le hb)).2 d hd
    rw [commutatorElement_def] at h
    exact congrArg Subtype.val h
  refine ⟨p, hpF, C, hp, hp3, hC, hCne, hDc, hDch, hmove, hrank, hodd, hcen, hloc,
    fun E hEN hE => card_le_eight_of_isElemAbelian (by omega) hDp hexp hcl hodd hloc hEN hE, ?_⟩
  intro X hXN hX hfaith
  have h39 := Sec3.rank3II_3_9_of_le hp hp3 hDp hXN hX hfaith
  have := hD.localRank_lt p hp hp3
  omega

theorem oddCoreAlt7_of [Group.IsPerfect L]
    (hO : IsQuasisimple (L ⧸ CFSG.oddCore L)) (φ : L →* alternatingGroup (Fin 7))
    (hφ : Function.Surjective φ) (hK : Group.IsSolvable φ.ker) : OddCoreAlt7 L φ.ker := by
  obtain ⟨h1, h2, h3⟩ := center_quotient_oddCore_of_alt7 hO φ hφ hK
  exact ⟨hO, h1, h2, h3⟩

theorem oddCore_characteristic' (X : Type*) [Group X] [Finite X] :
    (CFSG.oddCore X).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro σ
  have hN : ((CFSG.oddCore X).map σ.toMonoidHom).Normal :=
    (inferInstance : (CFSG.oddCore X).Normal).map _ σ.surjective
  refine le_sSup ⟨hN, ?_⟩
  rw [Subgroup.card_map_of_injective σ.injective]
  exact CFSG.ABGDGroups.odd_card_oddCore X

theorem commutator_le_oddCore_of_ne {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 c)
    (hL : L ∈ thetaComponentsAt 3 c) (hKL : K ≠ L) (hO : IsQuasisimple (L ⧸ CFSG.oddCore L)) :
    ⁅K, L⁆ ≤ (CFSG.oddCore L).map L.subtype := by
  set N := (CFSG.oddCore L).map L.subtype with hNdef
  have : (CFSG.oddCore L).Characteristic := oddCore_characteristic' L
  have hLN : L ≤ normalizer (N : Set G) := Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.oddCore L))
  have hKNL : K ≤ normalizer (L : Set G) := fun k hk =>
    Sec21.mem_normalizer_of_mem_thetaComponentsAt hK hL hk
  have hKN : K ≤ normalizer (N : Set G) := hKNL.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.oddCore L))
  have hKLθ : ⁅K, L⁆ ≤ (aschbacherSolvableCore 3 L).map L.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have h1 := Sec10.commutator_mem_theta_of_ne hK hL hKL hx hy
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKNL hx) y).mp hy) (L.inv_mem hy)
    have h3 := Sec6.theta_eq_inf_of_mem_thetaComponentsAt hL
    rw [commutatorElement_def]
    change _ ∈ inSubgroup (aschbacherSolvableCore 3) L
    rw [h3]
    exact ⟨h2, h1⟩
  have hθL : ⁅(aschbacherSolvableCore 3 L).map L.subtype, L⁆ ≤ N := by
    have hθs : Group.IsSolvable (aschbacherSolvableCore 3 L) :=
      (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).1
    have hθc : (aschbacherSolvableCore 3 L).Characteristic :=
      (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.1
    set π := QuotientGroup.mk' (CFSG.oddCore L) with hπ
    have hnorm : ((aschbacherSolvableCore 3 L).map π).Normal := by
      have := hθc
      exact (inferInstance : (aschbacherSolvableCore 3 L).Normal).map _
        (QuotientGroup.mk'_surjective _)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hO hnorm with htop | hcen
    · exfalso
      have hs : Group.IsSolvable ((aschbacherSolvableCore 3 L).map π) :=
        Group.isSolvable_of_surjective (π.subgroupMap_surjective _)
      rw [htop] at hs
      have hsol : Group.IsSolvable (L ⧸ CFSG.oddCore L) :=
        Group.isSolvable_of_surjective
          (f := ((Subgroup.topEquiv : (⊤ : Subgroup (L ⧸ CFSG.oddCore L)) ≃*
            (L ⧸ CFSG.oddCore L)) : (⊤ : Subgroup (L ⧸ CFSG.oddCore L)) →* (L ⧸ CFSG.oddCore L)))
          Subgroup.topEquiv.surjective
      have : Nontrivial (L ⧸ CFSG.oddCore L) := CFSG.LocalCores.isQuasisimple_nontrivial hO
      have : Group.IsPerfect (L ⧸ CFSG.oddCore L) := hO.1
      exact Group.IsPerfect.not_isSolvable (L ⧸ CFSG.oddCore L) hsol
    · rw [Subgroup.commutator_le]
      rintro _ ⟨t, ht, rfl⟩ y hy
      have hc : π t ∈ center (L ⧸ CFSG.oddCore L) := hcen ⟨t, ht, rfl⟩
      have h1 := Subgroup.mem_center_iff.mp hc (π ⟨y, hy⟩)
      rw [← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at h1
      refine ⟨t * ⟨y, hy⟩ * t⁻¹ * (⟨y, hy⟩ : L)⁻¹, ?_, by
        rw [commutatorElement_def]
        simp⟩
      have e2 : (t * ⟨y, hy⟩ * t⁻¹ * (⟨y, hy⟩ : L)⁻¹ : L) =
          ((⟨y, hy⟩ : L) * t) * ((⟨y, hy⟩ * t)⁻¹ * (t * ⟨y, hy⟩)) * ((⟨y, hy⟩ : L) * t)⁻¹ := by
        group
      rw [e2]
      exact (inferInstance : (CFSG.oddCore L).Normal).conj_mem _ h1 _
  have h1 : ⁅⁅K, L⁆, L⁆ ≤ N := (Subgroup.commutator_mono hKLθ le_rfl).trans hθL
  have h2 : ⁅⁅L, K⁆, L⁆ ≤ N := by
    rw [Subgroup.commutator_comm L K]
    exact h1
  have h3 := Sec6.three_subgroups_mod hLN hKN hLN h2 h1
  have hperf : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hL
  rw [Sec6.commutator_self_eq_of_isPerfect hperf] at h3
  rw [Subgroup.commutator_comm]
  exact h3

theorem crit135K_of (hD : Sec13Data G A c L) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 c)
    (hKL : K ≠ L) (hO : IsQuasisimple (L ⧸ CFSG.oddCore L)) {D : Subgroup L} [D.Characteristic]
    (hodd : Odd (Nat.card (centralizer ((D.map L.subtype : Subgroup G) : Set G)))) :
    Crit135K c L K (D.map L.subtype) := by
  have hL := hD.mem_thetaComponentsAt
  have hKN : K ≤ normalizer (L : Set G) := fun k hk =>
    Sec21.mem_normalizer_of_mem_thetaComponentsAt hK hL hk
  have hLN : L ≤ normalizer (K : Set G) := fun l hl =>
    Sec21.mem_normalizer_of_mem_thetaComponentsAt hL hK hl
  have hsup : K ⊔ L ≤ normalizer (((D.map L.subtype : Subgroup G)) : Set G) :=
    sup_le (fun k hk => mem_normalizer_map_of_characteristic (hKN hk))
      (fun l hl => mem_normalizer_map_of_characteristic (Subgroup.le_normalizer hl))
  exact ⟨hKL, hKN, hLN, fun x hx y hy => Sec10.commutator_mem_theta_of_ne hK hL hKL hx hy,
    commutator_le_oddCore_of_ne hK hL hKL hO, hsup, centralizer_subgroupOf_le_oddCore hsup hodd⟩

end Bundle

end CFSG.RankThree.PartTwo.Sec13.CritProof

namespace CFSG.RankThree.PartTwo.Sec13.CritProof

open CFSG Subgroup CFSG.RankThree CFSG.RankThree.LocalRank

theorem ne_of_tripleCover {G : Type} [Group G] {K L : Subgroup G}
    (hK : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)))
    (hL : Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7))) :
    K ≠ L := by
  rintro rfl
  obtain ⟨-, ⟨e6⟩⟩ := hK
  obtain ⟨-, ⟨e7⟩⟩ := hL
  have h := Nat.card_congr (e6.symm.trans e7).toEquiv
  rw [CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin,
    CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin] at h
  revert h
  decide

end CFSG.RankThree.PartTwo.Sec13.CritProof
