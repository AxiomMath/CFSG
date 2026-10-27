module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofExcl
import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofTools
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiag
import CFSG.RankThree.PartTwo.Sec15.Sylow155NODeg
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofTripleA6

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Ronan155W315

variable {G : Type} [Group G] [Finite G]

open Proof152ConfA

theorem exists_mem_not_mem_thetaQuotCentralizer_of_five {A X : Subgroup G}
    (hAF : A ∈ partTwoF G) (hA : Late.IsE27 A) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (e : ↥X ⧸ aschbacherSolvableCore 3 ↥X ≃* alternatingGroup (Fin 5)) :
    ∃ y ∈ A, y ∈ X ∧ y ∉ Sec4.thetaQuotCentralizer X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hXs : IsSimpleGroup (↥X ⧸ aschbacherSolvableCore 3 ↥X) := e.isSimpleGroup
  have hX60 : Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) = 60 := Proof15Res8Diag.card_five e
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1
  set φ : ↥A →* MulAut ↥X := X.normalizerMonoidHom.comp (Subgroup.inclusion hAX) with hφ
  have hS : IsPGroup 3 φ.range := by
    rw [MonoidHom.range_eq_map]
    exact (hA.isPGroup.of_equiv Subgroup.topEquiv.symm).map φ
  obtain ⟨R, hR⟩ := exists_sylow_three_fixed hS
  have hRcard : Nat.card (R : Subgroup ↥X) = 3 := by
    rw [Sylow.card_eq_multiplicity]
    have hX : Nat.card ↥X = 60 * Nat.card θ := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup θ
      rwa [hX60] at this
    have h60 : Nat.factorization 60 3 = 1 := by
      rw [show (60 : ℕ) = 3 * 20 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [hX, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply, h60,
      Nat.factorization_eq_zero_of_not_dvd hθ3, add_zero, pow_one]
  have hRnt : Nontrivial (R : Subgroup ↥X) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hRcard]
    norm_num
  obtain ⟨⟨r, hrR⟩, hr1⟩ := exists_ne (1 : (R : Subgroup ↥X))
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hrord : orderOf r = 3 := by
    have h := orderOf_dvd_natCard (⟨r, hrR⟩ : (R : Subgroup ↥X))
    rw [hRcard, Subgroup.orderOf_mk] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hr1'
    · exact h1
  have hRz : (R : Subgroup ↥X) = Subgroup.zpowers r := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hrR) ?_).symm
    rw [Nat.card_zpowers, hrord, hRcard]
  have hrA : ∀ a ∈ A, a * (r : G) * a⁻¹ = r := by
    intro a ha
    have hσ : (φ ⟨a, ha⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨a, ha⟩ : ↥A) ^ 3 = 1 := Subtype.ext (hA.1.2 a ha)
      rw [this, map_one]
    have hmem : φ ⟨a, ha⟩ r ∈ Subgroup.zpowers r := by
      rw [← hRz, ← hR (φ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩]
      exact ⟨r, hrR, rfl⟩
    have h := eq_of_pow_three_eq_one hσ hrord hmem
    have h' := congrArg Subtype.val h
    rwa [hφ, MonoidHom.comp_apply, Sec4.normalizerMonoidHom_apply_coe] at h'
  have hr3 : (r : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hrord, pow_orderOf_eq_one, Subgroup.coe_one]
  have hrAm : (r : G) ∈ A := by
    refine mem_of_mem_partTwoF hAF hr3 fun a ha => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a * (r : G) = a * r * a⁻¹ * a := by group
      _ = r * a := by rw [hrA a ha]
  have hrθ : r ∉ θ := by
    intro ht
    have h := orderOf_dvd_natCard (⟨r, ht⟩ : θ)
    rw [Subgroup.orderOf_mk, hrord] at h
    exact hθ3 h
  refine ⟨r, hrAm, r.2, fun hrC => hrθ ?_⟩
  have hZ := center_theta_quot_eq_bot hXs hX60
  have hcen : (QuotientGroup.mk' θ r : ↥X ⧸ θ) ∈ Subgroup.center (↥X ⧸ θ) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective θ q
    obtain ⟨-, hl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hrC
    obtain ⟨t, ht, hte⟩ := hl l l.2
    have hte' : (t : G) = (l : G)⁻¹ * ((r : G) * l * (r : G)⁻¹) := hte
    have h1 : (QuotientGroup.mk' θ l : ↥X ⧸ θ) = QuotientGroup.mk' θ (r * l * r⁻¹) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have : l⁻¹ * (r * l * r⁻¹) = t := Subtype.ext (by rw [hte']; simp)
      rw [this]
      exact ht
    rw [map_mul, map_mul, map_inv] at h1
    calc QuotientGroup.mk' θ l * QuotientGroup.mk' θ r =
        QuotientGroup.mk' θ r * QuotientGroup.mk' θ l * (QuotientGroup.mk' θ r)⁻¹ *
          QuotientGroup.mk' θ r := by rw [← h1]
      _ = QuotientGroup.mk' θ r * QuotientGroup.mk' θ l := by group
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  exact hcen

private theorem conj_injective_six {T : Type*} [Group T] (φ : T ≃* alternatingGroup (Fin 6)) :
    Function.Injective (MulAut.conj : T →* MulAut T) := by
  intro s t hst
  have hc : s⁻¹ * t ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun ψ : MulAut T => ψ g) hst
    simp only [MulAut.conj_apply] at h1
    calc g * (s⁻¹ * t) = s⁻¹ * (s * g * s⁻¹) * t := by group
      _ = s⁻¹ * (t * g * t⁻¹) * t := by rw [h1]
      _ = s⁻¹ * t * g := by group
  rw [Proof15Res8Diag.center_eq_bot_six φ, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc

private theorem centerQuotientHom_apply_mk {A X : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (a : ↥A) (x : ↥X) :
    ComponentClassification.PerfectAutomorphisms.centerQuotientHom
        (↥X ⧸ aschbacherSolvableCore 3 ↥X)
        (((Sec4.thetaQuotMulAut X).comp (X.normalizerMonoidHom.comp (Subgroup.inclusion hAX))) a)
        (QuotientGroup.mk' (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X))
          (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) x)) =
      QuotientGroup.mk' (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X))
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)
          ⟨(a : G) * x * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hAX a.2) x).mp x.2⟩) := by
  have h := ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk
    (((Sec4.thetaQuotMulAut X).comp (X.normalizerMonoidHom.comp (Subgroup.inclusion hAX))) a)
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) x)
  refine h.trans ?_
  congr 1

theorem card_range_le_three_of_tripleCover {A X : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : Late.IsE27 A) (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hΔ : X = delta A LB X)
    (hXp : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (htc : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6))) :
    Nat.card ((Sec4.thetaQuotMulAut X).comp
      (X.normalizerMonoidHom.comp (Subgroup.inclusion hAX))).range ≤ 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  set ρ := (Sec4.thetaQuotMulAut X).comp (X.normalizerMonoidHom.comp (Subgroup.inclusion hAX))
    with hρ
  have hR3 : IsPGroup 3 ρ.range := by
    rw [MonoidHom.range_eq_map]
    exact (hA.isPGroup.of_equiv Subgroup.topEquiv.symm).map ρ
  have hR9 := Proof15Res8Diag.card_le_nine_of_mulAut_tripleCover hXp htc ρ.range hR3
  obtain ⟨k, hk⟩ := hR3.exists_card_eq
  by_contra hgt
  rw [not_le] at hgt
  have h9 : Nat.card ρ.range = 9 := by
    rcases k with _ | _ | _ | k
    · have h1 : Nat.card ρ.range = 1 := by rw [hk]; norm_num
      omega
    · have h1 : Nat.card ρ.range = 3 := by rw [hk]; norm_num
      omega
    · rw [hk]
      norm_num
    · exfalso
      have h1 : 3 ^ 3 ≤ 3 ^ (k + 1 + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← hk] at h1
      omega
  obtain ⟨hZ3, ⟨φ⟩⟩ := htc
  set Q := ↥X ⧸ θ with hQ
  set Z := Subgroup.center Q with hZ
  set κ := ComponentClassification.PerfectAutomorphisms.centerQuotientHom Q with hκ
  have hκi : Function.Injective κ :=
    ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Q
  set D := ρ.range.map κ with hD
  have hD9 : Nat.card D = 9 := by rw [hD, Subgroup.card_map_of_injective hκi, h9]
  have hcinj : Function.Injective (MulAut.conj : Q ⧸ Z →* MulAut (Q ⧸ Z)) :=
    conj_injective_six φ
  have hDinn : D ≤ (MulAut.conj : Q ⧸ Z →* MulAut (Q ⧸ Z)).range := by
    rintro δ ⟨σ, ⟨a, rfl⟩, rfl⟩
    have h3 : (κ (ρ a)) ^ (3 ^ 1) = 1 := by
      have ha3 : a ^ 3 = 1 := Subtype.ext (hA.1.2 a a.2)
      rw [pow_one, ← map_pow, ← map_pow, ha3, map_one, map_one]
    exact Proof15Res8Diag.mem_inner_of_pow_eq_one_six φ h3
  set E : Subgroup (Q ⧸ Z) := D.comap MulAut.conj with hE
  have hE9 : Nat.card E = 9 := by
    have hmap : E.map MulAut.conj = D := by
      rw [hE, Subgroup.map_comap_eq]
      exact inf_eq_right.mpr hDinn
    rw [← hD9, ← hmap, Subgroup.card_map_of_injective hcinj]
  set π : ↥X →* Q ⧸ Z := (QuotientGroup.mk' Z).comp (QuotientGroup.mk' θ) with hπ
  have hπa : ∀ (a : ↥A) (x : ↥X), κ (ρ a) (π x) =
      π ⟨(a : G) * x * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hAX a.2) x).mp x.2⟩ :=
    fun a x => centerQuotientHom_apply_mk hAX a x
  have hRbot : ∀ R ∈ collectionIn (scriptQ A LB) X, (R.subgroupOf X).map π = ⊥ := by
    intro R hR
    obtain ⟨hRq, hRX⟩ := hR
    have hR3' : ¬ 3 ∣ Nat.card R := (isPiSubgroup_piCompl_iff Nat.prime_three R).mp hRq.1.2.1
    have hAR : A ≤ Subgroup.normalizer (R : Set G) := hRq.1.2.2
    have hRt3 : ¬ 3 ∣ Nat.card ((R.subgroupOf X).map π) := by
      intro h3
      apply hR3'
      have h1 : Nat.card ((R.subgroupOf X).map π) ∣ Nat.card (R.subgroupOf X) :=
        Subgroup.card_map_dvd _ _
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv] at h1
      exact h3.trans h1
    have hmaps : ∀ t ∈ E, ∀ r ∈ (R.subgroupOf X).map π, t * r * t⁻¹ ∈ (R.subgroupOf X).map π := by
      intro t ht r hr
      obtain ⟨σ, ⟨a, rfl⟩, hσ⟩ := ht
      obtain ⟨x, hx, rfl⟩ := hr
      have e2 : t * π x * t⁻¹ = κ (ρ a) (π x) := by rw [hσ, MulAut.conj_apply]
      rw [e2, hπa]
      exact ⟨_, Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp (hAR a.2) x).mp (Subgroup.mem_subgroupOf.mp hx)), rfl⟩
    have hEN : E ≤ Subgroup.normalizer (((R.subgroupOf X).map π : Subgroup (Q ⧸ Z)) :
        Set (Q ⧸ Z)) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro r
      refine ⟨hmaps t ht r, fun hr => ?_⟩
      have h1 := hmaps t⁻¹ (E.inv_mem ht) _ hr
      simpa [mul_assoc] using h1
    exact Proof15Res8Diag.eq_bot_of_le_normalizer_six φ hE9 hRt3 hEN
  have hXker : ∀ x : ↥X, π x = 1 := by
    intro x
    have hle : delta A LB X ≤ π.ker.map X.subtype := by
      refine sSup_le fun R hR => ?_
      intro r hr
      have hrX : r ∈ X := hR.2 hr
      refine ⟨⟨r, hrX⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      have h1 : π ⟨r, hrX⟩ ∈ (R.subgroupOf X).map π :=
        ⟨⟨r, hrX⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
      rw [hRbot R hR] at h1
      exact h1
    have hx : (x : G) ∈ delta A LB X := hΔ ▸ x.2
    obtain ⟨x', hx', hxx'⟩ := hle hx
    have e3 : x' = x := Subtype.ext hxx'
    rw [← e3]
    exact hx'
  have htriv : ∀ t : Q ⧸ Z, t = 1 := by
    intro t
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective Z t
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ q
    exact hXker x
  have hsub : Subsingleton (Q ⧸ Z) := ⟨fun s t => (htriv s).trans (htriv t).symm⟩
  have h1 : Nat.card (Q ⧸ Z) = 1 := Nat.card_unique
  rw [Nat.card_congr φ.toEquiv, Proof15Res8Diag.card_alternatingGroup_six] at h1
  norm_num at h1

theorem exists_mem_not_mem_thetaQuotCentralizer_of_tripleCover {A X : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hAF : A ∈ partTwoF G) (hA : Late.IsE27 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hΔ : X = delta A LB X)
    (hXp : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (htc : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6))) :
    ∃ y ∈ A, y ∈ X ∧ y ∉ Sec4.thetaQuotCentralizer X := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  set Q := ↥X ⧸ θ with hQ
  set ρ := (Sec4.thetaQuotMulAut X).comp (X.normalizerMonoidHom.comp (Subgroup.inclusion hAX))
    with hρ
  have hR : Nat.card ρ.range ≤ 3 := card_range_le_three_of_tripleCover hA hAX hΔ hXp htc
  have hR3 : IsPGroup 3 ρ.range := by
    rw [MonoidHom.range_eq_map]
    exact (hA.isPGroup.of_equiv Subgroup.topEquiv.symm).map ρ
  obtain ⟨u, hu3, huZ, hufix⟩ : ∃ u : Q, u ^ 3 = 1 ∧ u ∉ Subgroup.center Q ∧
      ∀ a : ↥A, ρ a u = u := by
    obtain ⟨k, hk⟩ := hR3.exists_card_eq
    have hk1 : k ≤ 1 := by
      by_contra hc
      have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k
    ·
      obtain ⟨u, hu3, huZ⟩ := Sylow155NO.exists_pow_three_not_mem_center htc
      refine ⟨u, hu3, huZ, fun a => ?_⟩
      have h1 : ρ a ∈ ρ.range := ⟨a, rfl⟩
      have hbot : ρ.range = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
      rw [hbot, Subgroup.mem_bot] at h1
      rw [h1, MulAut.one_apply]
    ·
      rw [pow_one] at hk
      obtain ⟨⟨σ, hσR⟩, hσgen⟩ := (isCyclic_of_prime_card (p := 3) hk).exists_generator
      have hσ1 : σ ≠ 1 := by
        intro h1
        have hall : ∀ g : ρ.range, g = 1 := by
          intro g
          obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hσgen g)
          rw [← hn]
          have : (⟨σ, hσR⟩ : ρ.range) = 1 := Subtype.ext h1
          rw [this, one_zpow]
        have hsub : Subsingleton ρ.range := ⟨fun s t => (hall s).trans (hall t).symm⟩
        have h1' : Nat.card ρ.range = 1 := Nat.card_unique
        omega
      obtain ⟨hZ3, ⟨φ⟩⟩ := htc
      set Z := Subgroup.center Q with hZ
      set κ := ComponentClassification.PerfectAutomorphisms.centerQuotientHom Q with hκ
      have hκi : Function.Injective κ :=
        ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Q
      have hσ3 : σ ^ 3 = 1 := by
        obtain ⟨a, ha⟩ := hσR
        have ha3 : a ^ 3 = 1 := Subtype.ext (hA.1.2 a a.2)
        rw [← ha, ← map_pow, ha3, map_one]
      have hκσ3 : (κ σ) ^ (3 ^ 1) = 1 := by rw [pow_one, ← map_pow, hσ3, map_one]
      obtain ⟨ub, hub⟩ := Proof15Res8Diag.mem_inner_of_pow_eq_one_six φ hκσ3
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective Z ub
      have hκu : κ (MulAut.conj u) = MulAut.conj (QuotientGroup.mk' Z u) := by
        ext t
        obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective Z t
        rw [MulAut.conj_apply]
        refine (ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk
          (MulAut.conj u) q).trans ?_
        rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
      have hσu : σ = MulAut.conj u := hκi (by rw [hκu, ← hub])
      have hu3' : (QuotientGroup.mk' Z u) ^ 3 = 1 := by
        have h1 : MulAut.conj ((QuotientGroup.mk' Z u) ^ 3) = 1 := by
          rw [map_pow, hub, ← map_pow, hσ3, map_one]
        exact conj_injective_six φ (h1.trans (map_one _).symm)
      have hu3 : u ^ 3 = 1 :=
        Sec19.Item19Res4Proof.pow_three_eq_one_of_isTripleA6 ⟨hZ3, ⟨φ⟩⟩ hu3'
      have huZ : u ∉ Z := by
        intro huZ
        apply hσ1
        rw [hσu]
        ext q
        rw [MulAut.conj_apply, MulAut.one_apply]
        have h1 := Subgroup.mem_center_iff.mp huZ q
        rw [← h1]
        group
      refine ⟨u, hu3, huZ, fun a => ?_⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hσgen ⟨ρ a, ⟨a, rfl⟩⟩)
      have hn' : ρ a = σ ^ n := by
        have h1 := congrArg Subtype.val hn
        rw [Subgroup.coe_zpow] at h1
        exact h1.symm
      rw [hn', hσu, ← map_zpow, MulAut.conj_apply]
      group
  obtain ⟨n, hnA, hnu⟩ := Sec13.Item138Proof.exists_mem_of_fixed (E := A) (L := X) hAX hAF.1
    hAF.2.1 hu3 (fun x hx => hufix ⟨x, hx⟩)
  refine ⟨n, hnA, n.2, fun hnC => huZ ?_⟩
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective θ q
  obtain ⟨-, hl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hnC
  obtain ⟨t, ht, hte⟩ := hl l l.2
  have hte' : (t : G) = (l : G)⁻¹ * ((n : G) * l * (n : G)⁻¹) := hte
  have h1 : (QuotientGroup.mk' θ l : Q) = QuotientGroup.mk' θ (n * l * n⁻¹) := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : l⁻¹ * (n * l * n⁻¹) = t := Subtype.ext (by rw [hte']; simp)
    rw [this]
    exact ht
  rw [map_mul, map_mul, map_inv] at h1
  have hnu' : QuotientGroup.mk' θ n = u := hnu
  rw [hnu'] at h1
  calc QuotientGroup.mk' θ l * u = u * QuotientGroup.mk' θ l * u⁻¹ * u := by rw [← h1]
    _ = u * QuotientGroup.mk' θ l := by group

theorem exists_hyperplane_of_card_range_le_three {A X : Subgroup G} (hA : Late.IsE27 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hR : Nat.card ((Sec4.thetaQuotMulAut X).comp
      (X.normalizerMonoidHom.comp (Subgroup.inclusion hAX))).range ≤ 3) :
    ∃ B : Subgroup G, IsHyperplane A B ∧ IsPGroup 3 B ∧
      ∀ x ∈ X, ∀ b ∈ B, ⁅x, b⁆ ∈ (aschbacherSolvableCore 3 ↥X).map X.subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  set ρ := (Sec4.thetaQuotMulAut X).comp (X.normalizerMonoidHom.comp (Subgroup.inclusion hAX))
    with hρ
  have hcard : Nat.card ρ.range * Nat.card ρ.ker = 27 := by
    rw [← hA.2, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker).symm
  have hker9 : 3 ^ 2 ∣ Nat.card ρ.ker := by
    have hr0 : 0 < Nat.card ρ.range := Nat.card_pos
    interval_cases h : Nat.card ρ.range <;> omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hker9
  set B : Subgroup G := (K.map ρ.ker.subtype).map A.subtype with hB
  have hBcard : Nat.card B = 9 := by
    rw [hB, Subgroup.card_map_of_injective A.subtype_injective,
      Subgroup.card_map_of_injective ρ.ker.subtype_injective, hK]
    norm_num
  refine ⟨B, ⟨Subgroup.map_subtype_le _, by rw [hA.2, hBcard]⟩,
    IsPGroup.of_card (n := 2) (by rw [hBcard]; norm_num), ?_⟩
  rintro x hx _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  have hρk : ρ (k : A) = 1 := k.2
  set x' : X := ⟨x, hx⟩ with hx'
  set b : A := (k : A) with hbdef
  have h1 : ((x'⁻¹ : X) : X ⧸ θ) =
      ((X.normalizerMonoidHom ⟨(b : G), hAX b.2⟩ x'⁻¹ : X) : X ⧸ θ) := by
    have h2 := congrArg (fun τ : MulAut (X ⧸ θ) => τ ((x'⁻¹ : X) : X ⧸ θ)) hρk
    simp only [MulAut.one_apply] at h2
    exact h2.symm
  rw [QuotientGroup.eq, inv_inv] at h1
  refine ⟨x' * X.normalizerMonoidHom ⟨(b : G), hAX b.2⟩ x'⁻¹, h1, ?_⟩
  change (x : G) * (b * x⁻¹ * (b : G)⁻¹) = ⁅x, (b : G)⁆
  rw [commutatorElement_def]
  group

theorem exists_lbConfig_of_hyperplane {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    {X B : Subgroup G} (hΔ : X = delta A (lB A) X) (hB : IsHyperplane A B) (hB3 : IsPGroup 3 B)
    (hBX : ∀ x ∈ X, ∀ y ∈ B, ⁅x, y⁆ ∈ (aschbacherSolvableCore 3 ↥X).map X.subtype)
    (h3 : 3 ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X)) :
    ∃ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hno
  have hno' : ∀ b d Lb, ¬ IsLBConfig A B b d Lb := fun b d Lb hc => hno ⟨b, d, Lb, hc⟩
  have hLB : lB A B = ⊥ := lB_eq_bot hno'
  have hle := le_qBound_sup_of_eq_delta hΔ hB hB3 hBX
  have hndvd : ∀ K : Subgroup G, ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 K) := fun K =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
  have hq3 : ¬ 3 ∣ Nat.card (qBound A (lB A) B) := by
    rw [qBound, hLB, sup_bot_eq]
    exact not_three_dvd_card_sup
      ((pPrimeCoreOf_le 3 _).trans (centralizer_le_normalizer_pPrimeCoreOf hB.1)) (hndvd _)
      (hndvd _)
  have hQ3 : ¬ 3 ∣ Nat.card (X ⊓ qBound A (lB A) B : Subgroup G) := fun h3' =>
    hq3 (h3'.trans (Subgroup.card_dvd_of_le inf_le_right))
  exact Proof15Res6.not_three_dvd_card_quot_of_le_sup (aschbacherSolvableCore 3 ↥X) inf_le_left
    hQ3 hle h3

theorem ncard_subgroups_card_three_le_four {B : Subgroup G} (hB : Nat.card B = 9) :
    {F : Subgroup G | F ≤ B ∧ Nat.card F = 3}.ncard ≤ 4 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  set Ts : Finset (Subgroup G) :=
    Finset.univ.filter (fun F : Subgroup G => F ≤ B ∧ Nat.card F = 3) with hTs
  have hTeq : {F : Subgroup G | F ≤ B ∧ Nat.card F = 3} = (Ts : Set (Subgroup G)) := by
    ext F
    simp [hTs]
  have hcardS : ∀ S : Subgroup G, (Finset.univ.filter (fun x : G => x ∈ S)).card =
      Nat.card S := fun S => by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  set P : Finset G := (Finset.univ.filter (fun x : G => x ∈ B)).erase 1 with hP
  have hPcard : P.card = 8 := by
    rw [hP, Finset.card_erase_of_mem (by simp [one_mem]), hcardS, hB]
  set f : Subgroup G → Finset G := fun F => (Finset.univ.filter (fun x : G => x ∈ F)).erase 1
    with hf
  have hfcard : ∀ F ∈ Ts, (f F).card = 2 := by
    intro F hF
    obtain ⟨-, h3⟩ := (Finset.mem_filter.mp hF).2
    rw [hf, Finset.card_erase_of_mem (by simp [one_mem]), hcardS, h3]
  have hdisj : (Ts : Set (Subgroup G)).PairwiseDisjoint f := by
    intro F hF F' hF' hne
    obtain ⟨-, h3⟩ := (Finset.mem_filter.mp hF).2
    obtain ⟨-, h3'⟩ := (Finset.mem_filter.mp hF').2
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [hf, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    apply hne
    have hFx : F = Subgroup.zpowers x := by
      have hxF : Subgroup.zpowers x ≤ F := Subgroup.zpowers_le.mpr hx.2
      refine (Subgroup.eq_of_le_of_card_ge hxF ?_).symm
      have hd : Nat.card (Subgroup.zpowers x) ∣ 3 := h3 ▸ Subgroup.card_dvd_of_le hxF
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
      · exfalso
        rw [Nat.card_zpowers, orderOf_eq_one_iff] at h
        exact hx.1 h
      · rw [h3, h]
    have hle : F ≤ F' := by
      rw [hFx]
      exact Subgroup.zpowers_le.mpr hx'.2
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h3, h3'])
  have hsub : Ts.biUnion f ⊆ P := by
    intro x hx
    obtain ⟨F, hF, hxF⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hFB, -⟩ := (Finset.mem_filter.mp hF).2
    simp only [hf, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hxF
    simp only [hP, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hxF.1, hFB hxF.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hfcard, Finset.sum_const, smul_eq_mul,
    hPcard] at hcard
  rw [hTeq, Set.ncard_coe_finset]
  omega

end Ronan155W315

end CFSG.RankThree.PartTwo.Sec15
