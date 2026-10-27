module

public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofL3Nine
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofCover
public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
public import CFSG.RankThree.PartTwo.Sec4.Item4Res3ProofRank

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence
  centerQuotientOuterHom centerQuotient_outer_injective)
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Res413Cover

theorem not_three_dvd_card_outer_of_quotient {X H : Type*} [Group X] [Group H]
    [Group.IsPerfect X] (e : X ⧸ Subgroup.center X ≃* H) (hH : ¬ 3 ∣ Nat.card (Outer H)) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  intro h3
  apply hH
  have hinj := centerQuotient_outer_injective X
  have h1 : Nat.card (Outer X) = Nat.card (centerQuotientOuterHom X).range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have h2 := Subgroup.card_subgroup_dvd_card (centerQuotientOuterHom X).range
  rw [← h1] at h2
  rw [← Nat.card_congr (equivalence e).toEquiv]
  exact h3.trans h2

variable {G : Type} [Group G] [Finite G]

theorem le_and_center_eq_of_lift (h45 : Item4_5) {H : Type} [Group H]
    (hlift : ∀ (Y : Type) [Group Y] (ρ : Y →* H), Function.Surjective ρ →
      ρ.ker ≤ Subgroup.center Y → (∀ z ∈ ρ.ker, z ^ 3 = 1) → ∀ B : Subgroup H,
      CFSG.Assembly.IsElemAbelian 3 B → 81 ≤ Nat.card B →
      CFSG.Assembly.IsElemAbelian 3 (B.comap ρ))
    (hOut : ¬ 3 ∣ Nat.card (Outer H)) {L A E : Subgroup G} {c : G} (hyp : Hyp413 L A E c)
    (hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (φ : (L ⧸ aschbacherSolvableCore 3 L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃* H)
    (hθ : aschbacherSolvableCore 3 L = ⊥) :
    A ≤ L ∧ (Subgroup.center L).map L.subtype = Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hG, hL, hT, hr⟩ := hyp
  obtain ⟨hAmax, hAc, hc3, -, -, -⟩ := hT
  have hA := hAmax.prop
  obtain ⟨m, hm5, hm⟩ := exists_card_eq_of_four_lt_pRank hA hr
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    h45 G hG A (isPGroup_of_isElemAbelian hA) (Or.inr ⟨hA, m, by omega, hm⟩) L
      (mem_thetaComponents_of_isComponent3 hL)
  set θ := aschbacherSolvableCore 3 L with hθdef
  set X := L ⧸ θ
  have hXq : CFSG.IsQuasisimple X :=
    (CFSG.LocalCores.quasisimple_central_quotient hL.1 θ (aschbacherSolvableCore_le_center hL.1)).1
  have : Group.IsPerfect X := hXq.1
  have hZX3 : ∀ z ∈ Subgroup.center X, z ^ 3 = 1 := fun z hz => by
    have h := pow_card_eq_one' (G := Subgroup.center X) (x := ⟨z, hz⟩)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  set R := (thetaAct hAN).range with hR
  have hRe : CFSG.Assembly.IsElemAbelian 3 R := isElemAbelian_range_thetaAct hAN hA
  have hRinn : R ≤ (MulAut.conj : X →* MulAut X).range := by
    rintro _ ⟨a, rfl⟩
    refine mem_range_conj_of_pow_three (not_three_dvd_card_outer_of_quotient φ hOut) ?_
    have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hA.2 _ a.2)
    rw [← map_pow, ha3, map_one]
  have hRcard : Nat.card R = 3 ^ (m - 1) := by
    have h1 := card_range_thetaAct_mul hL.1 hAN
    rw [hAc, Nat.card_zpowers, hc3, hm] at h1
    have h2 : 3 ^ m = 3 ^ (m - 1) * 3 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  obtain ⟨hρ, hker⟩ := Res417Five.surjective_ker_of_mulEquiv φ
  set ρ := φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) with hρdef
  set Bh : Subgroup X := R.comap (MulAut.conj : X →* MulAut X) with hBh
  have hconj1 : ∀ z ∈ Subgroup.center X, MulAut.conj z = 1 := fun z hz => by
    rw [← MonoidHom.mem_ker, ker_conj_eq_center]
    exact hz
  have hZBh : Subgroup.center X ≤ Bh := fun z hz => by
    change MulAut.conj z ∈ R
    rw [hconj1 z hz]
    exact R.one_mem
  have hRcomm : ∀ σ ∈ R, ∀ τ ∈ R, σ * τ = τ * σ := fun σ hσ τ hτ =>
    congrArg Subtype.val (hRe.1.1.comm ⟨σ, hσ⟩ ⟨τ, hτ⟩)
  set B := Bh.map ρ with hBdef
  have hBcomap : B.comap ρ = Bh :=
    Subgroup.comap_map_eq_self (by rw [hker]; exact hZBh)
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨y₁, hy₁, hy₁x⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨y₂, hy₂, hy₂y⟩ := Subgroup.mem_map.mp y.2
      apply Subtype.ext
      change (x : H) * y = y * x
      rw [← hy₁x, ← hy₂y, ← map_mul, ← map_mul]
      have hc : MulAut.conj (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hRcomm _ hy₁ _ hy₂]
        group
      have hmem : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ ρ.ker := by
        rw [hker, ← ker_conj_eq_center, MonoidHom.mem_ker]
        exact hc
      rw [MonoidHom.mem_ker] at hmem
      calc ρ (y₁ * y₂) = ρ (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * ρ (y₂ * y₁) := by
            rw [← map_mul]; congr 1; group
        _ = ρ (y₂ * y₁) := by rw [hmem, one_mul]
    · obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow]
      have hc : MulAut.conj (y ^ 3) = 1 := by
        rw [map_pow]
        exact hRe.2 _ hy
      have hmem : y ^ 3 ∈ ρ.ker := by
        rw [hker, ← ker_conj_eq_center, MonoidHom.mem_ker]
        exact hc
      exact hmem
  have hBhcard : Nat.card Bh = 3 ^ (m - 1) * 3 := by
    set κ := (MulAut.conj : X →* MulAut X).rangeRestrict with hκ
    have hκs : Function.Surjective κ := MonoidHom.rangeRestrict_surjective _
    have h1 := Res417Five.card_comap_of_surjective κ hκs
      (R.subgroupOf (MulAut.conj : X →* MulAut X).range)
    have h2 : (R.subgroupOf (MulAut.conj : X →* MulAut X).range).comap κ = Bh := by
      ext y
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      rfl
    have h3 : Nat.card (R.subgroupOf (MulAut.conj : X →* MulAut X).range) = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRinn).toEquiv
    have h4 : Nat.card κ.ker = 3 := by
      rw [hκ, MonoidHom.ker_rangeRestrict, ker_conj_eq_center, hZ3]
    rw [h2, h3, h4, hRcard] at h1
    exact h1
  have hBcard : Nat.card B = 3 ^ (m - 1) := by
    have h1 := Res417Five.card_comap_of_surjective ρ hρ B
    rw [hBcomap, hBhcard, hker, hZ3] at h1
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h1).symm
  have h81 : 81 ≤ Nat.card B := by
    rw [hBcard]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hBhe : CFSG.Assembly.IsElemAbelian 3 Bh := by
    have := hlift X ρ hρ hker.le (fun z hz => hZX3 z (hker ▸ hz)) B hBe h81
    rwa [hBcomap] at this
  have hmkinj : Function.Injective (QuotientGroup.mk' θ) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hθ
  set Bt : Subgroup G := (Bh.comap (QuotientGroup.mk' θ)).map L.subtype with hBt
  have hBtL : Bt ≤ L := Subgroup.map_subtype_le _
  have hBtA : Bt ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    have hx3 : (x : G) ^ 3 = 1 := by
      have h := hBhe.2 _ hx
      have h' : QuotientGroup.mk' θ (x ^ 3) = QuotientGroup.mk' θ 1 := by
        rw [map_pow, map_one]; exact h
      have := hmkinj h'
      exact congrArg Subtype.val this
    refine mem_of_maximal_of_commute hAmax hx3 fun a ha => ?_
    obtain ⟨y, hy⟩ := hRinn ⟨⟨a, ha⟩, rfl⟩
    have hyBh : y ∈ Bh := by
      change MulAut.conj y ∈ R
      rw [hy]
      exact ⟨⟨a, ha⟩, rfl⟩
    have hfix : thetaAct hAN ⟨a, ha⟩ (QuotientGroup.mk' θ x) = QuotientGroup.mk' θ x := by
      rw [← hy, MulAut.conj_apply]
      have := congrArg Subtype.val (hBhe.1.1.comm ⟨y, hyBh⟩ ⟨_, hx⟩)
      simp only [Subgroup.coe_mul] at this
      rw [this, mul_inv_cancel_right]
    have hax : (⟨a * x * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hAN ha) x).mp x.2⟩ : L) = x := by
      apply hmkinj
      rw [← hfix]
      rfl
    have := congrArg Subtype.val hax
    simp only at this
    calc a * (x : G) = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [this]
  have hBtcard : Nat.card Bt = Nat.card A := by
    rw [hBt, Subgroup.card_map_of_injective L.subtype_injective, hm]
    have hbij : Function.Bijective (QuotientGroup.mk' θ) :=
      ⟨hmkinj, QuotientGroup.mk'_surjective θ⟩
    set e := MulEquiv.ofBijective (QuotientGroup.mk' θ) hbij
    have h1 : Bh.comap (QuotientGroup.mk' θ) = Bh.comap e.toMonoidHom := rfl
    rw [← Subgroup.card_map_of_injective e.injective, Subgroup.map_comap_eq_self_of_surjective
      e.surjective, hBhcard, ← pow_succ]
    congr 1
    omega
  have hBtEq : Bt = A := Subgroup.eq_of_le_of_card_ge hBtA (by rw [hBtcard])
  have hAL : A ≤ L := hBtEq ▸ hBtL
  refine ⟨hAL, ?_⟩
  have hZL3 : Nat.card (Subgroup.center L) = 3 := by
    have hbij : Function.Bijective (QuotientGroup.mk' θ) :=
      ⟨hmkinj, QuotientGroup.mk'_surjective θ⟩
    set e := MulEquiv.ofBijective (QuotientGroup.mk' θ) hbij
    rw [← hZ3, ← Subgroup.map_center_eq e]
    exact (Subgroup.card_map_of_injective e.injective).symm
  have hle : (Subgroup.center L).map L.subtype ≤ Subgroup.zpowers c := by
    rintro _ ⟨z, hz, rfl⟩
    have hz3 : (z : G) ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := Subgroup.center L) (x := ⟨z, hz⟩)
      rw [hZL3] at h
      exact congrArg Subtype.val (congrArg Subtype.val h)
    have hzC : (z : G) ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨y, hy⟩))
    have hzA : (z : G) ∈ A := mem_of_maximal_of_commute hAmax hz3 fun a ha =>
      Subgroup.mem_centralizer_iff.mp hzC a (hAL ha)
    rw [← hAc]
    exact ⟨hzA, hzC⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, hc3, Subgroup.card_map_of_injective L.subtype_injective, hZL3]

theorem theta_eq_bot_of_card_center_dvd {L : Subgroup G} (hL : CFSG.IsQuasisimple L)
    (h : Nat.card (Subgroup.center L) ∣ 3) : aschbacherSolvableCore 3 L = ⊥ := by
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hdvd : Nat.card (aschbacherSolvableCore 3 L) ∣ 3 :=
    (Subgroup.card_dvd_of_le (aschbacherSolvableCore_le_center hL)).trans h
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · rw [h1] at hθ3
    exact absurd (dvd_refl 3) hθ3

theorem theta_eq_bot_of_u43 {L : Subgroup G} (hL : CFSG.IsQuasisimple L)
    (hZodd : Odd (Nat.card (Subgroup.center L)))
    (e : L ⧸ Subgroup.center L ≃* projSU 4 3 1) : aschbacherSolvableCore 3 L = ⊥ := by
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hdvd : Nat.card (aschbacherSolvableCore 3 L) ∣ Nat.card (Subgroup.center L) :=
    Subgroup.card_dvd_of_le (aschbacherSolvableCore_le_center hL)
  by_contra hne
  have h1 : Nat.card (aschbacherSolvableCore 3 L) ≠ 1 := fun h =>
    hne (Subgroup.eq_bot_of_card_eq _ h)
  set p := (Nat.card (aschbacherSolvableCore 3 L)).minFac with hp
  have hpp : p.Prime := Nat.minFac_prime h1
  have hpθ : p ∣ Nat.card (aschbacherSolvableCore 3 L) := Nat.minFac_dvd _
  have hpZ : p ∣ Nat.card (Subgroup.center L) := hpθ.trans hdvd
  have hp2 : p ≠ 2 := by
    rintro h2
    rw [h2] at hpZ
    obtain ⟨k, hk⟩ := hZodd
    omega
  have hp3 : p ≠ 3 := by
    rintro h3
    rw [h3] at hpθ
    exact hθ3 hpθ
  refine Res4Three.not_dvd_card_center_of_not_sq_dvd hL.1.commutator_eq_top hpp ?_ hpZ
  rw [Nat.card_congr e.toEquiv, Res4Three.card_U43]
  exact Res4Three.not_sq_dvd_of_eq_mul (i := 7) (j := 6) (m := 35) (by norm_num) hpp hp2 hp3
    (Res4Three.no_sq_of_le (by norm_num) (by norm_num) (by decide))

theorem center_eq_of_isExtOf {X : Type} [Group X] [Finite X] (hX : CFSG.IsQuasisimple X)
    {S : Type} [Group S] (hS : Subgroup.center S = ⊥)
    (h : IsExtOf X S (Multiplicative (ZMod 3))) :
    Nat.card (Subgroup.center X) = 3 ∧ Nonempty (X ⧸ Subgroup.center X ≃* S) := by
  obtain ⟨K, hKn, ⟨eK⟩, ⟨eS⟩⟩ := h
  have hK3 : Nat.card K = 3 := by
    rw [Nat.card_congr eK.toEquiv]
    simp
  have hKZ : K ≤ Subgroup.center X := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hX hKn with h | h
    · exfalso
      have hab : ∀ x y : X, x * y = y * x := fun x y => by
        have hx : x ∈ K := h ▸ Subgroup.mem_top x
        have hy : y ∈ K := h ▸ Subgroup.mem_top y
        have h1 : eK (⟨x, hx⟩ * ⟨y, hy⟩) = eK (⟨y, hy⟩ * ⟨x, hx⟩) := by
          rw [map_mul, map_mul, mul_comm]
        exact congrArg Subtype.val (eK.injective h1)
      have hcomm : commutator X = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hab y x
      have htop := hX.1.commutator_eq_top
      rw [hcomm] at htop
      have hcard : Nat.card X = 1 := by
        rw [← Subgroup.card_top (G := X), ← htop, Subgroup.card_bot]
      have : Nat.card K ≤ Nat.card X := Subgroup.card_le_card_group K
      omega
    · exact h
  have hZK : Subgroup.center X ≤ K := by
    intro z hz
    have hzq : eS (QuotientGroup.mk z) ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨q, rfl⟩ := eS.surjective s
      induction q using QuotientGroup.induction_on with
      | H x =>
        rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          (Subgroup.mem_center_iff.mp hz) x]
    rw [hS, Subgroup.mem_bot, map_eq_one_iff _ eS.injective, QuotientGroup.eq_one_iff] at hzq
    exact hzq
  have hKeq : K = Subgroup.center X := le_antisymm hKZ hZK
  refine ⟨?_, ⟨(QuotientGroup.quotientMulEquivOfEq hKeq.symm).trans eS⟩⟩
  rw [← hKeq]
  exact hK3

theorem odd_card_center_of_hyp413 (h45 : Item4_5) {L A E : Subgroup G} {c : G}
    (hyp : Hyp413 L A E c) : Odd (Nat.card (Subgroup.center L)) := by
  obtain ⟨hG, hL, hT, hr⟩ := hyp
  have hA := hT.1.prop
  obtain ⟨m, hm5, hm⟩ := exists_card_eq_of_four_lt_pRank hA hr
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    h45 G hG A (isPGroup_of_isElemAbelian hA) (Or.inr ⟨hA, m, by omega, hm⟩) L
      (mem_thetaComponents_of_isComponent3 hL)
  exact odd_card_center_of_le_normalizer hG hA (by omega) hm hAN

end Res413Cover

section Closed


open Res413Cover in
theorem inputs413CoverU43McL_of (h45 : Item4_5) : Inputs413CoverU43McL := by
  intro G _ _ L A E c hyp hcov
  have hL := hyp.2.1
  have hZodd := odd_card_center_of_hyp413 h45 hyp
  rcases hcov with ⟨hZ3, ⟨e₁⟩⟩ | hext
  ·
    have hθ := theta_eq_bot_of_u43 hL.1 hZodd
      ((Res417Three.thetaQuotCenterEquiv hL.1).symm.trans e₁)
    have hOut : ¬ 3 ∣ Nat.card (Outer Item434RemU43.UX) := fun h3 => outU43_holds (by
      rw [Nat.card_congr (equivalence Item434RemU43.projSUEquivUX).toEquiv]
      exact h3)
    obtain ⟨hAL, hZc⟩ := le_and_center_eq_of_lift h45
      (fun Y _ ρ hρ hk hz B hB h81 => Res417Five.isElemAbelian_comap_u43 ρ hρ hk hz hB h81)
      hOut hyp hZ3 (e₁.trans Item434RemU43.projSUEquivUX) hθ
    exact ⟨hAL, Subgroup.center L, inferInstance, hZc,
      Or.inl ⟨(Res417Three.thetaQuotCenterEquiv hL.1).symm.trans e₁⟩⟩
  ·
    have hXq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) :=
      (CFSG.LocalCores.quasisimple_central_quotient hL.1 _
        (aschbacherSolvableCore_le_center hL.1)).1
    have hZS : Subgroup.center Blueprint.NativeSporadic.McL = ⊥ :=
      center_carrier_eq_bot_of_cover (s := .McL) (by simp [sporadicCovers46])
    obtain ⟨hZ3, ⟨e₁⟩⟩ := center_eq_of_isExtOf hXq hZS hext
    have : Group.IsPerfect L := hL.1.1
    have hθ := theta_eq_bot_of_card_center_dvd hL.1
      (CFSG.Sporadic.Recognition.McLMultiplier.card_center_dvd_three_of_certificate
        inferInstance ((Res417Three.thetaQuotCenterEquiv hL.1).symm.trans e₁))
    have hle : Nat.card (Outer CFSG.Sporadic.Schreier.mclP) ≤ 2 :=
      CFSG.Sporadic.SmallOddCore.mcl_outer_card_le
    have hOut : ¬ 3 ∣ Nat.card (Outer CFSG.Sporadic.Schreier.mclP) := by
      intro h3
      have hpos : 0 < Nat.card (Outer CFSG.Sporadic.Schreier.mclP) := Nat.card_pos
      have := Nat.le_of_dvd hpos h3
      omega
    obtain ⟨hAL, hZc⟩ := le_and_center_eq_of_lift h45
      (fun Y _ ρ hρ hk hz B hB h81 => Res417Five.isElemAbelian_comap_mcl ρ hρ hk hz hB h81)
      hOut hyp hZ3 (e₁.trans CFSG.Sporadic.Schreier.mclPermEquiv) hθ
    exact ⟨hAL, Subgroup.center L, inferInstance, hZc,
      Or.inr ⟨(Res417Three.thetaQuotCenterEquiv hL.1).symm.trans e₁⟩⟩

end Closed

section Holds

theorem inputs413CoverU43McL_holds
    : Inputs413CoverU43McL :=
  inputs413CoverU43McL_of rank3II_4_5

end Holds

end CFSG.RankThree.PartTwo.Sec4
