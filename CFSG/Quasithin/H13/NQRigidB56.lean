module

public import CFSG.Quasithin.H13.NQRigidInputs
public import CFSG.Quasithin.H13.NQTermG2Cyclic
public import CFSG.Quasithin.H13.NQTermTrialityCyclic
public import CFSG.Quasithin.H13.NQCatSymplecticFour
public import CFSG.Quasithin.H13.NQBlockExcludesLargeRee
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.LocalAnalysis.ComponentInitial (pairAutSubgroup pairAutRestrict)
open scoped Pointwise

theorem exists_centerPreimage {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) :
    ∃ (N : Subgroup K) (_ : N.Characteristic), ¬ p ∣ Nat.card N ∧
      Nonempty (((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≃* K ⧸ N) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := CFSG.pCore 2 K with hM
  set Z := center (K ⧸ M) with hZdef
  set N : Subgroup K := Z.comap (QuotientGroup.mk' M) with hNdef
  have hMN : M ≤ N := fun x hx => by
    have h1 : QuotientGroup.mk' M x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hNdef, mem_comap, h1]
    exact one_mem Z
  have hNc : N.Characteristic := by
    refine characteristic_iff_le_comap.mpr fun φ x hx => ?_
    change QuotientGroup.mk' M (φ x) ∈ Z
    have h1 : QuotientGroup.mk' M (φ x) =
        CFSG.SectionRank.Ccomm.autQuotient M φ (QuotientGroup.mk' M x) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, CFSG.SectionRank.Ccomm.autQuotient_mk]
    rw [h1]
    exact (characteristic_iff_le_comap.mp (inferInstance : Z.Characteristic) _) hx
  have hNp : ¬ p ∣ Nat.card N := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
    set z : Z := ⟨QuotientGroup.mk' M (x : K), x.2⟩ with hz
    have hzp : z ^ p = 1 := Subtype.ext (show QuotientGroup.mk' M (x : K) ^ p = 1 by
      rw [← map_pow, ← SubgroupClass.coe_pow, hxp, OneMemClass.coe_one, map_one])
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hzp) with h1 | h1
    · rw [orderOf_eq_one_iff] at h1
      have hxM : (x : K) ∈ M := by
        have h2 : QuotientGroup.mk' M (x : K) = 1 := congrArg Subtype.val h1
        exact (QuotientGroup.eq_one_iff _).mp h2
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp CFSG.pCore_isPGroup) (⟨x, hxM⟩ : M)
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx] at hk
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ k by rw [hk])
      have := Nat.le_of_dvd (by norm_num) h2
      have h3 := hp.two_le
      omega
    · exact hZ (h1 ▸ orderOf_dvd_natCard z)
  have hmap : N.map (QuotientGroup.mk' M) = Z :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) Z
  exact ⟨N, hNc, hNp, ⟨(QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient M N hMN)⟩⟩

theorem mulAut_smul_subgroup {C : Type*} [Group C] (α : MulAut C) (S : Subgroup C) :
    α • S = S.map α.toMonoidHom := by
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

theorem cyclic_QW_of_cyclic_pair_restriction {H : Type} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {D : Subgroup H} (Q : Sylow 2 H) (hQD : (Q : Subgroup H) ≤ D)
    {K : Subgroup H} [K.Normal] {X : Subgroup H} (hXD : X ≤ D) (hXn : (X.subgroupOf D).Normal)
    (hXK : X ≤ K) (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) {N : Subgroup K} [N.Characteristic]
    (hN : ¬ p ∣ Nat.card N) {C : Type*} [Group C] (ψ : K ⧸ N ≃* C) {d : ℕ} (hd : 1 ≤ d)
    (hC : ∀ (U : Sylow 2 C) (A : Subgroup C), Odd (Nat.card A) → ¬ 3 ∣ Nat.card A →
      (A : Set C) * ((U : Subgroup C) : Set C) = ((U : Subgroup C) : Set C) * (A : Set C) →
      IsCyclic (pairAutRestrict A (U : Subgroup C)).range ∧
        Nat.card (pairAutRestrict A (U : Subgroup C)).range ∣ d) :
    IsCyclic (((Q : Subgroup H).subgroupOf (normalizer (X : Set H))).map
        (normalizerFrattiniConj X)) ∧
      Nat.card (((Q : Subgroup H).subgroupOf (normalizer (X : Set H))).map
        (normalizerFrattiniConj X)) ∣ d := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have : Finite C := Finite.of_equiv _ ψ.toEquiv
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X
  have hPp : IsPGroup p P := hP.isPGroup
  set P₀ := (P.subgroupOf K).map (QuotientGroup.mk' N) with hP₀
  set U₀ := ((Q : Subgroup H).subgroupOf K).map (QuotientGroup.mk' N) with hU₀
  obtain ⟨-, ⟨U, hU⟩, hPU, -, -, gres, -, hgres, -, -, -, -, -, hfin⟩ :=
    SteinbergCC.original_local_sylow_prime_action_is_quotient_of_common_normalizer_restriction
      hp hp2 Q hQD hXD hXn hXK hXA hN hP
  have hΓ1 : ∀ γ ∈ MulAction.stabilizer (MulAut (K ⧸ N)) P₀ ⊓
      MulAction.stabilizer (MulAut (K ⧸ N)) U₀, γ ∈ pairAutSubgroup P₀ U₀ := by
    intro γ hγ
    obtain ⟨h1, h2⟩ := mem_inf.mp hγ
    have e1 : γ • P₀ = P₀ := h1
    have e2 : γ • U₀ = U₀ := h2
    rw [mulAut_smul_subgroup] at e1 e2
    exact ⟨e1, e2⟩
  have hΓ2 : ∀ γ ∈ pairAutSubgroup P₀ U₀, γ ∈ MulAction.stabilizer (MulAut (K ⧸ N)) P₀ ⊓
      MulAction.stabilizer (MulAut (K ⧸ N)) U₀ := by
    intro γ hγ
    obtain ⟨e1, e2⟩ := hγ
    refine mem_inf.mpr ⟨?_, ?_⟩
    · show γ • P₀ = P₀
      rw [mulAut_smul_subgroup]
      exact e1
    · show γ • U₀ = U₀
      rw [mulAut_smul_subgroup]
      exact e2
  have hrange : gres.range = (pairAutRestrict P₀ U₀).range := by
    ext θ
    constructor
    · rintro ⟨γ, rfl⟩
      refine ⟨⟨γ, hΓ1 γ γ.2⟩, ?_⟩
      ext x
      rw [hgres]
      rfl
    · rintro ⟨α, rfl⟩
      refine ⟨⟨α, hΓ2 α α.2⟩, ?_⟩
      ext x
      rw [hgres]
      rfl
  obtain ⟨eR⟩ := NQBlock.range_pairAutRestrict_congr ψ P₀ U₀
  have hψs : Function.Surjective ψ.toMonoidHom := ψ.surjective
  set U' : Sylow 2 C := U.mapSurjective hψs with hU'def
  have hU' : (U' : Subgroup C) = U₀.map ψ.toMonoidHom := by
    rw [hU'def, Sylow.coe_mapSurjective, hU]
  have hA'p : IsPGroup p (P₀.map ψ.toMonoidHom) := (hPp.comap_subtype.map _).map _
  obtain ⟨m, hm⟩ := hA'p.exists_card_eq
  have hAodd : Odd (Nat.card (P₀.map ψ.toMonoidHom)) := by
    rw [hm]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hA3 : ¬ 3 ∣ Nat.card (P₀.map ψ.toMonoidHom) := by
    rw [hm]
    intro h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  have hAU : ((P₀.map ψ.toMonoidHom : Subgroup C) : Set C) * ((U' : Subgroup C) : Set C) =
      ((U' : Subgroup C) : Set C) * ((P₀.map ψ.toMonoidHom : Subgroup C) : Set C) := by
    rw [hU', coe_map ψ.toMonoidHom P₀, coe_map ψ.toMonoidHom U₀, ← Set.image_mul, hPU,
      Set.image_mul]
  obtain ⟨hcyc, hcard⟩ := hC U' (P₀.map ψ.toMonoidHom) hAodd hA3 hAU
  rw [hU'] at hcyc hcard
  have hcycG : IsCyclic gres.range := by
    rw [hrange]
    have : IsCyclic (pairAutRestrict (P₀.map ψ.toMonoidHom) (U₀.map ψ.toMonoidHom)).range :=
      hcyc
    exact isCyclic_of_surjective eR.symm.toMonoidHom eR.symm.surjective
  have hcardG : Nat.card gres.range ∣ d := by
    rw [hrange, Nat.card_congr eR.toEquiv]
    exact hcard
  exact hfin d hd hcycG hcardG

theorem noncyclic_local_Sylow_prime_action_excludes_four_even_models
    {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {D : Subgroup H}
    (Q : Sylow 2 H) (hQD : (Q : Subgroup H) ≤ D) {K : Subgroup H} [K.Normal] {X : Subgroup H}
    (hXD : X ≤ D) (hXn : (X.subgroupOf D).Normal) (hXK : X ≤ K)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hnc : ¬ IsCyclic (((Q : Subgroup H).subgroupOf (normalizer (X : Set H))).map
      (normalizerFrattiniConj X)))
    (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) :
    (∀ f : ℕ, 2 ≤ f → ¬ StatedClassicalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSp 2 2 f) ∧
      (∀ f : ℕ, 2 ≤ f → ¬ ChevalleyExceptionalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .G2 2 f) ∧
      (∀ f : ℕ, 1 ≤ f → ¬ ChevalleyExceptionalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .trialityD4 2 f) ∧
      ∀ a : ℕ, 1 ≤ a → ¬ ReeTitsModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .twistedF4 2 (2 * a + 1) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨N, hNc, hN, ⟨eS⟩⟩ := exists_centerPreimage (K := K) hp hp2 hZ
  have key : ∀ (C : Type) [Group C]
      (_ : ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≃* C) (d : ℕ), 1 ≤ d →
      (∀ (U : Sylow 2 C) (A : Subgroup C), Odd (Nat.card A) → ¬ 3 ∣ Nat.card A →
        (A : Set C) * ((U : Subgroup C) : Set C) = ((U : Subgroup C) : Set C) * (A : Set C) →
        IsCyclic (pairAutRestrict A (U : Subgroup C)).range ∧
          Nat.card (pairAutRestrict A (U : Subgroup C)).range ∣ d) → False :=
    fun C _ ψ d hd hC => hnc (cyclic_QW_of_cyclic_pair_restriction hp hp5 Q hQD hXD hXn hXK hXA
      hN (eS.symm.trans ψ) hd hC).1
  refine ⟨fun f hf hmod => ?_, fun f hf hmod => ?_, fun f hf hmod => ?_, fun a ha hmod => ?_⟩
  · obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hmod
    exact key _ e (2 * f) (by omega) fun U A hAodd hA3 hAU =>
      (NQCat.even_symplectic_four_common_sylow_odd_subgroup_normalizer_action_is_cyclic hf k hk
        U A hAodd hA3 hAU).2.2.1
  · obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hmod
    let eC : AdjointQuotient .G2 k ≃* adjointGroup .G2 k :=
      (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot
    exact key _ (e.trans eC) f (by omega) fun U A hAodd hA3 hAU =>
      (NQTerm.even_G2_common_sylow_odd_subgroup_normalizer_action_is_cyclic hf k hk U A hAodd hA3
        hAU).2.2.1
  · obtain ⟨k, _, _, σ, hk, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hmod.2
    exact key _ e (3 * f) (by omega) fun U A hAodd hA3 hAU =>
      (NQTerm.even_triality_common_sylow_odd_subgroup_normalizer_action_is_cyclic hf k hk σ hσ U
        A hAodd hA3 hAU).2.2.1
  · have hDX : D ≤ normalizer (X : Set H) := (normal_subgroupOf_iff_le_normalizer hXD).mp hXn
    have htriv :=
      (NQBlock.large_Ree_normal_quotient_forces_local_Sylow_centralization_of_prime_witness hp2
        Q hQD hXD hDX hXK hXA hZ ⟨a, ha, hmod⟩).2
    apply hnc
    have hbot : ((Q : Subgroup H).subgroupOf (normalizer (X : Set H))).map
        (normalizerFrattiniConj X) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨n, hn, rfl⟩
      have hnQ : ((n : normalizer (X : Set H)) : H) ∈ (Q : Subgroup H) :=
        mem_subgroupOf.mp (show n ∈ (Q : Subgroup H).subgroupOf (normalizer (X : Set H)) from hn)
      rw [mem_bot]
      exact htriv n hnQ
    rw [hbot]
    infer_instance

theorem stmtNoncyclicLocalSylowFourEven_holds :
    StmtNoncyclicLocalSylowFourEven :=
  fun _ _ _ _ hp hp5 _ Q hQD _ _ _ hXD hXn hXK hXA hnc hZ =>
    noncyclic_local_Sylow_prime_action_excludes_four_even_models hp hp5 Q hQD hXD hXn hXK hXA hnc
      hZ

theorem local_Sylow_prime_action_four_divisibility_restricts_three_even_model_fields
    {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {D : Subgroup H}
    (Q : Sylow 2 H) (hQD : (Q : Subgroup H) ≤ D) {K : Subgroup H} [K.Normal] {X : Subgroup H}
    (hXD : X ≤ D) (hXn : (X.subgroupOf D).Normal) (hXK : X ≤ K)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (h4 : 4 ∣ Nat.card (((Q : Subgroup H).subgroupOf (normalizer (X : Set H))).map
      (normalizerFrattiniConj X)))
    (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) :
    (∀ f : ℕ, 2 ≤ f → StatedClassicalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSp 2 2 f → Even f) ∧
      (∀ f : ℕ, 2 ≤ f → ChevalleyExceptionalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .G2 2 f → 4 ∣ f) ∧
      ∀ f : ℕ, 1 ≤ f → ChevalleyExceptionalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .trialityD4 2 f → 4 ∣ f := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨N, hNc, hN, ⟨eS⟩⟩ := exists_centerPreimage (K := K) hp hp2 hZ
  have key : ∀ (C : Type) [Group C]
      (_ : ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≃* C) (d : ℕ), 1 ≤ d →
      (∀ (U : Sylow 2 C) (A : Subgroup C), Odd (Nat.card A) → ¬ 3 ∣ Nat.card A →
        (A : Set C) * ((U : Subgroup C) : Set C) = ((U : Subgroup C) : Set C) * (A : Set C) →
        IsCyclic (pairAutRestrict A (U : Subgroup C)).range ∧
          Nat.card (pairAutRestrict A (U : Subgroup C)).range ∣ d) → 4 ∣ d :=
    fun C _ ψ d hd hC => h4.trans (cyclic_QW_of_cyclic_pair_restriction hp hp5 Q hQD hXD hXn hXK
      hXA hN (eS.symm.trans ψ) hd hC).2
  refine ⟨fun f hf hmod => ?_, fun f hf hmod => ?_, fun f hf hmod => ?_⟩
  · obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hmod
    have h := key _ e (2 * f) (by omega) fun U A hAodd hA3 hAU =>
      (NQCat.even_symplectic_four_common_sylow_odd_subgroup_normalizer_action_is_cyclic hf k hk
        U A hAodd hA3 hAU).2.2.1
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by omega⟩
  · obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hmod
    let eC : AdjointQuotient .G2 k ≃* adjointGroup .G2 k :=
      (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot
    exact key _ (e.trans eC) f (by omega) fun U A hAodd hA3 hAU =>
      (NQTerm.even_G2_common_sylow_odd_subgroup_normalizer_action_is_cyclic hf k hk U A hAodd hA3
        hAU).2.2.1
  · obtain ⟨k, _, _, σ, hk, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hmod.2
    have h := key _ e (3 * f) (by omega) fun U A hAodd hA3 hAU =>
      (NQTerm.even_triality_common_sylow_odd_subgroup_normalizer_action_is_cyclic hf k hk σ hσ U
        A hAodd hA3 hAU).2.2.1
    omega

theorem stmtFourDivisibilityFields_holds :
    StmtFourDivisibilityFields :=
  fun _ _ _ _ hp hp5 _ Q hQD _ _ _ hXD hXn hXK hXA h4 hZ =>
    local_Sylow_prime_action_four_divisibility_restricts_three_even_model_fields hp hp5 Q hQD hXD
      hXn hXK hXA h4 hZ

end CFSG.Quasithin.H13.NQRigid
