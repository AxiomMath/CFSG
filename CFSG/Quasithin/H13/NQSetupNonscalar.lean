module

public import CFSG.Quasithin.SteinbergCCLocalSylowAction
public import CFSG.Quasithin.H13.NQSetupFieldPowerTriality
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.Quasithin.H13.NQSetup

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open scoped Pointwise

theorem exists_mem_sylow_mk_eq {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {X P : Subgroup H} (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hP : IsSylowOf p P X) (x : X) :
    ∃ y : X, (y : H) ∈ P ∧
      QuotientGroup.mk' (CFSG.pCore 2 X) y = QuotientGroup.mk' (CFSG.pCore 2 X) x := by
  obtain ⟨S₁, hS₁⟩ := hP.exists_sylow_eq_subgroupOf
  have h := (S₁.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 X))).is_maximal'
    (hXA.to_subgroup ⊤) le_top
  have hx : QuotientGroup.mk' (CFSG.pCore 2 X) x ∈
      ((S₁.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 X)) : Sylow p _) :
        Subgroup (X ⧸ CFSG.pCore 2 X)) := by
    rw [← h]
    exact mem_top _
  rw [Sylow.coe_mapSurjective, hS₁] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  exact ⟨y, mem_subgroupOf.mp hy, hyx⟩

theorem pow_prime_eq_one_of_frattini {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {X : Subgroup H} (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (w : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) : w ^ p = 1 := by
  have : Fact (IsPGroup p (X ⧸ CFSG.pCore 2 X)) := ⟨hXA⟩
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective _ w
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact CFSG.pth_power_mem_frattini_of_isPGroup r

theorem scalar_of_power_action {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {D : Subgroup H} (Q : Sylow 2 H) (hQD : (Q : Subgroup H) ≤ D)
    {K : Subgroup H} [K.Normal] {X : Subgroup H} (hXD : X ≤ D) (hXn : (X.subgroupOf D).Normal)
    (hXK : X ≤ K) (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) {N : Subgroup K} [N.Characteristic]
    (hN : ¬ p ∣ Nat.card N) {C : Type*} [Group C] (ψ : K ⧸ N ≃* C)
    (hC : ∀ (U : Sylow 2 C) (A : Subgroup C), Odd (Nat.card A) → ¬ 3 ∣ Nat.card A →
      (A : Set C) * ((U : Subgroup C) : Set C) = ((U : Subgroup C) : Set C) * (A : Set C) →
      ∀ α : MulAut C, A.map α.toMonoidHom = A → (U : Subgroup C).map α.toMonoidHom = U →
        ∃ i : ℕ, ∀ a ∈ A, α a = a ^ 2 ^ i) :
    ∀ γ ∈ ((Q : Subgroup H).subgroupOf (normalizer (X : Set H))).map (normalizerFrattiniConj X),
      ∃ c : ZMod p, ∀ w, γ w = w ^ c.val := by
  classical
  intro γ hγ
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have : Finite C := Finite.of_equiv _ ψ.toEquiv
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X
  have hPp : IsPGroup p P := hP.isPGroup
  have hPK : P ≤ K := hP.le.trans hXK
  have hDN : D ≤ normalizer (X : Set H) := (normal_subgroupOf_iff_le_normalizer hXD).mp hXn
  have hQN : (Q : Subgroup H) ≤ normalizer (X : Set H) := hQD.trans hDN
  obtain ⟨hσinj, ⟨U, hU⟩, hPU, -, hBΓ, -, bres, -, -, -, ⟨fW, hfW, hfWn⟩, -⟩ :=
    SteinbergCC.original_local_sylow_prime_action_is_quotient_of_common_normalizer_restriction
      hp hp2 Q hQD hXD hXn hXK hXA hN hP
  set θ : H →* MulAut (K ⧸ N) :=
    (CFSG.SectionRank.Ccomm.autQuotient N).comp MulAut.conjNormal with hθ
  set P₀ := (P.subgroupOf K).map (QuotientGroup.mk' N) with hP₀
  set U₀ := ((Q : Subgroup H).subgroupOf K).map (QuotientGroup.mk' N) with hU₀
  obtain ⟨⟨_, n, rfl⟩, hb⟩ := hfW ⟨γ, hγ⟩
  have hnQ : (n : H) ∈ (Q : Subgroup H) := (mem_inf.mp n.2).1
  have hnP : (n : H) ∈ normalizer (P : Set H) := (mem_inf.mp n.2).2
  have hγn : γ = normalizerFrattiniConj X ⟨n, hQN hnQ⟩ := by
    rw [← hfWn n (hQN hnQ)]
    exact (congrArg Subtype.val hb).symm
  have hθΓ : θ n ∈ MulAction.stabilizer (MulAut (K ⧸ N)) P₀ ⊓
      MulAction.stabilizer (MulAut (K ⧸ N)) U₀ := hBΓ ⟨n, n.2, rfl⟩
  set α : MulAut C := ψ.symm.trans ((θ n).trans ψ) with hα
  have hαψ : ∀ x, α (ψ x) = ψ (θ n x) := fun x => by simp [hα]
  set A' := P₀.map ψ.toMonoidHom with hA'
  have hψs : Function.Surjective ψ.toMonoidHom := ψ.surjective
  set U' : Sylow 2 C := U.mapSurjective hψs with hU'def
  have hU' : (U' : Subgroup C) = U₀.map ψ.toMonoidHom := by
    rw [hU'def, Sylow.coe_mapSurjective, hU]
  have hA'p : IsPGroup p A' := (hPp.comap_subtype.map _).map _
  obtain ⟨m, hm⟩ := hA'p.exists_card_eq
  have hAodd : Odd (Nat.card A') := by
    rw [hm]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hA3 : ¬ 3 ∣ Nat.card A' := by
    rw [hm]
    intro h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  have hAU : (A' : Set C) * ((U' : Subgroup C) : Set C) =
      ((U' : Subgroup C) : Set C) * (A' : Set C) := by
    rw [hU', hA', coe_map ψ.toMonoidHom P₀, coe_map ψ.toMonoidHom U₀, ← Set.image_mul, hPU,
      Set.image_mul]
  have hαA : A'.map α.toMonoidHom = A' := by
    refine eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨θ n x, SteinbergCC.apply_mem_of_mem_stabilizer (mem_inf.mp hθΓ).1 hx,
        (hαψ x).symm⟩
    · rw [card_map_of_injective (f := α.toMonoidHom) α.injective]
  have hαU : (U' : Subgroup C).map α.toMonoidHom = U' := by
    refine eq_of_le_of_card_ge ?_ ?_
    · rw [hU']
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨θ n x, SteinbergCC.apply_mem_of_mem_stabilizer (mem_inf.mp hθΓ).2 hx,
        (hαψ x).symm⟩
    · rw [card_map_of_injective (f := α.toMonoidHom) α.injective]
  obtain ⟨i, hi⟩ := hC U' A' hAodd hA3 hAU α hαA hαU
  have hθpow : ∀ x ∈ P₀, θ n x = x ^ 2 ^ i := by
    intro x hx
    apply ψ.injective
    rw [← hαψ, map_pow]
    exact hi _ ⟨x, hx, rfl⟩
  have hconjP : ∀ z ∈ P, (n : H) * z * (n : H)⁻¹ = z ^ 2 ^ i := by
    intro z hz
    have hz' : (⟨z, hPK hz⟩ : K) ∈ P.subgroupOf K := mem_subgroupOf.mpr hz
    have hc : MulAut.conjNormal (n : H) ⟨z, hPK hz⟩ ∈ P.subgroupOf K := by
      rw [mem_subgroupOf, MulAut.conjNormal_apply]
      exact (mem_normalizer_iff.mp hnP z).mp hz
    have hpow : (⟨z, hPK hz⟩ : K) ^ 2 ^ i ∈ P.subgroupOf K := pow_mem hz' _
    have h1 := hθpow (QuotientGroup.mk' N ⟨z, hPK hz⟩) ⟨_, hz', rfl⟩
    rw [hθ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      CFSG.SectionRank.Ccomm.autQuotient_mk, ← QuotientGroup.mk_pow] at h1
    have h2 : (⟨_, hc⟩ : P.subgroupOf K) = ⟨_, hpow⟩ := hσinj h1
    have h3 := congrArg (fun w : P.subgroupOf K => ((w : K) : H)) h2
    simpa [MulAut.conjNormal_apply] using h3
  refine ⟨((2 ^ i : ℕ) : ZMod p), fun w => ?_⟩
  rw [hγn, ZMod.val_natCast]
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (frattini (X ⧸ CFSG.pCore 2 X)) w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 X) v
  obtain ⟨y, hyP, hyx⟩ := exists_mem_sylow_mk_eq hXA hP x
  rw [← hyx]
  have hy : X.normalizerMonoidHom ⟨n, hQN hnQ⟩ y = y ^ 2 ^ i :=
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hconjP y hyP)
  change QuotientGroup.mk' _ (QuotientGroup.mk' _ (X.normalizerMonoidHom ⟨n, hQN hnQ⟩ y)) = _
  rw [hy, map_pow, map_pow]
  exact pow_eq_pow_mod _ (pow_prime_eq_one_of_frattini hXA _)

theorem nonscalar_original_local_sylow_prime_action_excludes_even_G2_and_triality_quotients
    {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {D : Subgroup H}
    (Q : Sylow 2 H) (hQD : (Q : Subgroup H) ≤ D) {K : Subgroup H} [K.Normal] {X : Subgroup H}
    (hXD : X ≤ D) (hXn : (X.subgroupOf D).Normal) (hXK : X ≤ K)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hns : ∃ γ ∈ ((Q : Subgroup H).subgroupOf (normalizer (X : Set H))).map
        (normalizerFrattiniConj X), ¬ ∃ c : ZMod p, ∀ w, γ w = w ^ c.val)
    (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) :
    (∀ f : ℕ, 2 ≤ f → ¬ ChevalleyExceptionalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .G2 2 f) ∧
      ∀ f : ℕ, 1 ≤ f → ¬ ChevalleyExceptionalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .trialityD4 2 f := by
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
  have : N.Characteristic := by
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
      omega
    · exact hZ (h1 ▸ orderOf_dvd_natCard z)
  have hmap : N.map (QuotientGroup.mk' M) = Z :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) Z
  let eS : (K ⧸ M) ⧸ Z ≃* K ⧸ N := (QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient M N hMN)
  have key : ∀ (C : Type) [Group C] (ψ : K ⧸ N ≃* C),
      (∀ (U : Sylow 2 C) (A : Subgroup C), Odd (Nat.card A) → ¬ 3 ∣ Nat.card A →
        (A : Set C) * ((U : Subgroup C) : Set C) = ((U : Subgroup C) : Set C) * (A : Set C) →
        ∀ α : MulAut C, A.map α.toMonoidHom = A → (U : Subgroup C).map α.toMonoidHom = U →
          ∃ i : ℕ, ∀ a ∈ A, α a = a ^ 2 ^ i) → False := by
    intro C _ ψ hC
    obtain ⟨γ, hγ, hγns⟩ := hns
    exact hγns (scalar_of_power_action hp hp5 Q hQD hXD hXn hXK hXA hNp ψ hC γ hγ)
  refine ⟨fun f hf hmod => ?_, fun f hf hmod => ?_⟩
  · obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hmod
    let eC : AdjointQuotient .G2 k ≃* adjointGroup .G2 k :=
      (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot
    refine key _ (eS.symm.trans (e.trans eC)) fun U A hAodd hA3 hAU α hαA hαU => ?_
    obtain ⟨i, -, hi⟩ := (even_G2_common_Sylow_normalizer_acts_by_field_power_on_odd_subgroup hf k
      hk U A hAodd hA3 hAU).2.1 α hαA hαU
    exact ⟨i, hi⟩
  · obtain ⟨k, _, _, σ, hk, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hmod.2
    refine key _ (eS.symm.trans e) fun U A hAodd hA3 hAU α hαA hαU => ?_
    obtain ⟨i, -, hi⟩ := (even_triality_common_Sylow_normalizer_acts_by_field_power_on_odd_subgroup
      hf k hk σ hσ U A hAodd hA3 hAU).2.1 α hαA hαU
    exact ⟨i, hi⟩

end CFSG.Quasithin.H13.NQSetup
