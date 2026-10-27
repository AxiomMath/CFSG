module

public import CFSG.Quasithin.H13.NQCatD4Center
public import CFSG.Quasithin.H13.NQCatG24Split

public section

namespace CFSG.Quasithin.H13.NQCat.F112D4

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.L239.Lie

section Abstract

variable {G : Type*} [Group G] [Finite G]

theorem perfectCore_le_of_parabolicFacts {P Q N : Subgroup G} (hF : ParabolicFacts P Q)
    (hNP : N ≤ P) (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hN : ¬ Group.IsSolvable N) :
    perfectCore P ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := perfectCore P with hC
  set D := perfectCore N with hD
  have hCP : C ≤ P := perfectCore_le P
  have hDC : D ≤ C := perfectCore_mono hNP
  have hPD : P ≤ Subgroup.normalizer (D : Set G) :=
    hPN.trans (normalizer_le_normalizer_perfectCore N)
  have hDQ : ¬ D ≤ Q := fun hle => hN ((isSolvable_iff_perfectCore_eq_bot N).2
    (G24Split.eq_bot_of_perfect_of_isPGroup (perfectCore_perfect N) (hF.pGroup.to_le hle)))
  rcases hF.levi with hCQ | ⟨hQ, T, _, g, hT, hg, hker⟩
  · exact absurd (hDC.trans hCQ) hDQ
  have hQC : Q ≤ C := by
    refine hQ.trans (Subgroup.commutator_le.2 fun x hx c hc => ?_)
    have hxN : x ∈ Subgroup.normalizer (C : Set G) :=
      normalizer_le_normalizer_perfectCore P (Subgroup.le_normalizer (hF.le hx))
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 hxN c).1 hc) (inv_mem hc)
  have himg : ∀ A : Subgroup G, A ≤ C → C ≤ Subgroup.normalizer (A : Set G) →
      (A.subgroupOf C).map g = ⊥ ∨ (A.subgroupOf C).map g = ⊤ := fun A hAC hCA => by
    have hn : (A.subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAC).2 hCA
    have := hn.map g hg
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal _
  have hbot : ∀ A : Subgroup G, (hAC : A ≤ C) → (A.subgroupOf C).map g = ⊥ → A ≤ Q :=
    fun A hAC h0 x hx => by
      have h1 := Subgroup.mem_map_of_mem g
        (show (⟨x, hAC hx⟩ : ↥C) ∈ A.subgroupOf C from hx)
      rw [h0, Subgroup.mem_bot] at h1
      exact hker _ h1
  have hCD : C ≤ D := by
    rcases himg D hDC (hCP.trans hPD) with h0 | htop
    · exact absurd (hbot D hDC h0) hDQ
    have hCDQ : C = D ⊔ Q := by
      refine le_antisymm (fun x hx => ?_) (sup_le hDC hQC)
      have h1 : g ⟨x, hx⟩ ∈ (D.subgroupOf C).map g := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨d, hd, hdx⟩ := h1
      have hq : ((d⁻¹ * ⟨x, hx⟩ : ↥C) : G) ∈ Q :=
        hker _ (by rw [map_mul, map_inv, hdx, inv_mul_cancel])
      have hx' : x = (d : G) * ((d⁻¹ * ⟨x, hx⟩ : ↥C) : G) := by simp
      rw [hx']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right hq)
    have hDn : (D.subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hDC).2 (hCP.trans hPD)
    have : Group.IsNilpotent Q := hF.pGroup.isNilpotent
    have h1 := perfectCore_le_of_sup_solvable hDC hDn hCDQ inferInstance
    rwa [perfectCore_eq_self_of_perfect (perfectCore_perfect P)] at h1
  exact hCD.trans (perfectCore_le N)

theorem card_le_card_oTwoQuot {P N : Subgroup G} (hCN : perfectCore P ≤ N) {T : Type*} [Group T]
    [IsSimpleGroup T] (hTp : Group.IsPerfect T) (g : ↥(perfectCore P) →* T)
    (hg : Function.Surjective g) : Nat.card T ≤ Nat.card (oTwoQuot ↥N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite T := Finite.of_surjective g hg
  let ι : ↥(perfectCore P) →* oTwoQuot ↥N :=
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥N)).comp (Subgroup.inclusion hCN)
  have hker : ι.ker ≤ g.ker := by
    have hn := (MonoidHom.normal_ker ι).map g hg
    rcases hn.eq_bot_or_eq_top with h0 | htop
    · intro x hx
      have : g x ∈ ι.ker.map g := ⟨x, hx, rfl⟩
      rwa [h0, Subgroup.mem_bot] at this
    · exfalso
      have hp : IsPGroup 2 T := by
        intro t
        have ht : t ∈ ι.ker.map g := htop ▸ Subgroup.mem_top t
        obtain ⟨x, hx, rfl⟩ := ht
        have hx' : (Subgroup.inclusion hCN x : ↥N) ∈ CFSG.Open.pCore 2 ↥N :=
          (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hx)
        obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥N)) ⟨_, hx'⟩
        refine ⟨k, ?_⟩
        have hk' : x ^ 2 ^ k = 1 := by
          apply Subgroup.inclusion_injective hCN
          have := congrArg Subtype.val hk
          simpa using this
        rw [← map_pow, hk', map_one]
      exact Group.IsPerfect.not_isNilpotent T hp.isNilpotent
  let g' : ι.range →* T := (MonoidHom.liftOfSurjective ι.rangeRestrict ι.rangeRestrict_surjective)
    ⟨g, by rw [MonoidHom.ker_rangeRestrict]; exact hker⟩
  have hg' : Function.Surjective g' := fun t => by
    obtain ⟨x, rfl⟩ := hg t
    exact ⟨ι.rangeRestrict x, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x⟩
  exact (Nat.card_le_card_of_surjective g' hg').trans (Subgroup.card_le_card_group _)

end Abstract

section D4

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

omit [Finite K] in
theorem weyl_x6_x5
    (b : trialityFixedField K σ.toRingHom) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection fa1) *
        ox₆ σ b * (canonicalRep (coxeterSystem TwistTag.D4.tag) K
          (TwistTag.D4.orbitReflection fa1))⁻¹ = ox₅ σ b := by
  have hroot6 : IsRoot TwistTag.D4.tag (trialityRoot 5) := (isRoot_trialityRoot 5 0).1
  have hr1 : TwistTag.D4.orbitReflection fa1 • trialityRoot 5 = trialityRoot 4 := by
    have hw : TwistTag.D4.orbitWord fa1 = [⟨2, by decide⟩] := by decide
    unfold TwistTag.orbitReflection
    rw [hw, CoxeterSystem.wordProd_singleton, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  have := canonicalRep_conj_charTwo' (K := K) (TwistTag.D4.orbitReflection fa1) hroot6 (b : K)
  rw [hr1] at this
  exact this

include hσ3 in
theorem eq_one_of_mem_centralizer_perfectCore_a1
    (hk4 : 4 ≤ Nat.card ↥(trialityFixedField K σ.toRingHom)) {z : ModGL TwistTag.D4.tag K}
    (hz : z ∈ P1 σ) (hzc : z ∈ Subgroup.centralizer
      (perfectCore (P1 σ) : Set (ModGL TwistTag.D4.tag K))) : z = 1 := by
  have hU := isPGroup_posUnipotent σ hσ3
  obtain ⟨-, -, -, hsc⟩ := library_facts σ fa1 singleton_ne_univ_fa1
  obtain ⟨-, -, -, hsc0⟩ := library_facts σ fa0 singleton_ne_univ_fa0
  have hQC : Q1 σ ≤ perfectCore (P1 σ) := by
    refine (generation_a1 σ hσ3 hU hk4).trans (Subgroup.commutator_le.2 fun x hx c hc => ?_)
    have hxN : x ∈ Subgroup.normalizer (perfectCore (P1 σ) : Set (ModGL TwistTag.D4.tag K)) :=
      normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer
        ((library_facts σ fa1 singleton_ne_univ_fa1).1 hx))
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 hxN c).1 hc) (inv_mem hc)
  have hcomm : ∀ y ∈ perfectCore (P1 σ), z * y = y * z := fun y hy =>
    ((Subgroup.mem_centralizer_iff.1 hzc) y hy).symm
  have hzQ1 : z ∈ Q1 σ := hsc ⟨hz, Subgroup.mem_centralizer_iff.2 fun y hy =>
    ((hcomm y (hQC hy))).symm⟩
  have hcard : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa1) =
      Nat.card ↥(trialityFixedField K σ.toRingHom) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun c =>
      (mem_orbitField_D4_one σ).trans (mem_trialityFixedField (K := K) (σ := σ.toRingHom)).symm)
  obtain ⟨R, hRx, -, hRW, hRP, -⟩ := levi_package σ fa1 hU
    (CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (hcard ▸ hk4))
  have hx2 : ∀ b : trialityFixedField K σ.toRingHom, z * ox₂ σ b = ox₂ σ b * z := fun b => by
    have hb : (b : K) ∈ orbitField TwistTag.D4 K σ.toRingHom fa1 :=
      (mem_orbitField_D4_one σ).2 ((mem_trialityFixedField (K := K) (σ := σ.toRingHom)).1 b.2)
    rw [← orbitX_fa1_eq σ ⟨b, hb⟩ b rfl, ← hRx]
    exact hcomm _ (hRP ⟨_, rfl⟩)
  have hzQ0c : z ∈ Subgroup.centralizer (Q0 σ : Set (ModGL TwistTag.D4.tag K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨b, c, d, e, f, rfl⟩ := (mem_radical_a0_iff σ hσ3).1 hy
    have h3 := hcomm _ (hQC (ox₃_mem_Q1 σ hσ3 c))
    have h4 := hcomm _ (hQC (ox₄_mem_Q1 σ hσ3 d))
    have h5 := hcomm _ (hQC (ox₅_mem_Q1 σ hσ3 e))
    have h6 := hcomm _ (hQC (ox₆_mem_Q1 σ hσ3 f))
    have h2 := hx2 b
    simp only [← mul_assoc]
    rw [mul_assoc _ _ z, ← h6, ← mul_assoc, mul_assoc _ (ox₅ σ e) z, ← h5, ← mul_assoc,
      mul_assoc _ (ox₄ σ d) z, ← h4, ← mul_assoc, mul_assoc _ (ox₃ σ c) z, ← h3, ← mul_assoc,
      h2]
  have hzP0 : z ∈ P0 σ :=
    graphFixedPosUnipotent_le_graphFixedRootBorel.trans
      (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _)
      (graphFixedParabolicRadical_le_graphFixedPosUnipotent _ hzQ1)
  obtain ⟨f, rfl⟩ := D4Center.eq_ox₆_of_mem_center_a0 σ hσ3 ⟨hsc0 ⟨hzP0, hzQ0c⟩, hzQ0c⟩
  have hn := hcomm _ (hRP ⟨WSL, rfl⟩)
  rw [hRW] at hn
  have h1 : canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection fa1) *
      ox₆ σ f * (canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection fa1))⁻¹ = ox₆ σ f := by
    rw [← hn, mul_inv_cancel_right]
  rw [weyl_x6_x5] at h1
  have h2 : ox₁ σ 0 * ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0 * ox₅ σ f * ox₆ σ 0 =
      ox₁ σ 0 * ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0 * ox₅ σ 0 * ox₆ σ f := by
    rw [ox₁_zero σ hσ3, ox₂_zero σ hσ3, ox₃_zero σ hσ3, ox₄_zero σ hσ3, ox₅_zero σ hσ3,
      ox₆_zero σ hσ3, h1]
    simp
  obtain ⟨-, -, -, -, he, -⟩ := coord_unique σ hσ3 h2
  rw [he, ox₆_zero σ hσ3]

include hσ3 in
theorem card_le_card_oTwoQuot_a0
    (hK4 : 4 ≤ Nat.card K) {N : Subgroup (ModGL TwistTag.D4.tag K)} (hNP : N ≤ P0 σ)
    (hPN : P0 σ ≤ Subgroup.normalizer (N : Set (ModGL TwistTag.D4.tag K)))
    (hN : ¬ Group.IsSolvable N) : Nat.card K ≤ Nat.card (oTwoQuot ↥N) := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hCN := perfectCore_le_of_parabolicFacts (parabolicFacts_a0 σ hσ3 hK4) hNP hPN hN
  have hU := isPGroup_posUnipotent σ hσ3
  have htop : orbitField TwistTag.D4 K σ.toRingHom fa0 = ⊤ :=
    orbitField_D4_zero_eq_top σ (fun c => ringHom_apply_apply_apply_of_pow_three hσ3 c)
  have hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom fa0), s.card = 4 := by
    have hc : 4 ≤ Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa0) := by
      rw [htop, Nat.card_congr Subfield.topEquiv.toEquiv]
      exact hK4
    exact CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four hc
  obtain ⟨R, hRx, -, -, -, hsimple, g, hg, -⟩ := levi_package σ fa0 hU hL4
  have : Group.IsPerfect (SL2 ↥(orbitField TwistTag.D4 K σ.toRingHom fa0)) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect hL4
  have h1 := card_le_card_oTwoQuot hCN (Group.IsPerfect.range R) g hg
  refine le_trans ?_ h1
  have hmem : ∀ c : K, c ∈ orbitField TwistTag.D4 K σ.toRingHom fa0 := fun c => htop ▸ trivial
  refine Nat.card_le_card_of_injective (fun c : K => ⟨R (uSL ⟨c, hmem c⟩), ⟨_, rfl⟩⟩) ?_
  intro c c' hcc'
  have e : ((orbitX TwistTag.D4 K σ.toRingHom fa0 ⟨c, hmem c⟩ : _) :
      ModGL TwistTag.D4.tag K) = ((orbitX TwistTag.D4 K σ.toRingHom fa0 ⟨c', hmem c'⟩ : _) :
        ModGL TwistTag.D4.tag K) := by
    rw [← hRx, ← hRx]
    exact congrArg Subtype.val hcc'
  have e2 : orbitXEquiv TwistTag.D4 σ.toRingHom fa0 (Multiplicative.ofAdd ⟨c, hmem c⟩) =
      orbitXEquiv TwistTag.D4 σ.toRingHom fa0 (Multiplicative.ofAdd ⟨c', hmem c'⟩) := by
    apply Subtype.ext
    rw [coe_orbitXEquiv, coe_orbitXEquiv]
    exact e
  have e3 := (orbitXEquiv TwistTag.D4 σ.toRingHom fa0).injective e2
  have e4 : (⟨c, hmem c⟩ : ↥(orbitField TwistTag.D4 K σ.toRingHom fa0)) = ⟨c', hmem c'⟩ :=
    Multiplicative.ofAdd.injective e3
  exact congrArg Subtype.val e4

end D4

section Main

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

theorem not_isSolvable_of_isL2Quot_two {X : Type*} [Group X] (h : IsL2Quot 2 X) :
    ¬ Group.IsSolvable X := by
  obtain ⟨e⟩ := h
  have hL4 : ∃ s : Finset (GaloisField 2 2), s.card = 4 := by
    have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    refine ⟨Finset.univ, ?_⟩
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect hL4
  let e' : X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
    e.trans (pslTwoGf2EquivSl 2)
  have hX : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := e'.symm.toMonoidHom)
    e'.symm.surjective
  have hc : Nat.card X = 60 := by
    rw [IsL2Quot.card (by norm_num) ⟨e⟩]
    norm_num
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.1 (by rw [hc]; norm_num)
  exact Group.IsPerfect.not_isSolvable X

end Main

end CFSG.Quasithin.H13.NQCat.F112D4
