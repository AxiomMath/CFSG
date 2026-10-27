module

public import CFSG.Quasithin.H13.NQCatExcParO2
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528SKG
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.LieType.Chevalley.G2FieldFourCoverRoots
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin.H13.NQCat.ExcParSq

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.A5.G3
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped Pointwise

abbrev OrdCond {X : Type*} [Group X] (c : ℕ → ℕ → Prop) (A : Subgroup X) : Prop :=
  c (Nat.card ↥A) (Nat.card (CFSG.pCore 2 ↥A))

theorem OrdCond.of_equiv {X Y : Type*} [Group X] [Group Y] {c : ℕ → ℕ → Prop} {A : Subgroup X}
    {B : Subgroup Y} (e : ↥A ≃* ↥B) (h : OrdCond c B) : OrdCond c A := by
  have h1 : Nat.card ↥A = Nat.card ↥B := Nat.card_congr e.toEquiv
  have h2 : Nat.card (CFSG.pCore 2 ↥A) = Nat.card (CFSG.pCore 2 ↥B) := by
    rw [← CFSG.pCore_map_iso 2 e]
    exact (Subgroup.card_map_of_injective e.injective).symm
  rw [OrdCond, h1, h2]
  exact h

theorem ordCond_bot {X : Type*} [Group X] {c : ℕ → ℕ → Prop} (h : c 1 1) :
    OrdCond c (⊥ : Subgroup X) := by
  have h2 : Nat.card (CFSG.pCore 2 ↥(⊥ : Subgroup X)) = 1 := by
    rw [Subgroup.eq_bot_of_subsingleton (CFSG.pCore 2 ↥(⊥ : Subgroup X)), Subgroup.card_bot]
  rw [OrdCond, Subgroup.card_bot, h2]
  exact h

theorem ordCond_of_subgroupOf {G : Type} [Group G] [Finite G] {c : ℕ → ℕ → Prop}
    {L P : Subgroup G} (hP : IsParabolic2 L P)
    (h : ∀ Pa : Subgroup ↥L, IsParabolic2 (⊤ : Subgroup ↥L) Pa → (Pa = ⊤ ↔ P = L) →
      OrdCond c (perfectCore Pa)) :
    OrdCond c (perfectCore P) := by
  have hmap : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hP.1
  have hpar : IsParabolic2 (⊤ : Subgroup ↥L) (P.subgroupOf L) := by
    rw [A312.isParabolic2_top_iff, hmap]
    exact hP
  have htop : P.subgroupOf L = ⊤ ↔ P = L := by
    constructor
    · intro ht
      have := congrArg (Subgroup.map L.subtype) ht
      rw [hmap, Subgroup.map_top, Subgroup.range_subtype] at this
      exact this
    · intro hPL
      rw [hPL]
      exact Subgroup.subgroupOf_self L
  have hcore : (perfectCore (P.subgroupOf L)).map L.subtype = perfectCore P := by
    rw [map_perfectCore, hmap]
  exact OrdCond.of_equiv (((perfectCore (P.subgroupOf L)).equivMapOfInjective L.subtype
    L.subtype_injective).trans (MulEquiv.subgroupCongr hcore)).symm (h _ hpar htop)

theorem ordCond_of_map_equiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    {c : ℕ → ℕ → Prop} (e : X ≃* Y) {Pa : Subgroup X}
    (h : OrdCond c (perfectCore (Pa.map e.toMonoidHom))) : OrdCond c (perfectCore Pa) :=
  OrdCond.of_equiv (((perfectCore Pa).equivMapOfInjective e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr (map_perfectCore e.toMonoidHom Pa))) h

theorem ordCond_of_parabolic {S : Type} [Group S] [Finite S] {c : ℕ → ℕ → Prop}
    {U : Subgroup S} (hU : IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup S}
    (hP : ResidualOvergroupsAt S U P) (hbot : c 1 1) (hPj : ∀ j, OrdCond c (perfectCore (P j)))
    {Pa : Subgroup S} (hpar : IsParabolic2 (⊤ : Subgroup S) Pa) (hne : Pa ≠ ⊤) :
    OrdCond c (perfectCore Pa) := by
  rcases perfectCore_parabolic_cases hU hP hpar hne with h | ⟨j, ⟨e⟩⟩
  · rw [h]
    exact ordCond_bot hbot
  · exact OrdCond.of_equiv e (hPj j)

theorem ordCond_subgroupOf_of {G : Type} [Group G] [Finite G] {c : ℕ → ℕ → Prop}
    {C P : Subgroup G} (hPC : P ≤ C) (h : OrdCond c (perfectCore P)) :
    OrdCond c (perfectCore (P.subgroupOf C)) := by
  have hcore : (perfectCore (P.subgroupOf C)).map C.subtype = perfectCore P := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPC]
  exact OrdCond.of_equiv (((perfectCore (P.subgroupOf C)).equivMapOfInjective
    C.subtype C.subtype_injective).trans (MulEquiv.subgroupCongr hcore)) h

theorem parabolicFacts_cases {G : Type*} [Group G] [Finite G] {P Q : Subgroup G}
    (hF : ParabolicFacts P Q) :
    Nat.card (CFSG.pCore 2 ↥(perfectCore P)) = Nat.card ↥(perfectCore P) ∨
      Nat.card ↥Q ≤ Nat.card (CFSG.pCore 2 ↥(perfectCore P)) := by
  rcases hF.levi with hle | ⟨hQ, -⟩
  · left
    have hp : IsPGroup 2 ↥(perfectCore P) := hF.pGroup.to_le hle
    have htop : CFSG.pCore 2 ↥(perfectCore P) = ⊤ :=
      top_unique (le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩)
    rw [htop, Subgroup.card_top]
  · right
    have hQC : Q ≤ perfectCore P := by
      refine hQ.trans (Subgroup.commutator_le.2 fun q hq c hc => ?_)
      have hqN : q ∈ Subgroup.normalizer (perfectCore P : Set G) :=
        normalizer_le_normalizer_perfectCore P (Subgroup.le_normalizer (hF.le hq))
      rw [commutatorElement_def]
      exact mul_mem ((Subgroup.mem_normalizer_iff.1 hqN c).1 hc) (inv_mem hc)
    have hn : (Q.subgroupOf (perfectCore P)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQC).2
        ((perfectCore_le P).trans hF.normalizes)
    have hle : Q.subgroupOf (perfectCore P) ≤ CFSG.pCore 2 ↥(perfectCore P) :=
      le_sSup ⟨hn, hF.pGroup.comap_subtype⟩
    calc Nat.card ↥Q = Nat.card ↥(Q.subgroupOf (perfectCore P)) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv).symm
      _ ≤ Nat.card (CFSG.pCore 2 ↥(perfectCore P)) := Subgroup.card_le_of_le hle

@[expose] def NoSq (a b : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → a = b * (2 ^ m * ((2 ^ m) ^ 2 - 1)) → b ≠ (2 ^ m) ^ 2

theorem six_le (m : ℕ) (hm : 1 ≤ m) : 6 ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h3 : 3 ≤ (2 ^ m) ^ 2 - 1 := by
    have : 4 ≤ (2 ^ m) ^ 2 := by nlinarith
    omega
  nlinarith

theorem noSq_one : NoSq 1 1 := fun m hm h => by
  have := six_le m hm
  omega

theorem sq_lt_cube {u v r : ℕ} (h : u ≤ v * r) (hr : r ^ 3 < u) : u ^ 2 < v ^ 3 := by
  by_contra hcon
  push Not at hcon
  have h1 : u ^ 3 ≤ v ^ 3 * r ^ 3 := by
    calc u ^ 3 ≤ (v * r) ^ 3 := Nat.pow_le_pow_left h 3
      _ = v ^ 3 * r ^ 3 := by ring
  have h2 : v ^ 3 * r ^ 3 ≤ u ^ 2 * r ^ 3 := Nat.mul_le_mul_right _ hcon
  have hu : 0 < u ^ 2 := by
    have : 0 < u := lt_of_le_of_lt (Nat.zero_le _) hr
    positivity
  have h3 : u ^ 2 * r ^ 3 < u ^ 2 * u := Nat.mul_lt_mul_of_pos_left hr hu
  have h4 : u ^ 2 * u = u ^ 3 := by ring
  omega

theorem noSq_of_parabolicFacts {G : Type*} [Group G] [Finite G] {C U P Q : Subgroup G}
    (hU : IsSylowTwoOf U C) (hPC : P ≤ C) (hF : ParabolicFacts P Q) {r : ℕ}
    (hr : Nat.card ↥U ≤ Nat.card ↥Q * r) (hr3 : r ^ 3 < Nat.card ↥U) :
    OrdCond NoSq (perfectCore P) := by
  intro m hm hcard hsq
  rcases parabolicFacts_cases hF with htop | hQO
  · rw [htop] at hcard
    have hpos : 0 < Nat.card ↥(perfectCore P) := Nat.card_pos
    have := six_le m hm
    nlinarith
  · rw [hsq] at hQO hcard
    have h1 : (2 ^ m) ^ 3 ∣ Nat.card ↥(perfectCore P) :=
      ⟨(2 ^ m) ^ 2 - 1, by rw [hcard]; ring⟩
    have h2 : Nat.card ↥(perfectCore P) ∣ Nat.card ↥C :=
      Subgroup.card_dvd_of_le ((perfectCore_le P).trans hPC)
    have h3 : Nat.card ↥C = Nat.card ↥U * (U.subgroupOf C).index := by
      rw [← Subgroup.card_mul_index (U.subgroupOf C),
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU.1).toEquiv]
    have hcop : Nat.Coprime ((2 ^ m) ^ 3) (U.subgroupOf C).index := by
      rw [← pow_mul]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hU.2.2)
    have h4 : (2 ^ m) ^ 3 ∣ Nat.card ↥U := hcop.dvd_of_dvd_mul_right (h3 ▸ h1.trans h2)
    have h5 : (2 ^ m) ^ 3 ≤ Nat.card ↥U := Nat.le_of_dvd Nat.card_pos h4
    have h6 : Nat.card ↥Q ^ 3 ≤ Nat.card ↥U ^ 2 := by
      calc Nat.card ↥Q ^ 3 ≤ ((2 ^ m) ^ 2) ^ 3 := Nat.pow_le_pow_left hQO 3
        _ = ((2 ^ m) ^ 3) ^ 2 := by ring
        _ ≤ Nat.card ↥U ^ 2 := Nat.pow_le_pow_left h5 2
    have h7 := sq_lt_cube hr hr3
    omega

theorem ncard_radicalRoots_g2 (i : Fin Tag.G2.rank) :
    (parabolicRadicalRoots Tag.G2 ({i} : Set (Fin Tag.G2.rank))).ncard = 5 := by
  rcases G2.fin_two_cases i with rfl | rfl
  · rw [G2.radicalRoots_zero, show ({G2.rR, G2.rU, G2.rV, G2.rB, G2.rC} :
        Set (Fin Tag.G2.rank → ℤ)) = ↑({G2.rR, G2.rU, G2.rV, G2.rB, G2.rC} :
          Finset (Fin Tag.G2.rank → ℤ)) by simp, Set.ncard_coe_finset]
    decide +kernel
  · rw [G2.radicalRoots_one, show ({G2.rA, G2.rU, G2.rV, G2.rB, G2.rC} :
        Set (Fin Tag.G2.rank → ℤ)) = ↑({G2.rA, G2.rU, G2.rV, G2.rB, G2.rC} :
          Finset (Fin Tag.G2.rank → ℤ)) by simp, Set.ncard_coe_finset]
    decide +kernel

theorem noSq_g2
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (i : Fin Tag.G2.rank) : OrdCond NoSq (perfectCore (parabolicSubgroup Tag.G2 K {i})) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hU : IsSylowTwoOf (posUnipotent Tag.G2 K) (adjointGroup Tag.G2 K) :=
    isSylowTwoOf_iff_isSylowOf.2 (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1
  have hF : ParabolicFacts (parabolicSubgroup Tag.G2 K {i}) (parabolicRadical Tag.G2 K {i}) := by
    rcases G2.fin_two_cases i with rfl | rfl
    · exact G2.parabolicFacts_zero hK hf
    · exact G2.parabolicFacts_one hK hf
  have hUcard : Nat.card ↥(posUnipotent Tag.G2 K) = Nat.card K ^ 6 := by
    rw [card_posUnipotent, CFSG.LieType.Chevalley.G2FieldFour.ncard_posRoots]
  have hQcard : Nat.card ↥(parabolicRadical Tag.G2 K {i}) = Nat.card K ^ 5 := by
    rw [card_parabolicRadical, ncard_radicalRoots_g2]
  have hq : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine noSq_of_parabolicFacts hU (parabolicSubgroup_le_adjointGroup _ _ _) hF
    (r := Nat.card K) ?_ ?_
  · rw [hUcard, hQcard, ← pow_succ]
  · rw [hUcard]
    exact Nat.pow_lt_pow_right hq (by norm_num)

theorem noSq_g2_max
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hf : 2 ≤ f) (hL : IsG2 2 f ↥L) (hP : IsMaxParabolic2 L P) :
    OrdCond NoSq (perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine ordCond_of_subgroupOf hpar fun Pa hpa htop => ?_
  have hna : Pa ≠ ⊤ := fun h => hne (htop.1 h)
  obtain ⟨-, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  refine ordCond_of_map_equiv e ?_
  refine ordCond_of_parabolic hU₀ G2_residualOvergroupsAt noSq_one (fun j => ?_)
    (isParabolic2_top_map_equiv e hpa) (map_ne_top_of_equiv e hna)
  exact ordCond_subgroupOf_of (parabolicSubgroup_le_adjointGroup _ _ _) (noSq_g2 hK hf _)

theorem card_le_card_mul_orbitField
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (a : Fin TwistTag.D4.foldedTag.rank) :
    Nat.card ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) ≤
      Nat.card ↥(graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a) *
        Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨-, -, hset, -⟩ := fixed_simple_positive_complement TwistTag.D4 K σ a
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective (fun p => ⟨(p.1 : ModGL TwistTag.D4.tag K) *
    (orbitX TwistTag.D4 K σ.toRingHom a p.2 : ModGL TwistTag.D4.tag K), ?_⟩) ?_
  · have h : (p.1 : ModGL TwistTag.D4.tag K) *
        (orbitX TwistTag.D4 K σ.toRingHom a p.2 : ModGL TwistTag.D4.tag K) ∈
          (graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a : Set (ModGL TwistTag.D4.tag K)) *
            Set.range (fun c : orbitField TwistTag.D4 K σ.toRingHom a =>
              (orbitX TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K)) :=
      Set.mul_mem_mul p.1.2 ⟨p.2, rfl⟩
    rw [← hset] at h
    exact h
  · intro u
    have hu : (u : ModGL TwistTag.D4.tag K) ∈
        (graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a : Set (ModGL TwistTag.D4.tag K)) *
          Set.range (fun c : orbitField TwistTag.D4 K σ.toRingHom a =>
            (orbitX TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K)) := by
      rw [← hset]
      exact u.2
    obtain ⟨v, hv, _, ⟨c, rfl⟩, hvc⟩ := hu
    exact ⟨(⟨v, hv⟩, c), Subtype.ext hvc⟩

theorem noSq_d4
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (a : Fin TwistTag.D4.foldedTag.rank) :
    OrdCond NoSq (perfectCore (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a})) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    ext c
    simp only [RingHom.coe_pow, Function.iterate_succ, Function.comp_apply, Function.iterate_zero,
      id_eq, RingHom.one_def, RingHom.id_apply]
    show σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    let _ := Fintype.ofFinite K
    have hq : 2 ^ f * (2 ^ f * 2 ^ f) = Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, hK]
      ring
    rw [hq]
    exact FiniteField.pow_card c
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (2 ^ f) ^ 3 := by rw [← pow_mul, mul_comm]
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hU : IsSylowTwoOf (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hcases : a = D4.fa0 ∨ a = D4.fa1 := by
    revert a
    decide
  have hF : ParabolicFacts (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a})
      (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {a}) := by
    rcases hcases with rfl | rfl
    · exact D4.parabolicFacts_a0 σ hσ3 hK4
    · exact D4.parabolicFacts_a1 σ hσ3
  have hQV : graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {a} =
      graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a := by
    rcases hcases with rfl | rfl
    · exact D4.radical_eq_simpleComplement _ _ D4.supp_fa0
    · exact D4.radical_eq_simpleComplement _ _ D4.supp_fa1
  have hσ' : ∀ c, σ.toRingHom c = c ^ ((2 ^ f) ^ 1) := fun c => by
    rw [pow_one]
    exact hσ c
  have hUcard : Nat.card ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) = (2 ^ f) ^ 12 :=
    (triality_both_orientations_exact_finite_order 2 f Nat.prime_two hf K hK 1 (Or.inl rfl)
      σ.toRingHom hσ').2.2
  have hLa : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) =
      (2 ^ f) ^ (TwistTag.D4.orbit a).card :=
    card_orbitField_D4_orientation Nat.prime_two hf hK (Or.inl rfl) hσ' a
  have horb : (TwistTag.D4.orbit a).card ≤ 3 := by
    rcases hcases with rfl | rfl <;> decide
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine noSq_of_parabolicFacts hU (graphFixedParabolic_le _ _ _ _) hF
    (r := (2 ^ f) ^ (TwistTag.D4.orbit a).card) ?_ ?_
  · rw [hQV, ← hLa]
    exact card_le_card_mul_orbitField σ a
  · rw [hUcard, ← pow_mul]
    exact Nat.pow_lt_pow_right hq (by omega)

theorem noSq_d4_max
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hf : 1 ≤ f) (hL : Is3D4 2 f ↥L) (hP : IsMaxParabolic2 L P) :
    OrdCond NoSq (perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine ordCond_of_subgroupOf hpar fun Pa hpa htop => ?_
  have hna : Pa ≠ ⊤ := fun h => hne (htop.1 h)
  obtain ⟨-, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hL
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : IsSylowTwoOf (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  refine ordCond_of_map_equiv e ?_
  refine ordCond_of_parabolic (isSylowTwoOf_subgroupOf_top hUsyl)
    (triality_residualOvergroupsAt σ) noSq_one (fun j => ?_)
    (isParabolic2_top_map_equiv e hpa) (map_ne_top_of_equiv e hna)
  exact ordCond_subgroupOf_of (graphFixedParabolic_le _ _ _ _) (noSq_d4 σ hf hK hσ _)

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution in
theorem noSq_f4
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (j : Fin F4.fixedOrbitCount) :
    OrdCond NoSq (perfectCore (F4.reeLocalParabolic K a j)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hU : IsSylowTwoOf (F4.reeFixedPosUnipotent K a) (F4.reeGamma K a) :=
    ⟨hUC, isPGroup_reeFixedPosUnipotent_subgroupOf.of_equiv (Subgroup.subgroupOfEquivOfLe hUC),
      not_dvd_index_reeFixedPosUnipotent⟩
  have hPC : F4.reeLocalParabolic K a j ≤ F4.reeGamma K a := by
    rw [← reeParabolic_singleton (t := F4) (K := K) (a := a)]
    exact reeParabolic_le F4 K a _
  obtain ⟨hF0, hF1⟩ := F4.largeReeParabolicFacts a K ha hK
  have hUcard := card_reeFixedPosUnipotent hK
  have hprod := card_reeFixedPosUnipotent_eq_mul (K := K) (a := a) j
  have hq : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨j, hj⟩ := j
  have hj2 : j < 2 := hj
  interval_cases j
  · refine noSq_of_parabolicFacts hU hPC hF0 (r := Nat.card K) ?_ ?_
    · rw [hprod, card_reeFixedOrbitUnipotent_zero hK]
    · rw [hUcard, hK]
      exact Nat.pow_lt_pow_right hq (by norm_num)
  · refine noSq_of_parabolicFacts hU hPC hF1 (r := Nat.card K ^ 2) ?_ ?_
    · rw [hprod, card_reeFixedOrbitUnipotent_one hK]
    · rw [hUcard, hK, ← pow_mul]
      exact Nat.pow_lt_pow_right hq (by norm_num)

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag in
theorem noSq_f4_max
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hL : Is2F4 f ↥L) (hP : IsMaxParabolic2 L P) : OrdCond NoSq (perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine ordCond_of_subgroupOf hpar fun Pa hpa htop => ?_
  have hna : Pa ≠ ⊤ := fun h => hne (htop.1 h)
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hL
  subst hfa
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : IsSylowTwoOf (F4.reeFixedPosUnipotent K a) (F4.reeGamma K a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  refine ordCond_of_map_equiv e ?_
  refine ordCond_of_parabolic (isSylowTwoOf_subgroupOf_top hUsyl)
    (large_Ree_residualOvergroupsAt hK) noSq_one (fun j => ?_)
    (isParabolic2_top_map_equiv e hpa) (map_ne_top_of_equiv e hna)
  refine ordCond_subgroupOf_of (reeParabolic_le F4 K a _) ?_
  rw [reeParabolic_singleton (t := F4) (K := K) (a := a)]
  exact noSq_f4 ha hK _

theorem card_psl2 {Y : Type} [Group Y] {m : ℕ} (h : IsPSL 2 2 m Y) :
    Nat.card Y = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  have hf : 1 ≤ m := h.1.2.1
  have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  have hodd : Odd (2 ^ m - 1) := by
    simpa using CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hf (n := 1) le_rfl
  have hgcd : Nat.gcd 2 (2 ^ m - 1) = 1 := Nat.coprime_two_left.mpr hodd
  rw [h1]
  unfold CFSG.Open.ordA
  norm_num [Finset.Icc_self, hgcd]

theorem factExcParabolicO2NeSq_holds :
    FactExcParabolicO2NeSq := by
  intro G _ _ L P m hm hL hP hPSL
  have hq : Nat.card (ModO2 (perfectCore P)) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := card_psl2 hPSL
  have hcard : Nat.card ↥(perfectCore P) =
      Nat.card (CFSG.pCore 2 ↥(perfectCore P)) * (2 ^ m * ((2 ^ m) ^ 2 - 1)) := by
    rw [← hq, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hc : OrdCond NoSq (perfectCore P) := by
    rcases hL with ⟨f, ⟨hf, hL⟩ | ⟨hf, hL⟩ | ⟨-, -, hL⟩⟩ | hL
    · exact noSq_g2_max L P f hf hL hP
    · exact noSq_d4_max L P f hf hL hP
    · exact noSq_f4_max L P f hL hP
    · rw [ExcPar.perfectCore_eq_bot_tits L P hL hP]
      exact ordCond_bot noSq_one
  exact hc m (by omega) hcard

end CFSG.Quasithin.H13.NQCat.ExcParSq
