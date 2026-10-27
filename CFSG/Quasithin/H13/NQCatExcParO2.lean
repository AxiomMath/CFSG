module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2Glue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListF4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice
public import CFSG.Quasithin.EmptyFaithful.SBc6Sl2
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure314
public import CFSG.Quasithin.Background.A3Structure36BCase3
public import CFSG.Quasithin.Background.A3Structure36BCases
public import CFSG.Quasithin.Background.A3Structure36BCommon
public import CFSG.Quasithin.Background.A3Structure36BStar
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut

public section

namespace CFSG.Quasithin.H13.NQCat.ExcPar

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.A5.G3
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem eq_bot_of_pCore_eq_bot_of_equiv {X Y : Type*} [Group X] [Group Y] {A : Subgroup X}
    {B : Subgroup Y} (e : ↥A ≃* ↥B) (h : CFSG.pCore 2 ↥B = ⊥ → B = ⊥)
    (hA : CFSG.pCore 2 ↥A = ⊥) : A = ⊥ := by
  have hB : B = ⊥ := h (by rw [← CFSG.pCore_map_iso 2 e, hA, Subgroup.map_bot])
  refine (Subgroup.eq_bot_iff_forall A).2 fun x hx => ?_
  have h1 : e ⟨x, hx⟩ = 1 :=
    Subtype.ext ((Subgroup.eq_bot_iff_forall B).1 hB _ (e ⟨x, hx⟩).2)
  exact congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))

theorem perfectCore_eq_bot_of_parabolicFacts {G : Type*} [Group G] {P Q : Subgroup G}
    (hF : ParabolicFacts P Q) (h : CFSG.pCore 2 ↥(perfectCore P) = ⊥) : perfectCore P = ⊥ := by
  rcases hF.levi with hle | ⟨hQ, -⟩
  · have hp : IsPGroup 2 ↥(perfectCore P) := hF.pGroup.to_le hle
    have htop : (⊤ : Subgroup ↥(perfectCore P)) ≤ CFSG.pCore 2 ↥(perfectCore P) :=
      le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩
    rw [h] at htop
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have h1 := htop (Subgroup.mem_top ⟨x, hx⟩)
    rw [Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  · exfalso
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
    rw [h] at hle
    obtain ⟨x, hx, y, -, hxy⟩ := hF.nonabelian
    have hx1 : x = 1 := by
      have h1 := hle (show (⟨x, hQC hx⟩ : ↥(perfectCore P)) ∈ Q.subgroupOf (perfectCore P)
        from hx)
      rw [Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
    exact hxy (by rw [hx1, one_mul, mul_one])

theorem perfectCore_eq_bot_of_subgroupOf {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (hP : IsParabolic2 L P) (hne : P ≠ L)
    (h : ∀ Pa : Subgroup ↥L, IsParabolic2 (⊤ : Subgroup ↥L) Pa → Pa ≠ ⊤ →
      CFSG.pCore 2 ↥(perfectCore Pa) = ⊥ → perfectCore Pa = ⊥) :
    CFSG.pCore 2 ↥(perfectCore P) = ⊥ → perfectCore P = ⊥ := by
  have hmap : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hP.1
  have hpar : IsParabolic2 (⊤ : Subgroup ↥L) (P.subgroupOf L) := by
    rw [A312.isParabolic2_top_iff, hmap]
    exact hP
  have hne' : P.subgroupOf L ≠ ⊤ := by
    intro htop
    apply hne
    have := congrArg (Subgroup.map L.subtype) htop
    rw [hmap, Subgroup.map_top, Subgroup.range_subtype] at this
    exact this
  have hcore : (perfectCore (P.subgroupOf L)).map L.subtype = perfectCore P := by
    rw [map_perfectCore, hmap]
  exact eq_bot_of_pCore_eq_bot_of_equiv (((perfectCore (P.subgroupOf L)).equivMapOfInjective
    L.subtype L.subtype_injective).trans (MulEquiv.subgroupCongr hcore)).symm (h _ hpar hne')

theorem perfectCore_eq_bot_of_map_equiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) {Pa : Subgroup X}
    (h : CFSG.pCore 2 ↥(perfectCore (Pa.map e.toMonoidHom)) = ⊥ →
      perfectCore (Pa.map e.toMonoidHom) = ⊥) :
    CFSG.pCore 2 ↥(perfectCore Pa) = ⊥ → perfectCore Pa = ⊥ :=
  eq_bot_of_pCore_eq_bot_of_equiv (((perfectCore Pa).equivMapOfInjective e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr (map_perfectCore e.toMonoidHom Pa))) h

theorem perfectCore_eq_bot_of_parabolic {S : Type} [Group S] [Finite S] {U : Subgroup S}
    (hU : IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup S} (hP : ResidualOvergroupsAt S U P)
    (hPj : ∀ j, CFSG.pCore 2 ↥(perfectCore (P j)) = ⊥ → perfectCore (P j) = ⊥)
    {Pa : Subgroup S} (hpar : IsParabolic2 (⊤ : Subgroup S) Pa) (hne : Pa ≠ ⊤) :
    CFSG.pCore 2 ↥(perfectCore Pa) = ⊥ → perfectCore Pa = ⊥ := by
  rcases perfectCore_parabolic_cases hU hP hpar hne with h | ⟨j, ⟨e⟩⟩
  · exact fun _ => h
  · exact eq_bot_of_pCore_eq_bot_of_equiv e (hPj j)

theorem perfectCore_eq_bot_subgroupOf_of {G : Type} [Group G] [Finite G] {C P : Subgroup G}
    (hPC : P ≤ C) (h : CFSG.pCore 2 ↥(perfectCore P) = ⊥ → perfectCore P = ⊥) :
    CFSG.pCore 2 ↥(perfectCore (P.subgroupOf C)) = ⊥ → perfectCore (P.subgroupOf C) = ⊥ := by
  have hcore : (perfectCore (P.subgroupOf C)).map C.subtype = perfectCore P := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPC]
  exact eq_bot_of_pCore_eq_bot_of_equiv (((perfectCore (P.subgroupOf C)).equivMapOfInjective
    C.subtype C.subtype_injective).trans (MulEquiv.subgroupCongr hcore)) h

theorem perfectCore_eq_bot_g2
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hf : 2 ≤ f) (hL : IsG2 2 f ↥L) (hP : IsMaxParabolic2 L P) :
    CFSG.pCore 2 ↥(perfectCore P) = ⊥ → perfectCore P = ⊥ := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine perfectCore_eq_bot_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  obtain ⟨-, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  refine perfectCore_eq_bot_of_map_equiv e ?_
  refine perfectCore_eq_bot_of_parabolic hU₀ G2_residualOvergroupsAt (fun j => ?_)
    (isParabolic2_top_map_equiv e hpa) (map_ne_top_of_equiv e hna)
  refine perfectCore_eq_bot_subgroupOf_of (parabolicSubgroup_le_adjointGroup _ _ _) ?_
  rcases G2.fin_two_cases (g2Index j) with h | h
  · rw [h]
    exact perfectCore_eq_bot_of_parabolicFacts (G2.parabolicFacts_zero hK hf)
  · rw [h]
    exact perfectCore_eq_bot_of_parabolicFacts (G2.parabolicFacts_one hK hf)

theorem perfectCore_eq_bot_d4
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hf : 1 ≤ f) (hL : Is3D4 2 f ↥L) (hP : IsMaxParabolic2 L P) :
    CFSG.pCore 2 ↥(perfectCore P) = ⊥ → perfectCore P = ⊥ := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine perfectCore_eq_bot_of_subgroupOf hpar hne fun Pa hpa hna => ?_
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
  have hU₀ := isSylowTwoOf_subgroupOf_top hUsyl
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
    rw [hK3]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine perfectCore_eq_bot_of_map_equiv e ?_
  refine perfectCore_eq_bot_of_parabolic hU₀ (triality_residualOvergroupsAt σ) (fun j => ?_)
    (isParabolic2_top_map_equiv e hpa) (map_ne_top_of_equiv e hna)
  refine perfectCore_eq_bot_subgroupOf_of (graphFixedParabolic_le _ _ _ _) ?_
  have hcases : ∀ i : Fin TwistTag.D4.foldedTag.rank, i = D4.fa0 ∨ i = D4.fa1 := by decide
  rcases hcases (d4Index j) with h | h
  · rw [h]
    exact perfectCore_eq_bot_of_parabolicFacts (D4.parabolicFacts_a0 σ hσ3 hK4)
  · rw [h]
    exact perfectCore_eq_bot_of_parabolicFacts (D4.parabolicFacts_a1 σ hσ3)

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag in
theorem perfectCore_eq_bot_f4
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hodd : Odd f) (hf : 3 ≤ f) (hL : Is2F4 f ↥L) (hP : IsMaxParabolic2 L P) :
    CFSG.pCore 2 ↥(perfectCore P) = ⊥ → perfectCore P = ⊥ := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine perfectCore_eq_bot_of_subgroupOf hpar hne fun Pa hpa hna => ?_
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
  have hU₀ := isSylowTwoOf_subgroupOf_top hUsyl
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨hF0, hF1⟩ := F4.largeReeParabolicFacts a K ha hK
  refine perfectCore_eq_bot_of_map_equiv e ?_
  refine perfectCore_eq_bot_of_parabolic hU₀ (large_Ree_residualOvergroupsAt hK) (fun j => ?_)
    (isParabolic2_top_map_equiv e hpa) (map_ne_top_of_equiv e hna)
  refine perfectCore_eq_bot_subgroupOf_of (reeParabolic_le F4 K a _) ?_
  rw [reeParabolic_singleton (t := F4) (K := K) (a := a)]
  rcases hcases (f4Index j) with h | h
  · rw [h]
    exact perfectCore_eq_bot_of_parabolicFacts hF0
  · rw [h]
    exact perfectCore_eq_bot_of_parabolicFacts hF1

theorem perfectCore_eq_bot_tits
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (hT : IsTits ↥L)
    (hP : IsMaxParabolic2 L P) : perfectCore P = ⊥ := by
  obtain ⟨⟨hPL, S, hS, hN⟩, hPne, -⟩ := hP
  have hU : IsSylowTwoOf (S.subgroupOf L) (⊤ : Subgroup ↥L) := isSylowTwoOf_top_subgroupOf hS
  obtain ⟨H, N, -, -, -, -, -, hlat, hHs, hNs⟩ := titsSylowOvergroupLattice ↥L hT _ hU
  have hSP : S ≤ P := fun x hx => hN ⟨hS.1 hx, Subgroup.le_normalizer hx⟩
  have hUP : S.subgroupOf L ≤ P.subgroupOf L := fun x hx => hSP hx
  have hsolv : Group.IsSolvable ↥(P.subgroupOf L) := by
    rcases hlat _ hUP with h | h | h | h
    · rw [h]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Group.IsNilpotent ↥(S.subgroupOf L) := hU.2.1.isNilpotent
      infer_instance
    · rw [h]
      exact hHs
    · rw [h]
      exact hNs
    · exfalso
      apply hPne
      refine le_antisymm hPL fun x hx => ?_
      have : (⟨x, hx⟩ : ↥L) ∈ P.subgroupOf L := h ▸ Subgroup.mem_top _
      exact this
  have hPs : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hPL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPL).symm.injective
  exact (isSolvable_iff_perfectCore_eq_bot P).mp hPs

theorem pCore_perfectCore_ne_bot
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (m : ℕ) (hm : 2 ≤ m)
    (hL : (∃ f : ℕ, (2 ≤ f ∧ IsG2 2 f ↥L) ∨ (1 ≤ f ∧ Is3D4 2 f ↥L) ∨
        (Odd f ∧ 3 ≤ f ∧ Is2F4 f ↥L)) ∨ IsTits ↥L)
    (hP : IsMaxParabolic2 L P) (hPSL : IsPSL 2 2 m (ModO2 (perfectCore P))) :
    CFSG.pCore 2 ↥(perfectCore P) ≠ ⊥ := by
  intro h
  have hbot : perfectCore P = ⊥ := by
    rcases hL with ⟨f, ⟨hf, hL⟩ | ⟨hf, hL⟩ | ⟨hodd, hf, hL⟩⟩ | hL
    · exact perfectCore_eq_bot_g2 L P f hf hL hP h
    · exact perfectCore_eq_bot_d4 L P f hf hL hP h
    · exact perfectCore_eq_bot_f4 L P f hodd hf hL hP h
    · exact perfectCore_eq_bot_tits L P hL hP
  have hs := SBc6.isSimpleGroup_of_psl (by omega : 1 < m) hPSL
  have h1 : ∀ z : ModO2 (perfectCore P), z = 1 := by
    intro z
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective z
    have ha : a = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 hbot _ a.2)
    rw [ha, QuotientGroup.mk_one]
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (ModO2 (perfectCore P))
  exact hxy ((h1 x).trans (h1 y).symm)

end CFSG.Quasithin.H13.NQCat.ExcPar
