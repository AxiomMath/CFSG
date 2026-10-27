module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofInner
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofCentJ
import CFSG.LieType.Chevalley.RootLocalComponentFree
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement

namespace KS11Lie3Proof

theorem not_hasType424_of_isCharacteristicP {Γ : Type} [Group Γ] [Finite Γ]
    (h : IsCharacteristicP 3 Γ) : ¬ KS11Lie2Proof.HasType424 Γ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro ⟨L, ⟨hLp, hLsn, hLq⟩, -⟩
  have hθΓ : aschbacherSolvableCore 3 Γ = ⊥ := by
    have := aschbacherSolvableCore_characteristic Γ
    have hn : (aschbacherSolvableCore 3 Γ).Normal := inferInstance
    exact (characteristic_p_normal_prime_complement_trivial h).1 _ hn
      (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hθL : aschbacherSolvableCore 3 L = ⊥ := by
    have h1 := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hLsn
    rw [hθΓ, inf_bot_eq] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h1
  have hLq' : IsQuasisimple L := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hθL).trans QuotientGroup.quotientBot) hLq
  exact CFSG.LieType.Chevalley.RootWeightDatum.not_isComponent_of_isCharacteristicP h L
    ⟨hLq', hLsn⟩

theorem fixSub_conj_eq_centralizer_zpowers {G : Type*} [Group G] (z : G) :
    Item426.fixSub (MulAut.conj z) = Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
  ext x
  rw [Item426.mem_fixSub, MulAut.conj_apply, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hc : Commute z x := by
      change z * x = x * z
      calc z * x = z * x * z⁻¹ * z := by group
        _ = x * z := by rw [hx]
    exact (hc.zpow_left n).eq
  · intro hx
    have h1 := hx z (Subgroup.mem_zpowers z)
    calc z * x * z⁻¹ = x * z * z⁻¹ := by rw [h1]
      _ = x := by group

theorem nonempty_derivedCentralQuotient_mulEquiv {M : Type} [Group M] (H : Subgroup M)
    [IsSimpleGroup H] (hna : ∃ x y : H, x * y ≠ y * x) :
    Nonempty (CFSG.Blueprint.DerivedCentralQuotient H ≃* H) := by
  obtain ⟨x, y, hxy⟩ := hna
  have hcomm : _root_.commutator H = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator H) with
      h | h
    · exfalso
      apply hxy
      have h1 : ⁅x, y⁆ ∈ _root_.commutator H := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [h, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    · exact h
  have hHH : ⁅H, H⁆ = H := by
    rw [← Subgroup.map_subtype_commutator, hcomm, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hcen : Subgroup.center H = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with
      h | h
    · exact h
    · exfalso
      apply hxy
      have h1 : x ∈ Subgroup.center H := by rw [h]; exact Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp h1 y).symm
  set e1 : ↥⁅H, H⁆ ≃* H := MulEquiv.subgroupCongr hHH
  have hcen' : Subgroup.center ↥⁅H, H⁆ = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e1 hcen
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcen').trans (QuotientGroup.quotientBot.trans e1)⟩

section Split

variable {F F' : ∀ (X : Type) [Group X], Prop}

@[expose] def SplitFamily (F F' : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z],
    (∃ (X : Type) (_ : Group X), F X ∧ Nonempty (Z ≃* _root_.commutator X)) →
    (∃ (X : Type) (_ : Group X), F' X ∧ Nonempty (Z ≃* _root_.commutator X)) ∨
    ∀ (z : Z) (J : Subgroup Z), MulAut.conj z ^ 3 = 1 →
      J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)) →
      IsType424 (J ⧸ aschbacherSolvableCore 3 J) → False

theorem thetaCentral119For_of_split (hs : SplitFamily F F') (h : ThetaCentral119For F') :
    ThetaCentral119For F := by
  intro Z _ _ hZ z J hz3 hJ hJT
  rcases hs Z hZ with hZ' | hno
  · exact h Z hZ' z J hz3 hJ hJT
  · exact (hno z J hz3 hJ hJT).elim

theorem normCentJ1117For_of_split (hs : SplitFamily F F') (h : NormCentJ1117For F') :
    NormCentJ1117For F := by
  intro Z _ _ hZ z J y g hz3 hJ hJT hyJ hyk hy3 hgk hgy
  rcases hs Z hZ with hZ' | hno
  · exact h Z hZ' z J y g hz3 hJ hJT hyJ hyk hy3 hgk hgy
  · exact (hno z J hz3 hJ hJT).elim

theorem centJ119InnFor_of_split (hs : SplitFamily F F') (h : CentJ119InnFor F') :
    CentJ119InnFor F := by
  intro Z _ _ hZ z b J hz3 hb hbz hJ hJT hbJ
  rcases hs Z hZ with hZ' | hno
  · exact h Z hZ' z b J hz3 hb hbz hJ hJT hbJ
  · exact (hno z J hz3 hJ hJT).elim

theorem centJ119OutFor_of_split (hs : SplitFamily F F') (h : CentJ119OutFor F') :
    CentJ119OutFor F := by
  intro Z _ _ hZ z β J hz3 hβ hzβ hJ hJT hβJ
  rcases hs Z hZ with hZ' | hno
  · exact h Z hZ' z β J hz3 hβ hzβ hJ hJT hβJ
  · exact (hno z J hz3 hJ hJT).elim

end Split

section G2Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem not_hasType424_fixSub_g2_three {K : Type} [Field K] [Finite K] [CharP K 3]
    {z : adjointGroup .G2 K} (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    ¬ KS11Lie2Proof.HasType424 (Item426.fixSub (MulAut.conj z)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hQp : IsPGroup 3 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1, pow_one])
  have hQ : Subgroup.zpowers z ≠ ⊥ := by
    intro h
    apply hz1
    have h1 : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [h, Subgroup.mem_bot] at h1
    exact h1
  obtain ⟨hchar, -⟩ :=
    (RootWeightDatum.ordinary (K := K) .G2).defining_characteristic_root_local_groups_component_free
      3 (Subgroup.zpowers z) hQp hQ _ (Or.inr rfl)
  rw [fixSub_conj_eq_centralizer_zpowers]
  exact not_hasType424_of_isCharacteristicP hchar


theorem false_of_isType424_g2_three {Z : Type} [Group Z] [Finite Z] {X : Type} [Group X]
    {q : TauCeti.PrimePower} {hq : (TauCeti.LieTypeIndex.G2 q).Valid} (hq3 : q.p = 3)
    (f : X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group) (e : Z ≃* _root_.commutator X)
    {z : Z} {J : Subgroup Z} (hz3 : MulAut.conj z ^ 3 = 1)
    (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)))
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) : False := by
  have hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) := ⟨X, inferInstance, ⟨q, hq, ⟨f⟩⟩, ⟨e⟩⟩
  have hz1 := ne_one_of_isType424_g2 hZ hJ hJT
  have hz3' : z ^ 3 = 1 := by
    have h1 := mem_center_of_conj_eq_one (x := z ^ 3) (by rw [map_pow, hz3])
    rwa [center_eq_bot_g2 Z hZ, Subgroup.mem_bot] at h1
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set K := GaloisField q.p q.exponent
  have : CharP K 3 := hq3 ▸ (inferInstance : CharP K q.p)
  have hK : Nat.card K = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card _ _ q.exponent_pos.ne'
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hq K hK
  have hXp : Group.IsPerfect X := by
    have := SetUp1118Proof.isPerfect_lie_G2 q hq
    exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  let E : Z ≃* adjointGroup Tag.G2 K :=
    ((e.trans ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans Subgroup.topEquiv)).trans
      (f.trans b.symm)).trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
  have hT := (KS11Lie2Proof.hasType424_of_mem hJ hJT).of_mulEquiv
    (KS11Lie2Proof.fixSubCongr E (MulAut.conj z))
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj] at hT
  refine not_hasType424_fixSub_g2_three (z := E z) ?_ ?_ hT
  · intro h
    exact hz1 (E.injective (h.trans (map_one E).symm))
  · rw [← map_pow, hz3', map_one]

theorem splitFamily_g2 : SplitFamily
    (fun X _ => ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group))
    (fun X _ => ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
      q.p ≠ 3 ∧ Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) := by
  intro Z _ _ hZ
  obtain ⟨X, _, ⟨q, hq, ⟨f⟩⟩, ⟨e⟩⟩ := hZ
  by_cases hq3 : q.p = 3
  · exact Or.inr fun z J hz3 hJ hJT => false_of_isType424_g2_three hq3 f e hz3 hJ hJT
  · exact Or.inl ⟨X, inferInstance, ⟨q, hq, hq3, ⟨f⟩⟩, ⟨e⟩⟩

end G2Three

section D4Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem d4_exists_e9_three {K : Type} [Field K] [Finite K] [CharP K 3] (σ : K →+* K)
    (hσ3 : σ ^ 3 = 1) (hK : 4 ≤ Nat.card K) :
    ∃ u v : graphFixedRootGroup TwistTag.D4 K σ, u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧
      u * v = v * u ∧ v ∉ Subgroup.zpowers u := by
  set a : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩ with ha
  have hcard : (TwistTag.D4.orbit a).card = 3 := by decide
  have hmem : ∀ c : K, c ∈ orbitField TwistTag.D4 K σ a := by
    intro c
    rw [mem_orbitField, hcard, hσ3]
    rfl
  let X : K → graphFixedRootGroup TwistTag.D4 K σ := fun c =>
    ⟨orbitX TwistTag.D4 K σ a ⟨c, hmem c⟩, Subgroup.mem_sup_left
      (orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ a ⟨c, hmem c⟩)⟩
  have hXadd : ∀ c d : K, X (c + d) = X c * X d := by
    intro c d
    apply Subtype.ext
    have h := orbitX_add σ a ⟨c, hmem c⟩ ⟨d, hmem d⟩
    have e : (⟨c, hmem c⟩ + ⟨d, hmem d⟩ : orbitField TwistTag.D4 K σ a) = ⟨c + d, hmem _⟩ := rfl
    rw [e] at h
    exact congrArg (fun x : adjointGroup TwistTag.D4.tag K => (x : ModGL TwistTag.D4.tag K)) h
  have hX0 : X 0 = 1 := by
    apply Subtype.ext
    have h := orbitX_zero TwistTag.D4 σ a
    exact congrArg (fun x : adjointGroup TwistTag.D4.tag K => (x : ModGL TwistTag.D4.tag K)) h
  have hXinj : Function.Injective X := by
    intro c d h
    have h1 : orbitX TwistTag.D4 K σ a ⟨c, hmem c⟩ = orbitX TwistTag.D4 K σ a ⟨d, hmem d⟩ :=
      Subtype.ext (congrArg
        (fun x : graphFixedRootGroup TwistTag.D4 K σ => (x : ModGL TwistTag.D4.tag K)) h)
    exact congrArg Subtype.val (orbitX_injective σ a h1)
  have hXpow : ∀ (c : K) (n : ℕ), X c ^ n = X (n * c) := by
    intro c n
    induction n with
    | zero => rw [pow_zero, Nat.cast_zero, zero_mul, hX0]
    | succ n ih => rw [pow_succ, ih, ← hXadd, Nat.cast_succ, add_mul, one_mul]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  obtain ⟨c, hc0, hc1, hc2⟩ : ∃ c : K, c ≠ 0 ∧ c ≠ 1 ∧ c ≠ 2 := by
    by_contra! h
    have hs : Function.Surjective fun i : Fin 3 => ((i : ℕ) : K) := by
      intro t
      by_cases ht0 : t = 0
      · exact ⟨0, by simp [ht0]⟩
      by_cases ht1 : t = 1
      · exact ⟨1, by simp [ht1]⟩
      · exact ⟨2, by rw [h t ht0 ht1]; norm_num⟩
    have := Nat.card_le_card_of_surjective _ hs
    rw [Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at this
    omega
  refine ⟨X 1, X c, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact one_ne_zero (hXinj (h.trans hX0.symm))
  · rw [hXpow, mul_one, show ((3 : ℕ) : K) = 3 by norm_num, h3, hX0]
  · rw [hXpow, show ((3 : ℕ) : K) = 3 by norm_num, h3, zero_mul, hX0]
  · rw [← hXadd, ← hXadd, add_comm]
  · intro hmem'
    rw [Subgroup.mem_zpowers_iff] at hmem'
    obtain ⟨n, hn⟩ := hmem'
    have hu3 : X 1 ^ 3 = 1 := by
      rw [hXpow, mul_one, show ((3 : ℕ) : K) = 3 by norm_num, h3, hX0]
    have hn' : X 1 ^ (n % 3).toNat = X c := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num)), ← hn]
      exact (zpow_eq_zpow_emod' n hu3).symm
    rw [hXpow, mul_one] at hn'
    have hk := hXinj hn'
    have hlt : (n % 3).toNat < 3 := by omega
    interval_cases h : (n % 3).toNat
    · exact hc0 (by rw [← hk]; simp)
    · exact hc1 (by rw [← hk]; simp)
    · exact hc2 (by rw [← hk]; norm_num)

theorem not_hasType424_d4_three {K : Type} [Field K] [Finite K] [CharP K 3] (σ : K →+* K)
    (hσ3 : σ ^ 3 = 1) (hK : 4 ≤ Nat.card K)
    [IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ)] :
    ¬ KS11Lie2Proof.HasType424 (graphFixedRootGroup TwistTag.D4 K σ) := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : IsSimpleGroup (⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ)) :=
    MulEquiv.isSimpleGroup Subgroup.topEquiv
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := d4_exists_e9_three σ hσ3 hK
  have hc : ⁅u, v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr huv
  exact KS11Lie2Proof.not_hasType424_of_simple ⊤ (fun _ _ => Subgroup.mem_top _)
    (Subgroup.mem_top u) (Subgroup.mem_top v) hu1 hu3 hv3 (by rw [hc]; exact Commute.one_left _)
    (by rw [hc]; exact Commute.one_left _) hvu

theorem not_hasType424_fixSub_d4_three {K : Type} [Field K] [Finite K] [CharP K 3]
    (σ : K ≃+* K) (hσ3 : σ ^ TwistTag.D4.order = 1)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    ¬ KS11Lie2Proof.HasType424 (Item426.fixSub (MulAut.conj z)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hQp : IsPGroup 3 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1, pow_one])
  have hQ : Subgroup.zpowers z ≠ ⊥ := by
    intro h
    apply hz1
    have h1 : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [h, Subgroup.mem_bot] at h1
    exact h1
  obtain ⟨hchar, -⟩ := (RootWeightDatum.fixed TwistTag.D4 σ hσ3
    ).defining_characteristic_root_local_groups_component_free 3 (Subgroup.zpowers z) hQp hQ _
      (Or.inr rfl)
  rw [fixSub_conj_eq_centralizer_zpowers]
  exact not_hasType424_of_isCharacteristicP hchar


theorem false_of_isType424_d4_three {Z : Type} [Group Z] [Finite Z] {X : Type} [Group X]
    {q : TauCeti.PrimePower} {hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid} (hq3 : q.p = 3)
    (f : X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)
    (e : Z ≃* _root_.commutator X) {z : Z} {J : Subgroup Z} (hz3 : MulAut.conj z ^ 3 = 1)
    (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)))
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) : False := by
  have hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) := ⟨X, inferInstance, ⟨q, hq, ⟨f⟩⟩, ⟨e⟩⟩
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set K := GaloisField q.p (3 * q.exponent)
  have hKp : CharP K q.p := inferInstanceAs (CharP (GaloisField q.p (3 * q.exponent)) q.p)
  have : CharP K 3 := CharP.congr q.p hq3
  have hK3 : Nat.card K = q.card ^ 3 := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card _ _ (by have := q.exponent_pos; omega),
      ← pow_mul, mul_comm]
  have hq3' : 3 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def, hq3]
    exact Nat.le_self_pow q.exponent_pos.ne' 3
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK3]
    calc 4 ≤ 3 ^ 3 := by norm_num
      _ ≤ q.card ^ 3 := Nat.pow_le_pow_left hq3' 3
  set σ' : K ≃+* K := iterateFrobeniusEquiv K q.p q.exponent with hσ'def
  have hσ'y : ∀ y : K, σ' y = y ^ q.card := fun y => by
    rw [hσ'def, iterateFrobeniusEquiv_def, TauCeti.PrimePower.card_def]
  have hσ'3 : ∀ y : K, σ' (σ' (σ' y)) = y := by
    intro y
    have : Fintype K := Fintype.ofFinite K
    rw [hσ'y, hσ'y, hσ'y, ← pow_mul, ← pow_mul]
    have h1 : q.card * (q.card * q.card) = Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, hK3]
      ring
    rw [h1, FiniteField.pow_card]
  have hσRE : σ' ^ TwistTag.D4.order = 1 := by
    apply RingEquiv.ext
    intro y
    exact hσ'3 y
  have hσRH : σ'.toRingHom ^ 3 = 1 := by
    apply RingHom.ext
    intro y
    exact hσ'3 y
  have hK3' : Nat.card K = q.card ^ TwistTag.D4.order := hK3
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hq K hK3'
    σ'.toRingHom hσ'y
  set L := AlgebraicClosure K
  have : CharP L q.p := @charP_of_injective_ringHom K L _ _ (algebraMap K L)
    (algebraMap K L).injective q.p hKp
  obtain ⟨-, -, hTG, hsimple, hnonab⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group q.p q.exponent q.prime_p
      q.exponent_pos K (by rw [hK3, TauCeti.PrimePower.card_def]) L 1 (Or.inl rfl) σ'.toRingHom
      (fun c => by rw [pow_one, ← TauCeti.PrimePower.card_def]; exact hσ'y c)
      (iterateFrobenius L q.p q.exponent) (fun c => iterateFrobenius_def q.p q.exponent c)
  set e3 := MulEquiv.subgroupCongr hTG
  have : IsSimpleGroup (CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K σ'.toRingHom) :=
    MulEquiv.isSimpleGroup e3
  obtain ⟨e2⟩ := nonempty_derivedCentralQuotient_mulEquiv
    (CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K σ'.toRingHom) (by
      obtain ⟨x, y, hxy⟩ := hnonab
      refine ⟨e3.symm x, e3.symm y, fun h => hxy ?_⟩
      have := congrArg e3 h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this)
  have hXp : Group.IsPerfect X := by
    have := SetUp1118Proof.isPerfect_lie_trialityD4 q hq
    exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  let E : Z ≃* graphFixedRootGroup TwistTag.D4 K σ'.toRingHom :=
    (e.trans ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans Subgroup.topEquiv)).trans
      (f.trans (b.symm.trans (e2.trans e3)))
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  by_cases hz1 : z = 1
  · subst hz1
    have hT := KS11Lie2Proof.hasType424_of_mem hJ hJT
    rw [map_one, Item426.fixSub_one] at hT
    exact not_hasType424_d4_three σ'.toRingHom hσRH hK4
      ((hT.of_mulEquiv Subgroup.topEquiv).of_mulEquiv E)
  · have hz3' : z ^ 3 = 1 := by
      have h1 := mem_center_of_conj_eq_one (x := z ^ 3) (by rw [map_pow, hz3])
      rwa [center_eq_bot_d4 Z hZ, Subgroup.mem_bot] at h1
    have hT := (KS11Lie2Proof.hasType424_of_mem hJ hJT).of_mulEquiv
      (KS11Lie2Proof.fixSubCongr E (MulAut.conj z))
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj] at hT
    refine not_hasType424_fixSub_d4_three σ' hσRE (z := E z) ?_ ?_ hT
    · intro h
      exact hz1 (E.injective (h.trans (map_one E).symm))
    · rw [← map_pow, hz3', map_one]

theorem splitFamily_d4 : SplitFamily
    (fun X _ => ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group))
    (fun X _ => ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      q.p ≠ 3 ∧ Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) := by
  intro Z _ _ hZ
  obtain ⟨X, _, ⟨q, hq, ⟨f⟩⟩, ⟨e⟩⟩ := hZ
  by_cases hq3 : q.p = 3
  · exact Or.inr fun z J hz3 hJ hJT => false_of_isType424_d4_three hq3 f e hz3 hJ hJT
  · exact Or.inl ⟨X, inferInstance, ⟨q, hq, hq3, ⟨f⟩⟩, ⟨e⟩⟩


end D4Three

end KS11Lie3Proof

@[expose] def ThetaCentral119G2Ss : Prop :=
  ThetaCentral119For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p ≠ 3 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)

@[expose] def NormCentJ1117G2Ss : Prop :=
  NormCentJ1117For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p ≠ 3 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)

@[expose] def ThetaCentral119D4Ss : Prop :=
  ThetaCentral119For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p ≠ 3 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

@[expose] def NormCentJ1117D4Ss : Prop :=
  NormCentJ1117For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p ≠ 3 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

section Assembly


theorem thetaCentral119G2_of_ss (h : ThetaCentral119G2Ss) : ThetaCentral119G2 :=
  KS11Lie3Proof.thetaCentral119For_of_split KS11Lie3Proof.splitFamily_g2 h

theorem normCentJ1117G2_of_ss (h : NormCentJ1117G2Ss) : NormCentJ1117G2 :=
  KS11Lie3Proof.normCentJ1117For_of_split KS11Lie3Proof.splitFamily_g2 h

theorem centJ119G2_of_parts (hI : CentJ119G2Inn) (hO : CentJ119G2Out) : CentJ119G2 :=
  KS11Lie3Proof.centJ119For_of_inn_out KS11Lie3Proof.center_eq_bot_g2
    (KS11Lie3Proof.centJ119InnFor_of_split KS11Lie3Proof.splitFamily_g2 hI)
    (KS11Lie3Proof.centJ119OutFor_of_split KS11Lie3Proof.splitFamily_g2 hO)

theorem thetaCentral119D4_of_ss (h : ThetaCentral119D4Ss) : ThetaCentral119D4 :=
  KS11Lie3Proof.thetaCentral119For_of_split KS11Lie3Proof.splitFamily_d4 h

theorem normCentJ1117D4_of_ss (h : NormCentJ1117D4Ss) : NormCentJ1117D4 :=
  KS11Lie3Proof.normCentJ1117For_of_split KS11Lie3Proof.splitFamily_d4 h

theorem centJ119D4_of_parts (hI : CentJ119D4Inn) (hO : CentJ119D4Out) : CentJ119D4 :=
  KS11Lie3Proof.centJ119For_of_inn_out KS11Lie3Proof.center_eq_bot_d4
    (KS11Lie3Proof.centJ119InnFor_of_split KS11Lie3Proof.splitFamily_d4 hI)
    (KS11Lie3Proof.centJ119OutFor_of_split KS11Lie3Proof.splitFamily_d4 hO)

end Assembly

end CFSG.RankThree.PartTwo.Sec11
