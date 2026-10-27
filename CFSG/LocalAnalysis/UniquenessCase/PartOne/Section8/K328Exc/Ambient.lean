module

public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
public import CFSG.Goldschmidt.Steps.G55Basic
public import CFSG.RankThree.PartTwo.KFacts.K412TripleCover
public import CFSG.GroupTheory.ConjTransport
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328Exc

open CFSG.Open CFSG.HardMathSupport.Solomon.Proving

theorem normalizer_le_rankThreeGamma_of_ne_bot {G : Type} [Group G] [Finite G]
    {P Q : Subgroup G} (hP : IsPGroup 3 P) (hQP : Q ≤ P) (hne : Q ≠ ⊥) :
    Subgroup.normalizer (Q : Set G) ≤ rankThreeGamma 1 3 P := by
  unfold rankThreeGamma
  exact normalizer_le_glbCore hQP
    (CFSG.AGLEmbedding.one_le_pRank_of_isPGroup_of_ne_bot Nat.prime_three (hP.to_le hQP) hne)

@[expose] def comCubeSet {G : Type} [Group G] (S : Subgroup G) : Set G :=
  {x | ∃ a ∈ S, ∃ b ∈ S, x = a * b * a⁻¹ * b⁻¹} ∪ {x | ∃ a ∈ S, x = a ^ 3}

theorem normalizer_le_normalizer_comCube {G : Type} [Group G] [Finite G] (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure (comCubeSet S) : Subgroup G) : Set G) := by
  intro n hn
  have key : ∀ m ∈ Subgroup.normalizer (S : Set G), ∀ x ∈ comCubeSet S, m * x * m⁻¹ ∈ comCubeSet S := by
    intro m hm x hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩
    · refine Or.inl ⟨m * a * m⁻¹, (Subgroup.mem_normalizer_iff.1 hm a).1 ha,
        m * b * m⁻¹, (Subgroup.mem_normalizer_iff.1 hm b).1 hb, by group⟩
    · exact Or.inr ⟨m * a * m⁻¹, (Subgroup.mem_normalizer_iff.1 hm a).1 ha, conj_pow.symm⟩
  exact CFSG.GroupTheory.mem_normalizer_closure fun x hx =>
    Subgroup.subset_closure (key n hn x hx)

theorem comCubeSet_subset_of_index {G : Type} [Group G] [Finite G] {P S : Subgroup G} (hPS : P ≤ S)
    (hS : IsPGroup 3 S) (hcard : Nat.card S = 3 * Nat.card P) : comCubeSet S ⊆ P := by
  set P' : Subgroup S := P.subgroupOf S
  have hP' : Nat.card P' = Nat.card P := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv
  have hidx : P'.index = 3 := by
    have h := Subgroup.card_mul_index P'
    rw [hP', hcard] at h
    have hpos : 0 < Nat.card P := Nat.card_pos
    nlinarith
  have hmin : (Nat.card S).minFac = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      have := Nat.card_pos (α := P)
      omega
    rw [hk, Nat.Prime.pow_minFac Nat.prime_three hk0]
  have hN : P'.Normal := Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hmin])
  have hq : Nat.card (S ⧸ P') = 3 := hidx
  have : Fact (Nat.Prime (Nat.card (S ⧸ P'))) := ⟨hq ▸ Nat.prime_three⟩
  have : IsCyclic (S ⧸ P') := isCyclic_of_prime_card rfl
  have hmem : ∀ x : S, (x : S ⧸ P') = 1 → (x : G) ∈ P := fun x hx => by
    have := (QuotientGroup.eq_one_iff x).1 hx
    exact Subgroup.mem_subgroupOf.1 this
  rintro x (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩)
  · have := hmem (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) (by
      have hc := (IsCyclic.commGroup (α := S ⧸ P')).mul_comm
        ((⟨a, ha⟩ : S) : S ⧸ P') ((⟨b, hb⟩ : S) : S ⧸ P')
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [show ((⟨a, ha⟩ : S) : S ⧸ P') * ((⟨b, hb⟩ : S) : S ⧸ P') =
        ((⟨b, hb⟩ : S) : S ⧸ P') * ((⟨a, ha⟩ : S) : S ⧸ P') from hc]
      group)
    simpa using this
  · have := hmem (⟨a, ha⟩ ^ 3) (by
      rw [QuotientGroup.mk_pow, ← hq]
      exact pow_card_eq_one')
    simpa using this

theorem isElemAbelian_of_comCube_eq_bot {G : Type} [Group G] {S : Subgroup G}
    (h : Subgroup.closure (comCubeSet S) = ⊥) : IsElemAbelian 3 S := by
  have h1 : ∀ x ∈ comCubeSet S, x = 1 := fun x hx => by
    have := Subgroup.subset_closure hx
    rw [h] at this
    exact (Subgroup.mem_bot).1 this
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => h1 _ (Or.inr ⟨a, ha, rfl⟩)⟩
  have := h1 _ (Or.inl ⟨a, a.2, b, b.2, rfl⟩)
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  have h2 : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ * b * a = b * a := by rw [this, one_mul]
  simpa [mul_assoc] using h2

theorem rankThreeGamma_eq_top_of_normal {G : Type} [Group G] [Finite G] (K : Subgroup G) [K.Normal]
    {P : Subgroup G} (hP : IsPGroup 3 P) (hPK : P ≤ K) (hP27 : 27 ≤ Nat.card P)
    (hidx : ¬ 9 * Nat.card P ∣ Nat.card K) (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3)
    (hK : K ≤ rankThreeGamma 1 3 P) : rankThreeGamma 1 3 P = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := (hP.comap_of_injective K.subtype Subtype.val_injective).exists_le_sylow
  set S' : Subgroup G := (S : Subgroup K).map K.subtype with hS'
  have hPS : P ≤ S' := fun x hx =>
    ⟨⟨x, hPK hx⟩, hS (show (⟨x, hPK hx⟩ : K) ∈ P.comap K.subtype from hx), rfl⟩
  have hS'p : IsPGroup 3 S' := S.isPGroup'.map K.subtype
  have hcardS : Nat.card S' = Nat.card S :=
    Subgroup.card_map_of_injective Subtype.val_injective
  have hSK : Nat.card S' ∣ Nat.card K := hcardS ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨a, ha⟩ := hS'p.exists_card_eq
  obtain ⟨b, hb⟩ := hP.exists_card_eq
  have hdvd : 3 ^ b ∣ 3 ^ a := hb ▸ ha ▸ Subgroup.card_dvd_of_le hPS
  have hba : b ≤ a := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hab : a ≤ b + 1 := by
    by_contra hlt
    apply hidx
    rw [hb]
    refine dvd_trans ?_ (ha ▸ hSK)
    rw [show 9 * 3 ^ b = 3 ^ (b + 2) by ring]
    exact Nat.pow_dvd_pow 3 (by omega)
  have hb3 : 3 ≤ b := by
    by_contra hlt
    have : 3 ^ b ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hfrat : Subgroup.normalizer (S' : Set G) ⊔ K = ⊤ := Sylow.normalizer_sup_eq_top S
  have hPne : P ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hP27
    omega
  rw [eq_top_iff, ← hfrat]
  refine sup_le ?_ hK
  rcases (show a = b ∨ a = b + 1 by omega) with rfl | rfl
  · have hEq : P = S' := Subgroup.eq_of_le_of_card_ge hPS (by rw [ha, hb])
    rw [← hEq]
    exact normalizer_le_rankThreeGamma_of_ne_bot hP le_rfl hPne
  · have hsub : comCubeSet S' ⊆ P :=
      comCubeSet_subset_of_index hPS hS'p (by rw [ha, hb, pow_succ]; ring)
    have hQP : Subgroup.closure (comCubeSet S') ≤ P := (Subgroup.closure_le P).2 hsub
    have hQne : Subgroup.closure (comCubeSet S') ≠ ⊥ := by
      intro hbot
      have hel := isElemAbelian_of_comCube_eq_bot hbot
      have : b + 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
        CFSG.SectionRank.le_pRank (by norm_num) le_top hel ha
      omega
    exact (normalizer_le_normalizer_comCube S').trans
      (normalizer_le_rankThreeGamma_of_ne_bot hP hQP hQne)

theorem exists_e9_le_sylow {G : Type} [Group G] [Finite G] {X P : Subgroup G}
    (hperf : commutator X = ⊤)
    (hZ : Nat.card (Subgroup.center X) = 3) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X) :
    ∃ E ≤ P, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, rfl⟩ := hP
  have : Nontrivial (Subgroup.center X) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hZ]; norm_num
  obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center X)
  have hz3 : z ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center X) (x := ⟨z, hz⟩)
    rw [hZ] at this
    exact congrArg Subtype.val this
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hnc : ¬ IsCyclic (Q : Subgroup X) := fun hc => by
    have := hc
    exact CFSG.RankThree.PartTwo.KFacts.K412.not_isMulCommutative_sylow hperf hz hz1' hz3 Q
      ⟨⟨(IsCyclic.commGroup (α := (Q : Subgroup X))).mul_comm⟩⟩
  obtain ⟨E, hEQ, hE, hcard⟩ := CFSG.Goldschmidt.G55.exists_isElemAbelian_card_sq
    Nat.prime_three (by norm_num) Q.isPGroup' hnc
  refine ⟨E.map X.subtype, Subgroup.map_mono hEQ,
    hE.map X.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective Subtype.val_injective, hcard]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328Exc
