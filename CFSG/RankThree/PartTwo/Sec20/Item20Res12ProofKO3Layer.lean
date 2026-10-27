module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofKO3
import CFSG.RankThree.PartTwo.Sec16.Item16Res6ProofActComp
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases
import CFSG.RankThree.PartTwo.Sec21.Item229Pre
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankFrattini

public section

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace CFSG.RankThree.PartTwo.Sec16.Res6Act
open CFSG CFSG.Blueprint

theorem range_eq_bot_of_not_three_dvd_pCore {K H : Type} [Group K] [Group H] [Finite K]
    (hK : Group.IsPerfect K) (hS : IsSimpleGroup (K ⧸ CFSG.pCore 2 K))
    (h3 : 3 ∣ Nat.card (K ⧸ CFSG.pCore 2 K)) (f : K →* H) (hf : ¬ 3 ∣ Nat.card f.range) :
    f.range = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := CFSG.pCore 2 K with hVdef
  have hNn : (f.ker.map (QuotientGroup.mk' V)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective V)
  have := hS
  have := hNn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map (QuotientGroup.mk' V)) with
    hbot | htop
  ·
    have hNV : f.ker ≤ V := by
      intro n hn
      have h1 : QuotientGroup.mk' V n ∈ f.ker.map (QuotientGroup.mk' V) :=
        Subgroup.mem_map_of_mem _ hn
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    exfalso
    apply hf
    have h1 : Nat.card f.range = f.ker.index := by
      rw [Subgroup.index, Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    rw [h1]
    exact h3.trans (Subgroup.index_dvd_of_le hNV)
  ·
    have hcov : ∀ k : K, ∃ v ∈ V, f k = f v := by
      intro k
      have hk : QuotientGroup.mk' V k ∈ f.ker.map (QuotientGroup.mk' V) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnk⟩ := hk
      refine ⟨n⁻¹ * k, ?_, ?_⟩
      · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnk
        exact hnk
      · rw [map_mul, map_inv, (MonoidHom.mem_ker).mp hn, inv_one, one_mul]
    have hr2 : IsPGroup 2 f.range := by
      rintro ⟨_, k, rfl⟩
      obtain ⟨v, hv, hkv⟩ := hcov k
      obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := 2) (G := K) ⟨v, hv⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change f k ^ 2 ^ a = 1
      rw [hkv, ← map_pow]
      have : v ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
      rw [this, map_one]
    have := hK
    have : Group.IsPerfect f.range := Group.IsPerfect.range f
    have hfin : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    exact Sec16.Res6Act.eq_bot_of_isPerfect_of_isPGroup (p := 2) (T := f.range) this hr2

theorem fix_component_of_perfect_three {X S : Type} [Group X] [Finite X] [Group S] [Finite S]
    (hSp : Group.IsPerfect S)
    (hS3 : ∀ (H : Type) [Group H] (f : S →* H), ¬ 3 ∣ Nat.card f.range → f.range = ⊥)
    (φ : S →* MulAut X) (hK : CFSG.IsKGroup X) (h3 : ¬ 3 ∣ Nat.card X)
    (hrank5 : CFSG.Open.pRank 5 (⊤ : Subgroup X) ≤ 2) {J : Subgroup X}
    (hJ : CFSG.IsComponent J) (s : S) {x : X} (hx : x ∈ J) : φ s x = x := by
  have := hSp
  have hJinv : ∀ t, J.map (φ t).toMonoidHom = J := map_eq_of_perfect φ hrank5
    (fun J' hJ' => exists_five_of_component hK h3 hJ') hJ
  set ρ := restrictAct φ J hJinv with hρ
  refine fix_of_range_eq_bot φ J hJinv ?_ s hx
  obtain ⟨f, hf⟩ := suzukiModel_of_component hK h3 hJ
  have : Group.IsPerfect ↥J := hJ.1.1
  have hcyc := ((CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity _ 2 f hf).2
    ↥J ⟨MulEquiv.refl _⟩).1
  have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥J) :=
    Group.isSolvable_of_comm fun a b => by
      have := IsCyclic.isMulCommutative
        (α := CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥J)
      exact mul_comm' a b
  have hinner : ρ.range ≤ (MulAut.conj : ↥J →* MulAut ↥J).range := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨j, hj⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner ρ t
    exact ⟨j, hj.symm⟩
  refine hS3 _ ρ fun h3ρ => h3 ?_
  have h1 : Nat.card ρ.range ∣ Nat.card (MulAut.conj : ↥J →* MulAut ↥J).range :=
    Subgroup.card_dvd_of_le hinner
  have h2 : Nat.card (MulAut.conj : ↥J →* MulAut ↥J).range ∣ Nat.card ↥J := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  exact (h3ρ.trans h1).trans (h2.trans (Subgroup.card_subgroup_dvd_card J))

end CFSG.RankThree.PartTwo.Sec16.Res6Act

namespace CFSG.RankThree.PartTwo.Sec20
open CFSG CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

theorem Res11.simple_three_dvd_of_kType {K : Type} [Group K] [Finite K]
    (htype : (∃ n : ℕ, Odd n ∧ 3 ≤ n ∧
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n))) ∨
      (∃ n : ℕ, Even n ∧ 4 ≤ n ∧
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 2 (GaloisField 2 n)))) :
    IsSimpleGroup (K ⧸ CFSG.pCore 2 K) ∧ 3 ∣ Nat.card (K ⧸ CFSG.pCore 2 K) := by
  rcases htype with ⟨n, -, -, ⟨e⟩⟩ | ⟨n, -, hn, ⟨e⟩⟩
  · haveI := CFSG.RankThree.PartTwo.Sec21.Item222Proof.isSimpleGroup_projSL_three (GaloisField 2 n)
    exact ⟨e.isSimpleGroup, CFSG.RankThree.PartTwo.KFacts.three_dvd_card_of_mulEquiv_projSL e⟩
  · haveI := CFSG.RankThree.PartTwo.Sec21.isSimpleGroup_projSL_two (m := n) (by omega)
    exact ⟨e.isSimpleGroup, CFSG.RankThree.PartTwo.Sec21.three_dvd_card_of_mulEquiv_projSL e⟩

theorem kFactKO3CentLayer_holds :
    KFactKO3CentLayer := by
  intro G _ _ hKP K O hO hperf htype hKN h3 hrank k hk o ho
  obtain ⟨x, hx, rfl⟩ := ho
  have hOK : CFSG.IsKGroup ↥O :=
    (KCore.KProperNonab.kGroupNonab CFSG.Assembly.inCatalog_isoInvariant hKP O hO).kGroupAllSimple
      CFSG.Assembly.inCatalog_isoInvariant CFSG.Assembly.inCatalog_containsAbelianSimple
  have hKX : CFSG.IsKGroup (↥O ⧸ CFSG.pCore 2 O) :=
    CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient hOK (CFSG.pCore 2 O)
  have h3X : ¬ 3 ∣ Nat.card (↥O ⧸ CFSG.pCore 2 O) := fun hd =>
    absurd (Nat.eq_one_of_dvd_coprimes h3 (dvd_refl (3 : ℕ))
      (hd.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 O)))) (by norm_num)
  have hrank5 : CFSG.Open.pRank 5 (⊤ : Subgroup (↥O ⧸ CFSG.pCore 2 O)) ≤ 2 := by
    have h5 := (Res11.pRank_quotient_le O (p := 5) (by norm_num) (by norm_num)).trans
      (hrank 5 (by norm_num) (le_refl 5))
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h5
    exact h5
  obtain ⟨hS, h3K⟩ := Res11.simple_three_dvd_of_kType htype
  have hS3 : ∀ (H : Type) [Group H] (f : ↥K →* H), ¬ 3 ∣ Nat.card f.range → f.range = ⊥ :=
    fun H _ f hf => CFSG.RankThree.PartTwo.Sec16.Res6Act.range_eq_bot_of_not_three_dvd_pCore
      hperf hS h3K f hf
  have hfixE : ∀ (k' : K), ∀ y ∈ CFSG.layer (↥O ⧸ CFSG.pCore 2 O),
      Res11.quotAction hKN k' y = y := by
    intro k' y hy
    have hle : CFSG.layer (↥O ⧸ CFSG.pCore 2 O) ≤
        RankThree.PartOne.FixedRank36.fixedSub (Res11.quotAction hKN k') :=
      sSup_le fun J hJ z hz =>
        CFSG.RankThree.PartTwo.Sec16.Res6Act.fix_component_of_perfect_three hperf hS3
          (Res11.quotAction hKN) hKX h3X hrank5 hJ k' hz
    exact hle hy
  have hfix : Res11.quotAction hKN (⟨k, hk⟩ : K) (QuotientGroup.mk' (CFSG.pCore 2 O) x) =
      QuotientGroup.mk' (CFSG.pCore 2 O) x :=
    hfixE ⟨k, hk⟩ (QuotientGroup.mk' (CFSG.pCore 2 O) x) hx
  exact Res11.comm_mem_of_quotAction_fix hKN ⟨k, hk⟩ x hfix

end CFSG.RankThree.PartTwo.Sec20
