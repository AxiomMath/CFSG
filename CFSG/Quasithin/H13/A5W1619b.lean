module

public import CFSG.Quasithin.H13.A5W1619a
public import CFSG.Quasithin.H13.NQCatLieOverRank1
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParGen
public import CFSG.Quasithin.EmptyFaithful.S151S9UPerf
public import CFSG.Quasithin.Background.SmithB42G2IdFact
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.FLcAutMat
public import CFSG.Quasithin.EmptyFaithful.FLcMLEGrp
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S151S6B
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.J4Core

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

local notation "StSL" => Assembly.LowTwoRank.StatedSL

local notation "StSp" => Assembly.LowTwoRank.StatedSp

@[expose] def FactNoGraphTwist : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ J X : Subgroup (MulAut V), B53Hyp J →
    (B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) → X ≤ J →
    (∀ y ∈ J, ∀ x ∈ X, y * x * y⁻¹ ∈ X) → CFSG.IsQuasisimple ↥X →
    ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    (Nonempty (↥X ≃* ↥(StSL 3 F)) ∨ Nonempty (↥X ≃* ↥(StSp 2 F)) ∨
      Nonempty (↥X ≃* ↥(CFSG.Open.quasithinG2 F))) →
    ∀ S M : Subgroup (MulAut V), IsSylowTwoOf S X → S ≤ M → M < X →
      (∀ M' : Subgroup (MulAut V), M ≤ M' → M' < X → M' = M) →
      ∀ g : MulAut V, g ∈ Subgroup.normalizer (J : Set (MulAut V)) →
        g ∈ Subgroup.normalizer (X : Set (MulAut V)) →
        g ∈ Subgroup.normalizer (S : Set (MulAut V)) →
        M.map (MulAut.conj g).toMonoidHom = M

theorem statedScalars_subgroupOf_statedSp_eq_bot {F : Type} [Field F] [CharP F 2] :
    (Assembly.LowTwoRank.StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StSp 2 F) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨g, hg⟩ hgs
  rw [Subgroup.mem_subgroupOf] at hgs
  obtain ⟨c, rfl⟩ := hgs
  have h := (CFSG.LieType.SteinbergBR.EvenSp.mem_statedSp_iff' (K := F)).mp hg
  have h1 := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 0)
  simp [Matrix.mul_apply, Matrix.fromBlocks, Fin.sum_univ_two] at h1
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hc : (c : F) = 1 := by
    have h3 : ((c : F) - 1) * ((c : F) - 1) = 0 := by linear_combination h1 + (1 - (c : F)) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  have hcu : c = 1 := Units.ext hc
  subst hcu
  rw [Subgroup.mem_bot]
  exact Subtype.ext (map_one _)


theorem exists_rank2Pkg
    {Y : Type} [Group Y] [Finite Y] {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n)
    (hY : Nonempty (Y ≃* ↥(StSL 3 F)) ∨ Nonempty (Y ≃* ↥(StSp 2 F)) ∨
      Nonempty (Y ≃* ↥(CFSG.Open.quasithinG2 F))) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup Y, Rk2.Rank2Pkg Y U P := by
  have hcharF : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hF
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rcases hY with h | h | h
  · obtain ⟨e⟩ := h
    exact Rk2.rank2Pkg_exists_sl3 hn ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩ hU
  · obtain ⟨e⟩ := h
    let eP : ↥(StSp 2 F) ≃* Assembly.LowTwoRank.StatedProj (StSp 2 F) :=
      ((QuotientGroup.quotientMulEquivOfEq statedScalars_subgroupOf_statedSp_eq_bot).trans
        QuotientGroup.quotientBot).symm
    refine Rk2.rank2Pkg_exists_sp4 hn ⟨⟨Nat.prime_two, by omega, le_rfl, ?_⟩, F, inferInstance,
      inferInstance, hF, ⟨e.trans eP⟩⟩ hU
    intro h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    omega
  · obtain ⟨e⟩ := h
    let e₀ : ↥(CFSG.Open.quasithinG2 F) ≃* ↥(Explicit.cayleyGroup F) :=
      MulEquiv.subgroupCongr G11.P3G2.quasithinG2_eq_cayleyGroup
    have hG : IsG2 2 n Y :=
      IsG2.of_mulEquiv (e.trans e₀).symm (B42G2Id.chevalleyExceptionalModel_cayleyGroup hF hn)
    exact Rk2.rank2Pkg_exists_g2 hG hU

section Levi

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem ker_eq_pCore_of_levi {L : Subgroup Γ} {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {g : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hg : Function.Surjective g) (hker : IsPGroup 2 g.ker) :
    g.ker = CFSG.Open.pCore 2 ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hs := Setting.isSimpleGroup_sl2 hK' hn
  refine le_antisymm (CFSG.LieType.BorelTits.le_pCore 2 inferInstance hker) ?_
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]; exact h4)
    exact ⟨s, hs⟩
  have hO : CFSG.Open.pCore 2 (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (CFSG.Open.pCore 2 (Matrix.SpecialLinearGroup (Fin 2) K)) with h | h
    · exact h
    · exfalso
      have h2 : IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) K) := fun x => by
        obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCore_isPGroup 2
          (G := Matrix.SpecialLinearGroup (Fin 2) K) ⟨x, h ▸ Subgroup.mem_top x⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      have : Group.IsNilpotent (Matrix.SpecialLinearGroup (Fin 2) K) := h2.isNilpotent
      exact SzN2.not_isSolvable_sl2 hK4 inferInstance
  have h1 := CFSG.LieType.BorelTits.map_pCore_le 2 g hg
  rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
  exact h1

theorem rankOneAt_of_levi {L T : Subgroup Γ}
    (hT : IsSylowTwoOf (T ⊓ L) L) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {g : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hg : Function.Surjective g) (hker : IsPGroup 2 g.ker) : RankOneAt L (T ⊓ L) := by
  have : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hK
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hLie : CFSG.Blueprint.LieModel (Matrix.SpecialLinearGroup (Fin 2) K) .PSL 2 2 n := by
    refine Or.inl ⟨by decide, ⟨Nat.prime_two, by omega, le_refl 2, ?_, ?_⟩, K, inferInstance,
      inferInstance, hK, ⟨Vol2Native.A312L.sl2EquivStatedProj⟩⟩
    · intro h
      have := congrArg Prod.snd h
      simp only at this
      omega
    · intro h
      have := congrArg Prod.snd h
      simp only at this
      omega
  have hR : IsRankOneSylow (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.Quasithin.H13.NQCat.l2RankOneSylowFact_holds _ n hn hLie
  have e : oTwoQuot ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.quotientMulEquivOfEq (ker_eq_pCore_of_levi hK hn hg hker).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  exact F1.rankOneAt_of_isRankOneSylow hT (hR.of_mulEquiv e.symm)

theorem mem_cComp_self_of_levi {L : Subgroup Γ} (hperf : ⁅L, L⁆ = L) {K : Type} [Field K]
    [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {g : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K} (hg : Function.Surjective g)
    (hker : IsPGroup 2 g.ker) : L ∈ cComp L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hs := Setting.isSimpleGroup_sl2 hK' hn
  have hne : L ≠ ⊥ := by
    intro h
    have hsub : Subsingleton ↥L := by rw [h]; infer_instance
    have hsub' : Subsingleton (Matrix.SpecialLinearGroup (Fin 2) K) :=
      hg.subsingleton
    exact not_subsingleton (Matrix.SpecialLinearGroup (Fin 2) K) hsub'
  have : Group.IsNilpotent ↥g.ker := hker.isNilpotent
  exact S151S9U.mem_cComp_self_of_simple_quotient g hg hne hperf inferInstance

end Levi

theorem false_of_charTwo_of_le_centralizer {Γ : Type} [Group Γ] [Finite Γ] {L : Subgroup Γ}
    (hc : CharTwo L) (hns : ¬ Group.IsSolvable ↥L)
    (hcen : ∀ r ∈ pCoreOf 2 L, ∀ x ∈ L, r * x = x * r) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLO : L ≤ pCoreOf 2 L := fun x hx => hc ⟨hx, Subgroup.mem_centralizer_iff.mpr fun r hr =>
    hcen r hr x hx⟩
  have h2 : IsPGroup 2 ↥L :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hLO
  have : Group.IsNilpotent ↥L := h2.isNilpotent
  exact hns inferInstance

end CFSG.Quasithin.H13.A5
