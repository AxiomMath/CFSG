module

public import CFSG.LocalAnalysis.StandardType.GGL45E67Config
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggL45E67Config_entrywise_of_frame
    {τ : Tag} {d : ℕ} (F : TableBExcTwo.OrthFrame τ d) {K : Type} [Field K] [CharP K 2]
    (σ : K ≃+* K) : GGL45E67Config (entrywiseAdjointAut τ σ) d := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hρu : ∀ i : Fin (d + 1),
      TableBExcTwo.rho K F i (uSL (1 : K)) =
        ⟨pinnedX τ K (F.root i) 1, pinnedX_mem_adjointGroup (F.root i) 1⟩ := by
    intro i
    apply Subtype.ext
    rw [TableBExcTwo.coe_rho]
    exact CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_uSL_of_two h2 (F.root i) 1
  have hρv : ∀ i : Fin (d + 1),
      TableBExcTwo.rho K F i (vSL (1 : K)) =
        ⟨pinnedX τ K (-F.root i) 1, pinnedX_mem_adjointGroup (-F.root i) 1⟩ := by
    intro i
    apply Subtype.ext
    rw [TableBExcTwo.coe_rho]
    exact CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_vSL_of_two h2 (F.isRoot i) 1
  have hvSL : (vSL (1 : K) : SL2 K) ^ 2 = 1 := by
    ext i j
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_vSL]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]
  have hab : ∀ i : Fin d,
      TableBExcTwo.rho K F i.castSucc (uSL (1 : K)) *
        TableBExcTwo.rho K F i.castSucc (vSL 1) = TableBExcTwo.torusGen K F i := by
    intro i
    rw [← map_mul]
    rfl
  have htorus : ∀ i : Fin d,
      TableBExcTwo.torusE K F (Multiplicative.ofAdd (Pi.single i 1)) =
        TableBExcTwo.torusGen K F i := by
    intro i
    rw [TableBExcTwo.torusE_apply]
    change TableBExcTwo.torusD K F
      (Pi.mulSingle (M := fun _ : Fin d => Multiplicative (ZMod 3)) i
        (Multiplicative.ofAdd (1 : ZMod 3))) = TableBExcTwo.torusGen K F i
    rw [TableBExcTwo.torusD, MonoidHom.noncommPiCoprod_mulSingle,
      TableBExcTwo.torusCoord_apply, TableBExcTwo.torusGen, toAdd_ofAdd]
    haveI : Fact (1 < 3) := ⟨by norm_num⟩
    rw [ZMod.val_one, pow_one]
  have hfixP : ∀ {β : Fin τ.rank → ℤ} {c : K}
      (hβ : pinnedX τ K β c ∈ adjointGroup τ K),
      entrywiseAdjointAut τ σ ⟨pinnedX τ K β c, hβ⟩ =
        ⟨pinnedX τ K β (σ c), pinnedX_mem_adjointGroup β (σ c)⟩ := by
    intro β c hβ
    apply Subtype.ext
    rw [coe_entrywiseAdjointAut]
    exact Units.ext (entrywise_pinnedX σ.toRingHom β c)
  have hfix : ∀ i : Fin d,
      entrywiseAdjointAut τ σ (TableBExcTwo.rho K F i.castSucc (uSL 1)) =
        TableBExcTwo.rho K F i.castSucc (uSL 1) := by
    intro i
    rw [hρu i.castSucc, hfixP, map_one]
  have hfixb : ∀ i : Fin d,
      entrywiseAdjointAut τ σ (TableBExcTwo.rho K F i.castSucc (vSL 1)) =
        TableBExcTwo.rho K F i.castSucc (vSL 1) := by
    intro i
    rw [hρv i.castSucc, hfixP, map_one]
  have hrootInv : entrywiseAdjointAut τ σ (TableBExcTwo.rootInv K F) =
      TableBExcTwo.rootInv K F := by
    show entrywiseAdjointAut τ σ (TableBExcTwo.rho K F (Fin.last d) (uSL 1)) =
      TableBExcTwo.rho K F (Fin.last d) (uSL 1)
    rw [hρu (Fin.last d), hfixP, map_one]
  refine ⟨fun i => TableBExcTwo.rho K F i.castSucc (uSL 1),
    fun i => TableBExcTwo.rho K F i.castSucc (vSL 1),
    Subgroup.zpowers (TableBExcTwo.rootInv K F), ?_, ?_, ?_, hfix, hfixb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    show (TableBExcTwo.rho K F i.castSucc (uSL (1 : K))) ^ 2 = 1
    rw [← map_pow, TableBF4Two.uSL_one_sq h2, map_one]
  · intro i
    show (TableBExcTwo.rho K F i.castSucc (vSL (1 : K))) ^ 2 = 1
    rw [← map_pow, hvSL, map_one]
  · intro i
    rw [hab i]
    exact orderOf_eq_prime (TableBExcTwo.torusGen_pow_three F i)
      (TableBExcTwo.torusGen_ne_one F i)
  · intro i j hij
    have hji : j.castSucc ≠ i.castSucc := fun he =>
      (ne_of_lt hij) (Fin.castSucc_injective d he)
    constructor
    · have h1 := TableBExcTwo.commute_rho (i := i.castSucc) (j := j.castSucc) F
        (Ne.symm hji) (uSL (1 : K)) (uSL (1 : K))
      have h2 := TableBExcTwo.commute_rho (i := i.castSucc) (j := j.castSucc) F
        (Ne.symm hji) (vSL (1 : K)) (uSL (1 : K))
      exact h1.mul_left h2
    · have h1 := TableBExcTwo.commute_rho (i := i.castSucc) (j := j.castSucc) F
        (Ne.symm hji) (uSL (1 : K)) (vSL (1 : K))
      have h2 := TableBExcTwo.commute_rho (i := i.castSucc) (j := j.castSucc) F
        (Ne.symm hji) (vSL (1 : K)) (vSL (1 : K))
      exact h1.mul_left h2
  · have hgen := card_closure_range_basis_eq_three_pow (φ := TableBExcTwo.torusE K F)
      (TableBExcTwo.torusE_injective F)
    simpa only [hab, htorus] using hgen
  · show IsPGroup 2 (Subgroup.zpowers (TableBExcTwo.rootInv K F))
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers,
      orderOf_eq_prime (TableBExcTwo.rootInv_sq F) (TableBExcTwo.rootInv_ne_one F), pow_one]
  · show Subgroup.zpowers (TableBExcTwo.rootInv K F) ≠ ⊥
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact TableBExcTwo.rootInv_ne_one F
  · intro g hg
    show entrywiseAdjointAut τ σ g ∈ Subgroup.zpowers (TableBExcTwo.rootInv K F)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [map_zpow, hrootInv]
    exact Subgroup.zpow_mem_zpowers _ _
  · intro i
    have hc : TableBExcTwo.torusE K F (Multiplicative.ofAdd (Pi.single i 1)) ∈
        Subgroup.centralizer
          (Subgroup.zpowers (TableBExcTwo.rootInv K F) : Set (adjointGroup τ K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((TableBExcTwo.torusE_commute_rootInv F _).zpow_right k).symm.eq
    have h := Subgroup.centralizer_le_normalizer
      (Subgroup.zpowers (TableBExcTwo.rootInv K F) : Set (adjointGroup τ K)) hc
    simpa only [hab i, htorus i] using h

theorem ggL45E67Config_entrywise_E6
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) :
    GGL45E67Config (entrywiseAdjointAut .E6 σ) 4 := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (1 < 3) := ⟨by norm_num⟩
  haveI : NeZero Tag.E6.rank := ⟨by decide⟩
  have hUp : (parabolicRadical .E6 K TableBExc.E6Three.jE6Two).subgroupOf
      (adjointGroup .E6 K) ≠ ⊥ := by
    intro hbot
    have h0 : (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∈
        parabolicRadicalRoots .E6 TableBExc.E6Three.jE6Two := by
      refine ⟨⟨isRoot_single .E6 0, by simp⟩, fun h => ?_⟩
      have h1 := h.1.2 0 (by
        change (0 : Fin 6) ∉ ({1, 2, 3, 4} : Set (Fin 6))
        decide)
      simp at h1
    have hx : (⟨pinnedX .E6 K (Pi.single 0 1) 1, pinnedX_mem_adjointGroup _ _⟩ :
        adjointGroup .E6 K) ∈
        (parabolicRadical .E6 K TableBExc.E6Three.jE6Two).subgroupOf
          (adjointGroup .E6 K) :=
      Subgroup.mem_subgroupOf.mpr (pinnedX_mem_rootSpan h0 1)
    rw [hbot, Subgroup.mem_bot] at hx
    have hx' : pinnedX .E6 K (Pi.single 0 1) 1 = pinnedX .E6 K (Pi.single 0 1) 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val hx
    exact one_ne_zero (pinnedX_injective .E6 K _ hx')
  have hU2 : IsPGroup 2 ((parabolicRadical .E6 K TableBExc.E6Three.jE6Two).subgroupOf
      (adjointGroup .E6 K)) :=
    ((isPGroup_posUnipotent 2 .E6).to_le
      (parabolicRadical_le_posUnipotent TableBExc.E6Three.jE6Two)).comap_of_injective _
        (adjointGroup .E6 K).subtype_injective
  have hmap : (parabolicRadical .E6 K TableBExc.E6Three.jE6Two).map
      (Units.map (entrywiseHom σ.toRingHom)) =
      parabolicRadical .E6 K TableBExc.E6Three.jE6Two :=
    map_rootSpan_of_forall fun α _ => map_entrywise_rootSubgroup σ α
  have hTU : ∀ g ∈ (parabolicRadical .E6 K TableBExc.E6Three.jE6Two).subgroupOf
      (adjointGroup .E6 K), entrywiseAdjointAut .E6 σ g ∈
      (parabolicRadical .E6 K TableBExc.E6Three.jE6Two).subgroupOf (adjointGroup .E6 K) := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    rw [coe_entrywiseAdjointAut, ← hmap]
    exact Subgroup.mem_map_of_mem _ hg
  have hnorm : ∀ i : Fin 4, TableBExc.E6Three.uE6Two (K := K) i ∈
      Subgroup.normalizer ((parabolicRadical .E6 K TableBExc.E6Three.jE6Two).subgroupOf
        (adjointGroup .E6 K) : Set (adjointGroup .E6 K)) := by
    intro i
    have hN := parabolicSubgroup_le_normalizer_parabolicRadical (τ := .E6) (K := K)
      TableBExc.E6Three.jE6Two (TableBExc.E6Three.coe_uE6Two_mem_parabolic i)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hc := (Subgroup.mem_normalizer_iff.mp hN (x : ModGL .E6 K)).1
        (Subgroup.mem_subgroupOf.mp hx)
      rw [Subgroup.mem_subgroupOf]
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hc
    · intro hx
      have hxQ := Subgroup.mem_subgroupOf.mp hx
      have hinv : ((TableBExc.E6Three.uE6Two (K := K) i : adjointGroup .E6 K)⁻¹ :
          ModGL .E6 K) ∈ Subgroup.normalizer
            (parabolicRadical .E6 K TableBExc.E6Three.jE6Two : Set (ModGL .E6 K)) :=
        Subgroup.inv_mem _ hN
      have hc := (Subgroup.mem_normalizer_iff.mp hinv _).1 hxQ
      rw [Subgroup.mem_subgroupOf]
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using hc
  have hab : ∀ i : Fin 4,
      (⟨pinnedX .E6 K (TableBExc.E6Three.bE6 i) 1, pinnedX_mem_adjointGroup _ _⟩ :
        adjointGroup .E6 K) *
        ⟨pinnedX .E6 K (-TableBExc.E6Three.bE6 i) 1, pinnedX_mem_adjointGroup _ _⟩ =
        TableBExc.E6Three.uE6Two (K := K) i := fun _ => rfl
  have htorus : ∀ i : Fin 4,
      TableBExc.E6Three.torusE6Two h2 (Multiplicative.ofAdd (Pi.single i 1)) =
        TableBExc.E6Three.uE6Two (K := K) i := by
    intro i
    rw [TableBExc.E6Three.torusE6Two_single]
    change (TableBExc.E6Three.uE6Two (K := K) i) ^ (1 : ZMod 3).val =
      TableBExc.E6Three.uE6Two (K := K) i
    rw [ZMod.val_one, pow_one]
  have hfixP : ∀ {β : Fin Tag.E6.rank → ℤ} {c : K}
      (hβ : pinnedX .E6 K β c ∈ adjointGroup .E6 K),
      entrywiseAdjointAut .E6 σ ⟨pinnedX .E6 K β c, hβ⟩ =
        ⟨pinnedX .E6 K β (σ c), pinnedX_mem_adjointGroup β (σ c)⟩ := by
    intro β c hβ
    apply Subtype.ext
    rw [coe_entrywiseAdjointAut]
    exact Units.ext (entrywise_pinnedX σ.toRingHom β c)
  have hfixa : ∀ i : Fin 4,
      entrywiseAdjointAut .E6 σ
        (⟨pinnedX .E6 K (TableBExc.E6Three.bE6 i) 1, pinnedX_mem_adjointGroup _ _⟩ :
          adjointGroup .E6 K) =
        ⟨pinnedX .E6 K (TableBExc.E6Three.bE6 i) 1, pinnedX_mem_adjointGroup _ _⟩ := by
    intro i
    rw [hfixP, map_one]
  have hfixb : ∀ i : Fin 4,
      entrywiseAdjointAut .E6 σ
        (⟨pinnedX .E6 K (-TableBExc.E6Three.bE6 i) 1, pinnedX_mem_adjointGroup _ _⟩ :
          adjointGroup .E6 K) =
        ⟨pinnedX .E6 K (-TableBExc.E6Three.bE6 i) 1, pinnedX_mem_adjointGroup _ _⟩ := by
    intro i
    rw [hfixP, map_one]
  refine ⟨fun i => ⟨pinnedX .E6 K (TableBExc.E6Three.bE6 i) 1, pinnedX_mem_adjointGroup _ _⟩,
    fun i => ⟨pinnedX .E6 K (-TableBExc.E6Three.bE6 i) 1, pinnedX_mem_adjointGroup _ _⟩,
    (parabolicRadical .E6 K TableBExc.E6Three.jE6Two).subgroupOf (adjointGroup .E6 K),
    ?_, ?_, ?_, hfixa, hfixb, ?_, ?_, hU2, hUp, hTU, ?_⟩
  · intro i
    apply Subtype.ext
    change (pinnedX .E6 K (TableBExc.E6Three.bE6 i) 1 : ModGL .E6 K) ^ 2 = 1
    rw [pow_two, ← pinnedX_add,
      show (1 : K) + 1 = 0 from by rw [one_add_one_eq_two, h2], pinnedX_zero]
  · intro i
    apply Subtype.ext
    change (pinnedX .E6 K (-TableBExc.E6Three.bE6 i) 1 : ModGL .E6 K) ^ 2 = 1
    rw [pow_two, ← pinnedX_add,
      show (1 : K) + 1 = 0 from by rw [one_add_one_eq_two, h2], pinnedX_zero]
  · intro i
    rw [hab i]
    exact TableBExc.E6Three.orderOf_uE6Two h2 i
  · intro i j hij
    have hij' : i ≠ j := ne_of_gt hij
    obtain ⟨h1, h2, h3, h4⟩ := TableBExc.E6Three.commute_pinnedX_bE6 (K := K) hij' 1 1
    constructor
    · apply Subtype.ext
      change Commute ((pinnedX .E6 K (TableBExc.E6Three.bE6 i) 1 : ModGL .E6 K) *
        pinnedX .E6 K (-TableBExc.E6Three.bE6 i) 1)
        (pinnedX .E6 K (TableBExc.E6Three.bE6 j) 1)
      exact (h1.mul_left h3).eq
    · apply Subtype.ext
      change Commute ((pinnedX .E6 K (TableBExc.E6Three.bE6 i) 1 : ModGL .E6 K) *
        pinnedX .E6 K (-TableBExc.E6Three.bE6 i) 1)
        (pinnedX .E6 K (-TableBExc.E6Three.bE6 j) 1)
      exact (h2.mul_left h4).eq
  · have hgen := card_closure_range_basis_eq_three_pow (φ := TableBExc.E6Three.torusE6Two h2)
      (TableBExc.E6Three.torusE6Two_injective h2)
    simpa only [hab, htorus] using hgen
  · intro i
    rw [hab i]
    exact hnorm i

private def GGConfigOn (K : Type) [Field K] (τ : Tag) (S : (Fin τ.rank → ℤ) → Prop) (r : ℕ) :
    Prop :=
  ∀ f ∈ RecipeFieldExcInn.markFieldImage S K (MarkChev.chevH τ.cartan S K false),
    GGL45E67Config f r

private theorem GGConfigOn.of_eq {K : Type} [Field K] {τ : Tag}
    {S S' : (Fin τ.rank → ℤ) → Prop} {r : ℕ} (hS : S = S')
    (h : GGConfigOn K τ S r) : GGConfigOn K τ S' r :=
  hS ▸ h

private theorem ggConfigOn_isRoot
    {τ : Tag} {K : Type} [Field K] [Finite K] {r : ℕ}
    (h : ∀ σ : K ≃+* K, GGL45E67Config (entrywiseAdjointAut τ σ) r) :
    GGConfigOn K τ (IsRoot τ) r := by
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot τ) K),
      H = adjointGroup τ K →
      ∀ f ∈ RecipeFieldExcInn.markFieldImage (IsRoot τ) K H, GGL45E67Config f r from
    key _ (chevH_false_eq_adjointGroup K τ)
  intro H hH
  subst hH
  intro f hf
  obtain ⟨σ, hσ⟩ := RecipeExcLang.autEquiv_eq_entrywise_of_mem_markField hf
  have hZ : Subgroup.center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hfm : f = (RecipeExcLang.autEquiv τ K).symm (entrywiseAdjointAut τ σ) := by
    rw [← hσ, MulEquiv.symm_apply_apply]
  rw [hfm]
  refine ggL45E67Config_of_mulEquiv (r := r) (R := adjointGroup τ K)
    (R' := LargeEvenCenterQuot (adjointGroup τ K))
    (e := (centerQuotEquivOfBot hZ).symm) (f := entrywiseAdjointAut τ σ)
    (f' := (RecipeExcLang.autEquiv τ K).symm (entrywiseAdjointAut τ σ)) ?_ (h σ)
  intro x
  simpa only [centerQuotEquivOfBot_symm] using
    RecipeExcLang.autEquiv_symm_apply (entrywiseAdjointAut τ σ) x

theorem ggL45E67Config_chevFieldImage
    {τ : Tag} {K : Type} [Field K] [Finite K] {r : ℕ}
    (h : ∀ σ : K ≃+* K, GGL45E67Config (entrywiseAdjointAut τ σ) r) :
    ∀ f ∈ LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false),
      GGL45E67Config f r := by
  have hroot := (ggConfigOn_isRoot (τ := τ) (K := K) (r := r) h).of_eq
    (largeEvenIsRoot_eq_isRoot τ).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL τ.cartan K),
      H = LargeEvenChevH τ.cartan K false →
      ∀ f ∈ LargeEvenChevFieldImage τ.cartan K H, GGL45E67Config f r from
    key _ rfl
  intro H hH
  rw [largeEvenChevH_eq] at hH
  subst hH
  intro f hf
  exact hroot f hf

end CFSG.StandardType
