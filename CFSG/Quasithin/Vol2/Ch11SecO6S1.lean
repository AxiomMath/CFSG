module

public import CFSG.Quasithin.Vol2.Ch11SecGTBar
public import CFSG.Quasithin.Vol2.Ch11SecDO22
public import CFSG.Quasithin.Vol2.Ch11SecGTSL2
public import CFSG.Quasithin.Vol2.Ch11SecO5F
public import CFSG.Quasithin.Vol2.Ch11SecO5G
public import Certificates.Certificate43
public import CFSG.Quasithin.Background.A3Structure312Quotient
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.SplitBNPair
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecD552
public import CFSG.Quasithin.Vol2.Ch11SecD556C
public import CFSG.Quasithin.Vol2.Ch11SecD556O
public import CFSG.Quasithin.Vol2.Ch11SecDFacts5
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD.O6S

open CFSG.Open
open scoped MatrixGroups

section SL2

variable {k : Type} [Field k] [Finite k]

theorem neg_one_mem_of_normal (hk : 4 ≤ Nat.card k) (h2 : (2 : k) ≠ 0) {N : Subgroup SL(2, k)}
    (hN : N.Normal) (hne : N ≠ ⊥) : (-1 : SL(2, k)) ∈ N := by
  have hs : IsSimpleGroup PSL(2, k) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hk
  set Z := Subgroup.center SL(2, k) with hZ
  have : (N.map (QuotientGroup.mk' Z)).Normal := hN.map _ (QuotientGroup.mk'_surjective Z)
  rcases hs.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' Z)) with h | h
  · obtain ⟨n, hn, hn1⟩ := (Subgroup.bot_or_exists_ne_one N).resolve_left hne
    have hnZ : n ∈ Z := by
      have h1 : QuotientGroup.mk' Z n ∈ N.map (QuotientGroup.mk' Z) :=
        Subgroup.mem_map_of_mem _ hn
      rwa [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rcases ABGLocalTools.sl2_eq_one_or_neg_one_of_sq_eq_one h2
        (SecG.SL2.sq_eq_one_of_mem_center hnZ) with h1 | h1
    · exact absurd h1 hn1
    · exact h1 ▸ hn
  · have hperf : Group.IsPerfect SL(2, k) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card k hk
    have hNZ : N ⊔ Z = ⊤ := by
      have h1 : Z ⊔ N = Subgroup.comap (QuotientGroup.mk' Z) (N.map (QuotientGroup.mk' Z)) :=
        (QuotientGroup.comap_map_mk' Z N).symm
      rw [h, Subgroup.comap_top] at h1
      rw [sup_comm]
      exact h1
    have hle : commutator SL(2, k) ≤ N :=
      hN.commutator_le_of_self_sup_commutative_eq_top hNZ (by infer_instance)
    exact hle Group.IsPerfect.mem_commutator

theorem le_center_or_eq_top_of_normal (hk : 4 ≤ Nat.card k) {N : Subgroup SL(2, k)}
    (hN : N.Normal) : N ≤ Subgroup.center SL(2, k) ∨ N = ⊤ := by
  have hs : IsSimpleGroup PSL(2, k) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hk
  set Z := Subgroup.center SL(2, k) with hZ
  have : (N.map (QuotientGroup.mk' Z)).Normal := hN.map _ (QuotientGroup.mk'_surjective Z)
  rcases hs.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' Z)) with h | h
  · left
    intro n hn
    have h1 : QuotientGroup.mk' Z n ∈ N.map (QuotientGroup.mk' Z) :=
      Subgroup.mem_map_of_mem _ hn
    rwa [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  · right
    have hperf : Group.IsPerfect SL(2, k) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card k hk
    have hNZ : N ⊔ Z = ⊤ := by
      have h1 : Z ⊔ N = Subgroup.comap (QuotientGroup.mk' Z) (N.map (QuotientGroup.mk' Z)) :=
        (QuotientGroup.comap_map_mk' Z N).symm
      rw [h, Subgroup.comap_top] at h1
      rw [sup_comm]
      exact h1
    have hle : commutator SL(2, k) ≤ N :=
      hN.commutator_le_of_self_sup_commutative_eq_top hNZ (by infer_instance)
    exact eq_top_iff.mpr fun x _ => hle Group.IsPerfect.mem_commutator

omit [Finite k] in
theorem mem_center_iff (h2 : (2 : k) ≠ 0) {z : SL(2, k)} :
    z ∈ Subgroup.center SL(2, k) ↔ z = 1 ∨ z = -1 := by
  refine ⟨fun hz => ABGLocalTools.sl2_eq_one_or_neg_one_of_sq_eq_one h2
    (SecG.SL2.sq_eq_one_of_mem_center hz), ?_⟩
  rintro (rfl | rfl)
  · exact Subgroup.one_mem _
  · rw [Subgroup.mem_center_iff]
    intro g
    rw [mul_neg_one, neg_one_mul]

omit [Finite k] in
theorem neg_one_ne_one (h2 : (2 : k) ≠ 0) : (-1 : SL(2, k)) ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at this
  exact h2 (by linear_combination -this)

omit [Finite k] in
theorem card_center (h2 : (2 : k) ≠ 0) : Nat.card (Subgroup.center SL(2, k)) = 2 := by
  have hm : (-1 : SL(2, k)) ∈ Subgroup.center SL(2, k) := (mem_center_iff h2).mpr (Or.inr rfl)
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨-1, hm⟩, fun h => neg_one_ne_one h2 (congrArg Subtype.val h).symm, ?_⟩
  ext ⟨z, hz⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases (mem_center_iff h2).mp hz with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Finite k] in
theorem exists_two_elt_neg_one {X : Type} [Group X] [Finite X] {ψ : X →* SL(2, k)}
    (hψ : Function.Surjective ψ) :
    ∃ s : X, ψ s = -1 ∧ ∃ e : ℕ, s ^ 2 ^ e = 1 := by
  obtain ⟨x, hx⟩ := hψ (-1)
  obtain ⟨e, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨x ^ m, ?_, e, ?_⟩
  · rw [map_pow, hx]
    exact hm.neg_one_pow
  · rw [← pow_mul, mul_comm, ← hxm, pow_orderOf_eq_one]

end SL2

section L1Bar

open SecG.Bar

variable {G : Type} [Group G] {K L₁ : Subgroup G}

@[expose] def l1Bar (K L₁ : Subgroup G) : Subgroup (KBar K) :=
  (L₁.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))

@[expose] noncomputable def l1Map (hL : L₁ ≤ K) : ↥L₁ →* KBar K :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion hL)

theorem l1Map_apply (hL : L₁ ≤ K) (l : ↥L₁) :
    l1Map hL l = ((⟨l, hL l.2⟩ : ↥K) : KBar K) := rfl

theorem range_l1Map (hL : L₁ ≤ K) : (l1Map hL).range = l1Bar K L₁ := by
  ext x
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨⟨l, hL l.2⟩, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩

theorem l1Map_mem (hL : L₁ ≤ K) (l : ↥L₁) : l1Map hL l ∈ l1Bar K L₁ := by
  rw [← range_l1Map hL]
  exact ⟨l, rfl⟩

theorem ker_l1Map_le [Finite G] (hL : L₁ ≤ K) : (l1Map hL).ker ≤ CFSG.pCore 2 ↥L₁ := by
  refine le_sSup ⟨inferInstance, fun x => ?_⟩
  have hx : Subgroup.inclusion hL (x : ↥L₁) ∈ CFSG.pCore 2 ↥K := by
    have := x.2
    rw [MonoidHom.mem_ker, l1Map_apply, QuotientGroup.eq_one_iff] at this
    exact this
  obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (⟨_, hx⟩ : ↥(CFSG.pCore 2 ↥K))
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun y : ↥(CFSG.pCore 2 ↥K) => ((y : ↥K) : G)) hn
  simpa using this

end L1Bar

section Chi

open SecG.Bar CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {K L₁ : Subgroup G} {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def chi (hL : L₁ ≤ K) (φ : KBar K →* SL(2, ZMod p)) :
    ↥L₁ →* PSL(2, ZMod p) :=
  (QuotientGroup.mk' (Subgroup.center SL(2, ZMod p))).comp (φ.comp (l1Map hL))

omit [Finite G] [Fact p.Prime] in
theorem chi_apply (hL : L₁ ≤ K) (φ : KBar K →* SL(2, ZMod p)) (l : ↥L₁) :
    chi hL φ l = QuotientGroup.mk' (Subgroup.center SL(2, ZMod p)) (φ (l1Map hL l)) := rfl

omit [Finite G] in
theorem index_pCore_eq_sixty {F₄ : Type} [Field F₄] [Finite F₄] (hF₄ : Nat.card F₄ = 4)
    (eL : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₄) :
    (CFSG.pCore 2 ↥L₁).index = 60 := by
  rw [Subgroup.index, Nat.card_congr eL.toEquiv, sl2_card_formula, hF₄]
  norm_num

theorem chi_spec (hp5 : 5 ≤ p) {φ : KBar K →* SL(2, ZMod p)}
    (hφk : φ.ker = CFSG.oddCore (KBar K)) (hL : L₁ ≤ K) (hperf : ⁅L₁, L₁⁆ = L₁)
    (h60 : (CFSG.pCore 2 ↥L₁).index = 60) :
    (chi hL φ).ker = CFSG.pCore 2 ↥L₁ ∧ Nat.card (chi hL φ).range = 60 := by
  have hZp : Nat.card (ZMod p) = p := Nat.card_zmod p
  have hL₁p : Group.IsPerfect ↥L₁ := Subgroup.isPerfect_iff.mpr hperf
  set χ := chi hL φ with hχ
  have hBperf : ⁅χ.range, χ.range⁆ = χ.range := by
    have : Group.IsPerfect χ.range := Group.IsPerfect.ofSurjective χ.rangeRestrict_surjective
    exact Subgroup.isPerfect_iff.mp this
  have hBne : χ.range ≠ ⊥ := by
    intro h
    have hc : ∀ l : ↥L₁, φ (l1Map hL l) ∈ Subgroup.center SL(2, ZMod p) := fun l => by
      have : χ l ∈ χ.range := ⟨l, rfl⟩
      rw [h, Subgroup.mem_bot, hχ, chi_apply, QuotientGroup.mk'_apply] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    let f := (φ.comp (l1Map hL)).codRestrict (Subgroup.center _) hc
    have hf : ∀ l : ↥L₁, f l = 1 := fun l => (MonoidHom.mem_ker).mp
      (Abelianization.commutator_subset_ker f Group.IsPerfect.mem_commutator)
    have hO : (l1Map hL).range ≤ CFSG.oddCore (KBar K) := by
      rintro _ ⟨l, rfl⟩
      rw [← hφk, MonoidHom.mem_ker]
      exact congrArg Subtype.val (hf l)
    have hodd : Odd (Nat.card (l1Map hL).range) :=
      (Quasithin.A312.odd_card_oddCore _).of_dvd_nat (Subgroup.card_dvd_of_le hO)
    have h1 : (CFSG.pCore 2 ↥L₁).index ∣ Nat.card (l1Map hL).range := by
      rw [← Subgroup.index_ker]
      exact Subgroup.index_dvd_of_le (ker_l1Map_le hL)
    rw [h60] at h1
    have := hodd.of_dvd_nat h1
    norm_num at this
  have hB := O5.perfect_cases (Fact.out : p.Prime) (by omega) hZp hBperf hBne
  have hBs : IsSimpleGroup χ.range := O5.isSimpleGroup_of_cases hp5 hZp hB
  have hBns : ¬ Group.IsSolvable χ.range := by
    have : Group.IsPerfect χ.range := Subgroup.isPerfect_iff.mpr hBperf
    have : Nontrivial χ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hBne
    exact Group.IsPerfect.not_isSolvable _
  have hO2 : CFSG.pCore 2 ↥L₁ ≤ χ.ker := by
    have hN := O5.eq_bot_of_isPGroup_two hBns
      (Subgroup.Normal.map CFSG.pCore_normal χ.rangeRestrict χ.rangeRestrict_surjective)
      (CFSG.pCore_isPGroup.map χ.rangeRestrict)
    intro c hc
    have h1 : χ.rangeRestrict c = 1 := by
      have : χ.rangeRestrict c ∈ (CFSG.pCore 2 ↥L₁).map χ.rangeRestrict := ⟨c, hc, rfl⟩
      rwa [hN, Subgroup.mem_bot] at this
    exact (MonoidHom.mem_ker).mpr (congrArg Subtype.val h1)
  have hdvd : Nat.card χ.range ∣ 60 := by
    rw [← Subgroup.index_ker, ← h60]
    exact Subgroup.index_dvd_of_le hO2
  have hcard : Nat.card χ.range = 60 := by
    rcases hB with h | he
    · have hodd : IsOddPrimePower (Nat.card (ZMod p)) :=
        ⟨p, 1, Fact.out, (Fact.out : p.Prime).odd_of_ne_two (by omega), le_rfl,
          by rw [hZp, pow_one]⟩
      have h1 : Nat.card χ.range = p * (p ^ 2 - 1) / 2 := by
        rw [h, Subgroup.card_top, psl2_card_formula (ZMod p) hodd, hZp]
      rw [h1] at hdvd ⊢
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      have hp5' : p = 5 := by
        by_contra hne
        have h6 : 6 ≤ p := by omega
        have h36 : 36 ≤ p ^ 2 := by nlinarith
        have h35 : 35 ≤ p ^ 2 - 1 := by omega
        have h210 : 210 ≤ p * (p ^ 2 - 1) := by nlinarith
        omega
      subst hp5'
      norm_num
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
  refine ⟨(Subgroup.eq_of_le_of_card_ge hO2 ?_).symm, hcard⟩
  have h1 := Subgroup.card_mul_index χ.ker
  have h2 := Subgroup.card_mul_index (CFSG.pCore 2 ↥L₁)
  rw [Subgroup.index_ker, hcard] at h1
  rw [h60] at h2
  omega

end Chi

end CFSG.Quasithin.Vol2.Ch11.SecD.O6S
