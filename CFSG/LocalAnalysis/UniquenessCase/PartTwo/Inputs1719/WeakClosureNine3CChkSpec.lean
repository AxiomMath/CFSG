module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNine3CChk
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsGeneric
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Spec
public import Certificates.Kernel.Sporadic.Fi22.C3151
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsNormal
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.WeakClosure81.ChkN

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6.Core

variable {n : ℕ}

local notation "PN" => Equiv.Perm (Fin n)

theorem codeN_mul_eq_iff {x y z w : PN} :
    cmul (codeN n x) (codeN n y) = cmul (codeN n z) (codeN n w) ↔ x * y = z * w := by
  rw [← codeN_mul, ← codeN_mul]
  exact ⟨fun h => codeN_injective h, fun h => by rw [h]⟩

theorem codeN_eq_range_iff {x : PN} : codeN n x = List.range n ↔ x = 1 := by
  rw [← codeN_one]
  exact ⟨fun h => codeN_injective h, fun h => by rw [h]⟩

theorem ccomm_iffN {x y : PN} : ccomm (codeN n x) (codeN n y) = true ↔ x * y = y * x := by
  rw [ccomm, beq_iff_eq, codeN_mul_eq_iff]

theorem cinvolN_iff {x : PN} : cinvolN n (codeN n x) = true ↔ x * x = 1 := by
  rw [cinvolN, beq_iff_eq, ← codeN_mul, codeN_eq_range_iff]

theorem codeN_pow (x : PN) (k : ℕ) : codeN n (x ^ k) = cpow (codeN n x) k := by
  induction k with
  | zero => rw [pow_zero, codeN_one, cpow, codeN_length]
  | succ k ih => rw [pow_succ, codeN_mul, ih, cpow]

structure DescN (H : Subgroup PN) (L : List (List ℕ)) : Prop where
  mem : ∀ x, x ∈ H ↔ codeN n x ∈ L
  surj : ∀ c ∈ L, ∃ x ∈ H, codeN n x = c

theorem DescN.card {H : Subgroup PN} {L : List (List ℕ)} (h : DescN H L) (hnd : L.Nodup) :
    Nat.card H = L.length := by
  classical
  have h1 : codeN n '' (H : Set PN) = ↑L.toFinset := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using (h.mem x).mp hx
    · intro hc
      have hc' : c ∈ L := by simpa using hc
      obtain ⟨x, hx, rfl⟩ := h.surj c hc'
      exact ⟨x, hx, rfl⟩
  calc Nat.card H = Nat.card (codeN n '' (H : Set PN)) :=
        (Nat.card_image_of_injective codeN_injective _).symm
    _ = Nat.card ↥(↑L.toFinset : Set (List ℕ)) := by rw [h1]
    _ = L.length := by
        rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem DescN.inf {H K : Subgroup PN} {L M : List (List ℕ)} (hH : DescN H L) (hK : DescN K M) :
    DescN (H ⊓ K) (L.filter M.contains) := by
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · rw [mem_inf, hH.mem, hK.mem, List.mem_filter, List.contains_iff_mem]
  · rw [List.mem_filter, List.contains_iff_mem] at hc
    obtain ⟨x, hx, rfl⟩ := hH.surj c hc.1
    exact ⟨x, ⟨hx, (hK.mem x).mpr hc.2⟩, rfl⟩

theorem exists_list_of_codesN {S : Set PN} :
    ∀ {L : List (List ℕ)}, (∀ c ∈ L, ∃ x ∈ S, codeN n x = c) →
      ∃ l : List PN, l.map (codeN n) = L ∧ ∀ x ∈ l, x ∈ S
  | [], _ => ⟨[], rfl, by simp⟩
  | c :: L, h => by
    obtain ⟨x, hx, rfl⟩ := h c List.mem_cons_self
    obtain ⟨l, hl, hlS⟩ := exists_list_of_codesN (L := L) fun d hd =>
      h d (List.mem_cons_of_mem _ hd)
    exact ⟨x :: l, by simp [hl], by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hlS y hy⟩

theorem SubData.specN {D : SubData} (hD : SubData.okN n D = true) {gens : List PN}
    (hg : gens.map (codeN n) = D.gc) :
    DescN (closure {g | g ∈ gens}) D.lit ∧ D.lit.Nodup := by
  simp only [SubData.okN, Bool.and_eq_true, beq_iff_eq] at hD
  obtain ⟨⟨hlit, htbl⟩, hnd⟩ := hD
  have htbl' : tblCheckC (List.range n) D.gc (buildCodes (List.range n) D.gc D.tree) D.tbl =
      true := by
    rw [← hlit]; exact htbl
  obtain ⟨hmem, hsurj⟩ := mem_closure_iff_of_tblN hg htbl'
  rw [← hlit] at hmem hsurj
  exact ⟨⟨hmem, hsurj⟩, NFA6.nodup_of_nodupB hnd⟩

theorem SubData.exists_descN {D : SubData} (hD : SubData.okN n D = true) {S : Set PN}
    (hgens : ∀ c ∈ D.gc, ∃ x ∈ S, codeN n x = c) :
    ∃ H : Subgroup PN, H ≤ closure S ∧ DescN H D.lit ∧ D.lit.Nodup := by
  obtain ⟨l, hl, hlS⟩ := exists_list_of_codesN hgens
  obtain ⟨hd, hnd⟩ := SubData.specN hD hl
  exact ⟨_, closure_mono fun x hx => hlS x hx, hd, hnd⟩

theorem getD_codeN_mem {gens : List PN} {gc : List (List ℕ)} (hgc : gens.map (codeN n) = gc)
    (i : ℕ) : ∃ g ∈ closure {g | g ∈ gens}, codeN n g = gc.getD i (List.range n) := by
  rcases getD_mem_or_default' gc i (List.range n) with h | h
  · rw [← hgc] at h ⊢
    obtain ⟨g, hg, hgc'⟩ := List.mem_map.mp h
    exact ⟨g, subset_closure hg, hgc'⟩
  · exact ⟨1, one_mem _, by rw [h, codeN_one]⟩

theorem evalWN_spec {gens : List PN} {gc : List (List ℕ)} (hgc : gens.map (codeN n) = gc)
    (w : List ℕ) : ∃ x ∈ closure {g | g ∈ gens}, codeN n x = evalWN n gc w := by
  unfold evalWN
  suffices h : ∀ (w : List ℕ) (x : PN), x ∈ closure {g | g ∈ gens} →
      ∃ y ∈ closure {g | g ∈ gens},
        codeN n y = w.foldl (fun acc i => cmul acc (gc.getD i (List.range n))) (codeN n x) by
    simpa [codeN_one] using h w 1 (one_mem _)
  intro w
  induction w with
  | nil => intro x hx; exact ⟨x, hx, rfl⟩
  | cons i w ih =>
    intro x hx
    obtain ⟨g, hg, hgc'⟩ := getD_codeN_mem hgc i
    simp only [List.foldl_cons]
    rw [← hgc', ← codeN_mul]
    exact ih (x * g) (mul_mem hx hg)

theorem normB_specN {K N : Subgroup PN} {KL NL : List (List ℕ)} (hK : DescN K KL)
    (hN : DescN N NL) (h : normB KL NL = true) {k x : PN} (hk : k ∈ K) (hx : x ∈ N) :
    k * x * k⁻¹ ∈ N := by
  simp only [normB, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨c, hc, he⟩ := h _ ((hK.mem k).mp hk) _ ((hN.mem x).mp hx)
  obtain ⟨x', hx', rfl⟩ := hN.surj c hc
  rw [codeN_mul_eq_iff] at he
  rw [he]
  simpa using hx'

theorem relIndex_of_cardN {H K : Subgroup PN} (hHK : H ≤ K) {a b : ℕ} (hH : Nat.card H = a)
    (hK : Nat.card K = b) (ha : a ≠ 0) : H.relIndex K = b / a := by
  have h1 := relIndex_mul_card H K
  rw [inf_eq_left.mpr hHK, hH, hK] at h1
  rw [← h1, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero ha)]

theorem KData.specN {G T₀ : Subgroup PN} {TL : List (List ℕ)} (hT : DescN T₀ TL)
    (hT2 : IsPGroup 2 T₀) {D : KData} (hD : KData.checkN n D TL = true)
    (hgens : ∀ c ∈ D.K.gc, ∃ x ∈ (G : Set PN), codeN n x = c) :
    ∃ K : Subgroup PN, K ≤ G ∧ DescN K D.K.lit ∧ D.K.lit.Nodup ∧
      (∃ y ∈ K, codeN n y = D.y ∧ TwoPTwo K (K ⊓ T₀) (zpowers y) D.p ∧
        Nat.card (zpowers y) = D.p) ∧
      ∃ N : Subgroup PN, DescN N D.N2.lit ∧ N ≤ pCoreOf 2 K := by
  simp only [KData.checkN, sylB, Bool.and_eq_true, and_assoc, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.or_eq_true] at hD
  obtain ⟨hKok, hN2ok, hNpok, hN2K, hNpK, hN2g, hNpg, hnorm2, hnormp, hexp2, hpow, hq, hy, hyp,
    hy1, hp35, hS0, -, hSodd, -, hpodd⟩ := hD
  obtain ⟨K, hKG, hK, hKnd⟩ := SubData.exists_descN hKok hgens
  rw [closure_eq] at hKG
  have hgK : ∀ {L : List (List ℕ)}, L.all D.K.lit.contains = true →
      ∀ c ∈ L, ∃ x ∈ (K : Set PN), codeN n x = c := by
    intro L hL c hc
    rw [List.all_eq_true] at hL
    exact hK.surj c (List.contains_iff_mem.mp (hL c hc))
  obtain ⟨N2, hN2le, hN2, -⟩ := SubData.exists_descN hN2ok (hgK hN2g)
  obtain ⟨Np, hNple, hNp, -⟩ := SubData.exists_descN hNpok (hgK hNpg)
  rw [closure_eq] at hN2le hNple
  have hpr : D.p.Prime := by rcases hp35 with h | h <;> rw [h] <;> norm_num
  have : Fact D.p.Prime := ⟨hpr⟩
  have hn2 : (N2.subgroupOf K).Normal :=
    ⟨fun x hx k => by
      rw [mem_subgroupOf] at hx ⊢
      exact normB_specN hK hN2 hnorm2 k.2 hx⟩
  have hnp : (Np.subgroupOf K).Normal :=
    ⟨fun x hx k => by
      rw [mem_subgroupOf] at hx ⊢
      exact normB_specN hK hNp hnormp k.2 hx⟩
  have hN2p : IsPGroup 2 (N2.subgroupOf K) := by
    intro g
    refine ⟨3, ?_⟩
    have hx : ((g : K) : PN) ∈ N2 := g.2
    rw [List.all_eq_true] at hexp2
    have h8 := hexp2 _ ((hN2.mem _).mp hx)
    rw [beq_iff_eq, ← codeN_pow, codeN_eq_range_iff] at h8
    apply Subtype.ext
    apply Subtype.ext
    simpa using h8
  have hO : CFSG.Quasithin.E1.oTwoPTwo ↥K D.p = ⊤ := by
    have := hn2
    have := hnp
    refine CFSG.Quasithin.E1.oTwoPTwo_eq_top_of_series (N₂ := N2.subgroupOf K)
      (N₂p := Np.subgroupOf K) hN2p (fun x hx => ⟨1, ?_⟩) (fun q => ⟨3, ?_⟩)
    · rw [mem_subgroupOf] at hx ⊢
      rw [List.all_eq_true] at hpow
      have h1 := List.contains_iff_mem.mp (hpow _ ((hNp.mem _).mp hx))
      rw [← codeN_pow] at h1
      rw [pow_one, Subgroup.coe_pow]
      exact (hN2.mem _).mpr h1
    · rw [mem_subgroupOf]
      rw [List.all_eq_true] at hq
      have h1 := List.contains_iff_mem.mp (hq _ ((hK.mem _).mp q.2))
      rw [← codeN_pow] at h1
      rw [Subgroup.coe_pow]
      exact (hNp.mem _).mpr (by simpa using h1)
  have hS : DescN (K ⊓ T₀) (D.K.lit.filter TL.contains) := hK.inf hT
  have hSc : Nat.card (K ⊓ T₀ : Subgroup PN) = (D.K.lit.filter TL.contains).length :=
    hS.card (hKnd.filter _)
  have hKc : Nat.card K = D.K.lit.length := hK.card hKnd
  obtain ⟨y, hyK, hyc⟩ := hK.surj _ (List.contains_iff_mem.mp hy)
  rw [← hyc, ← codeN_pow, codeN_eq_range_iff] at hyp
  have hy1' : y ≠ 1 := fun h => hy1 (by rw [← hyc, h, codeN_one])
  have hoy : orderOf y = D.p := orderOf_eq_prime hyp hy1'
  have hZc : Nat.card (zpowers y) = D.p := by rw [Nat.card_zpowers, hoy]
  refine ⟨K, hKG, hK, hKnd, ⟨y, hyK, hyc, ⟨hpr, ?_, hO, ⟨inf_le_left, hT2.to_le inf_le_right, ?_⟩,
    ⟨zpowers_le.mpr hyK, IsPGroup.of_card (n := 1) (by rw [hZc, pow_one]), ?_⟩⟩, hZc⟩,
    N2, hN2, ?_⟩
  · rcases hp35 with h | h <;> rw [h] <;> norm_num
  · rw [relIndex_of_cardN inf_le_left hSc hKc hS0]
    omega
  · rw [relIndex_of_cardN (zpowers_le.mpr hyK) hZc hKc hpr.ne_zero]
    exact hpodd ∘ Nat.mod_eq_zero_of_dvd
  · intro x hx
    have h1 : (⟨x, hN2le hx⟩ : ↥K) ∈ CFSG.pCore 2 ↥K :=
      CFSG.LieType.BorelTits.le_pCore 2 hn2 hN2p (show _ ∈ N2.subgroupOf K from hx)
    exact ⟨_, h1, rfl⟩

theorem mem_e4N_iff {a b x : PN} : codeN n x ∈ e4N n (codeN n a) (codeN n b) ↔
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  simp only [e4N, List.mem_cons, List.not_mem_nil, or_false, ← codeN_one, ← codeN_mul,
    codeN_injective.eq_iff]

theorem mem_e8N_iff {a b c x : PN} : codeN n x ∈ e8N n (codeN n a) (codeN n b) (codeN n c) ↔
    x = 1 ∨ x = a ∨ x = b ∨ x = c ∨ x = a * b ∨ x = a * c ∨ x = b * c ∨ x = a * b * c := by
  simp only [e8N, List.mem_cons, List.not_mem_nil, or_false, ← codeN_one, ← codeN_mul,
    codeN_injective.eq_iff]

theorem setEq_memN {E F : List (List ℕ)} (h : setEq E F = true) (c : List ℕ) :
    c ∈ E ↔ c ∈ F := by
  simp only [setEq, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨h.1 c, h.2 c⟩

theorem exists_two_neN {A : Subgroup PN} (h : 3 ≤ Nat.card A) :
    ∃ a ∈ A, a ≠ 1 ∧ ∃ b ∈ A, b ≠ 1 ∧ b ≠ a := by
  by_cases h1 : ∃ a ∈ A, a ≠ 1
  · obtain ⟨a, ha, ha1⟩ := h1
    by_contra hcon
    have hsub : (A : Set PN) ⊆ {1, a} := by
      intro b hb
      by_cases hb1 : b = 1
      · simp [hb1]
      · have : b = a := by
          by_contra hba
          exact hcon ⟨a, ha, ha1, b, hb, hb1, hba⟩
        simp [this]
    have h2 : Nat.card A ≤ 2 := by
      change Nat.card (A : Set PN) ≤ 2
      rw [Nat.card_coe_set_eq]
      calc (A : Set PN).ncard ≤ ({1, a} : Set PN).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by
          refine (Set.ncard_insert_le _ _).trans ?_
          rw [Set.ncard_singleton]
    omega
  · push Not at h1
    have : A = ⊥ := eq_bot_iff.mpr fun x hx => (mem_bot).mpr (h1 x hx)
    rw [this, card_bot] at h
    omega

theorem mem_invsN {T₀ : Subgroup PN} {TL : List (List ℕ)} (hT : DescN T₀ TL) {x : PN}
    (hx : x ∈ T₀) (hx1 : x ≠ 1) (hxx : x * x = 1) : codeN n x ∈ invsN n TL := by
  rw [invsN, List.mem_filter]
  refine ⟨(hT.mem x).mp hx, ?_⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨fun h => hx1 (codeN_eq_range_iff.mp h), cinvolN_iff.mpr hxx⟩

theorem seed_specN {T₀ : Subgroup PN} {TL : List (List ℕ)} (hT : DescN T₀ TL)
    {Es : List (List (List ℕ))} (hseed : seedCheckN n TL Es = true) {A : Subgroup PN}
    (hAT : A ≤ T₀) (hAe : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A) :
    ∃ E ∈ Es, ∀ x, x ∈ A ↔ codeN n x ∈ E := by
  obtain ⟨a, ha, ha1, b, hb, hb1, hba⟩ := exists_two_neN (by omega : 3 ≤ Nat.card A)
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have := hAe.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← pow_two]; exact hAe.2 x hx
  have hinvs : ∀ x ∈ A, x ≠ 1 → codeN n x ∈ invsN n TL := fun x hx hx1 =>
    mem_invsN hT (hAT hx) hx1 (hsq x hx)
  have hW : ∀ x ∈ A, x ≠ 1 →
      codeN n x ∈ ((invsN n TL).filter (ccomm (codeN n a))).filter (ccomm (codeN n b)) := by
    intro x hx hx1
    rw [List.mem_filter, List.mem_filter]
    exact ⟨⟨hinvs x hx hx1, ccomm_iffN.mpr (hcomm a ha x hx)⟩, ccomm_iffN.mpr (hcomm b hb x hx)⟩
  unfold seedCheckN seedCheckIN at hseed
  rw [List.all_eq_true] at hseed
  have h1 := hseed _ (hinvs a ha ha1)
  rw [List.all_eq_true] at h1
  have h2 := h1 (codeN n b)
    (List.mem_filter.mpr ⟨hinvs b hb hb1, ccomm_iffN.mpr (hcomm a ha b hb)⟩)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.any_eq_true,
    List.all_eq_true] at h2
  rcases h2 with h2 | ⟨⟨E, hE, hEeq⟩, hX⟩
  · exact absurd (codeN_injective h2).symm hba
  by_cases hall : ∀ x ∈ A, codeN n x ∈ e4N n (codeN n a) (codeN n b)
  · refine ⟨E, hE, fun x => ?_⟩
    rw [← setEq_memN hEeq]
    refine ⟨hall x, fun hx => ?_⟩
    rcases mem_e4N_iff.mp hx with rfl | rfl | rfl | rfl
    · exact one_mem A
    · exact ha
    · exact hb
    · exact mul_mem ha hb
  · push Not at hall
    obtain ⟨c, hc, hc4⟩ := hall
    have hc1 : c ≠ 1 := by
      rintro rfl
      exact hc4 (mem_e4N_iff.mpr (Or.inl rfl))
    rcases hX (codeN n c) (hW c hc hc1) with h3 | ⟨⟨E', hE', hE'eq⟩, hY⟩
    · exact absurd (List.contains_iff_mem.mp h3) hc4
    refine ⟨E', hE', fun x => ?_⟩
    rw [← setEq_memN hE'eq]
    constructor
    · intro hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact mem_e8N_iff.mpr (Or.inl rfl)
      · rcases hY (codeN n x) (hW x hx hx1) with h4 | h4
        · exact absurd (ccomm_iffN.mpr (hcomm c hc x hx)) (by simpa using h4)
        · exact List.contains_iff_mem.mp h4
    · intro hx
      rcases mem_e8N_iff.mp hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact one_mem A
      · exact ha
      · exact hb
      · exact hc
      · exact mul_mem ha hb
      · exact mul_mem ha hc
      · exact mul_mem hb hc
      · exact mul_mem (mul_mem ha hb) hc

theorem card_two_or_four_le {A : Subgroup PN} (hAe : IsElemAbelian 2 A) (hA : A ≠ ⊥) :
    Nat.card A = 2 ∨ 4 ≤ Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 A := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow]
    exact hAe.2 _ g.2
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  rcases k with _ | _ | k
  · exact absurd ((card_eq_one).mp (by rw [hk, pow_zero])) hA
  · left; rw [hk, pow_one]
  · right
    rw [hk, pow_succ, pow_succ]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

theorem seedAll_specN {T₀ : Subgroup PN} {TL : List (List ℕ)} (hT : DescN T₀ TL)
    {Es : List (List (List ℕ))} (hseed : seedCheckN n TL Es = true)
    (hseed2 : seed2CheckN n TL Es = true) {A : Subgroup PN} (hAT : A ≤ T₀)
    (hAe : IsElemAbelian 2 A) :
    A = ⊥ ∨ ∃ E ∈ Es, ∀ x, x ∈ A ↔ codeN n x ∈ E := by
  by_cases hA : A = ⊥
  · exact Or.inl hA
  right
  rcases card_two_or_four_le hAe hA with h2 | h4
  · obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
    have ha' : (a : PN) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hsq : (a : PN) * a = 1 := by rw [← pow_two]; exact hAe.2 _ a.2
    have h1 := List.all_eq_true.mp hseed2 _ (mem_invsN hT (hAT a.2) ha' hsq)
    rw [List.any_eq_true] at h1
    obtain ⟨E, hE, hEeq⟩ := h1
    refine ⟨E, hE, fun x => ?_⟩
    rw [← setEq_memN hEeq]
    have hAx : ∀ x, x ∈ A ↔ x = 1 ∨ x = a := by
      intro x
      constructor
      · intro hx
        by_contra hne
        push Not at hne
        have hsub : ({1, (a : PN), x} : Set PN) ⊆ (A : Set PN) := by
          intro y hy
          rcases hy with rfl | rfl | rfl
          · exact one_mem A
          · exact a.2
          · exact hx
        have h3 : ({1, (a : PN), x} : Set PN).ncard = 3 := by
          rw [Set.ncard_eq_three]
          exact ⟨1, a, x, fun h => ha' h.symm, fun h => hne.1 h.symm, fun h => hne.2 h.symm, rfl⟩
        have h4 : ({1, (a : PN), x} : Set PN).ncard ≤ Nat.card A := by
          change _ ≤ Nat.card (A : Set PN)
          rw [Nat.card_coe_set_eq]
          exact Set.ncard_le_ncard hsub (Set.toFinite _)
        omega
      · rintro (rfl | rfl)
        · exact one_mem A
        · exact a.2
    rw [hAx]
    simp only [List.mem_cons, List.not_mem_nil, or_false, ← codeN_one, codeN_injective.eq_iff]
  · exact seed_specN hT hseed hAT hAe h4

theorem normT_specN {S : Subgroup PN} {SL : List (List ℕ)} (hS : DescN S SL) {t : List ℕ}
    (h : normT SL t = true) {τ : PN} (hτ : codeN n τ = t) : τ ∈ normalizer (S : Set PN) := by
  simp only [normT, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    obtain ⟨c, hc, he⟩ := h1 _ ((hS.mem s).mp hs)
    obtain ⟨σ, hσ, rfl⟩ := hS.surj c hc
    rw [← hτ, codeN_mul_eq_iff] at he
    have e : τ * s * τ⁻¹ = σ := by rw [he]; group
    rw [e]
    exact hσ
  · intro hs
    obtain ⟨c, hc, he⟩ := h2 _ ((hS.mem _).mp hs)
    obtain ⟨σ, hσ, rfl⟩ := hS.surj c hc
    rw [← hτ, codeN_mul_eq_iff] at he
    have e : s = σ :=
      calc s = τ⁻¹ * (τ * s * τ⁻¹ * τ) := by group
        _ = τ⁻¹ * (τ * σ) := by rw [he]
        _ = σ := by group
    rw [e]
    exact hσ

theorem invCheck_specN {T₀ : Subgroup PN} {TL TLinv : List (List ℕ)} (hT : DescN T₀ TL)
    (hinv : invCheckN n TL TLinv = true) {h hi : List ℕ} (hmem : (h, hi) ∈ TL.zip TLinv) :
    ∃ y ∈ T₀, codeN n y = h ∧ codeN n y⁻¹ = hi := by
  simp only [invCheckN, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hinv
  obtain ⟨⟨-, hprod⟩, hin⟩ := hinv
  obtain ⟨hh, hhi⟩ := List.of_mem_zip hmem
  obtain ⟨y, hy, rfl⟩ := hT.surj h hh
  obtain ⟨z, -, rfl⟩ := hT.surj hi (List.contains_iff_mem.mp (hin _ hhi))
  have h1 := hprod _ hmem
  simp only at h1
  rw [← codeN_mul, codeN_eq_range_iff] at h1
  exact ⟨y, hy, rfl, by rw [eq_inv_of_mul_eq_one_right h1]⟩

theorem nonNormal_specN {T₀ : Subgroup PN} {TL TLinv : List (List ℕ)} (hT : DescN T₀ TL)
    (hinv : invCheckN n TL TLinv = true) {E : List (List ℕ)} (hET : E.all TL.contains = true)
    (h : nonNormal TL TLinv E = true) {A : Subgroup PN} (hA : ∀ x, x ∈ A ↔ codeN n x ∈ E) :
    ¬ T₀ ≤ normalizer (A : Set PN) := by
  intro hTN
  simp only [nonNormal, List.any_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hc, hic⟩, hmem, e, heE, hne⟩ := h
  obtain ⟨y, hyT, rfl, rfl⟩ := invCheck_specN hT hinv hmem
  obtain ⟨ε, -, rfl⟩ := hT.surj e (List.contains_iff_mem.mp ((List.all_eq_true.mp hET) e heE))
  have h1 : y * ε * y⁻¹ ∈ A := (mem_normalizer_iff.mp (hTN hyT) ε).mp ((hA ε).mpr heE)
  rw [hA, codeN_mul, codeN_mul] at h1
  simp only at hne
  rw [List.contains_iff_mem.mpr h1] at hne
  exact Bool.noConfusion hne

theorem centFreeN_spec {H : Subgroup PN} {HL : List (List ℕ)} (hH : DescN H HL)
    {gens : List PN} {gc : List (List ℕ)} (hgc : gens.map (codeN n) = gc)
    (h : centFreeN n HL gc = true) {x : PN} (hx : x ∈ H)
    (hc : ∀ l ∈ closure {g | g ∈ gens}, x * l = l * x) : x = 1 := by
  have h1 := List.all_eq_true.mp h _ ((hH.mem x).mp hx)
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with h1 | ⟨l, hl, hne⟩
  · exact codeN_eq_range_iff.mp h1
  · exfalso
    rw [← hgc] at hl
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hl
    rw [ccomm_iffN.mpr (hc g (subset_closure hg))] at hne
    exact Bool.noConfusion hne

end CFSG.LocalAnalysis.WeakClosure81.ChkN
