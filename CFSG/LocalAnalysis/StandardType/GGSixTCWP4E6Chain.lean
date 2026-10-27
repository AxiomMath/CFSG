module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6ChainDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Form
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.Chevalley.RootCharacterKernelProduct
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.TableCRes

open CFSG.StandardType.KGCentE6 (iform_comm_E6 iform_add_left_E6 iform_smul_left_E6
  iform_sub_left_E6 iform_right_neg_E6)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem list_length_five {c : List ℤ} (hc : c.length = 5) :
    ∃ c0 c1 c2 c3 c4 : ℤ, c = [c0, c1, c2, c3, c4] := by
  match c, hc with
  | [c0, c1, c2, c3, c4], _ => exact ⟨c0, c1, c2, c3, c4, rfl⟩

theorem chainVec_five (c0 c1 c2 c3 c4 : ℤ) (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) :
    tcChainVec [c0, c1, c2, c3, c4] δ = c0 • δ 0 + c1 • δ 1 + c2 • δ 2 + c3 • δ 3 + c4 • δ 4 := by
  simp [tcChainVec, Fin.sum_univ_five]

theorem iform_chainVec {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)}
    (hδ : ∀ j k, iform (δ j) (δ k) = a5gram j k) {c c' : List ℤ}
    (hc : c.length = 5) (hc' : c'.length = 5) :
    iform (tcChainVec c δ) (tcChainVec c' δ) = ip5 c c' := by
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ := list_length_five hc
  obtain ⟨d0, d1, d2, d3, d4, rfl⟩ := list_length_five hc'
  rw [chainVec_five, chainVec_five]
  simp only [iform_add_left_E6, iform_add_right_E6, iform_smul_left_E6, iform_smul_right_E6, hδ]
  simp [a5gram, ip5]
  ring

theorem chainVec_injective {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)}
    (hδ : ∀ j k, iform (δ j) (δ k) = a5gram j k) {c c' : List ℤ}
    (hc : c.length = 5) (hc' : c'.length = 5) (h : tcChainVec c δ = tcChainVec c' δ) : c = c' := by
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ := list_length_five hc
  obtain ⟨d0, d1, d2, d3, d4, rfl⟩ := list_length_five hc'
  have hc5 : ([c0, c1, c2, c3, c4] : List ℤ).length = 5 := rfl
  have hd5 : ([d0, d1, d2, d3, d4] : List ℤ).length = 5 := rfl
  have key : ∀ u : List ℤ, u.length = 5 →
      ip5 [c0, c1, c2, c3, c4] u = ip5 [d0, d1, d2, d3, d4] u := by
    intro u hu
    have h1 : iform (tcChainVec [c0, c1, c2, c3, c4] δ) (tcChainVec u δ) =
        iform (tcChainVec [d0, d1, d2, d3, d4] δ) (tcChainVec u δ) := by rw [h]
    rw [iform_chainVec hδ hc5 hu, iform_chainVec hδ hd5 hu] at h1
    exact h1
  have e0 := key [1, 0, 0, 0, 0] rfl
  have e1 := key [0, 1, 0, 0, 0] rfl
  have e2 := key [0, 0, 1, 0, 0] rfl
  have e3 := key [0, 0, 0, 1, 0] rfl
  have e4 := key [0, 0, 0, 0, 1] rfl
  simp only [ip5] at e0 e1 e2 e3 e4
  simp only [List.cons.injEq, and_true]
  omega

theorem chainVec_negS (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) (c : List ℤ) :
    tcChainVec (tcNegS c) δ = -tcChainVec c δ := by
  have hget : ∀ (l : List ℤ) (k : ℕ), (tcNegS l).getD k 0 = -(l.getD k 0) := by
    intro l k
    simp only [tcNegS, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases l[k]? <;> simp
  unfold tcChainVec
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hget, neg_smul]

theorem chainVec_intv_self (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) (k : ℕ) (hk : k < 5) :
    tcChainVec (intv k (k + 1)) δ = δ ⟨k, hk⟩ := by
  interval_cases k <;> simp [intv, tcChainVec, Fin.sum_univ_five]

theorem chainVec_intv_succ (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) (a k : ℕ) (hk : k < 5)
    (hak : a ≤ k) :
    tcChainVec (intv a (k + 1)) δ = tcChainVec (intv a k) δ + δ ⟨k, hk⟩ := by
  interval_cases k <;> interval_cases a <;> simp [intv, tcChainVec, Fin.sum_univ_five] <;> abel

theorem iform_chainVec_intv_succ {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)}
    (hδ : ∀ j k, iform (δ j) (δ k) = a5gram j k) (a k : ℕ) (hk : k < 5) (hak : a < k) :
    iform (tcChainVec (intv a k) δ) (δ ⟨k, hk⟩) = -1 := by
  interval_cases k <;> interval_cases a <;>
    simp [intv, tcChainVec, Fin.sum_univ_five, iform_add_left_E6, iform_smul_left_E6, hδ, a5gram]

theorem isRoot_of_mem_chainSet
    {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)} (hδ : A5Chain δ) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ tcChainSet δ) : IsRoot .E6 γ := by
  have hgram := hδ.gram
  have hstep : ∀ v w : Fin Tag.E6.rank → ℤ, IsRoot .E6 v → IsRoot .E6 w →
      iform w w = 2 → iform v w = -1 → IsRoot .E6 (v + w) := by
    intro v w hv hw hww hvw
    refine isRoot_add_of_iform_neg hv hw ?_ (by rw [hvw]; norm_num)
    intro heq
    have h2 : iform v w = -2 := by rw [heq, iform_neg_left_E6, hww]
    rw [hvw] at h2
    norm_num at h2
  have hint : ∀ n : ℕ, ∀ hn : n < 5, ∀ a : ℕ, a ≤ n →
      IsRoot .E6 (tcChainVec (intv a (n + 1)) δ) := by
    intro n
    induction n with
    | zero =>
      intro hn a ha
      obtain rfl : a = 0 := by omega
      rw [chainVec_intv_self δ 0 hn]
      exact hδ.root _
    | succ m ih =>
      intro hn a ha
      rcases Nat.lt_or_ge a (m + 1) with h | h
      · have hm : m < 5 := by omega
        have hroot := ih hm a (by omega)
        rw [chainVec_intv_succ δ a (m + 1) hn (by omega)]
        exact hstep _ _ hroot (hδ.root _)
          (by rw [hgram]; simp [a5gram]) (iform_chainVec_intv_succ hgram a (m + 1) hn h)
      · obtain rfl : a = m + 1 := by omega
        rw [chainVec_intv_self δ (m + 1) hn]
        exact hδ.root _
  have hint' : ∀ a b : ℕ, a < b → b ≤ 5 → IsRoot .E6 (tcChainVec (intv a b) δ) := by
    intro a b hab hb
    have h := hint (b - 1) (by omega) a (by omega)
    rwa [show b - 1 + 1 = b by omega] at h
  have hpos : ∀ c ∈ stdPos, IsRoot .E6 (tcChainVec c δ) := by
    intro c hc
    simp only [stdPos, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> exact hint' _ _ (by norm_num) (by norm_num)
  obtain ⟨c, hc, rfl⟩ := hγ
  rcases List.mem_append.1 (show c ∈ stdPos ++ stdPos.map tcNegS from hc) with h | h
  · exact hpos c h
  · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 h
    rw [chainVec_negS]
    exact IsRoot.neg (hpos c0 hc0)

theorem std30_length : ∀ c ∈ std30, c.length = 5 := by decide

theorem intv_succ_mem_std30 : ∀ k : Fin 5, intv k.val (k.val + 1) ∈ std30 := by decide

theorem delta_mem_chainSet (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) (k : Fin 5) : δ k ∈ tcChainSet δ :=
  ⟨intv k.val (k.val + 1), intv_succ_mem_std30 k, (chainVec_intv_self δ k.val k.isLt).symm⟩

theorem chainVec_intv_self' (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) (k : Fin 5) :
    tcChainVec (intv k.val (k.val + 1)) δ = δ k :=
  chainVec_intv_self δ k.val k.isLt

theorem chainSet_eq_image (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) :
    tcChainSet δ = (fun c => tcChainVec c δ) '' ↑(std30.toFinset) := by
  ext γ
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, Finset.mem_coe.2 (List.mem_toFinset.2 hc), rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, List.mem_toFinset.1 (Finset.mem_coe.1 hc), rfl⟩

theorem ncard_chainSet {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)}
    (hδ : ∀ j k, iform (δ j) (δ k) = a5gram j k) :
    (tcChainSet δ).ncard = 30 := by
  have hnd : std30.Nodup := by decide
  have hcard : std30.toFinset.card = 30 := by
    rw [List.toFinset_card_of_nodup hnd]
    rfl
  have hinj : Set.InjOn (fun c => tcChainVec c δ) ↑(std30.toFinset) := by
    intro c hc c' hc' h
    exact chainVec_injective hδ (std30_length c (List.mem_toFinset.1 (Finset.mem_coe.1 hc)))
      (std30_length c' (List.mem_toFinset.1 (Finset.mem_coe.1 hc'))) h
  rw [chainSet_eq_image δ, hinj.ncard_image, Set.ncard_coe_finset, hcard]

theorem compRank_chainSet {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)}
    (hδ : ∀ j k, iform (δ j) (δ k) = a5gram j k) : compRank (tcChainSet δ) = 5 := by
  have key : ∀ x y : Fin Tag.E6.rank → ℤ,
      ∑ i, ((x i : ℤ) : ℚ) * ∑ l, ((Tag.E6.symmetrizedCartan i l : ℤ) : ℚ) * ((y l : ℤ) : ℚ)
        = ((iform x y : ℤ) : ℚ) := by
    intro x y
    unfold iform
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hli : LinearIndependent ℚ
      (fun k : Fin 5 => fun i : Fin Tag.E6.rank => ((δ k i : ℤ) : ℚ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hfun : ∀ i : Fin Tag.E6.rank, ∑ k, g k * ((δ k i : ℤ) : ℚ) = 0 := by
      intro i
      have h := congrFun hg i
      simpa [Finset.sum_apply] using h
    have E : ∀ j : Fin 5, ∑ k, g k * ((a5gram k j : ℤ) : ℚ) = 0 := by
      intro j
      obtain ⟨W, hW⟩ : ∃ W : Fin Tag.E6.rank → ℚ,
          ∀ i, W i = ∑ l, ((Tag.E6.symmetrizedCartan i l : ℤ) : ℚ) * ((δ j l : ℤ) : ℚ) :=
        ⟨_, fun i => rfl⟩
      have hw : ∀ k : Fin 5, ∑ i, ((δ k i : ℤ) : ℚ) * W i = ((a5gram k j : ℤ) : ℚ) := by
        intro k
        simp only [hW]
        rw [key, hδ k j]
      have swap : ∑ i, (∑ k, g k * ((δ k i : ℤ) : ℚ)) * W i
          = ∑ k, g k * ∑ i, ((δ k i : ℤ) : ℚ) * W i := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
      have h0 : ∑ i, (∑ k, g k * ((δ k i : ℤ) : ℚ)) * W i = 0 := by
        simp [hfun]
      calc ∑ k, g k * ((a5gram k j : ℤ) : ℚ)
          = ∑ k, g k * ∑ i, ((δ k i : ℤ) : ℚ) * W i :=
            Finset.sum_congr rfl fun k _ => by rw [hw k]
        _ = ∑ i, (∑ k, g k * ((δ k i : ℤ) : ℚ)) * W i := swap.symm
        _ = 0 := h0
    have e0 := E 0
    have e1 := E 1
    have e2 := E 2
    have e3 := E 3
    have e4 := E 4
    simp [Fin.sum_univ_five, a5gram] at e0 e1 e2 e3 e4
    intro i
    fin_cases i <;> simp <;> linarith
  have hspan : Submodule.span ℚ ((fun γ (i : Fin Tag.E6.rank) => ((γ i : ℤ) : ℚ)) '' tcChainSet δ) =
      Submodule.span ℚ
        (Set.range fun k : Fin 5 => fun i : Fin Tag.E6.rank => ((δ k i : ℤ) : ℚ)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨γ, ⟨c, hc, rfl⟩, rfl⟩
      have hform : (fun i : Fin Tag.E6.rank => ((tcChainVec c δ i : ℤ) : ℚ)) =
          ∑ k : Fin 5, ((c.getD k.val 0 : ℤ) : ℚ) •
            (fun i : Fin Tag.E6.rank => ((δ k i : ℤ) : ℚ)) := by
        ext i
        simp [tcChainVec, Finset.sum_apply]
      show (fun i : Fin Tag.E6.rank => ((tcChainVec c δ i : ℤ) : ℚ)) ∈ _
      rw [hform]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨δ k, delta_mem_chainSet δ k, rfl⟩
  unfold compRank
  rw [hspan, finrank_span_eq_card hli]
  simp

theorem std30_ip5_ne_zero : ∀ c ∈ std30, ∃ a : Fin 5, ip5 c (intv a.val (a.val + 1)) ≠ 0 := by
  decide

theorem componentRoots_eq_chainSet
    {M : Type*} [CommGroup M] {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)} (hδ : A5Chain δ)
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M) (hker : kernelRoots χ = tcChainSet δ)
    (i : KernelComponent χ) : componentRoots χ i = tcChainSet δ := by
  have hg := hδ.gram
  have hk : ∀ x ∈ tcChainSet δ, x ∈ kernelRoots χ := fun x hx => by rw [hker]; exact hx
  have e01 : (⟦⟨δ 0, hk _ (delta_mem_chainSet δ 0)⟩⟧ : KernelComponent χ)
      = ⟦⟨δ 1, hk _ (delta_mem_chainSet δ 1)⟩⟧ :=
    mk_eq_of_iform_ne_zero (show iform (δ 0) (δ 1) ≠ 0 by rw [hg 0 1]; decide)
  have e12 : (⟦⟨δ 1, hk _ (delta_mem_chainSet δ 1)⟩⟧ : KernelComponent χ)
      = ⟦⟨δ 2, hk _ (delta_mem_chainSet δ 2)⟩⟧ :=
    mk_eq_of_iform_ne_zero (show iform (δ 1) (δ 2) ≠ 0 by rw [hg 1 2]; decide)
  have e23 : (⟦⟨δ 2, hk _ (delta_mem_chainSet δ 2)⟩⟧ : KernelComponent χ)
      = ⟦⟨δ 3, hk _ (delta_mem_chainSet δ 3)⟩⟧ :=
    mk_eq_of_iform_ne_zero (show iform (δ 2) (δ 3) ≠ 0 by rw [hg 2 3]; decide)
  have e34 : (⟦⟨δ 3, hk _ (delta_mem_chainSet δ 3)⟩⟧ : KernelComponent χ)
      = ⟦⟨δ 4, hk _ (delta_mem_chainSet δ 4)⟩⟧ :=
    mk_eq_of_iform_ne_zero (show iform (δ 3) (δ 4) ≠ 0 by rw [hg 3 4]; decide)
  have hf : ∀ a : Fin 5, (⟦⟨δ a, hk _ (delta_mem_chainSet δ a)⟩⟧ : KernelComponent χ)
      = ⟦⟨δ 0, hk _ (delta_mem_chainSet δ 0)⟩⟧ := by
    intro a
    fin_cases a
    · rfl
    · exact e01.symm
    · exact e12.symm.trans e01.symm
    · exact (e23.symm.trans e12.symm).trans e01.symm
    · exact ((e34.symm.trans e23.symm).trans e12.symm).trans e01.symm
  have hsame : ∀ x (hx : x ∈ tcChainSet δ), (⟦⟨x, hk x hx⟩⟧ : KernelComponent χ)
      = ⟦⟨δ 0, hk _ (delta_mem_chainSet δ 0)⟩⟧ := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨a, ha⟩ := std30_ip5_ne_zero c hc
    have hiff : iform (tcChainVec c δ) (δ a) ≠ 0 := by
      rw [← chainVec_intv_self' δ a,
        iform_chainVec hg (std30_length c hc) (by simp [intv])]
      exact ha
    exact (mk_eq_of_iform_ne_zero
      (α := ⟨tcChainVec c δ, hk _ ⟨c, hc, rfl⟩⟩) (β := ⟨δ a, hk _ (delta_mem_chainSet δ a)⟩)
      hiff).trans (hf a)
  ext x
  constructor
  · rintro ⟨h, -⟩
    rw [← hker]
    exact h
  · intro hx
    obtain ⟨a, ha⟩ := Quotient.exists_rep i
    refine ⟨hk x hx, ?_⟩
    have hy : (a : Fin Tag.E6.rank → ℤ) ∈ tcChainSet δ := by
      rw [← hker]
      exact a.2
    rw [← ha]
    exact (hsame x hx).trans (hsame _ hy).symm

theorem tcE6_componentOrbitLength_eq_one {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {Ψ : Set (Fin τ.rank → ℤ)} (h : (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' Ψ = Ψ) :
    componentOrbitLength ρ Ψ = 1 := by
  have h1 : (1 : ℕ) ∈ {s : ℕ | 0 < s ∧ (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[s] '' Ψ = Ψ} :=
    ⟨Nat.one_pos, by rw [Function.iterate_one]; exact h⟩
  unfold componentOrbitLength
  have hmem := Nat.sInf_mem (Set.nonempty_of_mem h1)
  have hle := Nat.sInf_le h1
  obtain ⟨hpos, -⟩ := hmem
  omega

theorem chainVec_five' (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) (c0 c1 c2 c3 c4 : ℤ) :
    tcChainVec [c0, c1, c2, c3, c4] δ = c0 • δ 0 + c1 • δ 1 + c2 • δ 2 + c3 • δ 3 + c4 • δ 4 := by
  simp [tcChainVec, Fin.sum_univ_five]

theorem exists_list5 {c : List ℤ} (hc : c.length = 5) :
    ∃ c0 c1 c2 c3 c4 : ℤ, c = [c0, c1, c2, c3, c4] := by
  rcases c with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, _ | ⟨c5, c⟩⟩⟩⟩⟩⟩ <;> simp at hc
  exact ⟨c0, c1, c2, c3, c4, rfl⟩

theorem length_applyWordStd_five {c : List ℤ} (hc : c.length = 5) (w : List (ℕ × ℕ)) :
    (applyWordStd w c).length = 5 := by
  induction w with
  | nil => simpa [applyWordStd] using hc
  | cons ab w ih =>
    show (reflectStd (intv ab.1 ab.2) (applyWordStd w c)).length = 5
    simp [reflectStd, ih, intv]

theorem smul_chainVec_eq_sum (g : WeylGroup Tag.E6) (δ : Fin 5 → (Fin Tag.E6.rank → ℤ))
    (c : List ℤ) :
    g • tcChainVec c δ = ∑ k : Fin 5, c.getD k.val 0 • (g • δ k) := by
  unfold tcChainVec
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_comm]

theorem ip5_eq_of_image {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)} (hδ : A5Chain δ)
    {ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)}
    (hρform : ∀ γ γ', iform (ρ γ) (ρ γ') = iform γ γ') {j k : Fin 5} {x y : List ℤ}
    (hx : x.length = 5) (hy : y.length = 5) (hxj : ρ (δ j) = tcChainVec x δ)
    (hyk : ρ (δ k) = tcChainVec y δ) : ip5 x y = a5gram j k := by
  rw [← iform_chainVec hδ.gram hx hy, ← hxj, ← hyk, hρform, hδ.gram]

theorem chainVec_sub_smul (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) (k : ℤ) {c g : List ℤ}
    (hc : c.length = 5) (hg : g.length = 5) :
    tcChainVec (List.zipWith (fun x y => x - k * y) c g) δ =
      tcChainVec c δ - k • tcChainVec g δ := by
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ := exists_list5 hc
  obtain ⟨g0, g1, g2, g3, g4, rfl⟩ := exists_list5 hg
  simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.zipWith_nil_right, chainVec_five']
  module

theorem rootReflection_chainVec
    {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)} (hδ : A5Chain δ) {a b : ℕ} (hab : intv a b ∈ std30)
    {c : List ℤ} (hc : c.length = 5) :
    rootReflection (tcChainVec (intv a b) δ) • tcChainVec c δ =
      tcChainVec (reflectStd (intv a b) c) δ := by
  have hroot : IsRoot .E6 (tcChainVec (intv a b) δ) :=
    isRoot_of_mem_chainSet hδ
      (show tcChainVec (intv a b) δ ∈ tcChainSet δ from ⟨intv a b, hab, rfl⟩)
  have hL : (intv a b).length = 5 := by simp [intv]
  have hsq : iform (tcChainVec (intv a b) δ) (tcChainVec (intv a b) δ) = 2 :=
    e6_iform_self _ (mem_rootFinset.2 hroot)
  have hcor : corootPair (tcChainVec (intv a b) δ) (tcChainVec c δ) = ip5 (intv a b) c := by
    have h1 := corootPair_mul hroot (tcChainVec c δ)
    rw [hsq] at h1
    have h2 := iform_chainVec hδ.gram hL hc
    omega
  have hr : tcChainVec (reflectStd (intv a b) c) δ =
      tcChainVec c δ - ip5 (intv a b) c • tcChainVec (intv a b) δ := by
    unfold reflectStd
    exact chainVec_sub_smul δ _ hc hL
  rw [rootReflection_smul hroot, hcor, hr]

theorem wordProd_chainVec
    {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)} (hδ : A5Chain δ) (w : List (ℕ × ℕ))
    (hw : ∀ ab ∈ w, intv ab.1 ab.2 ∈ std30) {c : List ℤ} (hc : c.length = 5) :
    (w.map fun ab => rootReflection (tcChainVec (intv ab.1 ab.2) δ)).prod • tcChainVec c δ =
      tcChainVec (applyWordStd w c) δ := by
  induction w with
  | nil => simp [applyWordStd]
  | cons ab w ih =>
    have hab : intv ab.1 ab.2 ∈ std30 := hw ab (by simp)
    have hw' : ∀ x ∈ w, intv x.1 x.2 ∈ std30 := fun x hx => hw x (by simp [hx])
    have h1 := ih hw'
    have h2 := rootReflection_chainVec hδ hab (length_applyWordStd_five hc w)
    simp only [List.map_cons, List.prod_cons, mul_smul]
    rw [h1, h2]
    rfl

theorem twistInner_chainSet
    {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)} (hδ : A5Chain δ)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hρform : ∀ γ γ', iform (ρ γ) (ρ γ') = iform γ γ')
    (hρw : ∃ w : WeylGroup .E6, ∀ γ, IsRoot .E6 γ → ρ γ = w • γ)
    (hs : A5Swap (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) δ) :
    twistInner (tcChainSet δ) (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) := by
  unfold twistInner
  obtain ⟨w₀, hw₀⟩ := hρw
  obtain ⟨e0, he0, hρ0⟩ := hs.s0
  obtain ⟨e1, he1, hρ1⟩ := hs.s1
  obtain ⟨e2, he2, hρ2⟩ := hs.s2
  obtain ⟨e3, he3, hρ3⟩ := hs.s3
  obtain ⟨e4, he4, hρ4⟩ := hs.s4
  have L2 : ∀ c ∈ stdX2, c.length = 5 := by decide +kernel
  have LF : ∀ c ∈ stdFneg, c.length = 5 := by decide +kernel
  have L1 : ∀ c ∈ stdX1, c.length = 5 := by decide +kernel
  have hBW : ∀ w ∈ blockSwapWords, ∀ ab ∈ w, intv ab.1 ab.2 ∈ std30 := by decide +kernel
  have g01 : ip5 e0 e1 = -1 :=
    (ip5_eq_of_image hδ hρform (L2 e0 he0) (L2 e1 he1) hρ0 hρ1).trans (by decide)
  have g12 : ip5 e1 e2 = -1 :=
    (ip5_eq_of_image hδ hρform (L2 e1 he1) (LF e2 he2) hρ1 hρ2).trans (by decide)
  have g02 : ip5 e0 e2 = 0 :=
    (ip5_eq_of_image hδ hρform (L2 e0 he0) (LF e2 he2) hρ0 hρ2).trans (by decide)
  have g23 : ip5 e2 e3 = -1 :=
    (ip5_eq_of_image hδ hρform (LF e2 he2) (L1 e3 he3) hρ2 hρ3).trans (by decide)
  have g13 : ip5 e1 e3 = 0 :=
    (ip5_eq_of_image hδ hρform (L2 e1 he1) (L1 e3 he3) hρ1 hρ3).trans (by decide)
  have g03 : ip5 e0 e3 = 0 :=
    (ip5_eq_of_image hδ hρform (L2 e0 he0) (L1 e3 he3) hρ0 hρ3).trans (by decide)
  have g34 : ip5 e3 e4 = -1 :=
    (ip5_eq_of_image hδ hρform (L1 e3 he3) (L1 e4 he4) hρ3 hρ4).trans (by decide)
  have g24 : ip5 e2 e4 = 0 :=
    (ip5_eq_of_image hδ hρform (LF e2 he2) (L1 e4 he4) hρ2 hρ4).trans (by decide)
  have g14 : ip5 e1 e4 = 0 :=
    (ip5_eq_of_image hδ hρform (L2 e1 he1) (L1 e4 he4) hρ1 hρ4).trans (by decide)
  have g04 : ip5 e0 e4 = 0 :=
    (ip5_eq_of_image hδ hρform (L2 e0 he0) (L1 e4 he4) hρ0 hρ4).trans (by decide)
  obtain ⟨w, hwmem, h0, h1, h2, h3, h4⟩ :=
    std_swap_words e0 he0 e1 he1 g01 e2 he2 g12 g02 e3 he3 g23 g13 g03 e4 he4 g34 g24 g14 g04
  have hw : ∀ ab ∈ w, intv ab.1 ab.2 ∈ std30 := hBW w hwmem
  obtain ⟨W, hWdef⟩ : ∃ W : WeylGroup Tag.E6,
      W = (w.map fun ab => rootReflection (tcChainVec (intv ab.1 ab.2) δ)).prod := ⟨_, rfl⟩
  have hWp : ∀ c : List ℤ, c.length = 5 → W • tcChainVec c δ = tcChainVec (applyWordStd w c) δ := by
    intro c hc
    rw [hWdef]
    exact wordProd_chainVec hδ w hw hc
  have hWmem : W ∈ Subgroup.closure
      {s : WeylGroup Tag.E6 | ∃ γ ∈ tcChainSet δ, s = rootReflection γ} := by
    rw [hWdef]
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨ab, hab, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.subset_closure
      ⟨tcChainVec (intv ab.1 ab.2) δ, (show tcChainVec (intv ab.1 ab.2) δ ∈ tcChainSet δ from
        ⟨intv ab.1 ab.2, hw ab hab, rfl⟩), rfl⟩
  have hI0 : tcChainVec (intv 0 1) δ = δ 0 := by
    rw [show intv 0 1 = [1, 0, 0, 0, 0] by decide, chainVec_five']
    simp
  have hI1 : tcChainVec (intv 1 2) δ = δ 1 := by
    rw [show intv 1 2 = [0, 1, 0, 0, 0] by decide, chainVec_five']
    simp
  have hI2 : tcChainVec (intv 2 3) δ = δ 2 := by
    rw [show intv 2 3 = [0, 0, 1, 0, 0] by decide, chainVec_five']
    simp
  have hI3 : tcChainVec (intv 3 4) δ = δ 3 := by
    rw [show intv 3 4 = [0, 0, 0, 1, 0] by decide, chainVec_five']
    simp
  have hI4 : tcChainVec (intv 4 5) δ = δ 4 := by
    rw [show intv 4 5 = [0, 0, 0, 0, 1] by decide, chainVec_five']
    simp
  have k0 : (⇑ρ) (δ 0) = W • δ 0 := by
    rw [hρ0, ← h0, ← hWp (intv 0 1) (by decide), hI0]
  have k1 : (⇑ρ) (δ 1) = W • δ 1 := by
    rw [hρ1, ← h1, ← hWp (intv 1 2) (by decide), hI1]
  have k2 : (⇑ρ) (δ 2) = W • δ 2 := by
    rw [hρ2, ← h2, ← hWp (intv 2 3) (by decide), hI2]
  have k3 : (⇑ρ) (δ 3) = W • δ 3 := by
    rw [hρ3, ← h3, ← hWp (intv 3 4) (by decide), hI3]
  have k4 : (⇑ρ) (δ 4) = W • δ 4 := by
    rw [hρ4, ← h4, ← hWp (intv 4 5) (by decide), hI4]
  have hk : ∀ k : Fin 5, (⇑ρ) (δ k) = W • δ k := by
    intro k
    fin_cases k
    exacts [k0, k1, k2, k3, k4]
  refine ⟨W, hWmem, ?_⟩
  intro γ hγ
  obtain ⟨c, hc, rfl⟩ := hγ
  have hroot : IsRoot .E6 (tcChainVec c δ) :=
    isRoot_of_mem_chainSet hδ (show tcChainVec c δ ∈ tcChainSet δ from ⟨c, hc, rfl⟩)
  rw [hw₀ _ hroot, smul_chainVec_eq_sum, smul_chainVec_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hw₀ _ (hδ.root k), hk k]

end CFSG.StandardType.TableCRes

end
