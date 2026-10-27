module

public import CFSG.Quasithin.EmptyFaithful.S151CLG2F4Gen
public import CFSG.Quasithin.EmptyFaithful.S151CLG2Step
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2c
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine

public section

namespace CFSG.Quasithin.CLG2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.L239
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Blueprint

set_option linter.unusedSectionVars false

structure RankTwoParG (Y : Type) [Group Y] (U : Subgroup Y) (P : Fin 2 → Subgroup Y) : Prop where
  res : ResidualOvergroupsAt Y U P
  levi : ∀ j, Rk2.Rank2Levi (P j) ∨ ∃ f, LeviDataSz f (P j)
  inv : ∀ α : MulAut Y, U.map α.toMonoidHom = U → ∀ j, (P j).map α.toMonoidHom = P j
  good : ∀ j, GoodLocal (P j)

theorem exists_hom_perfectCore_map {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y']
    {P : Subgroup Y} (e : Y ≃* Y') {T : Type} [Group T]
    (h : ∃ g : ↥(perfectCore P) →* T, Function.Surjective g ∧ IsPGroup 2 g.ker) :
    ∃ g : ↥(perfectCore (P.map e.toMonoidHom)) →* T,
      Function.Surjective g ∧ IsPGroup 2 g.ker := by
  obtain ⟨g, hg, hker⟩ := h
  let eP : ↥(perfectCore (P.map e.toMonoidHom)) ≃* ↥(perfectCore P) :=
    (MulEquiv.subgroupCongr (map_perfectCore e.toMonoidHom P).symm).trans
      (Subgroup.equivMapOfInjective (perfectCore P) e.toMonoidHom e.injective).symm
  refine ⟨g.comp eP.toMonoidHom, hg.comp eP.surjective, ?_⟩
  intro x
  have hx : (eP x.1 : ↥(perfectCore P)) ∈ g.ker := x.2
  obtain ⟨k, hk⟩ := hker ⟨eP x.1, hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (eP x.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h2 : eP (x.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
  exact eP.injective (h2.trans (map_one eP).symm)

theorem LeviDataSz.map {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y'] {P : Subgroup Y}
    {f : ℕ} (h : LeviDataSz f P) (e : Y ≃* Y') : LeviDataSz f (P.map e.toMonoidHom) := by
  obtain ⟨a, K, hF, hFin, ha, hfa, hK, hg⟩ := h
  exact ⟨a, K, hF, hFin, ha, hfa, hK, exists_hom_perfectCore_map e hg⟩

theorem RankTwoParG.map {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y']
    {U : Subgroup Y} {P : Fin 2 → Subgroup Y} (h : RankTwoParG Y U P) (e : Y ≃* Y') :
    RankTwoParG Y' (U.map e.toMonoidHom) (fun j => (P j).map e.toMonoidHom) where
  res := h.res.map e
  levi j := by
    rcases h.levi j with hL | ⟨f, hS⟩
    · exact Or.inl (hL.map e)
    · exact Or.inr ⟨f, LeviDataSz.map (hS : LeviDataSz f (P j)) e⟩
  inv := by
    intro α' hα' j
    set α : MulAut Y := e.trans (α'.trans e.symm) with hα
    have hαU : U.map α.toMonoidHom = U := by
      have h1 := hα'
      rw [map_comm_equiv] at h1
      exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h1
    have h2 := h.inv α hαU j
    rw [map_comm_equiv, ← hα, h2]
  good j := (h.good j).map e

theorem RankTwoParG.exists_of_equiv {Y C : Type} [Group Y] [Group C] [Finite Y] [Finite C]
    (e : Y ≃* C) {U₀ : Subgroup C} {P₀ : Fin 2 → Subgroup C} (h : RankTwoParG C U₀ P₀)
    (hU₀ : IsSylowTwoOf U₀ ⊤) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup Y, RankTwoParG Y U P := by
  have h1 := h.map e.symm
  have hU₁ := CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_map_top e.symm hU₀
  obtain ⟨k, -, hk⟩ :=
    (isSylowTwoOf_iff_isSylowOf.1 hU₁).exists_mem_conj (isSylowTwoOf_iff_isSylowOf.1 hU)
  have hconj : (U₀.map e.symm.toMonoidHom).map (MulAut.conj k).toMonoidHom = U := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  refine ⟨fun j => ((P₀ j).map e.symm.toMonoidHom).map (MulAut.conj k).toMonoidHom, ?_⟩
  have := h1.map (MulAut.conj k)
  rwa [hconj] at this

section Generation


theorem not_isSolvable_perfectCore_of_levi {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y}
    (h : Rk2.Rank2Levi P ∨ ∃ f, LeviDataSz f P) : ¬ Group.IsSolvable ↥(perfectCore P) := by
  intro hs
  rcases h with ⟨K, hF, hFin, hCh, n, hK, hn, g, hg, -⟩ | ⟨f, a, K, hF, hFin, ha, hfa, hK, g, hg, -⟩
  · have hK4 : ∃ s : Finset K, s.card = 4 := by
      refine exists_finset_card_four ?_
      rw [hK]
      exact four_le_pow_two hn
    exact SzN2.not_isSolvable_sl2 hK4 (Group.isSolvable_of_surjective hg)
  · have hSz : IsSz (2 * a + 1) (suzukiGroup a K) :=
      ⟨rfl, a, ha, K, hF, hFin, rfl, hfa ▸ hK, ⟨MulEquiv.refl _⟩⟩
    have hq : CFSG.IsQuasisimple (suzukiGroup a K) :=
      isQuasisimple_of_psl2_or_sz (n := 2 * a + 1) (by omega) (Or.inr hSz)
    have hsimple : IsSimpleGroup (suzukiGroup a K) := isSimpleGroup_of_psl2_or_sz (Or.inr hSz)
    have : Group.IsPerfect (suzukiGroup a K) := hq.1
    have : Group.IsSolvable (suzukiGroup a K) := Group.isSolvable_of_surjective hg
    have hsub : Subsingleton (suzukiGroup a K) :=
      CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
        (G := suzukiGroup a K)
    have := hsimple.toNontrivial
    exact not_subsingleton _ hsub

theorem sup_perfectCore_eq_top_of_res {Y : Type} [Group Y] [Finite Y] {U : Subgroup Y}
    {P : Fin 2 → Subgroup Y} (hres : ResidualOvergroupsAt Y U P)
    (hns : ∀ j, ¬ Group.IsSolvable ↥(perfectCore (P j))) :
    perfectCore (P 0) ⊔ perfectCore (P 1) ⊔ U = ⊤ := by
  have hle : ∀ j, U ≤ P j := hres.2.1
  have hne : ∀ j, P j ≠ ⊤ := fun j =>
    ((hres.2.2.1 (P j) (hle j)).2 ⟨j, rfl⟩).lt.ne
  have hnsle : ∀ j (A : Subgroup Y), perfectCore (P j) ≤ A → ¬ Group.IsSolvable ↥A := by
    intro j A hA hsolv
    exact hns j (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hA)
      (Subgroup.inclusion_injective hA))
  by_contra hne'
  set A := perfectCore (P 0) ⊔ perfectCore (P 1) ⊔ U with hA
  have hUA : U ≤ A := le_sup_right
  obtain ⟨j, hjk, -⟩ := hres.2.2.2.2.1 A hUA hne' (hnsle 0 A (le_sup_left.trans le_sup_left))
  have hAj : A ≤ P j := (hjk j).2 rfl
  set k : Fin 2 := j + 1 with hk
  have hkj : k ≠ j := by fin_cases j <;> decide
  have hPk : perfectCore (P k) ≤ A := by
    fin_cases j
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_left.trans le_sup_left
  set M := perfectCore (P k) ⊔ U with hM
  have hMk : M ≤ P k := sup_le (perfectCore_le _) (hle k)
  have hMA : M ≤ A := sup_le hPk hUA
  obtain ⟨l, hl, -⟩ := hres.2.2.2.2.1 M le_sup_right
    (fun hT => hne k (top_le_iff.1 (hT ▸ hMk))) (hnsle k M le_sup_left)
  have h1 : k = l := (hl k).1 hMk
  have h2 : j = l := (hl j).1 (hMA.trans hAj)
  exact hkj (h1.trans h2.symm)

end Generation

section Main

variable {G : Type} [Group G] [Finite G]


theorem le_mZ_of_isSz (hB42 : Input15120B42List) {T Mc M Z₁ Z₂ V₁ V₂ L K : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hK : K ∈ lFamilyOf (g1_1516 Z₁) (s1516 T Z₁))
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKchar : CharTwo K) {f : ℕ}
    (hf : Odd f) (hf3 : 3 ≤ f) (hKsz : IsSz f (↥K ⧸ CFSG.pCore 2 ↥K)) :
    K ≤ mZ1516 Mc Z₁ := by
  by_contra hKM
  have hcK : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ K := ⟨hc.ctx, hc.h17, hc.h18, hc.h19, ⟨hK, hKq, hKM⟩⟩
  exact not_list15120_of_isSz hf hf3 hKsz (hB42 G T Mc M Z₁ Z₂ V₁ V₂ K hcK hKchar)

theorem false_of_rankTwoParG (h118 : TheoremC118) (h126 : TheoremC126) (h42 : AsB42)
    (hLJ : Input15120LJ) (hB42 : Input15120B42List) (h1416 : StageLemma1416)
    (h15 : StageLemma1515CE) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G))
    {P : Fin 2 → Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)}
    (hP : RankTwoParG (↥L ⧸ CFSG.pCore 2 ↥L)
      (((s1516 T Z₁ ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) P) :
    False := by
  have hsyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
  have hSM : s1516 T Z₁ ≤ mZ1516 Mc Z₁ := s1516_le_mZ1516 hc.h18
  have hle : ∀ j, perfectCore (liftQ L (P j)) ≤ mZ1516 Mc Z₁ := by
    intro j
    obtain ⟨hchar2, hnochi⟩ := goodLocal_liftQ (hP.good j)
    have hSX : s1516 T Z₁ ≤ Subgroup.normalizer (liftQ L (P j) : Set G) :=
      normalizes_liftQ hSN (fun α hα => hP.inv α hα j)
    have hSK : s1516 T Z₁ ≤ Subgroup.normalizer (perfectCore (liftQ L (P j)) : Set G) :=
      hSX.trans (normalizer_le_normalizer_perfectCore _)
    have hKL : perfectCore (liftQ L (P j)) ≤ L := (perfectCore_le _).trans (liftQ_le L _)
    have hKchar : CharTwo (perfectCore (liftQ L (P j))) :=
      CharTwo.of_normal hchar2 (perfectCore_le _) (perfectCore_normal _)
    rcases hP.levi j with hL2 | ⟨f, hSz⟩
    · obtain ⟨m, hm, hKm, hKq⟩ := perfectCore_liftQ_levi (L := L) hL2
      have hmem := mem_lFamilyOf_of_normalized hc hKL (perfectCore_perfect _) hKq hSK
      exact le_mZ_of_not_chi0 h118 h126 h42 hLJ h1416 h15 hc hmem hKq hKchar ⟨m, hm, hKm⟩ hSK
        (perfectCore_le _) (perfectCore_normal _) hnochi
    · obtain ⟨a, K, hF, hFin, ha, hfa, hK, g, hg, hker⟩ := hSz
      obtain ⟨ρ, hρs, hρk⟩ := exists_hom_perfectCore (L := L) (P j)
      have hk : IsPGroup 2 (g.comp ρ).ker := by
        rw [← MonoidHom.comap_ker]
        exact hker.comap_of_ker_isPGroup ρ hρk
      have hK' : Nat.card K = 2 ^ (2 * a + 1) := hfa ▸ hK
      obtain ⟨hKsz, hKq⟩ := sz_quotient ha hK' (g.comp ρ) (hg.comp hρs) hk
      have hmem := mem_lFamilyOf_of_normalized hc hKL (perfectCore_perfect _) hKq hSK
      exact le_mZ_of_isSz hB42 hc hmem hKq hKchar (f := 2 * a + 1) ⟨a, rfl⟩ (by omega) hKsz
  have hgen := le_sup_perfectCore_liftQ (L := L) (R := s1516 T Z₁) (A₀ := P 0) (A₁ := P 1)
    (sup_perfectCore_eq_top_of_res hP.res (fun j => not_isSolvable_perfectCore_of_levi (hP.levi j)))
    ((pCoreOf_le_of_isSylowTwoOf hsyl).trans inf_le_left)
  exact hc.hL.not_le (hgen.trans (sup_le (sup_le (hle 0) (hle 1)) (inf_le_left.trans hSM)))

end Main

end CFSG.Quasithin.CLG2
