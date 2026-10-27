module

public import CFSG.Quasithin.EmptyFaithful.S151CLG2F4Pkg
public import CFSG.Quasithin.Background.RonanF918Four
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddEven

public section

namespace CFSG.Quasithin.CLG2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.LieType.Ree.LargeReeInvolution
open CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

@[expose] def LeviDataSL (n : ℕ) {S : Type} [Group S] (P : Subgroup S) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
    ∃ g : ↥(perfectCore P) →* Matrix.SpecialLinearGroup (Fin 2) K,
      Function.Surjective g ∧ IsPGroup 2 g.ker

theorem LeviDataSL.map {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y'] {P : Subgroup Y}
    {n : ℕ} (h : LeviDataSL n P) (e : Y ≃* Y') : LeviDataSL n (P.map e.toMonoidHom) := by
  obtain ⟨K, hF, hFin, hCh, hK, g, hg, hker⟩ := h
  exact ⟨K, hF, hFin, hCh, hK, exists_hom_perfectCore_map e ⟨g, hg, hker⟩⟩

@[expose] def f4OrbitIndex (j : Fin 2) : Fin F4.fixedOrbitCount :=
  if j = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩

theorem f4OrbitIndex_zero : f4OrbitIndex 0 = ⟨0, by decide⟩ := by
  simp [f4OrbitIndex]

theorem f4OrbitIndex_one : f4OrbitIndex 1 = ⟨1, by decide⟩ := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp [f4OrbitIndex, h10]

theorem _root_.CFSG.QuasithinUnique.Setup.X6.ResidualOvergroupsAt.swap {Y : Type} [Group Y]
    {U : Subgroup Y} {P : Fin 2 → Subgroup Y} (h : ResidualOvergroupsAt Y U P) :
    ResidualOvergroupsAt Y U (fun j => P (Equiv.swap (0 : Fin 2) 1 j)) := by
  obtain ⟨hne, hUP, hmax, hsolv, hC2, hC3⟩ := h
  set P' : Fin 2 → Subgroup Y := fun j => P (Equiv.swap (0 : Fin 2) 1 j) with hP'
  have hP'P : ∀ j : Fin 2, P' j = P (Equiv.swap (0 : Fin 2) 1 j) := fun j => by rw [hP']
  have hPP' : ∀ j : Fin 2, P' (Equiv.swap (0 : Fin 2) 1 j) = P j := by
    intro j
    rw [hP'P]
    rw [Equiv.swap_apply_self]
  have hP'0 : P' 0 = P 1 := by simp [hP', Equiv.swap_apply_left]
  have hP'1 : P' 1 = P 0 := by simp [hP', Equiv.swap_apply_right]
  refine ⟨?_, fun j => hUP _, ?_, ?_, ?_, fun α hodd hα M hUM hMt hMns =>
    hC3 α hodd hα M hUM hMt hMns⟩
  · rw [hP'0, hP'1]
    exact hne.symm
  · intro M hUM
    have hiff : (∃ j, M = P' j) ↔ ∃ j, M = P j := by
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨Equiv.swap 0 1 j, by rw [← hP'P j]; exact hj⟩
      · rintro ⟨j, hj⟩
        exact ⟨Equiv.swap 0 1 j, by rw [hPP' j]; exact hj⟩
    rw [hiff]
    exact hmax M hUM
  · rw [hP'0, hP'1, inf_comm]
    exact hsolv
  · intro M hUM hMt hMns
    obtain ⟨j, hj, hd⟩ := hC2 M hUM hMt hMns
    refine ⟨Equiv.swap 0 1 j, ?_, ?_⟩
    · intro k
      rw [show M ≤ P' k ↔ M ≤ P (Equiv.swap (0 : Fin 2) 1 k) from by rw [hP'P]]
      rw [hj (Equiv.swap 0 1 k)]
      constructor
      · intro hk
        rw [← Equiv.swap_apply_self (0 : Fin 2) 1 k, hk]
      · intro hk
        rw [hk, Equiv.swap_apply_self]
    · rw [hPP' j, hd]

theorem RankTwoParG.swap {Y : Type} [Group Y] {U : Subgroup Y}
    {P : Fin 2 → Subgroup Y} (h : RankTwoParG Y U P) :
    RankTwoParG Y U (fun j => P (Equiv.swap (0 : Fin 2) 1 j)) where
  res := ResidualOvergroupsAt.swap h.res
  levi j := h.levi (Equiv.swap (0 : Fin 2) 1 j)
  inv α hα j := h.inv α hα (Equiv.swap (0 : Fin 2) 1 j)
  good j := h.good (Equiv.swap (0 : Fin 2) 1 j)

theorem LeviDataSz.lieModel_quotient {S : Type} [Group S] [Finite S]
    {P : Subgroup S} {f : ℕ} (h : LeviDataSz f P) :
    LieModel (ModO2 (perfectCore P)) .twistedB2 0 2 f ∧
      Odd (Nat.card (Outer (ModO2 (perfectCore P)))) := by
  obtain ⟨a, K, hF, hFin, ha, hfa, hK, g, hg, hker⟩ := h
  subst hfa
  have hsz := sz_quotient (K := K) ha hK g hg hker
  have hLie : LieModel (ModO2 (perfectCore P)) .twistedB2 0 2 (2 * a + 1) :=
    CFSG.Quasithin.RonanF918.lieModel_of_isSz hsz.1
  exact ⟨hLie, CFSG.LocalAnalysis.EvenBN.GMSK.odd_card_outer_of_lieModel_twistedB2 hLie⟩

theorem LeviDataSL.lieModel_quotient {S : Type} [Group S] [Finite S] {P : Subgroup S} {n : ℕ}
    (h : LeviDataSL n P) (h2 : 2 ≤ n) (hn : Odd n) :
    LieModel (ModO2 (perfectCore P)) .PSL 2 2 n ∧
      Odd (Nat.card (Outer (ModO2 (perfectCore P)))) := by
  obtain ⟨K, hF, hFin, hCh, hK, g, hg, hker⟩ := h
  have hmodel := (sl2_quotient hK h2 g hg hker).1
  exact ⟨CFSG.Quasithin.RonanF918.lieModel_of_isPSL hmodel,
    CFSG.Quasithin.H13.NQCore.odd_outer_of_psl2_two hn hmodel⟩

theorem rankTwoParG_model_f4_labelled
    {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ P : Fin 2 → Subgroup ↥(F4.reeGamma K a),
      RankTwoParG ↥(F4.reeGamma K a)
        ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) P ∧
      LeviDataSL (2 * a + 1) (P 0) ∧ LeviDataSz (2 * a + 1) (P 1) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hchar : CharP K 2 := inferInstanceAs (CharP K F4.prime)
  have hU₀ : IsSylowTwoOf
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) ⊤ :=
    (CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.largeRee_named_covers a K hK).1
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a :=
    reeFixedPosUnipotent_le_reeGamma
  have hUp : IsPGroup 2 ↥(F4.reeFixedPosUnipotent K a) :=
    (hU₀.2.1).of_equiv (Subgroup.subgroupOfEquivOfLe hUC)
  obtain ⟨⟨h0eq, -, -⟩, ⟨h1eq, -, -⟩⟩ :=
    large_Ree_opposite_simple_blocks_generate_rank_one_model (K := K) (a := a) ha hK
  have key : ∀ k : Fin 2, k = 0 ∨ k = 1 := by
    intro k
    have hk : k.val < 2 := k.isLt
    rcases (by omega : k.val = 0 ∨ k.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hval : ∀ k : Fin F4.fixedOrbitCount, k = ⟨0, by decide⟩ ∨ k = ⟨1, by decide⟩ := by
    intro k
    have hk : k.val < 2 := k.isLt
    rcases (by omega : k.val = 0 ∨ k.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hinj : Function.Injective f4Index :=
    (Finite.injective_iff_surjective (f := f4Index)).mpr f4Index_surjective
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hfun : (∀ j : Fin 2, f4Index j = f4OrbitIndex j) ∨
      (∀ j : Fin 2, f4Index j = f4OrbitIndex (Equiv.swap (0 : Fin 2) 1 j)) := by
    rcases hval (f4Index (0 : Fin 2)) with h0 | h0
    · left
      have h1 : f4Index (1 : Fin 2) = ⟨1, by decide⟩ := by
        rcases hval (f4Index 1) with h | h
        · exfalso
          have heq : f4Index (0 : Fin 2) = f4Index 1 := by rw [h0, h]
          exact absurd (hinj heq) (by decide)
        · exact h
      intro j
      rcases key j with rfl | rfl
      · rw [h0, f4OrbitIndex_zero]
      · rw [h1, f4OrbitIndex_one]
    · right
      have h1 : f4Index (1 : Fin 2) = ⟨0, by decide⟩ := by
        rcases hval (f4Index 1) with h | h
        · exact h
        · exfalso
          have heq : f4Index (0 : Fin 2) = f4Index 1 := by rw [h0, h]
          exact absurd (hinj heq) (by decide)
      intro j
      rcases key j with rfl | rfl
      · rw [h0]
        simp [f4OrbitIndex, h10, Equiv.swap_apply_left]
      · rw [h1]
        simp [f4OrbitIndex, h10, Equiv.swap_apply_right]
  set Q : Fin 2 → Subgroup ↥(F4.reeGamma K a) := fun j =>
    (F4.reeParabolic K a {f4Index j}).subgroupOf (F4.reeGamma K a) with hQdef
  set P : Fin 2 → Subgroup ↥(F4.reeGamma K a) := fun j =>
    (F4.reeParabolic K a {f4OrbitIndex j}).subgroupOf (F4.reeGamma K a) with hPdef
  have hQ : RankTwoParG ↥(F4.reeGamma K a)
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) Q :=
    rankTwoParG_model_f4 (K := K) ha hK
  have hP : RankTwoParG ↥(F4.reeGamma K a)
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) P := by
    rcases hfun with h | h
    · have hQP : Q = P := by
        funext j
        show (F4.reeParabolic K a {f4Index j}).subgroupOf (F4.reeGamma K a) =
          (F4.reeParabolic K a {f4OrbitIndex j}).subgroupOf (F4.reeGamma K a)
        rw [h j]
      rwa [hQP] at hQ
    · have hQP : Q = fun j => P (Equiv.swap (0 : Fin 2) 1 j) := by
        funext j
        show (F4.reeParabolic K a {f4Index j}).subgroupOf (F4.reeGamma K a) =
          (F4.reeParabolic K a {f4OrbitIndex (Equiv.swap (0 : Fin 2) 1 j)}).subgroupOf
            (F4.reeGamma K a)
        rw [h j]
      have hsw := RankTwoParG.swap hQ
      rw [hQP] at hsw
      have hfin : (fun j => (fun i => P (Equiv.swap (0 : Fin 2) 1 i))
          (Equiv.swap (0 : Fin 2) 1 j)) = P := by
        funext j
        show P (Equiv.swap (0 : Fin 2) 1 (Equiv.swap (0 : Fin 2) 1 j)) = P j
        rw [Equiv.swap_apply_self]
      rwa [hfin] at hsw
  have hL0 : LeviDataSL (2 * a + 1) (P 0) := by
    have hj : f4OrbitIndex (0 : Fin 2) = ⟨0, by decide⟩ := f4OrbitIndex_zero
    haveI : IsSimpleGroup ↥(rankOneGroupOne K a) := (isSimpleGroup_rankOneGroupOne ha hK).1
    obtain ⟨g, hg, hker⟩ := ree_levi_hom (K := K) (a := a) hUp (f4OrbitIndex 0)
      (M := rankOneGroupOne K a) (by rw [hj]; exact h0eq)
      (isSimpleGroup_rankOneGroupOne ha hK).2
    refine ⟨K, inferInstance, inferInstance, inferInstance, hK, ?_⟩
    refine ⟨(rankOneEquivSL K a hK).symm.toMonoidHom.comp g,
      (rankOneEquivSL K a hK).symm.surjective.comp hg, ?_⟩
    have hker' : ((rankOneEquivSL K a hK).symm.toMonoidHom.comp g).ker = g.ker := by
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
      exact MulEquiv.map_eq_one_iff _
    rw [hker']
    exact hker
  have hL1 : LeviDataSz (2 * a + 1) (P 1) := by
    have hj : f4OrbitIndex (1 : Fin 2) = ⟨1, by decide⟩ := f4OrbitIndex_one
    haveI : IsSimpleGroup ↥(rankOneGroupTwo K a) := (isSimpleGroup_rankOneGroupTwo ha hK).1
    obtain ⟨g, hg, hker⟩ := ree_levi_hom (K := K) (a := a) hUp (f4OrbitIndex 1)
      (M := rankOneGroupTwo K a) (by rw [hj]; exact h1eq)
      (isSimpleGroup_rankOneGroupTwo ha hK).2
    refine ⟨a, K, inferInstance, inferInstance, ha, rfl, hK, ?_⟩
    refine ⟨(rankOneEquivSuzuki K a ha hK).toMonoidHom.comp g,
      (rankOneEquivSuzuki K a ha hK).surjective.comp hg, ?_⟩
    have hker' : ((rankOneEquivSuzuki K a ha hK).toMonoidHom.comp g).ker = g.ker := by
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
      exact MulEquiv.map_eq_one_iff _
    rw [hker']
    exact hker
  exact ⟨P, hP, hL0, hL1⟩

theorem rankTwoParG_f4_labelled
    {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hY : Is2F4 f Y)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup Y, RankTwoParG Y U P ∧ LeviDataSL f (P 0) ∧ LeviDataSz f (P 1) := by
  classical
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hY
  subst hfa
  obtain ⟨P₀, hP₀, hSL, hSz⟩ := rankTwoParG_model_f4_labelled (K := K) ha hK
  haveI : Finite (ModGL F4.tag K) := finite_modGL
  have hU₀ : IsSylowTwoOf
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) ⊤ :=
    (CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.largeRee_named_covers a K hK).1
  have h1 : RankTwoParG Y
      (((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)).map e.symm.toMonoidHom)
      (fun j => (P₀ j).map e.symm.toMonoidHom) := hP₀.map e.symm
  have hSL₁ : LeviDataSL (2 * a + 1) ((P₀ 0).map e.symm.toMonoidHom) :=
    LeviDataSL.map hSL e.symm
  have hSz₁ : LeviDataSz (2 * a + 1) ((P₀ 1).map e.symm.toMonoidHom) :=
    LeviDataSz.map hSz e.symm
  have hU₁ := CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_map_top e.symm hU₀
  obtain ⟨k, -, hk⟩ :=
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU₁).exists_mem_conj
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU)
  have hconj : (((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)).map
        e.symm.toMonoidHom).map (MulAut.conj k).toMonoidHom = U := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  refine ⟨fun j => ((P₀ j).map e.symm.toMonoidHom).map (MulAut.conj k).toMonoidHom, ?_, ?_, ?_⟩
  · have h2 := h1.map (MulAut.conj k)
    rwa [hconj] at h2
  · exact LeviDataSL.map hSL₁ (MulAut.conj k)
  · exact LeviDataSz.map hSz₁ (MulAut.conj k)

end CFSG.Quasithin.CLG2

end
