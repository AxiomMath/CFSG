module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenDiagR42
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourWeak
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexNormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem dichotomy_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) :
    (UC22.conjClosure D.M L = L ⊔ K ∧ ∃ x ∈ D.M, K = conjSubgroup L x) ∨
      (UC22.conjClosure D.M L = L ∧ (L.subgroupOf D.M).Normal ∧ (K.subgroupOf D.M).Normal) := by
  have hperm := permutesPair_of_ctx19_one h
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  by_cases hex : ∃ m ∈ D.M, L.map (MulAut.conj m).toMonoidHom = K
  · left
    obtain ⟨m, hm, hmK⟩ := hex
    refine ⟨le_antisymm ?_ (sup_le (TwelveTwentyThree.le_conjClosure D.M L) ?_),
      m⁻¹, D.M.inv_mem hm, ?_⟩
    · refine iSup₂_le fun J hJ => ?_
      obtain ⟨g, hg, rfl⟩ := hJ
      rcases hperm g hg with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]; exact le_sup_left
      · rw [h1]; exact le_sup_right
    · rw [← hmK]
      exact le_iSup₂ (f := fun J (_ : J ∈ UC22.conjSetOf D.M L) => J) _ ⟨m, hm, rfl⟩
    · rw [← hmK]
      show L.map (MulAut.conj m).toMonoidHom = L.map (MulAut.conj m⁻¹⁻¹).toMonoidHom
      rw [inv_inv]
  · right
    push Not at hex
    have hfix : ∀ m ∈ D.M, L.map (MulAut.conj m).toMonoidHom = L ∧
        K.map (MulAut.conj m).toMonoidHom = K := fun m hm =>
      (hperm m hm).resolve_right (fun h' => hex m hm h'.1)
    have hLn : (L.subgroupOf D.M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 fun m hm =>
        Subgroup.mem_normalizer_iff_map_conj_eq.2 (hfix m hm).1
    have hKn : (K.subgroupOf D.M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 fun m hm =>
        Subgroup.mem_normalizer_iff_map_conj_eq.2 (hfix m hm).2
    exact ⟨uc22p2214_conjClosure_eq_of_normal hLM hLn, hLn, hKn⟩

theorem inFSq_19_cases
    {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (hKc : Inputs1719.K_L2SzAutRank)
    (hU3 : Inputs1719.K_U3IndexNormal) (h43c : W3Lem45_2Chief) :
    ((L.subgroupOf D.M).Normal ∧ (K.subgroupOf D.M).Normal ∧ InFSq 2 (L ⊔ D.T) ∧
        InFSq 2 (K ⊔ D.T)) ∨ InFSq 2 (L ⊔ K ⊔ D.T) := by
  have hLc : L ∈ calC D.M := h.hyp.hL.1
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hLc.1
  rcases dichotomy_19 h with ⟨hXeq, x, hxM, hKx⟩ | ⟨-, hLn, hKn⟩
  · right
    have hL2 : IsL2 (Bar2 L) 2 := by
      rcases h.shape with hL2 | hU3'
      · exact hL2
      · exfalso
        have hcardK : Nat.card (Bar2 K) = Nat.card (Bar2 L) := by
          obtain ⟨e⟩ := UC22.uc22p20d_bar2_conj x⁻¹ L
          subst hKx
          exact (Nat.card_congr e.toEquiv).symm
        have h1 := card_bar2_of_isU3_two hU3'
        have h2 := card_bar2_of_isAlt_five h.hKshape
        omega
    have hL2' : IsL2 (Bar2 L) (S17.nOf L) ∨ IsSz (Bar2 L) (S17.nOf L) := by
      rw [S17.nOf_eq_of_isL2 hL2]
      exact Or.inl hL2
    have hXsup : UC22.conjClosure D.M L = L ⊔ conjSubgroup L x := by rw [hXeq, hKx]
    have hne : UC22.conjClosure D.M L ≠ L := by
      intro hXL
      have hKle : K ≤ L := le_sup_right.trans (hXeq.symm.trans hXL).le
      have hcard : Nat.card ↥K = Nat.card ↥L := by
        rw [hKx, CFSG.Quasithin.conjSubgroup]
        exact Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective
      exact h.hne (Subgroup.eq_of_le_of_card_ge hKle (by rw [hcard]))
    have hgen := S18.orbitClosure_imageBar2_sup_imageBar2_eq_top hLc hxM hXsup hne rfl
    have hcf : ∀ T' : Subgroup (Bar2 (UC22.conjClosure D.M L ⊔ D.T)),
        CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ → CompFactorAutInF (S17.nOf L) ⊤ T' :=
      fun T' hT' => compFactorAutInF_of_hasComponentShapes hT'.isPGroup
        (hasComponentShapes_of_mulEquiv Subgroup.topEquiv.symm
          (S18.hasComponentShapes_bar2_sup hLc hxM hXsup hne rfl hL2')) hKc
    have hF : InFSq (S17.nOf L) (UC22.conjClosure D.M L ⊔ D.T) :=
      S18.inFSq_conjClosure_sup_of_components hLc h43c hL2' hgen hcf
    rwa [S17.nOf_eq_of_isL2 hL2, hXeq] at hF
  · left
    have hLnH : (L.subgroupOf (L ⊔ D.T)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        ((sup_le hLM D.sylowM.le).trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hLn))
    refine ⟨hLn, hKn, ?_, S18.inFSq_sup_T_of_normal h.hK hKn h.hKshape hKc⟩
    rcases h.shape with hL2 | hU3'
    · exact S18.inFSq_of_isL2_of_normal_sup le_sup_left hLnH
        (TwelveShort.isSylowIn_of_le D le_sup_right) rfl hLc.2.1 hL2 hKc
    · exact hU3 G L D.T (L ⊔ D.T) 2 le_sup_left hLnH hLc.2.1 hLc.2.2
        (uc22p22d_isSU3_of_isU3 hLc.2.2 hU3') (TwelveShort.isSylowIn_of_le D le_sup_right) rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
