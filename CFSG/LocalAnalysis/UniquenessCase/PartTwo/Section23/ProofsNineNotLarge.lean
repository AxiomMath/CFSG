module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Bar2TransferSL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineKNotLarge
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

private theorem Hinf_subgroupOf (c : Ctx23L D Ch) {A : Subgroup G} (hA : A ≤ c.L) :
    Hinf (A.subgroupOf c.L) = (Hinf A).subgroupOf c.L := by
  apply Subgroup.map_subtype_inj.mp
  rw [Hinf_map, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le ((uc22p21c_Hinf_le A).trans hA)]

theorem map_inf_eq_stabilizer_Ztil (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
    ((D.M ⊓ c.L).subgroupOf c.L).map (c.phiL hV) =
      MulAction.stabilizer ↥(c.H hV)
        (((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV))) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (c.phiL_mem_stabilizer_Ztil_iff hV h4 h1930 x).2
      (Subgroup.mem_subgroupOf.1 hx).1
  · intro y hy
    obtain ⟨x, rfl⟩ := c.phiL_surjective hV y
    refine Subgroup.mem_map.mpr ⟨x,
      Subgroup.mem_subgroupOf.mpr
        ⟨(c.phiL_mem_stabilizer_Ztil_iff hV h4 h1930 x).1 hy, x.2⟩, rfl⟩

theorem map_Hinf_inf_eq (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
    ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) =
      Hinf (MulAction.stabilizer ↥(c.H hV)
        (((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV)))) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  have hsub := Hinf_subgroupOf c (A := D.M ⊓ c.L) inf_le_right
  rw [← hsub, Hinf_map, map_inf_eq_stabilizer_Ztil c hV h4 h1930]

end Ctx23L

private theorem nontrivial_of_isSLn_three {X : Type} [Group X] {n : ℕ}
    (h : IsSLn X 3 n) (hn : 3 ≤ n) : Nontrivial X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  have h2 : 2 ≤ Nat.card K := by
    rw [hKcard]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hgt : 1 < Nat.card (↥(StatedSL 3 K)) := by
    rw [CFSG.Open.StatedAPI.card_statedSL_three]
    have h8 : 8 ≤ Nat.card K ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left h2 3
    have h4 : 4 ≤ Nat.card K ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left h2 2
    have h3 : 3 ≤ Nat.card K ^ 2 - 1 := by omega
    have h7 : 7 ≤ Nat.card K ^ 3 - 1 := by omega
    calc 1 < 8 * (3 * 7) := by norm_num
      _ ≤ Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) :=
        Nat.mul_le_mul h8 (Nat.mul_le_mul h3 h7)
  haveI : Nontrivial (↥(StatedSL 3 K)) := Finite.one_lt_card_iff_nontrivial.mp hgt
  exact e.toEquiv.nontrivial

private theorem exists_quotient_bar2 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {K : Subgroup G}
    {Kstar : Subgroup ↥(c.H hV)} (hKle : K ≤ c.L)
    (hKstar_eq : (K.subgroupOf c.L).map (c.phiL hV) = Kstar) :
    ∃ (N : Subgroup (Bar2 K)) (hN : N.Normal),
      letI : N.Normal := hN
      Nonempty (Bar2 Kstar ≃* (Bar2 K ⧸ N)) := by
  let g : ↥K →* ↥(c.H hV) := (c.phiL hV).comp (Subgroup.inclusion hKle)
  let f : ↥K →* ↥Kstar := g.codRestrict Kstar fun x => by
    have hx : g x ∈ (K.subgroupOf c.L).map (c.phiL hV) :=
      Subgroup.mem_map.mpr ⟨⟨x.1, hKle x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
    rwa [hKstar_eq] at hx
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : ↥(c.H hV)) ∈ (K.subgroupOf c.L).map (c.phiL hV) := by
      rw [hKstar_eq]; exact y.2
    obtain ⟨x, hx, hxφ⟩ := Subgroup.mem_map.1 hy
    refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩, ?_⟩
    apply Subtype.ext
    exact hxφ
  let N : Subgroup (Bar2 K) :=
    (CFSG.pCore 2 ↥Kstar).comap f |>.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
  have hN : N.Normal :=
    ((CFSG.pCore_normal (p := 2) (G := ↥Kstar)).comap f).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (QuotientGroup.mk'_surjective _)
  refine ⟨N, hN, ?_⟩
  have hNle : CFSG.pCore 2 ↥K ≤ (CFSG.pCore 2 ↥Kstar).comap f :=
    pCore_le_comap_of_surjective f hf
  exact ⟨(quotientQuotientEquivQuotientOfSurjective
    (N := CFSG.pCore 2 ↥K) (P := CFSG.pCore 2 ↥Kstar) f hf hNle).symm⟩

private theorem false_of_K_eq_bot {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {n : ℕ} {Kstar : Subgroup ↥(c.H hV)}
    (hn : 3 ≤ n)
    (hKstar_eq : ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) = Kstar)
    (hKbot : Hinf (D.M ⊓ c.L) = ⊥)
    (hlarge : IsSLn (Bar2 Kstar) 3 n ∨ IsSp4 (Bar2 Kstar) n ∨ IsU4 (Bar2 Kstar) n) :
    False := by
  have hKstar_bot : Kstar = ⊥ := by
    rw [← hKstar_eq, hKbot]
    simp
  have hnt : Nontrivial (Bar2 Kstar) := by
    rcases hlarge with hSL | hSp | hU
    · exact nontrivial_of_isSLn_three hSL hn
    · exact (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags
        (by decide) hSp).toNontrivial
    · exact (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags
        (by decide) hU).toNontrivial
  have hss : Subsingleton (Bar2 Kstar) := by
    rw [hKstar_bot]
    exact ⟨fun a b => by
      induction a using QuotientGroup.induction_on
      induction b using QuotientGroup.induction_on
      congr 1
      exact Subsingleton.elim _ _⟩
  exact (not_nontrivial_iff_subsingleton.mpr hss) hnt

private theorem false_of_K_mem_calC {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {n : ℕ} {Kstar : Subgroup ↥(c.H hV)}
    (hn : 3 ≤ n) (h8 : S23_8 D Ch) (h1930 : H1930 D) (hNL : KNotLarge23)
    (hKstar_eq : ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) = Kstar)
    (hKcal : Hinf (D.M ⊓ c.L) ∈ calC D.M)
    (hlarge : IsSLn (Bar2 Kstar) 3 n ∨ IsSp4 (Bar2 Kstar) n ∨ IsU4 (Bar2 Kstar) n) :
    False := by
  let K : Subgroup G := Hinf (D.M ⊓ c.L)
  have hKcal' : K ∈ calC D.M := hKcal
  obtain ⟨-, hshape⟩ := h8 h1930 c K hKcal'
  have hshapeQ : (∃ a : ℕ, IsL2 (Bar2 K) a ∨ IsSz (Bar2 K) a) ∨
      (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsL2Odd (Bar2 K) q) ∨ IsJ1 (Bar2 K) := by
    rcases hshape with ⟨a, -, hL2 | hSz⟩ | ⟨hrest, -⟩
    · exact Or.inl ⟨a, Or.inl hL2⟩
    · exact Or.inl ⟨a, Or.inr hSz⟩
    · rcases hrest with hq | hJ | ⟨a, hL2⟩
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr hJ)
      · exact Or.inl ⟨2 * a, Or.inl hL2⟩
  obtain ⟨N, hN, ⟨e⟩⟩ :=
    exists_quotient_bar2 c hV (K := K)
      (show K ≤ c.L from (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right)
      (show (K.subgroupOf c.L).map (c.phiL hV) = Kstar from hKstar_eq)
  haveI : N.Normal := hN
  refine hNL.1 (Bar2 K) hshapeQ N n hn ?_
  rcases hlarge with hSL | hSp | hU
  · exact Or.inl (IsSLn.of_mulEquiv e hSL)
  · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hSp))
  · exact Or.inr (Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e hU))

private theorem false_of_su4 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) {n : ℕ} {Kstar : Subgroup ↥(c.H hV)}
    (hn : 3 ≤ n) (hNL : KNotLarge23) (hL2 : ∃ a : ℕ, IsL2 (Bar2 Kstar) a)
    (hlarge : IsSLn (Bar2 Kstar) 3 n ∨ IsSp4 (Bar2 Kstar) n ∨ IsU4 (Bar2 Kstar) n) :
    False := by
  obtain ⟨a, hL2⟩ := hL2
  have hshapeQ : (∃ a : ℕ, IsL2 (Bar2 Kstar) a ∨ IsSz (Bar2 Kstar) a) ∨
      (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsL2Odd (Bar2 Kstar) q) ∨ IsJ1 (Bar2 Kstar) :=
    Or.inl ⟨a, Or.inl hL2⟩
  have hcontra := hNL.1 (Bar2 Kstar) hshapeQ ⊥ n hn
  have e : Bar2 Kstar ⧸ (⊥ : Subgroup (Bar2 Kstar)) ≃* Bar2 Kstar :=
    QuotientGroup.quotientBot
  rcases hlarge with hSL | hSp | hU
  · exact hcontra (Or.inl (IsSLn.of_mulEquiv e.symm hSL))
  · exact hcontra (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hSp)))
  · exact hcontra (Or.inr (Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hU)))

theorem s23_9_NotLarge_of (D : Data G) (Ch : Choice2011 G)
    (hA : KTab23a) (hd : KTab23d) (h4 : S23_4 D Ch) (h8 : S23_8 D Ch)
    (hB23 : S23_9_B23 D Ch) (hNL : KNotLarge23) :
    S23_9_NotLarge D Ch := by
  intro h1930 c h3 hV
  let n : ℕ := CFSG.Open.pRank 2 D.Z
  change ¬ ((IsSLn ↥(c.H hV) 4 n ∧
      CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 4 n) ∨
    (IsSpn ↥(c.H hV) 6 n ∧ NatSpn (c.H hV) ⊤ ⊥ 6 n) ∨
    (IsOmega8m ↥(c.H hV) n ∧ NatOmegaMinus (c.H hV) ⊤ ⊥ 8 n))
  intro hline
  have hline0 := hline
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  let K : Subgroup G := Hinf (D.M ⊓ c.L)
  let Kstar : Subgroup ↥(c.H hV) :=
    Hinf (MulAction.stabilizer ↥(c.H hV)
      (((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
        Set (c.W hV))))
  have hnat : IsNaturalClassicalModule (c.H hV) n := by
    rcases hline with ⟨hSL, hBin⟩ | ⟨hSp, hNatSp⟩ | ⟨hO8, hNatO8⟩
    · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
        .inl ⟨hSL, hBin⟩
    · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
        .inl ⟨hSp, hNatSp⟩
    · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
        .inr ⟨hO8, hNatO8⟩
  have hd' := hd (c.W hV) (c.H hV) n hnat (c.commutator_H_eq hV) h3 (c.sylowStar hV)
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV :=
    c.fixedPointSubgroup_sylowStar_eq_Ztil hV hA hnat h4 h1930
  have hKstar_eq : (K.subgroupOf c.L).map (c.phiL hV) = Kstar := by
    dsimp only [Kstar]
    rw [show MulAction.stabilizer ↥(c.H hV)
        (((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
          Set (c.W hV))) =
      MulAction.stabilizer ↥(c.H hV)
        (((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV))) by rw [hℓ]]
    exact c.map_Hinf_inf_eq hV h4 h1930
  have hlarge : IsSLn (Bar2 Kstar) 3 n ∨ IsSp4 (Bar2 Kstar) n ∨
      IsU4 (Bar2 Kstar) n := by
    rcases hline0 with ⟨hSL, hBin⟩ | ⟨hSp, hNatSp⟩ | ⟨hO8, hNatO8⟩
    · exact Or.inl (hd'.2.2.2.2.2.2.2.1 ⟨hSL, hBin⟩)
    · exact Or.inr (Or.inl (hd'.2.2.2.2.2.2.2.2.2.1 ⟨hSp, hNatSp⟩))
    · exact Or.inr (Or.inr (hd'.2.2.2.2.2.2.2.2.2.2 ⟨hO8, hNatO8⟩))
  have hB := hB23 h1930 c h3
  dsimp only at hB
  rcases hB with hKbot | hKcal | hKthird | hKfourth
  · exact false_of_K_eq_bot c hV h3 hKstar_eq hKbot hlarge
  · exact false_of_K_mem_calC c hV h3 h8 h1930 hNL hKstar_eq hKcal hlarge
  · obtain ⟨⟨hV', hOplus, hNatPlus⟩, -⟩ := hKthird
    have hOplusH : IsOmegaPlus ↥(c.H hV) 6 n := hOplus
    have hNatPlusH : NatOmegaPlus (c.H hV) ⊤ ⊥ 6 n := hNatPlus
    have hL2sq : IsL2Square (Bar2 Kstar) n :=
      hd'.2.2.2.2.2.2.2.2.1 ⟨hOplusH, hNatPlusH⟩
    exact (hNL.2 (Bar2 Kstar) n h3 hL2sq) hlarge
  · obtain ⟨⟨hV', a, hn2, hSU, hNatSU⟩, -⟩ := hKfourth
    have hSUH : IsSUn ↥(c.H hV) 4 a := hSU
    have hNatSUH : NatSUn (c.H hV) ⊤ ⊥ 4 a := hNatSU
    obtain ⟨a', -, hL2⟩ := hd'.2.2.2.2.2.1 ⟨a, hn2, hSUH, hNatSUH⟩
    exact false_of_su4 c hV h3 hNL ⟨a', hL2⟩ hlarge

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
