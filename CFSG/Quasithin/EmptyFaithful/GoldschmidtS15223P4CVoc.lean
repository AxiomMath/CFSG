module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Facts
public import CFSG.Quasithin.EmptyFaithful.LRedTheta
public import CFSG.Quasithin.EmptyFaithful.LRed4Alt
public import CFSG.Quasithin.EmptyFaithful.R3cBlocks
public import CFSG.Quasithin.EmptyFaithful.S152U21

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S15223P4

namespace C

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

abbrev kI (T Mc M : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M))) : Subgroup G :=
  oPrimeResidualOf 3 (Subgroup.centralizer (zSOf T Mc M B₀ : Set G))

structure CData (T Mc M H : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M)))
    (I X : Subgroup G) : Prop where
  c : P4Ctx T Mc M H B₀ I X
  f : P4Fact T Mc M H B₀ I X
  oP : oPrimeResidualOf 3 I = X
  ln : IsLnTwoQuot X 4 ∨ IsLnTwoQuot X 5

theorem pRank_three_X (hLn : IsLnTwoQuot X 4 ∨ IsLnTwoQuot X 5) : CFSG.Open.pRank 3 X = 2 :=
  (threeRankBlocks_holds G X).2.2 (hLn.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inr (Or.inr h))

omit [Finite G] in
theorem isRankTwoListType_of (hLn : IsLnTwoQuot X 4 ∨ IsLnTwoQuot X 5) : IsRankTwoListType X :=
  hLn.elim (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

theorem oPrime_eq_X (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) (c : P4Ctx T Mc M H B₀ I X)
    (hLn : IsLnTwoQuot X 4 ∨ IsLnTwoQuot X 5) : oPrimeResidualOf 3 I = X := by
  symm
  rcases hLn with h | h
  · obtain ⟨e⟩ := h
    exact eq_oPrimeResidualOf_three_of_exclusion hF318 h36 h38 c.hyp.sqtk c.comp c.quasi
      (MulEquiv.refl _) (hK.l42 _ (LRed4.isPSL_two_of_statedSL' (by norm_num) e))
  · obtain ⟨e⟩ := h
    exact eq_oPrimeResidualOf_three_of_exclusion hF318 h36 h38 c.hyp.sqtk c.comp c.quasi
      (MulEquiv.refl _) (hK.l52 _ (LRed4.isPSL_two_of_statedSL' (by norm_num) e))

theorem CData.mk' (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) (c : P4Ctx T Mc M H B₀ I X)
    (hLn : IsLnTwoQuot X 4 ∨ IsLnTwoQuot X 5) : CData T Mc M H B₀ I X :=
  ⟨c, c.facts (thetaEqComponent_of_a318 hF318 h36 h38 hK) (pRank_three_X hLn)
    (isRankTwoListType_of hLn), oPrime_eq_X hF318 h36 h38 hK c hLn, hLn⟩

theorem kI_le_centralizer (T Mc M : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M))) :
    kI T Mc M B₀ ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

namespace CData

variable (d : CData T Mc M H B₀ I X)

include d

theorem centralizer_le_I : Subgroup.centralizer (zSOf T Mc M B₀ : Set G) ≤ I :=
  (centralizer_zS_le_inf152 d.c.inputs).trans inf_le_right

theorem kI_le_X : kI T Mc M B₀ ≤ X := by
  rw [← d.oP]
  exact Subgroup.closure_mono fun x hx => ⟨d.centralizer_le_I hx.1, hx.2⟩

theorem T_le_normalizer_zS : T ≤ Subgroup.normalizer (zSOf T Mc M B₀ : Set G) := by
  obtain ⟨B, hB⟩ := d.c.inputs.hN.sigmaPrime_nonempty
  have hZ := commutator_eq_zSOf d.c.inputs.h13 d.c.b0 hB
  exact hZ ▸ (d.c.inputs.h11 B hB).normal

theorem T_le_normalizer_centralizer :
    T ≤ Subgroup.normalizer
      ((Subgroup.centralizer (zSOf T Mc M B₀ : Set G) : Subgroup G) : Set G) :=
  d.T_le_normalizer_zS.trans (B2F.normalizer_le_normalizer_centralizer _)

theorem T_le_normalizer_kI : T ≤ Subgroup.normalizer (kI T Mc M B₀ : Set G) :=
  d.T_le_normalizer_centralizer.trans (normalizer_le_normalizer_oPrimeResidualOf1516 3 _)

theorem S_le_normalizer_X : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (X : Set G) := fun _ hs =>
  d.f.X_normal (S_le_I152 d.c.inputs hs)

end CData

end C

end S15223P4

end CFSG.Quasithin
