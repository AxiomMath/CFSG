module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Two
public import CFSG.Quasithin.Vol2.Ch6Sec1Residuals
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25LieB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G]

theorem exists_isHStar_le_ch625 {T M X : Subgroup G} (hX : InH T X) (hXM : ¬ X ≤ M) :
    ∃ H : Subgroup G, IsHStar T M H ∧ H ≤ X := by
  obtain ⟨H, ⟨hHH, hHM, hHX⟩, hmin⟩ :=
    (Set.toFinite {Y : Subgroup G | InH T Y ∧ ¬ Y ≤ M ∧ Y ≤ X}).exists_minimal
      ⟨X, hX, hXM, le_rfl⟩
  exact ⟨H, ⟨hHH, hHM, fun Y hY hYH hYM =>
    le_antisymm hYH (hmin ⟨hY, hYM, hYH.trans hHX⟩ hYH)⟩, hHX⟩

theorem lie625Elim_of (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact)
    (kf4 : LieOvergroupFact) (hres : Res625Lie) : Lie625Elim := by
  intro G _ _ T M L V n l DL K hI d hLie
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t₀, ht₀, ht₀K⟩ := d.exists_t0 hI
  obtain ⟨hK'c, -, -, -, -⟩ := d.KT_facts hI ht₀ ht₀K
  set K' := K.map (MulAut.conj t₀).toMonoidHom with hK'
  set Y := (K ⊔ K') ⊔ T with hY
  set Z := ch6ZS T L V with hZ
  have hZT : Z ≤ T := (inf_le_left : Z ≤ V).trans d.hyp.toHyp611.le_T
  have hZ2 : IsPGroup 2 Z :=
    (B2F.isPGroup_of_isElemAbelian d.hyp.toHyp611.isElemAbelian).to_le inf_le_left
  have hYZ : Y ≤ Subgroup.normalizer (Z : Set G) := by
    have hIN : Subgroup.centralizer (Z : Set G) ≤ Subgroup.normalizer (Z : Set G) :=
      Subgroup.centralizer_le_normalizer _
    refine sup_le (sup_le (d.K_le_I.trans hIN) ((le_of_mem_cComp hK'c).trans hIN)) ?_
    exact d.hyp.toHyp611Nat.T_le_normalizer_ZS
  have hYH : InH T Y := by
    refine ⟨le_sup_right, fun h0 => d.hyp.toHyp611Nat.ZS_ne_bot ?_⟩
    have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hZT.trans le_sup_right)
      hYZ hZ2
    rw [h0] at hle
    exact le_bot_iff.mp hle
  have hYM : ¬ Y ≤ M := fun h => d.K_not_le_M hI (le_sup_left.trans (le_sup_left.trans h))
  obtain ⟨H₂, hH₂, hH₂Y⟩ := exists_isHStar_le_ch625 hYH hYM
  by_cases hs : Group.IsSolvable ↥H₂
  · exact hH₂.2.1 (d.le_M_of_solvable hI kf1 h23 kf4 hLie ht₀ ht₀K hH₂.1.1 hH₂Y hs)
  · exact hres G T M L V n l DL K hI d hLie t₀ ht₀ ht₀K H₂ hH₂ hH₂Y hs
      (d.hyp.nParam_eq_one H₂ hH₂)

end CFSG.Quasithin.H13
