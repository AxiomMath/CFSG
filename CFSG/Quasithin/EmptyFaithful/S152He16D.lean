module

public import CFSG.Quasithin.EmptyFaithful.S152He16B
public import CFSG.Quasithin.EmptyFaithful.S152He16C
public import CFSG.Quasithin.EmptyFaithful.S152He9N
public import CFSG.Quasithin.Vol2.Ch1Chief

public section

namespace CFSG.Quasithin.He16

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem nonQuasi_commutator_le (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h36 : A36ForSQTK) (h129 : ASC129StatementUsed G)
    {G₀ R M₁ Lc S Y : Subgroup G} (hyp : HypC23 G₀ R M₁) (hchar : CharTwo G₀)
    (hne : pCoreOf 2 G₀ ≠ ⊥) (hL : Lc ∈ cComp G₀) (hLn : (Lc.subgroupOf G₀).Normal)
    (hS : IsSylowTwoOf S G₀) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hMY : M₁ ≤ Subgroup.normalizer (Y : Set G)) (hYL : Y ≤ Lc)
    (hY5 : (pCoreOf 2 Y).relIndex Y = 5) (hYo : Y = oTwoUpper Y)
    (hnq : ¬ CFSG.IsQuasisimple ↥(modO2Image G₀ Lc)) : ⁅Y, Lc⁆ ≤ pCoreOf 2 G₀ := by
  have hLG : Lc ≤ G₀ := le_of_mem_cComp hL
  have hYG : Y ≤ G₀ := hYL.trans hLG
  obtain ⟨hconc, hcommon, hextra⟩ := lemma_1_2_1_four_strong hK hs hnab h36 hne hL
  have hcase : A36Case3 ↥(modO2Image G₀ Lc) ∨ A36Case4 ↥(modO2Image G₀ Lc) := by
    rcases hconc with ⟨hc, -⟩ | ⟨hc, -⟩ | h3 | h4
    · exact absurd hc.1 hnq
    · exact absurd hc.1 hnq
    · exact Or.inl h3
    · exact Or.inr h4
  have hex := hextra hcase
  obtain ⟨hFO, hqs, -, -, -⟩ := hcommon
  have hFodd : ∀ x ∈ CFSG.fittingSubgroup ↥(modO2Image G₀ Lc), Odd (orderOf x) := by
    intro x hx
    have hx' : x ∈ CFSG.oddCore ↥(modO2Image G₀ Lc) := hFO ▸ hx
    exact Odd.of_dvd_nat (A312.odd_card_oddCore _) (Subgroup.orderOf_dvd_natCard _ hx')
  have h3F : ¬ 3 ∣ Nat.card (CFSG.fittingSubgroup ↥(modO2Image G₀ Lc)) := by
    rcases hcase with ⟨p, hp, hp3, -, hF, -⟩ | ⟨-, -, -, hprime⟩
    · rw [card_isElemAbelianOfRank hF]
      intro h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    · intro h3
      have := (hprime 3 Nat.prime_three h3).1
      omega
  have hgf : CFSG.generalizedFitting ↥(modO2Image G₀ Lc) =
      CFSG.fittingSubgroup ↥(modO2Image G₀ Lc) := by
    rcases hcase with ⟨p, hp, hp3, hgf, -⟩ | ⟨hgf, -⟩
    · exact hgf
    · exact hgf
  have hF₁le : preimageModTwoCore G₀ (fMap G₀ Lc) ≤ oTwoFIn G₀ :=
    preimageModTwoCore_mono (fMap_le_fitting hLn)
  have hF₁G : preimageModTwoCore G₀ (fMap G₀ Lc) ≤ G₀ := preimageModTwoCore_le
  have : (fMap G₀ Lc).Normal := normal_fMap hLn
  have hF₁n : ((preimageModTwoCore G₀ (fMap G₀ Lc)).subgroupOf G₀).Normal :=
    normal_preimageModTwoCore
  have hF₁N : G₀ ≤ Subgroup.normalizer (preimageModTwoCore G₀ (fMap G₀ Lc) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hF₁G).1 hF₁n
  have hcharF : CharTwo (oTwoFIn G₀) :=
    CFSG.Quasithin.CT.CharTwo.of_normal hchar C2Six.oTwoFIn_le C2Six.normal_oTwoFIn_subgroupOf
  have hFM : preimageModTwoCore G₀ (fMap G₀ Lc) ≤ M₁ := by
    refine le_of_threePrime h129 hyp hcharF hF₁le hF₁n fun x hx hxF => ?_
    obtain ⟨hx', hmem⟩ := mem_preimageModTwoCore.mp hxF
    rw [orderOf_mk_open_eq]
    intro h3
    exact h3F (h3.trans (orderOf_dvd_of_mem_fMap hmem))
  have hYF₁ : Y ≤ preimageModTwoCore G₀ (fMap G₀ Lc) :=
    Y_le_of_centralizes hY5 hYo hYG hF₁N (hFM.trans hMY)
      (fun x hx k hk => mem_pCoreOf_of_pow_eq_one hFodd hx hk)
      (fun y hy hc => mem_preimage_fMap_of_centralizes hgf hYL hYG hy hc)
  have hYhF : modO2Image G₀ Y ≤ fMap G₀ Lc := by
    intro u hu
    obtain ⟨y, hyG, hyY, rfl⟩ := mem_modO2Image_iff.mp hu
    exact (mem_preimageModTwoCore.mp (hYF₁ hyY)).2
  have hYodd : ¬ 2 ∣ Nat.card (modO2Image G₀ Y) :=
    not_two_dvd_card_of_forall_odd _ (fun x hx => odd_orderOf_of_mem_fMap hFodd (hYhF hx))
  have hY5' : Nat.card (modO2Image G₀ Y) = 5 := card_modO2Image_eq_five hYG hY5 hYodd
  have hFhN : fMap G₀ Lc ≤
      Subgroup.normalizer (modO2Image G₀ Y : Set (↥G₀ ⧸ CFSG.pCore 2 ↥G₀)) := by
    intro u hu
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
    have hgF : (g : G) ∈ preimageModTwoCore G₀ (fMap G₀ Lc) :=
      mem_preimageModTwoCore.mpr ⟨g.2, hu⟩
    exact mk_mem_normalizer_modO2Image g.2 (hMY (hFM hgF))
  have hShN : modO2Image G₀ S ≤
      Subgroup.normalizer (modO2Image G₀ Y : Set (↥G₀ ⧸ CFSG.pCore 2 ↥G₀)) := by
    intro u hu
    obtain ⟨x, hxG, hxS, rfl⟩ := mem_modO2Image_iff.mp hu
    exact mk_mem_normalizer_modO2Image hxG (hSY hxS)
  have hcentral := nq_core' (L := modO2Image G₀ Lc) (Y := modO2Image G₀ Y) (S := modO2Image G₀ S)
    hcase hex hFodd hqs.1 hY5' (Subgroup.map_mono (Subgroup.subgroupOf_mono G₀ hYL)) hYhF hFhN hShN
    (isSylowTwoOf_modO2Image_inf hS hLn)
  rw [Subgroup.commutator_le]
  intro y hy l hl
  have hyG : y ∈ G₀ := hYG hy
  have hlG : l ∈ G₀ := hLG hl
  have h1 := hcentral _ (mem_modO2Image_iff.mpr ⟨y, hyG, hy, rfl⟩) _
    (mem_modO2Image_iff.mpr ⟨l, hlG, hl, rfl⟩)
  exact (mk_commute_iff' ⟨y, hyG⟩ ⟨l, hlG⟩).mp h1

theorem commutator_le_of_not_quasisimple (h36 : A36ForSQTK)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G)
    {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)
    {Lc : Subgroup G} (tail : Tail15204 c Lc) (hYL : yOf152 T Mc M ≤ Lc)
    (hnq : ¬ CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc)) :
    ⁅yOf152 T Mc M, Lc⁆ ≤ pCoreOf 2 (g0Of T Mc M K₁) :=
  nonQuasi_commutator_le c.hs.qtfe.qtke c.hs.qtfe.simple c.hs.qtfe.nonabelian h36 (h129 G)
    tail.hyp tail.charTwo tail.ne_bot tail.comp tail.normal tail.sylow c.S_le_normalizer_Y
    (inf_le_left.trans c.y.normal) hYL c.y.relIndex_five (yOf152_eq_oTwoUpper T Mc M) hnq

@[expose] def Input15204BranchBQuasi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M H K₁ K₂ : Subgroup G) (π : ↥H →* W5)
    (c : Ctx15204 T Mc M H K₁ K₂ π) (Lc : Subgroup G), Tail15204 c Lc →
    yOf152 T Mc M ≤ Lc → ¬ IsSylowTwoOf (rOf T Mc M K₁) (rOf T Mc M K₁ ⊔ Lc) →
    CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc) → False

theorem input15204BranchB_of_quasi (h36 : A36ForSQTK)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G)
    (hQ : Input15204BranchBQuasi) : Input15204BranchB := by
  intro G _ _ T Mc M H K₁ K₂ π c Lc tail hYL hnot
  by_cases hq : CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc)
  · exact hQ G T Mc M H K₁ K₂ π c Lc tail hYL hnot hq
  · exact c.false_of_commutator_le tail.le (le_of_mem_cComp tail.comp) tail.sylow
      (commutator_le_of_not_quasisimple h36 h129 c tail hYL hq)

end CFSG.Quasithin.He16
