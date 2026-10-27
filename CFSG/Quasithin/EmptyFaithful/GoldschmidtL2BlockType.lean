module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockClass
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockRes
public import CFSG.Quasithin.EmptyFaithful.S151S5C
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Final
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Model
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Block
public import CFSG.Quasithin.Background.G2A5Iso

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem card_quot_eq_alt {G : Type} [Group G] {L : Subgroup G} {m : ℕ}
    (α : ↥L →* alternatingGroup (Fin m)) (hs : Function.Surjective α)
    (hk : α.ker = CFSG.pCore 2 ↥L) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card (alternatingGroup (Fin m)) :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hs)).toEquiv

theorem eq_five_of_card_alt {m : ℕ} (h : Nat.card (alternatingGroup (Fin m)) = 60) : m = 5 := by
  by_cases hm : 2 ≤ m
  · have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at h
    by_contra hne
    rcases Nat.lt_or_ge m 6 with hlt | hge
    · interval_cases m <;> simp [Nat.factorial] at h hne
    · have : Nat.factorial 6 ≤ Nat.factorial m := Nat.factorial_le hge
      simp [Nat.factorial] at this
      omega
  · exfalso
    have h1 : Nat.card (alternatingGroup (Fin m)) ≤ Nat.card (Equiv.Perm (Fin m)) :=
      Subgroup.card_le_card_group _
    rw [h, Nat.card_perm, Nat.card_fin] at h1
    interval_cases m <;> simp [Nat.factorial] at h1

theorem input15120L2BlockType_holds (h42 : AsB42) (hLJ : Input15120LJ) :
    Input15120L2BlockType := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hA hblock
  have hA' := hA
  obtain ⟨n, hn, hLn⟩ := hA
  set S := s1516 T Z₁ with hSdef
  set X := L ⊔ S with hXdef
  have hq := hc.ctx.qtfe
  have hSet := hc.ctx.setting
  have hMf := hc.ctx.mf
  have hlocal := quasithinIsLocal_iff_lFamily.mp hc.hL.mem.2
  have hSyl : IsSylowTwoOf S X := hlocal.2.1
  have hpcX : pCoreOf 2 X ≠ ⊥ := hlocal.2.2
  have hSQ : IsSQTKTC X :=
    ⟨kGroup_of_pCoreOf_ne_bot hq.qtke hq.simple hq.nonabelian hpcX,
      stronglyQuasithin_of_pCoreOf_ne_bot hq.qtke hpcX⟩
  have hX : CharTwo X := charTwo_sup_s1516_of_listA hc hchar hA'
  have hLG : L ≤ g1_1516 Z₁ := hc.hL.mem.1
  have hLJ' : ⁅L, thompsonJ S⁆ = L := hLJ G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar
  have hZ₁T : Z₁ ≤ T := hSet.z1_le_T hq hMf
  have hJN : thompsonJ S ≤ Subgroup.normalizer (L : Set G) := by
    refine L246.le_normalizer_of_forall_conj fun j hj l hl => ?_
    have h1 : ⁅l⁻¹, j⁆ ∈ ⁅L, thompsonJ S⁆ :=
      Subgroup.commutator_mem_commutator (L.inv_mem hl) hj
    rw [hLJ'] at h1
    have e : l * ⁅l⁻¹, j⁆ = j * l * j⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [← e]
    exact L.mul_mem hl h1
  have hTS : quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter S := by
    refine (Subgroup.closure_le _).mpr fun z hz => ?_
    have hzS : z ∈ S := ⟨hz.1.1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp hz.1.2 y (hZ₁T hy)⟩
    exact Subgroup.subset_closure ⟨⟨hzS, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp hz.1.2 y (s1516_le T Z₁ hy)⟩, hz.2⟩
  have hLnZS : ¬ L ≤ Subgroup.centralizer (quasithinOmegaOneCenter S : Set G) := by
    intro hLZ
    apply hc.hL.not_le
    intro x hx
    exact ⟨hLG hx, hq.centralizer_le_mc
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTS) (hLZ hx))⟩
  have hLnV : ¬ L ≤ Subgroup.centralizer (VZ S X : Set G) := fun hLV =>
    hLnZS fun x hx => Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr (le_conjClosure _ _)) (hLV hx)
  have hnot : ¬ ⁅L, thompsonJ S⁆ ≤ Subgroup.centralizer (VZ S X : Set G) := by
    rw [hLJ']; exact hLnV
  have hUV : blockU L ≤ VZ S X :=
    (L246C127.Setting.mk (X := X) (T := S) (P := X) (K := L) hX hSyl le_rfl hSyl.1
      hblock).blockU_le_VZ hLnZS
  by_cases hn2 : n = 2
  ·
    subst hn2
    obtain ⟨K, hF, hfin, hchar, hcard, ⟨e⟩⟩ := S151S4.exists_equiv_sl2 hLn
    have hK4 : Nat.card K = 4 := by simpa using hcard
    have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 60 := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK4]; norm_num
    obtain ⟨e5⟩ := CFSG.Quasithin.A5Model.sl2_four_equiv_alt5 K hK4 hSL
    let φ : ↥L →* alternatingGroup (Fin 5) :=
      (e.trans e5).toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    have hφs : Function.Surjective φ :=
      (e.trans e5).surjective.comp (QuotientGroup.mk'_surjective _)
    have hφk : φ.ker = (Subgroup.centralizer (VZ S X : Set G)).subgroupOf L := by
      rw [L246.centralizer_subgroupOf_eq_pCore hX hSyl hblock hUV]
      ext l
      rw [MonoidHom.mem_ker]
      show (e.trans e5) (QuotientGroup.mk' (CFSG.pCore 2 ↥L) l) = 1 ↔ _
      rw [map_eq_one_iff _ (e.trans e5).injective]
      exact QuotientGroup.eq_one_iff l
    have hchi := L238.altBlockStatementJ_of_asB42 h42 Bridge.alt57ModelFacts X S L hX hSQ hSyl
      hblock hUV hJN hnot ⟨5, ⟨2, rfl⟩, by norm_num, φ, hφs, hφk⟩
    have hcard60 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 := by
      rw [Nat.card_congr (e.trans e5).toEquiv, Bridge.card_alt_five]
    rcases hchi with ⟨-, hlin | ⟨m, -, -, hAlt⟩⟩ | hexc
    · exact Or.inr hlin
    · obtain ⟨α, hαs, hαk, hβ⟩ := hAlt
      have hm := eq_five_of_card_alt (m := m)
        ((card_quot_eq_alt α hαs hαk).symm.trans hcard60)
      subst hm
      exact Or.inl ⟨α, hαs, hαk, hβ⟩
    · exfalso
      obtain ⟨-, ⟨α, hαs, hαk⟩, -⟩ := hexc
      have h1 := (card_quot_eq_alt α hαs hαk).symm.trans hcard60
      rw [Bridge.card_alt_seven] at h1
      omega
  · have D : L246.BlockDataS X S L n := ⟨hX, hSyl, hblock, hJN, hUV, hnot, hLn⟩
    exact Or.inr ⟨n, by omega, D.isLin2Type (by omega) Bridge.kClosed_native
      (Bridge.asB42With_kGroup.2 h42) hSQ.1 hSQ.2⟩

end CFSG.Quasithin
