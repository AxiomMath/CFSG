module

public import CFSG.LocalAnalysis.StandardType.GGF4LabelPieces
public import CFSG.LocalAnalysis.StandardType.GGF4H5SevenConfig
public import CFSG.LocalAnalysis.StandardType.GGF4H5SevenBlocks
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGRealQFour
public import CFSG.LocalAnalysis.StandardType.GGRealKGTorusComponents
public import CFSG.LocalAnalysis.StandardType.GGSL7CentralCover
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeALift
public import CFSG.GroupTheory.MulAutCongr
import CFSG.LocalAnalysis.StandardType.GGCellWitness
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGen
import CFSG.LocalAnalysis.StandardType.GGFixedRealizedConfig
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGReflectionPairFix
import CFSG.LocalAnalysis.StandardType.GGF4H5Transport
import CFSG.LocalAnalysis.StandardType.GGF4A3ReflectionPair
import CFSG.LocalAnalysis.StandardType.GGF4B3ReflectionConjugacy

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

@[expose] def GGF4RowLarge
    (p : ℕ) (XL XK : Type) [Group XL] [Group XK] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.A, 3, f⟩ XL ∧ GGHasLabel ⟨.C, 3, f⟩ XK) ∨
  (∃ f : ℕ, 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.A, 3, f⟩ XL ∧ GGHasLabel ⟨.twD, 4, f⟩ XK) ∨
  (∃ f : ℕ, 2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.twA, 3, f⟩ XL ∧ GGHasLabel ⟨.C, 3, f⟩ XK) ∨
  (∃ f : ℕ, 2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.twA, 3, f⟩ XL ∧ GGHasLabel ⟨.twD, 4, f⟩ XK) ∨
  (∃ f : ℕ, 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.A, 3, 2 * f⟩ XL ∧ GGHasLabel ⟨.twA, 5, f⟩ XK)

@[expose] def GGF4H5Core
    : Prop :=
  GGLBalanceInput → GGStdSubPrimeInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
      (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) →
        ∀ K ∈ ks, ¬ GGReflRealizedIn p Bs K

theorem ggF4H5Pos_holds
    :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
        (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) →
          ∀ K ∈ ks, ∃ r ψ : MulAut ↥Bs, r ∈ ggAutomizer K Bs ∧ GGIsReflection p r ∧
            ψ ∈ ggAutomizerJoin L Bs ks ∧ x ∈ ggFixG Bs (ψ * r * ψ⁻¹) ∧
              ψ * r * ψ⁻¹ ∉ ggAutomizer L Bs := by
  intro G _ _ p B Bs x L D J ks hres hB K hK
  classical
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  obtain ⟨-, hp2, -⟩ := (hcfg.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  let : Fact p.Prime := ⟨hp⟩
  have hNT : GGNoTransvection p Bs := hres.1.1.2.2.2.1
  let A := ggAutomizerJoin L Bs ks
  have hALA : ggAutomizer L Bs ≤ A := le_sup_left
  have hAKA : ggAutomizer K Bs ≤ A :=
    le_sup_of_le_right (le_iSup₂_of_le K hK le_rfl)
  obtain ⟨ι, M, eP, hP, hF⟩ := hres.2.2.1
  obtain ⟨eI, rfl⟩ := hF
  have hW : GGWeylOfType p CoxeterMatrix.F₄ A :=
    GGWeylOfType.of_reindex (M := CoxeterMatrix.F₄) (e := eI) ⟨eP, hP.2⟩
  obtain ⟨e, he⟩ := hW
  let E : CoxeterMatrix.F₄.Group →* MulAut ↥Bs := A.subtype.comp e.toMonoidHom
  have hEinj : Function.Injective E := fun _ _ h => e.injective (Subtype.ext h)
  have hind : A ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    exact mem_ggInduced_top_of_mem_ggAutomizer
      (sup_le (ggAutomizer_mono Bs le_top)
        (iSup₂_le fun K _ => ggAutomizer_mono Bs le_top) hφ)
  have hM : GGIsWeylMatrix CoxeterMatrix.F₄ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩))))
  have hG2 : ¬ ∃ eI' : Fin 2 ≃ Fin 4, CoxeterMatrix.F₄ = CoxeterMatrix.G₂.reindex eI' := by
    rintro ⟨eI', -⟩
    have h := Fintype.card_congr eI'
    simp at h
  let cs := CoxeterMatrix.F₄.toCoxeterSystem
  have hconv : ∀ w : CoxeterMatrix.F₄.Group, GGIsReflection p (E w) → cs.IsReflection w := by
    intro w hw
    obtain ⟨j, g, hg⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds G p Bs hp hp2 hBs hNT
      A hind (Fin 4) CoxeterMatrix.F₄ hM hG2 e he (e w) hw
    exact ⟨g, j, e.injective hg⟩
  have hback : ∀ w : CoxeterMatrix.F₄.Group, cs.IsReflection w → GGIsReflection p (E w) := by
    rintro w ⟨g, j, rfl⟩
    simpa [cs, E, CoxeterMatrix.toCoxeterSystem_simple, map_mul, map_inv]
      using (he j).conj' (E g)
  obtain ⟨a, ha, oa01, oa12, oa02, hclosed⟩ :=
    ggF4H5Pos_A3_transport e hALA hres.2.2.2.1 hconv
  obtain ⟨b, hb, hbmem, ob01, ob12, ob02⟩ :=
    ggF4H5Pos_B3_transport e hAKA (hB K hK) hconv
  obtain ⟨t, u, ht, hu, hne, hcomm, hprod, hnot⟩ :=
    F4Model.exists_a3_reflection_pair cs a ha oa01 oa12 oa02
  obtain ⟨j, g, hconj⟩ := F4Model.exists_conj_b3_reflection cs b hb ob01 ob12 ob02 ht
  have hxL : ∀ φ ∈ ggAutomizer L Bs, x ∈ ggFixG Bs φ := by
    intro φ hφ
    exact Subgroup.mem_map.mpr ⟨⟨x, hxBs⟩,
      ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, hxBs⟩) hLx hφ, rfl⟩
  have hxprod : x ∈ ggFixG Bs (E t * E u) := by
    rw [← map_mul]
    exact hxL _ ((hclosed (t * u)).mpr hprod)
  have hcE : E t * E u = E u * E t := by rw [← map_mul, ← map_mul, hcomm]
  have hneE : E t ≠ E u := fun h => hne (hEinj h)
  have hxT := (ggFixG_mul_mem_of_commute hBs hp2 (hback t ht) (hback u hu) hcE hneE hxprod).1
  have hnotE : E t ∉ ggAutomizer L Bs := fun h => hnot ((hclosed t).mp h)
  have hconjE : E g * E (b j) * (E g)⁻¹ = E t := by
    rw [← map_inv, ← map_mul, ← map_mul, hconj]
  refine ⟨E (b j), E g, hbmem j, hback _ (hb j), (e g).2, ?_, ?_⟩
  · rwa [hconjE]
  · rwa [hconjE]

theorem ggF4H5Core_of_pos
    : GGF4H5Core := by
  have hpos := ggF4H5Pos_holds
  intro hL hP G _ _ p B Bs x L D J ks hres hB K hK hR
  obtain ⟨r, ψ, hrK, hrefl, hψ, hxfix, hnot⟩ := hpos G p B Bs x L D J ks hres hB K hK
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  have hInn : GGInnerDiagOn Bs L := hres.1.1.2.2.1.1
  have hP3 : GGFixedRealizedInL p Bs L x := ggFixedRealizedInL_of_config hL hP hcfg hInn
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  obtain ⟨y, hy⟩ := hres.1.2.2.2.1.2 K hK
  have hyB : y ∈ B := hy.1.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hyB
  have hKcomp : CFSG.Open.GLAPComponent p (Subgroup.centralizer ({y} : Set G)) K :=
    (CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent p _ K).mp hy.1.2.2.2.2.1
  have hrR : GGRealized p Bs r := ggRealized_of_reflRealizedIn hp hyBs hKcomp hR hrK hrefl
  obtain ⟨g, -, hg, rfl⟩ := eq_ggConjAut_of_mem_ggAutomizer (ggAutomizerJoin_le_top L Bs ks hψ)
  have hRt := hrR.conj hp hg
  exact hnot (hP3 _ (hrefl.conj' _) hRt.mem_ggInduced_top hxfix hRt)

theorem ggF4H5Core_holds
    : GGF4H5Core :=
  ggF4H5Core_of_pos

@[expose] def GGF4H5Large
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
      (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) →
        ∀ K ∈ ks, GGF4RowLarge p (L ⧸ Subgroup.center L) (K ⧸ Subgroup.center K) →
          GGReflRealizedIn p Bs K

theorem ggF4H5Seven_holds :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
        (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) →
          ∀ K ∈ ks, p = 3 → GGHasLabel ⟨.A, 3, 2⟩ (L ⧸ Subgroup.center L) →
            GGHasLabel ⟨.A, 6, 1⟩ (K ⧸ Subgroup.center K) → GGReflRealizedIn p Bs K := by
  intro G _ _ p B Bs x L D J ks hres _ K hK hp3 _ hKlab
  subst hp3
  obtain ⟨hp, hp2, hBs, hSC, hNT, hKperf, hN, ⟨y, hnb⟩, _⟩ :=
    ggF4H5Seven_premises hres hK
  let θSL : K ⧸ Subgroup.center K ≃* SL(7, ZMod 2) :=
    ggF4H5Seven_marking hKlab
  let e : SL(7, ZMod 2) ≃* projectiveSL 7 (ZMod 2) := ggSL7ToPSL7
  have hBsI : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut K (θSL.trans e) ⟨b, hN hb⟩ ∈
        Set.range (MulAut.conj :
          projectiveSL 7 (ZMod 2) →* MulAut (projectiveSL 7 (ZMod 2))) := by
    intro b hb
    obtain ⟨k, hk⟩ := ggF4H5Seven_image_inner (p := 3) rfl hBs hN θSL b hb
    refine ⟨e k, ?_⟩
    rw [NbrLangTypeA.ggLAut_trans θSL e ⟨b, hN hb⟩, ← hk, CFSG.mulAut_congr_conj]
  have hr : 3 ^ 3 ≤ Nat.card (ggGamma K hN).range :=
    pow_three_le_card_range_ggGamma_bstar hres.1.1.1 hnb hN
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma K hN).range := hr
  have hZ : Subgroup.center (projectiveSL 7 (ZMod 2)) = ⊥ :=
    CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 7) (k := ZMod 2)
      (by norm_num)
  have hclosed : GGCentrallyClosed (projectiveSL 7 (ZMod 2)) :=
    centrallyClosed_projectiveSL_seven_two
  have hcomp : GGKGComponentDatum 3 3 (projectiveSL 7 (ZMod 2)) :=
    ggKGComponentDatum_projectiveSL_seven
  have hT : GGTorusComponents 3 3 (projectiveSL 7 (ZMod 2))
      (Set.range (MulAut.conj :
        projectiveSL 7 (ZMod 2) →* MulAut (projectiveSL 7 (ZMod 2)))) :=
    ggTorusComponents_of_componentDatum (p := 3) (r := 3)
      (I := Set.range (MulAut.conj :
        projectiveSL 7 (ZMod 2) →* MulAut (projectiveSL 7 (ZMod 2))))
      Nat.prime_three (fun _ hx => hx) hZ hclosed hcomp
  exact ggReflRealizedIn_of_torusComponents (p := 3) (r := 3) (G := G)
    Nat.prime_three (by norm_num) hBs hSC hNT hKperf (θSL.trans e) hN hBsI hr h3 hT

theorem ggF4LabelH5_of_pieces
    (hcore : GGF4H5Core) (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hlarge : GGF4H5Large) : GGF4LabelH5 := by
  have hseven := ggF4H5Seven_holds
  intro G _ _ p B Bs x L D J ks hres hB K hK hrow
  have hc := hcore hL hP G p B Bs x L D J ks hres hB K hK
  rcases hrow with h | h | h | h | h | h | h
  · exact absurd (hlarge G p B Bs x L D J ks hres hB K hK (Or.inl h)) hc
  · exact absurd (hlarge G p B Bs x L D J ks hres hB K hK (Or.inr (Or.inl h))) hc
  · exact absurd (hlarge G p B Bs x L D J ks hres hB K hK (Or.inr (Or.inr (Or.inl h)))) hc
  · exact absurd (hlarge G p B Bs x L D J ks hres hB K hK
      (Or.inr (Or.inr (Or.inr (Or.inl h))))) hc
  · exact absurd (hlarge G p B Bs x L D J ks hres hB K hK
      (Or.inr (Or.inr (Or.inr (Or.inr h))))) hc
  · exact h
  · exact absurd (hseven G p B Bs x L D J ks hres hB K hK h.1 h.2.1 h.2.2) hc

end CFSG.StandardType

end
