module

public import CFSG.Milestones.ASVolI.C137.Cases
public import CFSG.Milestones.ASVolI.C137.G2Blk
public import CFSG.Quasithin.H13.GoldschmidtC137SQFinal
public import CFSG.Quasithin.MS93.MResOrd
public import CFSG.Quasithin.MS93.Burnside.Sp4HDesc
public import CFSG.Milestones.ASVolI.C137.G2Mark
public import CFSG.Milestones.ASVolI.C137.Setup
public import CFSG.Quasithin.H13.GoldschmidtC137U33Pt3
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Fin

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
  CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.U3 CFSG.Quasithin.H13.U3.GC137
open CFSG.Quasithin.H13 (ModQ g2QAct g2QAct_injective G2NaturalCover G2DerivedNormalizerZorn
  card_ModQ)

variable {G : Type} [Group G]

@[expose] def burnsideC137_Concl4 (X L P V U : Subgroup G) : Prop :=
  IsG2Two ↥(autOn X V) ∧
    InternalG2TwoNatural X V U (U ⊓ Subgroup.centralizer (L : Set G)) ∧
    (U ⊓ Subgroup.centralizer (L : Set G)).relIndex U = 2 ^ 6 ∧
    IsIrrSection X (U ⊓ Subgroup.centralizer (L : Set G)) U ∧
    ∃ l : Subgroup G, U ⊓ Subgroup.centralizer (L : Set G) ≤ l ∧ l ≤ U ∧
      (U ⊓ Subgroup.centralizer (L : Set G)).relIndex l = 4 ∧
      P = X ⊓ Subgroup.normalizer (l : Set G)

section Cfg

variable [Finite G] {X T U L P M : Subgroup G} (h : U33Cfg X T U L P M)
  (E : Entry33 X T U L (pCoreOf 2 P) h.hVe)
  (hF : G2Facts (autI h.hVe X) (autI h.hVe L))

include h E hF

theorem burnsideC137_u33_isG2Block {A : Subgroup (MulAut (IntMod U h.hVe))}
    (hA : PtA (autI h.hVe X) (autI h.hVe P) A)
    {c : MulAut (IntMod U h.hVe)} (hc : c ∈ autI h.hVe L)
    (hLc : autI h.hVe L ≤ A ⊔ B1.conjAut c A)
    (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32)
    (hn1 : ∀ C : Subgroup G, C ≤ baum (pCoreOf 2 P) → C ≠ ⊥ →
      (C.subgroupOf (baum (pCoreOf 2 P))).Characteristic → ¬ X ≤ normalizer (C : Set G)) :
    IsG2Block L := by
  have hC : ∀ B, ¬ IsStrongFFStarOffender (autI h.hVe (pCoreOf 2 P)) B := h.no_strong E hA
  have hDE := h.hDE_u33 E hA hc hLc hF.rk_L
  obtain ⟨hCV, -⟩ := b2_19_rel h.hVe h.hred.1 h.hXN h.toBaum.hLeq.symm
    (pCoreOf_isPGroup 2 P) h.hRX h.hVR h.toBaum.hA1 h.toBaum.hA2 h.toBaum.hA3 h.toBaum.hB hC hDE
  obtain ⟨hMS, hLcomp, hset⟩ := h.isMSPair_u33 E hF hA hn1 hCV
  have h132 := hC132 G (L ⊔ baum (pCoreOf 2 P)) (baum (pCoreOf 2 P)) L hMS hLcomp hset
  exact isG2Block_of_c132 (card_of_psu33 h.hlie) h132

theorem burnsideC137_u33_marking (hcov : G2NaturalCover) (hnorm : G2DerivedNormalizerZorn)
    (hfacts : U33G2Facts) :
    burnsideC137_G2Marking (autI h.hVe X) (fixV (autI h.hVe L)) := by
  obtain ⟨hnat, hcomm⟩ := h.natural_of_entry E hF
  obtain ⟨A, hA⟩ : ∃ A, IsFFStarOffender (autI h.hVe X) A := by
    obtain ⟨A, hA⟩ := E.stab.1
    exact ⟨A, E.stab.2.1 A hA⟩
  exact burnsideC137_g2Marking hcov hnorm hfacts IntMod.sq_eq_one (autI_mono h.hVe h.hLX)
    (autI_le_normalizer h.hVe E.normal) hcomm hnat E.card ⟨A, hA⟩

theorem burnsideC137_u33_concl4 (hcov : G2NaturalCover) (hnorm : G2DerivedNormalizerZorn)
    (hfacts : U33G2Facts) {V : Subgroup G} (hV : IsElemAbelian 2 V) (hUV : U ≤ V)
    (hXV : X ≤ normalizer (V : Set G))
    (hC : X ⊓ centralizer (U : Set G) = X ⊓ centralizer (V : Set G))
    (hl : G2Line (autI h.hVe L) (autI h.hVe P)) :
    burnsideC137_Concl4 X L P V U := by
  have hU := h.hVe
  have hXU : X ≤ normalizer (U : Set G) := h.hXN
  have hLU : L ≤ normalizer (U : Set G) := h.hLN
  have hXZ : X ≤ normalizer ((U ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 (hXU hx) y
    have h2 := Subgroup.mem_normalizer_iff.1 (burnsideC137_mem_normalizer_centralizer (h.hn hx)) y
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  obtain ⟨f, hfs, hfk, hfaith, hX, hX'⟩ := burnsideC137_u33_marking h E hF hcov hnorm hfacts
  have hfk' : ∀ w : IntMod U h.hVe, f w = 1 ↔ w.val ∈ U ⊓ centralizer (L : Set G) := by
    intro w
    rw [hfk, mem_fixV_autI h.hVe hLU w]
    exact ⟨fun h1 => ⟨w.val_mem, h1⟩, fun h1 => h1.2⟩
  have hG2 : IsG2Two ↥(autOn X V) :=
    burnsideC137_isG2Two_of_mulEquiv (burnsideC137_autIEquiv h.hVe hV hXU hXV hC)
      (h.isG2Two_Y E hF)
  have hD := FFModel.zornQ_isActionModel (quasithinG2 (ZMod 2)) le_rfl
  have hinj : Function.Injective hD.modAct := g2QAct_injective
  have hmem : ∀ x : ↥X, convHom h.hVe X hXU x ∈ autI h.hVe X := fun x => by
    rw [← range_convHom h.hVe X hXU]
    exact ⟨x, rfl⟩
  have hnat : InternalG2TwoNatural X V U (U ⊓ centralizer (L : Set G)) := by
    refine burnsideC137_ims_of_marking hD hinj h.hVe inf_le_left hUV hXU hXZ hC f hfs hfk'
      (fun x hx => hfaith _ (hmem x) hx) (fun x => hX _ (hmem x)) fun δ => ?_
    obtain ⟨φ, hφ, hφδ⟩ := hX' δ
    rw [← range_convHom h.hVe X hXU] at hφ
    obtain ⟨x, rfl⟩ := hφ
    exact ⟨x, hφδ⟩
  have hidx : (U ⊓ centralizer (L : Set G)).relIndex U = 2 ^ 6 := by
    rw [burnsideC137_relIndex_of_surj h.hVe f hfs hfk', card_ModQ]
    norm_num
  have hcomm : commV (autI h.hVe L) = ⊤ := commV_autI_eq_top h.hVe hLU h.hVL
  have hirr := E.case1i.1.2.2.2
  rw [hcomm] at hirr
  have hirrX : IsIrrSection X (U ⊓ centralizer (L : Set G)) U :=
    burnsideC137_isIrrSection_of_isIrrSec h.hVe h.hLX hXU h.hn hirr
  obtain ⟨l', hl1, hl2, hl3⟩ := hl
  set l : Subgroup G := l'.map (C124.blkVal h.hVe) with hldef
  have hZl : U ⊓ centralizer (L : Set G) ≤ l := by
    intro x hx
    have hw : IntMod.mk h.hVe ⟨x, hx.1⟩ ∈ fixV (autI h.hVe L) :=
      (mem_fixV_autI h.hVe hLU _).2 hx.2
    exact ⟨_, hl1 hw, rfl⟩
  have hlU : l ≤ U := by
    rintro _ ⟨w, -, rfl⟩
    exact w.val_mem
  have hcardl : Nat.card ↥l = 4 * Nat.card ↥(U ⊓ centralizer (L : Set G)) := by
    rw [hldef, Subgroup.card_map_of_injective (C124.blkVal_injective h.hVe), hl2,
      card_fixV_autI h.hVe hLU]
  have hidxl : (U ⊓ centralizer (L : Set G)).relIndex l = 4 := by
    have h1 := Subgroup.relIndex_mul_card (U ⊓ centralizer (L : Set G)) l
    rw [inf_eq_left.2 hZl, hcardl] at h1
    have hpos : 0 < Nat.card ↥(U ⊓ centralizer (L : Set G)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hPl : P ≤ X ⊓ normalizer (l : Set G) := by
    have hPN : ∀ q ∈ P, q ∈ normalizer (U : Set G) := fun q hq => h.hXN (h.hPX.le hq)
    have hfwd : ∀ q ∈ P, ∀ x ∈ l, q * x * q⁻¹ ∈ l := by
      rintro q hq _ ⟨w, hw, rfl⟩
      have hφ := hl3 (convI h.hVe ⟨q, hPN q hq⟩) (convI_mem_autI h.hVe hq (hPN q hq)) w hw
      refine ⟨_, hφ, ?_⟩
      rw [C124.blkVal_apply, C124.blkVal_apply, convI_apply_val]
    intro p hp
    refine ⟨h.hPX.le hp, Subgroup.mem_normalizer_iff.2 fun x => ⟨hfwd p hp x, fun hx => ?_⟩⟩
    have := hfwd p⁻¹ (P.inv_mem hp) _ hx
    simpa [mul_assoc] using this
  have hPeq : P = X ⊓ normalizer (l : Set G) := by
    rcases h.hmax (X ⊓ normalizer (l : Set G)) (h.hPeq ▸ hPl) inf_le_left with h1 | h1
    · rw [h1, h.hPeq]
    · exfalso
      have hXl : X ≤ normalizer (l : Set G) := by
        rw [← h1]
        exact inf_le_right
      rcases hirrX.2.2.2 l hZl hlU hXl with h2 | h2
      · rw [← h2] at hidxl
        rw [Subgroup.relIndex_self] at hidxl
        omega
      · rw [h2] at hidxl
        rw [hidxl] at hidx
        norm_num at hidx
  exact ⟨hG2, hnat, hidx, hirrX, l, hZl, hlU, hidxl, hPeq⟩

end Cfg

section Canonical

set_option linter.unusedSectionVars false


theorem burnsideC137_caseU33
    : burnsideC137_CaseU33 := by
  intro G _ _ X T L P M V hyp hpsu
  obtain ⟨hXLT, hT, hL, hX, -, -, hTP, hPM, hM, hPeq, hred, hVL, -⟩ := hyp
  have hprod := burnsideC137_prod hXLT
  have hL2 := burnsideC137_charTwo_L hL hX
  have hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 := Or.inl ⟨by decide, hpsu⟩
  obtain ⟨hMX, hmax⟩ := burnsideC137_max hM
  have hP : P = M := hPeq.resolve_right fun h =>
    not_hatA6_of_psu33 hlie ⟨h.1.1.1, h.1.2.1, h.1.2.2⟩
  have hSQ : SQTKGroup ↥X :=
    c137SQTKSupply_holds G X T L hX hT hprod hL hL2 (Or.inr (Or.inr (Or.inr hlie)))
  obtain ⟨hredU, hUU, hCeq⟩ := u33_reduce hred hT hprod hL hlie hVL
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hUV : ⁅V, L⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hLX.trans hred.2.1)
  have cfg : U33Cfg X T ⁅V, L⁆ L P M :=
    ⟨hSQ, hX, hT, hprod, hL, hL2, hlie, hTP, hPM, hMX, hmax, hP, hredU, hUU, hVL⟩
  have hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32 :=
    MS93.MRes.asC132_of_descSp4 MS93.S4L.burnsideSp4H_s34RDescSp4
  rcases entry33_or_concl1
      (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)
      asA21SQTKSection asA36NoOddCover_holds hX hSQ hredU hT hprod hL hL2 cfg.hVL' hlie
      cfg.toBaum.hQR cfg.toBaum.hRT with ⟨C, hC0, hCle, hCchar, hCn⟩ | E
  · exact Or.inl ⟨C, hC0, hCle, hCchar, hCn⟩
  · have hF := g2Facts_of_entry33 H13.VolI.g2NaturalCover_holds H13.g2DerivedNormalizerZorn
      u33G2Facts_holds E hUU
    rcases hF.dichotomy _ _ cfg.sylow_T cfg.T_le_P cfg.P_le_X cfg.P_ne_X cfg.P_max with hl | hp
    · exact Or.inr (Or.inr (Or.inr (Or.inl (burnsideC137_u33_concl4 cfg E hF
        H13.VolI.g2NaturalCover_holds H13.g2DerivedNormalizerZorn u33G2Facts_holds
        hred.2.2.1 hUV hred.2.1 hCeq hl))))
    · by_cases hcn : ∃ D : Subgroup G, D ≠ ⊥ ∧ D ≤ baum (pCoreOf 2 P) ∧
          (D.subgroupOf (baum (pCoreOf 2 P))).Characteristic ∧
          X ≤ Subgroup.normalizer (D : Set G)
      · exact Or.inl hcn
      · obtain ⟨A, hA, c, hc, hLc⟩ := hp.exists_PtA
        have hB := burnsideC137_u33_isG2Block cfg E hF hA hc hLc hC132
          fun C hCle hC0 hchar hXC => hcn ⟨C, hC0, hCle, hchar, hXC⟩
        refine Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr (burnsideC137_isG2TwoBlockNatural hB))),
          fun hH => ?_⟩)
        exact (not_hatA6_of_psu33 hlie ⟨hH.2.1.1.1, hH.2.1.2.1, hH.2.1.2.2⟩).elim

end Canonical

end CFSG.ASVolI
