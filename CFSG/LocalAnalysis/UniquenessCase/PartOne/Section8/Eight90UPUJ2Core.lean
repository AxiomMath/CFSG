module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90UJ2FF
import CFSG.Quasithin.Background.E6Gamma
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.OpCoreSylow
import CFSG.Sporadic.SmallOddCore.J2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.ABGLocalTools (IsSylowOf)

private theorem k90upc_charTwo_of_fstar {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hF : Fstar H = pCoreOf 2 H) : CFSG.QuasithinUnique.CharTwo H := by
  rintro y ⟨hyH, hyc⟩
  have hc : (⟨y, hyH⟩ : ↥H) ∈
      Subgroup.centralizer (CFSG.Open.genFittingFStar ↥H : Set ↥H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : (w : G) ∈ pCoreOf 2 H := by
      rw [← hF]
      exact Subgroup.mem_map_of_mem _ hw
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hyc) _ hw')
  rw [← hF]
  exact Subgroup.mem_map_of_mem H.subtype
    (CFSG.Adapters.generalized_fitting_self_centralizing ↥H hc)

theorem r890u_puCore_reduced {G : Type} [Group G] [Finite G] {L R : Subgroup G}
    (hR : IsSylowOf 2 R (L ⊔ R)) (hF : Fstar (L ⊔ R) = pCoreOf 2 (L ⊔ R)) :
    CFSG.Quasithin.IsTwoReducedIn (L ⊔ R)
      (CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter R) (L ⊔ R)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRX, hR2, hodd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hR
  exact CFSG.Quasithin.isTwoReducedIn_conjClosure_of_sylowIn hRX hR2 hodd
    (k90upc_charTwo_of_fstar hF) le_rfl

theorem r890u_puCore_noncentral
    {G : Type} [Group G] [Finite G] {L R V : Subgroup G}
    (hJ : IsSpor (Bar2 L) .J2) (hR : IsSylowOf 2 R (L ⊔ R))
    (hLn : (L.subgroupOf (L ⊔ R)).Normal) (hred : CFSG.Quasithin.IsTwoReducedIn (L ⊔ R) V)
    (hVL : ⁅V, L⁆ ≠ ⊥) :
    CFSG.Quasithin.baum R = CFSG.Quasithin.baum (pCoreOf 2 (L ⊔ R)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hLX : L ≤ L ⊔ R := le_sup_left
  have hn : L ⊔ R ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).1 hLn
  have hT : CFSG.QuasithinUnique.IsSylowTwoOf R (L ⊔ R) :=
    CFSG.ABGLocalTools.isSylowOf_iff.1 hR
  have hQR : pCoreOf 2 (L ⊔ R) ≤ R :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section12.pCoreOf_le_of_isSylowOf hR
  have hLT : ∀ x ∈ L ⊔ R, ∃ l ∈ L, ∃ t ∈ R, x = l * t := by
    intro x hx
    have hx' : x ∈ (↑(L ⊔ R) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L R (le_sup_right.trans hn)] at hx'
    obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.1 hx'
    exact ⟨l, hl, t, ht, rfl⟩
  have hLq : CFSG.IsQuasisimple (Bar2 L) ∨ Nat.card (Bar2 L) = 3 := by
    left
    obtain ⟨e⟩ := hJ
    let e' : Bar2 L ≃* CFSG.Blueprint.NativeSporadic.J2 := e
    have : IsSimpleGroup (Bar2 L) :=
      @MulEquiv.isSimpleGroup (Bar2 L) _ (CFSG.Blueprint.NativeSporadic.J2) _
        CFSG.Sporadic.J2.isSimpleGroup_J2 e'
    have hnab : ∃ a b : Bar2 L, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := CFSG.Sporadic.SmallOddCore.j2_not_comm
      refine ⟨e'.symm a, e'.symm b, fun h => hab ?_⟩
      calc a * b = e' (e'.symm a) * e' (e'.symm b) := by simp
        _ = e' (e'.symm a * e'.symm b) := by rw [map_mul]
        _ = e' (e'.symm b * e'.symm a) := by rw [h]
        _ = e' (e'.symm b) * e' (e'.symm a) := by rw [map_mul]
        _ = b * a := by simp
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  obtain ⟨-, -, hF, hcase⟩ :=
    CFSG.Quasithin.C124.B2_10_2 hV hred hQR le_rfl hT hLX hn hLT hVL hLq
  rcases hcase with hbaum | ⟨hstab, -, -⟩
  · exact hbaum
  · exfalso
    obtain ⟨A, hA⟩ := hstab.1
    have hFF : CFSG.Quasithin.IsFFModule (CFSG.Quasithin.autI hV (L ⊔ R)) :=
      CFSG.Quasithin.IsFFStarOffender.isFFModule (hstab.2.1 A hA)
    have hO2X : CFSG.pCore 2 ↥(CFSG.Quasithin.autI hV (L ⊔ R)) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (CFSG.Quasithin.autI hV (L ⊔ R)).subtype_injective).1
        (CFSG.Quasithin.C124.pCoreOf_autI_eq_bot hV hred)
    have hLV : ¬ L ≤ Subgroup.centralizer (V : Set G) := fun h => hVL (by
      rw [← Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact h)
    have hLJ : Nonempty (↥(CFSG.Quasithin.autI hV L) ≃* CFSG.Blueprint.NativeSporadic.J2) :=
      r890u_nonempty_autI_mulEquiv_J2 hV (hLX.trans hred.2.1)
        (CFSG.Quasithin.C124.pCoreOf_autI_L_eq_bot hV hred hLX hn) hLV hJ
    exact absurd hFF
      (r890u_not_isFFModule_of_fstar_J2 (W := CFSG.Quasithin.IntMod V hV)
        (fun w => by simpa [pow_two] using CFSG.Quasithin.IntMod.sq_eq_one w)
        hF.symm hO2X hLJ)

private theorem k90upc_omegaOneCenter_le_center {G : Type} [Group G] (T : Subgroup G) :
    CFSG.Quasithin.omegaOneCenterOf T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1

private theorem k90upc_omegaOneCenter_le_baum {G : Type} [Group G] (T : Subgroup G) :
    CFSG.Quasithin.omegaOneCenterOf T ≤ CFSG.Quasithin.baum T := by
  intro z hz
  have hz' := k90upc_omegaOneCenter_le_center T hz
  exact ⟨hz'.1, Subgroup.centralizer_le
    ((CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le (CFSG.Quasithin.thompsonJ T)).trans
      (iSup₂_le fun _ hA => hA.1)) hz'.2⟩

private theorem k90upc_ne_bot {G : Type} [Group G] [Finite G]
    {L R : Subgroup G} (hJ : IsSpor (Bar2 L) .J2)
    (hodd : ¬ 2 ∣ R.relIndex (L ⊔ R)) : R ≠ ⊥ := by
  intro hbot
  obtain ⟨e⟩ := hJ
  have hcard : Nat.card (Bar2 L) = 604800 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  have h2Bar : 2 ∣ Nat.card (Bar2 L) := by rw [hcard]; norm_num
  have h2L : 2 ∣ Nat.card ↥L := h2Bar.trans (Subgroup.card_quotient_dvd_card (pCore 2 ↥L))
  have h2LR : 2 ∣ Nat.card ↥(L ⊔ R) := h2L.trans (Subgroup.card_dvd_of_le le_sup_left)
  have hrel : R.relIndex (L ⊔ R) = Nat.card ↥(L ⊔ R) := by
    rw [hbot, Subgroup.relIndex_bot_left]
  exact hodd (hrel ▸ h2LR)

theorem puJ2Core_890_holds :
    PUJ2Core_890 := by
  intro _ _ G _ _ L R _ hJ hR hLn hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hR2, hodd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hR
  set V : Subgroup G :=
    CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter R) (L ⊔ R)
  have hred : CFSG.Quasithin.IsTwoReducedIn (L ⊔ R) V := r890u_puCore_reduced hR hF
  set Z : Subgroup G := CFSG.Quasithin.omegaOneCenterOf R
  have hZ1 : Z ≠ ⊥ :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hR2 (k90upc_ne_bot hJ hodd)
  have hNZ : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Z : Set G) :=
    CFSG.Quasithin.E6.normalizer_le_normalizer_of_char
      (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le R)
      (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf R)
  by_cases hVL : ⁅V, L⁆ = ⊥
  · refine ⟨Z, hZ1, CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le R, hNZ,
      sup_le ?_ (Subgroup.le_normalizer.trans hNZ)⟩
    have hLV : ⁅L, V⁆ = ⊥ := (Subgroup.commutator_comm L V).trans hVL
    have hLcV : L ≤ Subgroup.centralizer (V : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLV
    calc L ≤ Subgroup.centralizer (V : Set G) := hLcV
      _ ≤ Subgroup.centralizer (Z : Set G) :=
          Subgroup.centralizer_le (CFSG.Quasithin.le_conjClosure _ _)
      _ ≤ Subgroup.normalizer (Z : Set G) := Subgroup.centralizer_le_normalizer _
  · have hB := r890u_puCore_noncentral hJ hR hLn hred hVL
    refine ⟨CFSG.Quasithin.baum R, ?_, inf_le_left,
      CFSG.Quasithin.E6.normalizer_le_normalizer_of_char inf_le_left
        (CFSG.Quasithin.C1GN.characteristic_baum R), ?_⟩
    · have hZle : Z ≤ CFSG.Quasithin.baum R := k90upc_omegaOneCenter_le_baum R
      exact fun hb => hZ1 (le_bot_iff.mp (hb ▸ hZle))
    · rw [hB]
      exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) (L ⊔ R)).trans
        (CFSG.Quasithin.E6.normalizer_le_normalizer_of_char inf_le_left
          (CFSG.Quasithin.C1GN.characteristic_baum (pCoreOf 2 (L ⊔ R))))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
