module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import CFSG.LocalAnalysis.StandardType.FS81.S7Model
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainLift
public import Certificates.Certificate8064
public import CFSG.LocalAnalysis.StandardType.FS81.S7E7Incl
import CFSG.LocalAnalysis.StandardType.FS81.S7E7InclRange
import CFSG.LocalAnalysis.StandardType.FS81.S7ModelCent
import CFSG.LocalAnalysis.StandardType.FS81.S7ModelIdent
import CFSG.LocalAnalysis.StandardType.FS81.S7R120
import CFSG.LocalAnalysis.StandardType.FS81.S7AutAt
import CFSG.LocalAnalysis.StandardType.FS81.S7Fusion
import CFSG.LocalAnalysis.StandardType.FS81.RootD6ModelDefs
import CFSG.LocalAnalysis.StandardType.FS81.BasisMonomial
import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Neg

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "GF₂" => GaloisField 2 1
local notation "sθ" => rootThree Tag.E8 (GaloisField 2 1) (highRoot Tag.E8)
local notation "Dθ" => EPilot.perpLevi Tag.E8 (GaloisField 2 1)

open scoped Matrix

section Assembly


private theorem tE_single_frameE8_eq_rootThree (i : Fin (7 + 1)) :
    TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
      (Multiplicative.ofAdd (Pi.single i 1)) =
      rootThree .E8 GF₂ (TableBExcTwo.frameE8.root i) := by
  rw [TableBExcTwoTB.tE_apply]
  have hf : (fun j => Multiplicative.ofAdd ((Pi.single i 1 : Fin (7 + 1) → ZMod 3) j)) =
      Pi.mulSingle (M := fun _ : Fin (7 + 1) => Multiplicative (ZMod 3)) i
        (Multiplicative.ofAdd (1 : ZMod 3)) := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h, Pi.mulSingle_eq_of_ne h]
  rw [hf]
  unfold TableBExcTwoTB.tD
  rw [MonoidHom.noncommPiCoprod_mulSingle, TableBExcTwoTB.tC_one]
  apply Subtype.ext
  rw [coe_rootThree (TableBExcTwo.frameE8.isRoot i)]
  rfl

private theorem torusAct_redMod_frameE8 (w : WeylGroup .E8) (v : Fin Tag.E8.rank → ℤ) :
    TableBExc.torusAct .E8 3 w (TableBExc.redMod .E8 3 v) =
      TableBExc.redMod .E8 3 (w • v) := by
  rw [TableBExc.torusAct]
  exact TableBExc.redMod_smul_eq w (by rw [TableBExc.redMod_liftMod])

private theorem e7Incl_rootThree {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    e7Incl (rootThree .E7 (ZMod 2) γ) = rootThree .E8 GF₂ (E8Pilot.e7Embed γ) := by
  rw [rootThree, rootThree, map_mul, e7Incl_pinnedElt hγ, e7Incl_pinnedElt (IsRoot.neg hγ),
    show zmodTwoEquivGalois (1 : ZMod 2) = 1 from map_one _, E8Pilot.e7Embed_neg]

private theorem tE_single_mem_perpLevi {i : Fin (7 + 1)} (hi : i ≠ 0) :
    TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
      (Multiplicative.ofAdd (Pi.single i 1)) ∈ Dθ := by
  rw [tE_single_frameE8_eq_rootThree]
  have hperp : TableBExcTwo.frameE8.root i ∈ EPilot.perpRoots .E8 := by
    refine (EPilot.mem_perpRoots_iff_iform (Or.inr (Or.inr rfl))).mpr
      ⟨TableBExcTwo.frameE8.isRoot i, ?_⟩
    have h := TableBExcTwo.frameE8.orth 0 i (Ne.symm hi)
    rwa [show TableBExcTwo.frameE8.root 0 = highRoot .E8 from rfl] at h
  exact (Dθ).mul_mem (EPilot.pinnedElt_mem_perpLevi hperp 1)
    (EPilot.pinnedElt_mem_perpLevi (EPilot.neg_mem_perpRoots hperp) 1)

private theorem tE_coord_zero_mem_perpLevi (v : Fin (7 + 1) → ZMod 3) (hv : v 0 = 0) :
    TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8 (Multiplicative.ofAdd v) ∈ Dθ := by
  have hgen : ∀ i : Fin (7 + 1), TableBExcTwoTB.tGen GF₂ TableBExcTwo.frameE8 i =
      TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8 (Multiplicative.ofAdd (Pi.single i 1)) := by
    intro i
    rw [← TableBExcTwoTB.tC_one (K := GF₂) TableBExcTwo.frameE8 i]
    exact (TableBExcTwoTB.tE_single (K := GF₂) TableBExcTwo.frameE8 i 1).symm
  have hsingle : ∀ (i : Fin (7 + 1)) (c : ZMod 3),
      TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8 (Multiplicative.ofAdd (Pi.single i c)) =
        (TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
          (Multiplicative.ofAdd (Pi.single i 1))) ^ c.val := by
    intro i c
    rw [TableBExcTwoTB.tE_single, TableBExcTwoTB.tC_apply, hgen, toAdd_ofAdd]
  have hP : ∀ w : Fin (7 + 1) → ZMod 3, w 0 = 0 →
      TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8 (Multiplicative.ofAdd w) ∈ Dθ := by
    intro w hw
    have hdecomp : w = ∑ i : Fin (7 + 1), w i • (Pi.single i 1 : Fin (7 + 1) → ZMod 3) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro b _ hbj; rw [Pi.smul_apply, Pi.single_eq_of_ne hbj.symm, smul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hdecomp]
    have hsum : ∀ s : Finset (Fin (7 + 1)),
        TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
          (Multiplicative.ofAdd (∑ i ∈ s, w i • (Pi.single i 1 : Fin (7 + 1) → ZMod 3))) ∈
          Dθ := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, ofAdd_add, map_mul]
        refine (Dθ).mul_mem ?_ ih
        by_cases ha0 : a = 0
        · subst ha0
          simp [hw]
        · have hsing : w a • (Pi.single a 1 : Fin (7 + 1) → ZMod 3) = Pi.single a (w a) := by
            funext j
            by_cases hj : j = a <;> simp [Pi.smul_apply, hj]
          rw [hsing, hsingle a (w a)]
          exact Subgroup.pow_mem _ (tE_single_mem_perpLevi ha0) _
    exact hsum Finset.univ
  exact hP v hv


private theorem model_exists_conj_e7Incl
    {T : Subgroup (adjointGroup .E8 GF₂)}
    (hTab : IsElemAbelian 3 T) (hsT : sθ ∈ T) (hcardT : Nat.card T = 3 ^ 8)
    {x : adjointGroup .E8 GF₂} (hxD : x ∈ Dθ) (hxT : x ∈ T) (hx1 : x ≠ 1)
    (h120 : (normalizerLines ⊤ T x).ncard = 120) :
    ∃ g ∈ Dθ, ∃ r : ↥(adjointGroup .E7 (ZMod 2)),
      (r : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2) ∧ orderOf r = 3 ∧
        g * e7Incl r * g⁻¹ = x := by
  have hK : Nat.card GF₂ = 2 := natCard_galoisField_two_one
  have hTcent : T ≤ Subgroup.centralizer ({sθ} : Set (adjointGroup .E8 GF₂)) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hTab.1).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hsT))
  have hsT₀ : sθ ∈ frameTorusE8 GF₂ :=
    ⟨Multiplicative.ofAdd (Pi.single 0 1), tE_single_frameE8_eq_rootThree 0⟩
  have hT₀cent : frameTorusE8 GF₂ ≤
      Subgroup.centralizer ({sθ} : Set (adjointGroup .E8 GF₂)) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr
      (isElemAbelian_frameTorusE8 (K := GF₂)).1).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hsT₀))
  obtain ⟨d, hdD, hdmap⟩ :=
    exists_mem_perpLevi_map_conj_eq_of_le_centralizer_rootThree (K := GF₂) hK
      hTcent hT₀cent hTab (isElemAbelian_frameTorusE8 (K := GF₂)) hcardT
      (natCard_frameTorusE8 (K := GF₂))
  let x' := d * x * d⁻¹
  have hx'T₀ : x' ∈ frameTorusE8 GF₂ := by
    rw [← hdmap]
    exact ⟨x, hxT, rfl⟩
  have hx'D : x' ∈ Dθ := (Dθ).mul_mem ((Dθ).mul_mem hdD hxD) ((Dθ).inv_mem hdD)
  have hx'1 : x' ≠ 1 := by
    intro h1
    apply hx1
    calc x = d⁻¹ * x' * d := by simp only [x']; group
      _ = 1 := by rw [h1]; group
  have h120' : (normalizerLines ⊤ (frameTorusE8 GF₂) x').ncard = 120 := by
    have h := ncard_normalizerLines_map (ι := (MulAut.conj d).toMonoidHom)
      (MulAut.conj d).injective T x
    rw [MonoidHom.range_eq_top.mpr (MulAut.conj d).surjective, hdmap] at h
    rw [h120] at h
    simpa only [x', MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
  obtain ⟨u, hu⟩ := hx'T₀
  let a : Fin (7 + 1) → ZMod 3 := Multiplicative.toAdd u
  have hxa : TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8 (Multiplicative.ofAdd a) = x' := by
    change TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
      (Multiplicative.ofAdd (Multiplicative.toAdd u)) = x'
    rw [ofAdd_toAdd, hu]
  have ha : a ≠ 0 := by
    intro h0
    apply hx'1
    rw [← hxa, h0]
    simp
  have ha0 : a 0 = 0 := by
    have hDa : TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
        (Multiplicative.ofAdd a) ∈ Dθ := hxa ▸ hx'D
    let a' : Fin (7 + 1) → ZMod 3 := a - a 0 • (Pi.single 0 1 : Fin (7 + 1) → ZMod 3)
    have ha'0 : a' 0 = 0 := by simp [a']
    have ha'D : TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
        (Multiplicative.ofAdd a') ∈ Dθ := tE_coord_zero_mem_perpLevi a' ha'0
    have hdecomp : a = a 0 • (Pi.single 0 1 : Fin (7 + 1) → ZMod 3) + a' := by
      funext j
      simp only [a', Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      abel
    have hsingle : TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
        (Multiplicative.ofAdd (a 0 • (Pi.single 0 1 : Fin (7 + 1) → ZMod 3))) =
        sθ ^ (a 0).val := by
      have hsing : a 0 • (Pi.single 0 1 : Fin (7 + 1) → ZMod 3) = Pi.single 0 (a 0) := by
        funext j
        by_cases hj : j = 0 <;> simp [Pi.smul_apply, hj]
      have hgen0 : TableBExcTwoTB.tGen GF₂ TableBExcTwo.frameE8 0 = sθ := by
        rw [← TableBExcTwoTB.tC_one (K := GF₂) TableBExcTwo.frameE8 0,
          ← TableBExcTwoTB.tE_single (K := GF₂) TableBExcTwo.frameE8 0 1]
        simpa only [show TableBExcTwo.frameE8.root 0 = highRoot .E8 from rfl]
          using tE_single_frameE8_eq_rootThree 0
      rw [hsing, TableBExcTwoTB.tE_single, TableBExcTwoTB.tC_apply, hgen0, toAdd_ofAdd]
    have hDs : sθ ^ (a 0).val ∈ Dθ := by
      rw [← hsingle]
      have h1 : TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
          (Multiplicative.ofAdd (a 0 • (Pi.single 0 1 : Fin (7 + 1) → ZMod 3) + a')) =
          TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
            (Multiplicative.ofAdd (a 0 • (Pi.single 0 1 : Fin (7 + 1) → ZMod 3))) *
          TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8 (Multiplicative.ofAdd a') := by
        rw [ofAdd_add, map_mul]
      rw [← hdecomp] at h1
      have h2 : TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
          (Multiplicative.ofAdd (a 0 • (Pi.single 0 1 : Fin (7 + 1) → ZMod 3))) =
          TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8 (Multiplicative.ofAdd a) *
            (TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8 (Multiplicative.ofAdd a'))⁻¹ := by
        rw [h1]; group
      rw [h2]
      exact (Dθ).mul_mem hDa ((Dθ).inv_mem ha'D)
    have hmem1 : sθ ^ (a 0).val = 1 := by
      have hmem : sθ ^ (a 0).val ∈ Subgroup.zpowers sθ ⊓ Dθ :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers_iff.mpr
          ⟨((a 0).val : ℤ), by rw [zpow_natCast]⟩, hDs⟩
      exact Subgroup.mem_bot.mp
        ((disjoint_zpowers_rootThree_perpLevi_E8 (K := GF₂)).le_bot hmem)
    have h3 : (a 0).val = 0 := by
      have hdvd : orderOf sθ ∣ (a 0).val := orderOf_dvd_iff_pow_eq_one.mpr hmem1
      rw [orderOf_rootThree (isRoot_highRoot .E8)] at hdvd
      have hlt := ZMod.val_lt (a 0)
      omega
    exact (ZMod.val_eq_zero (a 0)).mp h3
  have hbound : Set.ncard {u : Fin Tag.E8.rank → ZMod 3 |
      ∃ w : WeylGroup .E8, u = TableBExc.torusAct .E8 3 w
        (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 a)} ≤ 240 := by
    have h := ncard_orbit_frameCoord_le (K := GF₂) hK a ha
    calc _ ≤ 2 * (normalizerLines ⊤ (frameTorusE8 GF₂)
          (TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8 (Multiplicative.ofAdd a))).ncard := h
      _ = 2 * (normalizerLines ⊤ (frameTorusE8 GF₂) x').ncard := by rw [hxa]
      _ = 240 := by rw [h120']
  have hv : ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 a ≠ 0 := by
    intro h0
    exact ha (frameCoordHom_frameE8_injective (by rw [h0, map_zero]))
  obtain ⟨w, hw⟩ := eq_torusAct_frameCoord_of_ncard_le
    (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 a) hv hbound
  let ρ : Fin Tag.E8.rank → ℤ := w • highRoot .E8
  have hρroot : IsRoot .E8 ρ := IsRoot.smul (isRoot_highRoot .E8) w
  have hΛe0 : ExcFrameIso.frameCoordHom TableBExcTwo.frameE8
      (Pi.single 0 1 : Fin (7 + 1) → ZMod 3) = TableBExc.redMod .E8 3 (highRoot .E8) := by
    rw [ExcFrameIso.frameCoordHom_single]
    simp [show TableBExcTwo.frameE8.root 0 = highRoot .E8 from rfl]
  have hpair0 : ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 a ⬝ᵥ
      (NoTvAut.cartanMod .E8 3 *ᵥ ExcFrameIso.frameCoordHom TableBExcTwo.frameE8
        (Pi.single 0 1 : Fin (7 + 1) → ZMod 3)) = 0 := by
    rw [ExcFrameIso.frameCoordHom_form TableBExcTwo.frameE8.symm_one]
    have hdot : a ⬝ᵥ (Pi.single 0 1 : Fin (7 + 1) → ZMod 3) = a 0 := by
      simp only [dotProduct, Pi.single_apply]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ 0) h
    rw [hdot, ha0, mul_zero]
  have hsmulform (ε : ZMod 3) :
      (ε • TableBExc.redMod .E8 3 ρ) ⬝ᵥ
        (NoTvAut.cartanMod .E8 3 *ᵥ TableBExc.redMod .E8 3 (highRoot .E8)) =
        ε * ((CFSG.LieType.Steinberg.Adjoint.iform ρ (highRoot .E8) : ℤ) : ZMod 3) := by
    rw [smul_dotProduct, smul_eq_mul, NoTvAut.redMod_form,
      CFSG.LieType.Chevalley.dotProduct_mulVec_eq_iform]
  have hε : ((CFSG.LieType.Steinberg.Adjoint.iform ρ (highRoot .E8) : ℤ) : ZMod 3) = 0 := by
    rcases hw with hw | hw
    · have hΛ : ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 a =
          TableBExc.redMod .E8 3 ρ := by
        rw [hw, hΛe0, torusAct_redMod_frameE8]
      have h1 : (TableBExc.redMod .E8 3 ρ) ⬝ᵥ (NoTvAut.cartanMod .E8 3 *ᵥ
          TableBExc.redMod .E8 3 (highRoot .E8)) =
          ((CFSG.LieType.Steinberg.Adjoint.iform ρ (highRoot .E8) : ℤ) : ZMod 3) := by
        simpa using hsmulform (1 : ZMod 3)
      rw [hΛ, hΛe0, h1] at hpair0
      simpa using hpair0
    · have hΛ : ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 a =
          - TableBExc.redMod .E8 3 ρ := by
        rw [hw, hΛe0, torusAct_redMod_frameE8]
      have hneg : (- TableBExc.redMod .E8 3 ρ) =
          (-1 : ZMod 3) • TableBExc.redMod .E8 3 ρ := by simp
      rw [hΛ, hΛe0, hneg, hsmulform (-1 : ZMod 3)] at hpair0
      simpa using hpair0
  have h0iform : CFSG.LieType.Steinberg.Adjoint.iform ρ (highRoot .E8) = 0 := by
    have hdvd : (3 : ℤ) ∣ CFSG.LieType.Steinberg.Adjoint.iform ρ (highRoot .E8) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd
        (CFSG.LieType.Steinberg.Adjoint.iform ρ (highRoot .E8)) 3).mp hε
    obtain ⟨k, hk⟩ := hdvd
    have hle := E8Pilot.abs_iform_le_two hρroot (isRoot_highRoot .E8)
    rw [hk] at hle
    have hk0 : k = 0 := by
      have h1 : (3 : ℤ) * |k| ≤ 2 := by
        simpa [abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 3)] using hle
      have h2 : (0 : ℤ) ≤ |k| := abs_nonneg k
      have h3 : |k| = 0 := by omega
      exact abs_eq_zero.mp h3
    rw [hk0, mul_zero] at hk
    exact hk
  have hρperp : ρ ∈ EPilot.perpRoots .E8 :=
    (EPilot.mem_perpRoots_iff_iform (Or.inr (Or.inr rfl))).mpr
      ⟨hρroot, by rw [CFSG.LieType.Steinberg.Adjoint.iform_comm]; exact h0iform⟩
  obtain ⟨γ, hγroot, hγeq⟩ := E8Pilot.exists_e7Embed_eq_of_mem_perpRoots hρperp
  have hroot1_perp : TableBExcTwo.frameE8.root 1 ∈ EPilot.perpRoots .E8 := by
    refine (EPilot.mem_perpRoots_iff_iform (Or.inr (Or.inr rfl))).mpr
      ⟨TableBExcTwo.frameE8.isRoot 1, ?_⟩
    have h := TableBExcTwo.frameE8.orth 0 1 (by decide)
    rwa [show TableBExcTwo.frameE8.root 0 = highRoot .E8 from rfl] at h
  obtain ⟨γ₁, hγ₁root, hγ₁eq⟩ := E8Pilot.exists_e7Embed_eq_of_mem_perpRoots hroot1_perp
  obtain ⟨w₁, hw₁⟩ := EPilot.exists_smul_highRoot_eq (Or.inr (Or.inl rfl)) hγ₁root
  obtain ⟨w₂, hw₂⟩ := EPilot.exists_smul_highRoot_eq (Or.inr (Or.inl rfl)) hγroot
  let w₇ : WeylGroup .E7 := w₂ * w₁⁻¹
  have hw₇ : w₇ • γ₁ = γ := by
    rw [← hw₁, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one, hw₂]
  obtain ⟨ω, hω⟩ := (coxeterSystem Tag.E7).wordProd_surjective w₇
  have hword : ∀ l : List (Fin (Tag.rank .E7)),
      (l.map E8Pilot.e7Node).foldr (reflect .E8) (highRoot .E8) = highRoot .E8 ∧
      ∀ v, (l.map E8Pilot.e7Node).foldr (reflect .E8) (E8Pilot.e7Embed v) =
        E8Pilot.e7Embed (l.foldr (reflect .E7) v) := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      constructor
      · rw [List.map_cons, List.foldr_cons, ih.1]
        exact CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.reflect_highRoot_of_ne
          .E8 (E8Pilot.e7Node i) (E8Pilot.e7Node_ne_highNode i)
      · intro v
        rw [List.map_cons, List.foldr_cons, ih.2, List.foldr_cons, E8Pilot.e7Embed_reflect]
  have hfix : ((coxeterSystem .E8).wordProd (ω.map E8Pilot.e7Node)) • highRoot .E8 =
      highRoot .E8 := by
    rw [CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.wordProd_smul_foldr]
    exact (hword ω).1
  have hmap : ((coxeterSystem .E8).wordProd (ω.map E8Pilot.e7Node)) • E8Pilot.e7Embed γ₁ = ρ := by
    rw [CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.wordProd_smul_foldr]
    have h := (hword ω).2 γ₁
    rw [← CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.wordProd_smul_foldr
      (τ := .E7) (l := ω) (v := γ₁)] at h
    rw [hω, hw₇, hγeq] at h
    exact h
  obtain ⟨n, hnN, hkey⟩ := exists_mem_normalizer_frameTorusE8_torusAct (K := GF₂) hK
    ((coxeterSystem .E8).wordProd (ω.map E8Pilot.e7Node))
  obtain ⟨v₀, hv₀, hΛv₀⟩ := hkey (Pi.single 0 1 : Fin (7 + 1) → ZMod 3)
  have hΛv₀' : ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 v₀ =
      ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 (Pi.single 0 1 : Fin (7 + 1) → ZMod 3) := by
    rw [hΛv₀, hΛe0, torusAct_redMod_frameE8, hfix]
  have hv₀eq : v₀ = Pi.single 0 1 := frameCoordHom_frameE8_injective hΛv₀'
  have hn_s : n * sθ * n⁻¹ = sθ := by
    have h1 : sθ = TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
        (Multiplicative.ofAdd (Pi.single 0 1)) := by
      simpa only [show TableBExcTwo.frameE8.root 0 = highRoot .E8 from rfl]
        using (tE_single_frameE8_eq_rootThree 0).symm
    rw [h1]
    simpa only [hv₀eq] using hv₀
  have hncent : n ∈ Subgroup.centralizer ({sθ} : Set (adjointGroup .E8 GF₂)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (mul_inv_eq_iff_eq_mul.mp hn_s).symm
  obtain ⟨k, d', hd'D, hn_eq⟩ :=
    exists_zpow_mul_of_mem_centralizer_rootThree (K := GF₂) hK hncent
  obtain ⟨v₁, hv₁, hΛv₁⟩ := hkey (Pi.single 1 1 : Fin (7 + 1) → ZMod 3)
  have hΛv₁' : ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 v₁ =
      TableBExc.redMod .E8 3 ρ := by
    rw [hΛv₁, ExcFrameIso.frameCoordHom_single]
    simp only [ZMod.val_one, one_smul]
    rw [torusAct_redMod_frameE8]
    rw [← hγ₁eq, hmap]
  have hsT₀' : sθ ∈ frameTorusE8 GF₂ := hsT₀
  have hT₀ab := (isElemAbelian_frameTorusE8 (K := GF₂)).1
  have hv₁T₀ : TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
      (Multiplicative.ofAdd v₁) ∈ frameTorusE8 GF₂ := ⟨_, rfl⟩
  have hcent_v₁ : frameTorusE8 GF₂ ≤
      Subgroup.centralizer (Set.singleton (TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
        (Multiplicative.ofAdd v₁)) : Set (adjointGroup .E8 GF₂)) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr
      (isElemAbelian_frameTorusE8 (K := GF₂)).1).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv₁T₀))
  have hcomm_eq : TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8 (Multiplicative.ofAdd v₁) *
      sθ ^ k = sθ ^ k * TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
        (Multiplicative.ofAdd v₁) :=
    Subgroup.mem_centralizer_iff.mp (hcent_v₁ (Subgroup.zpow_mem _ hsT₀' k)) _ rfl
  have hd'_conj : d' * TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
      (Multiplicative.ofAdd (Pi.single 1 1)) * d'⁻¹ =
      TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8 (Multiplicative.ofAdd v₁) := by
    calc d' * TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
            (Multiplicative.ofAdd (Pi.single 1 1)) * d'⁻¹
        = (sθ ^ k)⁻¹ * (n * TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
            (Multiplicative.ofAdd (Pi.single 1 1)) * n⁻¹) * (sθ ^ k) := by
          have hd'_eq : d' = (sθ ^ k)⁻¹ * n := by rw [hn_eq]; group
          rw [hd'_eq]; group
      _ = (sθ ^ k)⁻¹ * TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
            (Multiplicative.ofAdd v₁) * (sθ ^ k) := by rw [hv₁]
      _ = TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8 (Multiplicative.ofAdd v₁) := by
          rw [mul_assoc, hcomm_eq]; group
  have hmemr₀ : ((rootThree .E7 (ZMod 2) (highRoot .E7) : adjointGroup .E7 (ZMod 2)) :
      ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2) := by
    rw [coe_rootThree (isRoot_highRoot .E7)]
    exact E6Pilot.rootSL2_highRoot_mem_highRootSL2 (K := ZMod 2) (uSL 1 * vSL 1)
  have hordr₀ : orderOf (rootThree .E7 (ZMod 2) (highRoot .E7) : adjointGroup .E7 (ZMod 2)) = 3 :=
    orderOf_rootThree (isRoot_highRoot .E7)
  obtain ⟨g₇, hg₇⟩ := exists_conj_rootThree_eq (K := ZMod 2) (Or.inr (Or.inl rfl))
    (isRoot_highRoot .E7) hγ₁root
  have hφconj : e7Incl g₇ * e7Incl (rootThree .E7 (ZMod 2) (highRoot .E7)) * (e7Incl g₇)⁻¹ =
      TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8 (Multiplicative.ofAdd (Pi.single 1 1)) := by
    rw [← map_mul, ← map_inv, ← map_mul, hg₇, e7Incl_rootThree hγ₁root, hγ₁eq,
      ← tE_single_frameE8_eq_rootThree 1]
  have hmemDg₇ : e7Incl g₇ ∈ Dθ := by
    rw [← range_e7Incl]; exact ⟨g₇, rfl⟩
  have hφconj_inv : e7Incl g₇ * (e7Incl (rootThree .E7 (ZMod 2) (highRoot .E7)))⁻¹ *
      (e7Incl g₇)⁻¹ =
      (TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8 (Multiplicative.ofAdd (Pi.single 1 1)))⁻¹ := by
    rw [← hφconj]; group
  have hx : x = d⁻¹ * x' * d := by simp only [x']; group
  rcases hw with hw | hw
  · have hΛ : ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 a =
        TableBExc.redMod .E8 3 ρ := by
      rw [hw, hΛe0, torusAct_redMod_frameE8]
    have hav : a = v₁ := frameCoordHom_frameE8_injective (by rw [hΛ, hΛv₁'])
    have hx'v : x' = TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
        (Multiplicative.ofAdd v₁) := by rw [← hxa, hav]
    refine ⟨d⁻¹ * d' * e7Incl g₇, ?_, rootThree .E7 (ZMod 2) (highRoot .E7), hmemr₀, hordr₀, ?_⟩
    · exact (Dθ).mul_mem ((Dθ).mul_mem ((Dθ).inv_mem hdD) hd'D) hmemDg₇
    · calc (d⁻¹ * d' * e7Incl g₇) * e7Incl (rootThree .E7 (ZMod 2) (highRoot .E7)) *
            (d⁻¹ * d' * e7Incl g₇)⁻¹
          = d⁻¹ * (d' * (e7Incl g₇ * e7Incl (rootThree .E7 (ZMod 2) (highRoot .E7)) *
              (e7Incl g₇)⁻¹) * d'⁻¹) * d := by group
        _ = d⁻¹ * (d' * TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
              (Multiplicative.ofAdd (Pi.single 1 1)) * d'⁻¹) * d := by rw [hφconj]
        _ = d⁻¹ * TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
              (Multiplicative.ofAdd v₁) * d := by rw [hd'_conj]
        _ = d⁻¹ * x' * d := by rw [hx'v]
        _ = x := by rw [hx]
  · have hΛ : ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 a =
        - TableBExc.redMod .E8 3 ρ := by
      rw [hw, hΛe0, torusAct_redMod_frameE8]
    have hav : a = -v₁ := frameCoordHom_frameE8_injective (by rw [hΛ, map_neg, hΛv₁'])
    have hx'v : x' = (TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
        (Multiplicative.ofAdd v₁))⁻¹ := by rw [← hxa, hav, ofAdd_neg, map_inv]
    refine ⟨d⁻¹ * d' * e7Incl g₇, ?_, (rootThree .E7 (ZMod 2) (highRoot .E7))⁻¹,
      Subgroup.inv_mem _ hmemr₀, ?_, ?_⟩
    · exact (Dθ).mul_mem ((Dθ).mul_mem ((Dθ).inv_mem hdD) hd'D) hmemDg₇
    · rw [orderOf_inv, hordr₀]
    · calc (d⁻¹ * d' * e7Incl g₇) * e7Incl ((rootThree .E7 (ZMod 2) (highRoot .E7))⁻¹) *
            (d⁻¹ * d' * e7Incl g₇)⁻¹
          = d⁻¹ * (d' * (e7Incl g₇ * (e7Incl (rootThree .E7 (ZMod 2) (highRoot .E7)))⁻¹ *
              (e7Incl g₇)⁻¹) * d'⁻¹) * d := by rw [map_inv]; group
        _ = d⁻¹ * (d' * (TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
              (Multiplicative.ofAdd (Pi.single 1 1)))⁻¹ * d'⁻¹) * d := by rw [hφconj_inv]
        _ = d⁻¹ * (TableBExcTwoTB.tE GF₂ TableBExcTwo.frameE8
              (Multiplicative.ofAdd v₁))⁻¹ * d := by rw [← hd'_conj]; group
        _ = d⁻¹ * x' * d := by rw [hx'v]
        _ = x := by rw [hx]

private theorem normalizerLines_eq_of_zpowers_eq {G : Type} [Group G] {H E : Subgroup G} {u v : G}
    (h : Subgroup.zpowers u = Subgroup.zpowers v) :
    normalizerLines H E u = normalizerLines H E v := by
  ext Z
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : Subgroup.zpowers (g * u * g⁻¹) = Subgroup.zpowers (g * v * g⁻¹) := by
      have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h
      simpa only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this
    exact ⟨g, hg, hg'⟩
  · rintro ⟨g, hg, rfl⟩
    have hg' : Subgroup.zpowers (g * v * g⁻¹) = Subgroup.zpowers (g * u * g⁻¹) := by
      have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h.symm
      simpa only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this
    exact ⟨g, hg, hg'⟩

private theorem normalizerLines_conj_eq {G : Type} [Group G] {H E : Subgroup G} {x a : G}
    (ha : a ∈ H ⊓ Subgroup.normalizer (E : Set G)) :
    normalizerLines H E (a * x * a⁻¹) = normalizerLines H E x := by
  have haH : a ∈ H := (Subgroup.mem_inf.mp ha).1
  have haN : a ∈ Subgroup.normalizer (E : Set G) := (Subgroup.mem_inf.mp ha).2
  ext Z
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hgH : g ∈ H := (Subgroup.mem_inf.mp hg).1
    have hgN : g ∈ Subgroup.normalizer (E : Set G) := (Subgroup.mem_inf.mp hg).2
    refine ⟨g * a, Subgroup.mem_inf.mpr ⟨H.mul_mem hgH haH,
      (Subgroup.normalizer (E : Set G)).mul_mem hgN haN⟩, ?_⟩
    show Subgroup.zpowers (g * (a * x * a⁻¹) * g⁻¹) =
      Subgroup.zpowers ((g * a) * x * (g * a)⁻¹)
    congr 1
    group
  · rintro ⟨g, hg, rfl⟩
    have hgH : g ∈ H := (Subgroup.mem_inf.mp hg).1
    have hgN : g ∈ Subgroup.normalizer (E : Set G) := (Subgroup.mem_inf.mp hg).2
    refine ⟨g * a⁻¹, Subgroup.mem_inf.mpr ⟨H.mul_mem hgH (H.inv_mem haH),
      (Subgroup.normalizer (E : Set G)).mul_mem hgN
        ((Subgroup.normalizer (E : Set G)).inv_mem haN)⟩, ?_⟩
    show Subgroup.zpowers (g * x * g⁻¹) =
      Subgroup.zpowers ((g * a⁻¹) * (a * x * a⁻¹) * (g * a⁻¹)⁻¹)
    congr 1
    group


theorem exists_mem_perpLevi_conj_e7Incl_eq {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G (Row.twD7.n + 1)} {Y : Subgroup G}
    (h : RootSetting Row.twD7 b₀ K E B Y) (ι : adjointGroup .E8 GF₂ →* G)
    (hι : Function.Injective ι) (hrange : ι.range = Y) (hβ : ι sθ = b₀ * B.b 1)
    (hℓ : b₀ * (B.b 1)⁻¹ ∈ (Dθ).map ι) :
    ∃ g ∈ Dθ, ∃ r : ↥(adjointGroup .E7 (ZMod 2)),
      (r : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2) ∧ orderOf r = 3 ∧
        ι (g * e7Incl r * g⁻¹) = b₀ * (B.b 1)⁻¹ := by
  have hEab : IsElemAbelian 3 E := h.std.2.1.2.1.2.1
  have hEcard : Nat.card E = 3 ^ 8 := by
    rw [h.std.2.1.2.2.2.1]
    norm_num [Row.m, Row.n]
  have hEι : E ≤ ι.range := by
    rw [hrange]
    exact RootSetting.torus_le h
  have hβE : b₀ * B.b 1 ∈ E := by
    have h0 : b₀ ∈ E := by
      rw [← h.adapted.2.1]
      exact h.adapted.1 ▸ B.b_mem_span 0
    exact E.mul_mem h0 (h.adapted.1 ▸ B.b_mem_span 1)
  have hℓE : b₀ * (B.b 1)⁻¹ ∈ E := by
    refine E.mul_mem ?_ (E.inv_mem ?_)
    · rw [← h.adapted.2.1]
      exact h.adapted.1 ▸ B.b_mem_span 0
    · exact h.adapted.1 ▸ B.b_mem_span 1
  obtain ⟨ℓ₀, hℓ₀D, hℓ₀eq⟩ := Subgroup.mem_map.mp hℓ
  let T : Subgroup (adjointGroup .E8 GF₂) := E.comap ι
  have hTmap : T.map ι = E := Subgroup.map_comap_eq_self hEι
  have hsT : sθ ∈ T := by
    rw [Subgroup.mem_comap, hβ]
    exact hβE
  have hℓ₀T : ℓ₀ ∈ T := by
    rw [Subgroup.mem_comap, hℓ₀eq]
    exact hℓE
  have hb1 : (B.b 1) ^ 2 = (B.b 1)⁻¹ := by
    have h3 : (B.b 1) ^ 3 = 1 := by
      simpa [B.ord 1] using pow_orderOf_eq_one (B.b 1)
    have h2 : (B.b 1) ^ 2 * B.b 1 = 1 := by
      rw [← pow_succ]
      exact h3
    exact eq_inv_of_mul_eq_one_left h2
  have hvec : B.vec ((Pi.single 0 1 : Coords (Row.twD7.n + 1)) + Pi.single 1 (-1)) =
      b₀ * (B.b 1)⁻¹ := by
    have hv1 : (1 : ZMod 3).val = 1 := by decide
    have hvm1 : (-1 : ZMod 3).val = 2 := by decide
    rw [B.vec_add, B.vec_single_eq_pow, B.vec_single_eq_pow, h.adapted.2.1, hv1, hvm1, hb1,
      pow_one]
  let e : Coords (Row.twD7.n + 1) := Pi.single 0 1 + Pi.single 1 (-1)
  have hℓ1 : b₀ * (B.b 1)⁻¹ ≠ 1 := by
    intro h1
    have h0 : B.vec e = B.vec 0 := by
      rw [show e = (Pi.single 0 1 : Coords (Row.twD7.n + 1)) + Pi.single 1 (-1) from rfl,
        hvec, h1, B.vec_zero]
    have hc : e 0 ≠ 0 := by decide
    exact hc (congrFun (B.vec_injective h0) 0)
  have hℓ₀1 : ℓ₀ ≠ 1 := by
    intro h1
    exact hℓ1 (by rw [← hℓ₀eq, h1, map_one])
  have hcardT : Nat.card T = 3 ^ 8 := by
    rw [← Subgroup.card_map_of_injective (K := T) (f := ι) hι, hTmap, hEcard]
  have hTab : IsElemAbelian 3 T := isElemAbelian_comap ι hι hEab
  have he : e ≠ 0 := by decide
  have hwte : wt e = 2 := by decide
  have hline : B.line e = Subgroup.zpowers (b₀ * (B.b 1)⁻¹) := by
    rw [Basis3.line, hvec]
  have hconj : IsConjLineIn B.span (b₀ * B.b 1) (Subgroup.zpowers (b₀ * (B.b 1)⁻¹)) := by
    rw [← hline]
    exact (h.recOut.2.2 e he).mpr (Or.inl hwte)
  obtain ⟨g, hgN, hgline⟩ := hconj
  have hgN' : g ∈ Subgroup.normalizer (E : Set G) := by
    rwa [← h.adapted.1]
  have hA : Nat.card (ggAutomizer Y E) = Nat.card (ggAutomizer ⊤ E) :=
    e8AutAt_twD7 G b₀ K E B Y h
  obtain ⟨y, hyY, hyN, c, hcC, hgc⟩ := exists_mul_of_card_ggAutomizer_eq hA hgN'
  have hcβ : c * (b₀ * B.b 1) * c⁻¹ = b₀ * B.b 1 := by
    have hcomm : (b₀ * B.b 1) * c = c * (b₀ * B.b 1) :=
      Subgroup.mem_centralizer_iff.mp hcC _ hβE
    rw [← hcomm]
    group
  have hβconj : Subgroup.zpowers (y * (b₀ * B.b 1) * y⁻¹) =
      Subgroup.zpowers (b₀ * (B.b 1)⁻¹) := by
    rw [← hgline]
    congr 1
    rw [hgc]
    rw [show (y * c) * (b₀ * B.b 1) * (y * c)⁻¹ =
      y * (c * (b₀ * B.b 1) * c⁻¹) * y⁻¹ by group, hcβ]
  have h120β : (normalizerLines Y E (b₀ * B.b 1)).ncard = 120 :=
    ncard_normalizerLines_eq_120_twD7 h (e8AutAt_twD7 G b₀ K E B Y h)
  have hyK : y ∈ Y ⊓ Subgroup.normalizer (E : Set G) := Subgroup.mem_inf.mpr ⟨hyY, hyN⟩
  have hnormalizer_eq : normalizerLines Y E (b₀ * (B.b 1)⁻¹) = normalizerLines Y E (b₀ * B.b 1) :=
    (normalizerLines_eq_of_zpowers_eq hβconj).symm.trans (normalizerLines_conj_eq hyK)
  have h120ℓ : (normalizerLines Y E (b₀ * (B.b 1)⁻¹)).ncard = 120 := by
    rw [hnormalizer_eq, h120β]
  have h120T : (normalizerLines ⊤ T ℓ₀).ncard = 120 := by
    have hh := ncard_normalizerLines_map ι hι T ℓ₀
    rw [hrange, hTmap, hℓ₀eq] at hh
    rw [h120ℓ] at hh
    exact hh.symm
  obtain ⟨g, hgD, r, hr, hr3, hgr⟩ :=
    model_exists_conj_e7Incl hTab hsT hcardT hℓ₀D hℓ₀T hℓ₀1 h120T
  exact ⟨g, hgD, r, hr, hr3, by rw [hgr, hℓ₀eq]⟩


end Assembly

end CFSG.StandardType.FrameRoute.FS81

end
