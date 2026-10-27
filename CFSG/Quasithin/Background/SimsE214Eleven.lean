module

public import CFSG.Quasithin.Background.SimsE2Defs
public import CFSG.Quasithin.Background.E2Pair
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Quasithin.Vol2.Ch6Vocab
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

open scoped commutatorElement

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace E214E

variable {Γ : Type} [Group Γ]

theorem conjSubgroup_eq_conjSub_inv (V : Subgroup Γ) (g : Γ) :
    conjSubgroup V g = B6.conjSub g⁻¹ V := by
  ext x
  rw [mem_conjSubgroup_iff, B6.mem_conjSub, inv_inv]

variable [Finite Γ]

theorem pair_of_isInIHTV {H T M V I : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V)
    (hI : IsInIHTV H T M V I) (hg : g ∈ I) (hgen : I = V ⊔ conjSubgroup V g) :
    E2.Pair I (T ⊓ I) (M ⊓ I) V g⁻¹ := by
  have hVI : V ≤ I := by
    rw [hgen]
    exact le_sup_left
  refine ⟨hI.2.2.1, le_inf h.le_T hVI, inf_le_left.trans h.normal_T, h.elem,
    fun x hx => ⟨h.inf_normalizer_le ⟨hI.1 hx.1, hx.2⟩, hx.1⟩, inf_le_right, ?_, hI.2.2.2.1,
    I.inv_mem hg, by rw [← conjSubgroup_eq_conjSub_inv]; exact hgen⟩
  have hle : pCoreOf 2 M ⊓ I ≤ pCoreOf 2 (M ⊓ I) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (inf_le_inf_right I (CFSG.LieType.BorelTits.pCoreOf_le 2 M)) (fun x hx => ?_)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left)
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hx.1, Subgroup.le_normalizer hx.2⟩
  exact (le_inf h.le_pCoreOf hVI).trans hle

theorem commutator_sup_inf_eq {X T M V : Subgroup Γ} {g : Γ} (hp : E2.Pair X T M V g)
    {P : Subgroup Γ} (hBP : V ⊓ pCoreOf 2 X ≤ P) (hAP : B6.conjSub g V ⊓ pCoreOf 2 X ≤ P)
    (hPO : P ≤ pCoreOf 2 X) :
    ⁅V, P⁆ ⊔ (V ⊓ B6.conjSub g V) = V ⊓ pCoreOf 2 X := by
  have hBk : kerIn M X ⊓ V = V ⊓ pCoreOf 2 X := hp.kerIn_inf_eq
  have hAk : B6.conjSub g (kerIn M X ⊓ V) = B6.conjSub g V ⊓ pCoreOf 2 X :=
    hp.conjSub_kerIn_inf_eq
  have hZB : V ⊓ B6.conjSub g V ≤ V ⊓ pCoreOf 2 X := le_inf inf_le_left hp.inf_conj_le_pCoreOf
  have hVP : ⁅V, P⁆ ≤ V ⊓ pCoreOf 2 X := by
    rw [Subgroup.commutator_le]
    intro v hv x hx
    rw [commutatorElement_def, ← hBk]
    exact hp.commutator_mem_B hv (hPO hx)
  have hCB : ⁅V, P⁆ ⊔ (V ⊓ B6.conjSub g V) ≤ V ⊓ pCoreOf 2 X := sup_le hVP hZB
  refine le_antisymm hCB ?_
  set C := ⁅V, P⁆ ⊔ (V ⊓ B6.conjSub g V) with hC
  set W := C ⊔ (B6.conjSub g V ⊓ pCoreOf 2 X) with hW
  have hWP : W ≤ P := sup_le (hCB.trans hBP) hAP
  have hCW : C ≤ W := le_sup_left
  have hAW : B6.conjSub g V ⊓ pCoreOf 2 X ≤ W := le_sup_right
  have hVW : V ≤ Subgroup.normalizer (W : Set Γ) := by
    have key : ∀ u ∈ V, ∀ w ∈ W, u * w * u⁻¹ ∈ W := by
      intro u hu w hw
      have h1 : ⁅u, w⁆ ∈ W := hCW (le_sup_left (a := ⁅V, P⁆)
        (Subgroup.commutator_mem_commutator hu (hWP hw)))
      have e : u * w * u⁻¹ = ⁅u, w⁆ * w := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact W.mul_mem h1 hw
    exact fun v hv => B6.mem_normalizer_of_forall_mem (key v hv)
      (fun w hw => by simpa using key v⁻¹ (V.inv_mem hv) w hw)
  have hEW : B6.conjSub g V ≤ Subgroup.normalizer (W : Set Γ) := by
    have key : ∀ u ∈ B6.conjSub g V, ∀ w ∈ W, u * w * u⁻¹ ∈ W := by
      intro u hu w hw
      have h1 : u * w * u⁻¹ * w⁻¹ ∈ W := by
        have h2 := hp.commutator_mem_A hu (hPO (hWP hw))
        rw [hAk] at h2
        exact hAW h2
      have e : u * w * u⁻¹ = (u * w * u⁻¹ * w⁻¹) * w := by group
      rw [e]
      exact W.mul_mem h1 hw
    exact fun e he => B6.mem_normalizer_of_forall_mem (key e he)
      (fun w hw => by simpa using key e⁻¹ ((B6.conjSub g V).inv_mem he) w hw)
  have hXW : X ≤ Subgroup.normalizer (W : Set Γ) := by
    rw [hp.gen]
    exact sup_le hVW hEW
  have hBW : V ⊓ pCoreOf 2 X ≤ W := by
    intro b hb
    have hgb : g * b * g⁻¹ ∈ B6.conjSub g V ⊓ pCoreOf 2 X := by
      rw [← hAk, hBk, B6.mem_conjSub]
      simpa [mul_assoc] using hb
    have h1 := (Subgroup.mem_normalizer_iff.mp (hXW (X.inv_mem hp.mem)) _).mp (hAW hgb)
    simpa [mul_assoc] using h1
  have hAC : B6.conjSub g V ⊓ pCoreOf 2 X ≤ Subgroup.normalizer (C : Set Γ) := by
    have key : ∀ u ∈ B6.conjSub g V ⊓ pCoreOf 2 X, ∀ c ∈ C, u * c * u⁻¹ ∈ C := by
      intro u hu c hc
      have hcB : c ∈ kerIn M X ⊓ V := by
        rw [hBk]
        exact hCB hc
      have huA : u ∈ B6.conjSub g (kerIn M X ⊓ V) := by
        rw [hAk]
        exact hu
      have h1 := hp.commutator_B_A hcB huA
      have e : u * c * u⁻¹ = (c * u * c⁻¹ * u⁻¹)⁻¹ * c := by group
      rw [e]
      exact C.mul_mem (le_sup_right (a := ⁅V, P⁆) ((V ⊓ B6.conjSub g V).inv_mem h1)) hc
    exact fun a ha => B6.mem_normalizer_of_forall_mem (key a ha)
      (fun c hc => by simpa using key a⁻¹ ((B6.conjSub g V ⊓ pCoreOf 2 X).inv_mem ha) c hc)
  intro b hb
  have hbW : b ∈ ((W : Subgroup Γ) : Set Γ) := hBW hb
  rw [hW, Subgroup.coe_mul_of_right_le_normalizer_left C _ hAC] at hbW
  obtain ⟨c, hc, a, ha, hca⟩ := hbW
  have haB : a ∈ V ⊓ pCoreOf 2 X := by
    have e : a = c⁻¹ * b := by
      rw [← hca]
      group
    rw [e]
    exact (V ⊓ pCoreOf 2 X).mul_mem ((V ⊓ pCoreOf 2 X).inv_mem (hCB hc)) hb
  rw [← hca]
  exact C.mul_mem hc (le_sup_right (a := ⁅V, P⁆) ⟨haB.1, ha.1⟩)

end E214E

open E214E

theorem e214_eleven {Γ : Type} [Group Γ] [Finite Γ] (H T M V : Subgroup Γ)
    (h : E2.Hyp28 H T M V) : CharTwo H → IsTISetIn V M →
    ∀ (I : Subgroup Γ) (g : Γ), IsInIHTV H T M V I → g ∈ I → I = V ⊔ conjSubgroup V g →
      V ⊓ conjSubgroup V g ≠ ⊥ →
      ∀ (MI TI JI B A P Z : Subgroup Γ) (k : ℕ),
        MI = M ⊓ I → TI = T ⊓ I → JI = kerIn MI I → B = V ⊓ pCoreOf 2 I →
        A = conjSubgroup V g ⊓ pCoreOf 2 I → P = A ⊔ B → Z = V ⊓ conjSubgroup V g →
        E1.nParam (⊤ : Subgroup (E2.StarQuot MI I)) = (k : ℕ∞) →
        ⁅V, P⁆ ⊔ Z = B ⊔ Z := by
  intro _ _ I g hI hg hgen _ MI TI JI B A P Z k _ _ _ hB hA hP hZ _
  have hp := pair_of_isInIHTV h hI hg hgen
  subst hB hA hP hZ
  rw [conjSubgroup_eq_conjSub_inv V g, sup_eq_left.2 (le_inf inf_le_left hp.inf_conj_le_pCoreOf)]
  exact commutator_sup_inf_eq hp le_sup_right le_sup_left (sup_le inf_le_right inf_le_right)

theorem e214_eq_of_forall_commutator_mem {Γ : Type} [Group Γ] [Finite Γ] (H T M V : Subgroup Γ)
    (h : E2.Hyp28 H T M V) (I : Subgroup Γ) (g : Γ) (hI : IsInIHTV H T M V I) (hg : g ∈ I)
    (hgen : I = V ⊔ conjSubgroup V g) (B A P Z : Subgroup Γ) (hB : B = V ⊓ pCoreOf 2 I)
    (hA : A = conjSubgroup V g ⊓ pCoreOf 2 I) (hP : P = A ⊔ B) (hZ : Z = V ⊓ conjSubgroup V g)
    (Y : Subgroup Γ) (hZY : Z ≤ Y) (hYP : Y ≤ P) (hIY : I ≤ Subgroup.normalizer (Y : Set Γ))
    (htriv : ∀ i ∈ I, ∀ x ∈ P, i * x * i⁻¹ * x⁻¹ ∈ Y) : Y = P := by
  have hp := pair_of_isInIHTV h hI hg hgen
  subst hB hA hP hZ
  rw [conjSubgroup_eq_conjSub_inv V g] at hZY hYP htriv ⊢
  have hVI : V ≤ I := hp.V_le
  have hBY : V ⊓ pCoreOf 2 I ≤ Y := by
    rw [← commutator_sup_inf_eq hp le_sup_right le_sup_left (sup_le inf_le_right inf_le_right)]
    refine sup_le ?_ hZY
    rw [Subgroup.commutator_le]
    intro v hv x hx
    rw [commutatorElement_def]
    exact htriv v (hVI hv) x hx
  have hAY : B6.conjSub g⁻¹ V ⊓ pCoreOf 2 I ≤ Y := by
    intro a ha
    rw [← hp.conjSub_kerIn_inf_eq, hp.kerIn_inf_eq, B6.mem_conjSub, inv_inv] at ha
    exact (Subgroup.mem_normalizer_iff.mp (hIY hg) a).mpr (hBY ha)
  exact le_antisymm hYP (sup_le hAY hBY)

end CFSG.Quasithin.SimsE2
