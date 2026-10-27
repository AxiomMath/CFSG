module

public import CFSG.Quasithin.Background.SimsE214Eleven
public import CFSG.Quasithin.Background.SimsE215Two
public import CFSG.Quasithin.Background.SimsE215KF1Defs
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.DedekindNormalizer
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImages
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallerRecognitionDischarge
public import CFSG.Quasithin.Vol2.Ch3E213MSp4Irr

public section

namespace CFSG.Quasithin.SimsE2.KF1

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section ConjComm

variable {Γ : Type} [Group Γ]

theorem isMulCommutative_conjSubgroup {V : Subgroup Γ} (hV : IsMulCommutative ↥V) (g : Γ) :
    IsMulCommutative ↥(conjSubgroup V g) := by
  refine IsMulCommutative.of_comm fun x y => Subtype.ext ?_
  change (x : Γ) * (y : Γ) = (y : Γ) * (x : Γ)
  have hx : g * (x : Γ) * g⁻¹ ∈ V := (mem_conjSubgroup_iff).mp x.2
  have hy : g * (y : Γ) * g⁻¹ ∈ V := (mem_conjSubgroup_iff).mp y.2
  have hcomm := hV.is_comm.comm (⟨g * (x : Γ) * g⁻¹, hx⟩ : V)
    ⟨g * (y : Γ) * g⁻¹, hy⟩
  have hval : (g * (x : Γ) * g⁻¹) * (g * (y : Γ) * g⁻¹) =
      (g * (y : Γ) * g⁻¹) * (g * (x : Γ) * g⁻¹) := by
    simpa using congrArg Subtype.val hcomm
  calc (x : Γ) * (y : Γ)
      = g⁻¹ * ((g * (x : Γ) * g⁻¹) * (g * (y : Γ) * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * (y : Γ) * g⁻¹) * (g * (x : Γ) * g⁻¹)) * g := by rw [hval]
    _ = (y : Γ) * (x : Γ) := by group

theorem inf_conjSubgroup_le_centralizer_sup {V : Subgroup Γ} (hV : IsElemAbelian 2 V) (g : Γ) :
    V ⊓ conjSubgroup V g ≤
      Subgroup.centralizer (((V ⊔ conjSubgroup V g : Subgroup Γ) : Set Γ)) := by
  set Z : Subgroup Γ := V ⊓ conjSubgroup V g with hZ
  have hZV : Z ≤ Subgroup.centralizer (V : Set Γ) :=
    (inf_le_left : Z ≤ V).trans (Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1)
  have hZE : Z ≤ Subgroup.centralizer (conjSubgroup V g : Set Γ) :=
    (inf_le_right : Z ≤ conjSubgroup V g).trans
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        (isMulCommutative_conjSubgroup hV.1 g))
  have h1 : V ≤ Subgroup.centralizer (Z : Set Γ) := Subgroup.le_centralizer_iff.mpr hZV
  have h2 : conjSubgroup V g ≤ Subgroup.centralizer (Z : Set Γ) :=
    Subgroup.le_centralizer_iff.mpr hZE
  exact Subgroup.le_centralizer_iff.mp (sup_le h1 h2)

end ConjComm

section Member

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem commutator_sup_eq_of_isInIHTV {H T M V I : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V)
    (hI : IsInIHTV H T M V I) (hg : g ∈ I) (hgen : I = V ⊔ conjSubgroup V g) :
    ⁅V, (conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I)⁆ ⊔ (V ⊓ conjSubgroup V g) =
      V ⊓ pCoreOf 2 I := by
  have hp := E214E.pair_of_isInIHTV h hI hg hgen
  have h := E214E.commutator_sup_inf_eq (X := I) (T := T ⊓ I) (M := M ⊓ I) (V := V)
    (g := g⁻¹) hp (P := (conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I))
    le_sup_right (by rw [← E214E.conjSubgroup_eq_conjSub_inv V g]; exact le_sup_left)
    (sup_le inf_le_right inf_le_right)
  rwa [E214E.conjSubgroup_eq_conjSub_inv V g] at h

end Member

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem conjSubgroup_inf_pCoreOf_eq_bot {V : Subgroup X} {g : X} (hV : Nat.card V = 2)
    (hg : g ∈ V ⊔ conjSubgroup V g) (hI : ¬ IsPGroup 2 ↥(V ⊔ conjSubgroup V g)) :
    conjSubgroup V g ⊓ pCoreOf 2 (V ⊔ conjSubgroup V g) = ⊥ := by
  set I : Subgroup X := V ⊔ conjSubgroup V g with hIdef
  by_contra hne
  have hcardE : Nat.card (conjSubgroup V g) = 2 := by
    unfold conjSubgroup
    rw [Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g⁻¹)), hV]
  have hAdvd : Nat.card ↥(conjSubgroup V g ⊓ pCoreOf 2 I) ∣ 2 := by
    rw [← hcardE]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hAcard : Nat.card ↥(conjSubgroup V g ⊓ pCoreOf 2 I) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hAdvd with h1 | h2
    · exact absurd (Subgroup.eq_bot_of_card_eq (conjSubgroup V g ⊓ pCoreOf 2 I) h1) hne
    · exact h2
  have hAeq : conjSubgroup V g ⊓ pCoreOf 2 I = conjSubgroup V g :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hAcard, hcardE])
  have hle : conjSubgroup V g ≤ pCoreOf 2 I := hAeq ▸ inf_le_right
  have hVP : V ≤ pCoreOf 2 I := by
    intro x hx
    have hy : g⁻¹ * x * g ∈ conjSubgroup V g := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hx
    have hx' : g * (g⁻¹ * x * g) * g⁻¹ ∈ pCoreOf 2 I :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I hg) _).mp (hle hy)
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at hx'
  have hIle : I ≤ pCoreOf 2 I := by
    rw [hIdef]
    exact sup_le hVP hle
  have hIeq : I = pCoreOf 2 I := le_antisymm hIle (CFSG.LieType.BorelTits.pCoreOf_le 2 I)
  exact hI (hIeq.symm ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I)

theorem commutator_conjSubgroup_inf_pCoreOf_eq_bot {T V : Subgroup X} {g : X}
    (hT : IsSylowTwoOf (T ⊓ (V ⊔ conjSubgroup V g)) (V ⊔ conjSubgroup V g))
    (hV : V ≤ Subgroup.centralizer ((T ⊓ (V ⊔ conjSubgroup V g) : Subgroup X) : Set X)) :
    ⁅conjSubgroup V g ⊓ pCoreOf 2 (V ⊔ conjSubgroup V g), V⁆ = ⊥ := by
  have hPI : pCoreOf 2 (V ⊔ conjSubgroup V g) ≤ T ⊓ (V ⊔ conjSubgroup V g) :=
    hT.le_of_normalizes (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact (le_trans (inf_le_right.trans hPI) (Subgroup.le_centralizer_iff.mp hV))

theorem commutator_conjSubgroup_inf_pCoreOf_eq_bot_of_normal {T V F₀ : Subgroup X}
    (hF : F₀.Normal) (hVF : V ≤ F₀)
    (hV : V ≤ Subgroup.centralizer ((T ⊓ F₀ : Subgroup X) : Set X)) {g : X}
    (hT : IsSylowTwoOf (T ⊓ (V ⊔ conjSubgroup V g)) (V ⊔ conjSubgroup V g)) :
    ⁅conjSubgroup V g ⊓ pCoreOf 2 (V ⊔ conjSubgroup V g), V⁆ = ⊥ := by
  have hEg : conjSubgroup V g ≤ F₀ := by
    intro x hx
    have hx' : g * x * g⁻¹ ∈ V := (mem_conjSubgroup_iff).mp hx
    have h1 := hF.conj_mem (g * x * g⁻¹) (hVF hx') g⁻¹
    have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [h2] at h1
  have hIF : V ⊔ conjSubgroup V g ≤ F₀ := sup_le hVF hEg
  refine commutator_conjSubgroup_inf_pCoreOf_eq_bot (g := g) hT ?_
  exact hV.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (inf_le_inf_left T hIF)))

end Abstract

section Targets

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem commutator_sup_inf_le_pCoreOf_inf_of_kf1 {H V I : Subgroup Γ} {g : Γ}
    (hgen : I = V ⊔ conjSubgroup V g)
    (hKF1 : ⁅(conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I), I⁆ ≤ pCoreOf 2 H) :
    ⁅V, (conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I)⁆ ≤ pCoreOf 2 H ⊓ I := by
  have hVI : V ≤ I := by
    rw [hgen]
    exact le_sup_left
  have hPleI : (conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I) ≤ I :=
    sup_le (inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I))
      (inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I))
  refine le_inf ?_ ?_
  · calc ⁅V, (conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I)⁆ ≤
        ⁅I, (conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I)⁆ :=
        Subgroup.commutator_mono_left hVI
      _ = ⁅(conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I), I⁆ :=
        Subgroup.commutator_comm I _
      _ ≤ pCoreOf 2 H := hKF1
  · exact (Subgroup.commutator_le_sup V _).trans (sup_le hVI hPleI)

omit [Finite Γ] in
theorem inf_conjSubgroup_le_pCoreOf {V : Subgroup Γ} {g : Γ} (hV : IsElemAbelian 2 V) :
    V ⊓ conjSubgroup V g ≤ pCoreOf 2 (V ⊔ conjSubgroup V g) := by
  set Z : Subgroup Γ := V ⊓ conjSubgroup V g with hZ
  have hZI : Z ≤ Subgroup.centralizer (((V ⊔ conjSubgroup V g : Subgroup Γ) : Set Γ)) :=
    inf_conjSubgroup_le_centralizer_sup hV g
  have hZI_le : Z ≤ V ⊔ conjSubgroup V g := (inf_le_left : Z ≤ V).trans le_sup_left
  have hZnorm : (Z.subgroupOf (V ⊔ conjSubgroup V g)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hZI_le]
    intro z i hz hi
    have hcomm := Subgroup.mem_centralizer_iff.mp (hZI hz) i hi
    rw [show i * z * i⁻¹ = z by
      rw [hcomm]
      group]
    exact hz
  have hZ2 : IsPGroup 2 Z := (CFSG.Open.IsElemAbelian.isPGroup hV).to_le inf_le_left
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 hZI_le hZnorm hZ2

theorem conjSubgroup_inf_pCoreOf_le_sup_of_kf1 {H T M V I : Subgroup Γ} {g : Γ}
    (h : E2.Hyp28 H T M V) (hI : IsInIHTV H T M V I) (hg : g ∈ I)
    (hgen : I = V ⊔ conjSubgroup V g)
    (hKF1 : ⁅(conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I), I⁆ ≤ pCoreOf 2 H) :
    conjSubgroup V g ⊓ pCoreOf 2 I ≤ (pCoreOf 2 H ⊓ I) ⊔ (V ⊓ conjSubgroup V g) := by
  set A : Subgroup Γ := conjSubgroup V g ⊓ pCoreOf 2 I with hA
  set B : Subgroup Γ := V ⊓ pCoreOf 2 I with hB
  set Z : Subgroup Γ := V ⊓ conjSubgroup V g with hZ
  set N : Subgroup Γ := pCoreOf 2 H ⊓ I with hN
  have hVP_le_N : ⁅V, A ⊔ B⁆ ≤ N :=
    commutator_sup_inf_le_pCoreOf_inf_of_kf1 (H := H) (V := V) (I := I) hgen hKF1
  have hB_le : B ≤ N ⊔ Z := by
    have hlem : ⁅V, A ⊔ B⁆ ⊔ Z = B := commutator_sup_eq_of_isInIHTV h hI hg hgen
    rw [← hlem]
    exact sup_le (hVP_le_N.trans le_sup_left) le_sup_right
  have hPIfix : conjSubgroup (pCoreOf 2 I) g = pCoreOf 2 I :=
    (conjSubgroup_eq_iff_mem_normalizer).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I hg)
  have hA_eq : A = conjSubgroup B g := by
    rw [hB, E3.conjSubgroup_inf, hPIfix]
  have hO2H_fix : conjSubgroup (pCoreOf 2 H) g = pCoreOf 2 H :=
    (conjSubgroup_eq_iff_mem_normalizer).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hI.1 hg))
  have hI_fix : conjSubgroup I g = I :=
    (conjSubgroup_eq_iff_mem_normalizer).mpr (Subgroup.le_normalizer hg)
  have hN_fix : conjSubgroup N g = N := by
    rw [hN, E3.conjSubgroup_inf, hO2H_fix, hI_fix]
  have hZI : Z ≤ Subgroup.centralizer (I : Set Γ) := by
    rw [hgen]
    exact inf_conjSubgroup_le_centralizer_sup h.elem g
  have hgZ : g ∈ Subgroup.centralizer (Z : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hZI hz) g hg).symm
  have hZ_fix : conjSubgroup Z g = Z :=
    (conjSubgroup_eq_iff_mem_normalizer).mpr
      (Subgroup.centralizer_le_normalizer (Z : Set Γ) hgZ)
  have hsup : conjSubgroup (N ⊔ Z) g = conjSubgroup N g ⊔ conjSubgroup Z g := by
    simp only [conjSubgroup, Subgroup.map_sup]
  rw [hA_eq]
  calc conjSubgroup B g ≤ conjSubgroup (N ⊔ Z) g := E3.conjSubgroup_mono_left g hB_le
    _ = conjSubgroup N g ⊔ conjSubgroup Z g := hsup
    _ = N ⊔ Z := by rw [hN_fix, hZ_fix]

theorem conjSubgroup_inf_pCoreOf_eq_of_kf1 {H T M V I : Subgroup Γ} {g : Γ}
    (h : E2.Hyp28 H T M V) (hI : IsInIHTV H T M V I) (hg : g ∈ I)
    (hgen : I = V ⊔ conjSubgroup V g)
    (hKF1 : ⁅(conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I), I⁆ ≤ pCoreOf 2 H) :
    conjSubgroup V g ⊓ pCoreOf 2 I = (V ⊓ conjSubgroup V g) ⊔ (conjSubgroup V g ⊓ pCoreOf 2 H) := by
  set A : Subgroup Γ := conjSubgroup V g ⊓ pCoreOf 2 I with hA
  set Z : Subgroup Γ := V ⊓ conjSubgroup V g with hZ
  set N : Subgroup Γ := pCoreOf 2 H ⊓ I with hN
  set AH : Subgroup Γ := conjSubgroup V g ⊓ pCoreOf 2 H with hAH
  have hEI : conjSubgroup V g ≤ I := by
    rw [hgen]
    exact le_sup_right
  have hA_le_NZ : A ≤ N ⊔ Z := conjSubgroup_inf_pCoreOf_le_sup_of_kf1 h hI hg hgen hKF1
  have hZ_le_OI : Z ≤ pCoreOf 2 I := by
    rw [hgen]
    exact inf_conjSubgroup_le_pCoreOf h.elem
  have hZA : Z ≤ A := le_inf inf_le_right hZ_le_OI
  have hZI : Z ≤ Subgroup.centralizer (I : Set Γ) := by
    rw [hgen]
    exact inf_conjSubgroup_le_centralizer_sup h.elem g
  have hZ_norm_N : Z ≤ Subgroup.normalizer (N : Set Γ) :=
    hZI.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer (N : Set Γ)))
  have hA_le_ZN : A ≤ Z ⊔ N := by
    rw [sup_comm]
    exact hA_le_NZ
  have hA_split : A = Z ⊔ (A ⊓ N) := by
    have hD := CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer hZA hZ_norm_N
    rwa [inf_eq_left.mpr hA_le_ZN] at hD
  have hN_le_OI : N ≤ pCoreOf 2 I := by
    rw [hN]
    exact (inf_comm (pCoreOf 2 H) I).le.trans
      (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hI.1)
  have hAH_le_N : AH ≤ N := le_inf inf_le_right (inf_le_left.trans hEI)
  have hAH_le_A : AH ≤ A := le_inf inf_le_left (hAH_le_N.trans hN_le_OI)
  have hAIN : A ⊓ N = AH := by
    refine le_antisymm ?_ (le_inf hAH_le_A hAH_le_N)
    exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  rw [hA_split, hAIN]

theorem rAV_lt_two_of_kf1
    {H T M V I : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V) (hc : CharTwo H)
    (hTI : IsTISetIn V M) (hI : IsInIHTV H T M V I) (hg : g ∈ I)
    (hgen : I = V ⊔ conjSubgroup V g)
    (hKF1 : ⁅(conjSubgroup V g ⊓ pCoreOf 2 I) ⊔ (V ⊓ pCoreOf 2 I), I⁆ ≤ pCoreOf 2 H) :
    rAV (autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 H)) < 2 := by
  have hAeq := conjSubgroup_inf_pCoreOf_eq_of_kf1 h hI hg hgen hKF1
  have h215 : rAV (autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I)) < 2 :=
    e215_two_OI Γ H T M V h hc hTI I g hI hg hgen (conjSubgroup V g ⊓ pCoreOf 2 I) rfl
  have hTI_sylow : IsSylowTwoOf (T ⊓ I) I := hI.2.2.1
  have hO2I_le_T : pCoreOf 2 I ≤ T :=
    (hTI_sylow.le_of_normalizes (CFSG.LieType.BorelTits.pCoreOf_le 2 I)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I)).trans inf_le_left
  have hA_N : conjSubgroup V g ⊓ pCoreOf 2 I ≤ Subgroup.normalizer (V : Set Γ) :=
    (inf_le_right.trans hO2I_le_T).trans h.normal_T
  have hZ_N : V ⊓ conjSubgroup V g ≤ Subgroup.normalizer (V : Set Γ) :=
    (inf_le_left.trans h.le_T).trans h.normal_T
  have hAH_le_A : conjSubgroup V g ⊓ pCoreOf 2 H ≤ conjSubgroup V g ⊓ pCoreOf 2 I :=
    hAeq.symm ▸ le_sup_right
  have hAH_N : conjSubgroup V g ⊓ pCoreOf 2 H ≤ Subgroup.normalizer (V : Set Γ) :=
    hAH_le_A.trans hA_N
  have hZ_cent : V ⊓ conjSubgroup V g ≤ Subgroup.centralizer (V : Set Γ) :=
    (inf_le_left : V ⊓ conjSubgroup V g ≤ V).trans
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr h.elem.1)
  have hZ_aut : autI h.elem (V ⊓ conjSubgroup V g) = ⊥ :=
    autI_eq_bot_of_le_centralizer h.elem hZ_cent
  have hsup : autI h.elem ((V ⊓ conjSubgroup V g) ⊔ (conjSubgroup V g ⊓ pCoreOf 2 H)) =
      autI h.elem (V ⊓ conjSubgroup V g) ⊔ autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 H) :=
    autI_sup h.elem hZ_N hAH_N
  have hAut : autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I) =
      autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 H) := by
    rw [hAeq, hsup, hZ_aut, bot_sup_eq]
  rwa [hAut] at h215

end Targets

end CFSG.Quasithin.SimsE2.KF1
