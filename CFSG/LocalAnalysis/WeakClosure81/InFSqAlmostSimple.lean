module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5EF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsF
public import CFSG.GroupTheory.PerfectCentralExtensionUnique
public import CFSG.GroupTheory.PCore.NormalPCoreOf
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  (InFGroup IsOmegaColl genEi CompFactorAutInF W3Lem45_2Chief)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (IsEP eGenP InF ETwoPrint)
open CFSG.SignalizerFunctorTheorem.McBride.Near (IsChiefFactorOf)
open scoped Pointwise commutatorElement

theorem inF_top_of_inFGroup (j : ℕ) {Q : Type} [Group Q] [Finite Q]
    (h : InFGroup j Q) : InF j (⊤ : Subgroup Q) := by
  intro T hT Ω hΩ hne hbot
  have hΩ' : IsOmegaColl Ω := isOmegaColl_of_isInvColl_top hΩ hne hbot
  have hprod : ((genEi j T Ω : Subgroup Q) : Set Q) * (T : Set Q) = Set.univ := h T hT Ω hΩ'
  have hle : genEi j T Ω ≤ eGenP j (⊤ : Subgroup Q) T Ω := genEi_le_eGenP j T hΩ'
  have hsub : ((genEi j T Ω : Subgroup Q) : Set Q) * (T : Set Q) ⊆
      ((eGenP j (⊤ : Subgroup Q) T Ω : Subgroup Q) : Set Q) * (T : Set Q) := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hle hx, y, hy, rfl⟩
  rw [hprod] at hsub
  rw [Subgroup.coe_top]
  exact Set.eq_univ_of_univ_subset hsub

theorem isEP_zero_false {G : Type} [Group G] [Finite G] {H T A K : Subgroup G}
    (h : IsEP 0 H T A K) : False := by
  obtain ⟨-, -, -, hcase⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hcase with ⟨hE1, hcard⟩ | ⟨hE2, hcard⟩
  · obtain ⟨p, hp, hp2, -, -, -, hbar⟩ := hE1
    rw [hbar] at hcard
    norm_num at hcard
  · obtain ⟨-, -, -, L, hL, -, hdisj⟩ := hE2
    have hcard1 : Nat.card (E1.barRad ↥K (A.subgroupOf K)) ≤ 1 := by simpa using hcard
    have hcardpos : 1 ≤ Nat.card (E1.barRad ↥K (A.subgroupOf K)) := Nat.card_pos
    have hbar : E1.barRad ↥K (A.subgroupOf K) = ⊥ :=
      Subgroup.card_eq_one.mp (le_antisymm hcard1 hcardpos)
    rcases hdisj with hLbot | ⟨-, hcard2⟩
    · rw [hbar, Subgroup.commutator_bot_right] at hLbot
      have hsub : Subsingleton ↥L := by rw [hLbot]; infer_instance
      haveI := hsub
      obtain ⟨-, -, a, b, hab⟩ := hL.1
      exact hab (Subsingleton.elim (a * b) (b * a))
    · omega

theorem eGenP_zero_eq_bot {Q : Type} [Group Q] [Finite Q] (T : Subgroup Q)
    (Ω : Set (Subgroup Q)) : eGenP 0 (⊤ : Subgroup Q) T Ω = ⊥ := by
  refine le_bot_iff.mp (iSup₂_le fun A _ => iSup_le fun _ => iSup₂_le fun K hK => ?_)
  exact (isEP_zero_false hK).elim

theorem not_inFSq_zero {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (h2 : ¬ IsPGroup 2 (Bar2 H))
    (hA : ∃ A : Subgroup (Bar2 H), A ≠ ⊥ ∧ IsElemAbelian 2 A) : ¬ InFSq 0 H := by
  intro hF
  obtain ⟨A, hAne, hAel⟩ := hA
  let Ω : Set (Subgroup (Bar2 H)) := {B | ∃ g : Bar2 H, B = CFSG.Quasithin.A1b.conjSub g A}
  have hΩ : E1.IsInvColl (⊤ : Subgroup (Bar2 H)) Ω := by
    refine ⟨fun _ _ => le_top, ?_, ?_⟩
    · rintro B ⟨g, rfl⟩
      exact hAel.map _
    · intro B hB t _
      obtain ⟨g, rfl⟩ := hB
      exact ⟨t * g, (CFSG.Quasithin.A1b.conjSub_mul t g A).symm⟩
  have hne : Ω.Nonempty := ⟨A, 1, by rw [CFSG.Quasithin.A1b.conjSub_one]⟩
  have hbot : ∀ B ∈ Ω, B ≠ ⊥ := by
    rintro B ⟨g, rfl⟩ h
    rw [CFSG.Quasithin.A1b.conjSub,
      Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)] at h
    exact hAne h
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := Bar2 H)
  have hTsyl : IsSylowIn 2 (S : Subgroup (Bar2 H)) ⊤ := isSylowIn_top S
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup (Bar2 H)) ⊤ := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, hTsyl.isPGroup, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  have hprod := hF (S : Subgroup (Bar2 H)) hT Ω hΩ hne hbot
  rw [eGenP_zero_eq_bot (S : Subgroup (Bar2 H)) Ω, Subgroup.coe_bot,
    Subgroup.coe_top] at hprod
  have hScoe : ((S : Subgroup (Bar2 H)) : Set (Bar2 H)) = Set.univ := by
    simpa using hprod
  have htop : (S : Subgroup (Bar2 H)) = ⊤ := by
    rw [← SetLike.coe_set_eq, Subgroup.coe_top]
    exact hScoe
  exact h2 ((htop ▸ hTsyl.isPGroup).of_equiv Subgroup.topEquiv)

theorem mul_eq_top_of_chiefFactor_perfect {Q : Type} [Group Q] [Finite Q]
    {F Z E W T : Subgroup Q} (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥)
    (hperf : ⁅F, F⁆ = F) (hZ : Z ≤ Subgroup.centralizer (F : Set Q))
    (hchief : IsChiefFactorOf ⊤ F Z) (hC : Subgroup.centralizer (F : Set Q) ≤ F)
    (hFT : F ⊔ T = ⊤) (hEW : T ≤ Subgroup.normalizer (E : Set Q))
    (hW2 : IsPGroup 2 W) (hWne : W ≠ ⊥)
    (hcover : F = Z ⊔ ((E ⊔ T) ⊓ F) ∨ F = Z ⊔ (Subgroup.normalizer (W : Set Q) ⊓ F)) :
    ((E : Subgroup Q) : Set Q) * (T : Set Q) = ((⊤ : Subgroup Q) : Set Q) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFn : F.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hchief.2.1.2)
  have hZF : Z ≤ F := hchief.2.2.1.le
  have hperfF : Group.IsPerfect ↥F := by
    refine ⟨?_⟩
    apply Subgroup.map_injective (f := F.subtype) F.subtype_injective
    rw [Subgroup.map_subtype_commutator, hperf, Subgroup.map_top, Subgroup.range_subtype]
  have hle_of_sup : ∀ K : Subgroup Q, K ≤ F → F = Z ⊔ K → F ≤ K := by
    intro K hKF hFK
    have hZ' : Z.subgroupOf F ≤ Subgroup.center ↥F := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
        (hZ (Subgroup.mem_subgroupOf.mp hz)) (w : Q) w.2)
    have hsup : K.subgroupOf F ⊔ Z.subgroupOf F = ⊤ := by
      rw [sup_comm, ← Subgroup.subgroupOf_sup hZF hKF, ← hFK, Subgroup.subgroupOf_self]
    have hKtop : K.subgroupOf F = ⊤ :=
      CFSG.GroupTheory.eq_top_of_sup_le_center_of_isPerfect hZ' hsup
    exact Subgroup.subgroupOf_eq_top.mp hKtop
  rcases hcover with hcover | hcover
  · have hFle : F ≤ E ⊔ T :=
      (hle_of_sup ((E ⊔ T) ⊓ F) inf_le_right hcover).trans inf_le_left
    have hET : E ⊔ T = ⊤ := by
      have h1 : F ⊔ T ≤ E ⊔ T := sup_le hFle le_sup_right
      rw [hFT] at h1
      exact top_le_iff.mp h1
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ T hEW, hET, Subgroup.coe_top]
  · have hFle : F ≤ Subgroup.normalizer (W : Set Q) :=
      (hle_of_sup (Subgroup.normalizer (W : Set Q) ⊓ F) inf_le_right hcover).trans inf_le_left
    have hNF : W ≤ Subgroup.normalizer (F : Set Q) := by
      rw [Subgroup.normalizer_eq_top (h := hFn)]
      exact le_top
    have hnorm : F ≤ Subgroup.normalizer ((W ⊓ F : Subgroup Q) : Set Q) := by
      intro f hf
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      constructor
      · rintro ⟨hxW, hxF⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp (hFle hf) x).mp hxW,
          F.mul_mem (F.mul_mem hf hxF) (F.inv_mem hf)⟩
      · rintro ⟨hxW, hxF⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp (hFle hf) x).mpr hxW, ?_⟩
        have h2 : f⁻¹ * (f * x * f⁻¹) * f = x := by group
        rw [← h2]
        exact F.mul_mem (F.mul_mem (F.inv_mem hf) hxF) hf
    have hWFle : W ⊓ F ≤ pCoreOf 2 F :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm
        (hW2.to_le inf_le_left)
    have hpc : pCoreOf 2 F ≤ pCoreOf 2 (⊤ : Subgroup Q) :=
      CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_top
        (le_of_eq (Subgroup.normalizer_eq_top (h := hFn)).symm)
    have hWFbot : W ⊓ F = ⊥ :=
      le_bot_iff.mp (hWFle.trans (hpc.trans (le_of_eq hO2)))
    have hcommle : ⁅F, W⁆ ≤ W ⊓ F := by
      rw [Subgroup.commutator_le]
      intro f hf w hw
      refine ⟨?_, ?_⟩
      · have h1 : f * w * f⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hFle hf) w).mp hw
        have he : ⁅f, w⁆ = (f * w * f⁻¹) * w⁻¹ := by
          rw [commutatorElement_def]
        rw [he]
        exact W.mul_mem h1 (W.inv_mem hw)
      · have h1 : w * f * w⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp (hNF hw) f).mp hf
        have he : ⁅f, w⁆ = f * (w * f * w⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [he]
        exact F.mul_mem hf (F.inv_mem h1)
    have hcommbot : ⁅F, W⁆ = ⊥ := by
      rw [hWFbot] at hcommle
      exact le_bot_iff.mp hcommle
    have hWcen : W ≤ Subgroup.centralizer (F : Set Q) := by
      rw [Subgroup.commutator_comm] at hcommbot
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommbot
    exact absurd (le_bot_iff.mp (hWFbot ▸ le_inf le_rfl (hWcen.trans hC))) hWne

theorem inF_top_of_chiefFactor_perfect (h43c : W3Lem45_2Chief) {Q : Type} [Group Q] [Finite Q]
    {j : ℕ} (hj : 1 ≤ j) (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥)
    {F Z : Subgroup Q} (hperf : ⁅F, F⁆ = F) (hZ : Z ≤ Subgroup.centralizer (F : Set Q))
    (hchief : IsChiefFactorOf ⊤ F Z) (hC : Subgroup.centralizer (F : Set Q) ≤ F)
    (hFT : ∀ T : Subgroup Q, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → F ⊔ T = ⊤)
    (hcf : ∀ T : Subgroup Q, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → CompFactorAutInF j ⊤ T) :
    InF j (⊤ : Subgroup Q) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFn : F.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hchief.2.1.2)
  intro T hT Ω hΩ hne hbot
  have hSin : IsSylowIn 2 T ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  have hT2 : IsPGroup 2 T := hSin.isPGroup
  have hW2 : IsPGroup 2 (E1.weakClosure T Ω) :=
    hT2.to_le (E1.weakClosure_le (X := T) (Ω := Ω))
  have hWne : E1.weakClosure T Ω ≠ ⊥ := by
    obtain ⟨A, hAΩ, hAT⟩ := exists_mem_le_of_isSylowOf hT hΩ hne
    intro hWbot
    have hAle : A ≤ E1.weakClosure T Ω :=
      le_iSup₂_of_le A hAΩ (le_iSup_of_le hAT le_rfl)
    exact hbot A hAΩ (le_bot_iff.mp (hWbot ▸ hAle))
  have hFTtop : F ⊔ T = ⊤ := hFT T hT
  have hcover := h43c Q T j Ω F Z hj hSin hΩ hne hbot (hcf T hT) hO2 hperf hZ hchief hC hFTtop
  rcases hcover with hcover | hcover
  · exact mul_eq_top_of_chiefFactor_perfect hO2 hperf hZ hchief hC hFTtop
      (le_normalizer_eGenP j hΩ) hW2 hWne (Or.inl hcover)
  · rw [top_inf_eq] at hcover
    exact mul_eq_top_of_chiefFactor_perfect hO2 hperf hZ hchief hC hFTtop
      (le_normalizer_eGenP j hΩ) hW2 hWne (Or.inr hcover)

end CFSG.LocalAnalysis.WeakClosure81
