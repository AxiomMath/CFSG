module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEnds
public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
import CFSG.LocalAnalysis.StandardType.GGLieOddCoverModel
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter
import CFSG.LocalAnalysis.StandardType.GGTwistedLabelModels
import CFSG.LocalAnalysis.UniquenessCase.Lie.Cover
import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieCover
import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal
open CFSG.StandardType.S2MathFi1035Pos (GGPosTag)

section Cover

theorem ggF4Ends_centralImage_of_lieModel {t : StatedLieTag} {n f : ℕ} (ht : GGPosTag t)
    (hadm : StatedLieAdmissible t n 2 f)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* (ggU t n f).K),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ σ : (ggU t n f).K →* E, ∀ g, π (σ g) = g)
    {G : Type} [Group G] [Finite G] {X : Subgroup G} (hX : commutator ↥X = ⊤)
    (hM : CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) t n 2 f) :
    GGCentralImage t n f X := by
  haveI := LieKnownR2.OddCenter.finite_ggU ht hadm
  obtain ⟨ρ, hρ, hρc⟩ := LieOddCover.exists_ggU_central_cover_of_lieModel ht hadm hM
  obtain ⟨α, hα, hαc, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_exists_cover_of_closed_fin hsplit hX
      (QuotientGroup.mk' (Subgroup.center ↥X)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _).le ρ hρ hρc
  refine ⟨X.subtype.comp α, hadm,
    fun u hu => hαc (MonoidHom.mem_ker.2 (Subtype.ext (MonoidHom.mem_ker.1 hu))), ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hα, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem ggF4Ends_sp_split {f : ℕ} (hf : 2 ≤ f) (E : Type) [Group E] [Finite E]
    (π : E →* (ggU .PSp 3 f).K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ σ : (ggU .PSp 3 f).K →* E, ∀ g, π (σ g) = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  let Z := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 3 (GaloisField 2 f)
  have hZc : Z ≤ Subgroup.center (StatedSp 3 (GaloisField 2 f)) :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center
  haveI : Group.IsPerfect (StatedSp 3 (GaloisField 2 f)) :=
    CFSG.LieType.Steinberg.CentralExt.SpClosed.isPerfect_statedSp' (Or.inl h4)
  exact CFSG.LieType.Steinberg.CentralExt.CoverAssembly.exists_section_of_cover_and_coprime
    (p := 2) (θ := QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact hZc)
    (CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_two_cover_trivial hK (by omega) (by norm_num)
      fun _ => hf)
    (fun E' _ _ π' hπ' hcen' hc' =>
      CFSG.LieType.Steinberg.CentralExt.SpClosed.sp_exists_section_of_coprime E' π' hπ' hcen' hc')
    E π hπ hcen

theorem ggF4Ends_spinMinus_split {f : ℕ} (hf : 2 ≤ f) (E : Type) [Group E] [Finite E]
    (π : E →* (ggU .POmegaMinus 4 f).K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : (ggU .POmegaMinus 4 f).K →* E, ∀ g, π (σ g) = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.spinMinus_exists_section_of_central
    (minusCoeffs_irr 2 f) (le_refl 4) h4 hπ hcen

theorem ggF4Ends_centralImage_PSp {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : commutator ↥X = ⊤) {f : ℕ} (hf : 2 ≤ f)
    (h : GGHasLabel ⟨.B, 3, f⟩ (↥X ⧸ Subgroup.center ↥X) ∨
      GGHasLabel ⟨.C, 3, f⟩ (↥X ⧸ Subgroup.center ↥X)) :
    GGCentralImage .PSp 3 f X := by
  have hadm : StatedLieAdmissible .PSp 3 2 f := by
    refine ⟨Nat.prime_two, by omega, by norm_num, ?_⟩
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  have hM : CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .PSp 3 2 f := by
    refine Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hadm, ?_⟩
    rcases h with h | h
    · obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := h
      exact ⟨K, hF, hfin, hK, ⟨e⟩⟩
    · obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := h
      exact ⟨K, hF, hfin, hK, ⟨e⟩⟩
  exact ggF4Ends_centralImage_of_lieModel (Or.inr (Or.inr (Or.inl rfl))) hadm
    (ggF4Ends_sp_split hf) hX hM

theorem ggF4Ends_centralImage_POmegaMinus {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : commutator ↥X = ⊤) {f : ℕ} (hf : 2 ≤ f)
    (h : GGHasLabel ⟨.twD, 4, f⟩ (↥X ⧸ Subgroup.center ↥X)) :
    GGCentralImage .POmegaMinus 4 f X := by
  have hC := statedClassicalModel_of_hasLabel_typeTwD (le_refl 4) h
  have hM : CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .POmegaMinus 4 2 f :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hC⟩
  exact ggF4Ends_centralImage_of_lieModel (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hC.1
    (ggF4Ends_spinMinus_split hf) hX hM

theorem ggF4Ends_sl_split {m f : ℕ} (hm : 2 ≤ m) (hf : 2 ≤ f) (hm2 : ¬ (m = 2 ∧ f = 2))
    (E : Type) [Group E] [Finite E] (π : E →* (ggU .PSL (m + 1) f).K)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : (ggU .PSL (m + 1) f).K →* E, ∀ g, π (σ g) = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h8 : f ≠ 2 → 8 ≤ 2 ^ f := fun h => by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hev : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  exact TypeA.slHasSections_of_card (d := m + 1) (K := GaloisField 2 f) (by omega)
    (by rw [hK]; omega)
    (by
      rw [hK]
      rintro ⟨h3, hq⟩
      by_cases hf2 : f = 2
      · exact hm2 ⟨by omega, hf2⟩
      · have := h8 hf2
        omega)
    (by
      rw [hK]
      rintro ⟨-, hq⟩
      rw [hq] at hev
      omega) E π hπ hcen

theorem ggF4Ends_su_split {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f) (E : Type) [Group E] [Finite E]
    (π : E →* (ggU .PSU n f).K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ σ : (ggU .PSU n f).K →* E, ∀ g, π (σ g) = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf1 : 1 ≤ f := by omega
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf1
  have hK : ggU .PSU n f = ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * f)) 2 f) n, Unitary.rootDatum hF n⟩ := by
    simp only [ggU, lieUniversal, hf1, ↓reduceDIte]
  revert hcen hπ π
  rw [hK]
  intro π hπ hcen
  let e : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * f)) 2 f) n) ≃* CFSG.ClassicalInvolution.Phan.Su
        (GaloisField 2 (2 * f)) 2 f n :=
    (Unitary.equivStatedSU hF n).trans
      (MulEquiv.subgroupCongr (Unitary.SUid_eq_statedSU hF n).symm)
  obtain ⟨s, hs⟩ := ggSU_central_extension_splits (GaloisField 2 (2 * f)) f n hF hn (by omega)
    (by omega) E (e.toMonoidHom.comp π) (e.surjective.comp hπ) (by
      intro z hz
      apply hcen
      rw [MonoidHom.mem_ker] at hz ⊢
      exact e.injective (by simpa using hz))
  refine ⟨s.comp e.toMonoidHom, fun g => e.injective ?_⟩
  have h := DFunLike.congr_fun hs (e g)
  simpa using h

theorem ggF4Ends_centralImage_PSL {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : commutator ↥X = ⊤) {m f : ℕ} (hm : 2 ≤ m) (hf : 2 ≤ f) (hm2 : ¬ (m = 2 ∧ f = 2))
    (h : GGHasLabel ⟨.A, m, f⟩ (↥X ⧸ Subgroup.center ↥X)) :
    GGCentralImage .PSL (m + 1) f X := by
  have hΛ : LargeEvenInLambda2 (⟨.A, m, f⟩ : LargeEvenLabel) :=
    ⟨le_trans (by norm_num : 1 ≤ 2) hf, show 1 ≤ m by omega, fun _ => hf⟩
  have hC := statedClassicalModel_of_hasLabel_typeA hΛ h
  have hM : CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .PSL (m + 1) 2 f :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hC⟩
  exact ggF4Ends_centralImage_of_lieModel (Or.inl rfl) hC.1 (ggF4Ends_sl_split hm hf hm2) hX hM

theorem ggF4Ends_centralImage_PSU {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : commutator ↥X = ⊤) {m f : ℕ} (hm : 3 ≤ m) (hf : 2 ≤ f)
    (h : GGHasLabel ⟨.twA, m, f⟩ (↥X ⧸ Subgroup.center ↥X)) :
    GGCentralImage .PSU (m + 1) f X := by
  have hΛ : LargeEvenInLambda2 (⟨.twA, m, f⟩ : LargeEvenLabel) :=
    ⟨le_trans (by norm_num : 1 ≤ 2) hf, show 2 ≤ m by omega, fun _ => hf⟩
  have hC := statedClassicalModel_of_hasLabel_typeTwA hΛ h
  have hM : CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .PSU (m + 1) 2 f :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hC⟩
  exact ggF4Ends_centralImage_of_lieModel (Or.inr (Or.inl rfl)) hC.1
    (ggF4Ends_su_split (by omega) hf) hX hM

end Cover

section Row

theorem ggF4Ends_originalRow_of_B3 (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hT : GGNoTransvection p Bs) (hcard : Nat.card Bs = p ^ 4)
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L)
    (hB3 : GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer L Bs)) :
    (∃ f, 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ GGCentralImage .PSp 3 f L) ∨
      (∃ f, 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ GGCentralImage .POmegaMinus 4 f L) ∨
        (∃ f, 2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ GGCentralImage .POmegaMinus 4 f L) := by
  have hperf : commutator ↥L = ⊤ := (ggF4Ends_original_torCov hcfg hT hcard hq).1
  obtain ⟨f, hf, ⟨hp, hlab⟩ | ⟨hp | hp, hlab⟩⟩ :=
    ggF4Ends_original_label_B3 hRig hcfg hT hcard hq hB3
  · exact Or.inl ⟨f, hf, hp, ggF4Ends_centralImage_PSp hperf hf hlab⟩
  · exact Or.inr (Or.inl ⟨f, hf, hp, ggF4Ends_centralImage_POmegaMinus hperf hf hlab⟩)
  · exact Or.inr (Or.inr ⟨f, hf, hp, ggF4Ends_centralImage_POmegaMinus hperf hf hlab⟩)

end Row

end CFSG.StandardType

end
