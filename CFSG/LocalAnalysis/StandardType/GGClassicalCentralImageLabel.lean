module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEndsCover
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed
import CFSG.LocalAnalysis.StandardType.GGTwistedLabelModels
import CFSG.RankThree.PartOne.CTP.SpinCenterEven
import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
open scoped MatrixGroups

section Cover

theorem ggSp_split {m f : ℕ} (hm : 2 ≤ m) (hf : 2 ≤ f) (E : Type) [Group E] [Finite E]
    (π : E →* (ggU .PSp m f).K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ σ : (ggU .PSp m f).K →* E, ∀ g, π (σ g) = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  let Z := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars m (GaloisField 2 f)
  have hZc : Z ≤ Subgroup.center (StatedSp m (GaloisField 2 f)) :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center
  haveI : Group.IsPerfect (StatedSp m (GaloisField 2 f)) :=
    CFSG.LieType.Steinberg.CentralExt.SpClosed.isPerfect_statedSp' (Or.inl h4)
  exact CFSG.LieType.Steinberg.CentralExt.CoverAssembly.exists_section_of_cover_and_coprime
    (p := 2) (θ := QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact hZc)
    (CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_two_cover_trivial hK (by omega) hm
      fun _ => hf)
    (fun E' _ _ π' hπ' hcen' hc' =>
      CFSG.LieType.Steinberg.CentralExt.SpClosed.sp_exists_section_of_coprime E' π' hπ' hcen' hc')
    E π hπ hcen

theorem ggSpinMinus_split {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f) (E : Type) [Group E] [Finite E]
    (π : E →* (ggU .POmegaMinus n f).K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : (ggU .POmegaMinus n f).K →* E, ∀ g, π (σ g) = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.spinMinus_exists_section_of_central
    (minusCoeffs_irr 2 f) hn h4 hπ hcen

theorem ggCentralImage_PSp_of_hasLabel {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : commutator ↥X = ⊤) {m f : ℕ} (hm : 3 ≤ m) (hf : 2 ≤ f)
    (h : GGHasLabel ⟨.B, m, f⟩ (↥X ⧸ Subgroup.center ↥X) ∨
      GGHasLabel ⟨.C, m, f⟩ (↥X ⧸ Subgroup.center ↥X)) :
    GGCentralImage .PSp m f X := by
  have hadm : StatedLieAdmissible .PSp m 2 f := by
    refine ⟨Nat.prime_two, by omega, by omega, ?_⟩
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  have hM : CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .PSp m 2 f := by
    refine Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hadm, ?_⟩
    rcases h with h | h
    · obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := h
      exact ⟨K, hF, hfin, hK, ⟨e⟩⟩
    · obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := h
      exact ⟨K, hF, hfin, hK, ⟨e⟩⟩
  exact ggF4Ends_centralImage_of_lieModel (Or.inr (Or.inr (Or.inl rfl))) hadm
    (ggSp_split (by omega) hf) hX hM

theorem ggCentralImage_POmegaMinus_of_hasLabel {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : commutator ↥X = ⊤) {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (h : GGHasLabel ⟨.twD, n, f⟩ (↥X ⧸ Subgroup.center ↥X)) :
    GGCentralImage .POmegaMinus n f X := by
  have hC := statedClassicalModel_of_hasLabel_typeTwD hn h
  have hM : CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .POmegaMinus n 2 f :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hC⟩
  exact ggF4Ends_centralImage_of_lieModel (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    hC.1 (ggSpinMinus_split hn hf) hX hM

theorem nonempty_mulEquiv_statedSp_of_hasLabel {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : commutator ↥X = ⊤) {m f : ℕ} (hm : 3 ≤ m) (hf : 2 ≤ f)
    (h : GGHasLabel ⟨.B, m, f⟩ (↥X ⧸ Subgroup.center ↥X) ∨
      GGHasLabel ⟨.C, m, f⟩ (↥X ⧸ Subgroup.center ↥X)) :
    Nonempty (↥X ≃* StatedSp m (GaloisField 2 f)) := by
  obtain ⟨ψ, -, hker, hrange⟩ := ggCentralImage_PSp_of_hasLabel hX hm hf h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcent : Subgroup.center (ggU .PSp m f).K = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := m)
      (F := GaloisField 2 f) (by omega)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff ψ]
    rw [hcent] at hker
    exact le_bot_iff.1 hker
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem nonempty_mulEquiv_spinMinus_of_hasLabel {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : commutator ↥X = ⊤) {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (h : GGHasLabel ⟨.twD, n, f⟩ (↥X ⧸ Subgroup.center ↥X)) :
    Nonempty (↥X ≃*
      spinGroup (quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) := by
  obtain ⟨ψ, -, hker, hrange⟩ := ggCentralImage_POmegaMinus_of_hasLabel hX hn hf h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcent : Subgroup.center (ggU .POmegaMinus n f).K = ⊥ :=
    CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot (F := GaloisField 2 f)
      (n := n) hn (minusCoeffs_irr 2 f)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff ψ]
    rw [hcent] at hker
    exact le_bot_iff.1 hker
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem exists_sl_centralImage_of_hasLabel {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : commutator ↥X = ⊤) {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (h : GGHasLabel ⟨.A, n - 1, f⟩ (↥X ⧸ Subgroup.center ↥X)) :
    ∃ ψ : SL(n, GaloisField 2 f) →* G,
      ψ.ker ≤ Subgroup.center SL(n, GaloisField 2 f) ∧ ψ.range = X := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h' : GGHasLabel ⟨.A, m, f⟩ (↥X ⧸ Subgroup.center ↥X) := by simpa using h
  have hC := ggF4Ends_centralImage_PSL (m := m) hX (by omega) hf (by omega) h'
  simp only [GGCentralImage] at hC
  obtain ⟨ψ, -, hker, hrange⟩ := hC
  exact ⟨ψ, hker, hrange⟩

theorem exists_su_centralImage_of_hasLabel {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : commutator ↥X = ⊤) {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (h : GGHasLabel ⟨.twA, n - 1, f⟩ (↥X ⧸ Subgroup.center ↥X)) :
    ∃ ψ : ↥(Unitary.SU (BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n) →* G,
      ψ.ker ≤ Subgroup.center
        ↥(Unitary.SU (BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n) ∧
      ψ.range = X := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h' : GGHasLabel ⟨.twA, m, f⟩ (↥X ⧸ Subgroup.center ↥X) := by simpa using h
  have hC : GGCentralImage .PSU (m + 1) f X :=
    ggF4Ends_centralImage_PSU (m := m) hX (by omega) hf h'
  have hf1 : 1 ≤ f := by omega
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    card_galoisField_two_mul 2 f hf1
  have hK : ggU .PSU (m + 1) f = ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * f)) 2 f) (m + 1), Unitary.rootDatum hF (m + 1)⟩ := by
    simp only [ggU, lieUniversal, hf1, ↓reduceDIte]
  simp only [GGCentralImage] at hC
  rw [hK] at hC
  obtain ⟨ψ, -, hker, hrange⟩ := hC
  exact ⟨ψ, hker, hrange⟩

end Cover

end CFSG.StandardType

end
