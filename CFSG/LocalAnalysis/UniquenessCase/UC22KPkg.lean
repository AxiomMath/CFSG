module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sa
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22x
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22so
import CFSG.LocalAnalysis.UniquenessCase.UC22P22xf
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (InClassG tripleE tripleV InClassX oResidualTwo omegaOne omegaOneCenterIn
  CampbellTheoremAsPrinted)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x P22s

variable {G : Type} [Group G] [Finite G]

@[expose] def HiPkgK (D : Data G) (Y : Subgroup (MBar D.M D.U)) (H : Subgroup G) : Prop :=
  ∃ hSH : proofS D ≤ H,
    InClassG ↥(proofS D) ↥H (Subgroup.inclusion hSH) ∧
    ¬ H ≤ centralizer (omegaOneCenterIn (proofS D) : Set G) ∧
    ¬ InClassX ↥(oResidualTwo ↥H) ∧
    ⁅jOf D.T, omegaZJ22 (pCoreOf 2 H)⁆ = proofEiHat D (preN D Y) ∧
    proofEiHat D (preN D Y) ≤ ⁅H, omegaZJ22 (pCoreOf 2 H)⁆ ⊓ centralizer (proofS D : Set G) ∧
    H ≤ D.M ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card ↥Y → p ∣ Nat.card ↥H) ∧
    ¬ H ≤ centralizer (proofEiHat D (preN D Y) : Set G) ∧
    ∃ B : Subgroup G, B ≤ omegaZJ22 (pCoreOf 2 H) ∧ pCoreOf 2 H ≤ centralizer (B : Set G) ∧
      proofS D ⊓ centralizer (B : Set G) ≤ pCoreOf 2 H ∧
      (∀ A : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian D.T A →
        CFSG.Quasithin.IsMaxElemAbelian D.T ((A ⊓ centralizer (B : Set G)) ⊔ B)) ∧
      B ≤ D.U ∧ preN D Y ⊓ centralizer (B : Set G) ≤ centralizer (D.U : Set G)

namespace P22k

theorem isMax_le_proofS (D : Data G) {A : Subgroup G} (hA : CFSG.Quasithin.IsMaxElemAbelian D.T A) :
    A ≤ proofS D :=
  (le_jOf_of_isMax hA).trans (jOf_le_proofS D)

theorem isMax_map_conj (D : Data G) {A : Subgroup G} (hA : CFSG.Quasithin.IsMaxElemAbelian D.T A) {g : G}
    (hg : g ∈ normalizer (proofS D : Set G)) :
    CFSG.Quasithin.IsMaxElemAbelian D.T (A.map (MulAut.conj g).toMonoidHom) := by
  have hAS := isMax_le_proofS D hA
  refine ⟨?_, hA.2.1.map _, fun B hBT hB => ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    have h1 : g * a * g⁻¹ ∈ proofS D := (Subgroup.mem_normalizer_iff.1 hg a).1 (hAS ha)
    simpa [MulAut.conj_apply] using (inf_le_left : proofS D ≤ D.T) h1
  · have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
    rw [Subgroup.card_map_of_injective hinj]
    exact hA.2.2 B hBT hB

theorem omegaZJ22_le_of_isMax {T R A : Subgroup G} (hA : CFSG.Quasithin.IsMaxElemAbelian T A) (hAR : A ≤ R)
    (hRT : R ≤ T) : omegaZJ22 R ≤ A := by
  intro z hz
  obtain ⟨hzR, hzc, hz2⟩ := uc22p22e_mem_omegaZJ'.1 hz
  have hAJ : A ≤ jOf R := le_jOf_of_isMax (P22so.isMax_of_le hA hAR hRT)
  have hzel : IsElemAbelian 2 (Subgroup.closure ({z} : Set G)) :=
    IsElemAbelian.closure_of_commute (fun a ha b hb => by rw [ha, hb]) fun a ha => by rw [ha]; exact hz2
  have hzC : Subgroup.closure ({z} : Set G) ≤ centralizer (A : Set G) := by
    rw [Subgroup.closure_le, Set.singleton_subset_iff, SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    exact fun a ha => hzc a (hAJ ha)
  have hsup : IsElemAbelian 2 (A ⊔ Subgroup.closure ({z} : Set G)) :=
    hA.2.1.sup_of_commute hzel fun a ha b hb => Subgroup.mem_centralizer_iff.1 (hzC hb) a ha
  have hle : A ⊔ Subgroup.closure ({z} : Set G) ≤ T := by
    refine sup_le hA.1 ?_
    rw [Subgroup.closure_le, Set.singleton_subset_iff]
    exact hRT hzR
  have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : A ≤ _) (hA.2.2 _ hle hsup)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure rfl)

theorem pCoreOf_le_of_inClassG {S H : Subgroup G} (hSH : S ≤ H)
    (hG : InClassG ↥S ↥H (Subgroup.inclusion hSH)) : pCoreOf 2 H ≤ S := by
  rw [← map_pCore]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨s, hs⟩ := pCore_le_range hG hy
  rw [← hs]
  exact s.2

theorem commute_conj_of_pkg (D : Data G) {Y : Subgroup (MBar D.M D.U)} {H : Subgroup G}
    (hpkg : HiPkgK D Y H) {g : G} (hg : g ∈ normalizer (proofS D : Set G))
    (h1 : ∀ e ∈ omegaZJ22 (pCoreOf 2 H), g⁻¹ * e * g ∈ pCoreOf 2 H) :
    ∀ x ∈ omegaZJ22 (pCoreOf 2 H), ∀ y ∈ omegaZJ22 (pCoreOf 2 H), x * (g * y * g⁻¹) = (g * y * g⁻¹) * x := by
  obtain ⟨hSH, hG, -, -, -, -, -, -, -, B, hBE, hOB, hCB, hAB, -, -⟩ := hpkg
  have hRS : pCoreOf 2 H ≤ proofS D := pCoreOf_le_of_inClassG hSH hG
  have hRT : pCoreOf 2 H ≤ D.T := hRS.trans inf_le_left
  have hgi : g⁻¹ ∈ normalizer (proofS D : Set G) := inv_mem hg
  have hBB : ∀ b ∈ B, ∀ b' ∈ B, b * (g * b' * g⁻¹) = (g * b' * g⁻¹) * b := by
    intro b hb b' hb'
    have h2 : g⁻¹ * b * g ∈ pCoreOf 2 H := h1 b (hBE hb)
    have h3 := Subgroup.mem_centralizer_iff.1 (hOB h2) b' hb'
    calc b * (g * b' * g⁻¹) = g * ((g⁻¹ * b * g) * b') * g⁻¹ := by group
      _ = g * (b' * (g⁻¹ * b * g)) * g⁻¹ := by rw [h3]
      _ = (g * b' * g⁻¹) * b := by group
  obtain ⟨A₀', hA₀'⟩ := exists_mem_elemThompsonFamily ↥D.T
  have hA₀ := isMax_of_mem_family hA₀'
  set A₁ : Subgroup G := (A₀'.map D.T.subtype ⊓ centralizer (B : Set G)) ⊔ B with hA₁def
  have hA₁ : CFSG.Quasithin.IsMaxElemAbelian D.T A₁ := hAB _ hA₀
  set A₁g : Subgroup G := A₁.map (MulAut.conj g).toMonoidHom with hA₁gdef
  have hA₁g : CFSG.Quasithin.IsMaxElemAbelian D.T A₁g := isMax_map_conj D hA₁ hg
  set A₂ : Subgroup G := (A₁g ⊓ centralizer (B : Set G)) ⊔ B with hA₂def
  have hA₂ : CFSG.Quasithin.IsMaxElemAbelian D.T A₂ := hAB _ hA₁g
  have hBA₂ : B ≤ A₂ := le_sup_right
  have hBgA₂ : ∀ b ∈ B, g * b * g⁻¹ ∈ A₂ := by
    intro b hb
    refine Subgroup.mem_sup_left ⟨⟨b, Subgroup.mem_sup_right hb, by simp [MulAut.conj_apply]⟩,
      Subgroup.mem_centralizer_iff.2 ?_⟩
    intro b' hb'
    exact hBB b' hb' b hb
  have hA₂S := isMax_le_proofS D hA₂
  have hA₂R : A₂ ≤ pCoreOf 2 H := by
    intro a ha
    refine hCB ⟨hA₂S ha, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro b hb
    exact hA₂.2.1.comm (hBA₂ hb) ha
  set A₂' : Subgroup G := A₂.map (MulAut.conj g⁻¹).toMonoidHom with hA₂'def
  have hA₂' : CFSG.Quasithin.IsMaxElemAbelian D.T A₂' := isMax_map_conj D hA₂ hgi
  have hA₂'R : A₂' ≤ pCoreOf 2 H := by
    rintro _ ⟨a, ha, rfl⟩
    have haS : g⁻¹ * a * g⁻¹⁻¹ ∈ proofS D := (Subgroup.mem_normalizer_iff.1 hgi a).1 (hA₂S ha)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine hCB ⟨haS, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro b hb
    have h4 := hA₂.2.1.comm (hBgA₂ b hb) ha
    calc b * (g⁻¹ * a * g⁻¹⁻¹) = g⁻¹ * ((g * b * g⁻¹) * a) * g := by group
      _ = g⁻¹ * (a * (g * b * g⁻¹)) * g := by rw [h4]
      _ = g⁻¹ * a * g⁻¹⁻¹ * b := by group
  have hE₁ := omegaZJ22_le_of_isMax hA₂ hA₂R hRT
  have hE₂ := omegaZJ22_le_of_isMax hA₂' hA₂'R hRT
  intro x hx y hy
  obtain ⟨a, ha, hay⟩ := hE₂ hy
  have hya : g * y * g⁻¹ = a := by
    rw [← hay]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hya]
  exact hA₂.2.1.comm (hE₁ hx) ha

theorem commute_of_pkg_of_sharp (D : Data G) {Y : Subgroup (MBar D.M D.U)} {H X W : Subgroup G}
    (hpkg : HiPkgK D Y H) (hXT : pCoreOf 2 X ≤ D.T)
    (hsharp : ∀ A : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian D.T A →
      CFSG.Quasithin.IsMaxElemAbelian D.T ((A ⊓ centralizer (W : Set G)) ⊔ W))
    (hOW : pCoreOf 2 X ≤ centralizer (W : Set G)) (hCW : proofS D ⊓ centralizer (W : Set G) ≤ pCoreOf 2 X)
    (h1 : omegaZJ22 (pCoreOf 2 H) ≤ pCoreOf 2 X) :
    ∀ x ∈ omegaZJ22 (pCoreOf 2 X), ∀ y ∈ omegaZJ22 (pCoreOf 2 H), x * y = y * x := by
  obtain ⟨hSH, hG, -, -, -, -, -, -, -, B, hBE, hOB, hCB, hAB, -, -⟩ := hpkg
  have hRT : pCoreOf 2 H ≤ D.T := (pCoreOf_le_of_inClassG hSH hG).trans inf_le_left
  have hBW : ∀ b ∈ B, b ∈ centralizer (W : Set G) := fun b hb => hOW (h1 (hBE hb))
  obtain ⟨A₀', hA₀'⟩ := exists_mem_elemThompsonFamily ↥D.T
  have hA₀ := isMax_of_mem_family hA₀'
  set Ash : Subgroup G := (A₀'.map D.T.subtype ⊓ centralizer (W : Set G)) ⊔ W with hAshdef
  have hAsh : CFSG.Quasithin.IsMaxElemAbelian D.T Ash := hsharp _ hA₀
  set A₂ : Subgroup G := (Ash ⊓ centralizer (B : Set G)) ⊔ B with hA₂def
  have hA₂ : CFSG.Quasithin.IsMaxElemAbelian D.T A₂ := hAB _ hAsh
  have hWA₂ : W ≤ A₂ := by
    intro w hw
    refine Subgroup.mem_sup_left ⟨Subgroup.mem_sup_right hw, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro b hb
    exact (Subgroup.mem_centralizer_iff.1 (hBW b hb) w hw).symm
  have hBA₂ : B ≤ A₂ := le_sup_right
  have hA₂S := isMax_le_proofS D hA₂
  have hA₂X : A₂ ≤ pCoreOf 2 X := by
    intro a ha
    refine hCW ⟨hA₂S ha, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro w hw
    exact hA₂.2.1.comm (hWA₂ hw) ha
  have hA₂H : A₂ ≤ pCoreOf 2 H := by
    intro a ha
    refine hCB ⟨hA₂S ha, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro b hb
    exact hA₂.2.1.comm (hBA₂ hb) ha
  have hEX := omegaZJ22_le_of_isMax hA₂ hA₂X hXT
  have hEH := omegaZJ22_le_of_isMax hA₂ hA₂H hRT
  intro x hx y hy
  exact hA₂.2.1.comm (hEX hx) (hEH hy)

end P22k

end CFSG.LocalAnalysis.UniquenessCase.UC22
