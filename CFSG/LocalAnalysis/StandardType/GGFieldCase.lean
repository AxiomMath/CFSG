module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL43Hard
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseQuot

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type*} [Group G]

theorem exists_maxPSubgroup_of_le [Finite G] {p : ℕ} {H Q : Subgroup G} (hQ : IsPGroup p Q)
    (hQH : Q ≤ H) :
    ∃ R : Subgroup G, IsPGroup p R ∧ Q ≤ R ∧ R ≤ H ∧
      ∀ S : Subgroup G, S ≤ H → IsPGroup p S → R ≤ S → S = R := by
  obtain ⟨R, hR⟩ := (Set.toFinite {R : Subgroup G | IsPGroup p R ∧ Q ≤ R ∧ R ≤ H}).exists_maximal
    ⟨Q, hQ, le_rfl, hQH⟩
  exact ⟨R, hR.1.1, hR.1.2.1, hR.1.2.2, fun S hSH hS hRS =>
    le_antisymm (hR.2 ⟨hS, hR.1.2.1.trans hRS, hSH⟩ hRS) hRS⟩

theorem le_normalizer_of_maxPSubgroup {p : ℕ} {C R U : Subgroup G}
    (hRC : R ≤ Subgroup.normalizer (C : Set G)) (hR : IsPGroup p R) (hUR : U ≤ R) (hUC : U ≤ C)
    (hmax : ∀ Q : Subgroup G, Q ≤ C → IsPGroup p Q → U ≤ Q → Q = U) :
    R ≤ Subgroup.normalizer (U : Set G) := by
  have hU : R ⊓ C = U := hmax _ inf_le_right (hR.to_le inf_le_left) (le_inf hUR hUC)
  intro r hr
  rw [← hU, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨R.mul_mem (R.mul_mem hr h1) (R.inv_mem hr),
      (Subgroup.mem_normalizer_iff.mp (hRC hr) h).mp h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hRC hr) h).mpr h2⟩
    have := R.mul_mem (R.mul_mem (R.inv_mem hr) h1) hr
    simpa [mul_assoc] using this

theorem ggNormalizer_le_normalizer_centralizer (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hh s hs
    have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
    have h1 := hh _ hs'
    calc s * (g * h * g⁻¹) = g * ((g⁻¹ * s * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = g * h * g⁻¹ * s := by group
  · intro hh s hs
    have hs' : g * s * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hg s).mp hs
    have h1 := hh _ hs'
    calc s * h = g⁻¹ * ((g * s * g⁻¹) * (g * h * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * h * g⁻¹) * (g * s * g⁻¹)) * g := by rw [h1]
      _ = h * s := by group

theorem le_normalizer_zpowers_of_le {S U : Subgroup G} {d : G} (hd : d ∈ S)
    (hU : U ≤ Subgroup.centralizer (S : Set G)) :
    U ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  intro u hu
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hdu : d * u = u * d := Subgroup.mem_centralizer_iff.mp (hU hu) d hd
  exact (Commute.zpow_left hdu k).eq

end General

theorem ggFieldCaseInput_of_inputs (hTBM : GGTableBModuleInput) (h43 : GGL43Input)
    (h44 : GGL44iiiInput) (h45 : GGL45Input) (h46 : GGL46Input) (h47 : GGL47Input)
    (h48 : GGL48Input) : GGFieldCaseInput := by
  intro G _ _ p B Bs x L D J X hFC
  obtain ⟨hcfg, hbl5, hXN, hCX, hXn, hXp, hXC⟩ := hFC
  have hI := hcfg.1
  have : Fact p.Prime := ⟨hI.2.2.2.2.2.1.1⟩
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hI.2.2.2.2.2.2.1.2.1
  have hFC : GGFieldCase p B Bs x L D J X := ⟨hcfg, hbl5, hXN, hCX, hXn, hXp, hXC⟩
  have hL43 := h43 G p B Bs x L D J X hFC
  have hL44 := ggL44i_of_ggL43 hBs hxBs hXN hXp hL43
  obtain ⟨B₂, hM⟩ := hTBM G p B Bs x L D J hcfg
  have hL44ii := ggL44ii_of_ggL43 hFC hM hL43 hL44
  obtain ⟨d, y, K, hK⟩ := h44 G p B Bs x L D J X B₂ hFC hM hL43 hL44 hL44ii
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hBsC : Bs ≤ Subgroup.centralizer (B₁ : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact mul_comm_of_isElemAbelian hBs hc.1 hb
  obtain ⟨U, hUp, hBsU, hUC, hUmax⟩ := exists_maxPSubgroup_of_le (isPGroup_of_isElemAbelian hBs)
    hBsC
  have hsetup : GGL45Setup p Bs X U := ⟨hUC, hUp, hUmax, hBsU⟩
  have hd : d ∈ D ⊓ B₁ := hK.1 ▸ Subgroup.mem_zpowers d
  have hUK : U ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf (hUC.trans (Subgroup.centralizer_le_normalizer _))
      (le_normalizer_zpowers_of_le hd.2 hUC)).trans
      (hbl5 X hXN hCX hXn hXp hXC d hd hK.2.1 y K hK.2.2.1 hK.2.2.2.1)
  obtain ⟨U₁, hU₁, hNU₁⟩ :=
    h45 G p B Bs x L D J X B₂ d y K U hFC hM hL43 hL44 hL44ii hK hsetup hUK
  have hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ :=
    ⟨hFC, hM, hL43, hL44, hL44ii, hK, hsetup, hU₁, hNU₁⟩
  have hL46 := h46 G p B Bs x L D J X B₂ d y K U U₁ hS
  obtain ⟨hab, -, hJU, hΩ₁, -, -⟩ := id hL46
  obtain ⟨R, hRp, hUR, hRM, hRmax⟩ := exists_maxPSubgroup_of_le (H := Subgroup.normalizer
    (B₁ : Set G)) hUp (hUC.trans (Subgroup.centralizer_le_normalizer _))
  have hRU : R ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_of_maxPSubgroup (hRM.trans (ggNormalizer_le_normalizer_centralizer B₁)) hRp hUR
      hUC hUmax
  have hrep := h47 G p B Bs x L D J X B₂ d y K U U₁ hS hL46 R hRp hRM hRmax hUR
  obtain ⟨⟨S, hSR⟩, -, -⟩ := ggL47 hRp hRmax hUR hRU hU₁.2.1 hab hJU hΩ₁ le_rfl hrep
  have hA := thompsonAbelianSubgroups_eq_of_replacement hRp hUR hU₁.2.1
    (hRU.trans (normalizer_le_normalizer_of_forall_eq hJU)) hab hJU hrep
  have hRsyl : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R := fun Q hQ hRQ => by
    subst hSR
    exact S.is_maximal' hQ hRQ
  have hx48 := h48 G p B Bs x L D J X B₂ d y K U U₁ hS hL46 R hRp hRsyl hUR hA
  have hxN : x ∈ Subgroup.normalizer (U₁ : Set G) :=
    normalizer_le_normalizer_of_forall_eq hJU (Subgroup.le_normalizer (hBsU hxBs))
  obtain ⟨ψ, hψ⟩ := exists_monoidHom_zmod_ne_one_of_not_mem_commutator' hxN (hBs.2 x hxBs) hx48
  exact ⟨Subgroup.normalizer (B₁ : Set G), R, U, U₁,
    ⟨rfl, hRp, hRM, hRmax, hUR, hRU, hU₁.2.1, hab, hJU, hΩ₁, hrep⟩, ψ, hψ⟩

theorem ggProp41Input_of_inputs (hTBM : GGTableBModuleInput) (h43 : GGL43Input)
    (h44 : GGL44iiiInput) (h45 : GGL45Input) (h46 : GGL46Input) (h47 : GGL47Input)
    (h48 : GGL48Input) : GGProp41Input :=
  ggProp41Input_of_input (ggFieldCaseInput_of_inputs hTBM h43 h44 h45 h46 h47 h48)

theorem ggFieldCaseInput_of_inputs' (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hhard : GGL43HardInput) (h44 : GGL44iiiInput)
    (h45 : GGL45Input) (h46 : GGL46Input) (h47 : GGL47Input) (h48 : GGL48Input) :
    GGFieldCaseInput :=
  ggFieldCaseInput_of_inputs hTBM (ggL43Input_of_inputs hTB hNN (ggL43ProdInput_of_hard hTBM hhard))
    h44 h45 h46 h47 h48

theorem ggProp41Input_of_inputs' (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hhard : GGL43HardInput) (h44 : GGL44iiiInput)
    (h45 : GGL45Input) (h46 : GGL46Input) (h47 : GGL47Input) (h48 : GGL48Input) :
    GGProp41Input :=
  ggProp41Input_of_input (ggFieldCaseInput_of_inputs' hTB hNN hTBM hhard h44 h45 h46 h47 h48)

theorem ggFieldCaseInput_of_tableB (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) (h44 : GGL44iiiInput)
    (h45 : GGL45Input) (h46 : GGL46Input) (h47 : GGL47Input) (h48 : GGL48Input) :
    GGFieldCaseInput :=
  ggFieldCaseInput_of_inputs' hTB hNN hTBM (ggL43HardInput_of_tableB hTB hTBA) h44 h45 h46 h47 h48

theorem ggProp41Input_of_tableB (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) (h44 : GGL44iiiInput)
    (h45 : GGL45Input) (h46 : GGL46Input) (h47 : GGL47Input) (h48 : GGL48Input) :
    GGProp41Input :=
  ggProp41Input_of_input (ggFieldCaseInput_of_tableB hTB hNN hTBM hTBA h44 h45 h46 h47 h48)

end CFSG.StandardType

end
