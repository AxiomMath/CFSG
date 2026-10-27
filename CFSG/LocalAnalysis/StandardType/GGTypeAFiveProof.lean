module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestBlocks
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndInputs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

section Mechanism

variable {G : Type} [Group G]

theorem le_of_ggAutomizer_le_of_conjGen {Bs J H K' : Subgroup G} (hJH : J ≤ H)
    (hCJ : Subgroup.centralizer (Bs : Set G) ≤ Subgroup.normalizer (J : Set G))
    (hgen : K' ≤ ⨆ (g : G) (_ : g ∈ K' ⊓ Subgroup.normalizer (Bs : Set G)),
      J.map (MulAut.conj g).toMonoidHom)
    (hA : ggAutomizer K' Bs ≤ ggAutomizer H Bs) : K' ≤ H := by
  refine hgen.trans (iSup₂_le fun g hg => ?_)
  obtain ⟨hgK, hgN⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨h, hhH, -, hφ⟩ := mem_ggAutomizer_iff.mp (hA (ggConjAut_mem_ggAutomizer hgK hgN))
  have hc : h⁻¹ * g ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have e : g * b * g⁻¹ = h * b * h⁻¹ := by
      have := hφ ⟨b, hb⟩
      rwa [ggConjAut_apply] at this
    calc b * (h⁻¹ * g) = h⁻¹ * (h * b * h⁻¹) * g := by group
      _ = h⁻¹ * (g * b * g⁻¹) * g := by rw [e]
      _ = h⁻¹ * g * b := by group
  rintro _ ⟨j, hj, rfl⟩
  have hj' : (h⁻¹ * g) * j * (h⁻¹ * g)⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.mp (hCJ hc) j).mp hj
  have e : (MulAut.conj g).toMonoidHom j = h * ((h⁻¹ * g) * j * (h⁻¹ * g)⁻¹) * h⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e]
  exact H.mul_mem (H.mul_mem hhH (hJH hj')) (H.inv_mem hhH)

theorem ggAutomizer_sup_le (L K Bs : Subgroup G) :
    ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer (L ⊔ K) Bs :=
  sup_le (ggAutomizer_mono Bs le_sup_left) (ggAutomizer_mono Bs le_sup_right)

end Mechanism

section Config

variable {G : Type} [Group G] [Finite G]

theorem GGConfig.centralizer_bstar_le_normalizer (ha₀ : GGLNoncyclicInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) :
    Subgroup.centralizer (Bs : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hDJ : LargeEvenStdSubPre p B x L D J := hcfg.2.2.1
  have hnc := ha₀ G p B x L hcfg.1
  have hCB : Subgroup.centralizer (Bs : Set G) ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.centralizer_le hcfg.2.1.1
  have hCx : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hS.2.1)
  have hCD : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.centralizer_le hDJ.1
  rw [hDJ.2.2.2.2.1]
  exact le_normalizer_of_map_conj_le fun g hg => map_conj_largeEvenLayer_le
    (mem_normalizer_inf_centralizer (mem_normalizer_of_sstar hS hnc (hCx (hCB hg)))
      (hCD (hCB hg)))

theorem GGConfig.stdSub_le {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) : J ≤ L :=
  hcfg.2.2.1.2.2.2.2.2.1.1.trans inf_le_left

theorem GGConfig.le_of_ggAutomizer_le (ha₀ : GGLNoncyclicInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {H K' : Subgroup G}
    (hLH : L ≤ H)
    (hgen : K' ≤ ⨆ (g : G) (_ : g ∈ K' ⊓ Subgroup.normalizer (Bs : Set G)),
      J.map (MulAut.conj g).toMonoidHom)
    (hA : ggAutomizer K' Bs ≤ ggAutomizer H Bs) : K' ≤ H :=
  le_of_ggAutomizer_le_of_conjGen (hcfg.stdSub_le.trans hLH)
    (hcfg.centralizer_bstar_le_normalizer ha₀) hgen hA

end Config

@[expose] def GGTypeANbrConjGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbrCfg p B Bs x L D J n f y K →
    ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      K' ≤ ⨆ (g : G) (_ : g ∈ K' ⊓ Subgroup.normalizer (Bs : Set G)),
        J.map (MulAut.conj g).toMonoidHom

@[expose] def GGTypeAReflOverInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbrCfg p B Bs x L D J n f y K →
    ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      ¬ ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs →
      p ∣ n + 3 ∧
        GGWeylOfType p (CoxeterMatrix.A (n + 1)) (ggAutomizer L Bs ⊔ ggAutomizer K' Bs) ∧
        ∀ (y'' : G) (K'' : Subgroup G), GGNbr p B x D J y'' K'' →
          ggAutomizer K'' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs ⊔ ggAutomizer K' Bs

@[expose] def GGTypeANbrModelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbrCfg p B Bs x L D J n f y K →
    ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      GGWeylOfType p (CoxeterMatrix.A (n + 1)) (ggAutomizer L Bs ⊔ ggAutomizer K' Bs) →
      StatedClassicalModel (K' ⧸ Subgroup.center K') .PSL (n + 1) 2 f

theorem GGTypeANbrCfg.not_ggAutomizer_le (ha₀ : GGLNoncyclicInput)
    (hG : GGTypeANbrConjGenInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    (hNC : GGTypeANbrCfg p B Bs x L D J n f y K) {y' : G} {K' : Subgroup G}
    (hK' : GGNbr p B x D J y' K') (hout : ¬ K' ≤ L ⊔ K) :
    ¬ ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs := fun hA =>
  hout (hNC.1.le_of_ggAutomizer_le ha₀ le_sup_left (hG G p B Bs x L D J n f y K hNC y' K' hK')
    (hA.trans (ggAutomizer_sup_le L K Bs)))

theorem ggTypeAJoinAutInput_of_conjGen (ha₀ : GGLNoncyclicInput)
    (hG : GGTypeANbrConjGenInput) : GGTypeAJoinAutInput := by
  intro G _ _ p B Bs x L D J n f y K hN y' K' hK' hA
  by_contra hout
  exact hN.toNbrCfg.not_ggAutomizer_le ha₀ hG hK' hout hA

theorem ggTypeAJoinReflInput_of_reflOver (hR : GGTypeAReflOverInput) : GGTypeAJoinReflInput :=
  fun G _ _ p B Bs x L D J n f y K hN y' K' hK' hA =>
    (hR G p B Bs x L D J n f y K hN.toNbrCfg y' K' hK' hA).1

theorem ggTypeAJoinInput_of_conjGen_reflOver (ha₀ : GGLNoncyclicInput)
    (hG : GGTypeANbrConjGenInput) (hR : GGTypeAReflOverInput) : GGTypeAJoinInput :=
  ggTypeAJoinInput_of_aut_refl (ggTypeAJoinAutInput_of_conjGen ha₀ hG)
    (ggTypeAJoinReflInput_of_reflOver hR)

theorem ggTypeAThirdNbrInput_of_reflOver (ha₀ : GGLNoncyclicInput)
    (hG : GGTypeANbrConjGenInput) (hR : GGTypeAReflOverInput) (hM : GGTypeANbrModelInput) :
    GGTypeAThirdNbrInput := by
  intro G _ _ p B Bs x L D J n f y K hNC _ hex
  obtain ⟨y', K', hK', hout⟩ := hex
  have hA := hNC.not_ggAutomizer_le ha₀ hG hK' hout
  obtain ⟨-, hW, -⟩ := hR G p B Bs x L D J n f y K hNC y' K' hK' hA
  have hmod := hM G p B Bs x L D J n f y K hNC y' K' hK' hW
  obtain ⟨-, -, -, -, hmodL, hpq, hn, hsc, -, -, -, hAll⟩ := hNC
  exact ⟨y', K', ⟨hmodL, hpq, hn, hsc, hK', hmod, hW, hAll⟩, hout⟩

theorem ggTypeAJoinThreeInput_of_reflOver (ha₀ : GGLNoncyclicInput)
    (hG : GGTypeANbrConjGenInput) (hR : GGTypeAReflOverInput) : GGTypeAJoinThreeInput := by
  intro G _ _ p B Bs x L D J n f y K y₃ K₃ hNC hN₃ _ hK₃ y' K' hK'
  have hnbr₃ : GGNbr p B x D J y₃ K₃ := hN₃.2.2.2.2.1
  have hA₃ := hNC.not_ggAutomizer_le ha₀ hG hnbr₃ hK₃
  obtain ⟨-, -, hall⟩ := hR G p B Bs x L D J n f y K hNC y₃ K₃ hnbr₃ hA₃
  refine hNC.1.le_of_ggAutomizer_le ha₀ (le_sup_left.trans le_sup_left)
    (hG G p B Bs x L D J n f y K hNC y' K' hK') ((hall y' K' hK').trans ?_)
  exact sup_le ((ggAutomizer_sup_le L K Bs).trans (ggAutomizer_mono Bs le_sup_left))
    (ggAutomizer_mono Bs le_sup_right)

end CFSG.StandardType
