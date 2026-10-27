module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2E6
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2P9b

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem A2Cfg.E5a_of_comm_comm (h36 : A36ForSQTK) (c : A2Cfg G T M L D H K q)
    (hcc : ⁅⁅a2V L T, oTwoUpper H⁆, a2R H⁆ ≤ a2Z T) : E5aConcl L K T H := by
  have hG2 : a2G2 K T ≤ Subgroup.centralizer (a2Z T : Set G) := c.G2_le_centralizer_Z h36
  obtain ⟨hVe, hLV, hTV, -, -, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  have hYV : oTwoUpper H ≤ Subgroup.normalizer (vPlus L T : Set G) :=
    (oTwoUpper_le H).trans (c.nf.HLT.trans (sup_le hLV hTV))
  have hXV : ⁅a2V L T, oTwoUpper H⁆ ≤ a2V L T := commutator_le_left_of_le_normalizer' hYV
  have hZV : a2Z T ≤ a2V L T := le_conjClosure _ _
  have hVZ : ∀ v ∈ a2V L T, v ∈ Subgroup.centralizer (a2Z T : Set G) := fun v hv => by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have := hVe.1.is_comm.comm ⟨z, hZV hz⟩ ⟨v, hv⟩
    exact congrArg Subtype.val this
  let N : Subgroup G :=
    { carrier := {u | u ∈ Subgroup.centralizer (a2Z T : Set G) ∧
        ∀ s ∈ a2TC K T, ⁅u, s⁆ ∈ a2Z T}
      one_mem' := by
        refine ⟨Subgroup.one_mem _, fun s _ => ?_⟩
        simp
      mul_mem' := by
        rintro u₁ u₂ ⟨hu₁, h₁⟩ ⟨hu₂, h₂⟩
        refine ⟨Subgroup.mul_mem _ hu₁ hu₂, fun s hs => ?_⟩
        have e : ⁅u₁ * u₂, s⁆ = u₁ * ⁅u₂, s⁆ * u₁⁻¹ * ⁅u₁, s⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        have h3 : u₁ * ⁅u₂, s⁆ * u₁⁻¹ = ⁅u₂, s⁆ := by
          have := Subgroup.mem_centralizer_iff.mp hu₁ _ (h₂ s hs)
          calc u₁ * ⁅u₂, s⁆ * u₁⁻¹ = (u₁ * ⁅u₂, s⁆) * u₁⁻¹ := rfl
            _ = (⁅u₂, s⁆ * u₁) * u₁⁻¹ := by rw [this]
            _ = ⁅u₂, s⁆ := by group
        rw [h3]
        exact (a2Z T).mul_mem (h₂ s hs) (h₁ s hs)
      inv_mem' := by
        rintro u ⟨hu, h⟩
        refine ⟨Subgroup.inv_mem _ hu, fun s hs => ?_⟩
        have e : ⁅u⁻¹, s⁆ = u⁻¹ * (⁅u, s⁆)⁻¹ * u := by
          simp only [commutatorElement_def]; group
        rw [e]
        have hz : (⁅u, s⁆)⁻¹ ∈ a2Z T := (a2Z T).inv_mem (h s hs)
        have := Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hu) _ hz
        have h4 : u⁻¹ * (⁅u, s⁆)⁻¹ * u = (⁅u, s⁆)⁻¹ := by
          calc u⁻¹ * (⁅u, s⁆)⁻¹ * u = ((⁅u, s⁆)⁻¹ * u⁻¹) * u := by rw [this]
            _ = (⁅u, s⁆)⁻¹ := by group
        rw [h4]
        exact hz }
  have hgen : a2UH L T H K ≤ N := by
    refine conjClosure_le fun g hg x hx => ?_
    have hgC : g ∈ Subgroup.centralizer (a2Z T : Set G) := hG2 hg
    have hxC : x ∈ Subgroup.centralizer (a2Z T : Set G) := hVZ x (hXV hx)
    refine ⟨?_, fun s hs => ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have h1 := Subgroup.mem_centralizer_iff.mp hgC z hz
      have h2 := Subgroup.mem_centralizer_iff.mp hxC z hz
      calc z * (g * x * g⁻¹) = (z * g) * x * g⁻¹ := by group
        _ = (g * z) * x * g⁻¹ := by rw [← h1]
        _ = g * (z * x) * g⁻¹ := by group
        _ = g * (x * z) * g⁻¹ := by rw [← h2]
        _ = g * x * (z * g⁻¹) := by group
        _ = g * x * (g⁻¹ * z) := by
          congr 1
          have := Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hgC) z hz
          exact this.symm ▸ rfl
        _ = (g * x * g⁻¹) * z := by group
    ·
      have hs' : g⁻¹ * s * g ∈ a2TC K T := by
        have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (a2G2 K T) (Subgroup.inv_mem _ hg)
        have := (Subgroup.mem_normalizer_iff.mp hN s).mp hs
        simpa using this
      have hR : g⁻¹ * s * g ∈ a2R H := c.TC_le_R hs'
      have hmem : ⁅x, g⁻¹ * s * g⁆ ∈ a2Z T := hcc (Subgroup.commutator_mem_commutator hx hR)
      have e : ⁅g * x * g⁻¹, s⁆ = g * ⁅x, g⁻¹ * s * g⁆ * g⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      have := Subgroup.mem_centralizer_iff.mp hgC _ hmem
      have h5 : g * ⁅x, g⁻¹ * s * g⁆ * g⁻¹ = ⁅x, g⁻¹ * s * g⁆ := by
        calc g * ⁅x, g⁻¹ * s * g⁆ * g⁻¹ = (g * ⁅x, g⁻¹ * s * g⁆) * g⁻¹ := rfl
          _ = (⁅x, g⁻¹ * s * g⁆ * g) * g⁻¹ := by rw [← this]
          _ = ⁅x, g⁻¹ * s * g⁆ := by group
      rw [h5]
      exact hmem
  show ⁅a2UH L T H K, a2TC K T⁆ ≤ a2Z T
  refine Subgroup.commutator_le.mpr fun u hu s hs => ?_
  exact (hgen hu).2 s hs

end CFSG.Quasithin.H13.NFa2
