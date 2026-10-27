module

public import CFSG.RankThree.GF2n.Stroth80.Sec53CentralizerFinal
public import CFSG.RankThree.GF2n.Stroth80.Sec5HypPlaneSymm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

theorem sec53_hcentC (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement)
    (hBC : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∀ (m : ℕ), SpMNat hc t m →
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (γ : G → K)
        (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ →
      ∃ T : Submodule K M₀.E,
        (∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) ∧
        Module.finrank K ↥(imgQInfQB M₀ B ⊓
          imgQInfQB M₀ (conjSubgroup r B)) + 1 = 2 * m) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∀ d ∈ Q ⊓ QB (conjSubgroup r B),
        (∀ l ∈ (QB (conjSubgroup r B) ⊓ M) ⊓ hc.CN t, ⁅l, d⁆ ∈ Z) →
        d ∈ Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) := by
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane d hd hdz
  have hsp0 : SpNat hc t := hsp
  obtain ⟨K, iF, iFin, hK, m, hm, hrep⟩ := hsp
  have hrM : r ∈ M := hc.Rt_le_M t hr
  set C : Subgroup G := conjSubgroup r B with hCdef
  let hcC : Ctx M Q Z C := hc.conj_of_mem hrM
  have hRt : Rt M (LB M Q C) t = Rt M (LB M Q B) t := by
    rw [hCdef, hc.LB_conj hrM]
    exact Rt_conj_left hrM t
  have hVtC : Vt M (LB M Q C) C Z t = Vt M (LB M Q B) B Z t := by
    rw [hCdef, hc.LB_conj hrM]
    exact Vt_conj_left (M := M) (L := LB M Q B) (B := B) (Z := Z) hrM t
  have hCN : hcC.CN t = hc.CN t := Ctx.CN_conj_left hc hrM t
  have hspC' : SpMNat hcC t m := by
    refine ⟨K, iF, iFin, hK, ?_⟩
    rwa [hCN, hRt, hVtC]
  have hspC : SpNat hcC t := by
    refine ⟨K, iF, iFin, hK, m, hm, ?_⟩
    rwa [hCN, hRt, hVtC]
  have htC : t ∈ conjSubgroup r (LB M Q B) := by
    rw [mem_conjSubgroup]
    have hcomm : ⁅r⁻¹, t⁆ ∈ Q := hc.Rt_comm_mem_Q ((Rt M (LB M Q B) t).inv_mem hr)
    have e : r⁻¹ * t * r = ⁅r⁻¹, t⁆ * t := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (LB M Q B).mul_mem (sec39_Q_le_LB hcomm) hs.mem
  have hsC : Sec5Hyp hcC n t :=
    { width := hs.width
      n_gt := hs.n_gt
      noA2 := hc.noA2_conj hs.noA2 hrM
      gen := hs.gen.conj_of_mem hrM
      mem := by
        rw [hCdef, hc.LB_conj hrM]
        exact htC
      notQ := hs.notQ }
  have hplaneB : HypPlane Q Z B (conjSubgroup r B) t := by
    rwa [hCdef] at hplane
  have hsymmPlane : HypPlane Q Z C B t :=
    Ctx.hypPlane_symm_sp h34 hRoot hc hs hsp0 hr hplaneB
  have hCinv : conjSubgroup r⁻¹ C = B := by
    rw [hCdef, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hplaneC : HypPlane Q Z C (conjSubgroup r⁻¹ C) t := by
    rw [hCinv]
    exact hsymmPlane
  have hrInv : r⁻¹ ∈ Rt M (LB M Q C) t := by
    rw [hRt]
    exact (Rt M (LB M Q B) t).inv_mem hr
  obtain ⟨K₂, iF₂, iFin₂, iCh₂, γ, M₀, hD⟩ := stroth_globalModelData hcC.hyp
  letI := iF₂
  letI := iFin₂
  letI := iCh₂
  obtain ⟨T, hTmem, hBC'⟩ :=
    hBC G M Q Z C hcC n t hsC hspC r⁻¹ hrInv hplaneC m hspC' K₂ γ M₀ hD
  have hdzC : ∀ l ∈ (QB C ⊓ M) ⊓ hcC.CN t, ⁅l, d⁆ ∈ Z := by
    intro l hl
    exact hdz l (by simpa only [hCN] using hl)
  have hcent : d ∈ Vone Q C (conjSubgroup r⁻¹ C) (Vt M (LB M Q C) C Z t) :=
    Ctx.centLam_sp_vone h34 hRoot h51 hcC hsC hm hspC' hrInv hplaneC hD T hTmem hBC'
      d hd hdzC
  have hVone : Vone Q C (conjSubgroup r⁻¹ C) (Vt M (LB M Q C) C Z t) =
      Vone Q B C (Vt M (LB M Q B) B Z t) := by
    rw [hCinv, hVtC]
    simp only [Vone]
    exact inf_comm _ _
  rw [hVone] at hcent
  exact hcent

theorem sec53CentralizerW1Statement_holds_of_prod_hBC'
    (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement) (h51 : Stroth51Statement)
    (hprod : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ∀ x ∈ Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)),
          ∃ a ∈ QB B ⊓ Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)),
          ∃ b ∈ QB (conjSubgroup r B) ⊓
              Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)), x = a * b)
    (hBC : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∀ (m : ℕ), SpMNat hc t m →
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (γ : G → K)
        (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ →
      ∃ T : Submodule K M₀.E,
        (∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) ∧
        Module.finrank K ↥(imgQInfQB M₀ B ⊓
          imgQInfQB M₀ (conjSubgroup r B)) + 1 = 2 * m) :
    Sec53CentralizerW1Statement := by
  exact sec53CentralizerW1Statement_holds_of_prod_hBC h34 hRoot h51 hprod hBC
    (sec53_hcentC h34 hRoot h51 hBC)

end CFSG.RankThree.GF2n.Stroth80
