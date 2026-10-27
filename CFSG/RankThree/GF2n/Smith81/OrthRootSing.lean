module

public import CFSG.RankThree.GF2n.Smith81.Orth52Std
public import CFSG.RankThree.GF2n.Smith81.OrthMaxTSNonsing

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open CFSG.ClassicalGroups.Orthogonal (eichler)

variable {G : Type} [Group G] [Finite G] {M Q Z B A : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {ι : Type} [Fintype ι] [DecidableEq ι] {qU : QuadraticForm K (ι → K)}
  {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)}

theorem qU_eq_zero_of_root_std (hcB : Ctx M Q Z B) (hcA : Ctx M Q Z A)
    (hno : NoA2 Q Z (LB M Q A)) (hLA : LB M Q A ≤ Lgen M (LB M Q B))
    (hD : GlobalModelData M Q Z γ M₀) (hF : OrthPreFrame Q Z M₀ qU φ)
    (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))) (hn : 4 ≤ Fintype.card ι) {u : ι → K}
    (hu0 : u ≠ 0) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) (hpa : φ (M₀.π a) = (u, 0)) :
    qU u = 0 := by
  classical
  by_contra hqu
  have hn' : 2 < Fintype.card ι := by omega
  have hw := width_of_tensor hD φ
  obtain ⟨W, hW, hWn, -, hWs⟩ := hcA.lagr hw hn' hno hD
  have hmemD : ∀ p, p ∈ W.map (φ : M₀.E →ₗ[K] (ι → K) × (ι → K)) ↔
      φ.symm p ∈ M₀.img (Q ⊓ QB A) := fun p => by
    rw [hW]
    exact Submodule.mem_map_equiv W (e := φ)
  have hq : 4 ≤ Nat.card K := by
    rw [hD.card]
    exact hcB.hyp.q4
  have huD : ((u, 0) : (ι → K) × (ι → K)) ∈ W.map (φ : M₀.E →ₗ[K] (ι → K) × (ι → K)) := by
    rw [hmemD, φ.symm_apply_eq.mpr hpa.symm]
    exact M₀.pi_mem_img (Subgroup.mem_inf.mpr ⟨hcA.le haA, hcA.B_le_QB haA⟩) (hcA.le haA)
  have hts : ∀ p ∈ W.map (φ : M₀.E →ₗ[K] (ι → K) × (ι → K)),
      QuadraticMap.polar qU p.1 p.2 = 0 := by
    intro p hp
    have h1 := hWs _ ((hW _).mp ((hmemD p).mp hp))
    rwa [hF.qf, LinearEquiv.apply_symm_apply] at h1
  have hdim : Fintype.card ι ≤ Module.finrank K (W.map (φ : M₀.E →ₗ[K] (ι → K) × (ι → K))) := by
    have := LinearEquiv.finrank_map_eq φ W
    omega
  obtain ⟨Γ, hΓcard, hΓ⟩ := exists_unipotent_pairs hcA hno hLA hD hAct (by omega) hu0 haA ha1 hpa
  exact false_of_stable_nonsingular hF.nondeg hn hq hqu huD hts hdim
    (fun μ p hp => (hmemD _).mpr
      (img_stable_sl hcB hcA hD hAct haA ha1 hpa μ ((hmemD p).mp hp)))
    (fun s w hs hsw hsu hwu p hp => (hmemD _).mpr
      (img_stable_eichler hcB hcA hD hAct haA ha1 hpa hs hsw hsu hwu ((hmemD p).mp hp)))
    ⟨Γ, hΓcard, fun t ht => by
      obtain ⟨h1, h2, h3⟩ := hΓ t ht
      refine ⟨h1, h2, fun p hp => ?_⟩
      simpa using h3 (φ.symm p) ((hmemD p).mp hp)⟩

end CFSG.RankThree.GF2n.Smith81
