module

public import CFSG.RankThree.PartOne.KC.SymplecticInnerActorFix
public import CFSG.RankThree.PartOne.KC.MatrixAlgebraFewBlocks

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Matrix Polynomial Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (semilinConj semilinConj_apply semilin_symm_smul)

variable {r : ℕ} {K : Type} [Field K]

section Block

theorem blockScalar_of_mem_spCenterUnits {x : StatedSp r K}
    (hsq : Squarefree (minpoly K (spEnd x))) {A : gsp r K} (hA : A ∈ spCenterUnits x) :
    ∀ h ∈ primaryFactors (spEnd x), KCOrthComm.BlockScalar (spEquiv x) (gspLE r K A) h := by
  intro h hh
  obtain ⟨hz, hc⟩ := hA
  obtain ⟨c, hc'⟩ := (mem_center_commutant_iff hsq _).mp hc ⟨h, hh⟩
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective c
  refine ⟨f, fun v hv => ?_⟩
  have := hc' ⟨v, hv⟩
  rw [coe_mk_smul_primaryComponent] at this
  exact this

end Block

section Conj

theorem gspLE_spSemilinGAct (g : SemiGSp r K) (A : gsp r K) :
    gspLE r K (spSemilinGAct r K g A) =
      semilinConj (spFmap g) g.right (spFmap_smul g) (gspLE r K A) := by
  refine LinearEquiv.ext fun v => ?_
  rw [semilinConj_apply, gspLE_apply, gspLE_apply,
    spFmap_mulVec_symm, coe_spSemilinGAct]
  have : spSemilinAct r K g = spSemilinAct r K ⟨g.left, g.right⟩ := rfl
  rw [this, spSemilinAct_mk]

theorem spSemilinGAct_mem_spCenterUnits {x : StatedSp r K}
    (hsq : Squarefree (minpoly K (spEnd x))) {g : SemiGSp r K}
    (hFx : ∀ v, spFmap g (spEquiv x v) = spEquiv x (spFmap g v))
    (hfix : ∀ h ∈ primaryFactors (spEnd x), h.map (g.right : K →+* K) = h) {A : gsp r K}
    (hA : A ∈ spCenterUnits x) : spSemilinGAct r K g A ∈ spCenterUnits x := by
  have hM := blockScalar_of_mem_spCenterUnits hsq hA
  have hMc : ∀ v, gspLE r K A (spEquiv x v) = spEquiv x (gspLE r K A v) := by
    intro v
    obtain ⟨hz, -⟩ := hA
    have := (mem_commutant _).mp hz
    exact LinearMap.congr_fun this.eq v
  have hFx' : ∀ v, (spFmap g).symm (spEquiv x v) = spEquiv x ((spFmap g).symm v) := fun v => by
    apply (spFmap g).injective
    rw [AddEquiv.apply_symm_apply, hFx, AddEquiv.apply_symm_apply]
  have hconj := gspLE_spSemilinGAct g A
  have hz : ((gspLin r K (spSemilinGAct r K g A) : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) ∈ commutant (spEnd x) := by
    rw [mem_commutant]
    refine LinearMap.ext fun v => ?_
    change gspLE r K (spSemilinGAct r K g A) (spEquiv x v) =
      spEquiv x (gspLE r K (spSemilinGAct r K g A) v)
    rw [hconj, semilinConj_apply,
      semilinConj_apply, hFx', hMc, hFx]
  refine ⟨hz, ?_⟩
  refine (mem_center_commutant_iff hsq _).mpr fun a => ?_
  have hb := blockScalar_semilinConj (spFmap_smul g) hFx (hfix a a.2) (hM a a.2)
  obtain ⟨f, hf⟩ := hb
  refine ⟨AdjoinRoot.mk (a : K[X]) f, fun v => ?_⟩
  rw [coe_mk_smul_primaryComponent]
  have := hf v v.2
  rw [← hconj] at this
  exact this

end Conj

section Main

variable [Finite K]

theorem spA_conj_eq_of_two_pow (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : Odd p)
    {x : StatedSp r K} (hxp : x ^ p = 1) (hsq : Squarefree (minpoly K (spEnd x)))
    {α : MulAut (StatedProj (StatedSp r K))} (hα : α ∈ spSemilinearAutGroup r K)
    (hαt : α * conjAut r K (spXg x) = conjAut r K (spXg x) * α) {j : ℕ} (hαj : α ^ p ^ j = 1)
    {u : gsp r K} (hu : u ∈ spCenterUnits x) {k : ℕ} (huk : (conjAut r K u) ^ 2 ^ k = 1) :
    α * conjAut r K u * α⁻¹ = conjAut r K u := by
  classical
  obtain ⟨g, rfl⟩ : α ∈ (spPsi r K).range := by
    rw [range_spPsi]
    exact hα
  have hg : spPsi r K g * conjAut r K (spXg x) * (spPsi r K g)⁻¹ = conjAut r K (spXg x) := by
    rw [hαt, mul_inv_cancel_right]
  have hFx := spFmap_comm hr hp2 hxp g hg
  have hfix : ∀ h ∈ primaryFactors (spEnd x), h.map (g.right : K →+* K) = h := fun h hh =>
    spFmap_map_primaryFactor hp hr hxp hsq hαj hFx hh
  obtain ⟨hσN, -⟩ := spFmap_iterate_scalar hr hαj
  have hN : Odd (p ^ j) := hp2.pow
  rw [spPsi_conj_act]
  set G := spCenterUnits x with hG
  have hmem : ∀ Y ∈ G, spSemilinGAct r K g Y ∈ G := fun Y hY =>
    spSemilinGAct_mem_spCenterUnits hsq hFx hfix hY
  let φ : G →* G := (((spSemilinGAct r K g).toMonoidHom).comp G.subtype).codRestrict G
    (fun Y => hmem Y Y.2)
  have hφinj : Function.Injective φ := fun Y₁ Y₂ h =>
    Subtype.ext ((spSemilinGAct r K g).injective (congrArg Subtype.val h))
  have : Finite G := inferInstance
  let σ : MulAut G := MulEquiv.ofBijective φ ⟨hφinj, Finite.surjective_of_injective hφinj⟩
  have hσ : ∀ (Y : G) (k' : ℕ), Y ^ 2 ^ k' = 1 → σ Y = Y := by
    intro Y k' hk'
    refine Subtype.ext (gspLE_injective ?_)
    have hMs : (gspLE r K (Y : gsp r K)) ^ 2 ^ k' = 1 := by
      rw [← map_pow]
      have : (Y : gsp r K) ^ 2 ^ k' = 1 := by
        have := congrArg Subtype.val hk'
        simpa using this
      rw [this, map_one]
    have h1 := KCOrthComm.semilinConj_eq_of_blockScalar (xe := spEquiv x) hsq
      (spFmap_smul g) hFx hN hσN hfix (blockScalar_of_mem_spCenterUnits hsq Y.2) hMs
    change gspLE r K (spSemilinGAct r K g (Y : gsp r K)) = gspLE r K (Y : gsp r K)
    rw [gspLE_spSemilinGAct]
    exact h1
  have hker : ∀ c : G, c ∈ (conjAut r K).ker.subgroupOf G →
      σ c ∈ (conjAut r K).ker.subgroupOf G := by
    intro c hc
    have hc' : conjAut r K (c : gsp r K) = 1 := hc
    show conjAut r K (spSemilinGAct r K g (c : gsp r K)) = 1
    rw [← spPsi_conj_act, hc', mul_one, mul_inv_cancel]
  have hgu : (⟨u, hu⟩ : G) ^ 2 ^ k ∈ (conjAut r K).ker.subgroupOf G := by
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.coe_pow, map_pow]
    exact huk
  have key : σ ⟨u, hu⟩ * (⟨u, hu⟩ : G)⁻¹ ∈ (conjAut r K).ker.subgroupOf G := by
    let cg : CommGroup G :=
      { (inferInstance : Group G) with
        mul_comm := fun Y₁ Y₂ => Subtype.ext (gspLin_injective (by
          have h1 := commute_of_mem_centerSim (x := spLin r K x) Y₁.2
            (m := gspLin r K (Y₂ : gsp r K)) (by
              obtain ⟨hz, -⟩ := Y₂.2
              exact (mem_commutant _).mp hz)
          change gspLin r K ((Y₁ : gsp r K) * (Y₂ : gsp r K)) =
            gspLin r K ((Y₂ : gsp r K) * (Y₁ : gsp r K))
          rw [map_mul, map_mul]
          exact h1.eq)) }
    exact @KCMatrixAlgebra.mul_inv_mem_of_pow_two_pow_mem _ cg inferInstance σ hσ _ hker _ _ hgu
  have h1 : conjAut r K (spSemilinGAct r K g u * u⁻¹) = 1 := key
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

end Main

end CFSG.RankThree.PartOne.KCSpComm
