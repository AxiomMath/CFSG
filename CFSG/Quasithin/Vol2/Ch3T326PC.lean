module

public import CFSG.Quasithin.Vol2.Ch3T326PB

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open

variable {W : Type} [CommGroup W] [Finite W]

structure O2Sit (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W) (t : MulAut W) : Prop where
  hB : D321Base M Mp T L V t
  hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v
  side : SideHyp hB.hD.hyp.Mp_normal L V
  side' : SideHyp hB.hD.hyp.Mp_normal (conjAutSub t L) (V.map t.toMonoidHom)
  hZ : commV L ⊓ fixV Mp = ⊥
  hL3 : IsPSL 3 2 1 ↥L

theorem O2Sit.of (hA21 : AsA21SQTKSection) (hB42 : AsB42)
    (h9 : A38B42) {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    {A : Subgroup (MulAut W)} {r : ℚ} (hS : D321Sit M Mp T L V t A r)
    (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hU : commSub (orbSup T V) L = V)
    (hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hL3 : IsPSL 3 2 1 ↥L)
    (hnat : BinaryNaturalSL L V (V ⊓ fixV Mp) 3 1) : O2Sit M Mp T L V t := by
  obtain ⟨h1, h2, h3⟩ := sideHyps_of_nat hA21 hB42 h9 hS hVt hU hAC hAL hL3 hnat
  exact ⟨hS.toD321Base, hVt, h1, h2, h3, hL3⟩

namespace O2Sit

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  (h : O2Sit M Mp T L V t)
include h

theorem sup_eq_top : commV L ⊔ commV (conjAutSub t L) = ⊤ := by
  rw [← map_commV_conjAutSub]
  exact h.hB.commV_sup_map

theorem inf_fixV_Lt : commV (conjAutSub t L) ⊓ fixV Mp = ⊥ := by
  have htZ : (fixV Mp).map t.toMonoidHom = fixV Mp := by
    rw [map_fixV_conjAutSub,
      mem_normalizer_iff_conjAutSub.1 (h.hB.hD.hyp.Mp_normal h.hB.t_mem)]
  have h1 := congrArg (Subgroup.map t.toMonoidHom) h.hZ
  rw [Subgroup.map_inf_eq _ _ _ (MulEquiv.injective _), map_commV_conjAutSub, htZ,
    Subgroup.map_bot] at h1
  exact h1

theorem eq_one_of_triv {x : MulAut W} (hx1 : ∀ u ∈ commV L, x u = u)
    (hx2 : ∀ u ∈ commV (conjAutSub t L), x u = u) : x = 1 := by
  refine MulEquiv.ext fun w => ?_
  have hw : w ∈ commV L ⊔ commV (conjAutSub t L) := by
    rw [h.sup_eq_top]
    exact Subgroup.mem_top w
  obtain ⟨u, hu, u', hu', rfl⟩ := Subgroup.mem_sup.1 hw
  rw [map_mul, hx1 u hu, hx2 u' hu']
  rfl

end O2Sit

omit [Finite W] in
theorem triv_of_tilde {M Mp X : Subgroup (MulAut W)}
    (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))) (hZ : commV X ⊓ fixV Mp = ⊥)
    {g : MulAut W} (hg : g ∈ M) (hgX : g ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (htriv : letI := qAct hMp; ∀ q ∈ tilde Mp ⊤ (commV X), (⟨g, hg⟩ : ↥M) • q = q) :
    ∀ u ∈ commV X, g u = u := by
  let _i := qAct hMp
  intro u hu
  have h1 := htriv (QuotientGroup.mk u) ⟨u, hu, rfl⟩
  have h2 : (QuotientGroup.mk (g u) : W ⧸ modFix Mp (⊤ : Subgroup W)) = QuotientGroup.mk u := h1
  rw [QuotientGroup.eq, modFix_top_eq] at h2
  have h3 : (g u)⁻¹ * u ∈ commV X ⊓ fixV Mp :=
    ⟨(commV X).mul_mem ((commV X).inv_mem (B15P4.map_commV_mem hgX u hu)) hu, h2⟩
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at h3
  exact h3

omit [Finite W] in
theorem move_tilde {M Mp X : Subgroup (MulAut W)}
    (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))) (hZ : commV X ⊓ fixV Mp = ⊥)
    {g : MulAut W} (hg : g ∈ M) (hgX : g ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (hmove : ∃ u ∈ commV X, g u ≠ u) :
    letI := qAct hMp; ∃ q ∈ tilde Mp ⊤ (commV X), (⟨g, hg⟩ : ↥M) • q ≠ q := by
  let _i := qAct hMp
  by_contra hcon
  push Not at hcon
  obtain ⟨u, hu, hgu⟩ := hmove
  exact hgu (triv_of_tilde hMp hZ hg hgX hcon u hu)

end CFSG.Quasithin.H13.T326
