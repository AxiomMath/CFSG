module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCommutant
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsPiGL
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCore

public section

namespace CFSG.StandardType

namespace LayerFacts

open CFSG.RankThree.PartOne.KCLinComm Matrix

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]

theorem eq_one_of_scalar_sq_eq_one [CharP F 2] {c : Fˣ}
    (h : GeneralLinearGroup.scalar (Fin (m + 1)) c ^ 2 = 1) : c = 1 := by
  rw [← map_pow] at h
  have h5 := congrArg (fun g : GL (Fin (m + 1)) F =>
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) 0 0) h
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Units.val_one, Matrix.one_apply_eq] at h5
  exact eq_one_of_sq_eq_one_charTwo (Units.ext h5)

theorem natCast_card_inducedMatrices_ne_zero [Finite F] [CharP F 2]
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsPGroup p E) :
    (Nat.card (LinTorus.inducedMatrices ψ E) : F) ≠ 0 := by
  intro h0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 ((CharP.cast_eq_zero_iff F 2 _).mp h0)
  obtain ⟨e, he, hpair⟩ := LinTorus.mem_inducedMatrices.mp x.2
  obtain ⟨k, hk⟩ := hE ⟨e, he⟩
  have hek : e ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 := (LinFusion.ggInducedPairs ψ).pow_mem hpair (p ^ k)
  rw [Prod.pow_mk, hek] at h1
  obtain ⟨c, hc⟩ := LinTorus.exists_scalar_of_mem_ggInducedPairs_one hker h1
  have hx2 : (x : GL (Fin (m + 1)) F) ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this
  obtain ⟨j, hj⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
  have hxx : (x : GL (Fin (m + 1)) F) ^ (p ^ k) = x := by
    rw [hj, pow_succ, pow_mul, hx2, one_pow, one_mul]
  rw [hxx] at hc
  rw [hc] at hx2
  have hx1 : x = 1 := Subtype.ext (by simp [hc, eq_one_of_scalar_sq_eq_one hx2])
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by norm_num)

open CFSG.Assembly in
theorem ggLayer_sl [Finite F] [CharP F 2] {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsPGroup p E)
    (hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ LinFusion.ggInducedPairs ψ) :
    Odd (Nat.card (Subgroup.center
        ↥(LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G))))) ∧
      ∀ X : Subgroup G, X ≤ ψ.range ⊓ Subgroup.centralizer (E : Set G) → ⁅X, X⁆ = X →
        X ≤ LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G)) := by
  classical
  obtain ⟨r, D, d, _, _, _, θ, hθinj, hθrange⟩ :=
    exists_piGL_centralizer (LinTorus.inducedMatrices ψ E)
      (natCast_card_inducedMatrices_ne_zero hker hp hp2 hE)
  have : ∀ i, CharP (D i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap F (D i)).injective 2
  set ι : SpecialLinearGroup (Fin (m + 1)) F →* GL (Fin (m + 1)) F :=
    SpecialLinearGroup.toGL with hιdef
  have hιinj : Function.Injective ι := SpecialLinearGroup.toGL_injective
  have hC₀θ : ggCentSL ψ E = θ.range.comap ι := by rw [hθrange]; rfl
  set S : {b : Fin r // GoodBlock D d b} → Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
    fun b => ((blockSL D d b.1).map θ).comap ι with hSdef
  have hSrange : ∀ b : {b : Fin r // GoodBlock D d b}, (blockSL D d b.1).map θ ≤ ι.range := by
    intro b
    have hperf : ⁅blockSL D d b.1, blockSL D d b.1⁆ = blockSL D d b.1 :=
      CFSG.RankThree.PartOne.KCUnitary.commutator_eq_of_isPerfect
        (isPerfect_blockSL b.1 b.2.1 b.2.2)
    rw [← hperf, Subgroup.map_commutator]
    refine (Subgroup.commutator_mono le_top le_top).trans ?_
    rw [← _root_.commutator_def, hιdef, SpecialLinearGroup.range_toGL_eq_ker_det]
    exact Abelianization.commutator_subset_ker _
  have hSmap : ∀ b, (S b).map ι = (blockSL D d b.1).map θ := fun b =>
    Subgroup.map_comap_eq_self (hSrange b)
  have hÑmap : (⨆ b, S b).map ι = (goodSL D d).map θ := by
    rw [Subgroup.map_iSup, goodSL, Subgroup.map_iSup]
    exact iSup_congr hSmap
  refine (ggLayer_of_core ψ hker (map_ggCentSL_le hEA) (normal_map_ggCentSL hker)
    (commutator_le_map_ggCentSL hker) S (fun b => ?_) (fun b c hc s hs => ?_) (fun b => ?_) ?_
    ?_).2
  ·
    rw [hC₀θ]
    exact Subgroup.comap_mono (Subgroup.map_le_range θ _)
  ·
    rw [hC₀θ] at hc
    obtain ⟨w, hw⟩ := hc
    obtain ⟨g, hg, hgs⟩ := hs
    refine ⟨w * g * w⁻¹, conj_mem_blockSL b.1 w hg, ?_⟩
    rw [map_mul, map_mul, map_inv, hw, hgs, map_mul, map_mul, map_inv]
  ·
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (((Subgroup.equivMapOfInjective _ θ hθinj).trans
        (MulEquiv.subgroupCongr (hSmap b)).symm).trans
          (Subgroup.equivMapOfInjective _ ι hιinj).symm)
      (isQuasisimple_blockSL b.1 b.2.1 b.2.2)
  ·
    obtain ⟨k, hk⟩ := exists_derivedSeries_le_goodSL (E := D) (m := d)
    refine ⟨k, ?_⟩
    rw [← Subgroup.map_le_map_iff_of_injective hιinj, map_ggDer, hÑmap]
    calc ggDer ((ggCentSL ψ E).map ι) k ≤ ggDer θ.range k :=
          ggDer_mono (by rw [hC₀θ]; exact Subgroup.map_comap_le _ _) k
      _ = (ggDer ⊤ k).map θ := by rw [map_ggDer, ← MonoidHom.range_eq_map]
      _ = (derivedSeries _ k).map θ := by rw [ggDer_top]
      _ ≤ (goodSL D d).map θ := Subgroup.map_mono hk
  ·
    intro z hz hzc hz2
    obtain ⟨w, hw, hwz⟩ : ι z ∈ (goodSL D d).map θ := hÑmap ▸ Subgroup.mem_map_of_mem ι hz
    have hwc : ∀ g ∈ goodSL D d, w * g = g * w := by
      intro g hg
      obtain ⟨y, hy, hyg⟩ : θ g ∈ (⨆ b, S b).map ι := hÑmap ▸ Subgroup.mem_map_of_mem θ hg
      apply hθinj
      rw [map_mul, map_mul, hwz, ← hyg, ← map_mul, ← map_mul, hzc y hy]
    have hw2 : w ^ 2 = 1 := by
      apply hθinj
      rw [map_pow, hwz, map_one, ← map_pow, hz2, map_one]
    apply hιinj
    rw [← hwz, eq_one_of_mem_goodSL_of_commute hw hwc hw2, map_one, map_one]

end LayerFacts

end CFSG.StandardType
