module

public import CFSG.LieType.ChevTwo.Defs
import CFSG.LieType.ChevTwo.Orthogonal
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.OmegaFacts
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDGen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918OmegaLinear
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918OmegaTransv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.LieType.ChevTwo

private abbrev PlusOmega : Type := ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2)))

theorem nonempty_mulEquiv_statedSp_plus_of_induced
    (α : MulAut ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2)))) (hα : α * α = 1)
    (hαout : α ∉ (MulAut.conj : ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2))) →*
      MulAut ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2)))).range)
    (hind : InducedByIso (StatedQuadPlus 4 (ZMod 2)) α)
    (Y : Subgroup ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2))))
    (hY : ∀ y, y ∈ Y ↔ α y = y) (h5 : 5 ∣ Nat.card Y) :
    Nonempty (↥Y ≃* ↥(StatedSp 3 (ZMod 2))) := by
  obtain ⟨g, hgk⟩ := MonoidHom.mem_range.mp
    ((inducedByIso_iff_mem_range (StatedQuadPlus 4 (ZMod 2)) α).1 hind)
  have hG : GoodQ (StatedQuadPlus 4 (ZMod 2)) := goodQ_plus (n := 3) (by norm_num)
  have hg2 : g * g = 1 := by
    apply hG.kappa_injective
    rw [map_mul, hgk, hα, map_one]
  have hg2GL : (g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) * (g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) = 1 := by
    have h := congrArg
      (fun z : isoGrp (StatedQuadPlus 4 (ZMod 2)) => (z : GL (Fin 4 ⊕ Fin 4) (ZMod 2))) hg2
    simpa using h
  have hgΩ : (g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) ∉ StatedOmega (StatedQuadPlus 4 (ZMod 2)) := by
    intro hmem
    exact hαout (show α ∈ (MulAut.conj : PlusOmega →* MulAut PlusOmega).range from
      hgk ▸ (hG.kappa_mem_inner_iff g).2 hmem)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 5 h5
  let d : GL (Fin 4 ⊕ Fin 4) (ZMod 2) := (y : PlusOmega)
  have hd : orderOf d = 5 := by
    dsimp only [d]
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  have hcomm : (g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) * d *
      (g : GL (Fin 4 ⊕ Fin 4) (ZMod 2))⁻¹ = d := by
    have hx : α (y : PlusOmega) = (y : PlusOmega) := (hY (y : PlusOmega)).mp y.2
    have h1 : ((α (y : PlusOmega) : PlusOmega) : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) =
        ((y : PlusOmega) : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :=
      congrArg (fun z : PlusOmega => (z : GL (Fin 4 ⊕ Fin 4) (ZMod 2))) hx
    have hk := hgk ▸ kappa_apply_val (StatedQuadPlus 4 (ZMod 2)) g (y : PlusOmega)
    rw [hk] at h1
    simpa [d] using h1
  have hgd : (g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) * d =
      d * (g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) := by
    have h := congrArg (fun x : GL (Fin 4 ⊕ Fin 4) (ZMod 2) =>
      x * (g : GL (Fin 4 ⊕ Fin 4) (ZMod 2))) hcomm
    simpa [mul_assoc] using h
  have hle := rank_sub_one_le_of_commute_orderOf_five (ι := Fin 4 ⊕ Fin 4)
    (by simp) (g := (g : GL (Fin 4 ⊕ Fin 4) (ZMod 2))) (d := d) hg2GL hd hgd
  have hcard : Fintype.card (Fin 4 ⊕ Fin 4) = 8 := by simp
  rw [hcard] at hle
  norm_num at hle
  have hrank_not_even : ¬ Even (((g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) - 1).rank := by
    intro hev
    refine hgΩ ?_
    have hT : ∃ T : Submodule (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2),
        Module.finrank (ZMod 2) T = 3 ∧
          ∀ x ∈ T, CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2) x = 0 :=
      CFSG.SeitzReduction.SymplecticPilot.pd_exists_totallySingular_of
        (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2))
        (fun k : Fin 3 => (Sum.inl (Fin.castSucc k) : Fin 4 ⊕ Fin 4))
        (Sum.inl_injective.comp (Fin.castSucc_injective 3))
        (by
          intro v hv
          rw [CFSG.LieType.Universal.Spin.quadPlus_apply]
          apply Finset.sum_eq_zero
          intro i _
          have h1 : v (Sum.inr i) = 0 :=
            hv (Sum.inr i) (by rintro ⟨k, hk⟩; exact Sum.inl_ne_inr hk)
          rw [h1, mul_zero])
    have hmem : (g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) ∈
        StatedOmega (⇑(CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2))) :=
      CFSG.SeitzReduction.SymplecticPilot.pdMem_statedOmega_of_even
        (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2))
        (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 4 (ZMod 2)) hT
        (by
          intro v
          rw [← CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedQuadPlus_eq]
          exact g.2 v)
        hev
    rwa [← CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedQuadPlus_eq] at hmem
  have hodd : Odd (((g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) - 1).rank :=
    Nat.not_even_iff_odd.mp hrank_not_even
  have hrank1 : (((g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) - 1).rank = 1 := by
    have h2 : (((g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) - 1).rank ≤ 2 := by
      rcases hle with h | h
      · exact h
      · exact absurd h hrank_not_even
    rcases hodd with ⟨k, hk⟩
    omega
  have htrans := isTransvection_of_rank_sub_one_eq_one hg2GL hrank1
  have htN : (g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) ∈
      Subgroup.normalizer (StatedOmega (StatedQuadPlus 4 (ZMod 2)) :
        Set (GL (Fin 4 ⊕ Fin 4) (ZMod 2))) :=
    isoGrp_le_normalizer (StatedQuadPlus 4 (ZMod 2)) g.2
  obtain ⟨-, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.OmegaFacts.transv_plus_of_two_le
      (n := 3) (by norm_num) htN g.2 htrans
  have hnorm : (StatedOmega (StatedQuadPlus 4 (ZMod 2))).normalizerMonoidHom
      ⟨(g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)), htN⟩ = α := by
    rw [← hgk]
    rfl
  have hYfix : Y = CFSG.LocalAnalysis.GLTheoremB.MovingAround.fixSub α := by
    ext y
    rw [CFSG.LocalAnalysis.GLTheoremB.MovingAround.mem_fixSub]
    exact hY y
  have e' : CFSG.LocalAnalysis.GLTheoremB.MovingAround.fixSub α ≃*
      ↥(StatedSp 3 (ZMod 2)) := by
    rw [← hnorm]
    exact e
  exact ⟨(MulEquiv.subgroupCongr hYfix).trans e'⟩

theorem nonempty_mulEquiv_statedSp_plus_eight
    (α : MulAut ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2)))) (hα : α * α = 1)
    (hαout : α ∉ (MulAut.conj : ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2))) →*
      MulAut ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2)))).range)
    (Y : Subgroup ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2))))
    (hY : ∀ y, y ∈ Y ↔ α y = y) (h5 : 5 ∣ Nat.card Y) :
    Nonempty (↥Y ≃* ↥(StatedSp 3 (ZMod 2))) := by
  obtain ⟨τ, hτ⟩ := omegaPlusEightInvolutions α (by rw [pow_two]; exact hα)
  let α' : MulAut PlusOmega := τ * α * τ⁻¹
  have hα' : α' * α' = 1 := by
    have h : α' = (MulAut.conj τ) α := by
      simp only [α', MulAut.conj_apply]
    rw [h, ← map_mul, hα, map_one]
  have hαout' : α' ∉ (MulAut.conj : PlusOmega →* MulAut PlusOmega).range := by
    rintro ⟨a, ha⟩
    refine hαout ?_
    have hconj : (τ⁻¹ : MulAut PlusOmega) * MulAut.conj a * τ = MulAut.conj (τ⁻¹ a) := by
      ext x
      simp [MulAut.conj_apply]
    have hαeq : α = MulAut.conj (τ⁻¹ a) := by
      calc α = (τ⁻¹ : MulAut PlusOmega) * α' * τ := by
            dsimp only [α']
            group
        _ = (τ⁻¹ : MulAut PlusOmega) * MulAut.conj a * τ := by rw [← ha]
        _ = MulAut.conj (τ⁻¹ a) := hconj
    exact MonoidHom.mem_range.mpr ⟨τ⁻¹ a, hαeq.symm⟩
  let Y' : Subgroup PlusOmega := Y.map τ.toMonoidHom
  have hY' : ∀ y, y ∈ Y' ↔ α' y = y := by
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hxfix : α x = x := (hY x).mp hx
      show α' (τ x) = τ x
      dsimp only [α']
      simp [hxfix]
    · intro hy
      rw [Subgroup.mem_map]
      refine ⟨τ⁻¹ y, ?_, by simp⟩
      rw [hY]
      have h := congrArg (fun z => τ⁻¹ z) hy
      dsimp only [α'] at h
      simpa using h
  have h5' : 5 ∣ Nat.card Y' := by
    change 5 ∣ Nat.card (Y.map τ.toMonoidHom)
    rw [Subgroup.card_map_of_injective τ.injective]
    exact h5
  obtain ⟨e⟩ := nonempty_mulEquiv_statedSp_plus_of_induced α' hα' hαout' hτ Y' hY' h5'
  exact ⟨(Subgroup.equivMapOfInjective Y τ.toMonoidHom τ.injective).trans e⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
