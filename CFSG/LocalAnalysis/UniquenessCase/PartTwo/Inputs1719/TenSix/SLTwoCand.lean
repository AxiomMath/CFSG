module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.SLTwoFstar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

private theorem fstarTop_eq_top_of_isQuasisimple {H : Type} [Group H] [Finite H]
    (h : CFSG.IsQuasisimple H) : fstarTop H = ⊤ := by
  have hq : CFSG.IsQuasisimple ↥(⊤ : Subgroup H) :=
    (CFSG.IsQuasisimple.congr (Subgroup.topEquiv (G := H))).mpr h
  rw [fstarTop, Fstar, CFSG.Adapters.genFittingFStar_eq_foundations,
    CFSG.WholeGroup.generalizedFitting_eq_top_of_isQuasisimple hq]
  rw [Subgroup.map_top, Subgroup.range_subtype]

theorem aCandidate_le_of_sl2
    {H : Type} [Group H] [Finite H] {F : Type} [Field F] [Finite F]
    (hF2 : (2 : F) ≠ 0) (h3 : 3 < Nat.card F) (φ : Matrix.SpecialLinearGroup (Fin 2) F →* H)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) {n : ℕ}
    (c : ACandidate H n) : (9 < Nat.card F → n ≤ 1) ∧ n ≤ 2 := by
  classical
  let := c.commGroup
  let := c.finiteW
  have h4 : 4 ≤ Nat.card F := by omega
  have hSLq : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.Quasithin.C126.Nat.isQuasisimple_sl2 h4
  have hHq : CFSG.IsQuasisimple H :=
    CFSG.LocalCores.isQuasisimple_of_surjective hSLq φ hφ hker
  have hFtop : fstarTop H = ⊤ := fstarTop_eq_top_of_isQuasisimple hHq
  let eTop : ↥(fstarTop H) ≃* H :=
    (MulEquiv.subgroupCongr hFtop).trans (Subgroup.topEquiv (G := H))
  obtain ⟨Z₀, hZ₀, hZ₀c, ⟨e₀⟩⟩ := c.central_factor
  let : Z₀.Normal := hZ₀
  let φ' : Matrix.SpecialLinearGroup (Fin 2) F →* ↥(fstarTop H) :=
    eTop.symm.toMonoidHom.comp φ
  let ψ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥(fstarSubOf c.Y) :=
    e₀.symm.toMonoidHom.comp ((QuotientGroup.mk' Z₀).comp φ')
  have hψsurj : Function.Surjective ψ :=
    e₀.symm.surjective.comp ((QuotientGroup.mk'_surjective Z₀).comp
      (eTop.symm.surjective.comp hφ))
  have hZimg : ∀ z ∈ Z₀, eTop z ∈ Subgroup.center H := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨a, rfl⟩ := eTop.surjective h
    calc eTop a * eTop z = eTop (a * z) := (map_mul eTop a z).symm
      _ = eTop (z * a) := by rw [Subgroup.mem_center_iff.mp (hZ₀c hz) a]
      _ = eTop z * eTop a := map_mul eTop z a
  have hkerψ : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro x hx
    have hx2 : QuotientGroup.mk' Z₀ (φ' x) = 1 := by
      have h1 : e₀.symm (QuotientGroup.mk' Z₀ (φ' x)) = e₀.symm 1 := by
        rw [map_one]
        exact hx
      exact e₀.symm.injective h1
    have hxZ : φ' x ∈ Z₀ := (QuotientGroup.eq_one_iff (φ' x)).mp hx2
    have hφx : φ x ∈ Subgroup.center H := by
      have h := hZimg (φ' x) hxZ
      simpa [φ'] using h
    have hcomm : ∀ y : Matrix.SpecialLinearGroup (Fin 2) F,
        ⁅y, x⁆ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      intro y
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hφx (φ y))
    let q : Matrix.SpecialLinearGroup (Fin 2) F →*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
      QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
    have hqx : q x ∈ Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) y
      have hmem : ⁅y', x⁆ ∈ q.ker := by
        rw [show q.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) from
          QuotientGroup.ker_mk' _]
        exact hcomm y'
      exact commutatorElement_eq_one_iff_mul_comm.mp (by
        rw [← map_commutatorElement]
        exact MonoidHom.mem_ker.mp hmem)
    have hqx1 : q x = 1 := by
      have hc := hqx
      rw [CFSG.GorensteinWalter.psl2_center_eq_bot F] at hc
      exact Subgroup.mem_bot.mp hc
    have hxker : x ∈ q.ker := MonoidHom.mem_ker.mpr hqx1
    rwa [show q.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) from
      QuotientGroup.ker_mk' _] at hxker
  rcases Subgroup.bot_or_exists_ne_one ψ.ker with hbot | ⟨x, hxN, hx1⟩
  · have hLY : Fstar c.Y ≤ c.Y := Subgroup.map_subtype_le _
    let eTarget : ↥(fstarSubOf c.Y) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot)
    let e : ↥(Fstar c.Y) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
      (Subgroup.subgroupOfEquivOfLe hLY).symm.trans eTarget
    have h := aParam_le_of_fstar_sl2 c.expTwo hF2 h3 hLY c.hLgn rfl e
    exact ⟨fun h9 => by rw [c.eq_n]; exact h.1 h9, by rw [c.eq_n]; exact h.2⟩
  · have hcenter : ψ.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      refine le_antisymm hkerψ ?_
      intro z hz
      have hxZ := hkerψ hxN
      rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff x).mp hxZ with hxEq | hxNeg
      · exact absurd hxEq hx1
      · rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff z).mp hz with hzEq | hzNeg
        · rw [hzEq]
          exact ψ.ker.one_mem
        · rw [hzNeg, ← hxNeg]
          exact hxN
    have hLY : Fstar c.Y ≤ c.Y := Subgroup.map_subtype_le _
    let eTarget : ↥(fstarSubOf c.Y) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hcenter)
    let e : ↥(Fstar c.Y) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
      (Subgroup.subgroupOfEquivOfLe hLY).symm.trans eTarget
    have h := aParam_le_of_fstar_psl2 c.expTwo hF2 h3 hLY c.hLgn rfl e
    exact ⟨fun h9 => by rw [c.eq_n]; exact h.1 h9, by rw [c.eq_n]; exact h.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
