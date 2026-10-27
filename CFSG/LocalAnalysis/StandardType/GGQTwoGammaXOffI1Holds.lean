module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXInnerBCCell
public import CFSG.LocalAnalysis.StandardType.GGQ2PmHeartA
public import CFSG.LocalAnalysis.StandardType.GGQ2HeartBI1
public import CFSG.LocalAnalysis.StandardType.GGQ2LabelCartan

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2_pmW_heartA {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {r : ℕ} (e : Fin r ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A r i j) (hr : 4 ≤ r) (hB : M.ShapeB)
    (T : M.toWDatum.V ≃ₗ[ZMod 3] M.toWDatum.V)
    (hT : T ∈ Subgroup.normalizer
      (M.toWDatum.weyl : Set (M.toWDatum.V ≃ₗ[ZMod 3] M.toWDatum.V))) :
    ∃ w ∈ M.toWDatum.weyl, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : M.toWDatum.V, T (w v) - ε • v ∈ Submodule.span (ZMod 3) {M.xV} := by
  classical
  obtain ⟨-, -, hxVn, hsupB⟩ := hB
  have hcoSpan : M.coSpan =
      Submodule.span (ZMod 3) (Set.range fun j : Fin r => M.coroot (e j)) := by
    rw [GGQ2LDatum.coSpan]
    congr 1
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, by simp⟩
    · rintro ⟨k, rfl⟩
      exact ⟨e k, rfl⟩
  have hxH : M.xV ∉
      Submodule.span (ZMod 3) (Set.range fun j : Fin r => M.coroot (e j)) := by
    rw [← hcoSpan]
    exact hxVn
  have hsup : Submodule.span (ZMod 3) (Set.range fun j : Fin r => M.coroot (e j)) ⊔
      Submodule.span (ZMod 3) {M.xV} = ⊤ := by
    rw [← hcoSpan]
    exact hsupB
  have hweyl : ggQ2WeylOf (fun j : Fin r => M.coroot (e j))
      (fun j : Fin r => M.root (e j)) = M.toWDatum.weyl := by
    change Subgroup.closure {t : M.V ≃ₗ[ZMod 3] M.V |
        ∃ j : Fin r, ∀ v, t v = v - (fun j : Fin r => M.root (e j)) j v •
          (fun j : Fin r => M.coroot (e j)) j} =
      Subgroup.closure (Set.range M.toWDatum.simpleRefl)
    congr 1
    ext t
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨e j, LinearEquiv.ext fun v =>
        (GGQ2WDatum.simpleRefl_apply M.toWDatum (e j) v).trans (hj v).symm⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨j, rfl⟩ := e.surjective k
      exact ⟨j, fun v => GGQ2WDatum.simpleRefl_apply M.toWDatum (e j) v⟩
  have hxmem : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [M.fixed_x]
    exact Submodule.subset_span (Set.mem_singleton M.xV)
  have hxfix : ∀ ψ ∈ ggAutomizer L Bs, ggLin (p := 3) M.model ψ M.xV = M.xV :=
    mem_ggFixedSubmodule_iff.mp hxmem
  have hxk : ∀ j : Fin r, M.root (e j) M.xV = 0 := by
    intro j
    have hmem : M.simple (e j) ∈ ggAutomizer L Bs := by
      rw [M.automizer_L]
      exact Subgroup.subset_closure ⟨e j, rfl⟩
    have h := hxfix (M.simple (e j)) hmem
    rw [M.simple_apply] at h
    have hsm : M.root (e j) M.xV • M.coroot (e j) = 0 := sub_eq_self.mp h
    have hc : M.coroot (e j) ≠ 0 := by
      intro h0
      have h2 : M.root (e j) (M.coroot (e j)) = 2 := by
        rw [M.pairing (e j) (e j), M.isCartan.1 (e j)]
        norm_num
      rw [h0, map_zero] at h2
      exact absurd h2 (by decide)
    exact (smul_eq_zero.mp hsm).resolve_right hc
  have hfix : ∀ v : M.V, (∀ j : Fin r, M.root (e j) v = 0) →
      v ∈ Submodule.span (ZMod 3) {M.xV} := by
    intro v hv
    have hroot : ∀ k : M.Λ, M.root k v = 0 := by
      intro k
      have := hv (e.symm k)
      simpa only [Equiv.apply_symm_apply] using this
    have hfixall : ∀ ψ ∈ ggAutomizer L Bs, ggLin (p := 3) M.model ψ v = v := by
      intro ψ hψ
      rw [M.automizer_L] at hψ
      refine Subgroup.closure_induction (k := Set.range M.simple)
        (p := fun ψ _ => ggLin (p := 3) M.model ψ v = v) ?_ ?_ ?_ ?_ hψ
      · rintro ψ ⟨k, rfl⟩
        rw [M.simple_apply, hroot k, zero_smul, sub_zero]
      · simp
      · intro a c _ _ iha ihc
        rw [map_mul, LinearEquiv.mul_apply, ihc, iha]
      · intro a _ iha
        rw [map_inv]
        change (ggLin (p := 3) M.model a).symm v = v
        apply LinearEquiv.injective (ggLin (p := 3) M.model a)
        rw [LinearEquiv.apply_symm_apply, iha]
    have hmem : v ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) :=
      mem_ggFixedSubmodule_iff.mpr hfixall
    rw [M.fixed_x] at hmem
    exact hmem
  have hα : ∀ i j : Fin r, M.root (e i) (M.coroot (e j)) =
      ((CartanMatrix.A r i j : ℤ) : ZMod 3) := by
    intro i j
    calc M.root (e i) (M.coroot (e j))
        = (M.cartan (e i) (e j) : ZMod 3) := M.pairing (e i) (e j)
      _ = ((CartanMatrix.A r i j : ℤ) : ZMod 3) := by rw [hC i j]
  have hT' : T ∈ Subgroup.normalizer (ggQ2WeylOf (fun j : Fin r => M.coroot (e j))
      (fun j : Fin r => M.root (e j)) : Set (M.V ≃ₗ[ZMod 3] M.V)) := by
    rw [hweyl]
    exact hT
  obtain ⟨w, hw, ε, hε, hwε⟩ :=
    ggHA_pm hr (fun j : Fin r => M.coroot (e j)) (fun j : Fin r => M.root (e j))
      hα M.xV hxH hsup hxk hfix T hT'
  rw [hweyl] at hw
  exact ⟨w, hw, ε, hε, hwε⟩

theorem ggQ2_gammaX_of_heartA (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card (ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) {r : ℕ} (e : Fin r ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A r i j) (hr : 4 ≤ r) (hB : M.ShapeB) :
    GGQ2GammaX 3 B Bs x L D J := by
  refine ggQ2xd_gammaX_of_datumPM hLB hP hS rfl hCav M ?_
  intro u₀ _ hfix _ _ _ T hT
  obtain ⟨w, hw, ε, hε, hwε⟩ := ggQ2_pmW_heartA M e hC hr hB T hT
  have hxmem : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [M.fixed_x]
    exact Submodule.subset_span (Set.mem_singleton M.xV)
  have hxV : M.xV ∈ Submodule.span (ZMod 3) {u₀} := by
    refine (hfix M.xV).mp fun g hg => ?_
    rw [M.weyl_eq_map] at hg
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hg
    exact mem_ggFixedSubmodule_iff.mp hxmem ψ hψ
  have hle : Submodule.span (ZMod 3) {M.xV} ≤ Submodule.span (ZMod 3) {u₀} :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hxV
  exact ⟨w, hw, ε, hε, fun v => hle (hwε v)⟩

theorem ggQ2_gammaXOffI1_holds (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hT : GGQ2TableBI1Fail) (hI : GGQ2HeartBI1) (hG : GGQ2GammaXOffI1GraphInput) :
    GGQ2GammaXOffI1Input := by
  intro G _ _ p B Bs x L D J hS hp hnI hCav
  subst hp
  obtain ⟨lab, hlab, hTB, hmark, M, hLW, hshape, -⟩ := hT hS rfl hnI
  by_cases hgr : lab.tag = .D ∨ lab.tag = .F4
  · exact hG hS rfl hnI hCav ⟨hlab, hTB, hmark⟩ hgr M hLW hshape
  by_cases hinn : GGQ2InnerLabel lab
  · exact ggQ2_gammaX_of_innerLabel hLB hP hS hCav M hLW hinn
  by_cases hbc : GGQ2InnerLabelBC lab
  · exact ggQ2_gammaX_of_innerBCLabel hLB hP hS hCav M hLW hbc
  have hdetlab : GGQ2DetLabel lab := by
    rcases hTB with ⟨htag, h4⟩ | ⟨htag, h4⟩ | ⟨htag, -, -⟩ | ⟨htag, hodd, h4⟩ | htag | htag |
        htag | htag
    · by_cases h3 : 3 ∣ lab.rank + 1
      · exact Or.inl ⟨htag, h3⟩
      · exact absurd (Or.inl ⟨htag, h4, h3⟩) hinn
    · exact absurd (Or.inl ⟨htag, h4⟩) hbc
    · exact absurd (Or.inl htag) hgr
    · refine absurd (Or.inr ⟨htag, hodd, ?_⟩) hbc
      obtain ⟨k, hk⟩ := hodd
      omega
    · exact absurd (Or.inr htag) hgr
    · exact Or.inr htag
    · exact absurd (Or.inr (Or.inl htag)) hinn
    · exact absurd (Or.inr (Or.inr htag)) hinn
  by_cases hB : M.ShapeB
  · rcases hdetlab with ⟨htag, -⟩ | htag
    ·
      have hr : 4 ≤ lab.rank := by simpa [GGQ2TBLabel, htag] using hTB
      rcases ggQ2_label_cartan M hLW hTB with ⟨-, e, hC⟩ | h | h | h | h | h | h
      · exact ggQ2_gammaX_of_heartA hLB hP hS hCav M e hC hr hB
      all_goals simp [htag] at h
    ·
      exact absurd (hI hS htag hlab hmark M hLW hB) hnI
  · exact ggQ2_gammaX_of_detLabel hLB hP hS hCav M hLW hshape hdetlab hB

end CFSG.StandardType

end
