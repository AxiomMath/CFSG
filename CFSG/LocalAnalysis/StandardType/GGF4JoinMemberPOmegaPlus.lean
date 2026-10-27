module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinF4
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1POmegaPlus
import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoCommon
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedPSU
import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberPSL
import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGSelectedSiegelPair
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinGuardedOmega
import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlus
import all CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaPlusFE
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEOmegaFourMinusPOmegaPlus

public section

namespace CFSG.StandardType.F4JoinPOmegaPlus

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal
  CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieAdmissible)

theorem exists_block_of_actual_component
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G} {k f : ℕ}
    {ψ : (ggU .POmegaPlus (k + 3) f).K →* G}
    (hcfg : GGConfig p B Bs x L D J)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .POmegaPlus (k + 3) f).D
      .POmegaPlus (k + 3) f ψ)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hq : CFSG.Assembly.IsQuasisimple ↥X) :
    ∃ s : (ggU .POmegaPlus (k + 3) f).K,
      Odd (orderOf (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s)) ∧
      ∃ ε : Matrix (Fin (k + 3) ⊕ Fin (k + 3))
        (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f),
        IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
          (Algebra.adjoin (GaloisField 2 f)
            (Units.val '' {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s})) ε ∧
        ∃ X' : Subgroup (ggU .POmegaPlus (k + 3) f).K,
          IsComponentOf X'
            ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))
                {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s} ε :
                Subgroup (ggU .POmegaPlus (k + 3) f).K),
              (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))
                {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s} ε :
                Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆ ∧
          X'.map ψ = X := by
  obtain ⟨hp, hp2, -⟩ := (hcfg.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨z, -, hzG, hzp, hX⟩ := ggActualMember_internal_component hcfg horigin hq
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  have hf : 1 ≤ f := hadm.2.1
  have hdiag : GGPsiInnerDiag (ggU .POmegaPlus (k + 3) f).D ψ z :=
    ggPsiInnerDiag_of_mem_range _ (by simpa only [hrange] using hzG)
  have hXc : IsComponentOf X (ψ.range ⊓ Subgroup.centralizer {z}) := by
    simpa only [hrange] using hX
  obtain ⟨s, -, hs⟩ := RCKRP.rckF1_POmegaPlus hp hp2 hzp hf ψ rfl hker hdiag hXc
  exact ⟨s, hs⟩

section GuardedBlocks

theorem false_of_guarded_omega_four_minus_block
    {G : Type} [Group G] {k f : ℕ} (hf : 1 ≤ f)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* G)
    (hψ : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) f).K)
    {lab : LargeEvenLabel} (hg : GuardedLargeEvenLabel lab)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
      (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    {C : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hC : IsComponentOf C
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε < 2)
    (hrank : ε.rank = 4)
    (hminus : ∀ x y : (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f,
      Matrix.mulVec ε x = x → Matrix.mulVec ε y = y →
      Spin.quadPlus (k + 3) (GaloisField 2 f) x = 0 →
      Spin.quadPlus (k + 3) (GaloisField 2 f) y = 0 →
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y])
    (hM : MarkedModel lab (↥(C.map ψ) ⧸ Subgroup.center ↥(C.map ψ))) : False := by
  have hc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨η⟩ := feomeg_component_iso (k + 3) (GaloisField 2 f) (by omega) f hc
    S hSU hS hodd hε hC hdeg hrank hminus
  obtain ⟨ξ⟩ := feomeg_quotientCenter ψ hψ hC.2.2.1
  have hmodel : LieModel (↥(C.map ψ) ⧸ Subgroup.center ↥(C.map ψ)) .PSL 2 2 (2 * f) := by
    refine Or.inl ⟨by decide, ?_⟩
    refine ⟨feomeg_admissible f hf, GaloisField 2 (2 * f), inferInstance, inferInstance, ?_, ?_⟩
    · exact GaloisField.card 2 (2 * f) (by omega)
    · exact ⟨ξ.symm.trans η⟩
  exact false_of_guardedLabel_of_linear_unitary_model hg hM (Or.inl rfl)
    (fun _ => by omega) hmodel

theorem false_of_guarded_small_linear_model
    {X : Type} [Group X] {lab : LargeEvenLabel}
    (hg : GuardedLargeEvenLabel lab) (hM : MarkedModel lab X)
    {r f : ℕ} (hr : r < 6) (hmodel : LieModel X .PSL r 2 f) : False := by
  obtain ⟨-, hA, hrank⟩ := guarded_lieModel_PSL hg hM hmodel
  have hguardA : 5 ≤ lab.rank ∧ lab.n = 1 := by
    simpa [GuardedLargeEvenLabel, hA] using hg
  omega

theorem orthogonal_shape_of_guarded_selfDual_model
    {G U : Type} [Group G] [Group U] {f : ℕ} (hf : 1 ≤ f)
    (ψ : U →* G) (hψ : ψ.ker ≤ Subgroup.center U) {C : Subgroup U}
    (hns : ¬ Group.IsSolvable C) {lab : LargeEvenLabel}
    (hg : GuardedLargeEvenLabel lab)
    (hM : MarkedModel lab (↥(C.map ψ) ⧸ Subgroup.center ↥(C.map ψ)))
    {t : CFSG.Open.StatedLieTag} {m : ℕ} (ι : (ggU t m f).K →* U)
    (hcent : ∀ y, ι y ∈ Subgroup.center U → y ∈ Subgroup.center (ggU t m f).K)
    (hrange : ι.range = C)
    (hcase : ((t = .POmegaPlus ∨ t = .POmegaMinus) ∧ 3 ≤ m) ∨ (t = .PSL ∧ m = 2)) :
    (t = .POmegaPlus ∨ t = .POmegaMinus) ∧ 4 ≤ m := by
  have hrange' : (ψ.comp ι).range = C.map ψ := by
    rw [MonoidHom.range_comp, hrange]
  have hker : (ψ.comp ι).ker ≤ Subgroup.center (ggU t m f).K :=
    fun y hy => hcent y (hψ hy)
  rcases hcase with ⟨ht, hm3⟩ | ⟨rfl, rfl⟩
  · by_cases hm4 : 4 ≤ m
    · exact ⟨ht, hm4⟩
    · obtain rfl : m = 3 := by omega
      rcases ht with rfl | rfl
      · obtain ⟨eK, -⟩ := RCKRP.irgIsoCompat_omegaPlus_three (g := f) hf
        have hadm : StatedLieAdmissible .PSL 4 2 f :=
          ⟨Nat.prime_two, hf, by omega,
            fun h => by have := (Prod.mk.inj h).1; omega,
            fun h => by have := (Prod.mk.inj h).1; omega⟩
        have hmodel := RCKRP.irg_lieModel_quot (Or.inl rfl) hadm
          ((ψ.comp ι).comp eK.symm.toMonoidHom)
          (by rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eK.symm.surjective,
            ← MonoidHom.range_eq_map, hrange'])
          (fun y hy => Subgroup.comap_center_le_center eK.symm.injective (hker hy))
        exact (false_of_guarded_small_linear_model hg hM (by omega) hmodel).elim
      · obtain ⟨eK, -⟩ := RCKRP.irgIsoCompat_omegaMinus_three (g := f) hf
        have hadm : StatedLieAdmissible .PSU 4 2 f :=
          ⟨Nat.prime_two, hf, by omega, fun h => by have := (Prod.mk.inj h).1; omega⟩
        have hmodel := RCKRP.irg_lieModel_quot (Or.inr (Or.inl rfl)) hadm
          ((ψ.comp ι).comp eK.symm.toMonoidHom)
          (by rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eK.symm.surjective,
            ← MonoidHom.range_eq_map, hrange'])
          (fun y hy => Subgroup.comap_center_le_center eK.symm.injective (hker hy))
        exact (false_of_guardedLabel_of_linear_unitary_model hg hM (Or.inr rfl)
          (fun h => by cases h) hmodel).elim
  · rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · obtain rfl : f = 1 := by omega
      obtain ⟨χ⟩ := RCKRP.rckRP_nonempty_mulEquiv_PSL_two_PSp_one (f := 1) le_rfl
      have hq2 : Nat.card (GaloisField 2 1) = 2 := by
        rw [GaloisField.card 2 1 (by omega)]
        norm_num
      have hsolSp : Group.IsSolvable (ggU .PSp 1 1).K :=
        CFSG.AGLEmbedding.LeviBlock.spFlag_isSolvable_Sp (Or.inr ⟨rfl, hq2⟩)
      have hsolA : Group.IsSolvable (ggU .PSL 2 1).K :=
        Group.isSolvable_of_surjective (f := χ.symm.toMonoidHom) χ.symm.surjective
      have hsolC : Group.IsSolvable ι.range :=
        @FieldTwoPSp.isSolvable_range _ _ _ _ ι hsolA
      exact (hns (hrange ▸ hsolC)).elim
    · have hq4 : 4 ≤ 2 ^ f := by
        change 2 ^ 2 ≤ 2 ^ f
        exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hf2
      have hadm : StatedLieAdmissible .PSL 2 2 f :=
        ⟨Nat.prime_two, hf, le_rfl,
          fun h => by have := (Prod.mk.inj h).2; omega,
          fun h => by have := (Prod.mk.inj h).2; omega⟩
      have hmodel := RCKRP.irg_lieModel_quot (Or.inl rfl) hadm (ψ.comp ι) hrange' hker
      exact (false_of_guarded_small_linear_model hg hM (by omega) hmodel).elim

theorem selected_of_orthogonal_block_model
    {G : Type} [Group G] {k f m : ℕ} {t : CFSG.Open.StatedLieTag}
    (hk : 1 ≤ k) (hf : 1 ≤ f) (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (hm : 4 ≤ m)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* G)
    (hψ : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) f).K)
    (ι : (ggU t m f).K →* ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))))
    (hcent : ∀ y, ι y ∈ Subgroup.center ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) →
      y ∈ Subgroup.center (ggU t m f).K)
    {L : Subgroup G}
    (hrange : (ι.range).map (show ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) →* G
      from ψ) = L)
    (hadm : StatedLieAdmissible t m 2 f) (hrk : 2 ≤ (ggU t m f).D.rank)
    {β₀ : Fin (ggU t m f).D.rank → ℤ} (hlong : GGLongRoot (ggU t m f).D β₀)
    (a₁ a₂ b₁ b₂ : (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f)
    (hQ : Spin.quadPlus (k + 3) (GaloisField 2 f) a₁ = 0 ∧
      Spin.quadPlus (k + 3) (GaloisField 2 f) a₂ = 0 ∧
      Spin.quadPlus (k + 3) (GaloisField 2 f) b₁ = 0 ∧
      Spin.quadPlus (k + 3) (GaloisField 2 f) b₂ = 0)
    (h₁ : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ b₁ = 0)
    (hX : (((ggU t m f).D.rootGroup β₀).map ι).map
      (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
      siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂)
    (hX' : (((ggU t m f).D.rootGroup (-β₀)).map ι).map
      (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
      siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₁ b₂) :
    ∃ S : Subgroup G, MemberSelectedSL2At L S ∧ PresentedSelectedSL2At ψ S := by
  obtain ⟨δ, model, -, hpres⟩ := SiegelPair.exists_presented_of_siegelBlock_POmegaPlus
    hk hf ht hm ψ ι hlong a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀ hX hX'
  let ψ₀ : ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) →* G := ψ
  let lam : (ggU t m f).K →* G := ψ₀.comp ι
  have hker : lam.ker ≤ Subgroup.center (ggU t m f).K := by
    intro y hy
    exact hcent y (hψ hy)
  have hmap : lam.range = L := by
    rw [MonoidHom.range_comp]
    exact hrange
  refine ⟨(lam.comp model.phi).range, ?_, hpres⟩
  exact ⟨t, m, f, lam, hadm, hrk, hker, hmap, GaloisField 2 f,
    inferInstance, inferInstance, inferInstance, δ, model, rfl⟩

end GuardedBlocks

theorem _root_.CFSG.StandardType.ggActualMember_POmegaPlus_selected
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ}
    (ψ : (ggU .POmegaPlus n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .POmegaPlus n f).D .POmegaPlus n f ψ)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At ψ S := by
  have hadm := hpres.1.1
  have hf : 1 ≤ f := hadm.2.1
  have hn : 4 ≤ n := hadm.2.2
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hk : 1 ≤ k := by omega
  obtain ⟨s, hsodd, ε, hε, C, hC, hCmap⟩ :=
    exists_block_of_actual_component hcfg hpres horigin (isQuasisimple_of_largeEvenMarking hmark)
  let F := GaloisField 2 f
  letI : Fintype F := Fintype.ofFinite F
  let U := spinGroup (Spin.quadPlus (k + 3) F)
  let ψ₀ : U →* G := ψ
  have hψ₀ : ψ₀.ker ≤ Subgroup.center U := hpres.2.1.2
  have hZ : Subgroup.center U = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.q2Omega_center_spinGroup_quadPlus_eq_bot (by omega)
  have hψinj : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hψ₀.trans hZ.le
  let C₀ : Subgroup U := C
  have hmap : C₀.map ψ₀ = X := hCmap
  let eC : C₀ ≃* X :=
    (C₀.equivMapOfInjective ψ₀ hψinj).trans (MulEquiv.subgroupCongr hmap)
  have hmarkC : LargeEvenMarking C₀ (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab) :=
    largeEvenMarking_of_mulEquiv eC hmark
  let j : U →* GL (Fin (k + 3) ⊕ Fin (k + 3)) F :=
    Spin.spinMatrix (Spin.quadPlus (k + 3) F)
  have hj : Function.Injective j := (MonoidHom.ker_eq_bot_iff j).mp
    (Spin.ker_spinMatrix_quadPlus_eq_bot (CharP.cast_eq_zero F 2))
  have hr : j.range = CFSG.Open.StatedOmega ⇑(Spin.quadPlus (k + 3) F) :=
    AutOm.range_spinMatrix_plus (K := F) (n := k + 3) (by omega)
  let s₀ : U := s
  have hodd : Odd (orderOf s₀) := by
    rw [← orderOf_injective j hj s₀]
    exact hsodd
  have hC₀ : IsComponentOf C₀ ⁅glBlockCentralizer j {j s₀} ε,
      glBlockCentralizer j {j s₀} ε⁆ := hC
  obtain ⟨he, hfixed, hdegree, hdim⟩ := ClassicalBlocks.omega_block_facts_of_guarded_component
    (Spin.quadPlus (k + 3) F) (Spin.nondegenerate_polarBilin_quadPlus (k + 3) F)
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
    j hj hr s₀ hodd hε hC₀ hmarkC
  have hSU : ∀ y ∈ ({j s₀} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) F)), y ∈ j.range := by
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact ⟨s₀, rfl⟩
  have hS : ∀ y ∈ ({j s₀} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) F)),
      ∀ z ∈ ({j s₀} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) F)), Commute y z := by
    intro y hy z hz
    obtain rfl := Set.mem_singleton_iff.mp hy
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact Commute.refl _
  have hoddS : ∀ y ∈ ({j s₀} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) F)), Odd (orderOf y) := by
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact hsodd
  have hdeg : blockDegree (Algebra.adjoin F
      (Units.val '' ({j s₀} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) F)))) ε < 2 := by omega
  obtain ⟨lab, -, R, _, I, F₀, theta, -, -, hguard, hmarked⟩ :=
    largeEvenMarking_exists_markedModel hmark
  have hML : MarkedModel lab (↥X ⧸ Subgroup.center ↥X) :=
    MarkedModel.of_mulEquiv theta.symm hmarked
  have hMC : MarkedModel lab (↥(C₀.map ψ₀) ⧸ Subgroup.center ↥(C₀.map ψ₀)) := by
    rw [hmap]
    exact hML
  have hnm : ¬ (ε.rank = 4 ∧ ∀ v w : (Fin (k + 3) ⊕ Fin (k + 3)) → F,
      Matrix.mulVec ε v = v → Matrix.mulVec ε w = w →
      Spin.quadPlus (k + 3) F v = 0 → Spin.quadPlus (k + 3) F w = 0 →
      QuadraticMap.polar (Spin.quadPlus (k + 3) F) v w = 0 → ¬ LinearIndependent F ![v, w]) := by
    rintro ⟨hrank, hm⟩
    exact false_of_guarded_omega_four_minus_block hf ψ hpres.2.1.2 hguard
      {j s₀} hSU hS hoddS hε hC hdeg hrank hm hMC
  obtain ⟨t, m, ι, β₀, hcase, hlong, hcent, hirange, a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, hX, hX'⟩ :=
    exists_blockModel_selfDual_POmegaPlus_explicit k f hf {j s₀} hSU hS hoddS
      he hε.2.2.2.1 hdeg hnm hC₀
  have ht : (t = .POmegaPlus ∨ t = .POmegaMinus) ∧ 4 ≤ m :=
    orthogonal_shape_of_guarded_selfDual_model hf ψ₀ hψ₀
      (FieldTwoPSp.not_isSolvable_of_isComponentOf hC₀) hguard hMC ι hcent hirange
      (hcase.imp (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩))
  have hmember : StatedLieAdmissible t m 2 f ∧ 2 ≤ (ggU t m f).D.rank := by
    rcases ht.1 with rfl | rfl
    · obtain ⟨l, rfl⟩ : ∃ l, m = l + 3 := ⟨m - 3, by omega⟩
      exact ⟨⟨Nat.prime_two, hf, ht.2⟩, by change 2 ≤ l + 3; omega⟩
    · exact ⟨⟨Nat.prime_two, hf, ht.2⟩, by change 2 ≤ m - 1; omega⟩
  exact selected_of_orthogonal_block_model hk hf ht.1 ht.2 ψ hpres.2.1.2 ι hcent
    (by rw [hirange]; exact hmap) hmember.1 hmember.2 hlong
    a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀ hX hX'

end CFSG.StandardType.F4JoinPOmegaPlus
