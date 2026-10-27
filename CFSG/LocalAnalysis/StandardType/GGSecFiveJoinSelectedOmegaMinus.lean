module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelected
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPOmegaMinus
public import CFSG.RankThree.PartOne.CTP.SpinCenterEven
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoCommon
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinF4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinGuardedOmega
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSelectedSiegelPair

public section
namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
open CFSG.StandardType.ClassicalPosition

theorem ggActualMember_POmegaMinus_block
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ} (psi : (ggU .POmegaMinus n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .POmegaMinus n f).D .POmegaMinus n f psi)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    let F := GaloisField 2 f
    let Q := Spin.quadMinus n F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
    let psiS : spinGroup Q →* G := psi
    ∃ z : spinGroup Q, Odd (orderOf z) ∧
      ((X = L ∧ psiS z = x) ∨ GGNbr p B x D J (psiS z) X) ∧
      ∃ ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F,
        IsPrimAdjIdemIn (RingHom.id F)
          (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q))
          (Algebra.adjoin F (Units.val '' ({Spin.spinMatrix Q z} :
            Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)))) ε ∧
        CFSG.Assembly.IsComponentOf (X.comap psiS)
          ⁅glBlockCentralizer (Spin.spinMatrix Q) {Spin.spinMatrix Q z} ε,
            glBlockCentralizer (Spin.spinMatrix Q) {Spin.spinMatrix Q z} ε⁆ ∧
        (X.comap psiS).map psiS = X ∧
        LargeEvenMarking ↥(X.comap psiS)
          (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hpres.1.1.2.1
  have hn : 4 ≤ n := hpres.1.1.2.2
  let : NeZero f := ⟨by omega⟩
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  let F := GaloisField 2 f
  let Q := Spin.quadMinus n F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
  let psiS : spinGroup Q →* G := psi
  change ∃ z : spinGroup Q, _
  have hirr := minusCoeffs_irr 2 f
  have hcenter : Subgroup.center (spinGroup Q) = ⊥ :=
    CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot hn hirr
  have hkerle : psiS.ker ≤ Subgroup.center (spinGroup Q) := hpres.2.1.2
  have hker : psiS.ker = ⊥ := le_antisymm (hkerle.trans_eq hcenter) bot_le
  have hinj : Function.Injective psiS := (MonoidHom.ker_eq_bot_iff psiS).mp hker
  have hq : CFSG.Assembly.IsQuasisimple ↥X := isQuasisimple_of_largeEvenMarking hmark
  obtain ⟨z, hodd, hz, hX, hmap⟩ :=
    ggActualMember_injective_model hcfg psiS hinj hpres.2.1.1 horigin hq
  let j := Spin.spinMatrix Q
  have hj : Function.Injective j := (MonoidHom.ker_eq_bot_iff j).mp
    (Spin.ker_spinMatrix_quadMinus_eq_bot hirr (CharP.cast_eq_zero F 2))
  have hcentral : (Subgroup.centralizer {j z}).comap j = Subgroup.centralizer {z} := by
    ext u
    constructor
    · intro h
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro v hv
      have hvz : v = z := Set.mem_singleton_iff.mp hv
      subst v
      apply hj
      exact (j.map_mul z u).trans
        ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp h) (j z) rfl).trans
          (j.map_mul u z).symm)
    · intro h
      apply Subgroup.mem_comap.mpr
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro v hv
      have hvz : v = j z := Set.mem_singleton_iff.mp hv
      subst v
      exact (j.map_mul z u).symm.trans
        ((congrArg j (Subgroup.mem_centralizer_iff.mp h z rfl)).trans (j.map_mul u z))
  have hXj : CFSG.Assembly.IsComponentOf (X.comap psiS)
      ((Subgroup.centralizer {j z}).comap j) := hcentral.symm ▸ hX
  obtain ⟨ε, hε, hXε⟩ := exists_isComponentOf_glBlockCentralizer_POmegaMinus n hirr hn
    {j z} (by intro a ha b hb; rcases ha with rfl; rcases hb with rfl; exact Commute.refl _)
    hXj
  let eX : (X.comap psiS) ≃* X :=
    (Subgroup.equivMapOfInjective (X.comap psiS) psiS hinj).trans
      (MulEquiv.subgroupCongr hmap)
  exact ⟨z, hodd, hz, ε, hε, hXε, hmap, largeEvenMarking_of_mulEquiv eX hmark⟩

section GuardedFixed

theorem ggActualMember_POmegaMinus_fixed_block
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ} (psi : (ggU .POmegaMinus n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .POmegaMinus n f).D .POmegaMinus n f psi)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    let F := GaloisField 2 f
    let Q := Spin.quadMinus n F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
    let psiS : spinGroup Q →* G := psi
    ∃ z : spinGroup Q, Odd (orderOf z) ∧
      ((X = L ∧ psiS z = x) ∨ GGNbr p B x D J (psiS z) X) ∧
      ∃ ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F,
        IsPrimAdjIdemIn (RingHom.id F)
          (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q))
          (Algebra.adjoin F (Units.val '' ({Spin.spinMatrix Q z} :
            Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)))) ε ∧
        IsPrimIdemIn (Algebra.adjoin F (Units.val '' ({Spin.spinMatrix Q z} :
          Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)))) ε ∧
        (Spin.spinMatrix Q z : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) * ε = ε ∧
        blockDegree (Algebra.adjoin F (Units.val '' ({Spin.spinMatrix Q z} :
          Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)))) ε = 1 ∧
        8 ≤ Module.finrank F (LinearMap.range (Matrix.toLin' ε)) ∧
        CFSG.Assembly.IsComponentOf (X.comap psiS)
          ⁅glBlockCentralizer (Spin.spinMatrix Q) {Spin.spinMatrix Q z} ε,
            glBlockCentralizer (Spin.spinMatrix Q) {Spin.spinMatrix Q z} ε⁆ ∧
        (X.comap psiS).map psiS = X ∧
        LargeEvenMarking (X.comap psiS) (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hpres.1.1.2.1
  have hn : 4 ≤ n := hpres.1.1.2.2
  let : NeZero f := ⟨by omega⟩
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  let F := GaloisField 2 f
  let Q := Spin.quadMinus n F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
  let psiS : spinGroup Q →* G := psi
  let j := Spin.spinMatrix Q
  have hirr := minusCoeffs_irr 2 f
  have hj : Function.Injective j := (MonoidHom.ker_eq_bot_iff j).1
    (Spin.ker_spinMatrix_quadMinus_eq_bot hirr (CharP.cast_eq_zero F 2))
  have hr : j.range = StatedOmega ⇑Q := by
    simpa only [j, Q, Spin.coe_quadMinus] using (Spin.range_spinMatrix_quadMinus hn hirr)
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadMinus_of_finite n F hirr
  have h8 : 8 ≤ Fintype.card (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨z, hodd, hz, ε, hε, hC, hmap, hmarkC⟩ :=
    ggActualMember_POmegaMinus_block hcfg psi hpres horigin hmark
  obtain ⟨hprim, hfix, hdegree, hdim⟩ := ClassicalBlocks.omega_block_facts_of_guarded_component
    Q hQ h8 j hj hr z hodd hε hC hmarkC
  exact ⟨z, hodd, hz, ε, hε, hprim, hfix, hdegree, hdim, hC, hmap, hmarkC⟩

end GuardedFixed

section OriginalMember

theorem ggActualMember_POmegaMinus_selected
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ}
    (psi : (ggU .POmegaMinus n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .POmegaMinus n f).D .POmegaMinus n f psi)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At psi S := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hpres.1.1.2.1
  have hn : 4 ≤ n := hpres.1.1.2.2
  let : NeZero f := ⟨by omega⟩
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  let F := GaloisField 2 f
  let Q := Spin.quadMinus n F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
  let psiS : spinGroup Q →* G := psi
  let j := Spin.spinMatrix Q
  have hj : Function.Injective j := (MonoidHom.ker_eq_bot_iff j).1
    (Spin.ker_spinMatrix_quadMinus_eq_bot (minusCoeffs_irr 2 f) (CharP.cast_eq_zero F 2))
  obtain ⟨z, hodd, -, ε, hε, hprim, -, hdegree, hdim, hC, hmap, -⟩ :=
    ggActualMember_POmegaMinus_fixed_block hcfg psi hpres horigin hmark
  let S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) := {j z}
  change blockDegree (Algebra.adjoin F (Units.val '' S)) ε = 1 at hdegree
  change 8 ≤ Module.finrank F (LinearMap.range (Matrix.toLin' ε)) at hdim
  have hSU : ∀ a ∈ S, a ∈ j.range := by
    intro a ha
    have ha0 := Set.mem_singleton_iff.mp ha
    subst a
    exact ⟨z, rfl⟩
  have hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b := by
    intro a ha b hb
    have ha0 := Set.mem_singleton_iff.mp ha
    have hb0 := Set.mem_singleton_iff.mp hb
    subst a
    subst b
    exact Commute.refl (j z)
  have hoddS : ∀ a ∈ S, Odd (orderOf a) := by
    intro a ha
    have ha0 := Set.mem_singleton_iff.mp ha
    subst a
    simpa only [orderOf_injective j hj z] using hodd
  have hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) ε < 2 := by
    omega
  have hrank : ε.rank = Module.finrank F (LinearMap.range (Matrix.toLin' ε)) := by
    rw [Matrix.rank_eq_finrank_range_toLin ε (Pi.basisFun F _) (Pi.basisFun F _),
      Matrix.toLin_eq_toLin']
  have hnotFour : ε.rank ≠ 4 := by
    intro h4
    rw [hrank] at h4
    omega
  obtain ⟨t', m, iota, beta0, hshape, hlong, hpre, hirange,
      a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, hX, hX'⟩ :=
    exists_blockModel_selfDual_POmegaMinus_explicit n f hf S hSU hS hoddS hprim hn
      hε.2.2.2.1 hdeg (by rintro ⟨h4, -⟩; exact hnotFour h4) hC
  have hgood : (t' = .POmegaPlus ∨ t' = .POmegaMinus) ∧ 4 ≤ m := by
    rcases hshape with ⟨ht, hm, hdm⟩ | ⟨-, -, h4⟩
    · change 2 * m = Module.finrank F (LinearMap.range (Matrix.toLin' ε)) at hdm
      exact ⟨ht, by omega⟩
    · change Module.finrank F (LinearMap.range (Matrix.toLin' ε)) = 4 at h4
      omega
  have hadm : StatedLieAdmissible t' m 2 f := by
    rcases hgood.1 with rfl | rfl <;> exact ⟨Nat.prime_two, hf, hgood.2⟩
  have hrk : 2 ≤ (ggU t' m f).D.rank := by
    rcases hgood.1 with rfl | rfl
    · exact (ggTagFacts_POmegaPlus hadm (by simp only [bnRank]; omega)).1
    · exact (ggTagFacts_POmegaMinus hadm (by simp only [bnRank]; omega)).1
  let iotaU : (ggU t' m f).K →* (ggU .POmegaMinus n f).K := iota
  let lam : (ggU t' m f).K →* G := psi.comp iotaU
  have hker : lam.ker ≤ Subgroup.center (ggU t' m f).K := by
    intro u hu
    exact hpre u (hpres.2.1.2 hu)
  have hrange : lam.range = X := by
    change (psiS.comp iota).range = X
    rw [MonoidHom.range_comp, hirange, hmap]
  obtain ⟨δ, model, hmodel, hPresented⟩ := SiegelPair.exists_presented_of_siegelBlock_POmegaMinus
    hn hf hgood.1 hgood.2 psi iotaU hlong a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀ hX hX'
  let T := (lam.comp model.phi).range
  have hT : (ggRootLevi (ggU t' m f).D δ).map lam = T := by
    dsimp [T]
    rw [MonoidHom.range_comp, hmodel]
  have hMember := memberSelectedSL2At_map_ggRootLevi lam hadm hrk hker hrange model hmodel
  exact ⟨T, hT ▸ hMember, hPresented⟩

end OriginalMember

end CFSG.StandardType
