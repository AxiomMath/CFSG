module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.Geometry.GeneralizedPolygons

universe u

private theorem xv_mem_inner {X : Type} [Group X] {P1 P2 : Subgroup X}
    {Y : Type} [Group Y] {c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y}
    {n : ℕ} (hn : 3 ≤ n) : c.xv ∈ edgeBall (n - 2) c := by
  left
  rw [SimpleGraph.dist_self]
  omega

private theorem lv_mem_ball {X : Type} [Group X] {P1 P2 : Subgroup X}
    {Y : Type} [Group Y] {c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y}
    {n : ℕ} (hn : 3 ≤ n) : c.lv ∈ edgeBall (n - 1) c := by
  right
  rw [SimpleGraph.dist_self]
  omega

@[expose] def RootGroupLift (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (P1 P2 : Subgroup X) (Y : Type) [Group Y]
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y),
    3 ≤ n → c.IsFaithful → MoufangCondition ↥(c.φ1.range ⊔ c.φ2.range) c.graph n →
    ∀ (V : Type) [Fintype V] (Δ : SimpleGraph V) [DecidableRel Δ.Adj]
      (D : Type) [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Δ]
      (u v : V) (ψ₁ : ↥P1 →* D) (ψ₂ : ↥P2 →* D) (ι : c.Γ → V),
      IsGeneralizedPolygon Δ n → IsThick Δ → MoufangCondition D Δ n →
      IsWeissEmbedding n c Δ u v ψ₁ ψ₂ ι →
        ∀ p : GPath Δ n, p.NoBack → ∀ j : ℕ, j + 1 ≤ n →
          ((p j = u ∧ p (j + 1) = v) ∨ (p j = v ∧ p (j + 1) = u)) →
          pathRootGroup D Δ p ≤ (psiB P2 ψ₁).range

theorem weissEmbeddingFacts_of_rootGroupLift (n : ℕ) (hroot : RootGroupLift n) :
    WeissEmbeddingFacts n := by
  intro X _ P1 P2 Y _ c hn hc hM V _ Δ _ D _ _ _ _ u v ψ₁ ψ₂ ι hP hT hMΔ hW
  classical
  have hW' : IsWeissEmbedding n c Δ u v ψ₁ ψ₂ ι := hW
  rcases hW with ⟨hInj1, hInj2, hAgree, hGen, hιx, hιl, hBij, hE2, hE3₁, hE3₂⟩
  have hInjOn : Set.InjOn ι (edgeBall (n - 1) c) := hBij.2.1
  have hSurj : ∀ y : V, ∃ w ∈ edgeBall (n - 1) c, ι w = y := by
    intro y
    obtain ⟨w, hw, hwy⟩ := hBij.2.2 (Set.mem_univ y)
    exact ⟨w, hw, hwy⟩
  have hbase : c.graph.Adj c.xv c.lv := CosetGeom.adj_γ₀_γ₁
  have hbaseInner : c.xv ∈ edgeBall (n - 2) c := xv_mem_inner hn
  have hlBall : c.lv ∈ edgeBall (n - 1) c := lv_mem_ball hn
  have hfix_xv : ∀ h : ↥(c.φ1.range ⊔ c.φ2.range), (h : Y) ∈ c.φ1.range →
      h • c.xv = c.xv := by
    intro h hh
    exact CosetGeom.smul_eq_of_mem_stab (by
      rw [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) (G₁ := c.φ1.range)
        (G₂ := c.φ2.range) le_sup_left]
      exact hh)
  have hfix_lv : ∀ h : ↥(c.φ1.range ⊔ c.φ2.range), (h : Y) ∈ c.φ2.range →
      h • c.lv = c.lv := by
    intro h hh
    exact CosetGeom.smul_eq_of_mem_stab (by
      rw [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) (G₁ := c.φ1.range)
        (G₂ := c.φ2.range) le_sup_right]
      exact hh)
  have hm1 : ∀ g : ↥P1, c.φ1 g ∈ c.φ1.range := fun g => ⟨g, rfl⟩
  have hm2 : ∀ g : ↥P2, c.φ2 g ∈ c.φ2.range := fun g => ⟨g, rfl⟩
  have hdist_xv : c.graph.dist c.xv c.xv ≤ n - 1 := by
    rw [SimpleGraph.dist_self]; omega
  have hdist_lv : c.graph.dist c.xv c.lv ≤ n - 1 := by
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hbase]; omega
  have hdist_lvxv : c.graph.dist c.lv c.xv ≤ n - 1 := by
    rw [SimpleGraph.dist_comm, SimpleGraph.dist_eq_one_iff_adj.mpr hbase]; omega
  have hdist_lvlv : c.graph.dist c.lv c.lv ≤ n - 1 := by
    rw [SimpleGraph.dist_self]; omega
  have hAdjUV : Δ.Adj u v := by
    have h := (hE2 c.xv c.lv hbaseInner hlBall).mpr hbase
    rwa [hιx, hιl] at h
  have hψ1_le : ψ₁.range ≤ MulAction.stabilizer D u := by
    rintro _ ⟨g, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    have h := hE3₁ g ⟨c.φ1 g, Subgroup.mem_sup_left (hm1 g)⟩ rfl c.xv hdist_xv
    rw [hfix_xv ⟨c.φ1 g, Subgroup.mem_sup_left (hm1 g)⟩ (hm1 g)] at h
    simpa [hιx] using h
  have hψ2_le : ψ₂.range ≤ MulAction.stabilizer D v := by
    rintro _ ⟨g, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    have h := hE3₂ g ⟨c.φ2 g, Subgroup.mem_sup_right (hm2 g)⟩ rfl c.lv hdist_lvlv
    rw [hfix_lv ⟨c.φ2 g, Subgroup.mem_sup_right (hm2 g)⟩ (hm2 g)] at h
    simpa [hιl] using h
  have hInter1 : ψ₁.range ⊓ MulAction.stabilizer D v = (psiB P2 ψ₁).range := by
    apply le_antisymm
    · rintro _ ⟨hx, hv⟩
      obtain ⟨g, rfl⟩ := hx
      have hv' : ψ₁ g • ι c.lv = ι c.lv := by
        rw [hιl]
        exact MulAction.mem_stabilizer_iff.mp hv
      have hE := hE3₁ g ⟨c.φ1 g, Subgroup.mem_sup_left (hm1 g)⟩ rfl c.lv hdist_lv
      have himg : ι ((⟨c.φ1 g, Subgroup.mem_sup_left (hm1 g)⟩ :
          ↥(c.φ1.range ⊔ c.φ2.range)) • c.lv) = ι c.lv := by
        rw [← hE]; exact hv'
      have hmem : (⟨c.φ1 g, Subgroup.mem_sup_left (hm1 g)⟩ :
          ↥(c.φ1.range ⊔ c.φ2.range)) • c.lv ∈ edgeBall (n - 1) c := by
        left
        have hadj := (CosetGeom.smul_adj (G₀ := c.φ1.range ⊔ c.φ2.range)
          (G₁ := c.φ1.range) (G₂ := c.φ2.range)
          ⟨c.φ1 g, Subgroup.mem_sup_left (hm1 g)⟩).mpr hbase
        rw [hfix_xv ⟨c.φ1 g, Subgroup.mem_sup_left (hm1 g)⟩ (hm1 g)] at hadj
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj]
        omega
      have heq : (⟨c.φ1 g, Subgroup.mem_sup_left (hm1 g)⟩ :
          ↥(c.φ1.range ⊔ c.φ2.range)) • c.lv = c.lv :=
        hInjOn hmem hlBall himg
      have hφ2 : ((⟨c.φ1 g, Subgroup.mem_sup_left (hm1 g)⟩ :
          ↥(c.φ1.range ⊔ c.φ2.range)) : Y) ∈ c.φ2.range := by
        have := CosetGeom.mem_stab_of_smul_eq heq
        rwa [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) (G₁ := c.φ1.range)
          (G₂ := c.φ2.range) le_sup_right] at this
      have hmem12 : ((⟨c.φ1 g, Subgroup.mem_sup_left (hm1 g)⟩ :
          ↥(c.φ1.range ⊔ c.φ2.range)) : Y) ∈ c.φ12.range := by
        rw [← c.inter]
        exact ⟨hm1 g, hφ2⟩
      obtain ⟨b, hb⟩ := hmem12
      let b' : ↥(P1 ⊓ P2) := b
      have hb' : c.φ12 b' = ((⟨c.φ1 g, Subgroup.mem_sup_left (hm1 g)⟩ :
          ↥(c.φ1.range ⊔ c.φ2.range)) : Y) := hb
      refine ⟨b', ?_⟩
      have hg : g = Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) b' := by
        apply hc.1
        have hcomm : c.φ1 (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) b') =
            c.φ12 b' := c.comm1 b'
        calc c.φ1 g = ((⟨c.φ1 g, Subgroup.mem_sup_left (hm1 g)⟩ :
              ↥(c.φ1.range ⊔ c.φ2.range)) : Y) := rfl
          _ = c.φ12 b' := hb'.symm
          _ = c.φ1 (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) b') := hcomm.symm
      show (psiB P2 ψ₁) b' = ψ₁ g
      rw [hg]
      rfl
    · rintro _ ⟨b, rfl⟩
      constructor
      · exact ⟨Subgroup.inclusion inf_le_left b, rfl⟩
      · refine MulAction.mem_stabilizer_iff.mpr ?_
        show ψ₁ (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) b) • v = v
        have h := hE3₂ (Subgroup.inclusion (inf_le_right : P1 ⊓ P2 ≤ P2) b)
          ⟨c.φ2 (Subgroup.inclusion inf_le_right b), Subgroup.mem_sup_right
            (hm2 (Subgroup.inclusion inf_le_right b))⟩ rfl c.lv hdist_lvlv
        rw [hfix_lv ⟨c.φ2 (Subgroup.inclusion inf_le_right b),
          Subgroup.mem_sup_right (hm2 (Subgroup.inclusion inf_le_right b))⟩
          (hm2 (Subgroup.inclusion inf_le_right b))] at h
        rw [hAgree b]
        simpa [hιl] using h
  have hInter2 : ψ₂.range ⊓ MulAction.stabilizer D u = (psiB P2 ψ₁).range := by
    apply le_antisymm
    · rintro _ ⟨hx, hu⟩
      obtain ⟨g, rfl⟩ := hx
      have hu' : ψ₂ g • ι c.xv = ι c.xv := by
        rw [hιx]
        exact MulAction.mem_stabilizer_iff.mp hu
      have hE := hE3₂ g ⟨c.φ2 g, Subgroup.mem_sup_right (hm2 g)⟩ rfl c.xv hdist_lvxv
      have himg : ι ((⟨c.φ2 g, Subgroup.mem_sup_right (hm2 g)⟩ :
          ↥(c.φ1.range ⊔ c.φ2.range)) • c.xv) = ι c.xv := by
        rw [← hE]; exact hu'
      have hmem : (⟨c.φ2 g, Subgroup.mem_sup_right (hm2 g)⟩ :
          ↥(c.φ1.range ⊔ c.φ2.range)) • c.xv ∈ edgeBall (n - 1) c := by
        right
        have hadj := (CosetGeom.smul_adj (G₀ := c.φ1.range ⊔ c.φ2.range)
          (G₁ := c.φ1.range) (G₂ := c.φ2.range)
          ⟨c.φ2 g, Subgroup.mem_sup_right (hm2 g)⟩).mpr hbase.symm
        rw [hfix_lv ⟨c.φ2 g, Subgroup.mem_sup_right (hm2 g)⟩ (hm2 g)] at hadj
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj]
        omega
      have heq : (⟨c.φ2 g, Subgroup.mem_sup_right (hm2 g)⟩ :
          ↥(c.φ1.range ⊔ c.φ2.range)) • c.xv = c.xv :=
        hInjOn hmem (by left; rw [SimpleGraph.dist_self]; omega) himg
      have hφ1 : ((⟨c.φ2 g, Subgroup.mem_sup_right (hm2 g)⟩ :
          ↥(c.φ1.range ⊔ c.φ2.range)) : Y) ∈ c.φ1.range := by
        have := CosetGeom.mem_stab_of_smul_eq heq
        rwa [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) (G₁ := c.φ1.range)
          (G₂ := c.φ2.range) le_sup_left] at this
      have hmem12 : ((⟨c.φ2 g, Subgroup.mem_sup_right (hm2 g)⟩ :
          ↥(c.φ1.range ⊔ c.φ2.range)) : Y) ∈ c.φ12.range := by
        rw [← c.inter]
        exact ⟨hφ1, hm2 g⟩
      obtain ⟨b, hb⟩ := hmem12
      let b' : ↥(P1 ⊓ P2) := b
      have hb' : c.φ12 b' = ((⟨c.φ2 g, Subgroup.mem_sup_right (hm2 g)⟩ :
          ↥(c.φ1.range ⊔ c.φ2.range)) : Y) := hb
      refine ⟨b', ?_⟩
      have hg : g = Subgroup.inclusion (inf_le_right : P1 ⊓ P2 ≤ P2) b' := by
        apply hc.2.2
        have hcomm : c.φ2 (Subgroup.inclusion (inf_le_right : P1 ⊓ P2 ≤ P2) b') =
            c.φ12 b' := c.comm2 b'
        calc c.φ2 g = ((⟨c.φ2 g, Subgroup.mem_sup_right (hm2 g)⟩ :
              ↥(c.φ1.range ⊔ c.φ2.range)) : Y) := rfl
          _ = c.φ12 b' := hb'.symm
          _ = c.φ2 (Subgroup.inclusion (inf_le_right : P1 ⊓ P2 ≤ P2) b') := hcomm.symm
      have hpsi : (psiB P2 ψ₁) b' = ψ₂ (Subgroup.inclusion inf_le_right b') := by
        change ψ₁ (Subgroup.inclusion inf_le_left b') =
          ψ₂ (Subgroup.inclusion inf_le_right b')
        exact hAgree b'
      simpa [hpsi, hg]
    · rintro _ ⟨b, rfl⟩
      constructor
      · have hb : (psiB P2 ψ₁) b = ψ₂ (Subgroup.inclusion inf_le_right b) := by
          change ψ₁ (Subgroup.inclusion inf_le_left b) =
            ψ₂ (Subgroup.inclusion inf_le_right b)
          exact hAgree b
        rw [hb]
        exact ⟨Subgroup.inclusion inf_le_right b, rfl⟩
      · refine MulAction.mem_stabilizer_iff.mpr ?_
        show ψ₁ (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) b) • u = u
        have h := hE3₁ (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) b)
          ⟨c.φ1 (Subgroup.inclusion inf_le_left b), Subgroup.mem_sup_left
            (hm1 (Subgroup.inclusion inf_le_left b))⟩ rfl c.xv hdist_xv
        rw [hfix_xv ⟨c.φ1 (Subgroup.inclusion inf_le_left b),
          Subgroup.mem_sup_left (hm1 (Subgroup.inclusion inf_le_left b))⟩
          (hm1 (Subgroup.inclusion inf_le_left b))] at h
        simpa [hιx] using h
  have hTrans1 : ∀ w : V, Δ.Adj u w → ∃ g : ↥P1, ψ₁ g • v = w := by
    intro w huw
    obtain ⟨w', hw'ball, hw'w⟩ := hSurj w
    have hAdj : c.graph.Adj c.xv w' := by
      apply (hE2 c.xv w' hbaseInner hw'ball).mp
      rwa [hιx, hw'w]
    obtain ⟨h, hhx, hhl⟩ := CosetGeom.exists_stab_smul_eq hbase hAdj
    have hφ1 : (h : Y) ∈ c.φ1.range := by
      have := CosetGeom.mem_stab_of_smul_eq hhx
      rwa [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) (G₁ := c.φ1.range)
        (G₂ := c.φ2.range) le_sup_left] at this
    obtain ⟨g, hg⟩ := hφ1
    let g' : ↥P1 := g
    have hg' : c.φ1 g' = (h : Y) := hg
    refine ⟨g', ?_⟩
    have hE := hE3₁ g' h hg'.symm c.lv hdist_lv
    have hE' : ψ₁ g' • v = ι (h • c.lv) := by simpa [hιl] using hE
    rw [hE', hhl, hw'w]
  have hTrans2 : ∀ w : V, Δ.Adj v w → ∃ g : ↥P2, ψ₂ g • u = w := by
    intro w hvw
    obtain ⟨w', hw'ball, hw'w⟩ := hSurj w
    have hAdj : c.graph.Adj c.lv w' := by
      apply (hE2 c.lv w' (by
        right; rw [SimpleGraph.dist_self]; omega) hw'ball).mp
      rwa [hιl, hw'w]
    obtain ⟨h, hhl, hhx⟩ := CosetGeom.exists_stab_smul_eq (γ := c.lv) (δ := c.xv)
      (δ' := w') hbase.symm hAdj
    have hφ2 : (h : Y) ∈ c.φ2.range := by
      have := CosetGeom.mem_stab_of_smul_eq hhl
      rwa [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) (G₁ := c.φ1.range)
        (G₂ := c.φ2.range) le_sup_right] at this
    obtain ⟨g, hg⟩ := hφ2
    let g' : ↥P2 := g
    have hg' : c.φ2 g' = (h : Y) := hg
    refine ⟨g', ?_⟩
    have hE := hE3₂ g' h hg'.symm c.xv hdist_lvxv
    have hE' : ψ₂ g' • u = ι (h • c.xv) := by simpa [hιx] using hE
    rw [hE', hhx, hw'w]
  have hdeg1 : Δ.degree u = (P1 ⊓ P2).relIndex P1 := by
    classical
    let H1 : Subgroup ↥P1 := (P1 ⊓ P2).subgroupOf P1
    let f : ↥P1 ⧸ H1 → Δ.neighborSet u :=
      Quotient.lift
        (fun g => ⟨ψ₁ g • v, by
          rw [SimpleGraph.mem_neighborSet]
          have hu : ψ₁ g • u = u := hψ1_le (Set.mem_range_self g)
          rw [← hu]
          exact (GraphAction.adj_smul (ψ₁ g) u v).mpr hAdjUV⟩)
        (by
          intro a b hab
          apply Subtype.ext
          have hab' : a⁻¹ * b ∈ H1 := QuotientGroup.leftRel_apply.mp hab
          have hb0 : ((a⁻¹ * b : ↥P1) : X) ∈ P1 ⊓ P2 := hab'
          have hmem : ψ₁ (a⁻¹ * b) ∈ (psiB P2 ψ₁).range := by
            refine ⟨⟨a⁻¹ * b, hb0⟩, ?_⟩
            rfl
          have hfix : ψ₁ (a⁻¹ * b) • v = v := by
            have hmem' : ψ₁ (a⁻¹ * b) ∈ ψ₁.range ⊓
                MulAction.stabilizer D v := by
              rw [hInter1]
              exact hmem
            exact MulAction.mem_stabilizer_iff.mp hmem'.2
          calc ψ₁ a • v = ψ₁ a • (ψ₁ (a⁻¹ * b) • v) := by rw [hfix]
            _ = ψ₁ b • v := by
              rw [← mul_smul, ← map_mul, show a * (a⁻¹ * b) = b by group])
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨g, hg⟩ := hTrans1 y.1 y.2
      exact ⟨QuotientGroup.mk g, Subtype.ext hg⟩
    have hinj : Function.Injective f := by
      intro q1 q2 hq
      induction q1 using QuotientGroup.induction_on with
      | H a =>
        induction q2 using QuotientGroup.induction_on with
        | H b =>
          have hq' : ψ₁ a • v = ψ₁ b • v := congrArg Subtype.val hq
          have hfix : ψ₁ (a⁻¹ * b) • v = v := by
            rw [map_mul, map_inv, mul_smul, ← hq', inv_smul_smul]
          have hmem : ψ₁ (a⁻¹ * b) ∈ (psiB P2 ψ₁).range := by
            rw [← hInter1]
            exact ⟨⟨a⁻¹ * b, rfl⟩, hfix⟩
          obtain ⟨b0, hb0⟩ := hmem
          have hEq : a⁻¹ * b = Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) b0 :=
            (hInj1 hb0).symm
          exact QuotientGroup.eq.mpr (by
            rw [hEq]
            exact b0.2)
    have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
    have hcard : Nat.card (↥P1 ⧸ H1) = Nat.card (Δ.neighborSet u) :=
      Nat.card_eq_of_bijective f hbij
    rw [Subgroup.relIndex, Subgroup.index, hcard, Nat.card_eq_fintype_card,
      SimpleGraph.card_neighborSet_eq_degree]
  have hdeg2 : Δ.degree v = (P1 ⊓ P2).relIndex P2 := by
    classical
    let H2 : Subgroup ↥P2 := (P1 ⊓ P2).subgroupOf P2
    let f : ↥P2 ⧸ H2 → Δ.neighborSet v :=
      Quotient.lift
        (fun g => ⟨ψ₂ g • u, by
          rw [SimpleGraph.mem_neighborSet]
          have hv : ψ₂ g • v = v := hψ2_le (Set.mem_range_self g)
          rw [← hv]
          exact (GraphAction.adj_smul (ψ₂ g) v u).mpr hAdjUV.symm⟩)
        (by
          intro a b hab
          apply Subtype.ext
          have hab' : a⁻¹ * b ∈ H2 := QuotientGroup.leftRel_apply.mp hab
          have hb0 : ((a⁻¹ * b : ↥P2) : X) ∈ P1 ⊓ P2 := hab'
          have hmem : ψ₂ (a⁻¹ * b) ∈ (psiB P2 ψ₁).range := by
            refine ⟨⟨a⁻¹ * b, hb0⟩, ?_⟩
            rw [show psiB P2 ψ₁ ⟨a⁻¹ * b, hb0⟩ =
              ψ₁ (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1)
                ⟨a⁻¹ * b, hb0⟩) from rfl, hAgree]
            congr 1
          have hfix : ψ₂ (a⁻¹ * b) • u = u := by
            have hmem' : ψ₂ (a⁻¹ * b) ∈ ψ₂.range ⊓
                MulAction.stabilizer D u := by
              rw [hInter2]
              exact hmem
            exact MulAction.mem_stabilizer_iff.mp hmem'.2
          calc ψ₂ a • u = ψ₂ a • (ψ₂ (a⁻¹ * b) • u) := by rw [hfix]
            _ = ψ₂ b • u := by
              rw [← mul_smul, ← map_mul, show a * (a⁻¹ * b) = b by group])
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨g, hg⟩ := hTrans2 y.1 y.2
      exact ⟨QuotientGroup.mk g, Subtype.ext hg⟩
    have hinj : Function.Injective f := by
      intro q1 q2 hq
      induction q1 using QuotientGroup.induction_on with
      | H a =>
        induction q2 using QuotientGroup.induction_on with
        | H b =>
          have hq' : ψ₂ a • u = ψ₂ b • u := congrArg Subtype.val hq
          have hfix : ψ₂ (a⁻¹ * b) • u = u := by
            rw [map_mul, map_inv, mul_smul, ← hq', inv_smul_smul]
          have hmem : ψ₂ (a⁻¹ * b) ∈ (psiB P2 ψ₁).range := by
            rw [← hInter2]
            exact ⟨⟨a⁻¹ * b, rfl⟩, hfix⟩
          obtain ⟨b0, hb0⟩ := hmem
          have hpsi : ψ₁ (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) b0) =
              ψ₂ (Subgroup.inclusion (inf_le_right : P1 ⊓ P2 ≤ P2) b0) := hAgree b0
          have hEq : a⁻¹ * b = Subgroup.inclusion (inf_le_right : P1 ⊓ P2 ≤ P2) b0 := by
            symm
            apply hInj2
            exact hpsi.symm.trans hb0
          exact QuotientGroup.eq.mpr (by
            rw [hEq]
            exact b0.2)
    have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
    have hcard : Nat.card (↥P2 ⧸ H2) = Nat.card (Δ.neighborSet v) :=
      Nat.card_eq_of_bijective f hbij
    rw [Subgroup.relIndex, Subgroup.index, hcard, Nat.card_eq_fintype_card,
      SimpleGraph.card_neighborSet_eq_degree]
  exact ⟨hAdjUV, hψ1_le, hψ2_le, hInter1, hInter2, hTrans1, hTrans2, hdeg1,
    hdeg2, hroot X P1 P2 Y c hn hc hM V Δ D u v ψ₁ ψ₂ ι hP hT hMΔ hW'⟩
