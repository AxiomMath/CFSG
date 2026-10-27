module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagSetting
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCover
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

open scoped commutatorElement

theorem ys03_inv_mul_mem_center {X : Type} [Group X] (K : Subgroup X) (c c' : K)
    (h : ∀ z : K, (c : X) * (z : X) * (c : X)⁻¹ = (c' : X) * (z : X) * (c' : X)⁻¹) :
    c⁻¹ * c' ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have hg := h g
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc _ = (c : X)⁻¹ * ((c : X) * (g : X) * (c : X)⁻¹) * (c' : X) := by group
    _ = (c : X)⁻¹ * ((c' : X) * (g : X) * (c' : X)⁻¹) * (c' : X) := by rw [hg]
    _ = (c : X)⁻¹ * (c' : X) * (g : X) := by group

theorem ys03_exists_innerHom {Γ X : Type} [Group Γ] [Group X] (f : Γ →* X) {K : Subgroup X}
    (hrep : ∀ g : Γ, ∃ c : K, ∀ z : K, f g * (z : X) * (f g)⁻¹ = (c : X) * (z : X) * (c : X)⁻¹) :
    ∃ Ψ : Γ →* K ⧸ Subgroup.center K, ∀ (g : Γ) (c : K),
      (∀ z : K, f g * (z : X) * (f g)⁻¹ = (c : X) * (z : X) * (c : X)⁻¹) →
        Ψ g = (QuotientGroup.mk c : K ⧸ Subgroup.center K) := by
  choose c hc using hrep
  refine ⟨MonoidHom.mk' (fun g => (QuotientGroup.mk (c g) : K ⧸ Subgroup.center K)) ?_, ?_⟩
  · intro g g'
    show (QuotientGroup.mk (c (g * g')) : K ⧸ Subgroup.center K) =
      QuotientGroup.mk (c g) * QuotientGroup.mk (c g')
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
    apply ys03_inv_mul_mem_center K
    intro z
    have h1 := hc (g * g') z
    have h2 := hc g (c g' * z * (c g')⁻¹)
    have h3 := hc g' z
    rw [map_mul] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2 ⊢
    rw [← h1]
    calc f g * f g' * (z : X) * (f g * f g')⁻¹
        = f g * (f g' * (z : X) * (f g')⁻¹) * (f g)⁻¹ := by group
      _ = f g * ((c g' : X) * (z : X) * (c g' : X)⁻¹) * (f g)⁻¹ := by rw [h3]
      _ = (c g : X) * ((c g' : X) * (z : X) * (c g' : X)⁻¹) * (c g : X)⁻¹ := h2
      _ = (c g : X) * (c g' : X) * (z : X) * ((c g : X) * (c g' : X))⁻¹ := by group
  · intro g c' hc'
    show (QuotientGroup.mk (c g) : K ⧸ Subgroup.center K) = QuotientGroup.mk c'
    rw [QuotientGroup.eq]
    apply ys03_inv_mul_mem_center K
    intro z
    exact (hc g z).symm.trans (hc' z)

theorem ys03_range_nontrivial {I X : Type} [Group I] [Group X] (Ψ : I →* X) (hΨ : Ψ.ker ≠ ⊤) :
    Nontrivial ↥Ψ.range := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ Ψ.ker := by
    by_contra hcon
    push Not at hcon
    exact hΨ (Subgroup.ext fun x => ⟨fun _ => Subgroup.mem_top x, fun _ => hcon x⟩)
  refine ⟨⟨1, Subgroup.one_mem _⟩, ⟨Ψ x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩, ?_⟩
  intro heq
  apply hx
  rw [MonoidHom.mem_ker]
  have h2 : (1 : X) = Ψ x := congrArg Subtype.val heq
  exact h2.symm

theorem ys03_range_solvable_of_decomp {I X : Type} [Group I] [Group X] (P : Subgroup I)
    [Group.IsSolvable P] (Ψ : I →* X)
    (hdec : ∀ x : I, ∃ n ∈ Ψ.ker, ∃ p ∈ P, x = n * p) :
    Group.IsSolvable ↥Ψ.range := by
  let f : P →* ↥Ψ.range :=
    { toFun := fun p => ⟨Ψ (p : I), MonoidHom.mem_range.mpr ⟨(p : I), rfl⟩⟩
      map_one' := Subtype.ext (map_one Ψ)
      map_mul' := fun a b => Subtype.ext (map_mul Ψ (a : I) (b : I)) }
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    obtain ⟨n, hn, p, hp, rfl⟩ := hdec x
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    show Ψ p = Ψ (n * p)
    rw [map_mul, MonoidHom.mem_ker.mp hn, one_mul]
  exact Group.isSolvable_of_surjective hfs

theorem ys03_decomp_of_top {I : Type} [Group I] (N P : Subgroup I) [N.Normal] [P.Normal]
    (htop : (N ⊔ P).map (QuotientGroup.mk' P) = ⊤) :
    ∀ x : I, ∃ n ∈ N, ∃ p ∈ P, x = n * p := by
  intro x
  have hx : (QuotientGroup.mk x : I ⧸ P) ∈ (N ⊔ P).map (QuotientGroup.mk' P) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨m, hmM, hm⟩ := Subgroup.mem_map.mp hx
  have hm' : (QuotientGroup.mk m : I ⧸ P) = QuotientGroup.mk x := hm
  have hpx : m⁻¹ * x ∈ P := QuotientGroup.eq.mp hm'
  obtain ⟨n, hn, q, hq, hnq⟩ := Subgroup.mem_sup_of_normal_left.mp hmM
  refine ⟨n, hn, q * (m⁻¹ * x), P.mul_mem hq hpx, ?_⟩
  rw [← mul_assoc, hnq, mul_inv_cancel_left]

theorem ys03_le_of_bot {I : Type} [Group I] (N P : Subgroup I) [P.Normal]
    (hbot : (N ⊔ P).map (QuotientGroup.mk' P) = ⊥) : N ≤ P := by
  intro x hx
  have hmem : (QuotientGroup.mk' P) x ∈ (N ⊔ P).map (QuotientGroup.mk' P) :=
    Subgroup.mem_map_of_mem _ ((le_sup_left : N ≤ N ⊔ P) hx)
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff x).mp hmem

theorem ys03_central_conj {X : Type} [Group X] (K : Subgroup X) (c : K)
    (hc : c ∈ Subgroup.center K) (t : X) (ht : t ∈ K) :
    (c : X) * t * (c : X)⁻¹ = t := by
  have h2 : t * (c : X) = (c : X) * t := by
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨t, ht⟩)
    simpa only [Subgroup.coe_mul] using h1
  rw [← h2, mul_inv_cancel_right]

theorem ys03_ker_ne_top {Γ X : Type} [Group Γ] [Group X] (f : Γ →* X) (K : Subgroup X)
    (Ψ : Γ →* K ⧸ Subgroup.center K)
    (hΨ : ∀ (g : Γ) (c : K), (∀ z : K, f g * (z : X) * (f g)⁻¹ = (c : X) * (z : X) * (c : X)⁻¹) →
      Ψ g = (QuotientGroup.mk c : K ⧸ Subgroup.center K))
    (hrep : ∀ g : Γ, ∃ c : K, ∀ z : K,
      f g * (z : X) * (f g)⁻¹ = (c : X) * (z : X) * (c : X)⁻¹)
    (hnc : ¬ ∀ g : Γ, f g ∈ Subgroup.centralizer (K : Set X)) :
    Ψ.ker ≠ ⊤ := by
  intro htop
  apply hnc
  intro g
  have hgker : Ψ g = 1 := by
    have hmem : g ∈ Ψ.ker := by
      rw [htop]
      exact Subgroup.mem_top g
    exact MonoidHom.mem_ker.mp hmem
  obtain ⟨c, hc⟩ := hrep g
  have h1 : (QuotientGroup.mk c : K ⧸ Subgroup.center K) = 1 :=
    (hΨ g c hc).symm.trans hgker
  have hcZ : c ∈ Subgroup.center K := (QuotientGroup.eq_one_iff c).mp h1
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have hz : f g * t * (f g)⁻¹ = t :=
    (hc ⟨t, ht⟩).trans (ys03_central_conj K c hcZ t ht)
  exact (mul_inv_eq_iff_eq_mul.mp hz).symm

theorem ys03_rangeRestrict_surjective {I X : Type} [Group I] [Group X] (Ψ : I →* X) :
    Function.Surjective Ψ.rangeRestrict := by
  intro y
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp y.2
  exact ⟨x, Subtype.ext hx⟩

theorem ys03_ker_le_of_max {I X : Type} [Group I] [Group X] [Group.IsPerfect I] (Q : Subgroup I)
    [Q.Normal] [Group.IsSolvable Q] (hQs : IsSimpleGroup (I ⧸ Q)) (Ψ : I →* X)
    (hΨ : Ψ.ker ≠ ⊤) : Ψ.ker ≤ Q := by
  haveI : ((Ψ.ker ⊔ Q).map (QuotientGroup.mk' Q)).Normal :=
    Subgroup.Normal.map (inferInstance : (Ψ.ker ⊔ Q).Normal) (QuotientGroup.mk' Q)
      (QuotientGroup.mk'_surjective Q)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Ψ.ker ⊔ Q).map (QuotientGroup.mk' Q))
    with hbot | htop
  · exact ys03_le_of_bot Ψ.ker Q hbot
  · exfalso
    have hdec := ys03_decomp_of_top Ψ.ker Q htop
    have hsolv := ys03_range_solvable_of_decomp Q Ψ hdec
    haveI : Group.IsPerfect ↥Ψ.range :=
      Group.IsPerfect.ofSurjective (ys03_rangeRestrict_surjective Ψ)
    haveI : Nontrivial ↥Ψ.range := ys03_range_nontrivial Ψ hΨ
    exact Group.IsPerfect.not_isSolvable _ hsolv

theorem ys03_hasSection_of_ker {I X T : Type} [Group I] [Group X] [Group T] (Q : Subgroup I)
    [Q.Normal] (e : I ⧸ Q ≃* T) (Ψ : I →* X) (hle : Ψ.ker ≤ Q) : HasSection X T := by
  have h' : Ψ.ker ≤ (QuotientGroup.mk' Q).ker := by
    rw [QuotientGroup.ker_mk']
    exact hle
  let π' : I ⧸ Ψ.ker →* I ⧸ Q := QuotientGroup.lift Ψ.ker (QuotientGroup.mk' Q) h'
  let φ : ↥Ψ.range →* I ⧸ Q :=
    π'.comp (QuotientGroup.quotientKerEquivRange Ψ).symm.toMonoidHom
  have hφ : Function.Surjective φ := by
    intro t
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q t
    refine ⟨(QuotientGroup.quotientKerEquivRange Ψ) (QuotientGroup.mk x : I ⧸ Ψ.ker), ?_⟩
    have hsymm := MulEquiv.symm_apply_apply (QuotientGroup.quotientKerEquivRange Ψ)
      (QuotientGroup.mk x : I ⧸ Ψ.ker)
    show π' ((QuotientGroup.quotientKerEquivRange Ψ).symm
      ((QuotientGroup.quotientKerEquivRange Ψ) (QuotientGroup.mk x : I ⧸ Ψ.ker))) = _
    exact (congrArg π' hsymm).trans rfl
  unfold HasSection
  exact ⟨Ψ.range, φ.ker, inferInstance,
    ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).trans e⟩⟩

section Certs


theorem ys03_section_of_item45 {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G}
    {L : Subgroup G}
    (hS : SchreierFor CFSG.Assembly.InCatalog) (h45 : Item4_5)
    (h : DiagSetting G A M H s L) (K : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) (hK : CFSG.IsComponent K)
    (hmoved : ¬ (inSubgroup perfectResidual H).map (starQuot G) ≤
      Subgroup.centralizer (K : Set (G ⧸ CFSG.pPrimeCore 3 G))) :
    HasSection (K ⧸ Subgroup.center K) (projSL 3 (GaloisField 2 2)) := by
  have hKX : CFSG.IsKGroup (G ⧸ CFSG.pPrimeCore 3 G) :=
    CFSG.SectionRank.K_group_section_closure_inCatalog h.ctx.ctx444.sectionFourHyp.kGroup ⊤ _
      (Census.quotientTopEquiv (CFSG.pPrimeCore 3 G))
  have hYK : (inSubgroup perfectResidual H).map (starQuot G) ≤
      Subgroup.normalizer (K : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
    (DiagSetting.I_le_layer KFacts.kpSz hS h45 h).trans
      (CFSG.LocalCores.layer_le_normalizer hK)
  have hYp : ⁅(inSubgroup perfectResidual H).map (starQuot G),
      (inSubgroup perfectResidual H).map (starQuot G)⁆ =
      (inSubgroup perfectResidual H).map (starQuot G) := by
    rw [← Subgroup.map_commutator, DiagSetting.commutator_I_eq H]
  let f : ↥(inSubgroup perfectResidual H) →* (G ⧸ CFSG.pPrimeCore 3 G) :=
    (starQuot G).comp (inSubgroup perfectResidual H).subtype
  have hrep : ∀ g : ↥(inSubgroup perfectResidual H), ∃ c : K, ∀ z : K,
      f g * (z : G ⧸ CFSG.pPrimeCore 3 G) * (f g)⁻¹ =
        (c : G ⧸ CFSG.pPrimeCore 3 G) * (z : G ⧸ CFSG.pPrimeCore 3 G) *
          (c : G ⧸ CFSG.pPrimeCore 3 G)⁻¹ := by
    intro g
    have hmem : f g ∈ (inSubgroup perfectResidual H).map (starQuot G) :=
      Subgroup.mem_map_of_mem (starQuot G) g.2
    obtain ⟨c, hcK, hc⟩ := Item4443SL.inner_of_isComponent hS hKX hK hYK hYp (f g) hmem
    exact ⟨⟨c, hcK⟩, fun z => hc z z.2⟩
  obtain ⟨Ψ, hΨ⟩ := ys03_exists_innerHom f hrep
  have hnc : ¬ ∀ g : ↥(inSubgroup perfectResidual H),
      f g ∈ Subgroup.centralizer (K : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
    intro hall
    apply hmoved
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact hall ⟨x, hx⟩
  have hker : Ψ.ker ≠ ⊤ := ys03_ker_ne_top f K Ψ hΨ hrep hnc
  haveI : Group.IsPerfect ↥(inSubgroup perfectResidual H) :=
    Subgroup.isPerfect_iff.mpr (DiagSetting.commutator_I_eq H)
  obtain ⟨e⟩ := h.I_iso
  have hQsimple : IsSimpleGroup (↥(inSubgroup perfectResidual H) ⧸
      CFSG.pCore 2 (inSubgroup perfectResidual H)) :=
    (MulEquiv.isSimpleGroup_congr e).mpr isSimpleGroup_projSL
  haveI : Group.IsNilpotent ↥(CFSG.pCore 2 (inSubgroup perfectResidual H)) :=
    IsPGroup.isNilpotent (CFSG.pCore_isPGroup (p := 2) (G := ↥(inSubgroup perfectResidual H)))
  have hle : Ψ.ker ≤ CFSG.pCore 2 (inSubgroup perfectResidual H) :=
    ys03_ker_le_of_max (CFSG.pCore 2 (inSubgroup perfectResidual H)) hQsimple Ψ hker
  exact ys03_hasSection_of_ker (CFSG.pCore 2 (inSubgroup perfectResidual H)) e Ψ hle

end Certs

end CFSG.RankThree.PartTwo.Sec4

end
