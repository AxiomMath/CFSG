module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameA5
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2Levi
public import CFSG.RankThree.GF2n.Smith81.S81QGraphRoot
public import CFSG.GroupTheory.ConjTransport

public section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.WeakCT
open CFSG.Timmesfeld CFSG.SeitzReduction.E7Pilot CFSG.SeitzReduction.EPilot
open CFSG.RankThree.PartOne.KA5L CFSG.RankThree.PartOne.KE CFSG.ClassicalInvolution.ModelFacts
open CFSG.LieType.Steinberg (SpinPlus.x)

open CFSG.RankThree.GF2n.Smith81.D6Spin (graphSpin graphSpin_x swap45 swap45_mem_roots)

open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus)

open CFSG.LieType.RootSystem (roots)

open scoped MatrixGroups

attribute [-instance] CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

theorem map_subgroupOf_of_coe {G : Type*} [Group G] {A B X : Subgroup G} (e : A ≃* B) (n : G)
    (he : ∀ a : A, (e a : G) = n * a * n⁻¹) (hX : X ≤ A) :
    (X.subgroupOf A).map e.toMonoidHom = (X.map (MulAut.conj n).toMonoidHom).subgroupOf B := by
  ext b
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, (he a).symm⟩
  · rintro ⟨x, hx, hxb⟩
    refine ⟨⟨x, hX hx⟩, hx, Subtype.ext ?_⟩
    rw [he]
    exact hxb

theorem commute_map_conj {G : Type*} [Group G] {X : Subgroup G} {y : G}
    (hc : ∀ x ∈ X, y * x = x * y) (n : G) :
    ∀ x ∈ X.map (MulAut.conj n).toMonoidHom, n * y * n⁻¹ * x = x * (n * y * n⁻¹) := by
  rintro _ ⟨z, hz, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc n * y * n⁻¹ * (n * z * n⁻¹) = n * (y * z) * n⁻¹ := by group
    _ = n * (z * y) * n⁻¹ := by rw [hc z hz]
    _ = n * z * n⁻¹ * (n * y * n⁻¹) := by group

theorem conj_inv_mem_of_mem_map {G : Type*} [Group G] {X : Subgroup G} {n x : G}
    (hx : x ∈ X.map (MulAut.conj n).toMonoidHom) : n⁻¹ * x * n ∈ X := by
  obtain ⟨z, hz, rfl⟩ := hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [show n⁻¹ * (n * z * n⁻¹) * n = z by group]
  exact hz

theorem swap45_neg (v : Fin 6 → ℤ) : swap45 (-v) = -swap45 v := rfl

theorem neg_mem_perpRoots_E7 {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ perpRoots .E7) :
    -γ ∈ perpRoots .E7 :=
  ⟨IsRoot.neg hγ.1, by rw [Pi.neg_apply, hγ.2, neg_zero]⟩

@[expose] def rootA234 : Fin (Tag.rank .E7) → ℤ := ![0, 1, 1, 1, 0, 0, 0]

@[expose] def perpGraphWord : List (Fin (Tag.rank .E7)) :=
  [2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 1, 3, 2, 1, 0]

theorem perpGraphWord_smul :
    (coxeterSystem .E7).wordProd perpGraphWord • (Pi.single 6 1 : Fin (Tag.rank .E7) → ℤ) =
        theta ∧
      (coxeterSystem .E7).wordProd perpGraphWord • (Pi.single 5 1 : Fin (Tag.rank .E7) → ℤ) =
        -a2Root ∧
      (coxeterSystem .E7).wordProd perpGraphWord • theta = Pi.single 1 1 ∧
      (coxeterSystem .E7).wordProd perpGraphWord • (Pi.single 3 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 4 1 ∧
      (coxeterSystem .E7).wordProd perpGraphWord • rootA234 =
        Pi.single 6 1 := by
  simp only [perpGraphWord, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
    mul_smul, simple_smul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact List.ofFn_injective (by decide +kernel)

section Roots


theorem mem_rootsD6_of_isRoot {v : Fin 6 → ℤ} {γ : Fin (Tag.rank .E7) → ℤ} (h : d6Embed v = γ)
    (hγ : IsRoot .E7 γ) : v ∈ roots (isFiniteType_cartanD 6) ∅ :=
  isRoot_d6Embed_iff.1 (h ▸ hγ)

theorem neg_mem_rootsD6 {v : Fin 6 → ℤ} (hv : v ∈ roots (isFiniteType_cartanD 6) ∅) :
    -v ∈ roots (isFiniteType_cartanD 6) ∅ :=
  isRoot_d6Embed_iff.1 (by rw [d6Embed_neg]; exact IsRoot.neg (isRoot_d6Embed hv))

end Roots

section Core


noncomputable abbrev Dperp : Subgroup (ModGL .E7 (ZMod 2)) := rootSpan .E7 (ZMod 2) (perpRoots .E7)

@[expose] noncomputable def conjDperp (n : ModGL .E7 (ZMod 2)) {M : Subgroup (ModGL .E7 (ZMod 2))}
    (h : Dperp.map (MulAut.conj n).toMonoidHom = M) : ↥Dperp ≃* ↥M :=
  (Dperp.equivMapOfInjective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective).trans
    (MulEquiv.subgroupCongr h)

theorem coe_conjDperp (n : ModGL .E7 (ZMod 2)) {M : Subgroup (ModGL .E7 (ZMod 2))}
    (h : Dperp.map (MulAut.conj n).toMonoidHom = M) (z : Dperp) :
    (conjDperp n h z : ModGL .E7 (ZMod 2)) = n * z * n⁻¹ :=
  rfl

theorem coe_conjDperp_symm (n : ModGL .E7 (ZMod 2)) {M : Subgroup (ModGL .E7 (ZMod 2))}
    (h : Dperp.map (MulAut.conj n).toMonoidHom = M) (m : M) :
    ((conjDperp n h).symm m : ModGL .E7 (ZMod 2)) = n⁻¹ * m * n := by
  have h1 := congrArg Subtype.val ((conjDperp n h).apply_symm_apply m)
  rw [coe_conjDperp] at h1
  rw [← h1]
  group

private theorem closure_induction_Dperp {S : Set (ModGL .E7 (ZMod 2))}
    (hS : Subgroup.closure S ≤ Dperp) {P : ↥Dperp → Prop}
    (hgen : ∀ s (hs : s ∈ S), P ⟨s, hS (Subgroup.subset_closure hs)⟩) (hone : P 1)
    (hmul : ∀ a b, P a → P b → P (a * b)) (hinv : ∀ a, P a → P a⁻¹)
    {x : ModGL .E7 (ZMod 2)} (hx : x ∈ Subgroup.closure S) : P ⟨x, hS hx⟩ := by
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact hgen s hs
  | one => exact hone
  | mul y z hy hz ihy ihz => exact hmul _ _ ihy ihz
  | inv y hy ihy => exact hinv _ ihy

end Core

section Frame


theorem J_le_Dperp {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ perpRoots .E7) : J γ ≤ Dperp := by
  show rootRankOneGroup .E7 (ZMod 2) γ ≤ _
  rw [rootRankOneGroup_eq_sup (K := ZMod 2) hγ.1]
  exact sup_le
    (le_iSup₂ (f := fun α (_ : α ∈ perpRoots .E7) => rootSubgroup .E7 (ZMod 2) α) γ hγ)
    (le_iSup₂ (f := fun α (_ : α ∈ perpRoots .E7) => rootSubgroup .E7 (ZMod 2) α) (-γ)
      (neg_mem_perpRoots_E7 hγ))

theorem J_eq_closure {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    J γ = Subgroup.closure (Set.range (pinnedX .E7 (ZMod 2) γ) ∪
      Set.range (pinnedX .E7 (ZMod 2) (-γ))) := by
  show rootRankOneGroup .E7 (ZMod 2) γ = _
  rw [rootRankOneGroup_eq_sup (K := ZMod 2) hγ, CFSG.Blueprint.Chevalley.rootSubgroup,
    CFSG.Blueprint.Chevalley.rootSubgroup, Subgroup.closure_union]

theorem pinnedX_mem_J {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : ZMod 2) :
    pinnedX .E7 (ZMod 2) γ c ∈ J γ := by
  rw [J_eq_closure hγ]
  exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)

theorem pinnedX_neg_mem_J {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : ZMod 2) :
    pinnedX .E7 (ZMod 2) (-γ) c ∈ J γ := by
  rw [J_eq_closure hγ]
  exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)

theorem J_d6Embed_eq_closure {v : Fin 6 → ℤ} (hv : v ∈ roots (isFiniteType_cartanD 6) ∅) :
    J (d6Embed v) = Subgroup.closure (Set.range (pinnedX .E7 (ZMod 2) (d6Embed v)) ∪
      Set.range (pinnedX .E7 (ZMod 2) (d6Embed (-v)))) := by
  rw [J_eq_closure (isRoot_d6Embed hv), d6Embed_neg]

end Frame

section Native


theorem Dperp_eq : Dperp = L7 ⊓ Subgroup.centralizer (J theta : Set (ModGL .E7 (ZMod 2))) := by
  rw [show J theta = highRootSL2 .E7 (ZMod 2) from
      rootRankOneGroup_eq_sup (K := ZMod 2) isRoot_theta,
    adjointGroup_inf_centralizer_highRootSL2_eq_of_charTwo (Or.inr (Or.inl rfl))]

theorem map_conj_Dperp (ω : List (Fin (Tag.rank .E7))) :
    Dperp.map (MulAut.conj (wordRepE7 (ZMod 2) ω : ModGL .E7 (ZMod 2))).toMonoidHom =
      L7 ⊓ Subgroup.centralizer
        (J ((coxeterSystem .E7).wordProd ω • theta) : Set (ModGL .E7 (ZMod 2))) := by
  rw [Dperp_eq, Subgroup.map_inf _ _ _ (MulAut.conj _).injective,
    map_conj_adjointGroup_of_mem (wordRepE7 (ZMod 2) ω).2,
    ← CFSG.GroupTheory.centralizer_map_conj, map_conj_wordRepE7_J ω isRoot_theta]

theorem eq_one_of_commute_frame {g : ModGL .E7 (ZMod 2)} (hg : g ∈ L7)
    (hθ : ∀ x ∈ J theta, g * x = x * g) (hβ : ∀ x ∈ J a2Root, g * x = x * g)
    (h1 : ∀ x ∈ Jn 1, g * x = x * g) (h4 : ∀ x ∈ Jn 4, g * x = x * g)
    (h6 : ∀ x ∈ Jn 6, g * x = x * g) : g = 1 := by
  have hθ' : J theta = highRootSL2 .E7 (ZMod 2) :=
    rootRankOneGroup_eq_sup (K := ZMod 2) isRoot_theta
  have hβ' : J a2Root = a2SL2 (ZMod 2) := rootRankOneGroup_eq_sup (K := ZMod 2) isRoot_a2Root
  have hgC : g ∈ rootSpan .E7 (ZMod 2) (parabolicRoots .E7 a2PerpNodes) := by
    rw [← adjointGroup_inf_centralizer_highRootSL2_inf_centralizer_a2SL2 (K := ZMod 2)
      (fun u => Subsingleton.elim u 1)]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hg,
      Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    · rw [← hθ'] at hy
      exact (hθ y hy).symm
    · rw [← hβ'] at hy
      exact (hβ y hy).symm
  rw [← subsystemGroup_eq_rootSpan, a2PerpNodes_eq_a5Nodes, ← range_a5Frame] at hgC
  obtain ⟨A, rfl⟩ := hgC
  have hinj := a5Frame_injective
  have hc : ∀ k : Fin 5, (∀ x ∈ Jn (a5chain k),
      a5Frame (ZMod 2) A * x = x * a5Frame (ZMod 2) A) → ∀ x ∈ blk k, A * x = x * A := by
    intro k hk x hx
    apply hinj
    rw [map_mul, map_mul]
    exact hk _ (by rw [← map_a5Frame_blk k]; exact Subgroup.mem_map_of_mem _ hx)
  rw [eq_one_of_commute_blk_zero_two_four (hc 0 h1) (hc 2 h4) (hc 4 h6), map_one]

@[expose] noncomputable def perpLeviEquivDperp : ↥(perpLevi .E7 (ZMod 2)) ≃* ↥Dperp :=
  ((perpLevi .E7 (ZMod 2)).equivMapOfInjective (adjointGroup .E7 (ZMod 2)).subtype
    (adjointGroup .E7 (ZMod 2)).subtype_injective).trans
    (MulEquiv.subgroupCongr map_subtype_perpLevi_E7)

@[expose] noncomputable def perpGraph : MulAut ↥Dperp :=
  perpLeviEquivDperp.symm.trans ((spinEquivPerpLevi (ZMod 2)).symm.trans
    ((graphSpin 6 (ZMod 2) 5).trans ((spinEquivPerpLevi (ZMod 2)).trans perpLeviEquivDperp)))

theorem perpGraph_pinnedX {v : Fin 6 → ℤ} (hv : v ∈ roots (isFiniteType_cartanD 6) ∅)
    (c : ZMod 2) (h : pinnedX .E7 (ZMod 2) (d6Embed v) c ∈ Dperp) :
    (perpGraph ⟨pinnedX .E7 (ZMod 2) (d6Embed v) c, h⟩ : ModGL .E7 (ZMod 2)) =
      pinnedX .E7 (ZMod 2) (d6Embed (swap45 v)) c := by
  have h1 : perpLeviEquivDperp.symm ⟨pinnedX .E7 (ZMod 2) (d6Embed v) c, h⟩ =
      ⟨d6LeviPar (ZMod 2) v c, d6LeviPar_mem_perpLevi hv c⟩ :=
    (MulEquiv.symm_apply_eq _).2 rfl
  have h2 : (spinEquivPerpLevi (ZMod 2)).symm ⟨d6LeviPar (ZMod 2) v c, d6LeviPar_mem_perpLevi hv c⟩ =
      SpinPlus.x 6 (ZMod 2) three_le_rank_D6 v c :=
    (MulEquiv.symm_apply_eq _).2 (spinEquivPerpLevi_x hv c).symm
  simp only [perpGraph, MulEquiv.trans_apply]
  rw [h1, h2, graphSpin_x hv, spinEquivPerpLevi_x (swap45_mem_roots hv)]
  rfl

theorem perpGraph_mem_J {v : Fin 6 → ℤ} (hv : v ∈ roots (isFiniteType_cartanD 6) ∅)
    {x : ModGL .E7 (ZMod 2)} (hx : x ∈ J (d6Embed v)) (hxD : x ∈ Dperp) :
    (perpGraph ⟨x, hxD⟩ : ModGL .E7 (ZMod 2)) ∈ J (d6Embed (swap45 v)) := by
  have hle : Subgroup.closure (Set.range (pinnedX .E7 (ZMod 2) (d6Embed v)) ∪
      Set.range (pinnedX .E7 (ZMod 2) (d6Embed (-v)))) ≤ Dperp :=
    J_d6Embed_eq_closure hv ▸ J_le_Dperp (d6Embed_mem_perpRoots hv)
  have hx' : x ∈ Subgroup.closure (Set.range (pinnedX .E7 (ZMod 2) (d6Embed v)) ∪
      Set.range (pinnedX .E7 (ZMod 2) (d6Embed (-v)))) := J_d6Embed_eq_closure hv ▸ hx
  refine closure_induction_Dperp hle
    (P := fun z => (perpGraph z : ModGL .E7 (ZMod 2)) ∈ J (d6Embed (swap45 v)))
    (fun s hs => ?_) (by rw [map_one]; exact one_mem _)
    (fun a b ha hb => by rw [map_mul, Subgroup.coe_mul]; exact mul_mem ha hb)
    (fun a ha => by rw [map_inv, Subgroup.coe_inv]; exact inv_mem ha) hx'
  rcases hs with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · show (perpGraph ⟨pinnedX .E7 (ZMod 2) (d6Embed v) c, _⟩ : ModGL .E7 (ZMod 2)) ∈ _
    rw [perpGraph_pinnedX hv]
    exact pinnedX_mem_J (isRoot_d6Embed (swap45_mem_roots hv)) c
  · show (perpGraph ⟨pinnedX .E7 (ZMod 2) (d6Embed (-v)) c, _⟩ : ModGL .E7 (ZMod 2)) ∈ _
    rw [perpGraph_pinnedX (neg_mem_rootsD6 hv), swap45_neg, d6Embed_neg]
    exact pinnedX_neg_mem_J (isRoot_d6Embed (swap45_mem_roots hv)) c

theorem perpGraph_fix {v : Fin 6 → ℤ} (hv : v ∈ roots (isFiniteType_cartanD 6) ∅)
    (hsv : swap45 v = v) {x : ModGL .E7 (ZMod 2)} (hx : x ∈ J (d6Embed v)) (hxD : x ∈ Dperp) :
    perpGraph ⟨x, hxD⟩ = ⟨x, hxD⟩ := by
  have hle : Subgroup.closure (Set.range (pinnedX .E7 (ZMod 2) (d6Embed v)) ∪
      Set.range (pinnedX .E7 (ZMod 2) (d6Embed (-v)))) ≤ Dperp :=
    J_d6Embed_eq_closure hv ▸ J_le_Dperp (d6Embed_mem_perpRoots hv)
  have hx' : x ∈ Subgroup.closure (Set.range (pinnedX .E7 (ZMod 2) (d6Embed v)) ∪
      Set.range (pinnedX .E7 (ZMod 2) (d6Embed (-v)))) := J_d6Embed_eq_closure hv ▸ hx
  refine closure_induction_Dperp hle (P := fun z => perpGraph z = z) (fun s hs => ?_)
    (map_one _) (fun a b ha hb => by rw [map_mul, ha, hb])
    (fun a ha => by rw [map_inv, ha]) hx'
  apply Subtype.ext
  rcases hs with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · show (perpGraph ⟨pinnedX .E7 (ZMod 2) (d6Embed v) c, _⟩ : ModGL .E7 (ZMod 2)) = _
    rw [perpGraph_pinnedX hv, hsv]
  · show (perpGraph ⟨pinnedX .E7 (ZMod 2) (d6Embed (-v)) c, _⟩ : ModGL .E7 (ZMod 2)) = _
    rw [perpGraph_pinnedX (neg_mem_rootsD6 hv), swap45_neg, hsv]

theorem map_perpGraph_J {v : Fin 6 → ℤ} (hv : v ∈ roots (isFiniteType_cartanD 6) ∅) :
    ((J (d6Embed v)).subgroupOf Dperp).map perpGraph.toMonoidHom =
      (J (d6Embed (swap45 v))).subgroupOf Dperp := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hz ⊢
    exact perpGraph_mem_J hv hz z.2
  · intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    have hv' := swap45_mem_roots hv
    have hle : Subgroup.closure (Set.range (pinnedX .E7 (ZMod 2) (d6Embed (swap45 v))) ∪
        Set.range (pinnedX .E7 (ZMod 2) (d6Embed (-swap45 v)))) ≤ Dperp :=
      J_d6Embed_eq_closure hv' ▸ J_le_Dperp (d6Embed_mem_perpRoots hv')
    have hz' : (z : ModGL .E7 (ZMod 2)) ∈ Subgroup.closure
        (Set.range (pinnedX .E7 (ZMod 2) (d6Embed (swap45 v))) ∪
          Set.range (pinnedX .E7 (ZMod 2) (d6Embed (-swap45 v)))) :=
      J_d6Embed_eq_closure hv' ▸ hz
    refine closure_induction_Dperp hle
      (P := fun z => z ∈ ((J (d6Embed v)).subgroupOf Dperp).map perpGraph.toMonoidHom)
      (fun s hs => ?_) (one_mem _) (fun a b ha hb => mul_mem ha hb) (fun a ha => inv_mem ha) hz'
    rcases hs with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · refine ⟨⟨pinnedX .E7 (ZMod 2) (d6Embed v) c,
        J_le_Dperp (d6Embed_mem_perpRoots hv) (pinnedX_mem_J (isRoot_d6Embed hv) c)⟩,
        pinnedX_mem_J (isRoot_d6Embed hv) c, Subtype.ext ?_⟩
      exact perpGraph_pinnedX hv c _
    · have hnv := neg_mem_rootsD6 hv
      refine ⟨⟨pinnedX .E7 (ZMod 2) (d6Embed (-v)) c,
        J_le_Dperp (d6Embed_mem_perpRoots hnv) (pinnedX_mem_J (isRoot_d6Embed hnv) c)⟩, ?_,
        Subtype.ext ?_⟩
      · simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        rw [d6Embed_neg]
        exact pinnedX_neg_mem_J (isRoot_d6Embed hv) c
      · show (perpGraph ⟨pinnedX .E7 (ZMod 2) (d6Embed (-v)) c, _⟩ : ModGL .E7 (ZMod 2)) = _
        rw [perpGraph_pinnedX hnv, swap45_neg]

theorem not_isInnerAut_perpGraph : ¬ IsInnerAut perpGraph := by
  rintro ⟨y, hy⟩
  have hcomm : ∀ {v : Fin 6 → ℤ}, v ∈ roots (isFiniteType_cartanD 6) ∅ → swap45 v = v →
      ∀ x ∈ J (d6Embed v), (y : ModGL .E7 (ZMod 2)) * x = x * y := by
    intro v hv hsv x hx
    have hxD := J_le_Dperp (d6Embed_mem_perpRoots hv) hx
    have h := congrArg Subtype.val (perpGraph_fix hv hsv hx hxD)
    rw [hy, MulAut.conj_apply] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    calc (y : ModGL .E7 (ZMod 2)) * x = y * x * (y : ModGL .E7 (ZMod 2))⁻¹ * y := by group
      _ = x * y := by rw [h]
  have hyL : (y : ModGL .E7 (ZMod 2)) ∈ L7 := rootSpan_le_adjointGroup' _ y.2
  have hyθ : ∀ x ∈ J theta, (y : ModGL .E7 (ZMod 2)) * x = x * y := by
    have hy2 : (y : ModGL .E7 (ZMod 2)) ∈
        L7 ⊓ Subgroup.centralizer (J theta : Set (ModGL .E7 (ZMod 2))) := by
      rw [← Dperp_eq]
      exact y.2
    intro x hx
    exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy2).2) x hx).symm
  obtain ⟨hw7, hw6, hwθ, hw4, hw234⟩ := perpGraphWord_smul
  have hv0 : (Pi.single 0 1 : Fin 6 → ℤ) ∈ roots (isFiniteType_cartanD 6) ∅ :=
    mem_rootsD6_of_isRoot (γ := Pi.single 6 1) (by decide) (isRoot_single .E7 _)
  have hv1 : (Pi.single 1 1 : Fin 6 → ℤ) ∈ roots (isFiniteType_cartanD 6) ∅ :=
    mem_rootsD6_of_isRoot (γ := Pi.single 5 1) (by decide) (isRoot_single .E7 _)
  have hv3 : (Pi.single 3 1 : Fin 6 → ℤ) ∈ roots (isFiniteType_cartanD 6) ∅ :=
    mem_rootsD6_of_isRoot (γ := Pi.single 3 1) (by decide) (isRoot_single .E7 _)
  have hv234 : (![0, 0, 0, 1, 1, 1] : Fin 6 → ℤ) ∈ roots (isFiniteType_cartanD 6) ∅ :=
    mem_rootsD6_of_isRoot (γ := rootA234) (by decide)
      (mem_rootFinset.1 (by decide +kernel))
  have hc7 : ∀ x ∈ J (Pi.single 6 1), (y : ModGL .E7 (ZMod 2)) * x = x * y := by
    have h := hcomm hv0 (by decide)
    rwa [show d6Embed (Pi.single 0 1) = (Pi.single 6 1 : Fin (Tag.rank .E7) → ℤ) by decide] at h
  have hc6 : ∀ x ∈ J (Pi.single 5 1), (y : ModGL .E7 (ZMod 2)) * x = x * y := by
    have h := hcomm hv1 (by decide)
    rwa [show d6Embed (Pi.single 1 1) = (Pi.single 5 1 : Fin (Tag.rank .E7) → ℤ) by decide] at h
  have hc4 : ∀ x ∈ J (Pi.single 3 1), (y : ModGL .E7 (ZMod 2)) * x = x * y := by
    have h := hcomm hv3 (by decide)
    rwa [show d6Embed (Pi.single 3 1) = (Pi.single 3 1 : Fin (Tag.rank .E7) → ℤ) by decide] at h
  have hc234 : ∀ x ∈ J rootA234, (y : ModGL .E7 (ZMod 2)) * x = x * y := by
    have h := hcomm hv234 (by decide)
    rwa [show d6Embed ![0, 0, 0, 1, 1, 1] = rootA234 by
      decide] at h
  have hT : ∀ {γ : Fin (Tag.rank .E7) → ℤ}, IsRoot .E7 γ →
      (∀ x ∈ J γ, (y : ModGL .E7 (ZMod 2)) * x = x * y) →
      ∀ x ∈ J ((coxeterSystem .E7).wordProd perpGraphWord • γ),
        (wordRepE7 (ZMod 2) perpGraphWord : ModGL .E7 (ZMod 2)) * y *
            (wordRepE7 (ZMod 2) perpGraphWord : ModGL .E7 (ZMod 2))⁻¹ * x =
          x * ((wordRepE7 (ZMod 2) perpGraphWord : ModGL .E7 (ZMod 2)) * y *
            (wordRepE7 (ZMod 2) perpGraphWord : ModGL .E7 (ZMod 2))⁻¹) := by
    intro γ hγ hc
    have h := commute_map_conj hc (wordRepE7 (ZMod 2) perpGraphWord : ModGL .E7 (ZMod 2))
    rwa [map_conj_wordRepE7_J perpGraphWord hγ] at h
  have h7 := hT (isRoot_single .E7 6) hc7
  rw [hw7] at h7
  have h6 := hT (isRoot_single .E7 5) hc6
  rw [hw6, J_neg isRoot_a2Root] at h6
  have hθ := hT isRoot_theta hyθ
  rw [hwθ] at hθ
  have h4 := hT (isRoot_single .E7 3) hc4
  rw [hw4] at h4
  have h234 := hT (mem_rootFinset.1 (by decide +kernel)) hc234
  rw [hw234] at h234
  have hnL : (wordRepE7 (ZMod 2) perpGraphWord : ModGL .E7 (ZMod 2)) ∈ L7 :=
    (wordRepE7 (ZMod 2) perpGraphWord).2
  have key := eq_one_of_commute_frame (L7.mul_mem (L7.mul_mem hnL hyL) (L7.inv_mem hnL)) h7 h6 hθ
    h4 h234
  have hy1 : y = 1 := by
    apply Subtype.ext
    calc (y : ModGL .E7 (ZMod 2)) =
        (wordRepE7 (ZMod 2) perpGraphWord : ModGL .E7 (ZMod 2))⁻¹ *
          ((wordRepE7 (ZMod 2) perpGraphWord : ModGL .E7 (ZMod 2)) * y *
            (wordRepE7 (ZMod 2) perpGraphWord : ModGL .E7 (ZMod 2))⁻¹) *
          (wordRepE7 (ZMod 2) perpGraphWord : ModGL .E7 (ZMod 2)) := by group
      _ = 1 := by rw [key]; group
  have hv4 : (Pi.single 4 1 : Fin 6 → ℤ) ∈ roots (isFiniteType_cartanD 6) ∅ :=
    mem_rootsD6_of_isRoot (γ := Pi.single 2 1) (by decide) (isRoot_single .E7 _)
  have hmem : pinnedX .E7 (ZMod 2) (d6Embed (Pi.single 4 1)) 1 ∈ Dperp :=
    J_le_Dperp (d6Embed_mem_perpRoots hv4) (pinnedX_mem_J (isRoot_d6Embed hv4) 1)
  have h := perpGraph_pinnedX hv4 1 hmem
  rw [hy, hy1, map_one, MulAut.one_apply] at h
  have h' : pinnedX .E7 (ZMod 2) (d6Embed (Pi.single 4 1)) 1 =
      pinnedX .E7 (ZMod 2) (d6Embed (swap45 (Pi.single 4 1))) 1 := h
  rw [show d6Embed (Pi.single 4 1) = (Pi.single 2 1 : Fin (Tag.rank .E7) → ℤ) by decide,
    show d6Embed (swap45 (Pi.single 4 1)) = (Pi.single 1 1 : Fin (Tag.rank .E7) → ℤ) by decide]
    at h'
  have h21 := eq_of_pinnedX_eq_pinnedX_of_pos (isRoot_single .E7 2) (isRoot_single .E7 1)
    (by rw [height_single]; norm_num) one_ne_zero h'
  exact absurd h21 (by decide)

end Native

end CFSG.StandardType.FrameRoute.FS81.E7Frame
