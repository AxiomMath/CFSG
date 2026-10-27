module

public import CFSG.Monster.B.E6.FixedE6RootVector
public import CFSG.Monster.B.E6.StdF4LeviRank

public noncomputable section

namespace CFSG.Monster.B.E6.FixedE6Root

open Module CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.C2E6Overlap (K barHom)
open CFSG.Monster.B.Classical.E6Adjoint CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.StdF4

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem linearIndependent_coe_of_fixedL
    {ι : Type*} {w : ι → fixedL}
    (hw : LinearIndependent (ZMod 2) w) : LinearIndependent K fun i => (w i : V) := by
  have h := (Module.Flat.linearIndependent_one_tmul (S := K) hw).map'
    (tensorEquiv : TensorProduct (ZMod 2) K fixedL →ₗ[K] V) tensorEquiv.ker
  convert h using 1
  funext i
  exact (tensorEquiv_one_tmul (w i)).symm

theorem finrank_span_image_coe
    (t : Set fixedL) :
    finrank K (Submodule.span K ((fun u : fixedL => (u : V)) '' t)) =
      finrank (ZMod 2) (Submodule.span (ZMod 2) t) := by
  obtain ⟨b, hbt, hspan, hli⟩ := exists_linearIndependent (ZMod 2) t
  have : Fintype b := Fintype.ofFinite b
  set v : b → V := fun x => ((x : fixedL) : V)
  have hliK : LinearIndependent K v := linearIndependent_coe_of_fixedL hli
  have h1 : finrank (ZMod 2) (Submodule.span (ZMod 2) t) = Fintype.card b := by
    rw [← hspan, ← finrank_span_eq_card hli, Subtype.range_coe]
  have h2 : Submodule.span K ((fun u : fixedL => (u : V)) '' t) =
      Submodule.span K (Set.range v) := by
    have key : ∀ u ∈ Submodule.span (ZMod 2) b, (u : V) ∈ Submodule.span K (Set.range v) := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | smul c x _ hx => exact Submodule.smul_of_tower_mem _ c hx
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨u, hu, rfl⟩
      exact key u (hspan ▸ Submodule.subset_span hu)
    · rintro _ ⟨x, rfl⟩
      exact ⟨x, hbt x.2, rfl⟩
  rw [h2, finrank_span_eq_card hliK, h1]

theorem finrank_range_eq_of_forall
    {φ : Module.End (ZMod 2) fixedL} {Φ : Module.End K V}
    (h : ∀ u : fixedL, Φ u = φ u) :
    finrank (ZMod 2) (LinearMap.range φ) = finrank K (LinearMap.range Φ) := by
  have hr : LinearMap.range Φ =
      Submodule.span K ((fun u : fixedL => (u : V)) '' (LinearMap.range φ : Set fixedL)) := by
    rw [LinearMap.range_eq_map, ← span_K_fixedL, Submodule.map_span]
    congr 1
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨φ ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩, (h ⟨w, hw⟩).symm⟩
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, u.2, h u⟩
  rw [hr, finrank_span_image_coe, Submodule.span_eq]

theorem finrank_range_adL
    (a : fixedL) :
    finrank (ZMod 2) (LinearMap.range (adL a)) = finrank K (LinearMap.range (ad K (a : V))) :=
  finrank_range_eq_of_forall fun _ => rfl

theorem ad_gEnd
    (g : stdGroup) (a : V) : ad K (gEnd g a) = gEnd g * ad K a * gEnd g⁻¹ := by
  refine LinearMap.ext fun u => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, ad_apply, ad_apply,
    adjointGroup_bracket (stdGroup_mem_adjointGroup g), gEnd_gEnd_inv]

theorem finrank_range_conj
    (g : stdGroup) (f : Module.End K V) :
    finrank K (LinearMap.range (gEnd g * f * gEnd g⁻¹)) = finrank K (LinearMap.range f) := by
  have hD : LinearMap.range (gEnd g⁻¹) = ⊤ :=
    LinearMap.range_eq_top.2 fun v => ⟨gEnd g v, gEnd_inv_gEnd g v⟩
  have hC : Function.Injective (gEnd g) := fun v w e => by
    have := congrArg (gEnd g⁻¹) e
    rwa [gEnd_inv_gEnd, gEnd_inv_gEnd] at this
  rw [Module.End.mul_eq_comp, LinearMap.range_comp_of_range_eq_top _ hD, Module.End.mul_eq_comp,
    LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective _ hC _).finrank_eq.symm

theorem finrank_range_adL_gL
    (g : stdGroup) (a : fixedL) :
    finrank (ZMod 2) (LinearMap.range (adL (gL g a))) =
      finrank (ZMod 2) (LinearMap.range (adL a)) := by
  rw [finrank_range_adL, finrank_range_adL, coe_gL_apply, ad_gEnd, finrank_range_conj]

@[expose] def adIdx (A : ℕ) (L : List ℕ) : List ℕ := L.flatMap (brIdx A)

theorem bracket_lab_lvec_adIdx
    (A : Fin 78) :
    ∀ L : List ℕ, (∀ l ∈ L, l < 78) →
      bracket K (Finsupp.single (lab A) 1) (lvec K L) = lvec K (adIdx A L)
  | [], _ => by simp [adIdx, lvec_nil]
  | l :: L, hL => by
    have hl : l < 78 := hL l List.mem_cons_self
    have ih := bracket_lab_lvec_adIdx A L fun l' h' => hL l' (List.mem_cons_of_mem _ h')
    have e : adIdx A (l :: L) = brIdx A l ++ adIdx A L := List.flatMap_cons
    rw [e, lvec_append, lvec_cons, map_add, ih, toVec_one_shiftLeft' hl, bracket_lab,
      toVec_brMask]

theorem rootVec_eq_single_lab
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (A : Fin 78)
    (h6 : ¬(A : ℕ) < 6) (h : e6Certificate.root ((A : ℕ) - 6) = γ) :
    rootVec Tag.E6 K γ = Finsupp.single (lab A) 1 := by
  rw [CFSG.Monster.B.Classical.E6Adjoint.rootVec_eq_single hγ, lab_of_ge h6]
  exact congrArg (fun l => Finsupp.single l (1 : K)) (congrArg Sum.inr (Subtype.ext h.symm))

theorem a0_eq_single_lab : a0 = Finsupp.single (lab 76) 1 :=
  rootVec_eq_single_lab isRoot_theta 76 (by decide) (by decide)

theorem rootVec_repRootL_one :
    rootVec Tag.E6 K (repRootL 1) = Finsupp.single (lab 74) 1 :=
  rootVec_eq_single_lab (isRoot_repRootL 1) 74 (by decide) (by decide)

theorem rootVec_repRootL_two :
    rootVec Tag.E6 K (repRootL 2) = Finsupp.single (lab 9) 1 :=
  rootVec_eq_single_lab (isRoot_repRootL 2) 9 (by decide) (by decide)

@[expose] def fIdxA (L : List ℕ) : List ℕ := adIdx 76 L

@[expose] def fIdxB (L : List ℕ) : List ℕ := adIdx 76 L ++ adIdx 74 L

@[expose] def fIdxC (L : List ℕ) : List ℕ := adIdx 76 L ++ adIdx 9 L

@[expose] def pivA : List ℕ := [
  76, 74, 72, 68, 67, 64, 62, 61, 58, 55, 54, 50, 49, 45, 39, 38, 34, 27, 26, 15, 7, 0]

@[expose] def preA : List (List ℕ) := [
  [1], [14], [25], [36], [37], [43], [47], [48], [52], [56], [57], [59], [60], [63], [65], [66],
  [69], [70], [71], [73], [75], [77]]

@[expose] def zsA : List ℕ := [
  75557863725914323419136, 18889465931478580854784, 4722366482869645213696, 295147905179352825856,
  147573952589676412928, 18446744073709551616, 4611686018427387904, 2305843009213693952,
  288230376151711744, 36028797018963968, 18014398509481984, 1125899906842624, 562949953421312,
  35184372088832, 549755813888, 274877906944, 17179869184, 134217728, 67108864, 32768, 128, 41]

@[expose] def pivB : List ℕ := [
  74, 76, 72, 68, 67, 64, 62, 61, 58, 54, 49, 46, 41, 35, 31, 29, 24, 19, 17, 9, 0, 1]

@[expose] def preB : List (List ℕ) := [
  [3], [1, 3], [18], [28], [30], [33], [40], [42], [44], [51], [53], [56], [59], [63], [65], [66],
  [69], [70], [71], [73], [77], [75, 77]]

@[expose] def zsB : List ℕ := [
  18889465931478580854784, 75557863725914323419136, 4722366482869645213696, 295147905179352825856,
  147573952589676412928, 18446744073709551616, 4611686018427387904, 2305843009213693952,
  288230376151711744, 18014398509481984, 562949953421312, 36099165763141632, 1128098930098176,
  35218731827200, 551903297536, 275414777856, 17196646400, 134742016, 67239936, 33280, 16425, 16514]

@[expose] def pivC : List ℕ := [
  9, 76, 15, 17, 19, 24, 74, 3, 31, 14, 16, 20, 23, 68, 67, 49, 32, 64, 54, 62, 61, 58, 47, 50, 45,
  39, 38, 34, 27, 26, 7, 0]

@[expose] def preC : List (List ℕ) := [
  [2], [1, 2], [7], [8], [10], [13], [14], [18], [21], [25], [28], [30], [33], [36], [37], [38],
  [42], [43], [45], [47], [48], [50], [56], [59], [63], [65], [66], [69], [70], [71], [75],
  [18, 77]]

@[expose] def zsC : List ℕ := [
  512, 75557863725914323419136, 32768, 131072, 524288, 16777216, 18889465931478580854784, 8,
  2147483648, 4722366482869645230080, 65536, 1048576, 8388608, 295147905179352825856,
  147573952589676412928, 562949953421312, 4294967296, 18446744073709551616, 18014398509481984,
  4611686018427387904, 2305843009213693952, 288230376151711744, 36169534507319296,
  5629499534213120, 144150372447944704, 549755813888, 1152921779484753920, 17179869184, 134217728,
  67108864, 9444732965739290427520, 33]

theorem certOK_A : certOK fIdxA pivA preA zsA = true := by decide +kernel

theorem certOK_B : certOK fIdxB pivB preB zsB = true := by decide +kernel

theorem certOK_C : certOK fIdxC pivC preC zsC = true := by decide +kernel

theorem finrank_range_ad_a0 :
    finrank K (LinearMap.range (ad K a0)) = 22 :=
  finrank_range_of_certOK _ fIdxA (fun L hL => by
    rw [ad_apply, a0_eq_single_lab, bracket_lab_lvec_adIdx 76 L hL]
    rfl) pivA preA zsA certOK_A

theorem ad_add_lvec
    (x y : V) {A B : Fin 78} (hx : x = Finsupp.single (lab A) 1)
    (hy : y = Finsupp.single (lab B) 1) (L : List ℕ) (hL : ∀ l ∈ L, l < 78) :
    ad K (x + y) (lvec K L) = lvec K (adIdx A L ++ adIdx B L) := by
  rw [ad_apply, map_add, LinearMap.add_apply, hx, hy, bracket_lab_lvec_adIdx A L hL,
    bracket_lab_lvec_adIdx B L hL, lvec_append]

theorem finrank_range_ad_a0_add_one :
    finrank K (LinearMap.range (ad K (a0 + rootVec Tag.E6 K (repRootL 1)))) = 22 :=
  finrank_range_of_certOK _ fIdxB
    (fun L hL => ad_add_lvec _ _ a0_eq_single_lab rootVec_repRootL_one L hL)
    pivB preB zsB certOK_B

theorem finrank_range_ad_a0_add_two :
    finrank K (LinearMap.range (ad K (a0 + rootVec Tag.E6 K (repRootL 2)))) = 32 :=
  finrank_range_of_certOK _ fIdxC
    (fun L hL => ad_add_lvec _ _ a0_eq_single_lab rootVec_repRootL_two L hL)
    pivC preC zsC certOK_C

theorem fin5_cases : ∀ i : Fin 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide

abbrev rootVecSet :
    Set fixedL := rootVecOf '' rootClass

theorem gL_mem_rootVecSet
    {a : fixedL} (ha : a ∈ rootVecSet) (g : stdGroup) :
    gL g a ∈ rootVecSet := by
  obtain ⟨q, hq, rfl⟩ := ha
  exact ⟨g * q * g⁻¹, conj_mem_rootClass hq g, rootVecOf_conj hq g⟩

theorem finrank_range_adL_a0L :
    finrank (ZMod 2) (LinearMap.range (adL a0L)) = 22 := by
  rw [finrank_range_adL, coe_a0L, finrank_range_ad_a0]

theorem finrank_range_adL_of_mem
    {a : fixedL} (ha : a ∈ rootVecSet) :
    finrank (ZMod 2) (LinearMap.range (adL a)) = 22 := by
  obtain ⟨q, hq, rfl⟩ := ha
  obtain ⟨g, rfl⟩ := (mem_rootClass_iff q).1 hq
  rw [rootVecOf_rootMap, finrank_range_adL_gL, finrank_range_adL_a0L]

theorem bracketL_eq_zero_iff_commute
    {q₁ q₂ : stdGroup} (h₁ : q₁ ∈ rootClass)
    (h₂ : q₂ ∈ rootClass) : bracketL (rootVecOf q₁) (rootVecOf q₂) = 0 ↔ Commute q₁ q₂ := by
  obtain ⟨k, i, rfl, rfl⟩ := exists_conj_pair h₁ h₂
  obtain ⟨e₁, e₂⟩ := rootVecOf_conj_pair k i
  rw [e₁, e₂, bracketL_gL, commute_conj_pair_iff, ← bracketL_a0L_repPoint_eq_zero_iff]
  exact ⟨fun h => gL_injective k (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩

@[expose] def x2G :
    stdGroup :=
  ⟨xUnit Tag.E6 K ⟨1, by decide⟩ 1, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    (xUnit_mem_graphFixedPosUnipotent (t := TwistTag.E6) (σ := barHom) rfl (map_one barHom))⟩

theorem single_one_add_repRootL_one :
    (Pi.single (⟨1, by decide⟩ : Fin Tag.E6.rank) 1 : Fin Tag.E6.rank → ℤ) + repRootL 1 =
      theta := by
  decide

theorem gEnd_x2G_rootVec :
    gEnd x2G (rootVec Tag.E6 K (repRootL 1)) = rootVec Tag.E6 K (repRootL 1) + a0 := by
  have hne : repRootL 1 ≠ -(Pi.single (⟨1, by decide⟩ : Fin Tag.E6.rank) 1) := by decide
  change (xUnit Tag.E6 K ⟨1, by decide⟩ 1 : Module.End K V) _ = _
  rw [coe_xUnit, xOp_eq, CFSG.Monster.B.Classical.E6Adjoint.rootOp_apply,
    bracket_rootVec_rootVec (isRoot_single _ _) (isRoot_repRootL 1) hne,
    single_one_add_repRootL_one, form_rootVec_rootVec hne, one_smul, zero_smul, smul_zero,
    add_zero]
  rfl

theorem a0L_add_rootVecOf_repPoint_one :
    a0L + rootVecOf (repPoint 1) = gL x2G (rootVecOf (repPoint 1)) := by
  refine Subtype.ext ?_
  rw [Submodule.coe_add, coe_a0L, coe_gL_apply, coe_rootVecOf_repPoint, gEnd_x2G_rootVec,
    add_comm]

theorem a0L_add_rootVecOf_repPoint_one_mem :
    a0L + rootVecOf (repPoint 1) ∈ rootVecSet := by
  rw [a0L_add_rootVecOf_repPoint_one]
  exact gL_mem_rootVecSet ⟨_, repPoint_mem_rootClass 1, rfl⟩ x2G

theorem finrank_range_adL_a0L_add_one :
    finrank (ZMod 2) (LinearMap.range (adL (a0L + rootVecOf (repPoint 1)))) = 22 := by
  rw [finrank_range_adL, Submodule.coe_add, coe_a0L, coe_rootVecOf_repPoint]
  exact finrank_range_ad_a0_add_one

theorem finrank_range_adL_a0L_add_two :
    finrank (ZMod 2) (LinearMap.range (adL (a0L + rootVecOf (repPoint 2)))) = 32 := by
  rw [finrank_range_adL, Submodule.coe_add, coe_a0L, coe_rootVecOf_repPoint]
  exact finrank_range_ad_a0_add_two

theorem finrank_range_adL_add_of_commute
    {q₁ q₂ : stdGroup} (h₁ : q₁ ∈ rootClass)
    (h₂ : q₂ ∈ rootClass) (hne : rootVecOf q₁ ≠ rootVecOf q₂) (hc : Commute q₁ q₂) :
    (finrank (ZMod 2) (LinearMap.range (adL (rootVecOf q₁ + rootVecOf q₂))) = 22 ∨
      finrank (ZMod 2) (LinearMap.range (adL (rootVecOf q₁ + rootVecOf q₂))) = 32) ∧
    (rootVecOf q₁ + rootVecOf q₂ ∈ rootVecSet ↔
      finrank (ZMod 2) (LinearMap.range (adL (rootVecOf q₁ + rootVecOf q₂))) = 22) := by
  obtain ⟨k, i, rfl, rfl⟩ := exists_conj_pair h₁ h₂
  have hi := (commute_conj_pair_iff k i).1 hc
  obtain ⟨e₁, e₂⟩ := rootVecOf_conj_pair k i
  rw [e₁, e₂] at hne ⊢
  rw [← map_add, finrank_range_adL_gL]
  rcases fin5_cases i with rfl | rfl | rfl | rfl | rfl
  · exfalso
    apply hne
    rw [repPoint_zero, rootVecOf_rootInv]
  · rw [finrank_range_adL_a0L_add_one]
    exact ⟨Or.inl rfl, iff_of_true (gL_mem_rootVecSet a0L_add_rootVecOf_repPoint_one_mem k) rfl⟩
  · rw [finrank_range_adL_a0L_add_two]
    refine ⟨Or.inr rfl, iff_of_false (fun hmem => ?_) (by decide)⟩
    have h22 := finrank_range_adL_of_mem hmem
    rw [finrank_range_adL_gL, finrank_range_adL_a0L_add_two] at h22
    exact absurd h22 (by decide)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)

theorem fixed_E6_root_adjoint_ranks_and_commuting_sums :
    (∀ g : stdGroup, rootVecOf (g * rootInv * g⁻¹) = actStar (SemidirectProduct.inl g) a0L) ∧
    (∀ a u : fixedL, adL a u = bracketL a u) ∧
    (∀ a : fixedL, finrank (ZMod 2) (LinearMap.range (adL a)) =
      finrank K (LinearMap.range (ad K (a : V)))) ∧
    (∀ a ∈ rootVecOf '' {q : stdGroup | IsConj rootInv q},
      finrank (ZMod 2) (LinearMap.range (adL a)) = 22) ∧
    (∀ q₁ q₂ : stdGroup, IsConj rootInv q₁ → IsConj rootInv q₂ →
      (bracketL (rootVecOf q₁) (rootVecOf q₂) = 0 ↔ Commute q₁ q₂)) ∧
    ∀ q₁ q₂ : stdGroup, IsConj rootInv q₁ → IsConj rootInv q₂ →
      rootVecOf q₁ ≠ rootVecOf q₂ → Commute q₁ q₂ →
        (finrank (ZMod 2) (LinearMap.range (adL (rootVecOf q₁ + rootVecOf q₂))) = 22 ∨
          finrank (ZMod 2) (LinearMap.range (adL (rootVecOf q₁ + rootVecOf q₂))) = 32) ∧
        (rootVecOf q₁ + rootVecOf q₂ ∈ rootVecOf '' {q : stdGroup | IsConj rootInv q} ↔
          finrank (ZMod 2) (LinearMap.range (adL (rootVecOf q₁ + rootVecOf q₂))) = 22) :=
  ⟨rootVecOf_conj_rootInv, fun _ _ => rfl,
    finrank_range_adL, fun _ ha => finrank_range_adL_of_mem ha,
    fun _ _ h₁ h₂ => bracketL_eq_zero_iff_commute h₁ h₂,
    fun _ _ h₁ h₂ hne hc => finrank_range_adL_add_of_commute h₁ h₂ hne hc⟩

end CFSG.Monster.B.E6.FixedE6Root
