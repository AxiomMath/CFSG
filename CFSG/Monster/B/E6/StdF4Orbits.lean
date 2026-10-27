module

public import CFSG.Monster.B.E6.StdF4Cells
public import CFSG.Monster.B.E6.StdF4Orders

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.Classical

@[expose] def conjOrbit {M : Type*} [Group M] (H : Subgroup M) (x : M) : Set M :=
  {y | ∃ c ∈ H, c * x * c⁻¹ = y}

theorem mem_conjOrbit_self {M : Type*} [Group M] (H : Subgroup M) (x : M) : x ∈ conjOrbit H x :=
  ⟨1, one_mem H, by rw [one_mul, inv_one, mul_one]⟩

@[expose] def rootMap
    (g : stdGroup) : stdGroup := g * rootInv * g⁻¹

theorem rootMap_one :
    rootMap 1 = rootInv := by
  rw [rootMap, one_mul, inv_one, mul_one]

theorem rootMap_mul
    (g h : stdGroup) : rootMap (g * h) = g * rootMap h * g⁻¹ := by
  simp only [rootMap]
  group

theorem rootMap_eq_rootMap_iff
    (g h : stdGroup) : rootMap g = rootMap h ↔ g⁻¹ * h ∈ PJ := by
  rw [Subgroup.mem_subgroupOf, ← mem_centralizer_rootInv_iff]
  constructor
  · intro e
    calc g⁻¹ * h * rootInv * (g⁻¹ * h)⁻¹ = g⁻¹ * rootMap h * g := by rw [rootMap]; group
      _ = g⁻¹ * rootMap g * g := by rw [e]
      _ = rootInv := by rw [rootMap]; group
  · intro hp
    calc rootMap g = g * (g⁻¹ * h * rootInv * (g⁻¹ * h)⁻¹) * g⁻¹ := by rw [hp, rootMap]
      _ = rootMap h := by rw [rootMap]; group

theorem rootMap_mul_of_mem
    (g : stdGroup) {p : stdGroup} (hp : p ∈ PJ) :
    rootMap (g * p) = rootMap g := by
  rw [rootMap_eq_rootMap_iff]
  have e : (g * p)⁻¹ * g = p⁻¹ := by group
  rw [e]
  exact inv_mem hp

theorem isConj_rootInv_iff
    (x : stdGroup) : IsConj rootInv x ↔ ∃ g, rootMap g = x := isConj_iff

theorem lev_one :
    lev 1 = 2 := by
  rw [lev, wOf_one, level, wsmul_one]
  decide

theorem lev_eq_two_iff
    (g : stdGroup) : lev g = 2 ↔ g ∈ PJ := by
  constructor
  · intro h
    obtain ⟨p, hp, p', hp', e⟩ := exists_mul_mul_of_lev_eq (h.trans lev_one.symm)
    rw [e, mul_one]
    exact mul_mem hp hp'
  · intro hg
    have h := lev_mul_mul hg (one_mem PJ) 1
    rw [mul_one, mul_one] at h
    rw [h, lev_one]

theorem rootMap_eq_rootInv_iff
    (g : stdGroup) : rootMap g = rootInv ↔ lev g = 2 := by
  rw [← rootMap_one, rootMap_eq_rootMap_iff, mul_one, lev_eq_two_iff, inv_mem_iff]

@[expose] def levPoints
    (d : ℤ) : Set stdGroup := rootMap '' {g | lev g = d}

theorem rootMap_mem_levPoints
    (g : stdGroup) : rootMap g ∈ levPoints (lev g) := ⟨g, rfl, rfl⟩

theorem conjOrbit_PJ_rootMap
    (g : stdGroup) : conjOrbit PJ (rootMap g) = levPoints (lev g) := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p * g, ?_, by rw [rootMap_mul]⟩
    have h := lev_mul_mul hp (one_mem PJ) g
    rw [mul_one] at h
    exact h
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨p, hp, p', hp', rfl⟩ := exists_mul_mul_of_lev_eq hh
    exact ⟨p, hp, by rw [rootMap_mul_of_mem _ hp', rootMap_mul]⟩

theorem lev_apply_of_mem_betaGroup
    (b : betaGroup) (g : stdGroup) :
    lev ((b : MulAut stdGroup) g) = lev g := by
  rcases mem_betaGroup_iff.mp b.2 with h | h <;> rw [h]
  · rfl
  · exact lev_betaG g

theorem apply_rootMap_of_mem_betaGroup
    (b : betaGroup) (g : stdGroup) :
    (b : MulAut stdGroup) (rootMap g) = rootMap ((b : MulAut stdGroup) g) := by
  rw [rootMap, rootMap, map_mul, map_mul, map_inv, apply_rootInv_of_mem_betaGroup]

theorem conjOrbit_parStar_rootMap
    (g : stdGroup) :
    conjOrbit (parStar firstJ) (SemidirectProduct.inl (rootMap g)) =
      SemidirectProduct.inl '' levPoints (lev g) := by
  ext y
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rw [conj_inl, apply_rootMap_of_mem_betaGroup, ← rootMap_mul]
    refine ⟨_, ⟨_, ?_, rfl⟩, rfl⟩
    have hp : γ.left ∈ PJ := mem_parStar.mp hγ
    have h := lev_mul_mul hp (one_mem PJ) ((γ.right : MulAut stdGroup) g)
    rw [mul_one] at h
    rw [Set.mem_ofPred_eq, h, lev_apply_of_mem_betaGroup]
  · rintro ⟨x, hx, rfl⟩
    rw [← conjOrbit_PJ_rootMap] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨SemidirectProduct.inl p, hp, ?_⟩
    rw [conj_inl]
    rfl

theorem hpanel
    (i : Fin 4) (x : stdChamber) :
    (panel ncs stdDistance i x).encard = (E6Folded.letterWeight i : ℕ∞) + 1 := by
  rw [encard_panel_stdDistance]
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;> rfl

theorem finite_stdChamber :
    Finite stdChamber := inferInstance

theorem ncard_levChambers
    (d : ℤ) :
    {y : stdChamber | level (stdDistance c₀ y) = d}.ncard =
      ∑ᶠ w ∈ {w : NW | level w = d}, weylWeight ncs E6Folded.letterWeight w := by
  classical
  have : Fintype stdChamber := Fintype.ofFinite _
  have : Fintype NW := Fintype.ofFinite _
  have hset : {y : stdChamber | level (stdDistance c₀ y) = d} =
      ↑(Finset.univ.filter fun y => level (stdDistance c₀ y) = d) := by
    ext y
    simp
  rw [finsum_mem_eq_toFinset_sum, hset, Set.ncard_coe_finset,
    Finset.card_eq_sum_card_fiberwise (f := stdDistance c₀)
      (t := ({w : NW | level w = d} : Set NW).toFinset) (fun y hy => by simpa using hy)]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw' : level w = d := by simpa using hw
  rw [← (shell_finite_ncard hδ hpanel c₀ w).2, ← Set.ncard_coe_finset]
  congr 1
  ext y
  simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_ofPred_eq]
  exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hw', h⟩⟩

theorem card_levSet
    (d : ℤ) :
    Nat.card {g : stdGroup | lev g = d} = Nat.card stdBorelG *
      ∑ᶠ w ∈ {w : NW | level w = d}, weylWeight ncs E6Folded.letterWeight w := by
  rw [← ncard_levChambers, ← Nat.card_coe_set_eq]
  exact QuotientGroup.card_preimage_mk stdBorelG {y : stdChamber | level (stdDistance c₀ y) = d}

theorem card_PJ :
    Nat.card PJ = Nat.card stdBorelG * 93555 := by
  have hset : ((PJ : Subgroup stdGroup) : Set stdGroup) =
      QuotientGroup.mk ⁻¹' residue ncs stdDistance firstJ c₀ := by
    ext p
    rw [SetLike.mem_coe, Set.mem_preimage, mem_residue_mk_iff, inv_one, one_mul]
  have h93 : ∑ᶠ w ∈ (ncs.parabolic firstJ : Set NW), weylWeight ncs E6Folded.letterWeight w =
      93555 := finsum_parabolic_J_weylWeight
  rw [← h93, ← ncard_residue_eq_finsum hδ hpanel firstJ c₀,
    ← Nat.card_coe_set_eq (residue ncs stdDistance firstJ c₀),
    ← QuotientGroup.card_preimage_mk, ← hset]
  rfl

@[expose] def rootMapQ :
    stdGroup ⧸ PJ → stdGroup :=
  Quotient.lift rootMap fun a b hab =>
    (rootMap_eq_rootMap_iff a b).2 (QuotientGroup.leftRel_apply.mp hab)

theorem rootMapQ_mk
    (g : stdGroup) : rootMapQ (g : stdGroup ⧸ PJ) = rootMap g := rfl

theorem rootMapQ_injective :
    Function.Injective rootMapQ := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with | H a => ?_
  induction y using QuotientGroup.induction_on with | H b => ?_
  rw [rootMapQ_mk, rootMapQ_mk] at hxy
  exact QuotientGroup.eq.2 ((rootMap_eq_rootMap_iff a b).1 hxy)

theorem card_eq_card_PJ_mul
    {S : Set stdGroup} (hS : ∀ g ∈ S, ∀ p ∈ PJ, g * p ∈ S) :
    Nat.card S = Nat.card PJ * (rootMap '' S).ncard := by
  set T : Set (stdGroup ⧸ PJ) := (QuotientGroup.mk : stdGroup → stdGroup ⧸ PJ) '' S
  have hST : S = QuotientGroup.mk ⁻¹' T := by
    ext g
    constructor
    · intro hg
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g', hg', e⟩
      have h : g'⁻¹ * g ∈ PJ := QuotientGroup.eq.1 e
      have := hS g' hg' _ h
      rwa [mul_inv_cancel_left] at this
  have himg : rootMap '' S = rootMapQ '' T := by
    rw [Set.image_image]
    exact Set.image_congr fun g _ => (rootMapQ_mk g).symm
  rw [himg, Set.ncard_image_of_injective _ rootMapQ_injective, ← Nat.card_coe_set_eq T,
    ← QuotientGroup.card_preimage_mk, ← hST]

theorem card_levSet_eq
    (d : ℤ) :
    Nat.card {g : stdGroup | lev g = d} = Nat.card PJ * (levPoints d).ncard := by
  refine card_eq_card_PJ_mul fun g hg p hp => ?_
  have h := lev_mul_mul (one_mem PJ) hp g
  rw [one_mul] at h
  rw [Set.mem_ofPred_eq, h]
  exact hg

theorem card_stdBorelG_pos :
    0 < Nat.card stdBorelG := Nat.card_pos

theorem mul_ncard_levPoints
    (d : ℤ) :
    93555 * (levPoints d).ncard =
      ∑ᶠ w ∈ {w : NW | level w = d}, weylWeight ncs E6Folded.letterWeight w := by
  have h := (card_levSet d).symm.trans (card_levSet_eq d)
  rw [card_PJ, mul_assoc] at h
  exact (Nat.eq_of_mul_eq_mul_left card_stdBorelG_pos h).symm

theorem finsum_level_values :
    ∑ᶠ w ∈ {w : NW | level w = 2}, weylWeight ncs E6Folded.letterWeight w = 93555 * 1 ∧
    ∑ᶠ w ∈ {w : NW | level w = 1}, weylWeight ncs E6Folded.letterWeight w = 93555 * 1782 ∧
    ∑ᶠ w ∈ {w : NW | level w = 0}, weylWeight ncs E6Folded.letterWeight w = 93555 * 44352 ∧
    ∑ᶠ w ∈ {w : NW | level w = -1}, weylWeight ncs E6Folded.letterWeight w =
      93555 * 1824768 ∧
    ∑ᶠ w ∈ {w : NW | level w = -2}, weylWeight ncs E6Folded.letterWeight w =
      93555 * 2097152 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [finsum_level_weylWeight, E6Folded.finsum_level]
  · exact E6Folded.sum_levelPairs_two
  · exact E6Folded.sum_levelPairs_one
  · exact E6Folded.sum_levelPairs_zero
  · exact E6Folded.sum_levelPairs_neg_one
  · exact E6Folded.sum_levelPairs_neg_two

@[expose] def repSize : Fin 5 → ℕ := ![1, 1782, 44352, 1824768, 2097152]

@[expose] def repOrder : Fin 5 → ℕ := ![1, 2, 2, 4, 3]

theorem ncard_levPoints
    (i : Fin 5) : (levPoints (repLevel i)).ncard = repSize i := by
  have h := mul_ncard_levPoints (repLevel i)
  obtain ⟨h2, h1, h0, hm1, hm2⟩ := finsum_level_values
  refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 93555) (h.trans ?_)
  fin_cases i
  · exact h2
  · exact h1
  · exact h0
  · exact hm1
  · exact hm2

@[expose] def repPoint
    (i : Fin 5) : stdGroup := rootMap (stdRep (ncs.wordProd (repWord i)))

theorem lev_repPoint
    (i : Fin 5) : lev (stdRep (ncs.wordProd (repWord i))) = repLevel i := by
  rw [lev_stdRep, level_repWord]

theorem repPoint_mem_levPoints
    (i : Fin 5) : repPoint i ∈ levPoints (repLevel i) := by
  rw [← lev_repPoint]
  exact rootMap_mem_levPoints _

theorem coe_rootMap_stdRep
    (w : NW) :
    (rootMap (stdRep w) : ModGL Tag.E6 K) = pinnedX Tag.E6 K (toLat (wsmul w E6Folded.θ)) 1 :=
  canonicalRep_mul_pinnedX_mul_inv_of_two two_eq_zero_K (w : WeylGroup TwistTag.E6.tag)
    isRoot_e6HighestRoot (1 : K)

theorem coe_repPoint
    (i : Fin 5) :
    (repPoint i : ModGL Tag.E6 K) = pinnedX Tag.E6 K (repRootL i) 1 := by
  rw [repPoint, coe_rootMap_stdRep, wsmul_repWord]
  rfl

theorem orderOf_rootInv_mul
    (x : stdGroup) :
    orderOf (rootInv * x) = orderOf (rootInvM * (x : ModGL Tag.E6 K)) := by
  rw [← Subgroup.orderOf_coe (rootInv * x), Subgroup.coe_mul, coe_rootInv]

theorem repPoint_ne_rootInv
    {i : Fin 5} (hi : i ≠ 0) : repPoint i ≠ rootInv := by
  rw [repPoint, Ne, rootMap_eq_rootInv_iff, lev_repPoint]
  fin_cases i
  · exact absurd rfl hi
  all_goals decide

theorem orderOf_rootInv_mul_repPoint
    (i : Fin 5) : orderOf (rootInv * repPoint i) = repOrder i := by
  rw [orderOf_rootInv_mul, coe_repPoint]
  fin_cases i
  · rw [show (repRootL ((fun i => i) ⟨0, by decide⟩)) = theta from rfl, ← rootInvM,
      rootInvM_mul_self, orderOf_one]
    rfl
  · have hne := repPoint_ne_rootInv (i := 1) (by decide)
    have hne' : rootInvM ≠ pinnedX Tag.E6 K (repRootL 1) 1 := fun h =>
      hne (Subtype.ext ((coe_repPoint 1).trans h.symm))
    exact orderOf_mul_of_commute rootInvM_mul_self (pinnedX_mul_self _)
      (commute_rootInvM_of_pos (isRoot_repRootL 1) height_repRootL_one) hne'
  · have hne := repPoint_ne_rootInv (i := 2) (by decide)
    have hne' : rootInvM ≠ pinnedX Tag.E6 K (repRootL 2) 1 := fun h =>
      hne (Subtype.ext ((coe_repPoint 2).trans h.symm))
    exact orderOf_mul_of_commute rootInvM_mul_self (pinnedX_mul_self _)
      (commute_rootInvM_of_pos (isRoot_repRootL 2) height_repRootL_two) hne'
  · exact orderOf_rootInvM_mul_repRoot_three
  · exact orderOf_rootInvM_mul_repRoot_four

theorem orderOf_rootInv_mul_of_mem_levPoints
    {i : Fin 5} {x : stdGroup}
    (hx : x ∈ levPoints (repLevel i)) : orderOf (rootInv * x) = repOrder i := by
  rw [← lev_repPoint, ← conjOrbit_PJ_rootMap] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  have hpt : p * rootInv * p⁻¹ = rootInv := (mem_centralizer_rootInv_iff p).2 hp
  have e : rootInv * (p * rootMap (stdRep (ncs.wordProd (repWord i))) * p⁻¹) =
      MulAut.conj p (rootInv * repPoint i) := by
    rw [MulAut.conj_apply, repPoint]
    calc rootInv * (p * rootMap (stdRep (ncs.wordProd (repWord i))) * p⁻¹) =
        (p * rootInv * p⁻¹) * (p * rootMap (stdRep (ncs.wordProd (repWord i))) * p⁻¹) := by
          rw [hpt]
      _ = p * (rootInv * rootMap (stdRep (ncs.wordProd (repWord i)))) * p⁻¹ := by group
  rw [e, MulEquiv.orderOf_eq, orderOf_rootInv_mul_repPoint]

theorem exists_repLevel
    (g : stdGroup) : ∃ i : Fin 5, lev g = repLevel i := by
  rcases level_cases (wOf g) with h | h | h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩
  · exact ⟨3, h⟩
  · exact ⟨4, h⟩

theorem repLevel_injective : Function.Injective repLevel := by decide

end CFSG.Monster.B.E6.StdF4
