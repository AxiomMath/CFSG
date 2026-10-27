module

public import CFSG.LocalAnalysis.WeakClosure81.W183PglBridge
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.TwoSummands
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace

open Matrix CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81

variable {W : Type} [CommGroup W]

private def t1 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 1, 0; 0, 1, 0; 0, 0, 1],
    by decide, by decide⟩

private def t2 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], !![1, 0, 0; 0, 1, 1; 0, 0, 1],
    by decide, by decide⟩

private theorem t1_sq : t1 ^ 2 = 1 := by decide

private theorem t2_sq : t2 ^ 2 = 1 := by decide

private theorem t1_ne_one : t1 ≠ 1 := by decide

private def natFun (g : GL (Fin 3) (ZMod 2)) (v : W183PglVec) : W183PglVec :=
  Multiplicative.ofAdd (Matrix.mulVec (g : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (Multiplicative.toAdd v))

private def dualFun (g : GL (Fin 3) (ZMod 2)) (v : W183PglVec) : W183PglVec :=
  Multiplicative.ofAdd (Matrix.mulVec
    (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose)
    (Multiplicative.toAdd v))

private def dualInvFun (g : GL (Fin 3) (ZMod 2)) (v : W183PglVec) : W183PglVec :=
  Multiplicative.ofAdd (Matrix.mulVec
    (((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose)
    (Multiplicative.toAdd v))

private def adjFun (g : GL (Fin 3) (ZMod 2)) (X : W183PglAdj) : W183PglAdj :=
  ⟨Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) *
        ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))), by
    rw [w183Pgl_mem_adj]
    change Matrix.trace ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) *
        ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) = 0
    rw [Matrix.trace_units_conj]
    exact w183Pgl_mem_adj.mp X.2⟩

private def adjMatFun (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hA : A * A = 1)
    (X : W183PglAdj) : W183PglAdj :=
  ⟨Multiplicative.ofAdd (A *
      Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) * A), by
    rw [w183Pgl_mem_adj]
    change Matrix.trace (A *
      Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) * A) = 0
    rw [Matrix.trace_mul_cycle, hA, Matrix.one_mul]
    exact w183Pgl_mem_adj.mp X.2⟩

private def adjInvFun (g : GL (Fin 3) (ZMod 2)) (hg2 : g ^ 2 = 1) (X : W183PglAdj) :
    W183PglAdj :=
  adjMatFun (g : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (by rw [← Units.val_mul, ← pow_two, hg2, Units.val_one]) X

private instance decidableMemW183PglAdj :
    DecidablePred (fun X : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)) =>
      X ∈ W183PglAdj) :=
  fun X => decidable_of_iff (Matrix.trace (Multiplicative.toAdd X) = 0)
    (w183Pgl_mem_adj (X := X)).symm

private instance fintypeW183PglAdj : Fintype W183PglAdj :=
  Subtype.fintype (p := fun X : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)) =>
    X ∈ W183PglAdj)

private theorem dualFun_eq_dualInvFun (g : GL (Fin 3) (ZMod 2)) (hg2 : g ^ 2 = 1)
    (v : W183PglVec) : dualFun g v = dualInvFun g v := by
  have hg : g⁻¹ = g := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hg2)
  simp only [dualFun, dualInvFun, hg]

private theorem adjFun_eq_adjInvFun (g : GL (Fin 3) (ZMod 2)) (hg2 : g ^ 2 = 1)
    (X : W183PglAdj) : adjFun g X = adjInvFun g hg2 X := by
  have hg : g⁻¹ = g := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hg2)
  apply Subtype.ext
  simp only [adjFun, adjInvFun, adjMatFun, hg]

private theorem card_fix_nat_T :
    (Finset.univ.filter (fun v : W183PglVec => natFun t1 v = v ∧ natFun t2 v = v)).card = 2 := by
  decide +kernel

private theorem card_fix_dual_T :
    (Finset.univ.filter (fun v : W183PglVec => dualFun t1 v = v ∧ dualFun t2 v = v)).card = 2 := by
  have h1 : ∀ v, dualFun t1 v = dualInvFun t1 v := fun v => dualFun_eq_dualInvFun t1 t1_sq v
  have h2 : ∀ v, dualFun t2 v = dualInvFun t2 v := fun v => dualFun_eq_dualInvFun t2 t2_sq v
  simp only [h1, h2]
  decide +kernel

private theorem card_fix_adj_T :
    (Finset.univ.filter (fun X : W183PglAdj => adjFun t1 X = X ∧ adjFun t2 X = X)).card = 2 := by
  have h1 : ∀ X, adjFun t1 X = adjInvFun t1 t1_sq X :=
    fun X => adjFun_eq_adjInvFun t1 t1_sq X
  have h2 : ∀ X, adjFun t2 X = adjInvFun t2 t2_sq X :=
    fun X => adjFun_eq_adjInvFun t2 t2_sq X
  simp only [h1, h2]
  decide +kernel

private theorem card_fix_nat_mat :
    ∀ (A : Matrix (Fin 3) (Fin 3) (ZMod 2)), A * A = 1 → A ≠ 1 →
      (Finset.univ.filter (fun v : W183PglVec =>
        Multiplicative.ofAdd (Matrix.mulVec A (Multiplicative.toAdd v)) = v)).card = 4 := by
  decide +kernel

private theorem card_fix_dual_mat :
    ∀ (A : Matrix (Fin 3) (Fin 3) (ZMod 2)), A * A = 1 → A ≠ 1 →
      (Finset.univ.filter (fun v : W183PglVec =>
        Multiplicative.ofAdd (Matrix.mulVec A.transpose (Multiplicative.toAdd v)) = v)).card =
        4 := by
  decide +kernel

private theorem card_fix_adj_mat :
    ∀ (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hA : A * A = 1), A ≠ 1 →
      (Finset.univ.filter (fun X : W183PglAdj => adjMatFun A hA X = X)).card = 16 := by
  decide +kernel

private theorem card_fix_nat_a (g : GL (Fin 3) (ZMod 2)) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    (Finset.univ.filter (fun v : W183PglVec => natFun g v = v)).card = 4 :=
  card_fix_nat_mat (g : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (by rw [← Units.val_mul, ← pow_two, hg2, Units.val_one])
    (fun h => hg1 (Units.ext h))

private theorem card_fix_dual_a (g : GL (Fin 3) (ZMod 2)) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    (Finset.univ.filter (fun v : W183PglVec =>
      Multiplicative.ofAdd (Matrix.mulVec ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose)
        (Multiplicative.toAdd v)) = v)).card = 4 :=
  card_fix_dual_mat (g : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (by rw [← Units.val_mul, ← pow_two, hg2, Units.val_one])
    (fun h => hg1 (Units.ext h))

private theorem card_fix_adj_a (g : GL (Fin 3) (ZMod 2)) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    (Finset.univ.filter (fun X : W183PglAdj =>
      adjMatFun (g : Matrix (Fin 3) (Fin 3) (ZMod 2))
        (by rw [← Units.val_mul, ← pow_two, hg2, Units.val_one]) X = X)).card = 16 :=
  card_fix_adj_mat (g : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (by rw [← Units.val_mul, ← pow_two, hg2, Units.val_one])
    (fun h => hg1 (Units.ext h))

private theorem card_W183PglVec : Nat.card W183PglVec = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem card_W183PglAdj : Nat.card W183PglAdj = 256 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem natCard_fix_nat_T :
    Nat.card {v : W183PglVec // natFun t1 v = v ∧ natFun t2 v = v} = 2 := by
  rw [Nat.subtype_card (p := fun v : W183PglVec => natFun t1 v = v ∧ natFun t2 v = v)
    (Finset.univ.filter (fun v => natFun t1 v = v ∧ natFun t2 v = v)) (fun v => by simp)]
  exact card_fix_nat_T

private theorem natCard_fix_dual_T :
    Nat.card {v : W183PglVec // dualFun t1 v = v ∧ dualFun t2 v = v} = 2 := by
  rw [Nat.subtype_card (p := fun v : W183PglVec => dualFun t1 v = v ∧ dualFun t2 v = v)
    (Finset.univ.filter (fun v => dualFun t1 v = v ∧ dualFun t2 v = v)) (fun v => by simp)]
  exact card_fix_dual_T

private theorem natCard_fix_adj_T :
    Nat.card {X : W183PglAdj // adjFun t1 X = X ∧ adjFun t2 X = X} = 2 := by
  rw [Nat.subtype_card (p := fun X : W183PglAdj => adjFun t1 X = X ∧ adjFun t2 X = X)
    (Finset.univ.filter (fun X => adjFun t1 X = X ∧ adjFun t2 X = X)) (fun X => by simp)]
  exact card_fix_adj_T

private theorem natCard_fix_nat_a (g : GL (Fin 3) (ZMod 2)) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    Nat.card {v : W183PglVec // natFun g v = v} = 4 := by
  rw [Nat.subtype_card (p := fun v : W183PglVec => natFun g v = v)
    (Finset.univ.filter (fun v => natFun g v = v)) (fun v => by simp)]
  exact card_fix_nat_a g hg2 hg1

private theorem natCard_fix_dual_a (g : GL (Fin 3) (ZMod 2)) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    Nat.card {v : W183PglVec // dualInvFun g v = v} = 4 := by
  change Nat.card {v : W183PglVec //
    Multiplicative.ofAdd (Matrix.mulVec ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose)
      (Multiplicative.toAdd v)) = v} = 4
  rw [Nat.subtype_card (p := fun v : W183PglVec =>
      Multiplicative.ofAdd (Matrix.mulVec ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose)
        (Multiplicative.toAdd v)) = v)
    (Finset.univ.filter (fun v => Multiplicative.ofAdd
      (Matrix.mulVec ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose)
        (Multiplicative.toAdd v)) = v)) (fun v => by simp)]
  exact card_fix_dual_a g hg2 hg1

private theorem natCard_fix_adj_a (g : GL (Fin 3) (ZMod 2)) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    Nat.card {X : W183PglAdj // adjInvFun g hg2 X = X} = 16 := by
  change Nat.card {X : W183PglAdj // adjMatFun (g : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (by rw [← Units.val_mul, ← pow_two, hg2, Units.val_one]) X = X} = 16
  rw [Nat.subtype_card (p := fun X : W183PglAdj =>
      adjMatFun (g : Matrix (Fin 3) (Fin 3) (ZMod 2))
        (by rw [← Units.val_mul, ← pow_two, hg2, Units.val_one]) X = X)
    (Finset.univ.filter (fun X => adjMatFun (g : Matrix (Fin 3) (Fin 3) (ZMod 2))
      (by rw [← Units.val_mul, ← pow_two, hg2, Units.val_one]) X = X))
    (fun X => by simp)]
  exact card_fix_adj_a g hg2 hg1

private def irrAction {L : Subgroup (MulAut W)} (e : ↥L ≃* GL (Fin 3) (ZMod 2))
    {I : Subgroup W} (hLI : L ≤ stabSub I) : GL (Fin 3) (ZMod 2) →* MulAut I :=
  (resHom I).comp ((Subgroup.inclusion hLI).comp e.symm.toMonoidHom)

private theorem irrAction_apply {L : Subgroup (MulAut W)} (e : ↥L ≃* GL (Fin 3) (ZMod 2))
    {I : Subgroup W} (hLI : L ≤ stabSub I) (g : GL (Fin 3) (ZMod 2)) (x : ↥I) :
    ((irrAction e hLI g x : ↥I) : W) = (e.symm g : MulAut W) (x : W) := by
  rw [irrAction]
  exact resHom_apply I (Subgroup.inclusion hLI (e.symm g)) x

private theorem classify_irr [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hfix : fixV L = ⊥)
    (e : ↥L ≃* GL (Fin 3) (ZMod 2)) {I : Subgroup W} (hLI : L ≤ stabSub I)
    (hI : I ∈ irrSet L) :
    (∃ φ : ↥I ≃* W183PglVec, ∀ (g : GL (Fin 3) (ZMod 2)) (x : ↥I),
        Multiplicative.toAdd (φ (irrAction e hLI g x)) =
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (φ x)) ∨
      (∃ φ : ↥I ≃* W183PglVec, ∀ (g : GL (Fin 3) (ZMod 2)) (x : ↥I),
        Multiplicative.toAdd (φ (irrAction e hLI g x)) =
          ((w183PglTau g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
            Multiplicative.toAdd (φ x)) ∨
      (∃ φ : ↥I ≃* W183PglAdj, ∀ (g : GL (Fin 3) (ZMod 2)) (x : ↥I),
        Multiplicative.toAdd (φ (irrAction e hLI g x) :
            Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) =
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            Multiplicative.toAdd (φ x : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) *
              ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
  have hE : ∀ x : ↥I, x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hW (x : W))
  have hnt : ∃ (g : GL (Fin 3) (ZMod 2)) (x : ↥I), irrAction e hLI g x ≠ x := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hle : I ≤ fixV L := by
      intro x hx
      rw [mem_fixV]
      intro l hl
      have hcoe : ((irrAction e hLI (e ⟨l, hl⟩) ⟨x, hx⟩ : ↥I) : W) = l x := by
        rw [irrAction_apply, MulEquiv.symm_apply_apply]
      rw [h (e ⟨l, hl⟩) ⟨x, hx⟩] at hcoe
      exact hcoe.symm
    rw [hfix] at hle
    exact ne_bot_of_mem_irrSet hI (le_bot_iff.mp hle)
  have hirr : ∀ J : Subgroup ↥I,
      (∀ g, ∀ j ∈ J, irrAction e hLI g j ∈ J) → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    have hstab : StableUnder L (J.map I.subtype) := by
      intro l hl w hw
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hw
      refine Subgroup.mem_map.mpr ⟨irrAction e hLI (e ⟨l, hl⟩) j, hJ _ _ hj, ?_⟩
      change ((irrAction e hLI (e ⟨l, hl⟩) j : ↥I) : W) = l (j : W)
      rw [irrAction_apply, MulEquiv.symm_apply_apply]
    have hmax := hI.2.2.2.2 (J.map I.subtype) hstab (by rw [hfix, inf_bot_eq]; exact bot_le)
      (Subgroup.map_subtype_le J)
    rcases hmax with h | h
    · left
      rw [hfix, inf_bot_eq] at h
      have h' : J.map I.subtype = (⊥ : Subgroup ↥I).map I.subtype := by
        rw [h, Subgroup.map_bot]
      exact Subgroup.map_subtype_inj.mp h'
    · right
      rw [eq_top_iff]
      intro x _
      have hx : (x : W) ∈ J.map I.subtype := by rw [h]; exact x.2
      obtain ⟨j, hj, hje⟩ := Subgroup.mem_map.mp hx
      exact (Subtype.ext hje) ▸ hj
  exact w183Pgl_irreducible_classify hE (irrAction e hLI) hnt hirr

private def rho {L : Subgroup (MulAut W)} (e : ↥L ≃* GL (Fin 3) (ZMod 2)) :
    GL (Fin 3) (ZMod 2) →* MulAut W :=
  L.subtype.comp e.symm.toMonoidHom

private def Tsub {L : Subgroup (MulAut W)} (e : ↥L ≃* GL (Fin 3) (ZMod 2)) :
    Subgroup (MulAut W) :=
  (Subgroup.closure {t1, t2}).map (rho e)

private theorem Tsub_le {L : Subgroup (MulAut W)} (e : ↥L ≃* GL (Fin 3) (ZMod 2)) :
    Tsub e ≤ L := by
  rw [Tsub, Subgroup.map_le_iff_le_comap]
  intro g _
  exact (e.symm g).2

private theorem Tsub_eq_sup {L : Subgroup (MulAut W)} (e : ↥L ≃* GL (Fin 3) (ZMod 2)) :
    Tsub e = Subgroup.zpowers (rho e t1) ⊔ Subgroup.zpowers (rho e t2) := by
  rw [Tsub, MonoidHom.map_closure]
  have hset : (rho e) '' ({t1, t2} : Set (GL (Fin 3) (ZMod 2))) =
      {rho e t1, rho e t2} := by
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, (rfl | rfl), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨t1, Or.inl rfl, rfl⟩
      · exact ⟨t2, Or.inr rfl, rfl⟩
  have hset2 : ({rho e t1, rho e t2} : Set (MulAut W)) =
      {rho e t1} ∪ {rho e t2} := rfl
  rw [hset, hset2, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure]

private theorem mem_fixV_Tsub {L : Subgroup (MulAut W)} (e : ↥L ≃* GL (Fin 3) (ZMod 2))
    {u : W} : u ∈ fixV (Tsub e) ↔ (rho e t1) u = u ∧ (rho e t2) u = u := by
  rw [Tsub_eq_sup, FixVLat.fixV_sup_eq, Subgroup.mem_inf, mem_fixV_zpowers_iff_apply,
    mem_fixV_zpowers_iff_apply]

private theorem card_inf_fixV_Tsub_eq_model {L : Subgroup (MulAut W)}
    (e : ↥L ≃* GL (Fin 3) (ZMod 2)) {I : Subgroup W} (hLI : L ≤ stabSub I)
    {M : Type} [CommGroup M] (ψ : ↥I ≃* M) (τ1 τ2 : M → M)
    (hψ1 : ∀ x : ↥I, ψ (irrAction e hLI t1 x) = τ1 (ψ x))
    (hψ2 : ∀ x : ↥I, ψ (irrAction e hLI t2 x) = τ2 (ψ x)) :
    Nat.card ↥(I ⊓ fixV (Tsub e)) = Nat.card {m : M // τ1 m = m ∧ τ2 m = m} := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨ψ ⟨x.1, x.2.1⟩, ?_⟩
      invFun := fun m => ⟨(ψ.symm m.1).1, ⟨(ψ.symm m.1).2, ?_⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hx := (mem_fixV_Tsub e).mp x.2.2
    have h1 : irrAction e hLI t1 ⟨x.1, x.2.1⟩ = ⟨x.1, x.2.1⟩ := by
      apply Subtype.ext
      rw [irrAction_apply]
      exact hx.1
    have h2 : irrAction e hLI t2 ⟨x.1, x.2.1⟩ = ⟨x.1, x.2.1⟩ := by
      apply Subtype.ext
      rw [irrAction_apply]
      exact hx.2
    exact ⟨by rw [← hψ1, h1], by rw [← hψ2, h2]⟩
  · change (ψ.symm m.1).1 ∈ fixV (Tsub e)
    rw [mem_fixV_Tsub]
    constructor
    · have hy : irrAction e hLI t1 (ψ.symm m.1) = ψ.symm m.1 := by
        apply ψ.injective
        rw [hψ1, MulEquiv.apply_symm_apply, m.2.1]
      have h := irrAction_apply e hLI t1 (ψ.symm m.1)
      rw [hy] at h
      simpa [rho] using h.symm
    · have hy : irrAction e hLI t2 (ψ.symm m.1) = ψ.symm m.1 := by
        apply ψ.injective
        rw [hψ2, MulEquiv.apply_symm_apply, m.2.2]
      have h := irrAction_apply e hLI t2 (ψ.symm m.1)
      rw [hy] at h
      simpa [rho] using h.symm
  · intro x
    apply Subtype.ext
    simp
  · intro m
    apply Subtype.ext
    simp

private theorem card_inf_fixV_zpowers_eq_model {L : Subgroup (MulAut W)}
    (e : ↥L ≃* GL (Fin 3) (ZMod 2)) {I : Subgroup W} (hLI : L ≤ stabSub I)
    {M : Type} [CommGroup M] (ψ : ↥I ≃* M) (τ : M → M) (a : ↥L)
    (hψ : ∀ x : ↥I, ψ (irrAction e hLI (e a) x) = τ (ψ x)) :
    Nat.card ↥(I ⊓ fixV (Subgroup.zpowers (a : MulAut W))) =
      Nat.card {m : M // τ m = m} := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨ψ ⟨x.1, x.2.1⟩, ?_⟩
      invFun := fun m => ⟨(ψ.symm m.1).1, ⟨(ψ.symm m.1).2, ?_⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hx : (a : MulAut W) x.1 = x.1 :=
      mem_fixV_zpowers_iff_apply.mp x.2.2
    have h1 : irrAction e hLI (e a) ⟨x.1, x.2.1⟩ = ⟨x.1, x.2.1⟩ := by
      apply Subtype.ext
      rw [irrAction_apply]
      simpa using hx
    rw [← hψ, h1]
  · change (ψ.symm m.1).1 ∈ fixV (Subgroup.zpowers (a : MulAut W))
    rw [mem_fixV_zpowers_iff_apply]
    have hy : irrAction e hLI (e a) (ψ.symm m.1) = ψ.symm m.1 := by
      apply ψ.injective
      rw [hψ, MulEquiv.apply_symm_apply, m.2]
    have h := irrAction_apply e hLI (e a) (ψ.symm m.1)
    rw [hy] at h
    simpa using h.symm
  · intro x
    apply Subtype.ext
    simp
  · intro m
    apply Subtype.ext
    simp

private theorem padicValNat_two_three : padicValNat 2 8 = 3 := by
  have h : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h, padicValNat.prime_pow]

private theorem padicValNat_two_two : padicValNat 2 4 = 2 := by
  have h : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h, padicValNat.prime_pow]

private theorem padicValNat_two_eight : padicValNat 2 256 = 8 := by
  have h : (256 : ℕ) = 2 ^ 8 := by norm_num
  rw [h, padicValNat.prime_pow]

private theorem padicValNat_two_four : padicValNat 2 16 = 4 := by
  have h : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h, padicValNat.prime_pow]

theorem exists_mem_orderOf_eq_two {L : Subgroup (MulAut W)} (hL3 : IsL3 ↥L 1) :
    ∃ a ∈ L, orderOf a = 2 := by
  obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL3
  refine ⟨((e.symm t1 : ↥L) : MulAut W), (e.symm t1).2, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq e.symm]
  exact orderOf_eq_prime t1_sq t1_ne_one

theorem exists_le_forall_card_inf_fixV_eq_two [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hL3 : IsL3 ↥L 1) (hfix : fixV L = ⊥) :
    ∃ T ≤ L, ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2 := by
  obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL3
  refine ⟨Tsub e, Tsub_le e, ?_⟩
  intro I hI
  have hLI : L ≤ stabSub I := Thm14_5.le_stabSub_of_stableUnder (stableUnder_of_mem_irrSet hI)
  rcases classify_irr hW hfix e hLI hI with ⟨φ, hφ⟩ | ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · rw [card_inf_fixV_Tsub_eq_model e hLI φ (natFun t1) (natFun t2) ?_ ?_,
      natCard_fix_nat_T]
    · intro x
      exact Multiplicative.toAdd.injective (by rw [hφ t1 x]; rfl)
    · intro x
      exact Multiplicative.toAdd.injective (by rw [hφ t2 x]; rfl)
  · rw [card_inf_fixV_Tsub_eq_model e hLI φ (dualFun t1) (dualFun t2) ?_ ?_,
      natCard_fix_dual_T]
    · intro x
      apply Multiplicative.toAdd.injective
      rw [hφ t1 x, dualFun, Matrix.GeneralLinearGroup.coe_inverseTranspose]
      rfl
    · intro x
      apply Multiplicative.toAdd.injective
      rw [hφ t2 x, dualFun, Matrix.GeneralLinearGroup.coe_inverseTranspose]
      rfl
  · rw [card_inf_fixV_Tsub_eq_model e hLI φ (adjFun t1) (adjFun t2) ?_ ?_,
      natCard_fix_adj_T]
    · intro x
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      rw [hφ t1 x]
      rfl
    · intro x
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      rw [hφ t2 x]
      rfl

theorem rk_inf_fixV_zpowers_of_mem_irrSet [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hL3 : IsL3 ↥L 1) (hfix : fixV L = ⊥) {I : Subgroup W}
    (hI : I ∈ irrSet L) {a : MulAut W} (ha : a ∈ L) (ha2 : orderOf a = 2) :
    rk ↥I = 3 ∧ rk ↥(I ⊓ fixV (Subgroup.zpowers a)) = 2 ∨
      rk ↥I = 8 ∧ rk ↥(I ⊓ fixV (Subgroup.zpowers a)) = 4 := by
  obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL3
  have hLI : L ≤ stabSub I := Thm14_5.le_stabSub_of_stableUnder (stableUnder_of_mem_irrSet hI)
  have hclass := classify_irr hW hfix e hLI hI
  let aL : ↥L := ⟨a, ha⟩
  have ha2' : a ^ 2 = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha2] at h
  have haL2 : aL ^ 2 = 1 := Subtype.ext (by simpa using ha2')
  have hg2 : (e aL) ^ 2 = 1 := by rw [← map_pow, haL2, map_one]
  have hg1 : e aL ≠ 1 := by
    intro h
    have h1 : aL = 1 := e.injective (by rw [h, map_one])
    have h2 : a = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at ha2
    omega
  rcases hclass with ⟨φ, hφ⟩ | ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · left
    have hIcard : Nat.card ↥I = 8 := by
      rw [Nat.card_congr φ.toEquiv, card_W183PglVec]
    have hFixCard : Nat.card ↥(I ⊓ fixV (Subgroup.zpowers a)) = 4 := by
      rw [card_inf_fixV_zpowers_eq_model e hLI φ (natFun (e aL)) aL ?_,
        natCard_fix_nat_a (e aL) hg2 hg1]
      intro x
      exact Multiplicative.toAdd.injective (by rw [hφ (e aL) x]; rfl)
    constructor
    · unfold rk; rw [hIcard]; exact padicValNat_two_three
    · unfold rk; rw [hFixCard]; exact padicValNat_two_two
  · left
    have hIcard : Nat.card ↥I = 8 := by
      rw [Nat.card_congr φ.toEquiv, card_W183PglVec]
    have hFixCard : Nat.card ↥(I ⊓ fixV (Subgroup.zpowers a)) = 4 := by
      rw [card_inf_fixV_zpowers_eq_model e hLI φ (dualInvFun (e aL)) aL ?_,
        natCard_fix_dual_a (e aL) hg2 hg1]
      intro x
      apply Multiplicative.toAdd.injective
      rw [hφ (e aL) x, dualInvFun, Matrix.GeneralLinearGroup.coe_inverseTranspose,
        inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hg2)]
      rfl
    constructor
    · unfold rk; rw [hIcard]; exact padicValNat_two_three
    · unfold rk; rw [hFixCard]; exact padicValNat_two_two
  · right
    have hIcard : Nat.card ↥I = 256 := by
      rw [Nat.card_congr φ.toEquiv, card_W183PglAdj]
    have hFixCard : Nat.card ↥(I ⊓ fixV (Subgroup.zpowers a)) = 16 := by
      rw [card_inf_fixV_zpowers_eq_model e hLI φ (adjInvFun (e aL) hg2) aL ?_,
        natCard_fix_adj_a (e aL) hg2 hg1]
      intro x
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      rw [hφ (e aL) x, ← adjFun_eq_adjInvFun (e aL) hg2 (φ x)]
      rfl
    constructor
    · unfold rk; rw [hIcard]; exact padicValNat_two_eight
    · unfold rk; rw [hFixCard]; exact padicValNat_two_four

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace
