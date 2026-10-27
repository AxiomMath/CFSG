module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreTorus
public import TauCeti.LinearAlgebra.Matrix.Commute

public section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType.TwE6CorootCore

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction
  CFSG.SeitzReduction.TwistedE6Pilot CFSG.StandardType.TableBExcTwo
  CFSG.StandardType.TableBExcTwoFusion CFSG.RankThree.Classical

local instance twE6CorootCoreDiagNeZero : NeZero Tag.E6.rank := ⟨by decide⟩

theorem conj_commute_of_intertwine {G : Type*} [Group G] {g s e y : G} (he : g * e = y * g)
    (hs : s * y = y * s) : g⁻¹ * s * g * e = e * (g⁻¹ * s * g) := by
  have he' : e = g⁻¹ * y * g := by rw [mul_assoc, ← he, inv_mul_cancel_left]
  rw [he']
  calc g⁻¹ * s * g * (g⁻¹ * y * g) = g⁻¹ * (s * y) * g := by group
    _ = g⁻¹ * (y * s) * g := by rw [hs]
    _ = g⁻¹ * y * g * (g⁻¹ * s * g) := by group

theorem eq_one_of_conjSL_diagUnitOne {K : Type} [Field K] {χ : Kˣ} (P : SL2 K)
    (hu : conjSL (diagUnitOne χ) (P⁻¹ * uSL 1 * P) = P⁻¹ * uSL 1 * P)
    (hv : conjSL (diagUnitOne χ) (P⁻¹ * vSL 1 * P) = P⁻¹ * vSL 1 * P) : χ = 1 := by
  by_contra hχ
  have hX : ((diagUnitOne χ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ∉
      Set.range (Matrix.scalar (Fin 2)) := by
    rintro ⟨c, hc⟩
    rw [coe_diagUnitOne] at hc
    have h0 := congrFun (congrFun hc 0) 0
    have h1 := congrFun (congrFun hc 1) 1
    simp [Matrix.scalar_apply] at h0 h1
    exact hχ (Units.val_eq_one.1 (h0.symm.trans h1))
  have key : ∀ {M : SL2 K}, conjSL (diagUnitOne χ) M = M →
      Commute ((diagUnitOne χ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        (M : Matrix (Fin 2) (Fin 2) K) := fun hM =>
    (Units.mul_inv_eq_iff_eq_mul _).1 (by rw [← coe_conjSL, hM])
  have h := TauCeti.commute_of_commute_fin_two hX (key hu) (key hv)
  have e : P⁻¹ * uSL 1 * P * (P⁻¹ * vSL 1 * P) = P⁻¹ * vSL 1 * P * (P⁻¹ * uSL 1 * P) := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact h.eq
  refine CFSG.RankThree.Chevalley.uSL_mul_vSL_ne (K := K) ?_
  calc uSL 1 * vSL 1 = P * (P⁻¹ * uSL 1 * P * (P⁻¹ * vSL 1 * P)) * P⁻¹ := by group
    _ = P * (P⁻¹ * vSL 1 * P * (P⁻¹ * uSL 1 * P)) * P⁻¹ := by rw [e]
    _ = vSL 1 * uSL 1 := by group


variable {K : Type} [Field K]

theorem rootChar_eq_one_of_commute {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    {a : Fin Tag.E6.rank → Kˣ} (P : SL2 K)
    (hu : rootDiagUnit .E6 a * rootSL2 .E6 K β (P⁻¹ * uSL 1 * P) =
      rootSL2 .E6 K β (P⁻¹ * uSL 1 * P) * rootDiagUnit .E6 a)
    (hv : rootDiagUnit .E6 a * rootSL2 .E6 K β (P⁻¹ * vSL 1 * P) =
      rootSL2 .E6 K β (P⁻¹ * vSL 1 * P) * rootDiagUnit .E6 a) :
    rootChar a β = 1 := by
  have key : ∀ {M : SL2 K}, rootDiagUnit .E6 a * rootSL2 .E6 K β M =
      rootSL2 .E6 K β M * rootDiagUnit .E6 a → conjSL (diagUnitOne (rootChar a β)) M = M :=
    fun h => CFSG.RankThree.Chevalley.rootSL2_injective_of_field β (by
      rw [← CFSG.RankThree.Chevalley.rootDiagUnit_conj_rootSL2 a hβ, h, mul_inv_cancel_right])
  exact eq_one_of_conjSL_diagUnitOne P (key hu) (key hv)

theorem frameProd_conj_rootDiagUnit {a : Fin Tag.E6.rank → Kˣ}
    (ha : ∀ i : Fin 4, i ≠ 0 → rootChar a (corootFrameRoot i) = 1) (P : SL2 K) :
    (frameProd K corootFrame P : ModGL .E6 K) * rootDiagUnit .E6 a *
        (frameProd K corootFrame P : ModGL .E6 K)⁻¹ =
      rootSL2 .E6 K (corootFrameRoot 0) P * rootDiagUnit .E6 a *
        (rootSL2 .E6 K (corootFrameRoot 0) P)⁻¹ := by
  have hg : (frameProd K corootFrame P : ModGL .E6 K) = rootSL2 .E6 K (corootFrameRoot 0) P *
      (List.ofFn fun i : Fin 3 => rootSL2 .E6 K (corootFrameRoot i.succ) P).prod := by
    rw [coe_frameProd, List.ofFn_succ, List.prod_cons]
    rfl
  have hr : Commute (List.ofFn fun i : Fin 3 => rootSL2 .E6 K (corootFrameRoot i.succ) P).prod
      (rootDiagUnit .E6 a) :=
    Commute.list_prod_left _ _ fun z hz => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
      exact commute_rootSL2_rootDiagUnit (corootFrame.isRoot i.succ) (ha _ (Fin.succ_ne_zero i)) P
  rw [hg, mul_inv_rev, mul_assoc (rootSL2 .E6 K (corootFrameRoot 0) P), hr.eq]
  group

theorem eq_one_of_commute_pinnedX_mul {a : Fin Tag.E6.rank → Kˣ} {j j' : Fin Tag.E6.rank}
    (hne : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single j' 1)
    (hc : ∀ u v : K, pinnedX .E6 K (Pi.single j 1) u * pinnedX .E6 K (Pi.single j' 1) v =
      pinnedX .E6 K (Pi.single j' 1) v * pinnedX .E6 K (Pi.single j 1) u)
    (h : rootDiagUnit .E6 a * (pinnedX .E6 K (Pi.single j 1) 1 *
        pinnedX .E6 K (Pi.single j' 1) 1) =
      pinnedX .E6 K (Pi.single j 1) 1 * pinnedX .E6 K (Pi.single j' 1) 1 * rootDiagUnit .E6 a) :
    a j = 1 ∧ a j' = 1 := by
  have hpos : ∀ i : Fin Tag.E6.rank, IsRoot .E6 (Pi.single i 1) ∧
      0 < height (Pi.single i 1 : Fin Tag.E6.rank → ℤ) :=
    fun i => ⟨isRoot_single _ i, by rw [height_single]; norm_num⟩
  have e : pinnedX .E6 K (Pi.single j 1) ((rootChar a (Pi.single j 1) : K) * 1) *
      pinnedX .E6 K (Pi.single j' 1) ((rootChar a (Pi.single j' 1) : K) * 1) =
      pinnedX .E6 K (Pi.single j 1) 1 * pinnedX .E6 K (Pi.single j' 1) 1 := by
    rw [← rootDiagUnit_conj_pinnedX a (hpos j).1, ← rootDiagUnit_conj_pinnedX a (hpos j').1]
    calc _ = rootDiagUnit .E6 a * (pinnedX .E6 K (Pi.single j 1) 1 *
          pinnedX .E6 K (Pi.single j' 1) 1) * (rootDiagUnit .E6 a)⁻¹ := by group
      _ = _ := by rw [h, mul_inv_cancel_right]
  rw [EPilot.rootChar_single_eq, EPilot.rootChar_single_eq, mul_one, mul_one] at e
  rcases pinnedX_mul_eq_pinnedX_mul (hpos j).1 (hpos j').1 (hpos j) (hpos j') hne hne hc hc
    (Units.ne_zero _) (Units.ne_zero _) one_ne_zero e with ⟨-, -, h1, h2⟩ | ⟨h1, -⟩
  · exact ⟨Units.val_eq_one.1 h1, Units.val_eq_one.1 h2⟩
  · exact absurd h1 hne

theorem exists_inv_conj_eq_rootDiagUnit [CharP K 2] {x l : Kˣ} (hx : x ≠ 1) (hl : l ≠ 1)
    {g s c : ModGL .E6 K} (hg : g ∈ adjointGroup .E6 K) (hc : c ∈ adjointGroup .E6 K)
    (b : Fin Tag.E6.rank → Kˣ) (hs : s = c * rootDiagUnit .E6 b)
    (hy : ∀ e ∈ frameTori x l, ∃ y : ModGL .E6 K, g * rootDiagUnit .E6 e = y * g ∧ s * y = y * s) :
    ∃ a, g⁻¹ * s * g = rootDiagUnit .E6 a := by
  have h0 : g⁻¹ * s * g * (rootDiagUnit .E6 b)⁻¹ ∈ adjointGroup .E6 K := by
    have e : g⁻¹ * s * g * (rootDiagUnit .E6 b)⁻¹ =
        g⁻¹ * c * (rootDiagUnit .E6 b * g * (rootDiagUnit .E6 b)⁻¹) := by
      rw [hs]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hg) hc) (conj_rootDiagUnit_mem_adjointGroup b hg)
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (mem_torusGroup_of_commute_frameTori hx hl h0 fun e he => by
      obtain ⟨y, hgy, hsy⟩ := hy e he
      have hb : Commute (rootDiagUnit .E6 b)⁻¹ (rootDiagUnit .E6 e) := Commute.inv_left (by
        show _ * _ = _ * _
        rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm])
      exact (Commute.mul_left (conj_commute_of_intertwine hgy hsy) hb).eq)
  exact ⟨a * b, by rw [rootDiagUnit_mul, ← ha, inv_mul_cancel_right]⟩

end CFSG.StandardType.TwE6CorootCore

end
