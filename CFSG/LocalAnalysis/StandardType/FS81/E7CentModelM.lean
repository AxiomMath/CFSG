module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentPieces
public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogO2
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2OverlapCent

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.QuasithinUnique
open scoped commutatorElement

local instance e7CentModelMNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

private abbrev E7G : Type := ↥(adjointGroup .E7 (ZMod 2))

section



private theorem subgroupOf_le_subgroupOf {G S T : Subgroup (ModGL .E7 (ZMod 2))}
    (h : S ≤ T) : S.subgroupOf G ≤ T.subgroupOf G :=
  fun x hx => Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx))

private theorem subgroupOf_le_normalizer_subgroupOf {G S T : Subgroup (ModGL .E7 (ZMod 2))}
    (h : S ≤ Subgroup.normalizer (T : Set (ModGL .E7 (ZMod 2)))) :
    S.subgroupOf G ≤ Subgroup.normalizer (T.subgroupOf G : Set ↥G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact Subgroup.mem_subgroupOf.2
      ((Subgroup.mem_normalizer_iff.1 (h (Subgroup.mem_subgroupOf.1 hx)) y.val).1
        (Subgroup.mem_subgroupOf.1 hy))
  · intro hy
    exact Subgroup.mem_subgroupOf.2
      ((Subgroup.mem_normalizer_iff.1 (h (Subgroup.mem_subgroupOf.1 hx)) y.val).2
        (Subgroup.mem_subgroupOf.1 hy))

private theorem le_normalizer_inf {G : Type} [Group G] {A H K : Subgroup G}
    (hH : A ≤ Subgroup.normalizer (H : Set G)) (hK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hH ha) x).1 hx.1,
      (Subgroup.mem_normalizer_iff.1 (hK ha) x).1 hx.2⟩
  · intro hx
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hH ha) x).2 hx.1,
      (Subgroup.mem_normalizer_iff.1 (hK ha) x).2 hx.2⟩

private theorem exists_mul_of_le_normalizer {G : Type} [Group G] {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have key : ∀ y ∈ Subgroup.closure ((A : Set G) ∪ B), ∃ a ∈ A, ∃ b ∈ B, a * b = y := by
    intro y hy
    refine Subgroup.closure_induction (p := fun y _ => ∃ a ∈ A, ∃ b ∈ B, a * b = y)
      ?_ ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1)⟩ ?_ ?_ hy
    · rintro y (hy | hy)
      · exact ⟨y, hy, 1, B.one_mem, (mul_one y)⟩
      · exact ⟨1, A.one_mem, y, hy, (one_mul y)⟩
    · rintro y z - - ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
      have hb₁a₂ : b₁ * a₂ * b₁⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.1 (h hb₁) a₂).1 ha₂
      refine ⟨a₁ * (b₁ * a₂ * b₁⁻¹), A.mul_mem ha₁ hb₁a₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
      group
    · rintro y - ⟨a, ha, b, hb, rfl⟩
      have hba : b⁻¹ * a⁻¹ * b ∈ A := by
        simpa using (Subgroup.mem_normalizer_iff.1 (h (B.inv_mem hb)) a⁻¹).1 (A.inv_mem ha)
      exact ⟨b⁻¹ * a⁻¹ * b, hba, b⁻¹, B.inv_mem hb, by group⟩
  rw [Subgroup.sup_eq_closure] at hx
  exact key x hx

private theorem eq_and_eq_of_mul_eq_mul_of_inf_eq_bot {G : Type} [Group G] {H K : Subgroup G}
    (hbot : H ⊓ K = ⊥) {a₁ a₂ : G} (ha₁ : a₁ ∈ H) (ha₂ : a₂ ∈ H) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ K) (hb₂ : b₂ ∈ K) (heq : a₁ * b₁ = a₂ * b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have h1 : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
    calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ := by group
      _ = a₂⁻¹ * (a₂ * b₂) * b₁⁻¹ := by rw [heq]
      _ = b₂ * b₁⁻¹ := by group
  have hmem : a₂⁻¹ * a₁ ∈ H ⊓ K :=
    ⟨H.mul_mem (H.inv_mem ha₂) ha₁, h1 ▸ K.mul_mem hb₂ (K.inv_mem hb₁)⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  refine ⟨?_, ?_⟩
  · calc a₁ = a₂ * (a₂⁻¹ * a₁) := by group
      _ = a₂ := by rw [hmem]; group
  · have h2 : b₂ * b₁⁻¹ = 1 := by rw [← h1]; exact hmem
    have h3 : b₂ = b₁ := by
      calc b₂ = (b₂ * b₁⁻¹) * b₁ := by group
        _ = 1 * b₁ := by rw [h2]
        _ = b₁ := by group
    exact h3.symm

private theorem e7A1_le_rootPerpLevi_d6 :
    e7A1 ≤ rootPerpLevi .E7 (ZMod 2) d6HighRoot := by
  have hα7 : e7Alpha7 ∈ rootPerp .E7 d6HighRoot :=
    ⟨isRoot_single .E7 6, by rw [iform_single_six]; decide⟩
  have hnα7 : -e7Alpha7 ∈ rootPerp .E7 d6HighRoot := by
    refine ⟨IsRoot.neg hα7.1, ?_⟩
    rw [← neg_one_smul ℤ e7Alpha7, iform_smul_left, hα7.2, mul_zero]
  have hpair : rootSubgroup .E7 (ZMod 2) e7Alpha7 ⊔
      rootSubgroup .E7 (ZMod 2) (-e7Alpha7) ≤ rootSpan .E7 (ZMod 2) (rootPerp .E7 d6HighRoot) :=
    sup_le (le_iSup₂_of_le (f := fun δ (_ : δ ∈ rootPerp .E7 d6HighRoot) =>
        rootSubgroup .E7 (ZMod 2) δ) e7Alpha7 hα7 le_rfl)
      (le_iSup₂_of_le (f := fun δ (_ : δ ∈ rootPerp .E7 d6HighRoot) =>
        rootSubgroup .E7 (ZMod 2) δ) (-e7Alpha7) hnα7 le_rfl)
  exact subgroupOf_le_subgroupOf hpair

private theorem e7A1_le_perpLevi : e7A1 ≤ perpLevi .E7 (ZMod 2) := by
  have hα7 : e7Alpha7 ∈ perpRoots .E7 :=
    single_mem_perpRoots (by decide)
  have hnα7 : -e7Alpha7 ∈ perpRoots .E7 := neg_mem_perpRoots hα7
  have hpair : rootSubgroup .E7 (ZMod 2) e7Alpha7 ⊔
      rootSubgroup .E7 (ZMod 2) (-e7Alpha7) ≤ rootSpan .E7 (ZMod 2) (perpRoots .E7) :=
    sup_le (le_iSup₂_of_le (f := fun δ (_ : δ ∈ perpRoots .E7) =>
        rootSubgroup .E7 (ZMod 2) δ) e7Alpha7 hα7 le_rfl)
      (le_iSup₂_of_le (f := fun δ (_ : δ ∈ perpRoots .E7) =>
        rootSubgroup .E7 (ZMod 2) δ) (-e7Alpha7) hnα7 le_rfl)
  exact subgroupOf_le_subgroupOf hpair

private theorem e7A1_le_normalizer_e7CentS (hSR : E7CentSRoots) :
    e7A1 ≤ Subgroup.normalizer (e7CentS : Set E7G) := by
  have hA1norm : e7A1 ≤ Subgroup.normalizer
      (((rootSpan .E7 (ZMod 2) (radicalRoots .E7 d6HighRoot)).subgroupOf
        (adjointGroup .E7 (ZMod 2))) : Set E7G) :=
    e7A1_le_rootPerpLevi_d6.trans (subgroupOf_le_normalizer_subgroupOf
      (rootSpan_rootPerp_le_normalizer_radicalRoots (K := ZMod 2)
        (Or.inr (Or.inl rfl)) isRoot_d6HighRoot))
  rw [hSR]
  exact le_normalizer_inf hA1norm (e7A1_le_perpLevi.trans Subgroup.le_normalizer)

private theorem e7D4_le_perpLevi : e7D4 ≤ perpLevi .E7 (ZMod 2) := by
  have hD4sub : overlapRootsD4 .high .seven ⊆ perpRoots .E7 := by
    rintro α ⟨⟨⟨hα, h0⟩, -⟩, -⟩
    exact (mem_perpRoots_iff_iform (Or.inr (Or.inl rfl))).2 ⟨hα, h0⟩
  intro x hx
  exact Subgroup.mem_subgroupOf.2 (rootSpan_mono hD4sub (Subgroup.mem_subgroupOf.1 hx))

private theorem e7D4_centralizes_sigma : ∀ j ∈ e7D4, j * e7CentSigma = e7CentSigma * j := by
  intro j hj
  have hroot := rootSpan_le_centralizer_rootPair_E7 (K := ZMod 2)
    (S := overlapRootsD4 .high .seven) (β := d6HighRoot) isRoot_d6HighRoot
    (fun α hα => ⟨hα.1.1.1, by rw [iform_comm]; exact hα.2.2⟩)
  have hj' := hroot (Subgroup.mem_subgroupOf.1 hj)
  have hσ : (e7CentSigma : ModGL .E7 (ZMod 2)) ∈
      rootSubgroup .E7 (ZMod 2) d6HighRoot ⊔ rootSubgroup .E7 (ZMod 2) (-d6HighRoot) :=
    Subgroup.mem_sup_left (mem_rootSubgroup.2 ⟨1, rfl⟩)
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hj' _ hσ).symm

private theorem e7D4_le_normalizer_e7CentS (hSR : E7CentSRoots) :
    e7D4 ≤ Subgroup.normalizer (e7CentS : Set E7G) := by
  have hD4sub : overlapRootsD4 .high .seven ⊆ perpRoots .E7 := by
    rintro α ⟨⟨⟨hα, h0⟩, -⟩, -⟩
    exact (mem_perpRoots_iff_iform (Or.inr (Or.inl rfl))).2 ⟨hα, h0⟩
  have hD4perp : overlapRootsD4 .high .seven ⊆ rootPerp .E7 d6HighRoot := by
    rintro α ⟨⟨-, -⟩, hC⟩
    exact ⟨hC.1, by rw [iform_comm]; exact hC.2⟩
  have hD4norm : e7D4 ≤ Subgroup.normalizer
      (((rootSpan .E7 (ZMod 2) (radicalRoots .E7 d6HighRoot)).subgroupOf
        (adjointGroup .E7 (ZMod 2))) : Set E7G) :=
    (subgroupOf_le_subgroupOf (rootSpan_mono hD4perp)).trans
      (subgroupOf_le_normalizer_subgroupOf
        (rootSpan_rootPerp_le_normalizer_radicalRoots (K := ZMod 2)
          (Or.inr (Or.inl rfl)) isRoot_d6HighRoot))
  rw [hSR]
  refine le_normalizer_inf hD4norm fun x hx => ?_
  exact Subgroup.le_normalizer (Subgroup.mem_subgroupOf.2
      (rootSpan_mono hD4sub (Subgroup.mem_subgroupOf.1 hx)))

end

theorem e7CentModelJ_of
    (hSR : E7CentSRoots) :
    E7CentModelJ :=
  ⟨e7D4_le_perpLevi, e7D4_centralizes_sigma,
    fun j hj x hx => (e7A1_commute_D4 x hx j hj).symm,
    e7A1_le_normalizer_e7CentS hSR, e7D4_le_normalizer_e7CentS hSR⟩

section



private theorem commutator_pinnedX_E7_one {α β : Fin (Tag.rank .E7) → ℤ}
    (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hsum : IsRoot .E7 (α + β)) :
    ⁅(⟨pinnedX .E7 (ZMod 2) α 1, pinnedX_mem_adjointGroup α 1⟩ : E7G),
      (⟨pinnedX .E7 (ZMod 2) β 1, pinnedX_mem_adjointGroup β 1⟩ : E7G)⁆ =
      (⟨pinnedX .E7 (ZMod 2) (α + β) 1,
        pinnedX_mem_adjointGroup (α + β) 1⟩ : E7G) := by
  obtain ⟨hC, hform⟩ := (simply_laced_root_commutator_unit .E7 (Or.inr (Or.inr (Or.inl rfl)))
    hα hβ hne hne').1 hsum
  apply Subtype.ext
  change ⁅pinnedX .E7 (ZMod 2) α 1, pinnedX .E7 (ZMod 2) β 1⁆ =
    pinnedX .E7 (ZMod 2) (α + β) 1
  rw [hform (ZMod 2) 1 1]
  congr 1
  rcases hC with h | h
  · rw [h]; decide
  · rw [h]; decide

private theorem conj_eq_of_mem_zpowers_high {x z : E7G}
    (hx : x ∈ perpLevi .E7 (ZMod 2)) (hz : z ∈ Subgroup.zpowers e7HighInv) :
    x * z * x⁻¹ = z := by
  have ht0J : e7HighInv ∈ e7JTheta :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (mem_rootSubgroup.2 ⟨1, rfl⟩))
  have hx' : x ∈ Subgroup.centralizer (e7JTheta : Set E7G) := by
    rw [centralizer_highRootSL2_subgroupOf_E7_of_charTwo]
    exact hx
  have hcomm : e7HighInv * x = x * e7HighInv := Subgroup.mem_centralizer_iff.1 hx' _ ht0J
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  rw [(Commute.zpow_right hcomm.symm k).eq]
  group

private def e7CentModelP (x : E7G) : Prop :=
  ∀ w ∈ fs81CommSet (highRadical .E7 (ZMod 2)) e7CentSigma,
    ⁅x, w⁆ ∈ Subgroup.zpowers e7HighInv

private theorem e7CentModelP_mul {x y : E7G} (hx : x ∈ perpLevi .E7 (ZMod 2))
    (hy : y ∈ perpLevi .E7 (ZMod 2)) (hPx : e7CentModelP x) (hPy : e7CentModelP y) :
    e7CentModelP (x * y) := by
  intro w hw
  have hcomm : x * ⁅y, w⁆ * x⁻¹ = ⁅y, w⁆ := conj_eq_of_mem_zpowers_high hx (hPy w hw)
  have hid : ⁅x * y, w⁆ = x * ⁅y, w⁆ * x⁻¹ * ⁅x, w⁆ := by
    rw [commutatorElement_def]; group
  rw [hid, hcomm]
  exact Subgroup.mul_mem _ (hPy w hw) (hPx w hw)

private theorem e7CentModelP_inv {x : E7G} (hx : x ∈ perpLevi .E7 (ZMod 2))
    (hPx : e7CentModelP x) : e7CentModelP x⁻¹ := by
  intro w hw
  have hz : ⁅x, w⁆⁻¹ ∈ Subgroup.zpowers e7HighInv :=
    (Subgroup.zpowers e7HighInv).inv_mem (hPx w hw)
  have hcomm : x⁻¹ * ⁅x, w⁆⁻¹ * x = ⁅x, w⁆⁻¹ :=
    conj_eq_of_mem_zpowers_high ((perpLevi .E7 (ZMod 2)).inv_mem hx) hz
  have hid : ⁅x⁻¹, w⁆ = x⁻¹ * ⁅x, w⁆⁻¹ * x := by
    rw [commutatorElement_def]; group
  rw [hid, hcomm]
  exact hz

private theorem conj_mem_fs81CommSet {g w : E7G} (hgD : g ∈ perpLevi .E7 (ZMod 2))
    (hgσ : g * e7CentSigma = e7CentSigma * g)
    (hDQ : perpLevi .E7 (ZMod 2) ≤
      Subgroup.normalizer (highRadical .E7 (ZMod 2) : Set E7G))
    (hw : w ∈ fs81CommSet (highRadical .E7 (ZMod 2)) e7CentSigma) :
    g * w * g⁻¹ ∈ fs81CommSet (highRadical .E7 (ZMod 2)) e7CentSigma := by
  obtain ⟨q, hq, rfl⟩ := hw
  refine ⟨g * q * g⁻¹, (Subgroup.mem_normalizer_iff.1 (hDQ hgD) q).1 hq, ?_⟩
  have hgσ' : g * e7CentSigma * g⁻¹ = e7CentSigma := by
    calc g * e7CentSigma * g⁻¹ = (e7CentSigma * g) * g⁻¹ := by rw [hgσ]
      _ = e7CentSigma := by group
  rw [commutatorElement_def, commutatorElement_def]
  conv_rhs => rw [show e7CentSigma = g * e7CentSigma * g⁻¹ from hgσ'.symm]
  group

private noncomputable def e7CentModelN (hD : e7D4 ≤ perpLevi .E7 (ZMod 2)) :
    Subgroup ↥e7D4 where
  carrier := {x | e7CentModelP (x : E7G)}
  one_mem' := by
    intro w hw
    change ⁅((1 : ↥e7D4) : E7G), w⁆ ∈ Subgroup.zpowers e7HighInv
    rw [show ((1 : ↥e7D4) : E7G) = 1 from rfl, commutatorElement_def]
    simp
  mul_mem' := by
    intro x y hx hy
    change e7CentModelP (((x * y : ↥e7D4) : E7G))
    rw [show ((x * y : ↥e7D4) : E7G) = (x : E7G) * (y : E7G) from rfl]
    exact e7CentModelP_mul (hD x.2) (hD y.2) hx hy
  inv_mem' := by
    intro x hx
    change e7CentModelP (((x⁻¹ : ↥e7D4) : E7G))
    rw [show ((x⁻¹ : ↥e7D4) : E7G) = (x : E7G)⁻¹ from rfl]
    exact e7CentModelP_inv (hD x.2) hx

private theorem e7CentModelN_normal (hD : e7D4 ≤ perpLevi .E7 (ZMod 2))
    (hJσ : ∀ j ∈ e7D4, j * e7CentSigma = e7CentSigma * j)
    (hDQ : perpLevi .E7 (ZMod 2) ≤
      Subgroup.normalizer (highRadical .E7 (ZMod 2) : Set E7G)) :
    (e7CentModelN hD).Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  change e7CentModelP (((g * n * g⁻¹ : ↥e7D4) : E7G))
  rw [show ((g * n * g⁻¹ : ↥e7D4) : E7G) = (g : E7G) * (n : E7G) * (g : E7G)⁻¹ from rfl]
  intro w hw
  have hgD : (g : E7G) ∈ perpLevi .E7 (ZMod 2) := hD g.2
  have hgσ : (g : E7G) * e7CentSigma = e7CentSigma * (g : E7G) := hJσ g g.2
  have hg'σ : (g : E7G)⁻¹ * e7CentSigma = e7CentSigma * (g : E7G)⁻¹ := by
    calc (g : E7G)⁻¹ * e7CentSigma =
        (g : E7G)⁻¹ * (e7CentSigma * g) * (g : E7G)⁻¹ := by group
      _ = (g : E7G)⁻¹ * (g * e7CentSigma) * (g : E7G)⁻¹ := by rw [← hgσ]
      _ = e7CentSigma * (g : E7G)⁻¹ := by group
  have hgw : (g : E7G)⁻¹ * w * (g : E7G) ∈
      fs81CommSet (highRadical .E7 (ZMod 2)) e7CentSigma :=
    conj_mem_fs81CommSet ((perpLevi .E7 (ZMod 2)).inv_mem hgD) hg'σ hDQ hw
  have h := (hn : e7CentModelP (n : E7G)) ((g : E7G)⁻¹ * w * (g : E7G)) hgw
  have hid : ⁅(g : E7G) * (n : E7G) * (g : E7G)⁻¹, w⁆ =
      (g : E7G) * ⁅(n : E7G), (g : E7G)⁻¹ * w * (g : E7G)⁆ * (g : E7G)⁻¹ := by
    rw [commutatorElement_def]; group
  rw [hid, conj_eq_of_mem_zpowers_high hgD h]
  exact h

private theorem pinnedX_one_not_mem_zpowers_highRoot {δ : Fin (Tag.rank .E7) → ℤ}
    (hδroot : IsRoot .E7 δ) (hδ : δ ≠ highRoot .E7) :
    (⟨pinnedX .E7 (ZMod 2) δ 1, pinnedX_mem_adjointGroup δ 1⟩ : E7G) ∉
      Subgroup.zpowers e7HighInv := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hord : orderOf e7HighInv = 2 :=
    CFSG.SeitzReduction.E6Pilot.orderOf_pinnedX_one_adjointGroup (highRoot .E7)
  have h2 : e7HighInv ^ (2 : ℤ) = 1 := by
    have h := pow_orderOf_eq_one e7HighInv
    rw [hord] at h
    simpa using h
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · have hx1 : (⟨pinnedX .E7 (ZMod 2) δ 1, pinnedX_mem_adjointGroup δ 1⟩ : E7G) = 1 := by
      rw [← hk, zpow_eq_zpow_emod (x := e7HighInv) k h2, h]
      simp
    have h' : pinnedX .E7 (ZMod 2) δ 1 = pinnedX .E7 (ZMod 2) δ 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val hx1
    exact one_ne_zero (pinnedX_injective .E7 (ZMod 2) δ h')
  · have hxz : (⟨pinnedX .E7 (ZMod 2) δ 1, pinnedX_mem_adjointGroup δ 1⟩ : E7G) =
        e7HighInv := by
      rw [← hk, zpow_eq_zpow_emod (x := e7HighInv) k h2, h]
      simp
    have h' : δ = highRoot .E7 :=
      CFSG.SeitzReduction.F4Pilot.eq_of_pinnedX_eq_pinnedX hδroot
        ⟨isRoot_highRoot .E7, height_highRoot_pos .E7⟩ one_ne_zero (congrArg Subtype.val hxz)
    exact hδ h'

private abbrev e7WitAlpha2 : Fin (Tag.rank .E7) → ℤ := Pi.single 1 1

private abbrev e7WitMu : Fin (Tag.rank .E7) → ℤ := ![1, 0, 1, 1, 0, 0, 0]

private abbrev e7WitDelta : Fin (Tag.rank .E7) → ℤ := e7WitMu + d6HighRoot

private abbrev e7WitDelta' : Fin (Tag.rank .E7) → ℤ := e7WitAlpha2 + (e7WitMu + d6HighRoot)

private theorem isRoot_e7WitAlpha2 : IsRoot .E7 e7WitAlpha2 :=
  mem_rootFinset.1 (by decide +kernel)

private theorem isRoot_e7WitMu : IsRoot .E7 e7WitMu :=
  mem_rootFinset.1 (by decide +kernel)

private theorem isRoot_e7WitDelta : IsRoot .E7 e7WitDelta :=
  mem_rootFinset.1 (by decide +kernel)

private theorem isRoot_e7WitDelta' : IsRoot .E7 e7WitDelta' :=
  mem_rootFinset.1 (by decide +kernel)

private theorem mem_radical_e7WitMu :
    e7WitMu ∈ parabolicRadicalRoots .E7 (perpNodes .E7) := by
  rw [mem_parabolicRadicalRoots_perpNodes]
  exact ⟨isRoot_e7WitMu, by decide⟩

private theorem mem_overlap_e7WitAlpha2 :
    e7WitAlpha2 ∈ overlapRootsD4 .high .seven := by
  refine ⟨⟨⟨mem_rootFinset.1 (by decide +kernel), ?_⟩,
    mem_rootFinset.1 (by decide +kernel), ?_⟩,
    mem_rootFinset.1 (by decide +kernel), ?_⟩
  · change iform (highRoot .E7) e7WitAlpha2 = 0
    rw [iform_highRoot_E7]
    decide
  · change iform (Pi.single 6 1) e7WitAlpha2 = 0
    rw [iform_single_six]
    decide
  · change iform d6HighRoot e7WitAlpha2 = 0
    rw [iform_d6HighRoot]
    decide

private theorem e7WitDelta'_ne_highRoot : e7WitDelta' ≠ highRoot .E7 := by
  decide +kernel

private theorem e7WitAlpha2_ne_e7WitDelta : e7WitAlpha2 ≠ e7WitDelta := by
  decide +kernel

private theorem e7WitAlpha2_ne_neg_e7WitDelta : e7WitAlpha2 ≠ -e7WitDelta := by
  decide +kernel

private theorem e7WitMu_ne_d6HighRoot : e7WitMu ≠ d6HighRoot := by
  decide +kernel

private theorem e7WitMu_ne_neg_d6HighRoot : e7WitMu ≠ -d6HighRoot := by
  decide +kernel

private theorem exists_not_mem_e7CentModelN (hD : e7D4 ≤ perpLevi .E7 (ZMod 2)) :
    ∃ j₀ : ↥e7D4, j₀ ∉ e7CentModelN hD := by
  classical
  let j₀ : ↥e7D4 := ⟨⟨pinnedX .E7 (ZMod 2) e7WitAlpha2 1,
    pinnedX_mem_adjointGroup e7WitAlpha2 1⟩,
    Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan mem_overlap_e7WitAlpha2 1)⟩
  let q₀ : E7G := ⟨pinnedX .E7 (ZMod 2) e7WitMu 1, pinnedX_mem_adjointGroup e7WitMu 1⟩
  have hq₀ : q₀ ∈ highRadical .E7 (ZMod 2) :=
    Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan mem_radical_e7WitMu 1)
  refine ⟨j₀, fun hmem => ?_⟩
  let w₀ : E7G := ⁅q₀, e7CentSigma⁆
  have hw₀ : w₀ ∈ fs81CommSet (highRadical .E7 (ZMod 2)) e7CentSigma := ⟨q₀, hq₀, rfl⟩
  have h := hmem w₀ hw₀
  have hcompress : w₀ =
      (⟨pinnedX .E7 (ZMod 2) e7WitDelta 1, pinnedX_mem_adjointGroup e7WitDelta 1⟩ : E7G) :=
    commutator_pinnedX_E7_one isRoot_e7WitMu isRoot_d6HighRoot e7WitMu_ne_d6HighRoot
      e7WitMu_ne_neg_d6HighRoot isRoot_e7WitDelta
  have hdouble : ⁅(j₀ : E7G), w₀⁆ =
      (⟨pinnedX .E7 (ZMod 2) e7WitDelta' 1,
        pinnedX_mem_adjointGroup e7WitDelta' 1⟩ : E7G) := by
    rw [hcompress]
    exact commutator_pinnedX_E7_one isRoot_e7WitAlpha2 isRoot_e7WitDelta
      e7WitAlpha2_ne_e7WitDelta e7WitAlpha2_ne_neg_e7WitDelta isRoot_e7WitDelta'
  rw [hdouble] at h
  exact pinnedX_one_not_mem_zpowers_highRoot isRoot_e7WitDelta' e7WitDelta'_ne_highRoot h

private theorem units_zmod_two_eq_one : ∀ u : (ZMod 2)ˣ, u = 1 := by
  decide

private theorem mem_rootSpan_overlapNodes_of_mem_rootPerpLevi {m : E7G}
    (hmM : m ∈ rootPerpLevi .E7 (ZMod 2) d6HighRoot)
    (hmJ : m ∈ Subgroup.centralizer (e7JTheta : Set E7G)) :
    (m : ModGL .E7 (ZMod 2)) ∈ rootSpan .E7 (ZMod 2) (parabolicRoots .E7 overlapNodes) := by
  have hmMroot : (m : ModGL .E7 (ZMod 2)) ∈
      rootSpan .E7 (ZMod 2) (rootPerp .E7 d6HighRoot) :=
    Subgroup.mem_subgroupOf.1 hmM
  have hd6 : (m : ModGL .E7 (ZMod 2)) ∈
      Subgroup.centralizer ((d6HighRootSL2 (ZMod 2)) : Set (ModGL .E7 (ZMod 2))) :=
    rootSpan_le_centralizer_rootPair_E7 (K := ZMod 2) (S := rootPerp .E7 d6HighRoot)
      (β := d6HighRoot) isRoot_d6HighRoot (fun α hα => ⟨hα.1, hα.2⟩) hmMroot
  have hroot : (m : ModGL .E7 (ZMod 2)) ∈
      Subgroup.centralizer ((highRootSL2 .E7 (ZMod 2)) : Set (ModGL .E7 (ZMod 2))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyJ : (⟨y, highRootSL2_le_adjointGroup hy⟩ : E7G) ∈ e7JTheta :=
      Subgroup.mem_subgroupOf.2 hy
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hmJ _ hyJ)
  rw [← adjointGroup_inf_centralizer_highRootSL2_inf_centralizer_d6HighRootSL2
    (K := ZMod 2) units_zmod_two_eq_one]
  exact ⟨⟨m.2, hroot⟩, hd6⟩

private theorem mul_decomp_centralizer {d q m : E7G} {Q M : Subgroup E7G}
    (hd : d ∈ Subgroup.centralizer (e7JTheta : Set E7G)) (hJM : e7JTheta ≤ M)
    (hMn : M ≤ Subgroup.normalizer (Q : Set E7G)) (hbot : Q ⊓ M = ⊥) (hq : q ∈ Q)
    (hm : m ∈ M) (heq : q * m = d) :
    q ∈ Subgroup.centralizer (e7JTheta : Set E7G) ∧
      m ∈ Subgroup.centralizer (e7JTheta : Set E7G) := by
  have hfix : ∀ j ∈ e7JTheta, j * d * j⁻¹ = d := by
    intro j hj
    have h := Subgroup.mem_centralizer_iff.1 hd j hj
    calc j * d * j⁻¹ = d * j * j⁻¹ := by rw [h]
      _ = d := by group
  have hprod : ∀ j ∈ e7JTheta, (j * q * j⁻¹) * (j * m * j⁻¹) = q * m := by
    intro j hj
    calc (j * q * j⁻¹) * (j * m * j⁻¹) = j * (q * m) * j⁻¹ := by group
      _ = j * d * j⁻¹ := by rw [heq]
      _ = d := hfix j hj
      _ = q * m := heq.symm
  constructor <;> rw [Subgroup.mem_centralizer_iff] <;> intro j hj
  · have hq' : j * q * j⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.1 (hMn (hJM hj)) q).1 hq
    have hm' : j * m * j⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem (hJM hj) hm) (M.inv_mem (hJM hj))
    have := (eq_and_eq_of_mul_eq_mul_of_inf_eq_bot hbot hq' hq hm' hm (hprod j hj)).1
    calc j * q = (j * q * j⁻¹) * j := by group
      _ = q * j := by rw [this]
  · have hq' : j * q * j⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.1 (hMn (hJM hj)) q).1 hq
    have hm' : j * m * j⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem (hJM hj) hm) (M.inv_mem (hJM hj))
    have := (eq_and_eq_of_mul_eq_mul_of_inf_eq_bot hbot hq' hq hm' hm (hprod j hj)).2
    calc j * m = (j * m * j⁻¹) * j := by group
      _ = m * j := by rw [this]

private theorem exists_e7CentS_mul_e7A1_mul_e7D4 (hSR : E7CentSRoots) (hF : E7CentModelFlag)
    (hJ : E7CentModelJ) {d : E7G} (hdD : d ∈ perpLevi .E7 (ZMod 2))
    (hdσ : d * e7CentSigma = e7CentSigma * d) :
    ∃ r ∈ e7CentS, ∃ a ∈ e7A1, ∃ j ∈ e7D4, r * (a * j) = d := by
  have hdC : d ∈ Subgroup.centralizer ({e7CentSigma} : Set E7G) :=
    Subgroup.mem_centralizer_iff.2 fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hdσ.symm
  obtain ⟨-, hsup, hbot, hnorm⟩ := isTwoRadicalDecomp_root (τ := .E7) (K := ZMod 2)
    (Or.inr (Or.inl rfl)) (γ := d6HighRoot) isRoot_d6HighRoot (c := 1) one_ne_zero
  have hdSU : d ∈ rootRadical .E7 (ZMod 2) d6HighRoot ⊔
      rootPerpLevi .E7 (ZMod 2) d6HighRoot := by
    rw [hsup]
    exact hdC
  obtain ⟨q, hqQ, m, hmM, hqm⟩ := exists_mul_of_le_normalizer hnorm hdSU
  have hJM : e7JTheta ≤ rootPerpLevi .E7 (ZMod 2) d6HighRoot :=
    highRootSL2_subgroupOf_le_rootPerpLevi (Or.inr (Or.inl rfl))
      ((mem_perpRoots_iff_iform (Or.inr (Or.inl rfl))).2
        ⟨isRoot_d6HighRoot, iform_highRoot_d6HighRoot⟩)
  have hdDc : d ∈ Subgroup.centralizer (e7JTheta : Set E7G) := by
    rw [centralizer_highRootSL2_subgroupOf_E7_of_charTwo]
    exact hdD
  obtain ⟨hqJ, hmJ⟩ := mul_decomp_centralizer hdDc hJM hnorm hbot hqQ hmM hqm
  have hqD : q ∈ perpLevi .E7 (ZMod 2) := by
    rwa [centralizer_highRootSL2_subgroupOf_E7_of_charTwo] at hqJ
  have hmD : m ∈ perpLevi .E7 (ZMod 2) := by
    rwa [centralizer_highRootSL2_subgroupOf_E7_of_charTwo] at hmJ
  have hqS : q ∈ e7CentS := by
    rw [hSR]
    exact ⟨hqQ, hqD⟩
  have hmSpan : m ∈ (rootSpan .E7 (ZMod 2) (parabolicRoots .E7 overlapNodes)).subgroupOf
      (adjointGroup .E7 (ZMod 2)) :=
    Subgroup.mem_subgroupOf.2 (mem_rootSpan_overlapNodes_of_mem_rootPerpLevi hmM hmJ)
  have hmSup : m ∈ e7A1 ⊔ e7D4 := by
    rwa [overlapRootSpan_subgroupOf_eq_sup] at hmSpan
  have hD4normA1 : e7D4 ≤ Subgroup.normalizer (e7A1 : Set E7G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb a ha
    have hba : b * a * b⁻¹ = a := by rw [hJ.2.2.1 b hb a ha]; group
    rwa [hba]
  obtain ⟨a, haA1, j, hjD4, haj⟩ := exists_mul_of_le_normalizer hD4normA1 hmSup
  exact ⟨q, hqS, a, haA1, j, hjD4, by rw [haj, hqm]⟩

end

theorem e7CentModelM_of
    (hSR : E7CentSRoots)
    (hF : E7CentModelFlag) (hJ : E7CentModelJ) : E7CentModelM := by
  intro d hdD hdσ hdW
  obtain ⟨q, hqS, a, haA1, j, hjD4, hqaj⟩ :=
    exists_e7CentS_mul_e7A1_mul_e7D4 hSR hF hJ hdD hdσ
  have haD : a ∈ perpLevi .E7 (ZMod 2) := hF.2.1 haA1
  have hqD : q ∈ perpLevi .E7 (ZMod 2) := hF.1 hqS
  have hj_eq : j = a⁻¹ * q⁻¹ * d := by rw [← hqaj]; group
  have hPq : e7CentModelP q := hF.2.2.2.2.2.1 q hqS
  have hPa : e7CentModelP a := hF.2.2.2.2.2.2.1 a haA1
  have hPj : e7CentModelP j := by
    rw [hj_eq]
    exact e7CentModelP_mul ((perpLevi .E7 (ZMod 2)).mul_mem
      ((perpLevi .E7 (ZMod 2)).inv_mem haD) ((perpLevi .E7 (ZMod 2)).inv_mem hqD)) hdD
      (e7CentModelP_mul ((perpLevi .E7 (ZMod 2)).inv_mem haD)
        ((perpLevi .E7 (ZMod 2)).inv_mem hqD)
        (e7CentModelP_inv haD hPa) (e7CentModelP_inv hqD hPq)) hdW
  have hjN : (⟨j, hjD4⟩ : ↥e7D4) ∈ e7CentModelN hJ.1 := hPj
  have hDQ : perpLevi .E7 (ZMod 2) ≤
      Subgroup.normalizer (highRadical .E7 (ZMod 2) : Set E7G) :=
    (isTwoRadicalDecomp_highRoot (K := ZMod 2) (Or.inr (Or.inl rfl)) (c := 1)
      one_ne_zero).2.2.2
  haveI hsimple : IsSimpleGroup ↥e7D4 := isSimpleGroup_overlapSpanD4 (K := ZMod 2) (by decide)
  have hNnormal : (e7CentModelN hJ.1).Normal := e7CentModelN_normal hJ.1 hJ.2.1 hDQ
  have hNbot : e7CentModelN hJ.1 = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (e7CentModelN hJ.1) with h | h
    · exact h
    · obtain ⟨j₀, hj₀⟩ := exists_not_mem_e7CentModelN hJ.1
      exact absurd (h ▸ Subgroup.mem_top j₀) hj₀
  have hj1 : j = 1 := by
    have hmem : (⟨j, hjD4⟩ : ↥e7D4) ∈ (⊥ : Subgroup ↥e7D4) := hNbot ▸ hjN
    rw [Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hdqa : d = q * a := by rw [← hqaj, hj1, mul_one]
  rw [hdqa]
  exact Subgroup.mul_mem_sup hqS haA1

end CFSG.StandardType.FrameRoute.FS81
