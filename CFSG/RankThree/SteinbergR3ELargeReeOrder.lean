module

public import CFSG.LieType.Ree.LargeReeInvolutionTCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm

public section

namespace CFSG.RankThree.LargeReeOrder

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag

section Collection

variable {τ : Tag} {K : Type} [Field K]

theorem list_prod_pinnedX_append {m₁ m₂ : ℕ} (α₁ : Fin m₁ → Fin τ.rank → ℤ)
    (α₂ : Fin m₂ → Fin τ.rank → ℤ) (c₁ : Fin m₁ → K) (c₂ : Fin m₂ → K) :
    (List.ofFn fun k => pinnedX τ K (Fin.append α₁ α₂ k) (Fin.append c₁ c₂ k)).prod =
      (List.ofFn fun k => pinnedX τ K (α₁ k) (c₁ k)).prod *
        (List.ofFn fun k => pinnedX τ K (α₂ k) (c₂ k)).prod := by
  rw [← List.prod_append, ← List.ofFn_fin_append]
  congr 1
  refine List.ofFn_inj.2 (funext fun k => ?_)
  induction k using Fin.addCases with
  | left k => simp
  | right k => simp

theorem bijOn_mul_rootSpan {S₁ S₂ : Set (Fin τ.rank → ℤ)}
    (h₁ : ∀ α ∈ S₁, IsRoot τ α ∧ 0 < height α) (h₂ : ∀ α ∈ S₂, IsRoot τ α ∧ 0 < height α)
    (hc₁ : ∀ α ∈ S₁, ∀ β ∈ S₁, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S₁)
    (hc₂ : ∀ α ∈ S₂, ∀ β ∈ S₂, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S₂)
    (hc : ∀ α ∈ S₁ ∪ S₂, ∀ β ∈ S₁ ∪ S₂, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S₁ ∪ S₂)
    (hdisj : Disjoint S₁ S₂) :
    Set.BijOn (fun p : ModGL τ K × ModGL τ K => p.1 * p.2)
      ((rootSpan τ K S₁ : Set (ModGL τ K)) ×ˢ (rootSpan τ K S₂ : Set (ModGL τ K)))
      (rootSpan τ K (S₁ ∪ S₂) : Set (ModGL τ K)) := by
  obtain ⟨α₁, hinj₁, hr₁⟩ := exists_rootEnum (finite_of_forall_isRoot_pos h₁)
  obtain ⟨α₂, hinj₂, hr₂⟩ := exists_rootEnum (finite_of_forall_isRoot_pos h₂)
  have hmem₁ : ∀ k, α₁ k ∈ S₁ := fun k => hr₁ ▸ Set.mem_range_self k
  have hmem₂ : ∀ k, α₂ k ∈ S₂ := fun k => hr₂ ▸ Set.mem_range_self k
  have hS : ∀ α ∈ S₁ ∪ S₂, IsRoot τ α ∧ 0 < height α := fun α h => h.elim (h₁ α) (h₂ α)
  have hne : ∀ k l, α₁ k ≠ α₂ l := fun k l h =>
    Set.disjoint_left.1 hdisj (hmem₁ k) (h ▸ hmem₂ l)
  have hinj : Function.Injective (Fin.append α₁ α₂) := by
    intro k l h
    induction k using Fin.addCases with
    | left k =>
      induction l using Fin.addCases with
      | left l =>
        simp only [Fin.append_left] at h
        rw [hinj₁ h]
      | right l =>
        simp only [Fin.append_left, Fin.append_right] at h
        exact absurd h (hne k l)
    | right k =>
      induction l using Fin.addCases with
      | left l =>
        simp only [Fin.append_left, Fin.append_right] at h
        exact absurd h.symm (hne l k)
      | right l =>
        simp only [Fin.append_right] at h
        rw [hinj₂ h]
  have hrange : Set.range (Fin.append α₁ α₂) = S₁ ∪ S₂ := by
    ext β
    constructor
    · rintro ⟨k, rfl⟩
      induction k using Fin.addCases with
      | left k => simpa using Or.inl (hmem₁ k)
      | right k => simpa using Or.inr (hmem₂ k)
    · rintro (hβ | hβ)
      · obtain ⟨k, rfl⟩ : β ∈ Set.range α₁ := by rw [hr₁]; exact hβ
        exact ⟨Fin.castAdd _ k, by simp⟩
      · obtain ⟨k, rfl⟩ : β ∈ Set.range α₂ := by rw [hr₂]; exact hβ
        exact ⟨Fin.natAdd _ k, by simp⟩
  have hB := bijOn_prod_pinnedX K hS hc (Fin.append α₁ α₂) hinj hrange
  have hB₁ := bijOn_prod_pinnedX K h₁ hc₁ α₁ hinj₁ hr₁
  have hB₂ := bijOn_prod_pinnedX K h₂ hc₂ α₂ hinj₂ hr₂
  refine ⟨fun p hp => ?_, fun p hp p' hp' h => ?_, fun g hg => ?_⟩
  · exact mul_mem (rootSpan_mono Set.subset_union_left hp.1)
      (rootSpan_mono Set.subset_union_right hp.2)
  · obtain ⟨c₁, -, hc₁'⟩ := hB₁.2.2 hp.1
    obtain ⟨c₂, -, hc₂'⟩ := hB₂.2.2 hp.2
    obtain ⟨d₁, -, hd₁'⟩ := hB₁.2.2 hp'.1
    obtain ⟨d₂, -, hd₂'⟩ := hB₂.2.2 hp'.2
    simp only at hc₁' hc₂' hd₁' hd₂' h
    have e := hB.2.1 (Set.mem_univ (Fin.append c₁ c₂)) (Set.mem_univ (Fin.append d₁ d₂)) (by
      simp only
      rw [list_prod_pinnedX_append, list_prod_pinnedX_append, hc₁', hc₂', hd₁', hd₂']
      exact h)
    have e₁ : c₁ = d₁ := funext fun k => by simpa using congrFun e (Fin.castAdd _ k)
    have e₂ : c₂ = d₂ := funext fun k => by simpa using congrFun e (Fin.natAdd _ k)
    exact Prod.ext (by rw [← hc₁', ← hd₁', e₁]) (by rw [← hc₂', ← hd₂', e₂])
  · obtain ⟨c, -, rfl⟩ := hB.2.2 hg
    refine ⟨((List.ofFn fun k => pinnedX τ K (α₁ k) (c (Fin.castAdd _ k))).prod,
      (List.ofFn fun k => pinnedX τ K (α₂ k) (c (Fin.natAdd _ k))).prod),
      ⟨hB₁.1 (Set.mem_univ _), hB₂.1 (Set.mem_univ _)⟩, ?_⟩
    simp only
    rw [← list_prod_pinnedX_append, Fin.append_castAdd_natAdd]

end Collection

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem card_rootSpan_union_inf_reeGamma {S₁ S₂ : Set (Fin F4.tag.rank → ℤ)}
    (h₁ : ∀ α ∈ S₁, IsRoot F4.tag α ∧ 0 < height α)
    (h₂ : ∀ α ∈ S₂, IsRoot F4.tag α ∧ 0 < height α)
    (hc₁ : ∀ α ∈ S₁, ∀ β ∈ S₁, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot F4.tag (a • α + b • β) →
      a • α + b • β ∈ S₁)
    (hc₂ : ∀ α ∈ S₂, ∀ β ∈ S₂, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot F4.tag (a • α + b • β) →
      a • α + b • β ∈ S₂)
    (hc : ∀ α ∈ S₁ ∪ S₂, ∀ β ∈ S₁ ∪ S₂, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot F4.tag (a • α + b • β) → a • α + b • β ∈ S₁ ∪ S₂)
    (hdisj : Disjoint S₁ S₂)
    (hΨ₁ : ∀ α ∈ S₁, IsRoot F4.tag α ∧ F4.dualRoot α ∈ S₁)
    (hΨ₂ : ∀ α ∈ S₂, IsRoot F4.tag α ∧ F4.dualRoot α ∈ S₂) :
    Nat.card (rootSpan F4.tag K (S₁ ∪ S₂) ⊓ F4.reeGamma K a : Subgroup (ModGL F4.tag K)) =
      Nat.card (rootSpan F4.tag K S₁ ⊓ F4.reeGamma K a : Subgroup (ModGL F4.tag K)) *
        Nat.card (rootSpan F4.tag K S₂ ⊓ F4.reeGamma K a : Subgroup (ModGL F4.tag K)) := by
  have hB := bijOn_mul_rootSpan (K := K) h₁ h₂ hc₁ hc₂ hc hdisj
  have hbij : Set.BijOn (fun p : ModGL F4.tag K × ModGL F4.tag K => p.1 * p.2)
      (((rootSpan F4.tag K S₁ ⊓ F4.reeGamma K a : Subgroup (ModGL F4.tag K)) :
        Set (ModGL F4.tag K)) ×ˢ
        ((rootSpan F4.tag K S₂ ⊓ F4.reeGamma K a : Subgroup (ModGL F4.tag K)) :
          Set (ModGL F4.tag K)))
      ((rootSpan F4.tag K (S₁ ∪ S₂) ⊓ F4.reeGamma K a : Subgroup (ModGL F4.tag K)) :
        Set (ModGL F4.tag K)) := by
    refine ⟨fun p hp => ?_, fun p hp p' hp' h => ?_, fun g hg => ?_⟩
    · exact Subgroup.mem_inf.2 ⟨hB.1 ⟨(Subgroup.mem_inf.1 hp.1).1, (Subgroup.mem_inf.1 hp.2).1⟩,
        mul_mem (Subgroup.mem_inf.1 hp.1).2 (Subgroup.mem_inf.1 hp.2).2⟩
    · exact hB.2.1 ⟨(Subgroup.mem_inf.1 hp.1).1, (Subgroup.mem_inf.1 hp.2).1⟩
        ⟨(Subgroup.mem_inf.1 hp'.1).1, (Subgroup.mem_inf.1 hp'.2).1⟩ h
    · obtain ⟨hgU, hgΓ⟩ := Subgroup.mem_inf.1 hg
      obtain ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩ := hB.2.2 hgU
      have hua : u ∈ adjointGroup F4.tag K := rootSpan_le_adjointGroup _ hu
      have hva : v ∈ adjointGroup F4.tag K := rootSpan_le_adjointGroup _ hv
      have hFu := finiteReeAut_mem_of_map_le (a := a) (map_finiteReeAut_rootSpan_le hΨ₁) hu hua
      have hFv := finiteReeAut_mem_of_map_le (a := a) (map_finiteReeAut_rootSpan_le hΨ₂) hv hva
      have hF := finiteReeAut_eq_of_mem_reeGamma hgΓ (mul_mem hua hva)
      have e : (⟨u * v, mul_mem hua hva⟩ : adjointGroup F4.tag K) = ⟨u, hua⟩ * ⟨v, hva⟩ := rfl
      rw [e, map_mul, Subgroup.coe_mul] at hF
      have hmem : (((F4.finiteReeAut K a ⟨u, hua⟩ : adjointGroup F4.tag K) : ModGL F4.tag K),
          ((F4.finiteReeAut K a ⟨v, hva⟩ : adjointGroup F4.tag K) : ModGL F4.tag K)) ∈
          (rootSpan F4.tag K S₁ : Set (ModGL F4.tag K)) ×ˢ
            (rootSpan F4.tag K S₂ : Set (ModGL F4.tag K)) := ⟨hFu, hFv⟩
      have huv := hB.2.1 hmem ⟨hu, hv⟩ hF
      simp only [Prod.mk.injEq] at huv
      exact ⟨(u, v), ⟨Subgroup.mem_inf.2 ⟨hu, mem_reeGamma_of_fixed hua huv.1⟩,
        Subgroup.mem_inf.2 ⟨hv, mem_reeGamma_of_fixed hva huv.2⟩⟩, rfl⟩
  calc Nat.card (rootSpan F4.tag K (S₁ ∪ S₂) ⊓ F4.reeGamma K a : Subgroup (ModGL F4.tag K))
      = Nat.card (((rootSpan F4.tag K S₁ ⊓ F4.reeGamma K a : Subgroup (ModGL F4.tag K)) :
          Set (ModGL F4.tag K)) ×ˢ
          ((rootSpan F4.tag K S₂ ⊓ F4.reeGamma K a : Subgroup (ModGL F4.tag K)) :
            Set (ModGL F4.tag K))) := Nat.card_congr hbij.equiv.symm
    _ = _ := by rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]; rfl

end Fixed

section Cells

variable {t : ReeTag}

theorem inversionSet_mul_fixedOrbitElement {w : WeylGroup t.tag} (j : Fin t.fixedOrbitCount)
    (hpos : ∀ α ∈ t.fixedOrbitRoots j, 0 < height (w • α)) :
    inversionSet (w * t.fixedOrbitElement j) =
        ((t.fixedOrbitElement j • ·) '' inversionSet w) ∪ t.fixedOrbitRoots j ∧
      Disjoint ((t.fixedOrbitElement j • ·) '' inversionSet w) (t.fixedOrbitRoots j) := by
  set z := t.fixedOrbitElement j
  have hcompl : ∀ β, β ∈ t.fixedOrbitComplementRoots j ↔
      (IsRoot t.tag β ∧ 0 < height β) ∧ β ∉ t.fixedOrbitRoots j := fun β => by
    rw [fixedOrbitComplementRoots_eq]
    rfl
  have hEpos : ∀ β ∈ t.fixedOrbitRoots j, IsRoot t.tag β ∧ 0 < height β := fun β hβ =>
    ⟨(mem_fixedOrbitRoots_iff.1 hβ).1, (mem_fixedOrbitRoots_iff.1 hβ).2.1⟩
  have hImS : ∀ β ∈ inversionSet w, β ∈ t.fixedOrbitComplementRoots j := by
    intro β hβ
    refine (hcompl β).2 ⟨inversionSet_pos hβ, fun hβE => ?_⟩
    have := hpos β hβE
    have := hβ.2.2.2
    omega
  have hzS : ∀ β ∈ inversionSet w, z • β ∈ t.fixedOrbitComplementRoots j := fun β hβ =>
    (bijOn_fixedOrbitComplementRoots j).mapsTo (hImS β hβ)
  have hdisj : Disjoint ((z • ·) '' inversionSet w) (t.fixedOrbitRoots j) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨β, hβ, rfl⟩ hE
    exact ((hcompl _).1 (hzS β hβ)).2 hE
  refine ⟨Set.ext fun α => ⟨fun hα => ?_, fun hα => ?_⟩, hdisj⟩
  · obtain ⟨hr, hp, -, hneg⟩ := hα
    rw [mul_smul] at hneg
    by_cases hαE : α ∈ t.fixedOrbitRoots j
    · exact Or.inr hαE
    · have hzα : z • α ∈ t.fixedOrbitComplementRoots j :=
        (bijOn_fixedOrbitComplementRoots j).mapsTo ((hcompl α).2 ⟨⟨hr, hp⟩, hαE⟩)
      obtain ⟨⟨hzr, hzp⟩, -⟩ := (hcompl _).1 hzα
      refine Or.inl ⟨z • α, ⟨hzr, hzp, IsRoot.smul hzr w, hneg⟩, ?_⟩
      exact fixedOrbitElement_smul_smul j α
  · rcases hα with ⟨β, hβ, rfl⟩ | hαE
    · obtain ⟨⟨hzr, hzp⟩, -⟩ := (hcompl _).1 (hzS β hβ)
      refine ⟨hzr, hzp, ?_, ?_⟩
      · exact IsRoot.smul hzr _
      · rw [mul_smul, fixedOrbitElement_smul_smul]
        exact hβ.2.2.2
    · obtain ⟨hr, hp⟩ := hEpos α hαE
      have hzα : z • α ∈ Neg.neg '' t.fixedOrbitRoots j := by
        rw [← image_fixedOrbitRoots]
        exact ⟨α, hαE, rfl⟩
      obtain ⟨β, hβE, hβ⟩ := hzα
      refine ⟨hr, hp, IsRoot.smul hr _, ?_⟩
      rw [mul_smul, ← hβ, smul_neg, height_neg]
      have := hpos β hβE
      omega

theorem image_inversionSet_closed (z w : WeylGroup t.tag) :
    ∀ α ∈ (z • ·) '' inversionSet w, ∀ β ∈ (z • ·) '' inversionSet w, ∀ a b : ℕ, 1 ≤ a →
      1 ≤ b → IsRoot t.tag (a • α + b • β) → a • α + b • β ∈ (z • ·) '' inversionSet w := by
  rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩ m n hm hn hr
  rw [← smul_nsmul_add_nsmul] at hr ⊢
  exact ⟨_, inversionSet_closed w α hα β hβ m n hm hn ((isRoot_smul_iff z).1 hr), rfl⟩

theorem fixedOrbitRoots_closed (j : Fin t.fixedOrbitCount) :
    ∀ α ∈ t.fixedOrbitRoots j, ∀ β ∈ t.fixedOrbitRoots j, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot t.tag (a • α + b • β) → a • α + b • β ∈ t.fixedOrbitRoots j := by
  intro α hα β hβ m n hm hn hr
  have hs : (List.replicate m α ++ List.replicate n β).sum = m • α + n • β := by
    rw [List.sum_append, List.sum_replicate, List.sum_replicate]
  rw [← hs] at hr ⊢
  refine list_sum_mem_fixedOrbitRoots ?_ (fun x hx => ?_) hr
  · intro h
    have := congrArg List.length h
    simp only [List.length_append, List.length_replicate, List.length_nil] at this
    omega
  · rcases List.mem_append.1 hx with hx | hx
    · rw [List.eq_of_mem_replicate hx]
      exact hα
    · rw [List.eq_of_mem_replicate hx]
      exact hβ

end Cells

section CellOrders

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem card_reeFixedCellUnipotent_mul {w : WeylGroup F4.tag} (hw : w ∈ F4.relWeylRee)
    (j : Fin F4.fixedOrbitCount) (hpos : ∀ α ∈ F4.fixedOrbitRoots j, 0 < height (w • α)) :
    Nat.card (F4.reeFixedCellUnipotent K a (w * F4.fixedOrbitElement j)) =
      Nat.card (F4.reeFixedCellUnipotent K a w) * Nat.card (F4.reeFixedOrbitUnipotent K a j) := by
  set z := F4.fixedOrbitElement j
  obtain ⟨hdec, hdisj⟩ := inversionSet_mul_fixedOrbitElement j hpos
  have hsub : (z • ·) '' inversionSet w ⊆ inversionSet (w * z) := hdec ▸ Set.subset_union_left
  have h₁ : ∀ α ∈ (z • ·) '' inversionSet w, IsRoot F4.tag α ∧ 0 < height α := fun α hα =>
    inversionSet_pos (hsub hα)
  have h₂ : ∀ α ∈ F4.fixedOrbitRoots j, IsRoot F4.tag α ∧ 0 < height α := fun α hα =>
    ⟨(mem_fixedOrbitRoots_iff.1 hα).1, (mem_fixedOrbitRoots_iff.1 hα).2.1⟩
  have hz : F4.weylPerm z = z := fixedOrbitElement_mem j
  have hΨ₁ : ∀ α ∈ (z • ·) '' inversionSet w, IsRoot F4.tag α ∧
      F4.dualRoot α ∈ (z • ·) '' inversionSet w := by
    rintro _ ⟨β, hβ, rfl⟩
    refine ⟨IsRoot.smul hβ.1 z, F4.dualRoot β, dualRoot_mem_inversionSet hw hβ, ?_⟩
    change z • F4.dualRoot β = F4.dualRoot (z • β)
    rw [dualRoot_smul z hβ.1, hz]
  have hΨ₂ : ∀ α ∈ F4.fixedOrbitRoots j, IsRoot F4.tag α ∧ F4.dualRoot α ∈ F4.fixedOrbitRoots j :=
    fun α hα => ⟨(h₂ α hα).1, dualRoot_mem_fixedOrbitRoots_F4 hα⟩
  have hcard := card_rootSpan_union_inf_reeGamma (K := K) (a := a) h₁ h₂
    (image_inversionSet_closed z w) (fixedOrbitRoots_closed j)
    (hdec ▸ inversionSet_closed (w * z)) hdisj hΨ₁ hΨ₂
  have hn : canonicalRep (coxeterSystem F4.tag) K z ∈ F4.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial F4 K a (fixedOrbitElement_mem j)).2
  have hmap : rootSpan F4.tag K ((z • ·) '' inversionSet w) ⊓ F4.reeGamma K a =
      (F4.reeFixedCellUnipotent K a w).map
        (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K z)).toMonoidHom := by
    rw [reeFixedCellUnipotent, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
      (canonical_weyl_root_transport F4.tag K).1 z _ fun α hα => hα.1,
      map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]
  change Nat.card (rootSpan F4.tag K (inversionSet (w * z)) ⊓ F4.reeGamma K a :
    Subgroup (ModGL F4.tag K)) = _
  rw [hdec, hcard, hmap, Subgroup.card_map_of_injective (MulAut.conj _).injective]
  rfl

theorem card_reeFixedOrbitUnipotent_F4 (hK : Nat.card K = 2 ^ (2 * a + 1))
    (j : Fin F4.fixedOrbitCount) :
    Nat.card (F4.reeFixedOrbitUnipotent K a j) = Nat.card K ^ (j.val + 1) := by
  match j with
  | ⟨0, _⟩ => rw [pow_one]; exact card_reeFixedOrbitUnipotent_zero hK
  | ⟨1, _⟩ => exact card_reeFixedOrbitUnipotent_one hK

@[expose] def cellExp (k : Fin F4.fixedWeylOrder) : ℕ :=
  (![0, 1, 2, 3, 3, 4, 5, 6, 6, 7, 8, 9, 9, 10, 11, 12] : Fin 16 → ℕ) k

@[expose] def cellPred (k : Fin F4.fixedWeylOrder) : Fin F4.fixedWeylOrder :=
  (![0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : Fin 16 → Fin 16) k

@[expose] def cellLetter (k : Fin F4.fixedWeylOrder) : Fin F4.fixedOrbitCount :=
  (![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1] : Fin 16 → Fin 2) k

theorem cell_table_check : ∀ k : Fin F4.fixedWeylOrder, k.val ≠ 0 →
    (cellPred k).val < k.val ∧ F4.fixedRelRight (cellPred k) (cellLetter k) = k ∧
      cellExp k = cellExp (cellPred k) + (cellLetter k).val + 1 ∧
      ∀ x ∈ largeReeBlockImage (cellPred k) (cellLetter k), 0 < height x := by
  decide +kernel

theorem card_reeFixedCellUnipotent_fixedRelElt (hK : Nat.card K = 2 ^ (2 * a + 1))
    (k : Fin F4.fixedWeylOrder) :
    Nat.card (F4.reeFixedCellUnipotent K a (F4.fixedRelElt k)) = Nat.card K ^ cellExp k := by
  induction hn : k.val using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    by_cases hk : k.val = 0
    · have hk0 : k = ⟨0, by decide⟩ := Fin.ext hk
      subst hk0
      have h1 : F4.fixedRelElt ⟨0, by decide⟩ = 1 := rfl
      have hbot : rootSpan F4.tag K (inversionSet (1 : WeylGroup F4.tag)) = ⊥ := by
        rw [inversionSet_one]
        exact le_bot_iff.1 (iSup₂_le fun _ h => absurd h (Set.notMem_empty _))
      rw [h1, reeFixedCellUnipotent, hbot, bot_inf_eq, Subgroup.card_bot]
      rfl
    · obtain ⟨hlt, hright, hexp, hsign⟩ := cell_table_check k hk
      have hw := fixedRelElt_mem (t := F4) (cellPred k)
      have hpos : ∀ α ∈ F4.fixedOrbitRoots (cellLetter k),
          0 < height (F4.fixedRelElt (cellPred k) • α) := by
        intro α hα
        have hmem : F4.fixedRelElt (cellPred k) • α ∈
            (F4.fixedRelElt (cellPred k) • ·) '' F4.fixedOrbitRoots (cellLetter k) := ⟨α, hα, rfl⟩
        rw [image_fixedRelElt_fixedOrbitRoots] at hmem
        exact hsign _ hmem
      have hstep := card_reeFixedCellUnipotent_mul (K := K) (a := a) hw (cellLetter k) hpos
      rw [fixedRelElt_mul, hright] at hstep
      rw [hstep, ih _ (hn ▸ hlt) (cellPred k) rfl, card_reeFixedOrbitUnipotent_F4 hK, hexp,
        ← pow_add, add_assoc]

end CellOrders

section Borel

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

open CFSG.SectionRank.LargeRee (simpleChar simpleChar_mul simpleChar_reeTorus reeExp_zero_zero
  reeExp_zero_one reeExp_one_zero reeExp_one_one units_zpow_one_add_mul two_pow_eq_two_mul_sq
  zpow_mul_zpow_zpow)
open CFSG.LieType.Ree.LargeReeCover (f4i torusPair torusPair_eq_reeTorus torusPair_mem_reeGamma)

omit [CharP K F4.prime] in
theorem torusPair_injective (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Injective (torusPair (K := K) a) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  set e : ℤ := ((F4.prime ^ a : ℕ) : ℤ) with he
  have hq : (Nat.card K : ℤ) = 2 * e ^ 2 := by
    rw [hK]
    exact two_pow_eq_two_mul_sq a
  have hx : F4.reeTorus a (f4i 0) u * F4.reeTorus a (f4i 1) v =
      F4.reeTorus a (f4i 0) u' * F4.reeTorus a (f4i 1) v' :=
    Subtype.ext (by rw [← torusPair_eq_reeTorus, ← torusPair_eq_reeTorus]; exact h)
  have c0 := congrArg (fun g => simpleChar g (f4i 0)) hx
  have c1 := congrArg (fun g => simpleChar g (f4i 1)) hx
  simp only [simpleChar_mul (F4.reeTorus_mem_H a _ _) (F4.reeTorus_mem_H a _ _),
    simpleChar_reeTorus] at c0 c1
  rw [reeExp_zero_zero, reeExp_one_zero, ← Units.val_mul, ← Units.val_mul] at c0
  rw [reeExp_zero_one, reeExp_one_one, ← Units.val_mul, ← Units.val_mul, ← he] at c1
  have c0' := Units.ext c0
  have c1' := Units.ext c1
  have hexp : (4 * e + 3) * (3 - 4 * e) = 1 + (-8) * ((Nat.card K : ℤ) - 1) := by
    rw [hq]; ring
  have hu : ∀ x y : Kˣ, (x ^ (2 : ℤ) * y ^ (-1 : ℤ)) ^ ((4 * e + 3) * (2 - 2 * e)) *
      (x ^ (-1 : ℤ) * y ^ (2 - 2 * e)) ^ (4 * e + 3) = x := fun x y => by
    rw [zpow_mul_zpow_zpow]
    have e1 : 2 * ((4 * e + 3) * (2 - 2 * e)) + -1 * (4 * e + 3) = (4 * e + 3) * (3 - 4 * e) := by
      ring
    have e2 : -1 * ((4 * e + 3) * (2 - 2 * e)) + (2 - 2 * e) * (4 * e + 3) = 0 := by ring
    rw [e1, e2, zpow_zero, mul_one, hexp, units_zpow_one_add_mul]
  have hv : ∀ x y : Kˣ, (x ^ (2 : ℤ) * y ^ (-1 : ℤ)) ^ (4 * e + 3) *
      (x ^ (-1 : ℤ) * y ^ (2 - 2 * e)) ^ (2 * (4 * e + 3)) = y := fun x y => by
    rw [zpow_mul_zpow_zpow]
    have e1 : 2 * (4 * e + 3) + -1 * (2 * (4 * e + 3)) = 0 := by ring
    have e2 : -1 * (4 * e + 3) + (2 - 2 * e) * (2 * (4 * e + 3)) = (4 * e + 3) * (3 - 4 * e) := by
      ring
    rw [e1, e2, zpow_zero, one_mul, hexp, units_zpow_one_add_mul]
  refine Prod.ext ?_ ?_
  · rw [← hu u v, ← hu u' v', c0', c1']
  · rw [← hv u v, ← hv u' v', c0', c1']

theorem card_reeFixedTorus (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (F4.reeFixedTorus K a) = (Nat.card K - 1) ^ 2 := by
  have hrange : (torusPair (K := K) a).range = F4.reeFixedTorus K a := by
    refine le_antisymm ?_ fun h hh => ?_
    · rintro _ ⟨⟨u, v⟩, rfl⟩
      exact Subgroup.mem_inf.2
        ⟨CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog.torusPair_mem_torusGroup
          u v, torusPair_mem_reeGamma a hK (u, v)⟩
    · obtain ⟨u, v, rfl⟩ := LargeReeInvolution.rankOne_exists_torusPair_eq hK hh
      exact ⟨(u, v), rfl⟩
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective (torusPair_injective hK)).toEquiv,
    Nat.card_prod, Nat.card_units, sq]

theorem card_reeFixedBorel (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (F4.reeFixedBorel K a) = (2 ^ (2 * a + 1)) ^ 12 * (2 ^ (2 * a + 1) - 1) ^ 2 := by
  obtain ⟨hHU, -, huniq, -⟩ := ree_fixed_Bruhat_decomposition F4 a K
  have hbij : Set.BijOn (fun p : ModGL F4.tag K × ModGL F4.tag K => p.1 * p.2)
      ((F4.reeFixedTorus K a : Set (ModGL F4.tag K)) ×ˢ
        (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)))
      (F4.reeFixedBorel K a : Set (ModGL F4.tag K)) := by
    refine ⟨fun p hp => ?_, fun p hp p' hp' h => ?_, fun x hx => ?_⟩
    · rw [hHU]
      exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩
    · obtain ⟨h1, h2⟩ := huniq _ hp.1 _ hp'.1 _ hp.2 _ hp'.2 h
      exact Prod.ext h1 h2
    · rw [hHU] at hx
      obtain ⟨h, hh, u, hu, rfl⟩ := hx
      exact ⟨(h, u), ⟨hh, hu⟩, rfl⟩
  calc Nat.card (F4.reeFixedBorel K a)
      = Nat.card ((F4.reeFixedTorus K a : Set (ModGL F4.tag K)) ×ˢ
          (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K))) :=
        Nat.card_congr hbij.equiv.symm
    _ = Nat.card (F4.reeFixedTorus K a) * Nat.card (F4.reeFixedPosUnipotent K a) := by
        rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
        rfl
    _ = _ := by
        rw [card_reeFixedTorus hK, LargeReeInvolution.card_reeFixedPosUnipotent hK, hK, mul_comm]

end Borel

theorem sum_cellExp (q : ℕ) :
    ∑ k : Fin F4.fixedWeylOrder, q ^ cellExp k =
      1 + q + q ^ 2 + 2 * q ^ 3 + q ^ 4 + q ^ 5 + 2 * q ^ 6 + q ^ 7 + q ^ 8 + 2 * q ^ 9 +
        q ^ 10 + q ^ 11 + q ^ 12 := by
  change ∑ k : Fin 16, q ^ cellExp k = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, cellExp]
  simp
  ring

theorem large_Ree_exact_native_order_and_prime_factor_exhaustion (a : ℕ) (K : Type) [Field K]
    [Finite K] [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (F4.reeGamma K a) =
      (2 ^ (2 * a + 1)) ^ 12 * (2 ^ (2 * a + 1) - 1) ^ 2 * (2 ^ (2 * a + 1) + 1) ^ 2 *
        ((2 ^ (2 * a + 1)) ^ 2 + 1) ^ 2 * ((2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1) *
        ((2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 + 1) ∧
    ∀ p : ℕ, p.Prime → 3 < p → p ∣ Nat.card (F4.reeGamma K a) →
      p ∣ 2 ^ (2 * a + 1) - 1 ∨ p ∣ 2 ^ (2 * a + 1) + 1 ∨ p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 ∨
        p ∣ (2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1 ∨
        p ∣ (2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 + 1 := by
  set q := 2 ^ (2 * a + 1) with hq
  set D : Fin F4.fixedWeylOrder → Set (ModGL F4.tag K) :=
    fun k => F4.reeFixedBruhatCell K a (F4.fixedRelElt k) with hD
  obtain ⟨-, -, -, -, -, -, -, -, hunion, hdisj, hcell, -, -⟩ :=
    ree_fixed_Bruhat_decomposition F4 a K
  have hΓ : (F4.reeGamma K a : Set (ModGL F4.tag K)) = ⋃ k, D k := by
    rw [hunion]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨w, hx⟩
      obtain ⟨k, hk⟩ := exists_fixedRelElt_eq w.2
      exact ⟨k, by rw [hD]; simp only; rw [hk]; exact hx⟩
    · rintro ⟨k, hx⟩
      exact ⟨⟨_, fixedRelElt_mem k⟩, hx⟩
  have hpair : Pairwise (Function.onFun Disjoint D) := fun k k' hkk' =>
    hdisj _ _ fun h => hkk' (fixedRelElt_injective h)
  have hDcard : ∀ k, Nat.card (D k) =
      Nat.card (F4.reeFixedBorel K a) * Nat.card K ^ cellExp k := by
    intro k
    rw [← card_reeFixedCellUnipotent_fixedRelElt hK k,
      Nat.card_congr ((hcell _ (fixedRelElt_mem k)).1.equiv.symm),
      Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
    rfl
  have : ∀ k, Finite (D k) := fun k => Set.toFinite _
  have hcard : Nat.card (F4.reeGamma K a) =
      q ^ 12 * (q - 1) ^ 2 * (1 + q + q ^ 2 + 2 * q ^ 3 + q ^ 4 + q ^ 5 + 2 * q ^ 6 + q ^ 7 +
        q ^ 8 + 2 * q ^ 9 + q ^ 10 + q ^ 11 + q ^ 12) := by
    calc Nat.card (F4.reeGamma K a) = Nat.card (⋃ k, D k) := by
          rw [← hΓ]
          rfl
      _ = ∑ k, Nat.card (D k) := by
          rw [Nat.card_congr (Set.unionEqSigmaOfDisjoint hpair), Nat.card_sigma]
      _ = _ := by
          simp only [hDcard, ← Finset.mul_sum, hK, sum_cellExp, card_reeFixedBorel hK]
          rfl
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hle1 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hle2 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hpoly : 1 + q + q ^ 2 + 2 * q ^ 3 + q ^ 4 + q ^ 5 + 2 * q ^ 6 + q ^ 7 + q ^ 8 +
      2 * q ^ 9 + q ^ 10 + q ^ 11 + q ^ 12 =
      (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) := by
    zify [hle1, hle2]
    ring
  have horder : Nat.card (F4.reeGamma K a) = q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 *
      (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) := by
    rw [hcard, hpoly]
    ring
  refine ⟨horder, fun p hp hp3 hdvd => ?_⟩
  have hpq : ¬ p ∣ q ^ 12 := fun h => by
    have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h))
    omega
  rw [horder] at hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h6
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h5
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h4
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h3
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h2
          · exact absurd h hpq
          · exact Or.inl (hp.dvd_of_dvd_pow h2)
        · exact Or.inr (Or.inl (hp.dvd_of_dvd_pow h3))
      · exact Or.inr (Or.inr (Or.inl (hp.dvd_of_dvd_pow h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h5)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h6)))

end CFSG.RankThree.LargeReeOrder
