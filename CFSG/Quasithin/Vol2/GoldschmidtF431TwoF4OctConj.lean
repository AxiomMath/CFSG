module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctDefs
public import CFSG.GH74.BNPair.Defs
public import CFSG.Quasithin.Background.Equivariance

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley

@[expose] def octLP (k : ℤ) : List (Fin F4.tag.rank → ℤ) :=
  if k = 1 then largeReeBlockImage ⟨0, by decide⟩ ⟨1, by decide⟩
  else if k = 2 then largeReeBlockImage ⟨2, by decide⟩ ⟨0, by decide⟩
  else if k = 3 then largeReeBlockImage ⟨4, by decide⟩ ⟨1, by decide⟩
  else if k = 4 then largeReeBlockImage ⟨6, by decide⟩ ⟨0, by decide⟩
  else if k = 5 then largeReeBlockImage ⟨5, by decide⟩ ⟨1, by decide⟩
  else if k = 6 then largeReeBlockImage ⟨3, by decide⟩ ⟨0, by decide⟩
  else if k = 7 then largeReeBlockImage ⟨1, by decide⟩ ⟨1, by decide⟩
  else if k = 8 then largeReeBlockImage ⟨0, by decide⟩ ⟨0, by decide⟩
  else []

@[expose] def octL (k : ℤ) : List (Fin F4.tag.rank → ℤ) :=
  if 0 < k then octLP k else (octLP (-k)).map Neg.neg

@[expose] def octKeys : List ℤ := [1, 2, 3, 4, 5, 6, 7, 8, -1, -2, -3, -4, -5, -6, -7, -8]

theorem mem_octKeys_iff {k : ℤ} : k ∈ octKeys ↔ (1 ≤ k ∧ k ≤ 8) ∨ (-8 ≤ k ∧ k ≤ -1) := by
  simp only [octKeys, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem subgroupOf_map_conj {G : Type*} [Group G] (Γ X : Subgroup G) (n : Γ) :
    (X.subgroupOf Γ).map (MulAut.conj n).toMonoidHom =
      (X.map (MulAut.conj (n : G)).toMonoidHom).subgroupOf Γ := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x : G), hx, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    have hx' : x = (n : G)⁻¹ * (y : G) * n := by
      rw [← hxy]
      change x = (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * n
      group
    refine ⟨(n⁻¹ * y * n : Γ), ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hx']
      exact hx
    · apply Subtype.ext
      change (n : G) * ((n : G)⁻¹ * (y : G) * n) * (n : G)⁻¹ = y
      group

theorem fixedRelElt_zero : F4.fixedRelElt (⟨0, by decide⟩ : Fin F4.fixedWeylOrder) = 1 := rfl

theorem octBlock_pos {k : ℤ} (hk : 0 < k) : octBlock k = octPos k := by
  simp [octBlock, hk]

theorem octBlock_neg {k : ℤ} (hk : 0 < k) : octBlock (-k) = Neg.neg '' octPos k := by
  have : ¬ 0 < -k := by omega
  simp only [octBlock, this, ite_false, neg_neg]

theorem octPos_one : octPos 1 = F4.fixedOrbitRoots (⟨1, by decide⟩ : Fin F4.fixedOrbitCount) := by
  simp [octPos, octBlk, fixedRelElt_zero]

theorem octPos_eight : octPos 8 = F4.fixedOrbitRoots (⟨0, by decide⟩ : Fin F4.fixedOrbitCount) := by
  simp [octPos, octBlk, fixedRelElt_zero]

theorem height_octLP_pos : ∀ k ∈ [1, 2, 3, 4, 5, 6, 7, 8], ∀ x ∈ octLP k, 0 < height x := by
  decide +kernel

theorem subgroupOf_mono' {G : Type*} [Group G] {Γ X Y : Subgroup G} (h : X ≤ Y) :
    X.subgroupOf Γ ≤ Y.subgroupOf Γ := fun _ hx => Subgroup.mem_subgroupOf.2
  (h (Subgroup.mem_subgroupOf.1 hx))

theorem octLP_ne_nil : ∀ k ∈ [1, 2, 3, 4, 5, 6, 7, 8], octLP k ≠ [] := by
  decide +kernel

theorem octL_table : ∀ k ∈ octKeys, ∃ i : Fin 16,
    octL k ⊆ largeReeBlockTable i ∧ largeReeBlockTable i ⊆ octL k := by
  decide +kernel

@[expose] def zAct (j : Fin F4.fixedOrbitCount) (v : Fin F4.tag.rank → ℤ) :
    Fin F4.tag.rank → ℤ :=
  (F4.fixedOrbitWord j).foldr (reflect F4.tag) v

@[expose] def octSig₁ (k : ℤ) : ℤ :=
  if k = 1 then -1 else if k = -1 then 1 else if 0 < k then 10 - k else -(10 + k)

@[expose] def octSig₂ (k : ℤ) : ℤ :=
  if k = 8 then -8 else if k = -8 then 8 else if 0 < k then 8 - k else -(8 + k)

theorem octKeys_of_pos {k : ℤ} (h1 : 1 ≤ k) (h8 : k ≤ 8) : k ∈ octKeys :=
  mem_octKeys_iff.2 (Or.inl ⟨h1, h8⟩)

theorem octKeys_of_neg {k : ℤ} (h1 : 1 ≤ k) (h8 : k ≤ 8) : -k ∈ octKeys :=
  mem_octKeys_iff.2 (Or.inr ⟨by omega, by omega⟩)

theorem octSig₁_pos {i : ℤ} (h : 2 ≤ i) : octSig₁ i = 10 - i := by
  unfold octSig₁
  split_ifs <;> omega

theorem octSig₁_neg {i : ℤ} (h : 2 ≤ i) : octSig₁ (-i) = -(10 - i) := by
  unfold octSig₁
  split_ifs <;> omega

theorem octSig₂_pos {i : ℤ} (h : i ≤ 7) (h1 : 1 ≤ i) : octSig₂ i = 8 - i := by
  unfold octSig₂
  split_ifs <;> omega

theorem octSig₂_neg {i : ℤ} (h : i ≤ 7) (h1 : 1 ≤ i) : octSig₂ (-i) = -(8 - i) := by
  unfold octSig₂
  split_ifs <;> omega

theorem octL_z₂ : ∀ k ∈ octKeys, (octL k).map (zAct ⟨1, by decide⟩) ⊆ octL (octSig₁ k) ∧
    octL (octSig₁ k) ⊆ (octL k).map (zAct ⟨1, by decide⟩) := by
  decide +kernel

theorem octL_z₁ : ∀ k ∈ octKeys, (octL k).map (zAct ⟨0, by decide⟩) ⊆ octL (octSig₂ k) ∧
    octL (octSig₂ k) ⊆ (octL k).map (zAct ⟨0, by decide⟩) := by
  decide +kernel

section Certs


theorem octPos_eq (k : ℤ) : octPos k = {x | x ∈ octLP k} := by
  unfold octPos octLP octBlk
  split_ifs <;> first | exact image_fixedRelElt_fixedOrbitRoots _ _ | (ext x; simp)

theorem octBlock_eq (k : ℤ) : octBlock k = {x | x ∈ octL k} := by
  unfold octBlock octL
  by_cases hk : 0 < k
  · simp only [hk, ite_true]
    exact octPos_eq k
  · simp only [hk, ite_false]
    rw [octPos_eq]
    ext x
    simp [List.mem_map]

theorem octBlock_mem_largeReeBlocks {k : ℤ} (hk : k ∈ octKeys) : octBlock k ∈ largeReeBlocks := by
  obtain ⟨i, h1, h2⟩ := octL_table k hk
  rw [octBlock_eq, setOf_mem_eq_of_subset h1 h2]
  exact largeReeBlockSet_mem i

theorem isRoot_of_mem_octBlock {k : ℤ} (hk : k ∈ octKeys) {x : Fin F4.tag.rank → ℤ}
    (hx : x ∈ octBlock k) : IsRoot F4.tag x :=
  isRoot_of_mem_largeReeBlocks (octBlock_mem_largeReeBlocks hk) hx

theorem image_smul_octBlock {j : Fin F4.fixedOrbitCount} {k k' : ℤ}
    (h : (octL k).map (zAct j) ⊆ octL k' ∧ octL k' ⊆ (octL k).map (zAct j)) :
    (fun α => F4.fixedOrbitElement j • α) '' octBlock k = octBlock k' := by
  have hz : ∀ α, F4.fixedOrbitElement j • α = zAct j α := fun α =>
    CFSG.LieType.Ree.wordProd_smul (F4.fixedOrbitWord j) α
  rw [octBlock_eq, octBlock_eq]
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, hz]
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact h.1 (List.mem_map.2 ⟨α, hα, rfl⟩)
  · intro hx
    obtain ⟨α, hα, e⟩ := List.mem_map.1 (h.2 hx)
    exact ⟨α, hα, e⟩

section Group

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem largeReeBlockGroup_map_conj {w : WeylGroup F4.tag} (hw : w ∈ F4.relWeylRee)
    {S : Set (Fin F4.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot F4.tag α) :
    (largeReeBlockGroup K a S).map
        (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w)).toMonoidHom =
      largeReeBlockGroup K a ((fun α => w • α) '' S) := by
  have hn : canonicalRep (coxeterSystem F4.tag) K w ∈ F4.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial F4 K a hw).2
  rw [largeReeBlockGroup, largeReeBlockGroup,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    (canonical_weyl_root_transport F4.tag K).1 w S hS,
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]

theorem conjBy_octRoot {w : WeylGroup F4.tag} (hw : w ∈ F4.relWeylRee) {n : Gm K a}
    (hn : (n : ModGL F4.tag K) = canonicalRep (coxeterSystem F4.tag) K w) {k k' : ℤ}
    (hk : k ∈ octKeys) (h : (fun α => w • α) '' octBlock k = octBlock k') :
    CFSG.GH74.BNPair.conjBy n⁻¹ (octRoot K a k) = octRoot K a k' := by
  unfold CFSG.GH74.BNPair.conjBy octRoot
  rw [inv_inv, subgroupOf_map_conj, hn, largeReeBlockGroup_map_conj hw
    (fun α hα => isRoot_of_mem_octBlock hk hα), h]

end Group

end Certs

end CFSG.Quasithin.H13.F431.TwoF4
