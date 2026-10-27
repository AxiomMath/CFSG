module

public import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
import CFSG.OddTranspositions.PartThree.Ten.WreathClass
public import CFSG.OddTranspositions.PartThree.Ten.SetupQ
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.RankThree.PartOne.FIS.PermFacts

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

namespace SwapBlocks

open Equiv SemidirectProduct WreathEndgame
open scoped Pointwise

variable {f m : ℕ}

theorem inl_conj_swp (y : Fin m → PSL2Model f) (a : PSL2Model f) {i j : Fin m} (hij : i ≠ j) :
    inl y * swp a i j * (inl y)⁻¹ = swp (y i * a * (y j)⁻¹) i j := by
  set x : L2Wreath f m := inl y * swp a i j * (inl y)⁻¹ with hx
  have hr : x.right = swap i j := by rw [hx, WreathClass.inl_conj_right, swp_right]
  have hl : ∀ p, x.left p = y p * (swp a i j).left p * (y ((swap i j)⁻¹ p))⁻¹ := fun p => by
    rw [hx, WreathClass.inl_conj_left, swp_right]
  have hli : x.left i = y i * a * (y j)⁻¹ := by
    rw [hl, swp_left_fst hij, swap_inv, swap_apply_left]
  have hlj : x.left j = y j * a⁻¹ * (y i)⁻¹ := by
    rw [hl, swp_left_snd hij, swap_inv, swap_apply_right]
  have hlp : ∀ l, l ≠ i → l ≠ j → x.left l = 1 := fun l hli hlj => by
    rw [hl, swp_left_of_ne hli hlj, swap_inv, swap_apply_of_ne_of_ne hli hlj]
    group
  have h := eq_swp hij hr hlp (by rw [hli, hlj]; group)
  rwa [hli] at h

theorem inr_conj_swp (σ : Perm (Fin m)) (a : PSL2Model f) {i j : Fin m} (hij : i ≠ j) :
    inr σ * swp a i j * (inr σ)⁻¹ = swp a (σ i) (σ j) := by
  have hij' : σ i ≠ σ j := σ.injective.ne hij
  set x : L2Wreath f m := inr σ * swp a i j * (inr σ)⁻¹ with hx
  have hr : x.right = swap (σ i) (σ j) := by
    rw [hx, WreathClass.inr_conj_right, swp_right, swap_apply_apply]
  have hl : ∀ p, x.left p = (swp a i j).left (σ⁻¹ p) := fun p => by
    rw [hx, WreathClass.inr_conj_left]
  have hli : x.left (σ i) = a := by rw [hl, show σ⁻¹ (σ i) = i by simp, swp_left_fst hij]
  have hlj : x.left (σ j) = a⁻¹ := by rw [hl, show σ⁻¹ (σ j) = j by simp, swp_left_snd hij]
  have hlp : ∀ l, l ≠ σ i → l ≠ σ j → x.left l = 1 := fun l h1 h2 => by
    rw [hl]
    refine swp_left_of_ne (fun h => h1 ?_) (fun h => h2 ?_)
    · rw [← h]; simp
    · rw [← h]; simp
  have h := eq_swp hij' hr hlp (by rw [hli, hlj])
  rwa [hli] at h

@[expose] def conjStab (B : Set (L2Wreath f m)) : Subgroup (L2Wreath f m) where
  carrier := {w | ∀ x, w * x * w⁻¹ ∈ B ↔ x ∈ B}
  one_mem' x := by simp
  mul_mem' {w w'} hw hw' x := by
    rw [show w * w' * x * (w * w')⁻¹ = w * (w' * x * w'⁻¹) * w⁻¹ by group, hw, hw']
  inv_mem' {w} hw x := by
    have h := hw (w⁻¹ * x * w⁻¹⁻¹)
    rw [show w * (w⁻¹ * x * w⁻¹⁻¹) * w⁻¹ = x by group] at h
    exact h.symm

theorem mem_conjStab {B : Set (L2Wreath f m)} {w : L2Wreath f m} :
    w ∈ conjStab B ↔ ∀ x, w * x * w⁻¹ ∈ B ↔ x ∈ B := Iff.rfl

structure IsSwapBlock (B : Set (L2Wreath f m)) : Prop where
  subset : B ⊆ swapSet f m
  block : ∀ w : L2Wreath f m, ∀ b ∈ B, w * b * w⁻¹ ∈ B → w ∈ conjStab B

section Block

variable {B : Set (L2Wreath f m)}

theorem IsSwapBlock.mem_conjStab_of_conj (hB : IsSwapBlock B) {w b : L2Wreath f m} (hb : b ∈ B)
    (h : w * b * w⁻¹ ∈ B) : w ∈ conjStab B :=
  hB.block w b hb h

theorem IsSwapBlock.self_mem (hB : IsSwapBlock B) {b : L2Wreath f m} (hb : b ∈ B) :
    b ∈ conjStab B :=
  hB.block b b hb (by rwa [mul_inv_cancel_right])

theorem IsSwapBlock.mem_conjStab_of_commute (hB : IsSwapBlock B) {w b : L2Wreath f m}
    (hb : b ∈ B) (h : w * b * w⁻¹ = b) : w ∈ conjStab B :=
  hB.block w b hb (by rw [h]; exact hb)

theorem IsSwapBlock.inr_mem_conjStab (hB : IsSwapBlock B) {a : PSL2Model f} {i j : Fin m}
    (hij : i ≠ j) (hs : swp a i j ∈ B) {τ : Perm (Fin m)} (hi : τ i = i) (hj : τ j = j) :
    inr τ ∈ conjStab B :=
  hB.mem_conjStab_of_commute hs (by rw [inr_conj_swp τ a hij, hi, hj])

theorem mem_stabilizer_pair_iff {σ : Perm (Fin m)} {i j : Fin m} :
    σ ∈ MulAction.stabilizer (Perm (Fin m)) ({i, j} : Set (Fin m)) ↔
      (σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i) := by
  rw [MulAction.mem_stabilizer_iff]
  have h : σ • ({i, j} : Set (Fin m)) = {σ i, σ j} := by
    simp [Set.smul_set_insert, Equiv.Perm.smul_def]
  rw [h, Set.pair_eq_pair_iff]

theorem stab_pair_le_map (hB : IsSwapBlock B) {a : PSL2Model f} {i j : Fin m} (hij : i ≠ j)
    (hs : swp a i j ∈ B) :
    MulAction.stabilizer (Perm (Fin m)) ({i, j} : Set (Fin m)) ≤
      (conjStab B).map (SemidirectProduct.rightHom : L2Wreath f m →* Perm (Fin m)) := by
  intro τ hτ
  rw [mem_stabilizer_pair_iff] at hτ
  rcases hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨inr τ, hB.inr_mem_conjStab hij hs h1 h2, by simp⟩
  · refine ⟨inr (τ * swap i j) * swp a i j, Subgroup.mul_mem _
      (hB.inr_mem_conjStab hij hs ?_ ?_) (hB.self_mem hs), ?_⟩
    · simp [h2]
    · simp [h1]
    · simp [SemidirectProduct.rightHom_eq_right, mul_assoc]

theorem right_eq_of_map_eq (hB : IsSwapBlock B) {a : PSL2Model f} {i j : Fin m} (hij : i ≠ j)
    (hs : swp a i j ∈ B)
    (heq : (conjStab B).map (SemidirectProduct.rightHom : L2Wreath f m →* Perm (Fin m)) =
      MulAction.stabilizer (Perm (Fin m)) ({i, j} : Set (Fin m))) :
    ∀ b ∈ B, b.right = swap i j := by
  intro b hb
  obtain ⟨w, hw⟩ := isConj_iff.1
    ((isConj_of_mem_swapSet hij (hB.subset hs)).symm.trans
      (isConj_of_mem_swapSet hij (hB.subset hb)))
  have hwK : w ∈ conjStab B := hB.mem_conjStab_of_conj hs (hw ▸ hb)
  have hmem : w.right ∈ MulAction.stabilizer (Perm (Fin m)) ({i, j} : Set (Fin m)) := by
    rw [← heq]
    exact ⟨w, hwK, rfl⟩
  rw [mem_stabilizer_pair_iff] at hmem
  rw [← hw, SemidirectProduct.mul_right, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
    swp_right, ← swap_apply_apply]
  rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, swap_comm]

theorem exists_perm_pair {i j p q : Fin m} (hij : i ≠ j) (hpq : p ≠ q) :
    ∃ σ : Perm (Fin m), σ i = p ∧ σ j = q := by
  have hi : Function.Injective ![i, j] := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all
  have hp : Function.Injective ![p, q] := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair ![i, j] ![p, q] hi hp
  exact ⟨σ, hσ 0, hσ 1⟩

theorem exists_swp_mem_of_map_eq_top (hB : IsSwapBlock B) {a : PSL2Model f} {i j : Fin m}
    (hij : i ≠ j) (hs : swp a i j ∈ B)
    (htop : (conjStab B).map (SemidirectProduct.rightHom : L2Wreath f m →* Perm (Fin m)) = ⊤)
    {p q : Fin m} (hpq : p ≠ q) : ∃ c, swp c p q ∈ B := by
  obtain ⟨σ, hσi, hσj⟩ := exists_perm_pair hij hpq
  have hσ : σ ∈ (conjStab B).map
      (SemidirectProduct.rightHom : L2Wreath f m →* Perm (Fin m)) := by
    rw [htop]
    exact Subgroup.mem_top σ
  obtain ⟨g, hg, hgσ⟩ := hσ
  have hxB : g * swp a i j * g⁻¹ ∈ B := (hg _).2 hs
  have hxr : (g * swp a i j * g⁻¹).right = swap p q := by
    rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      swp_right, ← swap_apply_apply]
    have hg' : g.right = σ := hgσ
    rw [hg', hσi, hσj]
  exact ⟨_, (eq_swp_of_right_eq (hB.subset hxB) hpq hxr) ▸ hxB⟩

theorem inl_mem_conjStab (hm : 3 ≤ m) (hB : IsSwapBlock B)
    (hpairs : ∀ p q : Fin m, p ≠ q → ∃ c, swp c p q ∈ B) (y : Fin m → PSL2Model f) :
    inl y ∈ conjStab B := by
  have hsingle : ∀ (p : Fin m) (u : PSL2Model f),
      (inl (Pi.mulSingle p u : Fin m → PSL2Model f) : L2Wreath f m) ∈ conjStab B := by
    intro p u
    obtain ⟨a, ha, -⟩ := CFSG.RankThree.PartOne.FIS.PermFacts.exists_third hm p p
    obtain ⟨b, hb, hba⟩ := CFSG.RankThree.PartOne.FIS.PermFacts.exists_third hm p a
    obtain ⟨c, hc⟩ := hpairs a b hba.symm
    refine hB.mem_conjStab_of_commute hc ?_
    rw [inl_conj_swp _ c hba.symm, Pi.mulSingle_eq_of_ne ha, Pi.mulSingle_eq_of_ne hb]
    simp
  have hmem := Subgroup.noncommProd_mem
    ((conjStab B).comap (inl : (Fin m → PSL2Model f) →* L2Wreath f m))
    (t := Finset.univ) (f := fun p => (Pi.mulSingle p (y p) : Fin m → PSL2Model f))
    (fun i _ j _ _ => Pi.mulSingle_apply_commute y i j) (fun p _ => hsingle p (y p))
  rw [Finset.noncommProd_mulSingle] at hmem
  exact Subgroup.mem_comap.1 hmem

theorem eq_swapSet_of_map_eq_top (hm : 5 ≤ m) (hB : IsSwapBlock B) {a : PSL2Model f}
    {i j : Fin m} (hij : i ≠ j) (hs : swp a i j ∈ B)
    (htop : (conjStab B).map (SemidirectProduct.rightHom : L2Wreath f m →* Perm (Fin m)) = ⊤) :
    B = swapSet f m := by
  have hbase := inl_mem_conjStab (by omega) hB
    (fun p q hpq => exists_swp_mem_of_map_eq_top hB hij hs htop hpq)
  refine Set.Subset.antisymm hB.subset fun x hx => ?_
  obtain ⟨p, q, hpq, hxr, -⟩ := id hx
  obtain ⟨c', rfl⟩ : ∃ c', x = swp c' p q := ⟨_, eq_swp_of_right_eq hx hpq hxr⟩
  obtain ⟨c, hc⟩ := exists_swp_mem_of_map_eq_top hB hij hs htop hpq
  have h1 : inl (Pi.mulSingle p (c' * c⁻¹) : Fin m → PSL2Model f) * swp c p q *
      (inl (Pi.mulSingle p (c' * c⁻¹) : Fin m → PSL2Model f))⁻¹ = swp c' p q := by
    rw [inl_conj_swp _ c hpq, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hpq.symm]
    simp
  rw [← h1]
  exact (hbase _ _).2 hc

@[expose] noncomputable def coordStab (B : Set (L2Wreath f m)) (i : Fin m) :
    Subgroup (PSL2Model f) :=
  (conjStab B).comap (SetupQ.coordHom f m i)

theorem mem_coordStab_iff (hB : IsSwapBlock B) {a : PSL2Model f} {i j : Fin m} (hij : i ≠ j)
    (hs : swp a i j ∈ B) (x : PSL2Model f) : x ∈ coordStab B i ↔ swp (x * a) i j ∈ B := by
  have h1 : SetupQ.coordHom f m i x * swp a i j * (SetupQ.coordHom f m i x)⁻¹ =
      swp (x * a) i j := by
    rw [SetupQ.coordHom_apply, inl_conj_swp _ a hij, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne hij.symm]
    simp
  constructor
  · intro hx
    rw [← h1]
    exact (mem_conjStab.1 hx _).2 hs
  · intro hx
    exact hB.mem_conjStab_of_conj hs (h1 ▸ hx)

theorem normal_coordStab (hB : IsSwapBlock B) {a : PSL2Model f} {i j : Fin m} (hij : i ≠ j)
    (hs : swp a i j ∈ B) : (coordStab B i).Normal := by
  refine ⟨fun x hx y => ?_⟩
  have hx' : SetupQ.coordHom f m i x ∈ conjStab B := hx
  set dy : Fin m → PSL2Model f := Pi.mulSingle i y * Pi.mulSingle j (a⁻¹ * y * a) with hdy
  have hδ : (inl dy : L2Wreath f m) ∈ conjStab B := by
    refine hB.mem_conjStab_of_commute hs ?_
    have hi : dy i = y := by simp [hdy, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij]
    have hj : dy j = a⁻¹ * y * a := by
      simp [hdy, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.symm]
    rw [inl_conj_swp _ a hij, hi, hj]
    congr 1
    group
  have hfun : dy * Pi.mulSingle i x * dy⁻¹ = Pi.mulSingle i (y * x * y⁻¹) := by
    funext p
    by_cases hpi : p = i
    · rw [hpi]
      simp [hdy, Pi.mulSingle_eq_of_ne hij]
    · by_cases hpj : p = j
      · rw [hpj]
        simp [hdy, Pi.mulSingle_eq_of_ne hij.symm]
      · simp [hdy, Pi.mulSingle_eq_of_ne hpi, Pi.mulSingle_eq_of_ne hpj]
  have hconj : (inl dy : L2Wreath f m) * SetupQ.coordHom f m i x * (inl dy)⁻¹ =
      SetupQ.coordHom f m i (y * x * y⁻¹) := by
    rw [SetupQ.coordHom_apply, SetupQ.coordHom_apply, ← map_inv, ← map_mul, ← map_mul, hfun]
  have hmem : (inl dy : L2Wreath f m) * SetupQ.coordHom f m i x * (inl dy)⁻¹ ∈ conjStab B :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hδ hx') (Subgroup.inv_mem _ hδ)
  rw [hconj] at hmem
  exact hmem

theorem eq_singleton_or_sameSwaps (hf : 2 ≤ f) (hB : IsSwapBlock B) {a : PSL2Model f}
    {i j : Fin m} (hij : i ≠ j) (hs : swp a i j ∈ B) (hsup : ∀ b ∈ B, b.right = swap i j) :
    B = {swp a i j} ∨ B = sameSwaps f m (swap i j) := by
  have : IsSimpleGroup (PSL2Model f) :=
    IsBenderGroup.isSimpleGroup (IsBenderGroup.isPSL2 f hf (MulEquiv.refl _))
  have hTnormal := normal_coordStab hB hij hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (coordStab B i) with hbot | htop
  · left
    refine Set.eq_singleton_iff_unique_mem.2 ⟨hs, fun b hb => ?_⟩
    obtain ⟨c, rfl⟩ : ∃ c, b = swp c i j :=
      ⟨_, eq_swp_of_right_eq (hB.subset hb) hij (hsup b hb)⟩
    have hx : c * a⁻¹ ∈ coordStab B i := by
      rw [mem_coordStab_iff hB hij hs]
      simpa using hb
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hx
    rw [hx]
  · right
    refine Set.Subset.antisymm (fun b hb => ⟨hB.subset hb, hsup b hb⟩) fun b hb => ?_
    obtain ⟨c, rfl⟩ : ∃ c, b = swp c i j := ⟨_, eq_swp_of_right_eq hb.1 hij hb.2⟩
    have hx : c * a⁻¹ ∈ coordStab B i := by rw [htop]; exact Subgroup.mem_top _
    rw [mem_coordStab_iff hB hij hs] at hx
    simpa using hx

theorem swap_block_trichotomy (hf : 2 ≤ f) (hm : 5 ≤ m) {B : Set (L2Wreath f m)}
    (hB : IsSwapBlock B) {s : L2Wreath f m} (hs : s ∈ B) {i j : Fin m} (hij : i ≠ j)
    (hsr : s.right = swap i j) :
    B = {s} ∨ B = sameSwaps f m (swap i j) ∨ B = swapSet f m := by
  obtain ⟨a, rfl⟩ : ∃ a, s = swp a i j :=
    ⟨s.left i, eq_swp_of_right_eq (hB.subset hs) hij hsr⟩
  have hcoatom : IsCoatom (MulAction.stabilizer (Perm (Fin m)) ({i, j} : Set (Fin m))) := by
    refine Equiv.Perm.isCoatom_stabilizer ⟨i, by simp⟩ ?_ ?_
    · obtain ⟨k, hki, hkj, -⟩ :=
        CFSG.RankThree.PartOne.FIS.PermFacts.exists_fourth (by omega : 4 ≤ m) i j i
      exact ⟨k, by simp [hki, hkj]⟩
    · rw [Set.ncard_pair hij, Nat.card_fin]
      omega
  rcases hcoatom.le_iff.1 (stab_pair_le_map hB hij hs) with htop | heq
  · exact Or.inr (Or.inr (eq_swapSet_of_map_eq_top hm hB hij hs htop))
  · rcases eq_singleton_or_sameSwaps hf hB hij hs (right_eq_of_map_eq hB hij hs heq) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end Block

end SwapBlocks

end CFSG.OddTranspositions.PartThree

end
