module

public import CFSG.Quasithin.Background.A1bHyperplane
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

@[expose] def s16t_blk_Hyp {T : Type} [CommGroup T] (A : Subgroup (MulAut T)) (p : ℕ) :
    Set (Subgroup (MulAut T)) :=
  {B | B ≤ A ∧ Nat.card ↥B * p = Nat.card ↥A ∧ fixV B ≠ ⊥}

private theorem s16t_blk_hyp_fixV_map {T : Type} [CommGroup T] {A : Subgroup (MulAut T)}
    (B : Subgroup ↥A) :
    fixedPointSubgroup B T = fixV (B.map A.subtype) := by
  ext t
  rw [mem_fixV, FixedPoints.mem_subgroup]
  constructor
  · intro h x hx
    obtain ⟨b, hb, rfl⟩ := hx
    simpa [Subgroup.smul_def, MulAut.smul_def] using h ⟨b, hb⟩
  · intro h b
    simpa [Subgroup.smul_def, MulAut.smul_def] using
      h (b : ↥A) (Subgroup.mem_map_of_mem A.subtype b.2)

private theorem s16t_blk_hyp_commutatorAction_eq {T : Type} [CommGroup T]
    {A : Subgroup (MulAut T)} :
    commutatorAction ↥A T = commSub (⊤ : Subgroup T) A := by
  unfold commutatorAction commutatorSubgroup commSub
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨a, h, -, rfl⟩
    exact Subgroup.subset_closure ⟨(a : MulAut T), a.2, h, Subgroup.mem_top _, by
      rw [Subgroup.smul_def, MulAut.smul_def]
      exact mul_comm _ _⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, w, -, rfl⟩
    exact Subgroup.subset_closure ⟨⟨x, hx⟩, w, Subgroup.mem_top _, by
      rw [Subgroup.smul_def, MulAut.smul_def]
      exact mul_comm _ _⟩

theorem s16t_blk_hyperplane_blocks {T : Type} [CommGroup T] [Finite T]
    (hT : ∀ t : T, t ^ 2 = 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A : Subgroup (MulAut T)} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAp : ∀ a ∈ A, a ^ p = 1) (hfix : fixV A = ⊥) :
    iSupIndep (fun B : s16t_blk_Hyp A p => fixV (B : Subgroup (MulAut T))) ∧
      ⨆ B : s16t_blk_Hyp A p, fixV (B : Subgroup (MulAut T)) = ⊤ := by
  classical
  haveI : Finite (MulAut T) := MulEquiv.finite_left
  letI hComm : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with
      mul_comm := fun a b => Subtype.ext (hAc a a.2 b b.2) }
  have hAp' : ∀ a : ↥A, a ^ p = 1 := fun a => Subtype.ext (by
    change (a : MulAut T) ^ p = 1
    exact hAp a a.2)
  have hG : ¬ p ∣ Nat.card T := by
    intro hdvd
    have h2 : p ∣ 2 ^ rk T := by rwa [card_eq_two_pow_rk hT] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow h2))
  have hOddA : Odd (Nat.card ↥A) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp
      (CFSG.Quasithin.A1b.isPGroup_of_pow_eq_one hAp')
    rw [hn]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hcommA : commSub (⊤ : Subgroup T) A = ⊤ := by
    have h := (coprime_decomp (P := A) hOddA hT (W := ⊤)
      (fun _ _ _ _ => Subgroup.mem_top _)).1
    rwa [top_inf_eq, hfix, sup_bot_eq] at h
  have hGA : commutatorAction ↥A T = ⊤ := by
    rw [s16t_blk_hyp_commutatorAction_eq]
    exact hcommA
  let ι := {B : Subgroup ↥A | IsCyclic (↥A ⧸ B) ∧ fixedPointSubgroup B T ≠ ⊥}
  have h117 : IsIndexedDirectProduct (fun B : ι => fixedPointSubgroup B T) :=
    a117_isIndexedDirectProduct hAp' hG hGA
  let F : s16t_blk_Hyp A p → Subgroup T := fun C => fixV (C : Subgroup (MulAut T))
  let toHyp : ι → s16t_blk_Hyp A p := fun B =>
    ⟨B.1.map A.subtype, map_subtype_le B.1, by
      rw [Subgroup.card_subtype A B.1, mul_comm (Nat.card ↥B.1) p,
        ← a117_index_eq hAp' hG hGA B.2.1 B.2.2]
      exact Subgroup.index_mul_card B.1, by
      rw [← s16t_blk_hyp_fixV_map B.1]
      exact B.2.2⟩
  let g : s16t_blk_Hyp A p → ι := fun C =>
    ⟨C.1.subgroupOf A, by
      have hcard : Nat.card ↥(C.1.subgroupOf A) = Nat.card ↥C.1 := by
        rw [← Subgroup.card_subtype A (C.1.subgroupOf A),
          Subgroup.map_subgroupOf_eq_of_le C.2.1]
      have hindex : (C.1.subgroupOf A).index = p := by
        have h1 : (C.1.subgroupOf A).index * Nat.card ↥C.1 = Nat.card ↥A := by
          rw [← hcard]
          exact Subgroup.index_mul_card (C.1.subgroupOf A)
        have h2 : (C.1.subgroupOf A).index * Nat.card ↥C.1 = p * Nat.card ↥C.1 := by
          rw [h1, ← C.2.2.1, mul_comm]
        haveI : Nonempty ↥C.1 := ⟨⟨1, C.1.one_mem⟩⟩
        exact Nat.mul_right_cancel (Nat.card_pos (α := ↥C.1)) h2
      exact isCyclic_of_prime_card (p := p) (α := ↥A ⧸ C.1.subgroupOf A)
        (by rw [← Subgroup.index_eq_card, hindex]), by
      rw [s16t_blk_hyp_fixV_map (C.1.subgroupOf A), Subgroup.map_subgroupOf_eq_of_le C.2.1]
      exact C.2.2.2⟩
  have hg_toHyp : ∀ B : ι, g (toHyp B) = B := fun B => by
    apply Subtype.ext
    exact Subgroup.comap_map_eq_self_of_injective A.subtype_injective B.1
  have htoHyp_g : ∀ C : s16t_blk_Hyp A p, toHyp (g C) = C := fun C => by
    apply Subtype.ext
    exact Subgroup.map_subgroupOf_eq_of_le C.2.1
  have hg_inj : Function.Injective g := fun C C' h => by
    rw [← htoHyp_g C, h, htoHyp_g C']
  have hg_surj : Function.Surjective g := fun B => ⟨toHyp B, hg_toHyp B⟩
  have hF : F = (fun B : ι => fixedPointSubgroup B T) ∘ g := by
    funext C
    show fixV C.1 = fixedPointSubgroup (C.1.subgroupOf A) T
    rw [s16t_blk_hyp_fixV_map (C.1.subgroupOf A), Subgroup.map_subgroupOf_eq_of_le C.2.1]
  have hind : iSupIndep F := by
    rw [hF]
    exact h117.independent.comp hg_inj
  have hsup : ⨆ C : s16t_blk_Hyp A p, F C = ⊤ := by
    have h1 : (⨆ C : s16t_blk_Hyp A p, F C) =
        ⨆ C : s16t_blk_Hyp A p, (fun B : ι => fixedPointSubgroup B T) (g C) :=
      iSup_congr fun C => congrFun hF C
    rw [h1, Function.Surjective.iSup_comp hg_surj (fun B : ι => fixedPointSubgroup B T)]
    exact h117.iSup_eq_top
  exact ⟨hind, hsup⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
