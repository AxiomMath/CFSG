module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2ZGen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87V
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem zSet_cases (h7 : Fan7 F L) (h512 : Fan512 F L) :
    ∀ g ∈ L.zSet 2 α, g = L.z α ∨ (∃ l, g = L.z (D.alpha l)) ∨
      ∃ l, g = L.z (D.alpha l) * L.z α := by
  have h71c : Fan71c F L := h7.2.2.1
  rintro g ⟨δ, hd, hv, rfl⟩
  have hd' : Γ.dist α δ = 0 ∨ Γ.dist α δ = 1 ∨ Γ.dist α δ = 2 := by omega
  rcases hd' with h0 | h1 | h2
  · have hδα : δ = α := (F.isTree.connected.dist_eq_zero_iff.1 h0).symm
    rw [hδα]
    exact Or.inl rfl
  · exfalso
    have := valence_adj_three F D.val (dist_eq_one_iff_adj.1 h1)
    omega
  · obtain ⟨β, hβδ, hαβ⟩ := IsTree.exists_adj_dist_succ F.isTree (u := α) (v := δ) (n := 1) h2
    obtain ⟨l, rfl⟩ := D.exists_beta_eq F h71c (dist_eq_one_iff_adj.1 hαβ)
    obtain ⟨t, hts, hat, hjt⟩ := exists_third_neighbor (D.valence_beta F l)
      (D.adj_start_beta l).symm (D.adj_beta_alpha l) (D.alpha_ne_start l).symm
    have hmem : δ ∈ Γ.neighborSet (D.beta l) := hβδ
    rw [hts] at hmem
    rcases hmem with h1 | h1 | h1
    · exfalso
      rw [h1, SimpleGraph.dist_self] at h2
      omega
    · exact Or.inr (Or.inl ⟨l, by rw [h1]⟩)
    · refine Or.inr (Or.inr ⟨l, ?_⟩)
      rw [h1]
      have h3 := h512.2.2.1 (D.beta l) α (D.alpha l) t (D.valence_beta F l) hts
        (D.alpha_ne_start l).symm hat hjt
      rw [eq_inv_of_mul_eq_one_right h3, mul_inv_rev, L.z_inv (D.valence_alpha F l),
        L.z_inv D.val]

open scoped IsMulCommutative in
theorem zGroup_shapes (h7 : Fan7 F L) (h82 : Fan82a F L) (h512 : Fan512 F L) :
    ∀ ζ ∈ L.zGroup 2 α, ∃ e : Bool, ζ = powB (L.z α) e ∨
      (∃ l, ζ = powB (L.z α) e * L.z (D.alpha l)) ∨
      ∃ a b, a ≠ b ∧ ζ = powB (L.z α) e * (L.z (D.alpha a) * L.z (D.alpha b)) := by
  have h71c : Fan71c F L := h7.2.2.1
  have hcomm := F87.isMulCommutative_zGroup (α := α) h71c
  have hzV : ∀ s, L.z (D.alpha s) ∈ L.zGroup 2 α := fun s =>
    F87.z_mem_zGroup (by rw [D.dist_start_alpha F s]) (D.valence_alpha F s)
  have hzαV : L.z α ∈ L.zGroup 2 α := F87.z_mem_zGroup (by simp) D.val
  let zz : Fin 5 → ↥(L.zGroup 2 α) := fun s => ⟨L.z (D.alpha s), hzV s⟩
  let ww : ↥(L.zGroup 2 α) := ⟨L.z α, hzαV⟩
  have hsq : ∀ s, zz s * zz s = 1 := fun s => Subtype.ext (L.z_mul_self (D.valence_alpha F s))
  have hw : ww * ww = 1 := Subtype.ext (L.z_mul_self D.val)
  have hprod : ∏ s, zz s = 1 := by
    have := h82 α D
    unfold prodFive at this
    apply Subtype.ext
    simpa [Fin.prod_univ_five] using this
  have hmem : ∀ ζ : G, ζ ∈ Subgroup.closure (L.zSet 2 α) → ∀ hz : ζ ∈ L.zGroup 2 α,
      (⟨ζ, hz⟩ : ↥(L.zGroup 2 α)) ∈ Subgroup.closure (Set.range zz ∪ {ww}) := by
    intro ζ hζ
    induction hζ using Subgroup.closure_induction with
    | mem x hx =>
      intro hz
      rcases D.zSet_cases h7 h512 x hx with h1 | ⟨l, h1⟩ | ⟨l, h1⟩
      · have : (⟨x, hz⟩ : ↥(L.zGroup 2 α)) = ww := Subtype.ext h1
        rw [this]
        exact Subgroup.subset_closure (Or.inr rfl)
      · have : (⟨x, hz⟩ : ↥(L.zGroup 2 α)) = zz l := Subtype.ext h1
        rw [this]
        exact Subgroup.subset_closure (Or.inl ⟨l, rfl⟩)
      · have : (⟨x, hz⟩ : ↥(L.zGroup 2 α)) = zz l * ww := Subtype.ext h1
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨l, rfl⟩))
          (Subgroup.subset_closure (Or.inr rfl))
    | one => intro hz; exact one_mem _
    | mul x y hx hy ihx ihy =>
      intro hz
      exact Subgroup.mul_mem _ (ihx hx) (ihy hy)
    | inv x hx ihx =>
      intro hz
      exact Subgroup.inv_mem _ (ihx hx)
  intro ζ hζ
  obtain ⟨e, S, hS, hζe⟩ := exists_normal_form zz ww hsq hw hprod ⟨ζ, hζ⟩ (hmem ζ hζ hζ)
  have hpow : ∀ e : Bool, ((powB ww e : ↥(L.zGroup 2 α)) : G) = powB (L.z α) e := by
    intro e
    cases e <;> simp [powB, ww]
  have hval := congrArg Subtype.val hζe
  rw [Subgroup.coe_mul, hpow] at hval
  refine ⟨e, ?_⟩
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [Finset.card_eq_zero.1 h0] at hval
    exact Or.inl (by simpa using hval)
  · obtain ⟨l, rfl⟩ := Finset.card_eq_one.1 h1
    exact Or.inr (Or.inl ⟨l, by simpa [zz] using hval⟩)
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 h2
    exact Or.inr (Or.inr ⟨a, b, hab, by simpa [zz, Finset.prod_pair hab] using hval⟩)

end D10Set

end CFSG.Quasithin.Fan86
