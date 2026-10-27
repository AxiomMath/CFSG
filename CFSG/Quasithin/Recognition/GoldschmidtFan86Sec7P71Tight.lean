module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Cnt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Val
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TSlide

public section

namespace CFSG.Quasithin.Fan86

namespace P71

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem R_tight (F : FanTree Γ G) (R : Arc Γ 8) (h5 : Fan86.valence Γ (R.vert 4) = 5) {x : G}
    (hcent : ∀ g ∈ R.stab G, g * x = x * g)
    (hK : (Subgroup.centralizer ({x} : Set G)).relIndex (nbrStab Γ G (R.vert 4)) = 2 ^ 8) :
    RightTransitive Γ G R.vert 3 5 ∧ RightTransitive Γ G R.vert 3 6 ∧
      RightTransitive Γ G R.vert 3 7 ∧ LeftTransitive Γ G R.vert 3 8 ∧
      LeftTransitive Γ G R.vert 2 8 ∧ LeftTransitive Γ G R.vert 1 8 := by
  have hv := fun i hi => valence_arc F R (by norm_num) h5 i hi
  have v1 : Fan86.valence Γ (R.vert 1) = 3 := (hv 1 (by norm_num)).2 (by norm_num)
  have v2 : Fan86.valence Γ (R.vert 2) = 5 := (hv 2 (by norm_num)).1 (by norm_num)
  have v3 : Fan86.valence Γ (R.vert 3) = 3 := (hv 3 (by norm_num)).2 (by norm_num)
  have v5 : Fan86.valence Γ (R.vert 5) = 3 := (hv 5 (by norm_num)).2 (by norm_num)
  have v6 : Fan86.valence Γ (R.vert 6) = 5 := (hv 6 (by norm_num)).1 (by norm_num)
  have v7 : Fan86.valence Γ (R.vert 7) = 3 := (hv 7 (by norm_num)).2 (by norm_num)
  have hKa : ∀ m ∈ nbrStab Γ G (R.vert 4), m • R.vert 4 = R.vert 4 := fun m hm =>
    MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hm)
  have hKb : ∀ m ∈ nbrStab Γ G (R.vert 4), m • R.vert (4 + 1) = R.vert (4 + 1) := fun m hm =>
    mem_nbrStab.1 hm _ (R.adj 4 (by norm_num))
  have hadj : ∀ i, 4 ≤ i → i ≤ 4 + 3 → Γ.Adj (R.vert i) (R.vert (i + 1)) :=
    fun i _ h => R.adj i (by omega)
  have hnb : ∀ i, 4 ≤ i → i < 4 + 3 → R.vert i ≠ R.vert (i + 2) :=
    fun i _ h => R.nb i (by omega)
  have hb1 := chain_bound F R.vert 4 3 hadj hnb hKa hKb
  rw [prod_valence_chain R.vert 4 v5 v6 v7] at hb1
  have hr : ∀ i, R.rev.vert i = R.vert (8 - i) := fun i => Arc.rev_vert R i
  have hP3K : chainGp R.vert 4 (nbrStab Γ G (R.vert 4)) 3 ≤ nbrStab Γ G (R.vert 4) :=
    chainGp_le _ _ _ _
  have hMa : ∀ m ∈ chainGp R.vert 4 (nbrStab Γ G (R.vert 4)) 3, m • R.rev.vert 4 = R.rev.vert 4 :=
    fun m hm => by rw [hr]; exact hKa m (hP3K hm)
  have hMb : ∀ m ∈ chainGp R.vert 4 (nbrStab Γ G (R.vert 4)) 3,
      m • R.rev.vert (4 + 1) = R.rev.vert (4 + 1) := fun m hm => by
    rw [hr]; exact mem_nbrStab.1 (hP3K hm) _ (R.adj 3 (by norm_num)).symm
  have hadjr : ∀ i, 4 ≤ i → i ≤ 4 + 3 → Γ.Adj (R.rev.vert i) (R.rev.vert (i + 1)) :=
    fun i _ h => R.rev.adj i (by omega)
  have hnbr : ∀ i, 4 ≤ i → i < 4 + 3 → R.rev.vert i ≠ R.rev.vert (i + 2) :=
    fun i _ h => R.rev.nb i (by omega)
  have hb2 := chain_bound F R.rev.vert 4 3 hadjr hnbr hMa hMb
  rw [prod_valence_chain R.rev.vert 4 (by rw [hr]; exact v3) (by rw [hr]; exact v2)
    (by rw [hr]; exact v1)] at hb2
  set K := nbrStab Γ G (R.vert 4) with hKdef
  set P3 := chainGp R.vert 4 K 3 with hP3
  set P6 := chainGp R.rev.vert 4 P3 3 with hP6
  have hP63 : P6 ≤ P3 := chainGp_le _ _ _ _
  have hP6fix : P6 ≤ R.stab G := by
    intro g hg
    rw [Arc.mem_stab]
    intro i hi
    by_cases h4 : 4 ≤ i
    · exact fix_of_mem_chainGp R.vert 4 hKa hKb 3 g (hP63 hg) i h4 (by omega)
    · have := fix_of_mem_chainGp R.rev.vert 4 hMa hMb 3 g hg (8 - i) (by omega) (by omega)
      rwa [hr, show 8 - (8 - i) = i by omega] at this
  have hCle : P6 ≤ Subgroup.centralizer ({x} : Set G) ⊓ K := by
    intro g hg
    refine Subgroup.mem_inf.2 ⟨?_, (hP63.trans hP3K) hg⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact (hcent g (hP6fix hg)).symm
  have hfinK : Finite K := finite_nbrStab F _
  have hrel : P6.relIndex P3 * P3.relIndex K = P6.relIndex K :=
    Subgroup.relIndex_mul_relIndex P6 P3 K hP63 hP3K
  have hlow : 2 ^ 8 ≤ P6.relIndex K := by
    have h1 := Subgroup.relIndex_mul_relIndex P6 (Subgroup.centralizer ({x} : Set G) ⊓ K) K hCle
      inf_le_right
    rw [Subgroup.inf_relIndex_right, hK] at h1
    have hfin2 : Finite ↥(Subgroup.centralizer ({x} : Set G) ⊓ K) :=
      Finite.of_injective (Subgroup.inclusion (inf_le_right : _ ≤ K))
        (Subgroup.inclusion_injective _)
    have h2 : P6.relIndex (Subgroup.centralizer ({x} : Set G) ⊓ K) ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    rw [← h1]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h2)
  obtain ⟨e1, e2⟩ := eq_of_mul_ge hb2 hb1 (by norm_num) (by norm_num) (by omega)
  have htr1 := chain_trans F R.vert 4 3 hadj hnb hKa hKb
    (by rw [prod_valence_chain R.vert 4 v5 v6 v7, ← hP3]; omega)
  have htr2 := chain_trans F R.rev.vert 4 3 hadjr hnbr hMa hMb
    (by rw [prod_valence_chain R.rev.vert 4 (by rw [hr]; exact v3) (by rw [hr]; exact v2)
      (by rw [hr]; exact v1), ← hP6]; omega)
  have hfixK3 : ∀ m ∈ K, m • R.vert 3 = R.vert 3 := fun m hm =>
    mem_nbrStab.1 hm _ (R.adj 3 (by norm_num)).symm
  have fixR : ∀ j g, g ∈ chainGp R.vert 4 K j → ∀ i, 3 ≤ i → i ≤ 5 + j →
      g • R.vert i = R.vert i := by
    intro j g hg i h1 h2
    by_cases h3 : i = 3
    · subst h3; exact hfixK3 g (chainGp_le _ _ _ _ hg)
    · exact fix_of_mem_chainGp R.vert 4 hKa hKb j g hg i (by omega) (by omega)
  have fixL : ∀ j g, g ∈ chainGp R.rev.vert 4 P3 j → ∀ i, 3 - j ≤ i → i ≤ 8 →
      g • R.vert i = R.vert i := by
    intro j g hg i h1 h2
    by_cases h4 : 4 ≤ i
    · exact fix_of_mem_chainGp R.vert 4 hKa hKb 3 g (chainGp_le _ _ _ _ hg) i h4 (by omega)
    · have := fix_of_mem_chainGp R.rev.vert 4 hMa hMb j g hg (8 - i) (by omega) (by omega)
      rwa [hr, show 8 - (8 - i) = i by omega] at this
  have hR : ∀ j, j < 3 → RightTransitive Γ G R.vert 3 (5 + j) := by
    intro j hj a b ha hau hb hbu
    refine layer_trans (S := stabRange G R.vert 3 (5 + j)) (P := chainGp R.vert 4 K j)
      (fun g hg => mem_stabRange.2 fun i h1 h2 => fixR j g hg i h1 h2)
      (fun y hy hyu => htr1 j hj y hy hyu) a b ha ?_ hb ?_
    · simpa using hau
    · simpa using hbu
  have hL : ∀ j, j < 3 → LeftTransitive Γ G R.vert (3 - j) 8 := by
    intro j hj a b ha hau hb hbu
    refine layer_trans (S := stabRange G R.vert (3 - j) 8) (P := chainGp R.rev.vert 4 P3 j)
      (fun g hg => mem_stabRange.2 fun i h1 h2 => fixL j g hg i h1 h2)
      (fun y hy hyu => htr2 j hj y hy hyu) a b ?_ ?_ ?_ ?_
    · rw [hr, show 8 - (4 + 1 + j) = 3 - j by omega]; exact ha
    · rw [hr, show 8 - (4 + j) = 3 - j + 1 by omega]; exact hau
    · rw [hr, show 8 - (4 + 1 + j) = 3 - j by omega]; exact hb
    · rw [hr, show 8 - (4 + j) = 3 - j + 1 by omega]; exact hbu
  exact ⟨hR 0 (by norm_num), hR 1 (by norm_num), hR 2 (by norm_num), hL 0 (by norm_num),
    hL 1 (by norm_num), hL 2 (by norm_num)⟩

end P71

end CFSG.Quasithin.Fan86
