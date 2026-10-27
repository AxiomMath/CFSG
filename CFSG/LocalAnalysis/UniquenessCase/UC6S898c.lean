module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S898a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S898

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.UC6S846

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_of_card_prime {X : Subgroup G} {r : ℕ} (hr : r.Prime) (hX : Nat.card X = r) :
    IsElemAbelian r X := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : IsCyclic ↥X := isCyclic_of_prime_card (p := r) hX
  refine ⟨inferInstance, fun x hx => ?_⟩
  have : (⟨x, hx⟩ : ↥X) ^ Nat.card ↥X = 1 := pow_card_eq_one'
  rw [hX] at this
  simpa using congrArg Subtype.val this

theorem normalizes_of_rank_lt_four {M L : Subgroup G} (hL : L ∈ calC M) {y : G} (hy : y ∈ M) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hyr : orderOf y = r) {X : Subgroup G} (hXL : X ≤ L)
    (hXc : Nat.card X = r) (hZ : ¬ r ∣ Nat.card (center (Bar2 L))) (hrank : Open.pRank r M ≤ 3) :
    y ∈ normalizer (L : Set G) := by
  classical
  by_contra hyn
  have hr2 : r ≠ 2 := by omega
  let f : ℕ → MulAut G := fun i => MulAut.conj (y ^ i)
  have hM : ∀ i, M.map (f i).toMonoidHom = M := fun i =>
    mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer (M.pow_mem hy i))
  have hLi : ∀ i, L.map (f i).toMonoidHom ∈ calC M := fun i => calC_map M (f i) (hM i) hL
  have hLM : L ≤ M := hL.1.le
  have hLiM : ∀ i, L.map (f i).toMonoidHom ≤ M := fun i => (hLi i).1.le
  have hdist : ∀ i j : ℕ, i < j → j < 4 → L.map (f i).toMonoidHom ≠ L.map (f j).toMonoidHom := by
    intro i j hij hj4 heq
    have hcomp : f j = f i * f (j - i) := by
      show MulAut.conj (y ^ j) = MulAut.conj (y ^ i) * MulAut.conj (y ^ (j - i))
      rw [← map_mul, ← pow_add]
      congr 2
      omega
    have h1 : L.map (f j).toMonoidHom = (L.map (f (j - i)).toMonoidHom).map (f i).toMonoidHom := by
      rw [hcomp, Subgroup.map_map]
      rfl
    rw [h1] at heq
    have h2 : L = L.map (f (j - i)).toMonoidHom :=
      Subgroup.map_injective (f i).injective heq
    have hk : y ^ (j - i) ∈ normalizer (L : Set G) := mem_normalizer_iff_map_conj.2 h2.symm
    have hk3 : 0 < j - i ∧ j - i < 4 := by omega
    have hcop : Nat.Coprime (j - i) r := by
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hr).2 (fun hd => by
        have := Nat.le_of_dvd hk3.1 hd
        omega)
    obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime (x := y) (n := j - i) (by rw [hyr]; exact hcop)
    have hyt : y = (y ^ (j - i)) ^ t := ht.symm
    apply hyn
    rw [hyt]
    exact (Subgroup.normalizer _).pow_mem hk t
  have hXel : IsElemAbelian r X := isElemAbelian_of_card_prime hr hXc
  have hEi : ∀ i, (X.map (f i).toMonoidHom) ≤ L.map (f i).toMonoidHom := fun i => Subgroup.map_mono hXL
  have hcalC := fun i => calC_subgroupOf (hLi i)
  obtain ⟨W, hWel, hWcard⟩ := rank_sum_of_family (Y := ↥M) (ι := Fin 4)
    (A := fun i => (L.map (f (i : ℕ)).toMonoidHom).subgroupOf M)
    (E := fun i => (X.map (f (i : ℕ)).toMonoidHom).subgroupOf M) (q := r) (a := fun _ => 1) hr hr2
    (fun i => (hcalC (i : ℕ)).1) (fun i => (hcalC (i : ℕ)).2.1) (fun i => (hcalC (i : ℕ)).2.2.1)
    (by
      intro i j hij
      by_contra hne
      have hne' : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
      have hmap := congrArg (Subgroup.map M.subtype) hij
      rw [Subgroup.map_subgroupOf_eq_of_le (hLiM i), Subgroup.map_subgroupOf_eq_of_le (hLiM j)] at hmap
      rcases Nat.lt_or_gt_of_ne hne' with hlt | hgt
      · exact hdist i j hlt j.2 hmap
      · exact hdist j i hgt i.2 hmap.symm)
    (fun i => by
      rw [(hcalC (i : ℕ)).2.2.2, card_center_bar2_map]
      exact hZ)
    (fun i x hx => hEi i hx) (fun i => (hXel.map _).subgroupOf M)
    (fun i => by
      have hEM : X.map (f i).toMonoidHom ≤ M := (hEi i).trans (hLiM i)
      show Nat.card ((X.map (f (i : ℕ)).toMonoidHom).subgroupOf M) = r ^ 1
      rw [pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv,
        Subgroup.card_map_of_injective (f i).injective, hXc])
    Finset.univ
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin 4)), (fun _ : Fin 4 => 1) i) = 4 := by simp
  rw [hsum] at hWcard
  have h4 := le_pRank' hr (E := W.map M.subtype) (H := M) (Subgroup.map_subtype_le W)
    (hWel.map _) (by rw [Subgroup.card_map_of_injective M.subtype_injective, hWcard])
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC6S898
