module

public import CFSG.RankThree.PartOne.KD4T.InjBasic
public import CFSG.RankThree.PartOne.KE6.E6LEmb

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
open CFSG.RankThree.PartOne.KD4T

@[expose] def e6Set (τ : Tag) : Set (Fin τ.rank) := {i | i.val < Tag.E6.rank}

noncomputable instance e6SetFintype (τ : Tag) : Fintype (e6Set τ) := Fintype.ofFinite _

theorem e6Set_lt {τ : Tag} {i : Fin τ.rank} (hi : i ∈ e6Set τ) : i.val < Tag.E6.rank := hi

theorem e6Set_lt' {τ : Tag} : ∀ i ∈ e6Set τ, i.val < Tag.E6.rank := fun _ hi => hi

theorem e6Idx_mem_e6Set {τ : Tag} [E6Sub τ] (k : Fin Tag.E6.rank) : e6Idx (τ := τ) k ∈ e6Set τ :=
  k.2

theorem reflect_m27Root_E7 : ∀ a : Fin e6Data.d, ∀ j : Fin Tag.E6.rank,
    reflect Tag.E7 (e6Idx j) (m27Root Tag.E7 a) = m27RootN Tag.E7 (e6Data.weyl a j) := by
  decide +kernel

theorem reflect_m27Root_E8 : ∀ a : Fin e6Data.d, ∀ j : Fin Tag.E6.rank,
    reflect Tag.E8 (e6Idx j) (m27Root Tag.E8 a) = m27RootN Tag.E8 (e6Data.weyl a j) := by
  decide +kernel

theorem reflect_m27Root {τ : Tag} [M27Ok τ] [E6Sub τ] (a : Fin e6Data.d) (j : Fin Tag.E6.rank) :
    reflect τ (e6Idx j) (m27Root τ a) = m27Root τ ⟨e6Data.weyl a j, e6Data_weyl_lt a j⟩ := by
  rcases M27Ok.isE7E8 (τ := τ) with rfl | rfl
  · exact reflect_m27Root_E7 a j
  · exact reflect_m27Root_E8 a j

theorem exists_wt_neg_one : ∀ k : Fin Tag.E6.rank, ∃ a : Fin e6Data.d, e6wt a k.val = -1 := by
  decide +kernel

section Weyl

variable {τ : Tag} [M27Ok τ] [E6Sub τ]

theorem exists_smul_m27Root_aux {v : WeylGroup τ} (hv : v ∈ parabolicWeylGroup τ (e6Set τ)) :
    (∀ a, ∃ b, v • m27Root τ a = m27Root τ b) ∧ (∀ a, ∃ b, v⁻¹ • m27Root τ a = m27Root τ b) := by
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) (e6Set_lt hi)
    have hinv : (simple τ (e6Idx k))⁻¹ = simple τ (e6Idx k) := (coxeterSystem τ).inv_simple _
    have h1 : ∀ a, ∃ b, simple τ (e6Idx k) • m27Root τ a = m27Root τ b := fun a =>
      ⟨_, by rw [simple_smul, reflect_m27Root]⟩
    refine ⟨h1, ?_⟩
    rw [hinv]
    exact h1
  | one => exact ⟨fun a => ⟨a, one_smul _ _⟩, fun a => ⟨a, by rw [inv_one, one_smul]⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨fun a => ?_, fun a => ?_⟩
    · obtain ⟨b, hb⟩ := hy.1 a
      obtain ⟨c, hc⟩ := hx.1 b
      exact ⟨c, by rw [mul_smul, hb, hc]⟩
    · obtain ⟨b, hb⟩ := hx.2 a
      obtain ⟨c, hc⟩ := hy.2 b
      exact ⟨c, by rw [mul_inv_rev, mul_smul, hb, hc]⟩
  | inv x _ hx => exact ⟨hx.2, fun a => by simpa using hx.1 a⟩

theorem exists_smul_m27Root {v : WeylGroup τ} (hv : v ∈ parabolicWeylGroup τ (e6Set τ))
    (a : Fin e6Data.d) : ∃ b, v • m27Root τ a = m27Root τ b :=
  (exists_smul_m27Root_aux hv).1 a

theorem eq_one_of_smul_m27Root {v : WeylGroup τ} (hv : v ∈ parabolicWeylGroup τ (e6Set τ))
    (h : ∀ a, v • m27Root τ a = m27Root τ a) : v = 1 := by
  refine eq_one_of_fix_of_mem_parabolicWeylGroup hv fun j hj => ?_
  obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) (e6Set_lt hj)
  obtain ⟨a, ha⟩ := exists_wt_neg_one k
  have hs := m27_add_single (τ := τ) a k ha
  have hsub : (Pi.single (e6Idx k) 1 : Fin τ.rank → ℤ) =
      m27Root τ ⟨e6Data.weyl a k, e6Data_weyl_lt a k⟩ - m27Root τ a := by
    rw [hs]
    abel
  rw [hsub, smul_sub, h, h]

end Weyl

section Order

variable {τ : Tag} [M27Ok τ]

theorem eq_self_of_not_precedes (p : Fin e6Data.d → Fin e6Data.d) (hp : Function.Injective p)
    (h : ∀ a, ¬ Label.Precedes (m27Label (τ := τ) a) (m27Label (p a))) : ∀ a, p a = a := by
  classical
  have hle : ∀ a, (m27Label (τ := τ) (p a)).position ≤ (m27Label (τ := τ) a).position := by
    intro a
    by_cases hpa : p a = a
    · rw [hpa]
    · have hne : m27Label (τ := τ) a ≠ m27Label (τ := τ) (p a) := fun he =>
        hpa (m27Label_injective he).symm
      rcases Label.precedes_or_precedes hne with h1 | h1
      · exact absurd h1 (h a)
      · exact (Label.position_lt_position h1).le
  have hbij : Function.Bijective p := ⟨hp, Finite.surjective_of_injective hp⟩
  have hsum : ∑ a, (m27Label (τ := τ) (p a)).position = ∑ a, (m27Label (τ := τ) a).position :=
    Equiv.sum_comp (Equiv.ofBijective p hbij) fun b => (m27Label (τ := τ) b).position
  have heq := (Finset.sum_eq_sum_iff_of_le fun a _ => hle a).1 hsum
  intro a
  by_contra hpa
  have hne : m27Label (τ := τ) a ≠ m27Label (τ := τ) (p a) := fun he =>
    hpa (m27Label_injective he).symm
  rcases Label.precedes_or_precedes hne with h1 | h1
  · exact h a h1
  · exact absurd (heq a (Finset.mem_univ a)) (Nat.ne_of_lt (Label.position_lt_position h1))

end Order

@[expose] def posRoot6List : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1], [0, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 0], [0, 1, 0, 1, 0, 0],
   [1, 0, 1, 0, 0, 0], [0, 0, 0, 1, 1, 1], [0, 0, 1, 1, 1, 0], [0, 1, 0, 1, 1, 0], [0, 1, 1, 1, 0, 0],
   [1, 0, 1, 1, 0, 0], [0, 0, 1, 1, 1, 1], [0, 1, 0, 1, 1, 1], [0, 1, 1, 1, 1, 0], [1, 0, 1, 1, 1, 0],
   [1, 1, 1, 1, 0, 0], [0, 1, 1, 1, 1, 1], [0, 1, 1, 2, 1, 0], [1, 0, 1, 1, 1, 1], [1, 1, 1, 1, 1, 0],
   [0, 1, 1, 2, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 2, 1, 0], [0, 1, 1, 2, 2, 1], [1, 1, 1, 2, 1, 1],
   [1, 1, 2, 2, 1, 0], [1, 1, 1, 2, 2, 1], [1, 1, 2, 2, 1, 1], [1, 1, 2, 2, 2, 1], [1, 1, 2, 3, 2, 1],
   [1, 2, 2, 3, 2, 1]]

@[expose] def posRoot6 (k : Fin 36) : Fin Tag.E6.rank → ℤ := fun i => (posRoot6List.getD k []).getD i 0

theorem posRoot6_isRoot : ∀ k : Fin 36, List.ofFn (posRoot6 k) ∈ Tag.E6.artifactRoots := by
  decide +kernel

theorem posRoot6_pos : ∀ k : Fin 36, 0 < height (τ := Tag.E6) (posRoot6 k) := by
  decide +kernel

theorem posRoot6_complete : ∀ l ∈ Tag.E6.artifactRoots, 0 < l.sum → ∃ k : Fin 36,
    List.ofFn (posRoot6 k) = l := by
  decide +kernel

theorem posRoot6_injective : Function.Injective posRoot6 := by
  decide +kernel

theorem posRoot6_sorted : (List.ofFn posRoot6).Pairwise
    (fun γ δ => height (τ := Tag.E6) γ ≤ height (τ := Tag.E6) δ) := by
  decide +kernel

theorem posRoot6_isRoot' (k : Fin 36) : IsRoot Tag.E6 (posRoot6 k) := by
  rw [isRoot_iff_mem_artifactRoots]
  exact posRoot6_isRoot k

theorem exists_posRoot6 {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (hpos : 0 < height γ) :
    ∃ k, posRoot6 k = γ := by
  rw [isRoot_iff_mem_artifactRoots] at hγ
  have hs : 0 < (List.ofFn γ).sum := by
    rw [List.sum_ofFn]
    exact hpos
  obtain ⟨k, hk⟩ := posRoot6_complete _ hγ hs
  exact ⟨k, List.ofFn_injective hk⟩

section Support

variable {τ : Tag} [hτ : E6Sub τ]

theorem height_e6Lat' (β : Fin Tag.E6.rank → ℤ) : height (e6Lat τ β) = height β := by
  rw [height, height, sum_eq_sum_e6Idx _ (fun i hi => e6Lat_apply_of_le hi)]
  exact Finset.sum_congr rfl fun k _ => e6Lat_apply_e6Idx β k

theorem mem_parabolicRoots_e6Set_iff {γ : Fin τ.rank → ℤ} :
    γ ∈ parabolicRoots τ (e6Set τ) ↔ ∃ γ', IsRoot Tag.E6 γ' ∧ e6Lat τ γ' = γ := by
  constructor
  · rintro ⟨hγ, hz⟩
    have h6 : ∀ i : Fin τ.rank, Tag.E6.rank ≤ i.val → γ i = 0 := fun i hi =>
      hz i (fun hmem => by have := e6Set_lt hmem; omega)
    have hlat : e6Lat τ (fun k => γ (e6Idx k)) = γ := e6Lat_comp_e6Idx h6
    exact ⟨fun k => γ (e6Idx k), isRoot_e6Lat_iff.1 (hlat ▸ hγ), hlat⟩
  · rintro ⟨γ', hγ', rfl⟩
    exact ⟨isRoot_e6Lat_iff.2 hγ', fun i hi => e6Lat_apply_of_le (not_lt.1 hi)⟩

theorem range_e6Lat_posRoot6 :
    Set.range (fun k => e6Lat τ (posRoot6 k)) = parabolicPosRoots τ (e6Set τ) := by
  ext γ
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨mem_parabolicRoots_e6Set_iff.2 ⟨_, posRoot6_isRoot' k, rfl⟩,
      isRoot_e6Lat_iff.2 (posRoot6_isRoot' k), by rw [height_e6Lat']; exact posRoot6_pos k⟩
  · rintro ⟨hΦ, -, hpos⟩
    obtain ⟨γ', hγ', rfl⟩ := mem_parabolicRoots_e6Set_iff.1 hΦ
    rw [height_e6Lat'] at hpos
    obtain ⟨k, rfl⟩ := exists_posRoot6 hγ' hpos
    exact ⟨k, rfl⟩

theorem e6Lat_posRoot6_injective : Function.Injective fun k => e6Lat τ (posRoot6 k) := fun _ _ h =>
  posRoot6_injective (e6Lat_injective h)

end Support

end CFSG.RankThree.PartOne.KE6
