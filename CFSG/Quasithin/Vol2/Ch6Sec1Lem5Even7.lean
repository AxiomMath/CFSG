module

public import Certificates.Certificate7250
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCertDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H13.Even7

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.L246C127
open CFSG.QuasithinUnique
open scoped commutatorElement

theorem not_isSolvable_of_perf_ch615 {G : Type*} [Group G] {L : List G} {x y : G}
    {wx wy cx₁ cx₂ cy₁ cy₂ : List ℕ} (hx : evalW L wx = x) (hy : evalW L wy = y)
    (hcx : x = ⁅evalW [x, y] cx₁, evalW [x, y] cx₂⁆)
    (hcy : y = ⁅evalW [x, y] cy₁, evalW [x, y] cy₂⁆)
    (hx1 : x ≠ 1) : ¬ Group.IsSolvable ↥(Subgroup.closure {g | g ∈ L}) := by
  set P := Subgroup.closure {g | g ∈ [x, y]} with hP
  have hxP : x ∈ P := Subgroup.subset_closure (by simp)
  have hPL : P ≤ Subgroup.closure {g | g ∈ L} := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · rw [← hx]
      exact evalW_mem_closure L wx
    · rw [← hy]
      exact evalW_mem_closure L wy
  have hPP : P ≤ ⁅P, P⁆ := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · rw [hcx]
      exact Subgroup.commutator_mem_commutator (evalW_mem_closure _ _) (evalW_mem_closure _ _)
    · rw [hcy]
      exact Subgroup.commutator_mem_commutator (evalW_mem_closure _ _) (evalW_mem_closure _ _)
  have hcomm : ⁅P, P⁆ = P := le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)) hPP
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hcomm
  have : Nontrivial ↥P := ⟨⟨⟨x, hxP⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  intro hsol
  have : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPL)
  exact Group.IsPerfect.not_isSolvable ↥P this

theorem sign_eq_one_of_pow_ch615 {x : Perm (Fin 7)} {k : ℕ} (h : x ^ (2 * k + 1) = 1) :
    Perm.sign x = 1 := by
  have e : x = (x ^ (k + 1)) ^ 2 := by
    rw [← pow_mul, show (k + 1) * 2 = (2 * k + 1) + 1 by ring, pow_succ, h, one_mul]
  rw [e, map_pow]
  exact Int.units_sq _

theorem mGens_pow_ch615 : permOf 7 [[0,1,2]] ^ 3 = 1 ∧ permOf 7 [[0,1,2,3,4,5,6]] ^ 7 = 1 := by
  decide +kernel

theorem tGens_swap_ch615 : permOf 7 [[0,1],[4,5]] = swap 0 1 * swap 4 5 ∧
    permOf 7 [[0,2],[1,3]] = swap 0 2 * swap 1 3 := by
  decide +kernel

theorem mGens_even : ∀ g ∈ mGens, Perm.sign g = 1 := by
  intro g hg
  simp only [mGens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact sign_eq_one_of_pow_ch615 (k := 1) mGens_pow_ch615.1
  · exact sign_eq_one_of_pow_ch615 (k := 3) mGens_pow_ch615.2

theorem tGens_even : ∀ g ∈ tGens, Perm.sign g = 1 := by
  intro g hg
  simp only [tGens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · rw [tGens_swap_ch615.1, map_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
    rfl
  · rw [tGens_swap_ch615.2, map_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
    rfl

theorem closure_le_of_words_ch615 {G : Type*} [Group G] {L L' : List G} (ws : List (List ℕ))
    (h : ws.map (evalW L') = L) : Subgroup.closure {g | g ∈ L} ≤ Subgroup.closure {g | g ∈ L'} := by
  rw [Subgroup.closure_le]
  intro g hg
  rw [← h] at hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact evalW_mem_closure L' w

theorem words_six_ch615 : [[0], [1], [2]].map (evalW L6) = L1 ∧
    [[0], [1], [3, 2]].map (evalW L6) = L2 ∧ [[0], [1], [2, 3]].map (evalW L6) = L3 ∧
    [[0], [1], [3]].map (evalW L6) = L4 := by
  decide +kernel

theorem words_five_ch615 : [[0], [1], [1, 2, 1, 2, 1, 0, 2, 1]].map (evalW L8) = L5 ∧
    [[0], [1], [1, 0, 2, 1, 2, 1, 0, 2, 1]].map (evalW L9) = L5 ∧
    [[0], [1], [2, 1, 0, 1, 2, 2]].map (evalW L10) = L5 ∧
    [[0], [1], [0, 1, 2, 1, 2, 0, 1, 2, 0, 1, 0, 2, 1]].map (evalW L11) = L5 := by
  decide +kernel

theorem sizes_big : ∀ j < 12, 168 ≤ sizes.getD j 0 → 8 ≤ j := by decide +kernel

@[expose] def pg7 : List (Perm (Fin 7)) := [permOf 7 [[0,3,2,6,1]], permOf 7 [[0,2,3,1,6]]]

theorem perf7_ch615 :
    evalW L7 [2,1,0,2,1,0] = pg7.getD 0 1 ∧ evalW L7 [0,2,1,2,1,0,1] = pg7.getD 1 1 ∧
      pg7.getD 0 1 = ⁅evalW pg7 [1], evalW pg7 [1,1,1,0]⁆ ∧
      pg7.getD 1 1 = ⁅evalW pg7 [0], evalW pg7 [0,0,0,1]⁆ ∧
      pg7.getD 0 1 ≠ 1 := by
  decide +kernel

@[expose] def pg8 : List (Perm (Fin 7)) := [permOf 7 [[0,3,4,2,6,5,1]], permOf 7 [[0,6,2,1,3,5,4]]]

theorem perf8_ch615 :
    evalW L8 [1,0,2,1,0,1] = pg8.getD 0 1 ∧ evalW L8 [1,0,2,1,0,2] = pg8.getD 1 1 ∧
      pg8.getD 0 1 = ⁅evalW pg8 [0,0], evalW pg8 [1,1,1,0,0,1]⁆ ∧
      pg8.getD 1 1 = ⁅evalW pg8 [1,1], evalW pg8 [0,0,0,0,1,0]⁆ ∧
      pg8.getD 0 1 ≠ 1 := by
  decide +kernel

@[expose] def pg9 : List (Perm (Fin 7)) := [permOf 7 [[0,1,5,6,3,4,2]], permOf 7 [[0,6,4,3,2,1,5]]]

theorem perf9_ch615 :
    evalW L9 [0,2,2] = pg9.getD 0 1 ∧ evalW L9 [0,2,1,0] = pg9.getD 1 1 ∧
      pg9.getD 0 1 = ⁅evalW pg9 [0,0], evalW pg9 [1,0,0,1,1]⁆ ∧
      pg9.getD 1 1 = ⁅evalW pg9 [1,1], evalW pg9 [0,0,0,1,0]⁆ ∧
      pg9.getD 0 1 ≠ 1 := by
  decide +kernel

@[expose] def pg10 : List (Perm (Fin 7)) := [permOf 7 [[0,4,2,5,3]], permOf 7 [[0,5,2]]]

theorem perf10_ch615 :
    evalW L10 [0,2,1,2,0,1,2,0] = pg10.getD 0 1 ∧ evalW L10 [2,2,1,2,0,1,2,1] = pg10.getD 1 1 ∧
      pg10.getD 0 1 = ⁅evalW pg10 [0,0,0], evalW pg10 [1,0,0,0,1,1,0,0,1]⁆ ∧
      pg10.getD 1 1 = ⁅evalW pg10 [0], evalW pg10 [0,0,1,1,0,0,1]⁆ ∧
      pg10.getD 0 1 ≠ 1 := by
  decide +kernel

@[expose] def pg11 : List (Perm (Fin 7)) := [permOf 7 [[0,2,6],[1,5,4]], permOf 7 [[0,1,2],[3,6,4]]]

theorem perf11_ch615 :
    evalW L11 [0,1,0,2,0,2,1,0,2,1,2] = pg11.getD 0 1 ∧
      evalW L11 [1,2,1,2,1,2,0,2] = pg11.getD 1 1 ∧
      pg11.getD 0 1 = ⁅evalW pg11 [0,0], evalW pg11 [1,1,0,1,0,1,1]⁆ ∧
      pg11.getD 1 1 = ⁅evalW pg11 [1,1], evalW pg11 [0,0,1,0,1,0,0]⁆ ∧
      pg11.getD 0 1 ≠ 1 := by
  decide +kernel

theorem card_alt : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem closure_mGens :
    Subgroup.closure {g | g ∈ mGens} = alternatingGroup (Fin 7) := by
  have hle : Subgroup.closure {g | g ∈ mGens} ≤ alternatingGroup (Fin 7) := by
    rw [Subgroup.closure_le]
    intro g hg
    exact Perm.mem_alternatingGroup.2 (mGens_even g hg)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Certificates.certificate7250.1, card_alt]

abbrev D : Subgroup (Perm (Fin 7)) := Subgroup.closure {g | g ∈ tGens}

theorem D_le : D ≤ alternatingGroup (Fin 7) := by
  rw [Subgroup.closure_le]
  intro g hg
  exact Perm.mem_alternatingGroup.2 (tGens_even g hg)

theorem isSylow_D :
    IsSylowTwoOf (D.subgroupOf (alternatingGroup (Fin 7))) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : Nat.card (D.subgroupOf (alternatingGroup (Fin 7))) = 2 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe D_le).toEquiv]
    exact Certificates.certificate7250.2.1 0 (by norm_num)
  refine ⟨le_top, IsPGroup.of_card hD, ?_⟩
  have hrel : ((D.subgroupOf (alternatingGroup (Fin 7))).subgroupOf ⊤).index =
      (D.subgroupOf (alternatingGroup (Fin 7))).index :=
    Subgroup.relIndex_top_right _
  have h := Subgroup.card_mul_index (D.subgroupOf (alternatingGroup (Fin 7)))
  rw [hD, card_alt] at h
  have hidx : (D.subgroupOf (alternatingGroup (Fin 7))).index = 315 := by omega
  rw [hrel, hidx]
  decide

abbrev Lm (j : ℕ) : Subgroup (Perm (Fin 7)) :=
  Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat).getD j []}

theorem overgroup_idx_ch615 {Y : Subgroup (Perm (Fin 7))}
    (hDY : D ≤ Y) (hYA : Y ≤ alternatingGroup (Fin 7)) : ∃ j < 12, Y = Lm j := by
  have hYM : Y ≤ Subgroup.closure {g | g ∈ mGens} := by
    rw [closure_mGens]
    exact hYA
  exact Certificates.certificate7250.2.2 Y hDY hYM

theorem card_Lm_ch615 {j : ℕ} (hj : j < 12) :
    Nat.card ↥(Lm j) = sizes.getD j 0 :=
  Certificates.certificate7250.2.1 j hj

theorem le_six_ch615 {a : ℕ} (ha1 : 1 ≤ a) (ha6 : a ≤ 6) (ha5 : a ≠ 5) : Lm a ≤ Lm 6 := by
  obtain ⟨h1, h2, h3, h4⟩ := words_six_ch615
  interval_cases a
  · exact closure_le_of_words_ch615 _ h1
  · exact closure_le_of_words_ch615 _ h2
  · exact closure_le_of_words_ch615 _ h3
  · exact closure_le_of_words_ch615 _ h4
  · exact absurd rfl ha5
  · exact le_rfl

theorem five_le_ch615 {j : ℕ} (hj8 : 8 ≤ j) (hj : j < 12) : Lm 5 ≤ Lm j := by
  obtain ⟨h8, h9, h10, h11⟩ := words_five_ch615
  interval_cases j
  · exact closure_le_of_words_ch615 _ h8
  · exact closure_le_of_words_ch615 _ h9
  · exact closure_le_of_words_ch615 _ h10
  · exact closure_le_of_words_ch615 _ h11

theorem not_isSolvable_Lm_ch615 {j : ℕ} (hj7 : 7 ≤ j) (hj : j < 12) :
    ¬ Group.IsSolvable ↥(Lm j) := by
  interval_cases j
  · obtain ⟨h1, h2, h3, h4, h5⟩ := perf7_ch615
    exact not_isSolvable_of_perf_ch615 h1 h2 h3 h4 h5
  · obtain ⟨h1, h2, h3, h4, h5⟩ := perf8_ch615
    exact not_isSolvable_of_perf_ch615 h1 h2 h3 h4 h5
  · obtain ⟨h1, h2, h3, h4, h5⟩ := perf9_ch615
    exact not_isSolvable_of_perf_ch615 h1 h2 h3 h4 h5
  · obtain ⟨h1, h2, h3, h4, h5⟩ := perf10_ch615
    exact not_isSolvable_of_perf_ch615 h1 h2 h3 h4 h5
  · obtain ⟨h1, h2, h3, h4, h5⟩ := perf11_ch615
    exact not_isSolvable_of_perf_ch615 h1 h2 h3 h4 h5

theorem idx_of_solvable_ch615 {Y : Subgroup (Perm (Fin 7))}
    (hDY : D ≤ Y) (hYA : Y ≤ alternatingGroup (Fin 7)) (hYD : Y ≠ D) (hYs : Group.IsSolvable ↥Y) :
    ∃ j, 1 ≤ j ∧ j ≤ 6 ∧ Y = Lm j := by
  obtain ⟨j, hj, rfl⟩ := overgroup_idx_ch615 hDY hYA
  refine ⟨j, Nat.one_le_iff_ne_zero.mpr fun h0 => hYD (by subst h0; rfl), ?_, rfl⟩
  by_contra h7
  exact not_isSolvable_Lm_ch615 (by omega) hj hYs

theorem eq_five_of_gen_ch615 {Y₁ Y₂ : Subgroup (Perm (Fin 7))}
    (h1D : D ≤ Y₁) (h1A : Y₁ ≤ alternatingGroup (Fin 7)) (h1ne : Y₁ ≠ D)
    (h1s : Group.IsSolvable ↥Y₁) (h2D : D ≤ Y₂) (h2A : Y₂ ≤ alternatingGroup (Fin 7))
    (h2ne : Y₂ ≠ D) (h2s : Group.IsSolvable ↥Y₂) (hgen : alternatingGroup (Fin 7) ≤ Y₁ ⊔ Y₂) :
    Y₁ = Lm 5 ∨ Y₂ = Lm 5 := by
  obtain ⟨a, ha1, ha6, rfl⟩ := idx_of_solvable_ch615 h1D h1A h1ne h1s
  obtain ⟨b, hb1, hb6, rfl⟩ := idx_of_solvable_ch615 h2D h2A h2ne h2s
  by_contra hcon
  rw [not_or] at hcon
  have ha5 : a ≠ 5 := fun h => hcon.1 (by rw [h])
  have hb5 : b ≠ 5 := fun h => hcon.2 (by rw [h])
  have hle := hgen.trans (sup_le (le_six_ch615 ha1 ha6 ha5) (le_six_ch615 hb1 hb6 hb5))
  have hcard := Subgroup.card_le_of_le hle
  rw [card_alt, card_Lm_ch615 (by norm_num)] at hcard
  exact absurd hcard (by decide)

theorem five_le_of_card_ch615 {Y : Subgroup (Perm (Fin 7))}
    (hDY : D ≤ Y) (hYA : Y ≤ alternatingGroup (Fin 7)) (hcard : 168 ≤ Nat.card ↥Y) :
    Lm 5 ≤ Y := by
  obtain ⟨j, hj, rfl⟩ := overgroup_idx_ch615 hDY hYA
  rw [card_Lm_ch615 hj] at hcard
  exact five_le_ch615 (sizes_big j hj hcard) hj

end CFSG.Quasithin.H13.Even7
