module

public import CFSG.Timmesfeld.RankTwo.LevisBPar
public import CFSG.Timmesfeld.RankTwo.LevisBWords
public import CFSG.Timmesfeld.LieEmbed.C3Roots

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg
open CFSG.Timmesfeld.GradedPresentation CFSG.Timmesfeld.LieEmbed TauCeti.GLSymplecticFin
open CFSG.LieType.Universal.Symplectic.SpExtras
open scoped commutatorElement

variable {F : Type} [Field F]

theorem sp3_x_100 (c : F) : Sp.x 3 F ![1, 0, 0] c =
    equivStatedSp 3 F (differenceShortRootUnit (m := 3) (i := 0) (j := 1) (by decide) c) := by
  rw [Sp.x_eq (r := .difference 0 1 (by decide)) (by decide), elt,
    RootSubgroupIndex.hom_difference, differenceShortRootHom_apply]
  rfl

theorem sp3_x_010 (c : F) : Sp.x 3 F ![0, 1, 0] c =
    equivStatedSp 3 F (differenceShortRootUnit (m := 3) (i := 1) (j := 2) (by decide) c) := by
  rw [Sp.x_eq (r := .difference 1 2 (by decide)) (by decide), elt,
    RootSubgroupIndex.hom_difference, differenceShortRootHom_apply]
  rfl

theorem sp3_x_110 (c : F) : Sp.x 3 F ![1, 1, 0] c =
    equivStatedSp 3 F (differenceShortRootUnit (m := 3) (i := 0) (j := 2) (by decide) c) := by
  rw [Sp.x_eq (r := .difference 0 2 (by decide)) (by decide), elt,
    RootSubgroupIndex.hom_difference, differenceShortRootHom_apply]
  rfl

theorem sp3_x_001 (c : F) : Sp.x 3 F ![0, 0, 1] c =
    equivStatedSp 3 F (positiveLongRootTransvectionUnit (m := 3) 2 c) := by
  rw [Sp.x_eq (r := .positiveLong 2) (by decide), elt, RootSubgroupIndex.hom_positiveLong,
    positiveLongRootTransvectionHom_apply]
  rfl

theorem sp3_x_021 (c : F) : Sp.x 3 F ![0, 2, 1] c =
    equivStatedSp 3 F (positiveLongRootTransvectionUnit (m := 3) 1 c) := by
  rw [Sp.x_eq (r := .positiveLong 1) (by decide), elt, RootSubgroupIndex.hom_positiveLong,
    positiveLongRootTransvectionHom_apply]
  rfl

theorem sp3_x_011 (c : F) : Sp.x 3 F ![0, 1, 1] c =
    equivStatedSp 3 F (positiveSumShortRootUnit (m := 3) (i := 1) (j := 2) (by decide) c) := by
  rw [Sp.x_eq (r := .positiveSum 1 2 (by decide)) (by decide), elt,
    RootSubgroupIndex.hom_positiveSum, positiveSumShortRootHom_apply]
  rfl

theorem sp3_comm_100_010 (s t : F) :
    ⁅Sp.x 3 F ![1, 0, 0] s, Sp.x 3 F ![0, 1, 0] t⁆ = Sp.x 3 F ![1, 1, 0] (s * t) := by
  rw [sp3_x_100, sp3_x_010, sp3_x_110, ← map_commutatorElement,
    commutatorElement_differenceShortRootUnit_differenceShortRootUnit]

theorem sp3_comm_010_001 (s t : F) :
    ⁅Sp.x 3 F ![0, 1, 0] s, Sp.x 3 F ![0, 0, 1] t⁆ =
      Sp.x 3 F ![0, 1, 1] (s * t) * Sp.x 3 F ![0, 2, 1] (s ^ 2 * t) := by
  rw [sp3_x_010, sp3_x_001, sp3_x_011, sp3_x_021, ← map_commutatorElement, ← map_mul,
    commutatorElement_differenceShortRootUnit_positiveLongRootTransvectionUnit]

theorem sp3_commute_010_011 [CharP F 2] (s t : F) :
    Commute (Sp.x 3 F ![0, 1, 0] s) (Sp.x 3 F ![0, 1, 1] t) := by
  have e : positiveLongRootTransvectionUnit (R := F) (m := 3) 1 0 = 1 := by
    have := (positiveLongRootTransvectionHom (R := F) (m := 3) 1).map_one
    rwa [positiveLongRootTransvectionHom_apply, toAdd_one] at this
  rw [← commutatorElement_eq_one_iff_commute, sp3_x_010, sp3_x_011, ← map_commutatorElement,
    commutatorElement_differenceShortRootUnit_positiveSumShortRootUnit,
    CharTwo.two_eq_zero (R := F), zero_mul, zero_mul, e, map_one]

theorem sp_commute_of_notMem {n : ℕ} {α β : Fin n → ℤ}
    (hα : α ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0)
    (h11 : α + β ∉ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC n) ∅)
    (h21 : 2 • α + β ∉ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC n) ∅)
    (h12 : α + 2 • β ∉ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC n) ∅) (c d : F) :
    Commute (Sp.x n F α c) (Sp.x n F β d) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (rootDatum n F).isFiniteType
    (show (rootDatum n F).divisible = ∅ from rfl)
  have e := Sp.commutatorFormula O α hα β hβ hαβ c d
  have hnil : O.list α β = [] := by
    refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
    obtain ⟨hpS, hr⟩ := (Sp.mem_expPairs_iff hα hβ hαβ p).1 ((O.mem_iff α hα β hβ hαβ p).1 hp)
    simp only [Sp.expS, Finset.mem_insert, Finset.mem_singleton] at hpS
    rcases hpS with rfl | rfl | rfl
    · exact h11 (by simpa using hr)
    · exact h21 (by simpa using hr)
    · exact h12 (by simpa using hr)
  rw [hnil, List.map_nil, List.prod_nil] at e
  exact commutatorElement_eq_one_iff_commute.1 e

theorem c3_mem_roots {v : Fin 3 → ℤ} (hv : v ∈ c3Roots) :
    v ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅ :=
  mem_roots_of_mem_c3Roots hv

theorem c3_notMem_roots {v : Fin 3 → ℤ} (hv : v ∉ c3Roots) :
    v ∉ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅ :=
  fun h => hv (mem_roots_iff_mem_c3Roots.1 h)

theorem sp3_commute {α β : Fin 3 → ℤ} (hα : α ∈ c3Roots) (hβ : β ∈ c3Roots) (hαβ : α + β ≠ 0)
    (h11 : α + β ∉ c3Roots) (h21 : 2 • α + β ∉ c3Roots) (h12 : α + 2 • β ∉ c3Roots)
    (c d : F) : Commute (Sp.x 3 F α c) (Sp.x 3 F β d) :=
  sp_commute_of_notMem (c3_mem_roots hα) (c3_mem_roots hβ) hαβ (c3_notMem_roots h11)
    (c3_notMem_roots h21) (c3_notMem_roots h12) c d

@[expose] def ht3 : (Fin 3 → ℤ) →+ ℤ where
  toFun v := v 0 + v 1 + v 2
  map_zero' := by simp
  map_add' v w := by simp only [Pi.add_apply]; ring

theorem sp3_prodInjective (L : List (Fin 3 → ℤ)) (hL : L.Nodup)
    (hR : ∀ γ ∈ L, γ ∈ c3Roots ∧ 0 < γ 0 + γ 1 + γ 2)
    (hsort : L.Pairwise fun γ δ => γ 0 + γ 1 + γ 2 ≤ δ 0 + δ 1 + δ 2) :
    ProdInjectiveFor (Symplectic.rootGroup 3 F) L :=
  Sp.prodInjective ht3 L hL (fun γ hγ => ⟨c3_mem_roots (hR γ hγ).1, (hR γ hγ).2⟩) hsort

theorem sp3_commute_100_110 (s t : F) :
    Commute (Sp.x 3 F ![1, 0, 0] s) (Sp.x 3 F ![1, 1, 0] t) :=
  sp3_commute (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s t

theorem sp3_commute_110_010 (s t : F) :
    Commute (Sp.x 3 F ![1, 1, 0] s) (Sp.x 3 F ![0, 1, 0] t) :=
  sp3_commute (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s t

theorem sp3_commute_010_021 (s t : F) :
    Commute (Sp.x 3 F ![0, 1, 0] s) (Sp.x 3 F ![0, 2, 1] t) :=
  sp3_commute (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s t

theorem sp3_commute_011_021 (s t : F) :
    Commute (Sp.x 3 F ![0, 1, 1] s) (Sp.x 3 F ![0, 2, 1] t) :=
  sp3_commute (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s t

theorem sp3_commute_011_001 (s t : F) :
    Commute (Sp.x 3 F ![0, 1, 1] s) (Sp.x 3 F ![0, 0, 1] t) :=
  sp3_commute (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s t

theorem sp3_commute_021_001 (s t : F) :
    Commute (Sp.x 3 F ![0, 2, 1] s) (Sp.x 3 F ![0, 0, 1] t) :=
  sp3_commute (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s t

theorem sp3_commute_100_001 (s t : F) :
    Commute (Sp.x 3 F ![1, 0, 0] s) (Sp.x 3 F ![0, 0, 1] t) :=
  sp3_commute (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s t

theorem sp3_prodInjective01 :
    ProdInjectiveFor (Symplectic.rootGroup 3 F) [![1, 0, 0], ![0, 1, 0], ![1, 1, 0]] :=
  sp3_prodInjective _ (by decide) (by decide) (by decide)

theorem sp3_prodInjective12 :
    ProdInjectiveFor (Symplectic.rootGroup 3 F)
      [![0, 1, 0], ![0, 0, 1], ![0, 1, 1], ![0, 2, 1]] :=
  sp3_prodInjective _ (by decide) (by decide) (by decide)

theorem sp3_prodInjective02 :
    ProdInjectiveFor (Symplectic.rootGroup 3 F) [![1, 0, 0], ![0, 0, 1]] :=
  sp3_prodInjective _ (by decide) (by decide) (by decide)

@[expose] def c3r : Fin 12 → Fin 3 → ℤ :=
  ![![1, 0, 0], ![-1, 0, 0], ![0, 1, 0], ![0, -1, 0], ![0, 0, 1], ![0, 0, -1], ![1, 1, 0],
    ![-1, -1, 0], ![0, 1, 1], ![0, -1, -1], ![0, 2, 1], ![0, -2, -1]]

theorem c3r_injective : Function.Injective c3r := by decide

theorem c3r_mem (i : Fin 12) : c3r i ∈ c3Roots := by
  fin_cases i <;> decide

@[expose] noncomputable def c3PsiOf {G : Type*} [Group G] (f : Fin 12 → F → G) :
    (Fin 3 → ℤ) → F → G :=
  fun γ c => if h : ∃ i, c3r i = γ then f h.choose c else 1

omit [Field F] in
theorem c3PsiOf_r {G : Type*} [Group G] (f : Fin 12 → F → G) (i : Fin 12) (c : F) :
    c3PsiOf f (c3r i) c = f i c := by
  have h : ∃ j, c3r j = c3r i := ⟨i, rfl⟩
  simp only [c3PsiOf, dite_eq_left h]
  rw [c3r_injective h.choose_spec]

section Pairs

variable (F) in
noncomputable abbrev Φ3 : Steinberg.RootSystem (Fin 3) :=
  Steinberg.RootSystem.ofCartan (rootDatum 3 F).isFiniteType (rootDatum 3 F).divisible

theorem mem_c3Roots_of_mem_pairRoots {i j : Fin 3} {γ : Fin 3 → ℤ}
    (hγ : γ ∈ pairRoots (rootDatum 3 F) i j) : γ ∈ c3Roots :=
  mem_roots_iff_mem_c3Roots.1 hγ.1

theorem pairRoots_comm' {i j : Fin 3} :
    pairRoots (rootDatum 3 F) i j = pairRoots (rootDatum 3 F) j i := by
  ext γ
  exact ⟨fun h => ⟨h.1, fun k hj hi => h.2 k hi hj⟩, fun h => ⟨h.1, fun k hi hj => h.2 k hj hi⟩⟩

theorem c3_pair01 {γ : Fin 3 → ℤ} (hγ : γ ∈ pairRoots (rootDatum 3 F) (0 : Fin 3) (1 : Fin 3)) :
    γ = c3r 0 ∨ γ = c3r 1 ∨ γ = c3r 2 ∨ γ = c3r 3 ∨ γ = c3r 6 ∨ γ = c3r 7 := by
  have key : ∀ v ∈ c3Roots, v 2 = 0 →
      v = c3r 0 ∨ v = c3r 1 ∨ v = c3r 2 ∨ v = c3r 3 ∨ v = c3r 6 ∨ v = c3r 7 := by
    decide
  exact key γ (mem_c3Roots_of_mem_pairRoots hγ)
    (hγ.2 (2 : Fin 3) (show (2 : Fin 3) ≠ 0 by decide) (show (2 : Fin 3) ≠ 1 by decide))

theorem c3_pair12 {γ : Fin 3 → ℤ} (hγ : γ ∈ pairRoots (rootDatum 3 F) (1 : Fin 3) (2 : Fin 3)) :
    γ = c3r 2 ∨ γ = c3r 3 ∨ γ = c3r 4 ∨ γ = c3r 5 ∨ γ = c3r 8 ∨ γ = c3r 9 ∨ γ = c3r 10 ∨
      γ = c3r 11 := by
  have key : ∀ v ∈ c3Roots, v 0 = 0 →
      v = c3r 2 ∨ v = c3r 3 ∨ v = c3r 4 ∨ v = c3r 5 ∨ v = c3r 8 ∨ v = c3r 9 ∨ v = c3r 10 ∨
        v = c3r 11 := by
    decide
  exact key γ (mem_c3Roots_of_mem_pairRoots hγ)
    (hγ.2 (0 : Fin 3) (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide))

theorem c3_pair02 {γ : Fin 3 → ℤ} (hγ : γ ∈ pairRoots (rootDatum 3 F) (0 : Fin 3) (2 : Fin 3)) :
    γ = c3r 0 ∨ γ = c3r 1 ∨ γ = c3r 4 ∨ γ = c3r 5 := by
  have key : ∀ v ∈ c3Roots, v 1 = 0 → v = c3r 0 ∨ v = c3r 1 ∨ v = c3r 4 ∨ v = c3r 5 := by
    decide
  exact key γ (mem_c3Roots_of_mem_pairRoots hγ)
    (hγ.2 (1 : Fin 3) (show (1 : Fin 3) ≠ 0 by decide) (show (1 : Fin 3) ≠ 2 by decide))

theorem c3_pair_self {k : Fin 3} {γ : Fin 3 → ℤ} (hγ : γ ∈ pairRoots (rootDatum 3 F) k k) :
    γ = Pi.single k 1 ∨ γ = -Pi.single k 1 := by
  have key : ∀ k : Fin 3, ∀ v ∈ c3Roots, (∀ l, l ≠ k → v l = 0) →
      v = Pi.single k 1 ∨ v = -Pi.single k 1 := by
    decide
  exact key k γ (mem_c3Roots_of_mem_pairRoots hγ) fun l hl => hγ.2 l hl hl

theorem ht_c3r_neg {i : Fin 12} (hi : i ∈ ({1, 3, 5, 7, 9, 11} : Finset (Fin 12))) :
    ¬ 0 < Steinberg.ht (c3r i) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Pairs

structure IsC3Frame {G : Type*} [Group G] (f : Fin 12 → F → G) (w01 w12 w02 : Fin 3 → G) :
    Prop where
  add0 : ∀ c d, f 0 (c + d) = f 0 c * f 0 d
  add2 : ∀ c d, f 2 (c + d) = f 2 c * f 2 d
  add4 : ∀ c d, f 4 (c + d) = f 4 c * f 4 d
  add6 : ∀ c d, f 6 (c + d) = f 6 c * f 6 d
  add8 : ∀ c d, f 8 (c + d) = f 8 c * f 8 d
  add10 : ∀ c d, f 10 (c + d) = f 10 c * f 10 d
  comm_0_2 : ∀ s t, ⁅f 0 s, f 2 t⁆ = f 6 (s * t)
  commute_0_6 : ∀ s t, Commute (f 0 s) (f 6 t)
  commute_6_2 : ∀ s t, Commute (f 6 s) (f 2 t)
  comm_2_4 : ∀ s t, ⁅f 2 s, f 4 t⁆ = f 8 (s * t) * f 10 (s ^ 2 * t)
  commute_2_8 : ∀ s t, Commute (f 2 s) (f 8 t)
  commute_2_10 : ∀ s t, Commute (f 2 s) (f 10 t)
  commute_8_10 : ∀ s t, Commute (f 8 s) (f 10 t)
  commute_8_4 : ∀ s t, Commute (f 8 s) (f 4 t)
  commute_10_4 : ∀ s t, Commute (f 10 s) (f 4 t)
  commute_0_4 : ∀ s t, Commute (f 0 s) (f 4 t)
  w01_0_0 : ∀ c, w01 0 * f 0 c * (w01 0)⁻¹ = f 1 c
  w01_0_1 : ∀ c, w01 0 * f 1 c * (w01 0)⁻¹ = f 0 c
  w01_0_2 : ∀ c, w01 0 * f 2 c * (w01 0)⁻¹ = f 6 c
  w01_0_3 : ∀ c, w01 0 * f 3 c * (w01 0)⁻¹ = f 7 c
  w01_0_6 : ∀ c, w01 0 * f 6 c * (w01 0)⁻¹ = f 2 c
  w01_0_7 : ∀ c, w01 0 * f 7 c * (w01 0)⁻¹ = f 3 c
  w01_1_0 : ∀ c, w01 1 * f 0 c * (w01 1)⁻¹ = f 6 c
  w01_1_1 : ∀ c, w01 1 * f 1 c * (w01 1)⁻¹ = f 7 c
  w01_1_2 : ∀ c, w01 1 * f 2 c * (w01 1)⁻¹ = f 3 c
  w01_1_3 : ∀ c, w01 1 * f 3 c * (w01 1)⁻¹ = f 2 c
  w01_1_6 : ∀ c, w01 1 * f 6 c * (w01 1)⁻¹ = f 0 c
  w01_1_7 : ∀ c, w01 1 * f 7 c * (w01 1)⁻¹ = f 1 c
  w12_1_2 : ∀ c, w12 1 * f 2 c * (w12 1)⁻¹ = f 3 c
  w12_1_3 : ∀ c, w12 1 * f 3 c * (w12 1)⁻¹ = f 2 c
  w12_1_4 : ∀ c, w12 1 * f 4 c * (w12 1)⁻¹ = f 10 c
  w12_1_5 : ∀ c, w12 1 * f 5 c * (w12 1)⁻¹ = f 11 c
  w12_1_8 : ∀ c, w12 1 * f 8 c * (w12 1)⁻¹ = f 8 c
  w12_1_9 : ∀ c, w12 1 * f 9 c * (w12 1)⁻¹ = f 9 c
  w12_1_10 : ∀ c, w12 1 * f 10 c * (w12 1)⁻¹ = f 4 c
  w12_1_11 : ∀ c, w12 1 * f 11 c * (w12 1)⁻¹ = f 5 c
  w12_2_2 : ∀ c, w12 2 * f 2 c * (w12 2)⁻¹ = f 8 c
  w12_2_3 : ∀ c, w12 2 * f 3 c * (w12 2)⁻¹ = f 9 c
  w12_2_4 : ∀ c, w12 2 * f 4 c * (w12 2)⁻¹ = f 5 c
  w12_2_5 : ∀ c, w12 2 * f 5 c * (w12 2)⁻¹ = f 4 c
  w12_2_8 : ∀ c, w12 2 * f 8 c * (w12 2)⁻¹ = f 2 c
  w12_2_9 : ∀ c, w12 2 * f 9 c * (w12 2)⁻¹ = f 3 c
  w12_2_10 : ∀ c, w12 2 * f 10 c * (w12 2)⁻¹ = f 10 c
  w12_2_11 : ∀ c, w12 2 * f 11 c * (w12 2)⁻¹ = f 11 c
  w02_0_0 : ∀ c, w02 0 * f 0 c * (w02 0)⁻¹ = f 1 c
  w02_0_1 : ∀ c, w02 0 * f 1 c * (w02 0)⁻¹ = f 0 c
  w02_0_4 : ∀ c, w02 0 * f 4 c * (w02 0)⁻¹ = f 4 c
  w02_0_5 : ∀ c, w02 0 * f 5 c * (w02 0)⁻¹ = f 5 c
  w02_2_0 : ∀ c, w02 2 * f 0 c * (w02 2)⁻¹ = f 0 c
  w02_2_1 : ∀ c, w02 2 * f 1 c * (w02 2)⁻¹ = f 1 c
  w02_2_4 : ∀ c, w02 2 * f 4 c * (w02 2)⁻¹ = f 5 c
  w02_2_5 : ∀ c, w02 2 * f 5 c * (w02 2)⁻¹ = f 4 c
  rank0 : ∃ Θ : Matrix.SpecialLinearGroup (Fin 2) F →* G,
    (∀ c, Θ (sl2Upper c) = f 0 c) ∧ ∀ c, Θ (sl2Lower c) = f 1 c
  rank1 : ∃ Θ : Matrix.SpecialLinearGroup (Fin 2) F →* G,
    (∀ c, Θ (sl2Upper c) = f 2 c) ∧ ∀ c, Θ (sl2Lower c) = f 3 c
  rank2 : ∃ Θ : Matrix.SpecialLinearGroup (Fin 2) F →* G,
    (∀ c, Θ (sl2Upper c) = f 4 c) ∧ ∀ c, Θ (sl2Lower c) = f 5 c
  gen : Subgroup.closure (Set.range (f 0) ∪ Set.range (f 1) ∪ Set.range (f 2) ∪
    Set.range (f 3) ∪ Set.range (f 4) ∪ Set.range (f 5)) = ⊤
  nt : ∃ c, f 0 c ≠ 1

section Frame

variable {G : Type*} [Group G] {f : Fin 12 → F → G} {w01 w12 w02 : Fin 3 → G}

@[expose] def c3i01 : Fin 3 → Fin 12 := ![0, 6, 2]

@[expose] def c3i12 : Fin 4 → Fin 12 := ![2, 8, 10, 4]

@[expose] def c3i02 : Fin 2 → Fin 12 := ![0, 4]

theorem sp3_hn {i j : Fin 3} : ∀ k, (k = i ∨ k = j) → ∀ γ ∈ pairRoots (rootDatum 3 F) i j,
    ∀ y ∈ (rootDatum 3 F).rootGroup γ,
      weylElement (Sp.x 3 F) k 1 * y * (weylElement (Sp.x 3 F) k 1)⁻¹ ∈
        (rootDatum 3 F).rootGroup ((Φ3 F).refl k γ) :=
  fun k _ _ hγ _ hy => conj_mem_refl Sp.isParametrization (fun i _ hβ => Sp.weyl i hβ) k hγ.1 hy

theorem c3_conj_aux (w : G) (k : Fin 3) (a b : Fin 12)
    (hab : CFSG.LieType.RootSystem.reflection (cartanC 3) k (c3r a) = c3r b)
    (c : F) (e : w * f a c * w⁻¹ = f b c) :
    w * c3PsiOf f (c3r a) c * w⁻¹ = c3PsiOf f ((Φ3 F).refl k (c3r a)) c := by
  rw [show (Φ3 F).refl k (c3r a) = c3r b from hab, c3PsiOf_r, c3PsiOf_r]
  exact e

namespace IsC3Frame

variable (h : IsC3Frame f w01 w12 w02)
include h

theorem weyl01 : ∀ k, (k = 0 ∨ k = 1) → ∀ γ ∈ pairRoots (rootDatum 3 F) (0 : Fin 3) (1 : Fin 3),
    ∀ c, w01 k * c3PsiOf f γ c * (w01 k)⁻¹ = c3PsiOf f ((Φ3 F).refl k γ) c := by
  rintro k (rfl | rfl) γ hγ c <;> rcases c3_pair01 hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact c3_conj_aux _ 0 0 1 (by decide) c (h.w01_0_0 c)
  · exact c3_conj_aux _ 0 1 0 (by decide) c (h.w01_0_1 c)
  · exact c3_conj_aux _ 0 2 6 (by decide) c (h.w01_0_2 c)
  · exact c3_conj_aux _ 0 3 7 (by decide) c (h.w01_0_3 c)
  · exact c3_conj_aux _ 0 6 2 (by decide) c (h.w01_0_6 c)
  · exact c3_conj_aux _ 0 7 3 (by decide) c (h.w01_0_7 c)
  · exact c3_conj_aux _ 1 0 6 (by decide) c (h.w01_1_0 c)
  · exact c3_conj_aux _ 1 1 7 (by decide) c (h.w01_1_1 c)
  · exact c3_conj_aux _ 1 2 3 (by decide) c (h.w01_1_2 c)
  · exact c3_conj_aux _ 1 3 2 (by decide) c (h.w01_1_3 c)
  · exact c3_conj_aux _ 1 6 0 (by decide) c (h.w01_1_6 c)
  · exact c3_conj_aux _ 1 7 1 (by decide) c (h.w01_1_7 c)

theorem weyl12 : ∀ k, (k = 1 ∨ k = 2) → ∀ γ ∈ pairRoots (rootDatum 3 F) (1 : Fin 3) (2 : Fin 3),
    ∀ c, w12 k * c3PsiOf f γ c * (w12 k)⁻¹ = c3PsiOf f ((Φ3 F).refl k γ) c := by
  rintro k (rfl | rfl) γ hγ c <;>
    rcases c3_pair12 hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact c3_conj_aux _ 1 2 3 (by decide) c (h.w12_1_2 c)
  · exact c3_conj_aux _ 1 3 2 (by decide) c (h.w12_1_3 c)
  · exact c3_conj_aux _ 1 4 10 (by decide) c (h.w12_1_4 c)
  · exact c3_conj_aux _ 1 5 11 (by decide) c (h.w12_1_5 c)
  · exact c3_conj_aux _ 1 8 8 (by decide) c (h.w12_1_8 c)
  · exact c3_conj_aux _ 1 9 9 (by decide) c (h.w12_1_9 c)
  · exact c3_conj_aux _ 1 10 4 (by decide) c (h.w12_1_10 c)
  · exact c3_conj_aux _ 1 11 5 (by decide) c (h.w12_1_11 c)
  · exact c3_conj_aux _ 2 2 8 (by decide) c (h.w12_2_2 c)
  · exact c3_conj_aux _ 2 3 9 (by decide) c (h.w12_2_3 c)
  · exact c3_conj_aux _ 2 4 5 (by decide) c (h.w12_2_4 c)
  · exact c3_conj_aux _ 2 5 4 (by decide) c (h.w12_2_5 c)
  · exact c3_conj_aux _ 2 8 2 (by decide) c (h.w12_2_8 c)
  · exact c3_conj_aux _ 2 9 3 (by decide) c (h.w12_2_9 c)
  · exact c3_conj_aux _ 2 10 10 (by decide) c (h.w12_2_10 c)
  · exact c3_conj_aux _ 2 11 11 (by decide) c (h.w12_2_11 c)

theorem weyl02 : ∀ k, (k = 0 ∨ k = 2) → ∀ γ ∈ pairRoots (rootDatum 3 F) (0 : Fin 3) (2 : Fin 3),
    ∀ c, w02 k * c3PsiOf f γ c * (w02 k)⁻¹ = c3PsiOf f ((Φ3 F).refl k γ) c := by
  rintro k (rfl | rfl) γ hγ c <;> rcases c3_pair02 hγ with rfl | rfl | rfl | rfl
  · exact c3_conj_aux _ 0 0 1 (by decide) c (h.w02_0_0 c)
  · exact c3_conj_aux _ 0 1 0 (by decide) c (h.w02_0_1 c)
  · exact c3_conj_aux _ 0 4 4 (by decide) c (h.w02_0_4 c)
  · exact c3_conj_aux _ 0 5 5 (by decide) c (h.w02_0_5 c)
  · exact c3_conj_aux _ 2 0 0 (by decide) c (h.w02_2_0 c)
  · exact c3_conj_aux _ 2 1 1 (by decide) c (h.w02_2_1 c)
  · exact c3_conj_aux _ 2 4 5 (by decide) c (h.w02_2_4 c)
  · exact c3_conj_aux _ 2 5 4 (by decide) c (h.w02_2_5 c)

theorem hrank (k : Fin 3) :
    ExtendsToHom (rootDatum 3 F).rootGroup {Pi.single k 1, -Pi.single k 1}
      (phiOf (rootDatum 3 F) (Sp.x 3 F) (c3PsiOf f)) := by
  obtain ⟨φ, hφ, hφU, hφL⟩ := Sp.rankOne (n := 3) (F := F) k
  have key : ∀ a b : Fin 12, c3r a = Pi.single k 1 → c3r b = -Pi.single k 1 →
      (∃ Θ : Matrix.SpecialLinearGroup (Fin 2) F →* G,
        (∀ c, Θ (sl2Upper c) = f a c) ∧ ∀ c, Θ (sl2Lower c) = f b c) →
      ExtendsToHom (rootDatum 3 F).rootGroup {Pi.single k 1, -Pi.single k 1}
        (phiOf (rootDatum 3 F) (Sp.x 3 F) (c3PsiOf f)) := by
    rintro a b ha hb ⟨Θ, hΘU, hΘL⟩
    have e1 : ∀ c, c3PsiOf f (Pi.single k 1) c = f a c := fun c => by
      rw [← ha]
      exact c3PsiOf_r f a c
    have e2 : ∀ c, c3PsiOf f (-Pi.single k 1) c = f b c := fun c => by
      rw [← hb]
      exact c3PsiOf_r f b c
    exact extendsToHom_rankOne Sp.isParametrization k hφ hφU hφL (c3PsiOf f) (Θ := Θ)
      (fun c => (hΘU c).trans (e1 c).symm) (fun c => (hΘL c).trans (e2 c).symm)
  fin_cases k
  · exact key 0 1 (by decide) (by decide) h.rank0
  · exact key 2 3 (by decide) (by decide) h.rank1
  · exact key 4 5 (by decide) (by decide) h.rank2

theorem pos01 [Finite F] :
    ExtendsToHom (rootDatum 3 F).rootGroup
      (pairRoots (rootDatum 3 F) (0 : Fin 3) (1 : Fin 3) ∩ (Φ3 F).pos)
      (phiOf (rootDatum 3 F) (Sp.x 3 F) (c3PsiOf f)) := by
  have hψ : (fun g : Σ _ : Fin 3, F => c3PsiOf f (c3r (c3i01 g.1)) g.2) =
      fun g => f (c3i01 g.1) g.2 := funext fun g => c3PsiOf_r f _ _
  refine extendsToHom_of_wordRels Sp.isParametrization (cm := a2Cm (K := F)) (ht := a2Ht)
    (fun α s β t => a2Cm_mem_above α s β t) (fun i => c3r (c3i01 i))
    (c3r_injective.comp (by decide)) (fun i => c3_mem_roots (c3r_mem _)) ?_ [0, 2, 1]
    (by decide) sp3_prodInjective01 ?_ (c3PsiOf f) ?_
  · exact rels_a2Cm_of (fun i c d => (Sp.isParametrization _ (c3_mem_roots (c3r_mem _))).2.1 c d)
      (fun s t => sp3_comm_100_010 s t) (fun s t => sp3_commute_100_110 s t)
      (fun s t => sp3_commute_110_010 s t)
  · rintro γ ⟨hγ, hpos⟩
    rcases c3_pair01 hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact absurd hpos.2 (ht_c3r_neg (by decide))
    · exact ⟨2, rfl⟩
    · exact absurd hpos.2 (ht_c3r_neg (by decide))
    · exact ⟨1, rfl⟩
    · exact absurd hpos.2 (ht_c3r_neg (by decide))
  · rw [hψ]
    refine rels_a2Cm_of (fun i c d => ?_) h.comm_0_2 h.commute_0_6 h.commute_6_2
    fin_cases i
    exacts [h.add0 c d, h.add6 c d, h.add2 c d]

theorem pos12 [CharP F 2] [Finite F] :
    ExtendsToHom (rootDatum 3 F).rootGroup
      (pairRoots (rootDatum 3 F) (1 : Fin 3) (2 : Fin 3) ∩ (Φ3 F).pos)
      (phiOf (rootDatum 3 F) (Sp.x 3 F) (c3PsiOf f)) := by
  have hψ : (fun g : Σ _ : Fin 4, F => c3PsiOf f (c3r (c3i12 g.1)) g.2) =
      fun g => f (c3i12 g.1) g.2 := funext fun g => c3PsiOf_r f _ _
  refine extendsToHom_of_wordRels Sp.isParametrization (cm := b2Cm (K := F)) (ht := b2Ht)
    (fun α s β t => b2Cm_mem_above α s β t) (fun i => c3r (c3i12 i))
    (c3r_injective.comp (by decide)) (fun i => c3_mem_roots (c3r_mem _)) ?_ [0, 3, 1, 2]
    (by decide) sp3_prodInjective12 ?_ (c3PsiOf f) ?_
  · exact rels_b2Cm_of (fun i c d => (Sp.isParametrization _ (c3_mem_roots (c3r_mem _))).2.1 c d)
      (fun s t => sp3_comm_010_001 s t) (fun s t => sp3_commute_010_011 s t)
      (fun s t => sp3_commute_010_021 s t) (fun s t => sp3_commute_011_021 s t)
      (fun s t => sp3_commute_011_001 s t) (fun s t => sp3_commute_021_001 s t)
  · rintro γ ⟨hγ, hpos⟩
    rcases c3_pair12 hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact absurd hpos.2 (ht_c3r_neg (by decide))
    · exact ⟨3, rfl⟩
    · exact absurd hpos.2 (ht_c3r_neg (by decide))
    · exact ⟨1, rfl⟩
    · exact absurd hpos.2 (ht_c3r_neg (by decide))
    · exact ⟨2, rfl⟩
    · exact absurd hpos.2 (ht_c3r_neg (by decide))
  · rw [hψ]
    refine rels_b2Cm_of (fun i c d => ?_) h.comm_2_4 h.commute_2_8 h.commute_2_10 h.commute_8_10
      h.commute_8_4 h.commute_10_4
    fin_cases i
    exacts [h.add2 c d, h.add8 c d, h.add10 c d, h.add4 c d]

theorem pos02 [Finite F] :
    ExtendsToHom (rootDatum 3 F).rootGroup
      (pairRoots (rootDatum 3 F) (0 : Fin 3) (2 : Fin 3) ∩ (Φ3 F).pos)
      (phiOf (rootDatum 3 F) (Sp.x 3 F) (c3PsiOf f)) := by
  have hψ : (fun g : Σ _ : Fin 2, F => c3PsiOf f (c3r (c3i02 g.1)) g.2) =
      fun g => f (c3i02 g.1) g.2 := funext fun g => c3PsiOf_r f _ _
  refine extendsToHom_of_wordRels Sp.isParametrization (cm := a1a1Cm (K := F)) (ht := a1a1Ht)
    (fun α s β t => a1a1Cm_mem_above α s β t) (fun i => c3r (c3i02 i))
    (c3r_injective.comp (by decide)) (fun i => c3_mem_roots (c3r_mem _)) ?_ [0, 1]
    (by decide) sp3_prodInjective02 ?_ (c3PsiOf f) ?_
  · exact rels_a1a1Cm_of
      (fun i c d => (Sp.isParametrization _ (c3_mem_roots (c3r_mem _))).2.1 c d)
      (fun s t => sp3_commute_100_001 s t)
  · rintro γ ⟨hγ, hpos⟩
    rcases c3_pair02 hγ with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact absurd hpos.2 (ht_c3r_neg (by decide))
    · exact ⟨1, rfl⟩
    · exact absurd hpos.2 (ht_c3r_neg (by decide))
  · rw [hψ]
    refine rels_a1a1Cm_of (fun i c d => ?_) h.commute_0_4
    fin_cases i
    exacts [h.add0 c d, h.add4 c d]

omit h in
theorem cone_swap {i j : Fin 3}
    (hc : ∀ α ∈ pairRoots (rootDatum 3 F) i j, ∀ β ∈ pairRoots (rootDatum 3 F) i j,
      ¬ Universal.IsNegMultiple α β →
        ExtendsToHom (rootDatum 3 F).rootGroup
          ((rootDatum 3 F).cone α β ∩ pairRoots (rootDatum 3 F) i j)
          (phiOf (rootDatum 3 F) (Sp.x 3 F) (c3PsiOf f))) :
    ∀ α ∈ pairRoots (rootDatum 3 F) j i, ∀ β ∈ pairRoots (rootDatum 3 F) j i,
      ¬ Universal.IsNegMultiple α β →
        ExtendsToHom (rootDatum 3 F).rootGroup
          ((rootDatum 3 F).cone α β ∩ pairRoots (rootDatum 3 F) j i)
          (phiOf (rootDatum 3 F) (Sp.x 3 F) (c3PsiOf f)) := by
  rw [pairRoots_comm']
  exact hc

theorem hcone [CharP F 2] [Finite F] : ∀ i j, ∀ α ∈ pairRoots (rootDatum 3 F) i j,
    ∀ β ∈ pairRoots (rootDatum 3 F) i j, ¬ Universal.IsNegMultiple α β →
      ExtendsToHom (rootDatum 3 F).rootGroup
        ((rootDatum 3 F).cone α β ∩ pairRoots (rootDatum 3 F) i j)
        (phiOf (rootDatum 3 F) (Sp.x 3 F) (c3PsiOf f)) := by
  have hP := Sp.isParametrization (n := 3) (F := F)
  have h01 := extendsToHom_cone_pairRoots (D := rootDatum 3 F) (i := (0 : Fin 3))
    (j := (1 : Fin 3)) (fun k => weylElement (Sp.x 3 F) k 1) sp3_hn w01
    (conj_phiOf_refl hP (fun i _ hβ => Sp.weyl i hβ) (c3PsiOf f) w01 _ (fun _ hγ => hγ.1)
      h.weyl01) h.pos01
    (fun k _ => h.hrank k)
  have h12 := extendsToHom_cone_pairRoots (D := rootDatum 3 F) (i := (1 : Fin 3))
    (j := (2 : Fin 3)) (fun k => weylElement (Sp.x 3 F) k 1) sp3_hn w12
    (conj_phiOf_refl hP (fun i _ hβ => Sp.weyl i hβ) (c3PsiOf f) w12 _ (fun _ hγ => hγ.1)
      h.weyl12) h.pos12
    (fun k _ => h.hrank k)
  have h02 := extendsToHom_cone_pairRoots (D := rootDatum 3 F) (i := (0 : Fin 3))
    (j := (2 : Fin 3)) (fun k => weylElement (Sp.x 3 F) k 1) sp3_hn w02
    (conj_phiOf_refl hP (fun i _ hβ => Sp.weyl i hβ) (c3PsiOf f) w02 _ (fun _ hγ => hγ.1)
      h.weyl02) h.pos02
    (fun k _ => h.hrank k)
  have hself : ∀ k : Fin 3, ∀ α ∈ pairRoots (rootDatum 3 F) k k,
      ∀ β ∈ pairRoots (rootDatum 3 F) k k, ¬ Universal.IsNegMultiple α β →
        ExtendsToHom (rootDatum 3 F).rootGroup
          ((rootDatum 3 F).cone α β ∩ pairRoots (rootDatum 3 F) k k)
          (phiOf (rootDatum 3 F) (Sp.x 3 F) (c3PsiOf f)) := by
    intro k α _ β _ _
    refine (h.hrank k).mono fun γ hγ => ?_
    rcases c3_pair_self hγ.2 with e | e
    · exact Or.inl e
    · exact Or.inr e
  intro i j
  fin_cases i <;> fin_cases j
  · exact hself 0
  · exact h01
  · exact h02
  · exact cone_swap h01
  · exact hself 1
  · exact h12
  · exact cone_swap h02
  · exact cone_swap h12
  · exact hself 2

omit h in
theorem mem_range_phiOf (γ : Fin 3 → ℤ) (a : Fin 12) (ha : c3r a = γ) (x : G)
    (hx : x ∈ Set.range (f a)) :
    x ∈ Set.range (phiOf (rootDatum 3 F) (Sp.x 3 F) (c3PsiOf f) γ) := by
  subst ha
  obtain ⟨c, rfl⟩ := hx
  exact ⟨⟨Sp.x 3 F (c3r a) c, x_mem_rootGroup Sp.isParametrization (c3_mem_roots (c3r_mem a)) c⟩,
    (phiOf_x Sp.isParametrization (c3PsiOf f) (c3_mem_roots (c3r_mem a)) c _).trans
      (c3PsiOf_r f a c)⟩

omit h in
theorem range_phiOf_c3r (γ : Fin 3 → ℤ) (a : Fin 12) (ha : c3r a = γ) :
    Set.range (phiOf (rootDatum 3 F) (Sp.x 3 F) (c3PsiOf f) γ) = Set.range (f a) := by
  subst ha
  refine (range_phiOf Sp.isParametrization (c3PsiOf f) (c3_mem_roots (c3r_mem a))).trans ?_
  exact congrArg Set.range (funext fun c => c3PsiOf_r f a c)

theorem hgen : Subgroup.closure (⋃ k : Fin 3,
    Set.range (phiOf (rootDatum 3 F) (Sp.x 3 F) (c3PsiOf f) (Pi.single k 1)) ∪
      Set.range (phiOf (rootDatum 3 F) (Sp.x 3 F) (c3PsiOf f) (-Pi.single k 1))) = ⊤ := by
  rw [eq_top_iff, ← h.gen]
  refine Subgroup.closure_mono ?_
  rintro x (((((hx | hx) | hx) | hx) | hx) | hx)
  · exact Set.mem_iUnion.2 ⟨0, Or.inl (mem_range_phiOf (Pi.single 0 1) 0 (by decide) x hx)⟩
  · exact Set.mem_iUnion.2 ⟨0, Or.inr (mem_range_phiOf (-Pi.single 0 1) 1 (by decide) x hx)⟩
  · exact Set.mem_iUnion.2 ⟨1, Or.inl (mem_range_phiOf (Pi.single 1 1) 2 (by decide) x hx)⟩
  · exact Set.mem_iUnion.2 ⟨1, Or.inr (mem_range_phiOf (-Pi.single 1 1) 3 (by decide) x hx)⟩
  · exact Set.mem_iUnion.2 ⟨2, Or.inl (mem_range_phiOf (Pi.single 2 1) 4 (by decide) x hx)⟩
  · exact Set.mem_iUnion.2 ⟨2, Or.inr (mem_range_phiOf (-Pi.single 2 1) 5 (by decide) x hx)⟩

theorem hnt : ∃ k : Fin 3, ∃ x,
    phiOf (rootDatum 3 F) (Sp.x 3 F) (c3PsiOf f) (Pi.single k 1) x ≠ 1 := by
  obtain ⟨c, hc⟩ := h.nt
  have key : ∀ γ : Fin 3 → ℤ, c3r 0 = γ →
      ∃ x, phiOf (rootDatum 3 F) (Sp.x 3 F) (c3PsiOf f) γ x ≠ 1 := by
    rintro γ rfl
    refine ⟨⟨Sp.x 3 F (c3r 0) c, x_mem_rootGroup Sp.isParametrization
      (c3_mem_roots (c3r_mem 0)) c⟩, ?_⟩
    exact fun h1 => hc ((c3PsiOf_r f 0 c).symm.trans
      ((phiOf_x Sp.isParametrization (c3PsiOf f) (c3_mem_roots (c3r_mem 0)) c _).symm.trans h1))
  exact ⟨0, key (Pi.single 0 1) (by decide)⟩

end IsC3Frame

theorem sp3_isPGroup [CharP F 2] :
    ∀ γ ∈ (rootDatum 3 F).roots, IsPGroup 2 ((rootDatum 3 F).rootGroup γ) :=
  fun _ hγ => isPGroup_of_param Sp.isParametrization hγ

theorem sp3_commuting [CharP F 2] (i j : Fin 3) (hij : cartanC 3 i j = -2) :
    ∀ a ∈ Symplectic.rootGroup 3 F (Pi.single i 1),
      ∀ b ∈ Symplectic.rootGroup 3 F (Pi.single i 1 + Pi.single j 1),
      Commute a b := by
  have hij' : i = 1 ∧ j = 2 := by
    revert hij
    fin_cases i <;> fin_cases j <;> decide
  obtain ⟨rfl, rfl⟩ := hij'
  intro a ha b hb
  have e1 : (Pi.single (1 : Fin 3) 1 : Fin 3 → ℤ) = ![0, 1, 0] := by decide
  have e2 : (Pi.single (1 : Fin 3) 1 + Pi.single (2 : Fin 3) 1 : Fin 3 → ℤ) = ![0, 1, 1] := by
    decide
  rw [e1] at ha
  rw [e2] at hb
  obtain ⟨s, rfl⟩ := exists_x_eq Sp.isParametrization (c3_mem_roots (by decide)) ha
  obtain ⟨t, rfl⟩ := exists_x_eq Sp.isParametrization (c3_mem_roots (by decide)) hb
  exact sp3_commute_010_011 s t

end Frame

end CFSG.Timmesfeld.RankTwo
