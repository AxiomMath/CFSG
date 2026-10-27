module

public import CFSG.Monster.Schur.CentralEps
public import CFSG.Sporadic.Bridge.J3Surj
public import CFSG.Sporadic.Recognition.CoverRecipe
public import CFSG.Sporadic.Recognition.J3MultiplierWords

public section

namespace CFSG.Sporadic.Recognition.J3Multiplier

open CFSG.CosetTable CFSG.Monster.Schur CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Sporadic.Recognition.CoverTransfer
open CFSG.Sporadic.J3 (a b J rep_a rep_b faithful j3Facts closure_ab)
open CFSG.Sporadic.J3.Native (j3Data)
open CFSG.Sporadic.Th (Rep)

@[expose] noncomputable def ab (i : Fin 2) : J j3Data := img2 (a j3Data) (b j3Data) i.val

@[expose] noncomputable def gen (i : Fin 2) : J j3Data :=
  FreeGroup.lift ab (FreeGroup.mk (genWords.getD i []))

theorem gen_zero : gen 0 = a j3Data := by
  simp [gen, genWords, ab, img2, FreeGroup.lift_mk]

theorem gen_one : gen 1 = a j3Data * b j3Data := by
  simp [gen, genWords, ab, img2, FreeGroup.lift_mk]

theorem closure_gen : Subgroup.closure (Set.range gen) = ⊤ := by
  rw [eq_top_iff, ← closure_ab j3Data, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact Subgroup.subset_closure ⟨0, gen_zero⟩
  · have h0 : a j3Data ∈ Subgroup.closure (Set.range gen) :=
      Subgroup.subset_closure ⟨0, gen_zero⟩
    have h1 : a j3Data * b j3Data ∈ Subgroup.closure (Set.range gen) :=
      Subgroup.subset_closure ⟨1, gen_one⟩
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h0) h1
    simpa using this

section Lifts

variable {E : Type*} [Group E]

theorem lift_rep (f : Fin 2 → E) (n : ℕ) (u : List (Fin 2 × Bool)) :
    FreeGroup.lift f (FreeGroup.mk (rep n u)) = FreeGroup.lift f (FreeGroup.mk u) ^ n := by
  rw [rep, mk_flatten_replicate, map_pow]

theorem lift_ac3 (f : Fin 2 → E) : FreeGroup.lift f (FreeGroup.mk ac3) = (f 0 * f 1) ^ 3 := by
  rw [ac3, lift_rep]
  simp [FreeGroup.lift_mk]

theorem lift_c19 (f : Fin 2 → E) : FreeGroup.lift f (FreeGroup.mk c19) = f 1 ^ 19 := by
  rw [c19, lift_rep]
  simp [sc, FreeGroup.lift_mk]

theorem lift_a2 (f : Fin 2 → E) : FreeGroup.lift f (FreeGroup.mk a2) = f 0 ^ 2 := by
  simp [a2, FreeGroup.lift_mk, pow_succ]

theorem lift_a2inv (f : Fin 2 → E) :
    FreeGroup.lift f (FreeGroup.mk a2inv) = (f 0)⁻¹ * (f 0)⁻¹ := by
  simp [a2inv, FreeGroup.lift_mk]

theorem lift_conjWord (f : Fin 2 → E) (c u : List (Fin 2 × Bool)) :
    FreeGroup.lift f (FreeGroup.mk (conjWord c u)) =
      FreeGroup.lift f (FreeGroup.mk c) * f 0 * (FreeGroup.lift f (FreeGroup.mk c))⁻¹ *
        (FreeGroup.lift f (FreeGroup.mk u))⁻¹ := by
  simp only [conjWord, lift_mk_append, ← FreeGroup.inv_mk, map_inv]
  simp [FreeGroup.lift_mk]

end Lifts

theorem sq_eq_of_conj {E G : Type*} [Group E] [Group G] (π : E →* G) (hπ : Function.Surjective π)
    (hk : Nat.card π.ker = 2) {x a : E} (ha : π a ^ 2 = 1) (c : G)
    (hc : c * π a * c⁻¹ = π x) : x ^ 2 = a ^ 2 := by
  obtain ⟨ĉ, rfl⟩ := hπ c
  set y := ĉ * a * ĉ⁻¹ with hy
  have hyx : y⁻¹ * x ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy]
    simp only [map_mul, map_inv]
    rw [hc]
    group
  have hkc := mem_center_of_mem_ker π hk hyx
  have hk2 := sq_eq_one_of_mem_ker π hk hyx
  have ha2 : a ^ 2 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow]; exact ha
  have ha2c := mem_center_of_mem_ker π hk ha2
  have hxy : x = y * (y⁻¹ * x) := by group
  have hcomm : Commute (y⁻¹ * x) y := ((Subgroup.mem_center_iff.mp hkc) y).symm
  have e1 : x ^ 2 = y ^ 2 * (y⁻¹ * x) ^ 2 := by
    conv_lhs => rw [hxy]
    rw [hcomm.symm.mul_pow]
  have e2 : y ^ 2 = a ^ 2 := by
    have : y ^ 2 = ĉ * a ^ 2 * ĉ⁻¹ := by rw [hy]; simp only [sq]; group
    rw [this]
    have := (Subgroup.mem_center_iff.mp ha2c) ĉ
    calc ĉ * a ^ 2 * ĉ⁻¹ = (ĉ * a ^ 2) * ĉ⁻¹ := rfl
      _ = (a ^ 2 * ĉ) * ĉ⁻¹ := by rw [this]
      _ = a ^ 2 := by group
  rw [e1, e2, hk2, mul_one]

section Tables

theorem lift_ab_eq_one (h : j3RelCheck j3Data natWords = true) {w : List (Fin 2 × Bool)}
    (hw : w ∈ checkWords.map (substWord genWords)) :
    FreeGroup.lift ab (FreeGroup.mk w) = 1 := by
  have := faithful j3Facts
  have hA := rep_a j3Facts.orbitFacts
  have hB := rep_b j3Facts.orbitFacts
  exact CFSG.Sporadic.Recognition.CoverRecipe.lift_eq_one_of_relCheck
    (lt_trans j3Facts.n_lt (by norm_num)) hA (Rep.inv_of_invOK hA j3Facts.invA) hB
    (Rep.inv_of_invOK hB j3Facts.invB) h hw

theorem lift_gen_eq_one (h : j3RelCheck j3Data natWords = true) {w : List (Fin 2 × Bool)}
    (hw : w ∈ checkWords) : FreeGroup.lift gen (FreeGroup.mk w) = 1 := by
  have h1 : FreeGroup.lift gen (FreeGroup.mk w) =
      FreeGroup.lift ab (FreeGroup.mk (substWord genWords w)) :=
    lift_mk_substWord ab genWords w
  rw [h1]
  exact lift_ab_eq_one h (List.mem_map_of_mem hw)

theorem conj_gen (h : j3RelCheck j3Data natWords = true) {c u : List (Fin 2 × Bool)}
    (hc : conjWord c u ∈ checkWords) :
    FreeGroup.lift gen (FreeGroup.mk c) * gen 0 * (FreeGroup.lift gen (FreeGroup.mk c))⁻¹ =
      FreeGroup.lift gen (FreeGroup.mk u) := by
  have := lift_gen_eq_one h hc
  rw [lift_conjWord] at this
  exact mul_inv_eq_one.mp this

theorem exists_lifts (h : j3RelCheck j3Data natWords = true) (E : Type) [Group E]
    (π : E →* J j3Data) (hπ : Function.Surjective π) (hk : Nat.card π.ker = 2) :
    ∃ ĝ : Fin 2 → E, (∀ i, π (ĝ i) = gen i) ∧
      ∀ r ∈ U, FreeGroup.lift ĝ (FreeGroup.mk r) = 1 := by
  obtain ⟨a₀, ha₀⟩ := hπ (gen 0)
  obtain ⟨c₀, hc₀⟩ := hπ (gen 1)
  have hc19 : π c₀ ^ 19 = 1 := by
    rw [hc₀, ← lift_c19 gen]
    exact lift_gen_eq_one h (by simp [checkWords, U])
  have hac3 : (π a₀ * π c₀) ^ 3 = 1 := by
    rw [ha₀, hc₀, ← lift_ac3 gen]
    exact lift_gen_eq_one h (by simp [checkWords, U])
  obtain ⟨a', c', ha', hc', hc19', hac3'⟩ :=
    exists_lift_pair π hk a₀ c₀ ⟨9, rfl⟩ ⟨1, rfl⟩ hc19 hac3
  set ĝ : Fin 2 → E := ![a', c'] with hĝdef
  have hĝ : ∀ i, π (ĝ i) = gen i := by
    intro i
    fin_cases i
    · simp [ĝ, ha', ha₀]
    · simp [ĝ, hc', hc₀]
  have hlift : ∀ w, π (FreeGroup.lift ĝ (FreeGroup.mk w)) =
      FreeGroup.lift gen (FreeGroup.mk w) := by
    intro w
    have : π.comp (FreeGroup.lift ĝ) = FreeGroup.lift gen := by
      apply FreeGroup.ext_hom
      intro i
      simp [hĝ]
    exact DFunLike.congr_fun this (FreeGroup.mk w)
  have ha2 : π (ĝ 0) ^ 2 = 1 := by
    rw [hĝ, ← lift_a2 gen]
    exact lift_gen_eq_one h (by simp [checkWords])
  have key : ∀ {c u : List (Fin 2 × Bool)}, conjWord c u ∈ checkWords →
      FreeGroup.lift ĝ (FreeGroup.mk u) ^ 2 = ĝ 0 ^ 2 := by
    intro c u hc
    refine sq_eq_of_conj π hπ hk ha2 (FreeGroup.lift gen (FreeGroup.mk c)) ?_
    rw [hĝ 0, hlift]
    exact conj_gen h hc
  refine ⟨ĝ, hĝ, fun r hr => ?_⟩
  simp only [U, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [lift_ac3]
    simpa [ĝ] using hac3'
  · rw [lift_c19]
    simpa [ĝ] using hc19'
  · rw [lift_mk_append, r5, lift_rep, key (c := c5) (by simp [checkWords]), lift_a2inv]
    group
  · rw [lift_mk_append, r6, lift_rep, key (c := c6) (by simp [checkWords]), lift_a2inv]
    group
  · rw [lift_mk_append, r8, lift_rep, key (c := c8) (by simp [checkWords]), lift_a2inv]
    group

theorem lift_gen_T (h : j3RelCheck j3Data natWords = true) (i : Fin 2) :
    FreeGroup.lift gen (FreeGroup.mk (T i)) = 1 := by
  fin_cases i
  · exact lift_gen_eq_one h (by simp [checkWords, T])
  · exact lift_gen_eq_one h (by simp [checkWords, T])

theorem card_J : Nat.card (J j3Data) = 50232960 := by
  rw [← Nat.card_congr CFSG.Sporadic.Bridge.J3.nativeEquiv.toEquiv, CFSG.Sporadic.J3.card_J3]

end Tables

end CFSG.Sporadic.Recognition.J3Multiplier
