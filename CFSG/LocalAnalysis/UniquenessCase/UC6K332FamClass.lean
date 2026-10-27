module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332RowsDef
import CFSG.LocalAnalysis.UniquenessCase.UC6K332P2
import CFSG.LocalAnalysis.UniquenessCase.UC6K332P5
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL2
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSp4
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSp4Even
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSU4Two
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSL4W
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL4DiagCore
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU4Field
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU4FieldOuter
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU4DiagWitness
import CFSG.Adapters.ClassicalCatalogReverse
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Open.PGLModelStated
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
import CFSG.RankThree.PartOne.KF.R7Final
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowsBridge
import CFSG.RankThree.SubgroupLists.ExtraspecialNormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Blueprint CFSG.PGLModel
open CFSG.RankThree.PartTwo.Sec4.RonanK432

private theorem three_ne_zero_gf {p f : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) :
    (3 : GaloisField p f) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : GaloisField p f) = 0 := by exact_mod_cast h
  have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (GaloisField p f) p 3).mp h'
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp hdvd)

private theorem ne_three_of_pow_mod {p f r : ℕ} (hf : 1 ≤ f) (hr : r ≠ 0) (hq : p ^ f % 3 = r) :
    p ≠ 3 := by
  rintro rfl
  obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
  rw [pow_succ] at hq
  omega

private theorem exists_cube_root_gf {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (hq : p ^ f % 3 = 1) :
    ∃ ω : GaloisField p f, ω ^ 2 + ω + 1 = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card (GaloisField p f)ˣ := by
    rw [Nat.card_units, GaloisField.card p f (by omega)]
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField p f)ˣ) 3 hdvd
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    norm_num at hu
  refine ⟨(u : GaloisField p f), ?_⟩
  have h3 : (u : GaloisField p f) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  have hne : (u : GaloisField p f) ≠ 1 := fun h => hu1 (Units.ext h)
  have hfac : ((u : GaloisField p f) - 1) *
      ((u : GaloisField p f) ^ 2 + (u : GaloisField p f) + 1) = 0 := by
    linear_combination h3
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

private theorem noroot_gf {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (hq : p ^ f % 3 = 2)
    (hp3 : p ≠ 3) : ∀ c : GaloisField p f, c ^ 2 + c + 1 ≠ 0 := by
  intro c hc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := three_ne_zero_gf (p := p) (f := f) hp3
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hc3 : c ^ 3 = 1 := by linear_combination (c - 1) * hc
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply h3
    linear_combination hc
  let u : (GaloisField p f)ˣ := Units.mk0 c hc0
  have hu3 : u ^ 3 = 1 := Units.ext (by simp [u, hc3])
  have hu1 : u ≠ 1 := fun h => hc1 (by simpa [u] using congrArg Units.val h)
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hdvd : 3 ∣ Nat.card (GaloisField p f)ˣ := hord ▸ orderOf_dvd_natCard u
  rw [Nat.card_units, GaloisField.card p f (by omega)] at hdvd
  omega

theorem goodRow_psl2_27 {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : LieModel S .PSL 2 3 3) : GoodRow S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := nonempty_projSL_of_lieModel h
  exact rowOf_projSL_two (GaloisField 3 3) S hs hna ⟨e⟩

theorem goodRow_psp4_three_one {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : LieModel S .PSp 2 3 1) : GoodRow S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : LieModel S .PSU 4 2 1 :=
    Or.inl ⟨by decide, CFSG.ClassicalModels.statedClassicalModel_PSU_four_two_of_PSp_two_three
      (h.statedClassicalModel (by decide))⟩
  obtain ⟨e⟩ := nonempty_projSU_of_lieModel hU
  exact rowOf_seven_SU4 1 le_rfl S hs hna ⟨e⟩

theorem goodRow_psp4 {S : Type} [Group S] [Finite S] {p f : ℕ} (h : LieModel S .PSp 2 p f)
    (hp3 : p ≠ 3) : GoodRow S := by
  haveI : Fact p.Prime := ⟨h.admissible.1⟩
  obtain ⟨e⟩ := nonempty_projSp_of_lieModel h
  have hlist : ListRow (projSp 2 (GaloisField p f)) := listRow_projSp_two (three_ne_zero_gf hp3)
  by_cases hp2 : p = 2
  · subst hp2
    exact GoodRow.of_mulEquiv e.symm ⟨hlist, evenSp4_outerRow_projSp (GaloisField 2 f)⟩
  · obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨eS⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
    exact ⟨ListRow.of_mulEquiv e.symm hlist,
      OuterRow.of_mulEquiv eS.symm (outerRow_statedProj_sp_two_odd hp hp2 hp3 hf hK)⟩

theorem three_le_pRank_of_psp4_char_three {L : Type} [Group L] [Finite L] {f : ℕ}
    (h : LieModel L .PSp 2 3 f) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨-, hf, h1⟩ := CFSG.SectionRank.classical_model_rank (by norm_num : (3 : ℕ) ≠ 2)
    (h.statedClassicalModel (by decide))
  rcases h1 with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, ⟨-, h2⟩ | h2⟩ | h2
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · omega
  · omega
  · omega

theorem outerRow_psl4 (hR : K332Rows) {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : LieModel S .PSL 4 p f) (hp3 : p ≠ 3) : OuterRow S := by
  haveI : Fact p.Prime := ⟨h.admissible.1⟩
  by_cases hf1 : f = 1
  · subst hf1
    obtain ⟨e⟩ := nonempty_projSL_of_lieModel h
    exact OuterRow.of_mulEquiv e.symm (outerRow_projSL_four_sl4w p)
  · exact hR.outer_psl4 S p f h hp3 (by have := h.admissible.2.1; omega)

theorem outerRow_psu4 (hR : K332Rows) {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : LieModel S .PSU 4 p f) (hp3 : p ≠ 3) : OuterRow S := by
  haveI : Fact p.Prime := ⟨h.admissible.1⟩
  have hf : 1 ≤ f := h.admissible.2.1
  obtain ⟨e⟩ := nonempty_projSU_of_lieModel h
  by_cases hp2 : p = 2
  · subst hp2
    exact OuterRow.of_mulEquiv e.symm (outerRow_projSU_four_two_all hf)
  · by_cases hf1 : f = 1
    · subst hf1
      exact OuterRow.of_mulEquiv e.symm outerRow_projSU_four_prime
    · exact hR.outer_psu4 S p f h hp2 hp3 (by omega)

theorem goodRow_psl4_of_mod_two (hR : K332Rows) {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : LieModel S .PSL 4 p f) (hq : p ^ f % 3 = 2) : GoodRow S := by
  haveI : Fact p.Prime := ⟨h.admissible.1⟩
  have hp3 : p ≠ 3 := ne_three_of_pow_mod h.admissible.2.1 (by norm_num) hq
  obtain ⟨e⟩ := nonempty_projSL_of_lieModel h
  exact ⟨ListRow.of_mulEquiv e.symm (listRow_projSL_four_of_noroot (three_ne_zero_gf hp3)
      (noroot_gf h.admissible.2.1 hq hp3)), outerRow_psl4 hR h hp3⟩

theorem goodRow_psl4_of_mod_one (hR : K332Rows) {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : LieModel S .PSL 4 p f) (hq : p ^ f % 3 = 1) : GoodRow S := by
  haveI : Fact p.Prime := ⟨h.admissible.1⟩
  have hp3 : p ≠ 3 := ne_three_of_pow_mod h.admissible.2.1 (by norm_num) hq
  obtain ⟨e⟩ := nonempty_projSL_of_lieModel h
  obtain ⟨ω, hω⟩ := exists_cube_root_gf h.admissible.2.1 hq
  exact ⟨ListRow.of_mulEquiv e.symm (L4Diag.listRow_projSL_four_of_cube_root hω
      (three_ne_zero_gf hp3)), outerRow_psl4 hR h hp3⟩

theorem goodRow_psu4_of_mod_one (hR : K332Rows) {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : LieModel S .PSU 4 p f) (hq : p ^ f % 3 = 1) : GoodRow S := by
  haveI : Fact p.Prime := ⟨h.admissible.1⟩
  have hp3 : p ≠ 3 := ne_three_of_pow_mod h.admissible.2.1 (by norm_num) hq
  obtain ⟨e⟩ := nonempty_projSU_of_lieModel h
  exact ⟨ListRow.of_mulEquiv e.symm (listRow_projSU_four_of_dvd h.admissible.2.1 (by omega)),
    outerRow_psu4 hR h hp3⟩

theorem goodRow_psu4_of_mod_two (hR : K332Rows) {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : LieModel S .PSU 4 p f) (hq : p ^ f % 3 = 2) : GoodRow S := by
  haveI : Fact p.Prime := ⟨h.admissible.1⟩
  have hp3 : p ≠ 3 := ne_three_of_pow_mod h.admissible.2.1 (by norm_num) hq
  obtain ⟨e⟩ := nonempty_projSU_of_lieModel h
  exact ⟨ListRow.of_mulEquiv e.symm (listRow_projSU_four_of_dvd_succ h.admissible.2.1 (by omega)),
    outerRow_psu4 hR h hp3⟩

theorem goodRow_psl5 {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {p f : ℕ} (h : LieModel S .PSL 5 p f)
    (hq : p ^ f % 3 = 2) : GoodRow S := by
  haveI : Fact p.Prime := ⟨h.admissible.1⟩
  obtain ⟨e⟩ := nonempty_projSL_of_lieModel h
  exact ⟨listRowOf_projSL_five p f hq S hs hna ⟨e⟩, outerRowOf_projSL_five p f hq S hs hna ⟨e⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
