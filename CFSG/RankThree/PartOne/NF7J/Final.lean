module

public import CFSG.RankThree.PartOne.NF7J.Norm
public import CFSG.RankThree.PartOne.NF7J.Lines
public import CFSG.RankThree.PartOne.NF7J.EvenG
public import CFSG.RankThree.PartOne.NF7J.PairStmt
public import CFSG.RankThree.PartOne.NF7J.Refl

public section

namespace CFSG.RankThree.PartOne.NF7J

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartOne

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem nf7j_false_odd
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hEA : E = A) (hdvd : p ∣ 2 ^ f - 1)
    (hodd : 2 ^ f % 3 = 2)
    (hmem : ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s * t ≠ t * s →
      (∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
        conjAut E w hw * s * (conjAut E w hw)⁻¹ ∈ torusImage E L) →
      (∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
        conjAut E w hw * t * (conjAut E w hw)⁻¹ ∈ torusImage E L) →
      ∃ J ∈ thetaCompZeroStarE p E, s ∈ torusImage E J ∧ t ∈ torusImage E J)
    (F : RFrame G p c L E f K) (D : Datum p E) (X : EFacts G p c E) : False := by
  obtain ⟨φ, N⟩ := exists_norm_aut F D X
  exact odd_false X N hdvd hodd (linesComm_of hGA h hF13 hEA hdvd
    (fun s hs t ht hst => hmem s hs t ht hst (exists_conj_into_L F (D.withE φ) X hs)
      (exists_conj_into_L F (D.withE φ) X ht))
    (fun s hs => kfAt_refl F (D.withE φ) X hs) (D.withE φ).exp6 (D.withE φ).exp8 (D.withE φ).hν)

theorem two_pow_mod_three_of_odd {f : ℕ} (hodd : Odd f) : 2 ^ f % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hodd
  have h4 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]
    norm_num [mul_comm]
  rw [this]
  omega

theorem nf7j_false
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hEA : E = A)
    (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 2 f) (hdvd : p ∣ 2 ^ f - 1)
    (hmem : ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s * t ≠ t * s →
      (∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
        conjAut E w hw * s * (conjAut E w hw)⁻¹ ∈ torusImage E L) →
      (∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
        conjAut E w hw * t * (conjAut E w hw)⁻¹ ∈ torusImage E L) →
      ∃ J ∈ thetaCompZeroStarE p E, s ∈ torusImage E J ∧ t ∈ torusImage E J)
    (D : Datum p E) : False := by
  have hf1 : 1 ≤ f := hmodel.1.2.1
  obtain ⟨K, hKf, hKfin, hchar, ⟨F⟩⟩ := exists_rframe hGA h hF hF13 hEA hf1 hdvd hmodel
  have hcE : c ∈ E := by rw [hEA]; exact h.c_mem
  have X : EFacts G p c E :=
    { prime := h.prime
      five_le := Sec12Three.five_le h
      c_mem := hcE
      c_ne := h.c_ne_one
      c_pow := Sec12Three.pow_eq_one_of_mem_E h hcE
      comm := fun x y => Subtype.ext (Torsion37.mul_comm_of_isElementaryAbelian h.E_elem x.2 y.2) }
  rcases Nat.even_or_odd f with hev | hodd
  · obtain ⟨φ, N⟩ := exists_norm_aut F D X
    exact nf7j_false_even F (D.withE φ) X N hev
  · exact nf7j_false_odd hGA h hF13 hEA hdvd (two_pow_mod_three_of_odd hodd) hmem F D X

theorem nf7j_false_of_pair
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hP : PairMember) (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E = A)
    (hnL3 : ¬ IsLThreeTypeAt p L) (hm7 : RowModel p L 7) (D : Datum p E) : False := by
  obtain ⟨f, -, hdvd, hmodel⟩ := id hm7
  exact nf7j_false hGA h hF hF13 hEA hmodel hdvd
    (fun s hs t ht hst hsL htL => hP G p A c L E h hF hF13 hT hEA hnL3 hm7 s hs t ht hst hsL htL) D

end CFSG.RankThree.PartOne.NF7J
