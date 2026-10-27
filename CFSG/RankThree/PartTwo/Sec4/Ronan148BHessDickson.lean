module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Orders
import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open CFSG.BenderSuzuki.MatrixGroups
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (commute_of_equiv_dihedral
  orderOf_dvd_of_equiv_alternating_four orderOf_dvd_of_equiv_perm_four
  orderOf_dvd_of_equiv_alternating_five)

theorem commutator_mem_of_sup_eq_top {H : Type*} [Group H] {N C : Subgroup H} (hN : N.Normal)
    (hC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) (hNC : N ⊔ C = ⊤) (a b : H) :
    a * b * a⁻¹ * b⁻¹ ∈ N := by
  have hmem : ∀ x : H, ∃ n ∈ N, ∃ c ∈ C, x = n * c := by
    intro x
    have hx : x ∈ ((N ⊔ C : Subgroup H) : Set H) := by rw [hNC]; exact Subgroup.mem_top x
    rw [Subgroup.normal_mul] at hx
    obtain ⟨n, hn, c, hc, h⟩ := Set.mem_mul.mp hx
    exact ⟨n, hn, c, hc, h.symm⟩
  obtain ⟨n₁, hn₁, c₁, hc₁, rfl⟩ := hmem a
  obtain ⟨n₂, hn₂, c₂, hc₂, rfl⟩ := hmem b
  refine (QuotientGroup.eq_one_iff _).mp ?_
  have h₁ : (QuotientGroup.mk (n₁ * c₁) : H ⧸ N) = QuotientGroup.mk c₁ := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n₁).mpr hn₁, one_mul]
  have h₂ : (QuotientGroup.mk (n₂ * c₂) : H ⧸ N) = QuotientGroup.mk c₂ := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n₂).mpr hn₂, one_mul]
  have hcc : (QuotientGroup.mk c₁ : H ⧸ N) * QuotientGroup.mk c₂ =
      QuotientGroup.mk c₂ * QuotientGroup.mk c₁ := by
    rw [← QuotientGroup.mk_mul, hC c₁ hc₁ c₂ hc₂, QuotientGroup.mk_mul]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h₁, h₂, hcc]
  group

theorem dickson_large {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] (hF : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    {x y : H} (hx : 2 < orderOf x) (hy : 2 < orderOf y) (hxy : x * y ≠ y * x)
    {w : H} (hw2 : w ^ 2 ≠ 1) (hw3 : w ^ 3 ≠ 1) (hw4 : w ^ 4 ≠ 1) (hw5 : w ^ 5 ≠ 1)
    (hB : ∀ N : Subgroup H, N.Normal → IsElementaryAbelian p N →
      (∀ a b : H, a * b * a⁻¹ * b⁻¹ ∈ N) → False) :
    (∃ m, m ≠ 0 ∧ m ∣ f ∧ Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m))) ∨
      (∃ m, m ≠ 0 ∧ 2 * m ∣ f ∧
        Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) := by
  have hpow : ∀ k : ℕ, orderOf w ∣ k → w ^ k = 1 := fun k hk => orderOf_dvd_iff_pow_eq_one.mp hk
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF H with
    hel | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNel, -, hC, -, -, hNC⟩ | hPSL | hPGL
  · exact absurd (hel.toIsMulCommutative.is_comm.comm x y) hxy
  · exact absurd (hcyc.commGroup.mul_comm x y) hxy
  · exact absurd
      (commute_of_equiv_dihedral e hx hy)
      hxy
  · rcases
      orderOf_dvd_of_equiv_alternating_four
        e w with h | h
    · exact absurd (hpow 2 h) hw2
    · exact absurd (hpow 3 h) hw3
  · rcases orderOf_dvd_of_equiv_perm_four
      e w with h | h
    · exact absurd (hpow 3 h) hw3
    · exact absurd (hpow 4 h) hw4
  · rcases
      orderOf_dvd_of_equiv_alternating_five
        e w with h | h | h
    · exact absurd (hpow 2 h) hw2
    · exact absurd (hpow 3 h) hw3
    · exact absurd (hpow 5 h) hw5
  · have hCc : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
      intro a ha b hb
      have := hC.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val this
    exact (hB N hN hNel (commutator_mem_of_sup_eq_top hN hCc hNC)).elim
  · exact Or.inl hPSL
  · exact Or.inr hPGL

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
