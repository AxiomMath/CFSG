module

public import CFSG.RankThree.PartTwo.Sec21.FF79Reduce
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec4Defs
public import CFSG.RankThree.PartTwo.Sec21.HeringFFGF2

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

@[expose] def FF79TheoremA_simpleK5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J : Subgroup G),
    IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
      FF79Hyp 5 b J → ConjInto b J

theorem ff79Extraspecial_of5 (h13 : FF79_1_3) (hA : FF79TheoremA_simpleK5) (h43 : FF79_4_3)
    (h44 : FF79_4_4X) : FF79Extraspecial := by
  intro G _ _ _ hnab hchar hkp b hb J hJ hmod hcyc hnsc hrk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyp : FF79Hyp 5 b J := ⟨hb, hJ, hmod, hcyc, hnsc, hrk⟩
  obtain ⟨B, hB⟩ := exists_isSylowOf 3 (Cen b)
  have hconj := hA G b J inferInstance hnab hkp hyp
  obtain ⟨-, -, -, hcase⟩ := h13 G 5 (Or.inr rfl) b J hyp B hB
  rcases hcase with ⟨hnc, -⟩ | ⟨-, -, b₁, hb₁, b₂, hb₂, hmono⟩
  · exact absurd hconj hnc
  have h4 : FF79Sec4 b J B b₁ b₂ :=
    ⟨inferInstance, Assembly.isCharTwoType_iff_isCharacteristicPType.mp hchar, hyp, hconj, hB,
      hb₁, hb₂, hmono, hnab, hkp⟩
  obtain ⟨hodd, -⟩ := h43 G b J B b₁ b₂ h4
  obtain ⟨-, hBcl, -, ⟨n, -, hnb, hn1, hn2⟩, -, -⟩ := hmono
  have hsq := sq_conj_eq_of_diag hBcl hnb hn1 hn2
  have hbB : b ∈ B := hBcl ▸ Subgroup.subset_closure (by simp)
  have hb1 : b⁻¹ ≠ b := by
    intro h
    have : b ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [← h]; exact inv_mul_cancel b
    have := orderOf_dvd_of_pow_eq_one this
    rw [hb] at this
    omega
  obtain ⟨m, hm, ht⟩ := exists_involution_of_odd hodd hsq hbB hb1 hnb
  have hcomm : ∀ {x : G}, x ∈ B → n * x * n⁻¹ = x → n ^ m * x = x * n ^ m := by
    intro x hx hnx
    have := conj_pow_odd_eq (hsq x hx) hm
    rw [hnx] at this
    calc n ^ m * x = (n ^ m * x * (n ^ m)⁻¹) * n ^ m := by group
      _ = x * n ^ m := by rw [this]
  have hb₁B : b₁ ∈ B := hBcl ▸ Subgroup.subset_closure (by simp)
  have hb₂B : b₂ ∈ B := hBcl ▸ Subgroup.subset_closure (by simp)
  have hT := h44 G b J B b₁ b₂ h4 (n ^ m) ht (hcomm hb₁B hn1) (hcomm hb₂B hn2)
    ((conj_pow_odd_eq (hsq b hbB) hm).trans hnb)
  exact ⟨n ^ m, ht, hT⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
