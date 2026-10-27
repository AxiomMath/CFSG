module

public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Off
public import CFSG.Quasithin.EmptyFaithful.T1521SOff
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Coord

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Quasithin.Sp4

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_inf_conj_iff {S L : Subgroup G} {a : G} (haS : a ∈ S)
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (y : G) :
    y ∈ S ⊓ L ↔ a * y * a⁻¹ ∈ S ⊓ L := by
  constructor
  · rintro ⟨hyS, hyL⟩
    exact ⟨S.mul_mem (S.mul_mem haS hyS) (S.inv_mem haS),
      (Subgroup.mem_normalizer_iff.mp haL y).mp hyL⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp haL y).mpr h2⟩
    have := S.mul_mem (S.mul_mem (S.inv_mem haS) h1) haS
    simpa [mul_assoc] using this

theorem thompsonJ_le_innerPart_sp4 {S L : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hL : IsPSp4 2 n ↥L) (hSyl : IsSylowTwoOf (S ⊓ L) L) (hS2 : IsPGroup 2 S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) :
    thompsonJ S ≤ innerPart1521 S L := by
  obtain ⟨K, hKf, hKfin, φ, hK, hφ⟩ := exists_equiv_projUnipotent hn hL hSyl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  have hRL : S ⊓ L ≤ L := inf_le_right
  have hRS : S ⊓ L ≤ S := inf_le_left
  have hVR : vSub φ ≤ S ⊓ L := vSub_le_R hφ
  refine thompsonJ_le_innerPart_of_offender (V := vSub φ) (hVR.trans hRS) isElemAbelian_vSub
    ?_ ?_
  ·
    rintro s ⟨hsS, hsC⟩
    obtain ⟨l₁, l₂, σ, ε, -, -, hact, hinner⟩ := exists_vAct_conj (φ := φ) (by omega) hK hφ
      (hSN hsS) (fun y _ => mem_inf_conj_iff hsS (hSN hsS) y)
    have hid : ∀ x : K × K, vAct l₁ l₂ σ ε x = x := by
      intro x
      apply vW_injective φ
      rw [← hact x]
      have h1 := Subgroup.mem_centralizer_iff.mp hsC (vW φ x) (vW_mem φ x)
      rw [mul_inv_eq_iff_eq_mul]
      exact h1.symm
    obtain ⟨l, hlR, hlc⟩ := hinner hid
    have hlS : (l : G) ∈ S := hlR.1
    have hs : s = (l : G) * ((l : G)⁻¹ * s) := by group
    rw [hs]
    exact Subgroup.mul_mem_sup hlR ⟨S.mul_mem (S.inv_mem hlS) hsS, hlc⟩
  ·
    intro A hA hAS hineq
    refine centralizes_of_offender_vAct hn hK (vW φ) (vW_injective φ) (vW_mem φ)
      (fun y hy => exists_vW_of_mem φ hy) hA ?_ ?_ hineq
    · intro a ha
      obtain ⟨l₁, l₂, σ, ε, h1, h2, hact, -⟩ := exists_vAct_conj (φ := φ) (by omega) hK hφ
        (hSN (hAS ha)) (fun y _ => mem_inf_conj_iff (hAS ha) (hSN (hAS ha)) y)
      exact ⟨l₁, l₂, σ, ε, h1, h2, hact⟩
    · exact card_le_two_mul_of_out (by omega) hK φ hSN hS2 hRL hRS hSyl (vSub_le_L φ)
        (fun r hr v hv => by
          obtain ⟨x, rfl⟩ := exists_vW_of_mem φ hv
          exact vW_commute_R hφ hRL hr x) hAS hA

end CFSG.Quasithin
