module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ CFSG.Quasithin.A94.He42PD

variable {G : Type} [Group G] [Finite G]

private theorem he42ps_card_map {Δ : Type*} [Group Δ] {L J A : Subgroup Δ}
    {ψ : ↥L →* Equiv.Perm (Fin 5)} (hker : ψ.ker = A.subgroupOf L) (hAL : A ≤ L) (hAJ : A ≤ J)
    (hJL : J ≤ L) (hA : Nat.card A = 64) (hJc : Nat.card J = 256) :
    Nat.card ((J.subgroupOf L).map ψ) = 4 := by
  have h1 : ψ.ker.relIndex (J.subgroupOf L) = Nat.card ((J.subgroupOf L).map ψ) :=
    Subgroup.relIndex_ker (K := J.subgroupOf L) (f := ψ)
  have h2 := Subgroup.relIndex_mul_card (H := A.subgroupOf L) (K := J.subgroupOf L)
  rw [inf_eq_left.mpr (Subgroup.subgroupOf_mono L hAJ)] at h2
  have hcA : Nat.card ↥(A.subgroupOf L) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hA]
  have hcJ : Nat.card ↥(J.subgroupOf L) = 256 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJL).toEquiv, hJc]
  rw [hker] at h1
  rw [hcA, hcJ] at h2
  omega

private theorem he42ps_pdata_mk {Δ : Type*} [Group Δ] {L K A J : Subgroup Δ}
    {ψ : ↥L →* Equiv.Perm (Fin 5)} (hKL : K ≤ L) (hAJ : A ≤ J) (hJK : J ≤ K)
    (hAn : ∀ l ∈ L, ∀ a ∈ A, l * a * l⁻¹ ∈ A) (hker : ψ.ker = A.subgroupOf L)
    (hrange : ψ.range = alternatingGroup (Fin 5)) (hstab : ∀ k : ↥L, ψ k 0 = 0 ↔ (k : Δ) ∈ K)
    (hA : Nat.card A = 64) (hJc : Nat.card J = 256) : PData L K A J ψ :=
  ⟨hKL, hAJ, hJK, hAn, hker, hrange, hstab,
    he42ps_card_map hker (hAJ.trans (hJK.trans hKL)) hAJ (hJK.trans hKL) hA hJc⟩

theorem HeSetup.stepPsi (S : HeSetup G) (hB : S.BaseFacts) : S.StepPsi := by
  unfold HeSetup.StepPsi
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨b, hb, hb1, hba, -, -, φ, hker, hrange, hstab⟩ :=
      S.hD.exists_alt5 S.hN S.hxN S.hxa S.hx3
    have hC : centralizer (S.B : Set G) = centralizer ({S.a} : Set G) ⊓ centralizer ({b} : Set G) :=
      S.hD.centralizer_B S.hxN S.hxa S.hx3 hb hb1 hba
    have hL1 : S.L1 = Lg S.A S.a b := by
      show normalizer (S.A : Set G) ⊓ centralizer (S.B : Set G) =
        (normalizer (S.A : Set G) ⊓ centralizer ({S.a} : Set G)) ⊓ centralizer ({b} : Set G)
      rw [hC, inf_assoc]
    have hK1 : S.K = Kg S.N S.a b := by
      show S.N ⊓ centralizer (S.B : Set G) =
        (S.N ⊓ centralizer ({S.a} : Set G)) ⊓ centralizer ({b} : Set G)
      rw [hC, inf_assoc]
    have hKL : Kg S.N S.a b ≤ Lg S.A S.a b := by
      rw [← hK1, ← hL1]
      exact hB.K_le_L1
    have hJK : S.J ≤ Kg S.N S.a b := by
      rw [← hK1]
      exact hB.J_le_K
    have hAn : ∀ l ∈ Lg S.A S.a b, ∀ a ∈ S.A, l * a * l⁻¹ ∈ S.A := by
      rw [← hL1]
      exact fun l hl a ha => (Subgroup.mem_normalizer_iff.mp (hB.L1_le_normalizer hl) a).mp ha
    rw [hL1, hK1]
    exact ⟨φ, he42ps_pdata_mk hKL hB.A_le_J hJK hAn hker hrange hstab hB.card_A hB.card_J⟩
  ·
    have hN' : S.N = normalizer ((S.A' ⊔ S.A : Subgroup G) : Set G) := by
      rw [S.hN, sup_comm]
    obtain ⟨b, hb, hb1, hba, -, -, φ, hker, hrange, hstab⟩ :=
      S.hD'.exists_alt5 hN' S.hxN S.hxa S.hx3
    have hBc : S.B = (S.A' ⊓ S.A) ⊓ centralizer ({S.x} : Set G) := by
      show (S.A ⊓ S.A') ⊓ centralizer ({S.x} : Set G) = (S.A' ⊓ S.A) ⊓ centralizer ({S.x} : Set G)
      rw [inf_comm S.A' S.A]
    have hC : centralizer (S.B : Set G) = centralizer ({S.a} : Set G) ⊓ centralizer ({b} : Set G) := by
      rw [hBc]
      exact S.hD'.centralizer_B S.hxN S.hxa S.hx3 hb hb1 hba
    have hL2 : S.L2 = Lg S.A' S.a b := by
      show normalizer (S.A' : Set G) ⊓ centralizer (S.B : Set G) =
        (normalizer (S.A' : Set G) ⊓ centralizer ({S.a} : Set G)) ⊓ centralizer ({b} : Set G)
      rw [hC, inf_assoc]
    have hK2 : S.K = Kg S.N S.a b := by
      show S.N ⊓ centralizer (S.B : Set G) =
        (S.N ⊓ centralizer ({S.a} : Set G)) ⊓ centralizer ({b} : Set G)
      rw [hC, inf_assoc]
    have hKL : Kg S.N S.a b ≤ Lg S.A' S.a b := by
      rw [← hK2, ← hL2]
      exact hB.K_le_L2
    have hJK : S.J ≤ Kg S.N S.a b := by
      rw [← hK2]
      exact hB.J_le_K
    have hAn : ∀ l ∈ Lg S.A' S.a b, ∀ a ∈ S.A', l * a * l⁻¹ ∈ S.A' := by
      rw [← hL2]
      exact fun l hl a ha => (Subgroup.mem_normalizer_iff.mp (hB.L2_le_normalizer hl) a).mp ha
    rw [hL2, hK2]
    exact ⟨φ, he42ps_pdata_mk hKL hB.A'_le_J hJK hAn hker hrange hstab hB.card_A' hB.card_J⟩

end CFSG.Quasithin.A94.He42
