module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2SShape
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TQB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL2S

open scoped Pointwise

namespace F6

namespace GoldAmL2T

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

@[expose] def yGrp (A B V : Subgroup D) : Subgroup D := conjClosure (kerK B V) A

section QA

variable [Finite D] {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem card_QA_of_card_T (hT : Nat.card ↥(A ⊓ B) = 64) : Nat.card ↥(pCoreOf 2 A) = 32 := by
  have := g.hyp.card_T_QA
  omega

theorem card_R_of_card_T (hT : Nat.card ↥(A ⊓ B) = 64) :
    Nat.card ↥(pCoreOf 2 A ⊓ pCoreOf 2 B) = 16 := by
  have := g.hyp.card_T_R
  omega

theorem a₁_not_mem_QA : a₁ ∉ pCoreOf 2 A := fun hQ => by
  have hc : a₁ ∈ A ⊓ Subgroup.centralizer (V : Set D) := by
    rw [g.hyp.natural.centralizer_eq]; exact hQ
  exact g.not_comm01 (Subgroup.mem_centralizer_iff.mp hc.2 a g.a_mem)

theorem card_U_inf_QA_le : Nat.card ↥(conjClosure V B ⊓ pCoreOf 2 A) ≤ 8 := by
  have hlt : conjClosure V B ⊓ pCoreOf 2 A < conjClosure V B := by
    refine lt_of_le_of_ne inf_le_left fun e => a₁_not_mem_QA g ?_
    have : a₁ ∈ conjClosure V B ⊓ pCoreOf 2 A := by rw [e]; exact g.a₁_mem_U
    exact this.2
  have hp : IsPGroup 2 ↥(conjClosure V B ⊓ pCoreOf 2 A) :=
    g.hyp.isPGroup_T.to_le (inf_le_left.trans g.hyp.U_le_T)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have h1 := card_lt_of_lt' hlt
  rw [hn, g.card_U] at h1
  have hn3 : n ≤ 3 := by
    by_contra hc
    push Not at hc
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hc
    omega
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
    _ = 8 := by norm_num

theorem exists_R_not_mem_U (hT : Nat.card ↥(A ⊓ B) = 64) :
    ∃ r ∈ pCoreOf 2 A ⊓ pCoreOf 2 B, r ∉ conjClosure V B := by
  by_contra hno
  push Not at hno
  have hle : pCoreOf 2 A ⊓ pCoreOf 2 B ≤ conjClosure V B := fun r hr => hno r hr
  have hRU : pCoreOf 2 A ⊓ pCoreOf 2 B = conjClosure V B :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [g.card_U, card_R_of_card_T g hT])
  refine a₁_not_mem_QA g ?_
  have : a₁ ∈ pCoreOf 2 A ⊓ pCoreOf 2 B := by rw [hRU]; exact g.a₁_mem_U
  exact this.1

theorem exists_noncomm_QA (hT : Nat.card ↥(A ⊓ B) = 64) :
    ∃ p ∈ pCoreOf 2 A, ∃ q ∈ pCoreOf 2 A, p * q ≠ q * p := by
  obtain ⟨r, hr, hrU⟩ := exists_R_not_mem_U g hT
  refine ⟨a * a₁ * a₂, g.hyp.K_le_QA (c_mem_kerK g), r, hr.1, fun hcomm => ?_⟩
  have h1 := comm_c_of_not_mem g hT hr.2 hrU
  have h2 : (a * a₁ * a₂) * r * (a * a₁ * a₂)⁻¹ * r⁻¹ = 1 := by rw [hcomm]; group
  rw [h2] at h1
  exact g.hyp.natural.z_ne h1.symm

theorem K_comm_conj {u : D} (hu : u ∈ A) {k k' : D} (hk : k ∈ kerK B V) (hk' : k' ∈ kerK B V) :
    k * (u * k' * u⁻¹) = (u * k' * u⁻¹) * k := by
  by_cases huT : u ∈ A ⊓ B
  · have hmem : u * k' * u⁻¹ ∈ kerK B V :=
      (Subgroup.mem_normalizer_iff.mp (g.hyp.B_le_normalizer_K huT.2) k').mp hk'
    rw [kerK_eq_zpowers_c g] at hk hmem
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hj]
    exact (Commute.zpow_zpow_self (a * a₁ * a₂) i j).eq
  · have hmem : u * k' * u⁻¹ ∈ conjSub u (kerK B V) := by
      rw [mem_conjSub]
      have e : u⁻¹ * (u * k' * u⁻¹) * u = k' := by group
      rw [e]; exact hk'
    exact g.hyp.kerK_comm_conjSub hu huT k hk _ hmem

theorem yGrp_comm {u v : D} (hu : u ∈ yGrp A B V) (hv : v ∈ yGrp A B V) : u * v = v * u := by
  refine closure_comm (s := {x | ∃ h ∈ A, ∃ z ∈ kerK B V, h * z * h⁻¹ = x}) ?_ hu hv
  rintro _ ⟨a₁', ha₁, k₁, hk₁, rfl⟩ _ ⟨a₂', ha₂, k₂, hk₂, rfl⟩
  have key := K_comm_conj g (A.mul_mem (A.inv_mem ha₁) ha₂) hk₁ hk₂
  calc a₁' * k₁ * a₁'⁻¹ * (a₂' * k₂ * a₂'⁻¹)
      = a₁' * (k₁ * ((a₁'⁻¹ * a₂') * k₂ * (a₁'⁻¹ * a₂')⁻¹)) * a₁'⁻¹ := by group
    _ = a₁' * (((a₁'⁻¹ * a₂') * k₂ * (a₁'⁻¹ * a₂')⁻¹) * k₁) * a₁'⁻¹ := by rw [key]
    _ = a₂' * k₂ * a₂'⁻¹ * (a₁' * k₁ * a₁'⁻¹) := by group

theorem yGrp_le_QA : yGrp A B V ≤ pCoreOf 2 A :=
  conjClosure_le fun _ ha' k hk =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 A ha') k).mp (g.hyp.K_le_QA hk)

omit [Finite D] g in
theorem A_le_normalizer_yGrp : A ≤ Subgroup.normalizer (yGrp A B V : Set D) :=
  le_normalizer_conjClosure _ _

omit [Finite D] g in
theorem K_le_yGrp : kerK B V ≤ yGrp A B V := le_conjClosure _ _

theorem c_mem_yGrp : a * a₁ * a₂ ∈ yGrp A B V := K_le_yGrp (c_mem_kerK g)

theorem yGrp_ne_QA (hT : Nat.card ↥(A ⊓ B) = 64) : yGrp A B V ≠ pCoreOf 2 A := fun e => by
  obtain ⟨p, hp, q, hq, hne⟩ := exists_noncomm_QA g hT
  rw [← e] at hp hq
  exact hne (yGrp_comm g hp hq)

end QA

end GoldAmL2T

end F6

end CFSG.Quasithin
