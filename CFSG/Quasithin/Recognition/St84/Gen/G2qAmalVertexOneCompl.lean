module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalBorel

import CFSG.Quasithin.Recognition.St84.Gen.CoprimeComplement
import CFSG.Quasithin.Recognition.St84.Gen.VertexComplement
import CFSG.Quasithin.EmptyFaithful.S1422Basic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem G2qLocalData.vertexOne_complement (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hfix : ∀ x ∈ pCoreOf 2 L1,
      (∀ h ∈ H ⊓ trivOTwoQuot L1, h * x * h⁻¹ = x) → x = 1) :
    pCoreOf 2 L1 ⊔
        (L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) = L1 ∧
      pCoreOf 2 L1 ⊓
        (L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) = ⊥ ∧
      H ⊓ L1 ≤ L1 ⊓
        Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G) ∧
      pCoreOf 2 L1 ⊔
        ((L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊔
          (H ⊓ trivOTwoQuot L1)) = L1 ⊔ bigB L1 L2 S := by
  classical
  set Q : Subgroup G := pCoreOf 2 L1 with hQ
  set H₀ : Subgroup G := H ⊓ trivOTwoQuot L1 with hH0
  set K : Subgroup G := L1 ⊓ Subgroup.centralizer (H₀ : Set G) with hK
  obtain ⟨-, hcardH0, -, hH0infL, hBLeq⟩ :=
    hD.torus_left_of_hall hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm
  have hcardH0' : Nat.card ↥H₀ = 2 ^ f - 1 := hcardH0
  have hcardQ : Nat.card ↥Q = 2 ^ (5 * f) := hD.card_left
  have hcop : Nat.Coprime (Nat.card ↥H₀) (Nat.card ↥Q) := by
    rw [hcardH0', hcardQ]
    have hfpos : 0 < f := Nat.lt_of_lt_of_le Nat.zero_lt_two hf
    have h2even : Even (2 ^ f) := Even.pow_of_ne_zero even_two (Nat.ne_of_gt hfpos)
    have hodd : Odd (2 ^ f - 1) := Nat.Even.sub_odd Nat.one_le_two_pow h2even odd_one
    exact Nat.Coprime.pow_right (5 * f) (Nat.coprime_two_left.mpr hodd).symm
  have hH0N : H₀ ≤ Subgroup.normalizer (Q : Set G) := by
    intro h hh
    rw [hH0] at hh
    exact (normalizer_le_normalizer_pCoreOf 2 L1)
      (mem_trivOTwoQuot.mp (Subgroup.mem_inf.mp hh).2).1
  have hcomm : ∀ h ∈ H₀, ∀ l ∈ L1, h * l * h⁻¹ * l⁻¹ ∈ Q := by
    intro h hh l hl
    rw [hH0] at hh
    exact (mem_trivOTwoQuot.mp (Subgroup.mem_inf.mp hh).2).2 l hl
  have hsupQK : Q ⊔ K = L1 :=
    sup_inf_centralizer_eq_of_coprime (Q := Q) (L := L1) (H := H₀)
      (pCoreOf_le 2 L1) (le_normalizer_pCoreOf 2 L1) hH0N hcop hcomm
  have hinfQK : Q ⊓ K = ⊥ := by
    have h := inf_centralizer_inf_eq_bot_of_fixed (L := L1) (Q := Q) (H := H₀) hfix
    rwa [inf_comm] at h
  have hHL : H ⊓ L1 ≤ K := by
    intro x hx
    obtain ⟨hxH, hxL⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxL, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hHcomm x hxH h (Subgroup.mem_inf.mp hh).1).symm
  have hsupB : Q ⊔ (K ⊔ H₀) = L1 ⊔ bigB L1 L2 S := by
    have h := sup_inf_centralizer_sup_eq_of_coprime (Q := Q) (L := L1) (H := H₀)
      (pCoreOf_le 2 L1) (le_normalizer_pCoreOf 2 L1) hH0N hcop hcomm
    have hBLeq' : L1 ⊔ bigB L1 L2 S = L1 ⊔ H₀ := hBLeq
    rwa [← hBLeq'] at h
  exact ⟨hsupQK, hinfQK, hHL, hsupB⟩

theorem G2qLocalData.vertexOne_complement_semidirect (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hfix : ∀ x ∈ pCoreOf 2 L1,
      (∀ h ∈ H ⊓ trivOTwoQuot L1, h * x * h⁻¹ = x) → x = 1) :
    Disjoint (pCoreOf 2 L1)
        ((L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊔
          (H ⊓ trivOTwoQuot L1)) ∧
      ((L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊔
          (H ⊓ trivOTwoQuot L1)) ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) ∧
      ∀ r ∈ ((L1 ⊓ Subgroup.centralizer
          ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊔ (H ⊓ trivOTwoQuot L1)),
        (∀ x ∈ pCoreOf 2 L1, r * x = x * r) → r = 1 := by
  classical
  set Q : Subgroup G := pCoreOf 2 L1 with hQ
  set H₀ : Subgroup G := H ⊓ trivOTwoQuot L1 with hH0
  set K : Subgroup G := L1 ⊓ Subgroup.centralizer (H₀ : Set G) with hK
  obtain ⟨-, -, -, hH0infL, -⟩ :=
    hD.torus_left_of_hall hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm
  have hH0infL' : H₀ ⊓ L1 = ⊥ := hH0infL
  have hH0N : H₀ ≤ Subgroup.normalizer (Q : Set G) := by
    intro h hh
    rw [hH0] at hh
    exact (normalizer_le_normalizer_pCoreOf 2 L1)
      (mem_trivOTwoQuot.mp (Subgroup.mem_inf.mp hh).2).1
  have hdisj : Disjoint Q (K ⊔ H₀) := by
    rw [disjoint_iff]
    exact inf_inf_centralizer_sup_eq_bot (Q := Q) (L := L1) (H := H₀)
      (pCoreOf_le 2 L1) hfix hH0infL'
  have hnorm : K ⊔ H₀ ≤ Subgroup.normalizer (Q : Set G) :=
    inf_centralizer_sup_le_normalizer (Q := Q) (L := L1) (H := H₀)
      (le_normalizer_pCoreOf 2 L1) hH0N
  have hS1 : S ≤ L1 := hD.le_left hH (Nat.le_of_lt (Nat.succ_le_iff.mp hf)) h1
  have hS2 : S ≤ L2 := hD.le_right hH (Nat.le_of_lt (Nat.succ_le_iff.mp hf)) h2
  have hcent : (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer (Q : Set G) ≤ Q :=
    sup_bigB_inf_centralizer_le_left_of_le (L1 := L1) (L2 := L2) (S := S) hH hS1 hS2
  refine ⟨hdisj, hnorm, ?_⟩
  intro r hr hrc
  have hrB : r ∈ L1 ⊔ bigB L1 L2 S := by
    have hle : K ⊔ H₀ ≤ L1 ⊔ bigB L1 L2 S :=
      sup_le (show K ≤ L1 ⊔ bigB L1 L2 S from inf_le_left.trans le_sup_left)
        (show H₀ ≤ L1 ⊔ bigB L1 L2 S from (inf_le_left.trans hHB).trans le_sup_right)
    exact hle hr
  have hrC : r ∈ Subgroup.centralizer (Q : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun x hx => (hrc x hx).symm)
  have hrQ : r ∈ Q := hcent ⟨hrB, hrC⟩
  have hEq : Q ⊓ (K ⊔ H₀) = ⊥ := disjoint_iff.mp hdisj
  have hmem : r ∈ Q ⊓ (K ⊔ H₀) := ⟨hrQ, hr⟩
  rwa [hEq, Subgroup.mem_bot] at hmem

theorem G2qLocalData.card_vertexOne_complement (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hfix : ∀ x ∈ pCoreOf 2 L1,
      (∀ h ∈ H ⊓ trivOTwoQuot L1, h * x * h⁻¹ = x) → x = 1) :
    Nat.card ↥((L1 ⊓ Subgroup.centralizer
        ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G)) ⊔ (H ⊓ trivOTwoQuot L1)) =
      2 ^ f * (2 ^ (2 * f) - 1) * (2 ^ f - 1) := by
  classical
  set Q : Subgroup G := pCoreOf 2 L1 with hQ
  set H₀ : Subgroup G := H ⊓ trivOTwoQuot L1 with hH0
  set K : Subgroup G := L1 ⊓ Subgroup.centralizer (H₀ : Set G) with hK
  obtain ⟨-, hcardH0, -, hH0infL, -⟩ :=
    hD.torus_left_of_hall hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm
  have hcardH0' : Nat.card ↥H₀ = 2 ^ f - 1 := hcardH0
  have hH0infL' : H₀ ⊓ L1 = ⊥ := hH0infL
  have hcompl := G2qLocalData.vertexOne_complement hf hH hD h1 h2 hHB hSH hSinfH
    hHcard hHcomm hfix
  have hsupQK : Q ⊔ K = L1 := hcompl.1
  have hinfQK : Q ⊓ K = ⊥ := hcompl.2.1
  have hQN : K ≤ Subgroup.normalizer (Q : Set G) :=
    inf_le_left.trans (le_normalizer_pCoreOf 2 L1)
  have hdisj : Disjoint Q K := by
    rw [disjoint_iff]
    exact hinfQK
  have hcardQK : Nat.card ↥L1 = Nat.card ↥Q * Nat.card ↥K := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (A := Q) (B := K) hQN hdisj
    rwa [hsupQK] at h
  have hcardL : Nat.card ↥L1 = Nat.card (oTwoQuot ↥L1) * Nat.card ↥Q := by
    have hpc : Nat.card ↥Q = Nat.card (CFSG.pCore 2 ↥L1) := by
      rw [hQ, CFSG.Open.pCoreOf, Subgroup.card_map_of_injective L1.subtype_injective]
    rw [hpc]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L1)
  have hquot : Nat.card (oTwoQuot ↥L1) = 2 ^ f * (4 ^ f - 1) :=
    CFSG.Quasithin.IsL2Quot.card (Nat.le_of_lt (Nat.succ_le_iff.mp hf)) h1
  have hKcard : Nat.card ↥K = 2 ^ f * (4 ^ f - 1) := by
    have hEq : Nat.card ↥Q * Nat.card ↥K =
        Nat.card ↥Q * (2 ^ f * (4 ^ f - 1)) := by
      calc Nat.card ↥Q * Nat.card ↥K = Nat.card ↥L1 := hcardQK.symm
        _ = Nat.card (oTwoQuot ↥L1) * Nat.card ↥Q := hcardL
        _ = (2 ^ f * (4 ^ f - 1)) * Nat.card ↥Q := by rw [hquot]
        _ = Nat.card ↥Q * (2 ^ f * (4 ^ f - 1)) := mul_comm _ _
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥Q)) hEq
  have hcardKH : Nat.card ↥(K ⊔ H₀) = Nat.card ↥K * Nat.card ↥H₀ :=
    card_inf_centralizer_sup (L := L1) (H := H₀) hH0infL'
  rw [hcardKH, hKcard, hcardH0']
  have h4 : (4 : ℕ) ^ f = 2 ^ (2 * f) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl]
    exact (pow_mul 2 2 f).symm
  rw [h4]

end CFSG.Quasithin.F112R.St84

end