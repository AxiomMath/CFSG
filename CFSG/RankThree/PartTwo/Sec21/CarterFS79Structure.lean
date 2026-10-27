module

public import CFSG.RankThree.PartTwo.Sec21.CarterFS79Setup
public import CFSG.GroupTheory.SupCommute
public import CFSG.ClassicalInvolution.Sp62Rec.I1.PermQuot

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem FS79Hyp.card_J (h : FS79Hyp b t b₁ b₂ J) : Nat.card ↥J = 720 := by
  obtain ⟨e⟩ := h.J_perm
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  norm_num

theorem FS79Hyp.b_not_mem_J (h : FS79Hyp b t b₁ b₂ J) : b ∉ J := by
  intro hbJ
  have hbZ : (⟨b, hbJ⟩ : ↥J) ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro j
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b j.2)
  obtain ⟨e⟩ := h.J_perm
  have hbZ' : e ⟨b, hbJ⟩ ∈ Subgroup.center (Equiv.Perm (Fin 6)) := by
    rw [← Subgroup.map_center_eq e]
    exact ⟨⟨b, hbJ⟩, hbZ, rfl⟩
  rw [CFSG.ClassicalInvolution.Sp62Rec.I1.center_perm_fin_six_eq_bot,
    Subgroup.mem_bot] at hbZ'
  have hb1J : (⟨b, hbJ⟩ : ↥J) = 1 := by
    apply e.injective
    rw [map_one]
    exact hbZ'
  have hb1 : b = 1 := congrArg Subtype.val hb1J
  have hord := h.ord_b
  rw [hb1, orderOf_one] at hord
  norm_num at hord

theorem FS79Hyp.isElemAb_B (h : FS79Hyp b t b₁ b₂ J) :
    IsElemAb 3 3 (Subgroup.closure ({b, b₁, b₂} : Set H)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set A : Subgroup H := Subgroup.closure ({b₁, b₂} : Set H) with hA
  set C : Subgroup H := Subgroup.zpowers b with hC
  have hb3 : b ^ 3 = 1 := by
    rw [← h.ord_b]
    exact pow_orderOf_eq_one b
  have hAab : IsElementaryAbelian 3 ↥A := by
    rw [hA]
    exact h.E9.1
  have hCab : IsElementaryAbelian 3 ↥C := by
    rw [hC]
    exact IsElementaryAbelian.zpowers_of_pow_eq_one hb3
  haveI := hAab
  haveI := hCab
  have hAleJ : A ≤ J := by
    rw [hA, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact h.b₁_mem
    · exact h.b₂_mem
  have hAcomm : A ≤ Subgroup.centralizer ({b} : Set H) := by
    rw [hA, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact h.J_le_cen_b h.b₁_mem
    · exact h.J_le_cen_b h.b₂_mem
  have hcardC : Nat.card C = 3 := by
    rw [hC, Nat.card_zpowers, h.ord_b]
  have hCJ : C ⊓ J = ⊥ := by
    have hdvd : Nat.card ↥(C ⊓ J) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : C ⊓ J ≤ C)
      rwa [hcardC] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hle : C ≤ J := by
        have hCeq : C ⊓ J = C :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcardC])
        rw [← hCeq]
        exact inf_le_right
      have hbC : b ∈ C := by
        rw [hC]
        exact Subgroup.mem_zpowers b
      exact h.b_not_mem_J (hle hbC)
  have hcomm : ∀ a ∈ A, ∀ c ∈ C, Commute a c := by
    intro a ha c hc
    have hab : Commute a b := Subgroup.mem_centralizer_singleton_iff.mp (hAcomm ha)
    rw [hC] at hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact hab.zpow_right k
  have hdisj : A ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxJ : x ∈ J := hAleJ hx.1
    have hxboth : x ∈ C ⊓ J := ⟨hx.2, hxJ⟩
    rw [hCJ] at hxboth
    exact hxboth
  have hcardA : Nat.card A = 9 := by
    rw [hA]
    simpa using h.E9.2
  have hcardSup : Nat.card ↥(A ⊔ C) = 27 := by
    rw [CFSG.card_sup_eq_mul_of_commute A C hcomm hdisj, hcardA, hcardC]
  have hsup : A ⊔ C = Subgroup.closure ({b, b₁, b₂} : Set H) := by
    rw [hA, hC, Subgroup.zpowers_eq_closure b, ← Subgroup.closure_union]
    congr 1
    ext x
    simp [or_comm, or_left_comm, or_assoc]
  have hCA : C ≤ Subgroup.centralizer (A : Set H) := by
    rw [← Subgroup.le_centralizer_iff (H := A) (K := C)]
    rw [hC, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hAcomm
  refine ⟨?_, ?_⟩
  · rw [← hsup]
    exact IsElementaryAbelian.sup_of_le_centralizer (p := 3) (E := A) (C := C) hCA
  · rw [← hsup, hcardSup]
    norm_num

end CFSG.RankThree.PartTwo.Sec21.FF81
