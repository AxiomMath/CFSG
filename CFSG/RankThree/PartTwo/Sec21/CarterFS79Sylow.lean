module

public import CFSG.RankThree.PartTwo.Sec21.CarterFS79Structure
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma14Base
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem FS79Hyp.card_bt (h : FS79Hyp b t b₁ b₂ J) :
    Nat.card ↥(Subgroup.closure ({b, t} : Set H)) = 6 := by
  classical
  set A : Subgroup H := Subgroup.zpowers b with hA
  set T : Subgroup H := Subgroup.zpowers t with hT
  have hAcard : Nat.card A = 3 := by
    rw [hA, Nat.card_zpowers, h.ord_b]
  have hTcard : Nat.card T = 2 := by
    rw [hT, Nat.card_zpowers, h.ord_t]
  have htNor : t ∈ Subgroup.normalizer (A : Set H) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmap : A.map (MulAut.conj t) = A := by
      rw [hA, MonoidHom.map_zpowers]
      have hconj : (↑(MulAut.conj t) : H →* H) b = b⁻¹ := by
        simpa [MulAut.conj_apply] using h.inv_b
      rw [hconj, Subgroup.zpowers_inv]
    exact hmap
  have hTle : T ≤ Subgroup.normalizer (A : Set H) := by
    rw [hT]
    exact Subgroup.zpowers_le.mpr htNor
  have hinf : T ⊓ A = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have hdvd3 : Nat.card ↥(T ⊓ A) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : T ⊓ A ≤ A)
      rwa [hAcard] at this
    have hdvd2 : Nat.card ↥(T ⊓ A) ∣ 2 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : T ⊓ A ≤ T)
      rwa [hTcard] at this
    have hdvd1 : Nat.card ↥(T ⊓ A) ∣ 1 := by
      have := Nat.dvd_gcd hdvd3 hdvd2
      simpa using this
    exact Nat.dvd_one.mp hdvd1
  have hcard := card_sup_mul_card_inf (H := T) (K := A) hTle
  rw [hinf, Subgroup.card_bot, mul_one, hTcard, hAcard] at hcard
  have h6 : Nat.card ↥(T ⊔ A) = 6 := by simpa using hcard
  have hsup : Subgroup.closure ({b, t} : Set H) = T ⊔ A := by
    rw [hT, hA, Subgroup.zpowers_eq_closure b, Subgroup.zpowers_eq_closure t,
      ← Subgroup.closure_union]
    congr 1
    ext x
    simp [or_comm]
  rw [hsup, h6]

theorem FS79Hyp.bt_inf_J (h : FS79Hyp b t b₁ b₂ J) :
    Subgroup.closure ({b, t} : Set H) ⊓ J = ⊥ := by
  classical
  set A : Subgroup H := Subgroup.zpowers b with hA
  set K : Subgroup H := Subgroup.closure ({b, t} : Set H) with hK
  have hAcard : Nat.card A = 3 := by
    rw [hA, Nat.card_zpowers, h.ord_b]
  have hKcard : Nat.card K = 6 := by
    rw [hK]
    exact h.card_bt
  have hbne : b ≠ b⁻¹ := by
    intro hb
    have hb2 : b ^ 2 = 1 := by
      rw [sq]
      exact eq_inv_iff_mul_eq_one.mp hb
    have hdvd : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one hb2
    rw [h.ord_b] at hdvd
    norm_num at hdvd
  have htNotCen : t ∉ Cen b := by
    intro htC
    have hcomm : t * b = b * t := Subgroup.mem_centralizer_singleton_iff.mp htC
    have hinv : t * b * t⁻¹ = b⁻¹ := h.inv_b
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one] at hinv
    exact hbne hinv
  have hAK : A ≤ K := by
    rw [hK, hA, Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_mono (Set.singleton_subset_iff.mpr (by simp))
  have hACen : A ≤ Cen b := by
    rw [hA, Cen, Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl b)
  have hA_le : A ≤ K ⊓ Cen b := le_inf hAK hACen
  have hCenK : K ⊓ Cen b = A := by
    apply le_antisymm
    · have hdvd : Nat.card ↥(K ⊓ Cen b) ∣ 6 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : K ⊓ Cen b ≤ K)
        rwa [hKcard] at this
      have h3dvd : 3 ∣ Nat.card ↥(K ⊓ Cen b) := by
        have := Subgroup.card_dvd_of_le hA_le
        rwa [hAcard] at this
      have hCcard : Nat.card ↥(K ⊓ Cen b) = 3 := by
        obtain ⟨k, hk⟩ := h3dvd
        have hk2 : k ∣ 2 := by
          have hd : 3 * k ∣ 3 * 2 := by
            rw [← hk]
            exact hdvd
          exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd
        rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with hk1 | hk2
        · rw [hk, hk1, mul_one]
        · exfalso
          have h6 : Nat.card ↥(K ⊓ Cen b) = 6 := by rw [hk, hk2]
          have hKeq : K ⊓ Cen b = K :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h6, hKcard])
          have htK : t ∈ K := by
            rw [hK]
            exact Subgroup.subset_closure (by simp)
          have htC : t ∈ Cen b := by
            have : t ∈ K ⊓ Cen b := by rw [hKeq]; exact htK
            exact this.2
          exact htNotCen htC
      have hcardle : Nat.card ↥(K ⊓ Cen b) ≤ Nat.card A := by
        rw [hCcard, hAcard]
      have heq : A = K ⊓ Cen b := Subgroup.eq_of_le_of_card_ge hA_le hcardle
      exact le_of_eq heq.symm
    · exact hA_le
  have hAJ : A ⊓ J = ⊥ := by
    have hdvd : Nat.card ↥(A ⊓ J) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : A ⊓ J ≤ A)
      rwa [hAcard] at this
    have hne3 : Nat.card ↥(A ⊓ J) ≠ 3 := by
      intro h3
      have heq : A ⊓ J = A :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hAcard])
      have hbJ : b ∈ J := by
        have hbA : b ∈ A := by
          rw [hA]
          exact Subgroup.mem_zpowers b
        have : b ∈ A ⊓ J := by rw [heq]; exact hbA
        exact this.2
      exact h.b_not_mem_J hbJ
    apply Subgroup.eq_bot_of_card_eq
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact h1
    · exact absurd h3 hne3
  apply le_antisymm _ bot_le
  intro x hx
  have hxK : x ∈ K := hx.1
  have hxJ : x ∈ J := hx.2
  have hxCen : x ∈ Cen b := h.J_le_cen_b hxJ
  have hxA : x ∈ A := by
    have : x ∈ K ⊓ Cen b := ⟨hxK, hxCen⟩
    rwa [hCenK] at this
  have hxbot : x ∈ A ⊓ J := ⟨hxA, hxJ⟩
  rwa [hAJ] at hxbot

theorem FS79Hyp.isSylow_B_N (h : FS79Hyp b t b₁ b₂ J) :
    IsSylowOf 3 (Subgroup.closure ({b, b₁, b₂} : Set H)) (Nor (Subgroup.zpowers b)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A : Subgroup H := Subgroup.zpowers b with hA
  set N : Subgroup H := Nor A with hN
  set O : Subgroup H := Opp 3 N with hO
  set B : Subgroup H := Subgroup.closure ({b, b₁, b₂} : Set H) with hB
  set C : Subgroup H := Subgroup.closure ({b, t} : Set H) with hC
  set K : Subgroup H := C ⊔ J with hK
  have htNor : t ∈ Subgroup.normalizer (A : Set H) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmap : A.map (MulAut.conj t) = A := by
      rw [hA, MonoidHom.map_zpowers]
      have hconj : (↑(MulAut.conj t) : H →* H) b = b⁻¹ := by
        simpa [MulAut.conj_apply] using h.inv_b
      rw [hconj, Subgroup.zpowers_inv]
    exact hmap
  have hbN : b ∈ N := by
    rw [hN]
    exact Subgroup.le_normalizer (Subgroup.mem_zpowers b)
  have htN : t ∈ N := by
    rw [hN]
    exact htNor
  have hJN : J ≤ N := by
    intro x hx
    rw [hN, hA]
    exact FS79Hyp.cen_le_nor h (h.J_le_cen_b hx)
  have hCN : C ≤ N := by
    rw [hC, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hbN
    · exact htN
  have hKN : K ≤ N := by
    rw [hK]
    exact sup_le hCN hJN
  have hKNorO : K ≤ Subgroup.normalizer (O : Set H) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro o
    constructor
    · intro ho
      exact L14.Opp_conj_mem (hKN hk) ho
    · intro ho
      have h := L14.Opp_conj_mem (N.inv_mem (hKN hk)) ho
      convert h using 1
      group
  have hNeq : setMul O K = N := by
    have h' := h.N_eq
    simp only [← hA, ← hN, ← hO, ← hC, ← hK] at h'
    simpa using h'
  have hset : (O : Set H) * (K : Set H) = (N : Set H) := by
    ext x
    rw [Set.mem_mul, ← hNeq, setMul]
    exact ⟨fun ⟨o, ho, k, hk, h⟩ => ⟨o, ho, k, hk, h.symm⟩,
      fun ⟨o, ho, k, hk, h⟩ => ⟨o, ho, k, hk, h.symm⟩⟩
  have hsupON : O ⊔ K = N := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_mul_of_right_le_normalizer_left O K hKNorO]
    exact hset
  have hcardNK : Nat.card ↥N * Nat.card ↥(O ⊓ K) = Nat.card ↥O * Nat.card ↥K := by
    have hc := card_sup_mul_card_inf (H := K) (K := O) hKNorO
    rw [sup_comm K O, hsupON, inf_comm K O] at hc
    exact hc.trans (mul_comm _ _)
  have hCcard : Nat.card ↥C = 6 := by
    rw [hC]
    exact h.card_bt
  have hCnorJ : C ≤ Nor J := hCN.trans h.N_le_NJ
  have hKcard : Nat.card ↥K = 4320 := by
    rw [hK]
    have hc := card_sup_mul_card_inf (H := C) (K := J) hCnorJ
    have hinf : C ⊓ J = ⊥ := by
      rw [hC]
      exact h.bt_inf_J
    rw [hinf, Subgroup.card_bot, mul_one, hCcard, FS79Hyp.card_J h] at hc
    simpa using hc
  have hOcop : Nat.Coprime 3 (Nat.card ↥O) := by
    rw [hO]
    exact L14.Opp_coprime 3 N
  have hOnot : ¬ 3 ∣ Nat.card ↥O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hOcop
  have hOKcop : Nat.Coprime 3 (Nat.card ↥(O ⊓ K)) :=
    hOcop.coprime_dvd_right (Subgroup.card_dvd_of_le (inf_le_left : O ⊓ K ≤ O))
  have hBcard : Nat.card ↥B = 27 := by
    have hE := h.isElemAb_B
    rw [← hB] at hE
    exact hE.2
  have hBK : B ≤ K := by
    rw [hB, hK, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (h.b₁_mem)
    · exact Subgroup.mem_sup_right (h.b₂_mem)
  have hrelK : B.relIndex K = 160 := by
    have hc := Subgroup.relIndex_mul_card (H := B) (K := K)
    rw [inf_of_le_left hBK, hBcard, hKcard] at hc
    omega
  have hBN : B ≤ N := hBK.trans hKN
  have hNrel : B.relIndex N * Nat.card B = Nat.card N := by
    have hc := Subgroup.relIndex_mul_card (H := B) (K := N)
    rwa [inf_of_le_left hBN] at hc
  have hKrel : B.relIndex K * Nat.card B = Nat.card K := by
    have hc := Subgroup.relIndex_mul_card (H := B) (K := K)
    rwa [inf_of_le_left hBK] at hc
  have hrel_eq : B.relIndex N * Nat.card ↥(O ⊓ K) = Nat.card ↥O * B.relIndex K := by
    have h1 : (B.relIndex N * Nat.card B) * Nat.card ↥(O ⊓ K) =
        Nat.card ↥O * (B.relIndex K * Nat.card B) := by
      rw [hNrel, hKrel]
      exact hcardNK
    refine Nat.mul_right_cancel (Nat.card_pos (α := ↥B)) ?_
    calc
      (B.relIndex N * Nat.card ↥(O ⊓ K)) * Nat.card B
          = (B.relIndex N * Nat.card B) * Nat.card ↥(O ⊓ K) := by ring
      _ = Nat.card ↥O * (B.relIndex K * Nat.card B) := h1
      _ = (Nat.card ↥O * B.relIndex K) * Nat.card B := by ring
  have hrelK3 : ¬ 3 ∣ B.relIndex K := by
    rw [hrelK]
    norm_num
  have hrelNcop : Nat.Coprime 3 (B.relIndex N) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro hdvd
    have hdvd' : 3 ∣ B.relIndex N * Nat.card ↥(O ⊓ K) := dvd_mul_of_dvd_left hdvd _
    rw [hrel_eq] at hdvd'
    rcases (Nat.prime_three.dvd_mul).mp hdvd' with hOdiv | hKdiv
    · exact hOnot hOdiv
    · exact hrelK3 hKdiv
  refine ⟨?_, ?_, ?_⟩
  · simpa [hN, hA, hB] using hBN
  · have hE := h.isElemAb_B
    rw [← hB] at hE
    haveI : IsElementaryAbelian 3 ↥B := hE.1
    simpa [hB] using (IsElementaryAbelian.isPGroup 3 B)
  · simpa [hN, hA, hB] using hrelNcop

end CFSG.RankThree.PartTwo.Sec21.FF81

