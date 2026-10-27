module

public import CFSG.Quasithin.EmptyFaithful.S1422Quot
public import CFSG.Quasithin.EmptyFaithful.S1422Center

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

section Cases

variable {G : Type} [Group G]

@[expose] def CaseTits (H L2 : Subgroup G) : Prop :=
  IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H L2) (fun Y _ => Nonempty (Y ≃* quasithinTits)) ∧
    (Nonempty (oTwoQuot ↥H ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥H ≃* ↥(Sz 0))) ∧
    Nat.card (pCoreOf 2 H) = 2 ^ 9 ∧
    IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 10

@[expose] def Case2F4 (H L2 : Subgroup G) : Prop :=
  IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H L2) (IsTwistedF4Over 1) ∧
    Nonempty (oTwoQuot ↥H ≃* Sz 0) ∧ Nat.card (pCoreOf 2 H) = 2 ^ 10 ∧
    IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 11

@[expose] def CaseG2 (H L2 : Subgroup G) : Prop :=
  IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H L2) (IsG2Over 1) ∧
    IsL2Quot 1 (oTwoQuot ↥H) ∧ IsL2Quot 1 (oTwoQuot ↥L2) ∧ IsSpecialPow 2 2 2 ↥(pCoreOf 2 H) ∧
    Nat.card (pCoreOf 2 L2) = 2 ^ 5

@[expose] def CaseG22P (H L2 : Subgroup G) : Prop :=
  IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H L2) (fun Y _ => Nonempty (Y ≃* PSU3 3 1)) ∧
    IsL2Quot 1 (oTwoQuot ↥H) ∧ IsL2Quot 1 (oTwoQuot ↥L2) ∧ IsZ4StarQ8 ↥(pCoreOf 2 H) ∧
    IsZ4Sq ↥(pCoreOf 2 L2)

@[expose] def CaseM12 (H L2 : Subgroup G) : Prop :=
  IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H L2) (fun Y _ => Nonempty (Y ≃* quasithinM12)) ∧
    IsL2Quot 1 (oTwoQuot ↥H) ∧ IsQ8Sq ↥(pCoreOf 2 H) ∧ IsL2Quot 1 (oTwoQuot ↥L2) ∧
    Nat.card (pCoreOf 2 L2) = 2 ^ 5

@[expose] def CaseAutM12 (H L2 : Subgroup G) : Prop :=
  IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H L2)
      (fun Y _ => Nonempty (Y ≃* MulAut quasithinM12)) ∧
    IsL2Quot 1 (oTwoQuot ↥H) ∧ IsAutM12Vertex H ∧ IsL2Quot 1 (oTwoQuot ↥L2) ∧
    Nat.card (pCoreOf 2 L2) = 2 ^ 6

end Cases

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}

theorem card_oTwoQuot_YT (S : Setting1422 T M Y H) : Nat.card (oTwoQuot ↥(Y ⊔ T)) = 6 := by
  have := S.card_quot_YT
  norm_num at this
  exact this

theorem H_not_iso_perm_four (S : Setting1422 T M Y H) : IsEmpty (↥H ≃* Equiv.Perm (Fin 4)) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨x, hx, hx1, hxc⟩ := S.exists_central_H
  have h1 : e ⟨x, hx⟩ = 1 := by
    have hc : ∀ σ : Equiv.Perm (Fin 4), (∀ τ, σ * τ = τ * σ) → σ = 1 := by decide
    apply hc
    intro τ
    have := hxc (e.symm τ : G) (e.symm τ).2
    have h2 : (⟨x, hx⟩ : ↥H) * e.symm τ = e.symm τ * ⟨x, hx⟩ := Subtype.ext this
    have h3 := congrArg e h2
    simpa using h3
  have : (⟨x, hx⟩ : ↥H) = 1 := e.injective (by rw [h1, map_one])
  exact hx1 (congrArg Subtype.val this)

theorem YT_not_iso_z2_perm_four (S : Setting1422 T M Y H) :
    IsEmpty (↥(Y ⊔ T) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) := by
  refine ⟨fun e => ?_⟩
  refine no_iso_of_trivial_center S.center_YT e (Multiplicative.ofAdd 1, 1) ?_ ?_
  · intro h
    have := congrArg Prod.fst h
    simp at this
  · intro y
    refine Prod.ext ?_ (by simp)
    exact mul_comm _ _

variable (hSz : Nat.card ↥(Sz 0) = 20)
include hSz

theorem unswapped_cases (S : Setting1422 T M Y H) (hL : F112ListBare H (Y ⊔ T) T) :
    CaseTits H (Y ⊔ T) ∨ Case2F4 H (Y ⊔ T) ∨ CaseG2 H (Y ⊔ T) ∨ CaseG22P H (Y ⊔ T) ∨
      CaseM12 H (Y ⊔ T) ∨ CaseAutM12 H (Y ⊔ T) := by
  have hB : bigB H (Y ⊔ T) T = T := S.bigB_eq hSz
  have hHT : H ⊔ T = H := sup_of_le_left S.T_le_H
  have hYT : (Y ⊔ T) ⊔ T = Y ⊔ T := sup_of_le_left T_le_YT
  have h6 : Nat.card (oTwoQuot ↥(Y ⊔ T)) = 6 := S.card_oTwoQuot_YT
  have hHle : Nat.card (oTwoQuot ↥H) ≤ 20 := S.card_quot_H_le hSz
  unfold F112ListBare at hL
  simp only [hB, hHT, hYT] at hL
  rcases hL with h1 | h2 | h3 | h4 | h5 | h6' | h7 | h8 | h9 | h10 | h11 | h12 | h13
  ·
    exfalso
    obtain ⟨f, hf, -, h⟩ := h1
    rcases h with ⟨hf2, -, -, -, hY⟩ | ⟨-, ⟨eH⟩, -⟩
    · have hc := isLin2Type_card_quot hY
      have := two_pow_mul_four_pow_sub_one_ge f hf2
      have h6'' : Nat.card (OTwoQuot (Y ⊔ T)) = 6 := h6
      omega
    · exact S.H_not_iso_perm_four.false eH
  ·
    exfalso
    obtain ⟨f, hf, -, h⟩ := h2
    rcases h with ⟨hf2, -, -, -, hY⟩ | ⟨-, -, ⟨eY⟩⟩
    · have hc := isLin2Type_card_quot hY
      have := two_pow_mul_four_pow_sub_one_ge f hf2
      have h6'' : Nat.card (OTwoQuot (Y ⊔ T)) = 6 := h6
      omega
    · rw [hYT] at eY
      exact S.YT_not_iso_z2_perm_four.false eY
  ·
    obtain ⟨f, hf, hA, hqH, hqY, hsp, hcard⟩ := h3
    have hf1 : f = 1 := hqY.eq_one_of_card_eq_six hf h6
    subst hf1
    rw [hHT] at hsp
    right; right; left
    exact ⟨hA, hqH, hqY, by simpa using hsp, by simpa using hcard⟩
  ·
    exfalso
    obtain ⟨f, hf, -, hqH, -, hqY, -⟩ := h4
    have hf1 : f = 1 := hqY.eq_one_of_card_eq_six hf h6
    subst hf1
    exact isL2Quot_card_le_false (by norm_num) hqH hHle
  ·
    obtain ⟨a, hA, hSz', hcardH, hqY, hcardY⟩ := h5
    have ha : 2 * a + 1 = 1 := hqY.eq_one_of_card_eq_six (by omega) h6
    have ha0 : a = 0 := by omega
    subst ha0
    right; left
    exact ⟨hA, hSz', by simpa using hcardH, hqY, by simpa using hcardY⟩
  ·
    exfalso
    obtain ⟨f, hf, -, -, -, -, hqY, -⟩ := h6'
    have := hqY.eq_one_of_card_eq_six (by omega) h6
    omega
  ·
    exfalso
    obtain ⟨-, -, -, hqY, -⟩ := h7
    have := hqY.eq_one_of_card_eq_six (by omega) h6
    omega
  ·
    obtain ⟨hA, hqH, hqY, hZ, hZ2⟩ := h8
    rw [hHT] at hZ
    rw [hYT] at hZ2
    right; right; right; left
    exact ⟨hA, hqH, hqY, hZ, hZ2⟩
  ·
    left
    exact h9
  ·
    exfalso
    obtain ⟨-, hqH, -, -, -⟩ := h10
    exact isL2Quot_card_le_false (by norm_num) hqH hHle
  ·
    exfalso
    obtain ⟨-, ⟨e⟩, -, -, -⟩ := h11
    have hc := Nat.card_congr e.toEquiv
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 5)), Fintype.card_perm] at hc
    have h120 : Nat.card (oTwoQuot ↥(H ⊔ T)) = 120 := by simpa [Nat.factorial] using hc
    rw [hHT] at h120
    omega
  ·
    right; right; right; right; left
    obtain ⟨hA, hqH, hQ, hqY, hcard⟩ := h12
    exact ⟨hA, hqH, hQ, hqY, hcard⟩
  ·
    right; right; right; right; right
    obtain ⟨hA, hqH, hQ, hqY, hcard⟩ := h13
    exact ⟨hA, hqH, hQ, hqY, hcard⟩


omit hSz in
theorem false_of_uci (S : Setting1422 T M Y H)
    (h : UniqueCentralInvolution ↥(pCoreOf 2 (Y ⊔ T))) : False := by
  obtain ⟨w, hwR, hw1, hwc⟩ := exists_central_of_uci
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y ⊔ T)) h
  have hwK : w ∈ Y ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hwR
  exact hw1 (S.center_YT w hwK (fun y hy => (hwc y hy).symm))

theorem not_swapped (S : Setting1422 T M Y H) : ¬ F112ListBare (Y ⊔ T) H T := by
  intro hL
  have hB : bigB (Y ⊔ T) H T = T := by rw [bigB_comm]; exact S.bigB_eq hSz
  have hHT : H ⊔ T = H := sup_of_le_left S.T_le_H
  have hYT : (Y ⊔ T) ⊔ T = Y ⊔ T := sup_of_le_left T_le_YT
  have h6 : Nat.card (oTwoQuot ↥(Y ⊔ T)) = 6 := S.card_oTwoQuot_YT
  have hHle : Nat.card (oTwoQuot ↥H) ≤ 20 := S.card_quot_H_le hSz
  unfold F112ListBare at hL
  simp only [hB, hHT, hYT] at hL
  rcases hL with h1 | h2 | h3 | h4 | h5 | h6' | h7 | h8 | h9 | h10 | h11 | h12 | h13
  ·
    obtain ⟨f, hf, -, h⟩ := h1
    rcases h with ⟨hf2, -, hY, -, -⟩ | ⟨-, -, ⟨eH⟩⟩
    · have hc := isLin2Type_card_quot hY
      have := two_pow_mul_four_pow_sub_one_ge f hf2
      have h6'' : Nat.card (OTwoQuot (Y ⊔ T)) = 6 := h6
      omega
    · exact S.H_not_iso_perm_four.false eH
  ·
    obtain ⟨f, hf, -, h⟩ := h2
    rcases h with ⟨hf2, -, hY, -, -⟩ | ⟨-, ⟨eY⟩, -⟩
    · have hc := isLin2Type_card_quot hY
      have := two_pow_mul_four_pow_sub_one_ge f hf2
      have h6'' : Nat.card (OTwoQuot (Y ⊔ T)) = 6 := h6
      omega
    · rw [hYT] at eY
      exact S.YT_not_iso_z2_perm_four.false eY
  ·
    obtain ⟨f, hf, -, hqY, -, hsp, -⟩ := h3
    have hf1 : f = 1 := hqY.eq_one_of_card_eq_six hf h6
    subst hf1
    rw [hYT] at hsp
    exact S.false_of_uci (uci_of_isSpecialPow (by simpa using hsp))
  ·
    obtain ⟨f, hf, -, hqY, -⟩ := h4
    have := hqY.eq_one_of_card_eq_six (by omega) h6
    omega
  ·
    obtain ⟨a, -, ⟨eY⟩, -, hqH, -⟩ := h5
    have ha : 2 * a + 1 = 1 := by
      by_contra hne
      exact isL2Quot_card_le_false (by omega) hqH hHle
    have ha0 : a = 0 := by omega
    subst ha0
    have := Nat.card_congr eY.toEquiv
    rw [h6, hSz] at this
    omega
  ·
    obtain ⟨f, hf, -, hqY, -, -, hqH, -⟩ := h6'
    have hf1 : f = 1 := hqY.eq_one_of_card_eq_six hf h6
    subst hf1
    exact isL2Quot_card_le_false (by norm_num) hqH hHle
  ·
    obtain ⟨-, -, -, hqH, -⟩ := h7
    exact isL2Quot_card_le_false (by norm_num) hqH hHle
  ·
    obtain ⟨-, -, -, hZ, -⟩ := h8
    rw [hYT] at hZ
    exact S.false_of_uci (uci_of_isZ4StarQ8 hZ)
  ·
    obtain ⟨-, hq, -, -, -⟩ := h9
    rcases hq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have := Nat.card_congr e.toEquiv
      rw [h6, Nat.card_eq_fintype_card (α := DihedralGroup 5), DihedralGroup.card] at this
      omega
    · have := Nat.card_congr e.toEquiv
      rw [h6, hSz] at this
      omega
  ·
    obtain ⟨-, hqY, -, -, -⟩ := h10
    have := hqY.eq_one_of_card_eq_six (by omega) h6
    omega
  ·
    obtain ⟨-, ⟨e⟩, -, -, -⟩ := h11
    have hc := Nat.card_congr e.toEquiv
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 5)), Fintype.card_perm] at hc
    have h120 : Nat.card (oTwoQuot ↥(Y ⊔ T ⊔ T)) = 120 := by simpa [Nat.factorial] using hc
    rw [hYT, h6] at h120
    omega
  ·
    obtain ⟨-, -, hQ, -, -⟩ := h12
    exact S.false_of_uci (centerOrderTwo_of_isQ8Sq hQ).uci
  ·
    obtain ⟨-, -, hQ, -, -⟩ := h13
    exact S.false_of_uci (uci_of_isAutM12Vertex hQ)

theorem six_cases (hF : F112LegacyPrintedError) (S : Setting1422 T M Y H) :
    CaseTits H (Y ⊔ T) ∨ Case2F4 H (Y ⊔ T) ∨ CaseG2 H (Y ⊔ T) ∨ CaseG22P H (Y ⊔ T) ∨
      CaseM12 H (Y ⊔ T) ∨ CaseAutM12 H (Y ⊔ T) := by
  rcases S.f112_list hSz hF with h | h
  · exact S.unswapped_cases hSz h
  · exact absurd h (S.not_swapped hSz)


end Setting1422

end CFSG.Quasithin
