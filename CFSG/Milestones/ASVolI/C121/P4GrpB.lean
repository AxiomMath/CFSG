module

public import CFSG.Milestones.ASVolI.C121.P4GrpA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem burnsideC121_p4_relIndex_autI {V : Subgroup Ω} (hV : IsElemAbelian 2 V)
    {A B : Subgroup Ω} (hAB : A ≤ B) (hB : B ≤ Subgroup.normalizer (V : Set Ω)) :
    A.relIndex B = (autI hV A).relIndex (autI hV B) *
      (A ⊓ Subgroup.centralizer (V : Set Ω)).relIndex (B ⊓ Subgroup.centralizer (V : Set Ω)) := by
  have hA := card_autI_mul_card_inf hV (hAB.trans hB)
  have hB' := card_autI_mul_card_inf hV hB
  have h1 := Subgroup.relIndex_mul_card A B
  rw [inf_eq_left.2 hAB] at h1
  have h2 := Subgroup.relIndex_mul_card (autI hV A) (autI hV B)
  rw [inf_eq_left.2 (autI_mono hV hAB)] at h2
  have h3 := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (V : Set Ω))
    (B ⊓ Subgroup.centralizer (V : Set Ω))
  rw [inf_eq_left.2 (inf_le_inf_right _ hAB)] at h3
  have hpos : 0 < Nat.card (autI hV A) * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set Ω)) := by
    rw [hA]; exact Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc A.relIndex B * (Nat.card (autI hV A) * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set Ω)))
      = A.relIndex B * Nat.card A := by rw [hA]
    _ = Nat.card (autI hV B) * Nat.card ↥(B ⊓ Subgroup.centralizer (V : Set Ω)) := by rw [h1, hB']
    _ = ((autI hV A).relIndex (autI hV B) * Nat.card (autI hV A)) *
        ((A ⊓ Subgroup.centralizer (V : Set Ω)).relIndex (B ⊓ Subgroup.centralizer (V : Set Ω)) *
          Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set Ω))) := by rw [h2, h3]
    _ = _ := by ring

theorem burnsideC121_p4_relIndex_sup {P Y : Subgroup Ω}
    (hP : P ≤ Subgroup.normalizer (Y : Set Ω)) :
    P.relIndex (P ⊔ Y) = (P ⊓ Y).relIndex Y := by
  have h0 := B2F.relIndex_sup_eq_of_le_normalizer' hP
  have h1 := Subgroup.relIndex_mul_card P (P ⊔ Y)
  rw [inf_eq_left.2 le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card Y (P ⊔ Y)
  rw [inf_eq_left.2 le_sup_right] at h2
  have h3 := Subgroup.relIndex_mul_card Y P
  have h4 := Subgroup.relIndex_mul_card (P ⊓ Y) Y
  rw [inf_eq_left.2 inf_le_right] at h4
  have hpos : 0 < Y.relIndex P * Nat.card ↥(Y ⊓ P) := by rw [h3]; exact Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [inf_comm Y P] at hpos h3 ⊢
  calc P.relIndex (P ⊔ Y) * (Y.relIndex P * Nat.card ↥(P ⊓ Y))
      = P.relIndex (P ⊔ Y) * Nat.card ↥P := by rw [h3]
    _ = Y.relIndex (P ⊔ Y) * Nat.card ↥Y := by rw [h1, h2]
    _ = (P ⊓ Y).relIndex Y * (Y.relIndex P * Nat.card ↥(P ⊓ Y)) := by
        rw [h0, ← h4]; ring

theorem burnsideC121_p4_sylow_of_le {P P' Y : Subgroup Ω} (hP : IsSylowTwoOf P Y) (hPP : P ≤ P')
    (hP'Y : P' ≤ Y) (hP'2 : IsPGroup 2 P') : IsSylowTwoOf P' Y :=
  ⟨hP'Y, hP'2, fun hd => hP.2.2 (hd.trans (Subgroup.relIndex_dvd_of_le_left Y hPP))⟩

theorem burnsideC121_p4_autI_le_normalizer {V : Subgroup Ω} (hV : IsElemAbelian 2 V)
    {K Y : Subgroup Ω} (hKY : K ≤ Subgroup.normalizer (Y : Set Ω)) :
    autI hV K ≤ Subgroup.normalizer (autI hV Y : Set (MulAut (IntMod V hV))) := by
  intro φ hφ
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  constructor
  · intro hψ
    exact C124.autI_conj_mem hV hKY φ hφ ψ hψ
  · intro hψ
    have := C124.autI_conj_mem hV hKY φ⁻¹ ((autI hV K).inv_mem hφ) _ hψ
    simpa [mul_assoc] using this

namespace burnsideC121_p4_Hyp

variable {X L T R V Y : Subgroup Ω} (h : burnsideC121_p4_Hyp X L T R V Y)
include h

theorem autI_K : autI h.hV (thompsonJ R ⊔ (X ⊓ Subgroup.centralizer (V : Set Ω))) =
    autI h.hV (thompsonJ R) := by
  rw [autI_sup h.hV (h.J_le_X.trans h.X_le_NV) (inf_le_left.trans h.X_le_NV),
    autI_eq_bot_of_le_centralizer h.hV inf_le_right, sup_bot_eq]

theorem odd_YK : ¬ 2 ∣ (Y ⊓ (thompsonJ R ⊔ (X ⊓ Subgroup.centralizer (V : Set Ω)))).relIndex Y := by
  set K := thompsonJ R ⊔ (X ⊓ Subgroup.centralizer (V : Set Ω)) with hK
  have hYN : Y ≤ Subgroup.normalizer (V : Set Ω) := h.hYX.trans h.X_le_NV
  rw [burnsideC121_p4_relIndex_autI h.hV inf_le_left hYN]
  have hC : (Y ⊓ K) ⊓ Subgroup.centralizer (V : Set Ω) = Y ⊓ Subgroup.centralizer (V : Set Ω) :=
    le_antisymm (inf_le_inf_right _ inf_le_left)
      (le_inf (le_inf inf_le_left (fun y hy => Subgroup.mem_sup_right ⟨h.hYX hy.1, hy.2⟩))
        inf_le_right)
  rw [hC, Subgroup.relIndex_self, mul_one]
  have hYK : autI h.hV (Y ⊓ K) = autI h.hV Y ⊓ autI h.hV (thompsonJ R) := by
    apply le_antisymm
    · refine le_inf (autI_mono h.hV inf_le_left) ?_
      rw [← h.autI_K]
      exact autI_mono h.hV inf_le_right
    · rintro φ ⟨hφY, hφJ⟩
      obtain ⟨y, hyY, rfl⟩ := (mem_autI h.hV).1 hφY
      obtain ⟨j, hjJ, hj⟩ := (mem_autI h.hV).1 hφJ
      have h2 : convI h.hV (j⁻¹ * y) = 1 := by rw [map_mul, map_inv, hj, inv_mul_cancel]
      have h3 := (convI_eq_one_iff h.hV _).1 h2
      have h4 : (j : Ω)⁻¹ * y ∈ X ⊓ Subgroup.centralizer (V : Set Ω) :=
        ⟨X.mul_mem (X.inv_mem (h.J_le_X hjJ)) (h.hYX hyY), by simpa using h3⟩
      have hyK : (y : Ω) ∈ K := by
        have : (y : Ω) = (j : Ω) * ((j : Ω)⁻¹ * y) := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hjJ) (Subgroup.mem_sup_right h4)
      exact (mem_autI h.hV).2 ⟨y, ⟨hyY, hyK⟩, rfl⟩
  rw [hYK]
  have hsyl' : IsSylowTwoOf (autI h.hV (thompsonJ R)) (autI h.hV (Y ⊔ thompsonJ R)) := h.hsyl
  have hYJN : Y ⊔ thompsonJ R ≤ Subgroup.normalizer (Y : Set Ω) :=
    sup_le Subgroup.le_normalizer (le_sup_left.trans h.hYN)
  have := A4.isSylowTwoOf_inf_normal hsyl' (N := autI h.hV Y) (autI_mono h.hV le_sup_left)
    (burnsideC121_p4_autI_le_normalizer h.hV hYJN)
  rw [inf_comm] at this
  exact this.2.2

theorem sylow_JQ_K : IsSylowTwoOf (thompsonJ R ⊔ pCoreOf 2 X)
    (thompsonJ R ⊔ (X ⊓ Subgroup.centralizer (V : Set Ω))) := by
  set K := thompsonJ R ⊔ (X ⊓ Subgroup.centralizer (V : Set Ω)) with hK
  have hJQK : thompsonJ R ⊔ pCoreOf 2 X ≤ K := sup_le_sup_left (le_inf h.Q_le_X h.Q_le_CV) _
  have hJQR : thompsonJ R ⊔ pCoreOf 2 X ≤ R := sup_le (h.J_le_S.trans h.S_le_R) h.hQR
  have hJQ2 : IsPGroup 2 ↥(thompsonJ R ⊔ pCoreOf 2 X) := h.hR2.to_le hJQR
  refine ⟨hJQK, hJQ2, ?_⟩
  have hKN : K ≤ Subgroup.normalizer (V : Set Ω) := (sup_le h.J_le_X inf_le_left).trans h.X_le_NV
  show ¬ 2 ∣ (thompsonJ R ⊔ pCoreOf 2 X).relIndex K
  rw [burnsideC121_p4_relIndex_autI h.hV hJQK hKN]
  have hJQ : autI h.hV (thompsonJ R ⊔ pCoreOf 2 X) = autI h.hV K := by
    rw [h.autI_K, autI_sup h.hV (h.J_le_X.trans h.X_le_NV) (h.Q_le_X.trans h.X_le_NV),
      autI_eq_bot_of_le_centralizer h.hV h.Q_le_CV, sup_bot_eq]
  rw [hJQ, Subgroup.relIndex_self, one_mul]
  have hC1 : (thompsonJ R ⊔ pCoreOf 2 X) ⊓ Subgroup.centralizer (V : Set Ω) = pCoreOf 2 X :=
    le_antisymm (h.le_Q (le_inf (inf_le_left.trans (sup_le h.J_le_X h.Q_le_X)) inf_le_right)
      (hJQ2.to_le inf_le_left)) (le_inf le_sup_right h.Q_le_CV)
  have hC2 : K ⊓ Subgroup.centralizer (V : Set Ω) = X ⊓ Subgroup.centralizer (V : Set Ω) :=
    le_antisymm (inf_le_inf_right _ (sup_le h.J_le_X inf_le_left)) (le_inf le_sup_right inf_le_right)
  rw [hC1, hC2]
  exact h.sylow_Q.2.2

theorem sylow_JQY : IsSylowTwoOf ((thompsonJ R ⊔ pCoreOf 2 X) ⊓ Y) Y := by
  set K := thompsonJ R ⊔ (X ⊓ Subgroup.centralizer (V : Set Ω)) with hK
  have hKN : K ≤ Subgroup.normalizer ((Y ⊓ K : Subgroup Ω) : Set Ω) :=
    B2F.le_normalizer_inf h.hYN Subgroup.le_normalizer
  have h1 := A4.isSylowTwoOf_inf_normal h.sylow_JQ_K (N := Y ⊓ K) inf_le_right hKN
  have hJQK : thompsonJ R ⊔ pCoreOf 2 X ≤ K := sup_le_sup_left (le_inf h.Q_le_X h.Q_le_CV) _
  have he : (thompsonJ R ⊔ pCoreOf 2 X) ⊓ (Y ⊓ K) = (thompsonJ R ⊔ pCoreOf 2 X) ⊓ Y := by
    rw [inf_comm Y K, ← inf_assoc, inf_eq_left.2 hJQK]
  rw [he] at h1
  refine ⟨inf_le_right, h1.2.1, ?_⟩
  have hmul := Subgroup.relIndex_mul_relIndex ((thompsonJ R ⊔ pCoreOf 2 X) ⊓ Y) (Y ⊓ K) Y
    (le_inf inf_le_right (inf_le_left.trans hJQK)) inf_le_left
  show ¬ 2 ∣ ((thompsonJ R ⊔ pCoreOf 2 X) ⊓ Y).relIndex Y
  rw [← hmul]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with hd | hd
  · exact h1.2.2 hd
  · exact h.odd_YK hd

theorem sylow_RY : IsSylowTwoOf (R ⊓ Y) Y :=
  burnsideC121_p4_sylow_of_le h.sylow_JQY
    (inf_le_inf_right _ (sup_le (h.J_le_S.trans h.S_le_R) h.hQR)) inf_le_right
    (h.hR2.to_le inf_le_left)

theorem sylow_R0Y : IsSylowTwoOf ((baum T ⊔ pCoreOf 2 X) ⊓ Y) Y :=
  burnsideC121_p4_sylow_of_le h.sylow_JQY (inf_le_inf_right _ (sup_le_sup_right h.J_le_S _))
    inf_le_right (h.hR2.to_le (inf_le_left.trans (sup_le h.S_le_R h.hQR)))

theorem R0_two : IsPGroup 2 ↥(baum T ⊔ pCoreOf 2 X) :=
  h.hR2.to_le (sup_le h.S_le_R h.hQR)

theorem H_le_X : (baum T ⊔ pCoreOf 2 X) ⊔ Y ≤ X := sup_le (sup_le h.S_le_X h.Q_le_X) h.hYX

theorem H_le_NV : (baum T ⊔ pCoreOf 2 X) ⊔ Y ≤ Subgroup.normalizer (V : Set Ω) :=
  h.H_le_X.trans h.X_le_NV

theorem H_le_NY : (baum T ⊔ pCoreOf 2 X) ⊔ Y ≤ Subgroup.normalizer (Y : Set Ω) :=
  sup_le h.SQ_le_NY Subgroup.le_normalizer

theorem Q_le_H : pCoreOf 2 X ≤ (baum T ⊔ pCoreOf 2 X) ⊔ Y := le_sup_right.trans le_sup_left

theorem J_le_H : thompsonJ R ≤ (baum T ⊔ pCoreOf 2 X) ⊔ Y :=
  h.J_le_S.trans (le_sup_left.trans le_sup_left)

theorem Y_le_H : Y ≤ (baum T ⊔ pCoreOf 2 X) ⊔ Y := le_sup_right

theorem sylow_R0H : IsSylowTwoOf (baum T ⊔ pCoreOf 2 X) ((baum T ⊔ pCoreOf 2 X) ⊔ Y) := by
  refine ⟨le_sup_left, h.R0_two, ?_⟩
  show ¬ 2 ∣ (baum T ⊔ pCoreOf 2 X).relIndex ((baum T ⊔ pCoreOf 2 X) ⊔ Y)
  rw [burnsideC121_p4_relIndex_sup h.SQ_le_NY]
  exact h.sylow_R0Y.2.2

theorem pow_mem_Y {x : Ω} (hx : x ∈ (baum T ⊔ pCoreOf 2 X) ⊔ Y) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ Y := by
  obtain ⟨r, hr, y, hy, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer h.SQ_le_NY).1 hx
  obtain ⟨k, hk⟩ := h.R0_two ⟨r, hr⟩
  have hk' : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hry : r * y = (r * y * r⁻¹) * r := by group
  have hy' : r * y * r⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 (h.SQ_le_NY hr) y).1 hy
  obtain ⟨y', hy'', he⟩ := A4.exists_pow_mul_eq (H := Y) hy' (h.SQ_le_NY hr) (2 ^ k)
  refine ⟨k, ?_⟩
  rw [hry, he, hk', mul_one]
  exact hy''

theorem H_CV : ((baum T ⊔ pCoreOf 2 X) ⊔ Y) ⊓ Subgroup.centralizer (V : Set Ω) = pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm _ (le_inf h.Q_le_H h.Q_le_CV)
  refine h.le_Q (inf_le_inf_right _ h.H_le_X) ?_
  intro g
  obtain ⟨k, hk⟩ := h.pow_mem_Y g.2.1
  have hkC : (g : Ω) ^ 2 ^ k ∈ Y ⊓ Subgroup.centralizer (V : Set Ω) :=
    ⟨hk, Subgroup.pow_mem _ g.2.2 _⟩
  rw [h.hYC] at hkC
  obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 Y) ⟨_, hkC⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have hm' : ((g : Ω) ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [pow_add, pow_mul, hm']

theorem autI_H : autI h.hV ((baum T ⊔ pCoreOf 2 X) ⊔ Y) = autI h.hV (Y ⊔ thompsonJ R) := by
  have hSN := h.S_le_X.trans h.X_le_NV
  have hQN := h.Q_le_X.trans h.X_le_NV
  have hYN := h.hYX.trans h.X_le_NV
  have hJN := h.J_le_X.trans h.X_le_NV
  rw [autI_sup h.hV (sup_le hSN hQN) hYN, autI_sup h.hV hSN hQN,
    autI_eq_bot_of_le_centralizer h.hV h.Q_le_CV, sup_bot_eq, autI_eq_autOn, h.autOn_baum,
    ← autI_eq_autOn h.hV, autI_sup h.hV hYN hJN, sup_comm]

theorem Q_le_O2H : pCoreOf 2 X ≤ pCoreOf 2 ((baum T ⊔ pCoreOf 2 X) ⊔ Y) :=
  le_pCoreOf_of_le_normalizer 2 h.Q_le_H (h.H_le_X.trans (le_normalizer_pCoreOf 2 X)) h.Q_two

theorem O2H_le_R0 : pCoreOf 2 ((baum T ⊔ pCoreOf 2 X) ⊔ Y) ≤ baum T ⊔ pCoreOf 2 X :=
  pCoreOf_le_of_isSylowTwoOf h.sylow_R0H

end burnsideC121_p4_Hyp

end CFSG.Quasithin
