module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cSub3C
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Red
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3c

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

open scoped Pointwise

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem inf_eq_of_card [Finite D] {X Q M : Subgroup D} (hMX : M ≤ X) (hMQ : M ≤ Q)
    (hXQ : ¬ X ≤ Q) (hX : Nat.card ↥X = 32) (hM : Nat.card ↥M = 16) : X ⊓ Q = M := by
  have hle : M ≤ X ⊓ Q := le_inf hMX hMQ
  have hdvd : Nat.card ↥(X ⊓ Q) ∣ 32 := hX ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card ↥(X ⊓ Q) ≠ 32 := by
    intro h
    exact hXQ ((Subgroup.eq_of_le_of_card_ge (inf_le_left : X ⊓ Q ≤ X) (by rw [h, hX])) ▸
      inf_le_right)
  have hle16 : Nat.card ↥(X ⊓ Q) ≤ 16 := by
    obtain ⟨k, hk⟩ := hdvd
    have hk0 : k ≠ 0 := by rintro rfl; omega
    have hk1 : k ≠ 1 := by rintro rfl; omega
    have : 2 ≤ k := by omega
    have := Nat.mul_le_mul_left (Nat.card ↥(X ⊓ Q)) this
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem card_inf_cases [Finite D] {M N : Subgroup D} (hM : M ≤ N) (hN : Nat.card ↥N = 32)
    (h8 : 8 ≤ Nat.card ↥M) : Nat.card ↥M = 8 ∨ Nat.card ↥M = 16 ∨ Nat.card ↥M = 32 := by
  have hdvd : Nat.card ↥M ∣ 32 := hN ▸ Subgroup.card_dvd_of_le hM
  have hle : Nat.card ↥M ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd
  generalize Nat.card ↥M = m at *
  interval_cases m <;> omega


section Final3

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂) {y e₁ e₂ : D} {Y : Subgroup D}
  (d : YDat A V a₁ y e₁ e₂ Y)

include g d

theorem YDat.exists_conj_e₁ (hU : Nat.card (conjClosure V B) = 8) (hyA : y ∈ A)
    (hy3 : orderOf y = 3) {t : D} (htT : t ∈ A ⊓ B) (htQ : t ∉ pCoreOf 2 A) :
    ∃ v ∈ V, t * e₁ * t⁻¹ = v * e₂ := by
  obtain ⟨q', hq'def⟩ : ∃ q', q' = t * y * t⁻¹ * y := ⟨_, rfl⟩
  have hq'Q : q' ∈ pCoreOf 2 A := by
    rw [hq'def]
    exact conj_inv_mem_of_vertex g.hyp.gold.vertex_left hy3 hyA htT htQ
  have hw : t * a₁ * t⁻¹ ∈ conjClosure V B :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B htT.2) a₁).mp g.a₁_mem_U
  have hwV : t * a₁ * t⁻¹ ∉ V := fun h => g.a₁_not_mem_V ((g.conj_mem_V_iff htT.1).mp h)
  obtain ⟨v, hv, hweq⟩ : ∃ v ∈ V, t * a₁ * t⁻¹ = v * a₁ := by
    rcases g.mem_U_cases hU hw with h | ⟨v, hv, h⟩
    · exact absurd h hwV
    · exact ⟨v, hv, h⟩
  have he₂' : e₂ = y⁻¹ * a₁ * y := by rw [← d.he₃]; group
  have e1 : t * e₁ * t⁻¹ = q' * ((y⁻¹ * v * y) * e₂) * q'⁻¹ := by
    calc t * e₁ * t⁻¹ = (t * y * t⁻¹) * (t * a₁ * t⁻¹) * (t * y * t⁻¹)⁻¹ := by
          rw [d.he₁]; group
      _ = (q' * y⁻¹) * (v * a₁) * (q' * y⁻¹)⁻¹ := by rw [hweq, hq'def]; group
      _ = q' * ((y⁻¹ * v * y) * (y⁻¹ * a₁ * y)) * q'⁻¹ := by group
      _ = q' * ((y⁻¹ * v * y) * e₂) * q'⁻¹ := by rw [he₂']
  have hv₁ : y⁻¹ * v * y ∈ V := by
    have := g.conj_mem_V (A.inv_mem hyA) hv
    simpa using this
  have he₂U : e₂ ∈ conjSub (y * y) (conjClosure V B) := by
    have : e₂ = (y * y) * a₁ * (y * y)⁻¹ := by rw [d.he₂, d.he₁]; group
    rw [this]
    exact mul_mem_conjSub g.a₁_mem_U
  have hc : q' * e₂ * q'⁻¹ * e₂⁻¹ ∈ V := by
    have h1 := V.inv_mem (g.comm_conjSub_mem_V hU (A.mul_mem hyA hyA) he₂U hq'Q)
    have e : (e₂ * q' * e₂⁻¹ * q'⁻¹)⁻¹ = q' * e₂ * q'⁻¹ * e₂⁻¹ := by group
    rwa [e] at h1
  refine ⟨(y⁻¹ * v * y) * (q' * e₂ * q'⁻¹ * e₂⁻¹), V.mul_mem hv₁ hc, ?_⟩
  rw [e1]
  have hcen : q' * (y⁻¹ * v * y) = (y⁻¹ * v * y) * q' := (g.V_comm_QA hv₁ hq'Q).symm
  calc q' * ((y⁻¹ * v * y) * e₂) * q'⁻¹
      = (q' * (y⁻¹ * v * y) * q'⁻¹) * (q' * e₂ * q'⁻¹) := by group
    _ = (y⁻¹ * v * y) * (q' * e₂ * q'⁻¹) := by rw [hcen]; group
    _ = ((y⁻¹ * v * y) * (q' * e₂ * q'⁻¹ * e₂⁻¹)) * e₂ := by group

theorem YDat.NA_not_le_QB : ¬ (conjClosure V B ⊔ Y ≤ pCoreOf 2 B) := by
  intro hle
  have he₁Q : e₁ ∈ pCoreOf 2 B := hle (d.e₁_mem_NA g)
  have he₂Q : e₂ ∈ pCoreOf 2 B := hle (d.e₂_mem_NA g)
  have h1 := g.hyp.commutator_mem a₁ g.a₁_mem_U e₁ he₁Q
  have h2 := g.hyp.commutator_mem a₁ g.a₁_mem_U e₂ he₂Q
  have ha : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right g.a₁_sq
  have hi1 : e₁⁻¹ = e₁ := inv_eq_of_mul_eq_one_right d.e₁_sq
  have hi2 : e₂⁻¹ = e₂ := inv_eq_of_mul_eq_one_right d.e₂_sq
  rw [ha, hi1] at h1
  rw [ha, hi2] at h2
  rcases zpowers_cases g.hyp h1 with e | e
  · exact d.κ₁_ne e
  · rcases zpowers_cases g.hyp h2 with e' | e'
    · exact d.κ₃_ne e'
    · exact d.κ_ne (e.trans e'.symm)

end Final3

section FinalNB

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)
  (hsq : ∀ q ∈ pCoreOf 2 B, q * q ∈ conjClosure V B)

include g

theorem Gen3.NB_not_le_QA (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 128)
    (hK : Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) = 16) :
    ¬ g.NB hsq ≤ pCoreOf 2 A := by
  intro hle
  have hR : g.NB hsq ≤ pCoreOf 2 A ⊓ pCoreOf 2 B := le_inf hle (g.NB_le_QB hsq)
  have heq : g.NB hsq = pCoreOf 2 A ⊓ pCoreOf 2 B :=
    Subgroup.eq_of_le_of_card_ge hR (by rw [g.card_R hT, g.card_NB hsq hU hK (g.card_QB' hT)])
  have hBR : B ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) := by
    rw [← heq]
    exact g.B_le_normalizer_NB hsq
  have hRB : pCoreOf 2 A ⊓ pCoreOf 2 B ≤ B := inf_le_right.trans (pCoreOf_le 2 B)
  have hRK := le_coreIn hRB hBR le_rfl
  have := Subgroup.card_le_of_le hRK
  rw [g.card_R hT, hK] at this
  omega

end FinalNB


section Compat

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂) {y e₁ e₂ : D} {Y : Subgroup D}
  (d : YDat A V a₁ y e₁ e₂ Y) (hsq : ∀ q ∈ pCoreOf 2 B, q * q ∈ conjClosure V B)

local notation "𝐍A" => (conjClosure V B ⊔ Y)
local notation "𝐍B" => g.NB hsq
local notation "𝐊" => coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B

include g d

theorem YDat.card_inf_NA_NB (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 128) (hyA : y ∈ A) (hy3 : orderOf y = 3)
    (hK : Nat.card ↥𝐊 = 16) : Nat.card ↥(𝐍A ⊓ 𝐍B) = 16 := by
  have hcA : Nat.card ↥𝐍A = 32 := d.card_NA g hU hyA
  have hcB : Nat.card ↥𝐍B = 32 := g.card_NB hsq hU hK (g.card_QB' hT)
  have hAT : 𝐍A ≤ A ⊓ B := (d.NA_le_QA g).trans g.hyp.gold.pCoreOf_left_le
  have hBT : 𝐍B ≤ A ⊓ B := (g.NB_le_QB hsq).trans g.hyp.gold.pCoreOf_right_le
  have hAnorm : A ≤ Subgroup.normalizer ((𝐍A : Subgroup D) : Set D) :=
    d.A_le_normalizer_NA g hU hyA hy3
  have hBnorm : B ≤ Subgroup.normalizer ((𝐍B : Subgroup D) : Set D) :=
    g.B_le_normalizer_NB hsq
  have hTA : A ⊓ B ≤ Subgroup.normalizer ((𝐍A : Subgroup D) : Set D) := inf_le_left.trans hAnorm
  have hTB : A ⊓ B ≤ Subgroup.normalizer ((𝐍B : Subgroup D) : Set D) := inf_le_right.trans hBnorm
  have hUM : conjClosure V B ≤ 𝐍A ⊓ 𝐍B := le_inf le_sup_left (g.U_le_NB hsq)
  have hprod := card_sup_mul_card_inf_of_le_normalizer (hAT.trans hTB)
  rw [hcA, hcB] at hprod
  have hsupT : 𝐍A ⊔ 𝐍B ≤ A ⊓ B := sup_le hAT hBT
  have hsupcard : Nat.card ↥(𝐍A ⊔ 𝐍B) ≤ 128 := hT ▸ Subgroup.card_le_of_le hsupT
  have h8 : 8 ≤ Nat.card ↥(𝐍A ⊓ 𝐍B) := hU ▸ Subgroup.card_le_of_le hUM
  rcases card_inf_cases (inf_le_left : 𝐍A ⊓ 𝐍B ≤ 𝐍A) hcA h8 with h | h | h
  · exfalso
    have hMU : conjClosure V B = 𝐍A ⊓ 𝐍B := Subgroup.eq_of_le_of_card_ge hUM (by omega)
    rw [h] at hprod
    have hsupeq : 𝐍A ⊔ 𝐍B = A ⊓ B := Subgroup.eq_of_le_of_card_ge hsupT (by omega)
    obtain ⟨t, htT, htQ⟩ : ∃ t ∈ A ⊓ B, t ∉ pCoreOf 2 A := by
      by_contra hall
      push Not at hall
      have := Subgroup.card_le_of_le (H := A ⊓ B) (K := pCoreOf 2 A) (fun t ht => hall t ht)
      rw [hT, g.card_QA' hT] at this
      omega
    obtain ⟨v, hv, hteq⟩ := d.exists_conj_e₁ g hU hyA hy3 htT htQ
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (𝐍A) (𝐍B) (hBT.trans hTA)
    have htmem : t ∈ ((𝐍A : Subgroup D) : Set D) * ((𝐍B : Subgroup D) : Set D) := by
      rw [← hmul]
      exact hsupeq ▸ htT
    obtain ⟨n, hn, m, hm, rfl⟩ := Set.mem_mul.mp htmem
    have he₁N : e₁ ∈ 𝐍A := d.e₁_mem_NA g
    have hu₁ : m * e₁ * m⁻¹ * e₁⁻¹ ∈ conjClosure V B := by
      rw [hMU]
      refine ⟨?_, ?_⟩
      · have h1 : m * e₁ * m⁻¹ ∈ 𝐍A :=
          (Subgroup.mem_normalizer_iff.mp (hTA (hBT hm)) e₁).mp he₁N
        exact (𝐍A).mul_mem h1 ((𝐍A).inv_mem he₁N)
      · have h1 : e₁ * m⁻¹ * e₁⁻¹ ∈ 𝐍B :=
          (Subgroup.mem_normalizer_iff.mp (hTB (hAT he₁N)) m⁻¹).mp ((𝐍B).inv_mem hm)
        have e : m * e₁ * m⁻¹ * e₁⁻¹ = m * (e₁ * m⁻¹ * e₁⁻¹) := by group
        rw [e]
        exact (𝐍B).mul_mem hm h1
    have hn₂ : n * e₁ * n⁻¹ * e₁⁻¹ ∈ V :=
      (g.mem_ceA_iff.mp (d.NA_le_ceA g hU hyA hn)).2.1 e₁ d.e₁_mem
    have hu₃ : n * (m * e₁ * m⁻¹ * e₁⁻¹) * n⁻¹ ∈ conjClosure V B :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B (hAT hn).2) _).mp hu₁
    have hPU : (n * (m * e₁ * m⁻¹ * e₁⁻¹) * n⁻¹) * (n * e₁ * n⁻¹ * e₁⁻¹) ∈ conjClosure V B :=
      (conjClosure V B).mul_mem hu₃ (le_conjClosure V B hn₂)
    have e1 : n * m * e₁ * (n * m)⁻¹ = ((n * (m * e₁ * m⁻¹ * e₁⁻¹) * n⁻¹) *
        (n * e₁ * n⁻¹ * e₁⁻¹)) * e₁ := by group
    rw [e1] at hteq
    have hUe : e₂ * e₁ ∈ conjClosure V B := by
      have h4 : e₂ = v⁻¹ * (((n * (m * e₁ * m⁻¹ * e₁⁻¹) * n⁻¹) * (n * e₁ * n⁻¹ * e₁⁻¹)) * e₁) := by
        rw [hteq]; group
      have h3 : e₂ * e₁ = v⁻¹ * ((n * (m * e₁ * m⁻¹ * e₁⁻¹) * n⁻¹) * (n * e₁ * n⁻¹ * e₁⁻¹)) := by
        calc e₂ * e₁ = v⁻¹ * (((n * (m * e₁ * m⁻¹ * e₁⁻¹) * n⁻¹) * (n * e₁ * n⁻¹ * e₁⁻¹)) * e₁) *
              e₁ := by rw [← h4]
          _ = v⁻¹ * ((n * (m * e₁ * m⁻¹ * e₁⁻¹) * n⁻¹) * (n * e₁ * n⁻¹ * e₁⁻¹)) *
              (e₁ * e₁) := by group
          _ = _ := by rw [d.e₁_sq, mul_one]
      rw [h3]
      exact (conjClosure V B).mul_mem ((conjClosure V B).inv_mem (le_conjClosure V B hv)) hPU
    have h1 : e₁⁻¹ = e₁ := inv_eq_of_mul_eq_one_right d.e₁_sq
    have h2 : e₂⁻¹ = e₂ := inv_eq_of_mul_eq_one_right d.e₂_sq
    have hYe : e₂ * e₁ ∈ Y := by
      have : e₂ * e₁ = (e₁ * e₂)⁻¹ := by rw [mul_inv_rev, h1, h2]
      rw [this]
      exact Y.inv_mem d.c₂_mem
    have hV' : e₂ * e₁ ∈ V := by
      rw [← d.inf_Y_eq g hU hyA]
      exact ⟨hUe, hYe⟩
    have hsq1 := g.V_sq hV'
    apply d.κ₂_ne
    calc e₁ * e₂ * e₁ * e₂ = (e₂ * e₁ * (e₂ * e₁))⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, h1, h2]; group
      _ = 1 := by rw [hsq1, inv_one]
  · exact h
  · exfalso
    have hMA : 𝐍A ⊓ 𝐍B = 𝐍A := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    have hMB : 𝐍A ⊓ 𝐍B = 𝐍B := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
    have heq : 𝐍A = 𝐍B := hMA.symm.trans hMB
    have hBnorm' : B ≤ Subgroup.normalizer ((𝐍A : Subgroup D) : Set D) := by
      rw [heq]
      exact hBnorm
    have hbot := g.hyp.gold.eq_bot_of_normalizes hAnorm hBnorm' hAT
    have : Nat.card ↥𝐍A = 1 := by rw [hbot]; simp
    omega

end Compat


section AutCohSec

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂) {y e₁ e₂ : D} {Y : Subgroup D}
  (d : YDat A V a₁ y e₁ e₂ Y) (hsq : ∀ q ∈ pCoreOf 2 B, q * q ∈ conjClosure V B)

local notation "𝐍A" => (conjClosure V B ⊔ Y)
local notation "𝐍B" => g.NB hsq
local notation "𝐊" => coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B

include g d

theorem YDat.autCoh (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 128)
    (hyA : y ∈ A) (hy3 : orderOf y = 3) (hK : Nat.card ↥𝐊 = 16) : AutCoh A B (𝐍A ⊔ 𝐍B) := by
  have hcA : Nat.card ↥𝐍A = 32 := d.card_NA g hU hyA
  have hcB : Nat.card ↥𝐍B = 32 := g.card_NB hsq hU hK (g.card_QB' hT)
  have hAT : 𝐍A ≤ A ⊓ B := (d.NA_le_QA g).trans g.hyp.gold.pCoreOf_left_le
  have hBT : 𝐍B ≤ A ⊓ B := (g.NB_le_QB hsq).trans g.hyp.gold.pCoreOf_right_le
  have hAnorm : A ≤ Subgroup.normalizer ((𝐍A : Subgroup D) : Set D) :=
    d.A_le_normalizer_NA g hU hyA hy3
  have hBnorm : B ≤ Subgroup.normalizer ((𝐍B : Subgroup D) : Set D) :=
    g.B_le_normalizer_NB hsq
  have hTA : A ⊓ B ≤ Subgroup.normalizer ((𝐍A : Subgroup D) : Set D) := inf_le_left.trans hAnorm
  have hTB : A ⊓ B ≤ Subgroup.normalizer ((𝐍B : Subgroup D) : Set D) := inf_le_right.trans hBnorm
  have hM := d.card_inf_NA_NB g hsq hU hT hyA hy3 hK
  have hprod := card_sup_mul_card_inf_of_le_normalizer (hAT.trans hTB)
  rw [hcA, hcB, hM] at hprod
  have hsupc : Nat.card ↥(𝐍A ⊔ 𝐍B) = 64 := by omega
  have hsupT : 𝐍A ⊔ 𝐍B ≤ A ⊓ B := sup_le hAT hBT
  have hNBnQA : ¬ 𝐍B ≤ pCoreOf 2 A := g.NB_not_le_QA hsq hU hT hK
  have hNAnQB : ¬ 𝐍A ≤ pCoreOf 2 B := d.NA_not_le_QB g
  have hBQA : 𝐍B ⊓ pCoreOf 2 A = 𝐍A ⊓ 𝐍B :=
    inf_eq_of_card (M := 𝐍A ⊓ 𝐍B) inf_le_right (inf_le_left.trans (d.NA_le_QA g)) hNBnQA hcB hM
  have hAQB : 𝐍A ⊓ pCoreOf 2 B = 𝐍A ⊓ 𝐍B :=
    inf_eq_of_card (M := 𝐍A ⊓ 𝐍B) inf_le_left (inf_le_right.trans (g.NB_le_QB hsq)) hNAnQB hcA hM
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (𝐍A) (𝐍B) (hBT.trans hTA)
  have hTQA : (𝐍A ⊔ 𝐍B) ⊓ pCoreOf 2 A = 𝐍A := by
    apply le_antisymm
    · rintro w ⟨hw, hwQ⟩
      have hw' : w ∈ ((𝐍A : Subgroup D) : Set D) * ((𝐍B : Subgroup D) : Set D) := by
        rw [← hmul]; exact hw
      obtain ⟨n, hn, m, hm, rfl⟩ := Set.mem_mul.mp hw'
      have hmQ : m ∈ pCoreOf 2 A := by
        have := (pCoreOf 2 A).mul_mem ((pCoreOf 2 A).inv_mem (d.NA_le_QA g hn)) hwQ
        simpa using this
      have hmM : m ∈ 𝐍B ⊓ pCoreOf 2 A := ⟨hm, hmQ⟩
      rw [hBQA] at hmM
      exact (𝐍A).mul_mem hn hmM.1
    · exact le_inf le_sup_left (d.NA_le_QA g)
  have hTQB : (𝐍A ⊔ 𝐍B) ⊓ pCoreOf 2 B = 𝐍B := by
    apply le_antisymm
    · rintro w ⟨hw, hwQ⟩
      have hw' : w ∈ ((𝐍A : Subgroup D) : Set D) * ((𝐍B : Subgroup D) : Set D) := by
        rw [← hmul]; exact hw
      obtain ⟨n, hn, m, hm, rfl⟩ := Set.mem_mul.mp hw'
      have hnQ : n ∈ pCoreOf 2 B := by
        have := (pCoreOf 2 B).mul_mem hwQ ((pCoreOf 2 B).inv_mem (g.NB_le_QB hsq hm))
        simpa using this
      have hnM : n ∈ 𝐍A ⊓ pCoreOf 2 B := ⟨hn, hnQ⟩
      rw [hAQB] at hnM
      exact (𝐍B).mul_mem hnM.2 hm
    · exact le_inf le_sup_right (g.NB_le_QB hsq)
  refine ⟨hsupT, ?_, ?_, ?_, ?_, ?_⟩
  · have := card_eq_relIndex_mul hsupT
    rw [hT, hsupc] at this
    omega
  · intro hle
    have heq : pCoreOf 2 A = 𝐍A ⊔ 𝐍B :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hsupc, g.card_QA' hT])
    exact hNBnQA (heq ▸ le_sup_right)
  · intro hle
    have heq : pCoreOf 2 B = 𝐍A ⊔ 𝐍B :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hsupc, g.card_QB' hT])
    exact hNAnQB (heq ▸ le_sup_left)
  · rw [hTQA]
    exact hAnorm
  · rw [hTQB]
    exact hBnorm

end AutCohSec

section FinalThm

variable {A B : Subgroup D} {z : D} {V : Subgroup D} [Finite D]

theorem isGoldCaseAutM12Cat_of_hKU
    (h : GoldHyp3 A B z V)
    (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 128) {y : D} (hyA : y ∈ A)
    (hy3 : orderOf y = 3)
    (hKU : ∀ q ∈ pCoreOf 2 A, q ∈ conjSub y (conjClosure V B) →
      (∀ u ∈ conjClosure V B, u * q = q * u) → q ∈ V) :
    IsGoldCaseAutM12Cat B A := by
  obtain ⟨x, a, a₁, a₂, g⟩ := GoldHyp3.exists_gen3 h
  obtain ⟨e₁, e₂, Y, d⟩ := g.exists_yDat hU hyA hy3 hKU
  have hsqA : ∀ q ∈ pCoreOf 2 A, q * q ∈ V := fun q hq => d.sq_mem_V_QA g hU hT hyA hq
  have hsqB : ∀ q ∈ pCoreOf 2 B, q * q ∈ conjClosure V B := fun q hq =>
    g.sq_mem_U_QB hU hsqA hq
  exact isGoldCaseAutM12Cat_of_coh h hU hT (d.autCoh g hsqB hU hT hyA hy3 (d.card_K g hU hT))

end FinalThm


section HKK

variable {A B : Subgroup D} {z : D} {V : Subgroup D} [Finite D]

local notation "𝐊" => coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B

theorem exists_hKU_of_inf_conjSub_le (h : GoldHyp3 A B z V) (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 128)
    (hKK : ∃ y ∈ A, 𝐊 ⊓ conjSub y 𝐊 ≤ V) :
    ∃ y ∈ A, orderOf y = 3 ∧ ∀ q ∈ pCoreOf 2 A, q ∈ conjSub y (conjClosure V B) →
      (∀ u ∈ conjClosure V B, u * q = q * u) → q ∈ V := by
  obtain ⟨y₁, hy₁A, hy₁N⟩ := hKK
  obtain ⟨y, hyA, hy3⟩ := h.gold.vertex_left.exists_order_three
  have hcube : y * y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3, pow_three'] at this
  have hyT := h.gold.vertex_left.not_mem_of_orderOf hy3
  have hy2T := h.gold.vertex_left.sq_not_mem_of_orderOf hy3
  have hKcard : 16 ≤ Nat.card ↥𝐊 := by
    have h1 := h.card_pCoreOf_left_le hU
    have h2 := h.card_inf_eq_two_mul_card_pCoreOf_left
    omega
  have hKT : ∀ t ∈ A ⊓ B, conjSub t 𝐊 = 𝐊 := fun t ht =>
    conjSub_eq_of_mem_normalizer (le_normalizer_coreIn _ _ ht.2)
  have hKy : 𝐊 ⊓ conjSub y 𝐊 ≤ V := by
    rcases coset_decomp h.gold.relIndex_left hyA hyT hy2T hy₁A with ht | ⟨t, ht, rfl⟩ |
        ⟨t, ht, rfl⟩
    · exfalso
      rw [hKT _ ht, inf_idem] at hy₁N
      have := Subgroup.card_le_of_le hy₁N
      rw [h.natural.card_eq] at this
      omega
    · rw [conjSub_mul, hKT t ht] at hy₁N
      exact hy₁N
    · rw [conjSub_mul, hKT t ht] at hy₁N
      intro w ⟨hwK, hwy⟩
      have hw' : y⁻¹ * w * y ∈ 𝐊 := mem_conjSub.mp hwy
      have hw'' : y⁻¹ * w * y ∈ conjSub (y * y) 𝐊 := by
        rw [mem_conjSub]
        have e : (y * y)⁻¹ * (y⁻¹ * w * y) * (y * y) = (y * y * y)⁻¹ * w * (y * y * y) := by
          group
        rw [e, hcube]
        simpa using hwK
      have hV : y⁻¹ * w * y ∈ V := hy₁N ⟨hw', hw''⟩
      have := (Subgroup.mem_normalizer_iff.mp (h.natural.reduced.2.1 hyA) _).mp hV
      have e : y * (y⁻¹ * w * y) * y⁻¹ = w := by group
      rwa [e] at this
  refine ⟨y, hyA, hy3, fun q hq hqy hqc => hKy ⟨h.mem_coreIn_of_comm hq hqc, ?_⟩⟩
  exact conjSub_mono y h.conjClosure_le_coreIn hqy

theorem isGoldCaseAutM12Cat_of_inf_conjSub_le
    (h : GoldHyp3 A B z V)
    (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 128)
    (hKK : ∃ y ∈ A, 𝐊 ⊓ conjSub y 𝐊 ≤ V) : IsGoldCaseAutM12Cat B A := by
  obtain ⟨y, hyA, hy3, hKU⟩ := exists_hKU_of_inf_conjSub_le h hU hT hKK
  exact isGoldCaseAutM12Cat_of_hKU h hU hT hyA hy3 hKU

end HKK

section Glue

universe u

variable {D : Type u} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem isGoldCaseM12_or_aut_of_inputs
    (hc : B3CardInput.{u})
    (hi : B3IntersectionInput.{u}) (h : GoldHyp3 A B z V) :
    IsGoldCaseM12 B A ∨ IsGoldCaseAutM12Cat B A := by
  have hk := b3KernelBoundInput_of_intersection hc hi
  have hU := hc D A B z V h
  rcases (b3_critDist_card_of_inputs hc hk h).2 with hT | hT
  · exact Or.inl (isGoldCaseM12_of_b3 h hU hT)
  · exact Or.inr (isGoldCaseAutM12Cat_of_inf_conjSub_le h hU hT (hi D A B z V h))

end Glue

end GoldAmL3c

end F6

end CFSG.Quasithin
