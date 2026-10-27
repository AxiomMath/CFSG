module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Str

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem coreIn_ne_pCoreOf_right :
    coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B ≠ pCoreOf 2 B := by
  intro heq
  have hle : pCoreOf 2 B ≤ pCoreOf 2 A := by
    rw [← heq]
    exact coreIn_right_le_pCoreOf_left
  have hR : pCoreOf 2 A ⊓ pCoreOf 2 B = pCoreOf 2 B := inf_eq_right.mpr hle
  have h4 := h.relIndex_inf_pCoreOf_T
  rw [hR, h.gold.relIndex_pCoreOf_T_right] at h4
  omega

theorem not_mem_normalizer_of_orderOf_three {x : D} (hxB : x ∈ B) (hx3 : orderOf x = 3) :
    x ∉ Subgroup.normalizer (V : Set D) := by
  have hxT : x ∉ A ⊓ B := h.gold.vertex_right.not_mem_of_orderOf hx3
  have hx2T : x * x ∉ A ⊓ B := h.gold.vertex_right.sq_not_mem_of_orderOf hx3
  intro hxN
  obtain ⟨b, hbB, hbN⟩ := h.exists_not_mem_normalizer
  apply hbN
  rcases coset_decomp h.gold.relIndex_right hxB hxT hx2T hbB with hbT | ⟨t, htT, rfl⟩ |
      ⟨t, htT, rfl⟩
  · exact h.natural.reduced.2.1 hbT.1
  · exact Subgroup.mul_mem _ hxN (h.natural.reduced.2.1 htT.1)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hxN) (h.natural.reduced.2.1 htT.1)

theorem inf_centralizer_le_zpowers (hU : Nat.card (conjClosure V B) = 8) :
    conjClosure V B ⊓ Subgroup.centralizer (pCoreOf 2 B : Set D) ≤ Subgroup.zpowers z := by
  intro c hc
  by_contra hcz
  obtain ⟨x, hxB, hx3⟩ := h.gold.vertex_right.exists_order_three
  have hxN := h.not_mem_normalizer_of_orderOf_three hxB hx3
  have hx3' : x * x * x = 1 := by
    have h1 : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
    rw [← pow_three' x]
    exact h1
  set U : Subgroup D := conjClosure V B with hUdef
  set C : Subgroup D := U ⊓ Subgroup.centralizer (pCoreOf 2 B : Set D) with hCdef
  obtain ⟨a, ha1, haz, hVset⟩ := h.natural.basis
  have hmemV : ∀ u, u ∈ V ↔ u = 1 ∨ u = z ∨ u = a ∨ u = z * a := by
    intro u
    have := Set.ext_iff.mp hVset u
    simpa using this
  have hzV : z ∈ V := h.natural.z_mem_V
  have haV : a ∈ V := (hmemV a).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hzaV : z * a ∈ V := (hmemV _).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hzz : z * z = 1 := by
    have := h.natural.z_sq
    rwa [pow_two] at this
  have hVU : V ≤ U := le_conjClosure V B
  have hUab : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u := fun u hu v hv =>
    isElemAbelian_comm h.abelian hu hv
  have hUsq : ∀ u ∈ U, u * u = 1 := fun u hu => by
    have := isElemAbelian_pow_eq_one h.abelian hu
    rwa [pow_two] at this
  have hzC : z ∈ C := ⟨hVU hzV, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    mul_eq_of_conj_eq (h.central q (pCoreOf_le 2 B hq))⟩
  have hCB : ∀ b ∈ B, ∀ w ∈ C, b * w * b⁻¹ ∈ C := by
    intro b hb w hw
    exact ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B hb) w).mp hw.1,
      conj_mem_centralizer' (le_normalizer_pCoreOf 2 B hb) hw.2⟩
  have hVC : ¬ V ≤ C := by
    intro hVC
    apply h.coreIn_ne_pCoreOf_right
    have hUC : U ≤ C := conjClosure_le fun k hk v hv => hCB k hk v (hVC hv)
    apply le_antisymm ((coreIn_le_right _ _).trans inf_le_right)
    rw [← h.pCoreOf_inf_centralizer_eq_coreIn]
    refine le_inf le_rfl ?_
    intro q hq
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    exact ((Subgroup.mem_centralizer_iff.mp (hUC hu).2) q hq).symm
  have haC_V : a ∈ C → False := by
    intro haC
    apply hVC
    intro v hv
    rcases (hmemV v).mp hv with e | e | e | e
    · rw [e]; exact C.one_mem
    · rw [e]; exact hzC
    · rw [e]; exact haC
    · rw [e]; exact C.mul_mem hzC haC
  have hCV : ∀ g ∈ C, g ∈ V → g = 1 ∨ g = z := by
    intro g hgC hgV
    rcases (hmemV g).mp hgV with e | e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · exact (haC_V (e ▸ hgC)).elim
    · refine (haC_V ?_).elim
      have : a = z * g := by rw [e, ← mul_assoc, hzz, one_mul]
      rw [this]
      exact C.mul_mem hzC hgC
  have hcV : c ∉ V := fun hcV => hcz (by
    rcases hCV c hc hcV with e | e
    · rw [e]; exact Subgroup.one_mem _
    · rw [e]; exact Subgroup.mem_zpowers z)
  have hcU : c ∈ U := hc.1
  have hzx : x * z * x⁻¹ = z := h.central x hxB
  obtain ⟨c', hc'⟩ : ∃ c', c' = x * c * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a', a' = x * a * x⁻¹ := ⟨_, rfl⟩
  have hc_eq : c = x⁻¹ * c' * x := by rw [hc']; group
  have ha_eq : a = x⁻¹ * a' * x := by rw [ha']; group
  have hc'C : c' ∈ C := hc' ▸ hCB x hxB c hc
  have hc'U : c' ∈ U := hc'C.1
  have hφφ : x * (x * a' * x⁻¹) * x⁻¹ = a := by
    rw [ha']
    calc x * (x * (x * a * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * a * (x * x * x)⁻¹ := by group
      _ = a := by rw [hx3']; group
  have hc'cases : c' = c ∨ c' = z * c := by
    have hc'V : c' ∉ V := by
      intro hc'V
      apply hcV
      have hx1 : x⁻¹ * z * x = z := by
        have := h.central x⁻¹ (B.inv_mem hxB)
        simpa using this
      rcases hCV c' hc'C hc'V with e | e
      · rw [hc_eq, e]
        have : x⁻¹ * (1 : D) * x = 1 := by group
        rw [this]; exact V.one_mem
      · rw [hc_eq, e, hx1]; exact hzV
    have h1 : c' * c⁻¹ ∈ V := h.mul_inv_mem_V_of_not_mem hU hc'U hcU hc'V hcV
    have h2 : c' * c⁻¹ ∈ C := C.mul_mem hc'C (C.inv_mem hc)
    rcases hCV _ h2 h1 with e | e
    · left
      calc c' = (c' * c⁻¹) * c := by group
        _ = c := by rw [e, one_mul]
    · right
      calc c' = (c' * c⁻¹) * c := by group
        _ = z * c := by rw [e]
  have ha'V : a' ∉ V := by
    intro ha'V
    apply hxN
    have hconj : ∀ y ∈ V, x * y * x⁻¹ ∈ V := by
      intro y hy
      rcases (hmemV y).mp hy with e | e | e | e
      · rw [e]
        have : x * (1 : D) * x⁻¹ = 1 := by group
        rw [this]; exact V.one_mem
      · rw [e, hzx]; exact hzV
      · rw [e, ← ha']; exact ha'V
      · rw [e]
        have : x * (z * a) * x⁻¹ = z * a' := by
          rw [ha']
          calc x * (z * a) * x⁻¹ = (x * z * x⁻¹) * (x * a * x⁻¹) := by group
            _ = z * (x * a * x⁻¹) := by rw [hzx]
        rw [this]; exact V.mul_mem hzV ha'V
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨hconj y, fun hy => ?_⟩
    have h2 := hconj _ (hconj _ hy)
    have e : x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ = y := by
      calc _ = (x * x * x) * y * (x * x * x)⁻¹ := by group
        _ = y := by rw [hx3']; group
    rwa [e] at h2
  have ha'U : a' ∈ U := by
    rw [ha']
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B hxB) a).mp (hVU haV)
  have ha'C : a' ∉ C := by
    intro ha'C
    apply haC_V
    rw [ha_eq]
    have := hCB x⁻¹ (B.inv_mem hxB) a' ha'C
    simpa using this
  have hcc : c * c = 1 := hUsq c hcU
  have hcz' : c * z = z * c := hUab c hcU z (hVU hzV)
  have hac : a' * c⁻¹ ∈ V := h.mul_inv_mem_V_of_not_mem hU ha'U hcU ha'V hcV
  have hφm : ∀ g₁ g₂ : D, x * (g₁ * g₂) * x⁻¹ = (x * g₁ * x⁻¹) * (x * g₂ * x⁻¹) := fun g₁ g₂ => by
    group
  have hφ3 : ∀ g₁ g₂ g₃ : D, x * (g₁ * g₂ * g₃) * x⁻¹ =
      (x * g₁ * x⁻¹) * (x * g₂ * x⁻¹) * (x * g₃ * x⁻¹) := fun g₁ g₂ g₃ => by group
  have hcase1 : a' = a * c → False := by
    intro haw
    rcases hc'cases with e | e
    · have hE : x * a' * x⁻¹ = a := by
        calc x * a' * x⁻¹ = x * (a * c) * x⁻¹ := by rw [haw]
          _ = (x * a * x⁻¹) * (x * c * x⁻¹) := hφm a c
          _ = a' * c' := by rw [← ha', ← hc']
          _ = (a * c) * c := by rw [haw, e]
          _ = a := by rw [mul_assoc, hcc, mul_one]
      have : a' = a := by
        have h5 := hφφ
        rw [hE] at h5
        rw [ha']
        exact h5
      exact ha'V (this ▸ haV)
    · have hE : x * a' * x⁻¹ = a * z := by
        calc x * a' * x⁻¹ = x * (a * c) * x⁻¹ := by rw [haw]
          _ = (x * a * x⁻¹) * (x * c * x⁻¹) := hφm a c
          _ = a' * c' := by rw [← ha', ← hc']
          _ = (a * c) * (z * c) := by rw [haw, e]
          _ = a * (c * z) * c := by group
          _ = a * (z * c) * c := by rw [hcz']
          _ = a * z * (c * c) := by group
          _ = a * z := by rw [hcc, mul_one]
      have h3 : a' * z = a := by
        have h2 : x * (a * z) * x⁻¹ = a' * z := by rw [hφm, ← ha', hzx]
        rw [← h2, ← hE]
        exact hφφ
      have h4 : c * z = 1 := by
        apply mul_left_cancel (a := a)
        calc a * (c * z) = a * c * z := by group
          _ = a := by rw [← haw]; exact h3
          _ = a * 1 := (mul_one a).symm
      have h5 : c = z := by
        calc c = c * z * z := by rw [mul_assoc, hzz, mul_one]
          _ = z := by rw [h4, one_mul]
      exact hcV (h5 ▸ hzV)
  have hcase2 : a' = z * a * c → False := by
    intro haw
    rcases hc'cases with e | e
    · have hE : x * a' * x⁻¹ = a := by
        calc x * a' * x⁻¹ = x * (z * a * c) * x⁻¹ := by rw [haw]
          _ = (x * z * x⁻¹) * (x * a * x⁻¹) * (x * c * x⁻¹) := hφ3 z a c
          _ = z * a' * c' := by rw [hzx, ← ha', ← hc']
          _ = z * (z * a * c) * c := by rw [haw, e]
          _ = (z * z) * a * (c * c) := by group
          _ = a := by rw [hzz, hcc]; group
      have : a' = a := by
        have h5 := hφφ
        rw [hE] at h5
        rw [ha']
        exact h5
      exact ha'V (this ▸ haV)
    · have hza : z * a = a * z := hUab z (hVU hzV) a (hVU haV)
      have hE : x * a' * x⁻¹ = a * z := by
        calc x * a' * x⁻¹ = x * (z * a * c) * x⁻¹ := by rw [haw]
          _ = (x * z * x⁻¹) * (x * a * x⁻¹) * (x * c * x⁻¹) := hφ3 z a c
          _ = z * a' * c' := by rw [hzx, ← ha', ← hc']
          _ = z * (z * a * c) * (z * c) := by rw [haw, e]
          _ = (z * z) * a * (c * z) * c := by group
          _ = (z * z) * a * (z * c) * c := by rw [hcz']
          _ = (z * z) * a * z * (c * c) := by group
          _ = a * z := by rw [hzz, hcc]; group
      have h3 : a' * z = a := by
        have h2 : x * (a * z) * x⁻¹ = a' * z := by rw [hφm, ← ha', hzx]
        rw [← h2, ← hE]
        exact hφφ
      have h3' : z * a * c * z = a := by rw [← haw]; exact h3
      have h7 : z * a * c * z = a * c := by
        calc z * a * c * z = z * a * (c * z) := by group
          _ = z * a * (z * c) := by rw [hcz']
          _ = (z * a * z) * c := by group
          _ = (a * z * z) * c := by rw [hza]
          _ = a * c := by rw [mul_assoc a z z, hzz, mul_one]
      have h6 : a * c = a := h7.symm.trans h3'
      have h8 : c = 1 := by
        apply mul_left_cancel (a := a)
        rw [h6, mul_one]
      exact hcV (h8 ▸ V.one_mem)
  rcases (hmemV _).mp hac with e | e | e | e
  · apply ha'C
    have : a' = c := by
      calc a' = (a' * c⁻¹) * c := by group
        _ = c := by rw [e, one_mul]
    rw [this]; exact hc
  · apply ha'C
    have : a' = z * c := by
      calc a' = (a' * c⁻¹) * c := by group
        _ = z * c := by rw [e]
    rw [this]; exact C.mul_mem hzC hc
  · apply hcase1
    calc a' = (a' * c⁻¹) * c := by group
      _ = a * c := by rw [e]
  · apply hcase2
    calc a' = (a' * c⁻¹) * c := by group
      _ = z * a * c := by rw [e]

theorem card_pCoreOf_right_mul_card_inf_centralizer :
    Nat.card ↥(pCoreOf 2 B) *
        Nat.card ↥(conjClosure V B ⊓ Subgroup.centralizer (pCoreOf 2 B : Set D)) =
      Nat.card (conjClosure V B) *
        Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) := by
  have key := h.hypF91V.F97_card_mul h.abelian
  rwa [h.pCoreOf_inf_centralizer_eq_coreIn] at key

theorem card_inf_eq_two_mul_card_pCoreOf_right :
    Nat.card ↥(A ⊓ B) = 2 * Nat.card ↥(pCoreOf 2 B) := by
  have e := Subgroup.relIndex_mul_card (pCoreOf 2 B) (A ⊓ B)
  rw [inf_eq_left.mpr h.gold.pCoreOf_right_le, h.gold.relIndex_pCoreOf_T_right] at e
  exact e.symm

omit [Finite D] in
theorem zpowers_le_inf_centralizer :
    Subgroup.zpowers z ≤ conjClosure V B ⊓ Subgroup.centralizer (pCoreOf 2 B : Set D) := by
  refine Subgroup.zpowers_le.mpr ⟨le_conjClosure V B h.natural.z_mem_V, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
  exact mul_eq_of_conj_eq (h.central q (pCoreOf_le 2 B hq))

theorem card_inf_centralizer_eq_two (hU : Nat.card (conjClosure V B) = 8) :
    Nat.card ↥(conjClosure V B ⊓ Subgroup.centralizer (pCoreOf 2 B : Set D)) = 2 := by
  have e : conjClosure V B ⊓ Subgroup.centralizer (pCoreOf 2 B : Set D) = Subgroup.zpowers z :=
    le_antisymm (h.inf_centralizer_le_zpowers hU) h.zpowers_le_inf_centralizer
  rw [e]
  exact card_zpowers_eq_two h.natural

theorem card_pCoreOf_right_eq (hU : Nat.card (conjClosure V B) = 8) :
    Nat.card ↥(pCoreOf 2 B) = 4 * Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) := by
  have h1 := h.card_pCoreOf_right_mul_card_inf_centralizer
  rw [h.card_inf_centralizer_eq_two hU, hU] at h1
  omega

theorem card_inf_eq_eight_mul (hU : Nat.card (conjClosure V B) = 8) :
    Nat.card ↥(A ⊓ B) = 8 * Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) := by
  have := h.card_inf_eq_two_mul_card_pCoreOf_right
  rw [h.card_pCoreOf_right_eq hU] at this
  omega

theorem card_pCoreOf_left_eq (hU : Nat.card (conjClosure V B) = 8) :
    Nat.card ↥(pCoreOf 2 A) = 4 * Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) := by
  have h1 := h.card_inf_eq_two_mul_card_pCoreOf_left
  have h2 := h.card_inf_eq_eight_mul hU
  omega

theorem card_inf_pCoreOf_eq (hU : Nat.card (conjClosure V B) = 8) :
    Nat.card ↥(pCoreOf 2 A ⊓ pCoreOf 2 B) =
      2 * Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) := by
  have e := Subgroup.relIndex_mul_card (pCoreOf 2 A ⊓ pCoreOf 2 B) (pCoreOf 2 A)
  rw [inf_eq_left.mpr (inf_le_left : pCoreOf 2 A ⊓ pCoreOf 2 B ≤ pCoreOf 2 A),
    h.relIndex_inf_pCoreOf_left] at e
  have := h.card_pCoreOf_left_eq hU
  omega

theorem not_conjClosure_le_inf_centralizer :
    ¬ conjClosure V B ≤ conjClosure V B ⊓ Subgroup.centralizer (pCoreOf 2 B : Set D) := by
  intro hUC
  apply h.coreIn_ne_pCoreOf_right
  apply le_antisymm ((coreIn_le_right _ _).trans inf_le_right)
  rw [← h.pCoreOf_inf_centralizer_eq_coreIn]
  refine le_inf le_rfl ?_
  intro q hq
  refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
  exact ((Subgroup.mem_centralizer_iff.mp (hUC hu).2) q hq).symm

theorem sixty_four_le_card_inf : 64 ≤ Nat.card ↥(A ⊓ B) := by
  rcases h.card_conjClosure_eq with hU | hU
  · have h1 := h.card_inf_eq_eight_mul hU
    have h2 := h.eight_le_card_coreIn
    omega
  · have h1 := h.card_pCoreOf_right_mul_card_inf_centralizer
    have hK : 16 ≤ Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) := by
      have := Subgroup.card_le_of_le h.conjClosure_le_coreIn
      omega
    set C : Subgroup D := conjClosure V B ⊓ Subgroup.centralizer (pCoreOf 2 B : Set D) with hC
    have hCU : C ≤ conjClosure V B := inf_le_left
    have hC8 : Nat.card ↥C ≤ 8 := by
      obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hCU
      rw [hU] at hm
      have hm1 : m ≠ 1 := by
        rintro rfl
        have : Nat.card ↥C = 16 := by omega
        exact h.not_conjClosure_le_inf_centralizer
          (Subgroup.eq_of_le_of_card_ge hCU (by omega)).ge
      have hm0 : m ≠ 0 := by
        rintro rfl
        omega
      have hm2 : 2 ≤ m := by omega
      have := Nat.mul_le_mul_left (Nat.card ↥C) hm2
      omega
    have h3 : Nat.card ↥(pCoreOf 2 B) * Nat.card ↥C ≤ Nat.card ↥(pCoreOf 2 B) * 8 :=
      Nat.mul_le_mul_left _ hC8
    rw [hU] at h1
    have h4 := h.card_inf_eq_two_mul_card_pCoreOf_right
    omega

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
