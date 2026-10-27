module

public import CFSG.Quasithin.Background.Harris.R1.D4L2BPre
public import CFSG.Quasithin.Background.Harris.R1.D4NFacts

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

open CFSG.Quasithin.D4Hex CFSG.LargeExtraspecial.S63 CFSG.CosetTable
  CFSG.Quasithin.Background.Harris.R1.J2Vert

@[expose] noncomputable def gD : Fin 5 → D := ![y1D, y2D, zeD, r0D, s0D]

theorem gD_eq : (fun i : Fin 5 => d4Word (nWords.getD i.val [])) = gD := by
  funext i
  fin_cases i <;> rfl

theorem evalWord_gD : ∀ r ∈ nRels, evalWord gD r = 1 := by
  intro r hr
  have := relsHold_spec nWords_lt Certificates.certificate300205.2.2 r hr
  rw [← gD_eq]
  exact this

@[expose] def W1 : List (Fin 5 × Bool) := (nRels.getD 25 []).drop 3

@[expose] def W2 : List (Fin 5 × Bool) := (nRels.getD 26 []).drop 3

theorem nRels_split : ∀ r ∈ nRels, (∀ p ∈ r, p.1.val < 4) ∨ r = nRels.getD 22 [] ∨
    r = nRels.getD 23 [] ∨ r = nRels.getD 24 [] ∨ r = nRels.getD 25 [] ∨
    r = nRels.getD 26 [] := by
  decide +kernel

theorem nRels22 : nRels.getD 22 [] = [(4, true), (4, true), (4, true)] := by decide +kernel

theorem nRels23 : nRels.getD 23 [] = [(4, true), (2, true), (4, false), (2, false)] := by
  decide +kernel

theorem nRels24 : nRels.getD 24 [] = [(3, true), (4, true), (3, false), (4, true)] := by
  decide +kernel

theorem nRels25 : nRels.getD 25 [] = [(4, true), (0, true), (4, false)] ++ W1 := by
  decide +kernel

theorem nRels26 : nRels.getD 26 [] = [(4, true), (1, true), (4, false)] ++ W2 := by
  decide +kernel

theorem W1_low : ∀ p ∈ W1, p.1.val < 3 := by decide +kernel

theorem W2_low : ∀ p ∈ W2, p.1.val < 3 := by decide +kernel

theorem nRels_mem (i : ℕ) (hi : i < 27) : nRels.getD i [] ∈ nRels := by
  interval_cases i <;> decide +kernel

theorem r0D_sq : r0D * r0D = 1 := by
  have h := evalWord_gD _ (nRels_mem 1 (by norm_num))
  have e : nRels.getD 1 [] = [(3, true), (3, true)] := by decide +kernel
  rw [e] at h
  simpa [evalWord, gD, mul_assoc] using h

theorem r0D_s0D : r0D * s0D * r0D⁻¹ * s0D = 1 := by
  have h := evalWord_gD _ (nRels_mem 24 (by norm_num))
  rw [nRels24] at h
  simpa [evalWord, gD, mul_assoc] using h

variable {G : Type*} [Group G] {K : Subgroup G}

theorem tail_rel (e : ↥K ≃* ↥d4H) {m : ℕ} (g : Fin m → G) (gY : Fin m → D)
    (W : List (Fin m × Bool)) (hW : ∀ p ∈ W, g p.1 ∈ K ∧ ebar e (g p.1) = gY p.1) {x : G}
    (hx : x ∈ K) {xY : D} (hxY : ebar e x = xY) (hrel : xY * evalWord gY W = 1) :
    x * evalWord g W = 1 := by
  obtain ⟨hw, hwe⟩ := evalWord_ebar e g gY W hW
  have h1 : evalWord gY W = xY⁻¹ := eq_inv_of_mul_eq_one_right hrel
  have h2 : evalWord g W = x⁻¹ := by
    apply ebar_inj e hw (K.inv_mem hx)
    rw [hwe, h1, ebar_inv e hx, hxY]
  rw [h2, mul_inv_cancel]

theorem relators_hold (e : ↥K ≃* ↥d4H) {Y1 Y2 T R0 S0 : G}
    (hY1 : Y1 ∈ K) (hY2 : Y2 ∈ K) (hT : T ∈ K) (hR0 : R0 ∈ K) (h1 : ebar e Y1 = y1D)
    (h2 : ebar e Y2 = y2D) (h3 : ebar e T = zeD) (h4 : ebar e R0 = r0D)
    (hS3 : S0 * S0 * S0 = 1) (hST : S0 * T * S0⁻¹ * T⁻¹ = 1) (hRS : R0 * S0 * R0⁻¹ * S0 = 1)
    (hSY1K : S0 * Y1 * S0⁻¹ ∈ K) (hSY1 : ebar e (S0 * Y1 * S0⁻¹) = s0D * y1D * s0D⁻¹)
    (hSY2K : S0 * Y2 * S0⁻¹ ∈ K) (hSY2 : ebar e (S0 * Y2 * S0⁻¹) = s0D * y2D * s0D⁻¹) :
    ∀ r ∈ nRels, evalWord ![Y1, Y2, T, R0, S0] r = 1 := by
  have hlow : ∀ i : Fin 5, i.val < 4 →
      (![Y1, Y2, T, R0, S0] : Fin 5 → G) i ∈ K ∧
        ebar e ((![Y1, Y2, T, R0, S0] : Fin 5 → G) i) = gD i := by
    intro i hi
    fin_cases i
    · exact ⟨hY1, h1⟩
    · exact ⟨hY2, h2⟩
    · exact ⟨hT, h3⟩
    · exact ⟨hR0, h4⟩
    · exact absurd hi (by decide)
  intro r hr
  rcases nRels_split r hr with hl | h | h | h | h | h
  · exact evalWord_eq_one_of_ebar e _ gD r (fun p hp => hlow p.1 (hl p hp)) (evalWord_gD r hr)
  · rw [h, nRels22]
    simpa [evalWord, mul_assoc] using hS3
  · rw [h, nRels23]
    simpa [evalWord, mul_assoc] using hST
  · rw [h, nRels24]
    simpa [evalWord, mul_assoc] using hRS
  · have hD := evalWord_gD _ (nRels_mem 25 (by norm_num))
    rw [nRels25, evalWord_append] at hD
    rw [h, nRels25, evalWord_append]
    have e1 : evalWord (![Y1, Y2, T, R0, S0] : Fin 5 → G) [(4, true), (0, true), (4, false)] =
        S0 * Y1 * S0⁻¹ := by simp [evalWord, mul_assoc]
    have e2 : evalWord gD [(4, true), (0, true), (4, false)] = s0D * y1D * s0D⁻¹ := by
      simp [evalWord, gD, mul_assoc]
    rw [e2] at hD
    rw [e1]
    exact tail_rel e _ gD W1 (fun p hp => hlow p.1 (lt_trans (W1_low p hp) (by norm_num))) hSY1K
      hSY1 hD
  · have hD := evalWord_gD _ (nRels_mem 26 (by norm_num))
    rw [nRels26, evalWord_append] at hD
    rw [h, nRels26, evalWord_append]
    have e1 : evalWord (![Y1, Y2, T, R0, S0] : Fin 5 → G) [(4, true), (1, true), (4, false)] =
        S0 * Y2 * S0⁻¹ := by simp [evalWord, mul_assoc]
    have e2 : evalWord gD [(4, true), (1, true), (4, false)] = s0D * y2D * s0D⁻¹ := by
      simp [evalWord, gD, mul_assoc]
    rw [e2] at hD
    rw [e1]
    exact tail_rel e _ gD W2 (fun p hp => hlow p.1 (lt_trans (W2_low p hp) (by norm_num))) hSY2K
      hSY2 hD

theorem exists_iso_of_relators
    (hF : D4NFacts) [Finite G] {X B : Subgroup G} (hBX : B ≤ X)
    {Y1 Y2 T R0 S0 : G} (hY1 : Y1 ∈ B) (hY2 : Y2 ∈ B) (hT : T ∈ B) (hR0 : R0 ∈ B) (hS0 : S0 ∈ X)
    (hrel : ∀ r ∈ nRels, evalWord ![Y1, Y2, T, R0, S0] r = 1)
    (hgen : Subgroup.closure ({Y1, Y2, T, R0} : Set G) = B) (hS0B : S0 ∉ B)
    (hX : Nat.card X = 3 * Nat.card B) (hB : Nat.card B = 28672)
    (eB : ↥B →* D) (h1 : eB ⟨Y1, hY1⟩ = y1D) (h2 : eB ⟨Y2, hY2⟩ = y2D) (h3 : eB ⟨T, hT⟩ = zeD)
    (h4 : eB ⟨R0, hR0⟩ = r0D) :
    ∃ ψ : ↥X ≃* ↥d4N, ∀ (b : G) (hb : b ∈ B), (ψ ⟨b, hBX hb⟩ : D) = eB ⟨b, hb⟩ := by
  have hp : ∀ r ∈ nRels, (r.map fun p => if p.2 then (![Y1, Y2, T, R0, S0] : Fin 5 → G) p.1
      else ((![Y1, Y2, T, R0, S0] : Fin 5 → G) p.1)⁻¹).prod = 1 := hrel
  have hrange := range_pgHom hp
  have hgX : ∀ i : Fin 5, (![Y1, Y2, T, R0, S0] : Fin 5 → G) i ∈ X := by
    intro i
    fin_cases i
    · exact hBX hY1
    · exact hBX hY2
    · exact hBX hT
    · exact hBX hR0
    · exact hS0
  have hCX : Subgroup.closure (Set.range (![Y1, Y2, T, R0, S0] : Fin 5 → G)) ≤ X :=
    (Subgroup.closure_le X).mpr (by rintro _ ⟨i, rfl⟩; exact hgX i)
  have hBC : B ≤ Subgroup.closure (Set.range (![Y1, Y2, T, R0, S0] : Fin 5 → G)) := by
    rw [← hgen]
    refine Subgroup.closure_mono ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  have hS0C : S0 ∈ Subgroup.closure (Set.range (![Y1, Y2, T, R0, S0] : Fin 5 → G)) :=
    Subgroup.subset_closure ⟨4, rfl⟩
  have hCeq : Subgroup.closure (Set.range (![Y1, Y2, T, R0, S0] : Fin 5 → G)) = X := by
    set C := Subgroup.closure (Set.range (![Y1, Y2, T, R0, S0] : Fin 5 → G)) with hC
    have hBpos : 0 < Nat.card B := Nat.card_pos
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hBC
    obtain ⟨n, hn⟩ := Subgroup.card_dvd_of_le hCX
    have hmn : m * n = 3 := by
      refine Nat.eq_of_mul_eq_mul_left hBpos ?_
      calc Nat.card B * (m * n) = (Nat.card B * m) * n := by ring
        _ = Nat.card C * n := by rw [← hm]
        _ = Nat.card X := hn.symm
        _ = Nat.card B * 3 := by rw [hX]; ring
    rcases (Nat.dvd_prime Nat.prime_three).mp ⟨n, hmn.symm⟩ with hm1 | hm3
    · exfalso
      have : B = C := Subgroup.eq_of_le_of_card_ge hBC (by rw [hm, hm1, mul_one])
      exact hS0B (this ▸ hS0C)
    · refine Subgroup.eq_of_le_of_card_ge hCX ?_
      rw [hX, hm, hm3, mul_comm]
  have hfin := card_PG_n_le.1
  have hle := card_PG_n_le.2
  have hge : 86016 ≤ Nat.card (Subgroup.closure
      (Set.range (![Y1, Y2, T, R0, S0] : Fin 5 → G))) := by
    rw [hCeq, hX, hB]
  have hinj := pgHom_injective hp hfin hle hge
  have hpr : (pgHom hp).range = X := hrange.trans hCeq
  let pE : PG 5 nRels ≃* ↥X :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hpr)
  let nE : PG 5 nRels ≃* ↥d4N :=
    (MonoidHom.ofInjective hF.inj_n).trans (MulEquiv.subgroupCongr hF.range_n)
  have hpE : ∀ i : Fin 5, (pE (PresentedGroup.of i) : G) = (![Y1, Y2, T, R0, S0] : Fin 5 → G) i :=
    fun i => pgHom_of hp i
  have hnE : ∀ i : Fin 5, (nE (PresentedGroup.of i) : D) = d4Word (nWords.getD i.val []) :=
    fun i => nModel_of i
  have hψ : ∀ (i : Fin 5) (x : ↥X), (x : G) = (![Y1, Y2, T, R0, S0] : Fin 5 → G) i →
      ((pE.symm.trans nE) x : D) = d4Word (nWords.getD i.val []) := by
    intro i x hx
    have : pE.symm x = PresentedGroup.of i :=
      pE.symm_apply_eq.mpr (Subtype.ext (by rw [hpE]; exact hx))
    show (nE (pE.symm x) : D) = _
    rw [this, hnE]
  refine ⟨pE.symm.trans nE, fun b hb => ?_⟩
  have key : ∀ b (hb' : b ∈ Subgroup.closure ({Y1, Y2, T, R0} : Set G)) (hb : b ∈ B),
      ((pE.symm.trans nE) ⟨b, hBX hb⟩ : D) = eB ⟨b, hb⟩ := by
    intro b hb'
    induction hb' using Subgroup.closure_induction with
    | mem x hx =>
      intro hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact (hψ 0 ⟨x, hBX hb⟩ rfl).trans h1.symm
      · exact (hψ 1 ⟨x, hBX hb⟩ rfl).trans h2.symm
      · exact (hψ 2 ⟨x, hBX hb⟩ rfl).trans h3.symm
      · exact (hψ 3 ⟨x, hBX hb⟩ rfl).trans h4.symm
    | one =>
      intro hb
      show (((pE.symm.trans nE) (1 : ↥X) : ↥d4N) : D) = (eB (1 : ↥B) : D)
      rw [map_one, map_one]
      rfl
    | mul x y hx hy ihx ihy =>
      intro hb
      have hxB : x ∈ B := by rw [← hgen]; exact hx
      have hyB : y ∈ B := by rw [← hgen]; exact hy
      show (((pE.symm.trans nE) ((⟨x, hBX hxB⟩ : ↥X) * ⟨y, hBX hyB⟩) : ↥d4N) : D) =
        (eB ((⟨x, hxB⟩ : ↥B) * ⟨y, hyB⟩) : D)
      rw [map_mul, map_mul, Subgroup.coe_mul, ihx hxB, ihy hyB]
    | inv x hx ih =>
      intro hb
      have hxB : x ∈ B := by rw [← hgen]; exact hx
      show (((pE.symm.trans nE) ((⟨x, hBX hxB⟩ : ↥X)⁻¹) : ↥d4N) : D) =
        (eB ((⟨x, hxB⟩ : ↥B)⁻¹) : D)
      rw [map_inv, map_inv, Subgroup.coe_inv, ih hxB]
  exact key b (by rw [hgen]; exact hb) hb

end CFSG.Quasithin.Background.Harris.R1.D4Vert
