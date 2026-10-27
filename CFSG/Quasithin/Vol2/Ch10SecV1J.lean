module

public import CFSG.Quasithin.Vol2.Ch10SecV1I
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerImprimitiveField

public noncomputable section

namespace CFSG.Quasithin.Vol2.Ch10.V1C

open CFSG.ShultStronglyClosedTI.Singer Module MulAction
open scoped LinearAlgebra.Projectivization Pointwise

universe u

variable {F : Type u} [Field F]

theorem card_proj_odd [Finite F] [CharP F 2] {k : Type u} [Field k] [Algebra k F]
    (hm : 2 ≤ finrank k F) : Odd (Nat.card (ℙ k F)) ∧ 2 ≤ Nat.card (ℙ k F) := by
  have : Finite k := Finite.of_injective _ (algebraMap k F).injective
  have : CharP k 2 := RingHom.charP (algebraMap k F) (algebraMap k F).injective 2
  have := Fintype.ofFinite k
  obtain ⟨n, -, hn⟩ := FiniteField.card k 2
  have hq : Nat.card k = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hq2 : 2 ∣ Nat.card k := by
    rw [hq]
    exact dvd_pow_self 2 (PNat.ne_zero n)
  have hqpos : 2 ≤ Nat.card k := Finite.one_lt_card
  obtain ⟨j, hj⟩ : ∃ j, finrank k F = j + 1 + 1 := ⟨finrank k F - 2, by omega⟩
  rw [Projectivization.card_of_finrank k F hj, Finset.sum_range_succ', pow_zero]
  simp only [pow_succ, ← Finset.sum_mul]
  have hS : 1 ≤ ∑ i ∈ Finset.range (j + 1), Nat.card k ^ i := by
    rw [Finset.sum_range_succ', pow_zero]
    omega
  obtain ⟨q', hq'⟩ := hq2
  refine ⟨⟨(∑ i ∈ Finset.range (j + 1), Nat.card k ^ i) * q', ?_⟩, ?_⟩
  · rw [hq']
    ring
  · nlinarith

theorem normalizes_of_odd [Finite F] [CharP F 2] :
    ∀ (m : ℕ) (k : Type u) [Field k] [Algebra k F], finrank k F = m →
      ∀ G : Subgroup (F ≃ₗ[k] F), scalars k F ≤ G → Odd (Nat.card G) →
        ∀ g ∈ G, ∀ c : Fˣ, ∃ c' : Fˣ, ∀ x, g (c * x) = c' * g x := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro k _ _ hm G hSG hodd
  have : FiniteDimensional k F := Module.Finite.of_finite
  have : Finite k := Finite.of_injective _ (algebraMap k F).injective
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  ·
    intro g _ c
    refine ⟨c, fun x => ?_⟩
    have hm1 : finrank k F = 1 := by
      have := Module.finrank_pos (R := k) (M := F)
      omega
    have htop : (⊤ : IntermediateField k F) = ⊥ :=
      IntermediateField.finrank_eq_one_iff.mp ((IntermediateField.finrank_top').trans hm1)
    have hc : (c : F) ∈ (⊥ : IntermediateField k F) := htop ▸ IntermediateField.mem_top
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp hc
    rw [← hr, ← Algebra.smul_def, map_smul, Algebra.smul_def]
  obtain ⟨hPodd, hP2⟩ := card_proj_odd (k := k) (hm ▸ hm2)
  by_cases hprim : IsPreprimitive G (ℙ k F)
  ·
    have := isPreprimitive_projectiveImage G
    have := isPretransitive_projectiveImage_scalars (k := k) (F := F)
    rcases CFSG.burnside_schur (projectiveImage G) (projectiveImage (scalars k F)) hP2
        (projectiveImage_mono hSG) stabilizer_projectiveImage_scalars with
      h2 | ⟨p, -, -, -, -, -, hN⟩
    · exfalso
      have hdiv := mul_pred_dvd_card h2 hP2
      have hGcard := card_eq_card_projectiveImage_mul G hSG
      have hev : Even (Nat.card (ℙ k F) - 1) := by
        obtain ⟨j, hj⟩ := hPodd
        exact ⟨j, by omega⟩
      have h2dvd : 2 ∣ Nat.card G :=
        hev.two_dvd.trans ((Dvd.intro_left _ rfl).trans
          (hdiv.trans (Dvd.intro _ hGcard.symm)))
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
    · exact fun g hg c => normalizes_of_normal hSG hN hg c
  · obtain ⟨M, rfl⟩ := exists_minimalBlock G hSG hprim
    by_cases hl : M.l = ⊤
    ·
      intro g hg c
      have hB : ∀ b ∈ M.Bu, ∃ b' ∈ M.Bu, ∀ x, g (b * x) = b' * g x := by
        rcases M.burnside_schur_K with h2 | ⟨p, hp, -, e, he, haff⟩
        · exfalso
          have hΔ : 2 ≤ Nat.card M.Δ := by
            rw [Nat.card_coe_set_eq]
            exact M.one_lt_ncard
          have hdiv := mul_pred_dvd_card h2 hΔ
          have h1 : Nat.card M.permK ∣ Nat.card M.K := Subgroup.card_range_dvd _
          have h3 : Nat.card M.K ∣ Nat.card M.G := Subgroup.card_dvd_of_le M.K_le
          have hev : 2 ∣ Nat.card M.Δ * (Nat.card M.Δ - 1) := (Nat.even_mul_pred_self _).two_dvd
          exact (Nat.not_even_iff_odd.mpr hodd)
            (even_iff_two_dvd.mpr (hev.trans (hdiv.trans (h1.trans h3))))
        · exact fun b hb => M.normal_of_affine hl hp e he haff hg hb
      have hall : ∀ a ∈ M.l, ∃ a' ∈ M.l, ∀ x, g (a * x) = a' * g x := by
        intro a ha
        rw [M.mem_l_iff] at ha
        induction ha using Submodule.span_induction with
        | mem a ha =>
          obtain ⟨b, hb, rfl⟩ := ha
          obtain ⟨b', hb', h⟩ := hB b hb
          exact ⟨b', M.coe_mem_l hb', h⟩
        | zero => exact ⟨0, M.l.zero_mem, fun x => by rw [zero_mul, map_zero, zero_mul]⟩
        | add a b _ _ ha hb =>
          obtain ⟨a', ha', h⟩ := ha
          obtain ⟨b', hb', h'⟩ := hb
          exact ⟨a' + b', M.l.add_mem ha' hb', fun x => by rw [add_mul, map_add, h, h', add_mul]⟩
        | smul r a _ ha =>
          obtain ⟨a', ha', h⟩ := ha
          exact ⟨r • a', M.l.smul_mem ha', fun x => by
            rw [smul_mul_assoc, map_smul, h, smul_mul_assoc]⟩
      obtain ⟨a', -, ha'⟩ := hall c (hl ▸ IntermediateField.mem_top)
      have ha'0 : a' ≠ 0 := by
        intro h0
        have h1 := ha' 1
        rw [mul_one, h0, zero_mul] at h1
        exact c.ne_zero (g.injective (h1.trans g.map_zero.symm))
      exact ⟨Units.mk0 a' ha'0, ha'⟩
    ·
      have hσ : ∀ g ∈ M.G, ∃ σ : M.l ≃ₐ[k] M.l, ∀ (a : M.l) (x : F), g (a * x) = σ a * g x :=
        fun g hg => exists_algEquiv_of_normalizes M.l g (M.normalizes_of_ne_top hl hg)
      obtain ⟨G₁, -, hG₁lin, hG₁mem, h, -, hcardG⟩ :=
        exists_card_eq_mul_of_semilinear M.G M.l hσ
      have hl2 : 2 ≤ finrank k M.l := by
        have h1 : finrank k M.l ≠ 1 := fun h1 =>
          M.l_ne_bot (IntermediateField.finrank_eq_one_iff.mp h1)
        have := Module.finrank_pos (R := k) (M := M.l)
        omega
      have htower : finrank k M.l * finrank M.l F = m := by rw [Module.finrank_mul_finrank, hm]
      have hlF : 0 < finrank M.l F := Module.finrank_pos
      have hlt : finrank M.l F < m := by
        rw [← htower]
        nlinarith
      set G' := G₁.comap (restrictScalarsHom k M.l) with hG'
      have hcardG' : Nat.card G' = Nat.card G₁ := by
        have hmap : G'.map (restrictScalarsHom k M.l) = G₁ := by
          rw [Subgroup.map_comap_eq, inf_eq_right]
          intro g hg
          obtain ⟨g', hg'⟩ := exists_restrictScalarsHom_eq (hG₁lin g hg)
          exact ⟨g', hg'⟩
        rw [← hmap, Subgroup.card_map_of_injective restrictScalarsHom_injective]
      have hSG' : scalars M.l F ≤ G' := by
        rintro _ ⟨c, rfl⟩
        change restrictScalarsHom k M.l (scalarHom M.l F c) ∈ G₁
        rw [restrictScalarsHom_scalarHom]
        exact hG₁mem _ (hSG (scalarHom_mem_scalars c)) fun b x => by
          rw [scalarHom_apply, scalarHom_apply, mul_left_comm]
      have hodd' : Odd (Nat.card G') := by
        rw [hcardG']
        exact (Nat.odd_mul.mp (hcardG ▸ hodd)).1
      have hG'N := ih (finrank M.l F) hlt M.l rfl G' hSG' hodd'
      have hG₁N : ∀ h ∈ G₁, ∀ c : Fˣ, ∃ c' : Fˣ, ∀ x, h (c * x) = c' * h x := by
        intro h hh c
        obtain ⟨h', rfl⟩ := exists_restrictScalarsHom_eq (hG₁lin h hh)
        exact hG'N h' hh c
      intro g hg c
      refine normalizes_of_conj_le hG₁N (fun c => ?_) c
      obtain ⟨σ, hσg⟩ := hσ g hg
      refine hG₁mem _ (M.G.mul_mem (M.G.mul_mem hg (M.units_mem c)) (M.G.inv_mem hg))
        fun a x => ?_
      have hinv : g⁻¹ (a * x) = (σ.symm a : F) * g⁻¹ x := by
        apply g.injective
        rw [hσg, AlgEquiv.apply_symm_apply, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply]
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv, scalarHom_apply, mul_left_comm,
        hσg, AlgEquiv.apply_symm_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        scalarHom_apply]

end CFSG.Quasithin.Vol2.Ch10.V1C
