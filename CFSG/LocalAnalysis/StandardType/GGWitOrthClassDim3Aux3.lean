module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassDim3Aux2

public section

namespace CFSG.StandardType.ZS

open Subgroup QuadraticMap

private theorem owD3_zmod7_sq_of_neg_not_sq (c e : ZMod 7) (hc : c ≠ 0) (he : e ≠ 0)
    (h : ¬ ∃ t : ZMod 7, t ^ 2 * e = -c) : ∃ t : ZMod 7, t ^ 2 * e = c := by
  revert c e
  decide +kernel


theorem owD3_wit_cr_of_isotropic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (c : ZMod p) (hc : c ≠ 0) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : A = closure (ClassRefl p Q c))
    (hp5 : 5 ≤ p) {a : U} (haQ : Q a = c) (ha : Q a ≠ 0)
    {r : U ≃ₗ[ZMod p] U} (hrA : r ∈ A)
    (hrefl : ∀ v, Q a • r v = Q a • v - polarBilin Q v a • a)
    {u : U} (hu_ne : u ≠ 0) (huQ : Q u = 0) (huB : polarBilin Q u a = 0) :
    WitCR p A r := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  letI : Field (ZMod p) := @ZMod.instField p ⟨hp⟩
  have h2K : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    exact absurd (le_antisymm hle hp.two_le) hp2
  have hr_a : r = owCr_orthRefl Q a ha := by
    ext w
    rw [owCr_orthRefl_apply]
    have h := hrefl w
    calc r w = (Q a)⁻¹ • (Q a • r w) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      _ = (Q a)⁻¹ • (Q a • w - polarBilin Q w a • a) := by rw [h]
      _ = w - (polarBilin Q w a / Q a) • a := by
            rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul]
            congr 1
            field_simp [ha]
  have hBau : polar Q a u = 0 := by
    rw [polar_comm]
    exact (polarBilin_apply_apply Q u a).symm.trans huB
  let v : U := a + (2 : ZMod p)⁻¹ • u
  have hQu : Q ((2 : ZMod p)⁻¹ • u) = 0 := by
    rw [QuadraticMap.map_smul, huQ]; simp
  have hBu : polarBilin Q ((2 : ZMod p)⁻¹ • u) a = 0 := by
    rw [polarBilin_apply_apply, polar_smul_left, polar_comm, hBau, smul_zero]
  have hQv : Q v = c := by
    show Q (a + (2 : ZMod p)⁻¹ • u) = c
    rw [owCr_Q_add_eq Q a ((2 : ZMod p)⁻¹ • u) hQu hBu, haQ]
  have hv : Q v ≠ 0 := by rw [hQv]; exact hc
  have hv_ne : v ≠ 0 := fun h => hv (by rw [h, QuadraticMap.map_zero])
  let g : U ≃ₗ[ZMod p] U := owCr_orthRefl Q v hv
  have hg_isom : ∀ w, Q (g w) = Q w := owCr_orthRefl_isIsom Q v hv
  have hgv : g v = -v := owCr_orthRefl_self Q v hv
  have hg_refl : IsRefl p g := by
    refine ⟨owCc_orthRefl_mul_self Q v hv, ?_⟩
    change Module.finrank (ZMod p)
      (LinearMap.range (((owCr_orthRefl Q v hv : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - LinearMap.id)) = 1
    rw [owCc_orthRefl_range Q v hv h2K]
    exact finrank_span_singleton hv_ne
  have hBav : polarBilin Q a v = 2 * Q a := by
    show polarBilin Q a (a + (2 : ZMod p)⁻¹ • u) = 2 * Q a
    rw [polarBilin_apply_apply, polar_add_right, polar_smul_right, hBau, smul_zero, add_zero,
      polar_self, two_smul]
    ring
  have hga : g a = -(a + u) := by
    have hg_eq : g = owCr_orthRefl Q v hv := rfl
    rw [hg_eq, owCr_orthRefl_apply]
    have hratio : polarBilin Q a v / Q v = 2 := by
      rw [hBav, hQv, haQ]
      field_simp
    rw [hratio]
    change a - (2 : ZMod p) • (a + (2 : ZMod p)⁻¹ • u) = -(a + u)
    rw [smul_add, smul_smul, mul_inv_cancel₀ h2K, one_smul]
    module
  have hga_ne : Q (g a) ≠ 0 := by rw [hg_isom a]; exact ha
  have ha'2 : Q (a + u) ≠ 0 := by rw [owCr_Q_add_eq Q a u huQ huB]; exact ha
  have hconj : g * r * g⁻¹ = owCr_orthRefl Q (a + u) ha'2 := by
    rw [hr_a, owCr_orthRefl_conj Q g hg_isom a ha hga_ne]
    convert owCr_orthRefl_neg Q (a + u) ha'2
      (show Q (-(a + u)) ≠ 0 by rwa [← hga]) using 2
  have horder : orderOf (owCr_orthRefl Q a ha * owCr_orthRefl Q (a + u) ha'2) = p :=
    owCr_order_orthRefl hp (by omega) Q a u ha ha'2 huQ huB hu_ne
  have hgA : g ∈ A := by
    rw [hA]
    exact Subgroup.subset_closure ⟨hg_refl, hg_isom, v, hQv, hgv⟩
  refine ⟨g, hgA, ?_⟩
  rw [hconj, hr_a, horder]
  omega


theorem owD3_exists_triple {U : Type} [AddCommGroup U] [Module (ZMod 7) U]
    [Module.Finite (ZMod 7) U]
    (Q : QuadraticForm (ZMod 7) U) (hQ : (polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 7) U = 3) (c : ZMod 7) (hc : c ≠ 0)
    {a : U} (haQ : Q a = c)
    (haniso : ¬ ∃ u : U, u ≠ 0 ∧ Q u = 0 ∧ polarBilin Q u a = 0) :
    ∃ b d : U, polarBilin Q a b = 0 ∧ polarBilin Q a d = 0 ∧
      polarBilin Q b d = 0 ∧ Q b = c ∧ Q d = c := by
  letI : Field (ZMod 7) := @ZMod.instField 7 ⟨by norm_num⟩
  have h2 : (2 : ZMod 7) ≠ 0 := by decide
  have ha : Q a ≠ 0 := by rw [haQ]; exact hc
  have ha_ne : a ≠ 0 := fun h => ha (by rw [h, QuadraticMap.map_zero])
  have hodd : Odd (Nat.card (ZMod 7)) := by rw [Nat.card_zmod]; norm_num
  let V : Submodule (ZMod 7) U := LinearMap.BilinForm.orthogonal (polarBilin Q) (ZMod 7 ∙ a)
  have hVfin : Module.finrank (ZMod 7) V = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ (ZMod 7 ∙ a), finrank_span_singleton ha_ne, hd]
  have hVnd : (polarBilin (Q.comp V.subtype)).Nondegenerate :=
    owCr_restrict_nondegenerate Q hQ h2 a ha
  obtain ⟨b, hbQ⟩ := owD3_binary_represents (K := ZMod 7) hodd (Q.comp V.subtype) hVnd hVfin c hc
  have hbUQ : Q (b : U) = c := by simpa using hbQ
  have ha_b : polarBilin Q a (b : U) = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp b.2) a (Submodule.mem_span_singleton_self a)
    simpa using h
  have hbUB : polarBilin Q (b : U) a = 0 := by
    rw [polarBilin_apply_apply, polar_comm, ← polarBilin_apply_apply]; exact ha_b
  have hbU_ne : (b : U) ≠ 0 := fun h => hc (by rw [← hbUQ, h, QuadraticMap.map_zero])
  have hind2 : LinearIndependent (ZMod 7) ![a, (b : U)] :=
    owD3_linearIndependent_pair Q hc ha haQ hbUQ (by rw [ha_b, zero_div]; decide)
  let W : Submodule (ZMod 7) U := Submodule.span (ZMod 7) ({a, (b : U)} : Set U)
  have hWfin : Module.finrank (ZMod 7) W = 2 := by
    have hset : ({a, (b : U)} : Set U) = Set.range ![a, (b : U)] := by
      ext x; simp [or_comm]
    change Module.finrank (ZMod 7) (Submodule.span (ZMod 7) ({a, (b : U)} : Set U)) = 2
    rw [hset, finrank_span_eq_card hind2]
    norm_num
  let D : Submodule (ZMod 7) U := LinearMap.BilinForm.orthogonal (polarBilin Q) W
  have hDfin : Module.finrank (ZMod 7) D = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ W, hWfin, hd]
  have hDne : D ≠ ⊥ := by intro h; rw [h] at hDfin; simp at hDfin
  obtain ⟨d₀, hd₀mem, hd₀ne⟩ := Submodule.ne_bot_iff D |>.mp hDne
  have hd₀_a : polarBilin Q a d₀ = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hd₀mem) a
      (Submodule.subset_span (by simp : a ∈ ({a, (b : U)} : Set U)))
    simpa using h
  have hd₀_a' : polarBilin Q d₀ a = 0 := by
    rw [polarBilin_apply_apply, polar_comm, ← polarBilin_apply_apply]; exact hd₀_a
  have hb_d : polarBilin Q (b : U) d₀ = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hd₀mem) (b : U)
      (Submodule.subset_span (by simp : (b : U) ∈ ({a, (b : U)} : Set U)))
    simpa using h
  have he : Q d₀ ≠ 0 := fun h0 => haniso ⟨d₀, hd₀ne, h0, hd₀_a'⟩
  have h_not_sq : ¬ ∃ t : ZMod 7, t ^ 2 * Q d₀ = -c := by
    rintro ⟨t, ht⟩
    apply haniso
    refine ⟨(b : U) + t • d₀, ?_, ?_, ?_⟩
    · intro hzero
      have hb_eq : (b : U) = -(t • d₀) := eq_neg_of_add_eq_zero_left hzero
      have hQt : Q (t • d₀) = t ^ 2 * Q d₀ := by
        rw [QuadraticMap.map_smul, smul_eq_mul]; ring
      have hc_eq : c = -c := by
        have h1 : Q (b : U) = -c := by
          calc Q (b : U) = Q (-(t • d₀)) := by rw [hb_eq]
            _ = Q (t • d₀) := by rw [QuadraticMap.map_neg]
            _ = t ^ 2 * Q d₀ := hQt
            _ = -c := ht
        rw [hbUQ] at h1
        exact h1
      have h2c : (2 : ZMod 7) * c = 0 := by linear_combination hc_eq
      exact (mul_ne_zero h2 hc) h2c
    · have hpolar : polar Q (b : U) d₀ = 0 := by
        rw [← polarBilin_apply_apply]; exact hb_d
      calc Q ((b : U) + t • d₀)
          = Q (b : U) + Q (t • d₀) + polar Q (b : U) (t • d₀) := QuadraticMap.map_add Q _ _
        _ = c + t ^ 2 * Q d₀ + t * polar Q (b : U) d₀ := by
              rw [QuadraticMap.map_smul, polar_smul_right, hbUQ]
              ring
        _ = c + t ^ 2 * Q d₀ + 0 := by rw [hpolar, mul_zero]
        _ = 0 := by rw [ht]; ring
    · calc polarBilin Q ((b : U) + t • d₀) a
          = polarBilin Q (b : U) a + polarBilin Q (t • d₀) a := by rw [map_add]; rfl
        _ = 0 := by
              rw [hbUB, polarBilin_apply_apply, polar_smul_left,
                show polar Q d₀ a = 0 by rw [← polarBilin_apply_apply]; exact hd₀_a']
              ring
  obtain ⟨t, ht⟩ := owD3_zmod7_sq_of_neg_not_sq c (Q d₀) hc he h_not_sq
  refine ⟨(b : U), t • d₀, ha_b, ?_, ?_, hbUQ, ?_⟩
  · rw [polarBilin_apply_apply, polar_smul_right,
      show polar Q a d₀ = 0 by rw [← polarBilin_apply_apply]; exact hd₀_a, smul_zero]
  · rw [polarBilin_apply_apply, polar_smul_right,
      show polar Q (b : U) d₀ = 0 by rw [← polarBilin_apply_apply]; exact hb_d, smul_zero]
  · simpa [QuadraticMap.map_smul, smul_eq_mul, pow_two, mul_assoc] using ht


theorem owD3_linearIndependent_triple {K : Type*} [Field K] {U : Type} [AddCommGroup U] [Module K U]
    (h2 : (2 : K) ≠ 0) (Q : QuadraticForm K U) {a b d : U}
    (ha : Q a ≠ 0) (hb : Q b ≠ 0) (hd : Q d ≠ 0)
    (hab : polarBilin Q a b = 0) (had : polarBilin Q a d = 0) (hbd : polarBilin Q b d = 0) :
    LinearIndependent K ![a, b, d] := by
  have hba : polarBilin Q b a = 0 := by
    rw [polarBilin_apply_apply, polar_comm, ← polarBilin_apply_apply]; exact hab
  have hda : polarBilin Q d a = 0 := by
    rw [polarBilin_apply_apply, polar_comm, ← polarBilin_apply_apply]; exact had
  have hdb : polarBilin Q d b = 0 := by
    rw [polarBilin_apply_apply, polar_comm, ← polarBilin_apply_apply]; exact hbd
  have hba' : polar Q b a = 0 := by rw [← polarBilin_apply_apply]; exact hba
  have hda' : polar Q d a = 0 := by rw [← polarBilin_apply_apply]; exact hda
  have hdb' : polar Q d b = 0 := by rw [← polarBilin_apply_apply]; exact hdb
  have hab' : polar Q a b = 0 := by rw [← polarBilin_apply_apply]; exact hab
  have had' : polar Q a d = 0 := by rw [← polarBilin_apply_apply]; exact had
  have hbd' : polar Q b d = 0 := by rw [← polarBilin_apply_apply]; exact hbd
  have hza : polar Q (0 : U) a = 0 := by simp
  have hzb : polar Q (0 : U) b = 0 := by simp
  have hzd : polar Q (0 : U) d = 0 := by simp
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 : g 0 = 0 := by
    have h := congrArg (fun w => polarBilin Q w a) hg
    rw [map_sum, Fin.sum_univ_three] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, LinearMap.add_apply,
      polarBilin_apply_apply, polar_smul_left] at h
    rw [polar_self, two_smul, hba', hda', hza, smul_zero, smul_zero, add_zero, add_zero,
      smul_eq_mul] at h
    have hmul : g 0 * ((2 : K) * Q a) = 0 := by
      convert h using 1
      ring
    rcases mul_eq_zero.mp hmul with h' | h'
    · exact h'
    · exact absurd h' (mul_ne_zero h2 ha)
  have h1 : g 1 = 0 := by
    have h := congrArg (fun w => polarBilin Q w b) hg
    rw [map_sum, Fin.sum_univ_three] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, LinearMap.add_apply,
      polarBilin_apply_apply, polar_smul_left] at h
    rw [polar_self, two_smul, hab', hdb', hzb, smul_zero, smul_zero, zero_add, add_zero,
      smul_eq_mul] at h
    have hmul : g 1 * ((2 : K) * Q b) = 0 := by
      convert h using 1
      ring
    rcases mul_eq_zero.mp hmul with h' | h'
    · exact h'
    · exact absurd h' (mul_ne_zero h2 hb)
  have h2' : g 2 = 0 := by
    have h := congrArg (fun w => polarBilin Q w d) hg
    rw [map_sum, Fin.sum_univ_three] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, LinearMap.add_apply,
      polarBilin_apply_apply, polar_smul_left] at h
    rw [polar_self, two_smul, had', hbd', hzd] at h
    simp only [smul_zero, zero_add, add_zero] at h
    rw [smul_eq_mul] at h
    have hmul : g 2 * ((2 : K) * Q d) = 0 := by
      convert h using 1
      ring
    rcases mul_eq_zero.mp hmul with h' | h'
    · exact h'
    · exact absurd h' (mul_ne_zero h2 hd)
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2'

theorem owD3_prod_orthRefl_triple {K : Type*} [Field K] {U : Type} [AddCommGroup U] [Module K U]
    [FiniteDimensional K U]
    (h2 : (2 : K) ≠ 0) (Q : QuadraticForm K U) {a b d : U} {c : K} (hc : c ≠ 0)
    (ha : Q a ≠ 0) (hb : Q b ≠ 0) (hd' : Q d ≠ 0)
    (haQ : Q a = c) (hbQ : Q b = c) (hdQ : Q d = c)
    (hab : polarBilin Q a b = 0) (had : polarBilin Q a d = 0) (hbd : polarBilin Q b d = 0)
    (hind : LinearIndependent K ![a, b, d]) (hfin : Module.finrank K U = 3) :
    owCr_orthRefl Q a ha * owCr_orthRefl Q b hb * owCr_orthRefl Q d hd' = LinearEquiv.neg K := by
  have hba : polarBilin Q b a = 0 := by
    rw [polarBilin_apply_apply, polar_comm, ← polarBilin_apply_apply]; exact hab
  have hda : polarBilin Q d a = 0 := by
    rw [polarBilin_apply_apply, polar_comm, ← polarBilin_apply_apply]; exact had
  have hdb : polarBilin Q d b = 0 := by
    rw [polarBilin_apply_apply, polar_comm, ← polarBilin_apply_apply]; exact hbd
  have hra : owCr_orthRefl Q a ha a = -a := owCr_orthRefl_self Q a ha
  have hrb : owCr_orthRefl Q b hb b = -b := owCr_orthRefl_self Q b hb
  have hrd : owCr_orthRefl Q d hd' d = -d := owCr_orthRefl_self Q d hd'
  have hra_b : owCr_orthRefl Q a ha b = b := by
    rw [owCr_orthRefl_apply, hba, zero_div, zero_smul, sub_zero]
  have hra_d : owCr_orthRefl Q a ha d = d := by
    rw [owCr_orthRefl_apply, hda, zero_div, zero_smul, sub_zero]
  have hrb_a : owCr_orthRefl Q b hb a = a := by
    rw [owCr_orthRefl_apply, hab, zero_div, zero_smul, sub_zero]
  have hrb_d : owCr_orthRefl Q b hb d = d := by
    rw [owCr_orthRefl_apply, hdb, zero_div, zero_smul, sub_zero]
  have hrd_a : owCr_orthRefl Q d hd' a = a := by
    rw [owCr_orthRefl_apply, had, zero_div, zero_smul, sub_zero]
  have hrd_b : owCr_orthRefl Q d hd' b = b := by
    rw [owCr_orthRefl_apply, hbd, zero_div, zero_smul, sub_zero]
  have hT_a : (owCr_orthRefl Q a ha * owCr_orthRefl Q b hb * owCr_orthRefl Q d hd') a = -a := by
    change owCr_orthRefl Q a ha (owCr_orthRefl Q b hb (owCr_orthRefl Q d hd' a)) = -a
    rw [hrd_a, hrb_a, hra]
  have hT_b : (owCr_orthRefl Q a ha * owCr_orthRefl Q b hb * owCr_orthRefl Q d hd') b = -b := by
    change owCr_orthRefl Q a ha (owCr_orthRefl Q b hb (owCr_orthRefl Q d hd' b)) = -b
    rw [hrd_b, hrb, map_neg, hra_b]
  have hT_d : (owCr_orthRefl Q a ha * owCr_orthRefl Q b hb * owCr_orthRefl Q d hd') d = -d := by
    change owCr_orthRefl Q a ha (owCr_orthRefl Q b hb (owCr_orthRefl Q d hd' d)) = -d
    rw [hrd, map_neg, hrb_d, map_neg, hra_d]
  have hspan : Submodule.span K (Set.range ![a, b, d]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hind, hfin]
    norm_num
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on hspan
  intro v hv
  rcases hv with ⟨i, rfl⟩
  fin_cases i
  · simpa using hT_a
  · simpa using hT_b
  · simpa using hT_d

private theorem owD3_neg_one_of_anisotropic {U : Type} [AddCommGroup U] [Module (ZMod 7) U]
    [Module.Finite (ZMod 7) U]
    (Q : QuadraticForm (ZMod 7) U) (hQ : (polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 7) U = 3) (c : ZMod 7) (hc : c ≠ 0)
    {A : Subgroup (U ≃ₗ[ZMod 7] U)} (hA : A = closure (ClassRefl 7 Q c))
    {a : U} (haQ : Q a = c)
    (haniso : ¬ ∃ u : U, u ≠ 0 ∧ Q u = 0 ∧ polarBilin Q u a = 0) :
    (LinearEquiv.neg (ZMod 7) : U ≃ₗ[ZMod 7] U) ∈ A := by
  letI : Field (ZMod 7) := @ZMod.instField 7 ⟨by norm_num⟩
  have h2 : (2 : ZMod 7) ≠ 0 := by decide
  have ha : Q a ≠ 0 := by rw [haQ]; exact hc
  haveI : FiniteDimensional (ZMod 7) U := ‹Module.Finite (ZMod 7) U›
  obtain ⟨b, d, hab, had, hbd, hbQ, hdQ⟩ := owD3_exists_triple Q hQ hd c hc haQ haniso
  have hb' : Q b ≠ 0 := by rw [hbQ]; exact hc
  have hd' : Q d ≠ 0 := by rw [hdQ]; exact hc
  have hind : LinearIndependent (ZMod 7) ![a, b, d] :=
    owD3_linearIndependent_triple h2 Q ha hb' hd' hab had hbd
  have hprod : owCr_orthRefl Q a ha * owCr_orthRefl Q b hb' * owCr_orthRefl Q d hd' =
      LinearEquiv.neg (ZMod 7) :=
    owD3_prod_orthRefl_triple h2 Q hc ha hb' hd' haQ hbQ hdQ hab had hbd hind hd
  have hra : owCr_orthRefl Q a ha ∈ A := by
    rw [hA]
    refine Subgroup.subset_closure ⟨⟨owCc_orthRefl_mul_self Q a ha, ?_⟩,
      owCr_orthRefl_isIsom Q a ha, a, haQ, owCr_orthRefl_self Q a ha⟩
    change Module.finrank (ZMod 7)
      (LinearMap.range (((owCr_orthRefl Q a ha : U ≃ₗ[ZMod 7] U) : U →ₗ[ZMod 7] U) - LinearMap.id)) = 1
    rw [owCc_orthRefl_range Q a ha h2]
    exact finrank_span_singleton (fun h => ha (by rw [h, QuadraticMap.map_zero]))
  have hrb : owCr_orthRefl Q b hb' ∈ A := by
    rw [hA]
    refine Subgroup.subset_closure ⟨⟨owCc_orthRefl_mul_self Q b hb', ?_⟩,
      owCr_orthRefl_isIsom Q b hb', b, hbQ, owCr_orthRefl_self Q b hb'⟩
    change Module.finrank (ZMod 7)
      (LinearMap.range (((owCr_orthRefl Q b hb' : U ≃ₗ[ZMod 7] U) : U →ₗ[ZMod 7] U) - LinearMap.id)) = 1
    rw [owCc_orthRefl_range Q b hb' h2]
    exact finrank_span_singleton (fun h => hb' (by rw [h, QuadraticMap.map_zero]))
  have hrd : owCr_orthRefl Q d hd' ∈ A := by
    rw [hA]
    refine Subgroup.subset_closure ⟨⟨owCc_orthRefl_mul_self Q d hd', ?_⟩,
      owCr_orthRefl_isIsom Q d hd', d, hdQ, owCr_orthRefl_self Q d hd'⟩
    change Module.finrank (ZMod 7)
      (LinearMap.range (((owCr_orthRefl Q d hd' : U ≃ₗ[ZMod 7] U) : U →ₗ[ZMod 7] U) - LinearMap.id)) = 1
    rw [owCc_orthRefl_range Q d hd' h2]
    exact finrank_span_singleton (fun h => hd' (by rw [h, QuadraticMap.map_zero]))
  have hmem : owCr_orthRefl Q a ha * owCr_orthRefl Q b hb' * owCr_orthRefl Q d hd' ∈ A :=
    mul_mem (mul_mem hra hrb) hrd
  rw [hprod] at hmem
  exact hmem


private theorem owD3_not_dvd_48 {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) : ¬ p ∣ 48 := by
  intro h
  have hle : p ≤ 48 := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> norm_num at *

private theorem owD3_not_dvd_45 {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) : ¬ p ∣ 45 := by
  intro h
  have hle : p ≤ 45 := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> norm_num at *

theorem owD3_wit_orthClass_dim3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (c : ZMod p) (hc : c ≠ 0) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : A = closure (ClassRefl p Q c))
    (hp7 : 7 ≤ p) (hd : Module.finrank (ZMod p) U = 3) :
    WitNEG3 p A ∨ ∀ r ∈ A, IsRefl p r → WitCR p A r := by
  by_cases h11 : 11 ≤ p
  · right
    by_cases hp47 : p = 47
    · subst p
      have hμ : (4 : ZMod 47) ^ 2 ≠ 4 := by decide
      have hx0 : 2 - (4 : ZMod 47) ^ 2 ≠ 0 := by decide
      have hx1 : (2 - (4 : ZMod 47) ^ 2) ^ 2 ≠ 1 := by decide
      have hx2 : (2 - (4 : ZMod 47) ^ 2) ^ 2 ≠ 2 := by decide
      have hx4 : (2 - (4 : ZMod 47) ^ 2) ^ 2 ≠ 4 := by decide
      exact owD3_wit_cr_mu (by norm_num) (by norm_num) Q hQ c hc hA hd 4 hμ hx0 hx1 hx2 hx4
    · have hμ : (3 : ZMod p) ^ 2 ≠ 4 := by
        intro h
        have h9 : (9 : ZMod p) = 4 := by
          rw [show (3 : ZMod p) ^ 2 = 9 by ring] at h
          exact h
        have h5 : (5 : ZMod p) = 0 := by linear_combination h9
        have hdiv : p ∣ 5 := (CharP.cast_eq_zero_iff (ZMod p) p 5).mp h5
        have hle : p ≤ 5 := Nat.le_of_dvd (by norm_num) hdiv
        omega
      have hx0 : 2 - (3 : ZMod p) ^ 2 ≠ 0 := by
        intro h
        have h' : (2 : ZMod p) - 9 = 0 := by
          rw [show (3 : ZMod p) ^ 2 = 9 by ring] at h
          exact h
        have h7 : (7 : ZMod p) = 0 := by linear_combination -h'
        have hdiv : p ∣ 7 := (CharP.cast_eq_zero_iff (ZMod p) p 7).mp h7
        have hle : p ≤ 7 := Nat.le_of_dvd (by norm_num) hdiv
        omega
      have hx1 : (2 - (3 : ZMod p) ^ 2) ^ 2 ≠ 1 := by
        intro h
        have h' : ((2 : ZMod p) - 9) ^ 2 = 1 := by
          rw [show (3 : ZMod p) ^ 2 = 9 by ring] at h
          exact h
        have h48 : (48 : ZMod p) = 0 := by
          have h'' : ((2 : ZMod p) - 9) ^ 2 - 1 = 0 := sub_eq_zero.mpr h'
          have h''' : ((2 : ZMod p) - 9) ^ 2 - 1 = (48 : ZMod p) := by ring
          rw [h'''] at h''
          exact h''
        exact owD3_not_dvd_48 hp h11 ((CharP.cast_eq_zero_iff (ZMod p) p 48).mp h48)
      have hx2 : (2 - (3 : ZMod p) ^ 2) ^ 2 ≠ 2 := by
        intro h
        have h' : ((2 : ZMod p) - 9) ^ 2 = 2 := by
          rw [show (3 : ZMod p) ^ 2 = 9 by ring] at h
          exact h
        have h47 : (47 : ZMod p) = 0 := by
          have h'' : ((2 : ZMod p) - 9) ^ 2 - 2 = 0 := sub_eq_zero.mpr h'
          have h''' : ((2 : ZMod p) - 9) ^ 2 - 2 = (47 : ZMod p) := by ring
          rw [h'''] at h''
          exact h''
        have hdiv : p ∣ 47 := (CharP.cast_eq_zero_iff (ZMod p) p 47).mp h47
        have hle : p ≤ 47 := Nat.le_of_dvd (by norm_num) hdiv
        have hp47' : p = 47 := by
          interval_cases p <;> norm_num at *
        exact hp47 hp47'
      have hx4 : (2 - (3 : ZMod p) ^ 2) ^ 2 ≠ 4 := by
        intro h
        have h' : ((2 : ZMod p) - 9) ^ 2 = 4 := by
          rw [show (3 : ZMod p) ^ 2 = 9 by ring] at h
          exact h
        have h45 : (45 : ZMod p) = 0 := by
          have h'' : ((2 : ZMod p) - 9) ^ 2 - 4 = 0 := sub_eq_zero.mpr h'
          have h''' : ((2 : ZMod p) - 9) ^ 2 - 4 = (45 : ZMod p) := by ring
          rw [h'''] at h''
          exact h''
        exact owD3_not_dvd_45 hp h11 ((CharP.cast_eq_zero_iff (ZMod p) p 45).mp h45)
      exact owD3_wit_cr_mu hp hp2 Q hQ c hc hA hd 3 hμ hx0 hx1 hx2 hx4
  · have hp_eq7 : p = 7 := by
      interval_cases p
      · rfl
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
    subst p
    by_cases hneg : WitNEG3 7 A
    · exact Or.inl hneg
    · right
      intro r hrA hr
      obtain ⟨a, ha, haQ, hrefl⟩ :=
        owD3_refl_form (p := 7) (by norm_num) (by norm_num) Q hQ c hc hA hrA hr
      by_cases hiso : ∃ u : U, u ≠ 0 ∧ Q u = 0 ∧ polarBilin Q u a = 0
      · obtain ⟨u, hu_ne, huQ, huB⟩ := hiso
        exact owD3_wit_cr_of_isotropic (p := 7) (by norm_num) (by norm_num) Q hQ c hc hA
          (by norm_num) haQ ha hrA hrefl hu_ne huQ huB
      · exact absurd ⟨hd, owD3_neg_one_of_anisotropic Q hQ hd c hc hA haQ hiso⟩ hneg

end CFSG.StandardType.ZS

end
