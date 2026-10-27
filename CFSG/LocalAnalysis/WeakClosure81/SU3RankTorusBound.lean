module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit
import CFSG.CGT.Foote82.Lemma62Tools

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic

private theorem fixSub_sup {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (A B : Subgroup (LGL 2 V)) : fixSub (A ⊔ B) = fixSub A ⊓ fixSub B := by
  refine le_antisymm (le_inf (fixSub_anti A (A ⊔ B) le_sup_left)
    (fixSub_anti B (A ⊔ B) le_sup_right)) ?_
  intro v hv
  rw [Submodule.mem_inf] at hv
  have hvA : ∀ a ∈ A, a v = v := hv.1
  have hvB : ∀ b ∈ B, b v = v := hv.2
  rw [mem_fixSub]
  intro g hg
  let K : Subgroup (LGL 2 V) :=
    { carrier := {a | a v = v}
      one_mem' := rfl
      mul_mem' := fun {a b} ha hb => by
        change a (b v) = v
        rw [hb, ha]
      inv_mem' := fun {a} ha => by
        change a⁻¹ v = v
        exact (congrArg (fun w => a⁻¹ w) ha).symm.trans (a.symm_apply_apply v) }
  have hK : A ⊔ B ≤ K := sup_le (fun a ha => hvA a ha) (fun b hb => hvB b hb)
  exact hK hg

private theorem zpowers_conj {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (g b : LGL 2 V) :
    Subgroup.zpowers (g * b * g⁻¹) = cj g (Subgroup.zpowers b) := by
  have h1 : Subgroup.zpowers (g * b * g⁻¹) = Subgroup.closure {g * b * g⁻¹} :=
    Subgroup.zpowers_eq_closure _
  have h2 : Subgroup.zpowers b = Subgroup.closure {b} := Subgroup.zpowers_eq_closure b
  rw [h1, h2, cj, MonoidHom.map_closure]
  congr 1
  ext a
  simp only [Set.mem_singleton_iff, Set.mem_image]
  constructor
  · rintro rfl
    exact ⟨b, rfl, MulAut.conj_apply g b⟩
  · rintro ⟨c, rfl, hc⟩
    change g * c * g⁻¹ = a at hc
    exact hc.symm

private theorem conj_mem_V {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {E : Subgroup (LGL 2 V)} {g b : LGL 2 V}
    (hg : g ∈ Subgroup.normalizer (E : Set (LGL 2 V))) {w : V}
    (hw : w ∈ fixSub (Subgroup.zpowers b) ⊓ commSub E) :
    g w ∈ fixSub (cj g (Subgroup.zpowers b)) ⊓ commSub E := by
  refine ⟨?_, map_mem_commSub_of_mem_normalizer E hg hw.2⟩
  have h : g w ∈ (fixSub (Subgroup.zpowers b)).map (g : V →ₗ[ZMod 2] V) :=
    Submodule.mem_map.mpr ⟨w, hw.1, rfl⟩
  rw [fixSub_cj]
  exact h

theorem two_mul_le_finrank_range_sub_of_conj {F : Type} [AddCommGroup F] [Module (ZMod 2) F]
    [Finite F] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {E : Subgroup (LGL 2 F)}
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ e ∈ E, e ^ ℓ = 1)
    (hcard : Nat.card E = ℓ ^ 2) {y c : LGL 2 F} (hyE : y ∈ E) (hy1 : y ≠ 1)
    (hcE : ∀ e ∈ E, c * e * c⁻¹ ∈ E) (hcE' : ∀ e ∈ E, c⁻¹ * e * c ∈ E)
    (h1 : Subgroup.zpowers (c * y * c⁻¹) ≠ Subgroup.zpowers y)
    (h2 : Subgroup.zpowers (c⁻¹ * y * c) ≠ Subgroup.zpowers y)
    (h3 : Subgroup.zpowers (c * y * c⁻¹) ≠ Subgroup.zpowers (c⁻¹ * y * c)) {d : ℕ}
    (hd : ∀ B : Subgroup (LGL 2 F), B ≤ E → Nat.card B = ℓ → fixSub B ⊓ commSub E ≠ ⊥ →
      d ≤ Module.finrank (ZMod 2) ↥(fixSub B ⊓ commSub E)) :
    2 * d ≤ Module.finrank (ZMod 2) (LinearMap.range ((y : F →ₗ[ZMod 2] F) - LinearMap.id)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : FiniteDimensional (ZMod 2) F := Module.Finite.of_finite
  have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have h2ℓ : 2 ≤ ℓ := hℓ.two_le
  have hcardE_odd : Odd (Nat.card E) := by
    rw [hcard]
    exact hℓodd.pow
  have hcompl : IsCompl (fixSub E) (commSub E) :=
    isCompl_fixSub_commSub (Q := E) (Nat.coprime_two_left.mpr hcardE_odd)
  have hmod : ∀ B : Subgroup (LGL 2 F), B ≤ E →
      fixSub B = fixSub E ⊔ (fixSub B ⊓ commSub E) := by
    intro B hBE
    have hFE : fixSub E ≤ fixSub B := fixSub_anti B E hBE
    calc fixSub B = fixSub B ⊓ ⊤ := (inf_top_eq _).symm
      _ = fixSub B ⊓ (fixSub E ⊔ commSub E) := by rw [hcompl.sup_eq_top]
      _ = (fixSub E ⊔ commSub E) ⊓ fixSub B := inf_comm _ _
      _ = fixSub E ⊔ commSub E ⊓ fixSub B := sup_inf_assoc_of_le (commSub E) hFE
      _ = fixSub E ⊔ (fixSub B ⊓ commSub E) := by rw [inf_comm]
  have hVbot : ∀ B : Subgroup (LGL 2 F), B ≤ E →
      (fixSub B ⊓ commSub E = ⊥ ↔ fixSub B = fixSub E) := by
    intro B hBE
    constructor
    · intro h
      rw [hmod B hBE, h, sup_bot_eq]
    · intro h
      rw [eq_bot_iff]
      calc fixSub B ⊓ commSub E ≤ fixSub E ⊓ commSub E := by
            refine le_inf ?_ inf_le_right
            rw [h]
            exact inf_le_left
        _ = ⊥ := hcompl.inf_eq_bot
  have hsup_eq_E : ∀ B C : Subgroup (LGL 2 F), B ≤ E → C ≤ E → Nat.card B = ℓ →
      Nat.card C = ℓ → B ≠ C → B ⊔ C = E := by
    intro B C hBE hCE hBc hCc hne
    have hle : B ⊔ C ≤ E := sup_le hBE hCE
    have hne' : C ≠ B ⊔ C := by
      intro h
      exact hne (Subgroup.eq_of_le_of_card_ge (h.symm ▸ le_sup_left) (by rw [hCc, hBc]))
    have hstrict : Nat.card C < Nat.card ↥(B ⊔ C) := by
      rw [lt_iff_not_ge]
      intro hle
      exact hne' (Subgroup.eq_of_le_of_card_ge le_sup_right hle)
    have hdvd : Nat.card (B ⊔ C : Subgroup (LGL 2 F)) ∣ ℓ ^ 2 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hle
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hℓ).mp hdvd
    have hlt : ℓ < ℓ ^ k := by
      rw [← hk, ← hCc]
      exact hstrict
    have hk_eq : k = 2 := by
      interval_cases k
      · simp at hlt; omega
      · simp at hlt
      · rfl
    have hsupcard : Nat.card (B ⊔ C : Subgroup (LGL 2 F)) = ℓ ^ 2 := by
      rw [hk, hk_eq]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hsupcard])
  have htwo : ∃ B1 B2 : Subgroup (LGL 2 F),
      B1 ≤ E ∧ Nat.card B1 = ℓ ∧ B2 ≤ E ∧ Nat.card B2 = ℓ ∧ B1 ≠ B2 ∧
      fixSub B1 ⊓ commSub E ≠ ⊥ ∧ fixSub B2 ⊓ commSub E ≠ ⊥ := by
    by_contra hcon
    have huniq : ∀ B1 B2 : Subgroup (LGL 2 F), B1 ≤ E → Nat.card B1 = ℓ →
        B2 ≤ E → Nat.card B2 = ℓ → fixSub B1 ⊓ commSub E ≠ ⊥ →
        fixSub B2 ⊓ commSub E ≠ ⊥ → B1 = B2 := by
      intro B1 B2 h1 h2 h3 h4 hn1 hn2
      by_contra hne
      exact hcon ⟨B1, B2, h1, h2, h3, h4, hne, hn1, hn2⟩
    have hsup : (⨆ (B : Subgroup (LGL 2 F)) (_ : B ≤ E) (_ : Nat.card B = ℓ),
        fixSub B) = ⊤ :=
      CFSG.CGT.Foote82.iSup_fixedSpace_eq_top (V := F) hℓ hℓ2 hcomm hexp hcard
    by_cases hS : ∃ B : Subgroup (LGL 2 F), B ≤ E ∧ Nat.card B = ℓ ∧
        fixSub B ⊓ commSub E ≠ ⊥
    · obtain ⟨B0, hB0E, hB0c, hB0V⟩ := hS
      have hle : (⨆ (B : Subgroup (LGL 2 F)) (_ : B ≤ E) (_ : Nat.card B = ℓ),
          fixSub B) ≤ fixSub B0 := by
        refine iSup_le fun B => ?_
        refine iSup_le fun hBE => ?_
        refine iSup_le fun hBc => ?_
        by_cases hVb : fixSub B ⊓ commSub E = ⊥
        · rw [(hVbot B hBE).mp hVb]
          exact fixSub_anti B0 E hB0E
        · rw [huniq B B0 hBE hBc hB0E hB0c hVb hB0V]
      have htop : fixSub B0 = ⊤ :=
        le_antisymm le_top (by rw [← hsup]; exact hle)
      have hbot : B0 = ⊥ := (fixSub_eq_top_iff B0).mp htop
      rw [hbot] at hB0c
      rw [Subgroup.card_bot] at hB0c
      omega
    · have hle : (⨆ (B : Subgroup (LGL 2 F)) (_ : B ≤ E) (_ : Nat.card B = ℓ),
          fixSub B) ≤ fixSub E := by
        refine iSup_le fun B => ?_
        refine iSup_le fun hBE => ?_
        refine iSup_le fun hBc => ?_
        have hVb : fixSub B ⊓ commSub E = ⊥ := by
          by_contra hVb
          exact hS ⟨B, hBE, hBc, hVb⟩
        rw [(hVbot B hBE).mp hVb]
      have htop : fixSub E = ⊤ :=
        le_antisymm le_top (by rw [← hsup]; exact hle)
      have hbot : E = ⊥ := (fixSub_eq_top_iff E).mp htop
      rw [hbot] at hcard
      rw [Subgroup.card_bot] at hcard
      nlinarith [h2ℓ]
  obtain ⟨B1, B2, hB1E, hB1c, hB2E, hB2c, hB1ne, hV1, hV2⟩ := htwo
  have hcNorm : c ∈ Subgroup.normalizer (E : Set (LGL 2 F)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm ?_ ?_
    · rintro x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
      simpa [MulAut.conj_apply] using hcE e he
    · intro e he
      exact Subgroup.mem_map.mpr ⟨c⁻¹ * e * c, hcE' e he, by
        show c * (c⁻¹ * e * c) * c⁻¹ = e
        group⟩
  have hcNorm' : c⁻¹ ∈ Subgroup.normalizer (E : Set (LGL 2 F)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm ?_ ?_
    · rintro x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
      simpa [MulAut.conj_apply] using hcE' e he
    · intro e he
      exact Subgroup.mem_map.mpr ⟨c * e * c⁻¹, hcE e he, by
        show c⁻¹ * (c * e * c⁻¹) * c = e
        group⟩
  have hy_ord : orderOf y = ℓ := by
    have hdvd : orderOf y ∣ ℓ := orderOf_dvd_iff_pow_eq_one.mpr (hexp y hyE)
    rcases hℓ.eq_one_or_self_of_dvd (orderOf y) hdvd with h | h
    · exact absurd ((orderOf_eq_one_iff).mp h) hy1
    · exact h
  have hYcard : Nat.card (Subgroup.zpowers y) = ℓ := by
    rw [Nat.card_zpowers, hy_ord]
  have hYE : Subgroup.zpowers y ≤ E := Subgroup.zpowers_le.mpr hyE
  have hB1card : Nat.card (Subgroup.zpowers (c * y * c⁻¹)) = ℓ := by
    rw [zpowers_conj, card_cj, hYcard]
  have hB2card : Nat.card (Subgroup.zpowers (c⁻¹ * y * c)) = ℓ := by
    rw [show c⁻¹ * y * c = c⁻¹ * y * (c⁻¹)⁻¹ by group]
    rw [zpowers_conj, card_cj, hYcard]
  have htwo' : ∃ B1 B2 : Subgroup (LGL 2 F),
      B1 ≤ E ∧ Nat.card B1 = ℓ ∧ B2 ≤ E ∧ Nat.card B2 = ℓ ∧ B1 ≠ B2 ∧
      B1 ≠ Subgroup.zpowers y ∧ B2 ≠ Subgroup.zpowers y ∧
      fixSub B1 ⊓ commSub E ≠ ⊥ ∧ fixSub B2 ⊓ commSub E ≠ ⊥ := by
    by_cases hYV : fixSub (Subgroup.zpowers y) ⊓ commSub E = ⊥
    · refine ⟨B1, B2, hB1E, hB1c, hB2E, hB2c, hB1ne, ?_, ?_, hV1, hV2⟩
      · intro h
        exact hV1 (by rw [h]; exact hYV)
      · intro h
        exact hV2 (by rw [h]; exact hYV)
    · have hB1V : fixSub (Subgroup.zpowers (c * y * c⁻¹)) ⊓ commSub E ≠ ⊥ := by
        intro hbot
        obtain ⟨w, hw, hw0⟩ :=
          Submodule.exists_mem_ne_zero_of_ne_bot
            (p := fixSub (Subgroup.zpowers y) ⊓ commSub E) hYV
        have hcw := conj_mem_V hcNorm hw
        rw [← zpowers_conj c y] at hcw
        rw [hbot] at hcw
        rw [Submodule.mem_bot] at hcw
        exact hw0 (c.injective (by rw [hcw, map_zero]))
      have hB2V : fixSub (Subgroup.zpowers (c⁻¹ * y * c)) ⊓ commSub E ≠ ⊥ := by
        intro hbot
        obtain ⟨w, hw, hw0⟩ :=
          Submodule.exists_mem_ne_zero_of_ne_bot
            (p := fixSub (Subgroup.zpowers y) ⊓ commSub E) hYV
        have hcw := conj_mem_V hcNorm' hw
        rw [← zpowers_conj c⁻¹ y] at hcw
        rw [show c⁻¹ * y * (c⁻¹)⁻¹ = c⁻¹ * y * c by group] at hcw
        rw [hbot] at hcw
        rw [Submodule.mem_bot] at hcw
        exact hw0 ((c⁻¹).injective (by rw [hcw, map_zero]))
      exact ⟨Subgroup.zpowers (c * y * c⁻¹), Subgroup.zpowers (c⁻¹ * y * c),
        Subgroup.zpowers_le.mpr (hcE y hyE), hB1card, Subgroup.zpowers_le.mpr (hcE' y hyE),
        hB2card, h3, h1, h2, hB1V, hB2V⟩
  obtain ⟨B1, B2, hB1E, hB1c, hB2E, hB2c, hB1ne, hB1Y, hB2Y, hV1, hV2⟩ := htwo'
  have hsup12 : B1 ⊔ B2 = E := hsup_eq_E B1 B2 hB1E hB2E hB1c hB2c hB1ne
  let T : F →ₗ[ZMod 2] F := (y : F →ₗ[ZMod 2] F) - LinearMap.id
  have hle_range : ∀ B : Subgroup (LGL 2 F), B ≤ E → Nat.card B = ℓ →
      B ≠ Subgroup.zpowers y → fixSub B ⊓ commSub E ≠ ⊥ →
      fixSub B ⊓ commSub E ≤ LinearMap.range T := by
    intro B hBE hBc hBY _
    have hyNormB : y ∈ Subgroup.normalizer (B : Set (LGL 2 F)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have hhE : h ∈ E := hBE hh
        have h' : y * h * y⁻¹ = h := by
          rw [hcomm y hyE h hhE]
          group
        rw [h']
        exact hh
      · intro hh
        have hhE : y * h * y⁻¹ ∈ E := hBE hh
        have hE : h ∈ E := by
          have h' : h = y⁻¹ * (y * h * y⁻¹) * y := by group
          rw [h']
          exact E.mul_mem (E.mul_mem (E.inv_mem hyE) hhE) hyE
        have h' : y * h * y⁻¹ = h := by
          rw [hcomm y hyE h hE]
          group
        rwa [h'] at hh
    have hyNormE : y ∈ Subgroup.normalizer (E : Set (LGL 2 F)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have h' : y * h * y⁻¹ = h := by
          rw [hcomm y hyE h hh]
          group
        rw [h']
        exact hh
      · intro hh
        have h' : h = y⁻¹ * (y * h * y⁻¹) * y := by group
        rw [h']
        exact E.mul_mem (E.mul_mem (E.inv_mem hyE) hh) hyE
    have hyV : ∀ v ∈ fixSub B ⊓ commSub E, y v ∈ fixSub B ⊓ commSub E := fun v hv =>
      ⟨map_mem_fixSub_of_mem_normalizer B hyNormB hv.1,
        map_mem_commSub_of_mem_normalizer E hyNormE hv.2⟩
    have hfixfree : ∀ u ∈ fixSub B ⊓ commSub E, T u = 0 → u = 0 := by
      intro u hu hT
      let K : Subgroup (LGL 2 F) :=
        { carrier := {a | a u = u}
          one_mem' := rfl
          mul_mem' := fun {a b} ha hb => by
            change a (b u) = u
            rw [hb, ha]
          inv_mem' := fun {a} ha => by
            change a⁻¹ u = u
            exact (congrArg (fun w => a⁻¹ w) ha).symm.trans (a.symm_apply_apply u) }
      have hyK : y ∈ K := by
        have h' : T u = 0 := hT
        rw [show T = ((y : F →ₗ[ZMod 2] F) - LinearMap.id) from rfl,
          LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h'
        exact h'
      have hBK : B ≤ K := fun b hb => hu.1 b hb
      have hsupK : B ⊔ Subgroup.zpowers y ≤ K :=
        sup_le hBK (Subgroup.zpowers_le.mpr hyK)
      have hBY' : B ⊔ Subgroup.zpowers y = E :=
        hsup_eq_E B (Subgroup.zpowers y) hBE hYE hBc hYcard hBY
      have hEK : E ≤ K := hBY' ▸ hsupK
      have huE : u ∈ fixSub E := fun a ha => hEK ha
      have hmem : u ∈ fixSub E ⊓ commSub E := ⟨huE, hu.2⟩
      rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hmem
      exact hmem
    have hyT : ∀ v ∈ fixSub B ⊓ commSub E, T v ∈ fixSub B ⊓ commSub E := by
      intro v hv
      have hTv : T v = y v - v := by simp [T]
      rw [hTv]
      exact Submodule.sub_mem _ (hyV v hv) hv
    let T' : ↥(fixSub B ⊓ commSub E) →ₗ[ZMod 2] ↥(fixSub B ⊓ commSub E) := T.restrict hyT
    have hTinj : Function.Injective T' := by
      intro u v huv
      have h : T ((u : F) - (v : F)) = 0 := by
        have h2 : T (u : F) = T (v : F) := by
          have := congrArg Subtype.val huv
          simpa only [T', LinearMap.restrict_apply, Submodule.coe_mk] using this
        rw [map_sub, h2, sub_self]
      have hmem : (u : F) - (v : F) ∈ fixSub B ⊓ commSub E := Submodule.sub_mem _ u.2 v.2
      have hzero : (u : F) - (v : F) = 0 := hfixfree _ hmem h
      exact Subtype.ext (sub_eq_zero.mp hzero)
    have hTsurj : Function.Surjective T' := LinearMap.injective_iff_surjective.mp hTinj
    intro w hw
    obtain ⟨v, hv⟩ := hTsurj ⟨w, hw⟩
    refine ⟨(v : F), ?_⟩
    have h := congrArg Subtype.val hv
    simpa only [T', LinearMap.restrict_apply, Submodule.coe_mk] using h
  have hle1 : fixSub B1 ⊓ commSub E ≤ LinearMap.range T := hle_range B1 hB1E hB1c hB1Y hV1
  have hle2 : fixSub B2 ⊓ commSub E ≤ LinearMap.range T := hle_range B2 hB2E hB2c hB2Y hV2
  have hsup_le : (fixSub B1 ⊓ commSub E) ⊔ (fixSub B2 ⊓ commSub E) ≤ LinearMap.range T :=
    sup_le hle1 hle2
  have hinf_le_fix : (fixSub B1 ⊓ commSub E) ⊓ (fixSub B2 ⊓ commSub E) ≤ fixSub E := by
    have hsub : (fixSub B1 ⊓ commSub E) ⊓ (fixSub B2 ⊓ commSub E) ≤
        fixSub B1 ⊓ fixSub B2 := by
      refine le_inf ?_ ?_
      · exact inf_le_left.trans inf_le_left
      · exact inf_le_right.trans inf_le_left
    rw [← fixSub_sup B1 B2, hsup12] at hsub
    exact hsub
  have hinf_le_comm : (fixSub B1 ⊓ commSub E) ⊓ (fixSub B2 ⊓ commSub E) ≤ commSub E :=
    inf_le_left.trans inf_le_right
  have hinf_bot : (fixSub B1 ⊓ commSub E) ⊓ (fixSub B2 ⊓ commSub E) = ⊥ := by
    have hle : (fixSub B1 ⊓ commSub E) ⊓ (fixSub B2 ⊓ commSub E) ≤
        fixSub E ⊓ commSub E := le_inf hinf_le_fix hinf_le_comm
    rw [hcompl.inf_eq_bot] at hle
    exact le_bot_iff.mp hle
  have hfinrank_eq : Module.finrank (ZMod 2)
        ↥((fixSub B1 ⊓ commSub E) ⊔ (fixSub B2 ⊓ commSub E))
      = Module.finrank (ZMod 2) ↥(fixSub B1 ⊓ commSub E)
        + Module.finrank (ZMod 2) ↥(fixSub B2 ⊓ commSub E) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (fixSub B1 ⊓ commSub E)
      (fixSub B2 ⊓ commSub E)
    rw [hinf_bot, finrank_bot, add_zero] at h
    exact h
  have hd1 : d ≤ Module.finrank (ZMod 2) ↥(fixSub B1 ⊓ commSub E) := hd B1 hB1E hB1c hV1
  have hd2 : d ≤ Module.finrank (ZMod 2) ↥(fixSub B2 ⊓ commSub E) := hd B2 hB2E hB2c hV2
  have hfin_le : Module.finrank (ZMod 2)
        ↥((fixSub B1 ⊓ commSub E) ⊔ (fixSub B2 ⊓ commSub E)) ≤
      Module.finrank (ZMod 2) (LinearMap.range T) :=
    Submodule.finrank_mono hsup_le
  calc 2 * d ≤ Module.finrank (ZMod 2) ↥(fixSub B1 ⊓ commSub E)
        + Module.finrank (ZMod 2) ↥(fixSub B2 ⊓ commSub E) := by omega
    _ = Module.finrank (ZMod 2)
        ↥((fixSub B1 ⊓ commSub E) ⊔ (fixSub B2 ⊓ commSub E)) := hfinrank_eq.symm
    _ ≤ Module.finrank (ZMod 2) (LinearMap.range T) := hfin_le

end CFSG.LocalAnalysis.WeakClosure81

end
