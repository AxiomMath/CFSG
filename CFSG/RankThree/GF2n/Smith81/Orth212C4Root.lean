module

public import CFSG.RankThree.GF2n.Smith81.Orth28Route
public import CFSG.RankThree.GF2n.Smith81.Lin28CondRest

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80

theorem orth212C4_qU_add_smul {K ι : Type} [Field K] (qU : QuadraticForm K (ι → K)) {a b : K}
    {u u' : ι → K} (hqu : qU u = 0) (hqu' : qU u' = 0) :
    qU (a • u + b • u') = a * b * QuadraticMap.polar qU u u' := by
  rw [QuadraticMap.map_add (⇑qU) (a • u) (b • u'), QuadraticMap.map_smul, QuadraticMap.map_smul,
    hqu, hqu', QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
  simp only [smul_zero, zero_add, add_zero, smul_eq_mul, mul_assoc, mul_zero]

theorem orth212C4_pure_pair {K ι : Type} [Field K] (qU : QuadraticForm K (ι → K))
    {c₀ c₁ c₀' c₁' d₀ d₁ : K} {u u' v : ι → K}
    (hc : c₀ ≠ 0 ∨ c₁ ≠ 0) (hc' : c₀' ≠ 0 ∨ c₁' ≠ 0) (hu : u ≠ 0) (hqu : qU u = 0)
    (hqu' : qU u' = 0) (hqv : qU v = 0)
    (h0 : c₀ • u + c₀' • u' = d₀ • v) (h1 : c₁ • u + c₁' • u' = d₁ • v) :
    ∃ (w : ι → K) (s t : K), QuadraticMap.polar qU w u = 0 ∧
      (c₀' • u', c₁' • u') = (c₀ • w + s • u, c₁ • w + t • u) := by
  have hqa : qU (c₀ • u + c₀' • u') = 0 := by
    rw [h0, QuadraticMap.map_smul, hqv, smul_zero]
  have hqb : qU (c₁ • u + c₁' • u') = 0 := by
    rw [h1, QuadraticMap.map_smul, hqv, smul_zero]
  by_cases hδ : c₀ * c₁' - c₁ * c₀' = 0
  · have hδ' : c₀ * c₁' = c₁ * c₀' := sub_eq_zero.mp hδ
    obtain ⟨μ, hμ0, hμ0', hμ1'⟩ : ∃ μ : K, μ ≠ 0 ∧ c₀' = μ * c₀ ∧ c₁' = μ * c₁ := by
      rcases eq_or_ne c₀ 0 with h00 | h00
      · have hc1 : c₁ ≠ 0 := hc.resolve_left (fun h => h h00)
        have hc0' : c₀' = 0 := by
          have h := hδ'
          rw [h00, zero_mul] at h
          exact (mul_eq_zero.mp h.symm).resolve_left hc1
        refine ⟨c₁' / c₁, ?_, by rw [hc0', h00, mul_zero], (div_mul_cancel₀ c₁' hc1).symm⟩
        intro hμ
        have hc1'0 : c₁' = 0 := by
          rcases div_eq_zero_iff.mp hμ with h | h
          · exact h
          · exact absurd h hc1
        exact hc'.elim (fun h => h hc0') (fun h => h hc1'0)
      · have hμc : c₀ * (c₀' / c₀) = c₀' := by field_simp
        refine ⟨c₀' / c₀, ?_, (div_mul_cancel₀ c₀' h00).symm, ?_⟩
        · intro hμ
          have hc0'0 : c₀' = 0 := by
            rcases div_eq_zero_iff.mp hμ with h | h
            · exact h
            · exact absurd h h00
          have hc1'0 : c₁' = 0 := by
            apply mul_left_cancel₀ h00
            rw [hδ', hc0'0, mul_zero, mul_zero]
          exact hc'.elim (fun h => h hc0'0) (fun h => h hc1'0)
        · apply mul_left_cancel₀ h00
          linear_combination hδ' - c₁ * hμc
    have hP : QuadraticMap.polar qU u u' = 0 := by
      have ha := orth212C4_qU_add_smul qU (a := c₀) (b := c₀') hqu hqu'
      have hb := orth212C4_qU_add_smul qU (a := c₁) (b := c₁') hqu hqu'
      rw [hqa] at ha
      rw [hqb] at hb
      rcases hc with h | h
      · have hne : c₀ * c₀' ≠ 0 := mul_ne_zero h (by rw [hμ0']; exact mul_ne_zero hμ0 h)
        exact (mul_eq_zero.mp ha.symm).resolve_left hne
      · have hne : c₁ * c₁' ≠ 0 := mul_ne_zero h (by rw [hμ1']; exact mul_ne_zero hμ0 h)
        exact (mul_eq_zero.mp hb.symm).resolve_left hne
    refine ⟨μ • u', 0, 0, ?_, ?_⟩
    · rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_comm qU u' u, hP, smul_zero]
    · refine Prod.ext ?_ ?_
      · simp only [zero_smul, add_zero, hμ0', smul_smul]
        rw [mul_comm]
      · simp only [zero_smul, add_zero, hμ1', smul_smul]
        rw [mul_comm]
  ·
    obtain ⟨δ, hδdef⟩ : ∃ δ : K, δ = c₀ * c₁' - c₁ * c₀' := ⟨_, rfl⟩
    have hδ0 : δ ≠ 0 := by rw [hδdef]; exact hδ
    have key0 : δ • u = (c₁' * d₀ - c₀' * d₁) • v := by
      rw [hδdef]; linear_combination (norm := module) c₁' • h0 - c₀' • h1
    have key1 : δ • u' = (c₀ * d₁ - c₁ * d₀) • v := by
      rw [hδdef]; linear_combination (norm := module) c₀ • h1 - c₁ • h0
    have hua : u = (δ⁻¹ * (c₁' * d₀ - c₀' * d₁)) • v := by
      calc u = δ⁻¹ • (δ • u) := by rw [smul_smul, inv_mul_cancel₀ hδ0, one_smul]
        _ = (δ⁻¹ * (c₁' * d₀ - c₀' * d₁)) • v := by rw [key0, smul_smul]
    have hu'b : u' = (δ⁻¹ * (c₀ * d₁ - c₁ * d₀)) • v := by
      calc u' = δ⁻¹ • (δ • u') := by rw [smul_smul, inv_mul_cancel₀ hδ0, one_smul]
        _ = (δ⁻¹ * (c₀ * d₁ - c₁ * d₀)) • v := by rw [key1, smul_smul]
    have ha0 : δ⁻¹ * (c₁' * d₀ - c₀' * d₁) ≠ 0 := by
      intro h
      apply hu
      rw [hua, h, zero_smul]
    have hu'u : u' = ((δ⁻¹ * (c₀ * d₁ - c₁ * d₀)) * (δ⁻¹ * (c₁' * d₀ - c₀' * d₁))⁻¹) • u := by
      calc u' = (δ⁻¹ * (c₀ * d₁ - c₁ * d₀)) • v := hu'b
        _ = ((δ⁻¹ * (c₀ * d₁ - c₁ * d₀)) * (δ⁻¹ * (c₁' * d₀ - c₀' * d₁))⁻¹) •
            ((δ⁻¹ * (c₁' * d₀ - c₀' * d₁)) • v) := by
          rw [smul_smul, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
        _ = _ := by rw [← hua]
    refine ⟨0, c₀' * ((δ⁻¹ * (c₀ * d₁ - c₁ * d₀)) * (δ⁻¹ * (c₁' * d₀ - c₀' * d₁))⁻¹),
      c₁' * ((δ⁻¹ * (c₀ * d₁ - c₁ * d₀)) * (δ⁻¹ * (c₁' * d₀ - c₀' * d₁))⁻¹), ?_, ?_⟩
    · exact QuadraticMap.polar_zero_left _ _
    · rw [hu'u]
      simp only [smul_zero, zero_add, smul_smul]

theorem orth212C4Root_of (h24 : Smith24ActStatement)
    (h52 : Smith52ActStatement) : Orth212C4RootStatement := by
  intro G _ _ M Q Z B hc X x hs hroot z' hz' h
  by_contra hz'1
  obtain ⟨v, hv1, hvc, hvQ, hvX⟩ := hroot
  obtain ⟨C⟩ := exists_orthCtx h24 hc
  have H := hc.ctx.hyp
  have h12 := smith_1_12 hs
  obtain ⟨h₀, hh₀⟩ := hs.conj
  have hX' : IsZConjugate Z X := ⟨h₀, hh₀⟩
  have hz₀ : h₀⁻¹ * x * h₀ ∈ Z := mem_conjSubgroup.mp (hh₀ ▸ hs.mem)
  have hz₀1 : h₀⁻¹ * x * h₀ ≠ 1 := by
    intro e
    apply hs.ne_one
    have e' : x = h₀ * (h₀⁻¹ * x * h₀) * h₀⁻¹ := by group
    rw [e', e]
    group
  have hvZ : v ∉ Z := by
    intro hvZ
    have hm : v ∈ Z ⊓ QB X := ⟨hvZ, hvX⟩
    rw [Z_inf_QB_eq_bot hs h12, Subgroup.mem_bot] at hm
    exact hv1 hm
  have hvcl : InZClass Z v := by
    obtain ⟨c, hc'⟩ := isConj_iff.mp hvc
    exact ⟨c * h₀, h₀⁻¹ * x * h₀, hz₀, hz₀1, by rw [← hc']; group⟩
  obtain ⟨A, hA, hAQX⟩ := exists_root_of_mem_module hc.ctx hs ⟨hvQ, hvX⟩ hvZ hvcl
  obtain ⟨g, rfl⟩ := hA
  have hAQ : conjSubgroup g Z ≤ Q := fun y hy => (hAQX hy).1
  have hAX : conjSubgroup g Z ≤ QB X := fun y hy => (hAQX hy).2
  have hAZ : conjSubgroup g Z ≠ Z := (lin29_of_sit hs ⟨g, rfl⟩ hAQ hAX).1
  have hA' : IsZConjugate Z (conjSubgroup g Z) := ⟨g, rfl⟩
  have hXA : X ≤ QB (conjSubgroup g Z) := (IsZConjugate.le_QB_iff H hA' hX').mpr hAX
  have hZA : Z ≤ QB (conjSubgroup g Z) :=
    (IsZConjugate.le_QB_iff H hA' (IsZConjugate.self Z)).mpr (by rw [H.QB_Z]; exact hAQ)
  have hQB : QB (conjSubgroup g Z) = conjSubgroup g Q := QB_conj_eq H g
  have hQBX : ∀ k : G, QB (conjSubgroup k X) = conjSubgroup k (QB X) := by
    intro k
    rw [hh₀, ← conjSubgroup_mul, QB_conj_eq H, QB_conj_eq H, conjSubgroup_mul]
  have hx₁Q : g⁻¹ * x * g ∈ Q := by
    have hm : x ∈ conjSubgroup g Q := by rw [← hQB]; exact hXA hs.mem
    exact mem_conjSubgroup.mp hm
  have hz₁Q : g⁻¹ * z' * g ∈ Q := by
    have hm : z' ∈ conjSubgroup g Q := by rw [← hQB]; exact hZA hz'
    exact mem_conjSubgroup.mp hm
  have hx₁1 : g⁻¹ * x * g ≠ 1 := by
    intro e
    apply hs.ne_one
    have e' : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e', e]
    group
  have hx₁Z : g⁻¹ * x * g ∉ Z := by
    intro hm
    apply hs.notQ
    exact hAQ (mem_conjSubgroup.mpr hm)
  have hz₁Z : g⁻¹ * z' * g ∉ Z := by
    intro hm
    have hmem : z' ∈ Z ⊓ conjSubgroup g Z := ⟨hz', mem_conjSubgroup.mpr hm⟩
    rw [inf_conjSubgroup_eq_bot_of_isTI H.ti hAZ, Subgroup.mem_bot] at hmem
    exact hz'1 hmem
  have hx₁z₁Z : g⁻¹ * x * g * (g⁻¹ * z' * g) ∉ Z := by
    intro hm
    have hxz : x * z' ∈ conjSubgroup g Z := by
      rw [mem_conjSubgroup]
      have e : g⁻¹ * (x * z') * g = g⁻¹ * x * g * (g⁻¹ * z' * g) := by group
      rw [e]
      exact hm
    apply hs.notQ
    have hxzQ : x * z' * z'⁻¹ ∈ Q := Q.mul_mem (hAQ hxz) (Q.inv_mem (H.Z_normal.1 hz'))
    simpa using hxzQ
  obtain ⟨m, -, hm⟩ := Z_isConj H hz' hz'1 hz₀ hz₀1
  have hz'x : IsConj z' x := by
    refine isConj_iff.mpr ⟨h₀ * m, ?_⟩
    calc h₀ * m * z' * (h₀ * m)⁻¹ = h₀ * (m * z' * m⁻¹) * h₀⁻¹ := by group
      _ = h₀ * (h₀⁻¹ * x * h₀) * h₀⁻¹ := by rw [hm]
      _ = x := by group
  have hx₁c : IsConj z' (g⁻¹ * x * g) := hz'x.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  have hz₁c : IsConj z' (g⁻¹ * z' * g) := isConj_iff.mpr ⟨g⁻¹, by group⟩
  have hx₁z₁c : IsConj z' (g⁻¹ * x * g * (g⁻¹ * z' * g)) :=
    (hz'x.trans h).trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  have hp₁ := (C.hF.root z' hz' hz'1 _ hx₁Q hx₁Z).mp hx₁c
  have hp₂ := (C.hF.root z' hz' hz'1 _ hz₁Q hz₁Z).mp hz₁c
  have hp₃ := (C.hF.root z' hz' hz'1 _ (Q.mul_mem hx₁Q hz₁Q) hx₁z₁Z).mp hx₁z₁c
  obtain ⟨c₀, c₁, u, hc01, hu0, hqu, hp₁'⟩ := hp₁
  obtain ⟨c₀', c₁', u', hc'01, hu'0, hqu', hp₂'⟩ := hp₂
  obtain ⟨d₀, d₁, e, hd01, he0, hqe, hp₃'⟩ := hp₃
  have hsum : (d₀ • e, d₁ • e) = (c₀ • u + c₀' • u', c₁ • u + c₁' • u') := by
    rw [← hp₃', C.M₀.π_mul _ hx₁Q _ hz₁Q, map_add, hp₁', hp₂', Prod.mk_add_mk]
  have h0 := (Prod.mk.inj hsum).1.symm
  have h1 := (Prod.mk.inj hsum).2.symm
  obtain ⟨w, s, t, hpol, hpz⟩ := orth212C4_pure_pair C.qU hc01 hc'01 hu0 hqu hqu' hqe h0 h1
  have hX₁C : IsZConjugate Z (conjSubgroup g⁻¹ X) := hX'.conj g⁻¹
  have hX₁Q : conjSubgroup g⁻¹ X ≤ Q := by
    intro y hy
    have h1' : (g⁻¹)⁻¹ * y * g⁻¹ ∈ X := mem_conjSubgroup.mp hy
    have h2' : (g⁻¹)⁻¹ * y * g⁻¹ ∈ conjSubgroup g Q := by
      rw [← hQB]
      exact hXA h1'
    have h3' := mem_conjSubgroup.mp h2'
    have e' : g⁻¹ * ((g⁻¹)⁻¹ * y * g⁻¹) * g = y := by group
    rwa [e'] at h3'
  have hx₁X₁ : g⁻¹ * x * g ∈ conjSubgroup g⁻¹ X := by
    rw [mem_conjSubgroup]
    have e' : (g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e']
    exact hs.mem
  have hX₁Z : conjSubgroup g⁻¹ X ≠ Z := by
    intro e'
    apply hx₁Z
    rw [← e']
    exact hx₁X₁
  obtain ⟨-, hconv⟩ := h52 G M Q Z B hc C.K C.γ C.M₀ C.hD C.ι C.qU C.φ C.hF C.hA
    (conjSubgroup g⁻¹ X) hX₁C hX₁Q hX₁Z c₀ c₁ u hc01 hu0 hqu
    ⟨g⁻¹ * x * g, hx₁X₁, hx₁1, hp₁'⟩
  obtain ⟨y, hyQB, hyφ⟩ := hconv w s t hpol
  have hyz : C.φ (C.M₀.π y) = C.φ (C.M₀.π (g⁻¹ * z' * g)) := by
    rw [hyφ, hp₂', hpz]
  have hπ : C.M₀.π y = C.M₀.π (g⁻¹ * z' * g) := C.φ.injective hyz
  have hyQ : y ∈ Q := hyQB.1
  have hw0 : y⁻¹ * (g⁻¹ * z' * g) ∈ Z := by
    have hmem : y⁻¹ * (g⁻¹ * z' * g) ∈ Q := Q.mul_mem (Q.inv_mem hyQ) hz₁Q
    have e1 := C.M₀.π_mul y hyQ _ hmem
    rw [show y * (y⁻¹ * (g⁻¹ * z' * g)) = g⁻¹ * z' * g by group, ← hπ] at e1
    have e2 : C.M₀.π (y⁻¹ * (g⁻¹ * z' * g)) = 0 := by
      simpa using e1
    exact (C.M₀.π_ker _ hmem).mp e2
  have hyB : y ∈ conjSubgroup g⁻¹ (QB X) := by
    rw [← hQBX g⁻¹]
    exact hyQB.2
  have hgy : g * y * g⁻¹ ∈ QB X := by
    have hm := mem_conjSubgroup.mp hyB
    rwa [inv_inv] at hm
  have hgw : g * (y⁻¹ * (g⁻¹ * z' * g)) * g⁻¹ ∈ QB X := by
    refine hAX (mem_conjSubgroup.mpr ?_)
    have e' : g⁻¹ * (g * (y⁻¹ * (g⁻¹ * z' * g)) * g⁻¹) * g = y⁻¹ * (g⁻¹ * z' * g) := by
      group
    rw [e']
    exact hw0
  have hz'eq : (g * y * g⁻¹) * (g * (y⁻¹ * (g⁻¹ * z' * g)) * g⁻¹) = z' := by group
  have hz'QB : z' ∈ QB X := by
    have hm := (QB X).mul_mem hgy hgw
    rwa [hz'eq] at hm
  have hbot : z' ∈ Z ⊓ QB X := ⟨hz', hz'QB⟩
  rw [Z_inf_QB_eq_bot hs h12, Subgroup.mem_bot] at hbot
  exact hz'1 hbot

end CFSG.RankThree.GF2n.Smith81
