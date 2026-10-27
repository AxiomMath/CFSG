module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Spure
public import CFSG.RankThree.GF2n.Stroth80.Sec5SL

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.exists_comm_form' (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {t : G} (ht : t ∈ LB M Q B)
    (htQ : t ∉ Q) (hnot : ¬ Vt M (LB M Q B) B Z t ≤ QB B) {K : Type} [Field K] [Finite K]
    [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    (hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t)) :
    ∃ F : LinearMap.BilinForm K ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS),
      F.Nondegenerate ∧ F.IsAlt ∧
      (∀ (r : ↥(Rt M (LB M Q B) t)) (S : M₀.E ≃ₗ[K] M₀.E),
        (∀ x ∈ Q, M₀.π ((r : G) * x * (r : G)⁻¹) = S (M₀.π x)) →
        ∀ (w w' : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS))
          (hw : S (w : M₀.E) ∈ imgSub M₀ (Vt M (LB M Q B) B Z t) hS)
          (hw' : S (w' : M₀.E) ∈ imgSub M₀ (Vt M (LB M Q B) B Z t) hS),
          F ⟨S w, hw⟩ ⟨S w', hw'⟩ = F w w') ∧
      (∀ (S : M₀.E ≃ₗ[K] M₀.E), (∀ x ∈ Q, M₀.π (t * x * t⁻¹) = S (M₀.π x)) →
        ∀ (w w' : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) (x : M₀.E),
          S x - x = (w' : M₀.E) → F w w' = M₀.B (w : M₀.E) x) ∧
      (∀ (S : M₀.E ≃ₗ[K] M₀.E), (∀ x ∈ Q, M₀.π (t * x * t⁻¹) = S (M₀.π x)) →
        ∀ w : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS), ∃ x : M₀.E, S x - x = (w : M₀.E)) := by
  classical
  set V := Vt M (LB M Q B) B Z t with hVdef
  obtain ⟨φ₀, hφπ, -, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  have htM : t ∈ M := hc.LB_le_M ht
  have htH : t ∈ H0 M Z := hc.LB_le_H0 ht
  obtain ⟨htQ1, htQ2⟩ := hc.conj_mem_Q_of_mem_M htM
  set τ : M₀.E ≃ₗ[K] M₀.E := φ₀ ⟨t, htH⟩ with hτdef
  have hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x) := fun x hx => hφπ ⟨t, htH⟩ x hx
  have hτiso : ∀ e, M₀.Qf (τ e) = M₀.Qf e := hφiso ⟨t, htH⟩
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  obtain ⟨hVU, -⟩ := hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB h35 ht htQ hnot
  have hmemV : ∀ e : M₀.E, e ∈ imgSub M₀ V hS ↔
      e ∈ LinearMap.range ((τ : M₀.E →ₗ[K] M₀.E) - 1) := by
    intro e
    have hVU' : V = Ut Q Z t := hVU
    rw [mem_imgSub, hVU']
    exact mem_img_comm_zpowers_sup_iff M₀ h.reg τ htQ1 htQ2 hτπ e
  have hQ0 : ∀ e ∈ imgSub M₀ V hS, M₀.Qf e = 0 := fun e he =>
    (M₀.isElemAbelian_iff h.reg hVQ).mp (hc.Vt_isElemAbelian h35 ht htQ) e (mem_imgSub.mp he)
  let Vs : Submodule K M₀.E := imgSub M₀ V hS
  let Tm : M₀.E →ₗ[K] M₀.E := (τ : M₀.E →ₗ[K] M₀.E) - 1
  have hTmV : ∀ e, Tm e ∈ Vs := fun e => (hmemV _).mpr ⟨e, rfl⟩
  let Tm' : M₀.E →ₗ[K] Vs := Tm.codRestrict Vs hTmV
  have hTm'e : ∀ e, ((Tm' e : Vs) : M₀.E) = τ e - e := fun e => by
    simp [Tm', Tm]
  have hTm'surj : LinearMap.range Tm' = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro w
    obtain ⟨e, he⟩ := (hmemV w).mp w.2
    refine ⟨e, Subtype.ext ?_⟩
    rw [hTm'e]
    simpa [Tm] using he
  obtain ⟨s, hs⟩ := Tm'.exists_rightInverse_of_surjective hTm'surj
  have hsec : ∀ w : Vs, τ (s w) - s w = (w : M₀.E) := by
    intro w
    have h1 := congrArg (fun f : Vs →ₗ[K] Vs => ((f w : Vs) : M₀.E)) hs
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [← hTm'e]
    exact h1
  let F : LinearMap.BilinForm K Vs := M₀.B.compl₁₂ Vs.subtype s
  have hF : ∀ w w' : Vs, F w w' = M₀.B (w : M₀.E) (s w') := fun w w' => rfl
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hBker : ∀ w ∈ Vs, ∀ z : M₀.E, τ z = z → M₀.B w z = 0 := by
    intro w hw z hz
    obtain ⟨x, hx⟩ := (hmemV w).mp hw
    have hx' : τ x - x = w := by simpa [Tm] using hx
    rw [← hx', map_sub, LinearMap.sub_apply]
    have h1 := Tim79.QuadModel.B_iso (T := (τ : M₀.E →ₗ[K] M₀.E)) hτiso x z
    simp only [LinearEquiv.coe_coe] at h1
    rw [hz] at h1
    rw [h1, sub_self]
  have hAlt : F.IsAlt := by
    intro w
    rw [hF]
    set x := s w with hxdef
    have hw' : (w : M₀.E) = τ x - x := (hsec w).symm
    have hQw : M₀.Qf (w : M₀.E) = 0 := hQ0 w w.2
    have hxx : x + x = 0 := by rw [← two_smul K x, h2K, zero_smul]
    have hwx : (w : M₀.E) = τ x + x := by
      rw [hw', sub_eq_add_neg, neg_eq_of_add_eq_zero_right hxx]
    have h3 := M₀.Qf_add (τ x) x
    rw [← hwx, hQw, hτiso x] at h3
    have h5 : M₀.Qf x + M₀.Qf x = 0 := by rw [← two_mul, h2K, zero_mul]
    have h4 : M₀.B (τ x) x = 0 := by linear_combination (-1 : K) * h3 - h5
    rw [hw', map_sub, LinearMap.sub_apply, h4, M₀.alt, sub_zero]
  have hLeft : ∀ w : Vs, (∀ w' : Vs, F w w' = 0) → w = 0 := by
    intro w hw
    apply Subtype.ext
    refine M₀.nondeg _ fun e => ?_
    set w'' : Vs := Tm' e with hw''
    have hz : τ (e - s w'') = e - s w'' := by
      have h1 := hsec w''
      have h2 : τ e - e = (w'' : M₀.E) := hTm'e e
      rw [map_sub]
      have h3 := h2.trans h1.symm
      calc τ e - τ (s w'') = (τ e - e) - (τ (s w'') - s w'') + (e - s w'') := by abel
        _ = e - s w'' := by rw [h3, sub_self, zero_add]
    have hsplit : M₀.B (w : M₀.E) e =
        M₀.B (w : M₀.E) (s w'') + M₀.B (w : M₀.E) (e - s w'') := by
      rw [← map_add]
      congr 1
      abel
    rw [hsplit, show M₀.B (w : M₀.E) (s w'') = 0 from hw w'', hBker w w.2 _ hz, add_zero]
  have hND : F.Nondegenerate := by
    refine ⟨hLeft, fun w hw => hLeft w fun w' => ?_⟩
    have h1 := hw w'
    have h2 : F w' w = - F w w' := by
      have h3 := hAlt (w + w')
      simp only [map_add, LinearMap.add_apply, hAlt w, hAlt w', zero_add, add_zero] at h3
      exact eq_neg_of_add_eq_zero_left h3
    rw [← neg_eq_zero, ← h2]
    exact h1
  refine ⟨F, hND, hAlt, ?_, ?_, ?_⟩
  · intro r S hS' w w' hw hw'
    have hrH : (r : G) ∈ H0 M Z := hc.Rt_le_H0 t r.2
    have hSφ : ∀ e, S e = φ₀ ⟨r, hrH⟩ e := by
      intro e
      obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
      rw [← hS' x hxQ, hφπ ⟨r, hrH⟩ x hxQ]
    have hSiso : ∀ e, M₀.Qf (S e) = M₀.Qf e := by
      intro e
      rw [hSφ]
      exact hφiso ⟨r, hrH⟩ e
    have hcomm : ∀ e, S (τ e) = τ (S e) := fun e =>
      hc.hyp.comm_action (M := M) (hc.Rt_le_M t r.2) htM (hc.Rt_comm_mem_Q r.2) hS' hτπ e
    have hker : τ (S (s w') - s ⟨S w', hw'⟩) = S (s w') - s ⟨S w', hw'⟩ := by
      have h1 := hsec ⟨S w', hw'⟩
      have h2 := hsec w'
      rw [map_sub, ← hcomm]
      have h3 : S (τ (s w') - s w') = S w' := by rw [h2]
      rw [map_sub] at h3
      calc S (τ (s w')) - τ (s ⟨S w', hw'⟩) =
          (S (τ (s w')) - S (s w')) - (τ (s ⟨S w', hw'⟩) - s ⟨S w', hw'⟩) +
            (S (s w') - s ⟨S w', hw'⟩) := by abel
        _ = S (s w') - s ⟨S w', hw'⟩ := by rw [h3, h1, sub_self, zero_add]
    rw [hF, hF]
    have h4 := hBker _ hw _ hker
    have h5 : M₀.B (S (w : M₀.E)) (S (s w')) = M₀.B (w : M₀.E) (s w') := by
      have := Tim79.QuadModel.B_iso (T := (S : M₀.E →ₗ[K] M₀.E)) hSiso (w : M₀.E) (s w')
      simpa using this
    rw [map_sub] at h4
    show M₀.B (S (w : M₀.E)) (s ⟨S w', hw'⟩) = _
    rw [← h5]
    have h6 : M₀.B (S (w : M₀.E)) (s ⟨S w', hw'⟩) = M₀.B (S (w : M₀.E)) (S (s w')) := by
      linear_combination (-1 : K) * h4
    exact h6
  · intro S hS' w w' x hx
    have hSτ : ∀ e, S e = τ e := by
      intro e
      obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
      rw [← hS' y hyQ, hτπ y hyQ]
    have hz : τ (x - s w') = x - s w' := by
      have h1 := hsec w'
      have h2 : τ x - x = (w' : M₀.E) := by rw [← hSτ x]; exact hx
      rw [map_sub]
      calc τ x - τ (s w') = (τ x - x) - (τ (s w') - s w') + (x - s w') := by abel
        _ = x - s w' := by rw [h2, h1, sub_self, zero_add]
    have h3 := hBker (w : M₀.E) w.2 _ hz
    rw [hF]
    rw [map_sub] at h3
    linear_combination (-1 : K) * h3
  · intro S hS' w
    have hSτ : ∀ e, S e = τ e := by
      intro e
      obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
      rw [← hS' y hyQ, hτπ y hyQ]
    obtain ⟨x, hx⟩ := (hmemV (w : M₀.E)).mp w.2
    refine ⟨x, ?_⟩
    rw [hSτ x]
    simpa [LinearMap.sub_apply] using hx


end CFSG.RankThree.GF2n.Stroth80
