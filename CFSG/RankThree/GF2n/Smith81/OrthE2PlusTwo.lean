module

public import CFSG.RankThree.GF2n.Smith81.OrthSL2Cube
public import CFSG.RankThree.GF2n.Smith81.OrthE2MinusTwo
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClOmegaPlusFour
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalarsPlusTwo

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 QuadraticMap
open CFSG.ClassicalGroups.Orthogonal (eichler toLinEquiv)
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

section Natural

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem orth_natural_card (hc : Ctx M Q Z B) {t : G}
    (hNtCN : hc.CN t = Nt M (LB M Q B) t) {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {X : Subgroup (GL ι K)}
    (hnat : NaturalRep K X (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t)) :
    Nat.card ↥(Rt M (LB M Q B) t) = Nat.card ↥X * Nat.card ↥(Nt M (LB M Q B) t) := by
  obtain ⟨φ, hφr, hφk, -⟩ := hnat
  have h1 := orth_card_eq_ker_mul_range φ
  rw [hφr, hφk, hNtCN] at h1
  have h2 : Nat.card ↥((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)) =
      Nat.card ↥(Nt M (LB M Q B) t) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (orth_Nt_le_Rt M (LB M Q B) t)).toEquiv
  rw [h2] at h1
  rw [h1, mul_comm]

theorem orth_not_pgroup_omegaPlus_four {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) : ¬ IsPGroup 2 ↥(StatedOmega (StatedQuadPlus 2 K)) := by
  intro h
  obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K hK
  have h1 : IsPGroup 2 (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) := h.of_equiv e
  exact orth_not_pgroup_statedSL hK
    (h1.of_injective (MonoidHom.inl _ _) (fun a b hab => (Prod.ext_iff.mp hab).1))

theorem orth_e2Natural_plus_two (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hc : Ctx M Q Z B) {t : G} (hs : Sec5Hyp hc 4 t) (hNtCN : hc.CN t = Nt M (LB M Q B) t)
    {KE : Type} [Field KE] [Finite KE] [CharP KE 2] (hKE : Nat.card KE = Nat.card Z)
    (hRN : Nat.card ↥(Rt M (LB M Q B) t) =
      Nat.card ↥(StatedOmega (StatedQuadPlus 2 KE)) * Nat.card ↥(Nt M (LB M Q B) t)) :
    OmegaPlusNat hc t 2 := by
  classical
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  have hq4 : 4 ≤ Nat.card KE := by rw [hKE]; exact hc.hyp.q4
  have hqZ : Even (Nat.card Z : ℤ) := by
    rw [← hKE]; exact orth_even_card_int KE
  have hq0 : (Nat.card Z : ℤ) ≠ 0 := by have := hc.hyp.q4; omega
  obtain ⟨XE, hXE, hYE⟩ := orth_card_omegaPlus_form hq4 (le_refl 2)
  rw [hKE] at hYE
  have hRLB : Rt M (LB M Q B) t ≠ LB M Q B := by
    intro heq
    have hL : IsPGroup 2 ↥(LB M Q B) := Ctx.isPGroup_LB h34 hc hs.width hs.n_gt hs.noA2 hs.gen
    have hR2 : IsPGroup 2 ↥(Rt M (LB M Q B) t) := by rw [heq]; exact hL
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).mp hR2
    have hdvd : Nat.card ↥(StatedOmega (StatedQuadPlus 2 KE)) ∣ 2 ^ j :=
      ⟨Nat.card ↥(Nt M (LB M Q B) t), by rw [← hj]; exact hRN⟩
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact orth_not_pgroup_omegaPlus_four hq4 (IsPGroup.of_card hi)
  rcases h310 G M Q Z B hc 4 hs.width hs.n_gt hs.noA2 hs.gen t hs.mem hs.notQ with
    hRL | ⟨K, fK, finK, hKq, hfam⟩
  · exact absurd hRL hRLB
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
  have hpos : 0 < Nat.card ↥(Nt M (LB M Q B) t) := Nat.card_pos
  rcases hfam with ⟨k, hk, hnat⟩ | ⟨k, hk, hnat⟩ | ⟨k, hk, hnat⟩ | ⟨k, b, c, hk, hirr, hnat⟩
  · exfalso
    have hcard : Nat.card ↥(StatedSL k K) = Nat.card ↥(StatedOmega (StatedQuadPlus 2 KE)) := by
      have h1 := orth_natural_card hc hNtCN hnat
      rw [hRN] at h1
      exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · have hk2 : k = 2 := by omega
      subst hk2
      rw [CFSG.Open.StatedAPI.card_statedSL_two K, hKq] at hcard
      have h1 : ((Nat.card Z * (Nat.card Z ^ 2 - 1) : ℕ) : ℤ) =
          (Nat.card Z : ℤ) ^ (2 * (2 - 1)) * XE := by rw [hcard]; exact hYE
      have hq4Z : 4 ≤ Nat.card Z := hc.hyp.q4
      have hsub : ((Nat.card Z ^ 2 - 1 : ℕ) : ℤ) = (Nat.card Z : ℤ) ^ 2 - 1 := by
        have : 1 ≤ Nat.card Z ^ 2 := Nat.one_le_pow _ _ (by omega)
        push_cast [Nat.cast_sub this]; ring
      push_cast [hsub] at h1
      have h2 : (Nat.card Z : ℤ) ^ 2 - 1 = (Nat.card Z : ℤ) * XE := by
        have : (Nat.card Z : ℤ) * ((Nat.card Z : ℤ) ^ 2 - 1) =
            (Nat.card Z : ℤ) * ((Nat.card Z : ℤ) * XE) := by
          rw [h1]; ring
        exact mul_left_cancel₀ hq0 this
      have h3 : Even ((Nat.card Z : ℤ) ^ 2 - 1) := by
        rw [h2]; exact hqZ.mul_right XE
      have h4 : Odd ((Nat.card Z : ℤ) ^ 2 - 1) :=
        (hqZ.pow_of_ne_zero (by norm_num)).sub_odd odd_one
      exact (Int.not_even_iff_odd.mpr h4) h3
    · refine orth_sl_exp_false_of_two_le (q := Nat.card Z) (m := 2) (k := k) ?_
        (by have := hc.hyp.q4; omega) (le_refl 2) (by omega)
        (Y := Nat.card ↥(StatedOmega (StatedQuadPlus 2 KE))) hXE ?_ ?_
      · rw [← hKE]; exact orth_even_card KE
      · exact_mod_cast hYE
      · rw [← hcard, ← hKq]
        exact orth_dvd_card_statedSL (by omega)
  · exfalso
    have hcard : Nat.card ↥(StatedSp k K) = Nat.card ↥(StatedOmega (StatedQuadPlus 2 KE)) := by
      have h1 := orth_natural_card hc hNtCN hnat
      rw [hRN] at h1
      exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
    obtain ⟨X', hX', hY'⟩ := orth_card_sp_form (K := K) k
    rw [hKq] at hY'
    have h1 : (Nat.card ↥(StatedSp k K) : ℤ) =
        (Nat.card ↥(StatedOmega (StatedQuadPlus 2 KE)) : ℤ) := by rw [hcard]
    rw [hY', hYE] at h1
    exact orth_sp_exp_ne hqZ hq0 (le_refl 2) hX' hXE h1
  · have hcard : Nat.card ↥(StatedOmega (StatedQuadPlus k K)) =
        Nat.card ↥(StatedOmega (StatedQuadPlus 2 KE)) := by
      have h1 := orth_natural_card hc hNtCN hnat
      rw [hRN] at h1
      exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
    have hq4K : 4 ≤ Nat.card K := by rw [hKq]; exact hc.hyp.q4
    obtain ⟨X', hX', hY'⟩ := orth_card_omegaPlus_form hq4K hk
    rw [hKq] at hY'
    have h1 : (Nat.card ↥(StatedOmega (StatedQuadPlus k K)) : ℤ) =
        (Nat.card ↥(StatedOmega (StatedQuadPlus 2 KE)) : ℤ) := by rw [hcard]
    rw [hY', hYE] at h1
    have hkm : k = 2 := orth_omega_exp_eq hqZ hq0 (by omega) (by omega) hX' hXE h1
    subst hkm
    exact ⟨K, fK, finK, hKq, hnat⟩
  · exfalso
    have hcard : Nat.card ↥(StatedOmega (StatedQuadMinus k K b c)) =
        Nat.card ↥(StatedOmega (StatedQuadPlus 2 KE)) := by
      have h1 := orth_natural_card hc hNtCN hnat
      rw [hRN] at h1
      exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
    obtain ⟨X', hX', hY'⟩ := orth_card_omegaMinus_form (K := K) hk hirr
    rw [hKq] at hY'
    have h1 : (Nat.card ↥(StatedOmega (StatedQuadMinus k K b c)) : ℤ) =
        (Nat.card ↥(StatedOmega (StatedQuadPlus 2 KE)) : ℤ) := by rw [hcard]
    rw [hY', hYE] at h1
    have hkm : k = 2 := orth_omega_exp_eq hqZ hq0 (by omega) (by omega) hX' hXE h1
    subst hkm
    exact orth_card_plus_ne_minus_of_two_le (K := KE) (K' := K) (hKq.trans hKE.symm) hq4
      (le_refl 2) hirr hcard.symm

theorem orth_notQB_plus_two (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {t : G}
    (hs : Sec5Hyp hc 4 t) (hnat : OmegaPlusNat hc t 2) : ¬ Vt M (LB M Q B) B Z t ≤ QB B := by
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV := hc.B_le_Vt hs.mem
  have hVQ := hc.Vt_le_Q t
  obtain ⟨K, _, _, hK, φ, hφr, -, hsec⟩ := hnat
  refine hc.not_le_QB_of_natural h35 hLR hZV hBV hVQ hK (ι := Fin 2 ⊕ Fin 2) ?_ φ hsec
    (polarBilin (quadPlus 2 K)) ?_
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · rintro A ⟨s, rfl⟩ u hu hrank
    have hA : φ s ∈ StatedOmega (StatedQuadPlus 2 K) := by
      rw [← hφr]
      exact ⟨s, rfl⟩
    exact omega_hform (CFSG.LieType.Universal.Spin.coe_quadPlus 2 K)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 2 K) hA hu hrank

theorem orth_Vt_eq_Ut_plus_two (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {t : G}
    (hs : Sec5Hyp hc 4 t) (hnat : OmegaPlusNat hc t 2) :
    Vt M (LB M Q B) B Z t = Ut Q Z t :=
  (hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB
    (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1 hs.mem hs.notQ
    (orth_notQB_plus_two h34 hc hs hnat)).1

end Natural

section Glue

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem orth_tensor_glue_cube [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (h34 : Stroth34Statement) {t : G} (ht : t ∈ LB M Q B) (htQ : t ∉ Q)
    (hVU : Vt M (LB M Q B) B Z t = Ut Q Z t)
    {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (qF : QuadraticForm F (ι → F)) (hFZ : Nat.card F = Nat.card Z) (hιn : Fintype.card ι = n)
    (hnd : ∀ u : ι → F, (∀ v, polar qF u v = 0) → u = 0)
    (hXiso : ∀ A ∈ StatedOmega ⇑qF, ∀ v, qF ((A : Matrix ι ι F) *ᵥ v) = qF v)
    (hscal : AddCommutantScalar (StatedOmega ⇑qF))
    (hEich : ∀ a' w' : ι → F, qF a' = 0 → polar qF a' w' = 0 →
      (toLinEquiv ι F).symm (eichler qF a' w') ∈ StatedOmega ⇑qF)
    (hnat : NaturalRep F (StatedOmega ⇑qF) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z
      (hc.CN t))
    {A B' : Type} [Group A] [Group B'] (ψ₀ : A × B' →* Mbar M Q)
    (hψ₀ : Function.Injective ψ₀) (hψ₀r : ψ₀.range = bar M Q (Lgen M (LB M Q B)))
    {F₂ : Type} [Field F₂] [Finite F₂] (hF₂card : Nat.card F₂ = Nat.card Z)
    (eA : A ≃* StatedSL 2 F₂)
    (hXR : embProdSnd ψ₀ ≤ bar M Q (Rt M (LB M Q B) t))
    (hRX : ∀ r ∈ bar M Q (Rt M (LB M Q B) t), ∃ k ∈ bar M Q (hc.CN t),
      ∃ x ∈ embProdSnd ψ₀, r = k * x) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ ∧
      ∃ (θ : K ≃+* F) (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
        OrthPreFrame Q Z M₀ (qTransport θ qF) φ ∧
        (∀ s ∈ Lgen M (LB M Q B), ∃ (g : Matrix (Fin 2) (Fin 2) K) (o : (ι → K) ≃ₗ[K] (ι → K)),
          g.det = 1 ∧ (∀ v, qTransport θ qF (o v) = qTransport θ qF v) ∧
            ActsAsTensor Q Z M₀ φ s g o) ∧
        (∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 → ∃ s ∈ Lgen M (LB M Q B),
          ActsAsTensor Q Z M₀ φ s g id) ∧
        (∀ a w : ι → K, qTransport θ qF a = 0 → polar (qTransport θ qF) a w = 0 →
          ∃ s ∈ Lgen M (LB M Q B),
            ActsAsTensor Q Z M₀ φ s 1 (eichler (qTransport θ qF) a w)) ∧
        (∃ u : ι → K, u ≠ 0 ∧ (∀ e : M₀.E, e ∈ M₀.img B ↔ ∃ s : K, φ e = s • (u, 0))) ∧
        (∀ (s : G) (hsM : s ∈ M) (a : A),
          (QuotientGroup.mk ⟨s, hsM⟩ : Mbar M Q) = ψ₀ (a, 1) →
            ∃ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 ∧ ActsAsTensor Q Z M₀ φ s g id) := by
  classical
  have hLM : Lgen M (LB M Q B) ≤ M := Lgen_le hc.LB_le_M
  obtain ⟨K, hK, hKfin, γ, M₀, ρ, b, hS⟩ := tensorSetup_of_34 h34 G M Q Z B hc n hw hn hno hgen
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hS.card.trans hZ2)
  have h35 := (stroth_3_5 h34 hc hw hn hno hgen).2.1
  obtain ⟨θ, Ψ, π, hπr, hπk, hΨθ, hΨπ⟩ := hc.natural_transport hS ht hFZ hscal hnat
  have hcardA : Nat.card A = Nat.card Z * (Nat.card Z ^ 2 - 1) := by
    rw [Nat.card_congr eA.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hF₂card]
  have hNR : bar M Q (hc.CN t) ≤ bar M Q (Rt M (LB M Q B) t) := hc.bar_CN_le_bar_Rt t
  have hXH0 : embProdSnd ψ₀ ≤ bar M Q (H0 M Z) := by
    refine (embProdSnd_le_range ψ₀).trans ?_
    rw [hψ₀r]; exact hc.bar_Lgen_le_bar_H0
  have hAH0 : embProdFst ψ₀ ≤ bar M Q (H0 M Z) := by
    refine (embProdFst_le_range ψ₀).trans ?_
    rw [hψ₀r]; exact hc.bar_Lgen_le_bar_H0
  let incA : A →* ↥(bar M Q (H0 M Z)) :=
    (ψ₀.comp (MonoidHom.inl A B')).codRestrict _ (fun a => hAH0 ⟨a, rfl⟩)
  let incX : B' →* ↥(bar M Q (H0 M Z)) :=
    (ψ₀.comp (MonoidHom.inr A B')).codRestrict _ (fun b => hXH0 ⟨b, rfl⟩)
  let ΦA : A →* (M₀.E ≃ₗ[K] M₀.E) := (orthLinAct hS).comp incA
  let ΦX : B' →* (M₀.E ≃ₗ[K] M₀.E) := (orthLinAct hS).comp incX
  have hincA : ∀ a, ((incA a : ↥(bar M Q (H0 M Z))) : Mbar M Q) = ψ₀ (a, 1) := fun a => rfl
  have hincX : ∀ b, ((incX b : ↥(bar M Q (H0 M Z))) : Mbar M Q) = ψ₀ (1, b) := fun b => rfl
  have hincXR : ∀ b, ψ₀ (1, b) ∈ bar M Q (Rt M (LB M Q B) t) := fun b => hXR ⟨b, rfl⟩
  let W : Submodule K M₀.E := hc.VtSub hS.model t
  let ν : (ι → K) →ₗ[K] M₀.E := orthNuMap θ W Ψ hΨθ
  let Ω : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) := omegaK θ (StatedOmega ⇑qF)
  have hAct : ∀ (g : ↥(bar M Q (H0 M Z)))
      (hgR : (g : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t)) (u : ι → K),
      orthLinAct hS g (ν u) = ν (((thetaLin θ).symm (π ⟨g, hgR⟩)) u) := by
    intro g hgR u
    set r : ↥(bar M Q (Rt M (LB M Q B) t)) := ⟨g, hgR⟩ with hr
    set o := (thetaLin θ).symm (π r) with ho
    have hmv : ((π r : GL ι F) : Matrix ι ι F) *ᵥ thetaVec θ u = thetaVec θ (o u) := by
      rw [← thetaLin_mulVec θ o u, ho, MulEquiv.apply_symm_apply]
    have key := hΨπ r (Ψ.symm (thetaVec θ u))
    rw [AddEquiv.apply_symm_apply, hmv] at key
    have key2 := congrArg (fun z : ↥W => (z : M₀.E)) (Ψ.symm_apply_eq.mpr key.symm)
    exact key2.symm
  have hXact : ∀ b : B', ∃ o ∈ Ω, ∀ u, ΦX b (ν u) = ν (o u) := by
    intro b
    refine ⟨(thetaLin θ).symm (π ⟨incX b, hincXR b⟩), ?_, hAct (incX b) (hincXR b)⟩
    rw [mem_omegaK, MulEquiv.apply_symm_apply, ← hπr]; exact ⟨_, rfl⟩
  have hXsurj : ∀ o ∈ Ω, ∃ b : B', ∀ u, ΦX b (ν u) = ν (o u) := by
    intro o ho
    have hA : thetaLin θ o ∈ π.range := by rw [hπr]; exact ho
    obtain ⟨r, hr⟩ := hA
    obtain ⟨n, hn, x, hx, hrnx⟩ := hRX r.1 r.2
    obtain ⟨b, rfl⟩ := hx
    have hxR := hincXR b
    have hπx : π ⟨ψ₀ (1, b), hxR⟩ = thetaLin θ o := by
      have h1 : r = ⟨n, hNR hn⟩ * ⟨ψ₀ (1, b), hxR⟩ := Subtype.ext hrnx
      have h2 : π ⟨n, hNR hn⟩ = 1 := (hπk _).mpr hn
      rw [← hr, h1, map_mul, h2, one_mul]
    refine ⟨b, fun u => ?_⟩
    rw [show ΦX b (ν u) = orthLinAct hS (incX b) (ν u) from rfl, hAct (incX b) hxR u]
    show ν (((thetaLin θ).symm (π ⟨ψ₀ (1, b), hxR⟩)) u) = ν (o u)
    rw [hπx, MulEquiv.symm_apply_apply]
  have hWr : LinearMap.range ν = W := range_nuMap θ W Ψ hΨθ
  have hirr : ∀ S : Submodule K M₀.E, S ≤ LinearMap.range ν →
      (∀ x ∈ ΦX.range, ∀ v ∈ S, x v ∈ S) → S = ⊥ ∨ S = LinearMap.range ν := by
    intro S hSle hSinv
    rw [hWr] at hSle ⊢
    refine hc.irred_VtSub hS h35 ht S hSle (fun x hx v hv => ?_)
    obtain ⟨n', hn', y, hy, hxny⟩ := hRX x hx
    obtain ⟨b, rfl⟩ := hy
    have h1 : (ρ x).toAdd v = (ρ n').toAdd ((ρ (ψ₀ (1, b))).toAdd v) := by
      rw [hxny]; exact act_mul_apply ρ n' _ v
    have h2 : (ρ (ψ₀ (1, b))).toAdd v ∈ S := hSinv (ΦX b) ⟨b, rfl⟩ v hv
    rw [h1, hc.act_CN hS ht n' hn' _ (hSle h2)]
    exact h2
  have htM : t ∈ M := hc.LB_le_M ht
  have htH : t ∈ H0 M Z := hc.LB_le_H0 ht
  let tb : ↥(bar M Q (H0 M Z)) :=
    ⟨QuotientGroup.mk ⟨t, htM⟩, ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.mpr htH, rfl⟩⟩
  let τ : M₀.E ≃ₗ[K] M₀.E := orthLinAct hS tb
  obtain ⟨htQ1, htQ2⟩ := hc.conj_mem_Q_of_mem_M htM
  have hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x) := fun x hx => hS.conj ⟨t, htM⟩ x hx
  have hττ : τ * τ = 1 := by
    have : tb * tb = 1 := by
      apply Subtype.ext
      show (QuotientGroup.mk ⟨t, htM⟩ * QuotientGroup.mk ⟨t, htM⟩ : Mbar M Q) = 1
      rw [← QuotientGroup.mk_mul]
      exact (QuotientGroup.eq_one_iff _).mpr
        (Subgroup.mem_subgroupOf.mpr (by
          show t * t ∈ Q
          rw [← _root_.sq]; exact hc.sq_mem_Q_of_mem_LB ht))
    rw [← map_mul, this, map_one]
  have hWrange : ∀ e, e ∈ W ↔ e ∈ LinearMap.range ((τ : M₀.E →ₗ[K] M₀.E) - 1) := by
    intro e
    have h1 : e ∈ W ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t) := hc.mem_VtSub hS.model t
    rw [h1, hVU]
    exact mem_img_comm_zpowers_sup_iff M₀ hS.model.reg τ htQ1 htQ2 hτπ e
  have hQ0 : ∀ u, M₀.Qf (ν u) = 0 := fun u =>
    (M₀.isElemAbelian_iff hS.model.reg (hc.Vt_le_Q t)).mp (hc.Vt_isElemAbelian h35 ht htQ) _
      ((hc.mem_VtSub hS.model t).mp (orthNuMap_mem θ W Ψ hΨθ u))
  let ψ : M₀.E →ₗ[K] M₀.E := (τ : M₀.E →ₗ[K] M₀.E) - 1
  have hψe : ∀ e, ψ e = τ e - e := fun e => rfl
  have hψrange : LinearMap.range ψ = LinearMap.range ν := by
    rw [hWr]; ext e; exact (hWrange e).symm
  have hψcomm : ∀ x ∈ ΦX.range, ∀ e, x (ψ e) = ψ (x e) := by
    rintro _ ⟨b, rfl⟩ e
    have hcomm := hc.bar_Rt_comm (t := ⟨t, htM⟩) (ψ₀ (1, b)) (hincXR b)
    have hxt : ΦX b * τ = τ * ΦX b := by
      show orthLinAct hS (incX b) * orthLinAct hS tb = orthLinAct hS tb * orthLinAct hS (incX b)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm
    have h1 : ΦX b (τ e) = τ (ΦX b e) := congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f e) hxt
    simp only [hψe, map_sub, h1]
  have hψψ : ∀ e, ψ (ψ e) = 0 := by
    intro e
    have h1 : τ (τ e) = e := congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f e) hττ
    have h2 : ∀ x : M₀.E, x + x = 0 := fun x => by
      rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
    simp only [hψe, map_sub, h1]
    have e1 : e - τ e - (τ e - e) = (e + e) - (τ e + τ e) := by abel
    rw [e1, h2, h2, sub_zero]
  have hKcard : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  have hcardKF : Nat.card K = Nat.card F := hS.card.trans hFZ.symm
  have hfinW : Module.finrank K W = n := by
    have h1 : Nat.card W = Nat.card (ι → F) := Nat.card_congr Ψ.toEquiv
    rw [Nat.card_fun, Module.natCard_eq_pow_finrank (K := K), ← hcardKF,
      Nat.card_eq_fintype_card (α := ι), hιn] at h1
    exact Nat.pow_right_injective hKcard h1
  have hkerψ : LinearMap.ker ψ = LinearMap.range ν := by
    have hle : LinearMap.range ν ≤ LinearMap.ker ψ := by
      rw [hWr]
      intro w hw
      obtain ⟨e, rfl⟩ := (hWrange w).mp hw
      exact hψψ e
    refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
    have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    rw [hψrange] at h1
    have h2 : Module.finrank K (LinearMap.range ν) = n := by rw [hWr]; exact hfinW
    have h3 := hS.dim
    omega
  have hq := statedSL_quasisimple_of_card 2 F₂ le_rfl (by rw [hF₂card]; exact hc.hyp.q4)
  haveI hSLperf : Group.IsPerfect ↥(StatedSL 2 F₂) := hq.1
  haveI hApf : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := eA.symm.toMonoidHom)
    eA.symm.surjective
  have hAnonab : ∃ a b : A, a * b ≠ b * a := by
    obtain ⟨a', b', hab⟩ := hq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
    have hne : a * b ≠ b * a := fun h =>
      hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])
    exact ⟨eA.symm a, eA.symm b, fun h => hne (eA.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hincAinj : Function.Injective incA := by
    intro a b h
    have h' : ψ₀ (a, 1) = ψ₀ (b, 1) :=
      congrArg (fun z : ↥(bar M Q (H0 M Z)) => (z : Mbar M Q)) h
    exact congrArg Prod.fst (hψ₀ h')
  have hΦAinj : Function.Injective ΦA := (orthLinAct_injective hS).comp hincAinj
  have hcore : TensorCoreHyp M₀.Qf M₀.B (qTransport θ qF) Ω ΦX.range ΦA.range ν ψ :=
    { qadd := M₀.Qf_add
      nondegB := M₀.nondeg
      nondegU := qTransport_nondeg θ qF hnd
      omega_isom := fun o ho v => omegaK_isom θ qF hXiso ho v
      omega_comm := fun f hf => omegaK_comm θ hscal f hf
      nu_inj := orthNuMap_injective θ W Ψ hΨθ
      x_isom := by rintro _ ⟨b, rfl⟩ e; exact orthLinAct_isom hS _ e
      a_isom := by rintro _ ⟨a, rfl⟩ e; exact orthLinAct_isom hS _ e
      a_comm_x := by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
        show orthLinAct hS (incA a) * orthLinAct hS (incX b) =
          orthLinAct hS (incX b) * orthLinAct hS (incA a)
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (embProdFst_comm ψ₀ ⟨a, rfl⟩ ⟨b, rfl⟩)
      x_inv := by rintro _ ⟨b, rfl⟩; exact hXact b
      x_surj := fun o ho => by
        obtain ⟨b, hb⟩ := hXsurj o ho
        exact ⟨ΦX b, ⟨b, rfl⟩, hb⟩
      irr := hirr
      psi_comm := hψcomm
      psi_range := hψrange
      psi_ker := hkerψ
      w_sing := hQ0
      a_perfect := Subgroup.isPerfect_iff.mp (Group.IsPerfect.range ΦA)
      a_nonabelian := by
        obtain ⟨a, b, hab⟩ := hAnonab
        exact ⟨ΦA a, ⟨a, rfl⟩, ΦA b, ⟨b, rfl⟩, fun h => hab (hΦAinj (by rw [map_mul, map_mul, h]))⟩
      a_card := by
        rw [Nat.card_congr (MonoidHom.ofInjective hΦAinj).toEquiv.symm, hcardA, hS.card] }
  obtain ⟨φ, hφQ, hφν, hφX1, hφX2, hφA1, hφA2⟩ := TensorCoreHyp.tensor_core hcore
  have hLH : Lgen M (LB M Q B) ≤ H0 M Z := hc.Lgen_le_H0_sec4x
  have hmkS : ∀ s : ↥M, (s : G) ∈ Lgen M (LB M Q B) →
      (QuotientGroup.mk s : Mbar M Q) ∈ ψ₀.range := by
    intro s hs
    rw [hψ₀r]; exact ⟨s, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  refine ⟨K, hK, hKfin, inferInstance, γ, M₀, hS.model, θ, φ,
    ⟨qTransport_nondeg θ qF hnd, hφQ⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hsM : s ∈ M := hLM hs
    obtain ⟨⟨a, b⟩, hab⟩ := hmkS ⟨s, hsM⟩ hs
    obtain ⟨g, hgdet, hgA⟩ := hφA1 (ΦA a) ⟨a, rfl⟩
    obtain ⟨o, ho, hoX⟩ := hφX1 (ΦX b) ⟨b, rfl⟩
    refine ⟨g, o, hgdet, fun v => omegaK_isom θ qF hXiso ho v, fun x hx => ?_⟩
    have hconj := hS.conj ⟨s, hsM⟩ x hx
    have hsab : (QuotientGroup.mk ⟨s, hsM⟩ : Mbar M Q) = ψ₀ (a, 1) * ψ₀ (1, b) := by
      rw [← map_mul, ← hab]; simp
    rw [hconj, hsab]
    have e1 : (ρ (ψ₀ (a, 1) * ψ₀ (1, b))).toAdd (M₀.π x) = ΦA a (ΦX b (M₀.π x)) := by
      rw [act_mul_apply]; rfl
    rw [e1, hgA (ΦX b (M₀.π x)), hoX (M₀.π x)]
    rfl
  · intro g hg
    obtain ⟨_, ⟨a, rfl⟩, hga⟩ := hφA2 g hg
    have hmem : ψ₀ (a, 1) ∈ bar M Q (Lgen M (LB M Q B)) := by
      rw [← hψ₀r]; exact ⟨(a, 1), rfl⟩
    obtain ⟨s, hsL, hsa⟩ := orth_exists_mk_of_mem_bar hmem
    refine ⟨(s : G), hsL, fun x hx => ?_⟩
    have hconj := hS.conj s x hx
    rw [hconj, hsa]
    have e1 : (ρ (ψ₀ (a, 1))).toAdd (M₀.π x) = ΦA a (M₀.π x) := rfl
    rw [e1, hga (M₀.π x)]
    rfl
  · intro a w ha hw
    have ha' : qF (thetaVec θ a) = 0 := by rw [← theta_qTransport θ qF a, ha, map_zero]
    have hw' : polar qF (thetaVec θ a) (thetaVec θ w) = 0 := by
      rw [← theta_polar_qTransport θ qF a w, hw, map_zero]
    have hoΩ : eichler (qTransport θ qF) a w ∈ Ω := by
      rw [mem_omegaK, thetaLin_eichler θ qF ha hw]
      exact hEich _ _ ha' hw'
    obtain ⟨_, ⟨b, rfl⟩, hxb⟩ := hφX2 _ hoΩ
    have hmem : ψ₀ (1, b) ∈ bar M Q (Lgen M (LB M Q B)) := by
      rw [← hψ₀r]; exact ⟨(1, b), rfl⟩
    obtain ⟨s, hsL, hsa⟩ := orth_exists_mk_of_mem_bar hmem
    refine ⟨(s : G), hsL, fun x hx => ?_⟩
    have hconj := hS.conj s x hx
    rw [hconj, hsa]
    have e1 : (ρ (ψ₀ (1, b))).toAdd (M₀.π x) = ΦX b (M₀.π x) := rfl
    rw [e1, hxb (M₀.π x)]
    ext <;> simp [orthTensor]
  ·
    obtain ⟨b₁, hb₁0, -, hb₁line, -, -⟩ := hc.dictB hS.model
    have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
    have hb₁B : b₁ ∈ M₀.img B := (hb₁line b₁).mpr ⟨1, (one_smul K b₁).symm⟩
    have hb₁W : b₁ ∈ W := by
      obtain ⟨u, huB, huQ, hu⟩ := M₀.mem_img.mp hb₁B
      exact (hc.mem_VtSub hS.model t).mpr (M₀.mem_img.mpr ⟨u, hBV huB, huQ, hu⟩)
    obtain ⟨u₀, hu₀⟩ : b₁ ∈ LinearMap.range ν := by rw [hWr]; exact hb₁W
    have hu₀ne : u₀ ≠ 0 := by
      rintro rfl
      exact hb₁0 (by rw [← hu₀, map_zero])
    have hφb₁ : φ b₁ = (u₀, 0) := by rw [← hu₀]; exact hφν u₀
    refine ⟨u₀, hu₀ne, fun e => ?_⟩
    rw [hb₁line e]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, by rw [map_smul, hφb₁]⟩
    · rintro ⟨s, hs⟩
      refine ⟨s, φ.injective ?_⟩
      rw [map_smul, hφb₁]
      exact hs
  ·
    intro s hsM a hsa
    obtain ⟨g, hgdet, hgA⟩ := hφA1 (ΦA a) ⟨a, rfl⟩
    refine ⟨g, hgdet, fun x hx => ?_⟩
    have hconj := hS.conj ⟨s, hsM⟩ x hx
    rw [hconj, hsa]
    have e1 : (ρ (ψ₀ (a, 1))).toAdd (M₀.π x) = ΦA a (M₀.π x) := rfl
    rw [e1, hgA (M₀.π x)]
    rfl


end Glue

section Plus

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem orth_exists_ne_zero_one (K : Type) [Field K] [Finite K] (h : 4 ≤ Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun c : K => (if c = 0 then (0 : Fin 2) else 1)) := by
    intro a b hab
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [ha, hb]
    · simp [ha, hb] at hab
    · simp [ha, hb] at hab
    · rw [hcon a ha, hcon b hb]
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

theorem orth_exists_psi [(Q.subgroupOf M).Normal]
    [(Q.subgroupOf (Lgen M (LB M Q B))).Normal] (hc : Ctx M Q Z B) {A B' : Type} [Group A]
    [Group B'] (e : (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) ≃* A × B') :
    ∃ ψ₀ : A × B' →* Mbar M Q, Function.Injective ψ₀ ∧
      ψ₀.range = bar M Q (Lgen M (LB M Q B)) := by
  have hLM : Lgen M (LB M Q B) ≤ M := Lgen_le hc.LB_le_M
  let e₃ : (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) ≃*
      ↥(bar M Q (Lgen M (LB M Q B))) :=
    (MonoidHom.ofInjective (quotIncl_injective (Q := Q) hLM)).trans
      (MulEquiv.subgroupCongr (quotIncl_range hLM))
  let eS : ↥(bar M Q (Lgen M (LB M Q B))) ≃* A × B' := e₃.symm.trans e
  let ψ₀ : A × B' →* Mbar M Q :=
    (bar M Q (Lgen M (LB M Q B))).subtype.comp eS.symm.toMonoidHom
  refine ⟨ψ₀, fun a b h => eS.symm.injective (Subtype.ext h), ?_⟩
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact (eS.symm p).2
  · intro hx
    exact ⟨eS ⟨x, hx⟩, by simp [ψ₀]⟩

theorem smith24E2PlusTwo_tensor (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hNt : StrothNtStatement) (hcfg : SmithOrthCfg M Q Z B) {t : G}
    (hE : CaseE2Plus M Q Z B t 2) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ ∧
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (qU : QuadraticForm K (ι → K))
        (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
        OrthPreFrame Q Z M₀ qU φ ∧ OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)) ∧
          (∃ u : ι → K, u ≠ 0 ∧ ∀ e : M₀.E, e ∈ M₀.img B ↔ ∃ s : K, φ e = s • (u, 0)) ∧
          ∀ x ∈ M, ∃ s ∈ LB M Q B, s ∉ Q ∧ ∃ g' : Matrix (Fin 2) (Fin 2) K, g'.det = 1 ∧
            ActsAsTensor Q Z M₀ φ (x * s * x⁻¹) g' id := by
  classical
  have hc : Ctx M Q Z B := hcfg.ctx
  haveI : (Q.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hc.hyp.Q_normal.2
  have hw : Width Q Z 4 := by
    unfold Width
    rw [hE.2.1]
  have hn : 2 < 4 := by norm_num
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  obtain ⟨hN', A, B', _, _, hA, hB', ⟨e⟩⟩ := hE.2.2.2.2
  haveI := hN'
  obtain ⟨ψ₀, hψ₀, hψ₀r⟩ := orth_exists_psi hc e
  obtain ⟨F₂, hF₂, hF₂fin, hF₂card, ⟨eA⟩⟩ := hA
  obtain ⟨KE, hKEf, hKEfin, hKE, ⟨eB₀⟩⟩ := hB'
  haveI : CharP F₂ 2 := charP_two_of_card_eq_two_pow (hF₂card.trans hZ2)
  haveI : CharP KE 2 := charP_two_of_card_eq_two_pow (hKE.trans hZ2)
  have hF4 : 4 ≤ Nat.card F₂ := by rw [hF₂card]; exact hc.hyp.q4
  have hK4 : 4 ≤ Nat.card KE := by rw [hKE]; exact hc.hyp.q4
  obtain ⟨eB₁⟩ := statedOmega_plus_four_nonempty_equiv KE hK4
  obtain ⟨t', ht'LB, ht'Q, hXR, hRX, hcard⟩ :=
    orth_support h34 hc hw hn hno hgen ψ₀ hψ₀ hψ₀r hF4 eA hK4 (eB₀.trans eB₁)
  have hs : Sec5Hyp hc 4 t' := ⟨hw, hn, hno, hgen, ht'LB, ht'Q⟩
  have hNtCN : hc.CN t' = Nt M (LB M Q B) t' :=
    (hNt G M Q Z B hc 4 hw hn hno hgen t' ht'LB ht'Q).symm
  have hRN : Nat.card ↥(Rt M (LB M Q B) t') =
      Nat.card ↥(StatedOmega (StatedQuadPlus 2 KE)) * Nat.card ↥(Nt M (LB M Q B) t') := by
    rw [hcard, Nat.card_congr eB₀.toEquiv]
  have hNat := orth_e2Natural_plus_two h34 h310 hc hs hNtCN hKE hRN
  have hVU := orth_Vt_eq_Ut_plus_two h34 hc hs hNat
  obtain ⟨K', hF', hFin', hK'card, hnat⟩ := hNat
  haveI : CharP K' 2 := charP_two_of_card_eq_two_pow (hK'card.trans hZ2)
  have hq4 : 4 ≤ Nat.card K' := by rw [hK'card]; exact hc.hyp.q4
  have hcoe : ⇑(quadPlus 2 K') = StatedQuadPlus 2 K' :=
    CFSG.LieType.Universal.Spin.coe_quadPlus 2 K'
  obtain ⟨c, hc0, hc1⟩ := orth_exists_ne_zero_one K' hq4
  haveI : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  have hnat' : NaturalRep (ι := Fin 2 ⊕ Fin 2) K' (StatedOmega ⇑(quadPlus 2 K'))
      (Rt M (LB M Q B) t') (Vt M (LB M Q B) B Z t') Z (hc.CN t') := by rw [hcoe]; exact hnat
  have hres := orth_tensor_glue_cube hc hw hn hno hgen h34 ht'LB ht'Q hVU
    (quadPlus 2 K') hK'card (by simp [Fintype.card_sum])
    (fun u hu => (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 2 K').1 u
      (fun v => by simpa [QuadraticMap.polarBilin_apply_apply] using hu v))
    (fun A hA v => mem_statedOmega_preserves (Q := quadPlus 2 K') rfl hA v)
    (by rw [hcoe]; exact addCommutantScalar_statedOmegaPlus_two ⟨c, hc0, hc1⟩)
    (fun a' w' _ _ => by
      rw [hcoe, CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_map_elementaryGroup
        (CFSG.LieType.Universal.Spin.coe_quadPlus 2 K')
        (Classify.commutator_orthogonalGroup_quadPlus_two K' hc0 hc1)]
      exact Subgroup.mem_map.mpr ⟨eichler (quadPlus 2 K') a' w',
        CFSG.ClassicalGroups.Orthogonal.eichler_mem_elementaryGroup _ a' w', rfl⟩)
    hnat' ψ₀ hψ₀ hψ₀r hF₂card eA hXR
    (by rw [hNtCN]; exact hRX)
  obtain ⟨K, hK, hKfin, hKchar, γ, M₀, hM, θ, φ, hpre, hact, hsl, heich, hline, hH1⟩ := hres
  refine ⟨K, hK, hKfin, hKchar, γ, M₀, hM, Fin 2 ⊕ Fin 2, inferInstance, inferInstance,
    qTransport θ (quadPlus 2 K'), φ, hpre, ⟨hact, hsl, heich⟩, hline, fun x hx => ?_⟩
  obtain ⟨s, hsLB, hsmk, hxs⟩ :=
    orth_exists_fixer h34 hc hw hn hno hgen ψ₀ hψ₀ hψ₀r hF4 eA ⟨x, hx⟩
  obtain ⟨a, ha⟩ := hxs
  have hsQ : (s : G) ∉ Q := by
    intro hq
    exact hsmk ((QuotientGroup.eq_one_iff s).mpr (Subgroup.mem_subgroupOf.mpr hq))
  have hxsM : x * (s : G) * x⁻¹ ∈ M := M.mul_mem (M.mul_mem hx s.2) (M.inv_mem hx)
  have hel : (⟨x * (s : G) * x⁻¹, hxsM⟩ : ↥M) = ⟨x, hx⟩ * s * ⟨x, hx⟩⁻¹ := Subtype.ext rfl
  obtain ⟨g', hg'det, hg'⟩ := hH1 (x * (s : G) * x⁻¹) hxsM a (by
    rw [hel]
    exact ha.symm)
  exact ⟨(s : G), hsLB, hsQ, g', hg'det, hg'⟩

end Plus

end CFSG.RankThree.GF2n.Smith81
