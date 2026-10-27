module

public import CFSG.RankThree.GF2n.Tim79a34BigIdentCQ

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

section BigIdentTorus

variable {G : Type} [Group G] {M V Q P H : Subgroup G} {n f : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 f} {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}

theorem bigIdent_torus [Finite G] (hc : MinCex M V Q P H)
    (hNat : BigNatCfg V H hc.V_le_H Φ ψ) (ha : a ≠ 0) (hT : CaseM.IsTransGroup a T)
    (hTV : T.map Φ.toMonoidHom = Vy V H) {l : GaloisField 2 f} (hl : l ≠ 0) :
    ∃ (x : ↥(xOf V H)) (g' : ↥(StatedSp n (GaloisField 2 f))),
      Φ.symm (xToXbar hc.V_le_H x) = g' ∧ SpExtras.mat n (GaloisField 2 f) g' *ᵥ a = l • a ∧
      conjSubgroup (x : G) V = V := by
  obtain ⟨g', hg'⟩ := exists_mat_mulVec_eq_of_ne_zero ha (smul_ne_zero hl ha)
  obtain ⟨x, hx⟩ := xToXbar_surjective hc.V_le_H (Φ g')
  have hgx : Φ.symm (xToXbar hc.V_le_H x) = g' := by
    rw [hx]
    exact Φ.symm_apply_apply g'
  refine ⟨x, g', hgx, hg', ?_⟩
  have key := hNat.equiv x a
  rw [hgx, hg'] at key
  have haV : psiElt ψ a ∈ V := hNat.point a T ha hT hTV
  have hlaV : psiElt ψ (l • a) ∈ V := bigB_psi_smul_mem hc.V_le_H hNat ha hT hTV l
  refine conjSubgroup_eq_of_isTI hc.ti ?_
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨psiElt ψ (l • a),
    Subgroup.mem_inf.mpr ⟨hlaV, ?_⟩⟩, ?_⟩
  · rw [mem_conjSubgroup]
    have e : (x : G)⁻¹ * psiElt ψ (l • a) * (x : G) = psiElt ψ a := by
      have h1 : psiElt ψ (l • a) = (x : G) * psiElt ψ a * (x : G)⁻¹ := key
      rw [h1]
      group
    rw [e]
    exact haV
  · intro h1
    have h2 : psiElt ψ (l • a) = psiElt ψ 0 := by
      have := congrArg Subtype.val h1
      rw [psiElt_zero]
      exact this
    have h3 := psiElt_injective ψ h2
    rcases smul_eq_zero.mp h3 with h | h
    · exact hl h
    · exact ha h

end BigIdentTorus

theorem bigIdent_comm_conj (hZ : Sec34CentreTrivialStatement) (hN : BigNaturalStatement)
    (hIW : BigIWStatement) (hγ : BigGammaStatement) (G : Type) [Group G] [Finite G]
    (M V Q P H : Subgroup G) (hH : BigEndHyp M V Q P H) {e : G} (heQ : e ∈ Q)
    (hec : ∀ w ∈ wOf V H, e * w = w * e) {x : G} (hxX : x ∈ xOf V H) (hxM : x ∈ M) {v₀ : G}
    (hv₀ : v₀ ∈ V) : ⁅e, x * v₀ * x⁻¹⁆ = x * ⁅e, v₀⁆ * x⁻¹ := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hQM : Q = inSubgroup (pCore 2) M := hc.hQ
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQM]
    exact (inSubgroup_pCore_two M).2.2
  have hQW : Q ⊓ wOf V H = P ⊓ wOf V H := bigQWStatement_of_natural hZ hN hIW hγ G M V Q P H hH
  have heM : e ∈ M := (inSubgroup_pCore_two M).2.1 (hQM ▸ heQ)
  have hec' : ∀ w ∈ wOf V H, e⁻¹ * w = w * e⁻¹ := fun w hw => by
    have := hec w hw
    calc e⁻¹ * w = e⁻¹ * (w * e) * e⁻¹ := by group
      _ = e⁻¹ * (e * w) * e⁻¹ := by rw [this]
      _ = w * e⁻¹ := by group
  have hW1 : ⁅e⁻¹, x⁻¹⁆ ∈ wOf V H :=
    bigIdent_comm_mem_W hZ hN G M V Q P H hH (M.inv_mem heM) hec' ((xOf V H).inv_mem hxX)
  have hfQ : e⁻¹ * (x⁻¹ * e * x) ∈ Q := by
    have h1 : x⁻¹ * e * x ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hMQ (M.inv_mem hxM)) e).mp heQ
      simpa using this
    exact Q.mul_mem (Q.inv_mem heQ) h1
  have hfW : e⁻¹ * (x⁻¹ * e * x) ∈ wOf V H := by
    have e1 : ⁅e⁻¹, x⁻¹⁆ = e⁻¹ * (x⁻¹ * e * x) := by
      simp only [commutatorElement_def]
      group
    rw [← e1]
    exact hW1
  have hfP : e⁻¹ * (x⁻¹ * e * x) ∈ P ⊓ wOf V H := by
    rw [← hQW]
    exact Subgroup.mem_inf.mpr ⟨hfQ, hfW⟩
  have hfv : v₀ * (e⁻¹ * (x⁻¹ * e * x)) = (e⁻¹ * (x⁻¹ * e * x)) * v₀ :=
    hc.commute_of_mem_P (Subgroup.mem_inf.mp hfP).1 hv₀
  set f := e⁻¹ * (x⁻¹ * e * x) with hf
  have hxe : x⁻¹ * e * x = e * f := by rw [hf]; group
  have h2 : x⁻¹ * ⁅e, x * v₀ * x⁻¹⁆ * x = ⁅x⁻¹ * e * x, v₀⁆ := by
    simp only [commutatorElement_def]
    group
  have h3 : ⁅e * f, v₀⁆ = ⁅e, v₀⁆ := by
    have : f * v₀ * f⁻¹ = v₀ := by
      have := hfv
      calc f * v₀ * f⁻¹ = (f * v₀) * f⁻¹ := by group
        _ = (v₀ * f) * f⁻¹ := by rw [← this]
        _ = v₀ := by group
    calc ⁅e * f, v₀⁆ = e * (f * v₀ * f⁻¹) * e⁻¹ * v₀⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = ⁅e, v₀⁆ := by rw [this]; simp only [commutatorElement_def]
  have h4 : x⁻¹ * ⁅e, x * v₀ * x⁻¹⁆ * x = ⁅e, v₀⁆ := by rw [h2, hxe, h3]
  calc ⁅e, x * v₀ * x⁻¹⁆ = x * (x⁻¹ * ⁅e, x * v₀ * x⁻¹⁆ * x) * x⁻¹ := by group
    _ = x * ⁅e, v₀⁆ * x⁻¹ := by rw [h4]

theorem bigIdent_conj_le_W (hZ : Sec34CentreTrivialStatement) (hN : BigNaturalStatement)
    (hIW : BigIWStatement) (hγ : BigGammaStatement) (G : Type) [Group G] [Finite G]
    (M V Q P H : Subgroup G) (hH : BigEndHyp M V Q P H) {B : Subgroup G}
    (hBW : B ≤ wOf V H) (hBP : B ⊓ P = ⊥) {g : G} (hg : g ∈ M)
    (hcomm : ∀ b ∈ B, ∀ w ∈ wOf V H, ⁅g * b * g⁻¹, w⁆ = 1) :
    conjSubgroup g B ≤ wOf V H := by
  intro y hy
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hcentre : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hcentre
  obtain ⟨n, f, Φ, ψ, -, hf, hequiv, ⟨a, T, ha, hTT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hcentre
  have hNat : BigNatCfg V H hVH Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨hiff, -, hxOf, -⟩ :=
    bigPLocalStatement_holds G M V Q P H hH hcentre hcP hf Φ ψ hNat a T ha hTT hTV
  obtain ⟨-, hFrat, -⟩ := bigPCommutatorStatement_holds hN G M V Q P H hH hcentre hcP
  have hQW : Q ⊓ wOf V H = P ⊓ wOf V H := bigQWStatement_of_natural hZ hN hIW hγ G M V Q P H hH
  have hQM : Q = inSubgroup (pCore 2) M := hc.hQ
  have hWM : wOf V H ≤ M := wOf_le_M_of_minCex hc
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQM]
    exact (inSubgroup_pCore_two M).2.2
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := hc.normalizer_eq.ge
  have hMP : M ≤ Subgroup.normalizer (P : Set G) := hc.M_le_normalizer_P
  have hWn : ∀ h ∈ H, ∀ w ∈ wOf V H, h * w * h⁻¹ ∈ wOf V H := fun h hh w hw =>
    (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hh) w).mp hw
  have hVX : V ≤ xOf V H := le_xOf (V_mem_omegaOf V H)
  have hAnorm : ∀ z ∈ V ⊓ wOf V H, g * z * g⁻¹ ∈ V ⊓ wOf V H := by
    intro z hz
    have h1 := mem_normalizer_inSubgroup_frattini (hMP hg)
    rw [hFrat] at h1
    exact (Subgroup.mem_normalizer_iff.mp h1 z).mp hz
  have hgV : ∀ z ∈ V, g⁻¹ * z * g ∈ V := fun z hz => by
    have := (Subgroup.mem_normalizer_iff.mp (hMV (M.inv_mem hg)) z).mp hz
    simpa using this
  have hy' : g⁻¹ * y * g ∈ B := mem_conjSubgroup.mp hy
  have hyeq : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
  by_cases hb1 : g⁻¹ * y * g = 1
  · have : y = 1 := by
      rw [hyeq, hb1]
      group
    rw [this]
    exact (wOf V H).one_mem
  obtain ⟨β₁, hβ₁⟩ := exists_psiElt ψ (hBW hy')
  have hs₁ : CaseM.spForm a β₁ ≠ 0 := by
    intro h0
    have h1 : g⁻¹ * y * g ∈ B ⊓ P :=
      Subgroup.mem_inf.mpr ⟨hy', by rw [← hβ₁]; exact (hiff β₁).mpr h0⟩
    rw [hBP, Subgroup.mem_bot] at h1
    exact hb1 h1
  obtain ⟨w', hw'W, e, heQ, hec, hyw⟩ :=
    bigIdent_exists_mul_CQ hZ hN hIW hγ G M V Q P H hH hBW hg hcomm hy
  have heM : e ∈ M := (inSubgroup_pCore_two M).2.1 (hQM ▸ heQ)
  obtain ⟨β', hβ'⟩ := exists_psiElt ψ hw'W
  have hs' : CaseM.spForm a β' ≠ 0 := by
    intro h0
    have hw'P : w' ∈ P := by rw [← hβ']; exact (hiff β').mpr h0
    have hyQ : y ∈ Q := by
      rw [hyw]
      exact Q.mul_mem (hc.P_le_Q hw'P) heQ
    have hb₁Q : g⁻¹ * y * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hMQ (M.inv_mem hg)) y).mp hyQ
      simpa using this
    have hb₁P : g⁻¹ * y * g ∈ P ⊓ wOf V H := by
      rw [← hQW]
      exact Subgroup.mem_inf.mpr ⟨hb₁Q, hBW hy'⟩
    have h1 : g⁻¹ * y * g ∈ B ⊓ P := Subgroup.mem_inf.mpr ⟨hy', (Subgroup.mem_inf.mp hb₁P).1⟩
    rw [hBP, Subgroup.mem_bot] at h1
    exact hb1 h1
  obtain ⟨v₀, hv₀V, hv₀W⟩ := SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
  obtain ⟨μ, hμ, hact⟩ := bigRW_conj_act_eq_trans hVH hNat hTT hTV hv₀V hv₀W
  have hev₀ : ⁅e, v₀⁆ ∈ V ⊓ wOf V H := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : e * v₀ * e⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hMV heM) v₀).mp hv₀V
      have e1 : ⁅e, v₀⁆ = (e * v₀ * e⁻¹) * v₀⁻¹ := by simp only [commutatorElement_def]
      rw [e1]
      exact V.mul_mem h1 (V.inv_mem hv₀V)
    · exact bigIdent_comm_mem_W hZ hN G M V Q P H hH heM hec (hVX hv₀V)
  obtain ⟨β₀, hβ₀⟩ := exists_psiElt ψ (Subgroup.mem_inf.mp hev₀).2
  obtain ⟨ℓ₀, hℓ₀⟩ := bigRW_eq_smul_of_psi_mem_V hH hf hNat ha hTT hTV (u := β₀)
    (by rw [show ((Additive.toMul (ψ β₀) : ↥(wOf V H)) : G) = ⁅e, v₀⁆ from hβ₀]
        exact (Subgroup.mem_inf.mp hev₀).1)
  have hev₀' : ⁅e, v₀⁆ = psiElt ψ (ℓ₀ • a) := by rw [← hℓ₀]; exact hβ₀.symm
  have hℓ0 : ℓ₀ = 0 := by
    by_contra hℓ
    have hl0 : ℓ₀ / (CaseM.spForm a β' * μ) ≠ 0 := div_ne_zero hℓ (mul_ne_zero hs' hμ)
    obtain ⟨x, g', hgx, hg', hxV⟩ := bigIdent_torus hc hNat ha hTT hTV hl0
    set l := ℓ₀ / (CaseM.spForm a β' * μ) with hl
    have hxX : (x : G) ∈ xOf V H := x.2
    have hxM : (x : G) ∈ M := by
      rw [← hc.normalizer_eq]
      exact mem_normalizer_iff_conjSubgroup_eq.mpr hxV
    have hxH : (x : G) ∈ H := xOf_le_H hVH hxX
    have hvV : (x : G) * v₀ * (x : G)⁻¹ ∈ V := by
      have : (x : G) * v₀ * (x : G)⁻¹ ∈ conjSubgroup (x : G) V := ⟨v₀, hv₀V, rfl⟩
      rwa [hxV] at this
    have hvact := hact x g' hgx β'
    rw [hg'] at hvact
    have hev : ⁅e, (x : G) * v₀ * (x : G)⁻¹⁆ = psiElt ψ ((l * ℓ₀) • a) := by
      rw [bigIdent_comm_conj hZ hN hIW hγ G M V Q P H hH heQ hec hxX hxM hv₀V, hev₀']
      have key : psiElt ψ (ℓ₀ • l • a) = (x : G) * psiElt ψ (ℓ₀ • a) * (x : G)⁻¹ := by
        have := hNat.equiv x (ℓ₀ • a)
        rw [hgx, Matrix.mulVec_smul, hg'] at this
        exact this
      rw [← key, smul_smul, mul_comm ℓ₀ l]
    have hz2 : psiElt ψ ((μ * (l * l * CaseM.spForm a β')) • a) *
        psiElt ψ ((μ * (l * l * CaseM.spForm a β')) • a) = 1 := bigRW_psi_mul_self _
    have hwv : ⁅w', (x : G) * v₀ * (x : G)⁻¹⁆ =
        psiElt ψ ((μ * (l * l * CaseM.spForm a β')) • a) := by
      have h1 : ((x : G) * v₀ * (x : G)⁻¹) * w' * ((x : G) * v₀ * (x : G)⁻¹)⁻¹ =
          w' * psiElt ψ ((μ * (l * l * CaseM.spForm a β')) • a) := by
        rw [← hβ']
        have h2 : (μ * CaseM.spForm (l • a) β') • l • a =
            (μ * (l * l * CaseM.spForm a β')) • a := by
          rw [spForm_smul_left', smul_smul]
          congr 1
          ring
        have hvact' : ((x : G) * v₀ * (x : G)⁻¹) * psiElt ψ β' * ((x : G) * v₀ * (x : G)⁻¹)⁻¹ =
            psiElt ψ (β' + (μ * CaseM.spForm (l • a) β') • l • a) := hvact
        rw [hvact', h2, psiElt_add]
      have h3 : ⁅(x : G) * v₀ * (x : G)⁻¹, w'⁆ =
          psiElt ψ ((μ * (l * l * CaseM.spForm a β')) • a) := by
        calc ⁅(x : G) * v₀ * (x : G)⁻¹, w'⁆
            = (((x : G) * v₀ * (x : G)⁻¹) * w' * ((x : G) * v₀ * (x : G)⁻¹)⁻¹) * w'⁻¹ := by
              simp only [commutatorElement_def]
          _ = (w' * psiElt ψ ((μ * (l * l * CaseM.spForm a β')) • a)) * w'⁻¹ := by rw [h1]
          _ = psiElt ψ ((μ * (l * l * CaseM.spForm a β')) • a) := by
              rw [hc.wOf_comm hw'W (psiElt_mem ψ _)]
              group
      rw [← commutatorElement_inv, h3]
      exact inv_eq_of_mul_eq_one_right hz2
    have hlℓ : l * (CaseM.spForm a β' * μ) = ℓ₀ := by
      rw [hl]
      field_simp
    have hsum : (l * ℓ₀) • a + (μ * (l * l * CaseM.spForm a β')) • a = 0 := by
      have e1 : μ * (l * l * CaseM.spForm a β') = l * ℓ₀ := by
        rw [← hlℓ]
        ring
      rw [e1, ← add_smul, CharTwo.add_self_eq_zero, zero_smul]
    have hyv : ⁅y, (x : G) * v₀ * (x : G)⁻¹⁆ = 1 := by
      have e1 : ⁅w' * e, (x : G) * v₀ * (x : G)⁻¹⁆ =
          w' * ⁅e, (x : G) * v₀ * (x : G)⁻¹⁆ * w'⁻¹ * ⁅w', (x : G) * v₀ * (x : G)⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      have e2 : w' * psiElt ψ ((l * ℓ₀) • a) * w'⁻¹ = psiElt ψ ((l * ℓ₀) • a) := by
        rw [hc.wOf_comm hw'W (psiElt_mem ψ _)]
        group
      rw [hyw, e1, hev, hwv, e2, ← psiElt_add, hsum, psiElt_zero]
    have huV : g⁻¹ * ((x : G) * v₀ * (x : G)⁻¹) * g ∈ V := hgV _ hvV
    have huW : g⁻¹ * ((x : G) * v₀ * (x : G)⁻¹) * g ∉ wOf V H := by
      intro hu
      have h1 := hAnorm _ (Subgroup.mem_inf.mpr ⟨huV, hu⟩)
      have e : g * (g⁻¹ * ((x : G) * v₀ * (x : G)⁻¹) * g) * g⁻¹ =
          (x : G) * v₀ * (x : G)⁻¹ := by group
      rw [e] at h1
      apply hv₀W
      have h2 := hWn (x : G)⁻¹ (H.inv_mem hxH) _ (Subgroup.mem_inf.mp h1).2
      have e2 : (x : G)⁻¹ * ((x : G) * v₀ * (x : G)⁻¹) * ((x : G)⁻¹)⁻¹ = v₀ := by group
      rwa [e2] at h2
    have hnc := bigDelta_noncomm hc hNat ha hTT hTV huV huW hs₁
    apply hnc
    have hyv' : y * ((x : G) * v₀ * (x : G)⁻¹) = ((x : G) * v₀ * (x : G)⁻¹) * y :=
      commutatorElement_eq_one_iff_mul_comm.mp hyv
    have hb₁ : psiElt ψ β₁ = g⁻¹ * y * g := hβ₁
    show g⁻¹ * ((x : G) * v₀ * (x : G)⁻¹) * g * psiElt ψ β₁ =
      psiElt ψ β₁ * (g⁻¹ * ((x : G) * v₀ * (x : G)⁻¹) * g)
    rw [hb₁]
    calc g⁻¹ * ((x : G) * v₀ * (x : G)⁻¹) * g * (g⁻¹ * y * g)
        = g⁻¹ * (((x : G) * v₀ * (x : G)⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * ((x : G) * v₀ * (x : G)⁻¹)) * g := by rw [hyv']
      _ = g⁻¹ * y * g * (g⁻¹ * ((x : G) * v₀ * (x : G)⁻¹) * g) := by group
  have heV : ∀ v ∈ V, v * e = e * v := by
    intro v hv
    by_cases hvW : v ∈ wOf V H
    · exact (hec v hvW).symm
    · obtain ⟨μv, hμv, hactv⟩ := bigRW_conj_act_eq_trans hVH hNat hTT hTV hv hvW
      obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq (GaloisField 2 f) 2) (μv / μ)
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [mul_zero, div_eq_zero_iff] at hr
        rcases hr with h | h
        · exact hμv h
        · exact hμ h
      obtain ⟨x, g', hgx, hg', hxV⟩ := bigIdent_torus hc hNat ha hTT hTV hr0
      have hxX : (x : G) ∈ xOf V H := x.2
      have hxM : (x : G) ∈ M := by
        rw [← hc.normalizer_eq]
        exact mem_normalizer_iff_conjSubgroup_eq.mpr hxV
      have hv'V : (x : G) * v₀ * (x : G)⁻¹ ∈ V := by
        have : (x : G) * v₀ * (x : G)⁻¹ ∈ conjSubgroup (x : G) V := ⟨v₀, hv₀V, rfl⟩
        rwa [hxV] at this
      have hvact : ∀ β, v * psiElt ψ β * v⁻¹ = psiElt ψ (β + (μv * CaseM.spForm a β) • a) := by
        intro β
        have h1 := hactv 1 1 (by rw [map_one, map_one]) β
        simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one, map_one,
          Matrix.one_mulVec] at h1
        exact h1
      have hv'act : ∀ β, ((x : G) * v₀ * (x : G)⁻¹) * psiElt ψ β * ((x : G) * v₀ * (x : G)⁻¹)⁻¹ =
          psiElt ψ (β + (μ * CaseM.spForm (r • a) β) • r • a) := by
        intro β
        have h1 := hact x g' hgx β
        rw [hg'] at h1
        exact h1
      have hv'inv : ((x : G) * v₀ * (x : G)⁻¹)⁻¹ = (x : G) * v₀ * (x : G)⁻¹ :=
        inv_eq_of_mul_eq_one_right (hc.elemAb.mul_self_eq_one hv'V)
      have hzV : ((x : G) * v₀ * (x : G)⁻¹) * v ∈ V := V.mul_mem hv'V hv
      have hzW : ((x : G) * v₀ * (x : G)⁻¹) * v ∈ wOf V H := by
        refine bigIdent_centralizer_X_le_W hZ hN G M V Q P H hH (hVX hzV) fun w hw => ?_
        obtain ⟨β, rfl⟩ := exists_psiElt ψ hw
        have e1 : (((x : G) * v₀ * (x : G)⁻¹) * v) * psiElt ψ β *
            (((x : G) * v₀ * (x : G)⁻¹) * v)⁻¹ =
            ((x : G) * v₀ * (x : G)⁻¹) * (v * psiElt ψ β * v⁻¹) *
              ((x : G) * v₀ * (x : G)⁻¹)⁻¹ := by group
        rw [e1, hvact, hv'act]
        have e2 : CaseM.spForm a (β + (μv * CaseM.spForm a β) • a) = CaseM.spForm a β := by
          rw [spForm_add_right, spForm_smul_right', CaseM.spForm_self, mul_zero, add_zero]
        have e3 : (β + (μv * CaseM.spForm a β) • a) +
            (μ * CaseM.spForm (r • a) (β + (μv * CaseM.spForm a β) • a)) • r • a = β := by
          rw [spForm_smul_left', e2, smul_smul]
          have e4 : μ * (r * CaseM.spForm a β) * r = μv * CaseM.spForm a β := by
            have h5 : μv = μ * (r * r) := by
              have := hr
              field_simp at this
              linear_combination this
            rw [h5]
            ring
          rw [e4, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
        rw [e3]
      have hev' : ⁅e, (x : G) * v₀ * (x : G)⁻¹⁆ = 1 := by
        rw [bigIdent_comm_conj hZ hN hIW hγ G M V Q P H hH heQ hec hxX hxM hv₀V, hev₀', hℓ0,
          zero_smul, psiElt_zero]
        group
      have hvz : v = ((x : G) * v₀ * (x : G)⁻¹) * (((x : G) * v₀ * (x : G)⁻¹) * v) := by
        have := hc.elemAb.mul_self_eq_one hv'V
        calc v = (((x : G) * v₀ * (x : G)⁻¹) * ((x : G) * v₀ * (x : G)⁻¹)) * v := by
              rw [this, one_mul]
          _ = _ := by group
      have hez : e * (((x : G) * v₀ * (x : G)⁻¹) * v) = (((x : G) * v₀ * (x : G)⁻¹) * v) * e :=
        hec _ hzW
      have hev : e * v = v * e := by
        have h1 : e * ((x : G) * v₀ * (x : G)⁻¹) = ((x : G) * v₀ * (x : G)⁻¹) * e :=
          commutatorElement_eq_one_iff_mul_comm.mp hev'
        calc e * v = e * (((x : G) * v₀ * (x : G)⁻¹) * (((x : G) * v₀ * (x : G)⁻¹) * v)) := by
              rw [← hvz]
          _ = (((x : G) * v₀ * (x : G)⁻¹) * e) * (((x : G) * v₀ * (x : G)⁻¹) * v) := by
              rw [← mul_assoc, h1, mul_assoc]
          _ = ((x : G) * v₀ * (x : G)⁻¹) * (e * (((x : G) * v₀ * (x : G)⁻¹) * v)) := by group
          _ = ((x : G) * v₀ * (x : G)⁻¹) * ((((x : G) * v₀ * (x : G)⁻¹) * v) * e) := by rw [hez]
          _ = v * e := by rw [← mul_assoc, ← hvz]
      exact hev.symm
  have heP : e ∈ P := by
    rw [hc.hP]
    exact Subgroup.mem_inf.mpr ⟨heQ, Subgroup.mem_centralizer_iff.mpr heV⟩
  have heX : e ∈ xOf V H := by
    rw [hxOf]
    exact hc.PleH heP
  have heW : e ∈ wOf V H := by
    refine bigIdent_centralizer_X_le_W hZ hN G M V Q P H hH heX fun w hw => ?_
    rw [hec w hw]
    group
  rw [hyw]
  exact (wOf V H).mul_mem hw'W heW

theorem bigIdentStatement_of_natural (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) (hγ : BigGammaStatement) :
    BigIdentStatement := by
  intro G _ _ M V Q P H hH _ B hBW hBP _ _ g hg hcomm
  exact (bigIdent_conj_le_W hZ hN hIW hγ G M V Q P H hH hBW hBP hg hcomm).trans le_sup_left

end CFSG.RankThree.GF2n.Tim79a
