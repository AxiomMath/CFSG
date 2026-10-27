module

public import CFSG.RankThree.GF2n.Tim79a34BigEpsCore
public import CFSG.RankThree.GF2n.Tim79a34BigEpsKQ

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

section BigEpsPartm6

theorem bigEpsTwo_data (hZ : Sec34CentreTrivialStatement) (hN : BigNaturalStatement)
    (hIW : BigIWStatement) (hγ : BigGammaStatement) (G : Type) [Group G] [Finite G]
    (M V Q P H : Subgroup G) (hH : BigEndHyp M V Q P H) :
    ∃ (n f : ℕ) (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H))
      (a : Fin n ⊕ Fin n → GaloisField 2 f) (B : Subgroup G),
      2 ^ f = qBar V H ∧ BigEpsCfg (psiElt ψ) a M P Q B ∧
      BigEpsExtra (psiElt ψ) a M P Q B V ∧ B ≤ wOf V H ∧
      (P ⊓ wOf V H) ⊔ B = wOf V H ∧
      ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f), spForm a c = 0 →
        (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
        ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), r ∈ M ∧
          (∀ b ∈ B, ⁅b, r⁆ ∈ Q) ∧
          ∀ y, r * psiElt ψ y * r⁻¹ = psiElt ψ (y + (μ * spForm c y) • c) := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcentre : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hcentre
  obtain ⟨n, f, Φ, ψ, hn2, hf, hequiv, ⟨a, T, ha, hTT, hTV⟩, hpoint⟩ :=
    hN G M V Q P H hH hcentre
  have hNat : BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨B, hBW, hBP, hPB, -⟩ := bigBStatement_of_local hZ hN hIW G M V Q P H hH
  obtain ⟨hiff, hRbar, hxOf, -⟩ :=
    bigPLocalStatement_holds G M V Q P H hH hcentre hcP hf Φ ψ hNat a T ha hTT hTV
  have hCover := bigPCoverStatement_holds G M V Q P H hH hcentre hcP hf Φ ψ hNat a T ha hTT hTV
  have hroot := bigRootElement_holds bigPLocalStatement_holds G M V Q P H hH hcentre hcP hf Φ ψ
    hNat a T ha hTT hTV
  have hPQ := (bigPQCommStatement_of_natural hZ hN hIW hγ G M V Q P H hH).1
  have hQW := bigQWStatement_of_natural hZ hN hIW hγ G M V Q P H hH
  have hiff' : ∀ w, psiElt ψ w ∈ P ↔ spForm a w = 0 := hiff
  have hWM : wOf V H ≤ M := wOf_le_M_of_minCex hc
  have hWC := bigWbarCentralizesStatement_holds G M V Q P H hH
  have hVcent : ∀ v ∈ V, ∀ p ∈ P, v * p = p * v := fun v hv p hp => hc.commute_of_mem_P hp hv
  have hAV : ∀ l : GaloisField 2 f, psiElt ψ (l • a) ∈ V := by
    intro l
    by_cases hl : l = 0
    · rw [hl, zero_smul, psiElt_zero]
      exact V.one_mem
    · have hla : l • a ≠ 0 := smul_ne_zero hl ha
      have hTla : CaseM.IsTransGroup (l • a) T :=
        CaseM.IsTransGroup.of_smul (v := l • a) (l := l⁻¹) (inv_ne_zero hl)
          (by rwa [inv_smul_smul₀ hl])
      exact hpoint (l • a) T hla hTla hTV
  have hVW : ∀ β : Fin n ⊕ Fin n → GaloisField 2 f, psiElt ψ β ∈ V →
      ∃ l : GaloisField 2 f, β = l • a :=
    fun β hβ => bigRW_eq_smul_of_psi_mem_V hH hf hNat ha hTT hTV (u := β) hβ
  have hnormV : ∀ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ V := fun m hm v hv => by
    have hmN : m ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq]
      exact hm
    exact (Subgroup.mem_normalizer_iff.mp hmN v).mp hv
  have hVact : ∀ c : GaloisField 2 f, ∃ v ∈ V, BigEpsParam (psiElt ψ) a v 0 c := by
    intro c
    obtain ⟨g, hg⟩ := hTT.2 c
    have hgT : g ∈ T := (hTT.1 g).mpr ⟨c, hg⟩
    have hΦg : Φ g ∈ Vy V H := by
      rw [← hTV]
      exact Subgroup.mem_map.mpr ⟨g, hgT, rfl⟩
    obtain ⟨x, hxV, hx⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp hΦg)
    have hxX : (x : G) ∈ xOf V H := by
      rw [hxOf]
      exact x.2
    have hk : xToXbar hc.V_le_H ⟨(x : G), hxX⟩ = Φ g := by
      apply Subtype.ext
      rw [coe_xToXbar]
      exact hx
    refine ⟨(x : G), hxV, fun β => ?_⟩
    have hE := hNat.equiv ⟨(x : G), hxX⟩ β
    rw [hk, Φ.symm_apply_apply, hg, spTrans_mulVec] at hE
    have e : β + spForm a β • (0 : Fin n ⊕ Fin n → GaloisField 2 f) +
        spForm (0 : Fin n ⊕ Fin n → GaloisField 2 f) β • a + (c * spForm a β) • a =
        β + (c * spForm a β) • a := by
      rw [smul_zero, spForm_zero_left, zero_smul, add_zero, add_zero]
    exact hE.symm.trans (congrArg (psiElt ψ) e.symm)
  have hkerP : ∀ p ∈ P, (∀ β, p * psiElt ψ β * p⁻¹ = psiElt ψ β) →
      ∃ x, spForm a x = 0 ∧ p = psiElt ψ x := by
    intro p hpP hfix
    have hpX : p ∈ xOf V H := by
      rw [hxOf]
      exact hc.PleH hpP
    have hfix' : ∀ β, SpExtras.mat n (GaloisField 2 f)
        (Φ.symm (xToXbar hc.V_le_H ⟨p, hpX⟩)) *ᵥ β = β := by
      intro β
      refine psiElt_injective ψ ?_
      exact (hNat.equiv ⟨p, hpX⟩ β).trans (hfix β)
    have hmat : SpExtras.mat n (GaloisField 2 f) (Φ.symm (xToXbar hc.V_le_H ⟨p, hpX⟩)) = 1 :=
      Matrix.ext_iff_mulVec.mpr fun v => by
        rw [Matrix.one_mulVec]
        exact hfix' v
    have hτ : Φ.symm (xToXbar hc.V_le_H ⟨p, hpX⟩) = 1 :=
      SpExtras.mat_injective (hmat.trans (map_one (SpExtras.mat n (GaloisField 2 f))).symm)
    have h1 : xToXbar hc.V_le_H ⟨p, hpX⟩ = 1 := by
      rw [(Φ.symm_apply_eq).mp hτ, map_one]
    have h2 : piBar V H (Subgroup.inclusion (xOf_le_H hc.V_le_H) ⟨p, hpX⟩) = 1 :=
      congrArg Subtype.val h1
    have hpW : p ∈ wOf V H := (piBar_eq_one_iff _).mp h2
    obtain ⟨x, hx⟩ := exists_psiElt ψ hpW
    refine ⟨x, ?_, hx.symm⟩
    exact (hiff' x).mp (by rw [hx]; exact hpP)
  have hPall : ∀ u : Fin n ⊕ Fin n → GaloisField 2 f, spForm a u = 0 →
      ∀ c : GaloisField 2 f, ∃ p ∈ P, BigEpsParam (psiElt ψ) a p u c := by
    intro u hu c
    obtain ⟨g, hg, hgf⟩ := exists_spRad_of_param hu c
    have hmem : Φ g ∈ Rbar V H P := by
      rw [hRbar]
      exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    obtain ⟨p', hp'P, hp'⟩ := mem_barOf_iff.mp (mem_Rbar.mp hmem)
    have hpX : (p' : G) ∈ xOf V H := by
      rw [hxOf]
      exact p'.2
    have hk : xToXbar hc.V_le_H ⟨(p' : G), hpX⟩ = Φ g := by
      apply Subtype.ext
      rw [coe_xToXbar]
      exact hp'
    refine ⟨(p' : G), hp'P, fun β => ?_⟩
    have hE := hNat.equiv ⟨(p' : G), hpX⟩ β
    rw [hk, Φ.symm_apply_apply, hgf β] at hE
    exact hE.symm
  have hq4 : 4 ≤ qBar V H := hH.q_big
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hf
    omega
  have hqK : Nat.card (GaloisField 2 f) = qBar V H := by
    rw [GaloisField.card 2 f hf0, hf]
  have hthree : ∀ d : GaloisField 2 f, ∃ s : GaloisField 2 f, s ≠ 0 ∧ s ≠ d := by
    intro d
    by_contra hcon
    push Not at hcon
    have hsurj : Function.Surjective (![(0 : GaloisField 2 f), d] : Fin 2 → GaloisField 2 f) := by
      intro s
      by_cases hs : s = 0
      · exact ⟨0, by simp [hs]⟩
      · exact ⟨1, by simp [hcon s hs]⟩
    have hle : Nat.card (GaloisField 2 f) ≤ Nat.card (Fin 2) :=
      Nat.card_le_card_of_surjective _ hsurj
    have hfin : Nat.card (Fin 2) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hrootB : ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f),
      spForm a c = 0 → (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
      ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), r ∈ M ∧
        (∀ b ∈ B, ⁅b, r⁆ ∈ Q) ∧
        ∀ y, r * psiElt ψ y * r⁻¹ = psiElt ψ (y + (μ * spForm c y) • c) := by
    intro c μ hc0 hca hμ
    obtain ⟨r, hr, hract⟩ := hroot c μ hc0 hca hμ
    have hrM : r ∈ M := by
      have h1 : r ∈ Subgroup.normalizer (V : Set G) :=
        Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hr).2
      rwa [hc.normalizer_eq] at h1
    have hrbar : ((⟨r, hrM⟩ : ↥M) : Mbar M) ∈ RbarM M V H :=
      Subgroup.mem_map.mpr ⟨⟨r, hrM⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
    refine ⟨r, hr, hrM, fun b hb => ?_, hract⟩
    have hbM : b ∈ M := hWM (hBW hb)
    have hbbar : ((⟨b, hbM⟩ : ↥M) : Mbar M) ∈ WbarM M V H :=
      mem_WbarM_iff.mpr ⟨⟨b, hbM⟩, hBW hb, rfl⟩
    have hcm := Subgroup.mem_centralizer_iff.mp (hWC hbbar) _ hrbar
    have key : ((⟨b, hbM⟩ * ⟨r, hrM⟩ : ↥M) : Mbar M) =
        ((⟨r, hrM⟩ * ⟨b, hbM⟩ : ↥M) : Mbar M) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hcm.symm
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf] at key
    have e : (((⟨b, hbM⟩ * ⟨r, hrM⟩) / (⟨r, hrM⟩ * ⟨b, hbM⟩) : ↥M) : G) = ⁅b, r⁆ := by
      simp only [div_eq_mul_inv, _root_.mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv,
        commutatorElement_def]
      group
    rw [e] at key
    rwa [hc.hQ]
  refine ⟨n, f, ψ, a, B, hf, ⟨hn2, ha, psiElt_add ψ, psiElt_injective ψ, hiff', ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩, ⟨hc.V_le_P, hVcent, hAV, hVW, hnormV, hVact, hkerP, hPall, hthree⟩,
    hBW, hPB, hrootB⟩
  · intro q hq x hx
    obtain ⟨hV, hW⟩ := Subgroup.mem_inf.mp (hPQ q hq x hx)
    obtain ⟨u, hu⟩ := exists_psiElt ψ hW
    obtain ⟨l, hl⟩ := bigRW_eq_smul_of_psi_mem_V hH hf hNat ha hTT hTV (u := u)
      (by rw [show ((Additive.toMul (ψ u) : ↥(wOf V H)) : G) = ⁅q, x⁆ from hu]; exact hV)
    exact ⟨l, by rw [← hu, hl]⟩
  · intro m hm p hp
    exact (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P hm) p).mp hp
  · intro m hm q hq
    rw [hc.hQ] at hq ⊢
    exact (Subgroup.mem_normalizer_iff.mp ((inSubgroup_pCore_two M).2.2 hm) q).mp hq
  · intro p hp
    obtain ⟨τ, hτ, -, -, hact⟩ := bigAlpha_act hc hNat hxOf hRbar hp
    obtain ⟨u, hu, c, hparam⟩ := exists_spRad_param ha hτ
    refine ⟨u, c, hu, fun β => ?_⟩
    exact (hact β).symm.trans (congrArg (psiElt ψ) (hparam β))
  · intro β hβ z hz
    exact hCover β hβ (psiElt ψ z) ⟨(hiff' z).mpr hz, psiElt_mem ψ z⟩
  · intro β hβ
    have h1 : psiElt ψ β ∈ Q ⊓ wOf V H := ⟨hβ, psiElt_mem ψ β⟩
    rw [hQW] at h1
    exact h1.1
  · intro b hb
    exact exists_psiElt ψ (hBW hb)
  · intro b hb hbP
    have h1 : b ∈ B ⊓ P := ⟨hb, hbP⟩
    rw [hBP, Subgroup.mem_bot] at h1
    exact h1

end BigEpsPartm6

section BigEpsTwoG

variable {G : Type} [Group G]

theorem bigEps_comm_mem_Q {M Q : Subgroup G} (hQ : Q = inSubgroup (pCore 2) M) {x y : ↥M}
    (h : (x : Mbar M) * (y : Mbar M) = (y : Mbar M) * (x : Mbar M)) :
    ⁅(x : G), (y : G)⁆ ∈ Q := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem,
    Subgroup.mem_subgroupOf] at h
  have e : (((x * y) / (y * x) : ↥M) : G) = ⁅(x : G), (y : G)⁆ := by
    simp only [div_eq_mul_inv, _root_.mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv,
      commutatorElement_def]
    group
  rw [e, ← hQ] at h
  exact h

theorem bigEpsTwo_in_Wbar [Finite G] {M V Q P H B : Subgroup G} (hc : MinCex M V Q P H)
    {n f : ℕ} {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 f}
    (hcfg : BigEpsCfg (psiElt ψ) a M P Q B) (hext : BigEpsExtra (psiElt ψ) a M P Q B V)
    (hBW : B ≤ wOf V H) (hPB : (P ⊓ wOf V H) ⊔ B = wOf V H)
    (hroot : ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f), spForm a c = 0 →
      (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
      ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), r ∈ M ∧ (∀ b ∈ B, ⁅b, r⁆ ∈ Q) ∧
        ∀ y, r * psiElt ψ y * r⁻¹ = psiElt ψ (y + (μ * spForm c y) • c))
    (hPP : ⁅P, P⁆ = V ⊓ wOf V H) (hCP : Subgroup.centralizer (P : Set G) = V)
    (t : ↥M) (htR : (t : Mbar M) ∈ Subgroup.centralizer (RbarM M V H : Set (Mbar M)))
    (htW : (t : Mbar M) ∈ Subgroup.centralizer (WbarM M V H : Set (Mbar M)))
    (hF : ∀ x, spForm a x = 0 → ∃ l : GaloisField 2 f,
      (t : G) * psiElt ψ x * (t : G)⁻¹ = psiElt ψ (x + l • a)) :
    (t : Mbar M) ∈ WbarM M V H := by
  have hQM : Q = inSubgroup (pCore 2) M := hc.hQ
  have hWM : wOf V H ≤ M := wOf_le_M_of_minCex hc
  have hKQ : ∀ m ∈ M, (∀ p ∈ P, BigEpsInA (psiElt ψ) a ⁅m, p⁆) → m ∈ Q := by
    intro m hm hA
    refine bigEps_K_le_Q hc hPP hCP m hm (fun p hp => ?_)
    obtain ⟨l, hl⟩ := hA p hp
    rw [hl]
    exact Subgroup.mem_inf.mpr ⟨hext.AV l, psiElt_mem ψ _⟩
  have hrootC : ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f),
      spForm a c = 0 → (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
      ∃ r : G, r ∈ M ∧ ⁅(t : G), r⁆ ∈ Q ∧ (∀ b ∈ B, ⁅b, r⁆ ∈ Q) ∧
        (∀ v ∈ V, r * v * r⁻¹ = v) ∧
        ∀ y, r * psiElt ψ y * r⁻¹ = psiElt ψ (y + (μ * spForm c y) • c) := by
    intro c μ hc0 hca hμ
    obtain ⟨r, hr, hrM, hBr, hract⟩ := hroot c μ hc0 hca hμ
    refine ⟨r, hrM, ?_, hBr, ?_, hract⟩
    · have hrbar : ((⟨r, hrM⟩ : ↥M) : Mbar M) ∈ RbarM M V H :=
        Subgroup.mem_map.mpr ⟨⟨r, hrM⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
      have hcm := Subgroup.mem_centralizer_iff.mp htR _ hrbar
      exact bigEps_comm_mem_Q hQM hcm.symm
    · intro v hv
      have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hr).2 v hv
      rw [← this]
      group
  have hcomm : ∀ f' ∈ P ⊓ wOf V H, ∀ b ∈ B, f' * b = b * f' := fun f' hf' b hb =>
    hc.wOf_isElemAbelian.comm (Subgroup.mem_inf.mp hf').2 (hBW hb)
  have hFB : ∀ β : Fin n ⊕ Fin n → GaloisField 2 f, ∃ x, spForm a x = 0 ∧ ∃ b ∈ B,
      psiElt ψ β = psiElt ψ x * b := by
    intro β
    have hβ : psiElt ψ β ∈ (P ⊓ wOf V H) ⊔ B := by
      rw [hPB]
      exact psiElt_mem ψ β
    obtain ⟨f', hf', b, hb, hfb⟩ := exists_mul_of_mem_sup hcomm hβ
    obtain ⟨x, hx⟩ := exists_psiElt ψ (Subgroup.mem_inf.mp hf').2
    refine ⟨x, (hcfg.mem_P x).mp (by rw [hx]; exact (Subgroup.mem_inf.mp hf').1), b, hb, ?_⟩
    rw [hx, hfb]
  have hB : ∀ b ∈ B, b⁻¹ * ((t : G) * b * (t : G)⁻¹) ∈ Q := by
    intro b hb
    have hbM : b ∈ M := hWM (hBW hb)
    have hbbar : ((⟨b, hbM⟩ : ↥M) : Mbar M) ∈ WbarM M V H :=
      mem_WbarM_iff.mpr ⟨⟨b, hbM⟩, hBW hb, rfl⟩
    have hcm := Subgroup.mem_centralizer_iff.mp htW _ hbbar
    have h1 := bigEps_comm_mem_Q hQM hcm.symm
    have e : b⁻¹ * ((t : G) * b * (t : G)⁻¹) = b⁻¹ * ⁅(t : G), b⁆ * (b⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hcfg.normQ _ (M.inv_mem hbM) _ h1
  obtain ⟨b, hbB, hbQ⟩ := hcfg.core hext t.2 hKQ hrootC (fun b hb => hWM (hBW hb)) hFB hB hF
  have hbM : b ∈ M := hWM (hBW hbB)
  have hmk : ((⟨b, hbM⟩ : ↥M)⁻¹ * t : ↥M) ∈ (inSubgroup (pCore 2) M).subgroupOf M := by
    rw [Subgroup.mem_subgroupOf, ← hQM]
    simpa using hbQ
  have hteq : (t : Mbar M) = ((⟨b, hbM⟩ : ↥M) : Mbar M) :=
    (QuotientGroup.eq.mpr hmk).symm
  rw [hteq]
  exact mem_WbarM_iff.mpr ⟨⟨b, hbM⟩, hBW hbB, rfl⟩

end BigEpsTwoG

section BigEpsPartm4f

theorem bigEpsilonFaithfulTwoStatement_of_natural (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) (hγ : BigGammaStatement) :
    BigEpsilonFaithfulTwoStatement := by
  intro G _ _ M V Q P H hH x hx hxk
  obtain ⟨k, hk⟩ := hxk
  obtain ⟨n, f, ψ, a, B, hf, hcfg, hext, hBW, hPB, hroot⟩ :=
    bigEpsTwo_data hZ hN hIW hγ G M V Q P H hH
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcentre : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hcentre
  obtain ⟨hPP, -, hCP⟩ := bigPCommutatorStatement_holds hN G M V Q P H hH hcentre hcP
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
  have hxR := (Subgroup.mem_inf.mp hx).1
  have hxW := (Subgroup.mem_inf.mp hx).2
  have hQM : Q = inSubgroup (pCore 2) M := hc.hQ
  have hxN : (t : Mbar M) ∈ Subgroup.normalizer (RbarM M V H : Set (Mbar M)) :=
    Subgroup.centralizer_le_normalizer _ hxR
  have hconj := bigEpsFConjStatement_of_natural hZ hN hIW hγ G M V Q P H hH t hxN
  have hT3 : ∀ y, spForm a y = 0 → ∃ z, psiElt ψ z = (t : G) * psiElt ψ y * (t : G)⁻¹ := by
    intro y hy
    have hmem : (t : G) * psiElt ψ y * (t : G)⁻¹ ∈ conjSubgroup (t : G) (P ⊓ wOf V H) := by
      rw [mem_conjSubgroup]
      have e : (t : G)⁻¹ * ((t : G) * psiElt ψ y * (t : G)⁻¹) * (t : G) = psiElt ψ y := by group
      rw [e]
      exact ⟨(hcfg.mem_P y).mpr hy, psiElt_mem ψ y⟩
    rw [hconj] at hmem
    exact exists_psiElt ψ hmem.2
  have hroot' : ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f),
      spForm a c = 0 → (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
      ∃ r : G, ⁅(t : G), r⁆ ∈ Q ∧
        ∀ y, r * psiElt ψ y * r⁻¹ = psiElt ψ (y + (μ * spForm c y) • c) := by
    intro c μ hc0 hca hμ
    obtain ⟨r, hr, hrM, -, hract⟩ := hroot c μ hc0 hca hμ
    refine ⟨r, ?_, hract⟩
    have hrbar : ((⟨r, hrM⟩ : ↥M) : Mbar M) ∈ RbarM M V H :=
      Subgroup.mem_map.mpr ⟨⟨r, hrM⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
    have hcm := Subgroup.mem_centralizer_iff.mp hxR _ hrbar
    exact bigEps_comm_mem_Q hQM hcm.symm
  obtain ⟨κ, hκ⟩ := hcfg.exists_kappa t.2 hT3 hroot'
  have hT4 : (t : G) ^ (2 ^ k) ∈ Q := by
    have h1 : t ^ (2 ^ k) ∈ (inSubgroup (pCore 2) M).subgroupOf M := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hk
    have h2 := Subgroup.mem_subgroupOf.mp h1
    rw [hQM]
    exact h2
  have hκ1 : κ = 1 := hcfg.kappa_eq_one hκ hT4
  have hF : ∀ y, spForm a y = 0 → ∃ l : GaloisField 2 f,
      (t : G) * psiElt ψ y * (t : G)⁻¹ = psiElt ψ (y + l • a) := by
    intro y hy
    obtain ⟨l, hl⟩ := hκ y hy
    exact ⟨l, by rw [hl, hκ1, one_smul]⟩
  exact bigEpsTwo_in_Wbar hc hcfg hext hBW hPB hroot hPP hCP t hxR hxW hF

end BigEpsPartm4f

end CFSG.RankThree.GF2n.Tim79a
