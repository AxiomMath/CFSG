module

public import CFSG.RankThree.GF2n.Stroth80.Sec78Core
public import CFSG.RankThree.GF2n.Stroth80.Sec78ModuleIneq
public import CFSG.RankThree.GF2n.Stroth80.Sec7WVOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec83ChiEndo


public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap
open scoped commutatorElement Matrix

theorem step78_arith2 {q a b e f c Vc m : ℕ} (hq : 1 < q) (ha : q * a = Vc) (hb : b * q = Vc)
    (he : e = q ^ 2) (hf : f * q = Vc * c) (hkey : e ^ 2 * f ≤ a * b)
    (hV : Vc = q * q ^ (2 * m)) : q ^ 4 * c ≤ q ^ (2 * m) := by
  subst he
  have hqpos : 0 < q := by omega
  have hVpos : 0 < Vc := by rw [hV]; positivity
  have h1 : q ^ 5 * (Vc * c) ≤ Vc * Vc := by
    calc q ^ 5 * (Vc * c) = (q ^ 2) ^ 2 * (f * q) * q := by rw [hf]; ring
      _ = ((q ^ 2) ^ 2 * f) * (q * q) := by ring
      _ ≤ (a * b) * (q * q) := Nat.mul_le_mul_right _ hkey
      _ = (q * a) * (b * q) := by ring
      _ = Vc * Vc := by rw [ha, hb]
  have h2 : q ^ 5 * c ≤ Vc := by
    refine Nat.le_of_mul_le_mul_left ?_ hVpos
    calc Vc * (q ^ 5 * c) = q ^ 5 * (Vc * c) := by ring
      _ ≤ Vc * Vc := h1
  have h3 : q * (q ^ 4 * c) ≤ q * q ^ (2 * m) := by
    calc q * (q ^ 4 * c) = q ^ 5 * c := by ring
      _ ≤ Vc := h2
      _ = q * q ^ (2 * m) := hV
  exact Nat.le_of_mul_le_mul_left h3 hqpos


theorem step78_of_data {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    [CharP K 2] {Q₀ : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q₀ X) (hQ : (polarBilin Q₀).Nondegenerate) (h4 : 4 ≤ Fintype.card ι)
    {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) {n m : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hm : 2 ≤ m) (h52c : Stroth52cStatement) (hZV : Sec7ZVStatement)
    {L₂ A₁ A₂ : Subgroup G}
    (hd : IsOppDecomp (Wt Q (Vt M (LB M Q B) B Z t)) (Vt M (LB M Q B) B Z t) (LB M Q B) L₂ A₁ A₂)
    (hNW : ∀ k ∈ hc.CN t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅k, y⁆ ∈ Vt M (LB M Q B) B Z t)
    (hL₂R : L₂ ≤ Rt M (LB M Q B) t)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    (hNφ : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    (hsec : SectionAct K (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z φ
      (fun g => (g : Matrix ι ι K)))
    (hKZ : Nat.card K = Nat.card Z)
    {u u' : ι → K} (hu : Q₀ u = 0) (hu' : Q₀ u' = 0) (hu0 : u ≠ 0) (huu' : polar Q₀ u u' ≠ 0)
    (hL₁ : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u)
    (hL₂ : (L₂.subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u')
    (hV : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card Z ^ (2 * m))
    (hbig : 6 ≤ Fintype.card ι ∨ ∀ β : ↥(Rt M (LB M Q B) t), (β : G) ∈ LB M Q B →
      (β : G) ∉ hc.CN t → ∃ v, polar Q₀ v ((φ β : Matrix ι ι K) *ᵥ v) ≠ 0)
    (ha : Conc71a hc t) : 2 * n + 16 ≤ 12 * m := by
  classical
  obtain ⟨s, hsR, hsc, g, hg, hgL, hgN⟩ := ha
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq : 1 < Nat.card Z := by omega
  have hQc : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.toSec5.width
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hūR : g * s * g⁻¹ ∈ Rt M (LB M Q B) t := hLR hgL
  set β : ↥(Rt M (LB M Q B) t) := ⟨g * s * g⁻¹, hūR⟩ with hβdef
  have hβG : (β : G) = g * s * g⁻¹ := rfl
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV' : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hZQ : Z ≤ Q := hc.Z_le_Q
  obtain ⟨Z0, hZ0⟩ := Ctx.exists_centre hc ht
  have hsZ0 : s ∈ Z0 := (hZ0 s).mpr ⟨hsR, hsc⟩
  have hsQ : s ∉ Q := fun hsQ' =>
    hgN (hc.Q_le_CN ht (mem_Q_conj_of_mem_M hc hg hsQ'))
  have hUtcard : Nat.card ↥(Ut Q Z (g * s * g⁻¹)) = Nat.card ↥(Vt M (LB M Q B) B Z t) := by
    rw [card_Ut_conj hc hg s, hZV G M Q Z B hc n t hs Z0 hZ0 s hsZ0 hsQ]
  have hSecQ : SecHyp (Rt M (LB M Q B) t) Q Z := sec7ctr_secHyp hc hRM
  obtain ⟨Md, iA, iD, κ, hκ⟩ := exists_sectionModule hSecQ
  haveI : Finite Md := hκ.finite
  have hP := hSecQ.normP
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := hd.1.trans hd.2.1
  have hZW : Z ≤ Wt Q (Vt M (LB M Q B) B Z t) := Z_le_Wt_of_le_Q hc hVQ
  have hchi := h52c G M Q Z B hc n t hs.toSec5 hs.omegaNat (Rt M (LB M Q B) t)
    (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl
  obtain ⟨ε, -, hεker, hεrange, hεR⟩ := exists_chi_endo hκ hchi hVQ hZW hZV' hP
  set T : Md →+ Md := comm Md β with hT
  have hcomm : ∀ x, T (ε x) = ε (T x) := by
    intro x
    simp only [hT, comm_apply, map_sub, hεR]
  have hle : ε.range ≤ ε.ker := by
    rw [hεker, hεrange]
    exact secSub_mono hVW
  have key := step78_module_ineq T ε hcomm hle
  have hVinv : ∀ x ∈ Vt M (LB M Q B) B Z t, (β : G) * x * (β : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht β.2) x).mp hx
  have hWinv : ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t),
      (β : G) * x * (β : G)⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
    fun x hx => sec7WVOrd_conj_mem hc ht β.2 hx
  have hWinv' : ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t),
      (β : G)⁻¹ * x * (β : G) ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
    intro x hx
    have := sec7WVOrd_conj_mem hc ht ((Rt M (LB M Q B) t).inv_mem β.2) hx
    simpa using this
  have hWcomm : ⁅Wt Q (Vt M (LB M Q B) B Z t), Subgroup.zpowers (β : G)⁆ ≤
      Wt Q (Vt M (LB M Q B) B Z t) := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hk : (β : G) ^ k ∈ Rt M (LB M Q B) t := zpow_mem β.2 k
    have e : ⁅x, (β : G) ^ k⁆ = x * ((β : G) ^ k * x⁻¹ * ((β : G) ^ k)⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Wt Q (Vt M (LB M Q B) B Z t)).mul_mem hx
      (sec7WVOrd_conj_mem hc ht hk ((Wt Q (Vt M (LB M Q B) B Z t)).inv_mem hx))
  obtain ⟨c, Y, hcW, hcV, hY, hYc⟩ := step78_core E hQ h4 φ hφ hNφ hsec hZV' hd
    (fun r hr x hx => sec7WVOrd_conj_mem hc ht hr hx)
    (fun r hr x hx => (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hr) x).mp hx)
    hNW hLR hL₂R hu hu' hu0 huu' hL₁ hL₂ (β := β) hgL hgN
    (hbig.imp_right (fun h => h β hgL hgN))
  have ha : Nat.card Z * Nat.card ↥T.range = Nat.card ↥(Vt M (LB M Q B) B Z t) := by
    have h1 := natCard_commutator_sup hκ hP hZQ β
    have h2 : Nat.card ↥(Ut Q Z (β : G)) = Nat.card ↥(Vt M (LB M Q B) B Z t) := by
      rw [hβG]
      exact hUtcard
    exact h1.symm.trans h2
  have hb : Nat.card ↥(secSub κ (Vt M (LB M Q B) B Z t)) * Nat.card Z =
      Nat.card ↥(Vt M (LB M Q B) B Z t) := natCard_secSub_mul hZQ hκ hZV' hVQ
  have he : Nat.card Z * Nat.card ↥(ε.range.map T) = Nat.card Z * Nat.card K ^ 2 := by
    have h1 := natCard_commutator_sup_of_le hκ hP hZV' hVQ β hVinv
    rw [hεrange]
    exact h1.symm.trans hcV
  have he' : Nat.card ↥(ε.range.map T) = Nat.card Z ^ 2 := by
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < Nat.card Z) he
    rw [this, hKZ]
  have hf : Nat.card ↥(ε.ker.map T ⊔ ε.range) * Nat.card Z =
      Nat.card ↥(⁅Wt Q (Vt M (LB M Q B) B Z t), Subgroup.zpowers (β : G)⁆ ⊔
        Vt M (LB M Q B) B Z t) := by
    have h1 := secSub_commutator_sup hκ hP hZW hWQ β hWinv hWinv'
    have hZU : Z ≤ ⁅Wt Q (Vt M (LB M Q B) B Z t), Subgroup.zpowers (β : G)⁆ ⊔
        Vt M (LB M Q B) B Z t := hZV'.trans le_sup_right
    have hUQ : ⁅Wt Q (Vt M (LB M Q B) B Z t), Subgroup.zpowers (β : G)⁆ ⊔
        Vt M (LB M Q B) B Z t ≤ Q := sup_le (hWcomm.trans hWQ) hVQ
    have h2 : ε.ker.map T ⊔ ε.range = secSub κ (⁅Wt Q (Vt M (LB M Q B) B Z t),
        Subgroup.zpowers (β : G)⁆ ⊔ Vt M (LB M Q B) B Z t) := by
      rw [hεker, hεrange, ← h1, ← secSub_sup (sup_le (hWcomm.trans hWQ) hZQ) hVQ, sup_assoc,
        sup_eq_right.mpr hZV']
    rw [h2]
    exact natCard_secSub_mul hZQ hκ hZU hUQ
  have hε : Nat.card ↥ε.range = Nat.card ↥(secSub κ (Vt M (LB M Q B) B Z t)) := by
    rw [hεrange]
  rw [hε] at key
  have hVc : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card Z ^ (2 * m) := hV
  have hf' : Nat.card ↥(ε.ker.map T ⊔ ε.range) * Nat.card Z =
      Nat.card ↥(Vt M (LB M Q B) B Z t) * c := hf.trans hcW
  have h1 : Nat.card Z ^ 4 * c ≤ Nat.card Z ^ (2 * m) :=
    step78_arith2 hq ha hb he' hf' key hVc
  haveI : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hVQ hv)))
  have hcQ := card_mul_card_of_isChiIso hchi hWQ hZV'
  have h2 : Nat.card Z ^ (2 * n + 2) = Nat.card Z ^ (4 * m + 2) * Y := by
    have e1 : Nat.card Z ^ (2 * n + 2) = Nat.card Q * Nat.card Z := by
      rw [hQc]
      ring
    rw [e1, hcQ, hY, hVc]
    ring
  exact step78_arith (by omega) hm h1 h2 hYc

theorem step78Ineq_of (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (h52c : Stroth52cStatement)
    (hZV : Sec7ZVStatement) : Step78IneqStatement := by
  intro G _ _ M Q Z B hc n t hs ha m hm htype
  classical
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq : 1 < Nat.card Z := by omega
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) :=
    hc.LB_conj (hc.Rt_le_M t hr.mem)
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    le_sup_right.trans hr.gen.ge
  obtain ⟨-, hNW⟩ := h52a G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (hc.CN t) (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t))
    rfl rfl rfl rfl
  have hd := h52b G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t)
    (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl rfl
  have hV := n12N_card_V hc t m hm htype
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
  rcases hcases with
    ⟨m', hm', φ, u, u', hu, hu', hu0, -, huu', hrange, hker, hsec, hLu, hLu'⟩ |
    ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩
  · have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    exact step78_of_data (ElemMatrixIso.plus hm') (nondegenerate_polarBilin_quadPlus m' K)
      (by rw [hι]; omega) hc hs hm h52c hZV hd hNW hL2R φ hrange hker hsec hKZ hu hu' hu0 huu'
      (by rw [ElemMatrixIso.LomGL_plus hm']; exact hLu)
      (by rw [hLA, ElemMatrixIso.LomGL_plus hm']; exact hLu') hV
      (Or.inl (by rw [hι]; omega)) ha
  · have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    have hQnd := nondegenerate_polarBilin_quadMinus_of_finite m' K hirr
    have hL₁ : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ =
        (ElemMatrixIso.minus hm' hirr).LomGL u := by
      rw [ElemMatrixIso.LomGL_minus hm' hirr]
      exact hLu
    have hL₂ : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
        (ElemMatrixIso.minus hm' hirr).LomGL u' := by
      rw [hLA, ElemMatrixIso.LomGL_minus hm' hirr]
      exact hLu'
    by_cases h3 : 3 ≤ m'
    · exact step78_of_data (ElemMatrixIso.minus hm' hirr) hQnd (by rw [hι]; omega) hc hs hm h52c
        hZV hd hNW hL2R φ hrange hker hsec hKZ hu hu' hu0 huu' hL₁ hL₂ hV
        (Or.inl (by rw [hι]; omega)) ha
    · have hm2 : m' = 2 := by omega
      subst hm2
      refine step78_of_data (ElemMatrixIso.minus hm' hirr) hQnd (by rw [hι]) hc hs hm h52c hZV hd
        hNW hL2R φ hrange hker hsec hKZ hu hu' hu0 huu' hL₁ hL₂ hV (Or.inr ?_) ha
      intro β hβL hβN
      have hβR : (β : G) ∈ Rt M (LB M Q B) t := β.2
      have hmem : φ β ∈ (ElemMatrixIso.minus hm' hirr).LomGL u := by
        rw [← hL₁]
        exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hβL)
      have hne1 : φ β ≠ 1 := by
        intro h1
        have h2 : β ∈ φ.ker := MonoidHom.mem_ker.mpr h1
        rw [hker, Subgroup.mem_subgroupOf] at h2
        exact hβN h2
      have huu'' : polar (quadMinus 2 K b c) u' u ≠ 0 := by
        rw [polar_comm]
        exact huu'
      have hroot : ∀ (A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)
          (v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K), quadMinus 2 K b c v = 0 → v ≠ 0 →
            A ∈ (ElemMatrixIso.minus hm' hirr).LomGL v →
              A ∈ rootGroupGL (quadMinus 2 K b c) v := by
        intro A v hv hv0 hAv
        obtain ⟨hAX, hrest⟩ :=
          ((ElemMatrixIso.minus hm' hirr).mem_LomGL_iff_flag hQnd hv hv0).mp hAv
        exact (mem_rootGroupGL_iff hQnd hv hv0).mpr
          ⟨fun x => (ElemMatrixIso.minus hm' hirr).quad_mulVec hAX x, hrest⟩
      exact ⟨u', sec7_polar_apply_ne_zero_of_mem_rootGroupGL hirr hu' hu hu0' hu0 huu''
        (hroot _ u hu hu0 hmem) hne1⟩

end CFSG.RankThree.GF2n.Stroth80
