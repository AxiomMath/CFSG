module

public import CFSG.RankThree.GF2n.Stroth80.Sec714ModelQuad
public import CFSG.RankThree.GF2n.Stroth80.Sec714NotTwelve
import CFSG.RankThree.GF2n.Stroth80.QuadSpaceScalars
import CFSG.RankThree.GF2n.Stroth80.Sec715ZNParts
import CFSG.RankThree.GF2n.Stroth80.Sec79MinOrder
import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorSetup
import CFSG.RankThree.GF2n.Stroth80.Sec111Order
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80.S714

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement


section N12

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E} {t r : G}

theorem card_CN_eq (I : MInputs) (hs : Sec7Hyp hc 12 t) (hp4 : OmegaPlusNat hc t 4)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    Nat.card ↥(hc.CN t) = Nat.card Z0 * Nat.card Z ^ 8 := by
  have hNc := I.hNO G M Q Z B hc 12 t hs 4 (by norm_num) (Or.inl hp4)
  have hQc : Nat.card Q = Nat.card Z ^ (2 * 12 + 1) := hs.toSec5.width
  have hZc := I.hZc G M Q Z B hc 12 t hs Z0 hZ0
  have hqpos : 0 < Nat.card Z := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hqpos (4 * 4))
  rw [hNc, hZc, hQc]
  ring

theorem Z0_ne_CN (I : MInputs) (hs : Sec7Hyp hc 12 t) (hp4 : OmegaPlusNat hc t 4)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : Z0 ≠ hc.CN t := by
  intro h
  have h1 := card_CN_eq I hs hp4 hZ0
  rw [← h] at h1
  have hq : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  have hpos : 0 < Nat.card Z0 := Nat.card_pos
  have h2 : 1 < Nat.card Z ^ 8 := Nat.one_lt_pow (by norm_num) hq
  nlinarith

theorem eq_Z0_of_isCentrePre_CN (I : MInputs) (h711 : Stroth711StrongStatement)
    (h79 : Sec79MinOrderStatement) (hs : Sec7Hyp hc 12 t) (hp4 : OmegaPlusNat hc t 4)
    {Z0 Zn : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZn : IsCentrePre Zn (hc.CN t) Q) : Zn = Z0 := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hZN : Z0 ≤ hc.CN t := Z0_le_CN I hs hZ0
  have hZ0Zn : Z0 ≤ Zn := fun z hz =>
    (hZn z).mpr ⟨hZN hz, fun y hy => ((hZ0 z).mp hz).2 y (hCNR hy)⟩
  have hZnN : Zn ≤ hc.CN t := fun x hx => ((hZn x).mp hx).1
  have hZnne : Zn ≠ hc.CN t := fun h => h711 G M Q Z B hc 12 t hs
    ((Subgroup.commutator_le).mpr fun x hx y hy => by
      rw [← h] at hx
      exact ((hZn x).mp hx).2 y hy)
  have hZnR : ∀ s ∈ Rt M (LB M Q B) t, ∀ y ∈ Zn, s * y * s⁻¹ ∈ Zn := by
    intro s hsR y hy
    obtain ⟨hyN, hyc⟩ := (hZn y).mp hy
    refine (hZn _).mpr ⟨conj_mem_CN hc ht hsR hyN, fun x hx => ?_⟩
    have hx' : s⁻¹ * x * s⁻¹⁻¹ ∈ hc.CN t := conj_mem_CN hc ht ((Rt M (LB M Q B) t).inv_mem hsR) hx
    rw [inv_inv] at hx'
    have e : ⁅s * y * s⁻¹, x⁆ = s * ⁅y, s⁻¹ * x * s⁆ * s⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hsR)) _).mp
      (hyc _ hx')
  have hZnR' : ∀ s ∈ Rt M (LB M Q B) t, conjSubgroup s Zn = Zn := fun s hsR =>
    conjSubgroup_eq_of_le fun x hx => by
      have h1 := hZnR s hsR _ (mem_conjSubgroup.mp hx)
      simpa [mul_assoc] using h1
  by_contra hne
  have hle := (h79 G M Q Z B hc 12 t hs Z0 hZ0 Zn hZ0Zn hZnN hZnR' hne 4 (by norm_num)).2 hp4
    (by norm_num)
  rw [show (2 : ℕ) ^ (4 - 1) = 8 by norm_num, ← card_CN_eq I hs hp4 hZ0] at hle
  exact hZnne (Subgroup.eq_of_le_of_card_ge hZnN hle)

theorem bilinPhi_nondeg (I : MInputs) (h711 : Stroth711StrongStatement)
    (h79 : Sec79MinOrderStatement) (hS : IsTensorSetup hc 12 M₀ ρ b) (hs : Sec7Hyp hc 12 t)
    (hr : Sec7A hc t r) (hp4 : OmegaPlusNat hc t 4) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {x₀ y₀ : M₀.E}
    (hγ : Tim79.GammaReg (bar M Q (hc.CN t)) (bar M Q Z0) (gammaFun ρ x₀ y₀))
    (e : ↥(phiSub I hS hs hr)) (he : ∀ f, bilinPhi I hS hs hr x₀ y₀ e f = 0) : e = 0 := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨Zn, hZn⟩ := exists_isCentrePre (sec8_Q_le_CN hc ht)
  have hZnZ0 := eq_Z0_of_isCentrePre_CN I h711 h79 hs hp4 hZ0 hZn
  have hxN : (pre I hS hs hr e : G) ∈ hc.CN t := pre_mem I hS hs hr e
  have hg := mk_pre_mem I hS hs hr e
  have hxZn : (pre I hS hs hr e : G) ∈ Zn := by
    refine (hZn _).mpr ⟨hxN, fun y hy => ?_⟩
    let ym : ↥M := ⟨y, hc.Rt_le_M t (Ctx.mem_CN.mp hy).1⟩
    have hh : (QuotientGroup.mk ym : Mbar M Q) ∈ bar M Q (hc.CN t) := mk_mem_bar ym hy
    have h1 : gammaFun ρ x₀ y₀ ⁅(QuotientGroup.mk (pre I hS hs hr e) : Mbar M Q),
        QuotientGroup.mk ym⁆ = 0 := by
      rw [gamma_comm x₀ y₀ I hS hs hr hZ0 hg hh, Fv_eq_fPhi I hS hs hr x₀ y₀ hg hh,
        piPhi_pre, ← bilinPhi_apply]
      exact he _
    have h2 := hγ.inj _ (comm_mem_bar_Z0 I hs hr hZ0 hg hh) h1
    exact (mk_commute_iff _ ym).mp (commutatorElement_eq_one_iff_mul_comm.mp h2)
  rw [hZnZ0] at hxZn
  have hxR : (QuotientGroup.mk (pre I hS hs hr e) : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t) :=
    mk_mem_bar _ (Ctx.mem_CN.mp hxN).1
  apply Subtype.ext
  rw [Submodule.coe_zero, ← delta_pre I hS hs hr e]
  exact (delta_eq_zero_iff I.hCRW I.hMp hS hs hZ0 hxR).mpr (mk_mem_bar _ hxZn)

theorem finrank_phiSub (I : MInputs) (hS : IsTensorSetup hc 12 M₀ ρ b) (hs : Sec7Hyp hc 12 t)
    (hr : Sec7A hc t r) (hp4 : OmegaPlusNat hc t 4) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    Module.finrank K ↥(phiSub I hS hs hr) = 8 := by
  have h1 := card_deltaGrp_mul I.h310chi I.h52a I.hCRW I.hMp hS hs hr hZ0 le_rfl
    (Z0_le_CN I hs hZ0)
  rw [card_CN_eq I hs hp4 hZ0] at h1
  have hZ0pos : 0 < Nat.card Z0 := Nat.card_pos
  have h2 : Nat.card ↥(phiSub I hS hs hr) = Nat.card K ^ 8 := by
    have h3 : Nat.card ↥(phiSub I hS hs hr) =
        Nat.card ↥(deltaGrp I.h310chi I.h52a hS hs hr (hc.CN t) le_rfl) := rfl
    rw [h3, hS.card]
    apply Nat.eq_of_mul_eq_mul_right hZ0pos
    rw [h1]
    ring
  have h4 : Nat.card ↥(phiSub I hS hs hr) =
      Nat.card K ^ Module.finrank K ↥(phiSub I hS hs hr) := Module.natCard_eq_pow_finrank
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  exact Nat.pow_right_injective hK2 (h4.symm.trans h2)

theorem mem_CN_of_psiPhi_eq_one (I : MInputs) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (hS : IsTensorSetup hc 12 M₀ ρ b)
    (hs : Sec7Hyp hc 12 t) (hr : Sec7A hc t r) (hp4 : OmegaPlusNat hc t 4) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (h : ↥(bar M Q (Rt M (LB M Q B) t)))
    (h1 : psiPhi I hS hs hr h = 1) : (h : Mbar M Q) ∈ bar M Q (hc.CN t) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hnormQ : ∀ s ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, s * y * s⁻¹ ∈ Q := fun s hsR y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hsR)) y).mp hy
  have hQZ0 : Q ≤ Z0 := hZ0.Q_le (hc.Q_le_Rt ht) hnormQ
  obtain ⟨y, hyR, hy⟩ := exists_of_mem_bar h.2
  have hhR : (h : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t) := h.2
  have hcomm : ∀ x ∈ hc.CN t, ⁅(y : G), x⁆ ∈ Z0 := by
    intro x hx
    let xm : ↥M := ⟨x, hc.Rt_le_M t (Ctx.mem_CN.mp hx).1⟩
    have hg : (QuotientGroup.mk xm : Mbar M Q) ∈ bar M Q (hc.CN t) := mk_mem_bar xm hx
    have hgR : (QuotientGroup.mk xm : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t) :=
      mk_mem_bar xm (Ctx.mem_CN.mp hx).1
    have hcg := conj_mem_bar_CN hs hhR hg
    have hginv : (QuotientGroup.mk xm : Mbar M Q)⁻¹ ∈ bar M Q (hc.CN t) :=
      Subgroup.inv_mem _ hg
    have e1 : delta hS t ((h : Mbar M Q) * QuotientGroup.mk xm * (h : Mbar M Q)⁻¹)
        (mem_bar_H0_of_CN hcg) = delta hS t (QuotientGroup.mk xm) (mem_bar_H0_of_CN hg) := by
      have e : ((psiPhi I hS hs hr h ⟨_, delta_mem_phiSub I hS hs hr hg⟩ :
          ↥(phiSub I hS hs hr)) : ↥(wsub hS t) →ₗ[K] M₀.E) =
          delta hS t (QuotientGroup.mk xm) (mem_bar_H0_of_CN hg) := by
        rw [h1]
        rfl
      rw [psiPhi_apply_coe, conjHom_delta] at e
      exact e
    have hcR : ⁅(h : Mbar M Q), QuotientGroup.mk xm⁆ ∈ bar M Q (Rt M (LB M Q B) t) := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hhR hgR)
        (Subgroup.inv_mem _ hhR)) (Subgroup.inv_mem _ hgR)
    have e2 : delta hS t ⁅(h : Mbar M Q), QuotientGroup.mk xm⁆ (mem_bar_H0_of_Rt hc hcR) = 0 := by
      have e3 := delta_mul I.h310chi I.h52a hS hs hr hcg hginv
      have e4 := delta_mul I.h310chi I.h52a hS hs hr hg hginv
      have e5 : delta hS t ((QuotientGroup.mk xm : Mbar M Q) * (QuotientGroup.mk xm)⁻¹)
          (Subgroup.mul_mem _ (mem_bar_H0_of_CN hg) (mem_bar_H0_of_CN hginv)) = 0 := by
        refine LinearMap.ext fun w => ?_
        rw [delta_apply, LinearMap.zero_apply, mul_inv_cancel]
        exact dmap_one (w : M₀.E)
      rw [e5] at e4
      rw [delta_congr hS t (commutatorElement_def _ _) _
        (Subgroup.mul_mem _ (mem_bar_H0_of_CN hcg) (mem_bar_H0_of_CN hginv)), e3, e1, ← e4]
    have hcZ : ⁅(h : Mbar M Q), QuotientGroup.mk xm⁆ ∈ bar M Q Z0 :=
      (delta_eq_zero_iff I.hCRW I.hMp hS hs hZ0 hcR).mp e2
    have e6 : ⁅(h : Mbar M Q), QuotientGroup.mk xm⁆ = (QuotientGroup.mk ⁅y, xm⁆ : Mbar M Q) := by
      rw [← hy]
      simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [e6] at hcZ
    exact (mk_mem_bar_iff_sec4 (M := M) hQZ0 ⁅y, xm⁆).mp hcZ
  have hJR : ∀ s ∈ Rt M (LB M Q B) t, ∀ z ∈ Z0, s * z * s⁻¹ ∈ Z0 := fun s hsR z hz =>
    (Subgroup.mem_normalizer_iff.mp (hZ0.mem_normalizer hnormQ hsR) z).mp hz
  have hyN : (y : G) ∈ hc.CN t :=
    (sec7_comm_mem_iff_mem_omegaPlus I.h51 hA hPts hc hs hZ0 le_rfl (Z0_le_CN I hs hZ0)
      (Z0_ne_CN I hs hp4 hZ0) hJR (by norm_num) hp4 y hyR).mp hcomm
  rw [← hy]
  exact mk_mem_bar y hyN

end N12

theorem sec714Model_of (I : MInputs) (h711 : Stroth711StrongStatement)
    (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement) :
    Sec714ModelStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp4 hn Z0 hZ0 K' _ _ hK'
  subst hn
  classical
  have h79 : Sec79MinOrderStatement := sec79MinOrder_of I.h51 hA hPts
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨K, hF, hFin, γ₀, M₀, ρ, b, hS⟩ := tensorSetup_of_34 I.h34 G M Q Z B hc 12
    hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen
  obtain ⟨r, hr⟩ := hA G M Q Z B hc 12 t hs
  let tm : ↥M := ⟨t, hc.LB_le_M ht⟩
  obtain ⟨x₀, y₀, hxy⟩ := exists_xy I hS hs tm rfl
  obtain ⟨e, -, he, -⟩ := hc.hyp.cp
  haveI hchar : CharP K 2 := charP_two_of_card_eq_two_pow (hS.card.trans he)
  have hγ := gammaReg I hS hs hr tm rfl hZ0 hxy
  have hnd := bilinPhi_nondeg I h711 h79 hS hs hr hp4 hZ0 hγ
  let M₁ := quadModelPhi I hS hs hr x₀ y₀ hZ0 hnd
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype K' := Fintype.ofFinite K'
  have hcard : Fintype.card K' = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK', hS.card]
  let θ : K' ≃+* K := FiniteField.ringEquivOfCardEq hcard
  obtain ⟨E', _, _, _, j, B', Qf', ρ', -, hB', hQf', hρ', hρQ', halt', hnd', hsmul', hadd',
    hfin'⟩ := exists_quadSpace_ringEquiv (E := ↥(phiSub I hS hs hr)) θ
      (bilinPhi I hS hs hr x₀ y₀) (quadPhi I hS hs hr x₀ y₀) M₁.alt M₁.nondeg M₁.Qf_smul
      M₁.Qf_add (psiPhi I hS hs hr) (fun a v => quadPhi_psi I hS hs hr x₀ y₀ hZ0 a v)
  refine ⟨fun g => θ.symm (gammaFun ρ x₀ y₀ g),
    { E := E'
      π := fun g => j (piPhi I hS hs hr g)
      B := B'
      Qf := Qf'
      π_mul := fun x hx y hy => (congrArg j (M₁.π_mul x hx y hy)).trans (map_add j _ _)
      π_surj := fun v => by
        obtain ⟨x, hx, hxv⟩ := M₁.π_surj (j.symm v)
        exact ⟨x, hx, (congrArg j hxv).trans (j.apply_symm_apply v)⟩
      π_ker := fun x hx => j.map_eq_zero_iff.trans (M₁.π_ker x hx)
      comm_mem := M₁.comm_mem
      sq_mem := M₁.sq_mem
      comm_eq := fun x hx y hy => by
        show θ.symm (gammaFun ρ x₀ y₀ ⁅x, y⁆) =
          B' (j (piPhi I hS hs hr x)) (j (piPhi I hS hs hr y))
        rw [hB']
        exact congrArg θ.symm (M₁.comm_eq x hx y hy)
      sq_eq := fun x hx => by
        show θ.symm (gammaFun ρ x₀ y₀ (x ^ 2)) = Qf' (j (piPhi I hS hs hr x))
        rw [hQf']
        exact congrArg θ.symm (M₁.sq_eq x hx)
      alt := halt'
      nondeg := hnd'
      Qf_smul := hsmul'
      Qf_add := hadd' }, ρ', ?_, ?_, ?_, ?_, hρQ', ?_⟩
  ·
    refine ⟨hγ.V_le, fun a ha c hc' => ?_, fun a ha h0 => ?_, fun s => ?_⟩
    · show θ.symm (gammaFun ρ x₀ y₀ (a * c)) =
        θ.symm (gammaFun ρ x₀ y₀ a) + θ.symm (gammaFun ρ x₀ y₀ c)
      rw [hγ.add a ha c hc', map_add]
    · exact hγ.inj a ha ((map_eq_zero_iff θ.symm θ.symm.injective).mp h0)
    · obtain ⟨a, ha, has⟩ := hγ.surj (θ s)
      exact ⟨a, ha, by
        show θ.symm (gammaFun ρ x₀ y₀ a) = s
        rw [has, RingEquiv.symm_apply_apply]⟩
  · exact charP_two_of_card_eq_two_pow (hK'.trans he)
  · rw [hfin']
    exact finrank_phiSub I hS hs hr hp4 hZ0
  · intro g x hx
    show j (piPhi I hS hs hr ((g : Mbar M Q) * x * (g : Mbar M Q)⁻¹)) =
      ρ' g (j (piPhi I hS hs hr x))
    rw [hρ', piPhi_conj I hS hs hr g hx]
  · intro g
    constructor
    · intro h1
      have h2 : psiPhi I hS hs hr g = 1 := by
        refine LinearEquiv.ext fun v => j.injective ?_
        rw [← hρ', h1]
        rfl
      exact mem_CN_of_psiPhi_eq_one I hA hPts hS hs hr hp4 hZ0 g h2
    · intro hg
      have h2 : ρ' g = 1 := by
        refine LinearEquiv.ext fun v' => ?_
        obtain ⟨v, rfl⟩ := j.surjective v'
        rw [hρ', psiPhi_eq_one I hS hs hr g hg]
        rfl
      exact h2

end CFSG.RankThree.GF2n.Stroth80.S714
