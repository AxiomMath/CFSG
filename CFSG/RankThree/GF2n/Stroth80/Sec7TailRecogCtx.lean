module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailRecogAbstract
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailOddCoreBar
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCaseA
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreeModel
public import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailFStarNormal
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailOddCent
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.VBasic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.recog_pcore_le (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))) :
    ∀ P : Subgroup (Mbar M Q), P ≤ bar M Q (NormH0 M Z Z0) →
      (∀ k ∈ bar M Q (NormH0 M Z Z0), k ∈ Subgroup.normalizer (P : Set (Mbar M Q))) →
      IsPGroup 2 P → P ≤ bar M Q (hc.CN t) := by
  intro P hP hPn hP2
  have hPnorm : (P.subgroupOf (bar M Q (NormH0 M Z Z0))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP).mpr fun k hk => hPn k hk
  have hPnil : Group.IsNilpotent ↥(P.subgroupOf (bar M Q (NormH0 M Z Z0))) :=
    ((hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hP).symm)).isNilpotent
  have := le_of_normal_nilpotent_of_fstar hPnil hF
  intro x hx
  have hx' := this (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hP hx⟩ : bar M Q (NormH0 M Z Z0)) ∈
    P.subgroupOf (bar M Q (NormH0 M Z Z0)))
  exact Subgroup.mem_subgroupOf.mp hx'

theorem Ctx.recog_cent_le (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))) :
    ∀ k ∈ bar M Q (NormH0 M Z Z0), (∀ n ∈ bar M Q (hc.CN t), k * n = n * k) →
      k ∈ bar M Q (hc.CN t) := by
  intro k hk hkc
  have hcent : (⟨k, hk⟩ : bar M Q (NormH0 M Z Z0)) ∈
      Subgroup.centralizer (generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) :
        Set ↥(bar M Q (NormH0 M Z Z0))) := by
    rw [hF]
    intro y hy
    have hy' : (y : Mbar M Q) ∈ bar M Q (hc.CN t) := Subgroup.mem_subgroupOf.mp hy
    exact Subtype.ext (hkc y hy').symm
  have h2 := CFSG.centralizer_generalizedFitting_le _ hcent
  rw [hF] at h2
  exact Subgroup.mem_subgroupOf.mp h2

theorem Ctx.recog_bar_Z0_comm (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    ∀ x ∈ bar M Q Z0, ∀ y ∈ bar M Q (Rt M (LB M Q B) t), x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
  exact step716_mk_mul_comm (hZ0.comm_mem (Subgroup.mem_subgroupOf.mp ha)
    (Subgroup.mem_subgroupOf.mp hb))

theorem Ctx.recog_odd_normal_bot (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    (hC : CentTwoInV hc t Z0)
    {O : Subgroup (Mbar M Q)} (hOle : O ≤ bar M Q (H0 M Z))
    (hOn : ∀ h ∈ bar M Q (H0 M Z), h ∈ Subgroup.normalizer (O : Set (Mbar M Q)))
    (hOodd : Odd (Nat.card O)) : O = ⊥ := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hKbar := bar_NormH0_eq hc hQZ0 hZ0M
  have hconf := hc.tiConfigC hs hZ0 hZt hZcard (sec7_CN_pgroup_bar h34 h311a hc hs) hTI hC
  exact odd_normal_eq_bot_of_cent hconf.V_le (sq_eq_one_bar hc hs hZc hZ0)
    (fun x hx y hy => Ctx.recog_bar_Z0_comm hc hZ0 x hx y (bar_mono' hZ0.le hy))
    (four_le_card_bar_Z0 hc hs hZcard hZ0) hconf.ti hconf.N_le hconf.N_normal hconf.N_pgroup
    (fun k hk hkc => Ctx.recog_cent_le hc hF k (by rw [hKbar]; exact hk) hkc) hOn hOle hOodd

theorem Ctx.recog_centralizer_normal_bot (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    (hC : CentTwoInV hc t Z0)
    {X : Subgroup (Mbar M Q)} (hXle : X ≤ bar M Q (H0 M Z))
    (hXn : ∀ h ∈ bar M Q (H0 M Z), h ∈ Subgroup.normalizer (X : Set (Mbar M Q)))
    (hVX : bar M Q Z0 ≤ X) :
    Subgroup.centralizer (X : Set (Mbar M Q)) ⊓ bar M Q (H0 M Z) = ⊥ := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hconf := hc.tiConfigC hs hZ0 hZt hZcard (sec7_CN_pgroup_bar h34 h311a hc hs) hTI hC
  have hKbar := bar_NormH0_eq hc hQZ0 hZ0M
  have hO2 : ∀ P : Subgroup (Mbar M Q), P ≤ bar M Q (H0 M Z) →
      (∀ h ∈ bar M Q (H0 M Z), h ∈ Subgroup.normalizer (P : Set (Mbar M Q))) →
      IsPGroup 2 P → P = ⊥ := fun P hPH hPn hP2 =>
    eq_bot_of_normal_pgroup_of_pCore (pCore_two_bar_H0_eq_bot hc) hPH hPn hP2
  have hO : ∀ P : Subgroup (Mbar M Q), P ≤ bar M Q (H0 M Z) →
      (∀ h ∈ bar M Q (H0 M Z), h ∈ Subgroup.normalizer (P : Set (Mbar M Q))) →
      Odd (Nat.card P) → P = ⊥ := fun P hPH hPn hPodd =>
    Ctx.recog_odd_normal_bot h34 h311a hc hs hZ0 hZt hZcard hZc hTI hF hC hPH hPn hPodd
  refine normal_eq_bot_of_fstar (V := bar M Q Z0) (N := bar M Q (hc.CN t)) ?_ inf_le_right ?_ ?_
    hconf.N_pgroup hconf.N_le hO2 hO
  · intro h hh
    refine TIConfig.mem_normalizer_of_conj_mem fun c hc' => ?_
    obtain ⟨hcX, hcH⟩ := Subgroup.mem_inf.mp hc'
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun x hx => ?_,
      (bar M Q (H0 M Z)).mul_mem ((bar M Q (H0 M Z)).mul_mem hh hcH)
        ((bar M Q (H0 M Z)).inv_mem hh)⟩
    have hxh : h⁻¹ * x * h ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hXn h⁻¹ ((bar M Q (H0 M Z)).inv_mem hh)) x).mp hx
      simpa using this
    have hcomm := Subgroup.mem_centralizer_iff.mp hcX _ hxh
    calc x * (h * c * h⁻¹) = h * ((h⁻¹ * x * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * x * h)) * h⁻¹ := by rw [hcomm]
      _ = (h * c * h⁻¹) * x := by group
  · intro c hc'
    obtain ⟨hcX, hcH⟩ := Subgroup.mem_inf.mp hc'
    refine mem_NormIn.mpr ⟨hcH, TIConfig.mem_normalizer_of_conj_mem fun v hv => ?_⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hcX v (hVX hv)
    have : c * v * c⁻¹ = v := by
      rw [show c * v * c⁻¹ = (c * v) * c⁻¹ from rfl, ← hcomm]; group
    rw [this]; exact hv
  · rw [← hKbar]; exact hF

theorem omegaPlusSix_equiv_statedProj {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    Nonempty (↥(StatedOmega (StatedQuadPlus 3 K)) ≃* StatedProj (StatedSL 4 K)) := by
  obtain ⟨eGS⟩ := nonempty_statedOmega_quadPlus_three_mulEquiv hK
  have hc : Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) = ⊥ :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 4 K).symm.trans
      (CFSG.SeitzReduction.OmegaPilot.scalars_four_eq_bot_of_charTwo K)
  let eP : Matrix.SpecialLinearGroup (Fin 4) K ≃* StatedProj (StatedSL 4 K) :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans
      (projectiveSpecialLinearGroupEquivStatedProj 4 K)
  let eS : ↥(StatedSL 4 K) ≃* StatedProj (StatedSL 4 K) :=
    (specialLinearGroupEquivStatedSL 4 K).symm.trans eP
  exact ⟨eGS.trans eS⟩

theorem Ctx.recog_quot_equiv (hc : Ctx M Q Z B) {t : G} (hp3 : OmegaPlusNat hc t 3) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀), Nat.card K₀ = Nat.card Z ∧
      ∃ _ : ((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).Normal,
        Nonempty ((↥(Rt M (LB M Q B) t) ⧸ (hc.CN t).subgroupOf (Rt M (LB M Q B) t)) ≃*
          StatedProj (StatedSL 4 K₀)) := by
  obtain ⟨K₀, hf, hfin, hcard, φ, hrange, hker, -⟩ := hp3
  obtain ⟨g, k, hg, -⟩ := hc.hyp.cp
  haveI : CharP K₀ 2 := charP_two_of_card_eq_two_pow (hcard.trans hg)
  have h4 : 4 ≤ Nat.card K₀ := by rw [hcard]; exact hc.hyp.q4
  obtain ⟨eΩ⟩ := omegaPlusSix_equiv_statedProj (K := K₀) h4
  have hnorm : ((hc.CN t).subgroupOf (Rt M (LB M Q B) t)).Normal := by
    rw [← hker]
    exact MonoidHom.normal_ker φ
  refine ⟨K₀, hf, hfin, hcard, hnorm, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange φ)).trans ((MulEquiv.subgroupCongr hrange).trans eΩ)

theorem mem_Q_of_mk_mul_comm {a b : M}
    (h : QuotientGroup.mk' (Q.subgroupOf M) a * QuotientGroup.mk' (Q.subgroupOf M) b =
      QuotientGroup.mk' (Q.subgroupOf M) b * QuotientGroup.mk' (Q.subgroupOf M) a) :
    ⁅(a : G), (b : G)⁆ ∈ Q := by
  have h1 : QuotientGroup.mk' (Q.subgroupOf M) ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr h
  have h2 : ⁅a, b⁆ ∈ Q.subgroupOf M := (QuotientGroup.eq_one_iff _).mp h1
  have := Subgroup.mem_subgroupOf.mp h2
  simpa [commutatorElement_def] using this

theorem quotEquiv_of_surj_aux {G Y : Type} [Group G] [Group Y] {R N : Subgroup G}
    [hN : (N.subgroupOf R).Normal] (θ : ↥R →* Y) (hθ : Function.Surjective θ)
    (K : Subgroup Y) (hK : ∀ r : ↥R, θ r ∈ K ↔ (r : G) ∈ N) :
    ∃ _ : K.Normal, Nonempty ((Y ⧸ K) ≃* (↥R ⧸ N.subgroupOf R)) := by
  have hnorm : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨r₀, rfl⟩ := hθ g
    obtain ⟨m, rfl⟩ := hθ n
    have hm : (m : G) ∈ N := (hK m).mp hn
    have hconj : r₀ * m * r₀⁻¹ ∈ N.subgroupOf R :=
      hN.conj_mem m (Subgroup.mem_subgroupOf.mpr hm) r₀
    have hmem : θ (r₀ * m * r₀⁻¹) ∈ K := (hK _).mpr (Subgroup.mem_subgroupOf.mp hconj)
    simpa [map_mul, map_inv] using hmem
  have hΘs : Function.Surjective ((QuotientGroup.mk' K).comp θ) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    obtain ⟨r, rfl⟩ := hθ x
    exact ⟨r, rfl⟩
  have hker : ((QuotientGroup.mk' K).comp θ).ker = N.subgroupOf R := by
    ext r
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hK r
  exact ⟨hnorm, ⟨(QuotientGroup.quotientKerEquivOfSurjective _ hΘs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩⟩

theorem nonempty_quot_equiv_bar {G : Type} [Group G]
    {M Q H R N : Subgroup G} [(Q.subgroupOf M).Normal] (hQN : Q ≤ N) (hNR : N ≤ R)
    (hRH : R ≤ H) (hHM : H ≤ M)
    [hN' : (N.subgroupOf R).Normal] {A : Type*} [Group A]
    (h : Nonempty ((↥R ⧸ N.subgroupOf R) ≃* A)) :
    ∃ _ : (((bar M Q N).subgroupOf (bar M Q H)).subgroupOf
          ((bar M Q R).subgroupOf (bar M Q H))).Normal,
      Nonempty ((↥((bar M Q R).subgroupOf (bar M Q H)) ⧸
        ((bar M Q N).subgroupOf (bar M Q H)).subgroupOf
          ((bar M Q R).subgroupOf (bar M Q H))) ≃* A) := by
  obtain ⟨eA⟩ := h
  have hQR : Q ≤ R := hQN.trans hNR
  have hQH : Q ≤ H := hQR.trans hRH
  have hRM : R ≤ M := hRH.trans hHM
  have hmemH : ∀ r : ↥R, QuotientGroup.mk' (Q.subgroupOf M) (⟨(r : G), hRM r.2⟩ : ↥M) ∈
      bar M Q H :=
    fun r => (mk_mem_bar_iff_sec4 hQH (⟨(r : G), hRM r.2⟩ : ↥M)).mpr (hRH r.2)
  have hmemR : ∀ r : ↥R, QuotientGroup.mk' (Q.subgroupOf M) (⟨(r : G), hRM r.2⟩ : ↥M) ∈
      bar M Q R :=
    fun r => (mk_mem_bar_iff_sec4 hQR (⟨(r : G), hRM r.2⟩ : ↥M)).mpr r.2
  let f : ↥R →* ↥M ⧸ Q.subgroupOf M :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hRM)
  let θ₁ : ↥R →* ↥(bar M Q H) := f.codRestrict (bar M Q H) hmemH
  let θ : ↥R →* ↥((bar M Q R).subgroupOf (bar M Q H)) :=
    θ₁.codRestrict ((bar M Q R).subgroupOf (bar M Q H))
      (fun r => Subgroup.mem_subgroupOf.mpr (hmemR r))
  have hθ : ∀ r : ↥R,
      (θ r).1.1 = QuotientGroup.mk' (Q.subgroupOf M) (⟨(r : G), hRM r.2⟩ : ↥M) :=
    fun r => rfl
  have hθs : Function.Surjective θ := by
    intro x
    have hx : x.1.1 ∈ (R.subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M)) :=
      Subgroup.mem_subgroupOf.mp x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyR : (y : G) ∈ R := Subgroup.mem_subgroupOf.mp hy
    refine ⟨⟨(y : G), hyR⟩, Subtype.ext (Subtype.ext ?_)⟩
    rw [hθ]
    exact hyx
  have hkey : ∀ r : ↥R, θ r ∈ ((bar M Q N).subgroupOf (bar M Q H)).subgroupOf
      ((bar M Q R).subgroupOf (bar M Q H)) ↔ (r : G) ∈ N := by
    intro r
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hθ]
    exact mk_mem_bar_iff_sec4 hQN (⟨(r : G), hRM r.2⟩ : ↥M)
  obtain ⟨hK, ⟨e⟩⟩ := quotEquiv_of_surj_aux θ hθs
    (((bar M Q N).subgroupOf (bar M Q H)).subgroupOf ((bar M Q R).subgroupOf (bar M Q H))) hkey
  exact ⟨hK, ⟨e.trans eA⟩⟩

theorem sec717Recog_of_inputs (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (h78 : Stroth78Statement) (hY : Sec713YStatement)
    (hCorB' : CorollaryBStmt) (hOut : OutSolvableListStatement)
    (hRank : TwoRankSporadicAltStatement) (hBorel : BorelRankOneSolvableStatement)
    (hArtin : ArtinLinearOrdersStatement) (hRad : RadicalTwoSubgroupLinearStatement) :
    Sec717RecogStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZNc hTI hF hC L hL hLn hCorB
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hnormR : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hRK : Rt M (LB M Q B) t ≤ NormH0 M Z Z0 := fun ρ hρ =>
    Subgroup.mem_inf.mpr ⟨hc.Rt_le_H0 t hρ, IsCentrePre.mem_normalizer hZ0 hnormR hρ⟩
  have hQK : Q ≤ NormH0 M Z Z0 := fun q hq =>
    Subgroup.mem_inf.mpr ⟨hQH hq, Subgroup.le_normalizer (hQZ0 hq)⟩
  have hZ0H0 : Z0 ≤ H0 M Z := hZ0.le.trans (hc.Rt_le_H0 t)
  have hZ0N : Z0 ≤ hc.CN t := sec7ctr_Z0_le_CN hc hs hZ0
  have hQL : Q ≤ L := hL.1
  have hLN : L ≤ hc.CN t := hL.2.1
  have hZ0L : Z0 ≤ L := hL.2.2.2.2.2
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hHM : H0 M Z ≤ M := fun x hx => hx.1
  have hKbar := bar_NormH0_eq hc hQZ0 hZ0M
  have hN2 := sec7_CN_pgroup_bar h34 h311a hc hs
  have hconf := hc.tiConfigC hs hZ0 hZt hZcard hN2 hTI hC
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ g : ℕ, Nat.card Z = 2 ^ g := by
    obtain ⟨g, k, hg, -⟩ := hc.hyp.cp
    exact ⟨g, hg⟩
  set Hb : Subgroup (Mbar M Q) := bar M Q (H0 M Z) with hHb
  have hO2y : ∀ P : Subgroup ↥Hb, P.Normal → IsPGroup 2 P → P = ⊥ := by
    intro P hP hP2
    have hle : P ≤ pCore 2 ↥Hb := le_sSup ⟨hP, hP2⟩
    rw [pCore_two_bar_H0_eq_bot hc] at hle
    exact le_bot_iff.mp hle
  have hOy : ∀ P : Subgroup ↥Hb, P.Normal → Odd (Nat.card P) → P = ⊥ := by
    intro P hP hPodd
    have hPn : ∀ h ∈ Hb, h ∈ Subgroup.normalizer ((P.map Hb.subtype : Subgroup (Mbar M Q)) :
        Set (Mbar M Q)) := fun h hh => mem_normalizer_map_of_normal P hh
    have hodd' : Odd (Nat.card ↥(P.map Hb.subtype)) := by
      rw [← Nat.card_congr (P.equivMapOfInjective Hb.subtype Hb.subtype_injective).toEquiv]
      exact hPodd
    have := Ctx.recog_odd_normal_bot h34 h311a hc hs hZ0 hZt hZcard hZc hTI hF hC
      (Subgroup.map_subtype_le P) hPn hodd'
    exact (Subgroup.map_eq_bot_iff_of_injective P Hb.subtype_injective).mp this
  have hCy : ∀ X : Subgroup ↥Hb, X.Normal → (bar M Q Z0).subgroupOf Hb ≤ X →
      ∀ c : ↥Hb, (∀ x ∈ X, c * x = x * c) → c = 1 := by
    intro X hX hVX c hcX
    have hX' : X.map Hb.subtype ≤ Hb := Subgroup.map_subtype_le X
    have hn : ∀ h ∈ Hb, h ∈ Subgroup.normalizer ((X.map Hb.subtype : Subgroup (Mbar M Q)) :
        Set (Mbar M Q)) := fun h hh => mem_normalizer_map_of_normal X hh
    have hV' : bar M Q Z0 ≤ X.map Hb.subtype := by
      intro v hv
      have hvH : v ∈ Hb := bar_mono' hZ0H0 hv
      exact ⟨⟨v, hvH⟩, hVX (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
    have hbot := Ctx.recog_centralizer_normal_bot h34 h311a hc hs hZ0 hZt hZcard hZc hTI hF hC
      hX' hn hV'
    have hc' : (c : Mbar M Q) ∈ Subgroup.centralizer ((X.map Hb.subtype : Subgroup (Mbar M Q)) :
        Set (Mbar M Q)) ⊓ Hb := by
      refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, c.2⟩
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hcX x hx).symm
    rw [hbot, Subgroup.mem_bot] at hc'
    exact Subtype.ext hc'
  set Vy : Subgroup ↥Hb := (bar M Q Z0).subgroupOf Hb with hVy
  set Ly : Subgroup ↥Hb := (bar M Q L).subgroupOf Hb with hLy
  set Ny : Subgroup ↥Hb := (bar M Q (hc.CN t)).subgroupOf Hb with hNy
  set Ry : Subgroup ↥Hb := (bar M Q (Rt M (LB M Q B) t)).subgroupOf Hb with hRy
  set Ky : Subgroup ↥Hb := (bar M Q (NormH0 M Z Z0)).subgroupOf Hb with hKy
  have hVH : bar M Q Z0 ≤ Hb := bar_mono' hZ0H0
  have hNH : bar M Q (hc.CN t) ≤ Hb := bar_mono' (hNR.trans hRH)
  have hRH' : bar M Q (Rt M (LB M Q B) t) ≤ Hb := bar_mono' hRH
  have hLH' : bar M Q L ≤ Hb := bar_mono' ((hLN.trans hNR).trans hRH)
  have hVLy : Vy ≤ Ly := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (bar_mono' hZ0L (Subgroup.mem_subgroupOf.mp hx))
  have hLNy : Ly ≤ Ny := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (bar_mono' hLN (Subgroup.mem_subgroupOf.mp hx))
  have hNRy : Ny ≤ Ry := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (bar_mono' hNR (Subgroup.mem_subgroupOf.mp hx))
  have hRKy : Ry ≤ Ky := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (bar_mono' hRK (Subgroup.mem_subgroupOf.mp hx))
  have hKV : ∀ g ∈ Subgroup.normalizer (Vy : Set ↥Hb), g ∈ Ky := by
    intro g hg
    rw [hVy, ← Subgroup.subgroupOf_normalizer_eq hVH] at hg
    have hgn : (g : Mbar M Q) ∈
        Subgroup.normalizer ((bar M Q Z0 : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := hg
    have : (g : Mbar M Q) ∈ bar M Q (NormH0 M Z Z0) := by
      rw [hKbar]
      exact mem_NormIn.mpr ⟨g.2, hgn⟩
    exact this
  have hN2y : IsPGroup 2 ↥Ny := hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hNn : ∀ k ∈ Ky, k ∈ Subgroup.normalizer (Ny : Set ↥Hb) := by
    intro k hk
    have hk' : (k : Mbar M Q) ∈ NormIn Hb (bar M Q Z0) := by
      rw [← hKbar]
      exact Subgroup.mem_subgroupOf.mp hk
    have h1 := hconf.N_normal k hk'
    rw [hNy, ← Subgroup.subgroupOf_normalizer_eq hNH]
    exact h1
  have hRn : ∀ k ∈ Ky, k ∈ Subgroup.normalizer (Ry : Set ↥Hb) := by
    intro k hk
    have hk' : (k : Mbar M Q) ∈ bar M Q (NormH0 M Z Z0) := Subgroup.mem_subgroupOf.mp hk
    obtain ⟨y, hyk⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (k : Mbar M Q)
    have hy' : (y : G) ∈ NormH0 M Z Z0 := (mk_mem_bar_iff_sec4 hQK y).mp (hyk ▸ hk')
    have hcR : conjSubgroup (y : G) (Rt M (LB M Q B) t) = Rt M (LB M Q B) t :=
      (sec7_normalizes_of_zt hZt hZcard hc hs hZ0 hy').1
    have hmem := mk_mem_normalizer_bar_of_normalizer hQR y (conjSubgroup_eq_self_iff.mp hcR)
    rw [hRy, ← Subgroup.subgroupOf_normalizer_eq hRH']
    show (k : Mbar M Q) ∈ Subgroup.normalizer ((bar M Q (Rt M (LB M Q B) t) :
      Subgroup (Mbar M Q)) : Set (Mbar M Q))
    rw [← hyk]
    exact hmem
  have hLnY : ∀ k ∈ Ky, k ∈ Subgroup.normalizer (Ly : Set ↥Hb) := by
    intro k hk
    have hk' : (k : Mbar M Q) ∈ bar M Q (NormH0 M Z Z0) := Subgroup.mem_subgroupOf.mp hk
    obtain ⟨y, hyk⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (k : Mbar M Q)
    have hy' : (y : G) ∈ NormH0 M Z Z0 := (mk_mem_bar_iff_sec4 hQK y).mp (hyk ▸ hk')
    have hmem := mk_mem_normalizer_bar_of_normalizer hQL y
      (conjSubgroup_eq_self_iff.mp (hLn (y : G) hy'))
    rw [hLy, ← Subgroup.subgroupOf_normalizer_eq hLH']
    show (k : Mbar M Q) ∈ Subgroup.normalizer ((bar M Q L : Subgroup (Mbar M Q)) :
      Set (Mbar M Q))
    rw [← hyk]
    exact hmem
  have hpcy : ∀ P : Subgroup ↥Hb, P ≤ Ky → (∀ k ∈ Ky, k ∈ Subgroup.normalizer (P : Set ↥Hb)) →
      IsPGroup 2 P → P ≤ Ny := by
    intro P hPK hPn hP2
    have hPK' : P.map Hb.subtype ≤ bar M Q (NormH0 M Z Z0) := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hPK hx)
    have hPn' : ∀ k ∈ bar M Q (NormH0 M Z Z0), k ∈ Subgroup.normalizer
        ((P.map Hb.subtype : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := by
      intro k hk
      have hkH : k ∈ Hb := bar_mono' (S := NormH0 M Z Z0) (T := H0 M Z) (fun x hx => hx.1) hk
      have hkn := Subgroup.mem_normalizer_iff.mp
        (hPn ⟨k, hkH⟩ (Subgroup.mem_subgroupOf.mpr hk))
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨⟨k, hkH⟩ * x * ⟨k, hkH⟩⁻¹, (hkn x).mp hx, rfl⟩
    have h1 := Ctx.recog_pcore_le hc hF _ hPK' hPn' (hP2.map Hb.subtype)
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (h1 ⟨x, hx, rfl⟩)
  have hZNy : ∀ x ∈ Ny, (∀ n ∈ Ny, x * n = n * x) → x ∈ Vy := by
    intro x hx hxc
    obtain ⟨x0, hx0⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : Mbar M Q)
    have hx0N : (x0 : G) ∈ hc.CN t :=
      (mk_mem_bar_iff_sec4 hQN x0).mp (hx0 ▸ Subgroup.mem_subgroupOf.mp hx)
    have hx0Z : (x0 : G) ∈ Z0 := by
      refine (hZNc (x0 : G)).mpr ⟨hx0N, fun r hr => ?_⟩
      have hrM : r ∈ M := hc.Rt_le_M t (hNR hr)
      have hrbar : QuotientGroup.mk' (Q.subgroupOf M) ⟨r, hrM⟩ ∈ bar M Q (hc.CN t) :=
        (mk_mem_bar_iff_sec4 hQN ⟨r, hrM⟩).mpr hr
      have hrH : QuotientGroup.mk' (Q.subgroupOf M) ⟨r, hrM⟩ ∈ Hb := hNH hrbar
      have hcomm := hxc ⟨_, hrH⟩ (Subgroup.mem_subgroupOf.mpr hrbar)
      have hcomm' : QuotientGroup.mk' (Q.subgroupOf M) x0 *
          QuotientGroup.mk' (Q.subgroupOf M) ⟨r, hrM⟩ =
          QuotientGroup.mk' (Q.subgroupOf M) ⟨r, hrM⟩ * QuotientGroup.mk' (Q.subgroupOf M) x0 := by
        have h1 := congrArg Subtype.val hcomm
        simp only [Subgroup.coe_mul] at h1
        rw [← hx0] at h1
        exact h1
      exact mem_Q_of_mk_mul_comm hcomm'
    exact Subgroup.mem_subgroupOf.mpr
      (by rw [← hx0]; exact (mk_mem_bar_iff_sec4 hQZ0 x0).mpr hx0Z)
  have hVcy : ∀ v ∈ Vy, ∀ n ∈ Ny, v * n = n * v := by
    intro v hv n hn
    apply Subtype.ext
    exact Ctx.recog_bar_Z0_comm hc hZ0 _ (Subgroup.mem_subgroupOf.mp hv) _
      (bar_mono' hNR (Subgroup.mem_subgroupOf.mp hn))
  have hVcard : Nat.card Vy = Nat.card Z := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv]
    exact card_bar_Z0 hc hs hZcard hZ0
  have hCNcard : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ 9 := by
    have h := h78 G M Q Z B hc n t hs.toSec5 hs.large hs.notPlus4 3 (by norm_num) (Or.inl hp3)
    rcases h with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | exact h | omega
  have hNcard : Nat.card Ny = Nat.card Z ^ 9 := by
    have h1 := bar_card_mul_card_of_le (M := M) (S := hc.CN t) hQN
      (fun x hx => hc.Rt_le_M t (hNR hx))
    have h2 : Nat.card (bar M Q (hc.CN t)) * Nat.card Q = Nat.card Z ^ 9 * Nat.card Q := by
      rw [h1, hCNcard, Nat.mul_comm]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hLcard : Nat.card Ly = Nat.card Z ^ 5 := by
    have h1 := bar_card_mul_card_of_le (M := M) (S := L) hQL
      (fun x hx => hc.Rt_le_M t (hNR (hLN hx)))
    have h2 : Nat.card (bar M Q L) * Nat.card Q = Nat.card Z ^ 5 * Nat.card Q := by
      rw [h1, hL.2.2.1, Nat.mul_comm]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH').toEquiv]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  obtain ⟨K₀, hKf, hKfin, hK₀, hnormN, hquot⟩ := Ctx.recog_quot_equiv hc hp3
  haveI := hnormN
  obtain ⟨hnormY, hquotY⟩ := nonempty_quot_equiv_bar (M := M) (Q := Q) (H := H0 M Z) hQN hNR
    hRH hHM hquot
  obtain ⟨y, hyR, hyQ, hy3, hyC⟩ := hY G M Q Z B hc n t hs Z0 hZ0
  have hyM : y ∈ M := hc.Rt_le_M t hyR
  have hybR : QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩ ∈ bar M Q (Rt M (LB M Q B) t) :=
    (mk_mem_bar_iff_sec4 hQR ⟨y, hyM⟩).mpr hyR
  have hybH : QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩ ∈ Hb := hRH' hybR
  have hyy : ∃ y' ∈ Ry, orderOf y' = 3 ∧ ∀ x ∈ Ny, y' * x = x * y' → x ∈ Vy := by
    refine ⟨⟨_, hybH⟩, Subgroup.mem_subgroupOf.mpr hybR, ?_, ?_⟩
    · have h3 : (⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩, hybH⟩ : ↥Hb) ^ 3 = 1 := by
        apply Subtype.ext
        show (QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩) ^ 3 = 1
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hy3))
      have hne : (⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩, hybH⟩ : ↥Hb) ≠ 1 := by
        intro h
        have h' := congrArg Subtype.val h
        exact hyQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h'))
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime h3 hne
    · intro x hx hxc
      obtain ⟨x0, hx0⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : Mbar M Q)
      have hx0N : (x0 : G) ∈ hc.CN t :=
        (mk_mem_bar_iff_sec4 hQN x0).mp (hx0 ▸ Subgroup.mem_subgroupOf.mp hx)
      have hcomm : ⁅y, (x0 : G)⁆ ∈ Q := by
        refine mem_Q_of_mk_mul_comm (a := ⟨y, hyM⟩) (b := x0) ?_
        have h1 := congrArg Subtype.val hxc
        simp only [Subgroup.coe_mul] at h1
        rw [← hx0] at h1
        exact h1
      have hx0Z : (x0 : G) ∈ Z0 := hyC _ hx0N hcomm
      exact Subgroup.mem_subgroupOf.mpr
        (by rw [← hx0]; exact (mk_mem_bar_iff_sec4 hQZ0 x0).mpr hx0Z)
  obtain ⟨K₁, hKf1, hKfin1, hK1, ⟨e⟩⟩ := recog_abstract hCorB' hOut hRank hBorel hArtin hRad
    (Nat.card Z) hq4 hq2 Vy Ly Ny Ry Ky hO2y hOy hCy hKV hVLy hLNy hNRy hRKy hN2y hpcy hNn hRn
    hLnY hZNy hVcy hVcard hNcard hLcard hCorB.1 hCorB K₀ hK₀ ⟨hnormY, hquotY⟩ hyy
  exact ⟨K₁, hKf1, hKfin1, hK1, ⟨e⟩⟩

end CFSG.RankThree.GF2n.Stroth80

