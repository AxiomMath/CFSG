module

public import CFSG.Quasithin.Vol2.Ch3E213MShare
public import CFSG.Quasithin.SteinbergBSSymplecticSection
public import CFSG.Quasithin.H13.QRCBenderAmbient
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSp4

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp antiUnipotent antiUnipotentCenter minorAut antiSpEquiv)
open CFSG.Quasithin.SteinbergBS (rootLong rootShort)
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)

variable {G : Type} [Group G]

@[expose] def kZero (H M : Subgroup G) : Subgroup (↥H ⧸ kerIn (M.subgroupOf H) ⊤) :=
  (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤))

@[expose] def coordIn {H M : Subgroup G} {k : Type} [Field k] (θ : ↥(kZero H M) ≃* antiSp k)
    (X : Subgroup G) : Subgroup (antiSp k) :=
  ((barIn M H X).subgroupOf (kZero H M)).map θ.toMonoidHom

open CFSG.Quasithin.SteinbergBS in
alias sp4Confinement :=
qrc_original_single_even_symplectic_section_confines_the_whole_image_to_both_central_root_directions

variable [Finite G]

structure Sp4Data (H T M V K : Subgroup G) (k : Type) [Field k] [Finite k] [CharP k 2] where
  θ : ↥(kZero H M) ≃* antiSp k
  ι : (↥H ⧸ kerIn (M.subgroupOf H) ⊤) →* MulAut ↥(kZero H M)
  ι_injective : Function.Injective ι
  ι_apply : ∀ (a : ↥H ⧸ kerIn (M.subgroupOf H) ⊤) (x : ↥(kZero H M)),
    ((ι a x : ↥(kZero H M)) : ↥H ⧸ kerIn (M.subgroupOf H) ⊤) = a * x * a⁻¹
  kZero_eq : kZero H M = barIn M H K
  sup_eq_top : kZero H M ⊔ barIn M H T = ⊤
  sylow : coordIn θ T = antiUnipotent k
  V_le : barIn M H V ≤ kZero H M
  V_le_center : coordIn θ V ≤ antiUnipotentCenter k
  V_not_le_long : ¬ coordIn θ V ≤ rootLong k
  V_not_le_short : ¬ coordIn θ V ≤ rootShort k
  card_V : Nat.card ↥(barIn M H V) = (V ⊓ pCoreOf 2 H).relIndex V
  swap : ∃ s ∈ barIn M H T, ∃ (h : antiSp k) (j : ℕ), Odd j ∧
    (∀ x, θ (ι s x) = (MulAut.conj h * minorAut k ^ j) (θ x)) ∧
    (rootLong k).map (MulAut.conj h * minorAut k ^ j).toMonoidHom = rootShort k ∧
    (rootShort k).map (MulAut.conj h * minorAut k ^ j).toMonoidHom = rootLong k ∧
    (coordIn θ V ⊓ rootLong k).map (MulAut.conj h * minorAut k ^ j).toMonoidHom =
      coordIn θ V ⊓ rootShort k
  uniqueMax : barIn M H T ≤ barIn M H M ∧ barIn M H M < ⊤ ∧
    ∀ Y : Subgroup (↥H ⧸ kerIn (M.subgroupOf H) ⊤), barIn M H T ≤ Y → Y < ⊤ →
      Y ≤ barIn M H M
  borel_le : kZero H M ⊓
      Subgroup.normalizer ((barIn M H T ⊓ kZero H M : Subgroup _) : Set (↥H ⧸ _)) ≤
    barIn M H M

theorem exists_sp4Data {H T M V K : Subgroup G} (hS : Setting H T M V K) (h2 : Case2 H T M K)
    {n : ℕ} (hn : 2 ≤ n) (hSp : E2.IsSp4Prime n ↥(E2.star M H K)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2), Nat.card k = 2 ^ n ∧
      Nonempty (Sp4Data H T M V K k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp' : IsPSp4 2 n ↥(E2.star M H K) := by
    have h := hSp
    unfold E2.IsSp4Prime at h
    rwa [ite_eq_right (show ¬ n = 1 by omega)] at h
  obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hSp'
  have : CharP k 2 := by
    have : Fintype k := Fintype.ofFinite k
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have hmp := hS.hyp.minParabolic
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hS.hyp.le_H
  obtain ⟨T', hT', hcharH, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', -⟩ :=
    qrcHyp_of_hyp28 hS.hyp hS.charTwo
  have := hel
  have hVQ' : 4 ≤ (V.subgroupOf H ⊓ CFSG.pCore 2 H).relIndex (V.subgroupOf H) := by
    rw [relIndex_subgroupOf_inf_pCore hVH]
    exact hS.four_le
  have hK₀ : kZero H M = barIn M H K := map_oddResidualPreimage_eq_of_case2 hS h2
  obtain ⟨φ⟩ := nonempty_mulEquiv_star hMH K
  let θ₀ : ↥(kZero H M) ≃* antiSp k :=
    (MulEquiv.subgroupCongr hK₀).trans (φ.trans (e.trans
      ((CFSG.LieType.SteinbergBR.EvenSp.projEquiv (K := k) (n := 2) (by norm_num)).trans
        (antiSpEquiv k).symm)))
  have hQ := sp4Confinement T' hTn hTM' hMH' hmax' hVT' hTV' hVQ' hn hk θ₀
  obtain ⟨-, ι, hιinj, hιapp, -, hsup, θ', -, hsyl, ⟨hVK, hVZ⟩, ⟨-, -, hcard⟩,
    ⟨s, hs, h, j, hj, -, hact⟩, hswap, hnl, hns, -⟩ := hQ
  obtain ⟨-, -, -, hKn, -, -, hmaxbar, -, -, -⟩ :=
    CFSG.Quasithin.H13.QRC.bender_section_setup hS.not_solvable T' hTn hTM' hMH' hmax' hVT' hVM'
  obtain ⟨hsl, hss, -, -, hVsw⟩ := hswap s hs h j hj hact
  rw [hT'] at hsup hsyl hs hmaxbar
  refine ⟨k, inferInstance, inferInstance, inferInstance, hk, ⟨{
    θ := θ'
    ι := ι
    ι_injective := hιinj
    ι_apply := hιapp
    kZero_eq := hK₀
    sup_eq_top := hsup
    sylow := hsyl
    V_le := hVK
    V_le_center := hVZ
    V_not_le_long := hnl
    V_not_le_short := hns
    card_V := hcard.trans (relIndex_subgroupOf_inf_pCore hVH)
    swap := ⟨s, hs, h, j, hj, hact, hsl, hss, hVsw⟩
    uniqueMax := hmaxbar
    borel_le := ?_ }⟩⟩
  set N := Subgroup.normalizer ((barIn M H T ⊓ kZero H M : Subgroup _) :
    Set (↥H ⧸ kerIn (M.subgroupOf H) ⊤)) with hNdef
  have hTN : barIn M H T ≤ N := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht,
      (Subgroup.normalizer_eq_top_iff.mpr hKn).symm ▸ Subgroup.mem_top t⟩
  have hNlt : N < ⊤ := by
    refine lt_of_le_of_ne le_top fun hNtop => ?_
    set w : antiSp k := CFSG.QuasithinUnique.Fin257.Sp4.wS with hw
    apply CFSG.QuasithinUnique.Fin257.Sp4.wS_not_mem_normalizer_U (K := k)
    rw [← hw]
    have hx : ((θ'.symm w : ↥(kZero H M)) : ↥H ⧸ kerIn (M.subgroupOf H) ⊤) ∈ N :=
      hNtop ▸ Subgroup.mem_top _
    have key : ∀ u ∈ antiUnipotent k, w * u * w⁻¹ ∈ antiUnipotent k := by
      intro u hu
      rw [← hsyl] at hu ⊢
      obtain ⟨y, hy, rfl⟩ := hu
      refine ⟨θ'.symm w * y * (θ'.symm w)⁻¹, ?_, by simp⟩
      have hy' : ((y : ↥(kZero H M)) : ↥H ⧸ kerIn (M.subgroupOf H) ⊤) ∈
          barIn M H T ⊓ kZero H M := ⟨hy, y.2⟩
      exact ((Subgroup.mem_normalizer_iff.mp hx _).mp hy').1
    have hww : w * w = 1 := CFSG.QuasithinUnique.Fin257.Sp4.wS_mul_self
    have hwi : w⁻¹ = w := CFSG.QuasithinUnique.Fin257.Sp4.wS_inv
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨key u, fun hu => ?_⟩
    have h1 := key _ hu
    have e : w * (w * u * w⁻¹) * w⁻¹ = u := by
      rw [hwi]
      calc w * (w * u * w) * w = (w * w) * u * (w * w) := by group
        _ = u := by rw [hww, one_mul, mul_one]
    rwa [e] at h1
  exact inf_le_right.trans (hmaxbar.2.2 N hTN hNlt)

end CFSG.Quasithin.Ch3E213M
