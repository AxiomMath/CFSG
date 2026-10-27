module

public import CFSG.RankThree.GF2n.Stroth80.Sec94FreeStmt
public import CFSG.GroupTheory.OddOrderPGroup
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9REnd

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement


namespace S94F

variable {G : Type} [Group G] [Finite G]

theorem le_of_normalClosure_two {Q L Y R N J : Subgroup G} (hQS : Q ≤ L ⊓ Y)
    (hNn : ∀ r ∈ R, ∀ x ∈ N, r * x * r⁻¹ ∈ N) (h2 : IsPGroup 2 ↥N)
    (h311a : N = ⨆ (h : G) (_ : h ∈ R), conjSubgroup h L ⊓ N)
    (hgen : ∀ r ∈ R, ∃ y ∈ J, y⁻¹ * r ∈ N)
    (hcomm : ∀ y ∈ J, ∀ w ∈ L ⊓ Y, ⁅y, w⁆ ∈ Q)
    (hSN : L ⊓ Y ≤ N) (hcard : Nat.card ↥(L ⊓ N) ≤ Nat.card ↥(L ⊓ Y)) : N ≤ Y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLN : L ⊓ Y = L ⊓ N :=
    Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left hSN) hcard
  have hJle : ∀ y ∈ J, conjSubgroup y (L ⊓ Y) ≤ L ⊓ Y := by
    intro y hy w hw
    rw [mem_conjSubgroup] at hw
    have e : w = ⁅y, y⁻¹ * w * y⁆ * (y⁻¹ * w * y) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (L ⊓ Y).mul_mem (hQS (hcomm y hy _ hw)) hw
  have hJS : ∀ y ∈ J, conjSubgroup y (L ⊓ Y) = L ⊓ Y := fun y hy =>
    Subgroup.eq_of_le_of_card_ge (hJle y hy) (by rw [card_conjSubgroup])
  have hRN : ∀ h ∈ R, conjSubgroup h N = N := fun h hh =>
    conjSubgroup_eq_self_iff.mpr (Subgroup.mem_normalizer_fintype fun x hx => hNn h hh x hx)
  have hpiece : ∀ h ∈ R, ∃ n ∈ N, conjSubgroup h L ⊓ N = conjSubgroup n (L ⊓ Y) := by
    intro h hh
    obtain ⟨y, hyJ, hyN⟩ := hgen h⁻¹ (R.inv_mem hh)
    refine ⟨h * y, ?_, ?_⟩
    · have := N.inv_mem hyN
      rwa [mul_inv_rev, inv_inv, inv_inv] at this
    · calc conjSubgroup h L ⊓ N = conjSubgroup h L ⊓ conjSubgroup h N := by rw [hRN h hh]
        _ = conjSubgroup h (L ⊓ N) := (conjSubgroup_inf _ _ _).symm
        _ = conjSubgroup h (L ⊓ Y) := by rw [hLN]
        _ = conjSubgroup (h * y) (conjSubgroup y⁻¹ (L ⊓ Y)) := by
          rw [← conjSubgroup_mul, mul_inv_cancel_right]
        _ = conjSubgroup (h * y) (L ⊓ Y) := by rw [hJS y⁻¹ (J.inv_mem hyJ)]
  have hNC : N ≤ ⨆ (n : G) (_ : n ∈ N), conjSubgroup n (L ⊓ Y) := by
    refine h311a.le.trans (iSup₂_le fun h hh => ?_)
    obtain ⟨n, hn, e⟩ := hpiece h hh
    rw [e]
    exact le_iSup₂_of_le n hn le_rfl
  by_contra hNY
  have hlt : L ⊓ Y < N := lt_of_le_of_ne hSN fun h => hNY (h ▸ inf_le_right)
  obtain ⟨X, hSX, hXN, hNX⟩ := exists_normal_of_lt_of_isPGroup (p := 2) h2 hlt
  have hle : ⨆ (n : G) (_ : n ∈ N), conjSubgroup n (L ⊓ Y) ≤ X := by
    refine iSup₂_le fun n hn => ?_
    calc conjSubgroup n (L ⊓ Y) ≤ conjSubgroup n X := Subgroup.map_mono hSX
      _ = X := conjSubgroup_eq_self_iff.mpr (hNX hn)
  exact absurd (hNC.trans hle) hXN.not_ge

end S94F

theorem step94CNAll_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h92 : Stroth92Statement) (hB : Step94ConjVStatement) (hGen : Step94GenStatement)
    (hCount : Step94CountNuStatement) (hSNu : Step94SNuStatement) : Step94CNAllStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj Y hdp hYsl hn5 u hu huQ
  have hs5 := hs.toSec5
  have huL : u ∈ LB M Q B := hu.1
  have hsplit := split95_of_step94 h92 hB hc hs hZ0 hs0 hxL hxN hconj hdp hYsl
  have h4 := sec4_of h34 h311a G M Q Z B hc n t hs _ Y hsplit
  have hcount :=
    hCount G M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj Y hdp hYsl hn5 u hu huQ
  have hSN := hSNu G M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj Y hdp hYsl hn5 u hu huQ
  have hQY : Q ≤ Y := hdp.2.2.1
  have hQS : Q ≤ LB M Q B ⊓ Y := le_inf le_sup_left hQY
  have hcardS : Nat.card ↥(LB M Q B ⊓ Y) = Nat.card Q * Nat.card Z := by
    have h1 := Subgroup.relIndex_mul_card (H := Q) (K := LB M Q B ⊓ Y)
    rw [inf_of_le_left hQS, h4.2.1] at h1
    rw [← h1, mul_comm]
  have hcard : Nat.card ↥(LB M Q B ⊓ hc.CN u) ≤ Nat.card ↥(LB M Q B ⊓ Y) := by
    rw [hcardS]
    exact hcount
  have hNR : hc.CN u ≤ Rt M (LB M Q B) u := fun y hy => (Ctx.mem_CN.mp hy).1
  by_cases hRe : Rt M (LB M Q B) u = LB M Q B
  ·
    have hNL : hc.CN u ≤ LB M Q B := hRe ▸ hNR
    have heq : LB M Q B ⊓ Y = LB M Q B ⊓ hc.CN u :=
      Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left hSN) hcard
    intro y hy
    have hy' : y ∈ LB M Q B ⊓ hc.CN u := ⟨hNL hy, hy⟩
    rw [← heq] at hy'
    exact hy'.2
  · obtain ⟨c, -, d, -, -, hgen, hcomm⟩ :=
      hGen G M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj Y hdp hYsl hn5 u hu huQ
    exact S94F.le_of_normalClosure_two (R := Rt M (LB M Q B) u)
      (J := LB M Q (conjSubgroup c B) ⊔ LB M Q (conjSubgroup d B)) hQS
      (fun r hr y hy => hc.CN_conj_mem huL hr hy) (HS9.isPGroup_CN h34 h311a hs huL huQ)
      (h311a G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen u huL huQ hRe) hgen hcomm hSN
      hcard

namespace S94F

open Classify in
theorem card_ge_of_elationFull {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {F : LinearMap.BilinForm K V} (hnd : F.Nondegenerate)
    (halt : F.IsAlt) {e : V} (he : e ≠ 0) {A : Subgroup (V ≃ₗ[K] V)}
    (hA : A ≤ pointRadSubgroup F e) (hfull : ElationFull F (A : Set _) e) :
    Nat.card K ^ (Module.finrank K V - 2) ≤ Nat.card A := by
  classical
  obtain ⟨z, hz⟩ : ∃ z : V, F e z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact he (hnd.1 e hcon)
  set f : V := (F e z)⁻¹ • z with hfdef
  have hef : F e f = 1 := by
    rw [hfdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hz]
  have hD : (A : Set (V ≃ₗ[K] V)) ⊆ pointRad F e := fun g hg => hA hg
  set Φ : V →ₗ[K] K × K := (F.flip e).prod (F.flip f) with hΦ
  have hW : ∀ ω ∈ LinearMap.ker Φ, F ω e = 0 ∧ F ω f = 0 := by
    intro ω hω
    rw [LinearMap.mem_ker, hΦ, LinearMap.prod_apply, Prod.mk_eq_zero] at hω
    exact hω
  have hex : ∀ ω : LinearMap.ker Φ, ∃ g : A, ∃ c : K,
      (g : V ≃ₗ[K] V) f - f = (ω : V) + c • e := by
    intro ω
    obtain ⟨g, hg, c, hc⟩ := ElationFull.om hnd halt hef hD hfull (hW ω ω.2).1
    exact ⟨⟨g, hg⟩, c, hc⟩
  choose g c hg using hex
  have hinj : Function.Injective g := by
    intro ω ω' h
    have h1 : (ω : V) + c ω • e = (ω' : V) + c ω' • e := by rw [← hg ω, ← hg ω', h]
    have h2 := congrArg (fun x => F x f) h1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, (hW ω ω.2).2,
      (hW ω' ω'.2).2, hef, smul_eq_mul, mul_one, zero_add] at h2
    rw [h2] at h1
    exact Subtype.ext (add_right_cancel h1)
  have hdimW : Module.finrank K V - 2 ≤ Module.finrank K (LinearMap.ker Φ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    have h2 : Module.finrank K (LinearMap.range Φ) ≤ 2 := by
      calc Module.finrank K (LinearMap.range Φ) ≤ Module.finrank K (K × K) :=
            Submodule.finrank_le _
        _ = 2 := by simp
    omega
  haveI := finite_linearEquiv (K := K) (V := V)
  calc Nat.card K ^ (Module.finrank K V - 2)
      ≤ Nat.card K ^ Module.finrank K (LinearMap.ker Φ) :=
        Nat.pow_le_pow_right Nat.card_pos hdimW
    _ = Nat.card (LinearMap.ker Φ) := (Module.natCard_eq_pow_finrank (K := K)).symm
    _ ≤ Nat.card A := Nat.card_le_card_of_injective g hinj

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem le_finrank_imgSub (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {u : G}
    (hs : Sec5Hyp hc n u) (hnot : ¬ Vt M (LB M Q B) B Z u ≤ QB B)
    (hdimQ : Nat.card Z ^ (n + 1) ≤ Nat.card ↥(⁅Q, Subgroup.zpowers u⁆ ⊔ Z))
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (h : GlobalModelData M Q Z γ M₀)
    (hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z u) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z u)) :
    n ≤ Module.finrank K ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) := by
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hVU := (hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB h35 hs.mem hs.notQ hnot).1
  have hcardM := M₀.card_eq (hc.Vt_le_Q u)
    (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := u))
  have hfin : Nat.card (M₀.img (Vt M (LB M Q B) B Z u)) =
      Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => mem_imgSub.symm)
  have hpow : Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) =
      Nat.card K ^ Module.finrank K ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) :=
    Module.natCard_eq_pow_finrank (K := K)
  have hKZ : Nat.card K = Nat.card Z := h.card
  rw [hfin, hpow, hKZ] at hcardM
  have hq1 : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  by_contra hlt
  push Not at hlt
  have h1 : Nat.card ↥(Vt M (LB M Q B) B Z u) <
      Nat.card Z ^ (n + 1) := by
    rw [hcardM, ← pow_succ']
    exact Nat.pow_lt_pow_right hq1 (by omega)
  rw [hVU] at h1
  exact absurd hdimQ (not_le.mpr h1)

end S94F

theorem step94CountNu_of (h34 : Stroth34Statement) (h92 : Stroth92Statement)
    (hB : Step94ConjVStatement) (hNotQB : Step94NotQBStatement) (hDimQ : Step94DimQStatement) :
    Step94CountNuStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj Y hdp hYsl hn5 u hu huQ
  classical
  have hs5 := hs.toSec5
  have huL : u ∈ LB M Q B := hu.1
  have hsu : Sec5Hyp hc n u := ⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, huL, huQ⟩
  have hnot :=
    hNotQB G M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj Y hdp hYsl hn5 u hu huQ
  have hsplit := split95_of_step94 h92 hB hc hs hZ0 hs0 hxL hxN hconj hdp hYsl
  have hdimQ := hDimQ G M Q Z B hc n t hs _ Y hsplit u hu huQ
  obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have hS : ∀ (c : GaloisField 2 n') (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z u) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z u) :=
    fun c _ he => hc.smul_mem_img_Vt h u c he
  obtain ⟨D⟩ := hc.exists_reprData h34 hsu hnot h hS
  have hnd := S94F.le_finrank_imgSub h34 hc hsu hnot hdimQ h hS
  have hdim4 : 4 ≤ Module.finrank (GaloisField 2 n')
      ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) := by omega
  have huL1 : u ∈ conjSubgroup 1 (LB M Q B) := by rw [conjSubgroup_one]; exact huL
  obtain ⟨e, he0, -, hepr, heful⟩ := D.elation_data h34 hsu h hdim4 M.one_mem huL1
  rw [conjSubgroup_one] at hepr heful
  have hA := S94F.card_ge_of_elationFull D.nondeg D.alt he0 hepr heful
  have hLR : LB M Q B ≤ Rt M (LB M Q B) u := le_Rt (M := M) (LB M Q B) huL
  have himg : Nat.card ↥(((LB M Q B).subgroupOf (Rt M (LB M Q B) u)).map D.ρ) =
      (hc.CN u).relIndex (LB M Q B) := by
    rw [← Subgroup.relIndex_ker, D.ker, Subgroup.relIndex_subgroupOf hLR]
  have hKZ : Nat.card (GaloisField 2 n') = Nat.card Z := h.card
  have hq1 : 1 ≤ Nat.card Z := Nat.card_pos
  have hge : Nat.card Z ^ (n - 2) ≤ (hc.CN u).relIndex (LB M Q B) := by
    calc Nat.card Z ^ (n - 2)
        ≤ Nat.card Z ^ (Module.finrank (GaloisField 2 n')
            ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) - 2) :=
          Nat.pow_le_pow_right hq1 (by omega)
      _ = Nat.card (GaloisField 2 n') ^ (Module.finrank (GaloisField 2 n')
            ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) - 2) := by rw [hKZ]
      _ ≤ _ := hA
      _ = _ := himg
  have hrel := Subgroup.relIndex_mul_card (H := hc.CN u) (K := LB M Q B)
  rw [(stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.2.1] at hrel
  have hn1 : n - 1 = (n - 2) + 1 := by have := hs5.n_gt; omega
  rw [hn1, pow_succ] at hrel
  have hle : Nat.card Z ^ (n - 2) * Nat.card ↥(hc.CN u ⊓ LB M Q B) ≤
      Nat.card Z ^ (n - 2) * (Nat.card Q * Nat.card Z) := by
    calc Nat.card Z ^ (n - 2) * Nat.card ↥(hc.CN u ⊓ LB M Q B)
        ≤ (hc.CN u).relIndex (LB M Q B) * Nat.card ↥(hc.CN u ⊓ LB M Q B) :=
          Nat.mul_le_mul_right _ hge
      _ = Nat.card Q * (Nat.card Z ^ (n - 2) * Nat.card Z) := hrel
      _ = Nat.card Z ^ (n - 2) * (Nat.card Q * Nat.card Z) := by ring
  rw [inf_comm]
  exact Nat.le_of_mul_le_mul_left hle (by positivity)

open Classify in
theorem step94SNu_of (h34 : Stroth34Statement) (h92 : Stroth92Statement)
    (hB : Step94ConjVStatement) (hNotQB : Step94NotQBStatement) (hDimQ : Step94DimQStatement)
    (hGen : Step94GenStatement) : Step94SNuStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj Y hdp hYsl hn5 u hu huQ w hw
  classical
  have hs5 := hs.toSec5
  have huL : u ∈ LB M Q B := hu.1
  have hsu : Sec5Hyp hc n u := ⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, huL, huQ⟩
  have hnot :=
    hNotQB G M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj Y hdp hYsl hn5 u hu huQ
  have hsplit := split95_of_step94 h92 hB hc hs hZ0 hs0 hxL hxN hconj hdp hYsl
  have hdimQ := hDimQ G M Q Z B hc n t hs _ Y hsplit u hu huQ
  obtain ⟨c, -, d, -, hJR, hgen, hcomm⟩ :=
    hGen G M Q Z B hc n t hs Z0 hZ0 hsc s hs0 x hxL hxN hconj Y hdp hYsl hn5 u hu huQ
  obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have hS : ∀ (c : GaloisField 2 n') (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z u) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z u) :=
    fun c _ he => hc.smul_mem_img_Vt h u c he
  obtain ⟨D⟩ := hc.exists_reprData h34 hsu hnot h hS
  have hnd := S94F.le_finrank_imgSub h34 hc hsu hnot hdimQ h hS
  have hdim4 : 4 ≤ Module.finrank (GaloisField 2 n')
      ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) := by omega
  have hLR : LB M Q B ≤ Rt M (LB M Q B) u := le_Rt (M := M) (LB M Q B) huL
  have hwL : w ∈ LB M Q B := hw.1
  have hwR : w ∈ Rt M (LB M Q B) u := hLR hwL
  have hQN : Q ≤ hc.CN u := hc.Q_le_CN huL
  refine Ctx.mem_CN.mpr ⟨hwR, ?_⟩
  suffices hρw : D.ρ ⟨w, hwR⟩ = 1 by
    have hker : (⟨w, hwR⟩ : ↥(Rt M (LB M Q B) u)) ∈ D.ρ.ker := hρw
    rw [D.ker, Subgroup.mem_subgroupOf] at hker
    exact (Ctx.mem_CN.mp hker).2
  set g : _ := D.ρ ⟨w, hwR⟩ with hgdef
  have hcommρ : ∀ r : ↥(Rt M (LB M Q B) u), D.ρ r * g = g * D.ρ r := by
    intro r
    obtain ⟨y, hyJ, hyN⟩ := hgen r r.2
    have hyR : y ∈ Rt M (LB M Q B) u := hJR hyJ
    have h1 : D.ρ r = D.ρ ⟨y, hyR⟩ := by
      have hk : (⟨y, hyR⟩⁻¹ * r : ↥(Rt M (LB M Q B) u)) ∈ D.ρ.ker := by
        rw [D.ker, Subgroup.mem_subgroupOf]
        exact hyN
      have h2 : D.ρ (⟨y, hyR⟩⁻¹ * r) = 1 := hk
      rw [map_mul, map_inv, inv_mul_eq_one] at h2
      exact h2.symm
    have h3 : (⁅(⟨y, hyR⟩ : ↥(Rt M (LB M Q B) u)), ⟨w, hwR⟩⁆) ∈ D.ρ.ker := by
      rw [D.ker, Subgroup.mem_subgroupOf]
      exact hQN (hcomm y hyJ w hw)
    have h4 : D.ρ ⁅(⟨y, hyR⟩ : ↥(Rt M (LB M Q B) u)), ⟨w, hwR⟩⁆ = 1 := h3
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h4
    rw [h1]
    exact h4
  have huL1 : u ∈ conjSubgroup 1 (LB M Q B) := by rw [conjSubgroup_one]; exact huL
  obtain ⟨e, he0, -, hepr, -⟩ := D.elation_data h34 hsu h hdim4 M.one_mem huL1
  rw [conjSubgroup_one] at hepr
  obtain ⟨z, hz⟩ : ∃ z, D.F e z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact he0 (D.nondeg.1 e hcon)
  have hef : D.F e ((D.F e z)⁻¹ • z) = 1 := by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hz]
  have hgpr : g ∈ pointRadSubgroup D.F e :=
    hepr ⟨⟨w, hwR⟩, (Subgroup.mem_subgroupOf).mpr hwL, rfl⟩
  have hg2 : g * g = 1 := pointRad_mul_self D.alt hef hgpr
  set U : Submodule (GaloisField 2 n') ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) :=
    LinearMap.ker ((g : _ →ₗ[GaloisField 2 n'] _) - LinearMap.id) with hUdef
  have hmemU : ∀ v, v ∈ U ↔ g v = v := by
    intro v
    rw [hUdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hUinv : ∀ k ∈ D.ρ.range, ∀ v ∈ U, k v ∈ U := by
    rintro _ ⟨r, rfl⟩ v hv
    rw [hmemU] at hv ⊢
    have := congrArg (fun φ => φ v) (hcommρ r)
    simp only [LinearEquiv.mul_apply] at this
    rw [← this, hv]
  have hUne : U ≠ ⊥ := by
    have hpos : (⊤ : Submodule (GaloisField 2 n')
        ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS)) ≠ ⊥ := by
      intro h0
      have : Module.finrank (GaloisField 2 n') ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) = 0 := by
        rw [← finrank_top, h0, finrank_bot]
      omega
    obtain ⟨v, -, hv0, hvfix⟩ := exists_fixed_of_two_group (Subgroup.zpowers g)
      (fun k hk => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
        rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hg2, one_zpow])
      ⊤ (fun _ _ _ _ => Submodule.mem_top) hpos
    intro hU0
    apply hv0
    have hvU : v ∈ U := (hmemU v).mpr (hvfix g (Subgroup.mem_zpowers g))
    rw [hU0, Submodule.mem_bot] at hvU
    exact hvU
  obtain ⟨P, hP0, hPspan, hPful, -⟩ := hc.theoremX_data h34 hsu h D hdim4
  have hH : D.ρ.range ≤ sympSubgroup D.F := by
    rintro _ ⟨r, rfl⟩
    exact D.isom r
  have hUtop := eq_top_of_invariant D.nondeg D.alt (by omega) hH hP0 hPful hPspan U hUinv hUne
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ U := hUtop ▸ Submodule.mem_top
  exact (hmemU v).mp hv

end CFSG.RankThree.GF2n.Stroth80
