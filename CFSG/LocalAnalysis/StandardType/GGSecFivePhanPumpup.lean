module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpMoves
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpLayerSub
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpRoute
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpSameSuppRoots
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneCard
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem ggRankOneIn_isQuasisimple_phan_L
    (hRk1 : GGSecFiveRk1PhanInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer L Bs) (hrC : r ∈ ggCoxRefl M e) :
    CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs r) := by
  obtain ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, -, -, -⟩ :=
    hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 L (Or.inl rfl) r hrA hrC
  have hcardSL : Nat.card (ggRankOneIn L Bs r) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← hθrange]
    exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm
  have hF2 : Nat.card F ≠ 2 := by
    intro h2
    apply hbig r hrA hrC
    rw [hcardSL, ggSL2_card F, h2]
    norm_num
  have h4 : 4 ≤ Nat.card F := by
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨p', hcharp', m, -, hcard⟩ := FiniteField.card' F
    have hpc : p' = 2 := CharP.eq F hcharp' hchar
    have hcard2 : Fintype.card F = 2 ^ (m : ℕ) := by rw [hcard, hpc]
    have hm2 : 2 ≤ (m : ℕ) := by
      rcases Nat.lt_or_ge (m : ℕ) 2 with hlt | hge
      · have hm1 : (m : ℕ) = 1 := by
          have := m.pos
          omega
        exfalso
        exact hF2 (by rw [Nat.card_eq_fintype_card, hcard2, hm1]; norm_num)
      · exact hge
    rw [Nat.card_eq_fintype_card, hcard2]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) hm2
  have hSL : CFSG.Assembly.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨(CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4).commutator_eq_top,
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4⟩
  rw [← hθrange]
  exact CFSG.Assembly.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hθinj).symm hSL

theorem ggDk_pumpup_sameSupp_phan
    (hRk1 : GGSecFiveRk1PhanInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι} (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    {ε : Fin k → ℤ} (hε : ∀ a, ε a = 1 ∨ ε a = -1)
    (hfix : ∃ xb : ↥Bs, (xb : G) = x ∧ ∀ (u : M.Group) (η : Fin k → ℤ), GGDReflRoot k (φ u) η →
      ((((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) xb = xb) ↔ ggDDot ε η = 0))
    {I : Finset (Fin k)} (hI : I.card = 3) {v : ↥Bs} (hD : D = Subgroup.closure {x, (v : G)})
    (hpJ : p ∣ Nat.card J)
    (hIJ : ∀ a ∈ I, ∀ b ∈ I, a ≠ b →
      Pi.single a (ε a) - Pi.single b (ε b) ∈ ggDMemberRoots e φ J)
    {θ : Additive ↥Bs ≃+ (Fin k → ZMod p)}
    (hθ : ∀ (u : M.Group) (η : Fin k → ℤ), GGDReflRoot k (φ u) η → ∀ b : ↥Bs,
      θ (Additive.ofMul (((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b)) =
        θ (Additive.ofMul b) - (∑ a, θ (Additive.ofMul b) a * (η a : ZMod p)) •
          fun a => (η a : ZMod p))
    (hvI : ∀ a ∈ I, θ (Additive.ofMul v) a = 0) :
    ∃ t t' : M.Group, GGDSameSupp k (φ t) (φ t') ∧
      ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
        ggAutomizer (ggLayerClosure p (Subgroup.centralizer ({(v : G)} : Set G)) J) Bs ∧
      ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈
        ggAutomizer (ggLayerClosure p (Subgroup.centralizer ({(v : G)} : Set G)) J) Bs ∧
      ∃ xb : ↥Bs, (xb : G) = x ∧ ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) xb ≠ xb := by
  obtain ⟨c1, c2, c3, h12, h13, h23, hIeq⟩ := Finset.card_eq_three.mp hI
  subst I
  have _ : 2 ≤ k := by omega
  let σ : Fin k → ℤ := Pi.single c1 (ε c1) - Pi.single c2 (ε c2)
  let ρ : Fin k → ℤ := Pi.single c1 (ε c1) - Pi.single c3 (ε c3)
  let η' : Fin k → ℤ := Pi.single c1 (ε c1) + Pi.single c2 (ε c2)
  obtain ⟨t, ht, htJ⟩ := hIJ c1 (by simp) c2 (by simp) h12
  obtain ⟨tρ, htρ, htρJ⟩ := hIJ c1 (by simp) c3 (by simp) h13
  have hη'mem : η' ∈ ggDRootSet k :=
    ⟨c1, c2, ε c1, ε c2, h12, hε c1, hε c2, rfl⟩
  obtain ⟨t'₀, ht'₀⟩ := exists_ggDReflRoot hη'mem
  let t' : M.Group := φ.symm t'₀
  have ht' : GGDReflRoot k (φ t') η' := by simpa [t'] using ht'₀
  let r₁ : MulAut ↥Bs := ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
  let rρ : MulAut ↥Bs := ((e tρ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
  let r' : MulAut ↥Bs := ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
  have hSS : GGDSameSupp k (φ t) (φ t') :=
    sameSupp_of_signed h12 (hε c1) (hε c2) ht ht'
  have hrC₁ : r₁ ∈ ggCoxRefl M e := mem_ggCoxRefl_of_ggDReflRoot e φ hφ ht
  have hrC' : r' ∈ ggCoxRefl M e := mem_ggCoxRefl_of_ggDReflRoot e φ hφ ht'
  have hconn : GGSimplyLacedConnected M := ggSimplyLacedConnected_of_weyl hpres.1 hle3
  obtain ⟨rδ, hrδA, hrδ⟩ := ggCoxRefl_conj_of_connected e hconn hrC₁ hrC'
  have hS : LargeEvenSStar p B x L := hcfg.1.1.1.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hxBs : x ∈ Bs := hcfg.1.1.2.1.1 hxB
  have hLcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hS.2.2.2.1
  have hpre : LargeEvenStdSubPre p B x L D J := hcfg.1.1.2.2.1
  have hp : p.Prime := (ggRouteCfg_prime hcfg).1
  have : Fact p.Prime := ⟨hp⟩
  have hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hpre.2.2.2.2.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  have hJx : J ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
    intro j hj
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp ((hJ.1.trans inf_le_right) hj) x hxD).symm
  obtain ⟨xb, hxb, hfix⟩ := hfix
  have hr₁x : r₁ xb = xb := by
    rw [← hxb] at hJx
    exact ggAutomizer_apply_eq_of_le_centralizer (x := xb) hJx htJ
  have hxH : x ∈ (ggHyperplane Bs r₁ : Set G) := ⟨xb, hr₁x, hxb⟩
  have hY : Subgroup.centralizer (ggHyperplane Bs r₁ : Set G) ≤
      Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxH)
  have hrA₁ : r₁ ∈ ggAutomizer L Bs := ggAutomizer_mono Bs hJL htJ
  have hq : CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs r₁) :=
    ggRankOneIn_isQuasisimple_phan_L hRk1 hcfg hns hpres hle3 hbig hrA₁ hrC₁
  have hr₁2 : r₁ * r₁ = 1 :=
    (sq r₁).symm.trans (ggCoxRefl_isReflection (fun i => hpres.2 i) hrC₁).1
  have hsub : IsSubnormal (ggLayerClosure p (Subgroup.centralizer ({(v : G)} : Set G)) J)
      (Subgroup.centralizer ({(v : G)} : Set G)) :=
    ggLayerClosure_isSubnormal_of_stdSub hLB hcfg.1.1.1 hcfg.1.1.2.2 hpJ hD
  have hJKd : J ≤ ggLayerClosure p (Subgroup.centralizer ({(v : G)} : Set G)) J :=
    le_ggLayerClosure p (Subgroup.centralizer ({(v : G)} : Set G)) J
  have hBs : ∀ a c : ↥Bs, a * c = c * a := (ggRouteCfg_isElemAbelian hcfg).1.is_comm.comm
  have hBsD : Bs ≤ Subgroup.centralizer (D : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun d hd =>
      congrArg Subtype.val (hBs ⟨d, hcfg.1.1.2.1.1 (hpre.1 hd)⟩ ⟨b, hb⟩)
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) := by
    rw [hpre.2.2.2.2.1]
    exact le_normalizer_of_map_conj_le fun g hg => map_conj_largeEvenLayer_le
      (mem_normalizer_inf_centralizer (GGInnerDiagOn.le_normalizer hcfg.1.2.2.1.1 hg) (hBsD hg))
  let b : ↥Bs := Additive.toMul (θ.symm (Pi.single c1 1))
  let θv : Fin k → ZMod p := θ (Additive.ofMul v)
  let θρb : Fin k → ZMod p := θ (Additive.ofMul (rρ b))
  have hθb : θ (Additive.ofMul b) = Pi.single c1 1 := by
    dsimp [b]
    exact θ.apply_symm_apply (Pi.single c1 1)
  have hε0 : ∀ c, (ε c : ZMod p) ≠ 0 := by
    intro c
    rcases hε c with h | h <;> rw [h] <;> simp
  have hεsq : ∀ c, (ε c : ZMod p) * (ε c : ZMod p) = 1 := by
    intro c
    rcases hε c with h | h <;> rw [h] <;> norm_num
  have hεsqZ : ∀ c, ε c * ε c = 1 := by
    intro c
    rcases hε c with h | h <;> rw [h] <;> norm_num
  have hsum_eta : ∀ f : Fin k → ZMod p,
      (∑ a, f a * ((η' a : ℤ) : ZMod p)) =
        f c1 * (ε c1 : ZMod p) + f c2 * (ε c2 : ZMod p) := by
    intro f
    simp [η', Pi.single_apply, Int.cast_ite, Int.cast_add, Int.cast_zero, mul_add,
      Finset.sum_add_distrib, mul_ite, mul_zero]
  have hsum_rho' : ∀ f : Fin k → ZMod p,
      (∑ a, f a * ((ρ a : ℤ) : ZMod p)) =
        f c1 * (ε c1 : ZMod p) - f c3 * (ε c3 : ZMod p) := by
    intro f
    have h1 : ∀ a, f a * ((ρ a : ℤ) : ZMod p) =
        (if a = c1 then f a * (ε c1 : ZMod p) else 0) +
          (if a = c3 then -(f a * (ε c3 : ZMod p)) else 0) := by
      intro a
      by_cases ha1 : a = c1
      · subst ha1
        by_cases ha3 : a = c3
        · exact absurd ha3 h13
        · simp [ρ, ha3]
      · by_cases ha3 : a = c3
        · simp [ρ, ha3, Ne.symm h13]
          rfl
        · simp [ρ, ha1, ha3]
    calc (∑ a, f a * ((ρ a : ℤ) : ZMod p))
        = ∑ a, ((if a = c1 then f a * (ε c1 : ZMod p) else 0) +
            (if a = c3 then -(f a * (ε c3 : ZMod p)) else 0)) :=
          Finset.sum_congr rfl fun a _ => h1 a
      _ = (∑ a, if a = c1 then f a * (ε c1 : ZMod p) else 0) +
            ∑ a, if a = c3 then -(f a * (ε c3 : ZMod p)) else 0 :=
          Finset.sum_add_distrib
      _ = f c1 * (ε c1 : ZMod p) + (-(f c3 * (ε c3 : ZMod p))) := by
          rw [Fintype.sum_ite_eq', Fintype.sum_ite_eq']
      _ = f c1 * (ε c1 : ZMod p) - f c3 * (ε c3 : ZMod p) := by abel
  have hsum_rho : (∑ a, θ (Additive.ofMul b) a * ((ρ a : ℤ) : ZMod p)) =
      (ε c1 : ZMod p) := by
    rw [hsum_rho', hθb]
    simp [h13.symm]
  have hθρb_eq : θρb = θ (Additive.ofMul b) -
      (ε c1 : ZMod p) • (fun a => ((ρ a : ℤ) : ZMod p)) := by
    dsimp [θρb]
    rw [hθ tρ ρ htρ b, hsum_rho]
  have hθρb_c1 : θρb c1 = 0 := by
    have h1 : θρb c1 = 1 - (ε c1 : ZMod p) * (ε c1 : ZMod p) := by
      rw [hθρb_eq]
      simp [hθb, ρ, h13]
    rw [h1, hεsq c1, sub_self]
  have hθρb_c2 : θρb c2 = 0 := by
    rw [hθρb_eq]
    simp [hθb, ρ, h12.symm, h23]
  have hsum_tρ : (∑ a, θρb a * ((η' a : ℤ) : ZMod p)) = 0 := by
    rw [hsum_eta, hθρb_c1, hθρb_c2]
    ring
  have hsum_b : (∑ a, θ (Additive.ofMul b) a * ((η' a : ℤ) : ZMod p)) =
      (ε c1 : ZMod p) := by
    rw [hsum_eta, hθb]
    simp [h12.symm]
  have hv1 : θv c1 = 0 := by simpa [θv] using hvI c1 (by simp)
  have hv2 : θv c2 = 0 := by simpa [θv] using hvI c2 (by simp)
  have hsum_v : (∑ a, θv a * ((η' a : ℤ) : ZMod p)) = 0 := by
    rw [hsum_eta, hv1, hv2]
    ring
  have hdv : r' v = v := by
    apply Additive.ofMul.injective
    apply θ.injective
    rw [hθ t' η' ht' v, hsum_v]
    simp
  have hdb : r' (rρ b) = rρ b := by
    apply Additive.ofMul.injective
    apply θ.injective
    rw [hθ t' η' ht' (rρ b), hsum_tρ]
    simp
  have hb' : r' b ≠ b := by
    intro h
    have hh : ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b = b := h
    have hcoord := congrFun (hθ t' η' ht' b) c2
    rw [hh, hsum_b, hθb] at hcoord
    simp only [η', Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.single_apply, Int.cast_ite,
      Int.cast_zero, Int.cast_add, smul_eq_mul, h12.symm, if_false, if_true] at hcoord
    have hzero : (ε c1 : ZMod p) * (ε c2 : ZMod p) = 0 := by
      have h := hcoord.symm
      rw [zero_add, zero_sub] at h
      exact neg_eq_zero.mp h
    rcases mul_eq_zero.mp hzero with h | h
    · exact hε0 c1 h
    · exact hε0 c2 h
  have hpump : rδ * r₁ * rδ⁻¹ ∈
      ggAutomizer (ggLayerClosure p (Subgroup.centralizer ({(v : G)} : Set G)) J) Bs :=
    ggPumpup_mem_ggAutomizer_of_moves hBs hLcomp hY hq hrA₁ hr₁2 hsub hJKd hBsJ
      (ggAutomizerJoin_le_top L Bs 𝒦 hrδA) htρJ
      (by rw [← hrδ]; exact hdv) (by rw [← hrδ]; exact hdb) (by rw [← hrδ]; exact hb')
  have hmove : r' xb ≠ xb := by
    intro h
    have hz : ggDDot ε η' = 0 := (hfix t' η' ht').mp h
    rw [ggDDot_comm, ggDDot_single_add_single] at hz
    rw [hεsqZ c1, hεsqZ c2] at hz
    norm_num at hz
  refine ⟨t, t', hSS, ggAutomizer_mono Bs hJKd htJ, ?_, ⟨xb, hxb, hmove⟩⟩
  rw [show ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = r' from rfl, hrδ]
  exact hpump

end CFSG.StandardType

end
