module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Res
public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Lift
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Elem
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Main
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5PZero
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item137ProofOrbit
import CFSG.RankThree.PartTwo.Sec11.Item116H3Rank
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofBalTools
import CFSG.RankThree.PartTwo.KFacts.K71Lift
import CFSG.RankThree.PartTwo.Sec8.Hering88FCoprime
import CFSG.RankThree.GF2n.Basic
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138P5

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU projImage)
open Matrix (ProjGenLinGroup)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_of_isQuasisimple_of_center_eq_bot {K : Type*} [Group K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K = ⊥) : IsSimpleGroup K := by
  obtain ⟨-, hs, -⟩ := hK
  let e : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem eq_bot_of_isSolvable_of_normal {K : Type*} [Group K] (hK : CFSG.IsQuasisimple K)
    (hZ : Subgroup.center K = ⊥) {N : Subgroup K} (hN : N.Normal) (hs : Group.IsSolvable N) :
    N = ⊥ := by
  have := isSimpleGroup_of_isQuasisimple_of_center_eq_bot hK hZ
  rcases hN.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have : Group.IsPerfect K := hK.1
    have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK
    have hsK : IsSolvable K := by
      subst h
      haveI := hs
      exact solvable_of_surjective (f := (⊤ : Subgroup K).subtype)
        (fun k => ⟨⟨k, Subgroup.mem_top k⟩, rfl⟩)
    exact Group.IsPerfect.not_isSolvable K hsK

theorem le_of_mem_of_mem {P₀ H : Subgroup G} (hP₀e : CFSG.Assembly.IsElemAbelian 3 P₀)
    (hP₀9 : Nat.card P₀ = 9) {c x : G} (hc : orderOf c = 3) (hcP : c ∈ P₀) (hxP : x ∈ P₀)
    (hxc : x ∉ Subgroup.zpowers c) (hcH : c ∈ H) (hxH : x ∈ H) : P₀ ≤ H := by
  have hcx : c * x = x * c := congrArg Subtype.val (hP₀e.1.is_comm.comm ⟨c, hcP⟩ ⟨x, hxP⟩)
  have h9 := card_sup_zpowers_eq_nine hc (hP₀e.2 x hxP) hxc hcx
  have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers x ≤ P₀ ⊓ H :=
    sup_le (Subgroup.zpowers_le.mpr ⟨hcP, hcH⟩) (Subgroup.zpowers_le.mpr ⟨hxP, hxH⟩)
  have heq : P₀ ⊓ H = P₀ := Subgroup.eq_of_le_of_card_ge inf_le_left (by
    rw [hP₀9, ← h9]
    exact Subgroup.card_le_of_le hle)
  rw [← heq]
  exact inf_le_right

theorem exists_lift_three_in {L J : Subgroup G} (hJL : J ≤ L)
    (hcov : L ≤ J ⊔ inSubgroup (aschbacherSolvableCore 3) L)
    {d : L ⧸ aschbacherSolvableCore 3 L} (hd3 : d ^ 3 = 1) :
    ∃ r ∈ J, ∃ hr : r ∈ L, ((⟨r, hr⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = d ∧
      r ^ 3 = 1 := by
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective d
  have hlJ : (l : G) ∈ (J : Set G) * (θL : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right J θL
      (hJL.trans (Sec6.le_normalizer_theta L))]
    exact hcov l.2
  obtain ⟨j, hj, k, hk, hjk⟩ := hlJ
  have hjL : j ∈ L := hJL hj
  have hjimg : ((⟨j, hjL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = d := by
    rw [← hl]
    apply QuotientGroup.eq.mpr
    obtain ⟨k', hk', rfl⟩ := hk
    have : (⟨j, hjL⟩ : L)⁻¹ * l = k' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hjk]
      simp
    rw [this]
    exact hk'
  obtain ⟨m, hmd, hm3⟩ := exists_pow_lift_three (⟨j, hjL⟩ : L) hjimg hd3
  refine ⟨(((⟨j, hjL⟩ : L) ^ m : L) : G), ?_, ((⟨j, hjL⟩ : L) ^ m : L).2, hmd, ?_⟩
  · rw [Subgroup.coe_pow]
    exact J.pow_mem hj m
  · rw [← Subgroup.coe_pow, hm3, Subgroup.coe_one]

theorem le_theta_of_le_thetaQuotCentralizer {L J Lx S₀ : Subgroup G}
    (hLq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) (hJL : J ≤ L)
    (hcov : L ≤ J ⊔ inSubgroup (aschbacherSolvableCore 3) L) (hJLx : J ≤ Lx)
    (hS₀J : S₀ ≤ J) (hS₀C : S₀ ≤ Sec4.thetaQuotCentralizer Lx) :
    S₀ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  set ψ : J →* L ⧸ aschbacherSolvableCore 3 L :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hJL) with hψ
  have hψs : Function.Surjective ψ := by
    intro d
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective d
    have hlJ : (l : G) ∈ (J : Set G) * (inSubgroup (aschbacherSolvableCore 3) L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right J _
        (hJL.trans (Sec6.le_normalizer_theta L))]
      exact hcov l.2
    obtain ⟨j, hj, k, hk, hjk⟩ := hlJ
    refine ⟨⟨j, hj⟩, ?_⟩
    rw [← hl]
    apply QuotientGroup.eq.mpr
    obtain ⟨k', hk', rfl⟩ := hk
    have : (Subgroup.inclusion hJL ⟨j, hj⟩)⁻¹ * l = k' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hjk]
      simp
    rw [this]
    exact hk'
  set Z₀ : Subgroup J := (Sec4.thetaQuotCentralizer Lx).subgroupOf J with hZ₀
  have hZ₀n : Z₀.Normal := by
    refine ⟨fun z hz g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Sec6.conj_mem_thetaQuotCentralizer hz (Subgroup.le_normalizer (hJLx g.2))
  have hZ₀s : Group.IsSolvable Z₀ := by
    set ζ : Z₀ →* Lx ⧸ aschbacherSolvableCore 3 Lx :=
      (QuotientGroup.mk' (aschbacherSolvableCore 3 Lx)).comp
        ((Subgroup.inclusion hJLx).comp Z₀.subtype) with hζ
    have hcomm : ∀ a b : ζ.range, a * b = b * a := by
      have hcent : ∀ z : Z₀, ζ z ∈ Subgroup.center (Lx ⧸ aschbacherSolvableCore 3 Lx) := by
        intro z
        have hzC : ((z : J) : G) ∈ Sec4.thetaQuotCentralizer Lx := z.2
        have hzL : ((z : J) : G) ∈ Lx := hJLx (z : J).2
        obtain ⟨hzN, h1⟩ := Sec4.Item424Proof.mem_thetaQuotCentralizer_iff_eq_one.mp hzC
        rw [KFacts.thetaQuotMulAut_compAction_of_mem hzL hzN] at h1
        rw [Subgroup.mem_center_iff]
        intro w
        have := congrArg (fun σ : MulAut (Lx ⧸ aschbacherSolvableCore 3 Lx) => σ w) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        have hζz : ζ z = QuotientGroup.mk' (aschbacherSolvableCore 3 Lx) ⟨_, hzL⟩ := rfl
        rw [hζz]
        calc w * QuotientGroup.mk' (aschbacherSolvableCore 3 Lx) ⟨_, hzL⟩ =
            (QuotientGroup.mk' (aschbacherSolvableCore 3 Lx) ⟨_, hzL⟩ * w *
              (QuotientGroup.mk' (aschbacherSolvableCore 3 Lx) ⟨_, hzL⟩)⁻¹) *
                QuotientGroup.mk' (aschbacherSolvableCore 3 Lx) ⟨_, hzL⟩ := by rw [this]
          _ = _ := by group
      rintro ⟨_, ⟨a, rfl⟩⟩ ⟨_, ⟨b, rfl⟩⟩
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp (hcent b) (ζ a))
    have hR : Group.IsSolvable ζ.range := Group.isSolvable_of_comm hcomm
    have hK : Group.IsSolvable ζ.ker := by
      have hθs : Group.IsSolvable (aschbacherSolvableCore 3 Lx) :=
        (solvable_prime_complement_core_characterization (H := Lx) Nat.prime_three).1
      set ι : ζ.ker →* aschbacherSolvableCore 3 Lx :=
        { toFun := fun k => ⟨Subgroup.inclusion hJLx (k : Z₀), by
            have := (MonoidHom.mem_ker).mp k.2
            exact (QuotientGroup.eq_one_iff _).mp this⟩
          map_one' := rfl
          map_mul' := fun a b => rfl }
      refine Group.isSolvable_of_isSolvable_injective (f := ι) ?_
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun t : aschbacherSolvableCore 3 Lx => ((t : Lx) : G)) hab
      exact this
    exact Group.isSolvable_of_ker_le_range ζ.ker.subtype ζ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  have hN : (Z₀.map ψ).Normal := hZ₀n.map ψ hψs
  have hNs : Group.IsSolvable (Z₀.map ψ) := by
    haveI := hZ₀s
    exact Group.isSolvable_of_surjective (f := ψ.subgroupMap Z₀) (ψ.subgroupMap_surjective Z₀)
  have hN1 := eq_bot_of_isSolvable_of_normal hLq hZ hN hNs
  intro s hs
  have hsZ : (⟨s, hS₀J hs⟩ : J) ∈ Z₀ := Subgroup.mem_subgroupOf.mpr (hS₀C hs)
  have himg : ψ ⟨s, hS₀J hs⟩ = 1 := by
    have : ψ ⟨s, hS₀J hs⟩ ∈ Z₀.map ψ := Subgroup.mem_map_of_mem ψ hsZ
    rwa [hN1, Subgroup.mem_bot] at this
  have hθ : (⟨s, hJL (hS₀J hs)⟩ : L) ∈ aschbacherSolvableCore 3 L :=
    (QuotientGroup.eq_one_iff _).mp himg
  exact ⟨_, hθ, rfl⟩

theorem exists_hessian_projImage {K : Type} [Field K] {π : Bool} {p f : ℕ}
    (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f)) :
    ∃ j d : projImage (Sec4.slPi π 3 (p ^ f) K), j ^ 3 = 1 ∧ j ≠ 1 ∧ d ^ 3 = 1 ∧ j * d = d * j ∧
      d ∉ Subgroup.zpowers j := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  have hq' : π = false → Sec4.ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set H := Sec4.slPi π 3 (p ^ f) K with hH
  have hJ := Sec4.diagTau_mem_slPi hπ hq' hτ
  have hD := Sec4.cycThree_mem_slPi (p := p) (f := f) (K := K) hπ
  set j := Sec4.projOf H ⟨Sec4.diagTau hτ, hJ⟩ with hjdef
  set d := Sec4.projOf H ⟨Sec4.cycThree, hD⟩ with hddef
  have hjc : (j : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (Sec4.diagTau hτ) :=
    Sec4.coe_projOf H _
  have hdc : (d : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk Sec4.cycThree :=
    Sec4.coe_projOf H _
  have hjpow : ∀ m : ℕ, ((j ^ m : projImage H) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (Sec4.diagTau hτ ^ m) := fun m => by rw [Subgroup.coe_pow, hjc, map_pow]
  have hj3 : j ^ 3 = 1 := Subtype.ext (by rw [hjpow, Sec4.diagTau_pow_three hτ, map_one]; rfl)
  refine ⟨j, d, hj3, fun h1 => ?_, Subtype.ext ?_, Subtype.ext ?_, fun hmem => ?_⟩
  · have h' : ProjGenLinGroup.mk (Sec4.diagTau hτ) = 1 := by rw [← hjc, h1]; rfl
    refine mk_ne_one_of_diag_ne (i := 0) (k := 2) ?_ h'
    simpa [Sec4.coe_diagTau] using hτ1
  · rw [Subgroup.coe_pow, hdc, ← map_pow, KFacts.cycThree_pow_three, map_one]
    rfl
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, hjc, hdc, ← map_mul, ← map_mul,
      mk_diagTau_mul_cycThree hτ hτ0]
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have hk' : j ^ k = j ^ ((k % 3).toNat) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg h0]
      exact zpow_eq_zpow_emod' k hj3
    have hlt : (k % 3).toNat < 3 := by omega
    apply mk_diagTau_pow_ne_cycThree hτ hτ0 hlt
    rw [← hjpow, ← hdc, ← hk, hk']

theorem exists_e9_in {L J : Subgroup G} (hJL : J ≤ L)
    (hcov : L ≤ J ⊔ inSubgroup (aschbacherSolvableCore 3) L) {n : ℕ} (hn : 1 ≤ n)
    (hq2 : 2 ^ n % 3 = 2)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃*
      (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; projSU 3 2 n)) :
    ∃ r₁ ∈ J, ∃ r₂ ∈ J, r₁ ^ 3 = 1 ∧ r₂ ^ 3 = 1 ∧ r₁ * r₂ = r₂ * r₁ ∧ r₁ ≠ 1 ∧
      r₂ ∉ Subgroup.zpowers r₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKF := Sec13.piField_galoisField_two 2 n hn
  obtain ⟨j₀, d₀, hj3, hj1, hd3, hjd, hdj⟩ := exists_hessian_projImage hKF hq2
  set ψ := φ.trans (MulEquiv.subgroupCongr (Sec4.projSU_eq_projImage 2 n)) with hψ
  set a := ψ.symm j₀ with ha
  set b := ψ.symm d₀ with hb
  have ha3 : a ^ 3 = 1 := by rw [ha, ← map_pow, hj3, map_one]
  have hb3 : b ^ 3 = 1 := by rw [hb, ← map_pow, hd3, map_one]
  have hab : a * b = b * a := by rw [ha, hb, ← map_mul, ← map_mul, hjd]
  have ha1 : a ≠ 1 := fun h1 => hj1 (by simpa [ha] using congrArg ψ h1)
  have hba : b ∉ Subgroup.zpowers a := by
    intro hmem
    apply hdj
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg ψ hk
    simpa [ha, hb] using this
  obtain ⟨r₁, hr₁J, hr₁L, hr₁a, hr₁3⟩ := exists_lift_three_in hJL hcov ha3
  obtain ⟨m, hmJ, hmL, hmb, -⟩ := exists_lift_three_in hJL hcov hb3
  have hr₁N : r₁ ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hr₁L
  have hr₁NJ : r₁ ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hr₁J
  obtain ⟨m', hm'r, hm'b⟩ := Sec8.Hering88F.exists_mem_centralizer_of_fixed (Y := L) (M := J)
    hJL hr₁N hr₁NJ hr₁3 hmJ (by
      rw [KFacts.thetaQuotMulAut_compAction_of_mem hr₁L hr₁N, MulAut.conj_apply]
      change ((⟨r₁, hr₁L⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) * _ *
        ((⟨r₁, hr₁L⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)⁻¹ = _
      rw [hr₁a, hmb, hab, mul_inv_cancel_right])
  have hm'b' : ((⟨m', hJL m'.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = b := hm'b.trans hmb
  obtain ⟨k, hkb, hk3⟩ := exists_pow_lift_three (⟨m', hJL m'.2⟩ : L) hm'b' hb3
  set r₂ : G := (((⟨m', hJL m'.2⟩ : L) ^ k : L) : G) with hr₂
  have hr₂J : r₂ ∈ J := by
    rw [hr₂, Subgroup.coe_pow]
    exact J.pow_mem m'.2 k
  have hm'r' : (m' : G) * r₁ = r₁ * m' := Subgroup.mem_centralizer_singleton_iff.mp hm'r
  refine ⟨r₁, hr₁J, r₂, hr₂J, hr₁3, ?_, ?_, fun h1 => ha1 ?_, fun hmem => hba ?_⟩
  · rw [hr₂, ← Subgroup.coe_pow, hk3, Subgroup.coe_one]
  · rw [hr₂, Subgroup.coe_pow]
    exact ((Commute.pow_left (show Commute (m' : G) r₁ from hm'r') k).eq).symm
  · rw [← hr₁a]
    have : (⟨r₁, hr₁L⟩ : L) = 1 := Subtype.ext h1
    rw [this, QuotientGroup.mk_one]
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    rw [← hr₁a, ← hkb, ← QuotientGroup.mk_zpow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hi

theorem mem_normalizer_sup {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem mem_normalizer_commutator {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_commutator, hH, hK]

theorem step13PZeroLx_of (h48 : Sec4.Item4_8) : Step13PZeroLx := by
  intro G _ _ A c L P₀ n hU S₀ hS₀ hS₀2 hS₀J₀ hS₀θ x hxP hxc hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hU.sec13
  have hEFeq : partTwoF G = partTwoE G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hc := h.orderOf_eq
  have hc3 : c ^ 3 = 1 := hc ▸ pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := h.ne_one
  have hLc := h.le_centralizer
  have hL := h.mem_thetaComponentsAt
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hL
  have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hL
  obtain ⟨φ⟩ := hU.iso
  have hn1 : 1 ≤ n := by have := hU.one_lt; omega
  have hq2 : 2 ^ n % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hU.odd
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hL3 : IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) :=
    ⟨2, n, ⟨Nat.prime_two⟩, hn1, Or.inr ⟨hq2, ⟨φ⟩⟩⟩
  have hZ := center_eq_bot_of_isLThreePi hLq hL3
  have hP₀e := hU.elem
  have hP₀9 := hU.card
  have hcP := hU.mem
  have hP₀3 : IsPGroup 3 P₀ := CFSG.Open.IsElemAbelian.isPGroup hP₀e
  have hx3 : x ^ 3 = 1 := hP₀e.2 x hxP
  have hx1 : x ≠ 1 := fun h1 => hxc (h1 ▸ Subgroup.one_mem _)
  have hcx : c * x = x * c := congrArg Subtype.val (hP₀e.1.is_comm.comm ⟨c, hcP⟩ ⟨x, hxP⟩)
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  have hCeq : L ⊓ Subgroup.centralizer (P₀ : Set G) =
      L ⊓ Subgroup.centralizer ({x} : Set G) := by
    ext l
    constructor
    · rintro ⟨hl, hlP⟩
      exact ⟨hl, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hlP x hxP).symm⟩
    · rintro ⟨hl, hlx⟩
      refine ⟨hl, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      exact (forall_commute_of_commute hP₀e hP₀9 hc hcP hxP hxc
        (Subgroup.mem_centralizer_singleton_iff.mp (hLc hl))
        (Subgroup.mem_centralizer_singleton_iff.mp hlx) q hq).symm
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({x} : Set G)) with hJdef
  have hJeq : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (P₀ : Set G)) = J := by
    rw [hCeq]
  have hcov : L ≤ J ⊔ θL := by
    have := Sec6.le_residual_inf_centralizer_sup_theta hLp hP₀3 hU.le
    rwa [hJeq] at this
  have hJL : J ≤ L := (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  have hJP : J ≤ Subgroup.centralizer (P₀ : Set G) := by
    rw [← hJeq]
    exact (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_right
  have hS₀J : S₀ ≤ J := hJeq ▸ hS₀J₀
  have hP₀L : ∀ q ∈ P₀, q ∈ L → q = 1 := fun q hq hqL =>
    eq_one_of_mem_inSubgroup_theta (k := 1)
      (Sec4.Item424Proof.mem_theta_of_mem_thetaQuotCentralizer hZ hqL (hU.le hq))
      (by simpa using hP₀e.2 q hq)
  obtain ⟨r₁, hr₁J, r₂, hr₂J, hr₁3, hr₂3, hr₁₂, hr₁1, hr₂r₁⟩ := exists_e9_in hJL hcov hn1 hq2 φ
  have hr₁o : orderOf r₁ = 3 := orderOf_eq_prime hr₁3 hr₁1
  set R₀ : Subgroup G := Subgroup.zpowers r₁ ⊔ Subgroup.zpowers r₂ with hR₀
  have hR₀J : R₀ ≤ J := sup_le (Subgroup.zpowers_le.mpr hr₁J) (Subgroup.zpowers_le.mpr hr₂J)
  have hR₀e : CFSG.Assembly.IsElemAbelian 3 R₀ := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hr₁3)
      (CFSG.Open.isElemAbelian_zpowers hr₂3) ?_
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (show Commute r₁ r₂ from hr₁₂) i j).eq
  have hR₀9 : Nat.card R₀ = 9 := card_sup_zpowers_eq_nine hr₁o hr₂3 hr₂r₁ hr₁₂
  have hR₀P : ∀ q ∈ P₀, ∀ r ∈ R₀, q * r = r * q := fun q hq r hr =>
    (Subgroup.mem_centralizer_iff.mp (hJP (hR₀J hr)) q hq)
  set A₀ : Subgroup G := P₀ ⊔ R₀ with hA₀
  have hA₀e : CFSG.Assembly.IsElemAbelian 3 A₀ :=
    CFSG.Open.IsElemAbelian.sup_of_commute hP₀e hR₀e hR₀P
  have hinfPR : R₀ ⊓ P₀ = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    exact hP₀L q hq.2 (hJL (hR₀J hq.1))
  have hRN : R₀ ≤ Subgroup.normalizer (P₀ : Set G) := by
    intro r hr
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun q hq => ?_)
    exact hR₀P q hq r hr
  have hA₀81 : Nat.card A₀ = 81 := by
    have := Sec6.card_sup_mul_card_inf hRN
    rw [hinfPR, Subgroup.card_bot, mul_one, hR₀9, hP₀9, sup_comm] at this
    rw [hA₀]
    omega
  have hA₀x : A₀ ≤ Subgroup.centralizer ({x} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hA₀e.1.is_comm.comm ⟨a, ha⟩ ⟨x, Subgroup.mem_sup_left hxP⟩)
  have hcA₀ : c ∈ A₀ := Subgroup.mem_sup_left hcP
  have hD3 : IsPGroup 3 (Subgroup.zpowers x) := Sec6.isPGroup_zpowers_of_pow_three hx3
  have hDC : Subgroup.zpowers x ≤ Sec4.thetaQuotCentralizer L :=
    Subgroup.zpowers_le.mpr (hU.le hxP)
  have hY := Sec6.residual_inf_centralizer_mem_thetaComponentsIn hL hD3 hDC
  rw [Sec6.centralizer_zpowers_eq] at hY
  have hM : SectionFourHyp (Subgroup.centralizer ({x} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hx1)
  obtain ⟨Lx, hLx, hJLx⟩ := Sec6.exists_le_mem_thetaComponentsIn h48 hM hA₀x hA₀e
    ⟨4, by norm_num, by rw [hA₀81]; norm_num⟩ hcA₀ hc1 hY
  have hJp : Group.IsPerfect J := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hJ1 : J ≠ ⊥ := by
    have := Sec6.residual_inf_centralizer_ne_bot hLp hLq hD3 hDC
    rwa [Sec6.centralizer_zpowers_eq] at this
  have hcN : c ∈ Subgroup.normalizer (Lx : Set G) := by
    have hcx' : c * x * c⁻¹ ∈ Subgroup.zpowers x := by
      rw [hcx, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers x
    have hLxc := Sec11.map_conj_mem_thetaComponentsAt hx3 hLx hcx'
    have hJc : J ≤ Lx.map (MulAut.conj c).toMonoidHom := by
      intro j hj
      refine ⟨j, hJLx hj, ?_⟩
      change c * j * c⁻¹ = j
      rw [← Subgroup.mem_centralizer_singleton_iff.mp (hLc (hJL hj)), mul_inv_cancel_right]
    exact Sec13.map_conj_eq_iff_mem_normalizer.mp
      (Sec6.eq_of_mem_thetaComponentsIn_of_le hLxc hLx hJp hJ1 hJc hJLx)
  refine ⟨Lx, hLx, hJLx, hcN, fun hcC => ?_⟩
  set M := Subgroup.normalizer (S₀ : Set G) with hMdef
  set T := CFSG.Open.pCoreOf 2 M with hTdef
  obtain ⟨hT2', hTM', hMT'⟩ := CFSG.RankThree.GF2n.inSubgroup_pCore_two M
  have hT2 : IsPGroup 2 T := hT2'
  have hTM : T ≤ M := hTM'
  have hMT : M ≤ Subgroup.normalizer (T : Set G) := hMT'
  set X₁ := T ⊓ Subgroup.centralizer ({x} : Set G) with hX₁
  have hX₁N : X₁ ≤ Subgroup.normalizer (Lx : Set G) := by
    intro g hg
    have hgS : g ∈ M := hTM hg.1
    have hgx : g * x * g⁻¹ ∈ Subgroup.zpowers x := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hg.2, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers x
    have hLxg := Sec11.map_conj_mem_thetaComponentsAt hx3 hLx hgx
    by_contra hgN
    have hne : Lx.map (MulAut.conj g).toMonoidHom ≠ Lx := fun heq =>
      hgN (Sec13.map_conj_eq_iff_mem_normalizer.mp heq)
    have hle := Sec14.BalTools.le_thetaQuotCentralizer_of_ne_in hLxg hLx hne
    apply hS₀θ
    refine le_theta_of_le_thetaQuotCentralizer hLq hZ hJL hcov hJLx hS₀J ?_
    intro s hs
    apply hle
    have hs' : g⁻¹ * s * g⁻¹⁻¹ ∈ S₀ := (Subgroup.mem_normalizer_iff.mp (inv_mem hgS) s).mp hs
    refine ⟨g⁻¹ * s * g⁻¹⁻¹, hJLx (hS₀J hs'), ?_⟩
    change g * (g⁻¹ * s * g⁻¹⁻¹) * g⁻¹ = s
    group
  have hczC : Subgroup.zpowers c ≤ Sec4.thetaQuotCentralizer Lx := Subgroup.zpowers_le.mpr hcC
  set S := ⁅X₁, Subgroup.zpowers c⁆ with hSdef
  have hSC : S ≤ Sec4.thetaQuotCentralizer Lx := by
    rw [hSdef, Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    refine Subgroup.mul_mem _ (Sec6.conj_mem_thetaQuotCentralizer (hczC hh) (hX₁N hg))
      (Subgroup.inv_mem _ (hczC hh))
  have hcM : c ∈ M := by
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun s hs => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLc (hJL (hS₀J hs)))
  have hcX₁ : Subgroup.zpowers c ≤ Subgroup.normalizer (X₁ : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro g
    have hcT := Subgroup.mem_normalizer_iff.mp (hMT hcM) g
    constructor
    · rintro ⟨hgT, hgx⟩
      refine ⟨hcT.mp hgT, ?_⟩
      change g ∈ Subgroup.centralizer ({x} : Set G) at hgx
      show c * g * c⁻¹ ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff] at hgx ⊢
      calc c * g * c⁻¹ * x = c * g * (c⁻¹ * x * c) * c⁻¹ := by group
        _ = c * g * x * c⁻¹ := by rw [show c⁻¹ * x * c = x by rw [mul_assoc, ← hcx]; group]
        _ = c * (x * g) * c⁻¹ := by rw [mul_assoc c g x, hgx]
        _ = (c * x * c⁻¹) * (c * g * c⁻¹) := by group
        _ = x * (c * g * c⁻¹) := by rw [hcx, mul_inv_cancel_right]
    · rintro ⟨hgT, hgx⟩
      refine ⟨hcT.mpr hgT, ?_⟩
      change c * g * c⁻¹ ∈ Subgroup.centralizer ({x} : Set G) at hgx
      show g ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff] at hgx ⊢
      have hx' : c⁻¹ * x * c = x := by rw [mul_assoc, ← hcx]; group
      have h1 : c⁻¹ * (c * g * c⁻¹ * x) * c = c⁻¹ * (x * (c * g * c⁻¹)) * c := by rw [hgx]
      calc g * x = g * (c⁻¹ * x * c) := by rw [hx']
        _ = c⁻¹ * (c * g * c⁻¹ * x) * c := by group
        _ = c⁻¹ * (x * (c * g * c⁻¹)) * c := h1
        _ = (c⁻¹ * x * c) * g := by group
        _ = x * g := by rw [hx']
  have hSX₁ : S ≤ X₁ := by
    rw [hSdef, Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    have h1 : h * g⁻¹ * h⁻¹ ∈ X₁ :=
      (Subgroup.mem_normalizer_iff.mp (hcX₁ hh) g⁻¹).mp (X₁.inv_mem hg)
    have h2 := X₁.mul_mem hg h1
    rwa [show g * (h * g⁻¹ * h⁻¹) = g * h * g⁻¹ * h⁻¹ by group] at h2
  have hS2 : IsPGroup 2 S := hT2.to_le (hSX₁.trans inf_le_left)
  set θLx := inSubgroup (aschbacherSolvableCore 3) Lx with hθLx
  set W₀ := S ⊔ θLx with hW₀
  have hSθN : S ≤ Subgroup.normalizer (θLx : Set G) :=
    hSC.trans ((Sec6.thetaQuotCentralizer_le_normalizer Lx).trans
      (Sec6.normalizer_le_normalizer_theta Lx))
  have hθLx3 : ¬ 3 ∣ Nat.card θLx := by
    rw [hθLx, inSubgroup, Subgroup.card_map_of_injective Lx.subtype_injective]
    exact KFacts.not_three_dvd_card_aschbacherSolvableCore Lx
  have hS3 : ¬ 3 ∣ Nat.card S := by
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hW3 : ¬ 3 ∣ Nat.card W₀ := by
    intro h3
    have hmul := Sec6.card_sup_mul_card_inf hSθN
    have h3' : 3 ∣ Nat.card S * Nat.card θLx := by
      rw [← hmul]
      exact Dvd.dvd.mul_right h3 _
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3' with h | h
    · exact hS3 h
    · exact hθLx3 h
  have hW2 : 2 ∣ Nat.card W₀ := by
    have h1 : 2 ∣ Nat.card S := by
      obtain ⟨k, hk⟩ := hS2.exists_card_eq
      rw [hk]
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · exfalso
        rw [h0, pow_zero] at hk
        exact hS (Subgroup.eq_bot_of_card_eq S hk)
      · exact dvd_pow_self 2 hpos.ne'
    exact h1.trans (Subgroup.card_dvd_of_le le_sup_left)
  have hP₀Lx : P₀ ≤ Subgroup.normalizer (Lx : Set G) := by
    refine le_of_mem_of_mem hP₀e hP₀9 hc hcP hxP hxc hcN ?_
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun l hl => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (Sec6.le_centralizer_of_mem_thetaComponentsAt hLx hl)
  have hP₀W : P₀ ≤ Subgroup.normalizer (W₀ : Set G) := by
    intro q hq
    have hqM : q ∈ M := by
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun t ht => ?_)
      exact (Subgroup.mem_centralizer_iff.mp (hJP (hS₀J ht)) q hq).symm
    have hqT := hMT hqM
    have hqx : q * x = x * q := congrArg Subtype.val (hP₀e.1.is_comm.comm ⟨q, hq⟩ ⟨x, hxP⟩)
    have hqX₁ : q ∈ Subgroup.normalizer (X₁ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      have hgT := Subgroup.mem_normalizer_iff.mp hqT g
      have hgC := Subgroup.mem_normalizer_iff.mp
        (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hqx)) g
      exact and_congr hgT hgC
    have hqZ : q ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hqc : q * c = c * q := congrArg Subtype.val (hP₀e.1.is_comm.comm ⟨q, hq⟩ ⟨c, hcP⟩)
      exact (Commute.zpow_left (show Commute c q from hqc.symm) k).eq
    have hqS : q ∈ Subgroup.normalizer (S : Set G) := mem_normalizer_commutator hqX₁ hqZ
    have hqθ : q ∈ Subgroup.normalizer (θLx : Set G) :=
      Sec6.normalizer_le_normalizer_theta Lx (hP₀Lx hq)
    exact mem_normalizer_sup hqS hqθ
  have hR₀W : R₀ ≤ Subgroup.normalizer (W₀ : Set G) := by
    intro r hr
    have hrLx : r ∈ Lx := hJLx (hR₀J hr)
    refine mem_normalizer_of_conj_mem_of_pow_three (hR₀e.2 r hr) fun w hw => ?_
    have hle : W₀ ≤ W₀.comap (MulAut.conj r).toMonoidHom := by
      refine sup_le (fun t ht => ?_) (fun t ht => ?_)
      · change r * t * r⁻¹ ∈ W₀
        have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp (hSC ht)).2 r⁻¹ (Lx.inv_mem hrLx)
        have h2 : r * t * r⁻¹ = (r⁻¹⁻¹ * (t * r⁻¹ * t⁻¹)) * t := by group
        rw [h2]
        exact W₀.mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left ht)
      · change r * t * r⁻¹ ∈ W₀
        exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta Lx hrLx) t).mp ht)
    exact hle hw
  have hA₀W : A₀ ≤ Subgroup.normalizer (W₀ : Set G) := sup_le hP₀W hR₀W
  have hA₀3 : IsPGroup 3 A₀ := CFSG.Open.IsElemAbelian.isPGroup hA₀e
  obtain ⟨Q, hSyl, -, hA₀Q⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    (r := 3) (q := 2) Nat.prime_three Nat.prime_two hA₀3 hW3 hA₀W bot_le IsPGroup.of_bot
    (by intro b _; exact Subgroup.mem_normalizer_iff.mpr fun h => by simp)
  have hQne : Q ≠ ⊥ := by
    intro hQ
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := W₀) 2 hW2
    have hP : Subgroup.zpowers (t : G) = Q := by
      refine hSyl.2.2 _ ?_ ?_ (hQ ▸ bot_le)
      · rw [Subgroup.zpowers_le]
        exact t.2
      · refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht, pow_one]
    have ht1 : (t : G) ∈ (⊥ : Subgroup G) := hQ ▸ hP ▸ Subgroup.mem_zpowers (t : G)
    have : t = 1 := Subtype.ext (Subgroup.mem_bot.mp ht1)
    rw [this, orderOf_one] at ht
    omega
  set B : Subgroup G := P₀ ⊔ Subgroup.zpowers r₁ with hBdef
  have hBA : B ≤ A₀ := sup_le le_sup_left
    ((Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers r₁))).trans
      le_sup_right)
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := hA₀e.mono hBA
  have hinfB : Subgroup.zpowers r₁ ⊓ P₀ = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    have hqL : q ∈ L := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq.1
      exact L.zpow_mem (hJL hr₁J) k
    exact hP₀L q hq.2 hqL
  have hr₁N : Subgroup.zpowers r₁ ≤ Subgroup.normalizer (P₀ : Set G) :=
    (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers r₁))).trans hRN
  have hB27 : Nat.card B = 27 := by
    have := Sec6.card_sup_mul_card_inf hr₁N
    rw [hinfB, Subgroup.card_bot, mul_one, Nat.card_zpowers, hr₁o, hP₀9, sup_comm] at this
    rw [hBdef]
    omega
  have hBE : B ∈ partTwoE G := ⟨hBe, hB27, Q, hQne, hSyl.2.1, hBA.trans hA₀Q⟩
  exact false_of_mem_partTwoE_lt hEFeq hBE hA₀e hBA (fun h => by
    have := congrArg (fun H : Subgroup G => Nat.card H) h
    rw [hB27, hA₀81] at this
    norm_num at this)

end CFSG.RankThree.PartTwo.Sec13.Ronan138P5
