module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Res
public import CFSG.RankThree.PartTwo.Sec4.Ronan138P5Census
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Ambient
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Lx
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Main
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.KFacts.KS44Transport
import CFSG.RankThree.PartTwo.Sec8.Hering88FCoprime
import CFSG.RankThree.PartTwo.Sec11.Item116R1Quot
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138P5

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem theta_le_thetaQuotCentralizer (L : Subgroup G) :
    inSubgroup (aschbacherSolvableCore 3) L ≤ Sec4.thetaQuotCentralizer L := by
  rintro _ ⟨t, ht, rfl⟩
  have htL : L.subtype t ∈ L := t.2
  have htN : L.subtype t ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer htL
  refine Sec4.Item424Proof.mem_thetaQuotCentralizer_iff_eq_one.mpr ⟨htN, ?_⟩
  rw [KFacts.thetaQuotMulAut_compAction_of_mem htL htN]
  have : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨L.subtype t, htL⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ht
  rw [this, map_one]

section Kinds


theorem typed419_of (hC : Sec4.K419UnitaryCensusCover) (h46 : Sec4.Item4_6) {A : Subgroup G}
    {c : G} {L P₀ : Subgroup G} {n : ℕ} (hU : PZeroU3 G A c L P₀ n) {x : G} (hxP : x ∈ P₀)
    (hxc : x ∉ Subgroup.zpowers c) {Lx : Subgroup G} (hLx : Lx ∈ thetaComponentsAt 3 x)
    (hJLx : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({x} : Set G)) ≤ Lx)
    (hcN : c ∈ Subgroup.normalizer (Lx : Set G)) (hcLx : c ∉ Sec4.thetaQuotCentralizer Lx) :
    (∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 (3 * n) K),
        InducesKindPSU3 h Lx c .field) ∨
      (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ n) ^ 3 ∧
        ∃ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ n) ∧ InducesKindTriality σ Lx c .graphField) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hU.sec13
  have hc := h.orderOf_eq
  have hc3 : c ^ 3 = 1 := hc ▸ pow_orderOf_eq_one c
  have hLc := h.le_centralizer
  have hL := h.mem_thetaComponentsAt
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hL
  have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hL
  obtain ⟨eL⟩ := hU.iso
  have hn1 : 1 ≤ n := by have := hU.one_lt; omega
  have hq2 : 2 ^ n % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hU.odd
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hL3 : IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) :=
    ⟨2, n, ⟨Nat.prime_two⟩, hn1, Or.inr ⟨hq2, ⟨eL⟩⟩⟩
  have hZ := center_eq_bot_of_isLThreePi hLq hL3
  have hP₀e := hU.elem
  have hx3 : x ^ 3 = 1 := hP₀e.2 x hxP
  have hx1 : x ≠ 1 := fun h1 => hxc (h1 ▸ Subgroup.one_mem _)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({x} : Set G)) with hJdef
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set θx := inSubgroup (aschbacherSolvableCore 3) Lx with hθx
  have hJL : J ≤ L := (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  have hJc : J ≤ Subgroup.centralizer ({c} : Set G) := hJL.trans hLc
  have hxL : Subgroup.zpowers x ≤ Sec4.thetaQuotCentralizer L :=
    Subgroup.zpowers_le.mpr (hU.le hxP)
  have hcov : L ≤ J ⊔ θL := by
    have := Sec6.le_residual_inf_centralizer_sup_theta hLp
      (Sec6.isPGroup_zpowers_of_pow_three hx3) hxL
    rwa [Sec6.centralizer_zpowers_eq] at this
  have hJperf : Group.IsPerfect J := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hJθ : J ∈ thetaComponentsIn
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) := by
    have := Sec6.residual_inf_centralizer_mem_thetaComponentsIn hL
      (Sec6.isPGroup_zpowers_of_pow_three hx3) hxL
    rwa [Sec6.centralizer_zpowers_eq] at this
  set N := Subgroup.normalizer (Lx : Set G) with hNdef
  have hLxN : Lx ≤ N := Subgroup.le_normalizer
  have hNθ : N ≤ Subgroup.normalizer (θx : Set G) := Sec6.normalizer_le_normalizer_theta Lx
  set T : Subgroup N := θx.subgroupOf N with hT
  have hTn : T.Normal := by
    refine ⟨fun t ht g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hNθ g.2) t).mp ht
  set φ : N →* N ⧸ T := QuotientGroup.mk' T with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective T
  have hφ1 : ∀ g : N, φ g = 1 ↔ (g : G) ∈ θx := fun g => by
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hφeq : ∀ g g' : N, φ g = φ g' ↔ (g : G)⁻¹ * g' ∈ θx := fun g g' => by
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hqeq : ∀ u v : Lx, (u : Lx ⧸ aschbacherSolvableCore 3 Lx) = v ↔ (u : G)⁻¹ * v ∈ θx := by
    intro u v
    rw [QuotientGroup.eq]
    constructor
    · intro huv
      exact ⟨_, huv, by simp⟩
    · rintro ⟨t, ht, hte⟩
      have : u⁻¹ * v = t := Subtype.ext (by simpa using hte.symm)
      rwa [this]
  set L₁ : Subgroup N := Lx.subgroupOf N with hL₁
  set L' : Subgroup (N ⧸ T) := L₁.map φ with hL'
  set e₀ : L₁ ≃* Lx := Subgroup.subgroupOfEquivOfLe hLxN with he₀
  have hθ₁ : ∀ l : L₁, l ∈ aschbacherSolvableCore 3 L₁ ↔ ((l : N) : G) ∈ θx := by
    intro l
    have hmap := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e₀
    have h1 : l ∈ aschbacherSolvableCore 3 L₁ ↔ e₀ l ∈ aschbacherSolvableCore 3 Lx := by
      rw [← hmap, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    have h2 : e₀ l ∈ aschbacherSolvableCore 3 Lx ↔ ((e₀ l : Lx) : G) ∈ θx :=
      (Subgroup.mem_map_iff_mem Lx.subtype_injective).symm
    rw [h1, h2]
    rfl
  set f₁ : L₁ →* L' := φ.subgroupMap L₁ with hf₁
  have hf₁s : Function.Surjective f₁ := φ.subgroupMap_surjective L₁
  have hf₁k : f₁.ker = aschbacherSolvableCore 3 L₁ := by
    ext l
    rw [MonoidHom.mem_ker, hθ₁]
    constructor
    · intro hl
      have : φ (l : N) = 1 := congrArg Subtype.val hl
      exact (hφ1 _).mp this
    · intro hl
      exact Subtype.ext ((hφ1 _).mpr hl)
  set E₁ : L₁ ⧸ aschbacherSolvableCore 3 L₁ ≃* L' :=
    (QuotientGroup.quotientMulEquivOfEq hf₁k.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f₁ hf₁s) with hE₁
  have hθ' : aschbacherSolvableCore 3 L' = ⊥ := by
    rw [← CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three E₁,
      Sec11.aschbacherSolvableCore_quotient_eq_bot, Subgroup.map_bot]
  have hcond : ∀ l : L₁, φ.subgroupMap L₁ l ∈ aschbacherSolvableCore 3 (L₁.map φ) ↔
      l ∈ aschbacherSolvableCore 3 L₁ := by
    intro l
    rw [hθ', Subgroup.mem_bot, ← hf₁k, MonoidHom.mem_ker]
  have hLxq : CFSG.IsQuasisimple (Lx ⧸ aschbacherSolvableCore 3 Lx) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hLx
  set e₁ : L₁ ⧸ aschbacherSolvableCore 3 L₁ ≃* Lx ⧸ aschbacherSolvableCore 3 Lx :=
    QuotientGroup.congr _ _ e₀
      (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e₀) with he₁
  have hL'q : CFSG.IsQuasisimple L' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (e₁.symm.trans E₁) hLxq
  have hL₁n : L₁.Normal := Subgroup.normal_in_normalizer
  have hL'n : L'.Normal := hL₁n.map φ hφs
  have hL'c : IsComponent L' := ⟨hL'q, hL'n.isSubnormal⟩
  have hM : SectionFourHyp (Subgroup.centralizer ({x} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hx1)
  have hL'46 : Sec4.IsList46 (L' ⧸ aschbacherSolvableCore 3 L') :=
    Sec21.Item223PrintProof.isList46_of_mulEquiv (e₁.symm.trans (thetaQuotEquivOfMap φ L₁ hcond))
      (isList46_of_mem_thetaComponentsAt h46 hxo hM hLx)
  set c' : N := ⟨c, hcN⟩ with hc'
  set a : N ⧸ T := φ c' with ha
  have hcθx : c ∉ θx := fun hcθ => hcLx (theta_le_thetaQuotCentralizer Lx hcθ)
  have ha3 : a ^ 3 = 1 := by
    have : c' ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hc3)
    rw [ha, ← map_pow, this, map_one]
  have ha1 : a ≠ 1 := fun h1 => hcθx ((hφ1 c').mp h1)
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have haN : a ∈ Subgroup.normalizer (L' : Set (N ⧸ T)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hL'n]
    exact Subgroup.mem_top a
  have hconj : ∀ l : Lx, φ ⟨c * l * c⁻¹, hLxN ((Subgroup.mem_normalizer_iff.mp hcN l).mp l.2)⟩ =
      a * φ ⟨l, hLxN l.2⟩ * a⁻¹ := by
    intro l
    rw [ha, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have haC : a ∉ Subgroup.centralizer (L' : Set (N ⧸ T)) := by
    intro haC
    apply hcLx
    refine Sec4.Item424Proof.mem_thetaQuotCentralizer_iff_eq_one.mpr ⟨hcN, ?_⟩
    ext q
    induction q using QuotientGroup.induction_on with
    | H l =>
      change ((Lx.normalizerMonoidHom ⟨c, hcN⟩ l : Lx) : Lx ⧸ aschbacherSolvableCore 3 Lx) =
        (l : Lx ⧸ _)
      rw [hqeq, Sec4.normalizerMonoidHom_apply_coe]
      have hlL' : φ ⟨l, hLxN l.2⟩ ∈ L' :=
        ⟨⟨l, hLxN l.2⟩, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp haC _ hlL'
      have h1 : φ ⟨c * l * c⁻¹, hLxN ((Subgroup.mem_normalizer_iff.mp hcN l).mp l.2)⟩ =
          φ ⟨l, hLxN l.2⟩ := by
        rw [hconj, ← hcomm, mul_inv_cancel_right]
      exact (hφeq _ _).mp h1
  have hJN : J ≤ N := hJLx.trans hLxN
  set χ : J →* N ⧸ T := φ.comp (Subgroup.inclusion hJN) with hχ
  set Y : Subgroup (N ⧸ T) := χ.range with hY
  have hYle : Y ≤ L' ⊓ Subgroup.centralizer ({a} : Set (N ⧸ T)) := by
    rintro _ ⟨j, rfl⟩
    refine ⟨⟨Subgroup.inclusion hJN j, Subgroup.mem_subgroupOf.mpr (hJLx j.2), rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hjc : (j : G) * c = c * j := Subgroup.mem_centralizer_singleton_iff.mp (hJc j.2)
    have : Subgroup.inclusion hJN j * c' = c' * Subgroup.inclusion hJN j := Subtype.ext hjc
    rw [hχ, MonoidHom.comp_apply, ha, ← map_mul, ← map_mul, this]
  have hYperf : Group.IsPerfect Y := by
    haveI := hJperf
    exact Group.IsPerfect.range χ
  set K : Subgroup G := Lx ⊓ Subgroup.centralizer ({c} : Set G) with hK
  have hKN : K ≤ N := inf_le_left.trans hLxN
  have hJK : J ≤ K := le_inf hJLx hJc
  set M : Subgroup G :=
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) with hMdef
  have hLxC : Lx ≤ Subgroup.centralizer ({x} : Set G) := (mem_thetaComponentsIn_iff.mp hLx).1
  have hKM : K ≤ M := inf_le_inf_right _ hLxC
  have hJsnM : (J.subgroupOf M).IsSubnormal := ((mem_thetaComponentsIn_iff.mp hJθ).2).2.1
  have hJsnK : (J.subgroupOf K).IsSubnormal := by
    have : J.subgroupOf K = (J.subgroupOf M).comap (Subgroup.inclusion hKM) := by
      ext k
      simp [Subgroup.mem_subgroupOf]
    rw [this]
    exact hJsnM.comap _
  have hψmem : ∀ k : K, (φ.comp (Subgroup.inclusion hKN)) k ∈
      L' ⊓ Subgroup.centralizer ({a} : Set (N ⧸ T)) := by
    intro k
    refine ⟨⟨Subgroup.inclusion hKN k, Subgroup.mem_subgroupOf.mpr k.2.1, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hkc : (k : G) * c = c * k := Subgroup.mem_centralizer_singleton_iff.mp k.2.2
    have : Subgroup.inclusion hKN k * c' = c' * Subgroup.inclusion hKN k := Subtype.ext hkc
    rw [MonoidHom.comp_apply, ha, ← map_mul, ← map_mul, this]
  set ψ : K →* ↥(L' ⊓ Subgroup.centralizer ({a} : Set (N ⧸ T))) :=
    (φ.comp (Subgroup.inclusion hKN)).codRestrict _ hψmem with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, ⟨l₁, hl₁, rfl⟩, hy⟩
    have hlLx : (l₁ : G) ∈ Lx := Subgroup.mem_subgroupOf.mp hl₁
    have hl₁e : l₁ = ⟨(⟨(l₁ : G), hlLx⟩ : Lx), hLxN hlLx⟩ := rfl
    have hy' : φ l₁ * a = a * φ l₁ := Subgroup.mem_centralizer_singleton_iff.mp hy
    obtain ⟨m', hm'c, hm'l⟩ := Sec8.Hering88F.exists_mem_centralizer_of_fixed (Y := Lx) (M := Lx)
      le_rfl hcN hcN hc3 hlLx (by
        change ((Lx.normalizerMonoidHom ⟨c, hcN⟩ ⟨(l₁ : G), hlLx⟩ : Lx) :
          Lx ⧸ aschbacherSolvableCore 3 Lx) = _
        rw [hqeq, Sec4.normalizerMonoidHom_apply_coe]
        have h1 := hconj ⟨(l₁ : G), hlLx⟩
        rw [← hl₁e, ← hy', mul_inv_cancel_right] at h1
        exact (hφeq _ _).mp h1)
    refine ⟨⟨m', m'.2, hm'c⟩, Subtype.ext ?_⟩
    change φ ⟨(m' : G), hLxN m'.2⟩ = φ l₁
    rw [hl₁e]
    exact (hφeq _ _).mpr ((hqeq _ _).mp hm'l)
  have hYsub : Y.subgroupOf (L' ⊓ Subgroup.centralizer ({a} : Set (N ⧸ T))) =
      (J.subgroupOf K).map ψ := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨⟨j, hJK j.2⟩, Subgroup.mem_subgroupOf.mpr j.2, Subtype.ext ?_⟩
      rw [← hj]
      rfl
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩
  have hYsn : (Y.subgroupOf (L' ⊓ Subgroup.centralizer ({a} : Set (N ⧸ T)))).IsSubnormal := by
    rw [hYsub]
    exact Subgroup.IsSubnormal.map hψs hJsnK
  set π₀ : J →* projSU 3 2 n := eL.toMonoidHom.comp
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hJL)) with hπ₀
  have hπ₀s : Function.Surjective π₀ := by
    intro z
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (eL.symm z)
    have hlJ : (l : G) ∈ (J : Set G) * (θL : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right J θL
        (hJL.trans (Sec6.le_normalizer_theta L))]
      exact hcov l.2
    obtain ⟨j, hj, k, hk, hjk⟩ := hlJ
    refine ⟨⟨j, hj⟩, ?_⟩
    have himg : ((Subgroup.inclusion hJL ⟨j, hj⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
        (l : L ⧸ aschbacherSolvableCore 3 L) := by
      apply QuotientGroup.eq.mpr
      obtain ⟨k', hk', rfl⟩ := hk
      have : (Subgroup.inclusion hJL ⟨j, hj⟩)⁻¹ * l = k' := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
        rw [← hjk]
        simp
      rw [this]
      exact hk'
    change eL ((Subgroup.inclusion hJL ⟨j, hj⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = z
    rw [himg, hl]
    exact eL.apply_symm_apply z
  set ρ : J →* Y := χ.rangeRestrict with hρ
  have hρs : Function.Surjective ρ := χ.rangeRestrict_surjective
  have hker : ρ.ker ≤ π₀.ker := by
    intro j hj
    have hj1 : χ j = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hj)
    have hjθ : (j : G) ∈ θx := (hφ1 _).mp hj1
    have hjθL : (j : G) ∈ θL :=
      le_theta_of_le_thetaQuotCentralizer (S₀ := J ⊓ θx) hLq hZ hJL hcov hJLx inf_le_left
        (inf_le_right.trans (theta_le_thetaQuotCentralizer Lx)) ⟨j.2, hjθ⟩
    rw [MonoidHom.mem_ker]
    obtain ⟨t, ht, hte⟩ := hjθL
    have : Subgroup.inclusion hJL j = t := Subtype.ext hte.symm
    change eL ((Subgroup.inclusion hJL j : L) : L ⧸ aschbacherSolvableCore 3 L) = 1
    rw [this, (QuotientGroup.eq_one_iff _).mpr ht, map_one]
  set π : Y →* projSU 3 2 n := ρ.liftOfSurjective hρs ⟨π₀, hker⟩ with hπ
  have hπρ : ∀ j : J, π (ρ j) = π₀ j := fun j =>
    ρ.liftOfRightInverse_comp_apply (Function.surjInv hρs) (Function.rightInverse_surjInv hρs)
      ⟨π₀, hker⟩ j
  have hπs : Function.Surjective π := by
    intro z
    obtain ⟨j, rfl⟩ := hπ₀s z
    exact ⟨ρ j, hπρ j⟩
  have hπk : Nat.Coprime (Nat.card π.ker) 3 := by
    have hkeq : π.ker = π₀.ker.map ρ := by
      ext y
      constructor
      · intro hy
        obtain ⟨j, rfl⟩ := hρs y
        have hj : π₀ j = 1 := by
          rw [← hπρ]
          exact MonoidHom.mem_ker.mp hy
        exact ⟨j, MonoidHom.mem_ker.mpr hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        have hj' : π₀ j = 1 := MonoidHom.mem_ker.mp hj
        refine MonoidHom.mem_ker.mpr ?_
        rw [hπρ]
        exact hj'
    have hmem : ∀ k : π₀.ker, Subgroup.inclusion hJL (k : J) ∈ aschbacherSolvableCore 3 L := by
      intro k
      have h1 : π₀ k = 1 := MonoidHom.mem_ker.mp k.2
      have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 L)
          (Subgroup.inclusion hJL (k : J)) = 1 := by
        apply eL.injective
        rw [map_one]
        exact h1
      exact (QuotientGroup.eq_one_iff _).mp h2
    set ι : π₀.ker →* aschbacherSolvableCore 3 L :=
      { toFun := fun k => ⟨Subgroup.inclusion hJL (k : J), hmem k⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl } with hι
    have hι : Function.Injective ι := by
      intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun t : aschbacherSolvableCore 3 L => ((t : L) : G)) huv
      exact this
    have hθ3 : Nat.Coprime (Nat.card (aschbacherSolvableCore 3 L)) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        (KFacts.not_three_dvd_card_aschbacherSolvableCore L)).symm
    rw [hkeq]
    exact Nat.Coprime.coprime_dvd_left
      ((Subgroup.card_map_dvd _ _).trans (Subgroup.card_dvd_of_injective ι hι)) hθ3
  have hc'N : c' ∈ Subgroup.normalizer (L₁ : Set N) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hL₁n]
    exact Subgroup.mem_top _
  have hLxeq : L₁.map N.subtype = Lx := by
    rw [hL₁, Subgroup.subgroupOf_map_subtype, inf_of_le_left hLxN]
  have hθN := thetaQuotMap_iff_of_injective N.subtype N.subtype_injective L₁
  rcases hC (N ⧸ T) L' hL'c hL'46 a haN hao haC Y hYle hYperf hYsn n π hU.odd hU.one_lt hπs
      hπk with ⟨K', _, hUK, hk⟩ | ⟨K', _, _, hK', σ, hσ, hk⟩
  · refine Or.inl ⟨K', inferInstance, hUK, ?_⟩
    obtain ⟨e, he⟩ := hk
    obtain ⟨e₂, he₂⟩ : InducesKindPSU3 hUK L₁ c' .field := ⟨_, he.of_map φ L₁ hcond hc'N⟩
    have h2 : InducesKindPSU3 hUK (L₁.map N.subtype) (N.subtype c') .field :=
      ⟨_, he₂.map N.subtype L₁ hθN⟩
    rw [hLxeq] at h2
    exact h2
  · refine Or.inr ⟨K', inferInstance, inferInstance, hK', σ, hσ, ?_⟩
    obtain ⟨e, hx', hR⟩ := hk
    obtain ⟨e₂, hx₂, hR₂⟩ : InducesKindTriality σ L₁ c' .graphField :=
      ⟨_, hc'N, by rwa [← inducedAutHom_map φ L₁ hcond e hc'N hx']⟩
    have h2 : InducesKindTriality σ (L₁.map N.subtype) (N.subtype c') .graphField :=
      ⟨_, map_mem_normalizer_map N.subtype hx₂,
        by rwa [inducedAutHom_map_symm N.subtype L₁ hθN e₂ hx₂]⟩
    rw [hLxeq] at h2
    exact h2

theorem step13PZero419_of (hC : Sec4.K419UnitaryCensusCover) (h46 : Sec4.Item4_6) :
    Step13PZero419 := by
  intro G _ _ A c L P₀ n hU x hxP hxc Lx hLx hJLx hcN hcLx
  have hq : 2 < 2 ^ (3 * n) := by
    have := hU.one_lt
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn1 : 1 ≤ n := by have := hU.one_lt; omega
  rcases typed419_of hC h46 hU hxP hxc hLx hJLx hcN hcLx with
    ⟨K', _, hUK, hk⟩ | ⟨K', _, _, hK', σ, hσ, hk⟩
  · exact Or.inl (InducesStdKind.psu3 hUK hq hk)
  · exact Or.inr (InducesStdKind.triality n hn1 K' hK' σ hσ hk)

end Kinds

end CFSG.RankThree.PartTwo.Sec13.Ronan138P5
