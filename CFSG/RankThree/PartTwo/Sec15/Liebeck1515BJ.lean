module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515HJMeet
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item155wProof
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec19.SimsItem316Narrow
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.CoreFreeTools
import CFSG.Quasithin.Background.A1cRankLemmas

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck1515B

open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank
  CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure CtxB (A : Subgroup G) (c : G) (L : Subgroup G) (d : G) (X : Subgroup G) : Prop where
  conf : Conf1515HJ A c L L
  free : ∀ e ∈ A, e ≠ 1 → IsZCentral L e →
    CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({e} : Set G) = ⊥
  mem_d : d ∈ A
  ne_d : d ≠ 1
  zCentral : IsZCentral L d
  odd : Odd (Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓
    pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))))
  meet : ∃ F ∈ omegaA A, F ≤ A ⊓ L
  delta_eq : delta A (lB A) (Subgroup.centralizer ({d} : Set G)) =
    pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X
  norm : Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer
    ((pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔ X : Subgroup G) : Set G)
  sSup_eq : ∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 d ∧ 𝒳.Nonempty ∧ X = sSup 𝒳
  type : IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)
  x₀_le : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤
    pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔ X
  r_le : ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
    pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔ X

theorem step1515HJEndFpfA6A6Meet_of_false
    (h : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (d : G)
      (X : Subgroup G), CtxB A c L d X → False) :
    Sec15.Step1515HJEndFpfA6A6Meet := by
  intro G _ _ A c L hconf hfree d hdA hd1 hdZ hodd hmeet X hΔ hnorm h𝒳 hcov hX₀ hRX
  exact (h G A c L d X
    ⟨hconf, hfree, hdA, hd1, hdZ, hodd, hmeet, hΔ, hnorm, h𝒳, hcov, hX₀, hRX⟩).elim

namespace CtxB

variable {A L X : Subgroup G} {c d : G}

theorem mem_centralizer_c (h : CtxB A c L d X) : c ∈ Subgroup.centralizer (L : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.conf.sec13Data.le_centralizer hy)

theorem le_centralizer_d (h : CtxB A c L d X) :
    Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer ({d} : Set G) :=
  Subgroup.centralizer_le
    (Set.singleton_subset_iff.mpr (Proof15Res4.mem_of_isZCentral h.zCentral))

theorem R_le_centralizer (h : CtxB A c L d X) :
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
      Subgroup.centralizer (L : Set G) :=
  Proof15Res10.commutator_le_centralizer h.conf.sec13Data.le_centralizer

theorem R_eq_commutator (h : CtxB A c L d X) :
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ =
      ⁅⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆,
        Subgroup.zpowers c⁆ :=
  Proof15Res11.commutatorR_eq h.conf

theorem isPGroup_R (h : CtxB A c L d X) :
    IsPGroup 2 ↥⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ :=
  (Proof15Res11.commutatorR_isPGroup h.conf).1

theorem R_inf_eq_bot (h : CtxB A c L d X) :
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) = ⊥ :=
  Proof15Res11.commutatorR_inf_eq_bot h.conf h.odd

private theorem mem_zpowers_of_mem_centralizer (h : CtxB A c L d X) {a : G}
    (haJ : a ∈ Subgroup.centralizer (L : Set G)) (haA : a ∈ A) : a ∈ Subgroup.zpowers c := by
  have hsec : a ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    refine ⟨haA, fun x hx => ?_⟩
    have hcomm : x * a = a * x := Subgroup.mem_centralizer_iff.mp haJ x hx
    have h1 : a * x * a⁻¹ * x⁻¹ = 1 := by
      rw [← hcomm]
      group
    rw [h1]
    exact one_mem _
  rw [h.conf.sec13Data.sectionCentralizer_eq] at hsec
  exact hsec

private theorem normalizer_le_normalizer_centralizer (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
    (Subgroup.normal_subgroupOf_centralizer_normalizer _)

section Unconditional

variable (h : CtxB A c L d X)

include h in
theorem mem_E_c :
    c ∈ Subgroup.closure {x | ∃ n ∈ Subgroup.normalizer (L : Set G), x = n * c * n⁻¹} :=
  Subgroup.subset_closure ⟨1, one_mem _, by group⟩

include h in
theorem le_normalizer_E :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer
      ((Subgroup.closure {x | ∃ n ∈ Subgroup.normalizer (L : Set G), x = n * c * n⁻¹} :
        Subgroup G) : Set G) := by
  have key : ∀ m ∈ Subgroup.normalizer (L : Set G),
      ∀ x ∈ Subgroup.closure {x | ∃ n ∈ Subgroup.normalizer (L : Set G), x = n * c * n⁻¹},
      m * x * m⁻¹ ∈
        Subgroup.closure {x | ∃ n ∈ Subgroup.normalizer (L : Set G), x = n * c * n⁻¹} := by
    intro m hm x hx
    induction hx using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨n, hn, rfl⟩ := ha
      exact Subgroup.subset_closure ⟨m * n, mul_mem hm hn, by group⟩
    | one => simp
    | mul a b _ _ iha ihb =>
      have e : m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) := by group
      rw [e]
      exact mul_mem iha ihb
    | inv a _ iha =>
      have e : m * a⁻¹ * m⁻¹ = (m * a * m⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem iha
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key m hm x, fun hx => ?_⟩
  have h1 := key m⁻¹ (inv_mem hm) _ hx
  have e : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
  rwa [e] at h1

end Unconditional

theorem le_centralizer_E (h : CtxB A c L d X) :
    Subgroup.closure {x | ∃ n ∈ Subgroup.normalizer (L : Set G), x = n * c * n⁻¹} ≤
      Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨n, hn, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer L hn) c).mp
    h.mem_centralizer_c

theorem le_E_R (h : CtxB A c L d X) :
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
      Subgroup.closure {x | ∃ n ∈ Subgroup.normalizer (L : Set G), x = n * c * n⁻¹} := by
  rw [Subgroup.commutator_le]
  intro g hg z hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hgN : g ∈ Subgroup.normalizer (L : Set G) := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hg
  have h1 : g * c * g⁻¹ ∈
      Subgroup.closure {x | ∃ n ∈ Subgroup.normalizer (L : Set G), x = n * c * n⁻¹} :=
    Subgroup.subset_closure ⟨g, hgN, rfl⟩
  rw [commutatorElement_def, ← conj_zpow]
  exact mul_mem (zpow_mem h1 k) (inv_mem (zpow_mem h.mem_E_c k))

section Route

theorem isCharacteristicP_centralizer (h : CtxB A c L d X) (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) :
    IsCharacteristicP 2 ↥(Subgroup.centralizer (L : Set G)) := by
  have hN := Proof15Res10.isCharacteristicP_normalizer h.conf h152 h153
  exact Sec14.isCharacteristicP_of_mulEquiv'
    (Subgroup.subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (L : Set G)))
    (Sec14.isCharacteristicP_of_normal _ hN)

theorem centralizer_inf_eq_bot (h : CtxB A c L d X) (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) :
    Subgroup.centralizer (L : Set G) ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) =
      ⊥ := by
  have hchar := h.isCharacteristicP_centralizer h152 h153
  have hJN : Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hJM : Subgroup.centralizer (L : Set G) ≤
      Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) : Set G) :=
    h.le_centralizer_d.trans (Sec14.le_normalizer_pPrimeCoreOf 3 _)
  have hnorm : Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer
      ((Subgroup.centralizer (L : Set G) ⊓
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) x)
      (Subgroup.mem_normalizer_iff.mp (hJM hg) x)
  haveI : ((Subgroup.centralizer (L : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))).subgroupOf
        (Subgroup.centralizer (L : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hnorm
  have hdvd : Nat.card ↥(Subgroup.centralizer (L : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))) ∣
      Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))) :=
    Subgroup.card_dvd_of_le (inf_le_inf_right _ hJN)
  have hnd : ¬ 2 ∣ Nat.card ↥((Subgroup.centralizer (L : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))).subgroupOf
        (Subgroup.centralizer (L : Set G))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    intro h2
    have := Nat.odd_iff.mp h.odd
    have := (h2.trans hdvd)
    omega
  have hbot := (characteristic_p_normal_prime_complement_trivial hchar).1 _ ‹_› hnd
  rw [eq_bot_iff]
  intro x hx
  have hmem : (⟨x, hx.1⟩ : ↥(Subgroup.centralizer (L : Set G))) ∈
      (Subgroup.centralizer (L : Set G) ⊓
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))).subgroupOf
          (Subgroup.centralizer (L : Set G)) := Subgroup.mem_subgroupOf.mpr hx
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

theorem R_ne_bot (h : CtxB A c L d X) (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A)) :
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≠ ⊥ := by
  have hD := h.conf.sec13Data
  refine Proof15Res10.commutator_pCoreOf_ne_bot
    (Proof15Res10.isCharacteristicP_normalizer h.conf h152 h153)
    (hD.le_normalizer hD.mem_A) ?_ hD.ne_one
  rw [← hD.orderOf_eq]
  exact pow_orderOf_eq_one c

private theorem isMaximalTwoLocal_normalizer (h : CtxB A c L d X) (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) : CFSG.IsMaximalTwoLocal (Subgroup.normalizer (L : Set G)) := by
  rw [Proof15Res10.normalizer_eq_n155 h.conf h152 h153]
  exact (n155_mem_maximalTwoLocalsContaining h153 h.conf.mem_scriptY0Star).1

theorem pRank_three_centralizer_le_one (h : CtxB A c L d X) (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) :
    CFSG.Open.pRank 3 (Subgroup.centralizer (L : Set G)) ≤ 1 := by
  have hD := h.conf.sec13Data
  obtain ⟨hcL, hB9, -⟩ := j2_point_facts hD h.conf.j2
  have hN3 : CFSG.Open.pRank 3 (Subgroup.normalizer (L : Set G)) ≤ 3 :=
    Sec19.Narrow316.pRank_three_le_of_le hD.evenRank_eq
      (h.isMaximalTwoLocal_normalizer h152 h153) le_rfl
  have hB₀ : CFSG.Open.IsElemAbelian 3 (A ⊓ L) := hD.isElemAbelian.mono inf_le_left
  refine CFSG.SectionRank.pRank_le (by norm_num) fun F hFJ hF => ?_
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hF.isPGroup
  have hFB : F ⊓ (A ⊓ L) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxF, hxA, hxL⟩
    have hxc := h.mem_zpowers_of_mem_centralizer (hFJ hxF) hxA
    have hbot := Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hD.orderOf_eq hcL
    have hx : x ∈ L ⊓ Subgroup.zpowers c := ⟨hxL, hxc⟩
    rw [hbot] at hx
    exact hx
  have hcomm : ∀ x ∈ F, ∀ y ∈ A ⊓ L, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hFJ hx) y hy.2).symm
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute F (A ⊓ L) hcomm).1
  rw [hFB, Subgroup.card_bot, mul_one, hm, hB9] at hcard
  have hle : F ⊔ (A ⊓ L) ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (hFJ.trans (Subgroup.centralizer_le_normalizer _))
      (inf_le_right.trans Subgroup.le_normalizer)
  have h1 : m + 2 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (L : Set G)) :=
    CFSG.SectionRank.le_pRank (by norm_num) hle (hF.sup_of_commute hB₀ hcomm)
      (by rw [hcard]; ring)
  have h2 : m ≤ 1 := by omega
  rw [hm]
  exact Nat.pow_le_pow_right (by norm_num) h2

theorem isCyclic_of_isPGroup_three (h : CtxB A c L d X) (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) :
    ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S → IsCyclic ↥S := by
  intro S hSJ hS
  by_contra hnc
  obtain ⟨F, hFS, hF, hcard⟩ :=
    CFSG.Quasithin.A1c.exists_isElemAbelian_card_sq (p := 3) (by norm_num) hS hnc
  have h2 : 2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (L : Set G)) :=
    CFSG.SectionRank.le_pRank (by norm_num) (hFS.trans hSJ) hF hcard
  have h1 := h.pRank_three_centralizer_le_one h152 h153
  omega

private theorem pRank_E_le_one (h : CtxB A c L d X) (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) :
    CFSG.Open.pRank 3
      (Subgroup.closure {x | ∃ n ∈ Subgroup.normalizer (L : Set G), x = n * c * n⁻¹}) ≤ 1 :=
  (CFSG.SectionRank.pRank_mono (by norm_num) h.le_centralizer_E).trans
    (h.pRank_three_centralizer_le_one h152 h153)

theorem eq_closure_E (h : CtxB A c L d X) (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) :
    Subgroup.closure {x | ∃ n ∈ Subgroup.normalizer (L : Set G), x = n * c * n⁻¹} =
      Subgroup.closure {x | ∃ e ∈ Subgroup.closure
        {x | ∃ n ∈ Subgroup.normalizer (L : Set G), x = n * c * n⁻¹}, x = e * c * e⁻¹} := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨n, hn, rfl⟩
    have hx : n * c * n⁻¹ ∈
        Subgroup.closure {x | ∃ n ∈ Subgroup.normalizer (L : Set G), x = n * c * n⁻¹} :=
      Subgroup.subset_closure ⟨n, hn, rfl⟩
    have hcard : Nat.card (Subgroup.zpowers (n * c * n⁻¹)) = 3 := by
      rw [Nat.card_zpowers, ← h.conf.sec13Data.orderOf_eq]
      exact orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective c
    obtain ⟨e, he, hconj⟩ := CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.exists_conj_of_pRank_le_one
      Nat.prime_three (h.pRank_E_le_one h152 h153) (Subgroup.zpowers_le.mpr h.mem_E_c)
      (Subgroup.zpowers_le.mpr hx) h.conf.sec13Data.card_zpowers hcard
    rw [MonoidHom.map_zpowers] at hconj
    have hmem : n * c * n⁻¹ ∈ Subgroup.zpowers ((MulAut.conj e).toMonoidHom c) := by
      rw [hconj]
      exact Subgroup.mem_zpowers _
    have hgen : (MulAut.conj e).toMonoidHom c ∈ Subgroup.closure {x | ∃ e ∈ Subgroup.closure
        {x | ∃ n ∈ Subgroup.normalizer (L : Set G), x = n * c * n⁻¹}, x = e * c * e⁻¹} :=
      Subgroup.subset_closure ⟨e, he, by simp⟩
    exact Subgroup.zpowers_le.mpr hgen hmem
  · rw [Subgroup.closure_le]
    rintro _ ⟨e, he, rfl⟩
    exact mul_mem (mul_mem he h.mem_E_c) (inv_mem he)

theorem three_not_dvd_of_normal (h : CtxB A c L d X) (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) :
    ∀ K : Subgroup G,
      K ≤ Subgroup.closure {x | ∃ n ∈ Subgroup.normalizer (L : Set G), x = n * c * n⁻¹} →
      Subgroup.closure {x | ∃ n ∈ Subgroup.normalizer (L : Set G), x = n * c * n⁻¹} ≤
        Subgroup.normalizer (K : Set G) → c ∉ K → ¬ 3 ∣ Nat.card K := by
  intro K hKE hEK hcK h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hxG : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
  have hcard : Nat.card (Subgroup.zpowers (x : G)) = 3 := by rw [Nat.card_zpowers, hxG]
  obtain ⟨e, he, hconj⟩ := CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.exists_conj_of_pRank_le_one
    Nat.prime_three (h.pRank_E_le_one h152 h153) (Subgroup.zpowers_le.mpr h.mem_E_c)
    (Subgroup.zpowers_le.mpr (hKE x.2)) h.conf.sec13Data.card_zpowers hcard
  have hmem : e * c * e⁻¹ ∈ K := by
    have h1 : e * c * e⁻¹ ∈ (Subgroup.zpowers c).map (MulAut.conj e).toMonoidHom :=
      ⟨c, Subgroup.mem_zpowers c, by simp⟩
    rw [hconj] at h1
    exact Subgroup.zpowers_le.mpr x.2 h1
  have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem (hEK he)) _).mp hmem
  have e' : e⁻¹ * (e * c * e⁻¹) * e⁻¹⁻¹ = c := by group
  rw [e'] at h2
  exact hcK h2

end Route

end CtxB

end CFSG.RankThree.PartTwo.Sec15.Liebeck1515B
