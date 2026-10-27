module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenCommon
public import CFSG.GroupTheory.PermutingSylowEight
public import CFSG.GroupTheory.ConjActionModPCore
public import CFSG.GroupTheory.PermutingProducts
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovL34
public import CFSG.RankThree.PartOne.S12.Sec159Fin
public import CFSG.LocalAnalysis.UniquenessCase.UC6K318Step
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81 CFSG.Quasithin CFSG.SignalizerFunctorTheorem.McBride
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem ree_case_core (hRee : K_ReeSylowGeneration) {D : Data G} {V₀ V L : Subgroup G}
    {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q) (h9 : R17_9At D V₀ V L r q hC) (h2 : P17_12_2 q L)
    {X : Subgroup G} (hXL : X ≤ L) (hperm : Permutes X (NTL17 D L))
    (hX : IsL2Over17 (Bar2 X) q) :
    Nat.card ↥(((CFSG.Open.pCoreOf 2 X).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ≤ 2 ∧
      CFSG.Open.pCoreOf 2 X ≤ D.T ∧
      ∀ s ∈ NTL17 D L, X.map (MulAut.conj s).toMonoidHom ≤ X ⊔ CFSG.Open.pCoreOf 2 L := by
  classical
  obtain ⟨n, hq_eq, hLie⟩ := h2
  have hq3 : 3 < q := h9
  have hn1 : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0] at hq_eq
    norm_num at hq_eq
    omega
  obtain ⟨P, hPcoe⟩ := exists_sylow_syl2Bar D L hC.memL.1
  obtain ⟨hZX, hOutOdd, hReePart⟩ :=
    hRee (Bar2 L) q n ⟨n, hq_eq, hLie⟩ hq_eq hn1
  obtain ⟨hEel, hP8, -⟩ := hReePart P
  let πL : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let fX : ↥X →* Bar2 L := πL.comp (Subgroup.inclusion hXL)
  let A : Subgroup (Bar2 L) := fX.range
  let N₀ : Subgroup (Bar2 L) := ((CFSG.Open.pCoreOf 2 X).subgroupOf L).map πL
  let N : Subgroup ↥X := CFSG.pCore 2 ↥X
  have hA : A = (X.subgroupOf L).map πL := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map_of_mem πL (Subgroup.mem_subgroupOf.mpr x.2)
    · rintro ⟨l, hl, rfl⟩
      refine ⟨⟨(l : G), Subgroup.mem_subgroupOf.mp hl⟩, ?_⟩
      show πL ⟨(l : G), hXL (Subgroup.mem_subgroupOf.mp hl)⟩ = πL l
      exact congrArg πL (Subtype.ext rfl)
  have hN : fX.ker ≤ N := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hO2L : (x : G) ∈ CFSG.Open.pCoreOf 2 L := by
      have h2 : (⟨(x : G), hXL x.2⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
        (QuotientGroup.eq_one_iff _).mp hx
      exact Subgroup.mem_map_of_mem L.subtype h2
    have hnorm : X ≤ Subgroup.normalizer ((X ⊓ CFSG.Open.pCoreOf 2 L : Subgroup G) : Set G) := by
      intro y hy
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hy,
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) (hXL hy)⟩
    have hnormal : ((X ⊓ CFSG.Open.pCoreOf 2 L).subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hnorm
    have hp : IsPGroup 2 ↥(X ⊓ CFSG.Open.pCoreOf 2 L) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_right
    have hxN : (x : G) ∈ CFSG.Open.pCoreOf 2 X :=
      (CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left hnormal hp) ⟨x.2, hO2L⟩
    have hxN' : x ∈ (CFSG.Open.pCoreOf 2 X).subgroupOf X :=
      Subgroup.mem_subgroupOf.mpr hxN
    rw [CFSG.openPCoreOf_subgroupOf] at hxN'
    show x ∈ CFSG.pCore 2 ↥X
    exact hxN'
  obtain ⟨hN'n, ⟨eAN⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.K318.exists_range_quotient_equiv fX N hN
  set N' := N.map fX.rangeRestrict with hN'eq
  have hN'map : N'.map A.subtype = N₀ := by
    rw [hN'eq, Subgroup.map_map]
    have hcomp : A.subtype.comp fX.rangeRestrict = fX := MonoidHom.ext fun _ => rfl
    rw [hcomp]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxG : (x : G) ∈ CFSG.Open.pCoreOf 2 X :=
        Subgroup.mem_map_of_mem X.subtype hx
      exact Subgroup.mem_map_of_mem πL (Subgroup.mem_subgroupOf.mpr hxG)
    · rintro ⟨l, hl, rfl⟩
      have hlG : (l : G) ∈ CFSG.Open.pCoreOf 2 X := Subgroup.mem_subgroupOf.mp hl
      obtain ⟨x, hx, hxl⟩ := Subgroup.mem_map.mp hlG
      refine ⟨x, hx, ?_⟩
      show πL ⟨(x : G), hXL x.2⟩ = πL l
      exact congrArg πL (Subtype.ext hxl)
  have hN'eq₂ : N' = N₀.subgroupOf A := by
    ext y
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hy
      rw [← hN'map]
      exact Subgroup.mem_map_of_mem A.subtype hy
    · intro hy
      rw [← hN'map] at hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      rwa [show z = y from Subtype.ext hzy] at hz
  have hN₀leA : N₀ ≤ A := by
    rw [hA]
    rintro z ⟨l, hl, rfl⟩
    exact Subgroup.mem_map_of_mem πL (Subgroup.mem_subgroupOf.mpr
      (CFSG.LieType.BorelTits.pCoreOf_le 2 X (Subgroup.mem_subgroupOf.mp hl)))
  have hbar4 : 4 ∣ Nat.card (Bar2 X) := by
    obtain ⟨p, f, hp, hp2, hqX, hf, hm⟩ := hX
    have hcard := CFSG.ComponentClassification.GSThmB.card_of_lieModel_psl_two hp2 hm
    have hp_odd : Odd p := hp.odd_of_ne_two hp2
    have hq_odd : Odd q := by
      rw [hqX]
      exact hp_odd.pow
    have h8 : 8 ∣ q ^ 2 - 1 :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.S19C.eight_dvd_sq_sub_one hq_odd
    have h2q : 2 ∣ q - 1 := by
      obtain ⟨k, hk⟩ := hq_odd
      omega
    have hgcd : Nat.gcd 2 (q - 1) = 2 := Nat.gcd_eq_left h2q
    rw [hcard, ← hqX, CFSG.ComponentClassification.GSThmB.Cov.ordA_one_formula, hgcd]
    obtain ⟨k, hk⟩ := h8
    have hhalf : (q ^ 2 - 1) / 2 = 4 * k := by
      rw [hk]
      omega
    have hmul : q * (q ^ 2 - 1) / 2 = q * ((q ^ 2 - 1) / 2) := by
      rw [Nat.mul_div_assoc]
      exact ⟨4 * k, by omega⟩
    rw [hmul, hhalf]
    exact ⟨q * k, by ring⟩
  have hquot : Nat.card (↥A ⧸ N') = Nat.card (Bar2 X) := Nat.card_congr eAN.toEquiv
  have hNcard : Nat.card ↥N' = Nat.card ↥N₀ := by
    rw [← hN'map]
    exact (Subgroup.card_map_of_injective A.subtype_injective).symm
  have h4 : 4 * Nat.card ↥N₀ ∣ Nat.card ↥A := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (α := ↥A) N', hquot, hNcard]
    exact Nat.mul_dvd_mul_right hbar4 (Nat.card ↥N₀)
  have hsimple : IsSimpleGroup (Bar2 X) := by
    obtain ⟨p, f, hp, hp2, hqX, hf, hm⟩ := hX
    exact CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hm
  have hnab : ∃ a b : Bar2 X, a * b ≠ b * a := by
    obtain ⟨p, f, hp, hp2, hqX, hf, hm⟩ := hX
    exact CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hm
  have hnab' : ¬ IsMulCommutative (Bar2 X) := by
    rintro hc
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (isMulCommutative_iff.mp hc a b)
  have hperfAN : commutator (↥A ⧸ N') = ⊤ := by
    have hbarperf : Group.IsPerfect (Bar2 X) :=
      Group.isPerfect_def.2 (CFSG.GroupTheory.commutator_eq_top_of_isSimpleGroup hsimple hnab')
    have hperfAN' : Group.IsPerfect (↥A ⧸ N') :=
      @Group.IsPerfect.ofSurjective (Bar2 X) (↥A ⧸ N') _ _ eAN.symm.toMonoidHom
        hbarperf eAN.symm.surjective
    exact Group.isPerfect_def.1 hperfAN'
  have hN₀normal : (N₀.subgroupOf A).Normal := by
    rw [← hN'eq₂]
    exact hN'n
  have hperf : ⁅A, A⁆ ⊔ N₀ = A := by
    have h := CFSG.Quasithin.E2.commutator_sup_eq_top (Q := ↥A) N' hperfAN
    rw [hN'eq₂] at h
    have hmap := congrArg (Subgroup.map A.subtype) h
    rw [Subgroup.map_sup, Subgroup.map_subtype_commutator,
      Subgroup.map_subgroupOf_eq_of_le hN₀leA,
      Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact hmap
  have hS_le_N : NTL17 D L ≤ Subgroup.normalizer (L : Set G) :=
    fun _ hx => (Subgroup.mem_inf.mp hx).2
  have hN₀n : ∀ a ∈ A, ∀ n ∈ N₀, a * n * a⁻¹ ∈ N₀ :=
    Subgroup.le_normalizer_iff.mp
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hN₀leA).mp hN₀normal)
  have hN₀2 : IsPGroup 2 ↥N₀ := by
    have h1 : IsPGroup 2 ↥((CFSG.Open.pCoreOf 2 X).subgroupOf L) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).of_equiv
        (Subgroup.subgroupOfEquivOfLe
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXL)).symm
    exact h1.map πL
  have hpermA : ((A : Subgroup (Bar2 L)) : Set (Bar2 L)) *
      ((P : Subgroup (Bar2 L)) : Set (Bar2 L)) =
      ((P : Subgroup (Bar2 L)) : Set (Bar2 L)) *
        ((A : Subgroup (Bar2 L)) : Set (Bar2 L)) := by
    have hpermSub : ((X.subgroupOf L : Subgroup ↥L) : Set ↥L) *
        (((NTL17 D L ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) =
        (((NTL17 D L ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) *
          ((X.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      CFSG.Quasithin.H23P4.mul_comm_subgroupOf hXL inf_le_right
        (CFSG.GroupTheory.permutes_inf_of_le (B := X) (T := NTL17 D L) (N := L) hXL hperm)
    have hmap := CFSG.GroupTheory.map_permutes_map (f := πL) hpermSub
    have hP : ((NTL17 D L ⊓ L).subgroupOf L).map πL = (P : Subgroup (Bar2 L)) := by
      rw [hPcoe]
      rfl
    rwa [← hA, hP] at hmap
  obtain ⟨hNcard_le, hNP, hB⟩ :=
    CFSG.GroupTheory.permuting_sylow_order_eight P hP8 hpermA hN₀leA hN₀n hN₀2 h4 hperf
  refine ⟨hNcard_le, ?_, ?_⟩
  ·
    intro x hx
    have hxL : (x : G) ∈ L := hXL (CFSG.LieType.BorelTits.pCoreOf_le 2 X hx)
    have hxN : πL ⟨x, hxL⟩ ∈ N₀ :=
      Subgroup.mem_map_of_mem πL (Subgroup.mem_subgroupOf.mpr hx)
    have hxP : πL ⟨x, hxL⟩ ∈ (P : Subgroup (Bar2 L)) := hNP hxN
    rw [hPcoe] at hxP
    unfold Syl2Bar at hxP
    obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.mp hxP
    have htT : (t : G) ∈ D.T :=
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ht)).1).1
    have hmemL : (t : G) * (x : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
      have h1 : (t / ⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
        QuotientGroup.eq_iff_div_mem.mp htx
      have h2 : ((t / ⟨x, hxL⟩ : ↥L) : G) = (t : G) * (x : G)⁻¹ := by
        simp [div_eq_mul_inv]
      rw [← h2]
      exact Subgroup.mem_map_of_mem L.subtype h1
    have hO2L_T : CFSG.Open.pCoreOf 2 L ≤ D.T :=
      (CFSG.Quasithin.pCoreOf_le_pCoreOf_of_isSubnormal hC.memL.1).trans
        (uc22p22e_pCoreOf_le_T D)
    have hx_eq : (x : G) = ((t : G) * (x : G)⁻¹)⁻¹ * (t : G) := by group
    rw [hx_eq]
    exact D.T.mul_mem (hO2L_T ((CFSG.Open.pCoreOf 2 L).inv_mem hmemL)) htT
  ·
    intro s hs
    have hsT : s ∈ D.T := (Subgroup.mem_inf.mp hs).1
    have hsN : s ∈ Subgroup.normalizer (L : Set G) := (Subgroup.mem_inf.mp hs).2
    have hinf : ((X : Set G) * ((NTL17 D L ⊓ L : Subgroup G) : Set G)) =
        (((NTL17 D L ⊓ L : Subgroup G) : Set G) * (X : Set G)) :=
      CFSG.GroupTheory.permutes_inf_of_le (B := X) (T := NTL17 D L) (N := L) hXL hperm
    let B : Subgroup (Bar2 L) :=
      ((X.map (MulAut.conj s).toMonoidHom).subgroupOf L).map πL
    have hXsL : X.map (MulAut.conj s).toMonoidHom ≤ L := by
      rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      rw [Subgroup.mem_comap]
      exact (Subgroup.mem_normalizer_iff.mp hsN (x : G)).mp (hXL hx)
    have hset : ((X.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) ⊆
        (((NTL17 D L ⊓ L : Subgroup G)) : Set G) * (X : Set G) := by
      rintro y ⟨x, hx, rfl⟩
      have h1 : s * x ∈ ((NTL17 D L : Subgroup G) : Set G) * (X : Set G) :=
        ⟨s, hs, x, hx, rfl⟩
      rw [← hperm] at h1
      obtain ⟨y, hy, t, ht, hyt⟩ := h1
      have hconjL : s * (x : G) * s⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hsN (x : G)).mp (hXL hx)
      have hyL : (y : G) ∈ L := hXL hy
      have htsL : t * s⁻¹ ∈ L := by
        have h2 : t * s⁻¹ = (y : G)⁻¹ * (s * (x : G) * s⁻¹) := by
          rw [← hyt]
          group
        rw [h2]
        exact L.mul_mem (L.inv_mem hyL) hconjL
      have hmem : s * (x : G) * s⁻¹ ∈ (X : Set G) * ((NTL17 D L ⊓ L : Subgroup G) : Set G) :=
        ⟨y, hy, t * s⁻¹,
          ⟨(NTL17 D L).mul_mem ht ((NTL17 D L).inv_mem hs), htsL⟩, by rw [← hyt]; group⟩
      rwa [hinf] at hmem
    have hXs_le : X.map (MulAut.conj s).toMonoidHom ≤ (NTL17 D L ⊓ L) ⊔ X := by
      intro z hz
      obtain ⟨h, hh, k, hk, rfl⟩ := hset hz
      exact ((NTL17 D L ⊓ L) ⊔ X).mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hk)
    have hBle : B ≤ A ⊔ (P : Subgroup (Bar2 L)) := by
      have h1 : B ≤ (((NTL17 D L ⊓ L) ⊔ X).subgroupOf L).map πL := by
        rintro z ⟨l, hl, rfl⟩
        exact Subgroup.mem_map_of_mem πL (Subgroup.mem_subgroupOf.mpr
          (hXs_le (Subgroup.mem_subgroupOf.mp hl)))
      have h2 : (((NTL17 D L ⊓ L) ⊔ X).subgroupOf L).map πL =
          A ⊔ (P : Subgroup (Bar2 L)) := by
        rw [Subgroup.subgroupOf_sup inf_le_right hXL, Subgroup.map_sup]
        rw [show ((NTL17 D L ⊓ L).subgroupOf L).map πL = (P : Subgroup (Bar2 L)) from by
          rw [hPcoe]; rfl]
        rw [show (X.subgroupOf L).map πL = A from hA.symm]
        exact sup_comm ..
      rwa [h2] at h1
    have hBcard : Nat.card ↥B = Nat.card ↥A := by
      let ψ : MulAut (Bar2 L) :=
        CFSG.GroupTheory.conjModPCore 2 L (NTL17 D L) hS_le_N ⟨s, hs⟩
      have hB_eq : B = A.map ψ.toMonoidHom := by
        ext z
        constructor
        · rintro ⟨l, hl, rfl⟩
          obtain ⟨x, hx, hxl⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hl)
          refine Subgroup.mem_map.mpr ⟨πL ⟨x, hXL hx⟩, ?_, ?_⟩
          · rw [hA]
            exact Subgroup.mem_map_of_mem πL (Subgroup.mem_subgroupOf.mpr hx)
          · have hψ := CFSG.GroupTheory.conjModPCore_mk 2 L (NTL17 D L) hS_le_N
              ⟨s, hs⟩ ⟨x, hXL hx⟩
            exact hψ.trans (congrArg πL (Subtype.ext hxl))
        · rintro ⟨w, hw, rfl⟩
          have hw' : w ∈ fX.range := hw
          obtain ⟨x, rfl⟩ := hw'
          have hxX : (x : G) ∈ X := x.2
          refine Subgroup.mem_map.mpr
            ⟨⟨(MulAut.conj s).toMonoidHom (x : G),
              hXsL (Subgroup.mem_map_of_mem (MulAut.conj s).toMonoidHom hxX)⟩, ?_, ?_⟩
          · exact Subgroup.mem_subgroupOf.mpr
              (Subgroup.mem_map_of_mem (MulAut.conj s).toMonoidHom hxX)
          · have hψ := CFSG.GroupTheory.conjModPCore_mk 2 L (NTL17 D L) hS_le_N
              ⟨s, hs⟩ ⟨x, hXL x.2⟩
            exact hψ.symm
      rw [hB_eq]
      exact Subgroup.card_map_of_injective ψ.injective
    have hBA : B = A := hB B hBle hBcard
    intro z hz
    have hzL : z ∈ L := hXsL hz
    have hzB : πL ⟨z, hzL⟩ ∈ B :=
      Subgroup.mem_map_of_mem πL (Subgroup.mem_subgroupOf.mpr hz)
    rw [hBA, hA] at hzB
    obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp hzB
    have hlX : (l : G) ∈ X := Subgroup.mem_subgroupOf.mp hl
    have hmemL : (l : G) * (z : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
      have h1 : (l / ⟨z, hzL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
        QuotientGroup.eq_iff_div_mem.mp hlx
      have h2 : ((l / ⟨z, hzL⟩ : ↥L) : G) = (l : G) * (z : G)⁻¹ := by
        simp [div_eq_mul_inv]
      rw [← h2]
      exact Subgroup.mem_map_of_mem L.subtype h1
    have hz_eq : (z : G) = ((l : G) * (z : G)⁻¹)⁻¹ * (l : G) := by group
    rw [hz_eq]
    exact (X ⊔ CFSG.Open.pCoreOf 2 L).mul_mem
      (Subgroup.mem_sup_right ((CFSG.Open.pCoreOf 2 L).inv_mem hmemL))
      (Subgroup.mem_sup_left hlX)


theorem delta17_12_case_ree_triple (hRee : K_ReeSylowGeneration) {D : Data G}
    {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    (h9 : R17_9At D V₀ V L r q hC) {H : Subgroup G}
    (hH : H ∈ Delta17_12 D (fundPred q) r q L) (h1 : ¬ P17_12_1 r q L) (h2 : P17_12_2 q L) :
    ∃ K : Subgroup (Bar2 H), CFSG.IsComponent K ∧
      orbitClosure K (CFSG.LocalAnalysis.WeakClosure81.barImage H D.T) ⊔
        CFSG.LocalAnalysis.WeakClosure81.barImage H D.T = ⊤ ∧
      OddComponentShapeCore q (↥K ⧸ Subgroup.center ↥K) := by
  classical
  rw [Delta17_12, dif_neg h1, dif_pos h2] at hH
  obtain ⟨X, hXL, hperm, hX, rfl⟩ := hH
  obtain ⟨hNcard, hO2T, hconjX⟩ := ree_case_core hRee hC h9 h2 hXL hperm hX
  let H' : Subgroup G := D.T ⊔ X
  have hXH : X ≤ H' := le_sup_right
  have hTH : D.T ≤ H' := le_sup_left
  have hH'M : H' ≤ D.M := by
    change D.T ⊔ X ≤ D.M
    exact sup_le D.sylowM.le (hXL.trans hC.memL.1.le)
  have hO2LH : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 H' :=
    (CFSG.Quasithin.pCoreOf_le_pCoreOf_of_isSubnormal hC.memL.1).trans
      (pCoreOf_M_le_of_T_le hTH hH'M)
  let πH : ↥H' →* Bar2 H' := QuotientGroup.mk' (CFSG.pCore 2 ↥H')
  let fXH : ↥X →* Bar2 H' := πH.comp (Subgroup.inclusion hXH)
  let Xbar : Subgroup (Bar2 H') := fXH.range
  let N : Subgroup ↥X := CFSG.pCore 2 ↥X
  have hXbar_eq : Xbar = (X.subgroupOf H').map πH := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map_of_mem πH (Subgroup.mem_subgroupOf.mpr x.2)
    · rintro ⟨l, hl, rfl⟩
      refine ⟨⟨(l : G), Subgroup.mem_subgroupOf.mp hl⟩, ?_⟩
      show πH ⟨(l : G), hXH (Subgroup.mem_subgroupOf.mp hl)⟩ = πH l
      exact congrArg πH (Subtype.ext rfl)
  have hNker : fXH.ker ≤ N := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hO2H : (x : G) ∈ CFSG.Open.pCoreOf 2 H' := by
      have h2 : (⟨(x : G), hXH x.2⟩ : ↥H') ∈ CFSG.pCore 2 ↥H' :=
        (QuotientGroup.eq_one_iff _).mp hx
      exact Subgroup.mem_map_of_mem H'.subtype h2
    have hnorm : X ≤ Subgroup.normalizer
        ((X ⊓ CFSG.Open.pCoreOf 2 H' : Subgroup G) : Set G) := by
      intro y hy
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hy,
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H') (hXH hy)⟩
    have hnormal : ((X ⊓ CFSG.Open.pCoreOf 2 H').subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hnorm
    have hp : IsPGroup 2 ↥(X ⊓ CFSG.Open.pCoreOf 2 H') :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H').to_le inf_le_right
    have hxN : (x : G) ∈ CFSG.Open.pCoreOf 2 X :=
      (CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left hnormal hp) ⟨x.2, hO2H⟩
    have hxN' : x ∈ (CFSG.Open.pCoreOf 2 X).subgroupOf X :=
      Subgroup.mem_subgroupOf.mpr hxN
    rw [CFSG.openPCoreOf_subgroupOf] at hxN'
    show x ∈ CFSG.pCore 2 ↥X
    exact hxN'
  obtain ⟨hObarn, ⟨eO⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.K318.exists_range_quotient_equiv fXH N hNker
  set Obar := N.map fXH.rangeRestrict with hObareq
  let πL : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let N₀ : Subgroup (Bar2 L) := ((CFSG.Open.pCoreOf 2 X).subgroupOf L).map πL
  have hNcard' : Nat.card ↥N₀ ≤ 2 := hNcard
  let A₀ : Subgroup G := CFSG.Open.pCoreOf 2 X
  have hA₀X : A₀ ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  let f₀ : ↥A₀ →* Bar2 L := πL.comp (Subgroup.inclusion (hA₀X.trans hXL))
  let g₀ : ↥A₀ →* Bar2 H' := πH.comp (Subgroup.inclusion (hA₀X.trans hXH))
  have hker₀ : f₀.ker ≤ g₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxO2L : (x : G) ∈ CFSG.Open.pCoreOf 2 L := by
      have h1 : (⟨(x : G), (hA₀X.trans hXL) x.2⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
        (QuotientGroup.eq_one_iff _).mp hx
      exact Subgroup.mem_map_of_mem L.subtype h1
    have hxH' : (x : G) ∈ CFSG.Open.pCoreOf 2 H' := hO2LH hxO2L
    have h1 : (⟨(x : G), (hA₀X.trans hXH) x.2⟩ : ↥H') ∈ CFSG.pCore 2 ↥H' := by
      rw [← CFSG.openPCoreOf_subgroupOf]
      exact Subgroup.mem_subgroupOf.mpr hxH'
    exact (QuotientGroup.eq_one_iff _).mpr h1
  have hf₀range : f₀.range = N₀ := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact Subgroup.mem_map_of_mem πL (Subgroup.mem_subgroupOf.mpr a.2)
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨(l : G), Subgroup.mem_subgroupOf.mp hl⟩,
        congrArg πL (Subtype.ext rfl)⟩
  have hg₀range : g₀.range = Obar.map Xbar.subtype := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      have haN : (⟨(a : G), hA₀X a.2⟩ : ↥X) ∈ N := by
        change (⟨(a : G), hA₀X a.2⟩ : ↥X) ∈ CFSG.pCore 2 ↥X
        rw [← CFSG.openPCoreOf_subgroupOf]
        exact Subgroup.mem_subgroupOf.mpr a.2
      have haO : fXH.rangeRestrict ⟨(a : G), hA₀X a.2⟩ ∈ Obar := by
        rw [hObareq]
        exact Subgroup.mem_map_of_mem fXH.rangeRestrict haN
      refine Subgroup.mem_map.mpr ⟨fXH.rangeRestrict ⟨(a : G), hA₀X a.2⟩, haO, ?_⟩
      show Xbar.subtype (fXH.rangeRestrict ⟨(a : G), hA₀X a.2⟩) = g₀ a
      rfl
    · rintro ⟨o, ho, rfl⟩
      rw [hObareq] at ho
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ho
      exact ⟨⟨(a : G), Subgroup.mem_map_of_mem X.subtype ha⟩, rfl⟩
  have hdvd : Nat.card ↥Obar ∣ Nat.card ↥N₀ := by
    have h := CFSG.RankThree.PartOne.Sec159Cfg.card_range_dvd_of_ker_le f₀ g₀ hker₀
    have hcardO : Nat.card ↥(Obar.map Xbar.subtype) = Nat.card ↥Obar :=
      Subgroup.card_map_of_injective Xbar.subtype_injective
    rwa [hg₀range, hf₀range, hcardO] at h
  have hN₀2 : IsPGroup 2 ↥N₀ := by
    have h1 : IsPGroup 2 ↥((CFSG.Open.pCoreOf 2 X).subgroupOf L) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).of_equiv
        (Subgroup.subgroupOfEquivOfLe ((hA₀X.trans hXL))).symm
    exact h1.map πL
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hN₀2
  have hN₀dvd2 : Nat.card ↥N₀ ∣ 2 := by
    have hk1 : k ≤ 1 := by
      have h2 : 2 ^ k ≤ 2 ^ 1 := by
        rw [← hk]
        simpa using hNcard'
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
    rw [hk]
    interval_cases k <;> norm_num
  have hObardvd2 : Nat.card ↥Obar ∣ 2 := hdvd.trans hN₀dvd2
  have hObarCenter : Obar ≤ Subgroup.center ↥Xbar :=
    CFSG.Walter.W67.JROut.le_center_of_card_dvd_two hObardvd2
  have hsimple : IsSimpleGroup (Bar2 X) := by
    obtain ⟨p, f, hp, hp2, hqX, hf, hm⟩ := hX
    exact CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hm
  have hnab : ∃ a b : Bar2 X, a * b ≠ b * a := by
    obtain ⟨p, f, hp, hp2, hqX, hf, hm⟩ := hX
    exact CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hm
  have hsimpleO : IsSimpleGroup (↥Xbar ⧸ Obar) :=
    (MulEquiv.isSimpleGroup_congr eO).mpr hsimple
  have hnaO : ∃ a b : ↥Xbar ⧸ Obar, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eO.symm a, eO.symm b, fun h => hab (by simpa using congrArg eO h)⟩
  have hperfO : commutator (↥Xbar ⧸ Obar) = ⊤ := by
    have hnab' : ¬ IsMulCommutative (Bar2 X) := by
      rintro hc
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (isMulCommutative_iff.mp hc a b)
    have hbarperf : Group.IsPerfect (Bar2 X) :=
      Group.isPerfect_def.2 (CFSG.GroupTheory.commutator_eq_top_of_isSimpleGroup hsimple hnab')
    have hperfO' : Group.IsPerfect (↥Xbar ⧸ Obar) :=
      @Group.IsPerfect.ofSurjective (Bar2 X) (↥Xbar ⧸ Obar) _ _ eO.symm.toMonoidHom
        hbarperf eO.symm.surjective
    exact Group.isPerfect_def.1 hperfO'
  obtain ⟨hKqs, ⟨eKZ⟩⟩ :=
    CFSG.Quasithin.E2.quasisimple_commutator (Q := ↥Xbar) Obar hObarCenter hperfO
      hsimpleO hnaO
  let K : Subgroup (Bar2 H') := (commutator ↥Xbar).map Xbar.subtype
  have hKqs' : CFSG.IsQuasisimple ↥K :=
    CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective (commutator ↥Xbar) Xbar.subtype
        Xbar.subtype_injective).symm hKqs
  let Tbar : Subgroup (Bar2 H') := CFSG.LocalAnalysis.WeakClosure81.barImage H' D.T
  have hK_Obar : K ⊔ Obar.map Xbar.subtype = Xbar := by
    have h := CFSG.Quasithin.E2.commutator_sup_eq_top (Q := ↥Xbar) Obar hperfO
    have hmap := congrArg (Subgroup.map Xbar.subtype) h
    rw [Subgroup.map_sup, Subgroup.map_subtype_commutator,
      Subgroup.map_top, Subgroup.range_subtype] at hmap
    rw [show K = ⁅Xbar, Xbar⁆ from Subgroup.map_subtype_commutator Xbar]
    exact hmap
  have hOT : Obar.map Xbar.subtype ≤ Tbar := by
    rintro z ⟨o, ho, rfl⟩
    rw [hObareq] at ho
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ho
    exact Subgroup.mem_map_of_mem πH (Subgroup.mem_subgroupOf.mpr
      (hO2T (Subgroup.mem_map_of_mem X.subtype hx)))
  have hXbarTop : Xbar ⊔ Tbar = ⊤ := by
    have h := barImage_sup_barImage_eq_top (H := H') (T := D.T) (X := X) rfl hXH
    rwa [← hXbar_eq] at h
  have hKtop : K ⊔ Tbar = ⊤ := by
    calc K ⊔ Tbar = (K ⊔ Obar.map Xbar.subtype) ⊔ Tbar := by
          rw [sup_assoc, sup_eq_right.mpr hOT]
      _ = Xbar ⊔ Tbar := by rw [hK_Obar]
      _ = ⊤ := hXbarTop
  have hconjXbar : ∀ t ∈ Tbar,
      Xbar.map (MulAut.conj t).toMonoidHom = Xbar ∨
        ⁅Xbar, Xbar.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
    intro t ht
    obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.mp ht
    have hsT : (s : G) ∈ D.T := Subgroup.mem_subgroupOf.mp hs
    rw [← hst]
    by_cases hsN : (s : G) ∈ NTL17 D L
    · left
      let ψ : MulAut (Bar2 H') := MulAut.conj (πH s)
      have hnat : ψ.toMonoidHom.comp πH = πH.comp (MulAut.conj s).toMonoidHom := by
        ext x
        simp [ψ, MulAut.conj_apply, map_mul]
      have hXbars : Xbar.map ψ.toMonoidHom =
          ((X.subgroupOf H').map (MulAut.conj s).toMonoidHom).map πH := by
        calc Xbar.map ψ.toMonoidHom = (X.subgroupOf H').map (ψ.toMonoidHom.comp πH) := by
              rw [hXbar_eq, ← Subgroup.map_map]
          _ = (X.subgroupOf H').map (πH.comp (MulAut.conj s).toMonoidHom) := by
              rw [hnat]
          _ = ((X.subgroupOf H').map (MulAut.conj s).toMonoidHom).map πH := by
              rw [← Subgroup.map_map]
      have hmap_le : (X.subgroupOf H').map (MulAut.conj s).toMonoidHom ≤
          ((X ⊔ CFSG.Open.pCoreOf 2 L).subgroupOf H') := by
        rintro z hz
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
        exact Subgroup.mem_subgroupOf.mpr
          (hconjX (s : G) hsN
            (Subgroup.mem_map_of_mem (MulAut.conj (s : G)).toMonoidHom
              (Subgroup.mem_subgroupOf.mp hx)))
      have hbot : ((CFSG.Open.pCoreOf 2 L).subgroupOf H').map πH = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        intro x hx
        rw [← CFSG.openPCoreOf_subgroupOf]
        exact Subgroup.mem_subgroupOf.mpr (hO2LH (Subgroup.mem_subgroupOf.mp hx))
      have hle : Xbar.map ψ.toMonoidHom ≤ Xbar := by
        rw [hXbars]
        calc ((X.subgroupOf H').map (MulAut.conj s).toMonoidHom).map πH
            ≤ (((X ⊔ CFSG.Open.pCoreOf 2 L).subgroupOf H')).map πH :=
              Subgroup.map_mono hmap_le
          _ = Xbar := by
              rw [Subgroup.subgroupOf_sup hXH
                (hO2LH.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H')),
                Subgroup.map_sup, hbot, sup_bot_eq]
              exact hXbar_eq.symm
      exact Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (MulAut.conj (πH s)).injective])
    · right
      have hnt : (s : G) ∉ Subgroup.normalizer (L : Set G) := fun h => hsN ⟨hsT, h⟩
      have hcomm := comm_conj_of_not_mem_normalizer hC.memL hXL hsT hnt
      let ψ : MulAut (Bar2 H') := MulAut.conj (πH s)
      have hnat : ψ.toMonoidHom.comp πH = πH.comp (MulAut.conj s).toMonoidHom := by
        ext x
        simp [ψ, MulAut.conj_apply, map_mul]
      have hXbars : Xbar.map ψ.toMonoidHom =
          ((X.subgroupOf H').map (MulAut.conj s).toMonoidHom).map πH := by
        calc Xbar.map ψ.toMonoidHom = (X.subgroupOf H').map (ψ.toMonoidHom.comp πH) := by
              rw [hXbar_eq, ← Subgroup.map_map]
          _ = (X.subgroupOf H').map (πH.comp (MulAut.conj s).toMonoidHom) := by
              rw [hnat]
          _ = ((X.subgroupOf H').map (MulAut.conj s).toMonoidHom).map πH := by
              rw [← Subgroup.map_map]
      have hcommH' : ⁅(X.subgroupOf H'),
          (X.subgroupOf H').map (MulAut.conj s).toMonoidHom⁆ ≤ CFSG.pCore 2 ↥H' := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
        have haX : (a : G) ∈ X := Subgroup.mem_subgroupOf.mp ha
        have hbX : (b' : G) ∈ X := Subgroup.mem_subgroupOf.mp hb'
        have hmemO2M : ⁅(a : G), MulAut.conj (s : G) (b' : G)⁆ ∈
            CFSG.Open.pCoreOf 2 D.M :=
          (Subgroup.commutator_le.mp hcomm) (a : G) haX (MulAut.conj (s : G) (b' : G))
            (Subgroup.mem_map_of_mem (MulAut.conj (s : G)).toMonoidHom hbX)
        have hmemH' : ⁅(a : G), MulAut.conj (s : G) (b' : G)⁆ ∈
            CFSG.Open.pCoreOf 2 H' :=
          (pCoreOf_M_le_of_T_le hTH hH'M) hmemO2M
        have hcoe : ((⁅a, (MulAut.conj s).toMonoidHom b'⁆ : ↥H') : G) =
            ⁅(a : G), MulAut.conj (s : G) (b' : G)⁆ := by
          simp [commutatorElement_def, MulAut.conj_apply]
        rw [← CFSG.openPCoreOf_subgroupOf]
        exact Subgroup.mem_subgroupOf.mpr (by rwa [hcoe])
      have hXcomm : ⁅Xbar, Xbar.map ψ.toMonoidHom⁆ = ⊥ := by
        rw [hXbars, hXbar_eq, ← Subgroup.map_commutator,
          Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        exact hcommH'
      exact hXcomm
  have hconjK : ∀ t ∈ Tbar,
      K.map (MulAut.conj t).toMonoidHom = K ∨
        ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
    intro t ht
    rcases hconjXbar t ht with hfix | hcomm
    · left
      rw [show K = ⁅Xbar, Xbar⁆ from Subgroup.map_subtype_commutator Xbar,
        Subgroup.map_commutator, hfix]
    · right
      have hKle : K ≤ Xbar := by
        rw [show K = ⁅Xbar, Xbar⁆ from Subgroup.map_subtype_commutator Xbar]
        exact Subgroup.commutator_le_self Xbar
      have hKle' : K.map (MulAut.conj t).toMonoidHom ≤
          Xbar.map (MulAut.conj t).toMonoidHom := Subgroup.map_mono hKle
      exact le_bot_iff.mp ((Subgroup.commutator_mono hKle hKle').trans (le_of_eq hcomm))
  obtain ⟨hKcomp, hKtop'⟩ :=
    CFSG.GroupTheory.isComponent_of_conj_dichotomy hKqs' hconjK hKtop
  refine ⟨K, hKcomp, hKtop', ?_⟩
  let eK : ↥(commutator ↥Xbar) ≃* ↥K :=
    Subgroup.equivMapOfInjective (commutator ↥Xbar) Xbar.subtype Xbar.subtype_injective
  let eKZ' : (↥(commutator ↥Xbar) ⧸ Subgroup.center ↥(commutator ↥Xbar)) ≃*
      (↥K ⧸ Subgroup.center ↥K) :=
    QuotientGroup.congr (Subgroup.center ↥(commutator ↥Xbar)) (Subgroup.center ↥K) eK
      (Subgroup.map_center_eq eK)
  exact Or.inl ⟨q, isL2Over17_of_mulEquiv (eKZ'.symm.trans (eKZ.trans eO)) hX,
    Or.inl rfl, h9⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
