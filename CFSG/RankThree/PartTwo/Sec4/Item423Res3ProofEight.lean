module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofCharThree
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemG23
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemL43
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.U43Census
public import Certificates.Certificate8177
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open Subgroup

namespace Res423Three

open Res423Two

theorem isElemAbelian_zpowers {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (zpowers x) := by
  refine ⟨inferInstance, fun y hy => ?_⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem sup_zpowers_eq_of_card_nine {G : Type*} [Group G] [Finite G] {D : Subgroup G}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9) {z s : G} (hz : z ∈ D)
    (hz1 : z ≠ 1) (hs : s ∈ D) (hsz : s ∉ zpowers z) : zpowers z ⊔ zpowers s = D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 := hD.2 z hz
  obtain ⟨-, hcard⟩ := Sec5.isElemAbelian_sup_zpowers (isElemAbelian_zpowers hz3) hsz (hD.2 s hs)
    fun a ha => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (comm_of_isElemAbelian hD z hz s hs) k).eq
  rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1] at hcard
  exact Subgroup.eq_of_le_of_card_ge (sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hs))
    (by rw [hD9, hcard])

theorem exists_not_mem_zpowers {G : Type*} [Group G] [Finite G] {D : Subgroup G}
    (hD9 : Nat.card D = 9) {z : G} (hz3 : z ^ 3 = 1) : ∃ s ∈ D, s ∉ zpowers z := by
  by_contra hc
  push Not at hc
  have h1 := Subgroup.card_le_of_le (show D ≤ zpowers z from hc)
  have h2 : Nat.card (zpowers z) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz3)
  omega

theorem isElemAbelian_subgroupOf {G : Type*} [Group G] {E H : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) : CFSG.Assembly.IsElemAbelian 3 (E.subgroupOf H) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
  · exact comm_of_isElemAbelian hE _ (mem_subgroupOf.mp a.2) _ (mem_subgroupOf.mp b.2)
  · rw [coe_pow, coe_one]
    exact hE.2 _ (mem_subgroupOf.mp hx)

theorem census423_of_forall_le {X M : Type} [Group X] [Finite X] [Group M] (θ : X ≃* M)
    (h : ∀ D : Subgroup M, CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
      ∃ E : Subgroup M, CFSG.Assembly.IsElemAbelian 3 E ∧ D ≤ E ∧ 27 ≤ Nat.card E) :
    Census423 X := by
  intro D hD hD9 Y hY hα
  exfalso
  obtain ⟨E, hE, hDE, hE27⟩ := h (D.map θ.toMonoidHom) (isElemAbelian_map' _ hD.prop)
    (by rw [Subgroup.card_map_of_injective θ.injective, hD9])
  have hle : D ≤ E.map θ.symm.toMonoidHom := fun x hx =>
    ⟨θ x, hDE ⟨x, hx, rfl⟩, θ.symm_apply_apply x⟩
  have h1 := Subgroup.card_le_of_le (hD.2 (isElemAbelian_map' _ hE) hle)
  rw [Subgroup.card_map_of_injective θ.symm.injective, hD9] at h1
  omega

theorem forall_le_of_sylow {M : Type*} [Group M] [Finite M] {S : Subgroup M}
    (hS : Nat.card S = 3 ^ (Nat.card M).factorization 3)
    (h : ∀ D : Subgroup M, D ≤ S → CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
      ∃ E : Subgroup M, CFSG.Assembly.IsElemAbelian 3 E ∧ D ≤ E ∧ 27 ≤ Nat.card E)
    (D : Subgroup M) (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9) :
    ∃ E : Subgroup M, CFSG.Assembly.IsElemAbelian 3 E ∧ D ≤ E ∧ 27 ≤ Nat.card E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hS (Sec5.isPGroup_of_isElemAbelian hD)
  obtain ⟨E, hE, hDE, hE27⟩ := h _ (Item434AltPerm.map_conj_inv_le hg) (isElemAbelian_map' _ hD)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hD9])
  refine ⟨E.map (MulAut.conj g).toMonoidHom, isElemAbelian_map' _ hE, ?_, ?_⟩
  · rw [← Item434AltPerm.map_conj_map_conj_inv D g]
    exact Subgroup.map_mono hDE
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hE27

section G23

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.Quasithin.G2U Item434RemG23


theorem exists_E27_of_E9_R3 (D : Subgroup R3) (hD : CFSG.Assembly.IsElemAbelian 3 D)
    (hD9 : Nat.card D = 9) :
    ∃ E : Subgroup R3, CFSG.Assembly.IsElemAbelian 3 E ∧ D ≤ E ∧ 27 ≤ Nat.card E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSR := sylow_le_R3 sylWord_lt
  refine forall_le_of_sylow (S := sylow.subgroupOf R3)
    (by rw [Item434SporE81.card_subgroupOf_of_le hSR]; exact card_sylow_eq) ?_ D hD hD9
  intro D' hD'S hD' hD'9
  obtain ⟨z, hzS, hz3, hz1, hzc, hgood⟩ := exists_hgood sylCheck_true k2Check_true sylWord_lt
  obtain ⟨z', hz'⟩ : ∃ z' : R3, (z' : GL (Fin 14) (ZMod 3)) = z := ⟨⟨z, hSR hzS⟩, rfl⟩
  subst hz'
  have hz'3 : z' ^ 3 = 1 := Subtype.ext (by rw [coe_pow]; exact hz3)
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  by_cases hzD : z' ∈ D'
  · obtain ⟨s, hsD, hsz⟩ := exists_not_mem_zpowers hD'9 hz'3
    have hsS : (s : GL (Fin 14) (ZMod 3)) ∈ sylow := mem_subgroupOf.mp (hD'S hsD)
    have hs3 : (s : GL (Fin 14) (ZMod 3)) ^ 3 = 1 := by rw [← coe_pow, hD'.2 s hsD, coe_one]
    have hsz' : (s : GL (Fin 14) (ZMod 3)) ∉ zpowers (z' : GL (Fin 14) (ZMod 3)) := by
      intro h
      apply hsz
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
      exact mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [coe_zpow]; exact hk)⟩
    obtain ⟨E, hER, hE, hE81, hsE, hzE⟩ := hgood _ hsS hs3 hsz'
    refine ⟨E.subgroupOf R3, isElemAbelian_subgroupOf hE, ?_, ?_⟩
    · rw [← sup_zpowers_eq_of_card_nine hD' hD'9 hzD hz'1 hsD hsz]
      exact sup_le (zpowers_le.mpr (mem_subgroupOf.mpr hzE))
        (zpowers_le.mpr (mem_subgroupOf.mpr hsE))
    · rw [Item434SporE81.card_subgroupOf_of_le hER]
      omega
  · obtain ⟨hE, hEcard⟩ := Sec5.isElemAbelian_sup_zpowers hD' hzD hz'3
      fun a ha => Subtype.ext (hzc _ (mem_subgroupOf.mp (hD'S ha)))
    exact ⟨_, hE, le_sup_left, by rw [hEcard, hD'9]⟩

theorem census423_of_g23 {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (hX : Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1) : Census423 X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have : Fintype K := Fintype.ofFinite K
  have hK3 : Fintype.card K = 3 := by
    rw [← Nat.card_eq_fintype_card]
    simpa using hK
  have hc : Subgroup.center (Blueprint.Chevalley.adjointGroup .G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have e1 : X ≃* X ⧸ Subgroup.center X :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have e2 : Blueprint.AdjointQuotient .G2 K ≃* Blueprint.Chevalley.adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have f : K ≃+* ZMod 3 := (ZMod.ringEquivOfPrime K Nat.prime_three hK3).symm
  have e3 := CFSG.TauCetiBridge.adjointGroupCongr (τ := .G2) f
  have θ : X ≃* R3 := ((e1.trans e).trans e2).trans (e3.trans adjointEquivR3)
  exact @census423_of_forall_le X R3 _ _ R3.toGroup θ exists_E27_of_E9_R3

end G23

section L43

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Item434RemL43

theorem coe_eq_uniMat {x : SL4} (hx : x ∈ unitriangular 4 (ZMod 3)) :
    (x : Mat4) = uniMat ((x : Mat4) 0 1) ((x : Mat4) 0 2) ((x : Mat4) 0 3) ((x : Mat4) 1 2)
      ((x : Mat4) 1 3) ((x : Mat4) 2 3) := by
  obtain ⟨hl, hd⟩ := mem_unitriangular.mp hx
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact hd _
    | exact hl _ _ (by decide)
    | rfl


theorem uniMat_mul_zMat : ∀ a b c d e f : ZMod 3,
    uniMat a b c d e f * zMat = zMat * uniMat a b c d e f :=
  Certificates.certificate8177.1

theorem wMat_comm : ∀ a b c d e f : ZMod 3, ¬ (a = 0 ∧ f = 0) →
    wMat a f * uniMat a b c d e f = uniMat a b c d e f * wMat a f :=
  Certificates.certificate8177.2.1

theorem wMat_facts : ∀ a f : ZMod 3, IsR (wMat a f) ∧ (wMat a f).det = 1 ∧ wMat a f ≠ 1 ∧
    wMat a f ≠ zMat ∧ wMat a f ≠ zMat * zMat :=
  Certificates.certificate8177.2.2

@[expose] def wSL (a f : ZMod 3) : SL4 := ⟨wMat a f, (wMat_facts a f).2.1⟩

theorem wSL_mem_rGrp (a f : ZMod 3) : wSL a f ∈ rGrp :=
  mem_rGrp_iff.mpr (wMat_facts a f).1

theorem wSL_not_mem_zpowers (a f : ZMod 3) : wSL a f ∉ zpowers zSL := by
  intro h
  obtain ⟨-, -, h1, hz, hz2⟩ := wMat_facts a f
  rcases eq_of_mem_zpowers_three zSL_pow_three h with h | h | h
  · exact h1 (congrArg (fun x : SL4 => (x : Mat4)) h)
  · exact hz (congrArg (fun x : SL4 => (x : Mat4)) h)
  · apply hz2
    have h2 : ((zSL ^ 2 : SL4) : Mat4) = zMat * zMat := by
      rw [sq]
      rfl
    exact (congrArg (fun x : SL4 => (x : Mat4)) h).trans h2

theorem mul_zSL_of_mem {x : SL4} (hx : x ∈ unitriangular 4 (ZMod 3)) : x * zSL = zSL * x := by
  apply Subtype.ext
  rw [coe_mul', coe_mul', coe_eq_uniMat hx]
  exact uniMat_mul_zMat _ _ _ _ _ _

theorem exists_E27_of_le_unitriangular {P : Subgroup SL4} (hPU : P ≤ unitriangular 4 (ZMod 3))
    (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9) :
    ∃ E : Subgroup SL4, E ≤ unitriangular 4 (ZMod 3) ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
      P ≤ E ∧ Nat.card E = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzU : zSL ∈ unitriangular 4 (ZMod 3) := rGrp_le_unitriangular zSL_mem_rGrp
  suffices h : ∃ y ∈ unitriangular 4 (ZMod 3), y ∉ P ∧ y ^ 3 = 1 ∧ ∀ a ∈ P, a * y = y * a by
    obtain ⟨y, hyU, hyP, hy3, hyc⟩ := h
    obtain ⟨hE, hEcard⟩ := Sec5.isElemAbelian_sup_zpowers hP hyP hy3 hyc
    exact ⟨_, sup_le hPU (zpowers_le.mpr hyU), hE, le_sup_left, by rw [hEcard, hP9]⟩
  by_cases hzP : zSL ∈ P
  swap
  · exact ⟨zSL, hzU, hzP, zSL_pow_three, fun a ha => mul_zSL_of_mem (hPU ha)⟩
  obtain ⟨d, hdP, hdz⟩ := exists_not_mem_zpowers hP9 zSL_pow_three
  have hPeq := sup_zpowers_eq_of_card_nine hP hP9 hzP zSL_ne_one hdP hdz
  have hdU := hPU hdP
  have hcomm : ∀ y : SL4, y * zSL = zSL * y → y * d = d * y → ∀ a ∈ P, a * y = y * a := by
    intro y hyz hyd a ha
    rw [← hPeq] at ha
    have hle : zpowers zSL ⊔ zpowers d ≤ Subgroup.centralizer ({y} : Set SL4) :=
      sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyz.symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyd.symm))
    exact mem_centralizer_singleton_iff.mp (hle ha)
  by_cases hdR : d ∈ rGrp
  · have hPR : P ≤ rGrp := by
      rw [← hPeq]
      exact sup_le (zpowers_le.mpr zSL_mem_rGrp) (zpowers_le.mpr hdR)
    obtain ⟨y, hyR, hyP⟩ : ∃ y ∈ rGrp, y ∉ P := by
      by_contra hc
      push Not at hc
      have := Subgroup.card_le_of_le (show rGrp ≤ P from hc)
      rw [card_rGrp, hP9] at this
      omega
    exact ⟨y, rGrp_le_unitriangular hyR, hyP, isElemAbelian_rGrp.2 y hyR,
      fun a ha => rGrp_comm (hPR ha) hyR⟩
  ·
    have haf : ¬ ((d : Mat4) 0 1 = 0 ∧ (d : Mat4) 2 3 = 0) := by
      rintro ⟨ha0, hf0⟩
      exact hdR (mem_rGrp_iff.mpr (isR_of_mem hdU ha0 hf0))
    set w := wSL ((d : Mat4) 0 1) ((d : Mat4) 2 3) with hwdef
    have hwR := wSL_mem_rGrp ((d : Mat4) 0 1) ((d : Mat4) 2 3)
    refine ⟨w, rGrp_le_unitriangular hwR, ?_, isElemAbelian_rGrp.2 _ hwR,
      hcomm _ (mul_zSL_of_mem (rGrp_le_unitriangular hwR)) ?_⟩
    ·
      intro hwP
      have hrange : 3 ≤ Nat.card (rhoP hPU).range := by
        have hne : (rhoP hPU).range ≠ ⊥ := by
          intro hbot
          have hmem : rhoP hPU ⟨d, hdP⟩ ∈ (rhoP hPU).range := ⟨_, rfl⟩
          rw [hbot, mem_bot] at hmem
          apply hdR
          exact (rhoU_eq_one_iff (Subgroup.inclusion hPU ⟨d, hdP⟩)).mp hmem
        have hdvd : Nat.card (rhoP hPU).range ∣ 9 := by
          have h := Subgroup.card_subgroup_dvd_card (rhoP hPU).range
          rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod] at h
        have h1 : Nat.card (rhoP hPU).range ≠ 1 := fun h1 =>
          hne ((Subgroup.card_eq_one).mp h1)
        have h9 : Nat.card (rhoP hPU).range ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hdvd, by
          norm_num⟩
        have : Nat.divisors 9 = {1, 3, 9} := by decide
        rw [this] at h9
        simp only [Finset.mem_insert, Finset.mem_singleton] at h9
        omega
      have hPR3 : Nat.card (P ⊓ rGrp : Subgroup SL4) ≤ 3 := by
        have h := card_eq_mul_rhoP hPU
        rw [hP9] at h
        by_contra hc
        push Not at hc
        have : 4 * 3 ≤ Nat.card (P ⊓ rGrp : Subgroup SL4) * Nat.card (rhoP hPU).range :=
          Nat.mul_le_mul hc hrange
        omega
      have hzPR : zpowers zSL = P ⊓ rGrp := by
        refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr ⟨hzP, zSL_mem_rGrp⟩) ?_
        rw [Nat.card_zpowers, orderOf_eq_prime zSL_pow_three zSL_ne_one]
        exact hPR3
      have hwPR : w ∈ P ⊓ rGrp := ⟨hwP, hwR⟩
      rw [← hzPR] at hwPR
      exact wSL_not_mem_zpowers _ _ hwPR
    · apply Subtype.ext
      rw [coe_mul', coe_mul', coe_eq_uniMat hdU]
      exact wMat_comm _ _ _ _ _ _ haf

theorem exists_E27_of_E9_PSL43 (D : Subgroup PSL43) (hD : CFSG.Assembly.IsElemAbelian 3 D)
    (hD9 : Nat.card D = 9) :
    ∃ E : Subgroup PSL43, CFSG.Assembly.IsElemAbelian 3 E ∧ D ≤ E ∧ 27 ≤ Nat.card E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := ZMod 3) 3 (n := 4) (by norm_num)
  refine forall_le_of_sylow (S := projUnitriangular 4 (ZMod 3))
    (by rw [← hS]; exact Sylow.card_eq_multiplicity S) ?_ D hD hD9
  intro D' hD'S hD' hD'9
  set Pt := D'.comap piL ⊓ unitriangular 4 (ZMod 3) with hPt
  have hPtU : Pt ≤ unitriangular 4 (ZMod 3) := inf_le_right
  have hPtmap : Pt.map piL = D' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · intro y hy
      obtain ⟨x, hxU, rfl⟩ := hD'S hy
      exact ⟨x, ⟨hy, hxU⟩, rfl⟩
  have hPtcard : Nat.card Pt = 9 := by
    rw [← card_map_piL_of_le hPtU, hPtmap, hD'9]
  have hinjU : ∀ x ∈ unitriangular 4 (ZMod 3), ∀ y ∈ unitriangular 4 (ZMod 3),
      piL x = piL y → x = y := fun x hx y hy hxy => proj_injOn_unitriangular 4 hx hy hxy
  have hPte : CFSG.Assembly.IsElemAbelian 3 Pt := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · refine hinjU _ ((unitriangular 4 (ZMod 3)).mul_mem (hPtU x.2) (hPtU y.2)) _
        ((unitriangular 4 (ZMod 3)).mul_mem (hPtU y.2) (hPtU x.2)) ?_
      simp only [Subgroup.coe_mul, map_mul]
      exact congrArg Subtype.val (hD'.1.is_comm.comm ⟨piL x, x.2.1⟩ ⟨piL y, y.2.1⟩)
    · refine hinjU _ ((unitriangular 4 (ZMod 3)).pow_mem (hPtU hx) 3) _
        (unitriangular 4 (ZMod 3)).one_mem ?_
      rw [map_pow, map_one]
      exact hD'.2 _ hx.1
  obtain ⟨Et, hEtU, hEt, hPtEt, hEt27⟩ := exists_E27_of_le_unitriangular hPtU hPte hPtcard
  refine ⟨Et.map piL, isElemAbelian_map_piL hEt, ?_, ?_⟩
  · rw [← hPtmap]
    exact Subgroup.map_mono hPtEt
  · rw [card_map_piL_of_le hEtU, hEt27]

theorem census423_of_l43 {X : Type} [Group X] [Finite X]
    (e : X ≃* projSL 4 (GaloisField 3 1)) : Census423 X :=
  census423_of_forall_le (e.trans projSLEquivPSL43) exists_E27_of_E9_PSL43

end L43

end Res423Three

open Res423Three

theorem k423Inner46EightRest_holds :
    K423Inner46EightRest := by
  rintro X _ _ hX - hZ -
  rcases hX with ⟨⟨e⟩⟩ | ⟨-, hG | ⟨⟨e⟩⟩⟩
  · exact census423_of_l43 e
  · exact census423_of_g23 hZ hG
  · exact CFSG.AGLEmbeddingD2.Wilson.Coordinator.U43.census423_of_quot_u43 hZ e

end CFSG.RankThree.PartTwo.Sec4
