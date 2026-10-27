module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSix
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Char
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSetup
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def U3EvenCentPerfect : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n r : ℕ), UC22.IsU3 X n → r.Prime → 3 < r →
    ∀ A P : Subgroup X, Nat.card A = r → ⁅P, P⁆ = P → ¬ r ∣ Nat.card P →
      A ≤ normalizer (P : Set X) → A ≤ centralizer (P : Set X)

@[expose] def zHat (Y : Subgroup G) : Subgroup G :=
  ((center (UC22.Bar2 Y)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map Y.subtype

theorem commutator_mem_normalizer {Y E A : Subgroup G} (hEY : E ≤ normalizer (Y : Set G))
    (hAY : A ≤ Y) {e a : G} (he : e ∈ E) (ha : a ∈ A) :
    ⁅e, a⁆ ∈ normalizer (Y : Set G) := by
  have heN := hEY he
  have haN : a ∈ normalizer (Y : Set G) := Subgroup.le_normalizer (hAY ha)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ heN haN) (Subgroup.inv_mem _ heN)) (Subgroup.inv_mem _ haN)

theorem exists_perfectLift [Finite G] {Y E : Subgroup G} {X : Type} [Group X]
    (hEY : E ≤ normalizer (Y : Set G)) (hE : ⁅E, E⁆ = E)
    (hXZ : Subgroup.center X = ⊥) [hOut : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)]
    (ψN : ↥(normalizer (Y : Set G)) →* MulAut X) :
    ∃ s : ↥E →* X, ∀ e, ψN (Subgroup.inclusion hEY e) = MulAut.conj (s e) := by
  classical
  have : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hE
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hXZ
  let ψE : ↥E →* MulAut X := ψN.comp (Subgroup.inclusion hEY)
  let f : ↥E → X := fun e =>
    Classical.choose (CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
      ψE e)
  have hf : ∀ e, ψE e = MulAut.conj (f e) := fun e => Classical.choose_spec
    (CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner ψE e)
  let s : ↥E →* X :=
    { toFun := f
      map_one' := by
        apply hinj
        rw [← hf 1, map_one]
        exact (map_one (MulAut.conj : X →* MulAut X)).symm
      map_mul' := fun e₁ e₂ => by
        apply hinj
        rw [← hf (e₁ * e₂), map_mul, map_mul, ← hf e₁, ← hf e₂] }
  exact ⟨s, fun e => hf e⟩

theorem isSolvable_zHat [Finite G] (Y : Subgroup G) : Group.IsSolvable ↥(zHat Y) := by
  classical
  let B := UC22.Bar2 Y
  let K : Subgroup ↥Y :=
    (Subgroup.center B).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
  have hzHat : zHat Y = K.map Y.subtype := rfl
  have hP : IsPGroup 2 (CFSG.pCore 2 ↥Y) := CFSG.pCore_isPGroup
  have hPsolv : Group.IsSolvable ↥(CFSG.pCore 2 ↥Y) := by
    have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥Y) := hP.isNilpotent
    infer_instance
  have hPK : CFSG.pCore 2 ↥Y ≤ K := by
    intro x hx
    refine Subgroup.mem_comap.mpr ?_
    have h1 : QuotientGroup.mk (s := CFSG.pCore 2 ↥Y) x = 1 :=
      (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥Y) x).mpr hx
    change QuotientGroup.mk (s := CFSG.pCore 2 ↥Y) x ∈ Subgroup.center B
    rw [h1]
    exact Subgroup.one_mem _
  have hK : Group.IsSolvable ↥K := by
    let N : Subgroup ↥K := (CFSG.pCore 2 ↥Y).subgroupOf K
    let eN : ↥N ≃* ↥(CFSG.pCore 2 ↥Y) := Subgroup.subgroupOfEquivOfLe hPK
    have hNsolv : Group.IsSolvable ↥N := by
      have : Group.IsSolvable ↥(CFSG.pCore 2 ↥Y) := hPsolv
      exact Group.isSolvable_of_isSolvable_injective (f := eN.toMonoidHom) eN.injective
    let g : ↥K →* ↥(Subgroup.center B) :=
      { toFun := fun k => ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (k : ↥Y), k.2⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun k l => Subtype.ext (map_mul _ _ _) }
    have hker : g.ker ≤ N.subtype.range := by
      intro k hk
      rw [MonoidHom.mem_ker] at hk
      have h1 := congrArg (fun z : ↥(Subgroup.center B) => (z : UC22.Bar2 Y)) hk
      change QuotientGroup.mk (s := CFSG.pCore 2 ↥Y) (k : ↥Y) = 1 at h1
      have hkP : (k : ↥Y) ∈ CFSG.pCore 2 ↥Y :=
        (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥Y) (k : ↥Y)).mp h1
      have hkN : k ∈ N := Subgroup.mem_subgroupOf.mpr hkP
      exact ⟨⟨k, hkN⟩, rfl⟩
    have : IsMulCommutative ↥(Subgroup.center B) :=
      Subgroup.center.isMulCommutative (G := B)
    refine Group.isSolvable_of_ker_le_range N.subtype g ?_
    simpa [Subgroup.range_subtype] using hker
  rw [hzHat]
  have : Group.IsSolvable ↥K := hK
  let eK := K.equivMapOfInjective Y.subtype Y.subtype_injective
  exact Group.isSolvable_of_isSolvable_injective (f := eK.symm.toMonoidHom) eK.symm.injective

theorem range_le_normalizer_of_lift [Finite G] {Y A E : Subgroup G} {X : Type} [Group X]
    (hAY : A ≤ Y) (hAE : A ≤ normalizer (E : Set G))
    (hXZ : Subgroup.center X = ⊥)
    (ψN : ↥(normalizer (Y : Set G)) →* MulAut X) (πA : ↥A →* X) (s : ↥E →* X)
    (hAψ : ∀ a : ↥A,
      ψN (Subgroup.inclusion (hAY.trans (Subgroup.le_normalizer)) a) = MulAut.conj (πA a))
    (hEY : E ≤ normalizer (Y : Set G))
    (hs : ∀ e : ↥E, ψN (Subgroup.inclusion hEY e) = MulAut.conj (s e)) :
    πA.range ≤ Subgroup.normalizer (s.range : Set X) := by
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hXZ
  let hNA : A ≤ normalizer (Y : Set G) := hAY.trans (Subgroup.le_normalizer)
  let conjE : ↥A → ↥E → ↥E := fun a e =>
    ⟨(a : G) * (e : G) * (a : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hAE a.2) (e : G)).mp e.2⟩
  have hconj : ∀ (a : ↥A) (e : ↥E),
      πA a * s e * (πA a)⁻¹ = s (conjE a e) := by
    intro a e
    apply hinj
    rw [← hs (conjE a e)]
    have hincl : Subgroup.inclusion hEY (conjE a e) =
        Subgroup.inclusion hNA a * Subgroup.inclusion hEY e *
          (Subgroup.inclusion hNA a)⁻¹ := Subtype.ext rfl
    rw [hincl, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, ← hAψ a, ← hs e]
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · rintro ⟨e, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨conjE a e, (hconj a e).symm⟩
  · intro hp
    have h1 : πA a⁻¹ * (πA a * p * (πA a)⁻¹) * (πA a⁻¹)⁻¹ ∈ s.range := by
      obtain ⟨e, he⟩ := hp
      rw [← he]
      exact MonoidHom.mem_range.mpr ⟨conjE a⁻¹ e, (hconj a⁻¹ e).symm⟩
    rw [map_inv, inv_inv] at h1
    have h2 : (πA a)⁻¹ * (πA a * p * (πA a)⁻¹) * πA a = p := by group
    rwa [h2] at h1

theorem mem_zHat_of_centerQuotientHom_eq_one [Finite G] {Y : Subgroup G} {n : ℕ}
    (hY : UC22.IsSU3 (UC22.Bar2 Y) n) {c : G}
    (hc : c ∈ normalizer (Y : Set G))
    (hψ : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom
      (UC22.Bar2 Y) (CFSG.Quasithin.EmptyFaithfulMultiple.L15420.quotConj Y c hc) = 1)
    {y : G} (hy : y ∈ Y) : ⁅c, y⁆ ∈ zHat Y := by
  have : Group.IsPerfect (UC22.Bar2 Y) := Group.isPerfect_def.mpr hY.1.1
  have hψ' : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom
      (UC22.Bar2 Y)
      (CFSG.Quasithin.EmptyFaithfulMultiple.L15420.quotConj Y c hc) =
      CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (UC22.Bar2 Y) 1 := by
    rw [map_one]
    exact hψ
  have hq : CFSG.Quasithin.EmptyFaithfulMultiple.L15420.quotConj Y c hc = 1 :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective
      (UC22.Bar2 Y) hψ'
  have hpc : c * y * c⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y :=
    (CFSG.Quasithin.EmptyFaithfulMultiple.L15420.quotConj_eq_one_iff hc).mp hq y hy
  rw [CFSG.openPCoreOf_eq_map_pCore] at hpc
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hpc
  have hK : z ∈ (Subgroup.center (UC22.Bar2 Y)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) := by
    refine Subgroup.mem_comap.mpr ?_
    have h1 : QuotientGroup.mk (s := CFSG.pCore 2 ↥Y) z = 1 :=
      (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥Y) z).mpr hz
    change QuotientGroup.mk (s := CFSG.pCore 2 ↥Y) z ∈ Subgroup.center (UC22.Bar2 Y)
    rw [h1]
    exact Subgroup.one_mem _
  have hzHat : Y.subtype z ∈ zHat Y := Subgroup.mem_map_of_mem Y.subtype hK
  rw [hzy] at hzHat
  exact hzHat

theorem commutator_action_eq_one [Finite G] (hU : U3EvenCentPerfect)
    {Y A E : Subgroup G} {n r : ℕ} (hY : UC22.IsSU3 (UC22.Bar2 Y) n)
    (hr : r.Prime) (hr3 : 3 < r) (hAY : A ≤ Y) (hA : Nat.card A = r)
    (hEY : E ≤ normalizer (Y : Set G)) (hE : ⁅E, E⁆ = E)
    (hAE : A ≤ normalizer (E : Set G)) (hrE : ¬ r ∣ Nat.card E)
    (e : ↥E) (a : ↥A) :
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (UC22.Bar2 Y)
      (CFSG.Quasithin.EmptyFaithfulMultiple.L15420.quotConj Y ⁅(e : G), (a : G)⁆
        (commutator_mem_normalizer hEY hAY e.2 a.2)) = 1 := by
  classical
  let B := UC22.Bar2 Y
  let X := B ⧸ Subgroup.center B
  let π₁ : ↥Y →* B := QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
  let π₂ : B →* X := QuotientGroup.mk' (Subgroup.center B)
  let π : ↥Y →* X := π₂.comp π₁
  let ψN : ↥(normalizer (Y : Set G)) →* MulAut X :=
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom B).comp
      (CFSG.Quasithin.EmptyFaithfulMultiple.L15420.quotConjHom Y)
  let hNA : A ≤ normalizer (Y : Set G) := hAY.trans (Subgroup.le_normalizer)
  let ψA : ↥A →* MulAut X := ψN.comp (Subgroup.inclusion hNA)
  let ψE : ↥E →* MulAut X := ψN.comp (Subgroup.inclusion hEY)
  let πA : ↥A →* X := π.comp (Subgroup.inclusion hAY)
  have hpsiA : ∀ a : ↥A, ψA a = MulAut.conj (πA a) := by
    intro a
    have hN : (a : G) ∈ normalizer (Y : Set G) := hNA a.2
    have h1 : ψA a = CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom B
        (CFSG.Quasithin.EmptyFaithfulMultiple.L15420.quotConj Y (a : G) hN) := rfl
    rw [h1]
    rw [show CFSG.Quasithin.EmptyFaithfulMultiple.L15420.quotConj Y (a : G) hN =
        CFSG.Quasithin.EmptyFaithfulMultiple.L15420.quotConj Y (a : G)
          (Subgroup.le_normalizer (hAY a.2)) from rfl]
    rw [CFSG.Quasithin.EmptyFaithfulMultiple.L15420.quotConj_of_mem (hAY a.2),
      CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_conj]
    rfl
  have : Group.IsPerfect B := Group.isPerfect_def.mpr hY.1.1
  have hXZ : Subgroup.center X = ⊥ := by
    simpa [X, B] using Group.IsPerfect.center_quotient_center_eq_bot B
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
    CFSG.SeitzReduction.UnitaryPilot.isSolvable_outer_of_lieModel hY.2
  have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := hOut
  obtain ⟨s, hs⟩ := exists_perfectLift hEY hE hXZ ψN
  have hAnorm : πA.range ≤ Subgroup.normalizer (s.range : Set X) :=
    range_le_normalizer_of_lift hAY hAE hXZ ψN πA s hpsiA hEY hs
  have : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hE
  have hPperf : ⁅s.range, s.range⁆ = s.range := by
    have hperf : Group.IsPerfect ↥s.range :=
      Group.IsPerfect.ofSurjective (f := s.rangeRestrict)
        (MonoidHom.rangeRestrict_surjective s)
    exact Subgroup.isPerfect_iff.mp hperf
  have hPr : ¬ r ∣ Nat.card (s.range : Subgroup X) := by
    intro hdvd
    exact hrE (hdvd.trans (Subgroup.card_range_dvd s))
  have hAdvd : Nat.card (πA.range : Subgroup X) ∣ r := by
    simpa [hA] using Subgroup.card_range_dvd πA
  have hAcent : πA.range ≤ Subgroup.centralizer (s.range : Set X) := by
    rcases Nat.Prime.eq_one_or_self_of_dvd hr (Nat.card (πA.range : Subgroup X)) hAdvd with
      h1 | h1
    · have hbot : πA.range = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      rw [hbot]
      exact bot_le
    · exact hU X n r hY.2 hr hr3 (πA.range) (s.range) h1 hPperf hPr hAnorm
  have hcommute : ∀ (a : ↥A) (e : ↥E), ψA a * ψE e = ψE e * ψA a := by
    intro a e
    have hEe : ψE e = MulAut.conj (s e) := hs e
    rw [hpsiA a, hEe, ← map_mul, ← map_mul]
    congr 1
    have hmemA : πA a ∈ πA.range := MonoidHom.mem_range.mpr ⟨a, rfl⟩
    have hmemP : s e ∈ s.range := MonoidHom.mem_range.mpr ⟨e, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hAcent hmemA) (s e) hmemP).symm
  change ψN (⟨⁅(e : G), (a : G)⁆,
    commutator_mem_normalizer hEY hAY e.2 a.2⟩ : ↥(normalizer (Y : Set G))) = 1
  have hincl : (⟨⁅(e : G), (a : G)⁆,
      commutator_mem_normalizer hEY hAY e.2 a.2⟩ : ↥(normalizer (Y : Set G))) =
      ⁅Subgroup.inclusion hEY e, Subgroup.inclusion hNA a⁆ := Subtype.ext rfl
  rw [hincl, map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr (hcommute a e).symm

theorem commutator_le_zHat [Finite G] (hU : U3EvenCentPerfect) {Y A E : Subgroup G} {n r : ℕ}
    (hY : UC22.IsSU3 (UC22.Bar2 Y) n) (hr : r.Prime) (hr3 : 3 < r) (hAY : A ≤ Y)
    (hA : Nat.card A = r) (hEY : E ≤ normalizer (Y : Set G)) (hE : ⁅E, E⁆ = E)
    (hAE : A ≤ normalizer (E : Set G)) (hrE : ¬ r ∣ Nat.card E) : ⁅E, A⁆ ≤ zHat Y := by
  classical
  let B := UC22.Bar2 Y
  let X := B ⧸ Subgroup.center B
  let ψN : ↥(normalizer (Y : Set G)) →* MulAut X :=
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom B).comp
      (CFSG.Quasithin.EmptyFaithfulMultiple.L15420.quotConjHom Y)
  have hcommN : ⁅E, A⁆ ≤ normalizer (Y : Set G) := by
    rw [Subgroup.commutator_le]
    intro e he a ha
    exact commutator_mem_normalizer hEY hAY he ha
  have hker : ⁅E, A⁆ ≤ (ψN.ker).map (Subgroup.normalizer (Y : Set G)).subtype := by
    rw [Subgroup.commutator_le]
    intro e he a ha
    refine Subgroup.mem_map.mpr ⟨⟨⁅e, a⁆, commutator_mem_normalizer hEY hAY he ha⟩, ?_, rfl⟩
    exact commutator_action_eq_one hU hY hr hr3 hAY hA hEY hE hAE hrE ⟨e, he⟩ ⟨a, ha⟩
  have hψc : ∀ (c : G) (hc : c ∈ normalizer (Y : Set G)), c ∈ ⁅E, A⁆ →
      CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom B
        (CFSG.Quasithin.EmptyFaithfulMultiple.L15420.quotConj Y c hc) = 1 := by
    intro c hc hmem
    change ψN ⟨c, hc⟩ = 1
    obtain ⟨n, hnker, hnc⟩ := Subgroup.mem_map.mp (hker hmem)
    have hn : n = ⟨c, hc⟩ := Subtype.ext (by simpa using hnc)
    rw [← hn]
    exact MonoidHom.mem_ker.mp hnker
  have hcomm2 : ⁅⁅E, A⁆, A⁆ ≤ zHat Y := by
    rw [Subgroup.commutator_le]
    intro c hc a ha
    have hcN : c ∈ normalizer (Y : Set G) := hcommN hc
    exact mem_zHat_of_centerQuotientHom_eq_one hY hcN (hψc c hcN hc) (hAY ha)
  have hAcop : IsPGroup r A :=
    IsPGroup.of_card (n := 1) (by rw [hA, pow_one])
  have hidem : ⁅⁅E, A⁆, A⁆ = ⁅E, A⁆ :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent
      r hr A E hAcop hrE hAE
  rwa [hidem] at hcomm2

theorem k_UC146M_of_u3EvenCentPerfect (hU : U3EvenCentPerfect) : K_UC146M := by
  intro G _ _ Y A E n r hY hr hr3 hAY hA hEY hE hAE hrE
  have hcomm : ⁅E, A⁆ ≤ zHat Y :=
    commutator_le_zHat hU hY hr hr3 hAY hA hEY hE hAE hrE
  have hcommE : ⁅E, A⁆ ≤ E := Subgroup.le_normalizer_iff_commutator_le_left.mp hAE
  have : Group.IsSolvable ↥(zHat Y) := isSolvable_zHat Y
  have hSsolv : Group.IsSolvable ↥(⁅E, A⁆) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hcomm)
      (Subgroup.inclusion_injective hcomm)
  have hSnorm : ((⁅E, A⁆).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcommE).mpr
      (Subgroup.normalizer_commutator_ge_left E A)
  have hle : ⁅E, A⁆ ≤ CFSG.Quasithin.solvRad E :=
    CFSG.Quasithin.le_solvRad hcommE hSnorm hSsolv
  rw [CFSG.Quasithin.solvRad_eq_map_solvableRadical] at hle
  simpa [UC22.OInf] using hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
