module

public import CFSG.RankThree.PartTwo.Sec18.Item189ListEven
public import CFSG.RankThree.PartTwo.Sec18.Item189ListRadical
public import CFSG.RankThree.PartOne.S12.Sec15BorelTits
public import CFSG.RankThree.PartOne.S12.Sec1511Model
public import CFSG.RankThree.PartTwo.Sec20.Item20Res7ProofL3Aut
public import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIL3EvenTools
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.Models.PGL
public import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic
public import CFSG.RankThree.PartTwo.Sec18.Item189StepProofOddL2

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section L3


theorem card_outer_projSL_three_dvd {n : ℕ} (hn : Odd n) :
    Nat.card (Outer ↥(projSL 3 (GaloisField 2 n))) ∣ 2 * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := hn.pos
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 3 2 n := by
    unfold CFSG.Open.StatedLieAdmissible
    refine ⟨Nat.prime_two, hn1, ?_⟩
    simp
  have hT := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm
    (MulEquiv.refl (projSL 3 (GaloisField 2 n)))
  have hdvd : Nat.card (Outer (projSL 3 (GaloisField 2 n))) ∣ 2 * n * Nat.gcd 3 (2 ^ n - 1) :=
    (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inl rfl) (le_refl 3) Nat.prime_two hn1 hT).1
  have hg : Nat.gcd 3 (2 ^ n - 1) = 1 :=
    Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (not_three_dvd_two_pow_sub_one189 hn))
  rwa [hg, mul_one] at hdvd

theorem lieModel_projSL_three {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (e : X ≃* projSL 3 (GaloisField 2 n)) : Blueprint.LieModel X .PSL 3 2 n := by
  refine Or.inl ⟨by decide, ?_, ?_⟩
  · exact ⟨Nat.prime_two, hn, by norm_num, by simp, by simp⟩
  · exact ⟨GaloisField 2 n, inferInstance, inferInstance, GaloisField.card 2 n (by omega),
      ⟨e.trans (CFSG.RankThree.PartOne.statedProjEquivRefl
        (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL 3 _)).symm⟩⟩

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem isCoatom_of_projUpperTriangular_lt {F : Type} [Field F] {P : Subgroup (projectiveSL 3 F)}
    (hP : P ≠ ⊤) (hBP : projUpperTriangular 3 F ≤ P) (hne : projUpperTriangular 3 F ≠ P) :
    IsCoatom P := by
  classical
  set A := P.comap (proj 3 F) with hA
  have hMA : A.map (proj 3 F) = P :=
    Subgroup.map_comap_eq_self_of_surjective (proj_surjective 3 F) P
  have hBA : upperTriangular 3 F ≤ A := by
    rw [hA, ← Subgroup.map_le_iff_le_comap]
    exact hBP
  obtain ⟨hAI, -⟩ := borel_overgroups A hBA
  set I := borelOvergroupCuts A with hI
  have hsub : I ⊆ {1, 2} := by
    rintro i ⟨hi, hin, -⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I
  · exfalso
    have hI12 : I = {1, 2} := Set.Subset.antisymm hsub (by
      intro i hi
      rcases hi with rfl | rfl
      · exact h1
      · exact h2)
    have hAB : A ≤ upperTriangular 3 F := by
      rw [hAI, hI12, (subflag_stabilizer_generation (K := F) (n := 3) {1, 2}).1,
        Subgroup.closure_le]
      rintro g (hg | ⟨j, hj, hjn, hjI, rfl⟩)
      · exact hg
      · exfalso
        apply hjI
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
    apply hne
    rw [← hMA, projUpperTriangular, le_antisymm hAB hBA]
  · have hI1 : I = {1} := Set.Subset.antisymm (by
      intro i hi
      rcases hsub hi with rfl | rfl
      · rfl
      · exact absurd hi h2) (by
      intro i hi
      rw [Set.mem_singleton_iff.mp hi]
      exact h1)
    have : P = projStabilizer (flagSpace 3 F 1) := by
      rw [← hMA, hAI, hI1, flagStabilizer_singleton]
      rfl
    rw [this]
    exact isCoatom_projStabilizer_flagSpace (by norm_num) (by norm_num)
  · have hI2 : I = {2} := Set.Subset.antisymm (by
      intro i hi
      rcases hsub hi with rfl | rfl
      · exact absurd hi h1
      · rfl) (by
      intro i hi
      rw [Set.mem_singleton_iff.mp hi]
      exact h2)
    have : P = projStabilizer (flagSpace 3 F 2) := by
      rw [← hMA, hAI, hI2, flagStabilizer_singleton]
      rfl
    rw [this]
    exact isCoatom_projStabilizer_flagSpace (by norm_num) (by norm_num)
  · exfalso
    have hI0 : I = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun i hi => by
      rcases hsub hi with rfl | rfl
      · exact h1 hi
      · exact h2 hi)
    apply hP
    rw [← hMA, hAI, hI0, flagStabilizer_empty, Subgroup.map_top_of_surjective _
      (proj_surjective 3 F)]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem isCoatom_of_borel_lt_model {F : Type} [Field F] [Finite F] [CharP F 2]
    {P : Subgroup (projectiveSL 3 F)} (hP : P ≠ ⊤) (T : Sylow 2 (projectiveSL 3 F))
    (hTP : Subgroup.normalizer ((T : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) ≤ P)
    (hne : Subgroup.normalizer ((T : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) ≠ P) :
    IsCoatom P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : Subgroup.normalizer ((T : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) ∈
      sylowNormalizers (projectiveSL 3 F) 2 := ⟨T, rfl⟩
  rw [sylowNormalizers_eq (K := F) 2 (by norm_num)] at hmem
  obtain ⟨x, hx⟩ := hmem
  set Φ := MulEquiv.mapSubgroup (MulAut.conj x⁻¹ : projectiveSL 3 F ≃* projectiveSL 3 F) with hΦ
  have hΦB : Φ (Subgroup.normalizer ((T : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))) =
      projUpperTriangular 3 F := by
    rw [hx]
    show ((projUpperTriangular 3 F).map (MulAut.conj x : projectiveSL 3 F →* projectiveSL 3 F)).map
      (MulAut.conj x⁻¹ : projectiveSL 3 F →* projectiveSL 3 F) = projUpperTriangular 3 F
    rw [Subgroup.map_map]
    have : (MulAut.conj x⁻¹ : projectiveSL 3 F →* projectiveSL 3 F).comp
        (MulAut.conj x : projectiveSL 3 F →* projectiveSL 3 F) = MonoidHom.id _ := by
      ext g
      simp [MulAut.conj_apply, mul_assoc]
    rw [this, Subgroup.map_id]
  rw [← OrderIso.isCoatom_iff Φ P]
  refine isCoatom_of_projUpperTriangular_lt ?_ ?_ ?_
  · intro h
    exact hP (Φ.injective (h.trans Φ.map_top.symm))
  · rw [← hΦB]
    exact Φ.monotone hTP
  · rw [← hΦB]
    exact fun h => hne (Φ.injective h)

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem isCoatom_of_borel_lt {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : Odd n)
    (e : Y ≃* projSL 3 (GaloisField 2 n)) (S : Sylow 2 Y) {P : Subgroup Y} (hP : P ≠ ⊤)
    (hSP : Subgroup.normalizer ((S : Subgroup Y) : Set Y) ≤ P)
    (hne : Subgroup.normalizer ((S : Subgroup Y) : Set Y) ≠ P) : IsCoatom P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e' : Y ≃* projectiveSL 3 (GaloisField 2 n) :=
    e.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 n))
  have hs : Function.Surjective e'.toMonoidHom := e'.surjective
  set Ψ := MulEquiv.mapSubgroup e' with hΨ
  have hN : Subgroup.normalizer
      (((S.mapSurjective hs : Sylow 2 (projectiveSL 3 (GaloisField 2 n))) :
        Subgroup (projectiveSL 3 (GaloisField 2 n))) : Set (projectiveSL 3 (GaloisField 2 n))) =
      Ψ (Subgroup.normalizer ((S : Subgroup Y) : Set Y)) := by
    rw [Sylow.coe_mapSurjective]
    exact (Subgroup.map_equiv_normalizer_eq (S : Subgroup Y) e').symm
  rw [← OrderIso.isCoatom_iff Ψ P]
  refine isCoatom_of_borel_lt_model ?_ (S.mapSurjective hs) ?_ ?_
  · intro h
    exact hP (Ψ.injective (h.trans Ψ.map_top.symm))
  · rw [hN]
    exact Ψ.monotone hSP
  · rw [hN]
    exact fun h => hne (Ψ.injective h)

theorem exists_maxParabolic_of_radical {Y : Type} [Group Y] [Finite Y] {X R : Subgroup Y}
    {n : ℕ} (hn : Odd n) (e : Nonempty (↥X ≃* projSL 3 (GaloisField 2 n))) (hRX : R ≤ X)
    (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hrad : CFSG.Open.pCoreOf 2 (Subgroup.normalizer (R : Set Y) ⊓ X) ≤ R) {x : Y}
    (hx : x ∈ Subgroup.normalizer (R : Set Y) ⊓ X) (hx3 : orderOf x = 3) :
    IsMaxParabolicRankTwo ((Subgroup.normalizer (R : Set Y) ⊓ X).subgroupOf X) ∧
      R = CFSG.Open.pCoreOf 2 (Subgroup.normalizer (R : Set Y) ⊓ X) := by
  obtain ⟨e⟩ := e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := hn.pos
  set N : Subgroup Y := Subgroup.normalizer (R : Set Y) ⊓ X with hN
  have hRN : R ≤ N := le_inf Subgroup.le_normalizer hRX
  have hcoreY : CFSG.Open.pCoreOf 2 N = R :=
    le_antisymm hrad (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRN
      (fun g hg => hg.1) hR2)
  refine ⟨?_, hcoreY.symm⟩
  set R' : Subgroup ↥X := R.subgroupOf X with hR'
  have hNR' : Subgroup.normalizer (R' : Set ↥X) = N.subgroupOf X := by
    rw [hN, Subgroup.inf_subgroupOf_right, ← Subgroup.subgroupOf_normalizer_eq hRX]
  have hcoreX : CFSG.Open.pCoreOf 2 (Subgroup.normalizer (R' : Set ↥X)) = R' := by
    rw [hNR', pCoreOf_subgroupOf189 (inf_le_right : N ≤ X), hcoreY]
  have hR'1 : R' ≠ ⊥ := by
    intro h
    apply hR1
    rw [hR', Subgroup.subgroupOf_eq_bot] at h
    exact (disjoint_iff.mp h).symm ▸ (inf_eq_left.mpr hRX).symm
  have hR'2 : IsPGroup 2 R' :=
    hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRX).symm
  obtain ⟨hneTop, S₀, hS₀, -⟩ := CFSG.RankThree.PartOne.borelTits_normalizer_parabolic
    Nat.prime_two (lieModel_projSL_three hn1 e) hR'1 hR'2 hcoreX
  have hS₀' := hS₀ (by decide)
  set x' : ↥X := ⟨x, hx.2⟩ with hx'
  have hx'N : x' ∈ Subgroup.normalizer (R' : Set ↥X) := by
    rw [hNR']
    exact hx
  have hx'3 : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3 ▸ pow_orderOf_eq_one x)
  have hne : Subgroup.normalizer ((S₀ : Subgroup ↥X) : Set ↥X) ≠
      Subgroup.normalizer (R' : Set ↥X) := by
    intro heq
    have h1 := eq_one_of_mem_normalizer_projSL189 hn e S₀ (heq ▸ hx'N) hx'3
    have : x = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at hx3
    omega
  rw [← hNR']
  exact ⟨isCoatom_of_borel_lt hn e S₀ hneTop hS₀' hne, S₀, hS₀'⟩

end L3

theorem ListData189.le_of_isMaxParabolic {Y : Type} [Group Y] [Finite Y] {X Q : Subgroup Y}
    {Γ : Subgroup (MulAut Y)} {x : Y} (h : ListData189 X Q Γ x) {n : ℕ} (hn : Odd n)
    (e : ↥X ≃* projSL 3 (GaloisField 2 n))
    (hpar : IsMaxParabolicRankTwo
      ((Subgroup.normalizer ((Q ⊓ X : Subgroup Y) : Set Y) ⊓ X).subgroupOf X)) : Q ≤ X := by
  haveI := h.normal
  intro σ hσ
  set P : Subgroup ↥X :=
    (Subgroup.normalizer ((Q ⊓ X : Subgroup Y) : Set Y) ⊓ X).subgroupOf X with hP
  have hα2 : ∃ a : ℕ, (MulAut.conjNormal σ : MulAut ↥X) ^ 2 ^ a = 1 := by
    obtain ⟨a, ha⟩ := h.isPGroup ⟨σ, hσ⟩
    refine ⟨a, ?_⟩
    rw [← map_pow]
    have : σ ^ 2 ^ a = 1 := congrArg Subtype.val ha
    rw [this, map_one]
  have hσN : σ ∈ Subgroup.normalizer ((Q ⊓ X : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨fun ht => ⟨Q.mul_mem (Q.mul_mem hσ ht.1) (Q.inv_mem hσ), h.normal.conj_mem t ht.2 σ⟩,
      fun ht => ⟨?_, ?_⟩⟩
    · have := Q.mul_mem (Q.mul_mem (Q.inv_mem hσ) ht.1) hσ
      simpa [mul_assoc] using this
    · have := h.normal.conj_mem _ ht.2 σ⁻¹
      simpa [mul_assoc] using this
  have hαP : P.map (MulAut.conjNormal σ : MulAut ↥X).toMonoidHom = P := by
    ext a
    rw [Subgroup.mem_map_equiv]
    set b := (MulAut.conjNormal σ : MulAut ↥X).symm a with hb
    have hab : (a : Y) = σ * (b : Y) * σ⁻¹ := by
      have : (MulAut.conjNormal σ : MulAut ↥X) b = a := (MulAut.conjNormal σ).apply_symm_apply a
      rw [← this]
      rfl
    have hba : (b : Y) = σ⁻¹ * (a : Y) * σ := by
      rw [hab]
      group
    rw [hP, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    refine ⟨fun hbN => ⟨?_, a.2⟩, fun haN => ⟨?_, b.2⟩⟩
    · rw [hab]
      exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hσN hbN.1)
        ((Subgroup.normalizer _).inv_mem hσN)
    · rw [hba]
      exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem
        ((Subgroup.normalizer _).inv_mem hσN) haN.1) hσN
  obtain ⟨g, hg⟩ := Sec20.kFactL3OddParabolicInner_holds n hn ↥X ⟨e⟩ P hpar _ hα2 hαP
  exact h.mem_of_conjNormal_inner hg

theorem list189L3Even_of :
    List189L3Even := by
  intro Y _ _ X Q Γ x n h hn ⟨e⟩
  by_cases hR : Q ⊓ X = ⊥
  ·
    right; right; right; left
    refine ⟨⟨n, hn, ⟨e⟩⟩, ?_, ?_⟩
    · have hout : Nat.card (Outer ↥X) ∣ 2 ^ 1 * n := by
        rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv,
          pow_one]
        exact card_outer_projSL_three_dvd hn
      have hd := h.card_dvd_two_pow hR hout rfl hn
      rw [pow_one] at hd
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
      · exact absurd (Subgroup.card_eq_one.mp h1) h.ne_bot
      · exact h2
    · rw [h.centralizer_eq, sup_bot_eq]
      exact hR
  · right; right; left
    have hxR : x ∈ Subgroup.normalizer ((Q ⊓ X : Subgroup Y) : Set Y) ⊓ X :=
      ⟨h.mem_normalizer_inf, h.mem⟩
    have hcore : CFSG.Open.pCoreOf 2 (Subgroup.normalizer ((Q ⊓ X : Subgroup Y) : Set Y) ⊓ X) ≤
        Q ⊓ X := h.pCoreOf_normalizer_le
    obtain ⟨hpar, hRcore⟩ := exists_maxParabolic_of_radical hn ⟨e⟩ inf_le_right hR
      (h.isPGroup.to_le inf_le_left) hcore hxR h.orderOf_eq
    have hQX : Q ≤ X := h.le_of_isMaxParabolic hn e hpar
    refine ⟨⟨n, hn, ⟨e⟩⟩, _, inf_le_right, hpar, ?_⟩
    rw [← hRcore, inf_eq_left.mpr hQX]

end CFSG.RankThree.PartTwo.Sec18
