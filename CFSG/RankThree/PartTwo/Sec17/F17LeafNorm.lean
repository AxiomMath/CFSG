module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res8ProofLoc
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec17.F17LeafCore
import CFSG.RankThree.PartTwo.Sec17.PropULemmaThree
import CFSG.RankThree.PartTwo.Sec17.Item17Res9ProofLd
import CFSG.RankThree.PartTwo.Sec14.Item148PointProof142
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
public import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet

public section

namespace CFSG.RankThree.PartTwo.Sec17.F17Leaf

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.PropU
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_le_L
    {A L U : Subgroup G} {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hJ2 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hA3 : IsPGroup 3 A) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hU : IsPGroup p U) (hUL : U ≤ L) (hAU : A ≤ Subgroup.normalizer (U : Set G)) : U = ⊥ := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
    KFacts.KS14.center_eq_bot_of_j2 h415 hJ2
  have hB3 : IsPGroup 3 (A ⊓ L : Subgroup G) := hA3.to_le inf_le_left
  have hBD : A ⊓ L ≤ Subgroup.normalizer (U : Set G) := inf_le_left.trans hAU
  have hDY : U ≤ Subgroup.normalizer (L : Set G) := hUL.trans Subgroup.le_normalizer
  have hact : ∀ (d : G) (hd : d ∈ U) (y : ↥L),
      QuotientGroup.mk' (CFSG.pCore 2 ↥L)
        ⟨d * y * d⁻¹, (Subgroup.mem_normalizer_iff.mp (hDY hd) y).mp y.2⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) y :=
    fun d hd y => CFSG.RankThree.PartTwo.Sec17.Proof17Res3.mk_conj_eq_of_j2
      (Y := L) (D := U) (B := A ⊓ L) hJ2 hp hp3 hU hDY inf_le_right hB3 h9 hBD hd y
  have hcen : ∀ (d : G) (hd : d ∈ U),
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨d, hUL hd⟩ : ↥L) ∈
        Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    intro d hd
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) q
    have e : (⟨d, hUL hd⟩ : ↥L) * y * (⟨d, hUL hd⟩ : ↥L)⁻¹ =
        ⟨d * y * d⁻¹, (Subgroup.mem_normalizer_iff.mp (hDY hd) y).mp y.2⟩ :=
      Subtype.ext (by simp)
    have key : QuotientGroup.mk' (CFSG.pCore 2 ↥L)
        ((⟨d, hUL hd⟩ : ↥L) * y * (⟨d, hUL hd⟩ : ↥L)⁻¹) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥L) y := by
      rw [e]
      exact hact d hd y
    rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul] at key
    exact key.symm
  rw [Subgroup.eq_bot_iff_forall]
  intro d hd
  have hr := hcen d hd
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hr
  have hpc : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := hpc ⟨⟨d, hUL hd⟩, hr⟩
  obtain ⟨n, hn⟩ := hU ⟨d, hd⟩
  have hk' : d ^ 2 ^ k = 1 := by
    have h := congrArg (fun x : ↥(CFSG.pCore 2 ↥L) => ((x : ↥L) : G)) hk
    simpa using h
  have hn' : d ^ p ^ n = 1 := by
    have h := congrArg (fun x : ↥U => (x : G)) hn
    simpa using h
  have hcop : Nat.Coprime (2 ^ k) (p ^ n) :=
    Nat.Coprime.pow k n ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega))
  have h1 : d ^ (2 ^ k).gcd (p ^ n) = 1 := pow_gcd_eq_one.mpr ⟨hk', hn'⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
  exact h1


section Item148Binders


theorem case148_struct
    {A : Subgroup G} {c : G} {L Y : Subgroup G} [(ker148 A Y).Normal]
    (hcases : Item148Cases A (lB A) Y)
    (hch : Chosen136 A) (hΩ : omegaA A = {Subgroup.zpowers c}) (hL : L ∈ lA A c)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    deltaZero A (lB A) Y ≤ pPrimeCoreOf 3 Y ∨
    (deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔
        deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G))) ∨
    (∃ d ∈ A, d ≠ 1 ∧ IsThreeCentralIn L d ∧
      deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔
        deltaZero A (lB A) (Y ⊓ Subgroup.centralizer ({d} : Set G))) := by
  classical
  have h3L : 3 ∣ Nat.card L := by
    obtain ⟨e⟩ := hJ
    have h1 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∣ Nat.card L :=
      Subgroup.card_quotient_dvd_card _
    rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2] at h1
    exact (by norm_num : 3 ∣ 604800).trans h1
  have hLJ : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) := by
    intro c' L' hc' hL'
    rw [eq_of_mem_lA hch hΩ hL h3L hc' hL']
    exact hJ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    exact Or.inl h1
  ·
    obtain ⟨c', hc', hdel, -⟩ := h2
    have hc'c : Subgroup.zpowers c' = Subgroup.zpowers c := by
      rw [hΩ] at hc'
      exact Set.mem_singleton_iff.mp hc'
    rw [hc'c] at hdel
    exact Or.inr (Or.inl hdel)
  ·
    obtain ⟨c', d, L', hc', hL', -, hdA, hd1, hd3, hdel, -⟩ := h3
    have hL'L : L' = L := eq_of_mem_lA hch hΩ hL h3L hc' hL'
    rw [hL'L] at hd3
    exact Or.inr (Or.inr ⟨d, hdA, hd1, hd3, hdel⟩)
  ·
    exfalso
    obtain ⟨-, ⟨c', L', hc', hL', hA7⟩, -⟩ := h4
    exact (isEmpty_equiv_small_of_equiv_J2 (hLJ c' L' hc' hL')).1.false hA7.some
  ·
    exfalso
    obtain ⟨c', hcA, L', n, m, hc', hL', -, -, -, -, -, -, hEps, -⟩ := h5
    exact not_isLThreeEpsAt_of_equiv_J2 (hLJ c' L' hc' hL') 2 (n * m) hEps
  ·
    exfalso
    obtain ⟨-, -, h6⟩ := h6
    rw [hΩ, Set.ncard_singleton] at h6
    omega
  ·
    exfalso
    obtain ⟨a₁, a₂, L₁, L₂, J₁, J₂, p₁, f₁, e₁, p₂, f₂, e₂, hp₁, hp₂, ha₁, ha₂, hL₁, hL₂, -, -, -,
      -, -, -, -, -, -, -, -, hπ₁, hπ₂⟩ := h7
    haveI := hp₁
    exact not_isoLThreePi_of_equiv_J2 (hLJ a₁ L₁ ha₁ hL₁) p₁ (f₁ * e₁) hπ₁

end Item148Binders

section Key


theorem key_case_two {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (hs : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {Y : Subgroup G} (hAY : A ≤ Y)
    (hXN : Y ≤ Subgroup.normalizer
      ((deltaZero A (lB A) Y ⊔ pPrimeCoreOf 3 Y : Subgroup G) : Set G))
    (hX : deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔
        deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)))
    {U : Subgroup G} (hU : IsPGroup p U) (hUX : U ≤ deltaZero A (lB A) Y)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hUA : ⁅U, A⁆ = U) :
    U ≤ pPrimeCoreOf 3 Y := by
  obtain ⟨hJ2, h9, hAc, -, -, -⟩ := hs.j2_local hJ
  have hA : Late.IsE27 A := hs.isE27
  have hA3 : IsPGroup 3 A := hA.isPGroup
  have h3L : 3 ∣ Nat.card L := by
    have h9L := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ L ≤ L)
    rw [h9] at h9L
    exact (show 3 ∣ 9 by norm_num).trans h9L
  have hcA : c ∈ A := hs.c_mem
  have hCL : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    Sec14.centralizer_le_normalizer_of_three_dvd hs.toSec14Std h3L
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hs.mem_lA.2.1
  have hVCA : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
      Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
  have hVL : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤ Subgroup.normalizer (L : Set G) :=
    hVCA.trans ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA)).trans hCL)
  set F := deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) with hF
  have hAF : A ≤ Subgroup.normalizer (F : Set G) :=
    Sec14.le_normalizer_sSup fun Q hQ => hQ.1.1.1.2.2
  have hFK : F ≤ L ⊔ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
    refine sSup_le fun Q hQ => ?_
    exact Sec14.Item148Point.le_sup_of_eq_zpowers_sup142 hs.toSec14Std hAc
      ⟨hQ.2.trans inf_le_right, hQ.1.1.1.2.1, hQ.1.1.1.2.2⟩
  refine key_core (K := L) (N₁ := ⊥) (V := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
    (F := F) hp (by omega) hA3 hAY (deltaZero_le Y) hXN hX hAF hFK hAL hVCA hVL ?_ ?_ ?_ hU hUX
    hAU hUA
  · rw [Subgroup.card_bot]
    exact fun h => absurd (Nat.le_of_dvd one_pos h) (by norm_num)
  · intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl
      simp
    · intro hh
      simpa using hh
  · intro U' hU'p hU'L hAU'
    exact le_bot_iff.mpr (eq_bot_of_le_L hp hp3 hJ2 hA3 h9 hU'p hU'L hAU')

theorem key_case_three (hbal : Step143Balance)
    {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (hs : Sec17Std G A c L Y₀)
    (hΩ : omegaA A = {Subgroup.zpowers c})
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {Y : Subgroup G} (hAY : A ≤ Y)
    (hXN : Y ≤ Subgroup.normalizer
      ((deltaZero A (lB A) Y ⊔ pPrimeCoreOf 3 Y : Subgroup G) : Set G))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d)
    (hX : deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔
        deltaZero A (lB A) (Y ⊓ Subgroup.centralizer ({d} : Set G)))
    {U : Subgroup G} (hU : IsPGroup p U) (hUX : U ≤ deltaZero A (lB A) Y)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hUA : ⁅U, A⁆ = U) :
    U ≤ pPrimeCoreOf 3 Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJ2, h9, hAc, -, -, -⟩ := hs.j2_local hJ
  have h14 : Sec14Std G A c L := hs.toSec14Std
  have hD13 : Sec13Data G A c L := hs.toSec13Data
  have hA : Late.IsE27 A := hs.isE27
  have hA3 : IsPGroup 3 A := hA.isPGroup
  have hcA : c ∈ A := hD13.mem_A
  have hc3 : orderOf c = 3 := hD13.orderOf_eq
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨hcL, -, -⟩ := Sec14.j2_point_facts hD13 hJ
  have h3L : 3 ∣ Nat.card L := by
    have h9L := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ L ≤ L)
    rw [h9] at h9L
    exact (show 3 ∣ 9 by norm_num).trans h9L
  obtain ⟨hdL, -, -, -⟩ := hdc
  set C := Subgroup.centralizer ({d} : Set G) with hCdef
  set N₁ := pPrimeCoreOf 3 C with hN₁def
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'def
  set Ld := inSubgroup perfectResidual (L ⊓ C) with hLddef
  have hdΩ : Subgroup.zpowers d ∉ omegaA A := by
    rw [hΩ, Set.mem_singleton_iff]
    intro hdc
    exact hcL ((Subgroup.zpowers_le.mpr hdL) (hdc ▸ Subgroup.mem_zpowers c))
  have hΔ : delta A (lB A) C ≤ N₁ ⊔ O' ⊔ Ld :=
    Proof17Res9.delta_le_sup_of_lB_le hbal h14 hdA hd1 hdΩ fun D hD hdD =>
      (Proof17Res9.lB_le_ld hΩ hc3 hcL hD13.mem_lA hdL hcA hAcomm hD.1 hdD).trans le_sup_right
  set F := deltaZero A (lB A) (Y ⊓ C) with hF
  have hFΔ : F ≤ delta A (lB A) C :=
    (Sec14.deltaZero_mono inf_le_right).trans (Sec14.deltaZero_le_delta C)
  have hAC : A ≤ C := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm a ha d hdA)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hs.mem_lA.2.1
  have hCN₁ : C ≤ Subgroup.normalizer (N₁ : Set G) := le_normalizer_pPrimeCoreOf 3 C
  have hLdC : Ld ≤ C := (Subgroup.map_subtype_le _).trans inf_le_right
  have hLdL : Ld ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hO'C : O' ≤ C := (pPrimeCoreOf_le 3 _).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdA))
  have hALd : A ≤ Subgroup.normalizer (Ld : Set G) :=
    (Late.le_normalizer_inf hAL (hAC.trans Subgroup.le_normalizer)).trans
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _)
  have hO'Ld : O' ≤ Subgroup.normalizer (Ld : Set G) := by
    have hCAc : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA)
    have hO'L : O' ≤ Subgroup.normalizer (L : Set G) :=
      ((pPrimeCoreOf_le 3 _).trans hCAc).trans
        (Sec14.centralizer_le_normalizer_of_three_dvd h14 h3L)
    exact (Late.le_normalizer_inf hO'L (hO'C.trans Subgroup.le_normalizer)).trans
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _)
  have hAN₁ : A ≤ Subgroup.normalizer (N₁ : Set G) := hAC.trans hCN₁
  have hAF : A ≤ Subgroup.normalizer (F : Set G) :=
    Sec14.le_normalizer_sSup fun Q hQ => hQ.1.1.1.2.2
  refine key_core (K := N₁ ⊔ Ld) (N₁ := N₁) (V := O') (F := F) hp (by omega) hA3 hAY
    (deltaZero_le Y) hXN hX hAF ?_ ?_ ?_ ?_ ?_ ?_ ?_ hU hUX hAU hUA
  ·
    refine (hFΔ.trans hΔ).trans ?_
    rw [sup_right_comm]
  · exact Sec14.le_normalizer_sup hAN₁ hALd
  · exact (pPrimeCoreOf_le 3 _)
  · exact Sec14.le_normalizer_sup (hO'C.trans hCN₁) hO'Ld
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 C)
  · exact ((deltaZero_le (Y ⊓ C)).trans inf_le_right).trans hCN₁
  · intro U' hU'p hU'K hAU'
    obtain ⟨S, hSLd, hSp, hAS, hU'S⟩ := exists_invariant_pSubgroup_le_sup hp (by omega) hA3
      (N := N₁) (T := C) (M := Ld) (U := U') (pPrimeCoreOf_le 3 C) hCN₁
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 C)) hLdC
      hU'p hU'K hAN₁ hALd hAU'
    have hS : S = ⊥ := eq_bot_of_le_L hp hp3 hJ2 hA3 h9 hSp (hSLd.trans hLdL) hAS
    rw [hS, sup_bot_eq] at hU'S
    exact hU'S

end Key

section Final


theorem key_lemma (h148 : Item148R) (hbal : Step143Balance) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (hs : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {Y : Subgroup G} (hY : Y ∈ scriptY A) (hAY : A ≤ Y)
    {U : Subgroup G} (hU : IsPGroup p U) (hUX : U ≤ deltaZero A (lB A) Y)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hUA : ⁅U, A⁆ = U) :
    U ≤ pPrimeCoreOf 3 Y := by
  obtain ⟨hΩ, -, -⟩ := rank3II_17_15_HJ_of hs (h1514 G A c L Y₀ hs) (hMeets G A c L Y₀ hs) hJ
  haveI : (ker148 A Y).Normal := ker148_normal hY.2
  have h148Y := h148 G A c L hs.toSec15R Y hY
  have hn := h148Y.1
  have hcases : Item148Cases A (lB A) Y := h148Y.2
  have hXN := le_normalizer_sup_of_normal_image (deltaZero_le Y) hn
  rcases case148_struct hcases hs.chosen136 hΩ hs.mem_lA hJ with h1 | h2 | ⟨d, hdA, hd1, hdc, h3⟩
  · exact hUX.trans h1
  · exact key_case_two hs hJ hp hp3 hAY hXN h2 hU hUX hAU hUA
  · exact key_case_three hbal hs hΩ hJ hp hp3 hAY hXN hdA hd1 hdc h3 hU hUX hAU hUA

end Final

end CFSG.RankThree.PartTwo.Sec17.F17Leaf

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec17.F17Leaf
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Final


theorem item1724NormThreePrime_of_inputs (h148 : Item148R) (hbal : Step143Balance)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) : Item1724NormThreePrime := by
  intro G _ _ A c L Y₀ Y₁ S p P w Q h hJ D hD hD1 _
  have hs := h.toSec17Std
  have hA : Late.IsE27 A := hs.isE27
  have hA3 : IsPGroup 3 A := hA.isPGroup
  have hp : p.Prime := h.p_prime
  have hp3 : 3 < p := h.three_lt_p
  haveI : Fact p.Prime := ⟨hp⟩
  have hDq : D ∈ scriptQ A (lB A) := hD.1.1
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := (mem_scriptQ_iff.mp hDq).2.1
  have hDp : IsPGroup p D := (isPiSubgroup_piOf_iff hp D).mp hD.2
  have hYtop : Subgroup.normalizer (D : Set G) ≠ ⊤ :=
    normalizer_ne_top_of_simple h.toTheoremFourHyp.isSimpleGroup
      h.toTheoremFourHyp.nonabelian hp hDp hD1
  set Y := Subgroup.normalizer (D : Set G) with hYdef
  have hYY : Y ∈ scriptY A := ⟨hYtop, hAD.trans Subgroup.le_normalizer⟩
  have hAY : A ≤ Y := hAD
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := pPrimeCoreOf 3 Y with hN
  set V := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y with hV
  have hNY : N ≤ Y := pPrimeCoreOf_le 3 Y
  have hYN : Y ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 Y
  have hN3 : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
  have hVxA : V ≤ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := inf_le_left
  have hxA3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hV3 : ¬ 3 ∣ Nat.card V := fun h3 => hxA3 (h3.trans (Subgroup.card_dvd_of_le hVxA))
  have hVC : V ≤ Subgroup.centralizer (A : Set G) := hVxA.trans (pPrimeCoreOf_le 3 _)
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.le_centralizer_iff.mpr hVC).trans (Subgroup.centralizer_le_normalizer _)
  refine ⟨N ⊔ V, sup_le hNY inf_le_right, ?_, ?_, ?_⟩
  · exact Sec14.le_normalizer_sup (hAY.trans hYN) hAV
  · exact not_three_dvd_card_sup (inf_le_right.trans hYN) hN3 hV3
  · intro S' hS'
    obtain ⟨⟨hS'Q, hS'Y⟩, hS'pi⟩ := hS'.1
    have hS'p : IsPGroup p S' := (isPiSubgroup_piOf_iff hp S').mp hS'pi
    have hAS' : A ≤ Subgroup.normalizer (S' : Set G) := (mem_scriptQ_iff.mp hS'Q).2.1
    have hS'3 : ¬ 3 ∣ Nat.card S' := by
      intro h3
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS'p
      rw [hk] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    have hUS' : ⁅S', A⁆ ≤ S' := commutator_le_self hAS'
    have hUp : IsPGroup p (⁅S', A⁆ : Subgroup G) := hS'p.to_le hUS'
    have hAU : A ≤ Subgroup.normalizer ((⁅S', A⁆ : Subgroup G) : Set G) :=
      le_normalizer_commutator hAS'
    have hUA : ⁅(⁅S', A⁆ : Subgroup G), A⁆ = ⁅S', A⁆ := commutator_commutator_eq hA3 hS'3 hAS'
    have hUQ0 : (⁅S', A⁆ : Subgroup G) ∈ scriptQZero A (lB A) :=
      ⟨mem_scriptQ_of_le hS'Q hUS' hAU, hUA.symm⟩
    have hUX : (⁅S', A⁆ : Subgroup G) ≤ deltaZero A (lB A) Y :=
      le_deltaZero hUQ0 (hUS'.trans hS'Y)
    have hUN : ⁅S', A⁆ ≤ N :=
      key_lemma h148 hbal h1514 hMeets hs hJ hp hp3 hYY hAY hUp hUX hAU hUA
    have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three A S' hA3 hS'3 hAS'
    have hCx : S' ⊓ Subgroup.centralizer (A : Set G) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) :=
      inf_centralizer_le_xA (Sec14Std.maximal_isElemAbelian hs.toSec14Std) hS'3
    refine hfac.le.trans (sup_le (hUN.trans le_sup_left) ?_)
    exact (le_inf hCx (inf_le_left.trans hS'Y)).trans le_sup_right


end Final

end CFSG.RankThree.PartTwo.Sec17
