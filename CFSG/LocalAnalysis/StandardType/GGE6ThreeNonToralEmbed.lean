module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Ad
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCubeFrame
public import CFSG.Mathlib.RingTheory.UnitOrderOf
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools
public import CFSG.RankThree.PartOne.K133H.G2Plane

public section

namespace CFSG.StandardType.E6NonToralThree

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.Three TableBExc.E6Three
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3

private abbrev conjE {G : Type*} [Group G] (E : Subgroup G) (g : G) : Subgroup G :=
  E.map (MulAut.conj g).toMonoidHom

private noncomputable abbrev kcard {G : Type*} [Group G] (E T : Subgroup G) (g : G) : ℕ :=
  Nat.card ↥(conjE E g ⊓ T)

private theorem kcard_def {G : Type*} [Group G] (E T : Subgroup G) (g : G) :
    kcard E T g = Nat.card ↥(conjE E g ⊓ T) := rfl

private theorem mem_conjE {G : Type*} [Group G] {E : Subgroup G} {g y : G} :
    y ∈ conjE E g ↔ ∃ x ∈ E, MulAut.conj g x = y := by
  rw [conjE, Subgroup.mem_map]
  exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h⟩⟩

private theorem conjE_conj_mul {G : Type*} [Group G] {E : Subgroup G} (a b : G) :
    conjE E (a * b) = (conjE E b).map (MulAut.conj a).toMonoidHom := by
  ext y
  rw [mem_conjE, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hm : MulAut.conj (a * b) = MulAut.conj a * MulAut.conj b := map_mul _ a b
    refine ⟨MulAut.conj b x, mem_conjE.2 ⟨x, hx, rfl⟩, ?_⟩
    rw [← hxy, hm, MulAut.mul_apply]
    rfl
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨x, hx, rfl⟩ := mem_conjE.1 hz
    have hm : MulAut.conj (a * b) = MulAut.conj a * MulAut.conj b := map_mul _ a b
    refine ⟨x, hx, ?_⟩
    rw [← hzy, hm, MulAut.mul_apply]
    rfl

private theorem kcard_le {G : Type*} [Group G] {E : Subgroup G} [Finite E] (T : Subgroup G)
    (g : G) : kcard E T g ≤ Nat.card E := by
  haveI : Finite ↥(conjE E g) :=
    ((Set.toFinite (E : Set G)).image (MulAut.conj g).toMonoidHom).to_subtype
  rw [kcard_def]
  calc Nat.card ↥(conjE E g ⊓ T) ≤ Nat.card ↥(conjE E g) := Subgroup.card_le_of_le inf_le_left
    _ = Nat.card ↥E := Subgroup.card_map_of_injective (MulAut.conj g).injective

private theorem le_of_conjE_le {G : Type*} [Group G] {E N : Subgroup G} (g : G)
    (h : conjE E g ≤ N) : ∀ x ∈ E, MulAut.conj g x ∈ N := fun x hx =>
  h (mem_conjE.2 ⟨x, hx, rfl⟩)

private theorem conjE_le_of_forall {G : Type*} [Group G] {E N : Subgroup G} (g : G)
    (h : ∀ x ∈ E, MulAut.conj g x ∈ N) : conjE E g ≤ N := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_conjE.1 hy
  exact h x hx

private theorem exists_maximal_monoConj {G : Type*} [Group G] (H E T N : Subgroup G) [Finite E]
    (hne : ∃ c ∈ H, conjE E c ≤ N) :
    ∃ g ∈ H, conjE E g ≤ N ∧
      ∀ g' ∈ H, conjE E g' ≤ N → kcard E T g' ≤ kcard E T g := by
  classical
  have hP : ∃ j, ∃ g ∈ H, conjE E g ≤ N ∧ kcard E T g = Nat.card E - j := by
    obtain ⟨c, hc, hcN⟩ := hne
    exact ⟨Nat.card E - kcard E T c, c, hc, hcN,
      (Nat.sub_sub_self (kcard_le T c)).symm⟩
  obtain ⟨g, hgH, hgN, hgk⟩ := Nat.find_spec hP
  refine ⟨g, hgH, hgN, fun g' hg'H hg'N => ?_⟩
  by_contra hlt
  push Not at hlt
  have hfindle : Nat.find hP ≤ Nat.card E := by
    obtain ⟨c, hc, hcN⟩ := hne
    have h1 : Nat.find hP ≤ Nat.card E - kcard E T c :=
      Nat.find_le (h := hP) ⟨c, hc, hcN, (Nat.sub_sub_self (kcard_le (E := E) T c)).symm⟩
    have b1 := kcard_le (E := E) T c
    omega
  have hj : Nat.card E - kcard E T g' < Nat.find hP := by
    have hj0 : Nat.find hP = Nat.card E - kcard E T g := by omega
    rw [hj0]
    have b1 := kcard_le (E := E) T g
    have b2 := kcard_le (E := E) T g'
    omega
  exact Nat.find_min hP hj
    ⟨g', hg'H, hg'N, (Nat.sub_sub_self (kcard_le (E := E) T g')).symm⟩

private theorem kcard_conj_mul_of_map_conj_eq {G : Type*} [Group G] {E T : Subgroup G}
    {c : G} (hc : T.map (MulAut.conj c).toMonoidHom = T) (g : G) :
    kcard E T (c * g) = kcard E T g := by
  rw [kcard_def, kcard_def, conjE_conj_mul]
  have h : ((conjE E g) ⊓ T).map (MulAut.conj c).toMonoidHom =
      (conjE E g).map (MulAut.conj c).toMonoidHom ⊓ T := by
    rw [Subgroup.map_inf_eq (conjE E g) T ((MulAut.conj c).toMonoidHom)
      (MulAut.conj c).injective, hc]
  rw [← h, Subgroup.card_map_of_injective (MulAut.conj c).injective]

private theorem gE6_zero_eq : gE6 0 = simple .E6 0 * simple .E6 2 := by
  have h0 : wordE6G 0 = wordE6G0 := rfl
  rw [gE6, h0, wordE6G0, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_nil, mul_one]

private theorem cE6_pow_conj_gE6 (i : Fin 3) :
    cE6 ^ (i : ℕ) * gE6 0 * (cE6 ^ (i : ℕ))⁻¹ = gE6 i := by
  fin_cases i
  · show cE6 ^ (0 : ℕ) * gE6 0 * (cE6 ^ (0 : ℕ))⁻¹ = gE6 ⟨0, by decide⟩
    simp
  · show cE6 ^ (1 : ℕ) * gE6 0 * (cE6 ^ (1 : ℕ))⁻¹ = gE6 ⟨1, by decide⟩
    rw [pow_one]
    have h := cE6_conj (0 : Fin 3)
    rw [show piE7 0 = (1 : Fin 3) from by decide] at h
    exact h
  · show cE6 ^ (2 : ℕ) * gE6 0 * (cE6 ^ (2 : ℕ))⁻¹ = gE6 ⟨2, by decide⟩
    rw [pow_two, mul_inv_rev]
    calc cE6 * cE6 * gE6 0 * (cE6⁻¹ * cE6⁻¹)
        = cE6 * (cE6 * gE6 0 * cE6⁻¹) * cE6⁻¹ := by group
      _ = cE6 * gE6 (piE7 0) * cE6⁻¹ := by rw [cE6_conj 0]
      _ = gE6 2 := by
          rw [show piE7 0 = (1 : Fin 3) from by decide]
          have h := cE6_conj (1 : Fin 3)
          rw [show piE7 1 = (2 : Fin 3) from by decide] at h
          exact h

private theorem gE6_ne_one (i : Fin 3) : gE6 i ≠ 1 := by
  intro h
  have hmove := (testE6_move i).1
  rw [h, one_smul] at hmove
  exact hmove rfl

private theorem adWord_gE6_zero_eq_self {y : Fin Tag.E6.rank → ZMod 3}
    (hy : adWord .E6 3 wordE6G0 y = y) : y 0 = 0 ∧ y 2 = 0 := by
  revert y
  decide +kernel

private theorem not_three_dvd_index_modelHomE6 :
    ¬ 3 ∣ (modelHomE6.range).index := by
  have hcard := Subgroup.card_mul_index modelHomE6.range
  rw [card_range_modelHomE6, NoOffExc.card_weyl_E6] at hcard
  have h : (modelHomE6.range).index = 640 := by omega
  rw [h]
  decide

private theorem exists_conj_le_modelHomE6
    {A : Subgroup (WeylGroup .E6)}
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) :
    ∃ w, A.map (MulAut.conj w).toMonoidHom ≤ modelHomE6.range := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 A := by
    rw [IsPGroup.iff_orderOf]
    intro a
    have hA3' : (a : WeylGroup .E6) ^ 3 = 1 := hA3 a.1 a.2
    have hdvd : orderOf a ∣ 3 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_iff_pow_eq_one.2 hA3'
    obtain ⟨k, -, hk⟩ :=
      (Nat.dvd_prime_pow (p := 3) (m := 1) Nat.prime_three).1 (by simpa using hdvd)
    exact ⟨k, hk⟩
  exact TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three
    not_three_dvd_index_modelHomE6 hP

private theorem adAct_gE6_zero_fix {i : Fin 3} {x : Fin Tag.E6.rank → ZMod 3}
    (hx : adAct .E6 3 (gE6 i) x = x) :
    adAct .E6 3 (gE6 0) (adAct .E6 3 (cE6 ^ (i : ℕ))⁻¹ x) =
        adAct .E6 3 (cE6 ^ (i : ℕ))⁻¹ x ∧
      (adAct .E6 3 (cE6 ^ (i : ℕ))⁻¹ x) 0 = 0 ∧
      (adAct .E6 3 (cE6 ^ (i : ℕ))⁻¹ x) 2 = 0 := by
  let y : Fin Tag.E6.rank → ZMod 3 := adAct .E6 3 (cE6 ^ (i : ℕ))⁻¹ x
  have hwy : adAct .E6 3 (cE6 ^ (i : ℕ)) y = x := by
    change adAct .E6 3 (cE6 ^ (i : ℕ)) (adAct .E6 3 (cE6 ^ (i : ℕ))⁻¹ x) = x
    rw [← adAct_mul, mul_inv_cancel, adAct_one]
  have hxfix0 : adAct .E6 3 (gE6 0) y = y := by
    have hw : (cE6 ^ (i : ℕ))⁻¹ * gE6 i * (cE6 ^ (i : ℕ)) = gE6 0 := by
      rw [← cE6_pow_conj_gE6 i]
      group
    calc adAct .E6 3 (gE6 0) y
        = adAct .E6 3 ((cE6 ^ (i : ℕ))⁻¹ * gE6 i * (cE6 ^ (i : ℕ))) y := by rw [hw]
      _ = adAct .E6 3 ((cE6 ^ (i : ℕ))⁻¹) (adAct .E6 3 (gE6 i)
            (adAct .E6 3 (cE6 ^ (i : ℕ)) y)) := by rw [adAct_mul, adAct_mul]
      _ = adAct .E6 3 ((cE6 ^ (i : ℕ))⁻¹) (adAct .E6 3 (gE6 i) x) := by rw [hwy]
      _ = adAct .E6 3 ((cE6 ^ (i : ℕ))⁻¹) x := by rw [hx]
      _ = y := rfl
  have hF1 : y 0 = 0 ∧ y 2 = 0 := by
    apply adWord_gE6_zero_eq_self
    rw [adWord_eq_adAct]
    simpa [gE6, wordE6G] using hxfix0
  exact ⟨hxfix0, hF1⟩

private theorem rootChar_gE6_smul_single
    {L : Type} [Field L] {u : Fin Tag.E6.rank → Lˣ}
    {n : ModGL .E6 L} (hnN : n ∈ monomialSubgroup .E6 L) {i : Fin 3}
    (hweyl : weylQuotientHom .E6 L ⟨n, hnN⟩ = gE6 i)
    (hcomm : rootDiagUnit .E6 u * n = n * rootDiagUnit .E6 u)
    (hpow : u ^ 3 = 1) {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {j : Fin Tag.E6.rank} (hj : j = 0 ∨ j = 2) :
    rootChar u ((cE6 ^ (i : ℕ)) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = 1 := by
  have hwt : weylTuple (gE6 i) u = u := by
    have hconj := monomial_conj_rootDiagUnit_weylTuple (K := L) hnN
      (mapsRootLines_weylQuotientHom ⟨n, hnN⟩) u
    rw [hweyl] at hconj
    have hdn : n * rootDiagUnit .E6 u * n⁻¹ = rootDiagUnit .E6 u := by
      rw [← hcomm, mul_inv_cancel_right]
    rw [hdn] at hconj
    exact (CFSG.LieType.Chevalley.rootDiagUnit_injective hconj).symm
  obtain ⟨x, hx⟩ := exists_zetaVec_eq (τ := .E6) (p := 3) hζo hζ hpow
  rw [← hx] at hwt
  rw [weylTuple_zetaVec] at hwt
  have hxfix : adAct .E6 3 (gE6 i) x = x := zetaVec_injective hζo hζ hwt
  let y : Fin Tag.E6.rank → ZMod 3 := adAct .E6 3 (cE6 ^ (i : ℕ))⁻¹ x
  have hwy : adAct .E6 3 (cE6 ^ (i : ℕ)) y = x := by
    change adAct .E6 3 (cE6 ^ (i : ℕ)) (adAct .E6 3 (cE6 ^ (i : ℕ))⁻¹ x) = x
    rw [← adAct_mul, mul_inv_cancel, adAct_one]
  have hF1 : y 0 = 0 ∧ y 2 = 0 := by
    simpa only [y] using (adAct_gE6_zero_fix hxfix).2
  rw [← hx]
  have hxeq : zetaVec ζ hζ x = weylTuple (cE6 ^ (i : ℕ)) (zetaVec ζ hζ y) := by
    rw [weylTuple_zetaVec, ← hwy]
  rw [hxeq, rootChar_weylTuple, inv_smul_smul]
  have hlast : rootChar (zetaVec ζ hζ y) (Pi.single j 1) =
      (zetaVec ζ hζ y j) ^ 1 := by
    simpa using rootChar_nsmul_single (zetaVec ζ hζ y) j 1
  rw [hlast, zetaVec_apply, pow_one]
  rcases hj with rfl | rfl
  · rw [hF1.1]
    simp
  · rw [hF1.2]
    simp

private theorem gE6_mem_kernelWeylGroup_of_comm
    {L : Type} [Field L] {ι : Type} (a : ι → Fin Tag.E6.rank → Lˣ)
    {n : ModGL .E6 L} (hnN : n ∈ monomialSubgroup .E6 L) {i : Fin 3}
    (hweyl : weylQuotientHom .E6 L ⟨n, hnN⟩ = gE6 i)
    (hcomm : ∀ t, rootDiagUnit .E6 (a t) * n = n * rootDiagUnit .E6 (a t))
    (hpow : ∀ t, a t ^ 3 = 1) {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    gE6 i ∈ kernelWeylGroup (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a) := by
  have key : ∀ t (j : Fin Tag.E6.rank), j = 0 ∨ j = 2 →
      rootChar (a t) ((cE6 ^ (i : ℕ)) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = 1 :=
    fun t j hj => rootChar_gE6_smul_single (u := a t) hnN hweyl (hcomm t) (hpow t) hζo hζ hj
  have hroot : ∀ j : Fin Tag.E6.rank, j = 0 ∨ j = 2 →
      ((cE6 ^ (i : ℕ)) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) ∈
        kernelRoots (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a) := by
    intro j hj
    refine ⟨IsRoot.smul (isRoot_single .E6 j) _, ?_⟩
    funext t
    change rootChar (a t) ((cE6 ^ (i : ℕ)) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = 1
    exact key t j hj
  have hgen : ∀ j : Fin Tag.E6.rank, j = 0 ∨ j = 2 →
      (cE6 ^ (i : ℕ)) * simple .E6 j * (cE6 ^ (i : ℕ))⁻¹ ∈
        kernelWeylGroup (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a) :=
    fun j hj => Subgroup.subset_closure ⟨cE6 ^ (i : ℕ), j, hroot j hj, rfl⟩
  have hprod : (cE6 ^ (i : ℕ)) * simple .E6 0 * (cE6 ^ (i : ℕ))⁻¹ *
      ((cE6 ^ (i : ℕ)) * simple .E6 2 * (cE6 ^ (i : ℕ))⁻¹) ∈
        kernelWeylGroup (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a) :=
    mul_mem (hgen 0 (Or.inl rfl)) (hgen 2 (Or.inr rfl))
  have heq : gE6 i = (cE6 ^ (i : ℕ)) * simple .E6 0 * (cE6 ^ (i : ℕ))⁻¹ *
      ((cE6 ^ (i : ℕ)) * simple .E6 2 * (cE6 ^ (i : ℕ))⁻¹) := by
    rw [← cE6_pow_conj_gE6 i, gE6_zero_eq]
    group
  rwa [heq]

private theorem exists_cube_root_unit {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓ : ℓ ≠ 3) [CharP L ℓ] : ∃ ζ : Lˣ, orderOf ζ = 3 := by
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    intro h
    have hdvd : ℓ ∣ 3 := (CharP.cast_eq_zero_iff L ℓ 3).1 h
    have hle : ℓ ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have h2 : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
    interval_cases ℓ
    · norm_num at hdvd
    · exact hℓ rfl
  exact CFSG.exists_unit_orderOf_eq_of_isAlgClosed h3L

private theorem conjE_pow_eq_one {G : Type*} [Group G] {E : Subgroup G} {g : G} {p : ℕ}
    (hexp : ∀ x ∈ E, x ^ p = 1) : ∀ u ∈ conjE E g, u ^ p = 1 := by
  intro u hu
  obtain ⟨x, hx, rfl⟩ := mem_conjE.1 hu
  calc MulAut.conj g x ^ p = MulAut.conj g (x ^ p) := (map_pow _ _ _).symm
    _ = 1 := by rw [hexp x hx, map_one]

private theorem conjE_comm {G : Type*} [Group G] {E : Subgroup G} {g : G}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∀ u ∈ conjE E g, ∀ v ∈ conjE E g, u * v = v * u := by
  intro u hu v hv
  obtain ⟨x, hx, rfl⟩ := mem_conjE.1 hu
  obtain ⟨y, hy, rfl⟩ := mem_conjE.1 hv
  rw [← map_mul, ← map_mul, hcomm x hx y hy]

private theorem exists_rootDiag_family
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    {g : ModGL .E6 L} (hpow : ∀ u ∈ conjE E g, u ^ 3 = 1) :
    ∃ a : ↥(conjE E g ⊓ torusGroup .E6 L) → Fin Tag.E6.rank → Lˣ,
      (∀ d, rootDiagUnit .E6 (a d) = (d : ModGL .E6 L)) ∧
        ∀ d, a d ^ 3 = 1 := by
  let a : ↥(conjE E g ⊓ torusGroup .E6 L) → Fin Tag.E6.rank → Lˣ := fun d =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (τ := .E6) (K := L) d.2.2).choose
  have ha : ∀ d : ↥(conjE E g ⊓ torusGroup .E6 L),
      rootDiagUnit .E6 (a d) = (d : ModGL .E6 L) := fun d =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (τ := .E6) (K := L) d.2.2).choose_spec.symm
  refine ⟨a, ha, fun d => ?_⟩
  apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := .E6) (K := L)
  rw [← rootDiagUnit_pow, ha d, rootDiagUnit_one]
  exact hpow _ d.2.1

private theorem exists_toral_conj
    {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 3) [CharP L ℓ]
    {E : Subgroup (ModGL .E6 L)} (hEab : IsElemAbelian 3 E)
    {g : ModGL .E6 L}
    {y : ModGL .E6 L} (hyEgg : y ∈ conjE E g)
    (hyN : y ∈ monomialSubgroup .E6 L) {i : Fin 3}
    (hweyl : weylQuotientHom .E6 L ⟨y, hyN⟩ = gE6 i) :
    ∃ (a : ↥(conjE E g ⊓ torusGroup .E6 L) → Fin Tag.E6.rank → Lˣ)
      (h : ModGL .E6 L),
      (∀ d, rootDiagUnit .E6 (a d) = (d : ModGL .E6 L)) ∧
        h ∈ adjointGroup .E6 L ∧
        (∀ d, rootDiagUnit .E6 (a d) * h = h * rootDiagUnit .E6 (a d)) ∧
        h * y * h⁻¹ ∈ torusGroup .E6 L := by
  obtain ⟨ζ, hζo⟩ := exists_cube_root_unit (L := L) hℓ
  have hζ : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hEgg3 : ∀ u ∈ conjE E g, u ^ 3 = 1 :=
    conjE_pow_eq_one fun x hx => hEab.2 x hx
  have hEggComm : ∀ u ∈ conjE E g, ∀ v ∈ conjE E g, u * v = v * u :=
    conjE_comm fun x hx y hy => CFSG.Open.IsElemAbelian.comm hEab hx hy
  obtain ⟨a, ha, hpow⟩ := exists_rootDiag_family hEgg3
  have hcomm_root : ∀ d, rootDiagUnit .E6 (a d) * y = y * rootDiagUnit .E6 (a d) :=
    fun d => by rw [ha d]; exact hEggComm _ d.2.1 _ hyEgg
  have hker : weylQuotientHom .E6 L ⟨y, hyN⟩ ∈ kernelWeylGroup
      (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a) := by
    rw [hweyl]
    exact gE6_mem_kernelWeylGroup_of_comm a hyN hweyl hcomm_root hpow hζo hζ
  have hL3 : ringChar L ≠ 3 := by rw [ringChar.eq L ℓ]; exact hℓ
  obtain ⟨h, hhG, hhcomm, hhyT⟩ :=
    exists_conj_mem_torusGroup_of_weyl_mem_kernel (p := 3) (a := a)
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.monomialToralAt_E6_three)
      hL3 hyN (hEgg3 y hyEgg) hker
  exact ⟨a, h, ha, hhG, hhcomm, hhyT⟩

private theorem family_option_comm
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    {g y h : ModGL .E6 L} {a : ↥(conjE E g ⊓ torusGroup .E6 L) → Fin Tag.E6.rank → Lˣ}
    {b : Fin Tag.E6.rank → Lˣ}
    (hcommE : ∀ u ∈ conjE E g, ∀ v ∈ conjE E g, u * v = v * u)
    (hyEgg : y ∈ conjE E g) (hb : rootDiagUnit .E6 b = h * y * h⁻¹)
    (ha : ∀ d, rootDiagUnit .E6 (a d) = (d : ModGL .E6 L))
    (hhcomm : ∀ d, rootDiagUnit .E6 (a d) * h = h * rootDiagUnit .E6 (a d)) :
    ∀ x ∈ conjE (conjE E g) h, ∀ t : Option ↥(conjE E g ⊓ torusGroup .E6 L),
      rootDiagUnit .E6 (t.elim b a) * x = x * rootDiagUnit .E6 (t.elim b a) := by
  intro x hx t
  obtain ⟨u, hu, rfl⟩ := mem_conjE.1 hx
  cases t with
  | none =>
    rw [show (Option.none : Option ↥(conjE E g ⊓ torusGroup .E6 L)).elim b a = b from rfl, hb]
    exact Commute.conj (hcommE y hyEgg u hu) h
  | some d =>
    have hd : rootDiagUnit .E6 ((Option.some d).elim b a) = (d : ModGL .E6 L) := by
      rw [show (Option.some d).elim b a = a d from rfl, ha d]
    have hhd : h * (d : ModGL .E6 L) * h⁻¹ = (d : ModGL .E6 L) := by
      have hh := hhcomm d
      rw [ha d] at hh
      rw [← hh, mul_inv_cancel_right]
    rw [hd]
    have hcomm' : (h * (d : ModGL .E6 L) * h⁻¹) * (h * u * h⁻¹) =
        (h * u * h⁻¹) * (h * (d : ModGL .E6 L) * h⁻¹) :=
      Commute.conj (hcommE (d : ModGL .E6 L) d.2.1 u hu) h
    rw [hhd] at hcomm'
    exact hcomm'

private theorem conjE_conjE_le_finite_exponent
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)} {g : ModGL .E6 L}
    (hEfin : (E : Set (ModGL .E6 L)).Finite)
    (hgN : conjE E g ≤ monomialSubgroup .E6 L)
    (hpow : ∀ u ∈ conjE E g, u ^ 3 = 1) {h : ModGL .E6 L}
    (hhG : h ∈ adjointGroup .E6 L) :
    conjE (conjE E g) h ≤ adjointGroup .E6 L ∧
      (conjE (conjE E g) h : Set (ModGL .E6 L)).Finite ∧
      ∀ x ∈ conjE (conjE E g) h, x ^ 3 = 1 := by
  have hEggFin : (conjE E g : Set (ModGL .E6 L)).Finite := by
    rw [conjE]
    exact hEfin.image _
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := mem_conjE.1 hx
    exact mul_mem (mul_mem hhG (monomialSubgroup_le_adjointGroup' (hgN hu)))
      (inv_mem hhG)
  · rw [show (conjE (conjE E g) h : Set (ModGL .E6 L)) =
      (MulAut.conj h).toMonoidHom '' (conjE E g : Set (ModGL .E6 L)) from rfl]
    exact hEggFin.image _
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := mem_conjE.1 hx
    calc MulAut.conj h u ^ 3 = MulAut.conj h (u ^ 3) := (map_pow _ _ _).symm
      _ = 1 := by rw [hpow u hu, map_one]

private theorem exists_family_conjugator
    {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 3) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {E : Subgroup (ModGL .E6 L)} {g h : ModGL .E6 L}
    {a : ↥(conjE E g ⊓ torusGroup .E6 L) → Fin Tag.E6.rank → Lˣ}
    {b : Fin Tag.E6.rank → Lˣ}
    [Fintype ↥(conjE E g ⊓ torusGroup .E6 L)]
    (hBG : conjE (conjE E g) h ≤ adjointGroup .E6 L)
    (hBfin : (conjE (conjE E g) h : Set (ModGL .E6 L)).Finite)
    (hBexp : ∀ x ∈ conjE (conjE E g) h, x ^ 3 = 1)
    (hBcomm : ∀ x ∈ conjE (conjE E g) h, ∀ t : Option ↥(conjE E g ⊓ torusGroup .E6 L),
      rootDiagUnit .E6 (t.elim b a) * x = x * rootDiagUnit .E6 (t.elim b a)) :
    ∃ z ∈ adjointGroup .E6 L,
      (∀ t : Option ↥(conjE E g ⊓ torusGroup .E6 L),
        rootDiagUnit .E6 (t.elim b a) * z = z * rootDiagUnit .E6 (t.elim b a)) ∧
      ∀ x ∈ conjE (conjE E g) h, z * x * z⁻¹ ∈ monomialSubgroup .E6 L :=
  exists_conj_le_monomial_familyCentralizer_bar (τ := .E6) (p := 3) hℓ halg
    (a := fun t : Option ↥(conjE E g ⊓ torusGroup .E6 L) => t.elim b a) hBG hBfin hBcomm hBexp

private theorem conj_notMem_conjE_inf_torusGroup
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)} {g y h : ModGL .E6 L} {i : Fin 3}
    {a : ↥(conjE E g ⊓ torusGroup .E6 L) → Fin Tag.E6.rank → Lˣ}
    (hyN : y ∈ monomialSubgroup .E6 L)
    (hweyl : weylQuotientHom .E6 L ⟨y, hyN⟩ = gE6 i)
    (ha : ∀ d, rootDiagUnit .E6 (a d) = (d : ModGL .E6 L))
    (hhcomm : ∀ d, rootDiagUnit .E6 (a d) * h = h * rootDiagUnit .E6 (a d))
    (hnhT : h * y * h⁻¹ ∈ torusGroup .E6 L) :
    h * y * h⁻¹ ∉ conjE E g ⊓ torusGroup .E6 L := by
  intro hd
  have hcomm_h : h * (h * y * h⁻¹) = (h * y * h⁻¹) * h := by
    have hh := hhcomm ⟨_, hd⟩
    rw [ha ⟨_, hd⟩] at hh
    exact hh.symm
  have hy_eq : y = h * y * h⁻¹ := by
    calc y = h⁻¹ * (h * y * h⁻¹) * h := by group
      _ = h * y * h⁻¹ := by
        have h2 : (h * y * h⁻¹) * h = h * (h * y * h⁻¹) := hcomm_h.symm
        calc h⁻¹ * (h * y * h⁻¹) * h = h⁻¹ * ((h * y * h⁻¹) * h) := by group
          _ = h⁻¹ * (h * (h * y * h⁻¹)) := by rw [h2]
          _ = h * y * h⁻¹ := by group
  have hyT : y ∈ torusGroup .E6 L := by rw [hy_eq]; exact hnhT
  have hyk : (⟨y, hyN⟩ : monomialSubgroup .E6 L) ∈ (weylQuotientHom .E6 L).ker := by
    rw [(CFSG.StandardType.TableBExc.weylQuotientHom_surjective_ker (τ := .E6) (K := L)).2,
      Subgroup.mem_subgroupOf]
    exact hyT
  rw [MonoidHom.mem_ker] at hyk
  rw [hweyl] at hyk
  exact gE6_ne_one i hyk

private theorem conjE_inf_torusGroup_lt
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)} {g y h z : ModGL .E6 L}
    (hyEgg : y ∈ conjE E g)
    (hzD : ∀ d ∈ conjE E g ⊓ torusGroup .E6 L, z * d * z⁻¹ = d)
    (hhD : ∀ d ∈ conjE E g ⊓ torusGroup .E6 L, h * d * h⁻¹ = d)
    (hzhnh : z * (h * y * h⁻¹) * z⁻¹ = h * y * h⁻¹)
    (hnhT : h * y * h⁻¹ ∈ torusGroup .E6 L)
    (hnh_notD : h * y * h⁻¹ ∉ conjE E g ⊓ torusGroup .E6 L) :
    conjE E g ⊓ torusGroup .E6 L <
      conjE E (z * h * g) ⊓ torusGroup .E6 L := by
  have hDle : conjE E g ⊓ torusGroup .E6 L ≤
      conjE E (z * h * g) ⊓ torusGroup .E6 L := by
    intro d hd
    refine ⟨?_, hd.2⟩
    obtain ⟨x, hx, hxd⟩ := mem_conjE.1 hd.1
    rw [MulAut.conj_apply] at hxd
    refine mem_conjE.2 ⟨x, hx, ?_⟩
    rw [MulAut.conj_apply]
    calc (z * h * g) * x * (z * h * g)⁻¹
        = z * (h * (g * x * g⁻¹) * h⁻¹) * z⁻¹ := by group
      _ = z * (h * (d : ModGL .E6 L) * h⁻¹) * z⁻¹ := by rw [hxd]
      _ = z * (d : ModGL .E6 L) * z⁻¹ := by rw [hhD d hd]
      _ = (d : ModGL .E6 L) := hzD d hd
  have hnhI : h * y * h⁻¹ ∈ conjE E (z * h * g) ⊓ torusGroup .E6 L := by
    refine ⟨?_, hnhT⟩
    obtain ⟨x, hx, hxy⟩ := mem_conjE.1 hyEgg
    rw [MulAut.conj_apply] at hxy
    refine mem_conjE.2 ⟨x, hx, ?_⟩
    rw [MulAut.conj_apply]
    calc (z * h * g) * x * (z * h * g)⁻¹
        = z * (h * (g * x * g⁻¹) * h⁻¹) * z⁻¹ := by group
      _ = z * (h * y * h⁻¹) * z⁻¹ := by rw [hxy]
      _ = h * y * h⁻¹ := hzhnh
  exact lt_of_le_of_ne hDle (fun heq => hnh_notD (heq ▸ hnhI))

private theorem mul_mul_mem_and_conjE_le_monomialSubgroup
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    {g h z : ModGL .E6 L}
    (hzG : z ∈ adjointGroup .E6 L) (hhG : h ∈ adjointGroup .E6 L)
    (hgG : g ∈ adjointGroup .E6 L)
    (hzB : ∀ x ∈ conjE (conjE E g) h, z * x * z⁻¹ ∈ monomialSubgroup .E6 L) :
    z * h * g ∈ adjointGroup .E6 L ∧
      conjE E (z * h * g) ≤ monomialSubgroup .E6 L := by
  have hmap : conjE E (z * h * g) =
      (conjE (conjE E g) h).map (MulAut.conj z).toMonoidHom := by
    rw [show z * h * g = (z * h) * g from by group, conjE_conj_mul]
    change conjE (conjE E g) (z * h) = (conjE (conjE E g) h).map _
    rw [conjE_conj_mul (E := conjE E g) (a := z) (b := h)]
  refine ⟨mul_mem (mul_mem hzG hhG) hgG, ?_⟩
  rw [hmap]
  intro w hw
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hw
  exact hzB u hu

private theorem exists_z_of_maximal
    {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 3) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {E : Subgroup (ModGL .E6 L)} (hEfin : (E : Set (ModGL .E6 L)).Finite)
    (hEab : IsElemAbelian 3 E) {g : ModGL .E6 L}
    (hgN : conjE E g ≤ monomialSubgroup .E6 L)
    {y : ModGL .E6 L} (hyEgg : y ∈ conjE E g)
    (hyN : y ∈ monomialSubgroup .E6 L) {i : Fin 3}
    (hweyl : weylQuotientHom .E6 L ⟨y, hyN⟩ = gE6 i) :
    ∃ (a : ↥(conjE E g ⊓ torusGroup .E6 L) → Fin Tag.E6.rank → Lˣ)
      (h z : ModGL .E6 L),
      (∀ d, rootDiagUnit .E6 (a d) = (d : ModGL .E6 L)) ∧
        h ∈ adjointGroup .E6 L ∧
        (∀ d, rootDiagUnit .E6 (a d) * h = h * rootDiagUnit .E6 (a d)) ∧
        h * y * h⁻¹ ∈ torusGroup .E6 L ∧
        (∀ d ∈ conjE E g ⊓ torusGroup .E6 L, h * d * h⁻¹ = d) ∧
        z ∈ adjointGroup .E6 L ∧
        (∀ d ∈ conjE E g ⊓ torusGroup .E6 L, z * d * z⁻¹ = d) ∧
        z * (h * y * h⁻¹) * z⁻¹ = h * y * h⁻¹ ∧
        (∀ x ∈ conjE (conjE E g) h, z * x * z⁻¹ ∈ monomialSubgroup .E6 L) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥(conjE E g ⊓ torusGroup .E6 L) :=
    ((hEfin.image (MulAut.conj g).toMonoidHom).subset (fun x hx => hx.1)).to_subtype
  letI : Fintype ↥(conjE E g ⊓ torusGroup .E6 L) :=
    Fintype.ofFinite ↥(conjE E g ⊓ torusGroup .E6 L)
  obtain ⟨a, h, ha, hhG, hhcomm, hhyT⟩ :=
    exists_toral_conj hℓ hEab hyEgg hyN hweyl
  have hhD : ∀ d ∈ conjE E g ⊓ torusGroup .E6 L, h * d * h⁻¹ = d := by
    intro d hd
    have hh := hhcomm ⟨d, hd⟩
    rw [ha ⟨d, hd⟩] at hh
    rw [← hh, mul_inv_cancel_right]
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhyT
  have hEgg3 : ∀ u ∈ conjE E g, u ^ 3 = 1 :=
    conjE_pow_eq_one fun x hx => hEab.2 x hx
  have hBcomm := family_option_comm (hyEgg := hyEgg)
    (conjE_comm fun x hx y hy => CFSG.Open.IsElemAbelian.comm hEab hx hy) hb.symm ha hhcomm
  obtain ⟨hBG, hBfin, hBexp⟩ := conjE_conjE_le_finite_exponent hEfin hgN hEgg3 hhG
  obtain ⟨z, hzG, hzcomm, hzB⟩ :=
    exists_family_conjugator (L := L) hℓ halg hBG hBfin hBexp hBcomm
  have hzD : ∀ d ∈ conjE E g ⊓ torusGroup .E6 L, z * d * z⁻¹ = d := by
    intro d hd
    have hc := hzcomm (some ⟨d, hd⟩)
    rw [show (Option.some ⟨d, hd⟩).elim b a = a ⟨d, hd⟩ from rfl, ha ⟨d, hd⟩] at hc
    rw [← hc, mul_inv_cancel_right]
  have hzhnh : z * (h * y * h⁻¹) * z⁻¹ = h * y * h⁻¹ := by
    have hc := hzcomm none
    rw [show (Option.none : Option ↥(conjE E g ⊓ torusGroup .E6 L)).elim b a = b from rfl,
      ← hb] at hc
    rw [← hc, mul_inv_cancel_right]
  exact ⟨a, h, z, ha, hhG, hhcomm, hhyT, hhD, hzG, hzD, hzhnh, hzB⟩

private theorem no_gE6_of_maximal
    {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 3) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {E : Subgroup (ModGL .E6 L)} (hEfin : (E : Set (ModGL .E6 L)).Finite)
    (hEab : IsElemAbelian 3 E) {g : ModGL .E6 L} (hgG : g ∈ adjointGroup .E6 L)
    (hgN : conjE E g ≤ monomialSubgroup .E6 L)
    (hgmax : ∀ g' ∈ adjointGroup .E6 L, conjE E g' ≤ monomialSubgroup .E6 L →
      kcard E (torusGroup .E6 L) g' ≤ kcard E (torusGroup .E6 L) g)
    {y : ModGL .E6 L} (hyEgg : y ∈ conjE E g)
    (hyN : y ∈ monomialSubgroup .E6 L) (i : Fin 3) :
    weylQuotientHom .E6 L ⟨y, hyN⟩ ≠ gE6 i := by
  classical
  intro hweyl
  obtain ⟨a, h, z, ha, hhG, hhcomm, hhyT, hhD, hzG, hzD, hzhnh, hzB⟩ :=
    exists_z_of_maximal hℓ halg hEfin hEab hgN hyEgg hyN hweyl
  have hDlt := conjE_inf_torusGroup_lt hyEgg hzD hhD hzhnh hhyT
      (conj_notMem_conjE_inf_torusGroup hyN hweyl ha hhcomm hhyT)
  obtain ⟨hzhgG, hzhgN⟩ := mul_mul_mem_and_conjE_le_monomialSubgroup hzG hhG hgG hzB
  haveI : Finite ↥(conjE E (z * h * g) ⊓ torusGroup .E6 L) :=
    ((hEfin.image (MulAut.conj (z * h * g)).toMonoidHom).subset
      (fun x hx => hx.1)).to_subtype
  have hcardlt : Nat.card ↥(conjE E g ⊓ torusGroup .E6 L) <
      Nat.card ↥(conjE E (z * h * g) ⊓ torusGroup .E6 L) :=
    Subgroup.card_lt_of_lt hDlt
  have hmax := hgmax (z * h * g) hzhgG hzhgN
  rw [kcard_def, kcard_def] at hmax
  exact absurd hcardlt (not_lt.mpr hmax)

private theorem weylImage_pow_three
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)} {g : ModGL .E6 L}
    (hgN : conjE E g ≤ monomialSubgroup .E6 L) (hexp : ∀ x ∈ E, x ^ 3 = 1) :
    ∀ a ∈ ((weylQuotientHom .E6 L).comp (Subgroup.inclusion hgN)).range, a ^ 3 = 1 := by
  rintro a ⟨e, he⟩
  rw [← he]
  have he3 : ((e : ModGL .E6 L)) ^ 3 = 1 := by
    obtain ⟨x, hx, hxe⟩ := mem_conjE.1 e.2
    rw [← hxe]
    calc MulAut.conj g x ^ 3 = MulAut.conj g (x ^ 3) := (map_pow _ _ _).symm
      _ = 1 := by rw [hexp x hx, map_one]
  have he3' : e ^ 3 = 1 := Subtype.ext (by simpa using he3)
  calc (((weylQuotientHom .E6 L).comp (Subgroup.inclusion hgN)) e) ^ 3
      = ((weylQuotientHom .E6 L).comp (Subgroup.inclusion hgN)) (e ^ 3) :=
        (map_pow _ e 3).symm
    _ = 1 := by rw [he3', map_one]

private theorem weylImage_canonicalRep_mem_range
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)} {g : ModGL .E6 L}
    {w : WeylGroup .E6}
    (hgN : conjE E g ≤ monomialSubgroup .E6 L)
    (hwS : (((weylQuotientHom .E6 L).comp (Subgroup.inclusion hgN)).range.map
      (MulAut.conj w).toMonoidHom) ≤ modelHomE6.range) :
    ∀ e ∈ conjE E (canonicalRep (coxeterSystem .E6) L w * g),
      ∀ he : e ∈ monomialSubgroup .E6 L,
        weylQuotientHom .E6 L ⟨e, he⟩ ∈ modelHomE6.range := by
  intro e he heN
  rw [conjE_conj_mul] at he
  obtain ⟨u, hu, hcu⟩ := Subgroup.mem_map.1 he
  subst e
  have hcw : canonicalRep (coxeterSystem .E6) L w ∈ monomialSubgroup .E6 L :=
    canonicalRep_mem_monomialSubgroup L w
  have hmemA : weylQuotientHom .E6 L ⟨u, hgN hu⟩ ∈
      ((weylQuotientHom .E6 L).comp (Subgroup.inclusion hgN)).range := ⟨⟨u, hu⟩, rfl⟩
  have hconj : MulAut.conj w (weylQuotientHom .E6 L ⟨u, hgN hu⟩) ∈
      modelHomE6.range :=
    hwS (Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom hmemA)
  have e1 : (⟨canonicalRep (coxeterSystem .E6) L w * u *
        (canonicalRep (coxeterSystem .E6) L w)⁻¹, heN⟩ : monomialSubgroup .E6 L) =
      ⟨canonicalRep (coxeterSystem .E6) L w, hcw⟩ * ⟨u, hgN hu⟩ *
        ⟨(canonicalRep (coxeterSystem .E6) L w)⁻¹, inv_mem hcw⟩ := rfl
  have e2 : (⟨(canonicalRep (coxeterSystem .E6) L w)⁻¹, inv_mem hcw⟩ :
        monomialSubgroup .E6 L) = (⟨canonicalRep (coxeterSystem .E6) L w, hcw⟩ :
        monomialSubgroup .E6 L)⁻¹ := rfl
  change weylQuotientHom .E6 L
    ⟨canonicalRep (coxeterSystem .E6) L w * u *
      (canonicalRep (coxeterSystem .E6) L w)⁻¹, heN⟩ ∈ modelHomE6.range
  rw [e1, map_mul, map_mul, e2, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep w)]
  simpa [MulAut.conj_apply] using hconj

private theorem conjE_canonicalRep_mul_le
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    {g : ModGL .E6 L} {w : WeylGroup .E6}
    (hgN : conjE E g ≤ monomialSubgroup .E6 L) :
    conjE E (canonicalRep (coxeterSystem .E6) L w * g) ≤ monomialSubgroup .E6 L := by
  rw [conjE_conj_mul]
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
  exact mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup L w) (hgN hu))
    (inv_mem (canonicalRep_mem_monomialSubgroup L w))

private theorem maximality_canonicalRep_mul {G : Type*} [Group G]
    (H E T N : Subgroup G) {c g : G}
    (hc : T.map (MulAut.conj c).toMonoidHom = T)
    (hgmax : ∀ g' ∈ H, conjE E g' ≤ N → kcard E T g' ≤ kcard E T g) :
    ∀ g' ∈ H, conjE E g' ≤ N → kcard E T g' ≤ kcard E T (c * g) := by
  intro g' hg'H hg'N
  rw [kcard_conj_mul_of_map_conj_eq hc g]
  exact hgmax g' hg'H hg'N

private theorem exists_maximal_monomial_conj
    {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 3) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {E : Subgroup (ModGL .E6 L)} (hE : E ≤ adjointGroup .E6 L)
    (hEfin : (E : Set (ModGL .E6 L)).Finite) (hEab : IsElemAbelian 3 E) :
    ∃ g ∈ adjointGroup .E6 L, conjE E g ≤ monomialSubgroup .E6 L ∧
      ∀ g' ∈ adjointGroup .E6 L, conjE E g' ≤ monomialSubgroup .E6 L →
        kcard E (torusGroup .E6 L) g' ≤ kcard E (torusGroup .E6 L) g := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite E := hEfin.to_subtype
  obtain ⟨c, hcG, hcN⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_conj_le_monomial_bar
      (τ := .E6) (p := 3) hℓ halg hE hEfin (fun x hx => hEab.2 x hx)
  have hcN' : conjE E c ≤ monomialSubgroup .E6 L :=
    conjE_le_of_forall c fun x hx => by
      have h := hcN x hx
      rwa [MulAut.conj_apply]
  exact exists_maximal_monoConj (adjointGroup .E6 L) E (torusGroup .E6 L)
    (monomialSubgroup .E6 L) ⟨c, hcG, hcN'⟩

theorem exists_conj_regular
    {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ ≠ 3) [CharP L ℓ] (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {E : Subgroup (ModGL .E6 L)} (hE : E ≤ adjointGroup .E6 L)
    (hEfin : (E : Set (ModGL .E6 L)).Finite) (hEab : IsElemAbelian 3 E) :
    ∃ g ∈ adjointGroup .E6 L,
      ∃ hEM : E.map (MulAut.conj g).toMonoidHom ≤ monomialSubgroup .E6 L,
        ∀ e (he : e ∈ E.map (MulAut.conj g).toMonoidHom),
          weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range ∧
            ∀ i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i := by
  classical
  obtain ⟨g, hgG, hgN, hgmax⟩ := exists_maximal_monomial_conj hℓ halg hE hEfin hEab
  let ρE : ↥(conjE E g) →* WeylGroup .E6 :=
    (weylQuotientHom .E6 L).comp (Subgroup.inclusion hgN)
  have hA3 : ∀ a ∈ ρE.range, a ^ 3 = 1 :=
    weylImage_pow_three hgN fun x hx => hEab.2 x hx
  obtain ⟨w, hwS⟩ := exists_conj_le_modelHomE6 hA3
  let cw : ModGL .E6 L := canonicalRep (coxeterSystem .E6) L w
  have hcwG : cw ∈ adjointGroup .E6 L :=
    canonicalRep_mem_adjointGroup (cs := coxeterSystem .E6) L w
  have hcwN : cw ∈ monomialSubgroup .E6 L := canonicalRep_mem_monomialSubgroup L w
  have hcwT : (torusGroup .E6 L).map (MulAut.conj cw).toMonoidHom = torusGroup .E6 L := by
    have hmem := mem_normalizer_torusGroup_of_mem_monomialSubgroup (τ := .E6) (K := L) hcwN
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hmem
  let g' : ModGL .E6 L := cw * g
  have hg'G : g' ∈ adjointGroup .E6 L := mul_mem hcwG hgG
  have hg'N : conjE E g' ≤ monomialSubgroup .E6 L := by
    rw [show g' = cw * g from rfl]
    exact conjE_canonicalRep_mul_le hgN
  have hg'max : ∀ g'' ∈ adjointGroup .E6 L, conjE E g'' ≤ monomialSubgroup .E6 L →
      kcard E (torusGroup .E6 L) g'' ≤ kcard E (torusGroup .E6 L) g' := by
    rw [show g' = cw * g from rfl]
    exact maximality_canonicalRep_mul _ _ _ _ hcwT hgmax
  have hS' : ∀ e ∈ conjE E g', ∀ he : e ∈ monomialSubgroup .E6 L,
      weylQuotientHom .E6 L ⟨e, he⟩ ∈ modelHomE6.range := by
    rw [show g' = cw * g from rfl]
    exact weylImage_canonicalRep_mem_range hgN hwS
  refine ⟨g', hg'G, hg'N, fun e he => ⟨hS' e he (hg'N he), fun i => ?_⟩⟩
  exact no_gE6_of_maximal hℓ halg hEfin hEab hg'G hg'N hg'max he (hg'N he) i

end CFSG.StandardType.E6NonToralThree
