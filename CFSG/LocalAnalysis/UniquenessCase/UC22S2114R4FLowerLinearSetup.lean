module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FLinearField
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FReduction
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
public import CFSG.LieType.SpecialLinear.NormalizerLift.Lift
public import CFSG.LocalAnalysis.UniquenessCase.UC22S211Setup4
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LieType.SpecialLinear.NormalizerLift.SylowNormalization
import CFSG.LieType.SpecialLinear.NormalizerLift.FieldGraph
import CFSG.LieType.SpecialLinear.BorelTwist.Upper
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229NSE
public import CFSG.LieType.SpecialLinear.CurtisDatum
import CFSG.LieType.SpecialLinear.Block222.Borel.Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

theorem uc22s2114r4f_three_le_pRank_three_psl_six {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) {m f : ℕ} (hm : 6 ≤ m)
    (hX : LieModel (BarInf L) .PSL m 2 f) : 3 ≤ CFSG.Open.pRank 3 L := by
  by_cases hfe : Even f
  · exact (by omega : 3 ≤ 4).trans
      (uc22s2114r4f_four_le_pRank_three_psl_even hL (by omega) hX hfe)
  have hfo : Odd f := Nat.not_even_iff_odd.1 hfe
  have h3Z : ¬ 3 ∣ Nat.card (center (Bar2 L)) := fun hd =>
    uc22p20v_not_three_dvd_sub_one hfo
      ((hd.trans (uc22s2114r4f_card_center_psl hL (by omega) hX)).trans
        (Nat.gcd_dvd_right _ _))
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    (LieModel.of_mulEquiv eb hX).statedClassicalModel (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have h3quot : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L ⧸ center (Bar2 L))) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e]
    exact CFSG.SectionRank.ClassicalEven.psl_three_le_pRank_three hm
  rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)]
  rwa [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd
    Nat.prime_three h3Z]

theorem uc22s2114r4f_isStronglyPEmbedded_three_psl_six_dataOfSetup4
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (S : Setup4 G)
    (hPart : PartIAt S.M) {L : Subgroup G} (hL : L ∈ calC S.M)
    {m f : ℕ} (hm : 6 ≤ m) (hX : LieModel (BarInf L) .PSL m 2 f) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M :=
  PartOne.Section8.isStronglyPEmbedded_three_of_calC_three_le hS S hPart hL
    (uc22s2114r4f_three_le_pRank_three_psl_six hL hm hX)

theorem uc22s2114r4f_false_of_psl_of_isStronglyPEmbedded_three_dataOfSetup4
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (_hMS : S.InMSigma) (_hPart : PartIAt S.M)
    (h74 : F07.R74Card (UC6.dataOfSetup4 hS hU S))
    {Ch : Choice2011 G} (hH : H1930 (UC6.dataOfSetup4 hS hU S))
    (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch) {L : Subgroup G}
    (hL : L ∈ calC S.M) {m f : ℕ} (hm : 5 ≤ m)
    (hX : LieModel (BarInf L) .PSL m 2 f)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M) {b : G} (hbB : b ∈ c.B0)
    (hbL : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hbr : orderOf b = r) (hrn : r ∣ 2 ^ c.n - 1) (_hrf : r ∣ f)
    (hcase : Odd c.n ∨ (LieModel (BarInf L) .PSL 5 2 f ∧ Odd f ∧ 3 ≤ f))
    (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) : False := by
  have : Fact r.Prime := ⟨hr⟩
  have hrg := uc22s2114r4f_not_dvd_gcd_psl_lower
    (UC6S846.sigmaStd_dataOfSetup4 hS hU S) hH c hL (by omega) hX hr hr5 hrn hcase
  have hrK := uc22s2114r4f_not_dvd_radical_psl hL (by omega) hX hr (by omega) hrg
  have hθr : inducedBarInfAutHom L ⟨b, hbL⟩ ^ r = 1 := by
    rw [← map_pow]
    have hb : (⟨b, hbL⟩ : normalizer (L : Set G)) ^ r = 1 :=
      Subtype.ext (hbr ▸ pow_orderOf_eq_one b)
    rw [hb, map_one]
  have hθ1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1 := fun h1 => hin ⟨1, by rw [map_one, h1]⟩
  have hθord : orderOf (inducedBarInfAutHom L ⟨b, hbL⟩) = r := orderOf_eq_prime hθr hθ1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  let θ := inducedBarInfAutHom L ⟨b, hbL⟩
  have hθ' : orderOf (MulAut.congr e θ) = r :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective θ).trans hθord
  have hout' : MulAut.congr e θ ∉
      (MulAut.conj : projectiveSL m K →* MulAut (projectiveSL m K)).range := by
    rintro ⟨x, hx⟩
    apply hin
    refine ⟨e.symm x, (MulAut.congr e).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply, hx]
  have hrg' : ¬ r ∣ Nat.gcd m (Nat.card K - 1) := by rwa [hK]
  obtain ⟨-, σ, hσ, δ, hδ⟩ := uc22s2114r4f_linear_field_descent (by omega)
    hX.admissible.2.1 hK hr (by omega) hrg' (MulAut.congr e θ) hθ' hout'
  let ε : projectiveSL m K ≃* BarInf L := δ.trans e.symm
  have hε : ∀ x, θ (ε x) = ε (fieldAut m K σ x) := by
    intro x
    have hx : (MulAut.congr e θ) (δ x) = δ (fieldAut m K σ x) := by
      simp [hδ, MulAut.mul_apply]
    have hx' := congrArg e.symm hx
    simpa [ε, MulAut.congr_apply] using hx'
  obtain ⟨X, hXp, hXc, hfix⟩ := uc22s2114r4f_exists_fixed_three_linear (m := m) (by omega) σ
  let j : X →* BarInf L := ε.toMonoidHom.comp X.subtype
  have hj : Function.Injective j := ε.injective.comp X.subtype_injective
  let η := MonoidHom.ofInjective hj
  have hXfix : ∀ x ∈ j.range, inducedBarInfAutHom L ⟨b, hbL⟩ x = x := by
    rintro _ ⟨x, rfl⟩
    exact (hε x).trans (congrArg ε (hfix x x.2))
  obtain ⟨q, hq, hq7, hqr, hqm, A, _, _, hAp, hAc, κ, hκ, ι, hι, hσι⟩ :=
    uc22s2114r4f_exists_fpf_nonsplit_linear (m := m) (by omega) hX.admissible.2.1 hK hr hr5 σ hσ
  have hqK := uc22s2114r4f_not_dvd_radical_psl hL (by omega) hX hq (by omega)
    (fun h => hqm (h.trans (Nat.gcd_dvd_right _ _)))
  have hθι : ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ε (ι a)) = ε (ι (κ a)) := by
    intro a
    exact (hε (ι a)).trans (congrArg ε (hσι a))
  exact uc22s2114r4f_false_of_fieldData_of_isStronglyPEmbedded h74 hH c hL hbB hbL hr hr5
    hbr hrK Nat.prime_three (by norm_num) hsp (hXp.of_equiv η)
    (fun hc => hXc (η.isCyclic.2 hc)) hXfix hq hq7 hqr hqK hAp hAc κ hκ
    (ε.toMonoidHom.comp ι) (ε.injective.comp hι) hθι

theorem uc22s2114r4f_false_of_psl_six_le_dataOfSetup4
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (_hMS : S.InMSigma) (hPart : PartIAt S.M)
    (h74 : F07.R74Card (UC6.dataOfSetup4 hS hU S))
    {Ch : Choice2011 G} (hH : H1930 (UC6.dataOfSetup4 hS hU S))
    (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch) {L : Subgroup G}
    (hL : L ∈ calC S.M) {m f : ℕ} (hm : 6 ≤ m)
    (hX : LieModel (BarInf L) .PSL m 2 f) {b : G} (hbB : b ∈ c.B0)
    (hbL : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hbr : orderOf b = r) (hrn : r ∣ 2 ^ c.n - 1) (_hrf : r ∣ f)
    (hcase : Odd c.n ∨ (LieModel (BarInf L) .PSL 5 2 f ∧ Odd f ∧ 3 ≤ f))
    (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) : False := by
  exact uc22s2114r4f_false_of_psl_of_isStronglyPEmbedded_three_dataOfSetup4
    hS hU S _hMS hPart h74 hH c hL (by omega) hX
    (uc22s2114r4f_isStronglyPEmbedded_three_psl_six_dataOfSetup4 hS S hPart hL hm hX)
    hbB hbL hr hr5 hbr hrn _hrf hcase hin

theorem uc22s2114r4f_two_le_pRank_three_psl_five {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) {f : ℕ}
    (hX : LieModel (BarInf L) .PSL 5 2 f) : 2 ≤ CFSG.Open.pRank 3 L := by
  have h3Z : ¬ 3 ∣ Nat.card (center (Bar2 L)) := by
    intro hd
    have h3 : 3 ∣ 5 := (hd.trans (uc22s2114r4f_card_center_psl hL (by norm_num) hX)).trans
      (Nat.gcd_dvd_left _ _)
    norm_num at h3
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨K, _, _, -, ⟨η⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  obtain ⟨X, hXp, hXc, -⟩ := uc22s2114r4f_exists_fixed_three_linear (m := 5) (by norm_num)
    (RingEquiv.refl K)
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (projectiveSL 5 K)) :=
    (UC6.two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num) hXp hXc).trans
      (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt le_top)
  rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num),
    ← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd
      Nat.prime_three h3Z,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e.symm,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt η]
  exact h2

theorem uc22s2114r4f_isStronglyPEmbedded_three_psl_five_of_not_normal_dataOfSetup4
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) {L : Subgroup G} (hL : L ∈ calC S.M) {f : ℕ}
    (hX : LieModel (BarInf L) .PSL 5 2 f)
    (hnN : ¬ (L.subgroupOf S.M).Normal) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M := by
  have h3Z : ¬ 3 ∣ Nat.card (center (Bar2 L)) := by
    intro hd
    have h3 : 3 ∣ 5 := (hd.trans (uc22s2114r4f_card_center_psl hL (by norm_num) hX)).trans
      (Nat.gcd_dvd_left _ _)
    norm_num at h3
  have hnotN : ¬ S.M ≤ normalizer (L : Set G) := fun h =>
    hnN ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).2 h)
  obtain ⟨E, hEL, hEel, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 3) Nat.prime_three.one_lt L
  have h4 := UC6S846.calCRankTwice S.M L hL hnotN 3 Nat.prime_three (by norm_num) h3Z
    E hEL hEel (CFSG.Open.pRank 3 L) hEc
  have h2 := uc22s2114r4f_two_le_pRank_three_psl_five hL hX
  have h4M : 4 ≤ CFSG.Open.pRank 3 (UC6.dataOfSetup4 hS hU S).M := by
    change 4 ≤ CFSG.Open.pRank 3 S.M
    omega
  have h3σ := (UC6S846.sigmaStd_dataOfSetup4 hS hU S).four_mem 3 Nat.prime_three
    (by norm_num) h4M
  exact PartOne.Section8.isStronglyPEmbedded_of_mem_sigma_of_calC hS hU S hL h3σ

theorem uc22s2114r4f_false_of_psl_five_of_not_normal_dataOfSetup4
    {G : Type} [Group G] [Finite G] (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M)
    (h74 : F07.R74Card (UC6.dataOfSetup4 hS hU S))
    {Ch : Choice2011 G} (hH : H1930 (UC6.dataOfSetup4 hS hU S))
    (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch) {L : Subgroup G}
    (hL : L ∈ calC S.M) {f : ℕ} (hX : LieModel (BarInf L) .PSL 5 2 f)
    (hnN : ¬ (L.subgroupOf S.M).Normal) {b : G} (hbB : b ∈ c.B0)
    (hbL : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hbr : orderOf b = r) (hrn : r ∣ 2 ^ c.n - 1) (hrf : r ∣ f)
    (hcase : Odd c.n ∨ (LieModel (BarInf L) .PSL 5 2 f ∧ Odd f ∧ 3 ≤ f))
    (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) : False := by
  exact uc22s2114r4f_false_of_psl_of_isStronglyPEmbedded_three_dataOfSetup4
    hS hU S hMS hPart h74 hH c hL (by norm_num) hX
    (uc22s2114r4f_isStronglyPEmbedded_three_psl_five_of_not_normal_dataOfSetup4
      hS hU S hL hX hnN)
    hbB hbL hr hr5 hbr hrn hrf hcase hin

section LinearFiveModel

open Matrix CFSG.LieType.SpecialLinear

private theorem exists_graph_fixed_torus_five {F : Type} [Field F] [Finite F] [CharP F 2]
    {q : ℕ} (hq : q.Prime) (hqd : q ∣ Nat.card F - 1) :
    ∃ t : SpecialLinearGroup (Fin 5) F, t ∈ (curtisDatum 4 F 2).H ∧
      t ^ q = 1 ∧ t ∉ scalars 5 F ∧ borelGraph 5 F t = t := by
  have : Fact q.Prime := ⟨hq⟩
  have hqU : q ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) q hqU
  have haq : a ^ q = 1 := ha ▸ pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at ha
    exact hq.ne_one ha.symm
  let s : Fin 4 := 0
  let z : Fin 4 := 3
  let d : Fin 4 → Fˣ →* SpecialLinearGroup (Fin 5) F := fun k =>
    { toFun := hdiag 4 F k
      map_one' := hdiag_one 4 F k
      map_mul' := hdiag_mul 4 F k }
  let t := d s a * d z a
  have hcomm : Commute (d s a) (d z a) := by
    change d s a * d z a = d z a * d s a
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change ((hdiag 4 F s a : Matrix (Fin 5) (Fin 5) F) *
      (hdiag 4 F z a : Matrix (Fin 5) (Fin 5) F)) i j =
      ((hdiag 4 F z a : Matrix (Fin 5) (Fin 5) F) *
        (hdiag 4 F s a : Matrix (Fin 5) (Fin 5) F)) i j
    rw [hdiag_matrix, hdiag_matrix, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      exact mul_comm _ _
    · simp [Matrix.diagonal_apply_ne _ hij]
  have htH : t ∈ (curtisDatum 4 F 2).H :=
    (curtisDatum 4 F 2).H.mul_mem (hdiag_mem_H 4 F s a) (hdiag_mem_H 4 F z a)
  have htq : t ^ q = 1 := by
    rw [hcomm.mul_pow]
    rw [← map_pow, ← map_pow, haq, map_one, map_one, one_mul]
  have htmat : (t : Matrix (Fin 5) (Fin 5) F) = Matrix.diagonal
      (fun i : Fin 5 => if i = 0 then (a : F) else if i = 1 then (a⁻¹ : Fˣ)
        else if i = 3 then (a : F) else if i = 4 then (a⁻¹ : Fˣ) else 1) := by
    change (hdiag 4 F s a * hdiag 4 F z a : Matrix (Fin 5) (Fin 5) F) = _
    rw [hdiag_matrix, hdiag_matrix, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [s, z]
  have htZ : t ∉ scalars 5 F := by
    rintro ⟨c, -, hc⟩
    have h0 := congrFun (congrFun hc (0 : Fin 5)) (0 : Fin 5)
    have h2 := congrFun (congrFun hc (2 : Fin 5)) (2 : Fin 5)
    rw [htmat] at h0 h2
    simp [Matrix.scalar_apply] at h0 h2
    exact ha1 (Units.ext (by simpa using h0.trans h2.symm))
  have htγ : borelGraph 5 F t = t := by
    change borelGraph 5 F (hdiag 4 F s a * hdiag 4 F z a) = _
    rw [map_mul, borelGraph_hdiag, borelGraph_hdiag]
    have hs : Fin.rev s = z := by decide
    have hz : Fin.rev z = s := by decide
    rw [hs, hz]
    exact hcomm.eq.symm
  exact ⟨t, htH, htq, htZ, htγ⟩

private theorem exists_borel_form_five_of_lift {F : Type} [Field F] [Finite F] [CharP F 2]
    {H : Type} [Group H] (π : Matrix.SpecialLinearGroup (Fin 5) F →* H)
    (hker : π.ker ≤ scalars 5 F) (e : rangeNormalizer π)
    (he : (e : H) ∈ normalizer ((unitriangular 5 F).map π : Set H))
    (hfield : fieldPart π hker (by norm_num) e = 1) :
    ∃ (A : GL (Fin 5) F) (ε : ℕ), IsUpperGL A ∧ ε ≤ 1 ∧
      liftAut π hker (by norm_num) e = borelStd 5 F A 1 ε := by
  have hU : unitriangular 5 F = (curtisDatum 4 F 2).U := by
    ext g
    rw [LinearFlag.mem_unitriangular, mem_curtisDatum_U_iff]
    exact and_comm
  have hσ : (stdData π hker (by norm_num) e).2.1 = 1 := hfield
  have hε := stdData_eps_le_one π hker (by norm_num) e
  have hmaps := liftAut_mapsTo_unitriangular π hker (by norm_num) e he
  let B := (stdData π hker (by norm_num) e).1
  have hform := liftAut_eq_stdAut π hker (by norm_num) e
  rw [hσ] at hform
  rcases (show (stdData π hker (by norm_num) e).2.2 = 0 ∨
      (stdData π hker (by norm_num) e).2.2 = 1 by omega) with h0 | h1
  · rw [h0] at hform
    have hB : IsUpperGL B := isUpperGL_of_stdAut_zero_mapsTo B 1 (by rwa [← hform])
    exact ⟨B, 0, hB, by omega, hform.trans (borelStd_zero B 1).symm⟩
  · rw [h1, stdAut_one_eq_borelStd] at hform
    let A := B * (revGL 5 F)⁻¹
    have hA : IsUpperGL A := by
      apply isUpperGL_of_stdAut_zero_mapsTo A 1
      intro u hu
      have hγu : borelGraph 5 F u ∈ unitriangular 5 F := by
        rw [hU] at hu ⊢
        exact borelGraph_mem_U 4 F hu
      have h := hmaps _ hγu
      rw [hform, borelStd_apply, pow_one] at h
      have hγγ : borelGraph 5 F (borelGraph 5 F u) = u := by
        simpa [MulAut.mul_apply] using
          DFunLike.congr_fun (borelGraph_mul_self (F := F) (n := 5)) u
      rwa [hγγ] at h
    exact ⟨A, 1, hA, by omega, hform⟩

private theorem lift_torus_eq_mod_unitriangular_five {F : Type} [Field F] [Finite F] [CharP F 2]
    {H : Type} [Group H] (π : Matrix.SpecialLinearGroup (Fin 5) F →* H)
    (hker : π.ker ≤ scalars 5 F) (e : rangeNormalizer π)
    (he : (e : H) ∈ normalizer ((unitriangular 5 F).map π : Set H))
    (hfield : fieldPart π hker (by norm_num) e = 1)
    {t : Matrix.SpecialLinearGroup (Fin 5) F} (ht : t ∈ (curtisDatum 4 F 2).H)
    (htγ : borelGraph 5 F t = t) :
    t⁻¹ * liftAut π hker (by norm_num) e t ∈ unitriangular 5 F := by
  obtain ⟨A, ε, hA, hε, hform⟩ := exists_borel_form_five_of_lift π hker e he hfield
  have hU : unitriangular 5 F = (curtisDatum 4 F 2).U := by
    ext g
    rw [LinearFlag.mem_unitriangular, mem_curtisDatum_U_iff]
    exact and_comm
  rw [hform, borelStd_apply]
  have hγpow : (borelGraph 5 F ^ ε) t = t := by
    rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
    · rfl
    · simpa only [pow_one] using htγ
  rw [hγpow, hU]
  simpa using stdAut_zero_torus 4 F A hA (1 : F ≃+* F) ht

private theorem exists_prime_order_normalizes_sylow_five_of_unitriangular
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {H : Type} [Group H] [Finite H] (π : Matrix.SpecialLinearGroup (Fin 5) F →* H)
    (hker : π.ker ≤ scalars 5 F) {f q : ℕ} (hF : Nat.card F = 2 ^ f) (hf : Odd f)
    (hq : q.Prime) (hqd : q ∣ Nat.card F - 1) (T : Sylow 2 H)
    (hTN : (T : Subgroup H) ≤ rangeNormalizer π)
    (hTU : (T : Subgroup H) ≤ normalizer ((unitriangular 5 F).map π : Set H)) :
    ∃ t : H, t ∈ normalizer ((T : Subgroup H) : Set H) ∧ orderOf t = q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact q.Prime := ⟨hq⟩
  have hU2 : IsPGroup 2 (unitriangular 5 F) := by
    obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := F) 2 (n := 5) (by norm_num)
    rw [← hP]
    exact P.isPGroup'
  have hUT : (unitriangular 5 F).map π ≤ (T : Subgroup H) := by
    have hp := (hU2.map π).to_sup_of_normal_left' T.isPGroup' hTU
    have heq := T.is_maximal' hp le_sup_right
    rw [← heq]
    exact le_sup_left
  have hfield : ∀ e (he : e ∈ (T : Subgroup H)), fieldPart π hker (by norm_num) ⟨e, hTN he⟩ = 1 := by
    intro e he
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨e, he⟩
    apply CFSG.ComponentClassification.AutL2Facts.eq_one_of_two_power_ringAut Nat.prime_two hF hf _ k
    rw [← map_pow]
    have hepow : (⟨e, hTN he⟩ : rangeNormalizer π) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [hepow, map_one]
  obtain ⟨t, htH, htq, htZ, htγ⟩ := exists_graph_fixed_torus_five hq hqd
  have hπtN : (π t)⁻¹ ∈ normalizer ((T : Subgroup H) : Set H) := by
    apply Subgroup.mem_normalizer_fintype
    intro e he
    have hcomm := lift_torus_eq_mod_unitriangular_five π hker ⟨e, hTN he⟩ (hTU he)
      (hfield e he) htH htγ
    have hcommπ : (π t)⁻¹ * e * π t * e⁻¹ ∈ (T : Subgroup H) := by
      apply hUT
      have hmem := Subgroup.mem_map_of_mem π hcomm
      simpa only [map_mul, map_inv, liftAut_spec, mul_assoc] using hmem
    have hnorm : (π t)⁻¹ * e * π t ∈ (T : Subgroup H) := by
      have h := (T : Subgroup H).mul_mem hcommπ he
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
    simpa only [inv_inv, SetLike.mem_coe] using hnorm
  have hπtq : (π t) ^ q = 1 := by rw [← map_pow, htq, map_one]
  have hπt1 : π t ≠ 1 := fun h => htZ (hker h)
  refine ⟨(π t)⁻¹, ?_, ?_⟩
  · exact hπtN
  · rw [orderOf_inv]
    exact orderOf_eq_prime hπtq hπt1

theorem uc22s2114r4f_prime_dvd_card_normalizer_sylow_five_of_scalar_kernel
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {H : Type} [Group H] [Finite H] (π : Matrix.SpecialLinearGroup (Fin 5) F →* H)
    (hker : π.ker ≤ scalars 5 F) {f q : ℕ} (hF : Nat.card F = 2 ^ f) (hf : Odd f)
    (hq : q.Prime) (hqd : q ∣ Nat.card F - 1) (T : Sylow 2 H)
    (hTN : (T : Subgroup H) ≤ rangeNormalizer π) :
    q ∣ Nat.card (normalizer ((T : Subgroup H) : Set H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_conj_normalizes_unitriangular π (by norm_num)
    (T : Subgroup H) hTN T.isPGroup'
  let α := MulAut.conj ((π x)⁻¹)
  let T' : Sylow 2 H := T.mapSurjective (f := α.toMonoidHom) α.surjective
  have hT' : (T' : Subgroup H) = (T : Subgroup H).map α.toMonoidHom :=
    Sylow.coe_mapSurjective (f := α.toMonoidHom) α.surjective T
  have hTN' : (T' : Subgroup H) ≤ rangeNormalizer π := by
    rw [hT']
    rintro _ ⟨t, ht, rfl⟩
    have hxN : π x ∈ rangeNormalizer π := Subgroup.le_normalizer ⟨x, rfl⟩
    dsimp [α]
    rw [inv_inv]
    exact (rangeNormalizer π).mul_mem
      ((rangeNormalizer π).mul_mem ((rangeNormalizer π).inv_mem hxN) (hTN ht)) hxN
  have hTU' : (T' : Subgroup H) ≤ normalizer ((unitriangular 5 F).map π : Set H) := by
    rw [hT']
    rintro _ ⟨t, ht, rfl⟩
    simpa only [α, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hx t ht
  obtain ⟨t, htN, hto⟩ := exists_prime_order_normalizes_sylow_five_of_unitriangular
    π hker hF hf hq hqd T' hTN' hTU'
  have hd : q ∣ Nat.card (normalizer ((T' : Subgroup H) : Set H)) := by
    have h := Subgroup.orderOf_dvd_natCard _ htN
    rwa [hto] at h
  rw [hT', ← Subgroup.map_equiv_normalizer_eq] at hd
  rwa [Subgroup.card_map_of_injective α.injective] at hd

end LinearFiveModel

open CFSG.Semidihedral.Principal.CoprimeFixedPoint (quotientAction_mk)

private theorem inner_le_inducedBarInf_range {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hLM : L ≤ M) (hN : M ≤ normalizer (L : Set G)) :
    (MulAut.conj : BarInf L →* MulAut (BarInf L)).range ≤
      ((inducedBarInfAutHom L).comp (Subgroup.inclusion hN)).range := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical L) x
  refine ⟨⟨l, hLM l.2⟩, ?_⟩
  ext y
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical L) y
  change inducedBarInfAutHom L ⟨l, hN (hLM l.2)⟩ (QuotientGroup.mk v) = _
  rw [inducedBarInfAutHom, quotientAction_mk]
  change (QuotientGroup.mk' (CFSG.solvableRadical L)) (l * v * l⁻¹) = _
  simp only [MulAut.conj_apply, map_mul, map_inv]

theorem uc22s2114r4f_prime_dvd_normalizer_psl_five_of_normal {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) (hLn : (L.subgroupOf M).Normal)
    {f : ℕ} (hX : LieModel (BarInf L) .PSL 5 2 f) (hfo : Odd f)
    {q : ℕ} (hq : q.Prime) (hqd : q ∣ 2 ^ f - 1) (T : Sylow 2 M) :
    q ∣ Nat.card (normalizer ((T : Subgroup M) : Set M)) := by
  have hN : M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hLn
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  have : Group.IsPerfect (Bar2 L) := ⟨hL.2.2.1⟩
  have hCentre : center (projectiveSL 5 K) = ⊥ := by
    let η := eb.symm.trans e
    have h := Group.IsPerfect.center_quotient_center_eq_bot (G := Bar2 L)
    have hmap := Subgroup.map_center_eq η
    rw [h] at hmap
    simpa using hmap.symm
  let Φ : M →* MulAut (projectiveSL 5 K) :=
    (MulAut.congr e).toMonoidHom.comp
      ((inducedBarInfAutHom L).comp (Subgroup.inclusion hN))
  have hinn : (MulAut.conj : projectiveSL 5 K →* MulAut (projectiveSL 5 K)).range ≤ Φ.range := by
    rintro _ ⟨x, rfl⟩
    have h := inner_le_inducedBarInf_range hL.1.le hN ⟨e.symm x, rfl⟩
    obtain ⟨m, hm⟩ := h
    refine ⟨m, ?_⟩
    change MulAut.congr e (((inducedBarInfAutHom L).comp (Subgroup.inclusion hN)) m) = _
    rw [hm, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply]
  let π : Matrix.SpecialLinearGroup (Fin 5) K →* Φ.range :=
    ((MulAut.conj : projectiveSL 5 K →* MulAut (projectiveSL 5 K)).comp (proj 5 K)).codRestrict
      Φ.range fun g => hinn ⟨proj 5 K g, rfl⟩
  have hker : π.ker ≤ scalars 5 K := by
    intro g hg
    have hπ : MulAut.conj (proj 5 K g) = 1 := congrArg Subtype.val hg
    have hc : proj 5 K g ∈ center (projectiveSL 5 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := DFunLike.congr_fun hπ y
      have hh : proj 5 K g * y * (proj 5 K g)⁻¹ = y := by simpa [MulAut.conj_apply] using h
      exact (mul_inv_eq_iff_eq_mul.1 hh).symm
    rw [hCentre, Subgroup.mem_bot] at hc
    exact proj_eq_one_iff.1 hc
  let S : Sylow 2 Φ.range := T.mapSurjective (f := Φ.rangeRestrict) Φ.rangeRestrict_surjective
  have hπN : (S : Subgroup Φ.range) ≤ CFSG.LieType.SpecialLinear.rangeNormalizer π := by
    intro s hs
    have hπrange : π.range =
        ((MulAut.conj : projectiveSL 5 K →* MulAut (projectiveSL 5 K)).range).subgroupOf Φ.range := by
      ext a
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨proj 5 K g, rfl⟩
      · rintro ⟨x, hx⟩
        obtain ⟨g, rfl⟩ := proj_surjective 5 K x
        exact ⟨g, Subtype.ext hx⟩
    change s ∈ normalizer (π.range : Set Φ.range)
    rw [hπrange]
    have hnorm : (((MulAut.conj : projectiveSL 5 K →* MulAut (projectiveSL 5 K)).range).subgroupOf
        Φ.range).Normal := inferInstance
    have := hnorm
    rw [Subgroup.normalizer_eq_top]
    trivial
  have hqdK : q ∣ Nat.card K - 1 := by rwa [hK]
  have hd := uc22s2114r4f_prime_dvd_card_normalizer_sylow_five_of_scalar_kernel
    π hker hK hfo hq hqdK S hπN
  rw [Sylow.coe_mapSurjective,
    normalizer_map_sylow_eq Φ.rangeRestrict Φ.rangeRestrict_surjective T] at hd
  exact hd.trans (Subgroup.card_map_dvd _ _)

theorem uc22s2114r4f_false_of_normal_psl_five_odd_of_s21_1 {G : Type} [Group G] [Finite G] (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G)
    {Ch : Choice2011 G} (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch)
    (hH : H1930 (UC6.dataOfSetup4 hS hU S)) (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch)
    {L : Subgroup G} (hL : L ∈ calC S.M) (hLn : (L.subgroupOf S.M).Normal)
    {f : ℕ} (hX : LieModel (BarInf L) .PSL 5 2 f) (hfo : Odd f) (hf : 2 ≤ f) : False := by
  have hne : 2 ^ f - 1 ≠ 1 := by
    have h4 : 4 ≤ 2 ^ f := (by norm_num : 4 = 2 ^ 2).trans_le (Nat.pow_le_pow_right (by norm_num) hf)
    omega
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  have : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by
    intro h
    subst q
    have hpow : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have hp := Nat.one_le_two_pow (n := f)
    omega
  have hq5 : q ≠ 5 := fun h => uc22p20v_not_five_dvd_sub_one hfo (h ▸ hqd)
  have hrank := (uc22s2114r4f_le_pRank_of_dvd_sub_one_psl_with_scalar hL (by norm_num) hX hq hq2 hqd).2
    (fun hd => hq5 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).1 hd))
  have h4M : 4 ≤ CFSG.Open.pRank q (UC6.dataOfSetup4 hS hU S).M := by
    change 4 ≤ CFSG.Open.pRank q S.M
    have hmono := CFSG.SectionRank.pRank_mono hq.one_lt hL.1.le
    norm_num at hrank
    omega
  have hqσ := (UC6S846.sigmaStd_dataOfSetup4 hS hU S).four_mem q hq hq2 h4M
  obtain ⟨P, hP⟩ := S.sylowM
  have hd := uc22s2114r4f_prime_dvd_normalizer_psl_five_of_normal hL hLn hX hfo hq hqd P
  have hdN : q ∣ Nat.card (normalizer (S.T : Set G)) := by
    have hnormal : (normalizer ((P : Subgroup S.M) : Set S.M)).map S.M.subtype ≤
        normalizer (S.T : Set G) := by
      have h := Subgroup.le_normalizer_map (H := (P : Subgroup S.M)) S.M.subtype
      rw [hP] at h
      exact h
    have hcard : Nat.card ((normalizer ((P : Subgroup S.M) : Set S.M)).map S.M.subtype) =
        Nat.card (normalizer ((P : Subgroup S.M) : Set S.M)) :=
      Subgroup.card_map_of_injective S.M.subtype_injective
    rw [← hcard] at hd
    exact hd.trans (Subgroup.card_dvd_of_le hnormal)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := normalizer (S.T : Set G)) q hdN
  have hxo : orderOf (x : G) = q := (Subgroup.orderOf_coe x).trans hx
  exact uc22ine229_not_mem_sig_of_mem_normalizer h211 (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    (UC6S846.not_solvable_of_mem_calC hL) hH c hq hq2 x.2 hxo hqσ

private theorem false_of_psl_five_dataOfSetup4_of_s21_1 {G : Type} [Group G] [Finite G] (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M)
    {Ch : Choice2011 G} (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch)
    (h74 : F07.R74Card (UC6.dataOfSetup4 hS hU S)) (hH : H1930 (UC6.dataOfSetup4 hS hU S))
    (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch) {L : Subgroup G} (hL : L ∈ calC S.M)
    {f : ℕ} (hX : LieModel (BarInf L) .PSL 5 2 f) {b : G} (hbB : b ∈ c.B0)
    (hbL : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hbr : orderOf b = r) (hrn : r ∣ 2 ^ c.n - 1) (hrf : r ∣ f)
    (hcase : Odd c.n ∨ (LieModel (BarInf L) .PSL 5 2 f ∧ Odd f ∧ 3 ≤ f))
    (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) : False := by
  by_cases hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M
  · exact uc22s2114r4f_false_of_psl_of_isStronglyPEmbedded_three_dataOfSetup4
      hS hU S hMS hPart h74 hH c hL (by norm_num) hX hsp hbB hbL hr hr5 hbr hrn hrf hcase hin
  by_cases hfe : Even f
  · exact hsp (PartOne.Section8.isStronglyPEmbedded_three_of_calC_three_le hS S hPart hL
      ((by omega : 3 ≤ 4).trans (uc22s2114r4f_four_le_pRank_three_psl_even hL (by norm_num) hX hfe)))
  have hfo : Odd f := Nat.not_even_iff_odd.1 hfe
  by_cases hn : (L.subgroupOf S.M).Normal
  · have hf : 2 ≤ f := by
      have hp := Nat.le_of_dvd (by have := hX.admissible.2.1; omega) hrf
      omega
    exact uc22s2114r4f_false_of_normal_psl_five_odd_of_s21_1 hS hU S h211 hH c hL hn hX hfo hf
  · exact uc22s2114r4f_false_of_psl_five_of_not_normal_dataOfSetup4
      hS hU S hMS hPart h74 hH c hL hX hn hbB hbL hr hr5 hbr hrn hrf hcase hin

section ActualSectionTwentyOne

theorem uc22s2114r4f_false_of_psl_five_dataOfSetup4 {G : Type} [Group G] [Finite G] (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M)
    {Ch : Choice2011 G}
    (h74 : F07.R74Card (UC6.dataOfSetup4 hS hU S)) (hH : H1930 (UC6.dataOfSetup4 hS hU S))
    (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch) {L : Subgroup G} (hL : L ∈ calC S.M)
    {f : ℕ} (hX : LieModel (BarInf L) .PSL 5 2 f) {b : G} (hbB : b ∈ c.B0)
    (hbL : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hbr : orderOf b = r) (hrn : r ∣ 2 ^ c.n - 1) (hrf : r ∣ f)
    (hcase : Odd c.n ∨ (LieModel (BarInf L) .PSL 5 2 f ∧ Odd f ∧ 3 ≤ f))
    (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) : False := by
  exact false_of_psl_five_dataOfSetup4_of_s21_1 hS hU S hMS hPart
    (s21_1_dataOfSetup4 hS hU S hMS hPart Ch) h74 hH c hL hX hbB hbL hr hr5 hbr hrn hrf hcase hin

end ActualSectionTwentyOne

end CFSG.LocalAnalysis.UniquenessCase.UC22
