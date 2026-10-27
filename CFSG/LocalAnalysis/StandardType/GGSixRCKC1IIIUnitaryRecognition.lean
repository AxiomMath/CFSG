module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIField
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIFixedUnitaryBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAt
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSU
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSU
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPSU
import CFSG.LocalAnalysis.SteinbergCDEvenClassicalOrderFour

public section

namespace CFSG.StandardType.RCKC1

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.StandardType
  CFSG.StandardType.ClassicalPosition CFSG.LocalAnalysis.SteinbergCD
  CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.RCKRP
open CFSG.Open (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj)

theorem exists_orderOf_eq_four_centerQuot_of_row_III
    {X : Type} [Group X] {J : Subgroup X} (hrow : GGSixRCKJRow .III J) :
    ∃ z : ↥J ⧸ Subgroup.center ↥J, orderOf z = 4 := by
  obtain ⟨lab, hlab, R, _, I, F, θ, _, _, hr, hmarked⟩ :=
    largeEvenMarking_exists_markedModel hrow
  have hm : MarkedModel lab (↥J ⧸ Subgroup.center ↥J) :=
    MarkedModel.of_mulEquiv θ.symm hmarked
  obtain ⟨hchar, hdeg, hshape⟩ := ggSixRCKLabelRow_III_parameters hlab hr
  have hm' : LieModel (↥J ⧸ Subgroup.center ↥J) (markTag lab) (markRank lab) 2 1 := by
    unfold MarkedModel at hm
    rwa [hchar, hdeg] at hm
  rcases hshape with ⟨ht, h3⟩ | ⟨ht, h4⟩
  · rw [ht] at hm'
    have hC : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSp (markRank lab) 2 1 := by
      simpa [LieModel, classicalTags, chevalleyExceptionalTags, reeTitsTags] using hm'
    obtain ⟨F, hF, hfinF, hcard, ⟨η⟩⟩ := hC.2
    let : Field F := hF
    have : Finite F := hfinF
    have h2 : (2 : F) = 0 := by
      simpa [hcard] using (card_nsmul_eq_zero' (x := (1 : F)))
    obtain ⟨z, -, hz⟩ := exists_orderOf_eq_four_statedSp h2 (by omega : 2 ≤ markRank lab)
    exact ⟨η.symm (QuotientGroup.mk z), by rw [MulEquiv.orderOf_eq]; exact hz⟩
  · rw [ht] at hm'
    have hC : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSU (markRank lab) 2 1 := by
      simpa [LieModel, classicalTags, chevalleyExceptionalTags, reeTitsTags] using hm'
    obtain ⟨F, hF, hfinF, hcard, ⟨η⟩⟩ := hC.2
    let : Field F := hF
    have : Finite F := hfinF
    let hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F :=
      { prime := Nat.prime_two, one_le := by norm_num,
        card := by simpa using hcard }
    obtain ⟨z, -, hz⟩ := exists_orderOf_eq_four_unitaryPSU hU (by omega : 3 ≤ markRank lab)
    let ηU := unitaryPSUEquiv hU (n := markRank lab) (by omega)
    exact ⟨η.symm (ηU (unitaryProj hU (markRank lab) z)), by
      rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq]
      exact hz⟩

private theorem orderOf_ne_four_of_gl_dim_le_two
    {F : Type} [Field F] [CharP F 2] {n : ℕ} (hn : n ≤ 2) (A : GL (Fin n) F) :
    orderOf A ≠ 4 := by
  intro hA
  have hA4 : (A : Matrix (Fin n) (Fin n) F) ^ 4 = 1 := by
    have h := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F))
      (show A ^ 4 = 1 by rw [← hA, pow_orderOf_eq_one])
    simpa using h
  have hdet : (A : Matrix (Fin n) (Fin n) F).det = 1 := by
    apply eq_one_of_pow_four_eq_one CharTwo.two_eq_zero
    simpa [det_pow] using congrArg Matrix.det hA4
  let B : SpecialLinearGroup (Fin n) F := ⟨(A : Matrix (Fin n) (Fin n) F), hdet⟩
  have hBA : SpecialLinearGroup.toGL B = A := Units.ext rfl
  have hinj : Function.Injective (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin n) F →* GL (Fin n) F) := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hxy)
  have hB : orderOf B = 4 := by
    rw [← orderOf_injective SpecialLinearGroup.toGL hinj B, hBA]
    exact hA
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn' with rfl | rfl | rfl
  · have hB1 : B = 1 := by
      apply Subtype.ext
      ext i j
      exact Fin.elim0 i
    simp [hB1] at hB
  · have hB1 : B = 1 := by
      apply Subtype.ext
      ext i j
      fin_cases i
      fin_cases j
      simpa [det_fin_one] using B.2
    simp [hB1] at hB
  · exact SL_two_orderOf_ne_four CharTwo.two_eq_zero B hB

theorem false_of_row_III_of_no_order_four
    {X G : Type} [Group X] [Group G] [Finite G]
    (π : G →* X) {J : Subgroup X} (hJ : J ≤ π.range)
    (hrow : GGSixRCKJRow .III J) (hno : ∀ g : G, orderOf g ≠ 4) : False := by
  classical
  obtain ⟨z, hz⟩ := exists_orderOf_eq_four_centerQuot_of_row_III hrow
  let H : Subgroup G := J.comap π
  let πJ : H →* J := (π.comp H.subtype).codRestrict J (fun g => g.2)
  have hπJ : Function.Surjective πJ := by
    intro j
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hJ j.2)
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    change π g ∈ J
    rw [hg]
    exact j.2
  let ρ : H →* (↥J ⧸ Subgroup.center ↥J) :=
    (QuotientGroup.mk' (Subgroup.center ↥J)).comp πJ
  have hρ : Function.Surjective ρ := (QuotientGroup.mk'_surjective _).comp hπJ
  obtain ⟨g, hg⟩ := hρ z
  have hdvd : 4 ∣ orderOf g := by
    have h := orderOf_map_dvd ρ g
    rwa [hg, hz] at h
  have h4 : orderOf (g ^ (orderOf g / 4)) = 4 :=
    orderOf_pow_orderOf_div (orderOf_pos g).ne' hdvd
  exact hno ((g ^ (orderOf g / 4) : H) : G)
    ((orderOf_injective H.subtype (Subgroup.subtype_injective H) _).trans h4)

theorem three_le_of_row_III_of_matrix_range
    {X G F : Type} [Group X] [Group G] [Finite G] [Field F] [CharP F 2]
    {n : ℕ} (j : G →* GL (Fin n) F) (hj : Function.Injective j)
    (π : G →* X) {J : Subgroup X} (hJ : J ≤ π.range)
    (hrow : GGSixRCKJRow .III J) : 3 ≤ n := by
  by_contra hn
  apply false_of_row_III_of_no_order_four π hJ hrow
  intro g hg
  exact orderOf_ne_four_of_gl_dim_le_two (by omega) (j g)
    ((orderOf_injective j hj g).trans hg)


theorem eq_zero_of_row_III_of_selfDual_unitary_block
    {X : Type} [Group X] {n g : ℕ}
    (φ : (ggU .PSU n (g + 1)).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .PSU n (g + 1)).K)
    (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hadj : formAdj (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (antidiag n) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2)
    {J' : Subgroup (ggU .PSU n (g + 1)).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype S e :
          Subgroup (ggU .PSU n (g + 1)).K),
        (glBlockCentralizer (SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype S e :
          Subgroup (ggU .PSU n (g + 1)).K)⁆)
    (hrow : GGSixRCKJRow .III (J'.map φ)) : g = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, ι, E, W, hgood, hιinj, hιrange, -⟩ :=
    exists_linearBlockModel_selfDual_PSU n g S hS he hadj hdeg hJe
  let ιA : (ggU .PSU r (g + 1)).K →* (ggU .PSU n (g + 1)).K := ι
  let ν : (ggU .PSU r (g + 1)).K →* X := φ.comp ιA
  have hιAinj : Function.Injective ιA := hιinj
  have hνr : ν.range = J'.map φ := by
    dsimp only [ν]
    rw [MonoidHom.range_comp, show ιA.range = J' from hιrange]
  have hνk : ν.ker ≤ Subgroup.center (ggU .PSU r (g + 1)).K := by
    intro y hy
    have hcy := hφk hy
    rw [Subgroup.mem_center_iff] at hcy ⊢
    intro z
    apply hιAinj
    rw [map_mul, map_mul, hcy (ιA z)]
  let j : (ggU .PSU r (g + 1)).K →* GL (Fin r) (GaloisField 2 (2 * (g + 1))) := (SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r).subtype
  have hj : Function.Injective j := Subgroup.subtype_injective _
  have : Finite (ggU .PSU r (g + 1)).K :=
    inferInstanceAs (Finite ↥(SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r))
  have hr3 : 3 ≤ r := three_le_of_row_III_of_matrix_range j hj ν
    (by rw [hνr]) hrow
  have hadm : StatedLieAdmissible .PSU r 2 (g + 1) := by
    refine ⟨Nat.prime_two, by omega, hr3, ?_⟩
    intro hbad
    rcases hgood with hgood | ⟨hr2, -⟩
    · exact hgood.2 ⟨(Prod.mk.inj hbad).1, (Prod.mk.inj hbad).2⟩
    · omega
  have hm := irg_lieModel_quot (ht := Or.inr (Or.inl rfl)) hadm ν hνr hνk
  have hf := (lieModel_parameters_of_row_III hrow hm).1
  omega

theorem false_of_row_III_of_dualPair_unitary_block
    {X : Type} [Group X] {n g : ℕ}
    (φ : (ggU .PSU n (g + 1)).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .PSU n (g + 1)).K)
    (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hSU : ∀ s ∈ S, conjTr (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) *
      antidiag n * (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (antidiag n) e ≠ e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2)
    {J' : Subgroup (ggU .PSU n (g + 1)).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype S
          (e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (antidiag n) e) :
          Subgroup (ggU .PSU n (g + 1)).K),
        (glBlockCentralizer (SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype S
          (e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (antidiag n) e) :
          Subgroup (ggU .PSU n (g + 1)).K)⁆)
    (hrow : GGSixRCKJRow .III (J'.map φ)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, ι, β₀, hdim, hconj, hlong, hcent, hιrange, -⟩ :=
    exists_blockModel_dualPair_PSU_explicitModel n g S hSU hS he hpair hdeg hJe
  let ιA : (ggU .PSL (k + 1) (2 * (g + 1))).K →* (ggU .PSU n (g + 1)).K := ι
  let ν : (ggU .PSL (k + 1) (2 * (g + 1))).K →* X := φ.comp ιA
  have hνr : ν.range = J'.map φ := by
    dsimp only [ν]
    rw [MonoidHom.range_comp, show ιA.range = J' from hιrange]
  have hνk : ν.ker ≤ Subgroup.center (ggU .PSL (k + 1) (2 * (g + 1))).K := by
    intro y hy
    exact hcent y (hφk hy)
  let j : (ggU .PSL (k + 1) (2 * (g + 1))).K →* GL (Fin (k + 1)) (GaloisField 2 (2 * (g + 1))) :=
    SpecialLinearGroup.toGL
  have hj : Function.Injective j := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun a : GL (Fin (k + 1)) (GaloisField 2 (2 * (g + 1))) =>
      (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (GaloisField 2 (2 * (g + 1))))) hxy)
  have : Finite (ggU .PSL (k + 1) (2 * (g + 1))).K :=
    inferInstanceAs (Finite (SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 (2 * (g + 1)))))
  have hk3 : 3 ≤ k + 1 := three_le_of_row_III_of_matrix_range j hj ν
    (by rw [hνr]) hrow
  have hadm : StatedLieAdmissible .PSL (k + 1) 2 (2 * (g + 1)) := by
    refine ⟨Nat.prime_two, by omega, by omega, ?_, ?_⟩
    all_goals intro hbad; have := (Prod.mk.inj hbad).1; omega
  have hm := irg_lieModel_quot (ht := Or.inl rfl) hadm ν hνr hνk
  have hf := (lieModel_parameters_of_row_III hrow hm).1
  omega

theorem fixedSUBlockAt_of_native_unitary_model
    {X : Type} [Group X] [Finite X] {p n g : ℕ} {K J : Subgroup X} {d : X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdp : d ^ p = 1)
    (φ : (ggU .PSU n (g + 1)).K →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .PSU n (g + 1)).K)
    (hdN : d ∈ Subgroup.normalizer (K : Set X))
    (hdID : GGPsiInnerDiag (ggU .PSU n (g + 1)).D φ d)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) : FixedSUBlockAt K J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let j : (ggU .PSU n (g + 1)).K →* GL (Fin n) (GaloisField 2 (2 * (g + 1))) := (SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype
  have hj : Function.Injective j := Subgroup.subtype_injective _
  have : Finite (ggU .PSU n (g + 1)).K :=
    inferInstanceAs (Finite ↥(SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n))
  have hJK : J ≤ φ.range := by rw [hφr]; exact hJ.1.trans inf_le_left
  have hn : 3 ≤ n := three_le_of_row_III_of_matrix_range j hj φ hJK hrow
  obtain ⟨s, hsU, -, hsodd, ε, hε, ⟨e, he, heε, hcase⟩, J', hJe, hJmap⟩ :=
    rckF1_PSU hp hp2 hdp hn φ hφr hφk hdN hdID hJ
  have hrow' : GGSixRCKJRow .III (J'.map φ) := by rw [hJmap]; exact hrow
  let S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))) := {s}
  have hSU : ∀ a ∈ S, conjTr (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (a : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) *
      antidiag n * (a : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = antidiag n := by
    intro a ha
    obtain rfl : a = s := ha
    exact hsU
  have hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b := by
    intro a ha b hb
    have ha' : a = s := ha
    have hb' : b = s := hb
    rw [ha', hb']
  have hodd : ∀ a ∈ S, Odd (orderOf a) := by
    intro a ha
    obtain rfl : a = s := ha
    exact hsodd
  have hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2 := by
    by_contra hdeg
    have hFE := ggSixLSevenFieldExtCase_PSU
      (card_galoisField_two_mul 2 (g + 1) (by omega)) n φ hφk S hSU hS hodd
      hε hJe he heε (by omega)
    exact not_fieldExtCase_of_row_III hrow' (by omega) hFE
  rcases hcase with hself | ⟨-, hpair, hεeq⟩
  · subst ε
    have hadj := hε.2.2.2.1
    have hg := eq_zero_of_row_III_of_selfDual_unitary_block φ hφk S hS he hadj hdeg hJe hrow'
    subst g
    have hφK : ∀ x, φ x ∈ K := by
      intro x
      rw [← hφr]
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
    let π : CFSG.StandardType.RCKK1IIISU.SUG n →* K := φ.codRestrict K hφK
    have hπsurj : Function.Surjective π := by
      intro k
      have hk : (k : X) ∈ φ.range := by rw [hφr]; exact k.2
      obtain ⟨x, hx⟩ := hk
      exact ⟨x, Subtype.ext hx⟩
    have hπk : π.ker ≤ Subgroup.center (CFSG.StandardType.RCKK1IIISU.SUG n) := by
      intro x hx
      apply hφk
      exact MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
    refine ⟨n, π, hπsurj, hπk, S, e, J', hS, he, hadj, hdeg, hJe, ?_⟩
    ext k
    constructor
    · rintro ⟨x, hx, hxk⟩
      change (k : X) ∈ J
      rw [← hJmap]
      exact ⟨x, hx, congrArg Subtype.val hxk⟩
    · intro hk
      change (k : X) ∈ J at hk
      rw [← hJmap] at hk
      obtain ⟨x, hx, hxk⟩ := hk
      exact ⟨x, hx, Subtype.ext hxk⟩
  · have hJe' : IsComponentOf J'
        ⁅glBlockCentralizer (SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype S
            (e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (antidiag n) e),
          glBlockCentralizer (SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype S
            (e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (antidiag n) e)⁆ := by
      rw [← hεeq]
      exact hJe
    exact (false_of_row_III_of_dualPair_unitary_block φ hφk S hSU hS he hpair hdeg hJe' hrow').elim

theorem fixedSUBlockAt_of_unitary_modelID
    {X : Type} [Group X] [Finite X] {p : ℕ} {K J B : Subgroup X} {d : X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ b ∈ B, b ^ p = 1)
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) (hdB : d ∈ B)
    (hmodel : RCKClassicalModelIDAt .PSU K B)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) : FixedSUBlockAt K J := by
  obtain ⟨n, f, φ, hf, hφr, hφk, hdiag⟩ := hmodel
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  exact fixedSUBlockAt_of_native_unitary_model hp hp2 (hpow d hdB)
    φ hφr hφk (hBK hdB) (hdiag d hdB) hJ hrow

theorem exists_nonunitary_modelID_of_not_fixedSUBlockAt
    {X : Type} [Group X] [Finite X] {p : ℕ} {K J B : Subgroup X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ b ∈ B, b ^ p = 1)
    (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hJd : ∃ d ∈ B, IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) (hnot : ¬ FixedSUBlockAt K J)
    (hmodel : RCKClassicalModelID K B) :
    ∃ t : StatedLieTag, RCKClassicalTag t ∧ t ≠ .PSU ∧ RCKClassicalModelIDAt t K B := by
  obtain ⟨t, n, f, φ, ht, hf, hφr, hφk, hdiag⟩ := hmodel
  have hAt : RCKClassicalModelIDAt t K B := ⟨n, f, φ, hf, hφr, hφk, hdiag⟩
  refine ⟨t, ht, ?_, hAt⟩
  intro htU
  subst t
  obtain ⟨d, hdB, hJ⟩ := hJd
  exact hnot (fixedSUBlockAt_of_unitary_modelID hp hp2 hpow hBK hdB hAt hJ hrow)

end CFSG.StandardType.RCKC1
