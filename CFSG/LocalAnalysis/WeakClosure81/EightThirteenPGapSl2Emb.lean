module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapF4Data
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import Certificates.Certificate43
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
import CFSG.GroupTheory.AlternatingFive.SylowTwo
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShape
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def slTwoDiag {F : Type} [Field F] (l : Fˣ) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![(l : F), 0; 0, ((l⁻¹ : Fˣ) : F)], by
    rw [Matrix.det_fin_two_of]
    simp⟩

private lemma wcgaps2_exists_diag_mul_unitriangular {F : Type} [Field F]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (hg : g ∈ upperTriangular 2 F) :
    ∃ l : Fˣ, ∃ u ∈ unitriangular 2 F, g = slTwoDiag l * u := by
  have hg10 : g 1 0 = 0 := by
    have h := (mem_upperTriangular.mp hg) 1 0 (by decide)
    simpa using h
  obtain ⟨a, c, ha, hg'⟩ :=
    Matrix.SpecialLinearGroup.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero g hg10
  let u : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![1, a⁻¹ * c; 0, 1], by rw [Matrix.det_fin_two_of]; simp⟩
  refine ⟨Units.mk0 a ha, u, ?_, ?_⟩
  · rw [mem_unitriangular]
    refine ⟨?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [u]
    · intro i
      fin_cases i <;> simp [u]
  · rw [hg']
    refine Subtype.ext ?_
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [u, slTwoDiag, Matrix.mul_apply, Fin.sum_univ_two, Units.val_mk0,
        Units.val_inv_eq_inv_val, mul_inv_cancel_left₀ ha]

private theorem wcgaps2_oTwoMod_bot_eq_bot {M : Type} [Group M] [Finite M] {K : Subgroup M}
    [IsSimpleGroup ↥K] (hcard : Nat.card K = 60) : oTwoMod (⊥ : Subgroup M) K = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff, oTwoMod]
  refine iSup₂_le ?_
  intro W hW
  obtain ⟨-, hWK, hWnorm, hWpow⟩ := hW
  haveI : (W.subgroupOf K).Normal := hWnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.subgroupOf K) with h | h
  · rw [Subgroup.subgroupOf_eq_bot, disjoint_iff] at h
    rw [inf_eq_left.mpr hWK] at h
    rw [h]
  · rw [Subgroup.subgroupOf_eq_top] at h
    have hWK' : W = K := le_antisymm hWK h
    exfalso
    rw [hWK'] at hWpow
    have hKpg : IsPGroup 2 ↥K := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro w
      obtain ⟨k, hk⟩ := hWpow w w.2
      rw [Subgroup.mem_bot] at hk
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hKpg
    rw [hcard] at hn
    have hn5 : n ≤ 5 := by
      by_contra h'
      have h6 : 6 ≤ n := by omega
      have h64 : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h6
      rw [← hn] at h64
      norm_num at h64
    interval_cases n <;> norm_num at hn

theorem centralKData_of_sl2_embedding {G : Type} [Group G]
    [Finite G] {S A : Subgroup G} (hS : IsPGroup 2 S) (hAS : A ≤ S)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (ι : Matrix.SpecialLinearGroup (Fin 2) F →* G) (hι : Function.Injective ι)
    (hA : A = (unitriangular 2 F).map ι)
    (hT : ∀ l : Fˣ, ι (slTwoDiag l) ∈ normalizer (S : Set G)) :
    CentralKData S A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU₂card : Nat.card (unitriangular 2 F) = 4 := by
    rw [card_unitriangular (K := F) 2, hF]
    norm_num
  have hU₂pgroup : IsPGroup 2 (unitriangular 2 F) :=
    IsPGroup.of_card (n := 2) (by rw [hU₂card]; norm_num)
  have hAcard : Nat.card A = 4 := by
    rw [hA, Subgroup.card_map_of_injective (f := ι) hι, hU₂card]
  have hAK : A ≤ ι.range := by
    rw [hA]
    exact Subgroup.map_le_range ι (unitriangular 2 F)
  have hL2 : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2
      (Matrix.SpecialLinearGroup (Fin 2) F) 2 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22d_isL2_of_statedSL (n := 2) (F := F)
      (by norm_num) (by rw [hF]; norm_num)
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)
  obtain ⟨e⟩ : Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃*
      alternatingGroup (Fin 5)) :=
    CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hL2
  have hA₅card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hG₂card : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
    rw [Nat.card_congr e.toEquiv, hA₅card]
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
  haveI hG₂simple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := e.isSimpleGroup
  have eK : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥ι.range := MonoidHom.ofInjective hι
  haveI hKsimple : IsSimpleGroup ↥ι.range := eK.symm.isSimpleGroup
  have hKcard : Nat.card ι.range = 60 := by
    rw [← Nat.card_congr eK.toEquiv]
    exact hG₂card
  have hAle : A ≤ S ⊓ ι.range := le_inf hAS hAK
  have hcardInf : Nat.card ↥(S ⊓ ι.range) = 4 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (hS.to_le inf_le_left)
    have h4le : 4 ≤ Nat.card ↥(S ⊓ ι.range) := by
      rw [← hAcard]
      exact Subgroup.card_le_of_le hAle
    have hle60 : Nat.card ↥(S ⊓ ι.range) ≤ 60 := by
      rw [← hKcard]
      exact Subgroup.card_le_of_le inf_le_right
    have hdvd : Nat.card ↥(S ⊓ ι.range) ∣ 60 := by
      rw [← hKcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hnle : n ≤ 5 := by
      by_contra h'
      have h6 : 6 ≤ n := by omega
      have h64 : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h6
      have h64' : 2 ^ 6 ≤ Nat.card ↥(S ⊓ ι.range) := by rwa [← hn] at h64
      norm_num at h64'
      omega
    interval_cases n
    · rw [hn] at h4le; norm_num at h4le
    · rw [hn] at h4le; norm_num at h4le
    · rw [hn]; norm_num
    · rw [hn] at hdvd; norm_num at hdvd
    · rw [hn] at hdvd; norm_num at hdvd
    · rw [hn] at hdvd; norm_num at hdvd
  have hinf : S ⊓ ι.range = A := by
    refine (Subgroup.eq_of_le_of_card_ge hAle ?_).symm
    rw [hcardInf, hAcard]
  have hnormU : normalizer (unitriangular 2 F : Set (Matrix.SpecialLinearGroup (Fin 2) F)) =
      upperTriangular 2 F := normalizer_unitriangular
  have hBU : (upperTriangular 2 F).map ι ≤ normalizer (S : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh k hk
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hh
    obtain ⟨l, u, hu, hbu⟩ := wcgaps2_exists_diag_mul_unitriangular b hb
    have hιb : ι b = ι (slTwoDiag l) * ι u := by rw [hbu, map_mul]
    have hιuA : ι u ∈ A := by
      rw [hA]
      exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    have hιbN : ι b ∈ normalizer (S : Set G) := by
      rw [hιb]
      exact (normalizer (S : Set G)).mul_mem (hT l) (Subgroup.le_normalizer (hAS hιuA))
    exact (Subgroup.mem_normalizer_iff.mp hιbN k).mp hk
  have hKinfN : ι.range ⊓ normalizer (S : Set G) ≤ (upperTriangular 2 F).map ι := by
    intro k hk
    obtain ⟨hkK, hkN⟩ := Subgroup.mem_inf.mp hk
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hkK
    have hkNA : k ∈ normalizer (A : Set G) := by
      have h2 : k ∈ normalizer (ι.range : Set G) :=
        (Subgroup.le_normalizer (H := ι.range)) hkK
      have h3 := Subgroup.inf_normalizer_le_normalizer_inf (H := S) (K := ι.range)
        (Subgroup.mem_inf.mpr ⟨hkN, h2⟩)
      rwa [hinf] at h3
    let φg : Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) F :=
      MulAut.conj g
    let φk : G →* G := MulAut.conj k
    have hcomp : ι.comp φg = φk.comp ι := by
      ext x
      change ι (g * x * g⁻¹) = k * ι x * k⁻¹
      rw [map_mul, map_mul, map_inv, hg]
    have hkAφk : A.map φk = A := by
      simpa only [φk] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hkNA
    have hkey : ((unitriangular 2 F).map φg).map ι = (unitriangular 2 F).map ι := by
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, ← hA, hkAφk, hA]
    have hconj : (unitriangular 2 F).map φg = unitriangular 2 F :=
      Subgroup.map_injective (f := ι) hι hkey
    have hgN : g ∈ normalizer (unitriangular 2 F : Set
        (Matrix.SpecialLinearGroup (Fin 2) F)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      simpa only [φg] using hconj
    have hgU : g ∈ upperTriangular 2 F := by
      rw [← hnormU]
      exact hgN
    exact Subgroup.mem_map.mpr ⟨g, hgU, hg⟩
  have hKN_eq : ι.range ⊓ (⊤ ⊓ normalizer (S : Set G)) = (upperTriangular 2 F).map ι := by
    rw [top_inf_eq]
    exact le_antisymm hKinfN (le_inf (Subgroup.map_le_range ι (upperTriangular 2 F)) hBU)
  have hP₀card : Nat.card ((unitriangular 2 F).map e.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hU₂card]
  have hP₀idx : ¬ 2 ∣ ((unitriangular 2 F).map e.toMonoidHom).index := by
    have h := Subgroup.index_mul_card ((unitriangular 2 F).map e.toMonoidHom)
    rw [hP₀card, hA₅card] at h
    have h15 : ((unitriangular 2 F).map e.toMonoidHom).index = 15 := by omega
    rw [h15]
    norm_num
  let P : Sylow 2 (alternatingGroup (Fin 5)) :=
    (hU₂pgroup.map e.toMonoidHom).toSylow hP₀idx
  have hPcoe : (P : Subgroup (alternatingGroup (Fin 5))) =
      (unitriangular 2 F).map e.toMonoidHom :=
    IsPGroup.toSylow_coe _ _
  have hPindex : (Subgroup.normalizer (P : Set (alternatingGroup (Fin 5)))).index = 5 := by
    rw [← Sylow.card_eq_index_normalizer P, CFSG.GroupTheory.AlternatingFive.card_sylowTwo]
  have hBindex : (upperTriangular 2 F).index = 5 := by
    have hmapB : (upperTriangular 2 F).map e.toMonoidHom =
        Subgroup.normalizer (P : Set (alternatingGroup (Fin 5))) := by
      rw [← hnormU,
        Subgroup.map_normalizer_eq_of_bijective (unitriangular 2 F)
          (f := e.toMonoidHom) e.bijective, ← hPcoe]
      rfl
    have hmapidx : ((upperTriangular 2 F).map e.toMonoidHom).index =
        (upperTriangular 2 F).index := by
      rw [Subgroup.index_map_of_injective (H := upperTriangular 2 F) (f := e.toMonoidHom)
        e.injective, MonoidHom.range_eq_top.mpr e.surjective, Subgroup.index_top, mul_one]
    rw [← hmapidx, hmapB, hPindex]
  have hidx5 : (ι.range ⊓ (⊤ ⊓ normalizer (S : Set G))).relIndex ι.range = 5 := by
    rw [hKN_eq]
    have hmap := Subgroup.relIndex_map_map_of_injective (f := ι) (upperTriangular 2 F)
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) hι
    rw [Subgroup.map_top] at hmap
    rw [hmap, Subgroup.relIndex_top_right]
    exact hBindex
  have hOt : oTwoMod (⊥ : Subgroup G) ι.range = ⊥ :=
    wcgaps2_oTwoMod_bot_eq_bot (K := ι.range) hKcard
  have hnA : ¬ A ≤ oTwoMod (⊥ : Subgroup G) ι.range := by
    rw [hOt]
    intro hle
    have hAeq : A = ⊥ := le_bot_iff.mp hle
    have h1 : Nat.card A = 1 := by rw [hAeq]; exact Subgroup.card_bot
    omega
  have hshape : HasQuotShape ι.range (oTwoMod (⊥ : Subgroup G) ι.range : Set G)
      (fun X _ => CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 X 2) := by
    rw [hOt]
    refine ⟨Matrix.SpecialLinearGroup (Fin 2) F, inferInstance, eK.symm,
      eK.symm.surjective, ?_, hL2⟩
    intro k
    constructor
    · intro hk
      have hk1 : k = 1 := (MulEquiv.map_eq_one_iff eK.symm).mp hk
      change (k : G) = 1
      exact congrArg Subtype.val hk1
    · intro hk
      have hk' : (k : G) = 1 := by simpa using hk
      have hk1 : k = 1 := Subtype.ext hk'
      rw [hk1]
      exact map_one eK.symm
  have hSyl : IsSylowIn 2 (S ⊓ ι.range) ι.range := by
    rw [hinf]
    refine ⟨hAK, ?_, ?_⟩
    · rw [hA]
      exact hU₂pgroup.map ι
    · intro hdvd
      have hmul := Subgroup.relIndex_mul_card (H := A) (K := ι.range)
      rw [inf_eq_left.mpr hAK, hAcard, hKcard] at hmul
      have hrel : A.relIndex ι.range = 15 := by omega
      rw [hrel] at hdvd
      norm_num at hdvd
  exact ⟨ι.range, hAK, hnA, hshape, hSyl, hidx5⟩

end CFSG.LocalAnalysis.WeakClosure81

end
