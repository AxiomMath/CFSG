module

import CFSG.RankThree.PartTwo.Sec18.Item181b
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec20.KFactL3OddRank
public import CFSG.RankThree.PartTwo.Sec20.OneStepsProofX
public import CFSG.RankThree.PartTwo.Sec20.Step2054Proof

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

section SL3

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem eq_one_of_pow_three_eq_one_of_card (hq : Nat.card F % 3 = 2) {x : F} (hx : x ^ 3 = 1) :
    x = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    norm_num at hx
  have h3 : ¬ 3 ∣ Nat.card F - 1 := by
    have : 2 ≤ Nat.card F := by omega
    omega
  have hu : (Units.mk0 x hx0) ^ (3 ^ 1) = 1 := Units.ext (by simp [hx])
  have := units_eq_one_of_pow_three_pow h3 hu
  simpa using congrArg Units.val this

theorem eq_one_of_mem_upperTriangular_of_pow_three (hq : Nat.card F % 3 = 2)
    {b : SpecialLinearGroup (Fin 3) F} (hb : b ∈ LinearFlag.upperTriangular 3 F)
    (hb3 : b ^ 3 = 1) : b = 1 := by
  have hbU : (b : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular :=
    LinearFlag.mem_upperTriangular_iff_isUpperTriangular.mp hb
  have hdiag : ∀ i, (b : Matrix (Fin 3) (Fin 3) F) i i = 1 := by
    intro i
    have h : ((b : Matrix (Fin 3) (Fin 3) F) * (b : Matrix (Fin 3) (Fin 3) F) *
        (b : Matrix (Fin 3) (Fin 3) F)) i i = 1 := by
      have := congrArg (fun A : SpecialLinearGroup (Fin 3) F =>
        (A : Matrix (Fin 3) (Fin 3) F) i i) ((pow_three' b).symm.trans hb3)
      exact this.trans (one_apply_eq i)
    rw [LinearFlag.mul_apply_self_of_isUpperTriangular (hbU.mul hbU) hbU,
      LinearFlag.mul_apply_self_of_isUpperTriangular hbU hbU] at h
    exact eq_one_of_pow_three_eq_one_of_card hq (by rw [pow_three']; exact h)
  have hbu : b ∈ LinearFlag.unitriangular 3 F := ⟨hb, hdiag⟩
  obtain ⟨P, hP⟩ := LinearFlag.exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  have h2 : IsPGroup 2 (LinearFlag.unitriangular 3 F) := by
    rw [← hP]
    exact P.isPGroup'
  obtain ⟨k, hk⟩ := h2 ⟨b, hbu⟩
  have hk' : b ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  exact Sec18.eq_one_of_pow_three_of_pow_two_pow hb3 hk'

omit [Finite F] [CharP F 2] in
theorem mem_upperTriangular_of_mem_stabilizer {g : SpecialLinearGroup (Fin 3) F}
    (h1 : g ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 F 1))
    (h2 : g ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 F 2)) :
    g ∈ LinearFlag.upperTriangular 3 F := by
  intro r c hcr
  have hc : (c : ℕ) + 1 = 1 ∨ (c : ℕ) + 1 = 2 := by
    have := r.2
    rw [Fin.lt_def] at hcr
    omega
  have hst : g ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 F ((c : ℕ) + 1)) := by
    rcases hc with h | h <;> rw [h] <;> assumption
  have hmem : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single c 1 ∈
      LinearFlag.flagSpace 3 F ((c : ℕ) + 1) := by
    have h := LinearFlag.mem_stabilizer.mp hst
    rw [← h]
    exact ⟨_, Submodule.subset_span ⟨c, by simp, rfl⟩, rfl⟩
  rw [LinearFlag.mem_flagSpace] at hmem
  have := hmem r (by rw [Fin.lt_def] at hcr; omega)
  rwa [mulVec_single_one, col_apply] at this

theorem sup_upperTriangular_eq_of_isCoatom (hq : Nat.card F % 3 = 2)
    {P Y : Subgroup (SpecialLinearGroup (Fin 3) F)} (hP : IsCoatom P)
    (hBP : LinearFlag.upperTriangular 3 F ≤ P) (hYP : Y ≤ P)
    {y : SpecialLinearGroup (Fin 3) F} (hyY : y ∈ Y) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    Y ⊔ LinearFlag.upperTriangular 3 F = P := by
  obtain ⟨hPI, -⟩ := LinearFlag.borel_overgroups P hBP
  obtain ⟨d, hdmem⟩ : (LinearFlag.borelOvergroupCuts P).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    apply hP.1
    rw [hPI, h, LinearFlag.flagStabilizer_empty]
  obtain ⟨hd, hdn, hdP⟩ := id hdmem
  have hPd : P = LinearFlag.stabilizer (LinearFlag.flagSpace 3 F d) := by
    have hle : P ≤ LinearFlag.stabilizer (LinearFlag.flagSpace 3 F d) := by
      intro g hg
      rw [hPI] at hg
      exact LinearFlag.mem_flagStabilizer.mp hg d hdmem
    rcases hP.le_iff.mp hle with h | h
    · exact absurd h (LinearFlag.stabilizer_flagSpace_ne_top hd hdn)
    · exact h.symm
  have hAP : Y ⊔ LinearFlag.upperTriangular 3 F ≤ P := sup_le hYP hBP
  obtain ⟨hAI, -⟩ := LinearFlag.borel_overgroups (Y ⊔ LinearFlag.upperTriangular 3 F) le_sup_right
  have hdA : d ∈ LinearFlag.borelOvergroupCuts (Y ⊔ LinearFlag.upperTriangular 3 F) :=
    ⟨hd, hdn, fun h => hdP (hAP h)⟩
  have hsub : LinearFlag.borelOvergroupCuts (Y ⊔ LinearFlag.upperTriangular 3 F) ⊆ {d} := by
    intro e he
    by_contra hed
    have hed' : e ≠ d := fun h => hed (Set.mem_singleton_iff.mpr h)
    obtain ⟨he1, hen, -⟩ := id he
    have hyA : y ∈ Y ⊔ LinearFlag.upperTriangular 3 F := Subgroup.mem_sup_left hyY
    rw [hAI] at hyA
    have hyd := LinearFlag.mem_flagStabilizer.mp hyA d hdA
    have hye := LinearFlag.mem_flagStabilizer.mp hyA e he
    have h1 : y ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 F 1) := by
      by_cases hd1 : d = 1
      · rw [← hd1]
        exact hyd
      · have he1' : e = 1 := by omega
        rw [← he1']
        exact hye
    have h2 : y ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 F 2) := by
      by_cases hd2 : d = 2
      · rw [← hd2]
        exact hyd
      · have he2 : e = 2 := by omega
        rw [← he2]
        exact hye
    exact hy1 (eq_one_of_mem_upperTriangular_of_pow_three hq
      (mem_upperTriangular_of_mem_stabilizer h1 h2) hy3)
  have hcuts : LinearFlag.borelOvergroupCuts (Y ⊔ LinearFlag.upperTriangular 3 F) = {d} :=
    Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr hdA)
  rw [hAI, hcuts, LinearFlag.flagStabilizer_singleton, ← hPd]

theorem exists_mem_mul_normalizer_of_isMaxParabolic (hq : Nat.card F % 3 = 2)
    {P Y : Subgroup (SpecialLinearGroup (Fin 3) F)} (hP : Sec18.IsMaxParabolicRankTwo P)
    (U : Sylow 2 (SpecialLinearGroup (Fin 3) F))
    (hUP : (U : Subgroup (SpecialLinearGroup (Fin 3) F)) ≤ P) (hYP : Y ≤ P)
    (hPY : P ≤ Subgroup.normalizer (Y : Set (SpecialLinearGroup (Fin 3) F)))
    {y : SpecialLinearGroup (Fin 3) F} (hyY : y ∈ Y) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∀ p ∈ P, ∃ y' ∈ Y, y'⁻¹ * p ∈
      Subgroup.normalizer ((U : Subgroup (SpecialLinearGroup (Fin 3) F)) :
        Set (SpecialLinearGroup (Fin 3) F)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPc, T₀, hT₀⟩ := hP
  have hsyl : ∀ R : Sylow 2 (SpecialLinearGroup (Fin 3) F),
      (R : Subgroup (SpecialLinearGroup (Fin 3) F)) ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 2 (R : Subgroup (SpecialLinearGroup (Fin 3) F)) P := by
    intro R hRP
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hRP, R.isPGroup', fun h => R.not_dvd_index (h.trans
      (Subgroup.relIndex_dvd_index_of_le hRP))⟩
  have hT₀P : (T₀ : Subgroup (SpecialLinearGroup (Fin 3) F)) ≤ P := Subgroup.le_normalizer.trans hT₀
  obtain ⟨p₀, hp₀, hU₀⟩ := Sec18.exists_map_conj_eq_of_isSylowOf (hsyl T₀ hT₀P) (hsyl U hUP)
  have hNUP : Subgroup.normalizer ((U : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F)) ≤ P := by
    rw [hU₀, ← Subgroup.map_equiv_normalizer_eq]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact P.mul_mem (P.mul_mem hp₀ (hT₀ hw)) (P.inv_mem hp₀)
  obtain ⟨Ut, hUt⟩ := LinearFlag.exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  have hsylTop : ∀ R : Sylow 2 (SpecialLinearGroup (Fin 3) F),
      CFSG.ABGLocalTools.IsSylowOf 2 (R : Subgroup (SpecialLinearGroup (Fin 3) F)) ⊤ := by
    intro R
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, R.isPGroup', R.not_dvd_index⟩
  obtain ⟨g, -, hg⟩ := Sec18.exists_map_conj_eq_of_isSylowOf (hsylTop U) (hsylTop Ut)
  rw [hUt] at hg
  set φ := MulAut.conj g with hφ
  have hB : LinearFlag.upperTriangular 3 F =
      (Subgroup.normalizer ((U : Subgroup (SpecialLinearGroup (Fin 3) F)) :
        Set (SpecialLinearGroup (Fin 3) F))).map
        φ.toMonoidHom := by
    rw [← LinearFlag.normalizer_unitriangular, hg, Subgroup.map_equiv_normalizer_eq]
  have hP₁ : IsCoatom (P.map φ.toMonoidHom) :=
    (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup φ) P).mpr hPc
  have hBP₁ : LinearFlag.upperTriangular 3 F ≤ P.map φ.toMonoidHom := by
    rw [hB]
    exact Subgroup.map_mono hNUP
  have hY₁ : Y.map φ.toMonoidHom ≤ P.map φ.toMonoidHom := Subgroup.map_mono hYP
  have hφy1 : φ y ≠ 1 := fun h => hy1 (φ.injective (h.trans (map_one φ).symm))
  have heq := sup_upperTriangular_eq_of_isCoatom hq hP₁ hBP₁ hY₁ (Subgroup.mem_map_of_mem _ hyY)
    (by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hy3, map_one]) hφy1
  have hBY : LinearFlag.upperTriangular 3 F ≤
      Subgroup.normalizer ((Y.map φ.toMonoidHom : Subgroup (SpecialLinearGroup (Fin 3) F)) :
        Set (SpecialLinearGroup (Fin 3) F)) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact hBP₁.trans (Subgroup.map_mono hPY)
  intro p hp
  have hp₁ : φ p ∈ Y.map φ.toMonoidHom ⊔ LinearFlag.upperTriangular 3 F := by
    rw [heq]
    exact Subgroup.mem_map_of_mem _ hp
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBY] at hp₁
  obtain ⟨_, ⟨y', hy', rfl⟩, b, hb, hyb⟩ := Set.mem_mul.mp hp₁
  refine ⟨y', hy', ?_⟩
  rw [hB] at hb
  obtain ⟨w, hw, hwb⟩ := hb
  have hyb' : φ p = φ y' * φ w := by
    rw [← hyb, ← hwb]
    rfl
  have : y'⁻¹ * p = w := by
    apply φ.injective
    rw [map_mul, map_inv, hyb']
    group
  rw [this]
  exact hw

end SL3

theorem isMaxParabolicRankTwo_map {Q S : Type*} [Group Q] [Group S] [Finite Q] (ε : Q ≃* S)
    {X : Subgroup Q} (h : Sec18.IsMaxParabolicRankTwo X) :
    Sec18.IsMaxParabolicRankTwo (X.map ε.toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hX, T, hT⟩ := h
  have hs : Function.Surjective ε.toMonoidHom := fun y => by
    obtain ⟨a, ha⟩ := ε.surjective y
    exact ⟨a, ha⟩
  refine ⟨(OrderIso.isCoatom_iff (MulEquiv.mapSubgroup ε) X).mpr hX, T.mapSurjective hs, ?_⟩
  show Subgroup.normalizer (((T : Subgroup Q).map ε.toMonoidHom : Subgroup S) : Set S) ≤ _
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hT

variable {G : Type} [Group G] [Finite G]

theorem step208S_core (h321 : Sec3.Item321Split) {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hKC : kTwenty M c ∈ oTwoComponentsIn M)
    (hpar : Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
      (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c)))))
    (h2 : ∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
      ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G))
    (h3 : KIsL3 M c) (hTN : T ≤ N) :
    CFSG.Open.pCoreOf 2 (normalClosureIn (kTwenty M c ⊓ N) c ⊔ T) ≤ sTwenty M N c T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLQ := sup_pCoreOf_eq_core h321 hT hKC h2 h3
  obtain ⟨n, hn, ⟨e⟩⟩ := h3
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  have hc3 : c ^ 3 = 1 := hT.mem_partTwoE.1.2 c hcA
  have hcK : c ∈ kTwenty M c := self_mem_normalClosureIn M c
  have hcN : c ∈ N := by
    rw [hN]
    exact hAL hcA
  have hcKN : c ∈ kTwenty M c ⊓ N := ⟨hcK, hcN⟩
  have hKM : kTwenty M c ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMK : M ≤ Subgroup.normalizer (kTwenty M c : Set G) := le_normalizer_normalClosureIn M c
  have hTM : T ≤ M := hT.sylow.le
  have hTK : T ≤ Subgroup.normalizer (kTwenty M c : Set G) := hTM.trans hMK
  have hXKN : normalClosureIn (kTwenty M c ⊓ N) c ≤ kTwenty M c ⊓ N := normalClosureIn_le hcKN
  have hKNX : kTwenty M c ⊓ N ≤
      Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G) :=
    le_normalizer_normalClosureIn (kTwenty M c ⊓ N) c
  have hQT : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ T :=
    pCoreOf_le_of_isSylowOf (hT.sylow.of_le le_sup_right (sup_le hKM hTM))
  have hOT : CFSG.Open.pCoreOf 2 (kTwenty M c) ≤ T :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKM)
      (hMK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)).trans (pCoreOf_le_of_isSylowOf hT.sylow)
  set Fq := GaloisField 2 n with hFq
  have hcardF : Nat.card Fq = 2 ^ n := GaloisField.card 2 n hn.pos.ne'
  have : CharP Fq 2 := inferInstance
  have hq : Nat.card Fq % 3 = 2 := by
    rw [hcardF]
    exact two_pow_mod_three_of_odd hn
  set ε : (↥(kTwenty M c) ⧸ CFSG.pCore 2 ↥(kTwenty M c)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) Fq :=
    (e.trans (projSLEquivStatedSL hn)).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 Fq).symm with hε
  set φ : ↥(kTwenty M c) →* Matrix.SpecialLinearGroup (Fin 3) Fq :=
    ε.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥(kTwenty M c))) with hφ
  have hφs : Function.Surjective φ := ε.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφk : ∀ w, φ w = 1 → ((w : G) ∈ CFSG.Open.pCoreOf 2 (kTwenty M c)) := by
    intro w hw
    have hw' : QuotientGroup.mk' (CFSG.pCore 2 ↥(kTwenty M c)) w = 1 := by
      apply ε.injective
      rw [map_one]
      exact hw
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw'
    exact ⟨w, hw', rfl⟩
  set P' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq) :=
    ((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map φ with hP'
  have hP'par : Sec18.IsMaxParabolicRankTwo P' := by
    have := isMaxParabolicRankTwo_map ε hpar
    rwa [Subgroup.map_map] at this
  have hTKsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ kTwenty M c) (kTwenty M c) :=
    hT.sylow.inf_of_le_normalizer hKM hMK
  obtain ⟨Q₀, hQ₀⟩ := hTKsyl.exists_sylow_eq_subgroupOf
  set U := Q₀.mapSurjective hφs with hU
  have hUcoe : (U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq)) =
      ((T ⊓ kTwenty M c).subgroupOf (kTwenty M c)).map φ := by
    rw [hU, Sylow.coe_mapSurjective, hQ₀]
  have hUP' : (U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq)) ≤ P' := by
    rw [hUcoe]
    refine Subgroup.map_mono fun w hw => ?_
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    exact ⟨hw.2, hTN hw.1⟩
  set Y : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq) :=
    ((normalClosureIn (kTwenty M c ⊓ N) c).subgroupOf (kTwenty M c)).map φ with hY
  have hYP' : Y ≤ P' := by
    refine Subgroup.map_mono fun w hw => ?_
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    exact hXKN hw
  have hP'Y : P' ≤ Subgroup.normalizer (Y : Set (Matrix.SpecialLinearGroup (Fin 3) Fq)) := by
    rintro _ ⟨k, hk, rfl⟩
    have hk' : ((k : ↥(kTwenty M c)) : G) ∈ kTwenty M c ⊓ N := hk
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hx' : ((x : ↥(kTwenty M c)) : G) ∈ normalClosureIn (kTwenty M c ⊓ N) c := hx
    refine ⟨k * x * k⁻¹, ?_, ?_⟩
    · show ((k * x * k⁻¹ : ↥(kTwenty M c)) : G) ∈ normalClosureIn (kTwenty M c ⊓ N) c
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hKNX hk') _).mp hx' 
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  have hc1 : φ ⟨c, hcK⟩ ≠ 1 := by
    intro h
    have hcO := hφk _ h
    have hKO : kTwenty M c ≤ CFSG.Open.pCoreOf 2 (kTwenty M c) := by
      rw [kTwenty, normalClosureIn, Subgroup.closure_le]
      rintro _ ⟨m, hm, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp
        ((hMK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)) hm) c).mp hcO
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    obtain ⟨w, hw⟩ := hφs (Matrix.SpecialLinearGroup.transvection h01 (1 : Fq))
    have hw1 : φ w = 1 := by
      have hwO : (w : G) ∈ CFSG.Open.pCoreOf 2 (kTwenty M c) := hKO w.2
      obtain ⟨w', hw', hww'⟩ := hwO
      have hw'' : w' = w := Subtype.ext hww'
      rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, ← hw'',
        (QuotientGroup.eq_one_iff _).mpr (by assumption), MulEquiv.coe_toMonoidHom,
        map_one]
    rw [hw1] at hw
    have h2' := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 3) Fq =>
      (B : Matrix (Fin 3) (Fin 3) Fq) 0 1) hw
    simp [Matrix.SpecialLinearGroup.transvection_coe] at h2'
  have hcY : φ ⟨c, hcK⟩ ∈ Y :=
    ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.mpr (self_mem_normalClosureIn _ c), rfl⟩
  have hc3' : φ ⟨c, hcK⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcK⟩ : ↥(kTwenty M c)) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hmul := exists_mem_mul_normalizer_of_isMaxParabolic hq hP'par U hUP' hYP' hP'Y hcY hc3'
    hc1
  have hkey : ∀ k ∈ kTwenty M c ⊓ N, ∀ t ∈ T ⊓ kTwenty M c,
      k * t * k⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c ⊔ T := by
    intro k hk t ht
    obtain ⟨_, ⟨x, hx, rfl⟩, hb⟩ := hmul (φ ⟨k, hk.1⟩)
      ⟨⟨k, hk.1⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have hx' : ((x : ↥(kTwenty M c)) : G) ∈ normalClosureIn (kTwenty M c ⊓ N) c := hx
    have hb' : φ (x⁻¹ * ⟨k, hk.1⟩) ∈
        Subgroup.normalizer ((U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq)) :
          Set (Matrix.SpecialLinearGroup (Fin 3) Fq)) := by
      rw [map_mul, map_inv]
      exact hb
    have htU : φ ⟨t, ht.2⟩ ∈ (U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq)) := by
      rw [hUcoe]
      exact ⟨⟨t, ht.2⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    have hconj := (Subgroup.mem_normalizer_iff.mp hb' _).mp htU
    rw [hUcoe] at hconj
    obtain ⟨t', ht'0, ht'eq⟩ := hconj
    have ht' : ((t' : ↥(kTwenty M c)) : G) ∈ T ⊓ kTwenty M c := ht'0
    obtain ⟨w, hw⟩ : ∃ w : ↥(kTwenty M c), w = x⁻¹ * ⟨k, hk.1⟩ := ⟨_, rfl⟩
    have ht'eq' : φ t' = φ w * φ ⟨t, ht.2⟩ * (φ w)⁻¹ := by
      rw [hw]
      exact ht'eq
    have hker : φ (t'⁻¹ * (w * ⟨t, ht.2⟩ * w⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv (f := φ) w, ← ht'eq', inv_mul_cancel]
    have hO := hφk _ hker
    have hwt : ((w * ⟨t, ht.2⟩ * w⁻¹ : ↥(kTwenty M c)) : G) ∈ T := by
      have : ((w * ⟨t, ht.2⟩ * w⁻¹ : ↥(kTwenty M c)) : G) =
          (t' : G) * ((t'⁻¹ * (w * ⟨t, ht.2⟩ * w⁻¹) : ↥(kTwenty M c)) : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [this]
      exact T.mul_mem ht'.1 (hOT hO)
    have hkt : k * t * k⁻¹ =
        (x : G) * ((w * ⟨t, ht.2⟩ * w⁻¹ : ↥(kTwenty M c)) : G) * (x : G)⁻¹ := by
      simp only [hw, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hkt]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hx')
      (Subgroup.mem_sup_right hwt)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left hx'))
  have hQK : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ Subgroup.normalizer (kTwenty M c : Set G) :=
    hQT.trans hTK
  have hkT : ∀ k ∈ kTwenty M c ⊓ N, ∀ t ∈ T,
      k * t * k⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c ⊔ T := by
    intro k hk t ht
    have htKQ : t ∈ kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) := by
      rw [hLQ]
      exact Subgroup.mem_sup_right ht
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hQK] at htKQ
    obtain ⟨a, ha, q, hq', rfl⟩ := Set.mem_mul.mp htKQ
    have haT : a ∈ T := by
      have : a = (a * q) * q⁻¹ := by group
      rw [this]
      exact T.mul_mem ht (T.inv_mem (hQT hq'))
    have h1' := hkey k hk a ⟨haT, ha⟩
    have h2' : k * q * k⁻¹ ∈ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hk.1)) q).mp hq'
    have : k * (a * q) * k⁻¹ = (k * a * k⁻¹) * (k * q * k⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ h1' (Subgroup.mem_sup_right (hQT h2'))
  have hmain : (kTwenty M c ⊔ T) ⊓ N ≤
      Subgroup.normalizer ((normalClosureIn (kTwenty M c ⊓ N) c ⊔ T : Subgroup G) : Set G) := by
    intro y hy
    have hyKT : y ∈ kTwenty M c ⊔ T := hy.1
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTK] at hyKT
    obtain ⟨k, hk, t, ht, rfl⟩ := Set.mem_mul.mp hyKT
    have hkN : k ∈ N := by
      have : k = (k * t) * t⁻¹ := by group
      rw [this]
      exact N.mul_mem hy.2 (N.inv_mem (hTN ht))
    have hkKN : k ∈ kTwenty M c ⊓ N := ⟨hk, hkN⟩
    refine Subgroup.mul_mem _ ?_ (Subgroup.le_normalizer (Subgroup.mem_sup_right ht))
    apply mem_normalizer_of_map_conj_le
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [map_conj_eq_of_mem_normalizer (hKNX hkKN)]
      exact le_sup_left
    · rintro _ ⟨t₁, ht₁, rfl⟩
      exact hkT k hkKN t₁ ht₁
  have hXle : normalClosureIn (kTwenty M c ⊓ N) c ⊔ T ≤ (kTwenty M c ⊔ T) ⊓ N :=
    sup_le (hXKN.trans (inf_le_inf_right N le_sup_left)) (le_inf le_sup_right hTN)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hXle)
    (hmain.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem step208S_of (h189 : Sec18.Item189) (h321 : Sec3.Item321Split) (h204 : Item204One)
    (h2051 : Step2051) (h2053 : Step2053) : Step208S := by
  intro G _ _ A M L N c T hT hTN
  have h2 := rank3II_20_5_2_of h204 hT (h2051 G A M L N c T hT)
  have h3 := h2053 G A M L N c T hT h2
  obtain ⟨hKC, -, hpar⟩ := item189_case_one h189 hT h3
  obtain ⟨H, -, -, -, hN⟩ := exists_sec18H_of_ctx20One hT
  exact step208S_core h321 hT.toCtx20 hN (le_normalizer_of_hyp201One hT.hyp201One) hKC hpar h2 h3
    hTN

theorem step208XActs_of (h189 : Sec18.Item189) (h321 : Sec3.Item321Split) (h204 : Item204One)
    (h2051 : Step2051) (h2053 : Step2053) : Step208XActs :=
  step208XActs_of_step208S (step208S_of h189 h321 h204 h2051 h2053)

end CFSG.RankThree.PartTwo.Sec20
