module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res4ProofSeven
public import CFSG.RankThree.PartTwo.Sec20.Item20Res4ProofSevenSL3
import CFSG.RankThree.PartTwo.Sec18.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_centralizer_of_mem {F : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (F : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (F : Set G) : Set G) := by
  apply mem_normalizer_of_map_conj_le
  rintro _ ⟨w, hw, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hw
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hf' : g⁻¹ * f * g ∈ F := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) f).mp hf
    simpa using this
  have h1 := hw _ hf'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc f * (g * w * g⁻¹) = g * ((g⁻¹ * f * g) * w) * g⁻¹ := by group
    _ = g * (w * (g⁻¹ * f * g)) * g⁻¹ := by rw [h1]
    _ = g * w * g⁻¹ * f := by group

theorem step207Struct_core (h321 : Sec3.Item321Split) {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hKC : kTwenty M c ∈ oTwoComponentsIn M)
    (hK : KType20 M N c)
    (hBn : M ≤ Subgroup.normalizer (((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G))
    (h204 : scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M})
    (h1 : ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (h3 : KIsL3 M c) (hTN : T ≤ N)
    (hCK : ¬ kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N) :
    ∃ x ∈ kTwenty M c, x ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
      x * c * x⁻¹ ∈ Subgroup.centralizer (fTwenty M N c T : Set G) ∧
      kTwenty M c ≤ (normalClosureIn (kTwenty M c ⊓
          Subgroup.centralizer (fTwenty M N c T : Set G)) (x * c * x⁻¹) ⊔ iTwenty M N c) ⊔
        CFSG.Open.pCoreOf 2 (kTwenty M c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 := rank3II_20_5_2_core hT h204 h1
  have hLQ := sup_pCoreOf_eq_core h321 hT hKC h2 h3
  have hpar := KType20.isMaxParabolic hK h3
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
  have hAM : A ≤ M := le_of_hyp201 hT.toHyp201
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
  have hOK : CFSG.Open.pCoreOf 2 (kTwenty M c) ≤ kTwenty M c :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (kTwenty M c)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hTZ : T ≤ Subgroup.centralizer (zTwenty T : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.mpr fun z hz => ((mem_and_commute_of_mem_zTwenty hz).2 t ht).symm
  set Fq := GaloisField 2 n with hFq
  have : CharP Fq 2 := inferInstance
  have hq : Nat.card Fq % 3 = 2 := by
    rw [GaloisField.card 2 n hn.pos.ne']
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
  obtain ⟨α, -, hαk⟩ := exists_hom_sl3_of_odd hn e
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
  have hNUP' := Res4.normalizer_le_of_isMaxParabolic hP'par U hUP'
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
    have h01 : (0 : Fin 3) ≠ 1 := by decide +revert
    obtain ⟨w, hw⟩ := hφs (Matrix.SpecialLinearGroup.transvection h01 (1 : Fq))
    have hw1 : φ w = 1 := by
      have := hKO w.2
      obtain ⟨w', hw', hww'⟩ := this
      have hw'' : w' = w := Subtype.ext hww'
      rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, ← hw'',
        (QuotientGroup.eq_one_iff _).mpr (by assumption),
        MulEquiv.coe_toMonoidHom, map_one]
    rw [hw1] at hw
    have h2' := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 3) Fq =>
      (B : Matrix (Fin 3) (Fin 3) Fq) 0 1) hw
    simp [Matrix.SpecialLinearGroup.transvection_coe] at h2'
  have hcne : c ≠ 1 := fun h => hc1 (by
    have : (⟨c, hcK⟩ : ↥(kTwenty M c)) = 1 := Subtype.ext h
    rw [this, map_one])
  have hcY : φ ⟨c, hcK⟩ ∈ Y :=
    ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.mpr (self_mem_normalClosureIn _ c), rfl⟩
  have hc3' : φ ⟨c, hcK⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcK⟩ : ↥(kTwenty M c)) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hmul := exists_mem_mul_normalizer_of_isMaxParabolic hq hP'par U hUP' hYP' hP'Y hcY hc3'
    hc1
  have hQK : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ Subgroup.normalizer (kTwenty M c : Set G) :=
    hQT.trans hTK
  have hTfac : ∀ t ∈ T, ∃ a ∈ T ⊓ kTwenty M c, ∃ q ∈ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T),
      t = a * q := by
    intro t ht
    have htKQ : t ∈ kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) := by
      rw [hLQ]
      exact Subgroup.mem_sup_right ht
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hQK] at htKQ
    obtain ⟨a, ha, q, hq', rfl⟩ := Set.mem_mul.mp htKQ
    have haT : a ∈ T := by
      have : a = (a * q) * q⁻¹ := by group
      rw [this]
      exact T.mul_mem ht (T.inv_mem (hQT hq'))
    exact ⟨a, ⟨haT, ha⟩, q, hq', rfl⟩
  have hkT : ∀ k : ↥(kTwenty M c), φ k ∈ Subgroup.normalizer
      ((U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq)) :
        Set (Matrix.SpecialLinearGroup (Fin 3) Fq)) →
        (k : G) ∈ Subgroup.normalizer (T : Set G) := by
    intro k hg
    have hkR : ∀ t ∈ T ⊓ kTwenty M c, (k : G) * t * (k : G)⁻¹ ∈ T ⊓ kTwenty M c := by
      intro t ht
      have htU : φ ⟨t, ht.2⟩ ∈ (U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq)) := by
        rw [hUcoe]
        exact ⟨⟨t, ht.2⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      have hconj := (Subgroup.mem_normalizer_iff.mp hg _).mp htU
      rw [hUcoe] at hconj
      obtain ⟨t', ht'0, ht'eq⟩ := hconj
      have ht' : ((t' : ↥(kTwenty M c)) : G) ∈ T ⊓ kTwenty M c := ht'0
      have hker : φ (t'⁻¹ * (k * ⟨t, ht.2⟩ * k⁻¹)) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, map_inv (f := φ) k, ht'eq, inv_mul_cancel]
      have hO := hφk _ hker
      have heq : (k : G) * t * (k : G)⁻¹ =
          (t' : G) * ((t'⁻¹ * (k * ⟨t, ht.2⟩ * k⁻¹) : ↥(kTwenty M c)) : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [heq]
      exact ⟨T.mul_mem ht'.1 (hOT hO), (kTwenty M c).mul_mem ht'.2 (hOK hO)⟩
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨a, ha, q, hq', rfl⟩ := hTfac t ht
    have h2q : (k : G) * q * (k : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left k.2)) q).mp
        hq'
    show (k : G) * (a * q) * (k : G)⁻¹ ∈ T
    rw [show (k : G) * (a * q) * (k : G)⁻¹ =
      ((k : G) * a * (k : G)⁻¹) * ((k : G) * q * (k : G)⁻¹) by group]
    exact T.mul_mem (hkR a ha).1 (hQT h2q)
  have hkN : ∀ k : ↥(kTwenty M c), φ k ∈ P' → (k : G) ∈ N := by
    intro k hk
    obtain ⟨y, hy, hyk⟩ := hk
    have hy' : ((y : ↥(kTwenty M c)) : G) ∈ kTwenty M c ⊓ N := hy
    have hker : φ (y⁻¹ * k) = 1 := by rw [map_mul, map_inv, hyk, inv_mul_cancel]
    have hO := hφk _ hker
    have : (k : G) = (y : G) * ((y⁻¹ * k : ↥(kTwenty M c)) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [this]
    exact N.mul_mem hy'.2 (hTN (hOT hO))
  set X' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq) :=
    ((kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G)).subgroupOf (kTwenty M c)).map φ
    with hX'
  have hnorm : Subgroup.normalizer ((U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq)) :
      Set (Matrix.SpecialLinearGroup (Fin 3) Fq)) ≤
      Subgroup.normalizer (X' : Set (Matrix.SpecialLinearGroup (Fin 3) Fq)) := by
    intro g hg
    obtain ⟨k, rfl⟩ := hφs g
    have hkZ : (k : G) ∈ Subgroup.normalizer (zTwenty T : Set G) :=
      normalizer_le_normalizer_fourChar T 0 (hkT k hg)
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hx' : ((x : ↥(kTwenty M c)) : G) ∈
        kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) := hx
    refine ⟨k * x * k⁻¹, ?_, ?_⟩
    · show ((k * x * k⁻¹ : ↥(kTwenty M c)) : G) ∈
        kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact ⟨(kTwenty M c).mul_mem ((kTwenty M c).mul_mem k.2 x.2) ((kTwenty M c).inv_mem k.2),
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer_of_mem hkZ) _).mp hx'.2⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  have hXP : ¬ X' ≤ P' := by
    intro hle
    apply hCK
    intro x hx
    exact hkN ⟨x, hx.1⟩ (hle ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)
  have hXtop : X' ≠ ⊤ := by
    intro hXtop
    have hKZ : kTwenty M c ≤ Subgroup.centralizer (zTwenty T : Set G) := by
      intro k hk
      have hmem : φ ⟨k, hk⟩ ∈ X' := by
        rw [hXtop]
        exact Subgroup.mem_top _
      obtain ⟨x, hx, hxk⟩ := hmem
      have hx' : ((x : ↥(kTwenty M c)) : G) ∈
          kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) := hx
      have hker : φ (x⁻¹ * ⟨k, hk⟩) = 1 := by
        rw [map_mul, map_inv, hxk, inv_mul_cancel]
      have hO := hφk _ hker
      have : k = (x : G) * ((x⁻¹ * ⟨k, hk⟩ : ↥(kTwenty M c)) : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [this]
      exact Subgroup.mul_mem _ hx'.2 (hTZ (hOT hO))
    have hT2 : IsPGroup 2 T := hT.sylow.isPGroup
    have hT1 : T ≠ ⊥ := by
      intro hbot
      have := pCoreOf_le_of_isSylowOf hT.sylow
      rw [hbot, le_bot_iff] at this
      exact pCoreOf_ne_bot_of_isMaximalTwoLocal hT.mem_scriptM.1 this
    have : (CFSG.omegaOneCenter (⊤ : Subgroup T)).Characteristic :=
      omegaOneCenter_top_characteristic
    refine h2 (CFSG.omegaOneCenter (⊤ : Subgroup T)) this ?_ ?_
    · intro hbot
      apply omegaZOf_ne_bot hT2 hT1
      rw [Sec3.omegaZOf, hbot, Subgroup.map_bot]
    · refine sup_le (hKZ.trans (Subgroup.centralizer_le_normalizer _)) ?_
      exact Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  obtain ⟨⟨xb, hxbX, hxb3, hxb1⟩, hnotP⟩ :=
    Res4.exists_and_not_mem_of_borel hn hP'par U hUP' hnorm hXP hXtop
  obtain ⟨k, hk, rfl⟩ := hxbX
  have hkZ : ((k : ↥(kTwenty M c)) : G) ∈
      kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) := hk
  have hk3O : ((k : ↥(kTwenty M c)) : G) ^ 3 ∈ CFSG.Open.pCoreOf 2 (kTwenty M c) := by
    have := hφk (k ^ 3) (by rw [map_pow, hxb3])
    simpa using this
  obtain ⟨j, hj⟩ := hO2 ⟨_, hk3O⟩
  have hj' : (((k : ↥(kTwenty M c)) : G) ^ 3) ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  set k' : G := ((k : ↥(kTwenty M c)) : G) ^ 2 ^ j with hk'def
  have hk'3 : k' ^ 3 = 1 := by
    rw [hk'def, ← pow_mul, mul_comm, pow_mul, hj']
  have hk'Z : k' ∈ kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) :=
    Subgroup.pow_mem _ hkZ _
  have hk'1 : k' ≠ 1 := by
    intro h
    have h1 : φ (k ^ 2 ^ j) = 1 := by
      have : k ^ 2 ^ j = 1 := Subtype.ext (by simpa [hk'def] using h)
      rw [this, map_one]
    rw [map_pow] at h1
    have hord : orderOf (φ k) = 3 := orderOf_eq_prime hxb3 hxb1
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hdvd
    exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by norm_num)
  obtain ⟨k₀, hk₀K, hk'k₀⟩ := exists_mem_zpowers_conj hq α hαk hO2 le_rfl hcK hk'Z.1 hc3 hk'3
    hcne
  have hcz : k₀ * c * k₀⁻¹ ∈ Subgroup.centralizer (zTwenty T : Set G) := by
    have hle : Subgroup.zpowers k' ≤ Subgroup.zpowers (k₀ * c * k₀⁻¹) :=
      Subgroup.zpowers_le.mpr hk'k₀
    have hck : (k₀ * c * k₀⁻¹) ^ 3 = 1 := by rw [conj_pow, hc3]; group
    have hck1 : k₀ * c * k₀⁻¹ ≠ 1 := by
      intro h
      apply hcne
      have : c = k₀⁻¹ * (k₀ * c * k₀⁻¹) * k₀ := by group
      rw [this, h]
      group
    have heq : Subgroup.zpowers k' = Subgroup.zpowers (k₀ * c * k₀⁻¹) :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hk'3 hk'1,
          orderOf_eq_prime hck hck1])
    have hmem : k₀ * c * k₀⁻¹ ∈ Subgroup.zpowers k' := heq ▸ Subgroup.mem_zpowers _
    exact (Subgroup.zpowers_le.mpr hk'Z.2) hmem
  set B := A ⊓ L with hBdef
  set D := CFSG.Open.pCoreOf 2 (kTwenty M c) with hDdef
  have hKB : ∀ k ∈ kTwenty M c, ∀ b ∈ B, ⁅k, b⁆ ∈ D := fun k hk b hb =>
    commutator_mem_pCoreOf_core hT hBn hKC ⟨n, hn, ⟨e⟩⟩ hk hb
  have hBD : B ≤ Subgroup.normalizer (D : Set G) :=
    (inf_le_left.trans hAM).trans
      (hMK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
  have hB3 : IsPGroup 3 B := fun b => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hT.mem_partTwoE.1.2 b b.2.1)⟩
  have hD3 : ¬ 3 ∣ Nat.card D := by
    obtain ⟨k, hk⟩ := hO2.exists_card_eq
    rw [hk]
    exact fun h => absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hBsyl : CFSG.ABGLocalTools.IsSylowOf 3 B (B ⊔ D) := isSylowOf_sup_of_coprime hB3 hD3 hBD
  have hB'le : B.map (MulAut.conj k₀).toMonoidHom ≤ B ⊔ D := by
    rintro _ ⟨b, hb, rfl⟩
    have e1 : (MulAut.conj k₀).toMonoidHom b = ⁅k₀, b⁆ * b := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hKB k₀ hk₀K b hb))
      (Subgroup.mem_sup_left hb)
  have hB'syl : CFSG.ABGLocalTools.IsSylowOf 3 (B.map (MulAut.conj k₀).toMonoidHom) (B ⊔ D) :=
    CFSG.ABGLocalTools.isSylowOf_of_card hB'le (by
      rw [Subgroup.card_map_of_injective (MulAut.conj k₀).injective, hBsyl.card_eq])
  obtain ⟨r, hr, hrB⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hBsyl hB'syl
  have hr' : r ∈ (D : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left D B hBD, sup_comm]
    exact hr
  obtain ⟨u, hu, b₀, hb₀, rfl⟩ := hr'
  have hb₀B : B.map (MulAut.conj b₀).toMonoidHom = B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hb₀)
  set x := u⁻¹ * k₀ with hxdef
  have hxK : x ∈ kTwenty M c := (kTwenty M c).mul_mem ((kTwenty M c).inv_mem (hOK hu)) hk₀K
  have hxB : x ∈ Subgroup.normalizer (B : Set G) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    show B.map (MulAut.conj x).toMonoidHom = B
    have e1 : (MulAut.conj x).toMonoidHom =
        (MulAut.conj u⁻¹).toMonoidHom.comp (MulAut.conj k₀).toMonoidHom := by
      ext y
      simp only [hxdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have e2 : (MulAut.conj (u * b₀)).toMonoidHom =
        (MulAut.conj u).toMonoidHom.comp (MulAut.conj b₀).toMonoidHom := by
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e1, ← Subgroup.map_map, hrB, e2, ← Subgroup.map_map, hb₀B, Subgroup.map_map]
    have e3 : (MulAut.conj u⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom = MonoidHom.id G := by
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [e3, Subgroup.map_id]
  set c' := x * c * x⁻¹ with hc'def
  have hc'Z : c' ∈ Subgroup.centralizer (zTwenty T : Set G) := by
    have huZ : u ∈ Subgroup.centralizer (zTwenty T : Set G) := hTZ (hOT hu)
    have e1 : c' = u⁻¹ * (k₀ * c * k₀⁻¹) * u := by
      rw [hc'def, hxdef]
      group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ huZ) hcz) huZ
  have hc'K : c' ∈ kTwenty M c := (kTwenty M c).mul_mem ((kTwenty M c).mul_mem hxK hcK)
    ((kTwenty M c).inv_mem hxK)
  set F := fTwenty M N c T with hFdef
  have hZF : Subgroup.centralizer (zTwenty T : Set G) ≤ Subgroup.centralizer (F : Set G) :=
    Subgroup.centralizer_le (fun z hz => hz.1)
  have hc'F : c' ∈ Subgroup.centralizer (F : Set G) := hZF hc'Z
  refine ⟨x, hxK, hxB, hc'F, ?_⟩
  set I := iTwenty M N c with hIdef
  set nc := normalClosureIn (kTwenty M c ⊓ Subgroup.centralizer (F : Set G)) c' with hncdef
  set J : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq) :=
    ((nc ⊔ I).subgroupOf (kTwenty M c)).map φ with hJ
  have hc'nc : c' ∈ nc := self_mem_normalClosureIn _ c'
  have hc'J : φ ⟨c', hc'K⟩ ∈ J :=
    ⟨⟨c', hc'K⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hc'nc), rfl⟩
  have hc'X : φ ⟨c', hc'K⟩ ∈ X' :=
    ⟨⟨c', hc'K⟩, Subgroup.mem_subgroupOf.mpr ⟨hc'K, hc'Z⟩, rfl⟩
  have hc'3 : c' ^ 3 = 1 := by rw [hc'def, conj_pow, hc3]; group
  have hc'3' : φ ⟨c', hc'K⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c', hc'K⟩ : ↥(kTwenty M c)) ^ 3 = 1 := Subtype.ext (by simpa using hc'3)
    rw [this, map_one]
  have hc'1 : φ ⟨c', hc'K⟩ ≠ 1 := by
    intro h
    have hO := hφk _ h
    apply hcne
    have hc'e : c' = 1 := Res4.eq_one_of_mem_of_isPGroup_two hO2 hO hc'3
    have : c = x⁻¹ * c' * x := by rw [hc'def]; group
    rw [this, hc'e]
    group
  have hc'P : φ ⟨c', hc'K⟩ ∉ P' := hnotP _ hc'X hc'3' hc'1
  have hYJ : Y ≤ J := by
    refine Subgroup.map_mono fun w hw => ?_
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    exact Subgroup.mem_sup_right hw
  have hncK : nc ≤ kTwenty M c :=
    (normalClosureIn_le (show c' ∈ kTwenty M c ⊓ Subgroup.centralizer (F : Set G) from
      ⟨hc'K, hc'F⟩)).trans inf_le_left
  have hIK : I ≤ kTwenty M c := hXKN.trans inf_le_left
  have hJN : Subgroup.normalizer ((U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq)) :
      Set (Matrix.SpecialLinearGroup (Fin 3) Fq)) ≤
      Subgroup.normalizer (J : Set (Matrix.SpecialLinearGroup (Fin 3) Fq)) := by
    intro g hg
    obtain ⟨k, rfl⟩ := hφs g
    have hkTT := hkT k hg
    have hkNN : (k : G) ∈ N := hkN k (hNUP' hg)
    have hkI : (k : G) ∈ Subgroup.normalizer (I : Set G) := hKNX ⟨k.2, hkNN⟩
    have hkZ' : (k : G) ∈ Subgroup.normalizer (zTwenty T : Set G) :=
      normalizer_le_normalizer_fourChar T 0 hkTT
    have hkE : (k : G) ∈ Subgroup.normalizer ((eTwenty M N c T : Subgroup G) : Set G) :=
      mem_normalizer_commutator_of_mem hkZ' hkI
    have hkF : (k : G) ∈ Subgroup.normalizer (F : Set G) := mem_normalizer_inf_of_mem hkZ' hkE
    have hkCF : (k : G) ∈ Subgroup.normalizer
        ((kTwenty M c ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_inf_of_mem (Subgroup.le_normalizer k.2)
        (mem_normalizer_centralizer_of_mem hkF)
    have hKCFnc : kTwenty M c ⊓ Subgroup.centralizer (F : Set G) ≤
        Subgroup.normalizer (nc : Set G) := le_normalizer_normalClosureIn _ c'
    have hknc : (k : G) ∈ Subgroup.normalizer (nc : Set G) := by
      apply mem_normalizer_of_map_conj_le
      rw [hncdef, normalClosureIn, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      have hm' : (k : G) * m * (k : G)⁻¹ ∈ kTwenty M c ⊓ Subgroup.centralizer (F : Set G) :=
        (Subgroup.mem_normalizer_iff.mp hkCF m).mp hm
      have hkc' : (k : G) * c' * (k : G)⁻¹ ∈ kTwenty M c ⊓ Subgroup.centralizer (F : Set G) :=
        (Subgroup.mem_normalizer_iff.mp hkCF c').mp ⟨hc'K, hc'F⟩
      obtain ⟨y, hy, hyc⟩ := exists_mem_zpowers_conj hq α hαk hO2 inf_le_left ⟨hc'K, hc'F⟩ hkc'
        hc'3 (by rw [conj_pow, hc'3]; group)
        (fun h => hc'1 (by
          have : (⟨c', hc'K⟩ : ↥(kTwenty M c)) = 1 := Subtype.ext h
          rw [this, map_one]))
      have hyc' : y * c' * y⁻¹ ∈ nc := Subgroup.subset_closure ⟨y, hy, rfl⟩
      have h1 : (k : G) * c' * (k : G)⁻¹ ∈ nc := (Subgroup.zpowers_le.mpr hyc') hyc
      show (k : G) * (m * c' * m⁻¹) * (k : G)⁻¹ ∈ nc
      rw [show (k : G) * (m * c' * m⁻¹) * (k : G)⁻¹ = ((k : G) * m * (k : G)⁻¹) *
        ((k : G) * c' * (k : G)⁻¹) * ((k : G) * m * (k : G)⁻¹)⁻¹ by group]
      exact (Subgroup.mem_normalizer_iff.mp (hKCFnc hm') _).mp h1
    have hkK0 : (k : G) ∈ Subgroup.normalizer ((nc ⊔ I : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hknc, hkI⟩
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hw' : ((w : ↥(kTwenty M c)) : G) ∈ nc ⊔ I := hw
    refine ⟨k * w * k⁻¹, ?_, ?_⟩
    · show ((k * w * k⁻¹ : ↥(kTwenty M c)) : G) ∈ nc ⊔ I
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp hkK0 _).mp hw'
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  have hP'le : P' ≤ J ⊔ Subgroup.normalizer
      ((U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq)) :
        Set (Matrix.SpecialLinearGroup (Fin 3) Fq)) := by
    intro p hp
    obtain ⟨y', hy', hyb⟩ := hmul p hp
    rw [show p = y' * (y'⁻¹ * p) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hYJ hy')) (Subgroup.mem_sup_right hyb)
  have hJtop' : J ⊔ Subgroup.normalizer ((U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq)) :
      Set (Matrix.SpecialLinearGroup (Fin 3) Fq)) = ⊤ := by
    rcases hP'par.1.le_iff.mp hP'le with h | h
    · exact h
    · exact absurd (h ▸ Subgroup.mem_sup_left hc'J) hc'P
  have hJn : J.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hJtop']
    exact sup_le Subgroup.le_normalizer hJN
  have hsimple := isSimpleGroup_sl3_of_odd hn
  have hJtop : J = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal J with h | h
    · exact absurd (h ▸ hc'J : φ ⟨c', hc'K⟩ ∈ (⊥ : Subgroup _)) hc'1
    · exact h
  intro k hk
  have hmem : φ ⟨k, hk⟩ ∈ J := by
    rw [hJtop]
    exact Subgroup.mem_top _
  obtain ⟨w, hw, hwk⟩ := hmem
  have hw' : ((w : ↥(kTwenty M c)) : G) ∈ nc ⊔ I := hw
  have hker : φ (w⁻¹ * ⟨k, hk⟩) = 1 := by
    rw [map_mul, map_inv, hwk, inv_mul_cancel]
  have hO := hφk _ hker
  have : k = (w : G) * ((w⁻¹ * ⟨k, hk⟩ : ↥(kTwenty M c)) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw') (Subgroup.mem_sup_right hO)

theorem step207Struct_of (h2031 : Item203One1) (h204 : Item204One) (h2051 : Step2051)
    (h2053 : Step2053) (h189 : Sec18.Item189) (h321 : Sec3.Item321Split) : Step207Struct := by
  intro G _ _ A M L N c T hT hTN hCK _ _
  obtain ⟨H, hH18, hH187, hL, hN⟩ := exists_sec18H_of_ctx20One hT
  obtain ⟨⟨hKC, -⟩, -, hcase⟩ := h189 G A M H c hH18 hH187
  rw [← hL, ← hN] at hcase
  have h1 := h2051 G A M L N c T hT
  exact step207Struct_core h321 hT.toCtx20 hN (le_normalizer_of_hyp201One hT.hyp201One) hKC
    hcase (h2031 G A M L N c hT.hyp201One) (h204 G A M L N c T hT) h1
    (h2053 G A M L N c T hT (rank3II_20_5_2_of h204 hT h1)) hTN hCK

end CFSG.RankThree.PartTwo.Sec20
