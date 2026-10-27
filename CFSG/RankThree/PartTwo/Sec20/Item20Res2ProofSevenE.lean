module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofSeven
public import CFSG.RankThree.PartTwo.Sec20.Item20ResProofXActs
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec20.OneStepsProofV

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

theorem isSimpleGroup_sl3_of_odd {n : ℕ} (hn : Odd n) :
    IsSimpleGroup (SpecialLinearGroup (Fin 3) (GaloisField 2 n)) := by
  have hPSL : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 n)) :=
    (CFSG.LinearGroups.linear_projective_simple (K := GaloisField 2 n) (n := 3) (by norm_num)
      (Or.inl le_rfl)).2.1
  have hcen : Subgroup.center (SpecialLinearGroup (Fin 3) (GaloisField 2 n)) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    have hr1 : r = 1 := eq_one_of_pow_three_eq_one hn hr
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hrA, hr1, map_one]
    rfl
  exact (MulEquiv.isSimpleGroup_congr
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot)).mp hPSL

variable {G : Type} [Group G] [Finite G]

theorem step207E_core (h321 : Sec3.Item321Split) {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hKC : kTwenty M c ∈ oTwoComponentsIn M)
    (hK : KType20 M N c) (h204 : scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M})
    (h1 : ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (h3 : KIsL3 M c) (hTN : T ≤ N)
    (hne : ¬ kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N) :
    ⁅zTwenty T, normalClosureIn (kTwenty M c ⊓ N) c⁆ ≠ ⊥ := by
  intro hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := rank3II_20_5_2_core hT h204 h1
  have hLQ := sup_pCoreOf_eq_core h321 hT hKC h2 h3
  have hpar := KType20.isMaxParabolic hK h3
  obtain ⟨n, hn, ⟨e⟩⟩ := h3
  have hIZ : normalClosureIn (kTwenty M c ⊓ N) c ≤ Subgroup.centralizer (zTwenty T : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hE)
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
  have hOK : CFSG.Open.pCoreOf 2 (kTwenty M c) ≤ kTwenty M c :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
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
  have hφk' : ∀ w : ↥(kTwenty M c), (w : G) ∈ CFSG.Open.pCoreOf 2 (kTwenty M c) → φ w = 1 := by
    intro w hwO
    obtain ⟨w', hw', hww'⟩ := hwO
    have hw'' : w' = w := Subtype.ext hww'
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, ← hw'',
      (QuotientGroup.eq_one_iff _).mpr (by assumption), MulEquiv.coe_toMonoidHom,
      map_one]
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
    rw [hφk' w (hKO w.2)] at hw
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
  set X' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq) :=
    ((kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G)).subgroupOf (kTwenty M c)).map φ
    with hX'
  have hYX : Y ≤ X' := by
    refine Subgroup.map_mono fun w hw => ?_
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    exact ⟨w.2, hIZ hw⟩
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
  have hnorm : Subgroup.normalizer ((U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq)) :
      Set (Matrix.SpecialLinearGroup (Fin 3) Fq)) ≤
      Subgroup.normalizer (X' : Set (Matrix.SpecialLinearGroup (Fin 3) Fq)) := by
    intro g hg
    obtain ⟨k, rfl⟩ := hφs g
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
    have hkT : (k : G) ∈ Subgroup.normalizer (T : Set G) := by
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
    have hkZ : (k : G) ∈ Subgroup.normalizer (zTwenty T : Set G) :=
      normalizer_le_normalizer_fourChar T 0 hkT
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hx' : ((x : ↥(kTwenty M c)) : G) ∈
        kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) := hx
    refine ⟨k * x * k⁻¹, ?_, ?_⟩
    · show ((k * x * k⁻¹ : ↥(kTwenty M c)) : G) ∈
        kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      refine ⟨(kTwenty M c).mul_mem ((kTwenty M c).mul_mem k.2 x.2) ((kTwenty M c).inv_mem k.2),
        Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      have hz' : (k : G)⁻¹ * z * (k : G) ∈ zTwenty T := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkZ) z).mp hz
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp hx'.2 _ hz'
      calc z * ((k : G) * x * (k : G)⁻¹) =
          (k : G) * (((k : G)⁻¹ * z * (k : G)) * x) * (k : G)⁻¹ := by group
        _ = (k : G) * (x * ((k : G)⁻¹ * z * (k : G))) * (k : G)⁻¹ := by rw [hc]
        _ = (k : G) * x * (k : G)⁻¹ * z := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  have hXP : ¬ X' ≤ P' := by
    intro hle
    apply hne
    intro x hx
    have hφx : φ ⟨x, hx.1⟩ ∈ P' := hle ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hφx
    have hy' : ((y : ↥(kTwenty M c)) : G) ∈ kTwenty M c ⊓ N := hy
    have hker : φ (y⁻¹ * ⟨x, hx.1⟩) = 1 := by
      rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have hO := hφk _ hker
    have : x = (y : G) * ((y⁻¹ * ⟨x, hx.1⟩ : ↥(kTwenty M c)) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [this]
    exact N.mul_mem hy'.2 (hTN (hOT hO))
  have hP'S : P' ≤ X' ⊔ Subgroup.normalizer ((U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq)) :
      Set (Matrix.SpecialLinearGroup (Fin 3) Fq)) := by
    intro p hp
    obtain ⟨y', hy', hyb⟩ := hmul p hp
    rw [show p = y' * (y'⁻¹ * p) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hYX hy')) (Subgroup.mem_sup_right hyb)
  have hStop : X' ⊔ Subgroup.normalizer ((U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Fq)) :
      Set (Matrix.SpecialLinearGroup (Fin 3) Fq)) = ⊤ := by
    rcases hP'par.1.le_iff.mp hP'S with h | h
    · exact h
    · exact absurd (le_sup_left.trans h.le) hXP
  have hXn : X'.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hStop]
    exact sup_le Subgroup.le_normalizer hnorm
  have hsimple := isSimpleGroup_sl3_of_odd hn
  have hXtop : X' = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X' with h | h
    · exact absurd (h ▸ hYX hcY : φ ⟨c, hcK⟩ ∈ (⊥ : Subgroup _)) hc1
    · exact h
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

theorem step207E_of (h204 : Item204One) (h2051 : Step2051) (h2053 : Step2053)
    (h189 : Sec18.Item189) (h321 : Sec3.Item321Split) : Step207E := by
  intro G _ _ A M L N c T hT hTN hne
  obtain ⟨H, hH18, hH187, hL, hN⟩ := exists_sec18H_of_ctx20One hT
  obtain ⟨⟨hKC, -⟩, -, hcase⟩ := h189 G A M H c hH18 hH187
  rw [← hL, ← hN] at hcase
  have h1 := h2051 G A M L N c T hT
  exact step207E_core h321 hT.toCtx20 hN (le_normalizer_of_hyp201One hT.hyp201One) hKC hcase
    (h204 G A M L N c T hT) h1 (h2053 G A M L N c T hT (rank3II_20_5_2_of h204 hT h1)) hTN hne

end CFSG.RankThree.PartTwo.Sec20
