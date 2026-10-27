module

public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofImg
import CFSG.RankThree.PartTwo.KFacts.K72SLPiInndiag
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTenTools
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofPGL
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec5.Items52
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Steps

@[expose] def Step148RankImgLeEq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      e ∈ A → ∀ J : Subgroup G, J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Eq A Y K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) →
        letI := ker148_normal hY.2
        img148 A Y (deltaZero A (lB A) Y) ≤ img148 A Y J

end Steps

namespace Item148Res4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

theorem exists_pow_cube_eq_of_coprime {M : Type*} [Monoid M] {x : M}
    (h : Nat.Coprime 3 (orderOf x)) : ∃ k : ℕ, (x ^ k) ^ 3 = x := by
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime h
  exact ⟨k, by rw [← pow_mul, mul_comm, pow_mul, hk]⟩

theorem isInnerAut_of_mem_linearAutGroup_of_coprime {K : Type} [Field K]
    {σ : MulAut (projectiveSL 3 K)} (hσ : σ ∈ linearAutGroup 3 K)
    (hcop : Nat.Coprime 3 (orderOf σ)) : IsInnerAut σ := by
  rw [linearAutGroup_eq_range] at hσ
  obtain ⟨A, rfl⟩ := hσ
  obtain ⟨k, hk⟩ := exists_pow_cube_eq_of_coprime hcop
  rw [← hk, ← map_pow, ← map_pow]
  exact Item148Rank.isInnerAut_conjAut_of_det_eq_cube148 _
    (u := Matrix.GeneralLinearGroup.det (A ^ k)) (map_pow _ _ _).symm

theorem det_pow_succ_eq_one {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    (A : unitaryIsom3 h) :
    Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K) ^ (p ^ f + 1) = 1 := by
  have hA := mem_unitaryIsom3.mp A.2
  have h1 := congrArg Matrix.det hA
  have hbar : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar).det =
      h.bar ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det :=
    (RingHom.map_det h.bar _).symm
  rw [Matrix.det_mul, Matrix.det_transpose, hbar, Matrix.det_one,
    UnitaryFieldData.bar_apply] at h1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ]
  exact h1

theorem isInnerAut_of_mem_psuConj_range_of_coprime {p f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData p f K} {σ : MulAut (unitaryPSU h 3)} (hσ : σ ∈ (psuConj h).range)
    (hcop : Nat.Coprime 3 (orderOf σ)) : IsInnerAut σ := by
  obtain ⟨A, rfl⟩ := hσ
  obtain ⟨k, hk⟩ := exists_pow_cube_eq_of_coprime hcop
  rw [← hk, ← map_pow, ← map_pow]
  refine Item148Rank.isInnerAut_psuConj_of_det_eq_cube148 _
    (u := Matrix.GeneralLinearGroup.det ((A ^ k : unitaryIsom3 h) : GL (Fin 3) K)) ?_
    (det_pow_succ_eq_one _)
  rw [← map_pow]
  rfl

theorem isInnerAut_of_mem_commutator_of_coprime {X : Type} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (hX : Sec4.IsoLThreePi X 2 m) {σ : MulAut X} (hσ : σ ∈ commutator (MulAut X))
    (hcop : Nat.Coprime 3 (orderOf σ)) : IsInnerAut σ := by
  have hcomm : ∀ {M : Type} [Group M] (τ : X ≃* M),
      MulAut.congr τ σ ∈ commutator (MulAut M) := by
    intro M _ τ
    have h1 : MulAut.congr τ σ ∈ (commutator (MulAut X)).map (MulAut.congr τ).toMonoidHom :=
      ⟨σ, hσ, rfl⟩
    rw [commutator_def, Subgroup.map_commutator] at h1
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top h1
  have hord : ∀ {M : Type} [Group M] (τ : X ≃* M), orderOf (MulAut.congr τ σ) = orderOf σ :=
    fun τ => orderOf_injective (MulAut.congr τ).toMonoidHom (MulAut.congr τ).injective σ
  rcases hX with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  · obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 (GaloisField 2 m)
    set τ : X ≃* projectiveSL 3 (GaloisField 2 m) := e.trans φ with hτ
    have hD : MulAut.congr τ σ ∈ linearAutGroup 3 (GaloisField 2 m) :=
      commutator_le_linearAutGroup (hcomm τ)
    exact (isInnerAut_congr τ σ).mp
      (isInnerAut_of_mem_linearAutGroup_of_coprime hD (by rw [hord τ]; exact hcop))
  · have h : UnitaryFieldData 2 m (GaloisField 2 (2 * m)) :=
      ⟨Nat.prime_two, by omega, GaloisField.card 2 (2 * m) (by omega)⟩
    obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
    set τ : X ≃* unitaryPSU h 3 := e.trans φ.symm with hτ
    have hq2 : 2 < 2 ^ m := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hD : MulAut.congr τ σ ∈ (psuConj h).range :=
      commutator_le_psuConj_range h hq2 (hcomm τ)
    exact (isInnerAut_congr τ σ).mp
      (isInnerAut_of_mem_psuConj_range_of_coprime hD (by rw [hord τ]; exact hcop))

theorem le_of_le_commutator_of_isoLThreePi {Γ : Type} [Group Γ] [Finite Γ]
    {X R T : Subgroup Γ} {m : ℕ} (hm : 2 ≤ m) (hX : Sec4.IsoLThreePi ↥X 2 m)
    (hRX : R ≤ Subgroup.normalizer (X : Set Γ)) (hTX : T ≤ Subgroup.normalizer (X : Set Γ))
    (hRT : R ≤ ⁅R, T⁆) (hR : Nat.Coprime 3 (Nat.card R))
    (hC : ∀ g ∈ R ⊔ X, g ∈ Subgroup.centralizer (X : Set Γ) → g = 1) : R ≤ X := by
  set N := Subgroup.normalizer (X : Set Γ) with hN
  set ρ := X.normalizerMonoidHom with hρ
  set S : Subgroup Γ := ((commutator (MulAut ↥X)).comap ρ).map N.subtype with hS
  have hRS : R ≤ S := by
    refine hRT.trans ?_
    rw [Subgroup.commutator_le]
    intro r hr t ht
    refine ⟨⟨r, hRX hr⟩ * ⟨t, hTX ht⟩ * (⟨r, hRX hr⟩)⁻¹ * (⟨t, hTX ht⟩)⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_mul, map_inv, map_inv,
      ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  intro r hr
  obtain ⟨n, hn, hnr⟩ := hRS hr
  have hcop : Nat.Coprime 3 (orderOf (ρ n)) := by
    refine Nat.Coprime.coprime_dvd_right ?_ hR
    refine (orderOf_map_dvd ρ n).trans ?_
    rw [← Subgroup.orderOf_coe]
    have hnr' : (n : Γ) = r := hnr
    rw [hnr']
    exact Subgroup.orderOf_dvd_natCard R hr
  obtain ⟨x, hx⟩ := isInnerAut_of_mem_commutator_of_coprime hm hX hn hcop
  have hxN : (x : Γ) ∈ N := Subgroup.le_normalizer x.2
  have hρx : ρ ⟨x, hxN⟩ = MulAut.conj x := MulEquiv.ext fun y => Subtype.ext rfl
  have hker : (⟨x, hxN⟩ : N)⁻¹ * n ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρx, hx, inv_mul_cancel]
  rw [hρ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
  have hxr : (x : Γ)⁻¹ * r ∈ Subgroup.centralizer (X : Set Γ) := by
    have h1 : (((⟨x, hxN⟩ : N)⁻¹ * n : N) : Γ) = (x : Γ)⁻¹ * r := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact congrArg _ hnr
    rw [← h1]
    exact hker
  have h1 := hC _ ((R ⊔ X).mul_mem ((R ⊔ X).inv_mem (Subgroup.mem_sup_right x.2))
    (Subgroup.mem_sup_left hr)) hxr
  rw [inv_mul_eq_one] at h1
  rw [← h1]
  exact x.2

section Quot

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_pPrimeCoreOf_of_ne {Y J J' : Subgroup G} (hJ : J ∈ thetaComponentsIn Y)
    (hJ' : J' ∈ thetaComponentsIn Y) (hne : J ≠ J') : ⁅J, J'⁆ ≤ pPrimeCoreOf 3 Y := by
  obtain ⟨K₁, hK₁, rfl⟩ := hJ
  obtain ⟨K₂, hK₂, rfl⟩ := hJ'
  have hne' : K₁ ≠ K₂ := fun h => hne (by rw [h])
  refine le_trans ?_ (inSubgroup_theta_le_pPrimeCoreOf Y)
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono (Sec6.commutator_le_theta_of_ne hK₁ hK₂ hne')

omit [Finite G] in
theorem exists_ne_one_mem_inf148 {A J : Subgroup G} {e : G} (he3 : e ^ 3 = 1)
    (h27 : Nat.card A = 27) (hA : A = Subgroup.zpowers e ⊔ (A ⊓ J)) :
    ∃ b ∈ A ⊓ J, b ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : A ⊓ J = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
  rw [hbot, sup_bot_eq] at hA
  have h3 : Nat.card (Subgroup.zpowers e) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one he3)
  rw [← hA] at h3
  omega

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem img148_deltaZero_le {LB : Subgroup G → Subgroup G}
    {T : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (h : ∀ Q ∈ collectionIn (scriptQZero A LB) Y, img148 A Y Q ≤ T) :
    img148 A Y (deltaZero A LB Y) ≤ T := by
  set T' : Subgroup G := (T.comap (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype
    with hT'
  have hle : deltaZero A LB Y ≤ T' := by
    refine sSup_le fun Q hQ => ?_
    intro g hg
    have hgM : g ∈ Y ⊔ A := Subgroup.mem_sup_left (hQ.2 hg)
    exact ⟨⟨g, hgM⟩, h Q hQ (mem_img148_iff.mpr ⟨g, hgM, hg, rfl⟩), rfl⟩
  intro x hx
  obtain ⟨g, hgM, hgD, rfl⟩ := mem_img148_iff.mp hx
  obtain ⟨m, hm, hmg⟩ := hle hgD
  have : m = ⟨g, hgM⟩ := Subtype.ext hmg
  rw [← this]
  exact hm

theorem eq_one_of_mem_centralizer_of_pow_three (hAF : A ∈ partTwoF G)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {e : G} (he : e ∈ A) {K J : Subgroup G}
    (hKJ : K ≤ J) (hJY : J ≤ Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hsec : Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G))
    (hecent : alpha148 A Y e he ∉
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {z : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hzC : z ∈ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hzY : z ∈ img148 A Y Y) (hz3 : z ^ 3 = 1) : z = 1 := by
  by_contra hz1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C₀ : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y) :=
    Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊓ img148 A Y Y with hC₀
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAp : IsPGroup 3 ↥(img148 A Y A) := by
    refine isPGroup_three_of_pow148 fun b hb => ?_
    obtain ⟨a, ha, haA, rfl⟩ := mem_img148_iff.mp hb
    rw [← map_pow]
    have : (⟨a, ha⟩ : ↥(Y ⊔ A)) ^ 3 = 1 := Subtype.ext (by simpa using hA3 a haA)
    rw [this, map_one]
  have hAN : img148 A Y A ≤ Subgroup.normalizer (C₀ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    le_trans (le_inf ((img148_le_normalizer hAJ).trans
      (Sec5.normalizer_le_normalizer_centralizer _)) (img148_le_normalizer hAY))
      Subgroup.inf_normalizer_le_normalizer_inf
  have hz3' : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have h3C : 3 ∣ Nat.card C₀ := hz3' ▸ Subgroup.orderOf_dvd_natCard C₀ ⟨hzC, hzY⟩
  have hmod := Sec6.card_inf_centralizer_modEq hAp hAN
  have h3D : 3 ∣ Nat.card
      ↥(C₀ ⊓ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr h3C))
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h3D
  have hw' : orderOf (w : ↥(Y ⊔ A) ⧸ ker148 A Y) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hw
  have hw3 : (w : ↥(Y ⊔ A) ⧸ ker148 A Y) ^ 3 = 1 := by
    rw [← hw']
    exact pow_orderOf_eq_one _
  have hwA : (w : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y A :=
    mem_img148_of_commute hAF hAY w.2.2 hw3
  obtain ⟨a, haM, haA, hwa⟩ := mem_img148_iff.mp hwA
  have hKM : K ≤ Y ⊔ A := (hKJ.trans hJY).trans le_sup_left
  have hwa' : alpha148 A Y a haA = (w : ↥(Y ⊔ A) ⧸ ker148 A Y) := hwa
  have hac : alpha148 A Y a haA ∈
      Subgroup.centralizer (img148 A Y K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hwa']
    exact Subgroup.centralizer_le (fun x hx => img148_mono hKJ hx) w.2.1.1
  have hasec := mem_sectionCentralizer_of_alpha148 hKM haA hac
  rw [hsec] at hasec
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hasec
  have hwe : (w : ↥(Y ⊔ A) ⧸ ker148 A Y) = alpha148 A Y e he ^ i := by
    rw [← hwa', alpha148_eq_mk', alpha148_eq_mk', ← map_zpow]
    rfl
  have he3 : alpha148 A Y e he ^ 3 = 1 := alpha148_pow_three hA3 he
  have hle : Subgroup.zpowers (w : ↥(Y ⊔ A) ⧸ ker148 A Y) ≤
      Subgroup.zpowers (alpha148 A Y e he) := by
    rw [Subgroup.zpowers_le, hwe]
    exact Subgroup.zpow_mem_zpowers _ i
  have hcard : Nat.card (Subgroup.zpowers (alpha148 A Y e he)) ≤
      Nat.card (Subgroup.zpowers (w : ↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hw']
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one he3)
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  apply hecent
  have hmem : alpha148 A Y e he ∈ Subgroup.zpowers (w : ↥(Y ⊔ A) ⧸ ker148 A Y) :=
    heq ▸ Subgroup.mem_zpowers _
  exact (Subgroup.zpowers_le.mpr w.2.1.1) hmem

theorem le_normalizer_of_not_mem_centralizer148 (hAF : A ∈ partTwoF G)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {e : G} (he : e ∈ A) {K J : Subgroup G}
    (hJ : J ∈ thetaComponentsIn Y) (hKJ : K ≤ J) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hsec : Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G))
    (hecent : alpha148 A Y e he ∉
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {b : G} (hbA : b ∈ A) (hbJ : b ∈ J) (hb1 : b ≠ 1) :
    Y ≤ Subgroup.normalizer (J : Set G) := by
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  intro y hy
  by_contra hyN
  set J' := J.map (MulAut.conj y).toMonoidHom with hJ'
  have hJ'mem : J' ∈ thetaComponentsIn Y :=
    Sec15.Proof1423.map_conj_mem_thetaComponentsIn1423 (Subgroup.le_normalizer hy) hJ
  have hne : J ≠ J' := Sec6.ne_map_conj_of_not_mem_normalizer hyN
  have hcomm := commutator_le_pPrimeCoreOf_of_ne hJ hJ'mem hne
  have hyb : y * b * y⁻¹ ∈ J' := ⟨b, hbJ, rfl⟩
  have hybY : y * b * y⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hy (hJY hbJ)) (Y.inv_mem hy)
  have hybM : y * b * y⁻¹ ∈ Y ⊔ A := Subgroup.mem_sup_left hybY
  set z := QuotientGroup.mk' (ker148 A Y) ⟨y * b * y⁻¹, hybM⟩ with hz
  have hzC : z ∈ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨j, hjM, hjJ, rfl⟩ := mem_img148_iff.mp hx
    rw [hz, ← map_mul, ← map_mul, mk'_ker148_eq_iff]
    have h1 : ⁅(y * b * y⁻¹)⁻¹, j⁻¹⁆ ∈ ⁅J, J'⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (J'.inv_mem hyb) (J.inv_mem hjJ)
    have h2 : ((⟨j, hjM⟩ * ⟨y * b * y⁻¹, hybM⟩ : ↥(Y ⊔ A)) : G)⁻¹ *
        ((⟨y * b * y⁻¹, hybM⟩ * ⟨j, hjM⟩ : ↥(Y ⊔ A)) : G) = ⁅(y * b * y⁻¹)⁻¹, j⁻¹⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, commutatorElement_def]
      group
    rw [h2]
    exact hcomm h1
  have hzY : z ∈ img148 A Y Y := mem_img148_iff.mpr ⟨_, hybM, hybY, rfl⟩
  have hb3 : b ^ 3 = 1 := hAF.1.2 b hbA
  have hz3 : z ^ 3 = 1 := by
    rw [hz, ← map_pow]
    have : (⟨y * b * y⁻¹, hybM⟩ : ↥(Y ⊔ A)) ^ 3 = 1 := by
      apply Subtype.ext
      show (y * b * y⁻¹) ^ 3 = 1
      rw [← MulAut.conj_apply, ← map_pow, hb3, map_one]
    rw [this, map_one]
  have hz1 := eq_one_of_mem_centralizer_of_pow_three hAF hAY he hKJ hJY hAJ hsec hecent hzC hzY
    hz3
  rw [hz, mk'_ker148_eq_one_iff] at hz1
  have h1 : y * b * y⁻¹ = 1 := eq_one_of_pow_three_pow_eq_one148
    (coprime_card_pPrimeCoreOf 3 Y) hz1 (k := 1) (by
      rw [pow_one, ← MulAut.conj_apply, ← map_pow, hb3, map_one])
  apply hb1
  have h2 : b = y⁻¹ * (y * b * y⁻¹) * y := by group
  rw [h2, h1]
  group

theorem eq_one_of_mem_centralizer_img148 (hAF : A ∈ partTwoF G)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {e : G} (he : e ∈ A) {K J : Subgroup G}
    (hKJ : K ≤ J) (hJY : J ≤ Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hsec : Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G))
    (hecent : alpha148 A Y e he ∉
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hYJ : Y ≤ Subgroup.normalizer (J : Set G)) {z : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hzY : z ∈ img148 A Y Y)
    (hzC : z ∈ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    z = 1 := by
  set C₀ : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y) :=
    Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊓ img148 A Y Y with hC₀
  set P : Subgroup G := (C₀.comap (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype ⊓ Y
    with hP
  have hYN : img148 A Y Y ≤ Subgroup.normalizer (C₀ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    le_trans (le_inf ((img148_le_normalizer hYJ).trans
      (Sec5.normalizer_le_normalizer_centralizer _))
      (img148_le_normalizer Subgroup.le_normalizer)) Subgroup.inf_normalizer_le_normalizer_inf
  have hPY : P ≤ Y := inf_le_right
  have key : ∀ y ∈ Y, ∀ g ∈ P, y * g * y⁻¹ ∈ P := by
    intro y hy g hg
    obtain ⟨⟨m, hm, rfl⟩, hgY⟩ := hg
    have hyM : y ∈ Y ⊔ A := Subgroup.mem_sup_left hy
    refine ⟨⟨⟨y, hyM⟩ * m * (⟨y, hyM⟩ : ↥(Y ⊔ A))⁻¹, ?_, rfl⟩,
      Y.mul_mem (Y.mul_mem hy hgY) (Y.inv_mem hy)⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have hyα : QuotientGroup.mk' (ker148 A Y) ⟨y, hyM⟩ ∈ img148 A Y Y :=
      mem_img148_iff.mpr ⟨y, hyM, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hYN hyα) _).mp hm
  have hnorm : Y ≤ Subgroup.normalizer (P : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key y hy g, fun h => ?_⟩
    have h1 := key y⁻¹ (Y.inv_mem hy) _ h
    rwa [show y⁻¹ * (y * g * y⁻¹) * y⁻¹⁻¹ = g by group] at h1
  have hcop : Nat.Coprime 3 (Nat.card P) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
    obtain ⟨⟨m, hm, hmg⟩, -⟩ := g.2
    have hmg' : (m : G) = (g : G) := hmg
    have hm3 : m ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hmg', Subgroup.coe_one, ← Subgroup.coe_pow, ← hg,
        pow_orderOf_eq_one, Subgroup.coe_one]
    have hmα3 : (QuotientGroup.mk' (ker148 A Y) m) ^ 3 = 1 := by rw [← map_pow, hm3, map_one]
    have h1 := eq_one_of_mem_centralizer_of_pow_three hAF hAY he hKJ hJY hAJ hsec hecent hm.1
      hm.2 hmα3
    rw [mk'_ker148_eq_one_iff] at h1
    have h2 : (m : G) = 1 := eq_one_of_pow_three_pow_eq_one148
      (coprime_card_pPrimeCoreOf 3 Y) h1 (k := 1) (by
        rw [pow_one, ← Subgroup.coe_pow, hm3, Subgroup.coe_one])
    have h3' : (g : G) = 1 := hmg' ▸ h2
    have : g = 1 := Subtype.ext h3'
    rw [this, orderOf_one] at hg
    exact absurd hg (by norm_num)
  have hPle := le_pPrimeCoreOf hPY hnorm hcop
  obtain ⟨g, hgM, hgY, rfl⟩ := mem_img148_iff.mp hzY
  rw [mk'_ker148_eq_one_iff]
  exact hPle ⟨⟨⟨g, hgM⟩, ⟨hzC, mem_img148_iff.mpr ⟨g, hgM, hgY, rfl⟩⟩, rfl⟩, hgY⟩

end Quot

end Item148Res4

open Item148Res4

section Steps

theorem step148RankImgLe_of (hEq : Step148RankImgLeEq) : Step148RankImgLe := by
  intro G _ _ A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hA
  rcases halt with hEq' | hTen | hField
  · exact hEq G A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq' hA
  ·
    have := ker148_normal hY.2
    have hAF : A ∈ partTwoF G := hstd.mem_partTwoF
    have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
    have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
    have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
    have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) :=
      hP.2.2.2.2.2.1
    have he1 : e ≠ 1 := hP.2.2.2.2.1
    have hle : img148 A Y A ≤ img148 A Y J :=
      Item148Rank.img148_le_of_lift148Ten148 hAF hAY he hK hKJ hJY hAJ hkt.1 hTen
    obtain ⟨-, ⟨φJ⟩⟩ := hTen
    have hecent : alpha148 A Y e he ∉
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      intro hc
      have heJ : alpha148 A Y e he ∈ img148 A Y J := hle (alpha148_mem_img148 he)
      have hZ : (⟨alpha148 A Y e he, heJ⟩ : ↥(img148 A Y J)) ∈
          Subgroup.center ↥(img148 A Y J) := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc g g.2)
      have hZ' : φJ ⟨alpha148 A Y e he, heJ⟩ ∈ Subgroup.center (alternatingGroup (Fin 10)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h2 := congrArg φJ (Subgroup.mem_center_iff.mp hZ (φJ.symm g))
        rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      have h10 : 4 ≤ Nat.card (Fin 10) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num
      rw [alternatingGroup.center_eq_bot h10, Subgroup.mem_bot] at hZ'
      have h3 : alpha148 A Y e he = 1 :=
        congrArg Subtype.val (φJ.injective (hZ'.trans (map_one φJ).symm))
      have h2 : alpha148 A Y e he = alpha148 A Y 1 A.one_mem := by
        rw [h3, alpha148_eq_mk']
        exact (map_one _).symm
      exact he1 (alpha148_injective hA3 he A.one_mem h2)
    obtain ⟨b, ⟨hbA, hbJ⟩, hb1⟩ :=
      exists_ne_one_mem_inf148 (hA3 e he) hstd.toSec13Data.card_eq hA
    have hYJ :=
      le_normalizer_of_not_mem_centralizer148 hAF hAY he hJ hKJ hAJ hkt.1 hecent hbA hbJ hb1
    refine img148_deltaZero_le fun R hR => ?_
    have hRM : R ≤ Y ⊔ A := hR.2.trans le_sup_left
    have hReq : img148 A Y R = ⁅img148 A Y R, img148 A Y A⁆ := by
      conv_lhs => rw [hR.1.2]
      exact Item148PtRes.img148_commutator hRM le_sup_right
    rw [hReq, Subgroup.commutator_le]
    intro q hq a ha
    have hqN := img148_le_normalizer (hR.2.trans hYJ) hq
    rw [commutatorElement_def]
    exact (img148 A Y J).mul_mem ((Subgroup.mem_normalizer_iff.mp hqN a).mp (hle ha))
      ((img148 A Y J).inv_mem (hle ha))
  ·
    have := ker148_normal hY.2
    have hAF : A ∈ partTwoF G := hstd.mem_partTwoF
    have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
    have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
    have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
    obtain ⟨n, hn, -, hJiso, hfield⟩ := hField
    have hecent : alpha148 A Y e he ∉
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      intro hc
      have hx : alpha148 A Y e he ∈
          Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
        Subgroup.centralizer_le_normalizer _ hc
      apply not_isInnerAut_of_inducesStdKind_field148 hfield hx
      have h1 : (img148 A Y J).normalizerMonoidHom ⟨alpha148 A Y e he, hx⟩ = 1 := by
        ext y
        show alpha148 A Y e he * (y : ↥(Y ⊔ A) ⧸ ker148 A Y) * (alpha148 A Y e he)⁻¹ =
          (y : ↥(Y ⊔ A) ⧸ ker148 A Y)
        rw [← Subgroup.mem_centralizer_iff.mp hc y y.2, mul_inv_cancel_right]
      rw [h1]
      exact ⟨1, map_one _⟩
    obtain ⟨b, ⟨hbA, hbJ⟩, hb1⟩ :=
      exists_ne_one_mem_inf148 (hA3 e he) hstd.toSec13Data.card_eq hA
    have hYJ :=
      le_normalizer_of_not_mem_centralizer148 hAF hAY he hJ hKJ hAJ hkt.1 hecent hbA hbJ hb1
    refine img148_deltaZero_le fun R hR => ?_
    have hRM : R ≤ Y ⊔ A := hR.2.trans le_sup_left
    have hRT : img148 A Y R ≤ ⁅img148 A Y R, img148 A Y A⁆ := by
      conv_lhs => rw [hR.1.2]
      rw [Item148PtRes.img148_commutator hRM le_sup_right]
    have hR3 : Nat.Coprime 3 (Nat.card (img148 A Y R)) := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      exact Item148PtRes.not_three_dvd_card_img148
        ((isPiSubgroup_piCompl_iff Nat.prime_three R).mp (mem_scriptQ_iff.mp hR.1.1).1)
    refine le_of_le_commutator_of_isoLThreePi (m := 3 * n) (by omega) hJiso
      (img148_le_normalizer (hR.2.trans hYJ)) (img148_le_normalizer hAJ) hRT hR3 ?_
    intro g hg hgC
    have hgY : g ∈ img148 A Y Y := (sup_le (img148_mono hR.2) (img148_mono hJY)) hg
    exact eq_one_of_mem_centralizer_img148 hAF hAY he hKJ hJY hAJ hkt.1 hecent hYJ hgY hgC

end Steps

end CFSG.RankThree.PartTwo.Sec14
