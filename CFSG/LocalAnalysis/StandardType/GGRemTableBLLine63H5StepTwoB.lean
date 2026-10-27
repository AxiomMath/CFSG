module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5StepTwoA
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Frame
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Det
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmall
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerMain
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5StepOneMarking

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.LineU CFSG.Assembly CFSG.StandardType CFSG.SectionRank.OddCover

variable {K : Type} [Field K] {n : ℕ}

theorem exists_layer_component_ggBeta {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hZ1 : ∀ z : ↥L, z ∈ Subgroup.center ↥L → z = 1) :
    ∃ a ∈ (ggBeta L θ hBsN).range, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) := by
  classical
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  obtain ⟨hDB, hDe, hDcard, hxD, hJdef, hJcomp, hDC⟩ := hcfg.2.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  obtain ⟨d, hdD, hdx⟩ := CFSG.StandardType.exists_mem_not_mem_zpowers hp hDcard
    (hS.1.1.2 x hS.2.1) hS.2.2.1
  have hD : D = Subgroup.zpowers x ⊔ Subgroup.zpowers d :=
    CFSG.StandardType.eq_sup_zpowers_of_card hp hDe hDcard hxD hS.2.2.1 hdD hdx
  set d₀ : Bs := ⟨d, hBBs (hDB hdD)⟩ with hd₀
  set aγ := ggGamma L hBsN d₀ with haγ
  have hfix : (ggFix aγ).map L.subtype = L ⊓ Subgroup.centralizer (D : Set G) := by
    rw [hD, inf_centralizer_sup_zpowers hLx]
    exact map_ggFix_ggGamma L hBsN d₀
  have hJE : J = (LargeEvenLayer (ggFix aγ)).map L.subtype := by
    rw [hJdef, ← hfix, largeEvenLayer_map_of_injective _ L.subtype_injective]
  have hEcomp : IsComponentOf (LargeEvenLayer (ggFix aγ)) (ggFix aγ) := by
    have h1 := isComponentOf_comap_of_injective L.subtype L.subtype_injective
      (K' := J) (C := ggFix aγ) (by rw [hfix]; exact hJcomp)
    have h2 : J.comap L.subtype = LargeEvenLayer (ggFix aγ) := by
      rw [hJE, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
    rw [← h2]
    exact h1.1
  have haγ1 : aγ ≠ 1 := by
    intro h
    rw [haγ, ggGamma_eq_one_iff] at h
    apply hdx
    rw [← inf_centralizer_eq_zpowers_of_sstar hp hS]
    exact ⟨hDB hdD, h⟩
  set f := ggQuotHom θ with hf
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h1 : l ∈ (ggQuotHom θ).ker := hl
    rw [ker_ggQuotHom] at h1
    exact hZ1 l h1
  have hfsurj : Function.Surjective f := ggQuotHom_surjective θ
  set a := ggBeta L θ hBsN d₀ with ha
  have hcompat : ∀ l, a (f l) = f (aγ l) := fun l => ggBeta_ggQuotHom L hBsN θ d₀ l
  have hFix : ggFix a = (ggFix aγ).map f := by
    ext r
    constructor
    · intro hr
      obtain ⟨l, rfl⟩ := hfsurj r
      refine ⟨l, ?_, rfl⟩
      have h1 := mem_ggFix.mp hr
      rw [hcompat] at h1
      exact mem_ggFix.mpr (hfinj h1)
    · rintro ⟨l, hl, rfl⟩
      rw [mem_ggFix, hcompat, mem_ggFix.mp hl]
  refine ⟨a, ⟨d₀, rfl⟩, ?_, ?_⟩
  · intro h
    apply haγ1
    refine MulEquiv.ext fun l => ?_
    apply hfinj
    rw [← hcompat, h]
    rfl
  · rw [hFix, largeEvenLayer_map_of_injective f hfinj]
    exact isComponentOf_map_of_injective f hfinj hEcomp

theorem not_isInner_of_pow_three_eq_scalar (hKd : UnitaryFieldData 2 n K) {M : GL (Fin 6) K}
    {l : Kˣ} (hM3 : M ^ 3 = GeneralLinearGroup.scalar (Fin 6) l) (hl : ∀ c : Kˣ, c ^ 3 ≠ l) :
    ¬ IsInner n M := by
  intro h
  obtain ⟨t, ht⟩ := det_eq_pow_six_of_isInner h hKd
  have hM : ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ^ 3 =
      (l : K) • (1 : Matrix (Fin 6) (Fin 6) K) := by
    have h1 := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) hM3
    simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] at h1
    rw [h1]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have hc : ∀ d : K, d ^ 3 ≠ (l : K) := fun d hd => by
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hd
      exact l.ne_zero hd.symm
    exact hl (Units.mk0 d hd0) (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hd]))
  apply det_smul_ne_one_of_pow_three_eq_smul hc hM ((t : K)⁻¹)
  rw [Matrix.det_smul, ht, Fintype.card_fin, ← mul_pow, inv_mul_cancel₀ t.ne_zero, one_pow]

theorem exists_scalar_of_projConj_eq [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : 3 ∣ 2 ^ n + 1) {M M' : GL (Fin 6) K}
    (hN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hN' : M' ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (h : TableB.projConj (unitarySU 2 n K 6) ⟨M, hN⟩ =
      TableB.projConj (unitarySU 2 n K 6) ⟨M', hN'⟩) :
    ∃ c : Kˣ, M = M' * GeneralLinearGroup.scalar (Fin 6) c := by
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have h1 : TableB.projConj (unitarySU 2 n K 6)
      ((⟨M', hN'⟩ : ↥(Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))))⁻¹ *
        ⟨M, hN⟩) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨c, hc⟩ := TableBUE.mem_scalars_of_projConj_eq_one hKd hK (by norm_num) hdq
    Nat.prime_three hpq h1
  refine ⟨c, ?_⟩
  have h2 : (M'⁻¹ * M : GL (Fin 6) K) = GeneralLinearGroup.scalar (Fin 6) c := hc.symm
  calc M = M' * (M'⁻¹ * M) := by group
    _ = M' * GeneralLinearGroup.scalar (Fin 6) c := by rw [h2]

theorem isDiag_conj_mul_scalar {P M₀ : GL (Fin 6) K} (c : Kˣ)
    (h : ((P⁻¹ * M₀ * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag) :
    ((P⁻¹ * (M₀ * GeneralLinearGroup.scalar (Fin 6) c) * P : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K).IsDiag := by
  obtain ⟨σ, hσ⟩ := TableBUE.exists_diagHom_of_isDiag h
  have h1 : P⁻¹ * (M₀ * GeneralLinearGroup.scalar (Fin 6) c) * P =
      diagHom 6 (σ * fun _ => c) := by
    calc P⁻¹ * (M₀ * GeneralLinearGroup.scalar (Fin 6) c) * P
        = P⁻¹ * M₀ * (GeneralLinearGroup.scalar (Fin 6) c * P) := by group
      _ = P⁻¹ * M₀ * (P * GeneralLinearGroup.scalar (Fin 6) c) := by
          rw [(TypeA.PGLTor.commute_scalar c P).eq]
      _ = (P⁻¹ * M₀ * P) * GeneralLinearGroup.scalar (Fin 6) c := by group
      _ = diagHom 6 (σ * fun _ => c) := by
          rw [hσ, ← diagHom_const_eq_scalar, ← map_mul]
  rw [h1, coe_diagHom]
  exact Matrix.isDiag_diagonal _

theorem exists_pow_three_eq_one_of_isInner [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {y : GL (Fin 6) K} (hy : IsInner n y) {w : Kˣ}
    (hw : y ^ 3 = GeneralLinearGroup.scalar (Fin 6) w) :
    ∃ c : Kˣ, (GeneralLinearGroup.scalar (Fin 6) c * y) ^ 3 = 1 := by
  obtain ⟨t, s, rfl⟩ := hy
  rw [TableBU63.scalar_mul_pow] at hw
  set u : Kˣ := w * (t ^ 3)⁻¹ with hu
  have hs3 : (s : GL (Fin 6) K) ^ 3 = GeneralLinearGroup.scalar (Fin 6) u := by
    have h1 : (s : GL (Fin 6) K) ^ 3 = (GeneralLinearGroup.scalar (Fin 6) (t ^ 3))⁻¹ *
        GeneralLinearGroup.scalar (Fin 6) w := by
      rw [← hw]
      group
    rw [h1, hu, ← map_inv, ← map_mul]
    congr 1
    exact mul_comm _ _
  have hu3 : u ^ 3 = 1 := by
    refine pow_three_eq_one_of_scalar_mem_unitarySU hKd hpq ?_
    have h1 := pow_mem s.2 3
    rwa [hs3] at h1
  have hsc : GeneralLinearGroup.scalar (Fin 6) t⁻¹ *
      (GeneralLinearGroup.scalar (Fin 6) t * (s : GL (Fin 6) K)) = s := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  by_cases hu1 : u = 1
  · refine ⟨t⁻¹, ?_⟩
    rw [hsc, hs3, hu1, map_one]
  · by_cases h9 : 9 ∣ 2 ^ n + 1
    · obtain ⟨d, hd⟩ := exists_cube_of_pow_three_eq_one (nine_dvd_card_units hKd h9) hu3
      refine ⟨(t * d)⁻¹, ?_⟩
      rw [TableBU63.scalar_mul_pow, TableBU63.scalar_mul_pow, hs3, ← map_mul, ← map_mul, ← hd,
        inv_pow, mul_pow, inv_mul_cancel, map_one]
    · exfalso
      refine false_of_pow_three_eq_scalar hKd hpq h9 hu3 hu1 s (Subtype.ext ?_)
      show (s : GL (Fin 6) K) ^ 3 = diagHom 6 (fun _ => u)
      rw [hs3, diagHom_const_eq_scalar]

theorem stepTwoB_of_marking
    [Finite K] {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hlt : Nat.card Bs < 3 ^ 5)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn2 : 2 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) (hL : commutator L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 n K 6))
    (hBN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hz : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z ^ 3 = 1 → z = 1) : False := by
  classical
  have hKd : UnitaryFieldData 2 n K := CFSG.StandardType.TableBU.unitaryFieldData_of_card hK
    (by omega)
  obtain ⟨φ, hφL, hφs, hφZ, hψ, hZ1, hinner⟩ :=
    all_inner_of_marking hcfg hlt hK hn2 hpq hL θ hBN hBI hz
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  obtain ⟨hcardBs, -⟩ := config_card_rank hcfg hlt
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN' : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hBN
  have hx3 : x ^ 3 = 1 := hBs.2 x hxBs
  have hxC : ∀ l ∈ L, x * l = l * x := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)).symm
  have hxL : x ∉ L := fun hxL => hS.2.2.1 (hz x hxL hxC hx3)
  have hN := TableBUE.gu_subset_normalizer (d := 6) hKd
  set Ab := (ggBeta L θ hBN).range with hAb
  have hAbab : CFSG.Open.IsElemAbelian 3 Ab := isElemAbelian_range_ggBeta θ hBs hBN
  have hcardAb : Nat.card Ab * 3 = Nat.card Bs :=
    (card_range_ggBeta_bstar hcfg hL θ hBN' hBN).2.2
  have hAb27 : Nat.card Ab = 27 := by
    rw [hcardBs] at hcardAb
    omega
  have hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)) := by
    rintro _ ⟨b, rfl⟩
    exact ggBeta_mem L θ hBN hBI b
  have hMb : ∀ (b : G) (hb : b ∈ Bs),
      ∃ (M : GL (Fin 6) K) (hMgu : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)),
      ActsAs φ b M ∧ IsInner n M ∧ ggLAut L θ ⟨b, hBN hb⟩ =
        TableB.projConj (unitarySU 2 n K 6) ⟨M, hN hMgu⟩ := by
    intro b hb
    obtain ⟨M, hMgu, hMact, hMin⟩ := hinner b hb
    exact ⟨M, hMgu, hMact, hMin,
      ggLAut_eq_projConj_of_actsAs θ hφL hψ (hBN hb) hMact (hN hMgu)⟩
  by_cases hfr : ∃ P ∈ primeFormUnitary hKd (idGram K 6), ∀ a ∈ Ab, ∃ (M : GL (Fin 6) K)
      (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)),
      ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag ∧
        a = TableB.projConj (unitarySU 2 n K 6) ⟨M, hN hM⟩
  ·
    obtain ⟨P, hP, hPd⟩ := hfr
    have hker : ∀ s, φ s = 1 → LargeEvenProjMk (unitarySU 2 n K 6) s = 1 := fun s hs =>
      (hφZ s).mp fun l _ => by rw [hs, one_mul, mul_one]
    have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := config_selfCent hcfg
    have hrange := le_range_of_frame hKd hpq φ hker (B := Bs) (by rw [hcardBs]) hSC hP
      (fun b hb => by
        obtain ⟨M, hMgu, hMact, -, hMeq⟩ := hMb b hb
        obtain ⟨M₀, hM₀gu, hM₀d, hM₀eq⟩ := hPd (ggBeta L θ hBN ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
        have hρ : TableB.projConj (unitarySU 2 n K 6) ⟨M, hN hMgu⟩ =
            TableB.projConj (unitarySU 2 n K 6) ⟨M₀, hN hM₀gu⟩ := by
          rw [← hMeq, ← ggBeta_eq L θ hBN ⟨b, hb⟩, hM₀eq]
        obtain ⟨c, hc⟩ := exists_scalar_of_projConj_eq hKd hK hpq (hN hMgu) (hN hM₀gu) hρ
        refine ⟨M, hMact, ?_⟩
        rw [hc]
        exact isDiag_conj_mul_scalar c hM₀d)
    obtain ⟨s, hs⟩ := hrange x hxBs
    exact hxL (hs ▸ hφL s)
  · rcases TableBU63.fieldType_or_heis hKd hK hpq hAbab hAbI (by rw [hAb27]; norm_num) hfr with
      ⟨M, hMN, l, -, hM3, hl, hMA⟩ | hheis
    ·
      obtain ⟨⟨b, hb⟩, hbeq⟩ := hMA
      obtain ⟨M', hM'gu, -, hM'in, hM'eq⟩ := hMb b hb
      have hρ : TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩ =
          TableB.projConj (unitarySU 2 n K 6) ⟨M', hN hM'gu⟩ := by
        rw [← hM'eq, ← ggBeta_eq L θ hBN ⟨b, hb⟩]
        exact hbeq.symm
      obtain ⟨c, hc⟩ := exists_scalar_of_projConj_eq hKd hK hpq hMN (hN hM'gu) hρ
      have hMin : IsInner n M := by
        rw [hc, ← (TypeA.PGLTor.commute_scalar c M').eq]
        exact (isInner_scalar_mul_iff c M').mpr hM'in
      exact not_isInner_of_pow_three_eq_scalar hKd hM3 hl hMin
    ·
      obtain ⟨x', y', z', hx'N, hy'N, hz'N, ζ, hxu, hyu, hzu, hxA, hyA, hzA, hx3, hz3, hζ3, hζ1,
        hxy, hxz, hyz, hzs⟩ := hheis
      have hyA' := hyA
      obtain ⟨⟨b, hb⟩, hbeq⟩ := hyA
      obtain ⟨M', hM'gu, -, hM'in, hM'eq⟩ := hMb b hb
      have hρ : TableB.projConj (unitarySU 2 n K 6) ⟨y', hy'N⟩ =
          TableB.projConj (unitarySU 2 n K 6) ⟨M', hN hM'gu⟩ := by
        rw [← hM'eq, ← ggBeta_eq L θ hBN ⟨b, hb⟩]
        exact hbeq.symm
      obtain ⟨c₀, hc₀⟩ := exists_scalar_of_projConj_eq hKd hK hpq hy'N (hN hM'gu) hρ
      have hy'in : IsInner n y' := by
        rw [hc₀, ← (TypeA.PGLTor.commute_scalar c₀ M').eq]
        exact (isInner_scalar_mul_iff c₀ M').mpr hM'in
      have hy'cube : ∃ w : Kˣ, y' ^ 3 = GeneralLinearGroup.scalar (Fin 6) w := by
        have hmem : y' ^ 3 ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
          Subgroup.pow_mem _ hy'N 3
        have hρ3 : TableB.projConj (unitarySU 2 n K 6) ⟨y' ^ 3, hmem⟩ =
            TableB.projConj (unitarySU 2 n K 6) ⟨1, Subgroup.one_mem _⟩ := by
          have h1 : (⟨y' ^ 3, hmem⟩ : ↥(Subgroup.normalizer
              (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))) = ⟨y', hy'N⟩ ^ 3 := rfl
          have h2 : (⟨1, Subgroup.one_mem _⟩ : ↥(Subgroup.normalizer
              (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))) = 1 := rfl
          rw [h1, h2, map_pow, map_one]
          exact hAbab.2 _ hyA'
        obtain ⟨w, hw⟩ := exists_scalar_of_projConj_eq hKd hK hpq hmem (Subgroup.one_mem _) hρ3
        exact ⟨w, by rw [hw, one_mul]⟩
      obtain ⟨w, hw⟩ := hy'cube
      obtain ⟨c, hc⟩ := exists_pow_three_eq_one_of_isInner hKd hpq hy'in hw
      have hsN : GeneralLinearGroup.scalar (Fin 6) c ∈
          Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
        TableB.scalar_mem_normalizer _ ⟨c, rfl⟩
      have hy''N : GeneralLinearGroup.scalar (Fin 6) c * y' ∈
          Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) := mul_mem hsN hy'N
      have hy''u : GeneralLinearGroup.scalar (Fin 6) c * y' ∈
          primeFormUnitary hKd (idGram K 6) :=
        TableBUD.mem_primeFormUnitary_of_pow_eq_one hKd hpq (by norm_num)
          (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hyu) (c := (c : K))
          (by rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
            TableBUD.scalar_mul_eq_smul]) hc
      have hy''A : TableB.projConj (unitarySU 2 n K 6) ⟨GeneralLinearGroup.scalar (Fin 6) c * y',
          hy''N⟩ ∈ Ab := by
        have : (⟨GeneralLinearGroup.scalar (Fin 6) c * y', hy''N⟩ :
            ↥(Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))) =
            ⟨GeneralLinearGroup.scalar (Fin 6) c, hsN⟩ * ⟨y', hy'N⟩ := rfl
        rw [this, map_mul, TableB.projConj_of_scalar _ ⟨c, rfl⟩, one_mul]
        exact hyA'
      have hxy' : x' * (GeneralLinearGroup.scalar (Fin 6) c * y') =
          GeneralLinearGroup.scalar (Fin 6) ζ *
            ((GeneralLinearGroup.scalar (Fin 6) c * y') * x') := by
        calc x' * (GeneralLinearGroup.scalar (Fin 6) c * y')
            = GeneralLinearGroup.scalar (Fin 6) c * (x' * y') := by
              rw [← mul_assoc, ← mul_assoc, (TypeA.PGLTor.commute_scalar c x').eq.symm]
          _ = GeneralLinearGroup.scalar (Fin 6) c *
                (GeneralLinearGroup.scalar (Fin 6) ζ * (y' * x')) := by rw [hxy]
          _ = (GeneralLinearGroup.scalar (Fin 6) c * GeneralLinearGroup.scalar (Fin 6) ζ) *
                (y' * x') := by rw [mul_assoc]
          _ = (GeneralLinearGroup.scalar (Fin 6) ζ * GeneralLinearGroup.scalar (Fin 6) c) *
                (y' * x') := by
              rw [(TypeA.PGLTor.commute_scalar c (GeneralLinearGroup.scalar (Fin 6) ζ)).eq]
          _ = GeneralLinearGroup.scalar (Fin 6) ζ *
                ((GeneralLinearGroup.scalar (Fin 6) c * y') * x') := by
              rw [mul_assoc, mul_assoc]
      have hy''z : (GeneralLinearGroup.scalar (Fin 6) c * y') * z' =
          z' * (GeneralLinearGroup.scalar (Fin 6) c * y') := by
        rw [mul_assoc, hyz, ← mul_assoc, ← mul_assoc, (TypeA.PGLTor.commute_scalar c z').eq]
      obtain ⟨a, haAb, ha1, hacomp⟩ := exists_layer_component_ggBeta hcfg θ hBN hZ1
      exact not_isComponentOf_layer_ggFix_of_heis_alt hKd hpq hAb27
        ⟨x', GeneralLinearGroup.scalar (Fin 6) c * y', z', hx'N, hy''N, hz'N, ζ, hxu, hy''u, hzu,
          hxA, hy''A, hzA, hx3, hc, hz3, hζ3, hζ1, hxy', hxz, hy''z, hzs⟩ a haAb ha1 hacomp

end CFSG.StandardType.Line63.H5

end
