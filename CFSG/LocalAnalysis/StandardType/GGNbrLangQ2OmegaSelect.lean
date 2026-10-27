module

public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagModel
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoOneLinear
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTypeDet
public import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTransfer
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDvd

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.Open (StatedOmega StatedSL)
open CFSG.StandardType.ClassicalPosition CFSG.StandardType.ClassicalBlocks
open CFSG.LocalAnalysis.GLTheoremA (canonLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10F

theorem exists_label_of_isComponentOf_statedOmega
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (C : Subgroup (GL ι K)) (hC : CFSG.Assembly.IsComponentOf C (StatedOmega ⇑Φ)) :
    ∃ lab : LargeEvenLabel, HasLabel ↥C (· = lab) ∧
      ((((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank) ∨
        (lab.tag = .A ∧ lab.rank = 1)) ∨
        (lab.tag = .A ∧ lab.rank = 3) ∨
        (lab.tag = .twA ∧ lab.rank = 3)) := by
  classical
  by_cases h3 : Fintype.card ι ≤ 3
  · exact absurd hC (not_isComponentOf_statedOmega_of_card_le_three Φ hΦ h3 C)
  by_cases hplus : Fintype.card ι = 4 ∧
      ∃ T : Submodule K (ι → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ x = 0
  · obtain ⟨f, hmodel⟩ :=
      statedClassicalModel_of_isComponentOf_statedOmega_four Φ hΦ hplus.1 hplus.2 hC
    have hCq : CFSG.IsQuasisimple ↥C :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥C).1 hC.2.2
    refine ⟨⟨.A, 1, f⟩, ?_, Or.inl (Or.inr ⟨rfl, rfl⟩)⟩
    exact hasLabel_of_statedClassicalModel_PSL (r := 1) (n := f) hCq hmodel
  · have hdim : 6 ≤ Fintype.card ι ∨ (Fintype.card ι = 4 ∧
        ¬ ∃ T : Submodule K (ι → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ x = 0) := by
      by_cases h4 : Fintype.card ι = 4
      · refine Or.inr ⟨h4, ?_⟩
        rintro ⟨T, hT, hzero⟩
        exact hplus ⟨h4, ⟨T, hT, hzero⟩⟩
      · left
        have hfinrank : Module.finrank K (ι → K) = Fintype.card ι :=
          Module.finrank_fintype_fun_eq_card K
        obtain ⟨k, hk⟩ :=
          CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Φ hΦ
        rw [hfinrank] at hk
        omega
    have hCeq : C = StatedOmega ⇑Φ :=
      GGHalf.eq_of_isComponentOf_isQuasisimple (isQuasisimple_statedOmega Φ hΦ hdim) hC
    rw [hCeq] at hC ⊢
    have hCq : CFSG.IsQuasisimple ↥(StatedOmega ⇑Φ) :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hC.2.2
    rcases exists_statedClassicalModel_statedOmega_cases Φ hΦ hdim with
      ⟨n, f, hn4, hM⟩ | ⟨n, f, hn4, hM⟩ | ⟨f, hM⟩ | ⟨f, hM⟩ | ⟨f, hM⟩
    · refine ⟨⟨.D, n, f⟩, ?_, Or.inl (Or.inl ⟨Or.inl rfl, hn4⟩)⟩
      exact hasLabel_of_statedClassicalModel_POmegaPlus hCq hM
    · refine ⟨⟨.twD, n, f⟩, ?_, Or.inl (Or.inl ⟨Or.inr rfl, hn4⟩)⟩
      exact hasLabel_of_statedClassicalModel_POmegaMinus hCq hM
    · refine ⟨⟨.A, 3, f⟩, ?_, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      exact hasLabel_of_statedClassicalModel_PSL (r := 3) (n := f) hCq hM
    · refine ⟨⟨.twA, 3, f⟩, ?_, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
      exact hasLabel_of_statedClassicalModel_PSU (r := 3) (n := f) hCq hM
    · refine ⟨⟨.A, 1, 2 * f⟩, ?_, Or.inl (Or.inr ⟨rfl, rfl⟩)⟩
      exact hasLabel_of_statedClassicalModel_PSL (r := 1) (n := 2 * f) hCq hM

theorem exists_label_of_isComponentOf_iso_statedOmega
    {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
    {F : Subgroup G} (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (e : ↥F ≃* ↥(StatedOmega ⇑Φ)) {C : Subgroup G} (hC : CFSG.Assembly.IsComponentOf C F) :
    ∃ lab : LargeEvenLabel, HasLabel ↥C (· = lab) ∧
      ((((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank) ∨
        (lab.tag = .A ∧ lab.rank = 1)) ∨
        (lab.tag = .A ∧ lab.rank = 3) ∨
        (lab.tag = .twA ∧ lab.rank = 3)) := by
  classical
  let g : ↥F →* GL ι K := (StatedOmega ⇑Φ).subtype.comp e.toMonoidHom
  have hg : Function.Injective g := (StatedOmega ⇑Φ).subtype_injective.comp e.injective
  let C' : Subgroup (GL ι K) := (C.subgroupOf F).map g
  have hC' : CFSG.Assembly.IsComponentOf C' (StatedOmega ⇑Φ) := by
    have hCsub : CFSG.Assembly.IsComponentOf (C.subgroupOf F) ⊤ := by
      rw [← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff F.subtype_injective]
      simpa [Subgroup.subgroupOf_map_subtype, Subgroup.map_top, Subgroup.range_subtype,
        inf_of_le_left hC.1] using hC
    have hmap :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hg).2 hCsub
    have htop : (⊤ : Subgroup ↥F).map g = StatedOmega ⇑Φ := by
      rw [Subgroup.map_top, MonoidHom.range_comp,
        MonoidHom.range_eq_top.2 e.surjective,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simpa [C', htop] using hmap
  obtain ⟨lab, hlab, hdisj⟩ := exists_label_of_isComponentOf_statedOmega Φ hΦ C' hC'
  let eC : ↥C ≃* ↥C' :=
    (Subgroup.subgroupOfEquivOfLe hC.1).symm.trans
      (Subgroup.equivMapOfInjective (C.subgroupOf F) g hg)
  exact ⟨lab, (hasLabel_congr eC (· = lab)).2 hlab, hdisj⟩

private theorem false_of_orthogonal_label_iso_A {d n : ℕ} (hd : 3 ≤ d) (hd4 : d ≠ 4)
    (lab : LargeEvenLabel)
    (hdisj : ((((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank) ∨
        (lab.tag = .A ∧ lab.rank = 1)) ∨
        (lab.tag = .A ∧ lab.rank = 3) ∨
        (lab.tag = .twA ∧ lab.rank = 3)))
    (hiso : GGLabelIso (⟨.A, d - 1, n⟩ : LargeEvenLabel) lab) : False := by
  obtain ⟨tag, rank, nn⟩ := lab
  have hcanon :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.canonLabel_eq_of_ggLabelIso hiso
  dsimp only [LargeEvenLabel.tag, LargeEvenLabel.rank] at hcanon hdisj
  rcases hdisj with hD | hAtail
  · rcases hD with ⟨hD, hr⟩ | ⟨hA1, hr⟩
    · rcases hD with hD | hD
      · change tag = .D at hD
        cases hD
        change 4 ≤ rank at hr
        have hr3 : rank ≠ 3 := by omega
        have htag := congrArg LargeEvenLabel.tag hcanon
        simpa [canonLabel, hr3] using htag
      · change tag = .twD at hD
        cases hD
        change 4 ≤ rank at hr
        have hr3 : rank ≠ 3 := by omega
        have hr2 : rank ≠ 2 := by omega
        have htag := congrArg LargeEvenLabel.tag hcanon
        simpa [canonLabel, hr3, hr2] using htag
    · change tag = .A at hA1
      cases hA1
      change rank = 1 at hr
      have hrank := congrArg LargeEvenLabel.rank hcanon
      simp [canonLabel] at hrank
      omega
  · rcases hAtail with ⟨hA3, hr⟩ | ⟨hAtwA3, hr⟩
    · change tag = .A at hA3
      cases hA3
      change rank = 3 at hr
      have hrank := congrArg LargeEvenLabel.rank hcanon
      simp [canonLabel] at hrank
      omega
    · change tag = .twA at hAtwA3
      cases hAtwA3
      have htag := congrArg LargeEvenLabel.tag hcanon
      simp [canonLabel] at htag

private theorem false_of_fixed_orthogonal_block_label
    {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
    {F : Subgroup G} (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (e : ↥F ≃* ↥(StatedOmega ⇑Φ)) {C : Subgroup G} (hC : CFSG.Assembly.IsComponentOf C F)
    {d n : ℕ} (hd : 3 ≤ d) (hd4 : d ≠ 4)
    (hK : Nat.card K = 2 ^ n)
    (hlam : LargeEvenInLambda2 (⟨.A, d - 1, n⟩ : LargeEvenLabel))
    (θ : ↥C ⧸ Subgroup.center ↥C ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K)) : False := by
  obtain ⟨lab, hlab, hdisj⟩ := exists_label_of_isComponentOf_iso_statedOmega Φ hΦ e hC
  have hlabData := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ggHasLabel_of_hasLabel hlab
  have hhasLab : GGHasLabel lab (↥C ⧸ Subgroup.center ↥C) := hlabData.2.2
  have hhasA : GGHasLabel (⟨.A, d - 1, n⟩ : LargeEvenLabel)
      (↥C ⧸ Subgroup.center ↥C) := ggHasLabel_linear_of_supplied (by omega) hK θ
  have hiso : GGLabelIso (⟨.A, d - 1, n⟩ : LargeEvenLabel) lab :=
    ggLabelRigidInput_holds _ _ _ hlam hlabData.1 hhasA hhasLab
  exact false_of_orthogonal_label_iso_A hd hd4 lab hdisj hiso

theorem exists_selected_glBlock_omegaPlus
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : 3 ≤ d) (hpd : p ∣ d) (hpK : p ∣ Nat.card K - 1)
    (s : ↥(StatedOmega ⇑Φ)) (hs : orderOf s = p)
    (C : Subgroup ↥(StatedOmega ⇑Φ)) (hC : CFSG.Assembly.IsComponentOf C (Subgroup.centralizer {s}))
    (θ : ↥C ⧸ Subgroup.center ↥C ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    ∃ (P : Finset (Matrix ι ι K)) (ε : Matrix ι ι K) (m : ℕ) (E : Type)
      (_ : Field E) (_ : Finite E) (_ : CharP E 2),
      let Fε := glBlockCentralizer (StatedOmega ⇑Φ).subtype
        ({(s : GL ι K)} : Set (GL ι K)) ε
      ε ∈ P ∧
      (∀ ε' ∈ P, IsPrimAdjIdemIn (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
        (Algebra.adjoin K (Units.val '' ({(s : GL ι K)} : Set (GL ι K)))) ε') ∧
      (⨆ ε' ∈ P, glBlockCentralizer (StatedOmega ⇑Φ).subtype
        ({(s : GL ι K)} : Set (GL ι K)) ε') =
        (Subgroup.centralizer ({(s : GL ι K)} : Set (GL ι K))).comap
          (StatedOmega ⇑Φ).subtype ∧
      CFSG.Assembly.IsComponentOf C Fε ∧ m = d ∧ Nat.card E = Nat.card K ∧
      Nonempty (↥Fε ≃* GL (Fin m) E) ∧
      Nonempty (↥C ≃* StatedSL m E) ∧
      Nonempty (↥C ⧸ Subgroup.center ↥C ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin m) E)) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let b : GL ι K := s
  have hb : b ∈ StatedOmega ⇑Φ := s.2
  have hordb : orderOf b = p := by simpa [b] using hs
  have hodd : Odd (orderOf b) := by
    rw [hordb]
    exact hp.odd_of_ne_two hp2
  obtain ⟨nK, hnK, hKcardF⟩ := FiniteField.card K 2
  have hKcard : Nat.card K = 2 ^ (nK : ℕ) := by
    rw [Nat.card_eq_fintype_card, hKcardF]
  have hK4 : 4 ≤ Nat.card K := by
    have hp_le : p ≤ Nat.card K - 1 :=
      Nat.le_of_dvd (by have := Finite.one_lt_card (α := K); omega) hpK
    have hp2le : 2 ≤ p := hp.two_le
    omega
  have hnK2 : 2 ≤ (nK : ℕ) := by
    by_contra h
    have hnle : (nK : ℕ) ≤ 1 := by omega
    have hpow : 2 ^ (nK : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hnle
    rw [hKcard] at hK4
    omega
  have hd3 : 3 ≤ d := by omega
  have hd4 : d ≠ 4 := by
    intro hd4'
    subst d
    have hpd4 : p ∣ 2 ^ 2 := by simpa using hpd
    have hp_dvd_two : p ∣ 2 := hp.dvd_of_dvd_pow hpd4
    exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hp_dvd_two) hp.two_le)
  obtain ⟨P, hPprim, -, -, hPcomm, hPsup, -⟩ :=
    centralizer_block_decomp_Omega Φ hΦ h8 b hb hodd
  have hcent : Subgroup.centralizer ({s} : Set ↥(StatedOmega ⇑Φ)) =
      (Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype := by
    ext g
    dsimp only [b]
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
      Subtype.ext_iff, Subgroup.coe_mul]
  have hCsup : CFSG.Assembly.IsComponentOf C (⨆ ε ∈ P,
      glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) := by
    rw [hcent, ← hPsup] at hC
    exact hC
  obtain ⟨ε, hεP, hCε⟩ :=
    exists_isComponentOf_block P
      (fun ε => glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)
      (fun i hi j hj hij x hx y hy => hPcomm i hi j hj hij x hx y hy) hCsup
  have hεprim : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε := hPprim ε hεP
  let G : Matrix ι ι K := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)
  have hG : IsUnit G.det := CFSG.StandardType.TableC.polarGram_isUnit_det Φ hΦ
  have hGt : Matrix.transpose G = G := CFSG.StandardType.TableC.polarGram_transpose Φ
  have hS : ∀ s' ∈ ({b} : Set (GL ι K)), ∀ s'' ∈ ({b} : Set (GL ι K)), Commute s' s'' := by
    intro s' hs' s'' hs''
    rw [Set.mem_singleton_iff] at hs' hs''
    rw [hs', hs'']
  have hSU : ∀ s' ∈ ({b} : Set (GL ι K)),
      Matrix.transpose (s' : Matrix ι ι K) * G * (s' : Matrix ι ι K) = G := by
    intro s' hs'
    rw [Set.mem_singleton_iff] at hs'
    subst hs'
    have hg : ∀ v : ι → K, Φ (Matrix.mulVec (b : Matrix ι ι K) v) = Φ v :=
      fun v => CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.isometry_of_mem_statedOmega
        (f := ⇑Φ) hb v
    have h := CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.gram_invariant (Q := Φ) hg
    simpa [G, Matrix.map_id,
      CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.polarGram_eq_toMatrix₂'] using h
  have hSUmap : ∀ s' ∈ ({b} : Set (GL ι K)),
      Matrix.transpose ((s' : Matrix ι ι K).map (RingHom.id K)) * G *
        (s' : Matrix ι ι K) = G := by
    intro s' hs'
    simpa using hSU s' hs'
  obtain ⟨e, he, heε, -⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id K)
    (fun _ => rfl) (G := G) hG (by simpa [Matrix.map_id] using hGt) hS hSUmap hεprim
  have hpF : p ∣ Nat.card Kˣ := by
    rwa [Nat.card_units]
  have hbp : b ^ p = 1 := by
    rw [← hordb]
    exact pow_orderOf_eq_one b
  have hpow : ∀ x ∈ ({b} : Set (GL ι K)), ∃ c : K,
      (x : Matrix ι ι K) ^ p = Matrix.scalar ι (c ^ p) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨1, ?_⟩
    simpa using congrArg (fun u : GL ι K => (u : Matrix ι ι K)) hbp
  have hoddS : ∀ x ∈ ({b} : Set (GL ι K)), Odd (orderOf x) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hodd
  rcases CFSG.StandardType.TableC.isPrimIdemIn_cases hG hGt hS hSU hεprim he heε with
    heq | ⟨-, e', he', hne', hεe⟩
  · have heprim : IsPrimIdemIn (Algebra.adjoin K
        (Units.val '' ({b} : Set (GL ι K)))) ε := heq ▸ he
    by_cases h1 : (b : Matrix ι ι K) * ε = ε
    ·
      obtain ⟨ι₁, hFintype₁, hDecEq₁, Q₁, -, hform₁, hcases₁⟩ :=
        blockGroup_iso_Omega_one Φ hΦ h8 b hb hodd hεprim h1
      letI : Fintype ι₁ := hFintype₁
      letI : DecidableEq ι₁ := hDecEq₁
      obtain ⟨Φ₁, hQ₁, hΦ₁⟩ := hform₁
      rcases hcases₁ with ⟨⟨eF⟩, -⟩ | ⟨-, -, hsol, -⟩
      · let eF' : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) ≃*
            ↥(StatedOmega ⇑Φ₁) := by
          exact hQ₁.symm ▸ eF
        exact (false_of_fixed_orthogonal_block_label Φ₁ hΦ₁ eF' hCε hd hd4 hKcard
          (by
            simp only [LargeEvenInLambda2]
            refine ⟨by omega, by omega, ?_⟩
            intro hrank
            omega) θ).elim
      · exact (ResU3Three.not_isComponentOf_of_isSolvable hsol hCε).elim
    ·
      obtain ⟨db, -, -, -, -, hdb1, -, -, hblockdeg, -⟩ :=
        blockGroup_iso_Omega_unitary Φ hΦ h8 b hb hodd hεprim heprim h1
      have hdeg1 : blockDegree (Algebra.adjoin K
          (Units.val '' ({b} : Set (GL ι K)))) ε = 1 :=
        CFSG.StandardType.TableCRes.blockDegree_eq_one_of_pow_eq_pow hp hpF hS hoddS hpow
          heprim
      exfalso
      omega
  ·
    obtain ⟨db, m, E, hEfld, hEfin, -, hcardE, -, -, ⟨eGL⟩⟩ :=
      blockGroup_iso_Omega_linear Φ hΦ h8 b hb hodd hεprim he he' hne' hεe
    letI : Field E := hEfld
    letI : Fintype E := hEfin
    have hEfinite : Finite E := Fintype.finite hEfin
    letI : Finite E := hEfinite
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hEtwo : Fintype.card E = 2 ^ ((nK : ℕ) * db) := by
      rw [hcardE, hKcardF, ← pow_mul]
    have hcharE : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := (nK : ℕ) * db) hEtwo
    let eC : ↥C ≃* StatedSL m E := componentEquivStatedSLOfMulEquiv eGL hCε
    let θC : ↥C ⧸ Subgroup.center ↥C ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin m) E) :=
      (centerQuotCongr eC).trans (statedSLQuotEquivLargeEvenProj (m := m) (E := E))
    let ψ : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL d K ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin m) E) :=
      (TypeA.recipeEquiv d K).symm.trans (θ.symm.trans θC)
    obtain ⟨hmd, hEcard⟩ :=
      kgLangS1A_psl_typeDet (d := d) (d₁ := m) (m := (nK : ℕ)) (F₀ := K) (E := E)
        hd3 hnK2 hKcard ψ
    refine ⟨P, ε, m, E, hEfld, hEfinite, hcharE, hεP, ?_, ?_, hCε, hmd, hEcard,
      ⟨eGL⟩, ⟨eC⟩, ⟨θC⟩⟩
    · intro ε' hε'
      exact hPprim ε' hε'
    · simpa [b] using hPsup

theorem exists_selected_glBlock_omegaPlus_of_cardEq
    {ι F K : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [CharP F 2] [Field K] [Finite K]
    (Φ : QuadraticForm F (ι → F)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : 3 ≤ d) (hpd : p ∣ d) (hpF : p ∣ Nat.card F - 1)
    (s : ↥(StatedOmega ⇑Φ)) (hs : orderOf s = p)
    (C : Subgroup ↥(StatedOmega ⇑Φ))
    (hC : CFSG.Open.IsComponentOf C (Subgroup.centralizer {s}))
    (hKF : Nat.card K = Nat.card F)
    (ξ : ↥C ⧸ Subgroup.center ↥C ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    ∃ (P : Finset (Matrix ι ι F)) (ε : Matrix ι ι F) (m : ℕ) (E : Type)
      (_ : Field E) (_ : Finite E) (_ : CharP E 2),
      let Fε := glBlockCentralizer (StatedOmega ⇑Φ).subtype
        ({(s : GL ι F)} : Set (GL ι F)) ε
      ε ∈ P ∧
      (∀ ε' ∈ P, IsPrimAdjIdemIn (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Φ))
        (Algebra.adjoin F (Units.val '' ({(s : GL ι F)} : Set (GL ι F)))) ε') ∧
      (⨆ ε' ∈ P, glBlockCentralizer (StatedOmega ⇑Φ).subtype
        ({(s : GL ι F)} : Set (GL ι F)) ε') =
        (Subgroup.centralizer ({(s : GL ι F)} : Set (GL ι F))).comap
          (StatedOmega ⇑Φ).subtype ∧
      CFSG.Open.IsComponentOf C Fε ∧ m = d ∧ Nat.card E = Nat.card F ∧
      Nonempty (↥Fε ≃* GL (Fin m) E) ∧
      Nonempty (↥C ≃* StatedSL m E) ∧
      Nonempty (↥C ⧸ Subgroup.center ↥C ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin m) E)) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Finite F := Fintype.finite (inferInstance : Fintype F)
  have hcardKF : Fintype.card K = Fintype.card F := by
    simpa [Nat.card_eq_fintype_card] using hKF
  let τ : K ≃+* F := FiniteField.ringEquivOfCardEq hcardKF
  let pslCongr : LargeEvenProj (LargeEvenSLGroup (Fin d) K) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) F) :=
    (TypeA.recipeEquiv d K).trans
      ((kgLangS1A_pslRingCongr d (by omega) τ).trans (TypeA.recipeEquiv d F).symm)
  let ξF : ↥C ⧸ Subgroup.center ↥C ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) F) := ξ.trans pslCongr
  have hCAssembly : CFSG.Assembly.IsComponentOf C (Subgroup.centralizer {s}) :=
    (CFSG.Assembly.isComponentOf_iff_open).2 hC
  obtain ⟨P, ε, m, E, hEfld, hEfin, hcharE, hεP, hPprim, hPsup,
      hCε, hmd, hEcard, ⟨eGL⟩, ⟨eC⟩, ⟨θC⟩⟩ :=
    exists_selected_glBlock_omegaPlus (K := F) Φ hΦ h8 hp hp2 hd hpd hpF s hs C
      hCAssembly ξF
  exact ⟨P, ε, m, E, hEfld, hEfin, hcharE, hεP, hPprim, hPsup,
    (CFSG.Assembly.isComponentOf_iff_open).1 hCε, hmd, hEcard, ⟨eGL⟩, ⟨eC⟩, ⟨θC⟩⟩

end CFSG.StandardType
