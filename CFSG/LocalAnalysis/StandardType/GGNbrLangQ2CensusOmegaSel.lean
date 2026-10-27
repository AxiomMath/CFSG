module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2OmegaSelect

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.Open (StatedOmega StatedSL)
open CFSG.StandardType.ClassicalPosition CFSG.StandardType.ClassicalBlocks
open CFSG.LocalAnalysis.GLTheoremA (canonLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10F


private theorem q2cOS_exists_label_of_isComponentOf_statedOmega
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

private theorem q2cOS_exists_label_of_isComponentOf_iso_statedOmega
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
  obtain ⟨lab, hlab, hdisj⟩ := q2cOS_exists_label_of_isComponentOf_statedOmega Φ hΦ C' hC'
  let eC : ↥C ≃* ↥C' :=
    (Subgroup.subgroupOfEquivOfLe hC.1).symm.trans
      (Subgroup.equivMapOfInjective (C.subgroupOf F) g hg)
  exact ⟨lab, (hasLabel_congr eC (· = lab)).2 hlab, hdisj⟩

private theorem q2cOS_false_of_orthogonal_label_iso_A {d n : ℕ} (hd : 3 ≤ d) (hd4 : d ≠ 4)
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

private theorem q2cOS_ggHasLabel_linear_of_supplied
    {C K : Type} [Group C] [Field K] [Finite K] {d n : ℕ} (hd1 : 1 ≤ d)
    (hK : Nat.card K = 2 ^ n)
    (θ : C ⧸ Subgroup.center C ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    GGHasLabel (⟨.A, d - 1, n⟩ : LargeEvenLabel) (C ⧸ Subgroup.center C) := by
  refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
  have hd1' : d - 1 + 1 = d := Nat.sub_add_cancel hd1
  refine ⟨?_⟩
  rw [hd1']
  exact θ

private theorem q2cOS_false_of_fixed_orthogonal_block_label
    {G ι K L : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
    [Field L] [Finite L]
    {F : Subgroup G} (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (e : ↥F ≃* ↥(StatedOmega ⇑Φ)) {C : Subgroup G} (hC : CFSG.Assembly.IsComponentOf C F)
    {d n : ℕ} (hd : 3 ≤ d) (hd4 : d ≠ 4)
    (hL : Nat.card L = 2 ^ n)
    (hlam : LargeEvenInLambda2 (⟨.A, d - 1, n⟩ : LargeEvenLabel))
    (θ : ↥C ⧸ Subgroup.center ↥C ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) L)) : False := by
  obtain ⟨lab, hlab, hdisj⟩ := q2cOS_exists_label_of_isComponentOf_iso_statedOmega Φ hΦ e hC
  have hlabData := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ggHasLabel_of_hasLabel hlab
  have hhasLab : GGHasLabel lab (↥C ⧸ Subgroup.center ↥C) := hlabData.2.2
  have hhasA : GGHasLabel (⟨.A, d - 1, n⟩ : LargeEvenLabel)
      (↥C ⧸ Subgroup.center ↥C) := q2cOS_ggHasLabel_linear_of_supplied (by omega) hL θ
  have hiso : GGLabelIso (⟨.A, d - 1, n⟩ : LargeEvenLabel) lab :=
    ggLabelRigidInput_holds _ _ _ hlam hlabData.1 hhasA hhasLab
  exact q2cOS_false_of_orthogonal_label_iso_A hd hd4 lab hdisj hiso

theorem q2cOS_selected_block {ι K K' : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    [CharP K 2] [Field K'] [Finite K']
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) {p d w m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : 3 ≤ d) (hpd : p ∣ d) (hpK : p ∣ Nat.card K - 1)
    (hm : 2 ≤ m) (hK' : Nat.card K' = 2 ^ m)
    (hw : ∀ W : Submodule K (ι → K), (∀ x ∈ W, Φ x = 0) → Module.finrank K W ≤ w)
    (s : ↥(StatedOmega ⇑Φ)) (hs : orderOf s = p)
    (C : Subgroup ↥(StatedOmega ⇑Φ))
    (hC : CFSG.Assembly.IsComponentOf C (Subgroup.centralizer {s}))
    (θ : ↥C ⧸ Subgroup.center ↥C ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K')) :
    Nat.card K' = Nat.card K ∧ d ≤ w := by
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
  obtain ⟨e, he, heε, hcase⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id K)
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
    heq | ⟨hneε, e', he', hne', hεe⟩
  ·
    have heprim : IsPrimIdemIn (Algebra.adjoin K
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
        exact (q2cOS_false_of_fixed_orthogonal_block_label Φ₁ hΦ₁ eF' hCε hd hd4 hK'
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
    have hεe_adj : ε = e + formAdj (RingHom.id K) G e := by
      rcases hcase with h | ⟨-, -, hεe'⟩
      · exact absurd h hneε
      · exact hεe'
    have hpair : formAdj (RingHom.id K) G e ≠ e := by
      rcases hcase with h | ⟨-, hp, -⟩
      · exact absurd h hneε
      · exact hp
    have he'eq : e' = formAdj (RingHom.id K) G e := by
      have hsum : e + e' = e + formAdj (RingHom.id K) G e := by
        rw [← hεe, hεe_adj]
      exact add_left_cancel hsum
    obtain ⟨db, mb, E, hEfld, hEfin, hdb1, hcardE, hdim, hblockdeg, ⟨eGL⟩⟩ :=
      blockGroup_iso_Omega_linear Φ hΦ h8 b hb hodd hεprim he he' hne' hεe
    letI : Field E := hEfld
    letI : Fintype E := hEfin
    have hEfinite : Finite E := Fintype.finite hEfin
    letI : Finite E := hEfinite
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let eC : ↥C ≃* StatedSL mb E := componentEquivStatedSLOfMulEquiv eGL hCε
    let θC : ↥C ⧸ Subgroup.center ↥C ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin mb) E) :=
      (centerQuotCongr eC).trans (statedSLQuotEquivLargeEvenProj (m := mb) (E := E))
    let ψ : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL d K' ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin mb) E) :=
      (TypeA.recipeEquiv d K').symm.trans (θ.symm.trans θC)
    obtain ⟨hmbd, hEcardK'⟩ :=
      kgLangS1A_psl_typeDet (d := d) (d₁ := mb) (m := m) (F₀ := K') (E := E)
        hd hm hK' ψ
    have hdeg1 : blockDegree (Algebra.adjoin K
        (Units.val '' ({b} : Set (GL ι K)))) e = 1 :=
      CFSG.StandardType.TableCRes.blockDegree_eq_one_of_pow_eq_pow hp hpF hS hoddS hpow he
    have hdb_one : db = 1 := hblockdeg.symm.trans hdeg1
    have hEcardK : Nat.card E = Nat.card K ^ db := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcardE]
    have hcardK'_eq : Nat.card K' = Nat.card K := by
      calc Nat.card K' = Nat.card E := hEcardK'.symm
        _ = Nat.card K ^ db := hEcardK
        _ = Nat.card K ^ 1 := by rw [hdb_one]
        _ = Nat.card K := pow_one _
    have hee' : e * e' = 0 := by
      rw [he'eq]
      exact (Geo.mul_formAdj_eq_zero_of_dualPair (RingHom.id K) (fun _ => rfl) hG
        (by simpa [Matrix.map_id] using hGt) hSUmap hS he hpair).1
    have he'e : e' * e = 0 := by
      rw [he'eq]
      exact (Geo.mul_formAdj_eq_zero_of_dualPair (RingHom.id K) (fun _ => rfl) hG
        (by simpa [Matrix.map_id] using hGt) hSUmap hS he hpair).2
    have hquad : ∀ x : ι → K, Φ (Matrix.mulVec e x) = 0 := by
      obtain ⟨s', hs', c, hsce, hcne⟩ := Geo.exists_eigen_mul_ne_one_of_dualPair
        (RingHom.id K) (fun _ => rfl) hG (by simpa [Matrix.map_id] using hGt) hSUmap hS he
        hdeg1 hpair
      rw [Set.mem_singleton_iff] at hs'
      subst hs'
      have hc' : c * c ≠ 1 := by simpa using hcne
      intro x
      have hiso : Φ (Matrix.mulVec (b : Matrix ι ι K) (Matrix.mulVec e x)) =
          Φ (Matrix.mulVec e x) :=
        CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.isometry_of_mem_statedOmega
          (f := ⇑Φ) hb (Matrix.mulVec e x)
      have hsm : Matrix.mulVec (b : Matrix ι ι K) (Matrix.mulVec e x) =
          c • Matrix.mulVec e x := by
        rw [Matrix.mulVec_mulVec, hsce, Matrix.smul_mulVec]
      rw [hsm] at hiso
      have hiso' : c * c * Φ (Matrix.mulVec e x) = Φ (Matrix.mulVec e x) := by
        simpa [QuadraticMap.map_smul, smul_eq_mul, pow_two] using hiso
      have hcsub : c * c - 1 ≠ 0 := sub_ne_zero.mpr hc'
      have hsub : (c * c - 1) * Φ (Matrix.mulVec e x) = 0 := by
        rw [sub_mul, one_mul, hiso', sub_self]
      exact (mul_eq_zero.mp hsub).resolve_left hcsub
    refine ⟨hcardK'_eq, ?_⟩
    have hsing : ∀ y ∈ LinearMap.range (Matrix.toLin' e), Φ y = 0 := by
      rintro y ⟨x, rfl⟩
      exact hquad x
    have hfin_rank : ∀ M : Matrix ι ι K,
        Module.finrank K (LinearMap.range (Matrix.toLin' M)) = M.rank := by
      intro M
      rw [Matrix.toLin'_apply']
      rfl
    have hGinv : IsUnit (G⁻¹).det := Matrix.isUnit_nonsing_inv_det G hG
    have hrank_adj : (formAdj (RingHom.id K) G e).rank = e.rank := by
      have hmap : e.map (RingHom.id K) = e := by ext i j; rfl
      rw [formAdj, hmap]
      calc (G⁻¹ * Matrix.transpose e * G).rank
          = (G⁻¹ * Matrix.transpose e).rank :=
            Matrix.rank_mul_eq_left_of_isUnit_det G _ hG
        _ = (Matrix.transpose e).rank :=
            Matrix.rank_mul_eq_right_of_isUnit_det G⁻¹ _ hGinv
        _ = e.rank := Matrix.rank_transpose e
    have hfin_e' : Module.finrank K (LinearMap.range (Matrix.toLin' e')) =
        Module.finrank K (LinearMap.range (Matrix.toLin' e)) := by
      rw [he'eq]
      calc Module.finrank K (LinearMap.range (Matrix.toLin' (formAdj (RingHom.id K) G e)))
          = (formAdj (RingHom.id K) G e).rank := hfin_rank _
        _ = e.rank := hrank_adj
        _ = Module.finrank K (LinearMap.range (Matrix.toLin' e)) := (hfin_rank _).symm
    have hεe_mul_e : ε * e = e := by
      rw [hεe, Matrix.add_mul, he.2.1.eq, he'e, add_zero]
    have hεe_mul_e' : ε * e' = e' := by
      rw [hεe, Matrix.add_mul, hee', zero_add, he'.2.1.eq]
    have hinf : LinearMap.range (Matrix.toLin' e) ⊓ LinearMap.range (Matrix.toLin' e') = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro x ⟨hx, hx'⟩
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hx'
      have hxid : Matrix.mulVec e x = x := by
        rw [← hu, Matrix.toLin'_apply, Matrix.mulVec_mulVec, he.2.1.eq]
      have hzero : Matrix.mulVec e x = 0 := by
        rw [← hv, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hee', Matrix.zero_mulVec]
      rw [← hxid, hzero]
    have hsup : LinearMap.range (Matrix.toLin' ε) =
        LinearMap.range (Matrix.toLin' e) ⊔ LinearMap.range (Matrix.toLin' e') := by
      apply le_antisymm
      · rintro y ⟨x, rfl⟩
        rw [Matrix.toLin'_apply, hεe, Matrix.add_mulVec]
        exact Submodule.add_mem_sup
          ⟨x, Matrix.toLin'_apply e x⟩ ⟨x, Matrix.toLin'_apply e' x⟩
      · rw [sup_le_iff]
        constructor
        · rintro y ⟨x, rfl⟩
          refine ⟨Matrix.mulVec e x, ?_⟩
          simp only [Matrix.toLin'_apply]
          rw [Matrix.mulVec_mulVec, hεe_mul_e]
        · rintro y ⟨x, rfl⟩
          refine ⟨Matrix.mulVec e' x, ?_⟩
          simp only [Matrix.toLin'_apply]
          rw [Matrix.mulVec_mulVec, hεe_mul_e']
    have hfin_sup : Module.finrank K (LinearMap.range (Matrix.toLin' e)) +
        Module.finrank K (LinearMap.range (Matrix.toLin' e')) =
        Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
      rw [hsup]
      have h := Submodule.finrank_sup_add_finrank_inf_eq
        (LinearMap.range (Matrix.toLin' e)) (LinearMap.range (Matrix.toLin' e'))
      rw [hinf, finrank_bot, add_zero] at h
      exact h.symm
    have hdim' : 2 * d = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
      have h := hdim
      rw [hdb_one, hmbd] at h
      omega
    have hfin_e : Module.finrank K (LinearMap.range (Matrix.toLin' e)) = d := by
      have h2 : Module.finrank K (LinearMap.range (Matrix.toLin' e)) +
          Module.finrank K (LinearMap.range (Matrix.toLin' e')) = 2 * d := by
        rw [hfin_sup, hdim']
      omega
    calc d = Module.finrank K (LinearMap.range (Matrix.toLin' e)) := hfin_e.symm
      _ ≤ w := hw _ hsing

end CFSG.StandardType
