module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresHerm
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresLinear
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivFactors
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLBasic

public section

namespace CFSG.StandardType

namespace ClNonsplit

open Matrix LayerCores CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section General

variable {G : Type*} [Group G]

theorem le_of_ggDer_le {U S X : Subgroup G} (hX : ⁅X, X⁆ = X) (hXU : X ≤ U) {k : ℕ}
    (hk : LayerFacts.ggDer U k ≤ S) : X ≤ S := by
  rw [← LayerFacts.ggDer_of_perfect hX k]
  exact (LayerFacts.ggDer_mono hXU k).trans hk

theorem not_isQuasisimple_of_le {U S : Subgroup G} (hU : Group.IsSolvable U) (hSU : S ≤ U)
    (hq : CFSG.IsQuasisimple S) : False := by
  obtain ⟨k, hk⟩ := exists_ggDer_eq_bot hU
  have h1 : S ≤ ⊥ :=
    hk ▸ le_of_ggDer_le (LayerFacts.ggCommutator_eq_of_isQuasisimple hq) hSU le_rfl
  obtain ⟨a, b, hab⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hq
  apply hab
  have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.mp (h1 a.2))
  rw [ha, one_mul, mul_one]

theorem eq_one_of_mem_of_not_dvd {S : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hpS : ¬ p ∣ Nat.card S) {g : G} (hg : g ∈ S) (hgp : g ^ p = 1) : g = 1 := by
  have h1 : (⟨g, hg⟩ : S) ^ p = 1 := Subtype.ext (by simpa using hgp)
  have h2 : orderOf (⟨g, hg⟩ : S) = 1 :=
    Nat.eq_one_of_dvd_coprimes ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpS)
      (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_natCard _)
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h2)

end General

theorem eq_one_of_pow_eq_one_gl {E : Type} [Field E] [Finite E] [CharP E 2] {m : ℕ}
    {S : Subgroup (GL (Fin m) E)}
    (hder : ∃ k, LayerFacts.ggDer (⊤ : Subgroup (GL (Fin m) E)) k ≤ S)
    (hq : CFSG.IsQuasisimple S) {p : ℕ} (hp : p.Prime) (hpS : ¬ p ∣ Nat.card S)
    {g : GL (Fin m) E} (hg : g ^ p = 1) : g = 1 := by
  obtain ⟨k, hk⟩ := hder
  by_cases hgood : 2 ≤ m ∧ (3 ≤ m ∨ ∃ s : Finset E, s.card = 4)
  · have hSLq : CFSG.IsQuasisimple
        (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) E →* GL (Fin m) E).range :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective)
        (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hgood.1 hgood.2)
    have hle := le_of_ggDer_le (LayerFacts.ggCommutator_eq_of_isQuasisimple hSLq) le_top hk
    have hpSL : ¬ p ∣ Nat.card (SpecialLinearGroup (Fin m) E) := by
      intro h
      apply hpS
      rw [Nat.card_congr (MonoidHom.ofInjective (SpecialLinearGroup.toGL_injective (n := Fin m)
        (R := E))).toEquiv] at h
      exact h.trans (Subgroup.card_dvd_of_le hle)
    exact LinNonsplit.eq_one_of_pow_eq_one_of_not_dvd hgood.1 hp hpSL hg
  · have : Group.IsSolvable (GL (Fin m) E) :=
      LayerFacts.isSolvable_of_not_goodBlock (E := fun _ : Unit => E) (m := fun _ => m)
        (b := ()) hgood
    exact (not_isQuasisimple_of_le (U := ⊤) inferInstance le_top hq).elim

theorem eq_one_of_pow_eq_one_alt {D : Type} [Field D] [Finite D] [CharP D 2] {d : ℕ}
    {T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D} (hT : IsInvol T)
    (h1 : ∀ c : D, T (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin d) c) (hy : ∃ y, y + T y = 1)
    {S : Subgroup (GL (Fin d) D)} (hSU : S ≤ matUnitary hT)
    (hder : ∃ k, LayerFacts.ggDer (matUnitary hT) k ≤ S) (hq : CFSG.IsQuasisimple S) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpS : ¬ p ∣ Nat.card S) {g : GL (Fin d) D}
    (hg : g ∈ matUnitary hT) (hgp : g ^ p = 1) : g = 1 := by
  classical
  obtain ⟨k, hk⟩ := hder
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have : Subsingleton (GL (Fin 0) D) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    exact Subsingleton.elim _ _
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨H, hH⟩ := hT.exists_gram_id h1
  have hsym := transpose_gram_eq hT H hH
  obtain ⟨y, hy⟩ := hy
  have hHy := gram_eq_add_transpose H hH hsym hy
  have hB : (Matrix.toBilin' (H : Matrix (Fin d) (Fin d) D)).IsAlt := by
    have h2 := isAlt_toBilin'_add_transpose ((H : Matrix (Fin d) (Fin d) D) * y)
    rwa [← hHy] at h2
  have hn := nondegenerate_toBilin'_gram H
  have hmap := map_toLin_matUnitary H hH (hT := hT)
  let e : matUnitary hT ≃* sesqUnitaryGroup (Matrix.toBilin' (H : Matrix (Fin d) (Fin d) D)) :=
    ((matUnitary hT).equivMapOfInjective _ Matrix.GeneralLinearGroup.toLin.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hfr : Module.finrank D (Fin d → D) = d := Module.finrank_fin_fun D
  have hquasi : CFSG.IsQuasisimple (sesqUnitaryGroup (Matrix.toBilin'
      (H : Matrix (Fin d) (Fin d) D))) → g = 1 := by
    intro hqU
    have hU : CFSG.IsQuasisimple (matUnitary hT) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqU
    exact eq_one_of_mem_of_not_dvd hp hpS
      (le_of_ggDer_le (LayerFacts.ggCommutator_eq_of_isQuasisimple hU) le_rfl hk hg) hgp
  obtain ⟨s, hs, -⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  rw [hfr] at hs
  rcases card_eq_two_or_four_le (D := D) with hD2 | hD4
  · by_cases h6 : 6 ≤ d
    · exact hquasi (CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hB hn
        (by omega) (Or.inr (Or.inr ⟨hD2, by omega⟩)))
    rcases (show d = 2 ∨ d = 4 by omega) with hd2 | hd4
    · subst hd2
      have : Group.IsSolvable (GL (Fin 2) D) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable 2 D
          (Or.inr ⟨rfl, Or.inl hD2⟩)
      exact (not_isQuasisimple_of_le (U := matUnitary hT) inferInstance hSU hq).elim
    ·
      obtain ⟨E⟩ := CFSG.RankThree.PartOne.nonempty_mulEquiv_sympFour hD2 hB hn (by rw [hfr, hd4])
      obtain ⟨hqc, hodd⟩ := CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour (e.trans E)
      set U := matUnitary hT with hUdef
      have hgc : (⟨g, hg⟩ : U) ∈ commutator U :=
        hodd hp hp2 _ (Subtype.ext (by simpa using hgp))
      let eS : ↥(commutator ↥U) ≃* ↥⁅U, U⁆ :=
        ((commutator ↥U).equivMapOfInjective U.subtype U.subtype_injective).trans
          (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator U))
      have hqS : CFSG.IsQuasisimple ↥⁅U, U⁆ := CFSG.LocalCores.isQuasisimple_of_mulEquiv eS hqc
      have hle := le_of_ggDer_le (LayerFacts.ggCommutator_eq_of_isQuasisimple hqS)
        (Subgroup.commutator_le_self U) hk
      have hgmem : g ∈ ⁅U, U⁆ := by
        rw [← Subgroup.map_subtype_commutator]
        exact ⟨_, hgc, rfl⟩
      exact eq_one_of_mem_of_not_dvd hp hpS (hle hgmem) hgp
  · exact hquasi (CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hB hn
      (by omega) (Or.inl hD4))

theorem mem_core_of_pow_eq_one_herm {D : Type} [Field D] [Finite D] [CharP D 2] {d : ℕ}
    {T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D} (hT : IsInvol T)
    (hk : ∃ c : D, T (Matrix.scalar (Fin d) c) ≠ Matrix.scalar (Fin d) c)
    {S : Subgroup (GL (Fin d) D)} (hSU : S ≤ matUnitary hT)
    (hder : ∃ k, LayerFacts.ggDer (matUnitary hT) k ≤ S) (hq : CFSG.IsQuasisimple S) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpD : ¬ p ∣ Nat.card D - 1) {g : GL (Fin d) D}
    (hg : g ∈ matUnitary hT) (hgp : g ^ p = 1) : g ∈ S := by
  classical
  obtain ⟨kS, hkS⟩ := hder
  have hdet : (g : Matrix (Fin d) (Fin d) D).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det g ^ p = 1 := by rw [← map_pow, hgp, map_one]
    have h2 : Matrix.GeneralLinearGroup.det g = 1 := by
      rw [← orderOf_eq_one_iff]
      exact Nat.eq_one_of_dvd_coprimes (LinNonsplit.coprime_card_units hp hpD).symm
        (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_natCard _)
    have h3 := congrArg Units.val h2
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h3
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exfalso
    obtain ⟨c, hc⟩ := hk
    exact hc (Subsingleton.elim _ _)
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨ρ, hρ, hρ2⟩ := hT.exists_rho
  have hρ1 : ∃ c, ρ c ≠ c := by
    obtain ⟨c, hc⟩ := hk
    exact ⟨c, fun h => hc (by rw [hρ, h])⟩
  obtain ⟨H, hH⟩ := hT.exists_gram ρ hρ hρ2
  obtain ⟨f', hE, hbar⟩ := exists_unitaryFieldData_of_invol ρ hρ2 hρ1
  obtain ⟨l, hlH, hl⟩ := exists_ct_gram_eq hT ρ hρ2 H hH
  obtain ⟨μ, hμ0, hμ⟩ := LayerCores.exists_hilbert90 ρ hρ2 hρ1 hl
  set G : Matrix (Fin d) (Fin d) D := μ • (H : Matrix (Fin d) (Fin d) D) with hGdef
  have hct : ∀ x : Matrix (Fin d) (Fin d) D, (x.map hE.bar)ᵀ = ct ρ x := fun x => by
    rw [show (⇑hE.bar : D → D) = ⇑ρ from funext hbar]
    rfl
  have hG : (G.map hE.bar)ᵀ = G := by
    rw [hct, hGdef, ct_smul, hlH, smul_smul, hμ]
  have hHdet : (H : Matrix (Fin d) (Fin d) D).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp H.isUnit).ne_zero
  have hGdet : G.det ≠ 0 := by
    rw [hGdef, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hμ0) hHdet
  have hMMi : (H : Matrix (Fin d) (Fin d) D) * ((H⁻¹ : GL (Fin d) D) :
      Matrix (Fin d) (Fin d) D) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : ((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) *
      (H : Matrix (Fin d) (Fin d) D) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hU : ∀ g : GL (Fin d) D, g ∈ matUnitary hT ↔
      ((g : Matrix (Fin d) (Fin d) D).map hE.bar)ᵀ * G * g = G := by
    intro g
    rw [mem_matUnitary, hH, hct, hGdef, Matrix.mul_smul, Matrix.smul_mul]
    constructor
    · intro h
      congr 1
      calc ct ρ (g : Matrix (Fin d) (Fin d) D) * H * g
          = H * (((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) *
            ((g : Matrix (Fin d) (Fin d) D).map ρ)ᵀ * H * g) := by
            simp only [← Matrix.mul_assoc, hMMi, Matrix.one_mul]
            rfl
        _ = H := by rw [h, Matrix.mul_one]
    · intro h
      have h1 : ct ρ (g : Matrix (Fin d) (Fin d) D) * H * g = H := smul_right_injective _ hμ0 h
      calc ((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) *
            ((g : Matrix (Fin d) (Fin d) D).map ρ)ᵀ * H * g
          = ((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) *
            (ct ρ (g : Matrix (Fin d) (Fin d) D) * H * g) := by
            simp only [Matrix.mul_assoc]
            rfl
        _ = 1 := by rw [h1, hMiM]
  have hBs : (gramForm hE G).IsSymm := gramForm_isSymm hE hG
  have hBl : (gramForm hE G).SeparatingLeft := gramForm_separatingLeft hE hGdet
  have hfr : Module.finrank D (Fin d → D) = d := Module.finrank_fin_fun D
  have hmapU := map_toLin_eq_sesqUnitaryGroup hE G hU
  have hq2 : 2 ≤ 2 ^ f' := by
    have := Nat.one_lt_two_pow (n := f') (by have := hE.one_le; omega)
    omega
  have hcard : Nat.card D = (2 ^ f') ^ 2 := hE.card_eq_sq
  by_cases hgood : 2 ≤ d ∧ ¬ (d ≤ 3 ∧ Nat.card D = 4)
  · have hq4 : d ≤ 3 → 4 ≤ 2 ^ f' := by
      intro h3
      have h4 : Nat.card D ≠ 4 := fun h4 => hgood.2 ⟨h3, h4⟩
      by_contra hlt
      have hf1 : f' = 1 := by
        by_contra hne
        have h2f : 2 ≤ f' := by have := hE.one_le; omega
        have : 2 ^ 2 ≤ 2 ^ f' := Nat.pow_le_pow_right (by norm_num) h2f
        omega
      rw [hcard, hf1] at h4
      exact h4 rfl
    have hqSU := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE
      hBs hBl (by rw [hfr]; exact hgood.1)
      ⟨fun h => hq4 (by rw [hfr] at h; omega), fun h => le_trans (by norm_num)
        (hq4 (by rw [hfr] at h; omega))⟩
    have hqG : CFSG.IsQuasisimple (gramSU hE G) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (((gramSU hE G).equivMapOfInjective _ Matrix.GeneralLinearGroup.toLin.injective).trans
          (MulEquiv.subgroupCongr (map_toLin_gramSU hE G))).symm hqSU
    have hSU' : gramSU hE G ≤ matUnitary hT := fun g hg => (hU g).mpr hg.1
    have hle := le_of_ggDer_le (LayerFacts.ggCommutator_eq_of_isQuasisimple hqG) hSU' hkS
    exact hle ⟨(hU g).mp hg, hdet⟩
  · by_cases hd1 : d = 1
    · subst hd1
      have : Group.IsSolvable (GL (Fin 1) D) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable 1 D
          (Or.inl rfl)
      exact (not_isQuasisimple_of_le (U := matUnitary hT) inferInstance hSU hq).elim
    have hd23 : d = 2 ∨ d = 3 := by omega
    have hD4 : Nat.card D = 4 := by
      by_contra h
      exact hgood ⟨by omega, fun h' => h h'.2⟩
    have hq : 2 ^ f' = 2 := by
      rw [hcard] at hD4
      nlinarith
    have hcardU : Nat.card (matUnitary hT) = 18 ∨ Nat.card (matUnitary hT) = 648 := by
      have h1 := (CFSG.LinearGroups.unitary_full_group_order hE hBs hBl hfr (by omega)).1
      have h2 : Nat.card (matUnitary hT) = Nat.card (sesqUnitaryGroup (gramForm hE G)) :=
        Nat.card_congr (((matUnitary hT).equivMapOfInjective _
          Matrix.GeneralLinearGroup.toLin.injective).trans
            (MulEquiv.subgroupCongr hmapU)).toEquiv
      rw [hq] at h1
      rcases hd23 with rfl | rfl
      · left
        have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
            ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by decide +kernel
        rw [h2]
        exact_mod_cast h1.trans e
      · right
        have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
            ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by decide +kernel
        rw [h2]
        exact_mod_cast h1.trans e
    have hp3 : ¬ p ∣ 3 := by rwa [hD4] at hpD
    have hpU : ¬ p ∣ Nat.card (matUnitary hT) := by
      have h23 : ∀ a b : ℕ, p ∣ 2 ^ a * 3 ^ b → False := by
        intro a b h
        rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
        · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h'))
        · exact hp3 (hp.dvd_of_dvd_pow h')
      rcases hcardU with h | h
      · rw [h, show (18 : ℕ) = 2 ^ 1 * 3 ^ 2 by norm_num]
        exact fun h' => h23 1 2 h'
      · rw [h, show (648 : ℕ) = 2 ^ 3 * 3 ^ 4 by norm_num]
        exact fun h' => h23 3 4 h'
    rw [eq_one_of_mem_of_not_dvd hp hpU hg hgp]
    exact S.one_mem

theorem eq_one_of_pow_eq_one_herm {D : Type} [Field D] [Finite D] [CharP D 2] {d : ℕ}
    {T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D} (hT : IsInvol T)
    (hk : ∃ c : D, T (Matrix.scalar (Fin d) c) ≠ Matrix.scalar (Fin d) c)
    {S : Subgroup (GL (Fin d) D)} (hSU : S ≤ matUnitary hT)
    (hder : ∃ k, LayerFacts.ggDer (matUnitary hT) k ≤ S) (hq : CFSG.IsQuasisimple S) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpS : ¬ p ∣ Nat.card S) {g : GL (Fin d) D}
    (hg : g ∈ matUnitary hT) (hgp : g ^ p = 1) : g = 1 := by
  obtain ⟨kS, hkS⟩ := hder
  have hpD : ¬ p ∣ Nat.card D - 1 := by
    rcases LayerPDiv.hermFactorPDivInput_holds D d T hT hk with hsol | ⟨X, hX1, hX2, hX3⟩
    · exact (not_isQuasisimple_of_le hsol hSU hq).elim
    · intro h
      exact hpS ((h.trans hX3).trans (Subgroup.card_dvd_of_le (le_of_ggDer_le hX2 hX1 hkS)))
  exact eq_one_of_mem_of_not_dvd hp hpS
    (mem_core_of_pow_eq_one_herm hT hk hSU ⟨kS, hkS⟩ hq hp hp2 hpD hg hgp) hgp

end ClNonsplit

end CFSG.StandardType
