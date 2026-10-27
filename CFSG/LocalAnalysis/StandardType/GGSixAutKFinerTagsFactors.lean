module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsBasic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClLift

public section

namespace CFSG.StandardType

namespace LayerExcThree

open Matrix LayerCores CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ComponentClassification.PresentationLocal

theorem ggNotExcThree_gl {D : Type} [Field D] [Finite D] [CharP D 2] {m : ℕ}
    {M : Subgroup (GL (Fin m) D)}
    (hder : ∃ k, LayerFacts.ggDer (⊤ : Subgroup (GL (Fin m) D)) k ≤ M)
    (hq : CFSG.IsQuasisimple M) : GGNotExcThreeOrder (ggCQ M) := by
  classical
  by_cases hg : 2 ≤ m ∧ (3 ≤ m ∨ ∃ s : Finset D, s.card = 4)
  · set X := (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) D →* GL (Fin m) D).range
      with hX
    have hXq : CFSG.IsQuasisimple X := CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective)
      (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hg.1 hg.2)
    obtain ⟨k, hk⟩ := hder
    have hXM : X ≤ M :=
      ClNonsplit.le_of_ggDer_le (LayerFacts.ggCommutator_eq_of_isQuasisimple hXq) le_top hk
    have hMX : M ≤ X := by
      rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple hq, hX,
        SpecialLinearGroup.range_toGL_eq_ker_det]
      exact (Subgroup.commutator_mono le_top le_top).trans (Abelianization.commutator_subset_ker _)
    obtain ⟨a, ha1, ha⟩ := exists_card_eq_two_pow D
    rw [le_antisymm hMX hXM, hX, ggCQ_range_toGL (by omega), ha]
    exact ggAKFG_ordSL_good hg.1 ha1
  · exfalso
    have : Group.IsSolvable (GL (Fin m) D) :=
      LayerFacts.isSolvable_of_not_goodBlock (E := fun _ : Unit => D) (m := fun _ => m)
        (b := ()) hg
    exact ClNonsplit.not_isQuasisimple_of_le (U := ⊤)
      (Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)) le_top hq

theorem ggNotExcThree_alt {D : Type} [Field D] [Finite D] [CharP D 2] {d : ℕ}
    {T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D} (hT : IsInvol T)
    (h1 : ∀ c : D, T (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin d) c)
    (hy : ∃ y, y + T y = 1) (hD : 4 ≤ Nat.card D) {M : Subgroup (GL (Fin d) D)}
    (hMle : M ≤ matUnitary hT) (hder : ∃ k, LayerFacts.ggDer (matUnitary hT) k ≤ M)
    (hq : CFSG.IsQuasisimple M) (hz : ∀ z ∈ M, (∀ y ∈ M, z * y = y * z) → z ^ 2 = 1 → z = 1) :
    GGNotExcThreeOrder (ggCQ M) := by
  classical
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exfalso
    have : Subsingleton (GL (Fin 0) D) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    obtain ⟨a, b, hab⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hq
    exact hab (Subsingleton.elim _ _)
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
  obtain ⟨s, hs, ⟨eS⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  rw [hfr] at hs
  have hs1 : 1 ≤ s := by omega
  have hqU : CFSG.IsQuasisimple (matUnitary hT) := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
    (CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hB hn
      (by omega) (Or.inl hD))
  obtain ⟨k, hk⟩ := hder
  have hUM : matUnitary hT ≤ M :=
    ClNonsplit.le_of_ggDer_le (LayerFacts.ggCommutator_eq_of_isQuasisimple hqU) le_rfl hk
  have hMeq : M = matUnitary hT := le_antisymm hMle hUM
  obtain ⟨a, -, ha⟩ := exists_card_eq_two_pow D
  have ha2 : 2 ≤ a := by
    by_contra hlt
    have h3 : 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : Finite (GL (Fin d) D) := inferInstance
  refine ggNotExcThreeOrder_of_card hz fun N₀ z hN₀ hz' heq => ?_
  have hcardM : Nat.card M =
      (2 ^ a) ^ (s ^ 2) * ∏ j ∈ Finset.Icc 1 s, ((2 ^ a) ^ (2 * j) - 1) := by
    rw [hMeq, Nat.card_congr (e.trans eS).toEquiv, SymplecticFlag.card_statedSp, ha]
  exact ggAKFG_ordSp_ne ha2 hs1 hN₀ hz' (hcardM.symm.trans heq)

theorem ggNotExcThree_herm {D : Type} [Field D] [Finite D] [CharP D 2] {d : ℕ}
    {T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D} (hT : IsInvol T)
    (hk : ∃ c : D, T (Matrix.scalar (Fin d) c) ≠ Matrix.scalar (Fin d) c)
    (hD : 16 ≤ Nat.card D) {M : Subgroup (GL (Fin d) D)}
    (hMle : M ≤ matUnitary hT) (hder : ∃ k, LayerFacts.ggDer (matUnitary hT) k ≤ M)
    (hq : CFSG.IsQuasisimple M) (hz : ∀ z ∈ M, (∀ y ∈ M, z * y = y * z) → z ^ 2 = 1 → z = 1) :
    GGNotExcThreeOrder (ggCQ M) := by
  classical
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
  obtain ⟨μ, hμ0, hμ⟩ := exists_hilbert90 ρ hρ2 hρ1 hl
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
  have hSU : gramSU hE G ≤ matUnitary hT := fun g hg => (hU g).mpr hg.1
  have hcard : Nat.card D = (2 ^ f') ^ 2 := hE.card_eq_sq
  have hf' : 2 ≤ f' := by
    by_contra hlt
    have h1 : 2 ^ f' ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (2 ^ f') ^ 2 ≤ (2 ^ 1) ^ 2 := Nat.pow_le_pow_left h1 2
    omega
  have h4f : 4 ≤ 2 ^ f' := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f' := Nat.pow_le_pow_right (by norm_num) hf'
  by_cases hd1 : d = 1
  · subst hd1
    exfalso
    have : Group.IsSolvable (GL (Fin 1) D) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable 1 D
        (Or.inl rfl)
    exact ClNonsplit.not_isQuasisimple_of_le (U := ⊤)
      (Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)) le_top hq
  have hd2 : 2 ≤ d := by omega
  have hqX := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE
    hBs hBl (by rw [hfr]; exact hd2) ⟨fun _ => h4f, fun _ => le_trans (by norm_num) h4f⟩
  let eSU := ((gramSU hE G).equivMapOfInjective _ Matrix.GeneralLinearGroup.toLin.injective).trans
    (MulEquiv.subgroupCongr (map_toLin_gramSU hE G))
  have hXq : CFSG.IsQuasisimple (gramSU hE G) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eSU.symm hqX
  obtain ⟨k, hk⟩ := hder
  have hXM : gramSU hE G ≤ M :=
    ClNonsplit.le_of_ggDer_le (LayerFacts.ggCommutator_eq_of_isQuasisimple hXq) hSU hk
  have hMX : M ≤ gramSU hE G := by
    intro x hx
    rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple hq] at hx
    have hx' : x ∈ ⁅matUnitary hT, matUnitary hT⁆ := Subgroup.commutator_mono hMle hMle hx
    have hxU : x ∈ matUnitary hT := Subgroup.commutator_le_self _ hx'
    have hxdet : x ∈ (Matrix.GeneralLinearGroup.det : GL (Fin d) D →* Dˣ).ker :=
      ((Subgroup.commutator_mono le_top le_top).trans
        (Abelianization.commutator_subset_ker _)) hx'
    refine ⟨(hU x).mp hxU, ?_⟩
    rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply] at hxdet
    exact hxdet
  have hMeq : M = gramSU hE G := le_antisymm hMX hXM
  have hSUcard := (CFSG.LinearGroups.unitary_full_group_order hE hBs hBl hfr (by omega)).2.1
  have : Finite (GL (Fin d) D) := inferInstance
  refine ggNotExcThreeOrder_of_card hz fun N₀ z hN₀ hz' heq => ?_
  refine ggAKFG_ordSU_ne hf' hd2 hN₀ hz' ?_
  rw [← hSUcard, ← heq, hMeq, Nat.card_congr eSU.toEquiv]

theorem ggNotExcThree_factor {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)] [∀ i, Finite (D i)]
    [∀ i, CharP (D i) 2] {d : Fin r → ℕ} [∀ i, NeZero (d i)] {τ : PiMat D d → PiMat D d}
    (hτ : IsInvol τ) {π : Fin r → Fin r} (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    (hy : ∃ y, y + τ y = 1) {b : Fin r} {M : Subgroup (GL (Fin (d b)) (D b))}
    (hMle : M ≤ factorGroup π hτ hπ b)
    (hder : ∃ k, LayerFacts.ggDer (factorGroup π hτ hπ b) k ≤ M) (hq : CFSG.IsQuasisimple M)
    (hz : ∀ z ∈ M, (∀ y ∈ M, z * y = y * z) → z ^ 2 = 1 → z = 1) (h4 : 4 ≤ Nat.card (D b))
    (h16 : π b = b → (∃ c : D b, tauFix τ b (Matrix.scalar (Fin (d b)) c) ≠
      Matrix.scalar (Fin (d b)) c) → 16 ≤ Nat.card (D b)) :
    GGNotExcThreeOrder (ggCQ M) := by
  by_cases hb : π b = b
  · have hfg : factorGroup π hτ hπ b = matUnitary (isInvol_tauFix hτ hπ hb) := by
      unfold factorGroup
      split_ifs
      rfl
    rw [hfg] at hMle hder
    by_cases hk : ∀ c : D b, tauFix τ b (Matrix.scalar (Fin (d b)) c) =
        Matrix.scalar (Fin (d b)) c
    · obtain ⟨Y, hY⟩ := hy
      have hYb : Y b + tauFix τ b (Y b) = 1 := by
        have h1 := congrFun hY b
        rwa [Pi.add_apply, apply_tau_eq_tauFix hτ hπ hb, Pi.one_apply] at h1
      exact ggNotExcThree_alt (isInvol_tauFix hτ hπ hb) hk ⟨Y b, hYb⟩ h4 hMle hder hq hz
    · push Not at hk
      exact ggNotExcThree_herm (isInvol_tauFix hτ hπ hb) hk (h16 hb hk) hMle hder hq hz
  · have hfg : factorGroup π hτ hπ b = ⊤ := by
      unfold factorGroup
      split_ifs
      rfl
    rw [hfg] at hder
    exact ggNotExcThree_gl hder hq

theorem exists_coreFamily_adjCent_excThree {K : Type} [Field K] [Finite K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι] {A : Subgroup (GL ι K)} (hA : (Nat.card A : K) ≠ 0)
    {adj : Matrix ι ι K → Matrix ι ι K} (hadj : IsInvol adj)
    (hstab : ∀ X : Matrix ι ι K, (∀ g ∈ A, X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * X) →
      ∀ g ∈ A, adj X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * adj X)
    (hsymd : ∃ Y : Matrix ι ι K, (∀ g ∈ A, Y * (g : Matrix ι ι K) = (g : Matrix ι ι K) * Y) ∧
      Y + adj Y = 1) (hK4 : 4 ≤ Nat.card K)
    (hK16 : 16 ≤ Nat.card K ∨ ∀ (c : K) (X : Matrix ι ι K), adj (c • X) = c • adj X) :
    ∃ (β : Type) (S : β → Subgroup (GL ι K)), IsCoreFamily (adjCent A hadj) S ∧
      ∀ c, GGNotExcThreeOrder (ggCQ (S c)) := by
  classical
  obtain ⟨r, D, d, _, _, _, _, _, Φ, τ, hτ, π, hπ, Sf, hΦ, -, hτΦ, himg, hy, hSle, hSn, hder,
    hq⟩ := ClNonsplit.exists_coreData hadj hA hstab hsymd
  have hΦu : Function.Injective (Units.map Φ.toMonoidHom) :=
    Units.map_injective (f := Φ.toMonoidHom) hΦ
  have hF := (ClNonsplit.isCoreFamily_coreOf hτ hπ hSle hSn hder hq).map _ hΦu
  rw [himg] at hF
  refine ⟨_, _, hF, fun c => ?_⟩
  show GGNotExcThreeOrder (ggCQ ((coreOf π hτ Sf c.1).map (Units.map Φ.toMonoidHom)))
  rw [ggCQ_map_of_injective _ hΦu,
    ggCQ_congr (MulEquiv.ofBijective _ (bijective_coreOf hτ hπ hSle c.1))]
  have hqc := (hq c.1).resolve_left c.2.2
  have hKD : Nat.card K ≤ Nat.card (D c.1) :=
    Nat.card_le_card_of_injective _ (algebraMap K (D c.1)).injective
  refine ggNotExcThree_factor hτ hπ hy (hSle c.1) (hder c.1) hqc.1 hqc.2 (hK4.trans hKD)
    fun hb hk => ?_
  rcases hK16 with h16 | hlin
  · exact h16.trans hKD
  · have hτF : ∀ a : K, τ (algebraMap K (PiMat D d) a) = algebraMap K (PiMat D d) a := by
      intro a
      apply hΦ
      rw [hτΦ, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, hlin, hadj.map_one]
    obtain ⟨ρ, hρ, hρ2⟩ := (isInvol_tauFix hτ hπ hb).exists_rho
    have hdvd : Nat.card K ^ 2 - 1 ∣ Nat.card (D c.1) - 1 := by
      refine LayerPDiv.sq_sub_one_dvd_card_sub_one_of_invol ρ hρ2 ?_ fun a => ?_
      · obtain ⟨c', hc'⟩ := hk
        exact ⟨c', fun h => hc' (by rw [hρ, h])⟩
      · apply scalar_injective (d := d c.1)
        rw [← hρ, LayerPDiv.tauFix_scalar_algebraMap hτ hπ hb hτF]
    have h2 : 1 < Nat.card (D c.1) := Finite.one_lt_card
    have h16 : 16 ≤ Nat.card K ^ 2 := by nlinarith
    have hle := Nat.le_of_dvd (by omega) hdvd
    generalize Nat.card K ^ 2 = t at h16 hle
    omega

end LayerExcThree

end CFSG.StandardType
