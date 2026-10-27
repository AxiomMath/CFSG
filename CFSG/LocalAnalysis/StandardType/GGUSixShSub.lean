module

public import CFSG.LocalAnalysis.StandardType.GGTorusFieldTransferSh
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGMain
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGFieldCase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniGeom
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section USixSh

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD
open CFSG.LocalAnalysis.GLTheoremA.FQ (fixF)
open CFSG.LocalAnalysis.GLTheoremA.T156.Uni (Induced subfieldHom subfieldEquiv)

@[expose] def ggUSixShSet {K : Type} [Field K] {n : ℕ} (hKd : UnitaryFieldData 2 n K) :
    Set (MulAut (LargeEvenProj (unitarySU 2 n K 6))) :=
  {φ | ∃ (M : GL (Fin 6) K)
      (hM : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))),
    M ∈ primeFormUnitary hKd (idGram K 6) ∧ UnitSixThreeKG.ShapeBadMat hKd M ∧
      TableB.projConj (unitarySU 2 n K 6) ⟨M, hM⟩ = φ}

theorem ggUSixSh_primeFormUnitary_map {k K : Type} [Field k] [Field K] {m n d : ℕ}
    (hkd : UnitaryFieldData 2 m k) (hKd : UnitaryFieldData 2 n K) (ι : k →+* K)
    (hbar : ∀ b : k, ι (hkd.bar b) = hKd.bar (ι b)) {P : GL (Fin d) k}
    (hP : P ∈ primeFormUnitary hkd (idGram k d)) :
    Matrix.GeneralLinearGroup.map ι P ∈ primeFormUnitary hKd (idGram K d) := by
  rw [mem_primeFormUnitary] at hP ⊢
  rw [Matrix.GeneralLinearGroup.val_map_apply]
  have hmap : ((P : Matrix (Fin d) (Fin d) k).map ι).map hKd.bar =
      ((P : Matrix (Fin d) (Fin d) k).map hkd.bar).map ι := by
    rw [Matrix.map_map, Matrix.map_map]
    rw [show hKd.bar ∘ ι = ι ∘ hkd.bar from funext fun x => (hbar x).symm]
  rw [hmap]
  have hid : (idGram k d).map ι = idGram K d := by simp [idGram]
  rw [← hid, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hP]

theorem ggUSixSh_bar_fixF {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : Odd (orderOf σ))
    (hkd : UnitaryFieldData 2 (n / orderOf σ) (fixF σ)) (hKd : UnitaryFieldData 2 n K)
    (b : fixF σ) : (fixF σ).subtype (hkd.bar b) = hKd.bar ((fixF σ).subtype b) := by
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, map_pow]
  exact (CFSG.LocalAnalysis.GLTheoremA.T156.Uni.fixF_pow hn hK σ hσ b).symm

theorem ggUSixSh_shapeBad_map {k K : Type} [Field k] [Field K] (ι : k →+* K) {τ : Fin 6 → kˣ}
    (h : UnitSixThreeKG.ShapeBad τ) :
    UnitSixThreeKG.ShapeBad (fun i => Units.map ι.toMonoidHom (τ i)) := by
  have hinj : Function.Injective (Units.map ι.toMonoidHom) := Units.map_injective ι.injective
  rcases h with ⟨v₁, v₂, S₁, S₂, hne, hS₁, hS₂, hc₁, hc₂⟩ |
    ⟨v₁, v₂, v₃, S₁, S₂, S₃, h12, h13, h23, hS₁, hS₂, hS₃, hc₁, hc₂, hc₃⟩
  · left
    refine ⟨Units.map ι.toMonoidHom v₁, Units.map ι.toMonoidHom v₂, S₁, S₂, ?_, ?_, ?_,
      hc₁, hc₂⟩
    · exact fun hh => hne (hinj hh)
    · intro i; rw [hS₁]
      exact ⟨fun hh => congrArg (Units.map ι.toMonoidHom) hh, fun hh => hinj hh⟩
    · intro i; rw [hS₂]
      exact ⟨fun hh => congrArg (Units.map ι.toMonoidHom) hh, fun hh => hinj hh⟩
  · right
    refine ⟨Units.map ι.toMonoidHom v₁, Units.map ι.toMonoidHom v₂, Units.map ι.toMonoidHom v₃,
      S₁, S₂, S₃, ?_, ?_, ?_, ?_, ?_, ?_, hc₁, hc₂, hc₃⟩
    · exact fun hh => h12 (hinj hh)
    · exact fun hh => h13 (hinj hh)
    · exact fun hh => h23 (hinj hh)
    · intro i; rw [hS₁]
      exact ⟨fun hh => congrArg (Units.map ι.toMonoidHom) hh, fun hh => hinj hh⟩
    · intro i; rw [hS₂]
      exact ⟨fun hh => congrArg (Units.map ι.toMonoidHom) hh, fun hh => hinj hh⟩
    · intro i; rw [hS₃]
      exact ⟨fun hh => congrArg (Units.map ι.toMonoidHom) hh, fun hh => hinj hh⟩

theorem ggUSixSh_shapeBadMat_map {k K : Type} [Field k] [Field K] {m n : ℕ}
    (hkd : UnitaryFieldData 2 m k) (hKd : UnitaryFieldData 2 n K) (ι : k →+* K)
    (hbar : ∀ b : k, ι (hkd.bar b) = hKd.bar (ι b)) {M : GL (Fin 6) k}
    (h : UnitSixThreeKG.ShapeBadMat hkd M) :
    UnitSixThreeKG.ShapeBadMat hKd (Matrix.GeneralLinearGroup.map ι M) := by
  obtain ⟨P, hP, τ, hMP, hτ⟩ := h
  refine ⟨Matrix.GeneralLinearGroup.map ι P,
    ggUSixSh_primeFormUnitary_map hkd hKd ι hbar hP,
    fun i => Units.map ι.toMonoidHom (τ i), ?_, ggUSixSh_shapeBad_map ι hτ⟩
  rw [← Matrix.GeneralLinearGroup.map_inv, ← Matrix.GeneralLinearGroup.map_mul,
    ← Matrix.GeneralLinearGroup.map_mul, hMP,
    CFSG.LocalAnalysis.GLTheoremA.T156.Uni.map_diagHom]

theorem ggUSixSh_projConj_mem_matConjImage {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {H : Subgroup (GL ι K)} {S : Set (GL ι K)} {A : GL ι K} (hA : A ∈ S)
    (hAN : A ∈ Subgroup.normalizer (H : Set (GL ι K))) :
    TableB.projConj H ⟨A, hAN⟩ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) S := by
  refine ⟨A, hA, ?_⟩
  intro h h' hh'
  change TableB.projConj H ⟨A, hAN⟩ (h : LargeEvenProj H) = (h' : LargeEvenProj H)
  rw [TableB.projConj_mk]
  apply congrArg (fun x : H => (x : LargeEvenProj H))
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  exact hh'.symm

theorem ggUSixSh_projConj_map_subfieldHom {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : Odd (orderOf σ))
    {M₀ : GL (Fin d) (fixF σ)}
    (hM₀ : M₀ ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (n / orderOf σ)) : Set (GL (Fin d) (fixF σ))))
    (hNN : Matrix.GeneralLinearGroup.map (fixF σ).subtype M₀ ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)))
    (s : LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (n / orderOf σ))) :
    TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
        ⟨Matrix.GeneralLinearGroup.map (fixF σ).subtype M₀, hNN⟩ (subfieldHom hn hK σ hσ s) =
      subfieldHom hn hK σ hσ
        ((LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (n / orderOf σ))).normalizerMonoidHom
          ⟨M₀, hM₀⟩ s) := by
  simp only [subfieldHom, MonoidHom.comp_apply]
  change TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
      ⟨(Matrix.GeneralLinearGroup.map (fixF σ).subtype) M₀, hNN⟩
      ((CFSG.LocalAnalysis.GLTheoremA.T156.Uni.subfieldInclusion hn hK σ hσ s) :
        LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) =
    ((CFSG.LocalAnalysis.GLTheoremA.T156.Uni.subfieldInclusion hn hK σ hσ
        ((LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (n / orderOf σ))).normalizerMonoidHom
          ⟨M₀, hM₀⟩ s)) : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
  rw [TableB.projConj_mk]
  refine congrArg (fun x : LargeEvenSUGroup (Fin d) K (2 ^ n) =>
    (x : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) ?_
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe,
    CFSG.LocalAnalysis.GLTheoremA.T156.Uni.coe_subfieldInclusion,
    CFSG.LocalAnalysis.GLTheoremA.T156.Uni.coe_subfieldInclusion,
    Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul,
    Matrix.GeneralLinearGroup.map_inv]

theorem ggUSixSh_eq_projConj_of_restrict {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hd : 3 ≤ d) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K}
    (hσ : Odd (orderOf σ)) (hdq : (d, 2 ^ (n / orderOf σ)) ≠ (3, 2))
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))} (hf : Induced (2 ^ n) σ f)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hφI : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)))
    (hφf : φ * f = f * φ) {M₀ : GL (Fin d) (fixF σ)}
    (hM₀ : M₀ ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (n / orderOf σ)) : Set (GL (Fin d) (fixF σ))))
    (hNG : Matrix.GeneralLinearGroup.map (fixF σ).subtype M₀ ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hNN : Matrix.GeneralLinearGroup.map (fixF σ).subtype M₀ ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)))
    (hres : ∀ (g : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) (hg : g ∈ ggFixDer f),
      (subfieldEquiv hd hn hK hσ hdq hf).symm ⟨φ g, ggFixDer_map_mem hφf hg⟩ =
        TableB.projConj (LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (n / orderOf σ))) ⟨M₀, hM₀⟩
          ((subfieldEquiv hd hn hK hσ hdq hf).symm ⟨g, hg⟩)) :
    φ = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
      ⟨Matrix.GeneralLinearGroup.map (fixF σ).subtype M₀, hNN⟩ := by
  classical
  let H : Subgroup (GL (Fin d) K) := LargeEvenSUGroup (Fin d) K (2 ^ n)
  let H₀ : Subgroup (GL (Fin d) (fixF σ)) :=
    LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (n / orderOf σ))
  let e : LargeEvenProj H₀ ≃* ggFixDer f := subfieldEquiv hd hn hK hσ hdq hf
  let c : MulAut (LargeEvenProj H) :=
    TableB.projConj H ⟨Matrix.GeneralLinearGroup.map (fixF σ).subtype M₀, hNN⟩
  have hrange : (subfieldHom hn hK σ hσ).range = ggFixDer f :=
    CFSG.LocalAnalysis.GLTheoremA.T156.Uni.range_subfieldHom hd hn hK hσ hdq hf
  have hmem : ∀ s : H₀, subfieldHom hn hK σ hσ s ∈ ggFixDer f := by
    intro s
    rw [← hrange]
    exact ⟨s, rfl⟩
  have hφc : ∀ s : H₀, φ (subfieldHom hn hK σ hσ s) = c (subfieldHom hn hK σ hσ s) := by
    intro s
    have hmk : e (QuotientGroup.mk s) = (⟨subfieldHom hn hK σ hσ s, hmem s⟩ : ggFixDer f) :=
      Subtype.ext (CFSG.LocalAnalysis.GLTheoremA.T156.Uni.coe_subfieldEquiv_mk hd hn hK hσ hdq hf s)
    have hmk_coe : ((e (QuotientGroup.mk s) : ggFixDer f) : LargeEvenProj H) =
        subfieldHom hn hK σ hσ s := by
      simpa using congrArg (fun x : ggFixDer f => (x : LargeEvenProj H)) hmk
    have hres_s := hres (e (QuotientGroup.mk s) : LargeEvenProj H) (e (QuotientGroup.mk s)).2
    have h1 : (⟨φ (e (QuotientGroup.mk s)),
          ggFixDer_map_mem hφf (e (QuotientGroup.mk s)).2⟩ : ggFixDer f) =
        e (TableB.projConj H₀ ⟨M₀, hM₀⟩ (e.symm (e (QuotientGroup.mk s)))) := by
      have hh := congrArg (subfieldEquiv hd hn hK hσ hdq hf) hres_s
      simpa only [MulEquiv.apply_symm_apply] using hh
    have h2 : ((e (TableB.projConj H₀ ⟨M₀, hM₀⟩ (e.symm (e (QuotientGroup.mk s)))) :
          ggFixDer f) : LargeEvenProj H) =
        subfieldHom hn hK σ hσ (H₀.normalizerMonoidHom ⟨M₀, hM₀⟩ s) := by
      rw [MulEquiv.symm_apply_apply, TableB.projConj_mk]
      exact CFSG.LocalAnalysis.GLTheoremA.T156.Uni.coe_subfieldEquiv_mk hd hn hK hσ hdq hf
        (H₀.normalizerMonoidHom ⟨M₀, hM₀⟩ s)
    have h3 : φ (e (QuotientGroup.mk s)) =
        subfieldHom hn hK σ hσ (H₀.normalizerMonoidHom ⟨M₀, hM₀⟩ s) := by
      have h1v := congrArg (fun x : ggFixDer f => (x : LargeEvenProj H)) h1
      exact h1v.trans h2
    have hU6 := ggUSixSh_projConj_map_subfieldHom hn hK σ hσ hM₀ hNN s
    calc φ (subfieldHom hn hK σ hσ s)
        = φ ((e (QuotientGroup.mk s) : ggFixDer f) : LargeEvenProj H) := by rw [hmk_coe]
      _ = subfieldHom hn hK σ hσ (H₀.normalizerMonoidHom ⟨M₀, hM₀⟩ s) := h3
      _ = c (subfieldHom hn hK σ hσ s) := hU6.symm
  have hKd : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  have hd1 : 1 ≤ d := by omega
  have hcI : c ∈ LargeEvenMatConjImage (LargeEvenProjMk H) (LargeEvenGUSet (Fin d) K (2 ^ n)) :=
    ggUSixSh_projConj_mem_matConjImage hNG hNN
  have hψI : c⁻¹ * φ ∈
      LargeEvenMatConjImage (LargeEvenProjMk H) (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
    have hcI' : c ∈ (RecipeFieldSU.recIU d hKd hd1 : Set _) := by
      rwa [RecipeFieldSU.coe_recIU hKd hK hd1]
    have hφI' : φ ∈ (RecipeFieldSU.recIU d hKd hd1 : Set _) := by
      rwa [RecipeFieldSU.coe_recIU hKd hK hd1]
    have hprod : c⁻¹ * φ ∈ (RecipeFieldSU.recIU d hKd hd1 : Set _) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hcI') hφI'
    rwa [RecipeFieldSU.coe_recIU hKd hK hd1] at hprod
  have hfix : ∀ s : H₀, (c⁻¹ * φ) (subfieldHom hn hK σ hσ s) = subfieldHom hn hK σ hσ s := by
    intro s
    rw [MulAut.mul_apply, hφc s, MulAut.inv_apply_self]
  have hψ1 : c⁻¹ * φ = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.T156.Uni.eq_one_of_fixes_subfield hd hn hK σ hσ hdq hψI hfix
  rw [inv_mul_eq_one] at hψ1
  exact hψ1.symm

theorem ggUSixSh_fixNotCycOn {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : 3 ∣ 2 ^ n + 1) {σ : K ≃+* K} (hσ : Odd (orderOf σ))
    (hdq : ((6 : ℕ), 2 ^ (n / orderOf σ)) ≠ (3, 2))
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))} (hf : Induced (2 ^ n) σ f)
    (hkd : UnitaryFieldData 2 (n / orderOf σ) (fixF σ)) :
    GGFixNotCycOn 3 (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) f
      (subfieldEquiv (by norm_num : (3 : ℕ) ≤ 6) hn hK hσ hdq hf).symm (ggUSixShSet hkd) := by
  intro φ hφI hφφ φ₀ hφ₀ hres
  obtain ⟨M₀, hM₀, hM₀u, hsh, rfl⟩ := hφ₀
  have hKd : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  have hbar : ∀ b : fixF σ, (fixF σ).subtype (hkd.bar b) = hKd.bar ((fixF σ).subtype b) :=
    ggUSixSh_bar_fixF hn hK σ hσ hkd hKd
  have hNu : Matrix.GeneralLinearGroup.map (fixF σ).subtype M₀ ∈
      primeFormUnitary hKd (idGram K 6) :=
    ggUSixSh_primeFormUnitary_map hkd hKd (fixF σ).subtype hbar hM₀u
  have hNG : Matrix.GeneralLinearGroup.map (fixF σ).subtype M₀ ∈
      LargeEvenGUSet (Fin 6) K (2 ^ n) :=
    TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hNu
  have hNN : Matrix.GeneralLinearGroup.map (fixF σ).subtype M₀ ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin 6) K (2 ^ n) : Set (GL (Fin 6) K)) :=
    TableBUE.gu_subset_normalizer hKd hNG
  have hφeq : φ = TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ n))
      ⟨Matrix.GeneralLinearGroup.map (fixF σ).subtype M₀, hNN⟩ :=
    ggUSixSh_eq_projConj_of_restrict (d := 6) (by norm_num) hn hK hσ hdq hf hφI hφφ
      hM₀ hNG hNN hres
  have hshN : UnitSixThreeKG.ShapeBadMat hKd
      (Matrix.GeneralLinearGroup.map (fixF σ).subtype M₀) :=
    ggUSixSh_shapeBadMat_map hkd hKd (fixF σ).subtype hbar hsh
  exact UnitSixThreeKG.not_ggFixCompCyclic_of_shapeBad hKd hpq (ψ := MonoidHom.id _)
    Function.surjective_id (by simp) hNN hshN (fun l => by rw [hφeq]; rfl)

end USixSh

end CFSG.StandardType
