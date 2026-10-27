module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitRealizationStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2UnitDiag

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SectionRank.OddCover (diagHom det_diagHom)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K] {N : ℕ} {ζ : Multiplicative (ZMod 3) →* Kˣ}

theorem diagOf_mem_blockSU (h : UnitaryFieldData 2 1 K) {N : ℕ}
    (ζ : Multiplicative (ZMod 3) →* Kˣ) {S : Finset (Fin N)} {w : UnitRaw.W N}
    (hS : ∀ i, i ∉ S → w i = 0) (hw : ∑ i, w i = 0) :
    (⟨diagOf ζ w, diagOf_mem_unitarySU ζ h hw⟩ : ↥(unitarySU 2 1 K N)) ∈
      TableBUE.blockSU (K := K) (n := 1) S := by
  rw [TableBUE.mem_blockSU]
  intro a b hab
  rw [coe_diagOf, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hab' : a = b
  · subst hab'
    have ha : a ∉ S := by
      rcases hab with h' | h'
      · exact h'
      · exact h'
    rw [if_pos rfl, if_pos rfl, hS a ha]
    simp
  · rw [if_neg hab', if_neg hab']

private lemma ubk_perm_conj_diag (d : Fin N → Kˣ) (σ : Equiv.Perm (Fin N)) :
    (CFSG.RankThree.Classical.permGL σ : GL (Fin N) K)⁻¹ * diagHom N d *
        CFSG.RankThree.Classical.permGL σ * (diagHom N d)⁻¹ =
      diagHom N (fun i => d (σ i) * (d i)⁻¹) := by
  have h1 : (CFSG.RankThree.Classical.permGL σ : GL (Fin N) K)⁻¹ * diagHom N d *
      CFSG.RankThree.Classical.permGL σ = diagHom N (d ∘ ⇑σ) := by
    have h := CFSG.RankThree.Classical2.permGL_mul_diagHom_mul_inv (K := K) (n := N) σ⁻¹ d
    have hσ : ((σ⁻¹ : Equiv.Perm (Fin N)).symm) = σ := Equiv.symm_symm σ
    rw [hσ] at h
    simpa [map_inv] using h
  rw [h1, ← map_inv (diagHom N), ← map_mul]
  rfl

private lemma ubk_diagHom_entry {d : Fin N → Kˣ} {c : Kˣ}
    (h : (diagHom N d : GL (Fin N) K) = GeneralLinearGroup.scalar (Fin N) c) (i : Fin N) :
    d i = c := by
  apply Units.ext
  have h1 := congrArg (fun g : GL (Fin N) K => ((g : Matrix (Fin N) (Fin N) K) i i)) h
  simpa [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h1

private lemma ubk_w_eq_of_fixes_swap (h : UnitaryFieldData 2 1 K)
    (hζ : Function.Injective ζ) {w : UnitRaw.W N}
    {hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))}
    {i j k : Fin N} (hki : k ≠ i) (hkj : k ≠ j)
    (hfix : TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩
      (LargeEvenProjMk _ ⟨CFSG.RankThree.Classical.permGL (Equiv.swap i j),
        TableBUE.permGL_swap_mem h i j⟩) =
      LargeEvenProjMk _ ⟨CFSG.RankThree.Classical.permGL (Equiv.swap i j),
        TableBUE.permGL_swap_mem h i j⟩) :
    w i = w j := by
  classical
  let σ : Equiv.Perm (Fin N) := Equiv.swap i j
  let P : GL (Fin N) K := CFSG.RankThree.Classical.permGL σ
  let x : ↥(unitarySU 2 1 K N) := ⟨P, TableBUE.permGL_swap_mem h i j⟩
  let d : Fin N → Kˣ := fun l => ζ (Multiplicative.ofAdd (w l))
  let D : GL (Fin N) K := diagHom N d
  let H : Subgroup (GL (Fin N) K) := unitarySU 2 1 K N
  let A : ↥(Subgroup.normalizer (H : Set (GL (Fin N) K))) := ⟨D, hD⟩
  let X : ↥H := (H.normalizerMonoidHom A) x
  have hxP : ((x : ↥H) : GL (Fin N) K) = P := rfl
  have hXD : ((X : ↥H) : GL (Fin N) K) = D * P * D⁻¹ := rfl
  have hfix' : LargeEvenProjMk H X = LargeEvenProjMk H x := by
    have htmp : TableB.projConj H A (LargeEvenProjMk H x) =
        LargeEvenProjMk H ((H.normalizerMonoidHom A) x) := TableB.projConj_mk H A x
    exact htmp.symm.trans hfix
  obtain ⟨c, hc⟩ := TableBUD.exists_scalar_of_mk_eq hfix'.symm
  have hc' : P⁻¹ * D * P * D⁻¹ = GeneralLinearGroup.scalar (Fin N) c := by
    rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv, hxP, hXD]
    group
  have hdiagD : P⁻¹ * D * P * D⁻¹ = diagHom N (fun l => d (σ l) * (d l)⁻¹) := by
    simpa [P, D] using ubk_perm_conj_diag (K := K) d σ
  have hmat : diagHom N (fun l => d (σ l) * (d l)⁻¹) =
      GeneralLinearGroup.scalar (Fin N) c := hdiagD.symm.trans hc'
  have hσk : σ k = k := by
    simp [σ, Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hσi : σ i = j := by simp [σ]
  have hck : c = 1 := by
    rw [← ubk_diagHom_entry hmat k, hσk, mul_inv_cancel]
  have hci : d (σ i) * (d i)⁻¹ = 1 := by
    rw [ubk_diagHom_entry hmat i, hck]
  have hdj : d i = d j := by
    rw [hσi] at hci
    exact (eq_of_mul_inv_eq_one hci).symm
  exact Multiplicative.ofAdd.injective (hζ hdj)

private lemma ubk_fixes_of_constOn
    {S : Finset (Fin N)} {w : UnitRaw.W N}
    {hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))}
    (hw : ∀ i ∈ S, ∀ j ∈ S, w i = w j) :
    ∀ y ∈ blockPSU (K := K) S,
      TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ y = y := by
  intro y hy
  simp only [blockPSU] at hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  have hxblock : TableBUE.IsBlockOn S ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) :=
    TableBUE.mem_blockSU.mp hx
  have hcomm : diagOf ζ w * (x : GL (Fin N) K) = (x : GL (Fin N) K) * diagOf ζ w :=
    TableBUE.diagHom_mul_comm_of_isBlockOn
      (σ := fun l => ζ (Multiplicative.ofAdd (w l)))
      (fun i hi j hj => by rw [hw i hi j hj]) hxblock
  rw [TableBUD.projConj_mk_coe]
  have hval : ((unitarySU 2 1 K N).normalizerMonoidHom ⟨diagOf ζ w, hD⟩) x = x := by
    apply Subtype.ext
    show diagOf ζ w * (x : GL (Fin N) K) * (diagOf ζ w)⁻¹ = (x : GL (Fin N) K)
    rw [hcomm]
    group
  rw [hval]

theorem unitBlockFixIff_holds :
    ∀ {K : Type} [Field K] [Finite K] (ζ : Multiplicative (ZMod 3) →* Kˣ) (N : ℕ),
      Nat.card K = 4 → Function.Injective ζ → 5 ≤ N →
      ∀ S : Finset (Fin N), UnitRaw.admissible S → ∀ (w : UnitRaw.W N)
        (hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))),
        (∀ y ∈ blockPSU (K := K) S, TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ y = y) ↔
          (UnitRaw.oneLine N).mkQ w ∈ UnitRaw.cent S := by
  intro K _ _ ζ N hK hζ hN S hS w hD
  have h : UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card (by rw [hK]; norm_num) le_rfl
  constructor
  · intro hfix
    rw [UnitRaw.mem_cent_iff]
    refine ⟨w, rfl, ?_⟩
    intro i hi j hj
    by_cases hij : i = j
    · subst hij
      rfl
    · have hmem : 0 < ((S.erase i).erase j).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩),
          Finset.card_erase_of_mem hi]
        have hS' : 4 ≤ S.card := hS
        omega
      obtain ⟨k, hk⟩ := Finset.card_pos.mp hmem
      simp only [Finset.mem_erase] at hk
      obtain ⟨hkj, hki, -⟩ := hk
      refine ubk_w_eq_of_fixes_swap (hD := hD) h hζ hki hkj ?_
      exact hfix _ (Subgroup.mem_map.mpr
        ⟨_, TableBUE.mem_blockSU.mpr (TableBUE.isBlockOn_permGL_swap hi hj), rfl⟩)
  · intro hmk
    rw [UnitRaw.mem_cent_iff] at hmk
    obtain ⟨w', hw', hw'c⟩ := hmk
    have hD' : diagOf ζ w' ∈
        Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
      diagOf_mem_normalizer ζ h w'
    have heq : TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ =
        TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', hD'⟩ := by
      have hsub : (⟨diagOf ζ w, hD⟩ : ↥(Subgroup.normalizer
          (unitarySU 2 1 K N : Set (GL (Fin N) K)))) =
          ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ := Subtype.ext rfl
      rw [hsub]
      exact (projConj_diagOf_eq_iff ζ h hK hζ (by omega) w w').mpr hw'.symm
    intro y hy
    rw [heq]
    exact ubk_fixes_of_constOn hw'c y hy

private lemma ubk_diagOf_entry {w : UnitRaw.W N} {z : Kˣ} {B : GL (Fin N) K}
    (h : diagOf ζ w = GeneralLinearGroup.scalar (Fin N) z * B) {i : Fin N}
    (hB : ((B : Matrix (Fin N) (Fin N) K)) i i = 1) :
    ζ (Multiplicative.ofAdd (w i)) = z := by
  apply Units.ext
  have h1 := congrArg (fun g : GL (Fin N) K => ((g : Matrix (Fin N) (Fin N) K) i i)) h
  rw [coe_diagOf, Matrix.diagonal_apply_eq, Units.val_mul,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul,
    hB, mul_one] at h1
  exact h1

private lemma ubk_det_diagOf {w : UnitRaw.W N} {z : Kˣ} {B : GL (Fin N) K}
    (h : diagOf ζ w = GeneralLinearGroup.scalar (Fin N) z * B)
    (hB : ((B : Matrix (Fin N) (Fin N) K)).det = 1) :
    ζ (Multiplicative.ofAdd (∑ i, w i)) = z ^ N := by
  apply Units.ext
  rw [← det_diagOf ζ w, Units.val_pow_eq_pow_val]
  have h1 := congrArg (fun g : GL (Fin N) K => ((g : Matrix (Fin N) (Fin N) K)).det) h
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.det_mul, Matrix.det_diagonal, hB, mul_one, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at h1
  exact h1

theorem unitBlockConjIff_holds :
    ∀ {K : Type} [Field K] [Finite K] (ζ : Multiplicative (ZMod 3) →* Kˣ) (N : ℕ),
      Nat.card K = 4 → Function.Injective ζ → 5 ≤ N →
      ∀ S : Finset (Fin N), UnitRaw.admissible S → ∀ (w : UnitRaw.W N)
        (hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))),
        (∃ y ∈ blockPSU (K := K) S,
            TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ = MulAut.conj y) ↔
          (UnitRaw.oneLine N).mkQ w ∈ UnitRaw.inside S := by
  intro K _ _ ζ N hK hζ hN S hS w hD
  have h : UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card (by rw [hK]; norm_num) le_rfl
  constructor
  · rintro ⟨y, hy, hyeq⟩
    simp only [blockPSU] at hy
    obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.mp hy
    let H : Subgroup (GL (Fin N) K) := unitarySU 2 1 K N
    let A : ↥(Subgroup.normalizer (H : Set (GL (Fin N) K))) := ⟨diagOf ζ w, hD⟩
    let Bn : ↥(Subgroup.normalizer (H : Set (GL (Fin N) K))) :=
      ⟨(B : GL (Fin N) K), Subgroup.le_normalizer B.2⟩
    have hBblock : TableBUE.IsBlockOn S ((B : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) :=
      TableBUE.mem_blockSU.mp hB
    have hdetB : ((B : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).det = 1 :=
      (mem_unitarySU_iff h).mp B.2 |>.1
    have hBn : TableB.projConj H Bn = MulAut.conj (LargeEvenProjMk H B) :=
      TableB.projConj_of_mem H (B : GL (Fin N) K) B.2
    have hprod : TableB.projConj H (A * Bn⁻¹) = 1 := by
      rw [map_mul, map_inv, hBn, ← hyeq]
      exact mul_inv_cancel _
    have hmem := TableBUE.mem_scalars_of_projConj_eq_one (n := 1) (d := N) (p := 3)
      h (by rw [hK]; norm_num) (by omega) (by rintro ⟨h1, h2⟩; omega)
      Nat.prime_three (by norm_num) hprod
    rw [largeEvenScalars_def] at hmem
    obtain ⟨z, hz⟩ := hmem
    have hDval : ((A * Bn⁻¹ : ↥(Subgroup.normalizer (H : Set (GL (Fin N) K)))) :
        GL (Fin N) K) = diagOf ζ w * (B : GL (Fin N) K)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
    have hDs : diagOf ζ w * (B : GL (Fin N) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin N) z := hDval.symm.trans hz.symm
    have hDB : diagOf ζ w = GeneralLinearGroup.scalar (Fin N) z * (B : GL (Fin N) K) := by
      rw [← hDs]
      group
    obtain ⟨c, hc⟩ := zeta_surjective ζ hK hζ z
    have hsumζ : ζ (Multiplicative.ofAdd (∑ i, w i)) = z ^ N :=
      ubk_det_diagOf hDB hdetB
    have hzpow : z ^ N = ζ (Multiplicative.ofAdd (N • Multiplicative.toAdd c)) := by
      rw [← hc, ← map_pow, ofAdd_nsmul]
      simp
    have hsum_eq : ∑ i, w i = N • Multiplicative.toAdd c :=
      Multiplicative.ofAdd.injective (hζ (hsumζ.trans hzpow))
    rw [UnitRaw.mem_inside_iff]
    refine ⟨fun i => w i - Multiplicative.toAdd c, ?_, ?_, ?_⟩
    · rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      have hdiff : (fun i => w i - Multiplicative.toAdd c) - w =
          fun _ => -Multiplicative.toAdd c := by
        funext i
        simp
      rw [hdiff]
      exact (UnitRaw.mem_oneLine _).mpr ⟨-Multiplicative.toAdd c, rfl⟩
    · intro i hi
      have hBi : ((B : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) i i = 1 := by
        simpa using hBblock i i (Or.inl hi)
      have hzi : ζ (Multiplicative.ofAdd (w i)) = z := ubk_diagOf_entry hDB hBi
      have hwi : w i = Multiplicative.toAdd c :=
        Multiplicative.ofAdd.injective (by simpa using hζ (hzi.trans hc.symm))
      show w i - Multiplicative.toAdd c = 0
      rw [hwi, sub_self]
    · rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        hsum_eq, sub_self]
  · intro hmk
    rw [UnitRaw.mem_inside_iff] at hmk
    obtain ⟨w', hw'mk, hsupp, hsum⟩ := hmk
    let H : Subgroup (GL (Fin N) K) := unitarySU 2 1 K N
    have hD'U : diagOf ζ w' ∈ H := diagOf_mem_unitarySU ζ h hsum
    have hD' : diagOf ζ w' ∈ Subgroup.normalizer (H : Set (GL (Fin N) K)) :=
      diagOf_mem_normalizer ζ h w'
    let y : ↥H := ⟨diagOf ζ w', diagOf_mem_unitarySU ζ h hsum⟩
    have hy : LargeEvenProjMk H y ∈ blockPSU (K := K) S := by
      simp only [blockPSU]
      exact Subgroup.mem_map.mpr ⟨y, diagOf_mem_blockSU h ζ hsupp hsum, rfl⟩
    refine ⟨LargeEvenProjMk H y, hy, ?_⟩
    have heq : TableB.projConj H ⟨diagOf ζ w, hD⟩ =
        TableB.projConj H ⟨diagOf ζ w', hD'⟩ := by
      have hsub : (⟨diagOf ζ w, hD⟩ : ↥(Subgroup.normalizer (H : Set (GL (Fin N) K)))) =
          ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ := Subtype.ext rfl
      rw [hsub]
      exact (projConj_diagOf_eq_iff ζ h hK hζ (by omega) w w').mpr hw'mk.symm
    rw [heq]
    have hsub2 : (⟨diagOf ζ w', hD'⟩ : ↥(Subgroup.normalizer (H : Set (GL (Fin N) K)))) =
        ⟨diagOf ζ w', Subgroup.le_normalizer hD'U⟩ := Subtype.ext rfl
    rw [hsub2]
    exact TableB.projConj_of_mem H (diagOf ζ w') hD'U

end

end CFSG.StandardType.GGQ2Frame.UnitPlacement

end
