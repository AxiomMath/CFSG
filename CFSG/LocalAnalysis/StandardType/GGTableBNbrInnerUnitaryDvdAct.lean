module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdCent
public import CFSG.LocalAnalysis.StandardType.GGTDCentFour

public section

namespace CFSG.StandardType.LineU

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType.TypeA

variable {K : Type} [Field K] {n d p : ℕ}

theorem exists_diagSU (hK : UnitaryFieldData 2 n K) {u : Fin d → K}
    (hu : ∀ i, u i ^ (2 ^ n + 1) = 1) (hprod : ∏ i, u i = 1) :
    ∃ D : ↥(unitarySU 2 n K d),
      ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u := by
  have hu0 : ∀ i, u i ≠ 0 := fun i h0 => by
    have h1 := hu i
    rw [h0, zero_pow (Nat.succ_ne_zero (2 ^ n))] at h1
    exact zero_ne_one h1
  let uu : Fin d → Kˣ := fun i => Units.mk0 (u i) (hu0 i)
  have hmem : CFSG.SectionRank.OddCover.diagHom d uu ∈ unitarySU 2 n K d := by
    rw [mem_unitarySU_iff hK]
    refine ⟨?_, ?_⟩
    · rw [CFSG.SectionRank.OddCover.det_diagHom]
      exact hprod
    · exact CFSG.RankThree.Classical2.diagHom_unitary hK (fun i => hu i)
  exact ⟨⟨CFSG.SectionRank.OddCover.diagHom d uu, hmem⟩,
    CFSG.SectionRank.OddCover.coe_diagHom uu⟩

theorem pow_eq_one_of_diagSU {D : ↥(unitarySU 2 n K d)} {u : Fin d → K}
    (hD : ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u) (hu : ∀ i, u i ^ p = 1) :
    D ^ p = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hD, diagonal_pow, Units.val_one]
  have e : u ^ p = fun _ => (1 : K) := funext hu
  rw [e, diagonal_one]

theorem ggPairVec_norm_one {ζ : K} (hζ : ζ ^ (2 ^ n + 1) = 1) (k l : Fin d) :
    ∀ m, ggPairVec k l ζ m ^ (2 ^ n + 1) = 1 := by
  intro m
  rw [ggPairVec_apply, mul_pow]
  split_ifs <;> simp [hζ, inv_pow]

section Acts

variable {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}

theorem ActsDiagU.mul {a b : MulAut L'} {t u : Fin d → K} (ha : ActsDiagU φ a t)
    (hb : ActsDiagU φ b u) : ActsDiagU φ (a * b) (fun k => t k * u k) := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  obtain ⟨E, hE, hEt, hbct⟩ := hb
  refine ⟨D * E, Subgroup.mul_mem _ hD hE, ?_, fun s => ?_⟩
  · rw [Units.val_mul, hDt, hEt, diagonal_mul_diagonal]
  · rw [MulAut.mul_apply, hbct s, hact (conjN E hE s)]
    congr 1
    apply Subtype.ext
    rw [coe_conjN, coe_conjN, coe_conjN]
    group

theorem ActsDiagU.inv {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t) :
    ActsDiagU φ a⁻¹ (fun k => (t k)⁻¹) := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  have hDinv : D⁻¹ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    Subgroup.inv_mem _ hD
  refine ⟨D⁻¹, hDinv, coe_inv_diag hDt, fun s => ?_⟩
  have h := hact (conjN D⁻¹ hDinv s)
  have e : conjN D hD (conjN D⁻¹ hDinv s) = s := by
    apply Subtype.ext
    rw [coe_conjN, coe_conjN]
    group
  rw [e] at h
  rw [← h, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem ActsDiagU.unique (hφs : Function.Surjective φ) {a b : MulAut L'} {t : Fin d → K}
    (ha : ActsDiagU φ a t) (hb : ActsDiagU φ b t) : a = b := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  obtain ⟨E, hE, hEt, hbct⟩ := hb
  have hDE : D = E := Units.ext (hDt.trans hEt.symm)
  subst hDE
  ext l
  obtain ⟨s, rfl⟩ := hφs l
  rw [hact, hbct]

theorem actsDiagU_conj {D : ↥(unitarySU 2 n K d)} {t : Fin d → K}
    (hD : ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal t) :
    ActsDiagU φ (MulAut.conj (φ D)) t := by
  refine ⟨(D : GL (Fin d) K), Subgroup.le_normalizer D.2, hD, fun s => ?_⟩
  rw [MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1

theorem ActsDiagU.mul_conj_comm {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t)
    {s : ↥(unitarySU 2 n K d)}
    (hs : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag) :
    a * MulAut.conj (φ s) = MulAut.conj (φ s) * a := by
  rw [CFSG.StandardType.TypeANbrDvd.mul_conj_eq_conj_apply_mul,
    ha.fix_of_diagonal s ((Matrix.isDiag_iff_diagonal_diag _).mp hs).symm]

theorem ActsDiagU.eq_one_of_conj_perm (hK : UnitaryFieldData 2 n K) (hd : 3 ≤ d)
    (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {b : MulAut L'} {t : Fin d → K} (hb : ActsDiagU φ b t)
    (hfix : ∀ σ : Equiv.Perm (Fin d),
      MulAut.conj (φ (permSU hK σ)) * b * (MulAut.conj (φ (permSU hK σ)))⁻¹ = b) : b = 1 := by
  refine ActsDiagU.eq_one_of_const hφs hb ⟨0, by omega⟩ fun i j => ?_
  by_cases hij : i = j
  · rw [hij]
  obtain ⟨k, hki, hkj⟩ := exists_not_mem_two hd i j
  have h1 := ActsDiagU.conj_perm hK hb (Equiv.swap i j)
  rw [hfix (Equiv.swap i j)] at h1
  have h2 := ActsDiagU.ratio_eq hK hd hφker hb h1 k i
  rw [Equiv.swap_inv i j, Equiv.swap_apply_of_ne_of_ne hki hkj,
    Equiv.swap_apply_left] at h2
  exact inv_inj.mp (mul_left_cancel₀ (hb.ne_zero k) h2)

end Acts

section Cover

variable {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}

theorem mem_scalars_subgroupOf_iff (hK : UnitaryFieldData 2 n K) (hd : 0 < d)
    {g : ↥(unitarySU 2 n K d)} :
    g ∈ (CFSG.Open.StatedScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) ↔
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c) := by
  rw [Subgroup.mem_subgroupOf]
  change (g : GL (Fin d) K) ∈ (Matrix.GeneralLinearGroup.scalar (Fin d)).range ↔
    ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨(c : K), ?_⟩
    rw [← hc]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    · simp [Matrix.diagonal_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        hij]
  · rintro ⟨c, hc⟩
    have hdet : (∏ _ : Fin d, c) = 1 := by
      have h1 : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1 :=
        ((mem_unitarySU_iff hK).mp g.2).1
      rw [hc, Matrix.det_diagonal] at h1
      exact h1
    have hc0 : c ≠ 0 := by
      intro h0
      rw [Finset.prod_eq_zero (Finset.mem_univ (⟨0, hd⟩ : Fin d)) h0] at hdet
      exact zero_ne_one hdet
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    exact hc.symm

theorem exists_scalar_of_map_conj_eq_U (hK : UnitaryFieldData 2 n K) (hd : 4 ≤ d)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {g : ↥(unitarySU 2 n K d)} (h : ∀ y, φ (g * y * g⁻¹) = φ y) :
    ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c) := by
  haveI : Finite K := hK.finite
  set Z : Subgroup (↥(unitarySU 2 n K d)) :=
    (CFSG.Open.StatedScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) with hZ
  haveI hZn : Z.Normal := by rw [hZ]; infer_instance
  have hmemZ : ∀ z : ↥(unitarySU 2 n K d),
      (∃ c : K, ((z : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) →
      z ∈ Z := by
    intro z hz
    rw [hZ]
    exact (mem_scalars_subgroupOf_iff hK (by omega)).mpr hz
  have hcomm : ∀ y : ↥(unitarySU 2 n K d),
      QuotientGroup.mk' Z (g * y) = QuotientGroup.mk' Z (y * g) := by
    intro y
    have hmem : (g * y) * (y * g)⁻¹ ∈ Z := by
      apply hmemZ
      have hker : φ ((g * y) * (y * g)⁻¹) = 1 := by
        have he : (g * y) * (y * g)⁻¹ = (g * y * g⁻¹) * y⁻¹ := by group
        rw [he, map_mul, map_inv, h y, mul_inv_cancel]
      exact hφker _ hker
    have h1 : QuotientGroup.mk' Z ((g * y) * (y * g)⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    rw [map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  have hq : QuotientGroup.mk' Z g ∈
      Subgroup.center (CFSG.Open.StatedProj (unitarySU 2 n K d)) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N := Z) x
    rw [← map_mul, ← map_mul]
    exact (hcomm y).symm
  have hqg : QuotientGroup.mk' Z g = 1 := by
    have hbot : Subgroup.center (CFSG.Open.StatedProj (unitarySU 2 n K d)) = ⊥ :=
      center_statedProj_statedSU_eq_bot hK.card_eq_sq hd
    rw [hbot] at hq
    exact Subgroup.mem_bot.mp hq
  have hgZ : g ∈ Z := (QuotientGroup.eq_one_iff g).mp hqg
  rw [hZ] at hgZ
  exact (mem_scalars_subgroupOf_iff hK (by omega)).mp hgZ

theorem isDiag_of_conj_comm_U (hK : UnitaryFieldData 2 n K) (hd : 4 ≤ d)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {ζ : K} (hζ : ζ ^ (2 ^ n + 1) = 1) (hζ2 : ζ ≠ ζ⁻¹) {s : ↥(unitarySU 2 n K d)}
    (h : ∀ k l : Fin d, k ≠ l → ∀ D : ↥(unitarySU 2 n K d),
      ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec k l ζ) →
      MulAut.conj (φ s) * MulAut.conj (φ D) = MulAut.conj (φ D) * MulAut.conj (φ s)) :
    ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag := by
  have hζ0 : ζ ≠ 0 := fun h0 => by
    rw [h0, zero_pow (Nat.succ_ne_zero (2 ^ n))] at hζ
    exact zero_ne_one hζ
  haveI : CharP K 2 := hK.charP
  refine CFSG.StandardType.TypeANbrDvd.isDiag_of_mul_diagonal_pairVec_of_four_le ?_ hd hζ2 ?_
  · rw [((mem_unitarySU_iff hK).mp s.2).1]
    exact one_ne_zero
  · intro k l hkl
    obtain ⟨D, hDm⟩ := exists_diagSU hK (u := ggPairVec k l ζ)
      (ggPairVec_norm_one hζ k l) (prod_ggPairVec ζ hζ0)
    have h1 : MulAut.conj (φ s * φ D) = MulAut.conj (φ D * φ s) := by
      rw [map_mul, map_mul, h k l hkl D hDm]
    set g : ↥(unitarySU 2 n K d) := (D * s)⁻¹ * (s * D) with hg
    have hgφ : φ g = (φ D * φ s)⁻¹ * (φ s * φ D) := by
      rw [hg, map_mul, map_inv, map_mul, map_mul]
    have hgy : ∀ y, φ (g * y * g⁻¹) = φ y := by
      intro y
      have h3 : (φ s * φ D) * φ y * (φ s * φ D)⁻¹ =
          (φ D * φ s) * φ y * (φ D * φ s)⁻¹ := by
        have := congrArg (fun f : MulAut L' => f (φ y)) h1
        simpa only [MulAut.conj_apply] using this
      rw [map_mul, map_mul, map_inv, hgφ]
      calc (φ D * φ s)⁻¹ * (φ s * φ D) * φ y * ((φ D * φ s)⁻¹ * (φ s * φ D))⁻¹
          = (φ D * φ s)⁻¹ * ((φ s * φ D) * φ y * (φ s * φ D)⁻¹) * (φ D * φ s) := by
            group
        _ = (φ D * φ s)⁻¹ * ((φ D * φ s) * φ y * (φ D * φ s)⁻¹) * (φ D * φ s) := by
            rw [h3]
        _ = φ y := by group
    obtain ⟨c, hc⟩ := exists_scalar_of_map_conj_eq_U hK (by omega) hφker hgy
    refine ⟨c, ?_⟩
    have h4 : s * D = D * s * g := by rw [hg]; group
    have h5 : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
            ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      have h4' := congrArg (fun x : ↥(unitarySU 2 n K d) =>
        ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) h4
      simpa only [Subgroup.coe_mul, Units.val_mul] using h4'
    rw [hDm] at h5
    rw [h5, hc, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

theorem conj_mem_of_selfCent_U {A : Subgroup (MulAut L')}
    (hsc : GGTorusSelfCent p A) (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t)
    {D : ↥(unitarySU 2 n K d)} {u : Fin d → K}
    (hD : ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u) (hu : ∀ i, u i ^ p = 1) :
    MulAut.conj (φ D) ∈ A := by
  refine hsc (φ D) (fun a ha => ?_) ?_
  · obtain ⟨t, hat⟩ := hdiag a ha
    exact hat.fix_of_diagonal D hD
  · rw [← map_pow, pow_eq_one_of_diagSU hD hu, map_one]

end Cover

end CFSG.StandardType.LineU

end
