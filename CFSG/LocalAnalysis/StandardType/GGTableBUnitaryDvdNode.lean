module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdTorality
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdLayer
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeElt
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndDvd

public section

namespace CFSG.StandardType

namespace TableBUD

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.UnitaryFlag TableBUE
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2

variable {K : Type} [Field K] {n d : ℕ}

section Diagonal

variable {S : Finset (Fin d)} {τ : Fin d → Kˣ}

theorem diagAt_of_commute (hτ : IsNodeOn τ S) {g : GL (Fin d) K}
    (hc : g * diagHom d τ = diagHom d τ * g) {i : Fin d} (hi : i ∉ S) :
    DiagAt i ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
  ⟨fun j hj => entry_eq_zero_of_commute hc (hτ.2 i hi j hj).symm,
    fun j hj => entry_eq_zero_of_commute hc (hτ.2 i hi j hj)⟩

theorem commutator_mem_blockSU_of_commute (hτ : IsNodeOn τ S) {g g' : ↥(unitarySU 2 n K d)}
    (hg : (g : GL (Fin d) K) * diagHom d τ = diagHom d τ * g)
    (hg' : (g' : GL (Fin d) K) * diagHom d τ = diagHom d τ * g') :
    g * g' * g⁻¹ * g'⁻¹ ∈ blockSU S := by
  have hginv : ((g⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * diagHom d τ =
      diagHom d τ * ((g⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) := by
    rw [Subgroup.coe_inv]
    exact (show Commute (g : GL (Fin d) K) (diagHom d τ) from hg).inv_left.eq
  have hg'inv : ((g'⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * diagHom d τ =
      diagHom d τ * ((g'⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) := by
    rw [Subgroup.coe_inv]
    exact (show Commute (g' : GL (Fin d) K) (diagHom d τ) from hg').inv_left.eq
  have key : ∀ i ∉ S, DiagAt i
      ((((g * g' * g⁻¹ * g'⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K)) :
        Matrix (Fin d) (Fin d) K) ∧
      ((((g * g' * g⁻¹ * g'⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K)) :
        Matrix (Fin d) (Fin d) K) i i = 1 := by
    intro i hi
    have d1 := diagAt_of_commute hτ hg hi
    have d2 := diagAt_of_commute hτ hg' hi
    have d3 := diagAt_of_commute hτ hginv hi
    have d4 := diagAt_of_commute hτ hg'inv hi
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] at d3 d4 ⊢
    refine ⟨((d1.mul d2).mul d3).mul d4, ?_⟩
    rw [(((d1.mul d2).mul d3)).mul_apply d4, ((d1.mul d2)).mul_apply d3, d1.mul_apply d2]
    have e1 : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
        ((((g : GL (Fin d) K))⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i = 1 := by
      rw [← d1.mul_apply d3, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    have e2 : ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
        ((((g' : GL (Fin d) K))⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i = 1 := by
      rw [← d2.mul_apply d4, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    linear_combination (((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
        ((((g' : GL (Fin d) K))⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i) * e1 + e2
  rintro i j (hi | hj)
  · obtain ⟨hd, h1⟩ := key i hi
    by_cases hij : j = i
    · subst hij
      rw [h1, Matrix.one_apply_eq]
    · rw [hd.1 j hij, Matrix.one_apply_ne (Ne.symm hij)]
  · obtain ⟨hd, h1⟩ := key j hj
    by_cases hij : i = j
    · subst hij
      rw [h1, Matrix.one_apply_eq]
    · rw [hd.2 i hij, Matrix.one_apply_ne hij]

theorem scalar_eq_one_of_conj_eq (hτ : ∀ i ∈ S, ∀ j ∈ S, τ i = τ j) (hS : Sᶜ.card < S.card)
    {s : GL (Fin d) K} {c : Kˣ}
    (h : diagHom d τ * s * (diagHom d τ)⁻¹ = GeneralLinearGroup.scalar (Fin d) c * s) :
    c = 1 := by
  by_contra hc
  have hmat : ((diagHom d τ * s * (diagHom d τ)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (fun i => (τ i : K)) * (s : Matrix (Fin d) (Fin d) K) *
        diagonal (fun k => ((τ k : Kˣ) : K)⁻¹) := by
    rw [Units.val_mul, Units.val_mul, coe_diagHom, ← map_inv, coe_diagHom]
    congr 2
    funext i
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val]
  have hzero : ∀ k ∈ S, ∀ l ∈ S, (s : Matrix (Fin d) (Fin d) K) k l = 0 := by
    intro k hk l hl
    have h1 : ((diagHom d τ * s * (diagHom d τ)⁻¹ : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) k l =
        ((GeneralLinearGroup.scalar (Fin d) c * s : GL (Fin d) K) :
          Matrix (Fin d) (Fin d) K) k l := by rw [h]
    rw [hmat, TypeA.diagonal_conj_apply, Units.val_mul, GeneralLinearGroup.coe_scalar,
      scalar_apply, diagonal_mul, hτ k hk l hl, mul_comm ((τ l : Kˣ) : K), mul_assoc,
      mul_inv_cancel₀ (Units.ne_zero _), mul_one] at h1
    have h3 : ((c : K) - 1) * (s : Matrix (Fin d) (Fin d) K) k l = 0 := by
      rw [sub_mul, ← h1, one_mul, sub_self]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (Units.ext (sub_eq_zero.mp h4)) hc
    · exact h4
  have hdet := TypeA.det_eq_zero_of_block_zero hS hzero
  exact (Matrix.isUnit_iff_isUnit_det _).mp s.isUnit |>.ne_zero hdet

end Diagonal

section Proj

variable {S : Finset (Fin d)} {τ : Fin d → Kˣ}

theorem projConj_mk_coe (D : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (s : ↥(unitarySU 2 n K d)) :
    ((TableB.projConj (unitarySU 2 n K d) D (LargeEvenProjMk _ s) :
      LargeEvenProj (unitarySU 2 n K d))) =
      LargeEvenProjMk _ ((unitarySU 2 n K d).normalizerMonoidHom D s) :=
  rfl

theorem exists_scalar_of_mk_eq {x y : ↥(unitarySU 2 n K d)}
    (hxy : LargeEvenProjMk (unitarySU 2 n K d) x = LargeEvenProjMk _ y) :
    ∃ c : Kˣ, ((x⁻¹ * y : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
      GeneralLinearGroup.scalar (Fin d) c := by
  have h1 := QuotientGroup.eq.mp hxy
  rw [Subgroup.mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, hc.symm⟩

theorem projConj_mk_eq_iff (hτ : ∀ i ∈ S, ∀ j ∈ S, τ i = τ j) (hS : Sᶜ.card < S.card)
    (hD : diagHom d τ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (s : ↥(unitarySU 2 n K d)) :
    TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hD⟩ (LargeEvenProjMk _ s) =
        LargeEvenProjMk _ s ↔
      (s : GL (Fin d) K) * diagHom d τ = diagHom d τ * s := by
  rw [projConj_mk_coe]
  constructor
  · intro hfix
    obtain ⟨c, hc⟩ := exists_scalar_of_mk_eq hfix
    have hc' : (s : GL (Fin d) K) = (diagHom d τ * s * (diagHom d τ)⁻¹) *
        GeneralLinearGroup.scalar (Fin d) c := by
      rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv]
      show (s : GL (Fin d) K) = (diagHom d τ * s * (diagHom d τ)⁻¹) *
        ((diagHom d τ * s * (diagHom d τ)⁻¹)⁻¹ * s)
      group
    have h1 : diagHom d τ * s * (diagHom d τ)⁻¹ =
        GeneralLinearGroup.scalar (Fin d) c⁻¹ * (s : GL (Fin d) K) := by
      calc diagHom d τ * s * (diagHom d τ)⁻¹ = (diagHom d τ * s * (diagHom d τ)⁻¹) *
            GeneralLinearGroup.scalar (Fin d) c * (GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by
            group
        _ = (s : GL (Fin d) K) * (GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by rw [← hc']
        _ = GeneralLinearGroup.scalar (Fin d) c⁻¹ * (s : GL (Fin d) K) := by
            rw [← map_inv, TypeA.PGLTor.scalar_mul_comm]
    have hc1 := scalar_eq_one_of_conj_eq hτ hS h1
    rw [hc1, map_one, one_mul] at h1
    calc (s : GL (Fin d) K) * diagHom d τ =
        (diagHom d τ * s * (diagHom d τ)⁻¹) * diagHom d τ := by rw [h1]
      _ = diagHom d τ * s := by group
  · intro hc
    congr 1
    apply Subtype.ext
    show diagHom d τ * (s : GL (Fin d) K) * (diagHom d τ)⁻¹ = s
    rw [← hc, mul_inv_cancel_right]

@[expose] def cenSU (D : GL (Fin d) K) : Subgroup ↥(unitarySU 2 n K d) :=
  (Subgroup.centralizer ({D} : Set (GL (Fin d) K))).comap (unitarySU 2 n K d).subtype

theorem mem_cenSU {D : GL (Fin d) K} {s : ↥(unitarySU 2 n K d)} :
    s ∈ cenSU D ↔ (s : GL (Fin d) K) * D = D * s := by
  rw [cenSU, Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff]

theorem ggFix_projConj_eq (hτ : ∀ i ∈ S, ∀ j ∈ S, τ i = τ j) (hS : Sᶜ.card < S.card)
    (hD : diagHom d τ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) :
    ggFix (TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hD⟩) =
      (cenSU (n := n) (diagHom d τ)).map (LargeEvenProjMk _) := by
  ext r
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective _ r
  rw [mem_ggFix]
  change _ = LargeEvenProjMk _ s ↔ _
  rw [projConj_mk_eq_iff hτ hS hD]
  constructor
  · intro hc
    exact ⟨s, mem_cenSU.mpr hc, rfl⟩
  · rintro ⟨s', hs', he⟩
    have hs'c := mem_cenSU.mp hs'
    rw [← projConj_mk_eq_iff hτ hS hD] at hs'c ⊢
    rw [← he]
    exact hs'c

end Proj

section Layer

variable (h : UnitaryFieldData 2 n K) {S : Finset (Fin d)} {τ : Fin d → Kˣ}

omit h in
theorem blockSU_le_cenSU (hτ : ∀ i ∈ S, ∀ j ∈ S, τ i = τ j) :
    blockSU (n := n) S ≤ cenSU (diagHom d τ) := fun _ hx =>
  mem_cenSU.mpr (diagHom_mul_comm_of_isBlockOn hτ hx).symm

omit h in
theorem ker_comp_blockSU_le_center :
    ((LargeEvenProjMk (unitarySU 2 n K d)).comp (blockSU (n := n) (K := K) S).subtype).ker ≤
      Subgroup.center (blockSU (n := n) (K := K) S) := by
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
  have h1 : (((x : ↥(unitarySU 2 n K d)) : GL (Fin d) K)) ∈ LargeEvenScalars (Fin d) K :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hx)
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (TableB.scalars_le_center h1) _

include h in
theorem layer_ggFix_projConj [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hτ : IsNodeOn τ S)
    (hS : Sᶜ.card < S.card) (hS3 : 3 ≤ S.card) (hSq : (S.card, 2 ^ n) ≠ (3, 2))
    (hD : diagHom d τ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) :
    LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hD⟩)) =
        (blockSU (n := n) S).map (LargeEvenProjMk _) ∧
      IsComponentOf ((blockSU (n := n) S).map (LargeEvenProjMk _))
        (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hD⟩)) := by
  rw [ggFix_projConj_eq hτ.1 hS hD]
  refine TableBSymp.largeEvenLayer_eq_of_commutator_mem
    (Subgroup.map_mono (blockSU_le_cenSU hτ.1)) ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
    refine ⟨g * g' * g⁻¹ * g'⁻¹,
      commutator_mem_blockSU_of_commute hτ (mem_cenSU.mp hg) (mem_cenSU.mp hg'), ?_⟩
    simp only [map_mul, map_inv]
  · have hq := isQuasisimple_blockSU S h hK hS3 hSq
    have := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_range hq
      ((LargeEvenProjMk _).comp (blockSU S).subtype) ker_comp_blockSU_le_center
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at this

omit h in
theorem diagHom_eq_scalar_iff {σ : Fin d → Kˣ} {c : Kˣ} :
    diagHom d σ = GeneralLinearGroup.scalar (Fin d) c ↔ ∀ k, σ k = c := by
  have he : GeneralLinearGroup.scalar (Fin d) c = diagHom d (fun _ => c) := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, scalar_apply, coe_diagHom]
  rw [he]
  constructor
  · intro h1 k
    exact congrFun (diagHom_injective d h1) k
  · intro h1
    congr 1
    funext k
    exact h1 k

include h in
theorem fix_blockSU_iff (hT : ∃ k, k ∉ S) {τ' : Fin d → Kˣ}
    (hD' : diagHom d τ' ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) :
    (∀ j ∈ (blockSU (n := n) S).map (LargeEvenProjMk _),
        TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ', hD'⟩ j = j) ↔
      ∀ i ∈ S, ∀ j ∈ S, τ' i = τ' j := by
  constructor
  · intro hfix i hi j hj
    set w : ↥(unitarySU 2 n K d) := ⟨permGL (Equiv.swap i j), permGL_swap_mem h i j⟩ with hw
    have hwS : w ∈ blockSU S := isBlockOn_permGL_swap hi hj
    have h1 := hfix _ ⟨w, hwS, rfl⟩
    rw [projConj_mk_coe] at h1
    obtain ⟨c, hc⟩ := exists_scalar_of_mk_eq h1
    have hW : (permGL (Equiv.swap i j) : GL (Fin d) K)⁻¹ = permGL (Equiv.swap i j) := by
      rw [← map_inv, Equiv.swap_inv]
    have hconj : (permGL (Equiv.swap i j) : GL (Fin d) K)⁻¹ * (diagHom d τ')⁻¹ *
        permGL (Equiv.swap i j) = diagHom d (τ'⁻¹ ∘ Equiv.swap i j) := by
      have := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap i j) τ'⁻¹
      rw [Equiv.symm_swap, map_inv, ← hW] at this
      rw [hW] at this ⊢
      rw [← this, hW]
    have hgl : (((((unitarySU 2 n K d).normalizerMonoidHom ⟨diagHom d τ', hD'⟩) w)⁻¹ * w :
        ↥(unitarySU 2 n K d)) : GL (Fin d) K) = diagHom d (τ' * (τ'⁻¹ ∘ Equiv.swap i j)) := by
      rw [map_mul, ← hconj]
      show (diagHom d τ' * permGL (Equiv.swap i j) * (diagHom d τ')⁻¹)⁻¹ *
        permGL (Equiv.swap i j) = _
      group
    rw [hgl, diagHom_eq_scalar_iff] at hc
    obtain ⟨k, hk⟩ := hT
    have hki : k ≠ i := fun h' => hk (h' ▸ hi)
    have hkj : k ≠ j := fun h' => hk (h' ▸ hj)
    have hck : c = 1 := by
      rw [← hc k]
      simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
    have hci := hc i
    rw [hck] at hci
    simp only [Pi.mul_apply, Function.comp_apply, Equiv.swap_apply_left, Pi.inv_apply] at hci
    exact (mul_inv_eq_one.mp hci)
  · rintro hσ _ ⟨x, hx, rfl⟩
    rw [projConj_mk_coe]
    congr 1
    apply Subtype.ext
    show diagHom d τ' * (x : GL (Fin d) K) * (diagHom d τ')⁻¹ = x
    rw [diagHom_mul_comm_of_isBlockOn hσ hx, mul_inv_cancel_right]

include h in
theorem exists_eq_mul_of_projConj_eq [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {τ τ' : Fin d → Kˣ}
    (hD : diagHom d τ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hD' : diagHom d τ' ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (he : TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hD⟩ =
      TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ', hD'⟩) :
    ∃ c : Kˣ, ∀ k, τ' k = c * τ k := by
  set M : Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    (⟨diagHom d τ, hD⟩)⁻¹ * ⟨diagHom d τ', hD'⟩ with hM
  have hM1 : TableB.projConj (unitarySU 2 n K d) M = 1 := by
    rw [hM, map_mul, map_inv, he, inv_mul_cancel]
  obtain ⟨c, hc⟩ := mem_scalars_of_projConj_eq_one h hK hd hdq hp hpq hM1
  have h1 : diagHom d (τ⁻¹ * τ') = GeneralLinearGroup.scalar (Fin d) c := by
    rw [hc, map_mul, map_inv]
    rfl
  rw [diagHom_eq_scalar_iff] at h1
  refine ⟨c, fun k => ?_⟩
  rw [← h1 k, Pi.mul_apply, Pi.inv_apply, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

end Layer

section Node

variable (h : UnitaryFieldData 2 n K)

theorem ratio_eq_of_eq_mul {τ τ' : Fin d → Kˣ} {c : Kˣ} (hc : ∀ k, τ' k = c * τ k) (k k₀ : Fin d) :
    τ k * (τ k₀)⁻¹ = τ' k * (τ' k₀)⁻¹ := by
  rw [hc k, hc k₀]
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

include h in
theorem endNode_of_diag [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d) (hq : 2 < 2 ^ n ∨ 6 ≤ d)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} (hAb : IsElemAbelian p Ab)
    (hdiag : ∀ a ∈ Ab, ∃ (τ : Fin d → Kˣ) (hτ : diagHom d τ ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
        a = TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hτ⟩)
    (hcard : p ^ (d - 2) ≤ Nat.card Ab) :
    ∃ a ∈ Ab, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
      ∀ a' ∈ Ab, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a) := by
  classical
  have hp2 := ne_two_of_dvd h hpq
  have hpK := dvd_card_sub_one' h hpq
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  set N := Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) with hN
  set ρ := TableB.projConj (unitarySU 2 n K d) with hρ
  choose τf hτfN hτf using fun a : Ab => hdiag a a.2
  set Dn : Ab → N := fun a => ⟨diagHom d (τf a), hτfN a⟩ with hDn
  have hρDn : ∀ a : Ab, ρ (Dn a) = a := fun a => (hτf a).symm
  set k₀ : Fin d := ⟨3, by omega⟩ with hk₀
  have hrat : ∀ {τ τ' : Fin d → Kˣ} (hD : diagHom d τ ∈ N) (hD' : diagHom d τ' ∈ N),
      ρ ⟨diagHom d τ, hD⟩ = ρ ⟨diagHom d τ', hD'⟩ →
      ∀ k, τ k * (τ k₀)⁻¹ = τ' k * (τ' k₀)⁻¹ := by
    intro τ τ' hD hD' he k
    obtain ⟨c, hc⟩ := exists_eq_mul_of_projConj_eq h hK (by omega) hdq hp hpq hD hD' he
    exact ratio_eq_of_eq_mul hc k k₀
  have hone : diagHom d (1 : Fin d → Kˣ) ∈ N := by rw [map_one]; exact N.one_mem
  have hρone : ρ ⟨diagHom d 1, hone⟩ = 1 := by
    have : (⟨diagHom d 1, hone⟩ : N) = 1 := Subtype.ext (map_one _)
    rw [this, map_one]
  have hνone : ∀ k, τf 1 k * (τf 1 k₀)⁻¹ = 1 := by
    intro k
    have he : ρ ⟨diagHom d (τf 1), hτfN 1⟩ = ρ ⟨diagHom d 1, hone⟩ := by
      have h1 := hρDn 1
      rw [hρone]
      exact h1
    have h1 := hrat (hτfN 1) hone he k
    rw [h1]
    simp
  have hνmul : ∀ a b : Ab, ∀ k, τf (a * b) k * (τf (a * b) k₀)⁻¹ =
      τf a k * (τf a k₀)⁻¹ * (τf b k * (τf b k₀)⁻¹) := by
    intro a b k
    have hab : diagHom d (τf a * τf b) ∈ N := by
      rw [map_mul]
      exact N.mul_mem (hτfN a) (hτfN b)
    have hprod : ρ ⟨diagHom d (τf a * τf b), hab⟩ = ((a * b : Ab) : MulAut _) := by
      have : (⟨diagHom d (τf a * τf b), hab⟩ : N) = Dn a * Dn b :=
        Subtype.ext (map_mul _ _ _)
      rw [this, map_mul, hρDn, hρDn, Subgroup.coe_mul]
    have he : ρ ⟨diagHom d (τf (a * b)), hτfN (a * b)⟩ = ρ ⟨diagHom d (τf a * τf b), hab⟩ := by
      have h1 := hρDn (a * b)
      rw [hprod]
      exact h1
    rw [hrat (hτfN (a * b)) hab he k]
    apply Units.ext
    simp only [Pi.mul_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  let ν : Ab →* (Fin d → Kˣ) :=
    { toFun := fun a k => τf a k * (τf a k₀)⁻¹
      map_one' := funext hνone
      map_mul' := fun a b => funext (hνmul a b) }
  have hν : ∀ a k, ν a k = τf a k * (τf a k₀)⁻¹ := fun _ _ => rfl
  have hνinj : Function.Injective ν := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hc : ∀ k, τf a k = τf a k₀ := fun k => by
      have h1 := congrFun ha k
      rw [hν, Pi.one_apply, mul_inv_eq_one] at h1
      exact h1
    have hs : diagHom d (τf a) = GeneralLinearGroup.scalar (Fin d) (τf a k₀) :=
      diagHom_eq_scalar_iff.mpr hc
    have hz : diagHom d (τf a) ∈ LargeEvenScalars (Fin d) K := ⟨τf a k₀, hs.symm⟩
    apply Subtype.ext
    rw [← hρDn a, Subgroup.coe_one]
    exact TableB.projConj_of_scalar (unitarySU 2 n K d) hz
  set Y := ν.range with hY
  have hYcard : Nat.card Y = Nat.card Ab := Nat.card_range_of_injective hνinj
  have hY0 : ∀ y ∈ Y, y ⟨3, by omega⟩ = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [hν, mul_inv_cancel]
  have hYp : ∀ y ∈ Y, ∀ k, y k ∈ rootsOfUnity p K := by
    rintro _ ⟨a, rfl⟩ k
    rw [mem_rootsOfUnity]
    have hpow : diagHom d (τf a ^ p) ∈ N := by rw [map_pow]; exact N.pow_mem (hτfN a) p
    have hap : ρ ⟨diagHom d (τf a ^ p), hpow⟩ = 1 := by
      have : (⟨diagHom d (τf a ^ p), hpow⟩ : N) = Dn a ^ p := Subtype.ext (map_pow _ _ _)
      rw [this, map_pow, hρDn]
      exact hAb.2 _ a.2
    have h1 := hrat hpow hone (hap.trans hρone.symm) k
    rw [Pi.pow_apply, Pi.pow_apply, Pi.one_apply, Pi.one_apply, inv_one, mul_one, ← inv_pow,
      ← mul_pow] at h1
    rw [hν]
    exact h1
  obtain ⟨y, ⟨a₁, rfl⟩, hy1, T, hTne, hT2, hyT, hyc, hyz⟩ :=
    TypeA.exists_node hp hp2 hpK hd hY0 hYp (hYcard ▸ hcard)
  set τ := τf a₁ with hτ
  set S : Finset (Fin d) := Tᶜ with hSdef
  have hnode : IsNodeOn τ S := by
    refine ⟨fun i hi j hj => ?_, fun i hi j hj he => ?_⟩
    · have h1 := hyc i j (Finset.mem_compl.mp hi) (Finset.mem_compl.mp hj)
      rw [hν, hν] at h1
      exact mul_right_cancel h1
    · have hiT : i ∈ T := by simpa [hSdef] using hi
      apply hyT i hiT j hj
      rw [hν, hν]
      show τ j * (τ k₀)⁻¹ = τ i * (τ k₀)⁻¹
      rw [he]
  have hScard : S.card = d - T.card := by
    rw [hSdef, Finset.card_compl, Fintype.card_fin]
  have hT2' : T.card ≤ 2 := hT2
  have hSc : Sᶜ.card < S.card := by
    rw [hSdef, compl_compl, hScard]
    omega
  have hS3 : 3 ≤ S.card := by
    rw [hScard]
    omega
  have hSq : (S.card, 2 ^ n) ≠ (3, 2) := by
    intro he
    have h1 : S.card = 3 := congrArg Prod.fst he
    have h2 : 2 ^ n = 2 := congrArg Prod.snd he
    rcases hq with hq | hq <;> omega
  obtain ⟨hlayer, hcomp⟩ :=
    layer_ggFix_projConj h hK hnode hSc hS3 hSq (hτfN a₁)
  have ha₁ : ((a₁ : Ab) : MulAut _) = ρ ⟨diagHom d τ, hτfN a₁⟩ := hτf a₁
  have hT' : ∃ k, k ∉ S := by
    obtain ⟨k, hk⟩ := hTne
    exact ⟨k, by simpa [hSdef] using hk⟩
  refine ⟨a₁, a₁.2, fun h1 => hy1 ?_, ?_, fun a' ha' => ?_⟩
  · have : a₁ = 1 := Subtype.ext h1
    rw [this, map_one]
  · rw [ha₁, hlayer]
    exact hcomp
  · constructor
    · intro hfix
      set b : Ab := ⟨a', ha'⟩ with hb
      have hb' : a' = ρ ⟨diagHom d (τf b), hτfN b⟩ := hτf b
      rw [ha₁, hlayer, hb'] at hfix
      have hconst := (fix_blockSU_iff h hT' (hτfN b)).mp hfix
      have hνc : ∀ k l, k ∉ T → l ∉ T → ν b k = ν b l := by
        intro k l hk hl
        rw [hν, hν, hconst k (Finset.mem_compl.mpr hk) l (Finset.mem_compl.mpr hl)]
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hyz (ν b) ⟨b, rfl⟩ hνc)
      have h3 : a₁ ^ m = b := hνinj (by rw [map_zpow, hm])
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨m, by rw [← Subgroup.coe_zpow, h3]⟩
    · intro hmem j hj
      rw [ha₁, hlayer] at hj
      have hj' : ((a₁ : Ab) : MulAut _) j = j := by
        rw [ha₁]
        exact mem_ggFix.mp (hcomp.1 hj)
      exact apply_eq_of_mem_zpowers hmem hj'

end Node

end TableBUD

end CFSG.StandardType
