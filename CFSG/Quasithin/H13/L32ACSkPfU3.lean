module

public import CFSG.Quasithin.H13.L32ACSkPfB
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismHyperbolic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSylow
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOnePoint
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H13.L32A.C.SkPf

open CFSG.QuasithinUnique CFSG.Quasithin

section Count

theorem mem_of_pow_three_mem {G : Type*} [Group G] {H : Subgroup G} {x : G} (h3 : x ^ 3 ∈ H)
    (h2 : ∃ k : ℕ, x ^ 2 ^ k = 1) : x ∈ H := by
  obtain ⟨k, hk⟩ := h2
  have hc : Nat.Coprime 3 (orderOf x) :=
    (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one hk)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hc
  rw [← hm]
  exact pow_mem h3 m

variable {K : Type} [Field K] [Finite K]

theorem card_comap_pow_three_le (F : Subgroup Kˣ) :
    Nat.card (F.comap (powMonoidHom 3 : Kˣ →* Kˣ)) ≤ 3 * Nat.card F := by
  set E := F.comap (powMonoidHom 3 : Kˣ →* Kˣ)
  let κ : E →* F := ((powMonoidHom 3 : Kˣ →* Kˣ).comp E.subtype).codRestrict F fun a => a.2
  have h1 := κ.ker.card_mul_index
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card κ.range ≤ Nat.card F := Subgroup.card_le_card_group _
  have h3 : Nat.card κ.ker ≤ 3 := by
    have hmem : ∀ a : κ.ker, ((a : E) : Kˣ) ∈ rootsOfUnity 3 K := fun a => by
      rw [mem_rootsOfUnity]
      have h0 : ((κ (a : E) : F) : Kˣ) = 1 := by
        rw [MonoidHom.mem_ker.mp a.2, OneMemClass.coe_one]
      exact h0
    refine le_trans (Nat.card_le_card_of_injective (fun a : κ.ker => (⟨_, hmem a⟩ :
      rootsOfUnity 3 K)) fun a b hab => ?_) (card_rootsOfUnity K 3)
    exact Subtype.ext (Subtype.ext (congrArg (fun x : rootsOfUnity 3 K => (x : Kˣ)) hab))
  calc Nat.card E = Nat.card κ.ker * Nat.card κ.range := h1.symm
    _ ≤ 3 * Nat.card F := Nat.mul_le_mul h3 h2

theorem card_le_sixtyFour {σ : K ≃+* K} (hσ : σ ≠ 1)
    (h : Nat.card Kˣ ≤ 9 * Nat.card (unitsFix σ)) : Nat.card K ≤ 64 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set E := Finset.univ.filter (fun x : K => σ x = x) with hE
  have hsq : E.card ^ 2 ≤ Fintype.card K := card_fixed_sq_le σ hσ
  have e1 : (unitsFix σ) ≃ {x : K // σ x = x ∧ x ≠ 0} :=
    { toFun := fun t => ⟨(t : Kˣ), t.2, (t : Kˣ).ne_zero⟩
      invFun := fun x => ⟨Units.mk0 x.1 x.2.2, x.2.1⟩
      left_inv := fun t => Subtype.ext (Units.ext rfl)
      right_inv := fun x => rfl }
  have hc1 : Nat.card (unitsFix σ) = (E.erase 0).card := by
    rw [Nat.card_congr e1, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    exact and_comm
  have hc2 : (E.erase 0).card + 1 = E.card :=
    Finset.card_erase_add_one (by simp [hE])
  have hq := Nat.card_eq_card_units_add_one K
  rw [Nat.card_eq_fintype_card] at hq ⊢
  have he : E.card = Nat.card (unitsFix σ) + 1 := by rw [← hc2, ← hc1]
  rw [he] at hsq
  have hu : Nat.card (unitsFix σ) ≤ 7 := by nlinarith
  omega

theorem eq_one_of_forall_pow_three (h4 : Nat.card K ≠ 4) {σ : K ≃+* K}
    (h : ∀ a : Kˣ, Units.map σ.toRingHom.toMonoidHom a ^ 3 = a ^ 3) : σ = 1 := by
  have hE : (unitsFix σ).comap (powMonoidHom 3 : Kˣ →* Kˣ) = ⊤ := eq_top_iff.mpr fun a _ => by
    rw [Subgroup.mem_comap, powMonoidHom_apply, mem_unitsFix, Units.val_pow_eq_pow_val, map_pow]
    have := congrArg Units.val (h a)
    rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at this
  have h1 := card_comap_pow_three_le (unitsFix σ)
  rw [hE, Subgroup.card_top] at h1
  have h2 := (unitsFix σ).card_mul_index
  have h3 : (unitsFix σ).index ≤ 3 :=
    Nat.le_of_mul_le_mul_left (h2.trans_le (h1.trans (mul_comm _ _).le)) Nat.card_pos
  rcases eq_one_or_card_eq_four_of_index_unitsFix_le_three h3 with h5 | h5
  · exact h5
  · exact absurd h5 h4

end Count

section U3

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut map_bar_comm
  normalizer_hypProjUnitriangular rkOneDHomSU rkOneD rkOneDiag diagonal_gram)
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism (exists_isometry_hypPSU)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

local notation "Ū₃" => hypProjUnitriangular h 1 1

local notation "N₃" => Subgroup.normalizer
  ((hypProjUnitriangular h 1 1 : Subgroup (hypPSU h 1 1)) : Set (hypPSU h 1 1))

@[expose] def u3DEntries (c : K) : HypIndex 1 1 → K
  | .inl _ => 1
  | .inr (.inl _) => c
  | .inr (.inr _) => 1

@[expose] noncomputable def u3D (c : Kˣ) : GL (HypIndex 1 1) K :=
  ⟨diagonal (u3DEntries (c : K)), diagonal (u3DEntries ((c⁻¹ : Kˣ) : K)), by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext x
    rcases x with i | k | i <;> simp [u3DEntries], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext x
    rcases x with i | k | i <;> simp [u3DEntries]⟩

theorem coe_u3D (c : Kˣ) :
    ((u3D c : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      diagonal (u3DEntries (c : K)) :=
  rfl

theorem coe_u3D_inv (c : Kˣ) :
    (((u3D c)⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      diagonal (u3DEntries ((c⁻¹ : Kˣ) : K)) :=
  rfl

theorem u3D_conj_apply (c : Kˣ) (M : Matrix (HypIndex 1 1) (HypIndex 1 1) K)
    (a b : HypIndex 1 1) :
    ((u3D c : Matrix (HypIndex 1 1) (HypIndex 1 1) K) * M *
        (((u3D c)⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) a b =
      u3DEntries (c : K) a * M a b * u3DEntries ((c⁻¹ : Kˣ) : K) b := by
  rw [coe_u3D, coe_u3D_inv, mul_diagonal, diagonal_mul]

theorem norm_det_of_gram {B : GL (HypIndex 1 1) K}
    (hB : ((B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar)ᵀ * hypGram 1 1 K *
      (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = hypGram 1 1 K) :
    h.norm (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det = 1 := by
  have h1 := congrArg Matrix.det hB
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at h1
  have hJ : (hypGram 1 1 K).det ≠ 0 := det_hypGram_ne_zero
  have h2 : (h.bar (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det *
      (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det - 1) * (hypGram 1 1 K).det = 0 := by
    linear_combination h1
  have h3 := (mul_eq_zero.1 h2).resolve_right hJ
  rw [UnitaryFieldData.norm]
  linear_combination h3

theorem scalar_gram_of_norm {c : K} (hc : h.norm c = 1) :
    ((Matrix.scalar (HypIndex 1 1) c).map h.bar)ᵀ * hypGram 1 1 K *
      Matrix.scalar (HypIndex 1 1) c = hypGram 1 1 K := by
  rw [scalar_apply]
  refine diagonal_gram h _ fun x => ?_
  rw [mul_comm]
  exact hc

theorem det_scalar_u3 (c : K) : (Matrix.scalar (HypIndex 1 1) c).det = c ^ 3 := by
  rw [scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, card_hypIndex]

theorem pow_three_mem_range_conj_u3 {B : GL (HypIndex 1 1) K}
    (hB : ((B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar)ᵀ * hypGram 1 1 K *
      (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = hypGram 1 1 K)
    {α : MulAut (hypPSU h 1 1)}
    (hα : ∀ x : hypSU h 1 1, ∃ hx : B * (x : GL (HypIndex 1 1) K) * B⁻¹ ∈ hypSU h 1 1,
      α (hypProj h 1 1 x) = hypProj h 1 1 ⟨_, hx⟩) :
    α ^ 3 ∈ (MulAut.conj : hypPSU h 1 1 →* MulAut (hypPSU h 1 1)).range := by
  set δ : K := (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det with hδ
  have hδ0 : δ ≠ 0 := (Matrix.isUnits_det_units B).ne_zero
  have hNδ : h.norm δ = 1 := norm_det_of_gram h hB
  set d : Kˣ := (Units.mk0 δ hδ0)⁻¹
  have hdK : (d : K) = δ⁻¹ := rfl
  set s : GL (HypIndex 1 1) K := GeneralLinearGroup.scalar (HypIndex 1 1) d
  have hB3 : (((B ^ 3 : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map
      h.bar)ᵀ * hypGram 1 1 K * ((B ^ 3 : GL (HypIndex 1 1) K) :
        Matrix (HypIndex 1 1) (HypIndex 1 1) K) = hypGram 1 1 K := by
    rw [pow_three, Units.val_mul, conjTranspose_mul_mul, Units.val_mul, conjTranspose_mul_mul, hB,
      hB, hB]
  have hS : s * B ^ 3 ∈ hypSU h 1 1 := by
    refine mem_hypSU.mpr ⟨?_, ?_⟩
    · rw [Units.val_mul, conjTranspose_mul_mul, GeneralLinearGroup.coe_scalar,
        scalar_gram_of_norm h (by rw [hdK, norm_inv_eq h, hNδ, inv_one]), hB3]
    · rw [Units.val_mul, det_mul, GeneralLinearGroup.coe_scalar, det_scalar_u3,
        Units.val_pow_eq_pow_val, det_pow, ← hδ, hdK, ← mul_pow, inv_mul_cancel₀ hδ0, one_pow]
  refine ⟨hypProj h 1 1 ⟨_, hS⟩, MulEquiv.ext fun z => ?_⟩
  obtain ⟨x, rfl⟩ := hypProj_surjective h 1 1 z
  obtain ⟨h1, e1⟩ := hα x
  obtain ⟨h2, e2⟩ := hα ⟨_, h1⟩
  obtain ⟨h3, e3⟩ := hα ⟨_, h2⟩
  rw [MulAut.conj_apply, pow_three α, MulAut.mul_apply, MulAut.mul_apply, e1, e2, e3, ← map_inv,
    ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hc : ∀ X : GL (HypIndex 1 1) K, s * X * s⁻¹ = X := fun X => by
    rw [← (commute_scalar d X).eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [pow_three B]
  calc s * (B * (B * B)) * (x : GL (HypIndex 1 1) K) * (s * (B * (B * B)))⁻¹ =
      s * (B * (B * B) * (x : GL (HypIndex 1 1) K) * (B * (B * B))⁻¹) * s⁻¹ := by group
    _ = B * (B * B) * (x : GL (HypIndex 1 1) K) * (B * (B * B))⁻¹ := hc _
    _ = _ := by group

theorem exists_u3_normal_form (hq : 2 < p ^ f) (α : MulAut (hypPSU h 1 1)) :
    ∃ (σ : K ≃+* K) (c : Kˣ) (g : hypSU h 1 1) (ψ : MulAut (hypPSU h 1 1)),
      α = MulAut.conj (hypProj h 1 1 g) * ψ ∧
      (∀ x : hypSU h 1 1, ∃ y : hypSU h 1 1,
        (y : GL (HypIndex 1 1) K) = u3D c * glAut σ (x : GL (HypIndex 1 1) K) * (u3D c)⁻¹ ∧
          ψ (hypProj h 1 1 x) = hypProj h 1 1 y) ∧
      (σ = 1 → α ^ 3 ∈ (MulAut.conj : hypPSU h 1 1 →* MulAut (hypPSU h 1 1)).range) := by
  obtain ⟨σ, B, hB, hα⟩ := exists_isometry_hypPSU h hq α
  set δ : K := (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det with hδ
  have hδ0 : δ ≠ 0 := (Matrix.isUnits_det_units B).ne_zero
  have hNδ : h.norm δ = 1 := norm_det_of_gram h hB
  set c : Kˣ := Units.mk0 δ hδ0
  have hcK : (c : K) = δ := rfl
  have hgS : B * (u3D c)⁻¹ ∈ hypSU h 1 1 := by
    refine mem_hypSU.mpr ⟨?_, ?_⟩
    · rw [Units.val_mul, conjTranspose_mul_mul, hB, coe_u3D_inv]
      refine diagonal_gram h _ fun x => ?_
      rcases x with i | k | i
      · simp [u3DEntries]
      · change h.bar ((c⁻¹ : Kˣ) : K) * ((c⁻¹ : Kˣ) : K) = 1
        rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, mul_comm, hcK]
        rw [UnitaryFieldData.norm] at hNδ
        rw [hNδ, inv_one]
      · simp [u3DEntries]
    · rw [Units.val_mul, det_mul, coe_u3D_inv, det_diagonal, ← hδ]
      simp only [Fintype.prod_sum_type, Finset.univ_unique, Finset.prod_singleton, u3DEntries,
        mul_one, one_mul, Units.val_inv_eq_inv_val, hcK]
      exact mul_inv_cancel₀ hδ0
  set g : hypSU h 1 1 := ⟨_, hgS⟩
  refine ⟨σ, c, g, (MulAut.conj (hypProj h 1 1 g))⁻¹ * α, by rw [mul_inv_cancel_left],
    fun x => ?_, fun hσ => ?_⟩
  · obtain ⟨hx, ex⟩ := hα x
    refine ⟨g⁻¹ * ⟨_, hx⟩ * g, ?_, ?_⟩
    · change (B * (u3D c)⁻¹)⁻¹ * (B * glAut σ (x : GL (HypIndex 1 1) K) * B⁻¹) *
        (B * (u3D c)⁻¹) = _
      group
    · rw [MulAut.mul_apply, ex, ← map_inv, MulAut.conj_apply, inv_inv, ← map_inv, ← map_mul,
        ← map_mul]
  · subst hσ
    refine pow_three_mem_range_conj_u3 h hB fun x => ?_
    obtain ⟨hx, ex⟩ := hα x
    exact ⟨hx, ex⟩

@[expose] noncomputable def u3T : Kˣ →* hypPSU h 1 1 :=
  (hypProj h 1 1).comp (rkOneDHomSU h)

theorem u3T_apply (a : Kˣ) : u3T h a = hypProj h 1 1 (rkOneDHomSU h a) :=
  rfl

theorem coe_rkOneDHomSU (a : Kˣ) :
    (((rkOneDHomSU h a : hypSU h 1 1) : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) = diagonal (rkOneDiag h a) :=
  rfl

theorem u3T_mem (c : Kˣ) (hc : u3T h c ∈ Ū₃) : h.norm (c : K) = 1 ∧ c ^ 3 = 1 := by
  obtain ⟨u, hu, he⟩ := hc
  have hz : u⁻¹ * rkOneDHomSU h c ∈ hypScalars h 1 1 := by
    rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, he, u3T_apply, inv_mul_cancel]
  obtain ⟨l, hlN, hl3, hl⟩ := mem_normOneScalars.mp hz
  have h1 : ((rkOneDHomSU h c : hypSU h 1 1) : GL (HypIndex 1 1) K) =
      (u : GL (HypIndex 1 1) K) * GeneralLinearGroup.scalar (HypIndex 1 1) l := by
    rw [← hl, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  have h2 := congrArg (fun M : GL (HypIndex 1 1) K =>
    (M : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inl 0) (.inl 0)) h1
  simp only [coe_rkOneDHomSU, diagonal_apply_eq, Units.val_mul, GeneralLinearGroup.coe_scalar,
    scalar_apply, mul_diagonal, (mem_hypUnitriangular.mp hu).2, one_mul] at h2
  have hcl : c = l := Units.ext h2
  subst hcl
  exact ⟨hlN, hl3⟩

theorem u3T_range_le : (u3T h).range ≤ N₃ := by
  rintro _ ⟨a, rfl⟩
  rw [normalizer_hypProjUnitriangular h le_rfl le_rfl]
  refine ⟨rkOneDHomSU h a, mem_hypBorel_of_blockTriangular h ?_, rfl⟩
  rw [coe_rkOneDHomSU]
  exact blockTriangular_diagonal _

theorem u3_comm_mem : ∀ a ∈ N₃, ∀ b ∈ N₃, a * b * a⁻¹ * b⁻¹ ∈ Ū₃ := by
  intro a ha b hb
  rw [normalizer_hypProjUnitriangular h le_rfl le_rfl] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have key : ∀ x y : Fin 1 → Kˣ, x * y * x⁻¹ * y⁻¹ = 1 := fun x y => by
    rw [mul_comm x y]
    group
  have hk : (⟨a', ha'⟩ * ⟨b', hb'⟩ * (⟨a', ha'⟩ : hypBorel h 1 1)⁻¹ *
      (⟨b', hb'⟩ : hypBorel h 1 1)⁻¹ : hypBorel h 1 1) ∈
        (hypUnitriangular h 1 1).subgroupOf (hypBorel h 1 1) := by
    rw [← ker_hypDiagHom le_rfl, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact key _ _
  exact ⟨_, Subgroup.mem_subgroupOf.mp hk, by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]⟩

variable {h}

theorem map_u3_psi [Finite K] {ψ : MulAut (hypPSU h 1 1)} {σ : K ≃+* K} {c : Kˣ}
    (hψ : ∀ x : hypSU h 1 1, ∃ y : hypSU h 1 1,
      (y : GL (HypIndex 1 1) K) = u3D c * glAut σ (x : GL (HypIndex 1 1) K) * (u3D c)⁻¹ ∧
        ψ (hypProj h 1 1 x) = hypProj h 1 1 y) :
    (Ū₃).map ψ.toMonoidHom = Ū₃ := by
  refine map_eq_of_forall_mem ?_
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨y, hy, he⟩ := hψ u
  have hu' := mem_hypUnitriangular.mp hu
  refine ⟨y, mem_hypUnitriangular.mpr ⟨fun a b hab => ?_, fun a => ?_⟩, he.symm⟩
  · rw [hy, Units.val_mul, Units.val_mul, u3D_conj_apply, coe_glAut, Matrix.map_apply,
      hu'.1 hab, map_zero, mul_zero, zero_mul]
  · rw [hy, Units.val_mul, Units.val_mul, u3D_conj_apply, coe_glAut, Matrix.map_apply, hu'.2 a,
      map_one, mul_one]
    rcases a with i | k | i <;> simp [u3DEntries]

theorem u3_psi_u3T {ψ : MulAut (hypPSU h 1 1)} {σ : K ≃+* K} {c : Kˣ}
    (hψ : ∀ x : hypSU h 1 1, ∃ y : hypSU h 1 1,
      (y : GL (HypIndex 1 1) K) = u3D c * glAut σ (x : GL (HypIndex 1 1) K) * (u3D c)⁻¹ ∧
        ψ (hypProj h 1 1 x) = hypProj h 1 1 y) (a : Kˣ) :
    ψ (u3T h a) = u3T h (Units.map σ.toRingHom.toMonoidHom a) := by
  obtain ⟨y, hy, he⟩ := hψ (rkOneDHomSU h a)
  rw [u3T_apply, he, u3T_apply]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [hy, Units.val_mul, Units.val_mul, coe_glAut, coe_rkOneDHomSU, coe_rkOneDHomSU, coe_u3D,
    coe_u3D_inv, diagonal_map (map_zero σ), diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext x
  have hc : (c : K) ≠ 0 := c.ne_zero
  rcases x with i | k | i
  · simp [u3DEntries, rkOneDiag]
  · simp only [u3DEntries, rkOneDiag, map_div₀, map_bar_comm, Units.coe_map,
      Units.val_inv_eq_inv_val]
    field_simp
    exact mul_comm _ _
  · simp [u3DEntries, rkOneDiag, map_bar_comm]

theorem mem_of_mem_comap_u3 {ψ : MulAut (hypPSU h 1 1)} {σ : K ≃+* K} {c : Kˣ}
    (hψ : ∀ x : hypSU h 1 1, ∃ y : hypSU h 1 1,
      (y : GL (HypIndex 1 1) K) = u3D c * glAut σ (x : GL (HypIndex 1 1) K) * (u3D c)⁻¹ ∧
        ψ (hypProj h 1 1 x) = hypProj h 1 1 y) {a : Kˣ}
    (ha : a ∈ (centMod Ū₃ ψ).comap (u3T h)) :
    h.norm ((Units.map σ.toRingHom.toMonoidHom a * a⁻¹ : Kˣ) : K) = 1 ∧
      (Units.map σ.toRingHom.toMonoidHom a * a⁻¹) ^ 3 = 1 := by
  rw [Subgroup.mem_comap, mem_centMod, u3_psi_u3T hψ, ← map_inv, ← map_mul] at ha
  exact u3T_mem h _ ha.2

end U3

section Main

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type} [Field K]

theorem isSylowTwoOf_u3 (h : UnitaryFieldData 2 n K) :
    IsSylowTwoOf (hypProjUnitriangular h 1 1) ⊤ := by
  have := h.finite
  obtain ⟨P, hP⟩ := (unitary_order_and_Sylow h le_rfl le_rfl).2.2.2.2.1
  rw [← hP]
  exact isSylowTwoOf_sylow P

theorem n4At_u3 (h : UnitaryFieldData 2 n K) (hn : 2 ≤ n) :
    N4At (hypPSU h 1 1) (hypProjUnitriangular h 1 1) := by
  have := h.finite
  have hq : 2 < 2 ^ n := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK4 : Nat.card K ≠ 4 := by
    rw [h.card]
    have : 2 ^ 4 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  intro α hα hαU hcent
  obtain ⟨σ, c, g, ψ, rfl, hψ, h3⟩ := exists_u3_normal_form h hq α
  rw [centMod_conj_mul_eq (u3_comm_mem h) (map_u3_psi hψ) hαU] at hcent
  have hσ : σ = 1 := eq_one_of_forall_pow_three hK4 fun a => by
    have h1 := (mem_of_mem_comap_u3 hψ (hcent (u3T_range_le h ⟨a, rfl⟩))).2
    rwa [mul_pow, inv_pow, mul_inv_eq_one] at h1
  exact Or.inl (mem_of_pow_three_mem (h3 hσ) hα)

theorem n2At_u3 (h : UnitaryFieldData 2 n K) (hn : 2 ≤ n)
    (hE : n = 3 → ExcLie (hypPSU h 1 1)) : N2At (hypPSU h 1 1) (hypProjUnitriangular h 1 1) := by
  have := h.finite
  have hq : 2 < 2 ^ n := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  intro α hα hαU hidx
  obtain ⟨σ, c, g, ψ, rfl, hψ, h3⟩ := exists_u3_normal_form h hq α
  have hψU := map_u3_psi hψ
  have hσ : σ ≠ 1 := by
    intro hσ
    obtain ⟨y, hy⟩ := mem_of_pow_three_mem (h3 hσ) hα
    rw [← hy] at hαU hidx
    have hyN := mem_normalizer_of_map_conj_eq hαU
    have hN : centMod (hypProjUnitriangular h 1 1) (MulAut.conj y) =
        Subgroup.normalizer ((hypProjUnitriangular h 1 1 : Subgroup (hypPSU h 1 1)) :
          Set (hypPSU h 1 1)) :=
      le_antisymm (centMod_le_normalizer _ _) fun b hb =>
        ⟨hb, conj_mul_inv_mem (u3_comm_mem h) hyN b hb⟩
    rw [hN, Subgroup.relIndex_self] at hidx
    omega
  rw [centMod_conj_mul_eq (u3_comm_mem h) hψU hαU] at hidx
  have h1 := index_comap_le (hypProjUnitriangular h 1 1) ψ (u3T h) (u3T_range_le h)
  rw [hidx] at h1
  have hcE : (centMod (hypProjUnitriangular h 1 1) ψ).comap (u3T h) ≤
      (unitsFix σ).comap (powMonoidHom 3 : Kˣ →* Kˣ) := fun a ha => by
    have h31 := (mem_of_mem_comap_u3 hψ ha).2
    rw [mul_pow, inv_pow, mul_inv_eq_one] at h31
    rw [Subgroup.mem_comap, powMonoidHom_apply, mem_unitsFix, Units.val_pow_eq_pow_val, map_pow]
    have := congrArg Units.val h31
    rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at this
  have hEidx := (Subgroup.index_antitone hcE).trans h1
  have hcard : Nat.card Kˣ ≤ 9 * Nat.card (unitsFix σ) := by
    have h2 := ((unitsFix σ).comap (powMonoidHom 3 : Kˣ →* Kˣ)).card_mul_index
    have h4 := card_comap_pow_three_le (unitsFix σ)
    rw [← h2]
    nlinarith
  have h64 := card_le_sixtyFour hσ hcard
  have hKc := h.card
  have hn3 : n ≤ 3 := by
    by_contra hn3
    have : 2 ^ 8 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain rfl | rfl : n = 2 ∨ n = 3 := by omega
  ·
    exfalso
    have hcF : (centMod (hypProjUnitriangular h 1 1) ψ).comap (u3T h) ≤ unitsFix σ :=
      fun a ha => by
        obtain ⟨hN1, h31⟩ := mem_of_mem_comap_u3 hψ ha
        set x : Kˣ := Units.map σ.toRingHom.toMonoidHom a * a⁻¹ with hx
        have hx5 : (x : K) ^ 5 = 1 := by
          rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at hN1
          rw [← hN1]
          ring
        have hx3 : (x : K) ^ 3 = 1 := by
          rw [← Units.val_pow_eq_pow_val, h31, Units.val_one]
        have hx1 : x = 1 := by
          refine Units.ext ?_
          have hx0 : (x : K) ≠ 0 := x.ne_zero
          calc (x : K) = ((x : K) ^ 3) ^ 2 / (x : K) ^ 5 := by field_simp
            _ = 1 := by rw [hx3, hx5]; norm_num
        rw [hx, mul_inv_eq_one] at hx1
        exact congrArg Units.val hx1
    have hFidx := (Subgroup.index_antitone hcF).trans h1
    rcases eq_one_or_card_eq_four_of_index_unitsFix_le_three hFidx with h5 | h5
    · exact hσ h5
    · rw [hKc] at h5
      norm_num at h5
  · exact hE rfl

end Main

theorem n2Model_n4Model_of_isPSU3 {M : Type} [Group M] {n : ℕ} (hn : 1 < n)
    (hM : IsPSU 3 2 n M) : N2Model M ∧ N4Model M := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hM
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_isHypTransport (r := 1) (ε := 1) h
  let e' : M ≃* CFSG.ClassicalGroups.UnitaryFlag.hypPSU h 1 1 :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.hypPSUEquivStatedProj h hR (by norm_num)).symm
  have hE : n = 3 → ExcLie (CFSG.ClassicalGroups.UnitaryFlag.hypPSU h 1 1) := fun h3 =>
    ExcLie.map e' (Or.inr (Or.inl (h3 ▸ hM)))
  exact ⟨(N2Model.of_at (isSylowTwoOf_u3 h) (n2At_u3 h hn hE)).of_mulEquiv e'.symm,
    (N4Model.of_at (isSylowTwoOf_u3 h) (n4At_u3 h hn)).of_mulEquiv e'.symm⟩

end CFSG.Quasithin.H13.L32A.C.SkPf
