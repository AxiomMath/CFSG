module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGProper
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConjLabels

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp
open scoped commutatorElement

namespace L45Fix

@[expose] def invol (M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) (h : M * M = 1) :
    GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  ⟨M, M, h, h⟩

@[expose] def gP (j : Fin 4) : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  invol ((pairSwap j).permMatrix (ZMod 2))
    (by rw [← Matrix.permMatrix_mul, pairSwap, Equiv.swap_mul_self, Matrix.permMatrix_one])

@[expose] def gW : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  invol (Equiv.Perm.permMatrix (ZMod 2) (Equiv.sumComm (Fin 4) (Fin 4))) (by decide +kernel)

@[expose] def gS (i j : Fin 4) : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  invol (siegelMat i j 1)
    (by rw [siegelMat_mul, show (1 : ZMod 2) + 1 = 0 from rfl, siegelMat_zero])

@[expose] def z1 : GL (Fin 4 ⊕ Fin 4) (ZMod 2) := ⁅gW * gS 0 1 * gW, gS 0 1⁆

@[expose] def z2 : GL (Fin 4 ⊕ Fin 4) (ZMod 2) := ⁅gP 0 * gS 0 1 * gP 0, gP 1 * gS 0 1 * gP 1⁆

@[expose] def z3 : GL (Fin 4 ⊕ Fin 4) (ZMod 2) := ⁅gP 2 * gS 2 3 * gP 2, gP 3 * gS 2 3 * gP 3⁆

@[expose] def w0 : GL (Fin 4 ⊕ Fin 4) (ZMod 2) := ⁅gP 0 * gS 0 2 * gP 0, gS 0 3⁆

theorem z1_cube : z1 ^ 3 = 1 := by decide +kernel

theorem z2_cube : z2 ^ 3 = 1 := by decide +kernel

theorem z3_cube : z3 ^ 3 = 1 := by decide +kernel

theorem w0_sq : w0 ^ 2 = 1 := by decide +kernel

theorem commute_z1_z2 : Commute z1 z2 := by
  change z1 * z2 = z2 * z1
  decide +kernel

theorem commute_z1_z3 : Commute z1 z3 := by
  change z1 * z3 = z3 * z1
  decide +kernel

theorem commute_z2_z3 : Commute z2 z3 := by
  change z2 * z3 = z3 * z2
  decide +kernel

theorem commute_w0_z1 : Commute w0 z1 := by
  change w0 * z1 = z1 * w0
  decide +kernel

theorem commute_w0_z2 : Commute w0 z2 := by
  change w0 * z2 = z2 * w0
  decide +kernel

theorem commute_w0_z3 : Commute w0 z3 := by
  change w0 * z3 = z3 * w0
  decide +kernel

theorem w0_apply :
    (w0 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) (.inl 2) (.inr 3) = 1 := by
  decide +kernel

theorem exists_offDiag_of_ne : ∀ a b c : ZMod 3, (a, b, c) ≠ (0, 0, 0) →
    ∃ r s : Fin 4 ⊕ Fin 4, r ≠ s ∧
      ((z1 ^ a.val * (z2 ^ b.val * z3 ^ c.val) : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) r s = 1 := by
  decide +kernel

abbrev M3 : Type := Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 3)

theorem zmod_three_pow (a : Multiplicative (ZMod 3)) : a ^ 3 = 1 := by
  rw [← ofAdd_toAdd a, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

theorem m3_pow_three (x : M3) : x ^ 3 = 1 :=
  Prod.ext (zmod_three_pow _) (Prod.ext (zmod_three_pow _) (zmod_three_pow _))

theorem card_m3 : Nat.card M3 = 27 := by
  rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    ZMod.card]

theorem isElemAbelian_range_m3 {G : Type*} [Group G] (χ : M3 →* G) : IsElemAbelian 3 χ.range := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, x, rfl⟩ := a
    obtain ⟨_, y, rfl⟩ := b
    change χ x * χ y = χ y * χ x
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, m3_pow_three x, map_one]

theorem card_range_m3 {G : Type*} [Group G] {χ : M3 →* G} (hχ : Function.Injective χ) :
    Nat.card χ.range = 27 := by
  rw [← card_m3]
  exact Nat.card_congr (MonoidHom.ofInjective hχ).toEquiv.symm

theorem commute_zmodPowHom {G : Type*} [Group G] {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (h : Commute a b) (x y : Multiplicative (ZMod 3)) :
    Commute (zmodPowHom ha x) (zmodPowHom hb y) := by
  rw [zmodPowHom_apply, zmodPowHom_apply]
  exact h.pow_pow _ _

@[expose] noncomputable def triHom : M3 →* GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  (zmodPowHom z1_cube).noncommCoprod
    ((zmodPowHom z2_cube).noncommCoprod (zmodPowHom z3_cube)
      (commute_zmodPowHom z2_cube z3_cube commute_z2_z3))
    (fun x y => by
      rw [MonoidHom.noncommCoprod_apply]
      exact (commute_zmodPowHom z1_cube z2_cube commute_z1_z2 x y.1).mul_right
        (commute_zmodPowHom z1_cube z3_cube commute_z1_z3 x y.2))

theorem triHom_apply (x : M3) :
    triHom x = z1 ^ (Multiplicative.toAdd x.1).val *
      (z2 ^ (Multiplicative.toAdd x.2.1).val * z3 ^ (Multiplicative.toAdd x.2.2).val) := by
  rw [triHom, MonoidHom.noncommCoprod_apply, MonoidHom.noncommCoprod_apply, zmodPowHom_apply,
    zmodPowHom_apply, zmodPowHom_apply]

theorem commute_w0_triHom (x : M3) : Commute w0 (triHom x) := by
  rw [triHom_apply]
  exact (commute_w0_z1.pow_right _).mul_right
    ((commute_w0_z2.pow_right _).mul_right (commute_w0_z3.pow_right _))

section Field

variable {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] noncomputable def toK : GL (Fin 4 ⊕ Fin 4) (ZMod 2) →* GL (Fin 4 ⊕ Fin 4) K :=
  Matrix.GeneralLinearGroup.map (ZMod.castHom (dvd_refl 2) K)

theorem toK_val (g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
    ((toK K g : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)).map (ZMod.castHom (dvd_refl 2) K) :=
  rfl

theorem toK_gP (j : Fin 4) : toK K (gP j) = TauCeti.permutationGL (pairSwap j) := by
  apply Units.ext
  rw [toK_val, TauCeti.permutationGL_coe, pairSwap_inv]
  exact PEquiv.map_toMatrix _ _

theorem toK_gW : toK K gW = TauCeti.permutationGL (Equiv.sumComm (Fin 4) (Fin 4)) := by
  apply Units.ext
  rw [toK_val, TauCeti.permutationGL_coe, Equiv.Perm.inv_def, Equiv.sumComm_symm]
  exact PEquiv.map_toMatrix _ _

theorem toK_gS (i j : Fin 4) : toK K (gS i j) = siegelGL i j 1 := by
  apply Units.ext
  rw [toK_val, coe_siegelGL]
  change (siegelMat i j (1 : ZMod 2)).map (ZMod.castHom (dvd_refl 2) K) = siegelMat i j 1
  simp only [siegelMat, siegelS, Matrix.fromBlocks_map, one_smul,
    Matrix.map_add (ZMod.castHom (dvd_refl 2) K) (map_add _), Matrix.map_single, map_one,
    Matrix.map_zero (ZMod.castHom (dvd_refl 2) K) (map_zero _),
    Matrix.map_one (ZMod.castHom (dvd_refl 2) K) (map_zero _) (map_one _)]

theorem toK_gP_mem (j : Fin 4) : toK K (gP j) ∈ LargeEvenOrthGroup (LargeEvenQPlus K 4) := by
  rw [toK_gP]
  exact pairSwap_mem_orthPlus j

theorem toK_gW_mem : toK K gW ∈ LargeEvenOrthGroup (LargeEvenQPlus K 4) := by
  rw [toK_gW]
  exact sumComm_mem_orthPlus

theorem toK_gS_mem (i j : Fin 4) : toK K (gS i j) ∈ LargeEvenOrthGroup (LargeEvenQPlus K 4) := by
  rw [toK_gS]
  exact siegelGL_mem_orthPlus i j 1

theorem toK_conj_mem {g s : GL (Fin 4 ⊕ Fin 4) (ZMod 2)}
    (hg : toK K g ∈ LargeEvenOrthGroup (LargeEvenQPlus K 4))
    (hs : toK K s ∈ LargeEvenOrthGroup (LargeEvenQPlus K 4)) :
    toK K (g * s * g) ∈ LargeEvenOrthGroup (LargeEvenQPlus K 4) := by
  rw [map_mul, map_mul]
  exact mul_mem (mul_mem hg hs) hg

theorem toK_commutator_mem {a b : GL (Fin 4 ⊕ Fin 4) (ZMod 2)}
    (ha : toK K a ∈ LargeEvenOrthGroup (LargeEvenQPlus K 4))
    (hb : toK K b ∈ LargeEvenOrthGroup (LargeEvenQPlus K 4)) :
    toK K ⁅a, b⁆ ∈ LargeEvenOmega (LargeEvenQPlus K 4) := by
  rw [map_commutatorElement]
  exact Subgroup.commutator_mem_commutator ha hb

variable (K) in
@[expose] noncomputable def omega2 : Subgroup (GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :=
  (LargeEvenOmega (LargeEvenQPlus K 4)).comap (toK K)

theorem z1_mem : z1 ∈ omega2 K :=
  toK_commutator_mem (toK_conj_mem toK_gW_mem (toK_gS_mem 0 1)) (toK_gS_mem 0 1)

theorem z2_mem : z2 ∈ omega2 K :=
  toK_commutator_mem (toK_conj_mem (toK_gP_mem 0) (toK_gS_mem 0 1))
    (toK_conj_mem (toK_gP_mem 1) (toK_gS_mem 0 1))

theorem z3_mem : z3 ∈ omega2 K :=
  toK_commutator_mem (toK_conj_mem (toK_gP_mem 2) (toK_gS_mem 2 3))
    (toK_conj_mem (toK_gP_mem 3) (toK_gS_mem 2 3))

theorem w0_mem : w0 ∈ omega2 K :=
  toK_commutator_mem (toK_conj_mem (toK_gP_mem 0) (toK_gS_mem 0 2)) (toK_gS_mem 0 3)

theorem triHom_mem (x : M3) : triHom x ∈ omega2 K := by
  rw [triHom_apply]
  exact mul_mem (pow_mem z1_mem _) (mul_mem (pow_mem z2_mem _) (pow_mem z3_mem _))

variable (K) in
@[expose] noncomputable def toR :
    omega2 K →* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)) :=
  (LargeEvenProjMk _).comp ((toK K).subgroupComap _)

theorem toR_apply (g : omega2 K) : toR K g = LargeEvenProjMk _ ⟨toK K g, g.2⟩ :=
  rfl

theorem toR_ne_one {g : omega2 K} {r s : Fin 4 ⊕ Fin 4} (hrs : r ≠ s)
    (h : ((g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) r s =
      1) :
    toR K g ≠ 1 := by
  intro h1
  rw [toR_apply] at h1
  have hmem := (QuotientGroup.eq_one_iff _).mp h1
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := hmem
  have e := congrArg
    (fun x : GL (Fin 4 ⊕ Fin 4) K => (x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) r s) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ hrs] at e
  rw [toK_val, Matrix.map_apply, h, map_one] at e
  exact zero_ne_one e

theorem fieldImage_apply_toR {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4))))
    (g : omega2 K) : f (toR K g) = toR K g := by
  obtain ⟨σ, hσ⟩ := hf
  rw [toR_apply]
  refine hσ _ _ ?_
  change (toK K g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
    (toK K g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K).map σ
  rw [toK_val, Matrix.map_map]
  congr 1
  funext x
  exact (DFunLike.congr_fun (RingHom.ext_zmod (σ.toRingHom.comp (ZMod.castHom (dvd_refl 2) K))
    (ZMod.castHom (dvd_refl 2) K)) x).symm

variable (K) in
@[expose] noncomputable def torusR : M3 →* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)) :=
  (toR K).comp (triHom.codRestrict (omega2 K) triHom_mem)

theorem torusR_apply (x : M3) : torusR K x = toR K ⟨triHom x, triHom_mem x⟩ :=
  rfl

theorem torusR_injective : Function.Injective (torusR K) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  have hne : (Multiplicative.toAdd x.1, Multiplicative.toAdd x.2.1, Multiplicative.toAdd x.2.2) ≠
      (0, 0, 0) := by
    intro h
    apply hx1
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    exact Prod.ext (toAdd_eq_zero.mp h1) (Prod.ext (toAdd_eq_zero.mp h2) (toAdd_eq_zero.mp h3))
  obtain ⟨r, s, hrs, h⟩ := exists_offDiag_of_ne _ _ _ hne
  refine toR_ne_one (g := ⟨triHom x, triHom_mem x⟩) hrs ?_ hx
  change (triHom x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) r s = 1
  rw [triHom_apply]
  exact h

variable (K) in
@[expose] noncomputable def invR : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)) :=
  toR K ⟨w0, w0_mem⟩

theorem invR_sq : invR K ^ 2 = 1 := by
  rw [invR, ← map_pow]
  have h : (⟨w0, w0_mem⟩ : omega2 K) ^ 2 = 1 := Subtype.ext w0_sq
  rw [h, map_one]

theorem invR_ne_one : invR K ≠ 1 :=
  toR_ne_one (g := ⟨w0, w0_mem⟩) (r := .inl 2) (s := .inr 3) Sum.inl_ne_inr w0_apply

theorem commute_torusR_invR (x : M3) : Commute (torusR K x) (invR K) := by
  rw [torusR_apply, invR]
  refine Commute.map ?_ (toR K)
  exact Subtype.ext (commute_w0_triHom x).symm.eq

end Field

end L45Fix

namespace L45Fix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggD4FieldFixLocal_omegaPlus :
    GGD4FieldFixLocal (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  intro hs hna φ hφ3 hφI hφ
  obtain ⟨u, hu, f, hf, rfl⟩ := hφ
  obtain ⟨f', hf'F, _, ⟨r, rfl⟩, -, heq⟩ :=
    RecipeFieldOmega.ggRawFieldConj_omegaPlus (K := K) (m := 4) (by norm_num) Nat.prime_three
      (by norm_num) hs hna u hu f hf (fun h => hφI (by obtain ⟨y, hy⟩ := h; exact ⟨y, hy⟩)) hφ3
  rw [heq]
  set c : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) := MulAut.conj r with hc
  have hcf : ∀ y, (c * f' * c⁻¹) (c y) = c (f' y) := fun y => by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have hfix : ∀ g : omega2 K, (c * f' * c⁻¹) (c (toR K g)) = c (toR K g) := fun g => by
    rw [hcf, fieldImage_apply_toR hf'F]
  refine ⟨(c.toMonoidHom.comp (torusR K)).range, c (invR K), isElemAbelian_range_m3 _,
    card_range_m3 (c.injective.comp torusR_injective), ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hfix ⟨triHom x, triHom_mem x⟩
  · rw [← map_pow, invR_sq, map_one]
  · intro h1
    exact invR_ne_one ((map_eq_one_iff c c.injective).mp h1)
  · exact hfix ⟨w0, w0_mem⟩
  · rintro _ ⟨x, rfl⟩
    change c (torusR K x) * c (invR K) = c (invR K) * c (torusR K x)
    rw [← map_mul, ← map_mul, (commute_torusR_invR x).eq]

end L45Fix

open L45Fix

theorem ggD4FieldFixLocal_labelAll (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .D) (h4 : lab.rank = 4) : LargeEvenLabelAll lab GGD4FieldFixLocal := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h4
  subst h4
  exact largeEvenLabelAll_omegaPlus ht le_rfl fun _ _ _ _ _ => ggD4FieldFixLocal_omegaPlus

theorem ggD4FieldFixLocalOddInput_holds : GGD4FieldFixLocalOddInput :=
  fun lab hlab ht h4 _ => ggD4FieldFixLocal_labelAll lab hlab ht h4

end CFSG.StandardType
