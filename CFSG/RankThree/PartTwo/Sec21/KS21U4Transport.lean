module

public import CFSG.RankThree.PartTwo.Sec21.Item229URoots
public import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.RankThree.PartTwo.Sec21.U4Lines

open CFSG CFSG.RankThree
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly.LowTwoRank (StatedScalars StatedSU)
open CFSG.LieType.Universal.Unitary (SU equivStatedSU)
open CFSG.LieType.BorelTits (unitaryInvolution)

variable {G G' : Type} [Group G] [Group G']

@[expose] def LinesHyp (Y ℓ₁ ℓ₂ ℓ₃ : Subgroup G) : Prop :=
  ℓ₁ ≤ Y ∧ ℓ₂ ≤ Y ∧ ℓ₁ ≤ Subgroup.centralizer (ℓ₂ : Set G) ∧
    Nat.card ℓ₁ = 3 ∧ Nat.card ℓ₂ = 3 ∧ Nat.card ℓ₃ = 3 ∧ ℓ₃ ≤ ℓ₁ ⊔ ℓ₂ ∧
    ℓ₁ ≠ ℓ₂ ∧ ℓ₃ ≠ ℓ₁ ∧ ℓ₃ ≠ ℓ₂ ∧
    ℓ₂ ≤ inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ₁ : Set G))

@[expose] def LinesConcl (Y ℓ₁ ℓ₃ : Subgroup G) (b : ℕ) : Prop :=
  (Nonempty (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ₁ : Set G)) ≃*
      projSL 2 (GaloisField 2 b)) ∧
    Nonempty (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ₃ : Set G)) ≃*
      projSL 2 (GaloisField 2 (2 * b)))) ∨
  (Nonempty (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ₁ : Set G)) ≃*
      projSL 2 (GaloisField 2 (2 * b))) ∧
    Nonempty (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ₃ : Set G)) ≃*
      projSL 2 (GaloisField 2 b)))

@[expose] def LinesAt (Y : Subgroup G) (b : ℕ) : Prop :=
  ∀ ℓ₁ ℓ₂ ℓ₃ : Subgroup G, LinesHyp Y ℓ₁ ℓ₂ ℓ₃ → LinesConcl Y ℓ₁ ℓ₃ b

theorem u4ThreeTorusLines_of_linesAt
    (h : ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G) (b : ℕ), 0 < b → Even b →
      Nonempty (Y ≃* projSU 4 2 b) → LinesAt Y b) : U4ThreeTorusLines := by
  intro G _ _ Y b hb hbe hY ℓ₁ ℓ₂ ℓ₃ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  exact h G Y b hb hbe hY ℓ₁ ℓ₂ ℓ₃ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

section Transport

variable {Y : Subgroup G} {Y' : Subgroup G'} (e : Y ≃* Y')

@[expose] def embedOf : Y →* G' := Y'.subtype.comp e.toMonoidHom

theorem embedOf_injective : Function.Injective (embedOf e) :=
  Y'.subtype_injective.comp e.injective

@[expose] def mapL (Z : Subgroup G) : Subgroup G' := (Z.subgroupOf Y).map (embedOf e)

theorem mapL_le (Z : Subgroup G) : mapL e Z ≤ Y' := by
  rintro _ ⟨z, -, rfl⟩
  exact (e z).2

theorem mapL_mono {Z₁ Z₂ : Subgroup G} (h : Z₁ ≤ Z₂) : mapL e Z₁ ≤ mapL e Z₂ :=
  Subgroup.map_mono (Subgroup.comap_mono h)

noncomputable def mapLEquiv {Z : Subgroup G} (hZ : Z ≤ Y) : Z ≃* mapL e Z :=
  (Subgroup.subgroupOfEquivOfLe hZ).symm.trans
    ((Z.subgroupOf Y).equivMapOfInjective _ (embedOf_injective e))

theorem card_mapL {Z : Subgroup G} (hZ : Z ≤ Y) : Nat.card (mapL e Z) = Nat.card Z :=
  (Nat.card_congr (mapLEquiv e hZ).toEquiv).symm

theorem mapL_sup {Z₁ Z₂ : Subgroup G} (h₁ : Z₁ ≤ Y) (h₂ : Z₂ ≤ Y) :
    mapL e (Z₁ ⊔ Z₂) = mapL e Z₁ ⊔ mapL e Z₂ := by
  rw [mapL, Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]
  rfl

theorem mapL_inj {Z₁ Z₂ : Subgroup G} (h₁ : Z₁ ≤ Y) (h₂ : Z₂ ≤ Y)
    (h : mapL e Z₁ = mapL e Z₂) : Z₁ = Z₂ := by
  have h' := Subgroup.map_injective (embedOf_injective e) h
  rwa [Subgroup.subgroupOf_inj, inf_eq_left.mpr h₁, inf_eq_left.mpr h₂] at h'

theorem mapL_le_centralizer {Z₁ Z₂ : Subgroup G} (h : Z₁ ≤ Subgroup.centralizer (Z₂ : Set G)) :
    mapL e Z₁ ≤ Subgroup.centralizer (mapL e Z₂ : Set G') := by
  rintro _ ⟨z₁, hz₁, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨z₂, hz₂, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (h hz₁) _ hz₂)

theorem mapL_inf_centralizer {Z : Subgroup G} (hZ : Z ≤ Y) :
    mapL e (Y ⊓ Subgroup.centralizer (Z : Set G)) =
      Y' ⊓ Subgroup.centralizer (mapL e Z : Set G') := by
  apply le_antisymm
  · exact le_inf (mapL_le e _) (mapL_le_centralizer e inf_le_right)
  · rintro x ⟨hxY, hxC⟩
    obtain ⟨y, rfl⟩ : ∃ y : Y, embedOf e y = x :=
      ⟨e.symm ⟨x, hxY⟩, by simp [embedOf]⟩
    refine ⟨y, ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hxC (embedOf e ⟨z, hZ hz⟩) ⟨⟨z, hZ hz⟩, hz, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (embedOf_injective e h1)

theorem mapL_perfectResidual [Finite G] [Finite G'] {X : Subgroup G} (hX : X ≤ Y) :
    mapL e (inSubgroup perfectResidual X) = inSubgroup perfectResidual (mapL e X) := by
  have h1 : inSubgroup perfectResidual X =
      (inSubgroup perfectResidual (X.subgroupOf Y)).map Y.subtype := by
    rw [GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _ Y.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hX]
  have h2 : (inSubgroup perfectResidual X).subgroupOf Y =
      inSubgroup perfectResidual (X.subgroupOf Y) := by
    rw [h1]
    exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  rw [mapL, h2, GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _
    (embedOf_injective e)]
  rfl

theorem linesHyp_mapL [Finite G] [Finite G'] {ℓ₁ ℓ₂ ℓ₃ : Subgroup G}
    (h : LinesHyp Y ℓ₁ ℓ₂ ℓ₃) : LinesHyp Y' (mapL e ℓ₁) (mapL e ℓ₂) (mapL e ℓ₃) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have h3Y : ℓ₃ ≤ Y := h7.trans (sup_le h1 h2)
  refine ⟨mapL_le e _, mapL_le e _, mapL_le_centralizer e h3, by rw [card_mapL e h1, h4],
    by rw [card_mapL e h2, h5], by rw [card_mapL e h3Y, h6], ?_,
    fun h => h8 (mapL_inj e h1 h2 h), fun h => h9 (mapL_inj e h3Y h1 h),
    fun h => h10 (mapL_inj e h3Y h2 h), ?_⟩
  · rw [← mapL_sup e h1 h2]
    exact mapL_mono e h7
  · rw [← mapL_inf_centralizer e h1, ← mapL_perfectResidual e inf_le_left]
    exact mapL_mono e h11

theorem mapL_perfectResidual_inf [Finite G] [Finite G'] {ℓ : Subgroup G} (hℓ : ℓ ≤ Y) :
    mapL e (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ : Set G))) =
      inSubgroup perfectResidual (Y' ⊓ Subgroup.centralizer (mapL e ℓ : Set G')) := by
  rw [mapL_perfectResidual e inf_le_left, mapL_inf_centralizer e hℓ]

noncomputable def perfectResidualEquiv [Finite G] [Finite G'] {ℓ : Subgroup G} (hℓ : ℓ ≤ Y) :
    inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ : Set G)) ≃*
      inSubgroup perfectResidual (Y' ⊓ Subgroup.centralizer (mapL e ℓ : Set G')) :=
  (mapLEquiv e ((Subgroup.map_subtype_le _).trans inf_le_left)).trans
    (MulEquiv.subgroupCongr (mapL_perfectResidual_inf e hℓ))

theorem linesConcl_of_mapL [Finite G] [Finite G'] {ℓ₁ ℓ₃ : Subgroup G} (h₁ : ℓ₁ ≤ Y)
    (h₃ : ℓ₃ ≤ Y) {b : ℕ} (h : LinesConcl Y' (mapL e ℓ₁) (mapL e ℓ₃) b) :
    LinesConcl Y ℓ₁ ℓ₃ b := by
  rcases h with ⟨⟨a⟩, ⟨c⟩⟩ | ⟨⟨a⟩, ⟨c⟩⟩
  · exact Or.inl ⟨⟨(perfectResidualEquiv e h₁).trans a⟩, ⟨(perfectResidualEquiv e h₃).trans c⟩⟩
  · exact Or.inr ⟨⟨(perfectResidualEquiv e h₁).trans a⟩, ⟨(perfectResidualEquiv e h₃).trans c⟩⟩

include e in
theorem linesAt_of_mulEquiv [Finite G] [Finite G'] {b : ℕ} (h : LinesAt Y' b) : LinesAt Y b := by
  intro ℓ₁ ℓ₂ ℓ₃ hl
  have h3Y : ℓ₃ ≤ Y := hl.2.2.2.2.2.2.1.trans (sup_le hl.1 hl.2.1)
  exact linesConcl_of_mapL e hl.1 h3Y (h _ _ _ (linesHyp_mapL e hl))

end Transport

theorem mapL_conj {Y : Subgroup G} (g : Y) {Z : Subgroup G} (hZ : Z ≤ Y) :
    mapL (MulAut.conj g) Z = Z.map (MulAut.conj (g : G)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hZ hz⟩, hz, rfl⟩

theorem perfectResidual_conj [Finite G] {Y : Subgroup G} {w : G} (hw : w ∈ Y) (ℓ : Subgroup G) :
    inSubgroup perfectResidual
        (Y ⊓ Subgroup.centralizer (ℓ.map (MulAut.conj w).toMonoidHom : Set G)) =
      (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer (ℓ : Set G))).map
        (MulAut.conj w).toMonoidHom := by
  rw [GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _
      (MulAut.conj w).injective, Subgroup.map_inf_eq _ _ _ (MulAut.conj w).injective,
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hw), map_centralizer_mulEquiv]
  rfl

theorem card_galoisField_two_mul (b : ℕ) (hb : 0 < b) :
    Nat.card (GaloisField 2 (2 * b)) = (2 ^ b) ^ 2 := by
  rw [GaloisField.card 2 (2 * b) (by omega), ← pow_mul, mul_comm]

theorem nonempty_projSU_mulEquiv_SU (b : ℕ) (hb : 0 < b) :
    Nonempty (projSU 4 2 b ≃* SU (unitaryInvolution (GaloisField 2 (2 * b)) 2 b) 4) := by
  have hF := card_galoisField_two_mul b hb
  have hbot : (StatedScalars (Fin 4) (GaloisField 2 (2 * b))).subgroupOf
      (StatedSU 4 (2 ^ b) (GaloisField 2 (2 * b))) = ⊥ := by
    rw [← Subgroup.card_eq_one, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF
      (by norm_num)).2.2]
    have hodd : Odd (2 ^ b + 1) := (Nat.even_pow.mpr ⟨even_two, hb.ne'⟩).add_one
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
  exact ⟨(MulEquiv.subgroupCongr (Census.projImage_statedSU 4 2 b).symm).trans
    ((Census.statedProjEquivProjImage _).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hbot).trans
        (QuotientGroup.quotientBot.trans (equivStatedSU hF 4).symm)))⟩

theorem u4ThreeTorusLines_of_SU
    (h : ∀ b : ℕ, 0 < b → Even b →
      LinesAt (SU (unitaryInvolution (GaloisField 2 (2 * b)) 2 b) 4) b) :
    U4ThreeTorusLines :=
  u4ThreeTorusLines_of_linesAt fun G _ _ Y b hb hbe ⟨eY⟩ => by
    obtain ⟨e₀⟩ := nonempty_projSU_mulEquiv_SU b hb
    exact linesAt_of_mulEquiv (eY.trans e₀) (h b hb hbe)

end CFSG.RankThree.PartTwo.Sec21.U4Lines
