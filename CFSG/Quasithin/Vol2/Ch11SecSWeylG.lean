module

public import CFSG.Quasithin.Vol2.Ch11SecSWeylE
public import CFSG.Quasithin.Vol2.Ch11SecSWeylF
public import CFSG.Quasithin.Vol2.Ch11SecS12ZC
public import CFSG.Quasithin.Vol2.Ch11SecQ9aG2C
public import CFSG.Quasithin.Vol2.Ch11SecQ9aG2D
public import CFSG.Quasithin.Vol2.Ch11SecQ9aShE
public import CFSG.Quasithin.Vol2.Ch11SecSWeylD

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.SWeyl

open CFSG.Open CFSG.Blueprint C11P9A CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley


theorem part2_g2 {Q : Type} [Group Q] [Finite Q] (hQ : LieModel Q .G2 0 2 2)
    {S : Subgroup Q} (hS : QuasithinUnique.IsSylowTwoOf S ⊤) {B₁ B₂ : Subgroup Q}
    (hne : B₁ ≠ B₂) (h₁ : IsL24Sub S B₁) (h₂ : IsL24Sub S B₂) {E : Subgroup Q}
    (hE : Nat.card ↥E = 9) (hE₁ : E ≤ Subgroup.normalizer (B₁ : Set Q))
    (hE₂ : E ≤ Subgroup.normalizer (B₂ : Set Q)) (E₂ : Subgroup Q)
    (hle : E₂ ≤ E ⊓ sectionCentralizer B₂ (pCoreOf 2 B₂)) (hne₂ : E₂ ≠ ⊥) :
    ¬ Subgroup.normalizer (E₂ : Set Q) ≤ Subgroup.normalizer (B₂ : Set Q) := by
  have hX := chevalleyExceptionalModel_of_lieModel hQ
  have := (CFSG.LieType.Simplicity.fam_g2_simplicity Q 2 2 hX).2
  obtain ⟨K, _, _, _, φ, hK, hφ, hres, -⟩ := even_rank_two_residual_G2 hX hS
  have hK' : Nat.card K = 4 := by rw [hK]; norm_num
  have hB := fun j => dInf_map_ne_bot φ.symm (factG2FourParabNonsolv_holds K hK' j)
  have hN : ∀ X : Subgroup Q, X.Normal → ⁅X, X⁆ = X → X ≠ ⊥ → X = ⊤ := fun X _ _ hX1 =>
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal X).resolve_left hX1
  have hpp := parabPair_of_residual hS hres hB
  obtain ⟨hinf₀, hcard₀⟩ := factG2FourBorelNorm_holds K hK'
  have hS' : S = ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map
      φ.symm.toMonoidHom := by
    rw [← hφ]
    ext x
    simp
  have hinf : ((parabolicSubgroup Tag.G2 K {g2Index 0}).subgroupOf
      (adjointGroup Tag.G2 K)).map φ.symm.toMonoidHom ⊓
      ((parabolicSubgroup Tag.G2 K {g2Index 1}).subgroupOf
        (adjointGroup Tag.G2 K)).map φ.symm.toMonoidHom ≤ Subgroup.normalizer (S : Set Q) := by
    rw [← Subgroup.map_inf_eq _ _ _ φ.symm.injective, hS', ← Subgroup.map_equiv_normalizer_eq]
    refine Subgroup.map_mono (le_trans (le_of_eq ?_) hinf₀)
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hcard : Nat.card ↥(Subgroup.normalizer (S : Set Q)) = Nat.card ↥S * 9 := by
    rw [hS', ← Subgroup.map_equiv_normalizer_eq, Subgroup.card_map_of_injective φ.symm.injective,
      Subgroup.card_map_of_injective φ.symm.injective, hcard₀]
  refine part2_of_residual hS hres hB hN hpp.top_not ?_ hne h₁ h₂ hE hE₁ hE₂ E₂ hle hne₂
  intro j _ E hEM hE9 E₂ hle _
  have hu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK']
  have hcube : ∀ t : Kˣ, t ^ 3 = 1 := fun t => hu ▸ pow_card_eq_one'
  have hTA : torusGroup Tag.G2 K ≤ adjointGroup Tag.G2 K := (Subgroup.closure_le _).2 (by
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact torusElt_mem_adjointGroup i t)
  have hwA : (g2N : ModGL Tag.G2 K) ^ 3 ∈ adjointGroup Tag.G2 K :=
    pow_mem (mul_mem (weylElt_mem_adjointGroup _ _) (weylElt_mem_adjointGroup _ _)) 3
  have hTP : ∀ i : Fin 2, ((torusGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map
      φ.symm.toMonoidHom ≤ ((parabolicSubgroup Tag.G2 K {g2Index i}).subgroupOf
        (adjointGroup Tag.G2 K)).map φ.symm.toMonoidHom := fun i =>
    Subgroup.map_mono fun x hx => torusGroup_le_parabolicSubgroup _ hx
  have hTc : Nat.card ↥(((torusGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map
      φ.symm.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA).toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_G2, hK']
    norm_num
  refine part2_of_inverting (not_dvd_of_borel hS.2.1 hinf hcard) (le_inf (hTP 0) (hTP 1)) hTc
    hEM hE9 ?_ (w := φ.symm ⟨_, hwA⟩) ?_ ?_ E₂ (hle.trans inf_le_left)
  · fin_cases j
    · exact inf_le_left
    · exact inf_le_right
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (g2N_cube_conj_torus hcube hx)
  · rintro ⟨y, hy, hyw⟩
    have hy' : y = ⟨_, hwA⟩ := φ.symm.injective hyw
    rw [hy'] at hy
    exact g2N_cube_not_mem_parabolic (g2Index j) hy

theorem factShapeWeyl_holds : FactShapeWeyl := by
  intro Q _ _ hQ hnot S hS B₁ B₂ hne h₁ h₂ E hE hE₁ hE₂
  obtain ⟨B, hB⟩ := C11P9A.exists_parabPair_shape4 factG2FourParabNonsolv_holds hQ hS
  refine ⟨fun H hB₂H hSH _ => part1 hB hne h₁ h₂ H hB₂H hSH, fun E₂ hle hne₂ => ?_⟩
  rcases hQ with ⟨K, _, _, hK, ⟨e⟩⟩ | hL | hP | hG
  · exact part2_sl3 hK e hS hne h₁ h₂ hE hE₁ hE₂ E₂ hle hne₂
  · rcases hL with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hnot
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
  · rcases hP with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact part2_sp4 h hS hne h₁ h₂ hE hE₁ hE₂ E₂ hle hne₂
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
  · exact part2_g2 hG hS hne h₁ h₂ hE hE₁ hE₂ E₂ hle hne₂

end CFSG.Quasithin.Vol2.Ch11.SecS.SWeyl
