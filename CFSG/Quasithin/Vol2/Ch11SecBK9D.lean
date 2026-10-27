module

public import CFSG.Quasithin.Vol2.Ch11SecBK9C
public import CFSG.Quasithin.Vol2.Ch11SecBK4B
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 Matrix
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe statedSL_eq_range_toGL)
open scoped IsMulCommutative

namespace K9

section Gen

variable {G : Type} [Group G] {L V : Subgroup G} [IsMulCommutative ↥V] {ι : Type} [Fintype ι]
  {K : Type} [Field K] [CharP K 2] {D : FFModel} {LM : KGNat.LinModel D K (ι → K)}
  {f : ↥V → (ι → K)}

theorem conj_hypOf {H : Subgroup (MulAut ↥V)} {Z : Subgroup ↥V} {π : D.Gam →* ↥H}
    (hf : KGNat.IsCoord LM H Z π f) {γ : D.Gam} {l : G}
    (hlV : l ∈ Subgroup.normalizer (V : Set G))
    (hlγ : ((π γ : ↥H) : MulAut ↥V) = SecA.conjV V l hlV) {a a' : ι → K}
    (haa : ∀ x, a ⬝ᵥ LM.lin γ x = a' ⬝ᵥ x) :
    conjSubgroup (hypOf hf.map_mul a) l = hypOf hf.map_mul a' := by
  ext g
  rw [mem_conjSubgroup_iff, mem_hypOf, mem_hypOf]
  by_cases hg : g ∈ V
  · have hlg : l * g * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hlV g).mp hg
    have hval : (⟨l * g * l⁻¹, hlg⟩ : ↥V) = ((π γ : ↥H) : MulAut ↥V) ⟨g, hg⟩ := by
      apply Subtype.ext
      rw [hlγ, SecA.conjV_apply_coe]
    have key : tr (a ⬝ᵥ f ⟨l * g * l⁻¹, hlg⟩) = tr (a' ⬝ᵥ f ⟨g, hg⟩) := by
      rw [hval, hf.act, haa]
    exact ⟨fun ⟨_, h⟩ => ⟨hg, key ▸ h⟩, fun ⟨_, h⟩ => ⟨hlg, key.symm ▸ h⟩⟩
  · have hlg : l * g * l⁻¹ ∉ V := fun h => hg ((Subgroup.mem_normalizer_iff.mp hlV g).mpr h)
    exact ⟨fun ⟨h, _⟩ => absurd h hlg, fun ⟨h, _⟩ => absurd h hg⟩

theorem hyperplaneT_of_coord [Finite G] [DecidableEq ι] [Nonempty ι] [Finite K]
    (hK : Nat.card K = 4) {T : Subgroup G} (hV2 : IsPGroup 2 ↥V)
    {π : D.Gam →* ↥(autOn L V)}
    (hf : KGNat.IsCoord LM (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    (hC : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (htrans : ∀ a a' : ι → K, a ≠ 0 → a' ≠ 0 → ∃ γ : D.Gam, ∀ x, a ⬝ᵥ LM.lin γ x = a' ⬝ᵥ x)
    (hT2 : IsPGroup 2 ↥T) (hTV : T ≤ Subgroup.normalizer (V : Set G)) {U : Subgroup G}
    (hUV : U ≤ V) (hU : E3.mQuot V U = 1) :
    ∃ g ∈ L, T ≤ Subgroup.normalizer (conjSubgroup U g : Set G) := by
  have hinj : Function.Injective f := fun u u' h => by
    have h1 := (hf.eq_iff u u').mp h
    have h2 : ((u * u'⁻¹ : ↥V) : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨(u * u'⁻¹).2, h1⟩
    rw [hC, Subgroup.mem_bot] at h2
    exact mul_inv_eq_one.mp (Subtype.ext h2)
  have hUs : U ∈ hypSet V := ⟨hUV, by rw [E3.relIndex_eq_two_pow hV2, hU, pow_one]⟩
  obtain ⟨U₀, hU₀, hTU₀⟩ := exists_fixed_hyp hT2 hTV
    (not_two_dvd_card_hypSet hf.map_mul hK hinj hf.surj)
  obtain ⟨a, ha, rfl⟩ := exists_param hf.map_mul hK hinj hf.surj hUs
  obtain ⟨a₀, ha₀, rfl⟩ := exists_param hf.map_mul hK hinj hf.surj hU₀
  obtain ⟨γ, hγ⟩ := htrans a a₀ ha ha₀
  obtain ⟨l, hl, hlV, hlγ⟩ := SecA.mem_autOn_iff.mp (π γ).2
  exact ⟨l, hl, by rw [conj_hypOf hf hlV hlγ hγ]; exact hTU₀⟩

end Gen

section Dual

variable {K : Type} [Field K]

theorem sl3_dual_trans (a a' : Fin 3 → K) (ha : a ≠ 0) (ha' : a' ≠ 0) :
    ∃ γ : ↥(StatedSL 3 K), ∀ x, a ⬝ᵥ (KGNat.linModelNat (StatedSL 3 K)).lin γ x = a' ⬝ᵥ x := by
  obtain ⟨δ, hδ⟩ := KGNat.exists_sl3_lin_eq a a' ha ha'
  rw [KGNat.linModelNat_lin] at hδ
  have hmem : (δ : GL (Fin 3) K) ∈ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K).range := by
    rw [← statedSL_eq_range_toGL]
    exact δ.2
  obtain ⟨A, hA⟩ := hmem
  have hAδ : (A : Matrix (Fin 3) (Fin 3) K) =
      ((δ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← hA]
    rfl
  refine ⟨specialLinearGroupEquivStatedSL 3 K A.transpose, fun x => ?_⟩
  rw [KGNat.linModelNat_lin, specialLinearGroupEquivStatedSL_coe,
    Matrix.SpecialLinearGroup.coe_transpose, hAδ, dotProduct_mulVec, vecMul_transpose, hδ]

theorem dotProduct_eq_spB (a y : Fin 2 ⊕ Fin 2 → K) :
    a ⬝ᵥ y = Matrix.toBilin' (KGNat.spJ K) (KGNat.spJ K *ᵥ a) y := by
  rw [KGNat.toBilin'_spJ_apply, KGNat.spJ_mulVec, dotProduct, Fintype.sum_sum_type,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

theorem spJ_mulVec_ne_zero {a : Fin 2 ⊕ Fin 2 → K} (ha : a ≠ 0) : KGNat.spJ K *ᵥ a ≠ 0 := by
  intro h
  apply ha
  funext k
  have h' := congrFun h
  rw [KGNat.spJ_mulVec] at h'
  rcases k with i | i
  · simpa using h' (.inr i)
  · simpa using h' (.inl i)

theorem sp4_dual_trans (a a' : Fin 2 ⊕ Fin 2 → K) (ha : a ≠ 0) (ha' : a' ≠ 0) :
    ∃ γ : ↥(StatedSp 2 K), ∀ x, a ⬝ᵥ (KGNat.linModelNat (StatedSp 2 K)).lin γ x = a' ⬝ᵥ x := by
  obtain ⟨γ, hγ⟩ := KGNat.exists_sp4_lin_eq _ _ (spJ_mulVec_ne_zero ha') (spJ_mulVec_ne_zero ha)
  rw [KGNat.linModelNat_lin] at hγ
  refine ⟨γ, fun x => ?_⟩
  rw [KGNat.linModelNat_lin, dotProduct_eq_spB, dotProduct_eq_spB a', ← hγ]
  exact KGNat.spB_mat γ _ _

end Dual

end K9

theorem factHyperplaneT_holds : FactHyperplaneT := by
  intro G _ _ L V T hV hLV hVL hnat hG2 hC hT hTV _ U hUV hU
  obtain ⟨_, hnat⟩ := hnat
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV.2 w w.2)
  have hV2 : IsPGroup 2 ↥V := fun w => ⟨1, by rw [pow_one]; exact hsq w⟩
  rcases hnat with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
  · have : CharP K 2 := KGNat.charP_two_of_card (by norm_num) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
    exact K9.hyperplaneT_of_coord (by rw [hK]; norm_num) hV2 hf hC K9.sl3_dual_trans hT.2.1
      hTV hUV hU
  · have : CharP K 2 := KGNat.charP_two_of_card (by norm_num) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
    exact K9.hyperplaneT_of_coord (by rw [hK]; norm_num) hV2 hf hC K9.sp4_dual_trans hT.2.1
      hTV hUV hU
  · exfalso
    have : CharP K 2 := KGNat.charP_two_of_card (by norm_num) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (G2Q8.lmG K) hπ
    exact hG2 (BK4.kindG2_of_isCoord (by norm_num) hK hf)

end CFSG.Quasithin.Vol2.Ch11.SecB
