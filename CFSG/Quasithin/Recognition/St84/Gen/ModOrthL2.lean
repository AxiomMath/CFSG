module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
import CFSG.Quasithin.Recognition.St84.Gen.ModOrthL2Rep
import CFSG.Quasithin.Recognition.St84.Gen.TransferL2Inner
import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Small
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.CfgBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InExclusive

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.RankThree.GF2n.Tim81.Sec2 CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped Matrix MatrixGroups commutatorElement

section Natural

variable {F : Type} [Field F]

private theorem modOrthL2_entries_of_mem_range {y : SL(2, F)}
    (hy : y ∈ (upperUnipotent (F := F)).range) :
    (y : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧ (y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (y : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
  have h := (sl2_fixes_first_iff y).mpr hy
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec_single_one] at h
  have h00 : (y : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by simpa using congrFun h 0
  have h10 : (y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simpa using congrFun h 1
  have hdet := y.2
  rw [Matrix.det_fin_two, h00, h10] at hdet
  exact ⟨h00, h10, by simpa using hdet⟩

private theorem modOrthL2_conj_sub_one_mul_eq_zero (x : SL(2, F)) {y z : SL(2, F)}
    (hy : y ∈ (upperUnipotent (F := F)).range) (hz : z ∈ (upperUnipotent (F := F)).range) :
    ((↑(x * y * x⁻¹) : Matrix (Fin 2) (Fin 2) F) - 1) *
      ((↑(x * z * x⁻¹) : Matrix (Fin 2) (Fin 2) F) - 1) = 0 := by
  obtain ⟨hy0, hy1, hy2⟩ := modOrthL2_entries_of_mem_range hy
  obtain ⟨hz0, hz1, hz2⟩ := modOrthL2_entries_of_mem_range hz
  have hU : ((y : Matrix (Fin 2) (Fin 2) F) - 1) * ((z : Matrix (Fin 2) (Fin 2) F) - 1) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, hy0, hy1, hy2, hz0, hz1, hz2]
  have hX : (x : Matrix (Fin 2) (Fin 2) F) * (↑x⁻¹ : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hX' : (↑x⁻¹ : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have e : ∀ w : SL(2, F), (↑(x * w * x⁻¹) : Matrix (Fin 2) (Fin 2) F) - 1 =
      (x : Matrix (Fin 2) (Fin 2) F) * ((w : Matrix (Fin 2) (Fin 2) F) - 1) *
        (↑x⁻¹ : Matrix (Fin 2) (Fin 2) F) := by
    intro w
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, hX]
  rw [e, e]
  calc (x : Matrix (Fin 2) (Fin 2) F) * ((y : Matrix (Fin 2) (Fin 2) F) - 1) *
        (↑x⁻¹ : Matrix (Fin 2) (Fin 2) F) * ((x : Matrix (Fin 2) (Fin 2) F) *
          ((z : Matrix (Fin 2) (Fin 2) F) - 1) * (↑x⁻¹ : Matrix (Fin 2) (Fin 2) F))
      = (x : Matrix (Fin 2) (Fin 2) F) * (((y : Matrix (Fin 2) (Fin 2) F) - 1) *
          ((↑x⁻¹ : Matrix (Fin 2) (Fin 2) F) * x) * ((z : Matrix (Fin 2) (Fin 2) F) - 1)) *
          (↑x⁻¹ : Matrix (Fin 2) (Fin 2) F) := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_one, hU, Matrix.mul_zero, Matrix.zero_mul]

private theorem modOrthL2_natural_quadratic [Finite F] [CharP F 2] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : Representation (ZMod 2) SL(2, F) W} (hρ : IsNaturalModule ρ)
    {P : Subgroup SL(2, F)} (hP : IsPGroup 2 P) {a b : SL(2, F)} (ha : a ∈ P) (hb : b ∈ P)
    (w : W) : ρ a (ρ b w - w) - (ρ b w - w) = 0 := by
  obtain ⟨φ, hφ⟩ := hρ
  obtain ⟨x, hx⟩ := pgroup_sl2_conjugate_unipotent P hP
  have hconj : ∀ g ∈ P, x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range := fun g hg => by
    simpa using hx (Subgroup.mem_map_of_mem _ hg)
  have key := modOrthL2_conj_sub_one_mul_eq_zero x (hconj a ha) (hconj b hb)
  have ea : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
  have eb : x * (x⁻¹ * b * x) * x⁻¹ = b := by group
  rw [ea, eb] at key
  apply φ.injective
  rw [map_zero]
  have e : φ (ρ a (ρ b w - w) - (ρ b w - w)) =
      (((a : Matrix (Fin 2) (Fin 2) F) - 1) * ((b : Matrix (Fin 2) (Fin 2) F) - 1)) *ᵥ φ w := by
    rw [← Matrix.mulVec_mulVec]
    simp only [map_sub, hφ, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
    abel
  rw [e, key, Matrix.zero_mulVec]

end Natural

section Blocks

variable {G : Type} [Group G] {L : Subgroup G}

theorem modOrthL2_blockU_eq
    (hirr : ∀ N : Subgroup G, N ≤ pCoreOf 2 L → L ≤ Subgroup.normalizer (N : Set G) →
      N = ⊥ ∨ N = pCoreOf 2 L)
    (hnt : ¬ L ≤ Subgroup.centralizer (pCoreOf 2 L : Set G)) : blockU L = pCoreOf 2 L := by
  rcases hirr _ (Lin2.blockU_le_pCoreOf L) (Lin2.le_normalizer_blockU L) with h | h
  · exfalso
    apply hnt
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 : ⁅q, l⁆ ∈ blockU L := Subgroup.commutator_mem_commutator hq hl
    rw [h, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  · exact h

theorem modOrthL2_blockZ_eq_bot
    (hirr : ∀ N : Subgroup G, N ≤ pCoreOf 2 L → L ≤ Subgroup.normalizer (N : Set G) →
      N = ⊥ ∨ N = pCoreOf 2 L)
    (hnt : ¬ L ≤ Subgroup.centralizer (pCoreOf 2 L : Set G)) : blockZ L = ⊥ := by
  have hN : L ≤ Subgroup.normalizer
      ((pCoreOf 2 L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff.mp inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  rcases hirr _ inf_le_left hN with h | h
  · rw [eq_bot_iff, ← h]
    exact inf_le_inf_right _ (Lin2.blockU_le_pCoreOf L)
  · exact absurd (Subgroup.le_centralizer_iff.mp (inf_eq_left.mp h)) hnt

end Blocks

private theorem modOrthL2_isOmega4MinusType_of_orth {G : Type} [Group G] {L : Subgroup G}
    {f : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2] (hF : Fintype.card F = 2 ^ (2 * f))
    {α₀ : ↥L →* SL(2, F)} (hα₀ : Function.Surjective α₀)
    (hker₀ : α₀.ker = (pCoreOf 2 L).subgroupOf L) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : Representation (ZMod 2) SL(2, F) W}
    {cls : ↥(pCoreOf 2 L) →* Multiplicative W} (hcls : Function.Bijective cls)
    (hact : ∀ (ℓ : ↥L) (u v : ↥(pCoreOf 2 L)), (v : G) = ℓ * u * ℓ⁻¹ →
      ρ (α₀ ℓ) (Multiplicative.toAdd (cls u)) = Multiplicative.toAdd (cls v))
    (hU : blockU L = pCoreOf 2 L) (hZ : blockZ L = ⊥) {j : ℕ}
    {β : W ≃+ ↥(JonesParshall.hermA f F)}
    (hβ : ∀ g w, β (ρ g w) =
      JonesParshall.hermAct f (JonesParshall.sig_sig hF) (fieldAut F j g) (β w)) :
    IsOmega4MinusType L f := by
  let incl : ↥(blockU L) →* ↥(pCoreOf 2 L) := Subgroup.inclusion hU.le
  let βA : W →+ Matrix (Fin 2) (Fin 2) F :=
    (JonesParshall.hermA f F).subtype.comp β.toAddMonoidHom
  let βm : ↥(blockU L) →* Multiplicative (Matrix (Fin 2) (Fin 2) F) :=
    (AddMonoidHom.toMultiplicative βA).comp (cls.comp incl)
  have hβm : ∀ u, Multiplicative.toAdd (βm u) =
      ((β (Multiplicative.toAdd (cls (incl u))) : ↥(JonesParshall.hermA f F)) :
        Matrix (Fin 2) (Fin 2) F) := fun _ => rfl
  have hinj : Function.Injective βm := by
    intro a b hab
    have h1 := congrArg Multiplicative.toAdd hab
    rw [hβm, hβm] at h1
    exact Subgroup.inclusion_injective hU.le
      (hcls.1 (Multiplicative.toAdd.injective (β.injective (Subtype.ext h1))))
  refine ⟨F, inferInstance, inferInstance, hF, (fieldAut F j).comp α₀,
    (B45L2.fieldAut_bijective j).2.comp hα₀, ?_, βm, ?_, ?_, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ (B45L2.fieldAut_bijective j).1, hker₀,
      CFSG.openPCoreOf_subgroupOf]
  · intro X
    constructor
    · rintro ⟨u, rfl⟩
      rw [hβm]
      have h := JonesParshall.mem_hermA.mp (β (Multiplicative.toAdd (cls (incl u)))).2
      conv_rhs => rw [← h]
      exact (Matrix.transpose_transpose _).symm
    · intro hX
      have hmem : X ∈ JonesParshall.hermA f F := JonesParshall.mem_hermA.mpr (by
        change (X.map (· ^ 2 ^ f))ᵀ = X
        rw [hX, Matrix.transpose_transpose])
      obtain ⟨q, hq⟩ := hcls.2 (Multiplicative.ofAdd (β.symm ⟨X, hmem⟩))
      refine ⟨⟨q, hU.ge q.2⟩, ?_⟩
      rw [hβm]
      have hq' : cls (incl ⟨q, hU.ge q.2⟩) = Multiplicative.ofAdd (β.symm ⟨X, hmem⟩) := hq
      rw [hq', toAdd_ofAdd, AddEquiv.apply_symm_apply]
  · rw [(MonoidHom.ker_eq_bot_iff βm).mpr hinj, hZ, Subgroup.bot_subgroupOf]
  · intro ℓ u v huv
    rw [hβm, hβm, ← hact ℓ (incl u) (incl v) huv, hβ]
    rfl

private theorem modOrthL2_commutator_commutator_eq_one {G : Type} [Group G]
    {L Q T : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2] {α : ↥L →* SL(2, F)}
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {ρ : Representation (ZMod 2) SL(2, F) W}
    {cls : ↥Q →* Multiplicative W} (hcls : Function.Injective cls)
    (hact : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      ρ (α ℓ) (Multiplicative.toAdd (cls u)) = Multiplicative.toAdd (cls v))
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hnat : IsNaturalModule ρ) (hTL : T ≤ L)
    (hT : IsPGroup 2 T) {t t' u : G} (ht : t ∈ T) (ht' : t' ∈ T) (hu : u ∈ Q) :
    ⁅t, ⁅t', u⁆⁆ = 1 := by
  have hcommQ : ∀ ℓ ∈ L, ∀ x ∈ Q, ⁅ℓ, x⁆ ∈ Q := fun ℓ hℓ x hx => by
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLQ hℓ) x).mp hx) (Q.inv_mem hx)
  have hm1 := hcommQ t' (hTL ht') u hu
  have hm2 := hcommQ t (hTL ht) _ hm1
  have e1 := modOrthL2_toAdd_cls_commutator hact (hTL ht') hu hm1
  have e2 := modOrthL2_toAdd_cls_commutator hact (hTL ht) hm1 hm2
  rw [e1] at e2
  have hP : IsPGroup 2 ((T.subgroupOf L).map α) :=
    (hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm).map α
  have hz := modOrthL2_natural_quadratic hnat hP
    (Subgroup.mem_map_of_mem α (show (⟨t, hTL ht⟩ : ↥L) ∈ T.subgroupOf L from ht))
    (Subgroup.mem_map_of_mem α (show (⟨t', hTL ht'⟩ : ↥L) ∈ T.subgroupOf L from ht'))
    (Multiplicative.toAdd (cls ⟨u, hu⟩))
  have h0 : cls ⟨⁅t, ⁅t', u⁆⁆, hm2⟩ = cls 1 := by
    rw [map_one]
    exact Multiplicative.toAdd.injective (e2.trans hz)
  exact congrArg Subtype.val (hcls h0)

theorem isOmega4MinusType_of_irreducible_of_not_quadratic {G : Type} [Group G]
    {L : Subgroup G} [Finite ↥L] {f : ℕ} (hf : 1 ≤ f) (hq : IsL2Quot (2 * f) (oTwoQuot ↥L))
    (hQ : IsElemAbelian 2 (pCoreOf 2 L)) (hcard : Nat.card (pCoreOf 2 L) = 2 ^ (4 * f))
    (hirr : ∀ N : Subgroup G, N ≤ pCoreOf 2 L → L ≤ Subgroup.normalizer (N : Set G) →
      N = ⊥ ∨ N = pCoreOf 2 L)
    (hnt : ¬ L ≤ Subgroup.centralizer (pCoreOf 2 L : Set G))
    {T : Subgroup G} (hT : IsSylowTwoOf T L)
    (hnq : ∃ t ∈ T, ∃ t' ∈ T, ∃ u ∈ pCoreOf 2 L, ⁅t, ⁅t', u⁆⁆ ≠ 1) :
    CFSG.Quasithin.IsOmega4MinusType L f := by
  classical
  obtain ⟨α₀, hα₀, hker₀⟩ := exists_surjective_SL2_of_isL2Quot hq
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hkerQ : ∀ ℓ : ↥L, α₀ ℓ = 1 → (ℓ : G) ∈ pCoreOf 2 L := fun ℓ h => by
    have hℓ : ℓ ∈ α₀.ker := h
    rw [hker₀] at hℓ
    exact hℓ
  obtain ⟨W, _, _, ρ, cls, hcls, hact⟩ := exists_modOrthL2_conjRep hQ hLQ α₀ hα₀ hkerQ
  haveI : Finite ↥(pCoreOf 2 L) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (CFSG.LieType.BorelTits.pCoreOf_le 2 L))
  haveI : Finite W := Finite.of_surjective (fun u => Multiplicative.toAdd (cls u)) fun w => by
    obtain ⟨u, hu⟩ := hcls.2 (Multiplicative.ofAdd w)
    exact ⟨u, by simp only [hu, toAdd_ofAdd]⟩
  have hWcard : Nat.card W = 2 ^ (4 * f) := by
    rw [← hcard]
    exact (Nat.card_congr ((Equiv.ofBijective cls hcls).trans Multiplicative.toAdd)).symm
  haveI : Nontrivial W := by
    rw [← Finite.one_lt_card_iff_nontrivial, hWcard]
    exact Nat.one_lt_two_pow (by omega)
  haveI : Fact ρ.IsIrreducible := ⟨modOrthL2_isIrreducible hcls.2 hact hLQ hirr⟩
  have hntρ : ∃ g, ρ g ≠ 1 := modOrthL2_exists_ne_one hcls.1 hact hLQ hnt
  letI : Fintype (GaloisField 2 (2 * f)) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 (2 * f)) = 2 ^ (2 * f) := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 (2 * f) (by omega)
  have hA2 : ∀ a ∈ (upperUnipotent (F := GaloisField 2 (2 * f))).range, a * a = 1 := by
    rintro _ ⟨c, rfl⟩
    rw [← map_mul]
    have hc : c * c = 1 := Multiplicative.toAdd.injective (by
      rw [toAdd_mul, toAdd_one]
      exact CharTwo.add_self_eq_zero _)
    rw [hc, map_one]
  have hAc : Nat.card (upperUnipotent (F := GaloisField 2 (2 * f))).range = 2 ^ (2 * f) := by
    rw [upperUnipotent_card, ← Fintype.card_eq_nat_card, hF]
  have hlt : Nat.card W < 2 ^ (4 * (2 * f)) := by
    rw [hWcard]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases isNaturalModule_or_isOrthModule_or_of_card_lt (by omega) hF ρ hntρ _ hA2 hAc hlt with
    hnat | ⟨l, hl, hnl, horth⟩ | ⟨l, hnl, hWl, -⟩
  · exfalso
    obtain ⟨t, ht, t', ht', u, hu, hne⟩ := hnq
    exact hne (modOrthL2_commutator_commutator_eq_one hcls.1 hact hLQ hnat hT.1 hT.2.1 ht ht' hu)
  · obtain rfl : f = l := by omega
    obtain ⟨j, β, hβ⟩ := horth
    exact modOrthL2_isOmega4MinusType_of_orth hl hα₀ hker₀ hcls hact
      (modOrthL2_blockU_eq hirr hnt) (modOrthL2_blockZ_eq_bot hirr hnt) hβ
  · exfalso
    rw [hWcard] at hWl
    have h48 : 4 * f = 8 * l := Nat.pow_right_injective (le_refl 2) hWl
    omega

end CFSG.Quasithin.F112R.St84

end
