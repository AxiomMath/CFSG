module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallNatural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRankOne
public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2Fac
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.MBound
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJModel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaMinusLine
import CFSG.LocalAnalysis.UniquenessCase.UC22K147Excl
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.FixedCount
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Quasithin.Background.SmithB45L2Main
import CFSG.Quasithin.Background.E3MParamAttained
import CFSG.Quasithin.Background.RonanE42Small
import CFSG.Quasithin.Vol2.Ch11SecOE2D

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Lift
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.RankThree.FFModules
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

variable {I : Type} [CommGroup I] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem trichotomy_of_involution {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
    (hn : 3 ≤ n) (hF : Fintype.card F = 2 ^ n) [Finite I] (hI : ∀ w : I, w ^ 2 = 1) [Finite W]
    (θ : I ≃* Multiplicative W) {X L : Subgroup (MulAut I)} (hLX : L ≤ X)
    (hLn : (L.subgroupOf X).Normal) (hirr : IsIrrOn L ⊤ ⊥) (φ : ↥L ≃* SL(2, F)) (t : ↥X)
    (ht : orderOf t = 2) :
    Module.finrank (ZMod 2) W ≤
        2 * Module.finrank (ZMod 2) (W ⧸ fixSub (subRep θ X) (zpowers t)) ∨
      (∃ s, n = 2 * s ∧ Module.finrank (ZMod 2) (W ⧸ fixSub (subRep θ X) (zpowers t)) = s ∧
        Module.finrank (ZMod 2) W = 4 * s ∧ ∃ hs : Fintype.card F = 2 ^ (2 * s),
          CFSG.RankThree.GF2n.Tim81.Sec2.IsOrthModule hs (B45L2.repOf θ φ)) ∨
      (∃ s, n = 2 * s ∧
        3 * s ≤ Module.finrank (ZMod 2) (W ⧸ fixSub (subRep θ X) (zpowers t))) := by
  classical
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hXN : X ≤ normalizer (L : Set (MulAut I)) :=
    (normal_subgroupOf_iff_le_normalizer hLX).mp hLn
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have ha2 : subRep θ X t * subRep θ X t = 1 := by rw [← map_mul, ht2, map_one]
  have hconj : ∀ l : ↥L, (t : MulAut I) * (l : MulAut I) * (t : MulAut I)⁻¹ ∈ L := fun l =>
    (Subgroup.mem_normalizer_iff.mp (hXN t.2) l).mp l.2
  have hτ : ∀ g, subRep θ X t * B45L2.repOf θ φ g =
      B45L2.repOf θ φ (φ ⟨_, hconj (φ.symm g)⟩) * subRep θ X t := by
    intro g
    apply LinearMap.ext
    intro w
    rw [Module.End.mul_apply, Module.End.mul_apply, B45L2.repOf_theta, B45L2.repOf_apply,
      subRep_apply, subRep_apply]
    have key : binPsi θ ((t : MulAut I) * ((φ.symm g : ↥L) : MulAut I) * (t : MulAut I)⁻¹) *
        binPsi θ (t : MulAut I) =
          binPsi θ (t : MulAut I) * binPsi θ ((φ.symm g : ↥L) : MulAut I) := by
      rw [← map_mul, ← map_mul, inv_mul_cancel_right]
    have := congrArg (fun f : W ≃ₗ[ZMod 2] W => f w) key
    simpa only [LinearEquiv.mul_apply] using this.symm
  have hτ1 : ∃ g, φ ⟨_, hconj (φ.symm g)⟩ ≠ g := by
    by_contra hne
    push Not at hne
    have ht1 : (t : MulAut I) = 1 := by
      refine eq_one_of_commute_of_isIrrOn hI hirr (by rw [pow_two]; exact congrArg Subtype.val ht2)
        fun l hl => ?_
      have h1 := hne (φ ⟨l, hl⟩)
      have h3 : (t : MulAut I) * l * (t : MulAut I)⁻¹ = l := by
        simpa using congrArg Subtype.val (φ.injective h1)
      calc (t : MulAut I) * l = (t : MulAut I) * l * (t : MulAut I)⁻¹ * t :=
            (inv_mul_cancel_right _ _).symm
        _ = l * t := by rw [h3]
    have : t = 1 := Subtype.ext ht1
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hmain := UC22.K147L2Fac.finrank_le_or_orth_or hn hF (B45L2.repOf θ φ)
    (B45L2.repOf_injective θ φ) (B45L2.repOf_isIrreducible θ φ (isIrrSec_of_isIrrOn_top hirr))
    (subRep θ X t) ha2 (fun g => φ ⟨_, hconj (φ.symm g)⟩) hτ hτ1
  have hd : Module.finrank (ZMod 2) W -
      Module.finrank (ZMod 2) (LinearMap.ker (subRep θ X t - 1)) =
      Module.finrank (ZMod 2) (W ⧸ fixSub (subRep θ X) (zpowers t)) := by
    rw [UC22.Excl147.fixSub_zpowers_eq_ker (subRep θ X) ht]
    have := Submodule.finrank_quotient_add_finrank (LinearMap.ker (subRep θ X t - 1))
    omega
  rw [hd] at hmain
  exact hmain

theorem le_of_isElemAbelian2_of_not_even {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (hodd : ¬ Even n) [Finite W]
    (θ : I ≃* Multiplicative W) {L : Subgroup (MulAut I)} (hirr : IsIrrOn L ⊤ ⊥)
    (φ : ↥L ≃* SL(2, F)) {A : Subgroup (MulAut I)}
    (hAN : A ≤ normalizer (L : Set (MulAut I))) (hA : IsElemAbelian2 A) : A ≤ L := by
  classical
  set A₀ := A.map (binPsi θ).toMonoidHom with hA₀
  have : CFSG.IsElementaryAbelian 2 ↥A₀ := (Actor.isElemAbelian2_iff_map θ A).1 hA
  have : CFSG.IsElementaryAbelian 2 ↥(toUnits A₀) :=
    isElementaryAbelian_of_equiv (toUnitsEquiv A₀) inferInstance
  have hAN' : toUnits A₀ ≤ Subgroup.normalizer
      ((B45L2.repOf θ φ).toHomUnits.range : Set (Module.End (ZMod 2) W)ˣ) := by
    rw [B45L2.repOf_range]
    apply toUnits_normalizer
    rw [hA₀, ← Subgroup.map_equiv_normalizer_eq L (binPsi θ)]
    exact Subgroup.map_mono hAN
  have hρU : Function.Injective (B45L2.repOf θ φ).toHomUnits := fun g h e =>
    B45L2.repOf_injective θ φ (by simpa using congrArg Units.val e)
  by_contra hAL
  have hAL' : ¬ toUnits A₀ ≤ (B45L2.repOf θ φ).toHomUnits.range := by
    intro h
    apply hAL
    intro a ha
    have hmem : (unitsEquiv (ZMod 2) W).symm (binPsi θ a) ∈ toUnits A₀ := by
      rw [mem_toUnits, MulEquiv.apply_symm_apply]
      exact ⟨a, ha, rfl⟩
    have h2 := h hmem
    rw [B45L2.repOf_range, mem_toUnits, MulEquiv.apply_symm_apply] at h2
    obtain ⟨l, hl, hla⟩ := h2
    have hla' : l = a := (binPsi θ).injective hla
    exact hla' ▸ hl
  obtain ⟨s, -, hns, -⟩ := outer_data hn hF (B45L2.repOf θ φ)
    (B45L2.repOf_isIrreducible θ φ (isIrrSec_of_isIrrOn_top hirr)) hρU (toUnits A₀) hAN' hAL'
  exact hodd ⟨s, by omega⟩

theorem card_fixV_le_pow_relIndex [Finite I] (hI : ∀ w : I, w ^ 2 = 1)
    {A : Subgroup (MulAut I)} (hA : IsElemAbelian2 A) {B : Subgroup (MulAut I)} (hBA : B ≤ A) :
    Nat.card (fixV B) ≤ Nat.card (fixV A) ^ B.relIndex A := by
  classical
  suffices H : ∀ k, ∀ B : Subgroup (MulAut I), B ≤ A → B.relIndex A = k →
      Nat.card (fixV B) ≤ Nat.card (fixV A) ^ B.relIndex A from H _ B hBA rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro B hBA h
  by_cases hAB : A ≤ B
  · obtain rfl : B = A := le_antisymm hBA hAB
    simp only [Subgroup.relIndex_self, pow_one, le_refl]
  · obtain ⟨a, haA, haB⟩ := SetLike.not_le_iff_exists.mp hAB
    set B' := B ⊔ Subgroup.zpowers a with hB'
    have hBB' : B ≤ B' := le_sup_left
    have hB'A : B' ≤ A := sup_le hBA (Subgroup.zpowers_le.mpr haA)
    have haB' : a ∈ B' := (le_sup_right : Subgroup.zpowers a ≤ B') (Subgroup.mem_zpowers a)
    have h1 : B.relIndex B' * B'.relIndex A = B.relIndex A :=
      Subgroup.relIndex_mul_relIndex _ _ _ hBB' hB'A
    have h2 : 2 ≤ B.relIndex B' := by
      have : B.IsFiniteRelIndex B' := Subgroup.isFiniteRelIndex_of_finiteIndex
      have hne : B.relIndex B' ≠ 0 := Subgroup.relIndex_ne_zero
      have hne1 : B.relIndex B' ≠ 1 := fun h1 => haB (Subgroup.relIndex_eq_one.mp h1 haB')
      omega
    have hpos : 0 < B'.relIndex A := by
      have : B'.IsFiniteRelIndex A := Subgroup.isFiniteRelIndex_of_finiteIndex
      exact Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
    have hlt : B'.relIndex A < k := by
      rw [← h, ← h1]
      nlinarith
    have ih' := ih _ hlt B' hB'A rfl
    have hcomm : ∀ b ∈ B, a * b = b * a := fun b hb => hA.1 a haA b (hBA hb)
    have ha2 : a * a = 1 := by rw [← pow_two]; exact hA.2 a haA
    let β : ↥(fixV B) →* ↥(fixV B) :=
      { toFun := fun v => ⟨a v, fun b hb => by
          calc b (a v) = (b * a) v := rfl
            _ = (a * b) v := by rw [hcomm b hb]
            _ = a (b v) := rfl
            _ = a v := by rw [v.2 b hb]⟩
        map_one' := Subtype.ext (map_one a)
        map_mul' := fun v w => Subtype.ext (map_mul a (v : I) (w : I)) }
    have hβ : ∀ v, β (β v) = v := fun v => Subtype.ext (by
      show a (a (v : I)) = v
      calc a (a (v : I)) = (a * a) v := rfl
        _ = v := by rw [ha2]; rfl)
    have hfix : Nat.card {v : ↥(fixV B) // β v = v} = Nat.card (fixV B') := by
      refine Nat.card_congr
        { toFun := fun v => ⟨v.1.1, ?_⟩
          invFun := fun w => ⟨⟨w.1, fun b hb => w.2 b (hBB' hb)⟩, Subtype.ext (w.2 a haB')⟩
          left_inv := fun v => rfl
          right_inv := fun w => rfl }
      have hle : B' ≤ MulAction.stabilizer (MulAut I) (v.1 : I) := by
        refine sup_le (fun b hb => MulAction.mem_stabilizer_iff.mpr ?_)
          (Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr ?_))
        · rw [MulAut.smul_def]
          exact v.1.2 b hb
        · rw [MulAut.smul_def]
          exact congrArg Subtype.val v.2
      intro x hx
      have := MulAction.mem_stabilizer_iff.mp (hle hx)
      rwa [MulAut.smul_def] at this
    have hstep : Nat.card (fixV B) ≤ Nat.card (fixV B') ^ 2 := by
      rw [← hfix]
      exact CFSG.EvenSporadicStandard.HNRecog.Section3.tableIII_card_le_sq_fixed
        (fun v => Subtype.ext (by simpa using hI v.1)) β hβ
    have hC : 0 < Nat.card (fixV A) := Nat.card_pos
    calc Nat.card (fixV B) ≤ Nat.card (fixV B') ^ 2 := hstep
      _ ≤ (Nat.card (fixV A) ^ B'.relIndex A) ^ 2 := Nat.pow_le_pow_left ih' 2
      _ = Nat.card (fixV A) ^ (2 * B'.relIndex A) := by rw [← pow_mul, mul_comm]
      _ ≤ Nat.card (fixV A) ^ (B.relIndex B' * B'.relIndex A) :=
          Nat.pow_le_pow_right hC (Nat.mul_le_mul_right _ h2)
      _ = Nat.card (fixV A) ^ B.relIndex A := by rw [h1]

theorem natCard_fixedSub_repOf {F : Type} [Field F] (θ : I ≃* Multiplicative W)
    {L : Subgroup (MulAut I)} (φ : ↥L ≃* SL(2, F)) (S : Subgroup SL(2, F)) :
    Nat.card (CFSG.QuasithinUnique.Setup.X7.fixedSub (B45L2.repOf θ φ) S) =
      Nat.card (fixV ((S.map φ.symm.toMonoidHom).map L.subtype)) := by
  refine (Nat.card_congr ?_).symm
  refine
    { toFun := fun v => ⟨Multiplicative.toAdd (θ v), fun g hg => ?_⟩
      invFun := fun w => ⟨θ.symm (Multiplicative.ofAdd w.1), fun x hx => ?_⟩
      left_inv := fun v => by
        apply Subtype.ext
        simp
      right_inv := fun w => by
        apply Subtype.ext
        simp }
  · rw [B45L2.repOf_apply, B42L2.toAdd_binPsi,
      v.2 ((φ.symm g : ↥L) : MulAut I) ⟨φ.symm g, ⟨g, hg, rfl⟩, rfl⟩]
  · obtain ⟨_, ⟨g, hg, rfl⟩, rfl⟩ := hx
    have h := w.2 g hg
    rw [B45L2.repOf_apply, binPsi_apply] at h
    apply θ.injective
    apply Multiplicative.toAdd.injective
    simpa using h

theorem not_mem_aSet_two_of_l2Eight {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ 3) [Finite I] (hI : ∀ w : I, w ^ 2 = 1) [Finite W]
    (θ : I ≃* Multiplicative W) {X L : Subgroup (MulAut I)} (hLX : L ≤ X)
    (hLn : (L.subgroupOf X).Normal) (hirr : IsIrrOn L ⊤ ⊥) (φ : ↥L ≃* SL(2, F))
    (hI8 : Nat.card I = 2 ^ 8)
    (hfix : ∀ S : Subgroup SL(2, F), (∀ a ∈ S, a * a = 1) → Nat.card S = 2 ^ 3 →
      Nat.card (CFSG.QuasithinUnique.Setup.X7.fixedSub (B45L2.repOf θ φ) S) = 2)
    (A : Subgroup (MulAut I)) : A ∉ E3.aSet 2 X := by
  classical
  rintro ⟨hAX, hA1, hA, hAfix⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXN : X ≤ normalizer (L : Set (MulAut I)) :=
    (normal_subgroupOf_iff_le_normalizer hLX).mp hLn
  have hFn : Nat.card F = 2 ^ 3 := by rw [Nat.card_eq_fintype_card, hF]
  have hAL : A ≤ L := le_of_isElemAbelian2_of_not_even (n := 3) (by norm_num) hFn (by decide) θ
    hirr φ (hAX.trans hXN) hA
  set A₁ : Subgroup SL(2, F) := (A.subgroupOf L).map φ.toMonoidHom with hA₁
  have hA₁2 : ∀ g ∈ A₁, g * g = 1 := by
    rintro _ ⟨l, hl, rfl⟩
    have hl2 : l * l = 1 := by
      apply Subtype.ext
      have := hA.2 _ hl
      rwa [pow_two] at this
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, hl2, map_one]
  obtain ⟨x, hx⟩ := exists_conj_le_rootGroup A₁ hA₁2
  set S₁ : Subgroup SL(2, F) := (UC22.K147L2Fac.rootSub F).map (MulAut.conj x).toMonoidHom
    with hS₁
  have hRcomm : ∀ u ∈ UC22.K147L2Fac.rootSub F, ∀ v ∈ UC22.K147L2Fac.rootSub F,
      u * v = v * u := by
    rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hS₁2 : ∀ g ∈ S₁, g * g = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ by group,
      UC22.K147L2Fac.mul_self_of_mem_rootSub hu, mul_one, mul_inv_cancel]
  have hS₁comm : ∀ g ∈ S₁, ∀ h ∈ S₁, g * h = h * g := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show x * u * x⁻¹ * (x * v * x⁻¹) = x * (u * v) * x⁻¹ by group, hRcomm u hu v hv]
    group
  have hS₁card : Nat.card S₁ = 2 ^ 3 := by
    rw [hS₁, Subgroup.card_map_of_injective (MulAut.conj x).injective,
      UC22.K147L2Fac.natCard_rootSub, hF]
  set U : Subgroup (MulAut I) := (S₁.map φ.symm.toMonoidHom).map L.subtype with hU
  have hUfix : Nat.card (fixV U) = 2 :=
    (natCard_fixedSub_repOf θ φ S₁).symm.trans (hfix S₁ hS₁2 hS₁card)
  have hUcard : Nat.card U = 2 ^ 3 := by
    rw [hU, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective φ.symm.injective, hS₁card]
  have hUel : IsElemAbelian2 U := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩ _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hS₁comm g hg h hh]
    · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
      rw [← Subgroup.coe_pow, ← map_pow, pow_two, hS₁2 g hg, map_one, Subgroup.coe_one]
  have hAU : A ≤ U := by
    intro a ha
    have haL : a ∈ L := hAL ha
    have hmem : φ ⟨a, haL⟩ ∈ A₁ := ⟨⟨a, haL⟩, ha, rfl⟩
    obtain ⟨s, hs⟩ := (mem_rootGroup_iff _).mp (hx _ hmem)
    have hR' : x⁻¹ * φ ⟨a, haL⟩ * x ∈ UC22.K147L2Fac.rootSub F := by
      rw [hs]
      exact ⟨Multiplicative.ofAdd s, rfl⟩
    have hS : φ ⟨a, haL⟩ ∈ S₁ := ⟨x⁻¹ * φ ⟨a, haL⟩ * x, hR', by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩
    exact ⟨φ.symm (φ ⟨a, haL⟩), ⟨φ ⟨a, haL⟩, hS, rfl⟩, by simp⟩
  have hAp : IsPGroup 2 ↥A := E3.isPGroup_of_isElemAbelian2 hA
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card (p := 2)).mp hAp
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      apply hA1
      rw [Subgroup.eq_bot_iff_card, hr, h0, pow_zero]
    · exact h0
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2
    (show 2 ^ (r - 1) ∣ Nat.card ↥A by rw [hr]; exact pow_dvd_pow 2 (Nat.sub_le r 1))
  set D : Subgroup (MulAut I) := K.map A.subtype with hD
  have hDA : D ≤ A := Subgroup.map_subtype_le K
  have hDcard : Nat.card D = 2 ^ (r - 1) := by
    rw [hD, Subgroup.card_map_of_injective A.subtype_injective, hK]
  have hr' : 2 ^ r = 2 * 2 ^ (r - 1) := by rw [← pow_succ', Nat.sub_add_cancel hr1]
  have hrelDA : D.relIndex A = 2 := by
    have h := Subgroup.relIndex_mul_relIndex _ _ _ (bot_le : (⊥ : Subgroup (MulAut I)) ≤ D) hDA
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, hDcard, hr, hr', mul_comm 2] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hDel : IsElemAbelian2 D :=
    ⟨fun a ha b hb => hA.1 a (hDA ha) b (hDA hb), fun a ha => hA.2 a (hDA ha)⟩
  have hfixDA : fixV D = fixV A := hAfix D hDA (by
    show padicValNat 2 (D.relIndex A) < 2
    rw [hrelDA, padicValNat.self (by norm_num)]
    norm_num)
  have h1 := card_fixV_le_pow_relIndex hI hUel hAU
  rw [hUfix] at h1
  have h2 := card_fixV_le_pow_relIndex hI hDel (bot_le : (⊥ : Subgroup (MulAut I)) ≤ D)
  have hbot : fixV (⊥ : Subgroup (MulAut I)) = ⊤ :=
    eq_top_iff.mpr fun v _ y hy => by simp [Subgroup.mem_bot.mp hy]
  rw [hfixDA, Subgroup.relIndex_bot_left, hDcard, hbot, Subgroup.card_top, hI8] at h2
  have h4 : 2 ^ (r - 1) * A.relIndex U = 4 := by
    have h := Subgroup.relIndex_mul_relIndex _ _ _ (bot_le : (⊥ : Subgroup (MulAut I)) ≤ A) hAU
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, hUcard, hr, hr', mul_assoc,
      show (2 : ℕ) ^ 3 = 2 * 4 by norm_num] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have h3 : Nat.card (fixV A) ^ 2 ^ (r - 1) ≤ (2 ^ A.relIndex U) ^ 2 ^ (r - 1) :=
    Nat.pow_le_pow_left h1 _
  rw [← pow_mul, mul_comm, h4] at h3
  have := h2.trans h3
  norm_num at this

theorem exists_orderOf_eq_two_of_sl2 {F : Type} [Field F] [CharP F 2] {X L : Subgroup (MulAut I)}
    (hLX : L ≤ X) (φ : ↥L ≃* SL(2, F)) : ∃ t : ↥X, orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨_, hLX (φ.symm (uElt 1)).2⟩, orderOf_eq_prime ?_ ?_⟩
  · apply Subtype.ext
    show ((φ.symm (uElt 1) : ↥L) : MulAut I) ^ 2 = 1
    rw [← Subgroup.coe_pow, ← map_pow, pow_two, ← uElt_add, CharTwo.add_self_eq_zero, uElt_zero,
      map_one, Subgroup.coe_one]
  · intro h
    have h1 : ((φ.symm (uElt 1) : ↥L) : MulAut I) = 1 := congrArg Subtype.val h
    have h2 : φ.symm (uElt 1) = 1 := Subtype.ext h1
    have h3 : uElt (1 : F) = 1 := by rw [← φ.apply_symm_apply (uElt 1), h2, map_one]
    exact one_ne_zero (uElt_injective (h3.trans uElt_zero.symm))

theorem k14_5SmallFor_l2 :
    K14_5SmallFor fun L _ e => IsL2 L e := by
  intro I _ _ hI X L P e n hLX hLn hq hirr hS hPL hpar hinf hN hn hm
  classical
  have hO2 := o2Trivial_of_isIrrOn hI hirr
  obtain rfl := (eq_of_parabolic_of_rankOne hO2 hq (Or.inl hS) hPL hpar hinf).symm
  rw [hinf_eq_self hq] at hN
  have hne := nParam_eq_of_isL2 (fun _ _ _ h =>
    CFSG.LocalAnalysis.EvenBN.GMSK.card_eq_ordSuzuki_of_lieModel_twistedB2 h) hq hS hN
  subst e
  obtain ⟨F, _, _, hF, ⟨φ⟩⟩ := CFSG.Quasithin.Vol2.Ch11.OE2.exists_sl2_of_lieModel hS
  have : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hF]
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := Actor.exists_binModel_of_binary (V := I) fun v => by
    rw [← pow_two]
    exact hI v
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hn3 : 3 ≤ n := hn
  have hirrρ : (B45L2.repOf θ φ).IsIrreducible :=
    B45L2.repOf_isIrreducible θ φ (isIrrSec_of_isIrrOn_top hirr)
  haveI : Fact (B45L2.repOf θ φ).IsIrreducible := ⟨hirrρ⟩
  have hevX := exists_orderOf_eq_two_of_sl2 hLX φ
  have hev : Even (Nat.card ↥X) := by
    obtain ⟨u, hu⟩ := hevX
    exact even_iff_two_dvd.2 (hu ▸ orderOf_dvd_natCard u)
  obtain ⟨t₀, ht₀X, ht₀, ht₀m⟩ := E3.exists_involution_rkIdx_fixV_eq_mParam X hev
  let t : ↥X := ⟨t₀, ht₀X⟩
  have ht : orderOf t = 2 := by rw [Subgroup.orderOf_mk]; exact ht₀
  have htm : Module.finrank (ZMod 2) (W ⧸ fixSub (subRep θ X) (zpowers t)) = E3.mParam X := by
    rw [finrank_quotient_fixSub_subRep, MonoidHom.map_zpowers]
    exact ht₀m
  rcases trichotomy_of_involution hn3 hF' hI θ hLX hLn hirr φ t ht with
    h1 | ⟨s, hns, -, -, hs, horth⟩ | ⟨s, hns, h3s⟩
  ·
    have hlt : Nat.card W < 2 ^ (4 * n) := by
      rw [UC22.K147L2Fac.natCard_eq_two_pow]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    rcases CFSG.RankThree.GF2n.Tim81.Sec2.isNaturalModule_or_isOrthModule_or_of_card_lt
        (by omega) hF' (B45L2.repOf θ φ) (B45L2.repOf_nontrivial θ φ) (UC22.K147L2Fac.rootSub F)
        (fun u hu => UC22.K147L2Fac.mul_self_of_mem_rootSub hu)
        (UC22.K147L2Fac.natCard_rootSub.trans hF') hlt with
      hnat | ⟨l, hl, hnl, horth⟩ | ⟨l, hnl, hW, hfixR⟩
    · exact Or.inl ⟨n, Or.inl ⟨hS, binaryNaturalSL_of_isNaturalModule hF θ φ hnat⟩, Or.inl rfl⟩
    · have hNat := natOmegaMinus_of_isOrthModule (by omega) hl θ φ horth
      exact Or.inl ⟨l, Or.inr (Or.inl ⟨isOmegaMinus_of_natOmegaMinus_four hNat, hNat⟩),
        Or.inr hnl⟩
    ·
      have hW8 : Module.finrank (ZMod 2) W = 8 * l := UC22.K147L2Fac.finrank_eq_of_natCard hW
      have hl1 : l = 1 := by omega
      subst hl1
      have hn3' : n = 3 := by omega
      subst hn3'
      refine Or.inr ⟨hS, rfl, le_antisymm hm ?_, ?_⟩
      ·
        rw [← mGV_subRep θ X]
        refine UC22.Excl147.le_mGV (subRep θ X) ⟨t, ht⟩ fun t' ht' => ?_
        rcases trichotomy_of_involution hn3 hF' hI θ hLX hLn hirr φ t' ht' with
          h | ⟨s, hs, -⟩ | ⟨s, hs, -⟩
        · omega
        · omega
        · omega
      ·
        have hEnd := CFSG.RankThree.GF2n.Tim81.Sec2.card_fixedSub_eq_card_endRing (by norm_num)
          hF' (B45L2.repOf θ φ) (B45L2.repOf_nontrivial θ φ) (UC22.K147L2Fac.rootSub F)
          (fun u hu => UC22.K147L2Fac.mul_self_of_mem_rootSub hu)
          (UC22.K147L2Fac.natCard_rootSub.trans hF')
        rw [hfixR] at hEnd
        have hI8 : Nat.card I = 2 ^ 8 := (Actor.natCard_eq θ).trans hW
        refine CFSG.Quasithin.RonanE42.aParam_le_of_aSet_empty X 1 fun A =>
          not_mem_aSet_two_of_l2Eight hF' hI θ hLX hLn hirr φ hI8 (fun S hS2 hScard => ?_) A
        rw [CFSG.RankThree.GF2n.Tim81.Sec2.card_fixedSub_eq_card_endRing (by norm_num) hF'
          (B45L2.repOf θ φ) (B45L2.repOf_nontrivial θ φ) S hS2 hScard, ← hEnd, pow_one]
  ·
    have hNat := natOmegaMinus_of_isOrthModule (by omega) hs θ φ horth
    exact Or.inl ⟨s, Or.inr (Or.inl ⟨isOmegaMinus_of_natOmegaMinus_four hNat, hNat⟩), Or.inr hns⟩
  ·
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
