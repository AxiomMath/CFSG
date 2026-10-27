module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonTorusNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonUnipotent
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorusMatrices
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonBorelMatrices
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_11
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Transfer

namespace CFSG
end CFSG
open CFSG

/-!
# Sylow normalizers in Dickson's classification

This module isolates Huppert II.8.21 and the Sylow-normalizer shape used by
the II.8.22 counting argument.
-/

namespace CFSG.Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups
open BenderSuzuki.External
open scoped Pointwise
open scoped LinearAlgebra.Projectivization

universe u v

/-- The Schur-Zassenhaus part of Huppert II.8.21, separated from the
projective-line argument which makes the complement maximal cyclic in `H`. -/
private theorem h821_schur_zassenhaus_core
    {F : Type u} [Field F] [Finite F] {p f m : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m)
    (N : Subgroup H) (hN : N = Subgroup.normalizer (P : Set H))
    (hP_le_N : (P : Subgroup H) ≤ N)
    (PN : Subgroup N) [PN.Normal]
    (hPN : PN = (P : Subgroup H).subgroupOf N)
    (hquotient_cyclic : IsCyclic (N ⧸ PN))
    (hquotient_card_dvd : Nat.card (N ⧸ PN) ∣ Nat.card F - 1)
    (hcomplement_maximal :
      ∀ C : Subgroup N, PN.IsComplement' C → IsCyclic C →
        let W : Subgroup H := C.map N.subtype
        W = ⊥ ∨
          (1 < Nat.card W ∧
            ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W)) :
    ∃ W : Subgroup H,
      IsCyclic W ∧
      Nat.Coprime p (Nat.card W) ∧
      (W = ⊥ ∨
        (1 < Nat.card W ∧
          ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W)) ∧
      Nat.card (Subgroup.normalizer (P : Set H)) =
        Nat.card P * Nat.card W := by
  classical
  have hf_ne_zero : f ≠ 0 := by
    intro hf
    subst f
    have hcard : Nat.card F = 1 := by simpa using hFcard
    exact (Nat.ne_of_gt (Finite.one_lt_card (α := F))) hcard
  have hp_dvd_cardF : p ∣ Nat.card F := by
    rw [hFcard]
    exact dvd_pow_self p hf_ne_zero
  have hp_not_dvd_cardF_sub_one : ¬ p ∣ Nat.card F - 1 := by
    intro hp_sub
    have hp_one : p ∣ 1 := by
      have h := Nat.dvd_sub hp_dvd_cardF hp_sub
      have hcard_pos : 0 < Nat.card F := Nat.card_pos
      have hsub : Nat.card F - (Nat.card F - 1) = 1 := by omega
      rwa [hsub] at h
    exact (Fact.out : p.Prime).not_dvd_one hp_one
  have hcop_p_cardF_sub_one : Nat.Coprime p (Nat.card F - 1) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd_cardF_sub_one
  have hcop_p_quotient : Nat.Coprime p (Nat.card (N ⧸ PN)) :=
    Nat.Coprime.of_dvd_right hquotient_card_dvd hcop_p_cardF_sub_one
  have hPNcard : Nat.card PN = p ^ m := by
    calc
      Nat.card PN = Nat.card ((P : Subgroup H).subgroupOf N) := by rw [hPN]
      _ = Nat.card P :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_N).toEquiv
      _ = p ^ m := hPcard
  have hPNindex : PN.index = Nat.card (N ⧸ PN) := rfl
  have hPN_coprime_index : Nat.Coprime (Nat.card PN) PN.index := by
    rw [hPNcard, hPNindex]
    exact hcop_p_quotient.pow_left m
  obtain ⟨C, hPN_C_complement⟩ :=
    Subgroup.exists_right_complement'_of_coprime hPN_coprime_index
  have hC_cyclic : IsCyclic C := by
    let eC : N ⧸ PN ≃* C := hPN_C_complement.symm.QuotientMulEquiv
    let : IsCyclic (N ⧸ PN) := hquotient_cyclic
    exact isCyclic_of_surjective eC eC.surjective
  have hCcard : Nat.card C = Nat.card (N ⧸ PN) := by
    calc
      Nat.card C = PN.index := hPN_C_complement.symm.index_eq_card.symm
      _ = Nat.card (N ⧸ PN) := hPNindex
  let W : Subgroup H := C.map N.subtype
  have hW_cyclic : IsCyclic W := by
    let eW : C ≃* W :=
      Subgroup.equivMapOfInjective C N.subtype N.subtype_injective
    let : IsCyclic C := hC_cyclic
    exact isCyclic_of_surjective eW eW.surjective
  have hWcard : Nat.card W = Nat.card C := by
    dsimp [W]
    exact Subgroup.card_map_of_injective N.subtype_injective
  have hW_coprime : Nat.Coprime p (Nat.card W) := by
    rw [hWcard, hCcard]
    exact hcop_p_quotient
  have hW_boundary :
      W = ⊥ ∨
        (1 < Nat.card W ∧
          ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) := by
    simpa [W] using
      hcomplement_maximal C hPN_C_complement hC_cyclic
  refine ⟨W, hW_cyclic, hW_coprime, hW_boundary, ?_⟩
  rw [← hN]
  calc
    Nat.card N = Nat.card PN * Nat.card C :=
      hPN_C_complement.card_mul_card.symm
    _ = Nat.card P * Nat.card W := by
      rw [hWcard, hPN, Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hP_le_N).toEquiv]

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The standard upper-triangular Borel data used in Huppert II.8.21. -/
private theorem h821_standard_borel_data
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) :
    ∃ U T : Subgroup (PSL2MatrixGroup F),
      Nat.card U = Nat.card F ∧
      IsPGroup p U ∧
      IsMulCommutative U ∧
      IsCyclic T ∧
      Nat.card T =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      Nat.card T ∣ Nat.card F - 1 ∧
      T ≤ Subgroup.normalizer (U : Set (PSL2MatrixGroup F)) ∧
      (∀ t : PSL2MatrixGroup F, t ∈ T →
        ∀ x : PSL2MatrixGroup F, x ∈ U →
          t * x * t⁻¹ = x → t = 1 ∨ x = 1) ∧
      (∀ x : PSL2MatrixGroup F, x ∈ U ⊔ T → x ∉ U →
        ∃ u : PSL2MatrixGroup F, u ∈ U ∧
          x ∈ T.map (MulAut.conj u).toMonoidHom) ∧
      (∀ R : Subgroup (PSL2MatrixGroup F), R ≤ U → R ≠ ⊥ →
        Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) ≤ U ⊔ T) ∧
      ∃ unipotent : AddChar F (PSL2MatrixGroup F),
        ∃ splitTorus : Fˣ →* PSL2MatrixGroup F,
          Function.Injective unipotent ∧
          U = unipotent.toMonoidHom.range ∧
          T = splitTorus.range ∧
          (∀ a : Fˣ, ∀ x : F,
            splitTorus a * unipotent x * (splitTorus a)⁻¹ =
              unipotent ((a : F) ^ 2 * x)) ∧
          (∀ x : F, unipotent x =
            QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)) ∧
          ∀ a : Fˣ, splitTorus a =
            QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                  by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  let qSL : Matrix.SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F :=
    QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  let unipotentSL :
      AddChar F (Matrix.SpecialLinearGroup (Fin 2) F) :=
    unipotentSLAddChar F
  let unipotent : AddChar F (PSL2MatrixGroup F) :=
    qSL.compAddChar unipotentSL
  have h_unipotent_injective : Function.Injective unipotent := by
    simpa [unipotent, qSL, unipotentSL, projectiveUnipotentAddChar] using
      projectiveUnipotentAddChar_injective F
  let U : Subgroup (PSL2MatrixGroup F) := unipotent.toMonoidHom.range
  have hUcard : Nat.card U = Nat.card F := by
    let e : Multiplicative F ≃ U :=
      Equiv.ofInjective unipotent.toMonoidHom h_unipotent_injective
    exact Nat.card_congr e.symm
  have hU_isPGroup : IsPGroup p U := by
    apply IsPGroup.of_card
    rw [hUcard, hFcard]
  have hU_commutative : IsMulCommutative U := by
    constructor
    constructor
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rcases hx with ⟨a, rfl⟩
    rcases hy with ⟨b, rfl⟩
    apply Subtype.ext
    change unipotent a.toAdd * unipotent b.toAdd =
      unipotent b.toAdd * unipotent a.toAdd
    rw [← unipotent.map_add_eq_mul, add_comm,
      unipotent.map_add_eq_mul]
  let splitTorusSL : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F :=
    splitTorusSLHom F
  let splitTorus : Fˣ →* PSL2MatrixGroup F :=
    qSL.comp splitTorusSL
  let T : Subgroup (PSL2MatrixGroup F) := splitTorus.range
  have hf_ne_zero : f ≠ 0 :=
    huppert_II_8_27_field_exponent_ne_zero hFcard
  have hcard_roots :
      Nat.card (rootsOfUnity 2 F) =
        Nat.gcd (Nat.card F - 1) 2 := by
    let e :=
      Equiv.Set.image ((↑) : Fˣ → F) (rootsOfUnity 2 F : Set Fˣ)
        Units.val_injective
    have he :
        Nat.card (rootsOfUnity 2 F) =
          Nat.card (((↑) : Fˣ → F) '' (rootsOfUnity 2 F : Set Fˣ)) :=
      Nat.card_congr e
    rw [Units.val_set_image_rootsOfUnity_two] at he
    by_cases hp_two : p = 2
    · have htwo : (2 : F) = 0 := by
        subst p
        exact CharP.cast_eq_zero F 2
      have hneg_one : (-1 : F) = 1 := by
        apply (neg_eq_iff_add_eq_zero).2
        have hone_add_one : (1 : F) + 1 = 0 := by
          rw [show (1 : F) + 1 = 2 by norm_num, htwo]
        exact hone_add_one
      have hleft : Nat.card (rootsOfUnity 2 F) = 1 := by
        simpa [hneg_one] using he
      have hq_even : Even (Nat.card F) := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hf_ne_zero
        rw [hFcard, hp_two, hk, pow_succ]
        use 2 ^ k
        ring
      have hq_sub_one_odd : Odd (Nat.card F - 1) := by
        rw [← Nat.not_even_iff_odd]
        intro heven
        have hparity :=
          (Nat.even_sub
            (show 1 ≤ Nat.card F from
              (Finite.one_lt_card (α := F)).le)).mp heven
        exact Nat.not_even_one (hparity.mp hq_even)
      have hgcd : Nat.gcd (Nat.card F - 1) 2 = 1 :=
        Nat.coprime_iff_gcd_eq_one.mp hq_sub_one_odd.coprime_two_right
      rw [hleft, hgcd]
    · have hring_char_ne_two : ringChar F ≠ 2 := by
        rw [ringChar.eq F p]
        exact hp_two
      have hneg_one : (-1 : F) ≠ 1 :=
        Ring.neg_one_ne_one_of_char_ne_two hring_char_ne_two
      have hleft : Nat.card (rootsOfUnity 2 F) = 2 := by
        simpa [hneg_one, Ne.symm hneg_one] using he
      have hq_odd : Odd (Nat.card F) := by
        rw [hFcard]
        exact ((Fact.out : p.Prime).odd_of_ne_two hp_two).pow
      have htwo_dvd : 2 ∣ Nat.card F - 1 := by
        rcases hq_odd with ⟨k, hk⟩
        use k
        omega
      have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
        Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
          (Nat.dvd_gcd htwo_dvd (dvd_refl 2))
      rw [hleft, hgcd]
  have hsplit_mem_ker_iff (a : Fˣ) :
      a ∈ splitTorus.ker ↔ a ∈ rootsOfUnity 2 F := by
    rw [MonoidHom.mem_ker, mem_rootsOfUnity]
    constructor
    · intro ha
      have hcenter :
          splitTorusSL a ∈
            Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
        (QuotientGroup.eq_one_iff (splitTorusSL a)).mp ha
      have hscalar :=
        Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
          hcenter (0 : Fin 2)
      have ha_inv_val :=
        congrFun (congrFun hscalar (1 : Fin 2)) (1 : Fin 2)
      have ha_inv : a = a⁻¹ := by
        apply Units.ext
        simpa [splitTorusSL] using ha_inv_val
      simpa [pow_two] using (eq_inv_iff_mul_eq_one.mp ha_inv)
    · intro ha
      apply (QuotientGroup.eq_one_iff (splitTorusSL a)).mpr
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨(a : F), ?_, ?_⟩
      · simpa using congrArg Units.val ha
      · have ha_inv : a = a⁻¹ :=
          eq_inv_iff_mul_eq_one.mpr (by simpa [pow_two] using ha)
        have ha_inv_val : (a : F) = (a⁻¹ : F) := by
          simpa using congrArg Units.val ha_inv
        simpa [splitTorusSL] using
          splitTorusSLHom_eq_scalar_of_val_eq_inv a ha_inv_val
  have hsplit_ker_eq : splitTorus.ker = rootsOfUnity 2 F := by
    ext a
    exact hsplit_mem_ker_iff a
  have hsplit_ker_card :
      Nat.card splitTorus.ker = Nat.gcd (Nat.card F - 1) 2 := by
    rw [hsplit_ker_eq, hcard_roots]
  have hsplit_range_mul :
      Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
        Nat.card F - 1 := by
    calc
      Nat.card splitTorus.range * Nat.gcd (Nat.card F - 1) 2 =
          splitTorus.ker.index * Nat.card splitTorus.ker := by
        rw [Subgroup.index_ker, hsplit_ker_card]
      _ = Nat.card Fˣ := splitTorus.ker.index_mul_card
      _ = Nat.card F - 1 := by
        simpa [Nat.card_eq_fintype_card] using
          (Fintype.card_units (α := F))
  have hTcard :
      Nat.card T =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
    apply Nat.eq_div_of_mul_eq_left
    · rw [← hcard_roots]
      exact Nat.ne_of_gt Nat.card_pos
    · exact hsplit_range_mul
  have hT_cyclic : IsCyclic T := by
    have hUnitsCyclic : IsCyclic Fˣ := by
      let : IsCyclic (⊤ : Subgroup Fˣ) := isCyclic_subgroup_units ⊤
      exact isCyclic_of_surjective
        ((⊤ : Subgroup Fˣ).subtype) (by
          intro a
          exact ⟨⟨a, Subgroup.mem_top a⟩, rfl⟩)
    let : IsCyclic Fˣ := hUnitsCyclic
    exact isCyclic_of_surjective splitTorus.rangeRestrict
      splitTorus.rangeRestrict_surjective
  have hTcard_dvd : Nat.card T ∣ Nat.card F - 1 := by
    have hdvd := Subgroup.card_dvd_of_surjective splitTorus.rangeRestrict_surjective
    have hUnitsCard : Nat.card Fˣ = Nat.card F - 1 := by
      simpa [Nat.card_eq_fintype_card] using
        (Fintype.card_units (α := F))
    rw [← hUnitsCard]
    simpa [T] using hdvd
  have hsplitSL_mul (a : Fˣ) (x : F) :
      splitTorusSL a * unipotentSL x =
        unipotentSL ((a : F) ^ 2 * x) * splitTorusSL a := by
    simpa [splitTorusSL, unipotentSL] using
      splitTorusSLHom_mul_unipotentSLAddChar a x
  have hsplitSL_conj (a : Fˣ) (x : F) :
      splitTorusSL a * unipotentSL x * (splitTorusSL a)⁻¹ =
        unipotentSL ((a : F) ^ 2 * x) := by
    rw [hsplitSL_mul]
    simp
  have hsplit_conj (a : Fˣ) (x : F) :
      splitTorus a * unipotent x * (splitTorus a)⁻¹ =
        unipotent ((a : F) ^ 2 * x) := by
    simpa [splitTorus, unipotent] using congrArg qSL
      (hsplitSL_conj a x)
  have hT_le_normalizer :
      T ≤ Subgroup.normalizer (U : Set (PSL2MatrixGroup F)) := by
    intro t ht
    rcases ht with ⟨a, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rcases hh with ⟨x, hx⟩
      refine ⟨Multiplicative.ofAdd ((a : F) ^ 2 * x.toAdd), ?_⟩
      change unipotent ((a : F) ^ 2 * x.toAdd) =
        splitTorus a * h * (splitTorus a)⁻¹
      rw [← hx]
      exact (hsplit_conj a x.toAdd).symm
    · intro hh
      rcases hh with ⟨y, hy⟩
      refine ⟨Multiplicative.ofAdd (((a⁻¹ : Fˣ) : F) ^ 2 * y.toAdd), ?_⟩
      change unipotent (((a⁻¹ : Fˣ) : F) ^ 2 * y.toAdd) = h
      calc
        unipotent (((a⁻¹ : Fˣ) : F) ^ 2 * y.toAdd) =
            splitTorus a⁻¹ * unipotent y.toAdd * (splitTorus a⁻¹)⁻¹ :=
          (hsplit_conj a⁻¹ y.toAdd).symm
        _ = h := by
          change unipotent y.toAdd = splitTorus a * h * (splitTorus a)⁻¹ at hy
          have hTa_inv : splitTorus a⁻¹ = (splitTorus a)⁻¹ :=
            map_inv splitTorus a
          rw [hy, hTa_inv]
          group
  have hT_fixedPointFree
      (t : PSL2MatrixGroup F) (ht : t ∈ T)
      (x : PSL2MatrixGroup F) (hx : x ∈ U)
      (hfix : t * x * t⁻¹ = x) : t = 1 ∨ x = 1 := by
    rcases ht with ⟨a, ha⟩
    rcases hx with ⟨b, hb⟩
    change unipotent b.toAdd = x at hb
    have hcoord : (a : F) ^ 2 * b.toAdd = b.toAdd := by
      apply h_unipotent_injective
      calc
        unipotent ((a : F) ^ 2 * b.toAdd) =
            splitTorus a * unipotent b.toAdd * (splitTorus a)⁻¹ :=
          (hsplit_conj a b.toAdd).symm
        _ = splitTorus a * x * (splitTorus a)⁻¹ := by rw [hb]
        _ = t * x * t⁻¹ := by rw [ha]
        _ = x := hfix
        _ = unipotent b.toAdd := hb.symm
    by_cases hbzero : b.toAdd = 0
    · right
      rw [← hb, hbzero]
      simp
    · left
      rw [← ha]
      apply MonoidHom.mem_ker.mp
      apply (hsplit_mem_ker_iff a).2
      rw [mem_rootsOfUnity]
      apply Units.ext
      apply mul_right_cancel₀ hbzero
      simpa using hcoord
  have hB_conjugate_torus
      (x : PSL2MatrixGroup F) (hxB : x ∈ U ⊔ T) (hxU : x ∉ U) :
      ∃ u : PSL2MatrixGroup F, u ∈ U ∧
        x ∈ T.map (MulAut.conj u).toMonoidHom := by
    have hB_product :
        (U : Set (PSL2MatrixGroup F)) * (T : Set (PSL2MatrixGroup F)) =
          (U ⊔ T : Subgroup (PSL2MatrixGroup F)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left
        U T hT_le_normalizer]
    change x ∈ ((U ⊔ T : Subgroup (PSL2MatrixGroup F)) :
      Set (PSL2MatrixGroup F)) at hxB
    rw [← hB_product] at hxB
    rcases hxB with ⟨y, hyU, z, hzT, hyz⟩
    rcases hyU with ⟨b, hb⟩
    rcases hzT with ⟨a, ha⟩
    have hfactor : unipotent b.toAdd * splitTorus a = x := by
      rw [← hb, ← ha] at hyz
      exact hyz
    have hsplit_ne_one : splitTorus a ≠ 1 := by
      intro ha_one
      apply hxU
      rw [← hfactor, ha_one, mul_one]
      exact ⟨b, rfl⟩
    have ha_sq_ne : (a : F) ^ 2 ≠ 1 := by
      intro ha_sq
      apply hsplit_ne_one
      have ha_sq_units : a ^ 2 = 1 := by
        apply Units.ext
        simpa using ha_sq
      exact MonoidHom.mem_ker.mp
        ((hsplit_mem_ker_iff a).2
          (by simpa [mem_rootsOfUnity] using ha_sq_units))
    have hden : 1 - (a : F) ^ 2 ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm ha_sq_ne)
    let s : F := b.toAdd / (1 - (a : F) ^ 2)
    let u : PSL2MatrixGroup F := unipotent s
    have hs : s + (a : F) ^ 2 * (-s) = b.toAdd := by
      dsimp [s]
      field_simp [hden]
      ring
    have hx_conj :
        u * splitTorus a * u⁻¹ = x := by
      rw [← hfactor]
      change unipotent s * splitTorus a * (unipotent s)⁻¹ =
        unipotent b.toAdd * splitTorus a
      calc
        unipotent s * splitTorus a * (unipotent s)⁻¹ =
            unipotent s *
              (splitTorus a * unipotent (-s) * (splitTorus a)⁻¹) *
                splitTorus a := by
          rw [unipotent.map_neg_eq_inv]
          group
        _ = unipotent s * unipotent ((a : F) ^ 2 * (-s)) *
              splitTorus a := by
          rw [hsplit_conj]
        _ = unipotent (s + (a : F) ^ 2 * (-s)) * splitTorus a := by
          rw [unipotent.map_add_eq_mul]
        _ = unipotent b.toAdd * splitTorus a := by rw [hs]
    refine ⟨u, ⟨Multiplicative.ofAdd s, rfl⟩, ?_⟩
    rw [← hx_conj]
    exact Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom
      (⟨a, rfl⟩ : splitTorus a ∈ T)
  have hnormalizer_le
      (R : Subgroup (PSL2MatrixGroup F)) (hR_le_U : R ≤ U)
      (hR_ne_bot : R ≠ ⊥) :
      Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) ≤ U ⊔ T := by
    obtain ⟨r, hr_ne_one⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR_ne_bot
    have hrU : (r : PSL2MatrixGroup F) ∈ U := hR_le_U r.property
    rcases hrU with ⟨t, ht⟩
    have ht_ne_zero : t.toAdd ≠ 0 := by
      intro ht_zero
      apply hr_ne_one
      apply Subtype.ext
      change (r : PSL2MatrixGroup F) = 1
      rw [← ht]
      change unipotent t.toAdd = 1
      rw [ht_zero]
      simp
    have hr_eq : (r : PSL2MatrixGroup F) = unipotent t.toAdd := by
      simpa using ht.symm
    intro g
    refine QuotientGroup.induction_on g ?_
    intro A hA_normalizes
    have hr_conj_R :
        qSL A * (r : PSL2MatrixGroup F) * (qSL A)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hA_normalizes
        (r : PSL2MatrixGroup F)).mp r.property
    have hconj_mem :
        qSL A * unipotent t.toAdd * (qSL A)⁻¹ ∈ U := by
      rw [← hr_eq]
      exact hR_le_U hr_conj_R
    rcases hconj_mem with ⟨x, hx⟩
    have hxq :
        qSL (unipotentSL x.toAdd) =
          qSL (A * unipotentSL t.toAdd * A⁻¹) := by
      simpa [unipotent] using hx
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hxq with
      ⟨z, hz_center, hz_eq⟩
    have hz_eq_mul_A :
        unipotentSL x.toAdd * z * A = A * unipotentSL t.toAdd := by
      calc
        unipotentSL x.toAdd * z * A =
            (A * unipotentSL t.toAdd * A⁻¹) * A := by rw [hz_eq]
        _ = A * unipotentSL t.toAdd := by group
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz_center (0 : Fin 2)
    have hz_eq_matrix := congrArg Subtype.val hz_eq_mul_A
    change
      (unipotentSL x.toAdd : Matrix (Fin 2) (Fin 2) F) *
          (z : Matrix (Fin 2) (Fin 2) F) *
            (A : Matrix (Fin 2) (Fin 2) F) =
        (A : Matrix (Fin 2) (Fin 2) F) *
          (unipotentSL t.toAdd : Matrix (Fin 2) (Fin 2) F) at hz_eq_matrix
    rw [← hscalar] at hz_eq_matrix
    have h10 := congrFun (congrFun hz_eq_matrix (1 : Fin 2)) (0 : Fin 2)
    have h11 := congrFun (congrFun hz_eq_matrix (1 : Fin 2)) (1 : Fin 2)
    simp [unipotentSL, Matrix.mul_apply] at h10 h11
    have hc_zero : A (1 : Fin 2) (0 : Fin 2) = 0 := by
      by_cases hr_one : (z : Matrix (Fin 2) (Fin 2) F) 0 0 = 1
      · rw [hr_one, one_mul] at h11
        have hcancel := congrArg (fun y : F => y - A 1 1) h11
        have hct : A 1 0 * t.toAdd = 0 := by
          simpa using hcancel.symm
        exact (mul_eq_zero.mp hct).resolve_right ht_ne_zero
      · have hprod :
            (((z : Matrix (Fin 2) (Fin 2) F) 0 0) - 1) *
                A (1 : Fin 2) (0 : Fin 2) = 0 := by
          calc
            (((z : Matrix (Fin 2) (Fin 2) F) 0 0) - 1) * A 1 0 =
                ((z : Matrix (Fin 2) (Fin 2) F) 0 0) * A 1 0 - A 1 0 := by ring
            _ = 0 := by rw [h10]; ring
        exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hr_one)
    obtain ⟨aU, hfactor0⟩ :=
      eq_unipotentSLAddChar_mul_splitTorusSLHom_of_lowerLeft_eq_zero
        A hc_zero
    have hfactor :
        A = unipotentSL (A 0 1 * A 0 0) * splitTorusSL aU := by
      simpa [unipotentSL, splitTorusSL] using hfactor0
    have hfactor_q := congrArg qSL hfactor
    change qSL A ∈ U ⊔ T
    have hfactor_q' :
        qSL A = unipotent (A 0 1 * A 0 0) * splitTorus aU := by
      simpa [unipotent, splitTorus] using hfactor_q
    rw [hfactor_q']
    exact (U ⊔ T).mul_mem
      ((show U ≤ U ⊔ T from le_sup_left)
        ⟨Multiplicative.ofAdd (A 0 1 * A 0 0), rfl⟩)
      ((show T ≤ U ⊔ T from le_sup_right) ⟨aU, rfl⟩)
  exact ⟨U, T, hUcard, hU_isPGroup, hU_commutative, hT_cyclic,
    hTcard, hTcard_dvd, hT_le_normalizer, hT_fixedPointFree,
    hB_conjugate_torus, hnormalizer_le, unipotent, splitTorus,
    h_unipotent_injective, rfl, rfl, hsplit_conj,
    fun _ => rfl, fun _ => rfl⟩

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The normalizer quotient in Huppert II.8.21 embeds in the cyclic
split-torus quotient of a standard Borel subgroup. -/
public theorem h821_borel_quotient_data
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hP_ne_bot : (P : Subgroup H) ≠ ⊥)
    (N : Subgroup H) (hN : N = Subgroup.normalizer (P : Set H))
    (PN : Subgroup N) [PN.Normal]
    (hPN : PN = (P : Subgroup H).subgroupOf N) :
    IsCyclic (N ⧸ PN) ∧
      Nat.card (N ⧸ PN) ∣
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      (∀ n : N, n ∉ PN → ∀ x : (P : Subgroup H), x ≠ 1 →
        (n : H) * (x : H) * (n : H)⁻¹ ≠ (x : H)) ∧
      ∃ U T : Subgroup (PSL2MatrixGroup F),
        ∃ conjH : H →* PSL2MatrixGroup F,
          Function.Injective conjH ∧
          (∃ g : PSL2MatrixGroup F, ∀ h : H,
            conjH h = g * (h : PSL2MatrixGroup F) * g⁻¹) ∧
          IsMulCommutative U ∧
          IsCyclic T ∧
          Nat.card T =
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
          (∀ t : PSL2MatrixGroup F, t ∈ T →
            ∀ x : PSL2MatrixGroup F, x ∈ U →
              t * x * t⁻¹ = x → t = 1 ∨ x = 1) ∧
          (P : Subgroup H).map conjH ≤ U ∧
          U ⊔ T ≤ Subgroup.normalizer
            (U : Set (PSL2MatrixGroup F)) ∧
          (∀ x : PSL2MatrixGroup F, x ∈ U ⊔ T → x ∉ U →
            ∃ u : PSL2MatrixGroup F, u ∈ U ∧
              x ∈ T.map (MulAut.conj u).toMonoidHom) ∧
          (∀ n : N, conjH (n : H) ∈ U ⊔ T) ∧
          (∀ n : N, conjH (n : H) ∈ U ↔ n ∈ PN) ∧
          ∃ unipotent : AddChar F (PSL2MatrixGroup F),
            ∃ splitTorus : Fˣ →* PSL2MatrixGroup F,
              Function.Injective unipotent ∧
              U = unipotent.toMonoidHom.range ∧
              T = splitTorus.range ∧
              (∀ a : Fˣ, ∀ x : F,
                splitTorus a * unipotent x * (splitTorus a)⁻¹ =
                  unipotent ((a : F) ^ 2 * x)) ∧
              (∀ x : F, unipotent x =
                QuotientGroup.mk'
                  (Subgroup.center
                    (Matrix.SpecialLinearGroup (Fin 2) F))
                  (⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                    Matrix.SpecialLinearGroup (Fin 2) F)) ∧
              ∀ a : Fˣ, splitTorus a =
                QuotientGroup.mk'
                  (Subgroup.center
                    (Matrix.SpecialLinearGroup (Fin 2) F))
                  (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                      by simp [Matrix.det_fin_two]⟩ :
                    Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  obtain ⟨U, T, hUcard, hU_isPGroup, hU_commutative,
      hT_cyclic, hTcard, hTcard_dvd, hT_le_normalizer,
      hT_fixedPointFree, hB_conjugate_torus, hnormalizer_le,
      unipotent, splitTorus, h_unipotent_injective,
      hU_range, hT_range, hsplit_conj, hunipotent_matrix,
      hsplitTorus_matrix⟩ :=
    h821_standard_borel_data hFcard
  obtain ⟨Q0, hU_le_Q0⟩ := hU_isPGroup.exists_le_sylow
  have hQ0card : Nat.card (Q0 : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    rcases huppert_II_8_2_a_sylow_equiv_additive hFcard Q0 with ⟨eQ⟩
    exact (Nat.card_congr eQ.toEquiv).symm
  have hU_eq_Q0 : U = (Q0 : Subgroup (PSL2MatrixGroup F)) :=
    Subgroup.eq_of_le_of_card_ge hU_le_Q0 (by rw [hQ0card, hUcard])
  obtain ⟨Q, hQcomap⟩ := P.exists_comap_subtype_eq
  have hPmap_le_Q : (P : Subgroup H).map H.subtype ≤
      (Q : Subgroup (PSL2MatrixGroup F)) := by
    rw [Subgroup.map_le_iff_le_comap, hQcomap]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    (PSL2MatrixGroup F) Q Q0
  let Pambient : Subgroup (PSL2MatrixGroup F) :=
    (P : Subgroup H).map H.subtype
  let Pconj : Subgroup (PSL2MatrixGroup F) :=
    Pambient.map (MulAut.conj g).toMonoidHom
  have hQconj_eq :
      (Q : Subgroup (PSL2MatrixGroup F)).map
          (MulAut.conj g).toMonoidHom = U := by
    have hg' := congrArg
      (fun S : Sylow p (PSL2MatrixGroup F) =>
        (S : Subgroup (PSL2MatrixGroup F))) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      ← hU_eq_Q0] at hg'
    exact hg'
  have hPconj_le_U : Pconj ≤ U := by
    rw [← hQconj_eq]
    exact Subgroup.map_mono hPmap_le_Q
  have hPambient_ne_bot : Pambient ≠ ⊥ := by
    intro hbot
    apply hP_ne_bot
    exact (Subgroup.map_eq_bot_iff_of_injective
      (P : Subgroup H) H.subtype_injective).mp hbot
  have hPconj_ne_bot : Pconj ≠ ⊥ := by
    intro hbot
    apply hPambient_ne_bot
    exact (Subgroup.map_eq_bot_iff_of_injective Pambient
      (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).mp hbot
  let B : Subgroup (PSL2MatrixGroup F) := U ⊔ T
  have hPconj_normalizer_le_B :
      Subgroup.normalizer (Pconj : Set (PSL2MatrixGroup F)) ≤ B := by
    simpa [B] using hnormalizer_le Pconj hPconj_le_U hPconj_ne_bot
  have h_normalizer_conj_to_B (n : N) :
      (MulAut.conj g) (H.subtype n) ∈ B := by
    have hn_normalizer : (n : H) ∈
        Subgroup.normalizer (P : Set H) := by
      rw [← hN]
      exact n.property
    have hn_ambient :
        H.subtype n ∈ Subgroup.normalizer
          (Pambient : Set (PSL2MatrixGroup F)) := by
      apply Subgroup.le_normalizer_map H.subtype
      exact ⟨n, hn_normalizer, rfl⟩
    have hn_conj :
        (MulAut.conj g) (H.subtype n) ∈
          Subgroup.normalizer (Pconj : Set (PSL2MatrixGroup F)) := by
      change (MulAut.conj g) (H.subtype n) ∈
        Subgroup.normalizer
          ((Pambient.map (MulAut.conj g).toMonoidHom :
            Subgroup (PSL2MatrixGroup F)) : Set (PSL2MatrixGroup F))
      apply Subgroup.le_normalizer_map (MulAut.conj g).toMonoidHom
      exact ⟨H.subtype n, hn_ambient, rfl⟩
    exact hPconj_normalizer_le_B hn_conj
  let conjH : H →* PSL2MatrixGroup F :=
    (MulAut.conj g).toMonoidHom.comp H.subtype
  have hconjH_injective : Function.Injective conjH :=
    (MulAut.conj g).injective.comp H.subtype_injective
  let KH : Subgroup H := U.comap conjH
  have hP_le_KH : (P : Subgroup H) ≤ KH := by
    intro x hx
    change conjH x ∈ U
    apply hPconj_le_U
    change conjH x ∈
      Pambient.map (MulAut.conj g).toMonoidHom
    refine ⟨H.subtype x, ?_, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hKH_isPGroup : IsPGroup p KH :=
    hU_isPGroup.comap_of_injective conjH hconjH_injective
  have hKH_eq_P : KH = (P : Subgroup H) :=
    P.is_maximal' hKH_isPGroup hP_le_KH
  have hU_le_B : U ≤ B := by
    exact le_sup_left
  have hT_le_B : T ≤ B := by
    exact le_sup_right
  let UB : Subgroup B := U.subgroupOf B
  let TB : Subgroup B := T.subgroupOf B
  let hUB_normal : UB.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (sup_le Subgroup.le_normalizer hT_le_normalizer)
  have hUB_sup_TB : UB ⊔ TB = ⊤ := by
    have hsup := Subgroup.subgroupOf_sup hU_le_B hT_le_B
    simpa [B, UB, TB] using hsup.symm
  have hTB_cyclic : IsCyclic TB := by
    let eTB : TB ≃* T := Subgroup.subgroupOfEquivOfLe hT_le_B
    let : IsCyclic T := hT_cyclic
    exact isCyclic_of_surjective eTB.symm eTB.symm.surjective
  let borelQuotient : B →* B ⧸ UB := QuotientGroup.mk' UB
  have hmap_UB_bot : Subgroup.map borelQuotient UB = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact le_of_eq (QuotientGroup.ker_mk' UB).symm
  have hmap_TB_top : Subgroup.map borelQuotient TB = ⊤ := by
    calc
      Subgroup.map borelQuotient TB =
          ⊥ ⊔ Subgroup.map borelQuotient TB := by simp
      _ = Subgroup.map borelQuotient (UB ⊔ TB) := by
        rw [Subgroup.map_sup, hmap_UB_bot]
      _ = Subgroup.map borelQuotient ⊤ := by rw [hUB_sup_TB]
      _ = ⊤ := Subgroup.map_top_of_surjective borelQuotient
        (QuotientGroup.mk'_surjective UB)
  let torusToBorelQuotient : TB →* B ⧸ UB :=
    borelQuotient.comp TB.subtype
  have htorusToBorelQuotient_surjective :
      Function.Surjective torusToBorelQuotient := by
    intro y
    have hy : y ∈ Subgroup.map borelQuotient TB := by
      rw [hmap_TB_top]
      trivial
    rcases hy with ⟨b, hb, hby⟩
    exact ⟨⟨b, hb⟩, hby⟩
  have hB_quotient_cyclic : IsCyclic (B ⧸ UB) := by
    let : IsCyclic TB := hTB_cyclic
    exact isCyclic_of_surjective torusToBorelQuotient
      htorusToBorelQuotient_surjective
  have hB_quotient_card_dvd : Nat.card (B ⧸ UB) ∣ Nat.card T := by
    have hdvd := Subgroup.card_dvd_of_surjective
      htorusToBorelQuotient_surjective
    have hTBcard : Nat.card TB = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_le_B).toEquiv
    rwa [hTBcard] at hdvd
  let normToB : N →* B :=
    (conjH.comp N.subtype).codRestrict B h_normalizer_conj_to_B
  have hnormToB_injective : Function.Injective normToB := by
    intro x y hxy
    apply Subtype.ext
    apply hconjH_injective
    exact congrArg Subtype.val hxy
  let normToBQuotient : N →* B ⧸ UB :=
    borelQuotient.comp normToB
  have hborelQuotient_ker : borelQuotient.ker = UB :=
    QuotientGroup.ker_mk' UB
  have hnormToBQuotient_ker : normToBQuotient.ker = PN := by
    ext n
    constructor
    · intro hn
      have hn' : normToB n ∈ borelQuotient.ker := hn
      rw [hborelQuotient_ker] at hn'
      have hnU : conjH (n : H) ∈ U := hn'
      have hnKH : (n : H) ∈ KH := hnU
      rw [hKH_eq_P] at hnKH
      rw [hPN]
      exact hnKH
    · intro hn
      have hnP : (n : H) ∈ (P : Subgroup H) := by
        rw [hPN] at hn
        exact hn
      have hnU : conjH (n : H) ∈ U := by
        change (n : H) ∈ KH
        rw [hKH_eq_P]
        exact hnP
      have hn' : normToB n ∈ borelQuotient.ker := by
        rw [hborelQuotient_ker]
        exact hnU
      exact hn'
  let eNormalizerQuotient : N ⧸ PN ≃* normToBQuotient.range :=
    (QuotientGroup.quotientMulEquivOfEq hnormToBQuotient_ker.symm).trans
      (QuotientGroup.quotientKerEquivRange normToBQuotient)
  have hNormalizer_quotient_cyclic : IsCyclic (N ⧸ PN) := by
    have hRangeCyclic : IsCyclic normToBQuotient.range := by
      let : IsCyclic (B ⧸ UB) := hB_quotient_cyclic
      exact Subgroup.isCyclic normToBQuotient.range
    let : IsCyclic normToBQuotient.range := hRangeCyclic
    exact isCyclic_of_surjective eNormalizerQuotient.symm
      eNormalizerQuotient.symm.surjective
  have hNormalizer_quotient_card_dvd :
      Nat.card (N ⧸ PN) ∣
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
    have hRange_dvd :
        Nat.card normToBQuotient.range ∣ Nat.card (B ⧸ UB) :=
      normToBQuotient.range.card_subgroup_dvd_card
    have hdvd := dvd_trans hRange_dvd hB_quotient_card_dvd
    have hquotient_eq_range :
        Nat.card (N ⧸ PN) = Nat.card normToBQuotient.range :=
      Nat.card_congr eNormalizerQuotient.toEquiv
    rw [hquotient_eq_range]
    rw [← hTcard]
    exact hdvd
  have hP_map_conjH_le_U : (P : Subgroup H).map conjH ≤ U := by
    rw [Subgroup.map_le_iff_le_comap]
    exact hP_le_KH
  have hB_le_normalizer :
      U ⊔ T ≤ Subgroup.normalizer
        (U : Set (PSL2MatrixGroup F)) :=
    sup_le Subgroup.le_normalizer hT_le_normalizer
  have hconjH_mem_U_iff (n : N) :
      conjH (n : H) ∈ U ↔ n ∈ PN := by
    constructor
    · intro hnU
      have hnKH : (n : H) ∈ KH := hnU
      rw [hKH_eq_P] at hnKH
      rw [hPN]
      exact hnKH
    · intro hn
      have hnP : (n : H) ∈ (P : Subgroup H) := by
        rw [hPN] at hn
        exact hn
      change (n : H) ∈ KH
      rw [hKH_eq_P]
      exact hnP
  have hNormalizer_fixedPointFree :
      ∀ n : N, n ∉ PN → ∀ x : (P : Subgroup H), x ≠ 1 →
        (n : H) * (x : H) * (n : H)⁻¹ ≠ (x : H) := by
    intro n hnPN x hx hfix
    have hn_not_U : conjH (n : H) ∉ U := by
      intro hnU
      exact hnPN ((hconjH_mem_U_iff n).mp hnU)
    obtain ⟨u, huU, hntorus⟩ :=
      hB_conjugate_torus (conjH (n : H))
        (h_normalizer_conj_to_B n) hn_not_U
    rcases hntorus with ⟨t, htT, ht⟩
    change u * t * u⁻¹ = conjH (n : H) at ht
    have hxU : conjH (x : H) ∈ U :=
      hP_map_conjH_le_U (Subgroup.mem_map_of_mem conjH x.property)
    let x' : PSL2MatrixGroup F := u⁻¹ * conjH (x : H) * u
    have hx'U : x' ∈ U := by
      exact U.mul_mem (U.mul_mem (U.inv_mem huU) hxU) huU
    have hx'ne : x' ≠ 1 := by
      intro hx'one
      apply hx
      apply Subtype.ext
      apply hconjH_injective
      have hconjx : conjH (x : H) = 1 := by
        calc
          conjH (x : H) = u * x' * u⁻¹ := by
            dsimp [x']
            group
          _ = 1 := by rw [hx'one]; simp
      simpa using hconjx
    have hfixMap :
        conjH (n : H) * conjH (x : H) * (conjH (n : H))⁻¹ =
          conjH (x : H) := by
      simpa using congrArg conjH hfix
    have hfix' : t * x' * t⁻¹ = x' := by
      dsimp [x']
      calc
        t * (u⁻¹ * conjH (x : H) * u) * t⁻¹ =
            u⁻¹ * ((u * t * u⁻¹) * conjH (x : H) *
              (u * t * u⁻¹)⁻¹) * u := by group
        _ = u⁻¹ * (conjH (n : H) * conjH (x : H) *
              (conjH (n : H))⁻¹) * u := by rw [ht]
        _ = u⁻¹ * conjH (x : H) * u := by rw [hfixMap]
    have htne : t ≠ 1 := by
      intro htone
      apply hn_not_U
      rw [← ht, htone]
      simp
    rcases hT_fixedPointFree t htT x' hx'U hfix' with htone | hx'one
    · exact htne htone
    · exact hx'ne hx'one
  exact ⟨hNormalizer_quotient_cyclic, hNormalizer_quotient_card_dvd,
    hNormalizer_fixedPointFree, U, T, conjH, hconjH_injective,
    ⟨g, fun _ => rfl⟩,
    hU_commutative, hT_cyclic,
    hTcard, hT_fixedPointFree, hP_map_conjH_le_U, hB_le_normalizer,
    hB_conjugate_torus, h_normalizer_conj_to_B,
    hconjH_mem_U_iff, unipotent, splitTorus,
    h_unipotent_injective, hU_range, hT_range, hsplit_conj,
    hunipotent_matrix, hsplitTorus_matrix⟩


private theorem h821_complement_maximal_of_overgroups_coprime
    {H : Type u} [Group H] [Finite H]
    (N : Subgroup H) (PN C : Subgroup N) [PN.Normal]
    (hcomp : PN.IsComplement' C)
    (hovergroups :
      let W : Subgroup H := C.map N.subtype
      ∀ V : Subgroup H, IsCyclic V → W ≤ V → W ≠ ⊥ →
        V ≤ N ∧ Nat.Coprime (Nat.card PN) (Nat.card V)) :
    let W : Subgroup H := C.map N.subtype
    W = ⊥ ∨
      (1 < Nat.card W ∧
        ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) := by
  classical
  let W : Subgroup H := C.map N.subtype
  by_cases hWbot : W = ⊥
  · exact Or.inl hWbot
  · right
    refine ⟨(Subgroup.one_lt_card_iff_ne_bot W).2 hWbot, ?_⟩
    intro V hVcyclic hWV
    obtain ⟨hV_le_N, hcoprime⟩ :=
      hovergroups V hVcyclic hWV hWbot
    let VN : Subgroup N := V.subgroupOf N
    have hC_le_VN : C ≤ VN := by
      intro c hc
      change (c : H) ∈ V
      apply hWV
      exact Subgroup.mem_map_of_mem N.subtype hc
    have hVNcard : Nat.card VN = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le_N).toEquiv
    have hdisjoint : Disjoint PN VN := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have hx_order_PN : orderOf x ∣ Nat.card PN := by
        simpa [Subgroup.orderOf_coe] using
          (orderOf_dvd_natCard (⟨x, hx.1⟩ : PN))
      have hx_order_VN : orderOf x ∣ Nat.card VN := by
        simpa [Subgroup.orderOf_coe] using
          (orderOf_dvd_natCard (⟨x, hx.2⟩ : VN))
      have hcoprime' : Nat.Coprime (Nat.card PN) (Nat.card VN) := by
        rw [hVNcard]
        exact hcoprime
      apply orderOf_eq_one_iff.mp
      apply Nat.eq_one_of_dvd_coprimes hcoprime'
      · exact hx_order_PN
      · exact hx_order_VN
    have hsup : PN ⊔ VN = ⊤ := by
      apply top_unique
      rw [← hcomp.sup_eq_top]
      exact sup_le_sup_left hC_le_VN PN
    have hmul : (PN : Set N) * (VN : Set N) = Set.univ := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left PN VN
        Subgroup.le_normalizer_of_normal, hsup]
      rfl
    have hcompV : PN.IsComplement' VN :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjoint hmul
    have hcardCV : Nat.card C = Nat.card VN := by
      calc
        Nat.card C = PN.index := hcomp.symm.index_eq_card.symm
        _ = Nat.card VN := hcompV.symm.index_eq_card
    have hCV : C = VN :=
      Subgroup.eq_of_le_of_card_ge hC_le_VN (by rw [hcardCV])
    calc
      V = VN.map N.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hV_le_N).symm
      _ = C.map N.subtype := by rw [← hCV]
      _ = W := rfl

private theorem h821_cyclic_overgroup_partition_component
    {G H : Type u} [Group G] [Group H] [Finite H]
    (Family : Subgroup G → Prop)
    (hpartition : ∀ x : G, x ≠ 1 →
      ∃! T : Subgroup G, x ∈ T ∧ Family T)
    (embed : H →* G) (hembed : Function.Injective embed)
    (W : Subgroup H) (A : Subgroup G) (qminus : ℕ)
    (hseed : ∃ x : H, x ∈ W ∧ x ≠ 1 ∧ embed x ∈ A)
    (hAfamily : Family A) (hAcard : Nat.card A ∣ qminus) :
    ∀ V : Subgroup H, IsCyclic V → W ≤ V →
      V.map embed ≤ A ∧ Nat.card V ∣ qminus := by
  intro V hVcyclic hWV
  obtain ⟨x, hxW, hx, hxA⟩ := hseed
  have hxembed : embed x ≠ 1 := by
    intro h
    apply hx
    exact hembed (h.trans (map_one embed).symm)
  have hVmap_cyclic : IsCyclic (V.map embed) := by
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective V embed hembed)).mp hVcyclic
  have hVmap_le : V.map embed ≤ A :=
    cyclic_le_unique_partition_family Family hpartition hxembed
      hxA hAfamily
      (Subgroup.mem_map_of_mem embed (hWV hxW)) hVmap_cyclic
  refine ⟨hVmap_le, ?_⟩
  have hmapcard : Nat.card (V.map embed) = Nat.card V :=
    Subgroup.card_map_of_injective hembed
  rw [← hmapcard]
  exact dvd_trans (Subgroup.card_dvd_of_le hVmap_le) hAcard


/-- An injective embedding into a commutative ambient `p`-subgroup reflects
normalization of that ambient subgroup back to a Sylow subgroup. -/
private theorem sylow_mem_normalizer_of_embed_mem_normalizer
    {H : Type u} {G : Type v} [Group H] [Finite H] [Group G]
    {p : ℕ} [Fact p.Prime]
    (embed : H →* G) (hembed : Function.Injective embed)
    (P : Sylow p H) (U B : Subgroup G)
    (hU_comm : IsMulCommutative U)
    (hP_le_U : (P : Subgroup H).map embed ≤ U)
    (hB_le : B ≤ Subgroup.normalizer (U : Set G))
    (y : H) (hyB : embed y ∈ B) :
    y ∈ Subgroup.normalizer ((P : Subgroup H) : Set H) := by
  let : IsMulCommutative U := hU_comm
  let K : Subgroup H :=
    (P : Subgroup H).map (MulAut.conj y).toMonoidHom
  have hyN : embed y ∈ Subgroup.normalizer (U : Set G) := hB_le hyB
  have hK_map_le_U : K.map embed ≤ U := by
    intro z hz
    rcases hz with ⟨k, hkK, rfl⟩
    rcases hkK with ⟨x, hxP, rfl⟩
    have hxU : embed x ∈ U :=
      hP_le_U (Subgroup.mem_map_of_mem embed hxP)
    have hconjU : embed y * embed x * (embed y)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hyN (embed x)).mp hxU
    simpa [MulAut.conj_apply] using hconjU
  have hK_p : IsPGroup p K :=
    P.isPGroup'.map (MulAut.conj y).toMonoidHom
  have hK_le_normalizer :
      K ≤ Subgroup.normalizer ((P : Subgroup H) : Set H) := by
    intro k hkK
    rw [← Subgroup.conjAct_pointwise_smul_iff]
    change (P : Subgroup H).map (MulAut.conj k).toMonoidHom =
      (P : Subgroup H)
    apply Subgroup.eq_of_le_of_card_ge
    · intro z hz
      rcases hz with ⟨x, hxP, rfl⟩
      have hkU : embed k ∈ U :=
        hK_map_le_U (Subgroup.mem_map_of_mem embed hkK)
      have hxU : embed x ∈ U :=
        hP_le_U (Subgroup.mem_map_of_mem embed hxP)
      have hcomm_embed : embed k * embed x = embed x * embed k :=
        setLike_mul_comm hkU hxU
      have hcomm : k * x = x * k := hembed (by simpa using hcomm_embed)
      change k * x * k⁻¹ ∈ (P : Subgroup H)
      rw [hcomm, mul_inv_cancel_right]
      exact hxP
    · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
  have hsup_p : IsPGroup p ((P : Subgroup H) ⊔ K : Subgroup H) :=
    P.isPGroup'.to_sup_of_normal_left' hK_p hK_le_normalizer
  have hsup_eq : (P : Subgroup H) ⊔ K = (P : Subgroup H) :=
    P.is_maximal' hsup_p le_sup_left
  have hK_le_P : K ≤ (P : Subgroup H) := by
    rw [← hsup_eq]
    exact le_sup_right
  have hK_card : Nat.card K = Nat.card (P : Subgroup H) := by
    exact Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hK_eq : K = (P : Subgroup H) :=
    Subgroup.eq_of_le_of_card_ge hK_le_P (by rw [hK_card])
  rw [← Subgroup.conjAct_pointwise_smul_iff]
  change K = (P : Subgroup H)
  exact hK_eq


/-- A nonidentity element of a cyclic split torus can only lie in the split
component of the II.8.5 partition. Exact split order then identifies that
component with the original torus. -/
private theorem h821_split_partition_seed
    {G : Type u} [Group G] [Finite G]
    (P U S T₀ B : Subgroup G)
    (hpartition : ∀ x : G, x ≠ 1 →
      ∃! A : Subgroup G, x ∈ A ∧
        ((∃ g, A = P.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, A = U.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, A = S.map (MulAut.conj g).toMonoidHom)))
    (hT₀cyclic : IsCyclic T₀) (hT₀B : T₀ ≤ B)
    (hP_T₀_coprime : Nat.Coprime (Nat.card P) (Nat.card T₀))
    (hT₀_U_card : Nat.card T₀ = Nat.card U)
    (hT₀_S_coprime : Nat.Coprime (Nat.card T₀) (Nat.card S))
    {x : G} (hx : x ≠ 1) (hxT₀ : x ∈ T₀) :
    ∃ A : Subgroup G, x ∈ A ∧
      ((∃ g, A = P.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, A = U.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, A = S.map (MulAut.conj g).toMonoidHom)) ∧
      A ≤ B ∧ Nat.card A = Nat.card T₀ := by
  let Family : Subgroup G → Prop := fun A =>
    (∃ g, A = P.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g, A = U.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g, A = S.map (MulAut.conj g).toMonoidHom)
  have hpartition' : ∀ y : G, y ≠ 1 →
      ∃! A : Subgroup G, y ∈ A ∧ Family A := by
    simpa [Family] using hpartition
  obtain ⟨A, hxA, hAfamily⟩ := (hpartition' x hx).exists
  have hT₀_le_A : T₀ ≤ A :=
    cyclic_le_unique_partition_family Family hpartition'
      hx hxA hAfamily hxT₀ hT₀cyclic
  rcases hAfamily with ⟨g, hAg⟩ | ⟨g, hAg⟩ | ⟨g, hAg⟩
  · exfalso
    have hcop : Nat.Coprime (Nat.card T₀) (Nat.card A) := by
      rw [hAg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hP_T₀_coprime.symm
    exact hx (hmem_eq_one_of_coprime_card T₀ A hcop
      hxT₀ (hT₀_le_A hxT₀))
  · have hcard : Nat.card T₀ = Nat.card A := by
      rw [hAg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hT₀_U_card
    have hT₀_eq_A : T₀ = A :=
      Subgroup.eq_of_le_of_card_ge hT₀_le_A (by rw [hcard])
    refine ⟨A, hxA, Or.inr (Or.inl ⟨g, hAg⟩), ?_, hcard.symm⟩
    rw [← hT₀_eq_A]
    exact hT₀B
  · exfalso
    have hcop : Nat.Coprime (Nat.card T₀) (Nat.card A) := by
      rw [hAg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hT₀_S_coprime
    exact hx (hmem_eq_one_of_coprime_card T₀ A hcop
      hxT₀ (hT₀_le_A hxT₀))


set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The Sylow-normalizer part of Huppert II.8.22, with the nontrivial
boundary from II.8.21 made explicit. -/
public theorem huppert_II_8_22_sylow_normalizer_shape
    {F : Type u} [Field F] [Finite F] {p f m r : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m)
    (Z : Fin r → Subgroup H)
    (_hcyclic : ∀ i, IsCyclic (Z i))
    (_hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (_hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i)
    (hrepresentative : ∀ W : Subgroup H,
      IsCyclic W → 1 < Nat.card W →
      Nat.Coprime p (Nat.card W) →
      (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
      ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom) :
    1 < p ^ m →
      (Nat.card (Subgroup.normalizer (P : Set H)) = p ^ m ∨
        ∃ i, Nat.card (Subgroup.normalizer (P : Set H)) =
          p ^ m * Nat.card (Z i)) := by
  classical
  intro hPcard_gt
  have hP_ne_bot : (P : Subgroup H) ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hPcard]
    exact hPcard_gt
  let N : Subgroup H := Subgroup.normalizer (P : Set H)
  have hN : N = Subgroup.normalizer (P : Set H) := rfl
  have hP_le_N : (P : Subgroup H) ≤ N := Subgroup.le_normalizer
  let PN : Subgroup N := (P : Subgroup H).subgroupOf N
  let : PN.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (by
      simp [N])
  obtain ⟨hquotient_cyclic, hquotient_card_dvd,
      _hNormalizer_fixedPointFree, U, T, embed, hembed, _hembed_conj,
      hU_comm, hT_cyclic, hTcard,
      _hT_fixedPointFree, hP_map_le_U, hB_le_normalizer, hB_conjugate_torus,
      hN_maps_B, hU_preimage, _hcoordinates⟩ :=
    h821_borel_quotient_data hFcard H P hP_ne_bot N hN PN rfl
  have hquotient_card_dvd_sub_one :
      Nat.card (N ⧸ PN) ∣ Nat.card F - 1 :=
    dvd_trans hquotient_card_dvd
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (Nat.card F - 1) 2))
  let P₀ : Sylow p (PSL2MatrixGroup F) := default
  obtain ⟨U₈₅, S₈₅, hU₈₅_cyclic, hU₈₅_card,
      hS₈₅_cyclic, hS₈₅_card, hpartition⟩ :=
    huppert_II_8_5_a_psl2_partition hFcard P₀
  let Family : Subgroup (PSL2MatrixGroup F) → Prop := fun A =>
    (∃ g, A = (P₀ : Subgroup (PSL2MatrixGroup F)).map
      (MulAut.conj g).toMonoidHom) ∨
    (∃ g, A = U₈₅.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g, A = S₈₅.map (MulAut.conj g).toMonoidHom)
  have hpartition' : ∀ x : PSL2MatrixGroup F, x ≠ 1 →
      ∃! A : Subgroup (PSL2MatrixGroup F), x ∈ A ∧ Family A := by
    simpa [Family] using hpartition
  have hP₀card :
      Nat.card (P₀ : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    obtain ⟨eP₀⟩ := huppert_II_8_2_a_sylow_equiv_additive hFcard P₀
    exact (Nat.card_congr eP₀.toEquiv).symm
  have hP₀_T_coprime :
      Nat.Coprime
        (Nat.card (P₀ : Subgroup (PSL2MatrixGroup F)))
        (Nat.card T) := by
    rw [hP₀card, hTcard]
    exact hq_coprime_split_order (Nat.card F) Nat.card_pos
  have hT_U₈₅_card : Nat.card T = Nat.card U₈₅ := by
    rw [hTcard, hU₈₅_card]
  have hT_S₈₅_coprime : Nat.Coprime (Nat.card T) (Nat.card S₈₅) := by
    rw [hTcard, hS₈₅_card]
    exact hsplit_nonsplit_order_coprime
      (Nat.card F) (Finite.one_lt_card (α := F))
  have hTcard_dvd : Nat.card T ∣ Nat.card F - 1 := by
    rw [hTcard]
    exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (Nat.card F - 1) 2)
  have hf_ne_zero : f ≠ 0 :=
    huppert_II_8_27_field_exponent_ne_zero hFcard
  have hp_dvd_cardF : p ∣ Nat.card F := by
    rw [hFcard]
    exact dvd_pow_self p hf_ne_zero
  have hp_not_dvd_cardF_sub_one : ¬ p ∣ Nat.card F - 1 := by
    intro hp_sub
    have hp_one : p ∣ 1 := by
      have h := Nat.dvd_sub hp_dvd_cardF hp_sub
      have hcard_pos : 0 < Nat.card F := Nat.card_pos
      have hsub : Nat.card F - (Nat.card F - 1) = 1 := by omega
      rwa [hsub] at h
    exact (Fact.out : p.Prime).not_dvd_one hp_one
  have hcop_p_cardF_sub_one : Nat.Coprime p (Nat.card F - 1) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      hp_not_dvd_cardF_sub_one
  have hPNcard : Nat.card PN = p ^ m := by
    calc
      Nat.card PN = Nat.card P :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hP_le_N).toEquiv
      _ = p ^ m := hPcard
  have hcomplement_maximal :
      ∀ C : Subgroup N, PN.IsComplement' C → IsCyclic C →
        let W : Subgroup H := C.map N.subtype
        W = ⊥ ∨
          (1 < Nat.card W ∧
            ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) := by
    intro C hcomp hC_cyclic
    let W : Subgroup H := C.map N.subtype
    have hovergroups :
        ∀ V : Subgroup H, IsCyclic V → W ≤ V → W ≠ ⊥ →
          V ≤ N ∧ Nat.Coprime (Nat.card PN) (Nat.card V) := by
      intro V hV_cyclic hWV hW_ne_bot
      obtain ⟨w, hw_ne⟩ :=
        Subgroup.ne_bot_iff_exists_ne_one.mp hW_ne_bot
      rcases w.property with ⟨c, hcC, hcw⟩
      have hc_ne : (c : H) ≠ 1 := by
        intro hc_one
        apply hw_ne
        apply Subtype.ext
        exact hcw.symm.trans hc_one
      have hc_not_U : embed (c : H) ∉ U := by
        intro hcU
        have hcPN : c ∈ PN := (hU_preimage c).mp hcU
        have hc_one : c = 1 :=
          Subgroup.disjoint_def.mp hcomp.disjoint hcPN hcC
        apply hc_ne
        simpa using congrArg Subtype.val hc_one
      obtain ⟨u, huU, hcuT⟩ :=
        hB_conjugate_torus (embed (c : H)) (hN_maps_B c) hc_not_U
      let T₀ : Subgroup (PSL2MatrixGroup F) :=
        T.map (MulAut.conj u).toMonoidHom
      have hT₀_cyclic : IsCyclic T₀ := by
        exact (MulEquiv.isCyclic
          (Subgroup.equivMapOfInjective T
            (MulAut.conj u).toMonoidHom
            (MulAut.conj u).injective)).mp hT_cyclic
      have hT₀card : Nat.card T₀ = Nat.card T :=
        Subgroup.card_map_of_injective (MulAut.conj u).injective
      have hT₀_le_B : T₀ ≤ U ⊔ T := by
        rw [Subgroup.map_le_iff_le_comap]
        intro t htT
        change u * t * u⁻¹ ∈ U ⊔ T
        exact (U ⊔ T).mul_mem
          ((U ⊔ T).mul_mem
            ((show U ≤ U ⊔ T from le_sup_left) huU)
            ((show T ≤ U ⊔ T from le_sup_right) htT))
          ((U ⊔ T).inv_mem ((show U ≤ U ⊔ T from le_sup_left) huU))
      have hP₀_T₀_coprime :
          Nat.Coprime
            (Nat.card (P₀ : Subgroup (PSL2MatrixGroup F)))
            (Nat.card T₀) := by
        rw [hT₀card]
        exact hP₀_T_coprime
      have hT₀_U₈₅_card : Nat.card T₀ = Nat.card U₈₅ := by
        rw [hT₀card]
        exact hT_U₈₅_card
      have hT₀_S₈₅_coprime :
          Nat.Coprime (Nat.card T₀) (Nat.card S₈₅) := by
        rw [hT₀card]
        exact hT_S₈₅_coprime
      have hc_embed_ne : embed (c : H) ≠ 1 := by
        intro hc_one
        apply hc_ne
        exact hembed (hc_one.trans (map_one embed).symm)
      obtain ⟨A, hcA, hAfamily, hA_le_B, hAcard⟩ :=
        h821_split_partition_seed
          (P₀ : Subgroup (PSL2MatrixGroup F)) U₈₅ S₈₅ T₀
          (U ⊔ T) hpartition hT₀_cyclic hT₀_le_B
          hP₀_T₀_coprime hT₀_U₈₅_card hT₀_S₈₅_coprime
          hc_embed_ne hcuT
      have hAfamily' : Family A := by
        simpa [Family] using hAfamily
      have hAcard_dvd : Nat.card A ∣ Nat.card F - 1 := by
        rw [hAcard, hT₀card]
        exact hTcard_dvd
      have hseed :
          ∃ x : H, x ∈ W ∧ x ≠ 1 ∧ embed x ∈ A := by
        refine ⟨(c : H), ?_, hc_ne, hcA⟩
        exact Subgroup.mem_map_of_mem N.subtype hcC
      obtain ⟨hVmap_le_A, hVcard_dvd⟩ :=
        h821_cyclic_overgroup_partition_component
          Family hpartition' embed hembed W A (Nat.card F - 1)
          hseed hAfamily' hAcard_dvd V hV_cyclic hWV
      have hV_le_N : V ≤ N := by
        intro y hyV
        rw [hN]
        apply sylow_mem_normalizer_of_embed_mem_normalizer
          embed hembed P U (U ⊔ T) hU_comm hP_map_le_U
          hB_le_normalizer y
        exact hA_le_B
          (hVmap_le_A (Subgroup.mem_map_of_mem embed hyV))
      have hcoprime_V :
          Nat.Coprime (Nat.card PN) (Nat.card V) := by
        rw [hPNcard]
        exact Nat.Coprime.of_dvd_right hVcard_dvd
          (hcop_p_cardF_sub_one.pow_left m)
      exact ⟨hV_le_N, hcoprime_V⟩
    exact h821_complement_maximal_of_overgroups_coprime N PN C hcomp
      hovergroups
  obtain ⟨W, hW_cyclic, hW_coprime, hW_boundary, hnormalizer_card⟩ :=
    h821_schur_zassenhaus_core hFcard H P hPcard N hN hP_le_N
      PN rfl hquotient_cyclic hquotient_card_dvd_sub_one hcomplement_maximal
  rcases hW_boundary with hW_bot | ⟨hW_card, hW_maximal⟩
  · left
    rw [hnormalizer_card, hPcard, hW_bot, Subgroup.card_bot, mul_one]
  · obtain ⟨i, g, hWrep⟩ :=
      hrepresentative W hW_cyclic hW_card hW_coprime hW_maximal
    right
    refine ⟨i, ?_⟩
    rw [hnormalizer_card, hPcard, hWrep,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]


end Dickson
end CFSG.Glauberman
