module

public import CFSG.OddTranspositions.PartThree.Twelve.FiveDefs
public import CFSG.OddTranspositions.PartThree.Twelve.SixComponent
public import CFSG.OddTranspositions.PartThree.FiveReflection
import CFSG.OddTranspositions.PartThree.Twelve.Seven
import CFSG.OddTranspositions.PartThree.Twelve.Three
import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockFive
import CFSG.OddTranspositions.PartFour.Fourteen.FivePlane
import CFSG.OddTranspositions.PartThree.Nine.Setup

public section

namespace CFSG.OddTranspositions.PartFour.RootBlockFive

open CFSG.OddTranspositions.PartFour.FivePlane CFSG.OddTranspositions.PartFour.TableE1Five

private theorem reflQ_mul_eq_mk {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    (p q : Fin n → ZMod 5) :
    reflQ b p * reflQ b q = QuotientGroup.mk
      ((⟨refl b p, refl_mem_reflGroup p⟩ : reflGroup b) *
        ⟨refl b q, refl_mem_reflGroup q⟩) := by
  unfold reflQ
  rw [← QuotientGroup.mk_mul]

private theorem reflQ_mul_ne_one {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n)
    {p q : Fin n → ZMod 5} (hp : b p p = 1) (hq : b q q = 1)
    (hqp : q ≠ p) (hqp' : q ≠ -p) : reflQ b p * reflQ b q ≠ 1 := by
  intro h1
  rw [reflQ_mul_eq_mk] at h1
  have hc : ((⟨refl b p, refl_mem_reflGroup p⟩ : reflGroup b) *
      ⟨refl b q, refl_mem_reflGroup q⟩) ∈ Subgroup.center (reflGroup b) :=
    (QuotientGroup.eq_one_iff _).mp h1
  have h2 := coe_eq_of_mem_center hsym hnd hn hp hc
  rw [Subgroup.coe_mul] at h2
  rcases h2 with h2 | h2
  · have h3 : refl b p = refl b q := by
      have h4 := inv_eq_of_mul_eq_one_right h2
      rwa [refl_inv] at h4
    rcases (refl_eq_refl_iff hp hq).mp h3 with h5 | h5
    · exact hqp h5
    · exact hqp' h5
  · have h3 : refl b q = -refl b p := by
      calc refl b q = refl b p * (refl b p * refl b q) := by
            rw [← mul_assoc, refl_mul_self, one_mul]
        _ = refl b p * (-1 : GL (Fin n) (ZMod 5)) := by rw [h2]
        _ = -refl b p := mul_neg_one _
    exact refl_ne_neg_refl (b := b) (by omega) p q h3

theorem orderOf_reflQ_mul {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n)
    {p q : Fin n → ZMod 5} (hp : b p p = 1) (hq : b q q = 1)
    (hqp : q ≠ p) (hqp' : q ≠ -p) (hβ : b p q ≠ 0) :
    orderOf (reflQ b p * reflQ b q) = if b p q ^ 2 = 1 then 5 else 3 := by
  classical
  have hne := reflQ_mul_ne_one hsym hnd hn hp hq hqp hqp'
  by_cases hβ2 : b p q ^ 2 = 1
  · have hβ1 : b p q = 1 ∨ b p q = -1 := by
      revert hβ2
      generalize b p q = c
      revert c
      decide
    have hgl : ((⟨refl b p, refl_mem_reflGroup p⟩ : reflGroup b) *
        ⟨refl b q, refl_mem_reflGroup q⟩) ^ 5 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one]
      exact refl_mul_refl_pow_five hsym hp hq hβ1
    have hpow : (reflQ b p * reflQ b q) ^ 5 = 1 := by
      rw [reflQ_mul_eq_mk, ← QuotientGroup.mk_pow, hgl, QuotientGroup.mk_one]
    rw [if_pos hβ2]
    exact orderOf_eq_prime (hp := ⟨Nat.prime_five⟩) hpow hne
  · have hβ2' : b p q = 2 ∨ b p q = -2 := by
      revert hβ2 hβ
      generalize b p q = c
      revert c
      decide
    have hgl : ((⟨refl b p, refl_mem_reflGroup p⟩ : reflGroup b) *
        ⟨refl b q, refl_mem_reflGroup q⟩) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one]
      exact refl_mul_refl_pow_three hsym hp hq hβ2'
    have hpow : (reflQ b p * reflQ b q) ^ 3 = 1 := by
      rw [reflQ_mul_eq_mk, ← QuotientGroup.mk_pow, hgl, QuotientGroup.mk_one]
    rw [if_neg hβ2]
    exact orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) hpow hne

end CFSG.OddTranspositions.PartFour.RootBlockFive

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.OddTranspositions.PartFour.FivePlane CFSG.OddTranspositions.PartFour.RootBlockFive
  CFSG.OddTranspositions.PartFour.TableE1Five

variable {G : Type} [Group G] [Finite G] {D : Set G}

private def IsChartVec (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) {n : ℕ}
    {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    (φ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha) ≃*
      reflGroup b ⧸ Subgroup.center (reflGroup b)) (vec : G → (Fin n → ZMod 5)) : Prop :=
  ∀ z (hz : z ∈ commSet D hC.d), b (vec z) (vec z) = 1 ∧
    φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha)) = reflQ b (vec z)

private theorem exists_reflQ_preimage (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    {φ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha) ≃*
      reflGroup b ⧸ Subgroup.center (reflGroup b)}
    (hφ : ∀ g : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha),
      g ∈ imageClass hC ↔ ∃ h : reflGroup b, (h : GL (Fin n) (ZMod 5)) ∈ reflSet b ∧
        φ g = QuotientGroup.mk h) :
    ∀ z (hz : z ∈ commSet D hC.d), ∃ v : Fin n → ZMod 5,
      b v v = 1 ∧ φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha)) = reflQ b v := by
  intro z hz
  have hmem : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha) ∈ imageClass hC :=
    ⟨_, mem_DstarH_of_mem_commSet hC hα hz, rfl⟩
  obtain ⟨h, hhT, hφh⟩ := (hφ _).mp hmem
  obtain ⟨v, hv, hvh⟩ := mem_reflSet_iff.mp hhT
  refine ⟨v, hv, ?_⟩
  rw [hφh]
  unfold reflQ
  congr 1
  exact Subtype.ext hvh.symm

private noncomputable def chartVec (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) {n : ℕ}
    {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    {φ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha) ≃*
      reflGroup b ⧸ Subgroup.center (reflGroup b)}
    (hφ : ∀ g : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha),
      g ∈ imageClass hC ↔ ∃ h : reflGroup b, (h : GL (Fin n) (ZMod 5)) ∈ reflSet b ∧
        φ g = QuotientGroup.mk h) : G → (Fin n → ZMod 5) := by
  classical
  exact fun z => if hz : z ∈ commSet D hC.d then
    Classical.choose (exists_reflQ_preimage hC hα hφ z hz) else 0

private theorem chartVec_spec (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) {n : ℕ}
    {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    {φ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha) ≃*
      reflGroup b ⧸ Subgroup.center (reflGroup b)}
    (hφ : ∀ g : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha),
      g ∈ imageClass hC ↔ ∃ h : reflGroup b, (h : GL (Fin n) (ZMod 5)) ∈ reflSet b ∧
        φ g = QuotientGroup.mk h) :
    IsChartVec hC hα φ (chartVec hC hα hφ) := by
  intro z hz
  unfold chartVec
  rw [dif_pos hz]
  exact Classical.choose_spec (exists_reflQ_preimage hC hα hφ z hz)

private theorem exists_vec_of_model (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    {φ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha) ≃*
      reflGroup b ⧸ Subgroup.center (reflGroup b)}
    {vec : G → (Fin n → ZMod 5)}
    (hφ : ∀ g : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha),
      g ∈ imageClass hC ↔ ∃ h : reflGroup b, (h : GL (Fin n) (ZMod 5)) ∈ reflSet b ∧
        φ g = QuotientGroup.mk h)
    (hvec : IsChartVec hC hα φ vec)
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) :
    ∀ v, b v v = 1 → ∃ z ∈ commSet D hC.d, vec z = v ∨ vec z = -v := by
  intro v hv
  have hxmem : φ.symm (reflQ b v) ∈ imageClass hC := by
    refine (hφ _).mpr ⟨⟨refl b v, refl_mem_reflGroup v⟩, refl_mem_reflSet hv, ?_⟩
    rw [MulEquiv.apply_symm_apply]
    rfl
  obtain ⟨y, hyD, hyx⟩ := hxmem
  have hyG : (y : G) ∈ commSet D hC.d := by
    rw [← Nine.DalphaStar_eq_commSet hC hα]
    exact (mem_DstarH_iff hC).mp hyD
  have hspec := hvec (y : G) hyG
  rw [show (⟨(y : G), mem_Halpha_of_mem_commSet hC hα hyG⟩ : Halpha D hC.alpha) = y
    from Subtype.ext rfl] at hspec
  have h1 : reflQ b (vec (y : G)) = reflQ b v := by
    rw [← hspec.2, hyx, MulEquiv.apply_symm_apply]
  have h2 : refl b (vec (y : G)) = refl b v :=
    refl_eq_of_reflQ_eq hsym hnd hn hspec.1 h1
  rcases (refl_eq_refl_iff hspec.1 hv).mp h2 with h3 | h3
  · exact ⟨(y : G), hyG, Or.inl h3.symm⟩
  · refine ⟨(y : G), hyG, Or.inr ?_⟩
    rw [h3]
    exact (neg_neg (vec (y : G))).symm

private theorem eq_of_vec_of_model (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    {φ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha) ≃*
      reflGroup b ⧸ Subgroup.center (reflGroup b)}
    {vec : G → (Fin n → ZMod 5)} (hvec : IsChartVec hC hα φ vec)
    (hinj : Set.InjOn (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
      (DstarH hC)) :
    ∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d,
      vec z' = vec z ∨ vec z' = -vec z → z' = z := by
  intro z hz z' hz' h
  have hzD : (⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha) ∈ DstarH hC :=
    mem_DstarH_of_mem_commSet hC hα hz
  have hz'D : (⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩ : Halpha D hC.alpha) ∈ DstarH hC :=
    mem_DstarH_of_mem_commSet hC hα hz'
  have hR : reflQ b (vec z') = reflQ b (vec z) := by
    rcases h with h | h
    · rw [h]
    · rw [h]
      exact reflQ_neg (b := b) (vec z)
  have hφeq : φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩) =
      φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩) := by
    rw [(hvec z hz).2, (hvec z' hz').2]
    exact hR.symm
  exact (congrArg Subtype.val (hinj hzD hz'D (φ.injective hφeq))).symm

private theorem commute_iff_of_model (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    {φ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha) ≃*
      reflGroup b ⧸ Subgroup.center (reflGroup b)}
    {vec : G → (Fin n → ZMod 5)} (hvec : IsChartVec hC hα φ vec)
    (heqvec : ∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d,
      vec z' = vec z ∨ vec z' = -vec z → z' = z)
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) :
    ∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d, z ≠ z' →
      (Commute z z' ↔ b (vec z) (vec z') = 0) := by
  intro z hz z' hz' hzz'
  rw [commute_iff_commute_mk hC hMZ hα hz hz']
  have hc : ∀ a b : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha),
      Commute a b ↔ Commute (φ a) (φ b) :=
    fun a b => ⟨fun h => h.map φ, fun h => φ.injective (by rw [map_mul, map_mul]; exact h.eq)⟩
  rw [hc, (hvec z hz).2, (hvec z' hz').2]
  constructor
  · intro h
    rcases eq_perp_or_of_reflQ_comm hsym hnd hn (hvec z hz).1 (hvec z' hz').1 h with
      h0 | h0 | h0
    · exact h0
    · exact absurd (heqvec z hz z' hz' (Or.inl h0)) (Ne.symm hzz')
    · exact absurd (heqvec z hz z' hz' (Or.inr h0)) (Ne.symm hzz')
  · intro h
    exact reflQ_comm_of_perp hsym h

private theorem orderOf_mul_of_model (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}
    {φ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha) ≃*
      reflGroup b ⧸ Subgroup.center (reflGroup b)}
    {vec : G → (Fin n → ZMod 5)} (hvec : IsChartVec hC hα φ vec)
    (heqvec : ∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d,
      vec z' = vec z ∨ vec z' = -vec z → z' = z)
    (hcomm : ∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d, z ≠ z' →
      (Commute z z' ↔ b (vec z) (vec z') = 0))
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) :
    ∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d, z ≠ z' →
      b (vec z) (vec z') ≠ 0 → orderOf (z * z') = if b (vec z) (vec z') ^ 2 = 1 then 5 else 3 := by
  intro z hz z' hz' hzz' hβ
  set R := CFSG.solvableRadical (Halpha D hC.alpha) with hRdef
  have hp : b (vec z) (vec z) = 1 := (hvec z hz).1
  have hq : b (vec z') (vec z') = 1 := (hvec z' hz').1
  have hqp : vec z' ≠ vec z := fun h => hzz' (heqvec z hz z' hz' (Or.inl h)).symm
  have hqp' : vec z' ≠ -vec z := fun h => hzz' (heqvec z hz z' hz' (Or.inr h)).symm
  have hzD : (⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha) ∈ DstarH hC :=
    mem_DstarH_of_mem_commSet hC hα hz
  have hz'D : (⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩ : Halpha D hC.alpha) ∈ DstarH hC :=
    mem_DstarH_of_mem_commSet hC hα hz'
  have hnc : ¬ Commute (⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha)
      ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩ := by
    rintro hcon
    exact hβ ((hcomm z hz z' hz' hzz').mp (congrArg Subtype.val hcon.eq))
  have hcoe : orderOf ((⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha) *
      ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩) = orderOf (z * z') := by
    simpa using (Subgroup.orderOf_coe
      ((⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha) *
        ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩)).symm
  have hquot : orderOf (QuotientGroup.mk' R ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ *
      QuotientGroup.mk' R ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩) =
      orderOf ((⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha) *
        ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩) :=
    orderOf_mul_mk_eq (DstarH_isOddTransp hC) hMZ hzD hz'D hnc
  have hφord' : orderOf (φ (QuotientGroup.mk' R ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩) *
      φ (QuotientGroup.mk' R ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩)) =
      orderOf (QuotientGroup.mk' R ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ *
        QuotientGroup.mk' R ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩) := by
    rw [← map_mul, MulEquiv.orderOf_eq]
  have hφord : orderOf (QuotientGroup.mk' R ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ *
      QuotientGroup.mk' R ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩) =
      orderOf (reflQ b (vec z) * reflQ b (vec z')) := by
    rw [← (hvec z hz).2, ← (hvec z' hz').2]
    exact hφord'.symm
  calc orderOf (z * z')
      = orderOf ((⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha) *
          ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩) := hcoe.symm
    _ = orderOf (QuotientGroup.mk' R ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ *
          QuotientGroup.mk' R ⟨z', mem_Halpha_of_mem_commSet hC hα hz'⟩) := hquot.symm
    _ = orderOf (reflQ b (vec z) * reflQ b (vec z')) := hφord
    _ = if b (vec z) (vec z') ^ 2 = 1 then 5 else 3 :=
          orderOf_reflQ_mul hsym hnd hn hp hq hqp hqp' hβ

private theorem vec_conj_of_model (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) {n : ℕ}
    {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)} (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n)
    {φ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha) ≃*
      reflGroup b ⧸ Subgroup.center (reflGroup b)}
    {vec : G → (Fin n → ZMod 5)} (hvec : IsChartVec hC hα φ vec) :
    ∀ x ∈ commSet D hC.d, ∀ y ∈ commSet D hC.d,
      vec (x * y * x⁻¹) = vec y - (2 * b (vec y) (vec x)) • vec x ∨
        vec (x * y * x⁻¹) = -(vec y - (2 * b (vec y) (vec x)) • vec x) := by
  intro x hx y hy
  set R := CFSG.solvableRadical (Halpha D hC.alpha) with hRdef
  have hmem : x * y * x⁻¹ ∈ commSet D hC.d := by
    refine ⟨hC.setup.conj_mem x hy.1, ?_, ?_⟩
    · have h1 : Commute (x * y * x⁻¹) (x * hC.d * x⁻¹) :=
        hy.2.1.map (MulAut.conj x).toMonoidHom
      rwa [hx.2.1.eq, mul_inv_cancel_right] at h1
    · intro he
      apply hy.2.2
      have h1 : y = x⁻¹ * hC.d * x := by rw [← he]; group
      have h2 : x⁻¹ * hC.d * x = hC.d := by
        calc x⁻¹ * hC.d * x = x⁻¹ * (hC.d * x) := by rw [mul_assoc]
          _ = x⁻¹ * (x * hC.d) := by rw [← hx.2.1.eq]
          _ = hC.d := by group
      rw [h1, h2]
  have hspec := hvec (x * y * x⁻¹) hmem
  have hxs := hvec x hx
  have hys := hvec y hy
  have hconj : φ (QuotientGroup.mk' R
        ⟨x * y * x⁻¹, mem_Halpha_of_mem_commSet hC hα hmem⟩) =
      reflQ b (act (refl b (vec x)) (vec y)) := by
    rw [show (⟨x * y * x⁻¹, mem_Halpha_of_mem_commSet hC hα hmem⟩ : Halpha D hC.alpha) =
        ⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩ * ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩ *
          ⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩⁻¹ from Subtype.ext rfl]
    simp only [map_mul, map_inv]
    rw [hxs.2, hys.2, reflQ_conj hsym]
  have hrefl : reflQ b (vec (x * y * x⁻¹)) = reflQ b (act (refl b (vec x)) (vec y)) := by
    rw [← hspec.2]
    exact hconj
  have hnorm : b (act (refl b (vec x)) (vec y)) (act (refl b (vec x)) (vec y)) = 1 := by
    rw [isom_norm (refl_mem_isomGroup hsym (vec x)) (vec y), hys.1]
  have h2 := (refl_eq_refl_iff hspec.1 hnorm).mp
    (refl_eq_of_reflQ_eq hsym hnd hn hspec.1 hrefl)
  have hact : act (refl b (vec x)) (vec y) =
      vec y - (2 * b (vec y) (vec x)) • vec x := by
    rw [act_refl hxs.1]
    module
  rcases h2 with h | h
  · exact Or.inl (h.symm.trans hact)
  · have hp : vec (x * y * x⁻¹) = -act (refl b (vec x)) (vec y) := by
      rw [h]
      exact (neg_neg (vec (x * y * x⁻¹))).symm
    exact Or.inr (by rw [hp, hact])

theorem exists_fiveChart (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (h5 : IsFiveReflectionModel k ε π (imageClass hC)) : Nonempty (FiveChart hC (k + 1)) := by
  classical
  obtain ⟨b, hsym, hnd, hM⟩ := fischerModel_of_isFiveReflectionModel h5
  obtain ⟨φ, hφ⟩ := hM
  obtain ⟨s₀, hs₀⟩ := imageClass_nonempty hC
  have hne : rootBlock (imageClass hC) s₀ ≠ imageClass hC :=
    (subset_rootBlock_and_ne_of_isFiveReflectionModel (imageClass_isClass hC) hk h5 hs₀).2
  have hinj := injOn_mk_DstarH_of_rootBlock_ne hC hMZ hs₀ hne
  let vec := chartVec hC hα hφ
  have hvec : IsChartVec hC hα φ vec := chartVec_spec hC hα hφ
  have heqvec := eq_of_vec_of_model hC hα hvec hinj
  have hcomm := commute_iff_of_model hC hMZ hα hvec heqvec hsym hnd (by omega)
  have horder := orderOf_mul_of_model hC hMZ hα hvec heqvec hcomm hsym hnd (by omega)
  have hexists := exists_vec_of_model hC hα hφ hvec hsym hnd (by omega)
  refine ⟨{ b := b, hsym := hsym, hnd := hnd,
             vec := vec, norm_vec := fun z hz => (hvec z hz).1,
             exists_vec := hexists, eq_of_vec := heqvec, commute_iff := hcomm,
             orderOf_mul := horder, vec_conj := vec_conj_of_model hC hα hsym hnd (by omega) hvec }⟩

end CFSG.OddTranspositions.PartThree

end
