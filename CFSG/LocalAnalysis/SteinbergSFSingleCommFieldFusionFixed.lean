module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionFrob
public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionFixedB

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixFF_ff8_aux_frob_diagTorus (k : ℕ) {g : antiSp K} (hg : g ∈ diagTorus K) :
    (frobAut K ^ k) g ∈ diagTorus K := by
  obtain ⟨r, s, hr, hs, hgl⟩ := hg
  refine ⟨r ^ 2 ^ k, s ^ 2 ^ k, pow_ne_zero _ hr, pow_ne_zero _ hs, ?_⟩
  have hm : mat ((frobAut K ^ k) g) = (mat g).map fun x => x ^ 2 ^ k :=
    FieldInvolution.mat_frobAut_pow k g
  have hg' : mat g = diagMat r s := hgl
  show mat ((frobAut K ^ k) g) = diagMat _ _
  rw [hm, hg']
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [diagMat, inv_pow, zero_pow (pow_ne_zero k two_ne_zero)]

theorem sixFF_ff8_aux_pull_conj {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹)
    {Y : Subgroup (antiSp K)} (hY : ∀ s ∈ Y, (frobAut K ^ m) s ∈ Y) :
    ∀ x ∈ pull φ Y, v₀ * x * v₀⁻¹ ∈ pull φ Y := by
  intro x hx
  obtain ⟨hxL, hφx⟩ := mem_pull.mp hx
  have h2 : v₀ * x * v₀⁻¹ = ((φ.symm ((frobAut K ^ m) (φ ⟨x, hxL⟩)) : L) : G) := by
    rw [hv ⟨x, hxL⟩]
  rw [h2]
  exact symm_mem_pull.mpr (hY _ hφx)

theorem sixFF_ff8_aux_conj_closure {g : G} {T : Set G} (hT : ∀ x ∈ T, g * x * g⁻¹ ∈ T) :
    ∀ x ∈ Subgroup.closure T, g * x * g⁻¹ ∈ Subgroup.closure T := by
  exact sixFF_ff3a_conj_closure fun x hx => Subgroup.subset_closure (hT x hx)

theorem sixFF_ff8_aux_hvt {v₀ : G} (hvc : v₀ ∈ centralizer ({t} : Set G)) :
    v₀ * t * v₀⁻¹ = t := by
  have hct : t * v₀ = v₀ * t := Subgroup.mem_centralizer_iff.mp hvc t (Set.mem_singleton t)
  rw [← hct, mul_inv_cancel_right]

theorem sixFF_ff8_aux_mem_normalizer_zpowers_sup {v₀ : G} (hvt : v₀ * t * v₀⁻¹ = t)
    {X : Subgroup G} (hX : ∀ x ∈ X, v₀ * x * v₀⁻¹ ∈ X) :
    v₀ ∈ normalizer ((zpowers t ⊔ X : Subgroup G) : Set G) := by
  apply RootAxisTwoCore.mem_normalizer_of_conj_le
  intro q hq
  have hZ : ∀ x ∈ zpowers t, v₀ * x * v₀⁻¹ ∈ zpowers t := by
    have hle : zpowers t ≤ (zpowers t).comap (MulAut.conj v₀).toMonoidHom := by
      rw [Subgroup.zpowers_le]
      show v₀ * t * v₀⁻¹ ∈ zpowers t
      rw [hvt]
      exact Subgroup.mem_zpowers t
    intro x hx
    exact hle hx
  exact RootAxisTwoCore.conj_mem_sup hZ hX hq

theorem sixFF_ff8_aux_conj_U {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹) (k : Axis) :
    ∀ x ∈ U φ k, v₀ * x * v₀⁻¹ ∈ U φ k :=
  sixFF_ff8_aux_pull_conj hv (Y := rootU K k) fun s hs =>
    (frobAut_pow_mem_iff (frobAut_mem_rootU_iff k) m s).mpr hs

theorem sixFF_ff8_aux_conj_A {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹) (k : Axis) :
    ∀ x ∈ A φ k, v₀ * x * v₀⁻¹ ∈ A φ k :=
  sixFF_ff8_aux_pull_conj hv (Y := rootA K k) fun s hs =>
    (frobAut_pow_mem_iff (frobAut_mem_rootA_iff k) m s).mpr hs

theorem sixFF_ff8_aux_conj_D {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹)
    (hvt : v₀ * t * v₀⁻¹ = t) (k : Axis) :
    ∀ x ∈ D φ t k, v₀ * x * v₀⁻¹ ∈ D φ t k := fun x hx =>
  FullCenter.conj_mem_pCore_map
    (sixFF_ff8_aux_mem_normalizer_zpowers_sup hvt (sixFF_ff8_aux_conj_U hv k)) hx

theorem sixFF_ff8_aux_conj_E {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹)
    (hvt : v₀ * t * v₀⁻¹ = t) (k : Axis) :
    ∀ x ∈ E φ t k, v₀ * x * v₀⁻¹ ∈ E φ t k := fun x hx =>
  FullCenter.conj_mem_pCore_map
    (sixFF_ff8_aux_mem_normalizer_zpowers_sup hvt (sixFF_ff8_aux_conj_A hv k)) hx

theorem sixFF_ff8_aux_conj_E0 {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹)
    (hvt : v₀ * t * v₀⁻¹ = t) : ∀ x ∈ E₀ φ t, v₀ * x * v₀⁻¹ ∈ E₀ φ t := fun x hx =>
  Subgroup.mem_inf.mpr ⟨sixFF_ff8_aux_conj_E hv hvt Axis.one x (Subgroup.mem_inf.mp hx).1,
    sixFF_ff8_aux_conj_E hv hvt Axis.two x (Subgroup.mem_inf.mp hx).2⟩

theorem sixFF_ff8_aux_conj_J0 {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹) :
    ∀ x ∈ J₀ φ, v₀ * x * v₀⁻¹ ∈ J₀ φ :=
  sixFF_ff8_aux_pull_conj hv (Y := diagTorus K) fun s hs =>
    sixFF_ff8_aux_frob_diagTorus m hs

theorem sixFF_ff8_aux_conj_F {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹)
    (hvt : v₀ * t * v₀⁻¹ = t) : ∀ x ∈ F φ t, v₀ * x * v₀⁻¹ ∈ F φ t := by
  apply sixFF_ff8_aux_conj_closure
  rintro x ⟨e, he, j, hj, rfl⟩
  simp only [Set.mem_setOf_eq]
  exact ⟨v₀ * e * v₀⁻¹, sixFF_ff8_aux_conj_E0 hv hvt e he, v₀ * j * v₀⁻¹,
    sixFF_ff8_aux_conj_J0 hv j hj, by group⟩

theorem sixFF_ff8_aux_conj_FD {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹)
    (hvt : v₀ * t * v₀⁻¹ = t) (k : Axis)
    (hF : ∀ x ∈ F φ t, v₀ * x * v₀⁻¹ ∈ F φ t) :
    ∀ x ∈ F φ t ⊓ D φ t k, v₀ * x * v₀⁻¹ ∈ F φ t ⊓ D φ t k := fun x hx =>
  Subgroup.mem_inf.mpr ⟨hF x (Subgroup.mem_inf.mp hx).1,
    sixFF_ff8_aux_conj_D hv hvt k x (Subgroup.mem_inf.mp hx).2⟩

theorem sixFF_ff8_aux_conj_Kc {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹)
    (hvt : v₀ * t * v₀⁻¹ = t) (k : Axis)
    (hF : ∀ x ∈ F φ t, v₀ * x * v₀⁻¹ ∈ F φ t) :
    ∀ x ∈ Kc φ t k, v₀ * x * v₀⁻¹ ∈ Kc φ t k := fun x hx =>
  RootAxisTwoCore.conj_mem_sup (sixFF_ff8_aux_conj_A hv k)
    (sixFF_ff8_aux_conj_FD hv hvt k hF) hx

theorem sixFF_ff8_aux_weyl_mat (k : Axis) :
    ∀ a b : Fin 4, mat (FullCenterWeyl.weylElt K k) a b = 0 ∨
      mat (FullCenterWeyl.weylElt K k) a b = 1 := by
  cases k <;> intro a b <;> fin_cases a <;> fin_cases b <;>
    simp [mat, FullCenterWeyl.glMat_weylElt, FullCenterWeyl.weylMat]

theorem sixFF_ff8_aux_w_conj {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹) (k : Axis) :
    v₀ * w φ k * v₀⁻¹ = w φ k := by
  have h := hv (φ.symm (FullCenterWeyl.weylElt K k))
  rw [MulEquiv.apply_symm_apply, FieldInvolution.frobAut_pow_eq_self m
    (sixFF_ff8_aux_weyl_mat k)] at h
  exact h.symm

theorem sixFF_ff8_aux_conj_Mw {v₀ : G} {a b : Axis} (hw : v₀ * w φ b * v₀⁻¹ = w φ b)
    (hM : ∀ x ∈ Mc φ t a, v₀ * x * v₀⁻¹ ∈ Mc φ t a) :
    ∀ x ∈ Mw φ t a b, v₀ * x * v₀⁻¹ ∈ Mw φ t a b := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hw' : v₀ * (w φ b)⁻¹ * v₀⁻¹ = (w φ b)⁻¹ := by
    rw [show v₀ * (w φ b)⁻¹ * v₀⁻¹ = (v₀ * w φ b * v₀⁻¹)⁻¹ by group, hw]
  refine Subgroup.mem_map.mpr ⟨v₀ * y * v₀⁻¹, hM y hy, ?_⟩
  show (w φ b)⁻¹ * (v₀ * y * v₀⁻¹) * (w φ b)⁻¹⁻¹ =
    v₀ * ((w φ b)⁻¹ * y * (w φ b)⁻¹⁻¹) * v₀⁻¹
  rw [inv_inv, show v₀ * ((w φ b)⁻¹ * y * w φ b) * v₀⁻¹ =
    (v₀ * (w φ b)⁻¹ * v₀⁻¹) * (v₀ * y * v₀⁻¹) * (v₀ * w φ b * v₀⁻¹) by group, hw', hw]

theorem sixFF_ff8_aux_conj_Mc {v₀ : G} {a : Axis}
    (hP0 : ∀ x ∈ P₀ φ t a, v₀ * x * v₀⁻¹ ∈ P₀ φ t a)
    (hJ0 : ∀ x ∈ J₀ φ, v₀ * x * v₀⁻¹ ∈ J₀ φ) :
    ∀ x ∈ Mc φ t a, v₀ * x * v₀⁻¹ ∈ Mc φ t a := by
  apply sixFF_ff8_aux_conj_closure
  rintro x ⟨p, hp, j, hj, rfl⟩
  simp only [Set.mem_setOf_eq]
  exact ⟨v₀ * p * v₀⁻¹, hP0 p hp, v₀ * j * v₀⁻¹, hJ0 j hj, by group⟩

theorem sixFF_ff8_aux_conj_P1 {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹)
    (hvt : v₀ * t * v₀⁻¹ = t) (i : Axis) : ∀ x ∈ P₁ φ t i, v₀ * x * v₀⁻¹ ∈ P₁ φ t i := fun x hx =>
  FullCenter.conj_mem_pCore_map
    (RootAxisTwoCore.mem_normalizer_of_conj_le (sixFF_ff8_aux_conj_D hv hvt i)) hx

theorem sixFF_ff8_aux_mem_En {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹)
    (hvt : v₀ * t * v₀⁻¹ = t) (k : Axis) : v₀ ∈ En φ t k :=
  Subgroup.mem_inf.mpr
    ⟨RootAxisTwoCore.mem_normalizer_of_conj_le (sixFF_ff8_aux_conj_E hv hvt k),
      RootAxisTwoCore.mem_normalizer_of_conj_le
        (sixFF_ff8_aux_conj_Kc hv hvt k (sixFF_ff8_aux_conj_F hv hvt))⟩

theorem sixFF_ff8_aux_conj_P2 {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹)
    (hvt : v₀ * t * v₀⁻¹ = t) (k : Axis) : ∀ x ∈ P₂ φ t k, v₀ * x * v₀⁻¹ ∈ P₂ φ t k := fun x hx =>
  FullCenter.conj_mem_pCore_map (sixFF_ff8_aux_mem_En hv hvt k) hx

theorem sixFF_ff8_aux_conj_P0 {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹)
    (hvt : v₀ * t * v₀⁻¹ = t) (i : Axis) : ∀ x ∈ P₀ φ t i, v₀ * x * v₀⁻¹ ∈ P₀ φ t i := fun x hx =>
  Subgroup.mem_inf.mpr
    ⟨sixFF_ff8_aux_conj_P1 hv hvt i x (Subgroup.mem_inf.mp hx).1,
      sixFF_ff8_aux_conj_P2 hv hvt i.swap x (Subgroup.mem_inf.mp hx).2⟩

theorem sixFF_ff8_aux_conj_Mhat {v₀ : G} {a b : Axis} (hw : v₀ * w φ b * v₀⁻¹ = w φ b)
    (hM : ∀ x ∈ Mc φ t a, v₀ * x * v₀⁻¹ ∈ Mc φ t a) :
    ∀ x ∈ Mhat φ t a b, v₀ * x * v₀⁻¹ ∈ Mhat φ t a b := fun x hx =>
  RootAxisTwoCore.conj_mem_sup hM (sixFF_ff8_aux_conj_Mw hw hM) hx

theorem sixFF_ff8_aux_conj_Dstar {v₀ : G} {a : Axis}
    (hMh : ∀ x ∈ Mhat φ t a a, v₀ * x * v₀⁻¹ ∈ Mhat φ t a a)
    (hK : ∀ x ∈ Kc φ t a.swap, v₀ * x * v₀⁻¹ ∈ Kc φ t a.swap) :
    ∀ x ∈ Dstar φ t a, v₀ * x * v₀⁻¹ ∈ Dstar φ t a := fun x hx =>
  RootAxisTwoCore.conj_mem_sup hMh hK hx

theorem sixFF_ff8_aux_conj_S {v₀ : G} {a : Axis}
    (h1 : ∀ x ∈ Mhat φ t a Axis.one, v₀ * x * v₀⁻¹ ∈ Mhat φ t a Axis.one)
    (h2 : ∀ x ∈ Mhat φ t a Axis.two, v₀ * x * v₀⁻¹ ∈ Mhat φ t a Axis.two) :
    ∀ x ∈ S φ t a, v₀ * x * v₀⁻¹ ∈ S φ t a := fun x hx =>
  RootAxisTwoCore.conj_mem_sup h1 h2 hx

theorem sixFF_ff8_aux_conj_bot (v₀ : G) :
    ∀ x ∈ (⊥ : Subgroup G), v₀ * x * v₀⁻¹ ∈ (⊥ : Subgroup G) := by
  intro x hx
  rw [Subgroup.mem_bot.mp hx]
  simp

theorem sixFF_ff8_aux_normal {m : ℕ} {v₀ : G}
    (hv : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹)
    (hvt : v₀ * t * v₀⁻¹ = t) : ∀ k : Fin 7, v₀ ∈ normalizer (ffSeries φ t i k : Set G) := by
  have hF := sixFF_ff8_aux_conj_F hv hvt
  have hMc := sixFF_ff8_aux_conj_Mc (sixFF_ff8_aux_conj_P0 hv hvt i) (sixFF_ff8_aux_conj_J0 hv)
  intro k
  fin_cases k
  · exact RootAxisTwoCore.mem_normalizer_of_conj_le (sixFF_ff8_aux_conj_bot v₀)
  · exact RootAxisTwoCore.mem_normalizer_of_conj_le (sixFF_ff8_aux_conj_U hv i)
  · exact RootAxisTwoCore.mem_normalizer_of_conj_le (sixFF_ff8_aux_conj_FD hv hvt i.swap hF)
  · exact RootAxisTwoCore.mem_normalizer_of_conj_le hMc
  · exact RootAxisTwoCore.mem_normalizer_of_conj_le
      (sixFF_ff8_aux_conj_Mhat (sixFF_ff8_aux_w_conj hv i) hMc)
  · exact RootAxisTwoCore.mem_normalizer_of_conj_le
      (sixFF_ff8_aux_conj_Dstar (sixFF_ff8_aux_conj_Mhat (sixFF_ff8_aux_w_conj hv i) hMc)
        (sixFF_ff8_aux_conj_Kc hv hvt i.swap hF))
  · exact RootAxisTwoCore.mem_normalizer_of_conj_le
      (sixFF_ff8_aux_conj_S (sixFF_ff8_aux_conj_Mhat (sixFF_ff8_aux_w_conj hv Axis.one) hMc)
        (sixFF_ff8_aux_conj_Mhat (sixFF_ff8_aux_w_conj hv Axis.two) hMc))

theorem sixFF_ff8 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hE : EmbConclusion φ t i) (hK : SixKConclusion φ t i) (f7 : FF7Concl φ t i) :
    FF8Concl n φ t i := by
  intro v₀ hv2 hvt hσ hn
  have hnorm : ∀ k : Fin 7, v₀ ∈ normalizer (ffSeries φ t i k : Set G) :=
    sixFF_ff8_aux_normal hσ (sixFF_ff8_aux_hvt hvt)
  exact ⟨hnorm, sixFF_ff8b hS hH hE hK f7 v₀ hv2 hvt hσ hn hnorm⟩

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
