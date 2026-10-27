module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSCore
import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification
open scoped commutatorElement

private theorem lsck_mem_center_of_commutator_mem_center {G : Type*} [Group G]
    (hG : commutator G = ⊤) {g : G} (hc : ∀ x : G, ⁅g, x⁆ ∈ Subgroup.center G) :
    g ∈ Subgroup.center G := by
  have hmul : ∀ x y : G, ⁅g, x * y⁆ = ⁅g, x⁆ * ⁅g, y⁆ := by
    intro x y
    have hxc : x * ⁅g, y⁆ = ⁅g, y⁆ * x := Subgroup.mem_center_iff.mp (hc y) x
    have hcx : ⁅g, y⁆ * x⁻¹ = x⁻¹ * ⁅g, y⁆ := by
      calc ⁅g, y⁆ * x⁻¹ = x⁻¹ * (x * ⁅g, y⁆) * x⁻¹ := by group
        _ = x⁻¹ * (⁅g, y⁆ * x) * x⁻¹ := by rw [hxc]
        _ = x⁻¹ * ⁅g, y⁆ := by group
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    calc g * (x * y) * g⁻¹ * (x * y)⁻¹
        = g * x * (g⁻¹ * (g * y * g⁻¹ * y⁻¹)) * x⁻¹ := by group
      _ = g * x * g⁻¹ * (⁅g, y⁆ * x⁻¹) := by rw [commutatorElement_def]; group
      _ = g * x * g⁻¹ * (x⁻¹ * ⁅g, y⁆) := by rw [hcx]
      _ = g * x * g⁻¹ * x⁻¹ * (g * y * g⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
  have hinv : ∀ u : G, ⁅g, u⁻¹⁆ * ⁅g, u⁆ = 1 := by
    intro u
    have h := hmul u⁻¹ u
    rw [inv_mul_cancel, commutatorElement_one_right] at h
    exact h.symm
  have hpow : ∀ x : G, ⁅g, x⁆ = 1 := by
    intro x
    have hx : x ∈ commutator G := by rw [hG]; exact Subgroup.mem_top x
    change x ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ at hx
    rw [Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, -, b, -, rfl⟩ := hw
      have hp : ⁅g, a⁆ * ⁅g, b⁆ = ⁅g, b⁆ * ⁅g, a⁆ :=
        Subgroup.mem_center_iff.mp (hc b) _
      have hpi : ⁅g, a⁻¹⁆ = ⁅g, a⁆⁻¹ := eq_inv_of_mul_eq_one_left (hinv a)
      have hqi : ⁅g, b⁻¹⁆ = ⁅g, b⁆⁻¹ := eq_inv_of_mul_eq_one_left (hinv b)
      rw [commutatorElement_def a b, hmul, hmul, hmul, hpi, hqi]
      calc ⁅g, a⁆ * ⁅g, b⁆ * ⁅g, a⁆⁻¹ * ⁅g, b⁆⁻¹
          = ⁅g, b⁆ * ⁅g, a⁆ * ⁅g, a⁆⁻¹ * ⁅g, b⁆⁻¹ := by rw [hp]
        _ = 1 := by group
    | one => simp
    | mul x y _ _ hx hy => rw [hmul, hx, hy, one_mul]
    | inv x _ hx =>
      have := hinv x
      rw [hx, mul_one] at this
      exact this
  refine Subgroup.mem_center_iff.mpr fun x => ?_
  exact (commutatorElement_eq_one_iff_mul_comm.mp (hpow x)).symm

private def lsck_centralQuotientMap {K X : Type*} [Group K] [Group X] (ψ : K →* X)
    (hψ : Function.Surjective ψ) : K ⧸ Subgroup.center K →* X ⧸ Subgroup.center X :=
  QuotientGroup.map (Subgroup.center K) (Subgroup.center X) ψ
    (fun z hz => Subgroup.map_center_le_center hψ ⟨z, hz, rfl⟩)

private theorem lsck_centralQuotientMap_mk {K X : Type*} [Group K] [Group X] (ψ : K →* X)
    (hψ : Function.Surjective ψ) (k : K) :
    lsck_centralQuotientMap ψ hψ (QuotientGroup.mk k) = QuotientGroup.mk (ψ k) :=
  rfl

private theorem lsck_centralQuotientMap_bijective {K X : Type*} [Group K] [Group X]
    (hK : commutator K = ⊤) (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) : Function.Bijective (lsck_centralQuotientMap ψ hψ) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective a
    rw [lsck_centralQuotientMap_mk, QuotientGroup.eq_one_iff] at ha
    rw [QuotientGroup.eq_one_iff]
    refine lsck_mem_center_of_commutator_mem_center hK fun x => hker ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp ha (ψ x)).symm
  · intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, rfl⟩ := hψ y
    exact ⟨QuotientGroup.mk k, rfl⟩

private noncomputable def lsck_centralQuotientIso {K X : Type*} [Group K] [Group X]
    (hK : commutator K = ⊤) (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) : K ⧸ Subgroup.center K ≃* X ⧸ Subgroup.center X :=
  MulEquiv.ofBijective (lsck_centralQuotientMap ψ hψ)
    (lsck_centralQuotientMap_bijective hK ψ hψ hker)

private theorem lsck_centralQuotientIso_mk {K X : Type*} [Group K] [Group X]
    (hK : commutator K = ⊤) (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) (k : K) :
    lsck_centralQuotientIso hK ψ hψ hker (QuotientGroup.mk k) = QuotientGroup.mk (ψ k) :=
  rfl

theorem ggNbrLSideSL3WitnessCK {T : Type} [Group T] {E : Type} [Field E] [Finite E]
    (ψ : ↥(StatedSL 3 E) →* T) (hker : ψ.ker ≤ Subgroup.center ↥(StatedSL 3 E))
    (β : MulAut T) (N : GL (Fin 3) E)
    (hβ : ∀ s s' : ↥(StatedSL 3 E), (s' : GL (Fin 3) E) = N * s * N⁻¹ → β (ψ s) = ψ s')
    {J : Subgroup T} (hJ : ψ.range = J) (α : MulAut (↥J ⧸ Subgroup.center ↥J))
    (hα : GGNbrLSideInduces β J α) :
    GGInnDiagPSL3 (Nat.card E) (↥J ⧸ Subgroup.center ↥J) α := by
  let SL := Matrix.SpecialLinearGroup (Fin 3) E
  let eSL : SL ≃* ↥(StatedSL 3 E) := LowTwoRank.specialLinearGroupEquivStatedSL 3 E
  let ψ₀ : SL →* T := ψ.comp eSL.toMonoidHom
  have hψ₀ker : ψ₀.ker ≤ Subgroup.center SL := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have h2 : eSL g ∈ Subgroup.center ↥(StatedSL 3 E) := by
      apply hker
      rw [MonoidHom.mem_ker]
      show ψ (eSL g) = 1
      exact hg
    have h3 : eSL g ∈ (Subgroup.center SL).map (eSL : SL →* ↥(StatedSL 3 E)) := by
      rw [Subgroup.map_center_eq eSL]
      exact h2
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp h3
    rwa [eSL.injective hyg] at hy
  have hψ₀range : ψ₀.range = J := by
    change (ψ.comp eSL.toMonoidHom).range = J
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 eSL.surjective]
    simp only [Subgroup.map_top]
    exact hJ
  let ψ'' : SL →* ↥J :=
    MonoidHom.codRestrict ψ₀ J fun g => by
      rw [← hψ₀range]
      exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
  have hψ''surj : Function.Surjective ψ'' := by
    intro j
    have hj : (j : T) ∈ ψ₀.range := by rw [hψ₀range]; exact j.2
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hj
    exact ⟨g, Subtype.ext hg⟩
  have hker'' : ψ''.ker ≤ Subgroup.center SL := by
    intro g hg
    apply hψ₀ker
    rw [MonoidHom.mem_ker] at hg ⊢
    have hgT : (ψ'' g : T) = 1 := congrArg Subtype.val hg
    show (ψ'' g : T) = 1
    exact hgT
  have hperfect : commutator SL = ⊤ :=
    CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (K := E) (n := 3) (by norm_num)
  let eQ : (SL ⧸ Subgroup.center SL) ≃* (↥J ⧸ Subgroup.center ↥J) :=
    lsck_centralQuotientIso hperfect ψ'' hψ''surj hker''
  have hmap : (Subgroup.center SL).map (MulEquiv.refl SL) = scalars 3 E :=
    (Subgroup.map_center_eq (MulEquiv.refl SL)).trans (scalars_eq_center 3 E).symm
  let eSt : (SL ⧸ Subgroup.center SL) ≃* projectiveSL 3 E :=
    QuotientGroup.congr (Subgroup.center SL) (scalars 3 E) (MulEquiv.refl SL) hmap
  let e : (↥J ⧸ Subgroup.center ↥J) ≃* projectiveSL 3 E := eQ.symm.trans eSt
  have he_mk : ∀ g : SL, e (QuotientGroup.mk (ψ'' g)) = QuotientGroup.mk' (scalars 3 E) g := by
    intro g
    have h1 : eQ (QuotientGroup.mk g) = QuotientGroup.mk (ψ'' g) :=
      lsck_centralQuotientIso_mk hperfect ψ'' hψ''surj hker'' g
    show eSt (eQ.symm (QuotientGroup.mk (ψ'' g))) = QuotientGroup.mk' (scalars 3 E) g
    rw [← h1, MulEquiv.symm_apply_apply]
    change QuotientGroup.congr (Subgroup.center SL) (scalars 3 E) (MulEquiv.refl SL) hmap
        (QuotientGroup.mk' (Subgroup.center SL) g) = QuotientGroup.mk' (scalars 3 E) g
    rw [QuotientGroup.congr_mk']
    rfl
  refine ggInnDiagPSL3_of_conjAut_apply (F := E) (Q := Nat.card E) rfl e N ?_
  intro x
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g, rfl⟩ := hψ''surj j
  obtain ⟨j', hj'val, hj'α⟩ := hα (ψ'' g)
  have hconj_gl : (eSL (CatalogueBHigherLinearAction.slConjugation 3 E N g) : GL (Fin 3) E) =
      N * (eSL g : GL (Fin 3) E) * N⁻¹ := by
    have hcoe : ∀ x : SL, (eSL x : GL (Fin 3) E) = Matrix.SpecialLinearGroup.toGL x := by
      intro x
      apply Units.ext
      exact LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 E x
    rw [hcoe (CatalogueBHigherLinearAction.slConjugation 3 E N g), hcoe g,
      CatalogueBHigherLinearAction.toGL_slConjugation]
  have hβconj : β (ψ₀ g) = ψ₀ (CatalogueBHigherLinearAction.slConjugation 3 E N g) :=
    hβ (eSL g) (eSL (CatalogueBHigherLinearAction.slConjugation 3 E N g)) hconj_gl
  have hj'_eq : j' = ψ'' (CatalogueBHigherLinearAction.slConjugation 3 E N g) := by
    apply Subtype.ext
    rw [hj'val]
    exact hβconj
  rw [hj'α, hj'_eq, he_mk, he_mk]
  exact (conjAut_proj (n := 3) (K := E) N g).symm

end CFSG.StandardType

end
