module

public import CFSG.RankThree.PartOne.CTP.IStd
public import CFSG.RankThree.PartOne.KF.LayerCover

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.LocalCores CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU

variable {G : Type} [Group G] [Finite G]

theorem conjBy_perfectResidual (w : G) (Y : Subgroup G) :
    conjBy w (inSubgroup perfectResidual Y) = inSubgroup perfectResidual (conjBy w Y) :=
  map_inSubgroup_perfectResidual (MulAut.conj w).toMonoidHom Y

theorem pairLayer_conjBy (w : G) (I BK Jab : Subgroup G) :
    conjBy w (pairLayer I BK Jab) = pairLayer (conjBy w I) (conjBy w BK) (conjBy w Jab) := by
  unfold pairLayer
  rw [conjBy_perfectResidual]
  congr 1
  have hinf : ∀ X Y : Subgroup G, conjBy w (X ⊓ Y) = conjBy w X ⊓ conjBy w Y := fun X Y => by
    unfold conjBy
    exact Subgroup.map_inf _ _ _ (MulAut.conj w).injective
  rw [hinf, ← Equivariance.centralizer_conjBy, hinf, ← Equivariance.centralizer_conjBy]

omit [Finite G] in
@[expose] noncomputable def conjEquiv (w : G) (X : Subgroup G) : ↥X ≃* ↥(conjBy w X) :=
  X.equivMapOfInjective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective

omit [Finite G] in
theorem coe_conjEquiv (w : G) (X : Subgroup G) (x : ↥X) :
    ((conjEquiv w X x : ↥(conjBy w X)) : G) = w * (x : G) * w⁻¹ := rfl

omit [Finite G] in
theorem conjBy_centralizer_singleton {w c : G} (h : w * c = c * w) :
    conjBy w (Subgroup.centralizer ({c} : Set G)) = Subgroup.centralizer ({c} : Set G) := by
  have hc : w * c * w⁻¹ = c := by rw [h]; group
  ext x
  rw [Equivariance.mem_conjBy, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  have e1 : (w⁻¹ * x * w) * c = w⁻¹ * (x * c) * w := by
    calc (w⁻¹ * x * w) * c = w⁻¹ * (x * (w * c * w⁻¹)) * w := by group
      _ = w⁻¹ * (x * c) * w := by rw [hc]
  have e2 : c * (w⁻¹ * x * w) = w⁻¹ * (c * x) * w := by
    calc c * (w⁻¹ * x * w) = w⁻¹ * ((w * c * w⁻¹) * x) * w := by group
      _ = w⁻¹ * (c * x) * w := by rw [hc]
  rw [e1, e2]
  constructor
  · intro h'
    exact mul_left_cancel (mul_right_cancel h')
  · intro h'
    rw [h']

omit [Finite G] in
theorem coe_conjEquiv_symm (w : G) (X : Subgroup G) (x : ↥(conjBy w X)) :
    (((conjEquiv w X).symm x : ↥X) : G) = w⁻¹ * (x : G) * w := by
  have h := congrArg Subtype.val ((conjEquiv w X).apply_symm_apply x)
  rw [coe_conjEquiv] at h
  rw [← h]
  group

theorem IConfig.conj {c : G} {f₀ : ℕ} {I K BK : Subgroup G} {J : Fin 3 → Fin 3 → Subgroup G}
    (h : IConfig c f₀ I K BK J) (w : G) (hwc : w * c = c * w) :
    IConfig c f₀ (conjBy w I) (conjBy w K) (conjBy w BK) (fun a b => conjBy w (J a b)) := by
  have hcw : w⁻¹ * c * w = c := by
    calc w⁻¹ * c * w = w⁻¹ * (c * w) := by group
      _ = w⁻¹ * (w * c) := by rw [hwc]
      _ = c := by group
  have hperf := h.perfect
  refine ⟨h.f_two, h.dvd5, h.ndvd25, ?_, ?_, ?_, h.c_pow, ?_, ?_, ?_, ?_⟩
  ·
    have e : ↥I ≃* ↥(conjBy w I) := conjEquiv w I
    exact Equivariance.statedClassicalModel_of_mulEquiv
      (QuotientGroup.congr (Subgroup.center ↥I) (Subgroup.center ↥(conjBy w I)) e
        (Subgroup.map_center_eq e)) h.model
  ·
    exact Group.IsPerfect.ofSurjective (f := (conjEquiv w I).toMonoidHom)
      (conjEquiv w I).surjective
  ·
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Equivariance.mem_conjBy, Equivariance.mem_conjBy]
    have e : w⁻¹ * (c * x * c⁻¹) * w = c * (w⁻¹ * x * w) * c⁻¹ := by
      calc w⁻¹ * (c * x * c⁻¹) * w = (w⁻¹ * c * w) * (w⁻¹ * x * w) * (w⁻¹ * c * w)⁻¹ := by group
        _ = c * (w⁻¹ * x * w) * c⁻¹ := by rw [hcw]
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp h.c_norm (w⁻¹ * x * w))
  ·
    intro hc
    apply h.c_outer
    rw [Equivariance.centralizer_conjBy] at hc
    have hsup : conjBy w I ⊔ conjBy w (Subgroup.centralizer (I : Set G)) =
        conjBy w (I ⊔ Subgroup.centralizer (I : Set G)) := (Subgroup.map_sup _ _ _).symm
    rw [hsup, Equivariance.mem_conjBy, hcw] at hc
    exact hc
  ·
    rw [h.K_eq, conjBy_perfectResidual]
    congr 1
    have hinf : conjBy w (I ⊓ Subgroup.centralizer ({c} : Set G)) =
        conjBy w I ⊓ conjBy w (Subgroup.centralizer ({c} : Set G)) := by
      unfold conjBy
      exact Subgroup.map_inf _ _ _ (MulAut.conj w).injective
    rw [hinf, conjBy_centralizer_singleton hwc]
  · exact Subgroup.map_mono h.K_le
  ·
    obtain ⟨Kq, _, hKq, φ, hJ, hBK, hBKφ⟩ := h.triangle
    refine ⟨Kq, inferInstance, hKq, (conjEquiv w K).symm.trans φ, ?_, ?_, ?_⟩
    · intro a b hab
      obtain ⟨hle, hiff⟩ := hJ a b hab
      refine ⟨Subgroup.map_mono hle, fun x => ?_⟩
      have hy := coe_conjEquiv_symm w K x
      have h1 := hiff ((conjEquiv w K).symm x)
      rw [hy] at h1
      rw [Equivariance.mem_conjBy]
      exact h1
    · exact Subgroup.map_mono hBK
    · intro x
      have hy := coe_conjEquiv_symm w K x
      have h1 := hBKφ ((conjEquiv w K).symm x)
      rw [hy] at h1
      rw [Equivariance.mem_conjBy]
      exact h1

end CFSG.RankThree.PartOne.CTP
