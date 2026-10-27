module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F6SQTK

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S153Q

namespace Q5

section Transfer

variable {A B : Type*} [Group A] [Group B]

theorem isQuasisimple_of_mulEquiv (e : A ≃* B) (hA : CFSG.Open.IsQuasisimple A) :
    CFSG.Open.IsQuasisimple B :=
  hA.of_mulEquiv e.symm

theorem isHatAlt_of_mulEquiv {n : ℕ} (e : A ≃* B) (h : F6.IsHatAlt n A) : F6.IsHatAlt n B := by
  obtain ⟨hq, hc, ⟨f⟩⟩ := h
  have hmap : (Subgroup.center A).map (e : A →* B) = Subgroup.center B := Subgroup.map_center_eq e
  refine ⟨isQuasisimple_of_mulEquiv e hq, ?_, ⟨(QuotientGroup.congr _ _ e hmap).symm.trans f⟩⟩
  rw [← hmap, Subgroup.card_map_of_injective e.injective, hc]

theorem isHatSym_of_mulEquiv {n : ℕ} (e : A ≃* B) (h : F6.IsHatSym n A) : F6.IsHatSym n B := by
  obtain ⟨φ, hφ, hk, hA⟩ := h
  refine ⟨φ.comp e.symm.toMonoidHom, hφ.comp e.symm.surjective, ?_, ?_⟩
  · have hker : (φ.comp e.symm.toMonoidHom).ker = φ.ker.map (e : A →* B) := by
      ext b
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_map]
      constructor
      · intro hb
        exact ⟨e.symm b, hb, by simp⟩
      · rintro ⟨a, ha, rfl⟩
        simpa using ha
    rw [hker, Subgroup.card_map_of_injective e.injective, hk]
  · have hcomap : (alternatingGroup (Fin n)).comap (φ.comp e.symm.toMonoidHom) =
        ((alternatingGroup (Fin n)).comap φ).map (e : A →* B) := by
      ext b
      simp only [Subgroup.mem_comap, MonoidHom.comp_apply, Subgroup.mem_map]
      constructor
      · intro hb
        exact ⟨e.symm b, hb, by simp⟩
      · rintro ⟨a, ha, rfl⟩
        simpa using ha
    rw [hcomap]
    exact isHatAlt_of_mulEquiv (e.subgroupMap _) hA

end Transfer

section Action

variable {G : Type*} [Group G] {I V₀ : Subgroup G}

noncomputable def kappa (I V₀ : Subgroup G)
    (h : I ≤ Subgroup.normalizer (V₀ : Set G)) : ↥I →* MulAut ↥V₀ :=
  (conjAct V₀).comp (Subgroup.inclusion h)

theorem kappa_apply_coe (h : I ≤ Subgroup.normalizer (V₀ : Set G)) (x : ↥I) (v : ↥V₀) :
    ((kappa I V₀ h x v : ↥V₀) : G) = (x : G) * v * (x : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V₀ (Subgroup.inclusion h x) v

theorem kappa_inv_apply_coe (h : I ≤ Subgroup.normalizer (V₀ : Set G)) (x : ↥I) (v : ↥V₀) :
    ((((kappa I V₀ h x)⁻¹ : MulAut ↥V₀) v : ↥V₀) : G) = (x : G)⁻¹ * v * (x : G) := by
  rw [← map_inv, kappa_apply_coe]
  simp

theorem ker_kappa (h : I ≤ Subgroup.normalizer (V₀ : Set G)) :
    (kappa I V₀ h).ker = (I ⊓ Subgroup.centralizer (V₀ : Set G)).subgroupOf I := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hk
    refine ⟨a.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h2 := congrArg (fun φ : MulAut ↥V₀ => ((φ ⟨v, hv⟩ : ↥V₀) : G)) hk
    simp only [kappa_apply_coe, MulAut.one_apply] at h2
    calc v * (a : G) = ((a : G) * v * (a : G)⁻¹) * a := by rw [h2]
      _ = a * v := by group
  · rintro ⟨-, hc⟩
    ext v
    rw [kappa_apply_coe, MulAut.one_apply]
    have hv := Subgroup.mem_centralizer_iff.mp hc v v.2
    rw [← hv, mul_inv_cancel_right]

theorem exists_quotEquiv (h : I ≤ Subgroup.normalizer (V₀ : Set G)) (Q : Subgroup ↥I) [Q.Normal]
    (hQ : (kappa I V₀ h).ker = Q) :
    ∃ e : ↥I ⧸ Q ≃* ↥(kappa I V₀ h).range,
      ∀ x : ↥I, ((e (QuotientGroup.mk x) : ↥(kappa I V₀ h).range) : MulAut ↥V₀) = kappa I V₀ h x :=
  ⟨(QuotientGroup.quotientMulEquivOfEq hQ.symm).trans
    (QuotientGroup.quotientKerEquivRange (kappa I V₀ h)), fun _ => rfl⟩

end Action

end Q5

end S153Q

end CFSG.Quasithin
