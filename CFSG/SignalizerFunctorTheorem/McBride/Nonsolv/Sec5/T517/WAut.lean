module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T517.Basic

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T517

variable {Γ : Type*} [Group Γ] [Finite Γ]

@[expose] noncomputable def autH (H : Subgroup Γ) : ↥H →* MulAut ↥(kOf H) :=
  (kOf H).normalizerMonoidHom.comp (Subgroup.inclusion (fun _ hx => mem_normalizer_kOf hx))

theorem autH_apply (H : Subgroup Γ) (x : ↥H) (k : ↥(kOf H)) :
    ((autH H x k : ↥(kOf H)) : Γ) = (x : Γ) * k * (x : Γ)⁻¹ := rfl

theorem autH_injective {H : Subgroup Γ} (hsol : sol H = ⊥) : Function.Injective (autH H) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : ∀ k : ↥(kOf H), (x : Γ) * k * (x : Γ)⁻¹ = k := fun k => by
    rw [← autH_apply, hx]
    rfl
  have h2 : (x : Γ) ∈ H ⊓ Subgroup.centralizer ((kOf H : Subgroup Γ) : Set Γ) := by
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    exact (mul_inv_eq_iff_eq_mul.mp (h1 ⟨k, hk⟩)).symm
  rw [centralizer_kOf_eq_bot hsol] at h2
  exact Subtype.ext (Subgroup.mem_bot.mp h2)

variable {p : ℕ} {H B : Subgroup Γ} {θ : Γ → Subgroup Γ}

@[expose] def ActsOn (J : Subgroup Γ) (w : Γ) (φ : MulAut ↥(kOf H)) : Prop :=
  ∀ j : ↥(kOf H), (j : Γ) ∈ J → ((φ j : ↥(kOf H)) : Γ) = w * j * w⁻¹

namespace Setting

variable (S : Setting p H B θ)

@[expose] noncomputable def thetaAut : (↥(lcal H) → ↥(thetaOf θ B)) →* MulAut ↥(kOf H) :=
  S.hK.ofFamily.comp (MonoidHom.pi fun J : ↥(lcal H) =>
    ((J : Subgroup Γ).normalizerMonoidHom.comp
      (Subgroup.inclusion (fun w hw => S.thetaOf_normalizes w hw J.1 J.2))).comp
      (Pi.evalMonoidHom (fun _ : ↥(lcal H) => ↥(thetaOf θ B)) J))

include S

theorem actsOn_thetaAut (w : ↥(lcal H) → ↥(thetaOf θ B)) {J : Subgroup Γ} (hJ : J ∈ lcal H) :
    ActsOn J (w ⟨J, hJ⟩ : Γ) (S.thetaAut w) := by
  rintro ⟨x, hxK⟩ hxJ
  have := S.hK.ofFamily_apply_of_mem (MonoidHom.pi (fun J : ↥(lcal H) =>
    ((J : Subgroup Γ).normalizerMonoidHom.comp
      (Subgroup.inclusion (fun w hw => S.thetaOf_normalizes w hw J.1 J.2))).comp
      (Pi.evalMonoidHom (fun _ : ↥(lcal H) => ↥(thetaOf θ B)) J)) w) hJ hxJ
  exact this

theorem eq_of_actsOn {J : Subgroup Γ} (hJ : J ∈ lcal H) {w w' : Γ} (hw : w ∈ thetaOf θ B)
    (hw' : w' ∈ thetaOf θ B) {φ : MulAut ↥(kOf H)} (h : ActsOn J w φ) (h' : ActsOn J w' φ) :
    w = w' := by
  have hx : w'⁻¹ * w = 1 := by
    refine S.eq_one_of_centralizes_one (mul_mem (inv_mem (S.thetaOf_le_H hw'))
      (S.thetaOf_le_H hw)) (mul_mem (inv_mem (S.thetaOf_le_centralizer hw'))
      (S.thetaOf_le_centralizer hw)) hJ fun j hj => ?_
    have e := (h ⟨j, S.hK.le hJ hj⟩ hj).symm.trans (h' ⟨j, S.hK.le hJ hj⟩ hj)
    calc w'⁻¹ * w * j = w'⁻¹ * (w * j * w⁻¹) * w := by group
      _ = w'⁻¹ * (w' * j * w'⁻¹) * w := by rw [e]
      _ = j * (w'⁻¹ * w) := by group
  exact (inv_mul_eq_one.mp hx).symm

theorem thetaAut_injective : Function.Injective S.thetaAut := by
  rw [injective_iff_map_eq_one]
  intro w hw
  funext J
  have h1 := S.actsOn_thetaAut w J.2
  have h1' : ActsOn J.1 (1 : Γ) (1 : MulAut ↥(kOf H)) := fun j _ => by simp
  rw [hw] at h1
  have := S.eq_of_actsOn J.2 (w J).2 (one_mem _) h1 h1'
  exact Subtype.ext this

theorem mem_range_thetaAut_iff {φ : MulAut ↥(kOf H)} :
    φ ∈ S.thetaAut.range ↔ ∀ J ∈ lcal H, ∃ w ∈ thetaOf θ B, ActsOn J w φ := by
  constructor
  · rintro ⟨w, rfl⟩ J hJ
    exact ⟨(w ⟨J, hJ⟩ : Γ), (w ⟨J, hJ⟩).2, S.actsOn_thetaAut w hJ⟩
  · intro h
    choose! f hfW hfA using h
    refine ⟨fun J => ⟨f J.1, hfW J.1 J.2⟩, ?_⟩
    apply S.hK.ext_of_forall_mem
    intro J hJ x hx
    apply Subtype.ext
    exact ((S.actsOn_thetaAut (fun J => ⟨f J.1, hfW J.1 J.2⟩) hJ) ⟨x, S.hK.le hJ hx⟩ hx).trans
      (hfA J hJ ⟨x, S.hK.le hJ hx⟩ hx).symm

theorem actsOn_autH_iff {J : Subgroup Γ} (hJ : J ∈ lcal H) {w : Γ} {x : ↥H} :
    ActsOn J w (autH H x) ↔ ∀ j ∈ J, (x : Γ) * j * (x : Γ)⁻¹ = w * j * w⁻¹ :=
  ⟨fun h j hj => h ⟨j, S.hK.le hJ hj⟩ hj, fun h j hj => h j hj⟩

theorem autH_mem_range_iff {x : ↥H} :
    autH H x ∈ S.thetaAut.range ↔ ∀ J ∈ lcal H, ∃ w ∈ thetaOf θ B,
      ∀ j ∈ J, (x : Γ) * j * (x : Γ)⁻¹ = w * j * w⁻¹ := by
  rw [S.mem_range_thetaAut_iff]
  refine forall_congr' fun J => forall_congr' fun hJ => exists_congr fun w =>
    and_congr_right fun _ => ?_
  exact S.actsOn_autH_iff hJ

theorem actsOn_conj {J : Subgroup Γ} {w : Γ} {φ : MulAut ↥(kOf H)} {b : Γ} (hb : b ∈ B)
    (hw : w ∈ thetaOf θ B)
    (h : ActsOn (J.map (MulAut.conj b⁻¹).toMonoidHom) w φ) :
    ActsOn J w (autH H ⟨b, S.le hb⟩ * φ * (autH H ⟨b, S.le hb⟩)⁻¹) := by
  intro j hj
  have hbw : Commute w b :=
    (Subgroup.mem_centralizer_iff.mp (S.thetaOf_le_centralizer hw) b hb).symm
  have hinv : (autH H ⟨b, S.le hb⟩)⁻¹ = autH H ⟨b⁻¹, inv_mem (S.le hb)⟩ := by
    rw [← map_inv]
    rfl
  have h1 := h ((autH H ⟨b⁻¹, inv_mem (S.le hb)⟩) j) ⟨j, hj, by simp [autH_apply]⟩
  show ((autH H ⟨b, S.le hb⟩ (φ ((autH H ⟨b, S.le hb⟩)⁻¹ j)) : ↥(kOf H)) : Γ) = _
  rw [hinv, autH_apply, h1, autH_apply]
  simp only [inv_inv]
  have e : b * (w * (b⁻¹ * (j : Γ) * b) * w⁻¹) * b⁻¹ = w * j * w⁻¹ := by
    calc b * (w * (b⁻¹ * (j : Γ) * b) * w⁻¹) * b⁻¹
        = (b * w) * (b⁻¹ * (j : Γ) * b) * (w⁻¹ * b⁻¹) := by group
      _ = (w * b) * (b⁻¹ * (j : Γ) * b) * (b⁻¹ * w⁻¹) := by
        rw [hbw.eq.symm, (hbw.inv_inv).eq]
      _ = w * j * w⁻¹ := by group
  exact e

end Setting

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T517
