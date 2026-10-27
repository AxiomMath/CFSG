module

public import CFSG.Quasithin.Background.HSecTransfer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H
open scoped IsMulCommutative

namespace Sec121

variable {G : Type} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  simp only [CFSG.conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by group⟩

theorem le_normalizer_conjugate {L V₀ : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (L : Set G)) (hL : L ≤ Subgroup.normalizer (V₀ : Set G)) :
    L ≤ Subgroup.normalizer (CFSG.conjugate V₀ t : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_conjugate_iff, mem_conjugate_iff]
  have hl' : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp ht l).mp hl
  have h := Subgroup.mem_normalizer_iff.mp (hL hl') (t * x * t⁻¹)
  rwa [show t * l * t⁻¹ * (t * x * t⁻¹) * (t * l * t⁻¹)⁻¹ = t * (l * x * l⁻¹) * t⁻¹ by group]
    at h

theorem isMulCommutative_conjugate (V₀ : Subgroup G) [IsMulCommutative ↥V₀] (t : G) :
    IsMulCommutative ↥(CFSG.conjugate V₀ t) := by
  unfold CFSG.conjugate
  infer_instance

theorem irr_conjugate {L V₀ : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (L : Set G))
    (hirr : ∀ J : Subgroup G, J ≤ V₀ → L ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = V₀) :
    ∀ J : Subgroup G, J ≤ CFSG.conjugate V₀ t → L ≤ Subgroup.normalizer (J : Set G) →
      J = ⊥ ∨ J = CFSG.conjugate V₀ t := by
  intro J hJ hLJ
  have ht' : t⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ ht
  have hJ' : CFSG.conjugate J t⁻¹ ≤ V₀ := fun x hx => by
    have h1 := hJ (mem_conjugate_iff.mp hx)
    rw [mem_conjugate_iff] at h1
    simpa [mul_assoc] using h1
  rcases hirr _ hJ' (le_normalizer_conjugate ht' hLJ) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have h1 : t * x * t⁻¹ ∈ CFSG.conjugate J t⁻¹ := by
      rw [mem_conjugate_iff]
      simpa [mul_assoc] using hx
    rw [h, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
      _ = 1 := by rw [h1]; group
  · right
    apply le_antisymm hJ
    intro x hx
    have h1 : t * x * t⁻¹ ∈ CFSG.conjugate J t⁻¹ := h ▸ mem_conjugate_iff.mp hx
    rw [mem_conjugate_iff] at h1
    simpa [mul_assoc] using h1

@[expose] noncomputable def conjEquiv (V₀ : Subgroup G) (t : G) :
    ↥(CFSG.conjugate V₀ t) ≃* ↥V₀ where
  toFun w := ⟨t * w * t⁻¹, mem_conjugate_iff.mp w.2⟩
  invFun v := ⟨t⁻¹ * v * t, mem_conjugate_iff.mpr (by
    rw [show t * (t⁻¹ * (v : G) * t) * t⁻¹ = v by group]
    exact v.2)⟩
  left_inv w := Subtype.ext (by
    change t⁻¹ * (t * (w : G) * t⁻¹) * t = w
    group)
  right_inv v := Subtype.ext (by
    change t * (t⁻¹ * (v : G) * t) * t⁻¹ = v
    group)
  map_mul' a b := Subtype.ext (by
    change t * ((a : G) * b) * t⁻¹ = t * a * t⁻¹ * (t * b * t⁻¹)
    group)

theorem coe_conjEquiv (V₀ : Subgroup G) (t : G) (w : ↥(CFSG.conjugate V₀ t)) :
    ((conjEquiv V₀ t w : ↥V₀) : G) = t * w * t⁻¹ :=
  rfl

theorem congr_conjAct {V₀ : Subgroup G} {t : G}
    (g : Subgroup.normalizer (CFSG.conjugate V₀ t : Set G))
    (hg : t * (g : G) * t⁻¹ ∈ Subgroup.normalizer (V₀ : Set G)) :
    MulAut.congr (conjEquiv V₀ t) (conjAct (CFSG.conjugate V₀ t) g) =
      conjAct V₀ ⟨t * (g : G) * t⁻¹, hg⟩ := by
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  change ((conjEquiv V₀ t (conjAct (CFSG.conjugate V₀ t) g ((conjEquiv V₀ t).symm v)) : ↥V₀) :
    G) = _
  rw [coe_conjEquiv, Setup.coe_conjAct_apply, Setup.coe_conjAct_apply]
  change t * ((g : G) * (t⁻¹ * (v : G) * t) * (g : G)⁻¹) * t⁻¹ = _
  group

theorem map_congr_autOn {L V₀ : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (L : Set G))
    (hL : L ≤ Subgroup.normalizer (V₀ : Set G)) :
    (autOn L (CFSG.conjugate V₀ t)).map (MulAut.congr (conjEquiv V₀ t)).toMonoidHom =
      autOn L V₀ := by
  ext f
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨g, hgL, rfl⟩ := Setup.mem_autOn_iff.mp hh
    have hgL' : t * (g : G) * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp ht _).mp hgL
    rw [MulEquiv.coe_toMonoidHom, congr_conjAct g (hL hgL')]
    exact Setup.mem_autOn_iff.mpr ⟨_, hgL', rfl⟩
  · intro hf
    obtain ⟨g, hgL, rfl⟩ := Setup.mem_autOn_iff.mp hf
    have ht' : t⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ ht
    have hgL' : t⁻¹ * (g : G) * t⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp ht' _).mp hgL
    rw [inv_inv] at hgL'
    have hgN : t⁻¹ * (g : G) * t ∈ Subgroup.normalizer (CFSG.conjugate V₀ t : Set G) :=
      le_normalizer_conjugate ht hL hgL'
    have h1 : t * (t⁻¹ * (g : G) * t) * t⁻¹ = g := by group
    have hg2 : t * ((⟨_, hgN⟩ : Subgroup.normalizer (CFSG.conjugate V₀ t : Set G)) : G) * t⁻¹ ∈
        Subgroup.normalizer (V₀ : Set G) := by
      rw [show ((⟨_, hgN⟩ : Subgroup.normalizer (CFSG.conjugate V₀ t : Set G)) : G) =
        t⁻¹ * (g : G) * t from rfl, h1]
      exact g.2
    refine ⟨conjAct (CFSG.conjugate V₀ t) ⟨_, hgN⟩,
      Setup.mem_autOn_iff.mpr ⟨⟨_, hgN⟩, hgL', rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, congr_conjAct ⟨_, hgN⟩ hg2]
    congr 1
    exact Subtype.ext h1

theorem binaryNaturalSL_conjugate {L V₀ : Subgroup G} [IsMulCommutative ↥V₀] {t : G}
    [IsMulCommutative ↥(CFSG.conjugate V₀ t)] (ht : t ∈ Subgroup.normalizer (L : Set G))
    (hL : L ≤ Subgroup.normalizer (V₀ : Set G)) {d a : ℕ}
    (h : BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ d a) :
    BinaryNaturalSL (V := ↥(CFSG.conjugate V₀ t)) (autOn L (CFSG.conjugate V₀ t)) ⊤ ⊥ d a := by
  obtain ⟨K, hK, hf, hc, hreal⟩ := h
  refine ⟨K, hK, hf, hc, ?_⟩
  let φ := conjEquiv V₀ t
  let j : ↥(⊤ : Subgroup ↥(CFSG.conjugate V₀ t)) ≃* ↥V₀ := Subgroup.topEquiv.trans φ
  let r : ↥(autOn L (CFSG.conjugate V₀ t)) ≃* ↥(autOn L V₀) :=
    ((MulAut.congr φ).subgroupMap (autOn L (CFSG.conjugate V₀ t))).trans
      (MulEquiv.subgroupCongr (map_congr_autOn ht hL))
  refine FFModel.realizes_of_equiv (fun _ _ _ _ => Subgroup.mem_top _) j r (fun h u => ?_) hreal
  change φ ((h : MulAut ↥(CFSG.conjugate V₀ t)) (φ.symm (φ u))) =
    φ ((h : MulAut ↥(CFSG.conjugate V₀ t)) u)
  rw [MulEquiv.symm_apply_apply]

end Sec121

end CFSG.Quasithin.H13
