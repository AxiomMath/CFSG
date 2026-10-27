module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IS
public import CFSG.Quasithin.Vol2.Ch11SecE3L0
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IR

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
  Module CFSG.Quasithin.E2P.Asc80
open scoped MatrixGroups

theorem congr_conj {X Y : Type} [Group X] [Group Y] (ψ : X ≃* Y) (x : X) :
    MulAut.congr ψ (MulAut.conj x) = MulAut.conj (ψ x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem not_mem_normalizer_projStabilizer {L : Subgroup G} (hAS : SecE3.AlmostSimple L)
    (e : ↥L ≃* PSL3 p) {W : Submodule (ZMod p) (Fin 3 → ZMod p)}
    (hW : finrank (ZMod p) W = 1 ∨ finrank (ZMod p) W = 2) {P₀ : Subgroup (PSL3 p)}
    (hP₀ : P₀.map (psl3EquivP p).toMonoidHom = projStabilizer W) {t : G} (ht : t ∉ L)
    (htN : t ∈ Subgroup.normalizer
      ((P₀.map (L.subtype.comp e.symm.toMonoidHom) : Subgroup G) : Set G)) : False := by
  have := hAS.normal
  have := zmod_ringEquiv_subsingleton p
  set ψ : ↥L ≃* projectiveSL 3 (ZMod p) := e.trans (psl3EquivP p) with hψ
  set σ : MulAut ↥L := MulAut.conjNormal t with hσ
  set α : MulAut (projectiveSL 3 (ZMod p)) := MulAut.congr ψ σ with hα
  obtain ⟨k, hk⟩ := hAS.two t
  have hαk : α ^ (2 ^ k) = MulAut.conj (ψ ⟨t ^ 2 ^ k, hk⟩) := by
    rw [hα, ← map_pow, hσ, ← map_pow]
    have h1 : MulAut.conjNormal (t ^ 2 ^ k) = MulAut.conj (⟨t ^ 2 ^ k, hk⟩ : ↥L) :=
      MulAut.conjNormal_val (h := ⟨t ^ 2 ^ k, hk⟩)
    rw [h1, congr_conj]
  set K₀ : Subgroup ↥L := P₀.map e.symm.toMonoidHom with hK₀
  have hK₀ψ : K₀.map ψ.toMonoidHom = projStabilizer W := by
    rw [← hP₀, hK₀, Subgroup.map_map]
    congr 1
    ext x
    simp [hψ]
  have hσK : K₀.map σ.toMonoidHom = K₀ := by
    have hle : K₀.map σ.toMonoidHom ≤ K₀ := by
      rintro _ ⟨x, hx, rfl⟩
      have hxG : (x : G) ∈ P₀.map (L.subtype.comp e.symm.toMonoidHom) := by
        obtain ⟨c, hc, rfl⟩ := hx
        exact ⟨c, hc, rfl⟩
      obtain ⟨c, hc, hcx⟩ := (Subgroup.mem_normalizer_iff.mp htN (x : G)).mp hxG
      refine ⟨c, hc, ?_⟩
      apply Subtype.ext
      show ((e.symm c : ↥L) : G) = ((MulAut.conjNormal t x : ↥L) : G)
      rw [MulAut.conjNormal_apply]
      exact hcx
    exact Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Nat.card_congr (K₀.equivMapOfInjective σ.toMonoidHom σ.injective).toEquiv))
  have hP' : (projStabilizer W).map (α : projectiveSL 3 (ZMod p) →* projectiveSL 3 (ZMod p)) =
      projStabilizer W := by
    rw [← hK₀ψ, Subgroup.map_map]
    have hcomp : (α : projectiveSL 3 (ZMod p) →* projectiveSL 3 (ZMod p)).comp ψ.toMonoidHom =
        ψ.toMonoidHom.comp σ.toMonoidHom := by
      ext x
      simp [hα, MulAut.congr_apply]
    rw [hcomp, ← Subgroup.map_map, hσK]
  obtain ⟨g', hg'⟩ := inner_of_map_projStabilizer p α hαk hW hP'
  set l₀ : ↥L := ψ.symm g' with hl₀
  have hσx : ∀ x : ↥L, σ x = l₀ * x * l₀⁻¹ := by
    intro x
    have h1 : ψ (σ x) = α (ψ x) := by simp [hα, MulAut.congr_apply]
    rw [hg', MulAut.conj_apply] at h1
    apply ψ.injective
    rw [h1, map_mul, map_mul, map_inv, hl₀, MulEquiv.apply_symm_apply]
  apply ht
  have hc : (l₀ : G)⁻¹ * t ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg Subtype.val (hσx ⟨x, hx⟩)
    rw [hσ, MulAut.conjNormal_apply] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc x * ((l₀ : G)⁻¹ * t) = (l₀ : G)⁻¹ * ((l₀ : G) * x * (l₀ : G)⁻¹) * t := by group
      _ = (l₀ : G)⁻¹ * (t * x * t⁻¹) * t := by rw [h1]
      _ = (l₀ : G)⁻¹ * t * x := by group
  rw [hAS.centralizer_eq, Subgroup.mem_bot] at hc
  have : t = l₀ := by
    calc t = (l₀ : G) * ((l₀ : G)⁻¹ * t) := by group
      _ = l₀ := by rw [hc, mul_one]
  rw [this]
  exact l₀.2

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
