module

public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] {L V : Subgroup G}

@[expose] def nLV (L V : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)

theorem conj_mem_comm {x : G} (hL : x ∈ Subgroup.normalizer (L : Set G))
    (hV : x ∈ Subgroup.normalizer (V : Set G)) {w : G} (hw : w ∈ ⁅V, L⁆) :
    x * w * x⁻¹ ∈ ⁅V, L⁆ := by
  have hle : ∀ {K : Subgroup G}, x ∈ Subgroup.normalizer (K : Set G) →
      K.map (MulAut.conj x).toMonoidHom ≤ K := by
    intro K hK
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hK y).mp hy
  have h := Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hw
  rw [Subgroup.map_commutator] at h
  exact Subgroup.commutator_mono (hle hV) (hle hL) h

theorem conj_mem_cent {x : G} (hL : x ∈ Subgroup.normalizer (L : Set G)) {z : G}
    (hz : z ∈ Subgroup.centralizer (L : Set G)) :
    x * z * x⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro l hl
  have hl' : x⁻¹ * l * x ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hL) l).mp hl
    simpa using this
  have h := hz _ hl'
  calc l * (x * z * x⁻¹) = x * ((x⁻¹ * l * x) * z) * x⁻¹ := by group
    _ = x * (z * (x⁻¹ * l * x)) * x⁻¹ := by rw [h]
    _ = x * z * x⁻¹ * l := by group

@[expose] def cW (g : ↥(nLV L V)) : ↥⁅V, L⁆ ≃* ↥⁅V, L⁆ where
  toFun w := ⟨g * w * (g : G)⁻¹, conj_mem_comm g.2.1 g.2.2 w.2⟩
  invFun w := ⟨(g : G)⁻¹ * w * g, by
    have := conj_mem_comm (Subgroup.inv_mem _ g.2.1) (Subgroup.inv_mem _ g.2.2) w.2
    simpa using this⟩
  left_inv w := Subtype.ext (by simp [mul_assoc])
  right_inv w := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_cW (g : ↥(nLV L V)) (w : ↥⁅V, L⁆) : ((cW g w : ↥⁅V, L⁆) : G) = g * w * (g : G)⁻¹ :=
  rfl

variable {F : Type} [Field F] (β : ↥⁅V, L⁆ →* H.StdMod (Fin 2) F)
  (hβ : Function.Surjective β)
  (hβk : β.ker = (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅V, L⁆)

include hβk in
theorem map_ker_cW (g : ↥(nLV L V)) :
    β.ker.map (cW g : ↥⁅V, L⁆ →* ↥⁅V, L⁆) = β.ker := by
  have key : ∀ (x : ↥(nLV L V)) (w : ↥⁅V, L⁆), w ∈ β.ker → cW x w ∈ β.ker := by
    intro x w hw
    rw [hβk, Subgroup.mem_subgroupOf] at hw ⊢
    exact ⟨(cW x w).2, conj_mem_cent x.2.1 hw.2⟩
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    exact key g w hw
  · intro w hw
    refine ⟨cW g⁻¹ w, key g⁻¹ w hw, Subtype.ext ?_⟩
    show (g : G) * ((g⁻¹ : ↥(nLV L V)) * w * ((g⁻¹ : ↥(nLV L V)) : G)⁻¹) * (g : G)⁻¹ = w
    simp [mul_assoc]

@[expose] noncomputable def rho (g : ↥(nLV L V)) : MulAut (H.StdMod (Fin 2) F) :=
  ((QuotientGroup.quotientKerEquivOfSurjective β hβ).symm.trans
    (QuotientGroup.congr β.ker β.ker (cW g) (map_ker_cW β hβk g))).trans
    (QuotientGroup.quotientKerEquivOfSurjective β hβ)

theorem rho_apply (g : ↥(nLV L V)) (w : ↥⁅V, L⁆) : rho β hβ hβk g (β w) = β (cW g w) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective β hβ).symm (β w) =
      (QuotientGroup.mk w : ↥⁅V, L⁆ ⧸ β.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show (QuotientGroup.quotientKerEquivOfSurjective β hβ) (QuotientGroup.congr β.ker β.ker
    (cW g) (map_ker_cW β hβk g) ((QuotientGroup.quotientKerEquivOfSurjective β hβ).symm (β w))) = _
  rw [h1]
  rfl

theorem rho_mul (g h : ↥(nLV L V)) :
    rho β hβ hβk (g * h) = rho β hβ hβk g * rho β hβ hβk h := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨w, rfl⟩ := hβ x
  rw [MulAut.mul_apply, rho_apply, rho_apply, rho_apply]
  congr 1
  apply Subtype.ext
  simp only [coe_cW, Subgroup.coe_mul]
  group

theorem rho_one : rho β hβ hβk 1 = 1 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨w, rfl⟩ := hβ x
  rw [rho_apply]
  show β (cW 1 w) = β w
  congr 1
  apply Subtype.ext
  simp [coe_cW]

@[expose] noncomputable def rhoHom : ↥(nLV L V) →* MulAut (H.StdMod (Fin 2) F) where
  toFun := rho β hβ hβk
  map_one' := rho_one β hβ hβk
  map_mul' := rho_mul β hβ hβk

theorem rhoHom_apply (g : ↥(nLV L V)) : rhoHom β hβ hβk g = rho β hβ hβk g := rfl

theorem rho_eq_one (hLV : L ≤ Subgroup.normalizer (V : Set G)) (g : ↥(nLV L V))
    (hg : (g : G) ∈ Subgroup.centralizer (V : Set G)) : rho β hβ hβk g = 1 := by
  have hWV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  refine MulEquiv.ext fun x => ?_
  obtain ⟨w, rfl⟩ := hβ x
  rw [rho_apply]
  show β (cW g w) = β w
  congr 1
  apply Subtype.ext
  rw [coe_cW]
  have h := Subgroup.mem_centralizer_iff.mp hg _ (hWV w.2)
  rw [← h, mul_inv_cancel_right]

theorem rho_of_mem (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (α : ↥L →* ↥(Assembly.LowTwoRank.StatedSL 2 F))
    (hβe : ∀ (a : ↥L) (u v : ↥⁅V, L⁆), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α a : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
          (Multiplicative.toAdd (β u)))
    (l : ↥L) :
    rho β hβ hβk ⟨l, Subgroup.le_normalizer l.2, hLV l.2⟩ =
      H.natAut (Assembly.LowTwoRank.StatedSL 2 F) (α l) := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨w, rfl⟩ := hβ x
  rw [rho_apply, H.natAut_apply]
  apply Multiplicative.toAdd.injective
  rw [hβe l w _ rfl]
  rfl

end CFSG.Quasithin.B610T

end
