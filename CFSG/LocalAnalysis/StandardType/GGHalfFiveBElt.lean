module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfFivePerm
public import CFSG.LocalAnalysis.StandardType.GGHalfGlue
public import CFSG.LocalAnalysis.StandardType.GGHalfZpowers

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)

include h

theorem phi1_omega4_eq : φ₁ (omegaBlock 5 4) = φ₂ (omegaBlock 5 2) := by
  have hagree : (φ₁.comp (slLower2Hom 3)) (omegaBlock 3 ⟨2, by omega⟩) =
      (φ₂.comp (slUpper2Hom 3)) (omegaBlock 3 ⟨2, by omega⟩) := by rw [h.coords.agree]
  simp only [MonoidHom.comp_apply] at hagree
  rw [slLower2Hom_omegaBlock, slUpper2Hom_omegaBlock] at hagree
  simpa using hagree

private theorem zeta5_ne_one : zeta5 ≠ 1 := by
  intro h1
  have homega : omegaScalar = 1 := by
    apply resGL_injective 3
    rw [← zeta5_eq, h1, map_one]
  have h2 : (omegaScalar : Matrix (Fin 3) (Fin 3) F4) 0 0 = 1 := by
    rw [homega]; simp
  rw [show (omegaScalar : Matrix (Fin 3) (Fin 3) F4) = Matrix.scalar (Fin 3) f4Omega from by
    rw [omegaScalar, Units.coe_map]; rfl] at h2
  exact f4Omega_ne_one (by simpa [Matrix.scalar_apply] using h2)

private theorem wElt_mem_zpowers_x : wElt φ₂ ∈ Subgroup.zpowers x := by
  rw [zpowers_x h]
  exact Subgroup.mem_zpowers _

private theorem vElt_mem_zpowers_y : vElt φ₁ ∈ Subgroup.zpowers y := by
  rw [zpowers_y h]
  exact Subgroup.mem_zpowers _

private theorem wElt_comm_phi1 (s : SpecialLinearGroup (Fin 6) F2) :
    wElt φ₂ * φ₁ s = φ₁ s * wElt φ₂ := by
  obtain ⟨-, -, -, -, -, -, hxL, -, -, -⟩ := h.basic
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (wElt_mem_zpowers_x h)
  have hsL : φ₁ s ∈ L := by rw [← h.coords.range₁]; exact ⟨s, rfl⟩
  have hxcomm : Commute x (φ₁ s) := hxL (φ₁ s) hsL
  rw [← hk]
  exact hxcomm.zpow_left k

private theorem vElt_comm_phi2 (t : SpecialLinearGroup (Fin 6) F2) :
    vElt φ₁ * φ₂ t = φ₂ t * vElt φ₁ := by
  obtain ⟨-, -, -, -, -, -, -, hyK, -, -⟩ := h.basic
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (vElt_mem_zpowers_y h)
  have htK : φ₂ t ∈ K := by rw [← h.coords.range₂]; exact ⟨t, rfl⟩
  have hycomm : Commute y (φ₂ t) := hyK (φ₂ t) htK
  rw [← hk]
  exact hycomm.zpow_left k

private theorem gElt_comm_wElt : gElt φ₁ * wElt φ₂ = wElt φ₂ * gElt φ₁ := by
  obtain ⟨-, -, -, -, -, -, hxL, -, -, -⟩ := h.basic
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (wElt_mem_zpowers_x h)
  have hgL : gElt φ₁ ∈ L := by rw [← h.coords.range₁]; exact ⟨_, rfl⟩
  have hxcomm : Commute x (gElt φ₁) := hxL (gElt φ₁) hgL
  rw [← hk]
  exact (hxcomm.zpow_left k).symm

private theorem bElt_eq_vElt_mul_phi2_zeta :
    bElt φ₁ φ₂ = vElt φ₁ * φ₂ zeta5 := by
  have hu : φ₁ (omegaBlock 5 2) = uElt φ₂ := (uElt_eq h).symm
  have h4 : φ₁ (omegaBlock 5 4) = φ₂ (omegaBlock 5 2) := phi1_omega4_eq h
  rw [bElt, zeta5]
  simp only [map_mul]
  rw [hu, h4, show φ₁ (omegaBlock 5 0) = vElt φ₁ from rfl,
    show uElt φ₂ = φ₂ (omegaBlock 5 0) from rfl]
  group

private theorem bElt_conj_phi1 (s : SpecialLinearGroup (Fin 6) F2) :
    bElt φ₁ φ₂ * φ₁ s * (bElt φ₁ φ₂)⁻¹ = φ₁ (zeta5 * s * zeta5⁻¹) := by
  have hw : wElt φ₂ * φ₁ s * (wElt φ₂)⁻¹ = φ₁ s := by
    rw [wElt_comm_phi1 h s]; group
  calc bElt φ₁ φ₂ * φ₁ s * (bElt φ₁ φ₂)⁻¹
      = φ₁ zeta5 * (wElt φ₂ * φ₁ s * (wElt φ₂)⁻¹) * (φ₁ zeta5)⁻¹ := by
          rw [show bElt φ₁ φ₂ = φ₁ zeta5 * wElt φ₂ from rfl]; group
    _ = φ₁ zeta5 * φ₁ s * (φ₁ zeta5)⁻¹ := by rw [hw]
    _ = φ₁ (zeta5 * s * zeta5⁻¹) := by
          rw [← map_inv, ← map_mul, ← map_mul]

theorem bElt_eq :
    bElt φ₁ φ₂ = vElt φ₁ * uElt φ₂ * φ₁ (omegaBlock 5 4) * wElt φ₂ := by
  have hu : φ₁ (omegaBlock 5 2) = uElt φ₂ := (uElt_eq h).symm
  rw [bElt, zeta5, map_mul, map_mul, hu]
  rfl

theorem bElt_mem_bs : bElt φ₁ φ₂ ∈ Bs := by
  rw [bElt_eq h]
  have hω4 : φ₁ (omegaBlock 5 4) ∈ Bs :=
    h.torusL_le (Subgroup.mem_map.mpr
      ⟨omegaBlock 5 4, Subgroup.subset_closure ⟨(4 : Fin 5), by norm_num, rfl⟩, rfl⟩)
  exact Bs.mul_mem (Bs.mul_mem (Bs.mul_mem h.vElt_mem h.uElt_mem) hω4) h.wElt_mem

theorem bElt_pow_three : bElt φ₁ φ₂ ^ 3 = 1 :=
  (h.basic.2.1) _ (bElt_mem_bs h)

theorem bElt_not_mem_zpowers_x : bElt φ₁ φ₂ ∉ Subgroup.zpowers x := by
  intro hb
  obtain ⟨-, -, -, -, -, -, hxL, -, -, -⟩ := h.basic
  have hbL : ∀ l ∈ L, bElt φ₁ φ₂ * l * (bElt φ₁ φ₂)⁻¹ = l := by
    intro l hl
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hxcomm : Commute x l := hxL l hl
    have hk' : x ^ k * l = l * x ^ k := hxcomm.zpow_left k
    rw [← hk, hk']
    group
  have hζcomm : ∀ s : SpecialLinearGroup (Fin 6) F2, zeta5 * s = s * zeta5 := by
    intro s
    have hsL : φ₁ s ∈ L := by rw [← h.coords.range₁]; exact ⟨s, rfl⟩
    have h1 : bElt φ₁ φ₂ * φ₁ s * (bElt φ₁ φ₂)⁻¹ = φ₁ (zeta5 * s * zeta5⁻¹) :=
      bElt_conj_phi1 h s
    have h2 : bElt φ₁ φ₂ * φ₁ s * (bElt φ₁ φ₂)⁻¹ = φ₁ s := hbL (φ₁ s) hsL
    have h3 : φ₁ (zeta5 * s * zeta5⁻¹) = φ₁ s := by rw [← h1, h2]
    have h4 : zeta5 * s * zeta5⁻¹ = s := h.coords.inj₁ h3
    calc zeta5 * s = zeta5 * s * zeta5⁻¹ * zeta5 := by group
      _ = s * zeta5 := by rw [h4]
  have hzeta1 : zeta5 = 1 :=
    eq_one_of_commute_range h.coords.inj₁ (fun t => by
      rw [← map_mul, ← map_mul, hζcomm t])
  exact zeta5_ne_one h hzeta1

theorem bElt_act_L (s : SpecialLinearGroup (Fin 6) F2) :
    bElt φ₁ φ₂ * φ₁ s * (bElt φ₁ φ₂)⁻¹ = φ₁ (zeta5 * s * zeta5⁻¹) :=
  bElt_conj_phi1 h s

theorem gElt_comm_b : gElt φ₁ * bElt φ₁ φ₂ = bElt φ₁ φ₂ * gElt φ₁ := by
  have hζcomm : slPerm gf2_two (sigmaPerm 3) * zeta5 = zeta5 * slPerm gf2_two (sigmaPerm 3) :=
    Subgroup.mem_centralizer_singleton_iff.mp (sl3four_le_centralizer slPerm_sigma_mem_sl3four)
  have hgζ : gElt φ₁ * φ₁ zeta5 = φ₁ zeta5 * gElt φ₁ := by
    rw [gElt, ← map_mul, ← map_mul, hζcomm]
  calc gElt φ₁ * bElt φ₁ φ₂
      = (gElt φ₁ * φ₁ zeta5) * wElt φ₂ := by
          rw [show bElt φ₁ φ₂ = φ₁ zeta5 * wElt φ₂ from rfl]; group
    _ = (φ₁ zeta5 * gElt φ₁) * wElt φ₂ := by rw [hgζ]
    _ = φ₁ zeta5 * (gElt φ₁ * wElt φ₂) := by group
    _ = φ₁ zeta5 * (wElt φ₂ * gElt φ₁) := by rw [gElt_comm_wElt h]
    _ = (φ₁ zeta5 * wElt φ₂) * gElt φ₁ := by group
    _ = bElt φ₁ φ₂ * gElt φ₁ := by
          rw [show bElt φ₁ φ₂ = φ₁ zeta5 * wElt φ₂ from rfl]

theorem hElt_comm_b : hElt φ₂ * bElt φ₁ φ₂ = bElt φ₁ φ₂ * hElt φ₂ := by
  have hζcomm : slPerm gf2_two (tauPerm 3) * zeta5 = zeta5 * slPerm gf2_two (tauPerm 3) :=
    Subgroup.mem_centralizer_singleton_iff.mp (sl3four_le_centralizer slPerm_tau_mem_sl3four)
  have hhζ : hElt φ₂ * φ₂ zeta5 = φ₂ zeta5 * hElt φ₂ := by
    rw [hElt, ← map_mul, ← map_mul, hζcomm]
  have hhv : hElt φ₂ * vElt φ₁ = vElt φ₁ * hElt φ₂ :=
    (vElt_comm_phi2 h (slPerm gf2_two (tauPerm 3))).symm
  calc hElt φ₂ * bElt φ₁ φ₂
      = (hElt φ₂ * vElt φ₁) * φ₂ zeta5 := by
          rw [bElt_eq_vElt_mul_phi2_zeta h]; group
    _ = (vElt φ₁ * hElt φ₂) * φ₂ zeta5 := by rw [hhv]
    _ = vElt φ₁ * (hElt φ₂ * φ₂ zeta5) := by group
    _ = vElt φ₁ * (φ₂ zeta5 * hElt φ₂) := by rw [hhζ]
    _ = (vElt φ₁ * φ₂ zeta5) * hElt φ₂ := by group
    _ = bElt φ₁ φ₂ * hElt φ₂ := by
          rw [bElt_eq_vElt_mul_phi2_zeta h]

end GGHalfCtx

end CFSG.StandardType

end
