module

public import CFSG.RankThree.GF2n.Smith81.Lin26Torus
public import CFSG.RankThree.GF2n.Stroth80.Sec34Trilinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.eq_one_of_mem_B_of_torus_fix (hc : Ctx M Q Z B) {y : G} (hyX : y ∈ Q ⊔ QB B)
    (hyZ : y ∈ Subgroup.normalizer (Z : Set G)) (hyB : y ∈ Subgroup.normalizer (B : Set G))
    (hreg : ∀ v ∈ Z, y * v = v * y → v = 1) {c : G} (hcB : c ∈ B) (hfix : y * c * y⁻¹ = c) :
    c = 1 := by
  have hcQ : c ∈ Q := hc.le hcB
  have hcen : c ∈ cen Q := by
    rw [cen_eq]
    refine ⟨hcQ, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    have h1 := Ctx.torus_comm hc hyX hyZ hyB hcB hg
    rw [hfix] at h1
    have h2 : ⁅c, g⁆ = 1 := hreg _ (hc.hyp.toHyp79.comm_mem_V hcQ hg) (by
      calc y * ⁅c, g⁆ = y * (y⁻¹ * ⁅c, g⁆ * y) := by rw [← h1]
        _ = ⁅c, g⁆ * y := by group)
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
  have hcZ : c ∈ Z := by
    rw [hc.hyp.hZ]
    exact hcen
  have h3 : c ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨hcZ, hcB⟩
  rwa [hc.inf_eq_bot, Subgroup.mem_bot] at h3

theorem Ctx.mem_Q_of_torus_comm_mem (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) {y : G} (hyX : y ∈ Q ⊔ QB B) (hyM : y ∈ M)
    (hyZ : y ∈ Subgroup.normalizer (Z : Set G)) (hyB : y ∈ Subgroup.normalizer (B : Set G))
    (hreg : ∀ v ∈ Z, y * v = v * y → v = 1) {l : G} (hl : l ∈ LB M Q B)
    (hyl : y * l * y⁻¹ * l⁻¹ ∈ Q) : l ∈ Q := by
  obtain ⟨s, hs, x, hx, rfl⟩ := hc.exists_mul_of_mem_LB hl
  have hsQB : s ∈ QB B := (Subgroup.mem_inf.mp hs).1
  have hsM : s ∈ M := (Subgroup.mem_inf.mp hs).2
  have hQn : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := fun m hm q hq =>
    (hc.conj_mem_Q_of_mem_M hm).1 q hq
  have hyQB : ∀ w ∈ QB B, y * w * y⁻¹ ∈ QB B := by
    intro w hw
    have h1 : QB B = conjSubgroup y (QB B) := by
      rw [← QB_conj, conjSubgroup_eq_self_iff.mpr hyB]
    rw [h1]
    exact mem_conjSubgroup.mpr (by
      have e : y⁻¹ * (y * w * y⁻¹) * y = w := by group
      rw [e]
      exact hw)
  have huQ : y * s * y⁻¹ * s⁻¹ ∈ Q := by
    have e : y * (s * x) * y⁻¹ * (s * x)⁻¹ =
        (y * s * y⁻¹ * s⁻¹) * (s * (y * x * y⁻¹ * x⁻¹) * s⁻¹) := by group
    have h2 : s * (y * x * y⁻¹ * x⁻¹) * s⁻¹ ∈ Q :=
      hQn s hsM _ (Q.mul_mem (hQn y hyM x hx) (Q.inv_mem hx))
    have h3 := Q.mul_mem (e ▸ hyl) (Q.inv_mem h2)
    rwa [mul_inv_cancel_right] at h3
  have huQB : y * s * y⁻¹ * s⁻¹ ∈ QB B := (QB B).mul_mem (hyQB s hsQB) ((QB B).inv_mem hsQB)
  have huD : y * s * y⁻¹ * s⁻¹ ∈ Q ⊓ QB B := Subgroup.mem_inf.mpr ⟨huQ, huQB⟩
  have hsZ : ∀ z ∈ Z, s * z * s⁻¹ = z :=
    hc.LB_centralizes_Z (Subgroup.mem_sup_right hs)
  have hBQB : B ≤ QB B := hc.B_le_QB
  have hkey : ∀ d ∈ Q ⊓ QB B, ⁅s, d⁆ = 1 := by
    intro d hd
    have hdQB : d ∈ QB B := (Subgroup.mem_inf.mp hd).2
    have hcB : ⁅s, d⁆ ∈ B := hc.comm_QB_le_B hsQB hdQB
    refine hc.eq_one_of_mem_B_of_torus_fix hyX hyZ hyB hreg hcB ?_
    obtain ⟨z, hz, b, hb, hzb⟩ := (Ctx.mem_sup_iff hc).mp (Ctx.sup_QB_comm_inf_mem hc hyX hd)
    set u := y * s * y⁻¹ * s⁻¹ with hu
    set c := ⁅s, d⁆ with hcdef
    have hcQ : c ∈ Q := hc.le hcB
    have huz : Commute u z := (hc.hyp.toHyp79.V_central hz huQ).symm
    have hub : Commute u b := (Ctx.B_central_QB hc hb huQB).symm
    have huc : Commute u c := (Ctx.B_central_QB hc hcB huQB).symm
    have hud : Commute u d :=
      congrArg Subtype.val ((Ctx.inf_QB_elemAbelian hc).1.is_comm.comm ⟨u, huD⟩ ⟨d, hd⟩)
    have hcz : Commute c z := (hc.hyp.toHyp79.V_central hz hcQ).symm
    have hcb : Commute c b := (Ctx.B_central_QB hc hb (hBQB hcB)).symm
    have hys : y * s * y⁻¹ = u * s := by rw [hu]; group
    have hyd : y * d * y⁻¹ = z * b * d := by
      calc y * d * y⁻¹ = ⁅y, d⁆ * d := by simp only [commutatorElement_def]; group
        _ = z * b * d := by rw [hzb]
    have hA : s * (z * b * d) * s⁻¹ = z * b * (c * d) := by
      have e : s * (z * b * d) * s⁻¹ = (s * z * s⁻¹) * (s * b * s⁻¹) * (s * d * s⁻¹) := by group
      have hsb : s * b * s⁻¹ = b := by
        rw [← Ctx.B_central_QB hc hb hsQB]
        group
      have hsd : s * d * s⁻¹ = c * d := by
        rw [hcdef]
        simp only [commutatorElement_def]
        group
      rw [e, hsZ z hz, hsb, hsd]
    have hB' : u * (z * b * (c * d)) * u⁻¹ = z * b * (c * d) := by
      rw [((huz.mul_right hub).mul_right (huc.mul_right hud)).eq]
      group
    have hC : z * b * (c * d) * (z * b * d)⁻¹ = c := by
      calc z * b * (c * d) * (z * b * d)⁻¹ = z * b * c * (z * b)⁻¹ := by group
        _ = c := by
          rw [← (hcz.mul_right hcb).eq]
          group
    calc y * c * y⁻¹ = ⁅y * s * y⁻¹, y * d * y⁻¹⁆ := by
          rw [hcdef]
          simp only [commutatorElement_def]
          group
      _ = u * (s * (z * b * d) * s⁻¹) * u⁻¹ * (z * b * d)⁻¹ := by
          rw [hys, hyd]
          simp only [commutatorElement_def]
          group
      _ = c := by rw [hA, hB', hC]
  have hsQ : s ∈ Q := hc.mem_Q_of_comm_inf_QB hw hn hno hs fun d hd => by
    rw [hkey d hd]
    exact Z.one_mem
  exact Q.mul_mem hsQ hx

end CFSG.RankThree.GF2n.Stroth80
