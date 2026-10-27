module

public import CFSG.RankThree.GF2n.Stroth80.Sec101Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec103Root
public import CFSG.RankThree.GF2n.Stroth80.Sec12Perp
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.exists_mem_conj_of_mem_sup (hc : Ctx M Q Z B) {x : G} (hx : x ∈ B ⊔ Z)
    (hxZ : x ∉ Z) : ∃ p ∈ Q, x ∈ conjSubgroup p B := by
  obtain ⟨b, hbB, z, hzZ, rfl⟩ := exists_mul_of_mem_sup
    (fun b hb z hz => (Smith81.Z_central hc.hyp hz (hc.le hb)).symm) hx
  have hbZ : b ∉ Z := fun hbZ => hxZ (Z.mul_mem hbZ hzZ)
  obtain ⟨w, hwQ, hw⟩ := Smith81.exists_comm_eq hc.hyp (hc.le hbB) hbZ hzZ
  refine ⟨w, hwQ, mem_conjSubgroup.mpr ?_⟩
  have hcomm : b * z = z * b := (Smith81.Z_central hc.hyp hzZ (hc.le hbB)).symm
  have hxeq : b * z = w * b * w⁻¹ := by
    rw [show w * b * w⁻¹ = ⁅w, b⁆ * b by simp only [commutatorElement_def]; group, hw]
    exact hcomm
  rw [hxeq]
  rw [show w⁻¹ * (w * b * w⁻¹) * w = b by group]
  exact hbB

theorem SLlike.exists_mem_conj_sup {hc : Ctx M Q Z B} {t : G} (ht : t ∈ LB M Q B)
    (hsl : SLlike hc t) {v : G} (hv : v ∈ Vt M (LB M Q B) B Z t) (hvZ : v ∉ Z) :
    ∃ r ∈ Rt M (LB M Q B) t, v ∈ conjSubgroup r B ⊔ Z := by
  obtain ⟨m, hm2, hslm⟩ := hsl.exists_SLMNat
  obtain ⟨b, hbB, hb1⟩ := hc.exists_ne_one_B
  have hbV : b ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht hbB
  have hbZ : b ∉ Z := fun hbZ => hb1 (by
    have h : b ∈ Z ⊓ B := ⟨hbZ, hbB⟩
    rwa [hc.inf_eq_bot, Subgroup.mem_bot] at h)
  obtain ⟨r, hrR, hrz⟩ := hslm.exists_conj_inv_mul_mem_Z hm2 hbV hbZ hv hvZ
  refine ⟨r, hrR, ?_⟩
  have hmem : r * b * r⁻¹ ∈ conjSubgroup r B := by
    rw [mem_conjSubgroup, show r⁻¹ * (r * b * r⁻¹) * r = b by group]
    exact hbB
  rw [show v = (r * b * r⁻¹) * ((r * b * r⁻¹)⁻¹ * v) by group]
  exact (conjSubgroup r B ⊔ Z).mul_mem (Subgroup.mem_sup_left hmem) (Subgroup.mem_sup_right hrz)

theorem SLlike.exists_eq_conj_of_le_Vt {hc : Ctx M Q Z B} {t : G} (ht : t ∈ LB M Q B)
    (hsl : SLlike hc t) {E : Subgroup G} (hE : IsRootB M B E)
    (hEV : E ≤ Vt M (LB M Q B) B Z t) : ∃ r ∈ Rt M (LB M Q B) t, E = conjSubgroup r B := by
  obtain ⟨m, hm, rfl⟩ := hE
  obtain ⟨g, hg⟩ := hc.conj
  have hne : conjSubgroup m B ≠ Z := by
    intro hEZ
    have hEq : conjSubgroup (m * g) Z = Z := by
      rw [conjSubgroup_mul, ← hg]
      exact hEZ
    have hmgM : m * g ∈ M := by
      rw [← hc.hyp.normalizer_Z.1]
      exact conjSubgroup_eq_self_iff.mp hEq
    have hgM : g ∈ M := by
      have h := M.mul_mem (M.inv_mem hm) hmgM
      simpa using h
    exact hc.ne (by rw [hg, hc.conj_Z_eq hgM])
  obtain ⟨b, hbB, hb1⟩ := hc.exists_ne_one_B
  have heE : m * b * m⁻¹ ∈ conjSubgroup m B := by
    rw [mem_conjSubgroup, show m⁻¹ * (m * b * m⁻¹) * m = b by group]
    exact hbB
  have he1 : m * b * m⁻¹ ≠ 1 := by
    intro h
    apply hb1
    calc b = m⁻¹ * (m * b * m⁻¹) * m := by group
      _ = m⁻¹ * 1 * m := by rw [h]
      _ = 1 := by group
  have hZE : Smith81.IsZConjugate Z (conjSubgroup m B) :=
    ⟨m * g, by rw [conjSubgroup_mul, ← hg]⟩
  have heZ : m * b * m⁻¹ ∉ Z := fun heZ =>
    hne (Smith81.IsZConjugate.eq_of_mem hc.hyp hZE (Smith81.IsZConjugate.self Z) he1 heE heZ)
  obtain ⟨r, hrR, hrv⟩ := hsl.exists_mem_conj_sup ht (hEV heE) heZ
  obtain ⟨p, hpQ, hpv⟩ := (hc.conj_of_mem (hc.Rt_le_M t hrR)).exists_mem_conj_of_mem_sup hrv heZ
  have hZR : Smith81.IsZConjugate Z (conjSubgroup (p * r) B) :=
    ⟨(p * r) * g, by rw [conjSubgroup_mul (p * r) g Z, ← hg]⟩
  have hpv' : m * b * m⁻¹ ∈ conjSubgroup (p * r) B := by
    rwa [conjSubgroup_mul]
  have heq : conjSubgroup m B = conjSubgroup (p * r) B :=
    Smith81.IsZConjugate.eq_of_mem hc.hyp hZE hZR he1 heE hpv'
  exact ⟨p * r, (Rt M (LB M Q B) t).mul_mem (hc.Q_le_Rt ht hpQ) hrR, heq⟩

end CFSG.RankThree.GF2n.Stroth80
