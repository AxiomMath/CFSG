module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDLocChain
public import Certificates.Certificate7050Base

public section

namespace CFSG.Quasithin.H13.F431.TitsD

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.RuType
  CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru CFSG.Sporadic.Schreier.Tits CFSG.RuF45
  CFSG.TwoF4Lie CFSG.TwoF4Loc CFSG.TitsLoc CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

set_option linter.unusedSectionVars false


theorem fusion_D : ∀ u ∈ Subgroup.centralizer ({tD} : Set ↥titsD), IsConj zD u →
    u ∈ VD ∨ ∃ n ∈ titsND, ∃ a ∈ titsSD, ∃ b ∈ titsSD, u = n * a * n⁻¹ ∧ tD = n * b * n⁻¹ ∧
      ∃ b' ∈ titsSD, Relation.ReflTransGen (PairLink titsSD titsHD titsND) (a, b) (zD, b') ∧
        ∀ h ∈ titsHD, h * tD * h⁻¹ ≠ b' := by
  intro u hu hconj
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  have hut : u * tD = tD * u := Subgroup.mem_centralizer_singleton_iff.1 hu
  have hcz : g⁻¹ * tD * g ∈ titsHD := by
    rw [← cent_z_D]
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc g⁻¹ * tD * g * zD = g⁻¹ * (tD * (g * zD * g⁻¹)) * g := by group
      _ = g⁻¹ * (tD * u) * g := by rw [hg]
      _ = g⁻¹ * (u * tD) * g := by rw [hut]
      _ = zD * (g⁻¹ * tD * g) := by rw [← hg]; group
  have ht0 : (g⁻¹ * tD * g).1 0 = 0 := fix_zero_of_mem_titsH (Subgroup.mem_subgroupOf.1 hcz)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Subgroup.coe_inv, Equiv.Perm.inv_eq_iff_eq] at ht0
  have htp : Certificates.c4180T (g.1 0) = g.1 0 := by
    rw [← tEl_eq]
    exact ht0
  obtain ⟨-, -, -, hfix⟩ := Certificates.certificate4182
  obtain ⟨m, hmA, hm0, hcase⟩ := hfix (g.1 0) htp
  set mM : ↥twoF4M := ⟨m, mem_twoF4M_of_mem_A hmA⟩ with hmM
  have hm : mM.1 0 = (ιD g).1 0 := hm0
  have hu_eq : ιD u = mM * zM * mM⁻¹ := by
    rw [← hg, map_mul, map_mul, map_inv, ιD_zD]
    exact zP_eq hm.symm
  have hu1 : u.1 = m * titsZ * m⁻¹ := congrArg Subtype.val hu_eq
  rcases hcase with h | h | h | ⟨hS, b, hb, hq, hchain⟩
  · left
    have : u = zD := Subtype.ext (hu1.trans h)
    rw [this]
    exact mem_VD.2 (Or.inr (Or.inl rfl))
  · left
    have : u = z1D := by
      refine Subtype.ext (hu1.trans (h.trans ?_))
      change _ = cEl.1 * titsZ * cEl.1⁻¹
      rw [cEl_eq]
    rw [this]
    exact mem_VD.2 (Or.inr (Or.inr (Or.inl rfl)))
  · left
    have : u = z2D := by
      refine Subtype.ext (hu1.trans (h.trans ?_))
      change _ = cEl.1⁻¹ * titsZ * cEl.1
      rw [cEl_eq]
    rw [this]
    exact mem_VD.2 (Or.inr (Or.inr (Or.inr rfl)))
  · right
    rw [← hu1] at hS hchain
    have huT : u ∈ titsSD := mem_titsSD hS
    have htT : tD ∈ titsSD := titsD_F431LieI.t_mem
    set b' : ↥titsD := ⟨b, hb.1⟩ with hb'
    have hch := pairChainD hchain u tD zD b' rfl tEl_eq rfl rfl
    exact ⟨1, Subgroup.one_mem _, u, huT, tD, htT, by simp, by simp, b', mem_titsSD hb, hch,
      hne_of_col_D hq⟩

end CFSG.Quasithin.H13.F431.TitsD
