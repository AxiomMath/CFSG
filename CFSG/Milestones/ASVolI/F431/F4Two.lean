module

public import CFSG.Milestones.ASVolI.F431.A35LieI
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Model
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Zid
import CFSG.Milestones.ASVolI.F4
import CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.LocalAnalysis.EvenBN.U4.Model.AutSection
public import CFSG.Milestones.ASVolI.F431.Asm
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2Complete
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieE
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieStdTwo
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Sporadic.Schreier.Tits CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.ASVolI.ChF.ExceptionalRoots CFSG.Blueprint CFSG.Blueprint.Chevalley

section F4Two

set_option linter.unusedSectionVars false


theorem burnsideF4m_F4Two_xi {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .F4tw 2 f Gp M₁ M₂) (hf : f < 3) :
    Gp = ⊤ ∧ ∃ Ξ : E ≃* ↥twoF4M, (∀ y, Ξ y ∈ twoF4M1 ↔ y ∈ M₁) ∧
      (∀ y, Ξ y ∈ twoF4M2 ↔ y ∈ M₂) := by
  haveI := hyp.normal
  have hyp4 := hyp.toHypF_4_4g
  obtain ⟨a, K, fK, finK, charK, hscope, hfa, marking, h1, h2⟩ :=
    burnsideF4gF4Two_chart_F4tw hyp4
  have ha : a = 0 := by omega
  subst ha
  letI := fK
  haveI := finK
  haveI : CharP K F4.prime := charK
  have hKa : Nat.card K = 2 ^ (2 * 0 + 1) := hscope
  have hK : Nat.card K = 2 := by simpa using hKa
  have hcen : Subgroup.center ↥(reeGroup K 0) = ⊥ := by
    have := large_Ree_fixed_group_center_trivial 0 K hKa
    rwa [burnsideF4gF4Two_reeGroup_eq]
  obtain ⟨q, hq⟩ := burnsideF4gF4Two_exists_quotEquiv hcen
  obtain ⟨Φ, -, hΦ1, hΦ2⟩ := burnsideF4gF4TwoInv_gamma hK hKa
  let e1 : ↥(reeGroup K 0) ≃* Gm K 0 := MulEquiv.subgroupCongr burnsideF4gF4Two_reeGroup_eq
  let Ψ0 : ↥(reeGroup K 0) ≃* ↥Gp := q.trans marking
  let Ψ : ↥Gp ≃* ↥twoF4M := Ψ0.symm.trans (e1.trans Φ)
  have hGp : Gp = ⊤ := burnsideF4gF4Two_eq_top hyp4.centralizer_trivial Ψ
  subst hGp
  refine ⟨rfl, Subgroup.topEquiv.symm.trans Ψ, fun y => ?_, fun y => ?_⟩
  · have e1' := burnsideF4gF4Two_mem_centralImage marking q hq h1 ⟨y, Subgroup.mem_top y⟩
    have e2' := burnsideF4gF4Two_mem_P₁_iff hK (e1 (Ψ0.symm ⟨y, Subgroup.mem_top y⟩))
    have e3' : Φ (e1 (Ψ0.symm ⟨y, Subgroup.mem_top y⟩)) ∈
        (burnsideF4gF4Two_system hK).P₁.map Φ.toMonoidHom ↔
        e1 (Ψ0.symm ⟨y, Subgroup.mem_top y⟩) ∈ (burnsideF4gF4Two_system hK).P₁ := by
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    rw [hΦ1] at e3'
    exact e3'.trans (e2'.trans e1'.symm)
  · have e1' := burnsideF4gF4Two_mem_centralImage marking q hq h2 ⟨y, Subgroup.mem_top y⟩
    have e2' := burnsideF4gF4Two_mem_P₂_iff hK (e1 (Ψ0.symm ⟨y, Subgroup.mem_top y⟩))
    have e3' : Φ (e1 (Ψ0.symm ⟨y, Subgroup.mem_top y⟩)) ∈
        (burnsideF4gF4Two_system hK).P₂.map Φ.toMonoidHom ↔
        e1 (Ψ0.symm ⟨y, Subgroup.mem_top y⟩) ∈ (burnsideF4gF4Two_system hK).P₂ := by
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    rw [hΦ2] at e3'
    exact e3'.trans (e2'.trans e1'.symm)

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_F4Two_zbar (hyp : HypF_4_31 .F4tw f Gp M₁ M₂ β ε z) (hGp : Gp = ⊤)
    (Ξ : E ≃* ↥twoF4M) (h1 : ∀ y, Ξ y ∈ twoF4M1 ↔ y ∈ M₁) :
    ∃ (zb : E) (hzb : zb ∈ M₁), Ξ zb = zM ∧ burnsideF4d_bOne β ε ⟨zb, hzb⟩ = z := by
  have hz := hyp.z_mem.1 (by decide)
  rw [burnsideF4j_Z1_eq hyp] at hz
  obtain ⟨x, hx1, hxZ, hxz⟩ := mem_subImg.mp hz
  refine ⟨x, hx1, ?_, hxz⟩
  have hbinj := burnsideF4j_bOne_injective hyp
  have hx1' : x ≠ 1 := by
    intro h
    apply hyp.z_inv.1
    rw [← hxz]
    have e : (⟨x, hx1⟩ : ↥M₁) = 1 := Subtype.ext h
    rw [e, map_one]
  have hx2 : x * x = 1 := by
    have e : burnsideF4d_bOne β ε (⟨x, hx1⟩ * ⟨x, hx1⟩) = burnsideF4d_bOne β ε 1 := by
      rw [map_mul, hxz, map_one]
      exact hyp.z_inv.2
    exact congrArg Subtype.val (hbinj e)
  have hmap1 : M₁.map Ξ.toMonoidHom = twoF4M1 := by
    ext w
    obtain ⟨y, rfl⟩ := Ξ.surjective w
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, h1]
  have hxZ' : x ∈ ctr (oPPrime 2 M₁) := by
    rw [hGp, top_inf_eq] at hxZ
    exact hxZ
  have hΞZ : Ξ x ∈ ctr (oPPrime 2 twoF4M1) := by
    rw [← hmap1, burnsideF4gF4TwoInv_oPPrime_map, burnsideF4gF4TwoInv_ctr_map]
    exact Subgroup.mem_map_of_mem _ hxZ'
  rw [burnsideF4gF4TwoInv_twoF4_oPPrime] at hΞZ
  obtain ⟨hΞ1, hΞc⟩ := Subgroup.mem_inf.mp hΞZ
  have hH : ((Ξ x : ↥twoF4M) : Equiv.Perm (Fin 1755)) ∈ twoF4H := hΞ1
  have hc : ∀ y ∈ twoF4H, y * ((Ξ x : ↥twoF4M) : Equiv.Perm (Fin 1755)) =
      ((Ξ x : ↥twoF4M) : Equiv.Perm (Fin 1755)) * y := by
    intro y hy
    have hyM : y ∈ twoF4M := twoF4H_le_twoF4M hy
    have hy1 : (⟨y, hyM⟩ : ↥twoF4M) ∈ twoF4M1 := hy
    have := Subgroup.mem_centralizer_iff.mp hΞc ⟨y, hyM⟩ hy1
    exact congrArg Subtype.val this
  have hsq : ((Ξ x : ↥twoF4M) : Equiv.Perm (Fin 1755)) *
      ((Ξ x : ↥twoF4M) : Equiv.Perm (Fin 1755)) = 1 := by
    have : Ξ x * Ξ x = 1 := by rw [← map_mul, hx2, map_one]
    exact congrArg Subtype.val this
  have hne : ((Ξ x : ↥twoF4M) : Equiv.Perm (Fin 1755)) ≠ 1 := by
    intro h
    apply hx1'
    apply Ξ.injective
    rw [map_one]
    exact Subtype.ext h
  exact Subtype.ext (eq_titsZ_of_central hH hc hsq hne)

theorem burnsideF4m_F_4_35_F4Two (hyp : HypF_4_31 .F4tw f Gp M₁ M₂ β ε z) (hf : f < 3)
    (i j : ↥(M₁ ⊓ M₂)) (hi : (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hj : (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (hi1 : i ≠ 1) (hj1 : j ≠ 1)
    (hi2 : i * i = 1) (hj2 : j * j = 1) :
    ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)) := by
  obtain ⟨hGp, Ξ, h1, h2⟩ := burnsideF4m_F4Two_xi hyp.amalgam hf
  obtain ⟨zb, hzb, hΞz, hbz⟩ := burnsideF4m_F4Two_zbar hyp hGp Ξ h1
  have L := twoF4_F431LieI
  have hnc := burnsideF4m_lieI_hnc hyp Ξ h1 h2 L hzb hΞz hbz (r := 3)
    (by rw [card_twoF4M1]; decide) three_dvd_card_cent_t
  exact burnsideF4m_F_4_35_of_lieI hyp (by decide) (by decide) Ξ h1 h2 L hnc i j hi hj hi1 hi2
    hj1 hj2

end F4Two

end CFSG.ASVolI
