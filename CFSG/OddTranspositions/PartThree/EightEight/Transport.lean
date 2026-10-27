module

public import CFSG.OddTranspositions.Blocks
public import CFSG.OddTranspositions.HypothesisC
public import CFSG.Timmesfeld.Bridge.Asc72Minimal

import CFSG.OddTranspositions.PartThree.EightEight.FibreCentre
import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralBlocks
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.OddTranspositions.PartThree.Nine.ThreeBlocks
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Bridge.Asc73Quotient
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.OddTranspositions.PartThree.Nine

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem xor_exists_mem_blockClass_of_mul_eq (hC : HypothesisC D)
    {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) {N : Subgroup G} {x z r v p q : G}
    (hx : x ∈ centSet D z) (hz2 : z * z = 1) (hzH : z ∈ Halpha D ρ)
    (hzN : z ∉ N)
    (hNmul : ∀ a ∈ DalphaStar D ρ, ∀ b ∈ DalphaStar D ρ, Commute a b → a * b ∈ N)
    (hNinv : ∀ c : G, c ∈ Halpha D ρ → (∀ d ∈ DalphaStar D ρ, Commute c d) →
      c * c = 1 → c ∈ N)
    (hrρ : r ∈ ρ) (hr : r ∈ conjOrbit (localGroup D z) x)
    (hv : v ∈ conjOrbit (localGroup D z) x) (hp : p ∈ conjOrbit (localGroup D z) x)
    (hq : q ∈ conjOrbit (localGroup D z) x)
    (hvpq : v * p * q = z) (hvp : Commute v p) (hvq : Commute v q) (hpq : Commute p q) :
    ((∃ β ∈ blockClass hC.alpha, v ∈ β ∧ p ∈ β) ∧
        ¬ ∃ β ∈ blockClass hC.alpha, v ∈ β ∧ q ∈ β) ∨
      ((∃ β ∈ blockClass hC.alpha, v ∈ β ∧ q ∈ β) ∧
        ¬ ∃ β ∈ blockClass hC.alpha, v ∈ β ∧ p ∈ β) := by
  classical
  have hrD : r ∈ D := (conjOrbit_subset_centSet hC.setup.normal hx hr).1
  have hpD : p ∈ D := (conjOrbit_subset_centSet hC.setup.normal hx hp).1
  have hqD : q ∈ D := (conjOrbit_subset_centSet hC.setup.normal hx hq).1
  obtain ⟨m, hm, hv_eq⟩ := hv
  obtain ⟨n, hn, hr_eq⟩ := hr
  set k : G := m * n⁻¹ with hkdef
  have hkM : k ∈ localGroup D z := by
    rw [hkdef]
    exact (localGroup D z).mul_mem hm ((localGroup D z).inv_mem hn)
  have hkr : k * r * k⁻¹ = v := by
    rw [hkdef, hv_eq, hr_eq]
    group
  have hkr' : k⁻¹ * v * k = r := by
    have h := congrArg (fun t => k⁻¹ * t * k) hkr
    rw [show k⁻¹ * (k * r * k⁻¹) * k = r by group] at h
    exact h.symm
  have hkz : Commute k z := commute_of_mem_localGroup hkM
  set p' : G := k⁻¹ * p * k with hp'def
  set q' : G := k⁻¹ * q * k with hq'def
  have hp'D : p' ∈ D := by
    rw [hp'def]
    simpa using hC.setup.conj_mem k⁻¹ hpD
  have hq'D : q' ∈ D := by
    rw [hq'def]
    simpa using hC.setup.conj_mem k⁻¹ hqD
  have hrp' : Commute r p' := by
    simpa [hp'def, hkr'] using hvp.conj k⁻¹
  have hrq' : Commute r q' := by
    simpa [hq'def, hkr'] using hvq.conj k⁻¹
  have hp'q' : Commute p' q' := by
    simpa [hp'def, hq'def] using hpq.conj k⁻¹
  have hkz' : k⁻¹ * z * k = z := by
    rw [hkz.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  have hrpq : r * p' * q' = z := by
    have h := congrArg (fun t => k⁻¹ * t * k) hvpq
    rw [hkz'] at h
    calc r * p' * q' = k⁻¹ * (v * p * q) * k := by rw [← hkr', hp'def, hq'def]; group
      _ = z := h
  have hp'2 : p' * p' = 1 := hC.setup.oddT.mul_self_eq_one hp'D
  have hq'2 : q' * q' = 1 := hC.setup.oddT.mul_self_eq_one hq'D
  have hr_eq' : r = z * q' * p' := by
    have h1 : r * p' = z * q' := by
      have h := congrArg (fun t => t * q') hrpq
      simpa [mul_assoc, hq'2] using h
    have h := congrArg (fun t => t * p') h1
    simpa [mul_assoc, hp'2] using h
  have hsplitp : p' ∈ ρ ∨ p' ∈ DalphaStar D ρ :=
    mem_block_or_DalphaStar_of_commute hC hρ hrρ hp'D hrp'
  have hsplitq : q' ∈ ρ ∨ q' ∈ DalphaStar D ρ :=
    mem_block_or_DalphaStar_of_commute hC hρ hrρ hq'D hrq'
  have hdisj : Disjoint ρ (DalphaStar D ρ) :=
    disjoint_alpha_DalphaStar (isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hρ)
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hρ
  have hkρ : (fun t => k * t * k⁻¹) '' ρ ∈ blockClass hC.alpha := by
    rw [hg]
    refine mem_blockClass_iff.mpr ⟨k * g, ?_⟩
    rw [Set.image_image]
    have hfun : (fun x => k * (g * x * g⁻¹) * k⁻¹) =
        (fun x => (k * g) * x * (k * g)⁻¹) := by
      funext x
      group
    rw [hfun]
  have hv_mem : v ∈ (fun t => k * t * k⁻¹) '' ρ := ⟨r, hrρ, hkr⟩
  have hp'_iff : p' ∈ ρ ↔ ∃ β ∈ blockClass hC.alpha, v ∈ β ∧ p ∈ β := by
    constructor
    · intro hpρ
      exact ⟨_, hkρ, hv_mem, ⟨p', hpρ, by rw [hp'def]; group⟩⟩
    · rintro ⟨β, hβ, hvβ, hpβ⟩
      have hβeq : β = (fun t => k * t * k⁻¹) '' ρ :=
        eq_of_mem_of_mem_blockClass hC.isBlock_alpha hβ hkρ ⟨v, hvβ, hv_mem⟩
      rw [hβeq] at hpβ
      obtain ⟨a, ha, hap⟩ := hpβ
      have hsimp : k⁻¹ * (k * a * k⁻¹) * k = a := by group
      rw [hp'def, ← hap, hsimp]
      exact ha
  have hq'_iff : q' ∈ ρ ↔ ∃ β ∈ blockClass hC.alpha, v ∈ β ∧ q ∈ β := by
    constructor
    · intro hqρ
      exact ⟨_, hkρ, hv_mem, ⟨q', hqρ, by rw [hq'def]; group⟩⟩
    · rintro ⟨β, hβ, hvβ, hqβ⟩
      have hβeq : β = (fun t => k * t * k⁻¹) '' ρ :=
        eq_of_mem_of_mem_blockClass hC.isBlock_alpha hβ hkρ ⟨v, hvβ, hv_mem⟩
      rw [hβeq] at hqβ
      obtain ⟨a, ha, haq⟩ := hqβ
      have hsimp : k⁻¹ * (k * a * k⁻¹) * k = a := by group
      rw [hq'def, ← haq, hsimp]
      exact ha
  rcases hsplitp with hpρ | hpS <;> rcases hsplitq with hqρ | hqS
  ·
    exfalso
    apply hzN
    have hzcomm : ∀ d ∈ DalphaStar D ρ, Commute z d := by
      intro d hd
      rw [← hrpq]
      exact ((commute_of_mem_of_mem_DalphaStar hrρ hd).mul_left
        (commute_of_mem_of_mem_DalphaStar hpρ hd)).mul_left
        (commute_of_mem_of_mem_DalphaStar hqρ hd)
    exact hNinv z hzH hzcomm hz2
  ·
    refine Or.inl ⟨hp'_iff.mp hpρ, fun h => ?_⟩
    exact (Set.disjoint_right.mp hdisj hqS) (hq'_iff.mpr h)
  ·
    refine Or.inr ⟨hq'_iff.mp hqρ, fun h => ?_⟩
    exact (Set.disjoint_right.mp hdisj hpS) (hp'_iff.mpr h)
  ·
    exfalso
    apply hzN
    have hrH : r ∈ Halpha D ρ := by
      rw [hr_eq']
      exact (Halpha D ρ).mul_mem ((Halpha D ρ).mul_mem hzH (Subgroup.subset_closure hqS))
        (Subgroup.subset_closure hpS)
    have hr2 : r * r = 1 := hC.setup.oddT.mul_self_eq_one hrD
    have hrcomm : ∀ d ∈ DalphaStar D ρ, Commute r d :=
      fun d hd => commute_of_mem_of_mem_DalphaStar hrρ hd
    have hrN : r ∈ N := hNinv r hrH hrcomm hr2
    have hpqN : p' * q' ∈ N := hNmul p' hpS q' hqS hp'q'
    have hmem : z ∈ N := by
      rw [← hrpq, show r * p' * q' = r * (p' * q') from by group]
      exact N.mul_mem hrN hpqN
    exact hmem

theorem mem_or_mem_or_mem_of_mem_conjOrbit (hC : HypothesisC D)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x y e : G} (hx : x ∈ D) (hy : y ∈ D) (he : e ∈ D) (hxy : Commute x y) (hxe : Commute x e)
    (hye : Commute y e) (hyO : y ∈ conjOrbit (localGroup D (x * y * e)) x)
    (heO : e ∈ conjOrbit (localGroup D (x * y * e)) x) {r : G}
    (hr : r ∈ conjOrbit (localGroup D (x * y * e)) x) (hrx : Commute r x) (hry : Commute r y)
    {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) (hrρ : r ∈ ρ) : x ∈ ρ ∨ y ∈ ρ ∨ e ∈ ρ := by
  classical
  set z : G := x * y * e with hzdef
  have hx2 : x * x = 1 := hC.setup.oddT.mul_self_eq_one hx
  have hy2 : y * y = 1 := hC.setup.oddT.mul_self_eq_one hy
  have he2 : e * e = 1 := hC.setup.oddT.mul_self_eq_one he
  have hx2' : x ^ 2 = 1 := by rw [pow_two]; exact hx2
  have hy2' : y ^ 2 = 1 := by rw [pow_two]; exact hy2
  have he2' : e ^ 2 = 1 := by rw [pow_two]; exact he2
  have hxy2 : (x * y) ^ 2 = 1 := by rw [hxy.mul_pow, hx2', hy2', mul_one]
  have hze : Commute (x * y) e := hxe.mul_left hye
  have hz2 : z * z = 1 := by
    rw [hzdef, ← pow_two, hze.mul_pow, hxy2, he2', mul_one]
  have hxz : Commute x z := ((Commute.refl x).mul_right hxy).mul_right hxe
  have hxcent : x ∈ centSet D z := ⟨hx, hxz⟩
  have hrz : Commute r z := (conjOrbit_subset_centSet hC.setup.normal hxcent hr).2
  have hxy2' : (x * y) * (x * y) = 1 := by rw [← pow_two]; exact hxy2
  have he_eq : x * y * z = e := by
    rw [hzdef]
    calc x * y * (x * y * e) = (x * y * (x * y)) * e := by group
      _ = e := by rw [hxy2', one_mul]
  have hre : Commute r e := by
    rw [← he_eq]
    exact (hrx.mul_right hry).mul_right hrz
  by_contra hcon
  push Not at hcon
  obtain ⟨hxρ, hyρ, heρ⟩ := hcon
  have hxS : x ∈ DalphaStar D ρ :=
    (mem_block_or_DalphaStar_of_commute hC hρ hrρ hx hrx).resolve_left hxρ
  have hyS : y ∈ DalphaStar D ρ :=
    (mem_block_or_DalphaStar_of_commute hC hρ hrρ hy hry).resolve_left hyρ
  have heS : e ∈ DalphaStar D ρ :=
    (mem_block_or_DalphaStar_of_commute hC hρ hrρ he hre).resolve_left heρ
  have hzH : z ∈ Halpha D ρ := by
    rw [hzdef]
    exact (Halpha D ρ).mul_mem ((Halpha D ρ).mul_mem (Subgroup.subset_closure hxS)
      (Subgroup.subset_closure hyS)) (Subgroup.subset_closure heS)
  have hxyN : x * y ∈ fibreSubgroup D ρ :=
    mul_mem_fibreSubgroup_of_commute hC hρ hxS hyS hxy
  have hzN : z ∉ fibreSubgroup D ρ := by
    intro hzmem
    have heN : e ∈ fibreSubgroup D ρ := by
      rw [← he_eq]
      exact (fibreSubgroup D ρ).mul_mem hxyN hzmem
    exact notMem_fibreSubgroup hC hne hρ heS heN
  have hNmul : ∀ a ∈ DalphaStar D ρ, ∀ b ∈ DalphaStar D ρ, Commute a b →
      a * b ∈ fibreSubgroup D ρ := fun a ha b hb hab =>
    mul_mem_fibreSubgroup_of_commute hC hρ ha hb hab
  have hNinv : ∀ c : G, c ∈ Halpha D ρ → (∀ d ∈ DalphaStar D ρ, Commute c d) →
      c * c = 1 → c ∈ fibreSubgroup D ρ := fun c hc hcd hc2 =>
    mem_fibreSubgroup_of_forall_commute hC hne hρ hc hcd hc2
  have hX1 : ((∃ β ∈ blockClass hC.alpha, x ∈ β ∧ y ∈ β) ∧
      ¬ ∃ β ∈ blockClass hC.alpha, x ∈ β ∧ e ∈ β) ∨
      ((∃ β ∈ blockClass hC.alpha, x ∈ β ∧ e ∈ β) ∧
        ¬ ∃ β ∈ blockClass hC.alpha, x ∈ β ∧ y ∈ β) :=
    xor_exists_mem_blockClass_of_mul_eq hC hρ hxcent hz2 hzH hzN hNmul hNinv hrρ hr
      (self_mem_conjOrbit (localGroup D z) x) hyO heO hzdef.symm hxy hxe hye
  have hyxe : y * x * e = z := by rw [← hxy.eq]
  have hX2 : ((∃ β ∈ blockClass hC.alpha, y ∈ β ∧ x ∈ β) ∧
      ¬ ∃ β ∈ blockClass hC.alpha, y ∈ β ∧ e ∈ β) ∨
      ((∃ β ∈ blockClass hC.alpha, y ∈ β ∧ e ∈ β) ∧
        ¬ ∃ β ∈ blockClass hC.alpha, y ∈ β ∧ x ∈ β) :=
    xor_exists_mem_blockClass_of_mul_eq hC hρ hxcent hz2 hzH hzN hNmul hNinv hrρ hr
      hyO (self_mem_conjOrbit (localGroup D z) x) heO hyxe hxy.symm hye hxe
  have hexy : e * x * y = z := by
    calc e * x * y = x * e * y := by rw [hxe.symm.eq]
      _ = x * (e * y) := by group
      _ = x * (y * e) := by rw [hye.symm.eq]
      _ = x * y * e := by group
      _ = z := hzdef.symm
  have hX3 : ((∃ β ∈ blockClass hC.alpha, e ∈ β ∧ x ∈ β) ∧
      ¬ ∃ β ∈ blockClass hC.alpha, e ∈ β ∧ y ∈ β) ∨
      ((∃ β ∈ blockClass hC.alpha, e ∈ β ∧ y ∈ β) ∧
        ¬ ∃ β ∈ blockClass hC.alpha, e ∈ β ∧ x ∈ β) :=
    xor_exists_mem_blockClass_of_mul_eq hC hρ hxcent hz2 hzH hzN hNmul hNinv hrρ hr
      heO (self_mem_conjOrbit (localGroup D z) x) hyO hexy hxe.symm hye.symm hxy
  let R : G → G → Prop := fun a b => ∃ β ∈ blockClass hC.alpha, a ∈ β ∧ b ∈ β
  have hRsymm : ∀ a b : G, R a b → R b a := by
    rintro a b ⟨β, hβ, haβ, hbβ⟩
    exact ⟨β, hβ, hbβ, haβ⟩
  have hRtrans : ∀ a b c : G, R a b → R b c → R a c := by
    rintro a b c ⟨β, hβ, haβ, hbβ⟩ ⟨γ, hγ, hbγ, hcγ⟩
    have hβγ : β = γ :=
      eq_of_mem_of_mem_blockClass hC.isBlock_alpha hβ hγ ⟨b, hbβ, hbγ⟩
    refine ⟨β, hβ, haβ, ?_⟩
    rw [hβγ]
    exact hcγ
  rcases hX1 with ⟨hxyR, hxeR⟩ | ⟨hxeR, hxyR⟩
  · rcases hX3 with ⟨hexR, -⟩ | ⟨heyR, -⟩
    · exact hxeR (hRsymm e x hexR)
    · exact hxeR (hRtrans x y e hxyR (hRsymm e y heyR))
  · rcases hX2 with ⟨hyxR, -⟩ | ⟨hyeR, -⟩
    · exact hxyR (hRsymm y x hyxR)
    · exact hxyR (hRtrans x e y hxeR (hRsymm y e hyeR))

end CFSG.OddTranspositions.PartThree.EightEight

end
