module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXGT
public import CFSG.Milestones.ASVolI.I3Components
public import CFSG.Goldschmidt.Steps.G37Basic

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

open CFSG.Open
open scoped commutatorElement

theorem oddCore_le_center_of_even {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hev : 2 ∣ Nat.card K) : CFSG.oddCore K ≤ Subgroup.center K := by
  rcases normal_le_center_or_top hK (CFSG.oddCore K) with h | h
  · exact h
  · exfalso
    have hodd := CFSG.ABGTheoremB.odd_card_oddCore K
    rw [h, Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hev)

theorem oddCore_centralizes_iSup {Γ : Type} [Group Γ] {K : Subgroup Γ}
    (hcen : ∀ o ∈ CFSG.oddCore Γ, ∀ k ∈ K, o * k = k * o) :
    ∀ o ∈ CFSG.oddCore Γ, ∀ j ∈ (⨆ g : Γ, CFSG.conjugate K g), o * j = j * o := by
  intro o ho j hj
  have hle : (⨆ g : Γ, CFSG.conjugate K g) ≤ Subgroup.centralizer ({o} : Set Γ) := by
    refine iSup_le fun g => ?_
    rintro k ⟨k₀, hk₀, rfl⟩
    have hOn : (CFSG.oddCore Γ).Normal := inferInstance
    have hn : g * o * g⁻¹ ∈ CFSG.oddCore Γ := hOn.conj_mem o ho g
    have hc := hcen (g * o * g⁻¹) hn k₀ hk₀
    have hmain : o * (g⁻¹ * k₀ * g) = (g⁻¹ * k₀ * g) * o := by
      calc o * (g⁻¹ * k₀ * g) = g⁻¹ * ((g * o * g⁻¹) * k₀) * g := by group
        _ = g⁻¹ * (k₀ * (g * o * g⁻¹)) * g := by rw [hc]
        _ = (g⁻¹ * k₀ * g) * o := by group
    have e : (MulAut.conj g⁻¹).toMonoidHom k₀ = g⁻¹ * k₀ * g := by
      simp [MulAut.conj_apply]
    rw [e, Subgroup.mem_centralizer_singleton_iff]
    exact hmain.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hj)).symm

theorem isCComponent_of_twoComp_top {Γ : Type} [Group Γ] [Finite Γ] {J : Subgroup Γ}
    (hJ : CFSG.ASVolI.ChIJK.IsTwoComponentIn J ⊤) : CFSG.IsCComponent J :=
  CFSG.Quasithin.mem_cComp_top_iff_isCComponent.mp
    (CFSG.ASVolI.burnsideI31_mem_cComp_iff.mpr ⟨le_top, hJ.1.2⟩)

theorem twoComp_quasisimple {Γ : Type} [Group Γ] [Finite Γ] {J : Subgroup Γ}
    (hJ : CFSG.ASVolI.ChIJK.IsTwoComponentIn J ⊤)
    (hcenJ : ∀ o ∈ CFSG.oddCore Γ, ∀ j ∈ J, o * j = j * o) :
    CFSG.IsQuasisimple ↥J ∧ CFSG.oddCore ↥J ≤ Subgroup.center ↥J := by
  have hc := isCComponent_of_twoComp_top hJ
  have hP : Group.IsPerfect ↥J := isPerfect_of_commutator_eq hc.2.1
  have hOJ : CFSG.oddCore ↥J ≤ Subgroup.center ↥J := by
    have hNJ : (CFSG.oddCore ↥J).map J.subtype ≤ J := Subgroup.map_subtype_le _
    have hsub : ((CFSG.oddCore ↥J).map J.subtype).subgroupOf J = CFSG.oddCore ↥J := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hxy : y = x := Subtype.ext hyx
        rw [← hxy]
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hsn : ((CFSG.oddCore ↥J).map J.subtype).IsSubnormal := by
      have hnorm : (((CFSG.oddCore ↥J).map J.subtype).subgroupOf J).IsSubnormal := by
        rw [hsub]
        exact Subgroup.Normal.isSubnormal (inferInstance : (CFSG.oddCore ↥J).Normal)
      exact Subgroup.IsSubnormal.trans hNJ hnorm hc.2.2.1
    have hodd : Odd (Nat.card ↥((CFSG.oddCore ↥J).map J.subtype)) := by
      rw [Subgroup.card_map_of_injective J.subtype_injective]
      exact CFSG.ABGTheoremB.odd_card_oddCore ↥J
    have hle := CFSG.Goldschmidt.G37.le_pPrimeCore_of_isSubnormal_of_odd hsn hodd
    rw [← CFSG.ASVolI.burnsideI31_oddCore_eq Γ] at hle
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hxO : (x : Γ) ∈ CFSG.oddCore Γ := hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    simp only [Subgroup.coe_mul]
    exact (hcenJ _ hxO _ g.2).symm
  exact ⟨isQuasisimple_of_quot_le_center hP (CFSG.oddCore ↥J) hOJ hJ.2, hOJ⟩

theorem twoComp_oddTwoCore_le_center {Γ : Type} [Group Γ] [Finite Γ] {J : Subgroup Γ}
    (hJ : CFSG.ASVolI.ChIJK.IsTwoComponentIn J ⊤)
    (hOJ : CFSG.oddCore ↥J ≤ Subgroup.center ↥J)
    (hO22 : CFSG.ASVolI.ChIJK.oddTwoCore ↥J ≠ ⊤) :
    CFSG.ASVolI.ChIJK.oddTwoCore ↥J ≤ Subgroup.center ↥J := by
  have hP : Group.IsPerfect ↥J := isPerfect_of_commutator_eq (isCComponent_of_twoComp_top hJ).2.1
  have hQ : CFSG.IsQuasisimple (↥J ⧸ CFSG.oddCore ↥J) := hJ.2
  have hPne : CFSG.pCore 2 (↥J ⧸ CFSG.oddCore ↥J) ≠ ⊤ := by
    intro htop
    apply hO22
    unfold CFSG.ASVolI.ChIJK.oddTwoCore
    rw [htop, Subgroup.comap_top]
  have hPle : CFSG.pCore 2 (↥J ⧸ CFSG.oddCore ↥J) ≤ Subgroup.center (↥J ⧸ CFSG.oddCore ↥J) :=
    (normal_le_center_or_top hQ _).resolve_right hPne
  intro x hx
  have hxP : QuotientGroup.mk' (CFSG.oddCore ↥J) x ∈
      CFSG.pCore 2 (↥J ⧸ CFSG.oddCore ↥J) := hx
  have hxZ := hPle hxP
  refine central_of_commutator_central hP.commutator_eq_top x (fun q => hOJ ?_)
  have h1 : QuotientGroup.mk' (CFSG.oddCore ↥J) ⁅x, q⁆ = 1 := by
    have hcq := Subgroup.mem_center_iff.mp hxZ (QuotientGroup.mk' (CFSG.oddCore ↥J) q)
    simp only [commutatorElement_def, map_mul, map_inv]
    rw [← hcq]
    group
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem normalizer_of_map_eq {Γ : Type} [Group Γ] {L : Subgroup Γ} {g : Γ}
    (h : L.map (MulAut.conj g).toMonoidHom = L) : g ∈ Subgroup.normalizer (L : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hm : (MulAut.conj g).toMonoidHom x ∈ L.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [h] at hm
    exact hm
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyx' : y = x := by
      have h2 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      exact mul_left_cancel (mul_right_cancel h2)
    rw [← hyx']
    exact hy

theorem isComponentOf_top_of_quasisimple {Γ : Type} [Group Γ] {L : Subgroup Γ}
    (hL : L.IsSubnormal) (hq : CFSG.IsQuasisimple ↥L) : CFSG.Open.IsComponentOf L ⊤ :=
  ⟨le_top, (CFSG.Quasithin.A3.subnormal_top_iff).mpr hL, hq.1.commutator_eq_top, hq.2.1⟩

theorem isComponentOf_top_conj {Γ : Type} [Group Γ] {L : Subgroup Γ}
    (hL : L.IsSubnormal) (hq : CFSG.IsQuasisimple ↥L) (g : Γ) :
    CFSG.Open.IsComponentOf (CFSG.conjugate L g) ⊤ := by
  refine isComponentOf_top_of_quasisimple
    (hL.map (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).surjective) ?_
  exact CFSG.IsQuasisimple.of_mulEquiv
    (L.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm hq

end CFSG.Quasithin.H13.Ch4.J4KX

end
