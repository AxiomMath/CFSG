module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShapes
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedF2Aux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.ComponentClassification.PerfectAutomorphisms

theorem fourGroupInnerOn_of_facts (Sh : ShapePred)
    (hSh : ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), Sh L → OddShape5 L)
    (hB : ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), Sh L →
      OuterFixedNoNormalTwo (↥L ⧸ Subgroup.center ↥L))
    (hC : ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), Sh L →
      OuterFixedRigid (↥L ⧸ Subgroup.center ↥L)) :
    FourGroupInnerOn Sh := by
  intro Y _ _ L A hLsh hAN hAe hA4 hAC hK
  by_contra hnot
  have hnot' : ¬ ∀ x : Y, x ∈ A → x ∈ L ⊔ Subgroup.centralizer (L : Set Y) := hnot
  obtain ⟨β, hβimp⟩ := not_forall.mp hnot'
  obtain ⟨hβA, hβnot⟩ := not_imp.mp hβimp
  obtain ⟨hq, hodd, _⟩ := hSh Y L hLsh
  haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
  haveI : Finite ↥L := Subtype.finite
  have hNoTwo : OuterFixedNoNormalTwo (↥L ⧸ Subgroup.center ↥L) := hB Y L hLsh
  have hRigid : OuterFixedRigid (↥L ⧸ Subgroup.center ↥L) := hC Y L hLsh
  have hmem : ∀ a ∈ A, a = 1 ∨ a = β := by
    intro a haA
    have ha2 : a * a = 1 := by simpa [pow_two] using hAe.2 a haA
    have hβ2 : β * β = 1 := by simpa [pow_two] using hAe.2 β hβA
    have haβ : a * β = β * a := by
      haveI : IsMulCommutative A := hAe.1
      exact congrArg Subtype.val (mul_comm' (⟨a, haA⟩ : A) ⟨β, hβA⟩)
    have hαβNotInner : ¬ ∃ g : ↥L, ∀ z : ↥L,
        wccg_conjAut L β (hAN hβA) z = g * z * g⁻¹ :=
      wccg_conjAut_not_inner_of_not_mem_sup (hAN hβA) hβnot
    let γa : MulAut (↥L ⧸ Subgroup.center ↥L) :=
      onCenterQuotient (wccg_conjAut L a (hAN haA))
    let γβ : MulAut (↥L ⧸ Subgroup.center ↥L) :=
      onCenterQuotient (wccg_conjAut L β (hAN hβA))
    have hγa2 : γa * γa = 1 := by
      rw [show γa * γa = onCenterQuotient (wccg_conjAut L a (hAN haA) *
            wccg_conjAut L a (hAN haA)) from (wccg_onCenterQuotient_mul _ _).symm,
          wccg_conjAut_mul_self L a (hAN haA) ha2]
      exact map_one (centerQuotientHom ↥L)
    have hγβ2 : γβ * γβ = 1 := by
      rw [show γβ * γβ = onCenterQuotient (wccg_conjAut L β (hAN hβA) *
            wccg_conjAut L β (hAN hβA)) from (wccg_onCenterQuotient_mul _ _).symm,
          wccg_conjAut_mul_self L β (hAN hβA) hβ2]
      exact map_one (centerQuotientHom ↥L)
    have hγβNotInner : ¬ ∃ g : ↥L ⧸ Subgroup.center ↥L,
        ∀ z : ↥L ⧸ Subgroup.center ↥L, γβ z = g * z * g⁻¹ := by
      rintro ⟨g, hg⟩
      exact hαβNotInner (isInner_of_onCenterQuotient_inner _
        ⟨g, fun z => hg z⟩)
    have hcomm : γa * γβ = γβ * γa := by
      rw [show γa * γβ = onCenterQuotient (wccg_conjAut L a (hAN haA) *
            wccg_conjAut L β (hAN hβA)) from (wccg_onCenterQuotient_mul _ _).symm,
          show γβ * γa = onCenterQuotient (wccg_conjAut L β (hAN hβA) *
            wccg_conjAut L a (hAN haA)) from (wccg_onCenterQuotient_mul _ _).symm,
          wccg_conjAut_mul_comm L a β (hAN haA) (hAN hβA) haβ]
    have hfix : ∀ u : ↥L ⧸ Subgroup.center ↥L, γβ u = u → γa u = u := by
      intro u hu
      obtain ⟨x, hxfix, hxeq⟩ := exists_fixed_lift_centerQuotient hodd
        (wccg_conjAut L β (hAN hβA)) (wccg_conjAut_mul_self L β (hAN hβA) hβ2) u hu
      have hxβ : (x : Y) * β = β * (x : Y) := by
        have h1 := congrArg (fun z : ↥L => (z : Y)) hxfix
        have hc : β * (x : Y) * β⁻¹ = (x : Y) := by
          simpa [wccg_conjAut_apply_coe] using h1
        calc (x : Y) * β = (β * (x : Y) * β⁻¹) * β := by rw [hc]
          _ = β * (x : Y) := by group
      have hxa : (x : Y) * a * (x : Y)⁻¹ = a := by
        simpa only [Subgroup.coe_inv] using
          wccg_conj_eq_of_forall_fixed hAe hK hAN haA hβA hq hodd hNoTwo hβnot x.2 hxβ
      rw [← hxeq]
      show onCenterQuotient (wccg_conjAut L a (hAN haA))
          ((QuotientGroup.mk' (Subgroup.center ↥L)) x) =
        (QuotientGroup.mk' (Subgroup.center ↥L)) x
      rw [onCenterQuotient_apply_mk]
      congr 1
      apply Subtype.ext
      have hax' : (x : Y) * a = a * (x : Y) := by
        calc (x : Y) * a = ((x : Y) * a * (x : Y)⁻¹) * (x : Y) := by group
          _ = a * (x : Y) := by rw [hxa]
      have hax : a * (x : Y) = (x : Y) * a := hax'.symm
      rw [wccg_conjAut_apply_coe, hax, mul_assoc, mul_inv_cancel, mul_one]
    rcases hRigid γβ hγβ2 hγβNotInner γa hγa2 hcomm hfix with h1 | h2
    · left
      have hαa1 : wccg_conjAut L a (hAN haA) = 1 :=
        onCenterQuotient_eq_one_imp _ (by simpa [γa] using h1)
      have haC : a ∈ Subgroup.centralizer (L : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h := congrArg (fun f : MulAut ↥L => f ⟨y, hy⟩) hαa1
        have hay : a * y * a⁻¹ = y := by
          simpa [wccg_conjAut_apply_coe] using congrArg (fun z : ↥L => (z : Y)) h
        have hay' : a * y = y * a := by
          calc a * y = (a * y * a⁻¹) * a := by group
            _ = y * a := by rw [hay]
        exact hay'.symm
      have haz : a ∈ A ⊓ Subgroup.centralizer (L : Set Y) :=
        Subgroup.mem_inf.mpr ⟨haA, haC⟩
      rw [hAC] at haz
      exact Subgroup.mem_bot.mp haz
    · right
      have hone : onCenterQuotient (wccg_conjAut L a (hAN haA) *
          (wccg_conjAut L β (hAN hβA))⁻¹) = 1 := by
        rw [wccg_onCenterQuotient_mul, wccg_onCenterQuotient_inv]
        change γa * γβ⁻¹ = 1
        rw [h2, mul_inv_cancel]
      have hαeq : wccg_conjAut L a (hAN haA) = wccg_conjAut L β (hAN hβA) :=
        mul_inv_eq_one.mp (onCenterQuotient_eq_one_imp _ hone)
      have haβC : a⁻¹ * β ∈ Subgroup.centralizer (L : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h := congrArg (fun f : MulAut ↥L => f ⟨y, hy⟩) hαeq
        have hyconj : a * y * a⁻¹ = β * y * β⁻¹ := by
          simpa [wccg_conjAut_apply_coe] using congrArg (fun z : ↥L => (z : Y)) h
        have hconj : (a⁻¹ * β) * y * (a⁻¹ * β)⁻¹ = y := by
          rw [show (a⁻¹ * β) * y * (a⁻¹ * β)⁻¹ =
              a⁻¹ * (β * y * β⁻¹) * a by group, ← hyconj]
          group
        have hcomm' : (a⁻¹ * β) * y = y * (a⁻¹ * β) := by
          calc (a⁻¹ * β) * y =
                ((a⁻¹ * β) * y * (a⁻¹ * β)⁻¹) * (a⁻¹ * β) := by group
            _ = y * (a⁻¹ * β) := by rw [hconj]
        exact hcomm'.symm
      have haz : a⁻¹ * β ∈ A ⊓ Subgroup.centralizer (L : Set Y) :=
        Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem haA) hβA, haβC⟩
      rw [hAC] at haz
      have h1 : a⁻¹ * β = 1 := Subgroup.mem_bot.mp haz
      have hβeq : β = a := by
        calc β = a * (a⁻¹ * β) := by group
          _ = a * 1 := by rw [h1]
          _ = a := mul_one a
      exact hβeq.symm
  have hcard : Nat.card ↥A ≤ 2 := by
    classical
    have h := Nat.card_le_card_of_injective
      (fun a : ↥A => if (a : Y) = 1 then (0 : Fin 2) else 1) (by
        intro u v huv
        change (if (u : Y) = 1 then (0 : Fin 2) else 1) =
          (if (v : Y) = 1 then (0 : Fin 2) else 1) at huv
        have hu := hmem u u.2
        have hv := hmem v v.2
        by_cases hu1 : (u : Y) = 1
        · have hfu : (if (u : Y) = 1 then (0 : Fin 2) else 1) = 0 := if_pos hu1
          rw [hfu] at huv
          have hv1 : (v : Y) = 1 := by
            by_contra hvne
            rw [if_neg hvne] at huv
            exact Fin.zero_ne_one huv
          exact Subtype.ext (hu1.trans hv1.symm)
        · have hfu : (if (u : Y) = 1 then (0 : Fin 2) else 1) = 1 := if_neg hu1
          rw [hfu] at huv
          have hv1 : (v : Y) ≠ 1 := by
            intro hv1
            rw [if_pos hv1] at huv
            exact Fin.zero_ne_one huv.symm
          rcases hu with hu | hu
          · exact absurd hu hu1
          · rcases hv with hv | hv
            · exact absurd hv hv1
            · exact Subtype.ext (hu.trans hv.symm))
    simpa only [Nat.card_fin] using h
  rw [hA4] at hcard
  omega

end CFSG.LocalAnalysis.WeakClosure81

end
