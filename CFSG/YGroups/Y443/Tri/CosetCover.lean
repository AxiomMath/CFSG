module

public import CFSG.Monster.Tri.CosetCover
public import CFSG.YGroups.Y443.Native.Surjective
public import CFSG.YGroups.Y443.Tri.Parabolic2
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6006
public import Certificates.Certificate6007
public import Certificates.Certificate6009
public import Certificates.Certificate6010
public import Certificates.Certificate6011
public import Certificates.Certificate6012
public import Certificates.Certificate6013
public import Certificates.Certificate6014
public import Certificates.Certificate6015
public import Certificates.Certificate6016
public import Certificates.Certificate6017
public import Certificates.Certificate6018
public import Certificates.Certificate10093
public import Certificates.Certificate10098
public import Certificates.Certificate10103
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10115
public import Certificates.Certificate10116
public import Certificates.Certificate10117
public import Certificates.Certificate10118
public import Certificates.Certificate10119
public import Certificates.Certificate10123
public import Certificates.Certificate10127
public import Certificates.Certificate16018
public import Certificates.Certificate16026
public import CFSG.Monster.AxisCount.BabyCoverSpec
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.GMS CFSG.Open
open CFSG.Monster.B.Recog (cosetGraph)
open CFSG.Monster.Tri (baseVertex coe_baseVertex longTri)

theorem y443_Y_comm_C :
    y443Y * y443C = y443C * y443Y := y443C_comm_H y443Y_mem_H

theorem y443S_inv :
    y443S⁻¹ = y443S := inv_eq_of_mul_eq_one_right y443S_mul_self

theorem y443S_conj
    (hcx : (y443C * y443X) ^ 3 = 1) : y443S * y443C * y443S = y443Y :=
  CFSG.Monster.Tri.coxeter_conj y443X_mul_self y443C_mul_self y443Y_mul_self
    y443_Y_comm_C.symm hcx y443_xy_cube

theorem fM_c_mul_self :
    fM y443C * fM y443C = 1 := by
  rw [← map_mul, y443C_mul_self, map_one]

theorem fM_c_ne_one :
    fM y443C ≠ 1 := fun h => fM_y443C_ne_one (by rw [h]; rfl)

theorem y443C_comm_H' :

    ∀ h ∈ y443H, h * y443C = y443C * h := fun _ hh => y443C_comm_H hh

theorem Hbar_conj_eq_Cgen
    (hN : Q343N ≤ Nat.card (y443H.map fM)) :
    ((y443H.map fM).map Gmat.subtype).map (MulAut.conj (wordLin omegaWord)).toMonoidHom = Cgen := by
  have hcard : Nat.card (((y443H.map fM).map Gmat.subtype).map
      (MulAut.conj (wordLin omegaWord)).toMonoidHom) = Nat.card (y443H.map fM) := by
    rw [natCard_map_conj, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hG : Finite Gmat := finite_Gmat
  have hfin : Finite Cgen :=
    Finite.of_injective (Subgroup.inclusion Cgen_le_Gmat) (Subgroup.inclusion_injective _)
  exact Subgroup.eq_of_le_of_card_ge Hbar_conj_le_Cgen
    (by rw [natCard_Cgen_eq_Q343N, hcard]; exact hN)

theorem Hbar_eq_centralizer
    (hN : Q343N ≤ Nat.card (y443H.map fM)) :
    y443H.map fM = Subgroup.centralizer {fM y443C} := by
  have heq := Hbar_conj_eq_Cgen hN
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, y443C_comm_H hh]
  · intro hg
    have h1 : ((g : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ∈
        Gmat ⊓ Subgroup.centralizer {((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB)} := by
      refine Subgroup.mem_inf.2 ⟨g.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
    rw [centralizer_fMc_eq] at h1
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 h1
    rw [← heq] at hy
    obtain ⟨_, ⟨_, ⟨h, hh, rfl⟩, rfl⟩, rfl⟩ := hy
    have hgh : g = fM h := by
      apply Subtype.ext
      rw [← hyg]
      simp [MulAut.conj_apply, mul_assoc]
    rw [hgh]
    exact Subgroup.mem_map_of_mem fM hh

theorem fM_S_conj
    (hcx : (fM y443C * fM y443X) ^ 3 = 1) :
    fM y443S * fM y443C * fM y443S = fM y443Y := by
  have h := CFSG.Monster.Tri.coxeter_conj (x := fM y443X) (c := fM y443C) (y := fM y443Y)
    (by rw [← map_mul, y443X_mul_self, map_one]) fM_c_mul_self
    (by rw [← map_mul, y443Y_mul_self, map_one])
    (by rw [← map_mul, ← map_mul, y443_Y_comm_C.symm]) hcx
    (by rw [← map_mul, ← map_pow, y443_xy_cube, map_one])
  simpa [y443S, map_mul] using h

theorem fM_cx_cube_of_source
    (hcx : (y443C * y443X) ^ 3 = 1) :
    (fM y443C * fM y443X) ^ 3 = 1 := by
  rw [← map_mul, ← map_pow, hcx, map_one]

theorem coe_fM_S_smul
    (hcx : (fM y443C * fM y443X) ^ 3 = 1) :
    ((fM y443S • baseVertex (fM y443C) : ConjVert (fM y443C)) : Gmat) = fM y443Y := by
  rw [coe_smul_conjVert, coe_baseVertex, ← map_inv, y443S_inv, fM_S_conj hcx]

theorem y443_adj
    (hcx : (fM y443C * fM y443X) ^ 3 = 1)
    (hcy : IsConj (fM y443C) (fM y443C * fM y443Y)) :
    (twoAGraph (fM y443C)).Adj (baseVertex (fM y443C)) (fM y443S • baseVertex (fM y443C)) := by
  rw [twoAGraph_adj]
  have hv := coe_fM_S_smul hcx
  refine ⟨fun e => ?_, ?_⟩
  · have e' : fM y443C = fM y443Y := by
      have := congrArg Subtype.val e
      rwa [hv] at this
    rw [← e'] at hcy
    have h1 : fM y443C * fM y443C = 1 := fM_c_mul_self
    rw [h1] at hcy
    exact fM_c_ne_one (isConj_one_left.1 hcy)
  · rw [hv]
    exact hcy

theorem y443_hloc
    (hcx : (fM y443C * fM y443X) ^ 3 = 1)
    (h : ∀ u : ConjVert (fM y443C), (twoAGraph (fM y443C)).Adj (baseVertex (fM y443C)) u →
      ∃ g ∈ Subgroup.centralizer {fM y443C}, g * fM y443Y * g⁻¹ = (u : Gmat)) :
    ∀ u : ConjVert (fM y443C), (twoAGraph (fM y443C)).Adj (baseVertex (fM y443C)) u →
      ∃ g ∈ Subgroup.centralizer {fM y443C},
        g • (fM y443S • baseVertex (fM y443C)) = u := by
  intro u hu
  obtain ⟨g, hg, hgu⟩ := h u hu
  refine ⟨g, hg, Subtype.ext ?_⟩
  rw [coe_smul_conjVert, coe_fM_S_smul hcx]
  exact hgu

theorem y443_hB
    (hcx : (fM y443C * fM y443X) ^ 3 = 1) (hinj : Set.InjOn fM y443H)
    (h : ∀ k ∈ y443H, k * y443Y = y443Y * k → y443S * k * y443S ∈ y443H) :
    ∀ k ∈ y443H, fM k • (fM y443S • baseVertex (fM y443C)) = fM y443S • baseVertex (fM y443C) →
      y443S * k * y443S ∈ y443H := by
  intro k hk hfix
  refine h k hk ?_
  have hk' : ((fM k • (fM y443S • baseVertex (fM y443C)) : ConjVert (fM y443C)) : Gmat) =
      fM k * fM y443Y * (fM k)⁻¹ := by
    rw [coe_smul_conjVert, coe_fM_S_smul hcx]
  have h1 := congrArg Subtype.val hfix
  rw [hk', coe_fM_S_smul hcx] at h1
  have h2 : fM k * fM y443Y = fM y443Y * fM k := mul_inv_eq_iff_eq_mul.1 h1
  have h3 : fM (k * y443Y) = fM (y443Y * k) := by rw [map_mul, map_mul, h2]
  exact hinj (y443H.mul_mem hk y443Y_mem_H) (y443H.mul_mem y443Y_mem_H hk) h3

theorem y443K_comm_X
    {k : MonsterY443Derived} (hk : k ∈ y443K) : k * y443X = y443X * k := by
  have hle : y443K ≤ Subgroup.centralizer {y443X} := by
    rw [y443K, Subgroup.closure_le]
    rintro _ ⟨s, ⟨hs, hs'⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (y443T_comm_X hs hs')
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hk)

theorem y443S_conj_of_mem_K
    {k : MonsterY443Derived} (hk : k ∈ y443K)
    (hky : k * y443Y = y443Y * k) : y443S * k * y443S = k := by
  have hkx : Commute k y443X := y443K_comm_X hk
  have hkc : Commute k y443C := y443C_comm_H (y443K_le_H hk)
  have hky' : Commute k y443Y := hky
  have hkS : Commute k y443S := ((hkx.mul_right hkc).mul_right hky').mul_right hkx
  calc y443S * k * y443S = k * y443S * y443S := by rw [← hkS.eq]
    _ = k := by rw [mul_assoc, y443S_mul_self, mul_one]

@[expose] def y443CR : Set MonsterY443Derived := {r | r ∈ y443R ∧ r * y443Y = y443Y * r}

@[expose] def y443CK : Set MonsterY443Derived := {k | k ∈ y443K ∧ k * y443Y = y443Y * k}

theorem fM_S_conj'
    (hcx : (fM y443C * fM y443X) ^ 3 = 1) :
    fM y443S * fM y443Y * fM y443S = fM y443C := by
  have hSS : fM y443S * fM y443S = 1 := by rw [← map_mul, y443S_mul_self, map_one]
  have h := fM_S_conj hcx
  calc fM y443S * fM y443Y * fM y443S
      = fM y443S * (fM y443S * fM y443C * fM y443S) * fM y443S := by rw [h]
    _ = (fM y443S * fM y443S) * fM y443C * (fM y443S * fM y443S) := by simp only [mul_assoc]
    _ = fM y443C := by rw [hSS, one_mul, mul_one]

theorem y443S_conj_mem_R
    (hinj' : Set.InjOn fM y443H')
    (hRH : y443H.map fM ⊓ y443H'.map fM = y443R.map fM)
    (hmap : y443H.map fM = Subgroup.centralizer {fM y443C})
    (hcx : (fM y443C * fM y443X) ^ 3 = 1) {r : MonsterY443Derived} (hr : r ∈ y443CR) :
    y443S * r * y443S ∈ y443R := by
  obtain ⟨hrR, hry⟩ := hr
  have h1 : y443S * r * y443S ∈ y443H' := y443S_conj_mem_H' hrR
  have hSS : fM y443S * fM y443S = 1 := by rw [← map_mul, y443S_mul_self, map_one]
  have hry' : Commute (fM r) (fM y443Y) := by
    show fM r * fM y443Y = fM y443Y * fM r
    rw [← map_mul, ← map_mul, hry]
  have h2 : fM (y443S * r * y443S) ∈ y443H.map fM := by
    rw [hmap, Subgroup.mem_centralizer_singleton_iff, ← fM_S_conj' hcx, map_mul, map_mul]
    simp only [mul_assoc]
    rw [mul_mul_cancel_of_mul_self hSS (fM y443Y * fM y443S),
      mul_mul_cancel_of_mul_self hSS (fM r * fM y443S), hry'.left_comm]
  have h3 : fM (y443S * r * y443S) ∈ y443H.map fM ⊓ y443H'.map fM :=
    ⟨h2, Subgroup.mem_map_of_mem fM h1⟩
  rw [hRH] at h3
  obtain ⟨r', hr', hrr'⟩ := h3
  have : r' = y443S * r * y443S := hinj' (y443R_le_H' hr') h1 hrr'
  rw [← this]
  exact hr'

theorem y443_edge_of_cent_gen
    (hinj' : Set.InjOn fM y443H')
    (hRH : y443H.map fM ⊓ y443H'.map fM = y443R.map fM)
    (hmap : y443H.map fM = Subgroup.centralizer {fM y443C})
    (hcx : (fM y443C * fM y443X) ^ 3 = 1)
    (hgen : ∀ k ∈ y443H, k * y443Y = y443Y * k → k ∈ Subgroup.closure (y443CR ∪ y443CK)) :
    ∀ k ∈ y443H, k * y443Y = y443Y * k → y443S * k * y443S ∈ y443H := by
  let B : Subgroup MonsterY443Derived := y443H.comap (MulAut.conj y443S).toMonoidHom
  have hB : ∀ k, k ∈ B ↔ y443S * k * y443S ∈ y443H := fun k => by
    simp [B, MulAut.conj_apply, y443S_inv]
  have hsub : y443CR ∪ y443CK ⊆ (B : Set MonsterY443Derived) := by
    rintro k (hk | hk)
    · exact (hB k).2 (y443R_le_H (y443S_conj_mem_R hinj' hRH hmap hcx hk))
    · rw [SetLike.mem_coe, hB, y443S_conj_of_mem_K hk.1 hk.2]
      exact y443K_le_H hk.1
  intro k hk hky
  exact (hB k).1 ((Subgroup.closure_le B).2 hsub (hgen k hk hky))

theorem y443_cent_gen_of_native
    (hinj : Set.InjOn fM y443H)
    (hnat : ∀ g : Gmat, g ∈ y443H.map fM → g * fM y443Y = fM y443Y * g →
      g ∈ Subgroup.closure (fM '' y443CR ∪ fM '' y443CK)) :
    ∀ k ∈ y443H, k * y443Y = y443Y * k → k ∈ Subgroup.closure (y443CR ∪ y443CK) := by
  intro k hk hky
  have hk' : fM k ∈ Subgroup.closure (fM '' y443CR ∪ fM '' y443CK) :=
    hnat (fM k) (Subgroup.mem_map_of_mem fM hk) (by rw [← map_mul, ← map_mul, hky])
  rw [← Set.image_union, ← MonoidHom.map_closure] at hk'
  obtain ⟨k', hk'c, hkk'⟩ := hk'
  have hle : Subgroup.closure (y443CR ∪ y443CK) ≤ y443H :=
    (Subgroup.closure_le _).2 (Set.union_subset (fun r hr => y443R_le_H hr.1)
      (fun k hk => y443K_le_H hk.1))
  have := hinj (hle hk'c) hk hkk'
  rw [← this]
  exact hk'c

theorem y443_lift_of_trans
    (hinj' : Set.InjOn fM y443H')
    (hRH : y443H.map fM ⊓ y443H'.map fM = y443R.map fM)
    (hmap : y443H.map fM = Subgroup.centralizer {fM y443C})
    (hs : (twoAGraph (fM y443C)).Adj (baseVertex (fM y443C)) (fM y443S • baseVertex (fM y443C)))
    (htrans : ∀ y z y' z' : ConjVert (fM y443C),
      longTri (fM y443C) (baseVertex (fM y443C)) y z →
      longTri (fM y443C) (baseVertex (fM y443C)) y' z' →
      ∃ g ∈ Subgroup.centralizer {fM y443C}, g • y = y' ∧ g • z = z')
    (hV : ∃ β γ : ConjVert (fM y443C), longTri (fM y443C) (baseVertex (fM y443C)) β γ ∧
      (∃ h ∈ y443H', fM h • baseVertex (fM y443C) = baseVertex (fM y443C) ∧
        fM h • (fM y443S • baseVertex (fM y443C)) = β) ∧
      (∃ h ∈ y443H', fM h • baseVertex (fM y443C) = baseVertex (fM y443C) ∧
        fM h • (fM y443S • baseVertex (fM y443C)) = γ) ∧
      (∃ h ∈ y443H', fM h • baseVertex (fM y443C) = β ∧
        fM h • (fM y443S • baseVertex (fM y443C)) = γ)) :
    ∀ y z : ConjVert (fM y443C), longTri (fM y443C) (baseVertex (fM y443C)) y z →
      ∃ b b' : MonsterY443Derived,
        (cosetGraph y443H y443S).Adj ((1 : MonsterY443Derived) : MonsterY443Derived ⧸ y443H)
          (b : MonsterY443Derived ⧸ y443H) ∧
        (cosetGraph y443H y443S).Adj (b : MonsterY443Derived ⧸ y443H)
          (b' : MonsterY443Derived ⧸ y443H) ∧
        (cosetGraph y443H y443S).Adj (b' : MonsterY443Derived ⧸ y443H)
          ((1 : MonsterY443Derived) : MonsterY443Derived ⧸ y443H) ∧
        fM b • baseVertex (fM y443C) = y ∧ fM b' • baseVertex (fM y443C) = z :=
  fun y z hyz => CFSG.Monster.Tri.exists_lift_of_trans y443S_mul_self y443S_mem_H' hinj'
    (hRH.le.trans (Subgroup.map_mono y443R_le_inf)) hmap hs htrans hV y z hyz

end CFSG.YGroups.Y443
