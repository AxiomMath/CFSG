module

public import CFSG.Monster.Tri.CoverFactsGBase
public import CFSG.Monster.Tri.GmatF1Type
public import CFSG.YGroups.Y443.Tri.Final
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.GMS CFSG.Monster.B.Short CFSG.Monster.Tri CFSG.Open CFSG.Blueprint.NativeSporadic
open CFSG.Monster.Tri.CoverG

section Relations

theorem isConj_fM_C_C' :
    IsConj (fM y443C) (fM y443C') :=
  isConj_iff.2 ⟨Grho, by rw [fM_y443C'_conj]⟩

theorem isConj_tStar_fM_C :
    IsConj (⟨tStar, tStar_mem_Gmat⟩ : Gmat) (fM y443C) := by
  refine isConj_iff.2 ⟨Omega⁻¹, Subtype.ext ?_⟩
  have h := omega_conj
  have e : ((Omega⁻¹ : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = (wordLin omegaWord)⁻¹ := rfl
  show ((Omega⁻¹ : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * tStar *
    ((Omega⁻¹ : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ = ((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB)
  rw [e, ← h]
  group

theorem isConj_tStar_of_mem_shortClass {x : Gmat}
    (hx : ((x : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ shortClass) :
    IsConj (⟨tStar, tStar_mem_Gmat⟩ : Gmat) x := by
  obtain ⟨g, hg, e⟩ := hx
  exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext e⟩

theorem isConj_fM_C_mul_C' :
    IsConj (fM y443C) (fM y443C * fM y443C') := by
  have h1 := isConj_tStar_of_mem_shortClass (x := fM y443C * fM y443C')
    fM_y443C_mul_y443C'_mem_shortClass
  exact isConj_tStar_fM_C.symm.trans h1

theorem fM_C'_comm_C :
    fM y443C' * fM y443C = fM y443C * fM y443C' := by
  rw [← map_mul, ← map_mul, y443C'_comm_H' y443C_mem_H']

theorem fM_C'_mul_self :
    fM y443C' * fM y443C' = 1 := by
  rw [← map_mul, y443C'_mul_self, map_one]

theorem fM_X_comm_C' :
    fM y443X * fM y443C' = fM y443C' * fM y443X := by
  rw [← map_mul, ← map_mul, y443C'_comm_X]

theorem fM_X_mul_self :
    fM y443X * fM y443X = 1 := by
  rw [← map_mul, y443X_mul_self, map_one]

theorem fM_S_conj_inv
    (hcx : (fM y443C * fM y443X) ^ 3 = 1) :
    fM y443S * fM y443C * (fM y443S)⁻¹ = fM y443Y := by
  rw [← map_inv, y443S_inv, fM_S_conj hcx]

theorem fM_Y_ne_C'_mul_C
    (hcx : (fM y443C * fM y443X) ^ 3 = 1)
    (hne : fM y443C ≠ fM y443Y) : fM y443Y ≠ fM y443C' * fM y443C := by
  intro h
  have hc2 : fM y443C * fM y443C = 1 := fM_c_mul_self
  have h1 : fM y443C * fM y443Y = fM y443C' := by
    rw [h, ← mul_assoc, ← fM_C'_comm_C, mul_assoc, hc2, mul_one]
  have hS : fM y443S = fM y443C' := by
    have e : fM y443S = fM y443X * (fM y443C * fM y443Y) * fM y443X := by
      simp [y443S, mul_assoc]
    rw [e, h1, fM_X_comm_C', mul_assoc, fM_X_mul_self, mul_one]
  have h2 := fM_S_conj hcx
  rw [hS, fM_C'_comm_C, mul_assoc, fM_C'_mul_self, mul_one] at h2
  exact hne h2

end Relations

section Centralizers

theorem y443H'_map_fM_eq_centralizer
    (hN : Q343N ≤ Nat.card (y443H.map fM)) :
    y443H'.map fM = Subgroup.centralizer {fM y443C'} := by
  rw [y443H'_map_fM, Hbar_eq_centralizer hN, fM_y443C'_conj]
  exact map_conj_centralizer _ _

theorem y443R_map_fM_eq_inf
    (hN : Q343N ≤ Nat.card (y443H.map fM))
    (hRH : y443H.map fM ⊓ y443H'.map fM = y443R.map fM) :
    y443R.map fM = Subgroup.centralizer {fM y443C} ⊓ Subgroup.centralizer {fM y443C'} := by
  rw [← hRH, Hbar_eq_centralizer hN, y443H'_map_fM_eq_centralizer hN]

end Centralizers

section Local

variable {d₀ : B} {a₀ z₀ : Gmat}

theorem fM_loc
    (I : TableVIFacts d₀ Gmat) (hG : GMSF1Type d₀ a₀ z₀)
    (hconj : IsConj a₀ (fM y443C)) (hcx : (fM y443C * fM y443X) ^ 3 = 1)
    (hcy : IsConj (fM y443C) (fM y443C * fM y443Y)) :
    ∀ u : ConjVert (fM y443C), (twoAGraph (fM y443C)).Adj (baseVertex (fM y443C)) u →
      ∃ g ∈ Subgroup.centralizer {fM y443C}, g * fM y443Y * g⁻¹ = (u : Gmat) := by
  intro u hu
  obtain ⟨g, hg, e⟩ := exists_smul_eq_of_adj I hG hconj (y443_adj hcx hcy) hu
  refine ⟨g, hg, ?_⟩
  have := congrArg Subtype.val e
  rwa [coe_smul_conjVert, coe_fM_S_smul hcx] at this

theorem fM_trans_long
    (I : TableVIFacts d₀ Gmat) (hG : GMSF1Type d₀ a₀ z₀)
    (hconj : IsConj a₀ (fM y443C)) :
    ∀ y z y' z' : ConjVert (fM y443C),
      longTri (fM y443C) (baseVertex (fM y443C)) y z →
      longTri (fM y443C) (baseVertex (fM y443C)) y' z' →
      ∃ g ∈ Subgroup.centralizer {fM y443C}, g • y = y' ∧ g • z = z' :=
  fun _ _ _ _ h h' => exists_smul_eq_of_longTri_base I hG hconj h h'

theorem fM_link
    (I : TableVIFacts d₀ Gmat) (hG : GMSF1Type d₀ a₀ z₀)
    (hconj : IsConj a₀ (fM y443C)) :
    ∀ w w' : ConjVert (fM y443C), (twoAGraph (fM y443C)).Adj (baseVertex (fM y443C)) w →
      (twoAGraph (fM y443C)).Adj (baseVertex (fM y443C)) w' →
        Relation.ReflTransGen (longTri (fM y443C) (baseVertex (fM y443C))) w w' :=
  fun _ _ hw hw' => link_of_interfaces I hG hconj hw hw'

end Local

section GenImage

variable {d₀ : B} {a₀ z₀ : Gmat}

theorem fM_gen_image
    (I : TableVIFacts d₀ Gmat) (hG : GMSF1Type d₀ a₀ z₀)
    (hconj : IsConj a₀ (fM y443C)) (hN : Q343N ≤ Nat.card (y443H.map fM))
    (hRH : y443H.map fM ⊓ y443H'.map fM = y443R.map fM)
    (hcx : (fM y443C * fM y443X) ^ 3 = 1) (hcy : IsConj (fM y443C) (fM y443C * fM y443Y)) :
    Subgroup.closure ((fM '' (y443R : Set MonsterY443Derived)) ∪ {fM y443S}) =
      y443H'.map fM := by
  have hconj' : IsConj a₀ (fM y443C') := hconj.trans isConj_fM_C_C'
  let u₀ : ConjVert (fM y443C') := ⟨fM y443C, isConj_fM_C_C'.symm⟩
  have hs : fM y443S ∈ Subgroup.centralizer ({fM y443C'} : Set Gmat) := by
    rw [← y443H'_map_fM_eq_centralizer hN]
    exact Subgroup.mem_map_of_mem fM y443S_mem_H'
  have hadj0 := y443_adj hcx hcy
  have hne : fM y443C ≠ fM y443Y := by
    intro e
    refine hadj0.1 (Subtype.ext ?_)
    rw [coe_baseVertex, coe_fM_S_smul hcx]
    exact e
  have hsu : ((fM y443S • u₀ : ConjVert (fM y443C')) : Gmat) = fM y443Y := by
    rw [coe_smul_conjVert]
    exact fM_S_conj_inv hcx
  have hbu : (twoAGraph (fM y443C')).Adj (baseVertex (fM y443C')) u₀ := by
    refine ⟨fun e => ?_, ?_⟩
    · have e' : fM y443C' = fM y443C := congrArg Subtype.val e
      have h1 := isConj_fM_C_mul_C'
      rw [e', fM_c_mul_self] at h1
      exact fM_c_ne_one (isConj_one_right.1 h1.symm)
    · show IsConj (fM y443C') (fM y443C' * fM y443C)
      rw [fM_C'_comm_C]
      exact isConj_fM_C_C'.symm.trans isConj_fM_C_mul_C'
  have hlong : longTri (fM y443C') (baseVertex (fM y443C')) u₀ (fM y443S • u₀) := by
    refine ⟨hbu, ⟨fun e => hne ?_, ?_⟩, ?_, ?_⟩
    · have := congrArg Subtype.val e
      rwa [hsu] at this
    · show IsConj (fM y443C') (fM y443C * ((fM y443S • u₀ : ConjVert (fM y443C')) : Gmat))
      rw [hsu]
      exact isConj_fM_C_C'.symm.trans hcy
    · have h1 := twoAGraph_adj_smul (fM y443S) hbu.symm
      have h2 : fM y443S • baseVertex (fM y443C') = baseVertex (fM y443C') :=
        (smul_eq_self_iff _ _).2 hs
      rwa [h2] at h1
    · show ((fM y443S • u₀ : ConjVert (fM y443C')) : Gmat) ≠ fM y443C' * fM y443C
      rw [hsu]
      exact fM_Y_ne_C'_mul_C hcx hne
  have h := closure_centralizer_inf_eq I hG hconj' hs hlong
  rw [← Subgroup.coe_map, y443R_map_fM_eq_inf hN hRH, inf_comm,
    y443H'_map_fM_eq_centralizer hN]
  exact h

end GenImage

section CentGen

@[expose] def TriangleStabMaximal :
    Prop := TriMax (fM y443C) (fM y443Y) (fM y443C')

theorem triangleStabMaximal_of_exists
    {d₀ : B} {a₀ z₀ : Gmat} (I : TableVIFacts d₀ Gmat)
    (hG : GMSF1Type d₀ a₀ z₀) (hconj : IsConj a₀ (fM y443C))
    (hcx : (fM y443C * fM y443X) ^ 3 = 1) (hcy : IsConj (fM y443C) (fM y443C * fM y443Y))
    (hex : ∃ x y z : ConjVert (fM y443C), longTri (fM y443C) x y z ∧
      TriMax (x : Gmat) (y : Gmat) (z : Gmat)) :
    TriangleStabMaximal := by
  obtain ⟨x, y, z, hxyz, hm⟩ := hex
  have hadj0 := y443_adj hcx hcy
  have hne : fM y443C ≠ fM y443Y := by
    intro e
    refine hadj0.1 (Subtype.ext ?_)
    rw [coe_baseVertex, coe_fM_S_smul hcx]
    exact e
  have hc2 : fM y443C * fM y443C = 1 := fM_c_mul_self
  let w : ConjVert (fM y443C) := ⟨fM y443C', isConj_fM_C_C'⟩
  have hbw : (twoAGraph (fM y443C)).Adj (baseVertex (fM y443C)) w := by
    refine ⟨fun e => ?_, isConj_fM_C_mul_C'⟩
    have e' : fM y443C = fM y443C' := congrArg Subtype.val e
    have h1 := isConj_fM_C_mul_C'
    rw [← e', hc2] at h1
    exact fM_c_ne_one (isConj_one_right.1 h1.symm)
  have hs : fM y443S ∈ Subgroup.centralizer ({fM y443C'} : Set Gmat) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      y443C'_comm_H' y443S_mem_H']
  have hsw : fM y443S • w = w := (smul_eq_self_iff _ _).2 hs
  have hlong : longTri (fM y443C) (baseVertex (fM y443C))
      (fM y443S • baseVertex (fM y443C)) w := by
    refine ⟨hadj0, ?_, hbw.symm, ?_⟩
    · have h1 := twoAGraph_adj_smul (fM y443S) hbw
      rwa [hsw] at h1
    · show (fM y443C' : Gmat) ≠ fM y443C * ((fM y443S • baseVertex (fM y443C) :
        ConjVert (fM y443C)) : Gmat)
      rw [coe_fM_S_smul hcx]
      intro e
      refine fM_Y_ne_C'_mul_C hcx hne ?_
      calc fM y443Y = fM y443C * (fM y443C * fM y443Y) := by rw [← mul_assoc, hc2, one_mul]
        _ = fM y443C * fM y443C' := by rw [← e]
        _ = fM y443C' * fM y443C := fM_C'_comm_C.symm
  have h := triMax_of_longTri I hG hconj hxyz hlong hm
  rw [coe_baseVertex, coe_fM_S_smul hcx] at h
  exact h

theorem y443X'_mem_CK :
    y443X' ∈ y443CK :=
  ⟨y443T_mem_K y443E2_ne_E1 y443E2_ne_D1,
    (y443T_comm_X' (s := y443D1) y443D1_ne_E2 (by decide)).symm⟩

theorem fM_cent_gen
    (hN : Q343N ≤ Nat.card (y443H.map fM))
    (hRH : y443H.map fM ⊓ y443H'.map fM = y443R.map fM) (hinj' : Set.InjOn fM y443H')
    (hmax : TriangleStabMaximal) :
    ∀ g : Gmat, g ∈ y443H.map fM → g * fM y443Y = fM y443Y * g →
      g ∈ Subgroup.closure (fM '' y443CR ∪ fM '' y443CK) := by
  intro g hg hgy
  have hH := Hbar_eq_centralizer hN
  have hH' := y443H'_map_fM_eq_centralizer hN
  set F : Subgroup Gmat := Subgroup.closure (fM '' y443CR ∪ fM '' y443CK) with hF
  have hFE : F ≤ Subgroup.centralizer {fM y443C} ⊓ Subgroup.centralizer {fM y443Y} := by
    rw [hF, Subgroup.closure_le]
    rintro _ (⟨r, hr, rfl⟩ | ⟨k, hk, rfl⟩)
    · have h1 : fM r ∈ Subgroup.centralizer {fM y443C} := by
        rw [← hH]
        exact Subgroup.mem_map_of_mem fM (y443R_le_H hr.1)
      have h2 : fM r ∈ Subgroup.centralizer {fM y443Y} := by
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hr.2]
      exact ⟨h1, h2⟩
    · have h1 : fM k ∈ Subgroup.centralizer {fM y443C} := by
        rw [← hH]
        exact Subgroup.mem_map_of_mem fM (y443K_le_H hk.1)
      have h2 : fM k ∈ Subgroup.centralizer {fM y443Y} := by
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hk.2]
      exact ⟨h1, h2⟩
  have hPF : Subgroup.centralizer {fM y443C} ⊓ Subgroup.centralizer {fM y443Y} ⊓
      Subgroup.centralizer {fM y443C'} ≤ F := by
    intro x hx
    have hx1 : x ∈ y443H.map fM := by rw [hH]; exact hx.1.1
    have hx2 : x ∈ y443H'.map fM := by rw [hH']; exact hx.2
    have hx3 : x ∈ y443R.map fM := by rw [← hRH]; exact ⟨hx1, hx2⟩
    obtain ⟨r, hr, rfl⟩ := hx3
    have hry : r * y443Y = y443Y * r := by
      refine hinj' (y443H'.mul_mem (y443R_le_H' hr) y443Y_mem_H')
        (y443H'.mul_mem y443Y_mem_H' (y443R_le_H' hr)) ?_
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.1 hx.1.2
    exact Subgroup.subset_closure (Or.inl ⟨r, ⟨hr, hry⟩, rfl⟩)
  have hFP : F ≠ Subgroup.centralizer {fM y443C} ⊓ Subgroup.centralizer {fM y443Y} ⊓
      Subgroup.centralizer {fM y443C'} := by
    intro e
    have hxF : fM y443X' ∈ F := Subgroup.subset_closure (Or.inr ⟨y443X', y443X'_mem_CK, rfl⟩)
    rw [e] at hxF
    have hcomm := Subgroup.mem_centralizer_singleton_iff.1 hxF.2
    have hx2 : fM y443X' * fM y443X' = 1 := by rw [← map_mul, y443X'_mul_self, map_one]
    have e1 : fM y443X' * fM y443C' * fM y443X' = fM y443C' := by
      rw [hcomm, mul_assoc, hx2, mul_one]
    apply hd_primed_fM_of_hd fM_C_X_noncomm
    rw [e1]
  have hFE' : F = Subgroup.centralizer {fM y443C} ⊓ Subgroup.centralizer {fM y443Y} :=
    (hmax F hPF hFE).resolve_left hFP
  rw [hFE']
  exact ⟨by rw [← hH]; exact hg, Subgroup.mem_centralizer_singleton_iff.2 hgy⟩

end CentGen

section Assembly

open CFSG.Monster.Existence (phiB uBar)

theorem y443CoverInputs_of_interfaces
    (I : TableVIFacts (phiB uBar) Gmat)
    (hinj : Set.InjOn fM y443H) (hN : Q343N ≤ Nat.card (y443H.map fM))
    (hcx : (fM y443C * fM y443X) ^ 3 = 1) (hcy : IsConj (fM y443C) (fM y443C * fM y443Y))
    (hRH : y443H.map fM ⊓ y443H'.map fM = y443R.map fM)
    (hmax : TriangleStabMaximal)
    (hVtri : ∃ β γ : ConjVert (fM y443C), longTri (fM y443C) (baseVertex (fM y443C)) β γ ∧
      (∃ h ∈ y443H', fM h • baseVertex (fM y443C) = baseVertex (fM y443C) ∧
        fM h • (fM y443S • baseVertex (fM y443C)) = β) ∧
      (∃ h ∈ y443H', fM h • baseVertex (fM y443C) = baseVertex (fM y443C) ∧
        fM h • (fM y443S • baseVertex (fM y443C)) = γ) ∧
      (∃ h ∈ y443H', fM h • baseVertex (fM y443C) = β ∧
        fM h • (fM y443S • baseVertex (fM y443C)) = γ))
    (htri : CFSG.Monster.B.Recog.Triangulable (twoAGraph (fM y443C)))
    (hquad : ∀ y u : ConjVert (fM y443C),
      (h : longTri (fM y443C) (baseVertex (fM y443C)) y u) →
        CFSG.YGroups.MarkedHomotopic (longTri (fM y443C))
          ((shortStruct_twoAGraph fM_c_mul_self fM_c_ne_one).quad h.1 h.2.2.1.symm h.2.1
            (Or.inl h)) .nil) :
    Y443CoverInputs where
  inj := hinj
  order := hN
  cx_cube := hcx
  cy_conj := hcy
  loc := fM_loc I gmsF1Type_Gmat isConj_tStar_fM_C hcx hcy
  RH := hRH
  cent_gen := fM_cent_gen hN hRH (injOn_fM_H'_iff.2 hinj) hmax
  gen_image := fM_gen_image I gmsF1Type_Gmat isConj_tStar_fM_C hN hRH hcx hcy
  trans_long := fM_trans_long I gmsF1Type_Gmat isConj_tStar_fM_C
  Vtri := hVtri
  triangulable := htri
  link := fM_link I gmsF1Type_Gmat isConj_tStar_fM_C
  quad := hquad

theorem triangleStabMaximal_Gmat
    (I : TableVIFacts (phiB uBar) Gmat)
    (hcx : (fM y443C * fM y443X) ^ 3 = 1) (hcy : IsConj (fM y443C) (fM y443C * fM y443Y))
    (hex : ∃ x y z : ConjVert (fM y443C), longTri (fM y443C) x y z ∧
      TriMax (x : Gmat) (y : Gmat) (z : Gmat)) :
    TriangleStabMaximal :=
  triangleStabMaximal_of_exists I gmsF1Type_Gmat isConj_tStar_fM_C hcx hcy hex

end Assembly

end CFSG.YGroups.Y443
