module

public import CFSG.YGroups.Y443.Tri.CosetCover
public import CFSG.YGroups.Y443.Native.Parabolic2Transfer
public import CFSG.Monster.Schur.Final

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.GMS CFSG.Monster.B.Recog CFSG.Open
  CFSG.YGroups
open CFSG.Monster.Tri
open CFSG.Monster.Schur (NoPerfectDoubleCover)

section Steps

variable
  (hinj : Set.InjOn fM y443H) (hN : Q343N ≤ Nat.card (y443H.map fM))
  (hcx : (fM y443C * fM y443X) ^ 3 = 1) (hcy : IsConj (fM y443C) (fM y443C * fM y443Y))
  (hloc : ∀ u : ConjVert (fM y443C),
    (twoAGraph (fM y443C)).Adj (baseVertex (fM y443C)) u →
      ∃ g ∈ Subgroup.centralizer {fM y443C}, g * fM y443Y * g⁻¹ = (u : Gmat))
  (hedge : ∀ k ∈ y443H, k * y443Y = y443Y * k → y443S * k * y443S ∈ y443H)
  (hgen : Subgroup.closure ((y443H : Set MonsterY443Derived) ∪ {y443S}) = ⊤)
  (hlift : ∀ y z : ConjVert (fM y443C),
    longTri (fM y443C) (baseVertex (fM y443C)) y z →
      ∃ b b' : MonsterY443Derived,
        (cosetGraph y443H y443S).Adj ((1 : MonsterY443Derived) : MonsterY443Derived ⧸ y443H)
          (b : MonsterY443Derived ⧸ y443H) ∧
        (cosetGraph y443H y443S).Adj (b : MonsterY443Derived ⧸ y443H)
          (b' : MonsterY443Derived ⧸ y443H) ∧
        (cosetGraph y443H y443S).Adj (b' : MonsterY443Derived ⧸ y443H)
          ((1 : MonsterY443Derived) : MonsterY443Derived ⧸ y443H) ∧
        fM b • baseVertex (fM y443C) = y ∧ fM b' • baseVertex (fM y443C) = z)
  (htri : Triangulable (twoAGraph (fM y443C)))
  (hlink : ∀ w w' : ConjVert (fM y443C), (twoAGraph (fM y443C)).Adj (baseVertex (fM y443C)) w →
    (twoAGraph (fM y443C)).Adj (baseVertex (fM y443C)) w' →
      Relation.ReflTransGen (longTri (fM y443C) (baseVertex (fM y443C))) w w')
  (hquad : ∀ y u : ConjVert (fM y443C), (h : longTri (fM y443C) (baseVertex (fM y443C)) y u) →
    MarkedHomotopic (longTri (fM y443C))
      ((shortStruct_twoAGraph fM_c_mul_self fM_c_ne_one).quad h.1 h.2.2.1.symm h.2.1 (Or.inl h))
      .nil)

include hinj hN hcx hcy hloc hedge hgen hlift htri hlink hquad

theorem exists_ker_eq_one_or_eq_of_ivanov :
    ∃ n : MonsterY443Derived, ∀ k ∈ fM.ker, k = 1 ∨ k = n := by
  have hmap := Hbar_eq_centralizer hN
  have hs := y443_adj hcx hcy
  have hlift' : LiftsMarked (chi fM y443H y443C y443S y443C_comm_H' hs) (longTri (fM y443C)) :=
    liftsMarked_chi_of_base y443C_comm_H' hs fun y z h1 h2 h3 hT =>
      hlift y z ((permClosure_longTri_iff fM_c_mul_self fM_c_ne_one h1 h2 h3).1 hT)
  exact exists_ker_eq_one_or_eq y443C_comm_H' hinj hmap y443S_mul_self hs
    (y443_hloc hcx hloc) (y443_hB hcx hinj hedge) hgen hlift' fM_c_mul_self fM_c_ne_one htri
    (longLinkGraph_twoAGraph_of_base (preconnected_longLinkGraph_of_reflTransGen hlink))
    (fun hxy hxu hyu hL => quad_null_twoAGraph_of_base fM_c_mul_self fM_c_ne_one
      (fun hxy hxu hyu hL => hquad _ _
        ((permClosure_longTri_iff fM_c_mul_self fM_c_ne_one hxy hyu hxu.symm).1 hL))
      hxy hxu hyu hL)

theorem card_ker_le_two :
    Nat.card fM.ker ≤ 2 :=
  (card_ker_le_two_of
    (exists_ker_eq_one_or_eq_of_ivanov hinj hN hcx hcy hloc hedge hgen hlift htri hlink
      hquad).choose_spec).2

theorem finite_ker :
    Finite fM.ker :=
  (card_ker_le_two_of
    (exists_ker_eq_one_or_eq_of_ivanov hinj hN hcx hcy hloc hedge hgen hlift htri hlink
      hquad).choose_spec).1

theorem finite_monsterY443Derived :
    Finite MonsterY443Derived := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  have := finite_ker hinj hN hcx hcy hloc hedge hgen hlift htri hlink hquad
  exact finite_of_finite_ker fM (fM_surjective_of_order hN) this

variable (hschur : NoPerfectDoubleCover Gmat)

include hschur

theorem ker_eq_bot_of_ivanov :
    fM.ker = ⊥ :=
  ker_eq_bot_of_noPerfectDoubleCover fM (fM_surjective_of_order hN) y443_derived_isPerfect hschur
    (exists_ker_eq_one_or_eq_of_ivanov hinj hN hcx hcy hloc hedge hgen hlift htri hlink
      hquad).choose_spec

theorem fM_injective_of_ivanov :
    Function.Injective fM :=
  (MonoidHom.ker_eq_bot_iff fM).1
    (ker_eq_bot_of_ivanov hinj hN hcx hcy hloc hedge hgen hlift htri hlink hquad hschur)

end Steps

structure Y443CoverInputs :
    Prop where
  inj : Set.InjOn fM y443H
  order : Q343N ≤ Nat.card (y443H.map fM)
  cx_cube : (fM y443C * fM y443X) ^ 3 = 1
  cy_conj : IsConj (fM y443C) (fM y443C * fM y443Y)
  loc : ∀ u : ConjVert (fM y443C),
    (twoAGraph (fM y443C)).Adj (baseVertex (fM y443C)) u →
      ∃ g ∈ Subgroup.centralizer {fM y443C}, g * fM y443Y * g⁻¹ = (u : Gmat)
  RH : y443H.map fM ⊓ y443H'.map fM = y443R.map fM
  cent_gen : ∀ g : Gmat, g ∈ y443H.map fM → g * fM y443Y = fM y443Y * g →
    g ∈ Subgroup.closure (fM '' y443CR ∪ fM '' y443CK)
  gen_image : Subgroup.closure ((fM '' (y443R : Set MonsterY443Derived)) ∪ {fM y443S}) =
    y443H'.map fM
  trans_long : ∀ y z y' z' : ConjVert (fM y443C),
    longTri (fM y443C) (baseVertex (fM y443C)) y z →
    longTri (fM y443C) (baseVertex (fM y443C)) y' z' →
    ∃ g ∈ Subgroup.centralizer {fM y443C}, g • y = y' ∧ g • z = z'
  Vtri : ∃ β γ : ConjVert (fM y443C), longTri (fM y443C) (baseVertex (fM y443C)) β γ ∧
    (∃ h ∈ y443H', fM h • baseVertex (fM y443C) = baseVertex (fM y443C) ∧
      fM h • (fM y443S • baseVertex (fM y443C)) = β) ∧
    (∃ h ∈ y443H', fM h • baseVertex (fM y443C) = baseVertex (fM y443C) ∧
      fM h • (fM y443S • baseVertex (fM y443C)) = γ) ∧
    (∃ h ∈ y443H', fM h • baseVertex (fM y443C) = β ∧
      fM h • (fM y443S • baseVertex (fM y443C)) = γ)
  triangulable : Triangulable (twoAGraph (fM y443C))
  link : ∀ w w' : ConjVert (fM y443C), (twoAGraph (fM y443C)).Adj (baseVertex (fM y443C)) w →
    (twoAGraph (fM y443C)).Adj (baseVertex (fM y443C)) w' →
      Relation.ReflTransGen (longTri (fM y443C) (baseVertex (fM y443C))) w w'
  quad : ∀ y u : ConjVert (fM y443C), (h : longTri (fM y443C) (baseVertex (fM y443C)) y u) →
    MarkedHomotopic (longTri (fM y443C))
      ((shortStruct_twoAGraph fM_c_mul_self fM_c_ne_one).quad h.1 h.2.2.1.symm h.2.1 (Or.inl h))
      .nil

structure Y443IvanovInputs :
    Prop extends Y443CoverInputs where
  m24 : NoPerfectDoubleCover CFSG.Blueprint.NativeSporadic.M24

theorem Y443CoverInputs.inj'
    (h : Y443CoverInputs) : Set.InjOn fM y443H' :=
  injOn_fM_H'_iff.2 h.inj

theorem Y443IvanovInputs.schur
    (h : Y443IvanovInputs) : NoPerfectDoubleCover Gmat :=
  CFSG.Monster.Schur.noPerfectDoubleCover_Gmat_of_native h.m24

theorem Y443CoverInputs.edge
    (h : Y443CoverInputs) :
    ∀ k ∈ y443H, k * y443Y = y443Y * k → y443S * k * y443S ∈ y443H :=
  y443_edge_of_cent_gen h.inj' h.RH (Hbar_eq_centralizer h.order) h.cx_cube
    (y443_cent_gen_of_native h.inj h.cent_gen)

theorem Y443CoverInputs.gen
    (h : Y443CoverInputs) :
    Subgroup.closure ((y443H : Set MonsterY443Derived) ∪ {y443S}) = ⊤ :=
  y443_closure_H_S_eq_top (y443_closure_R_S_of_injOn fM h.inj' h.gen_image)

theorem Y443CoverInputs.lift
    (h : Y443CoverInputs) :
    ∀ y z : ConjVert (fM y443C), longTri (fM y443C) (baseVertex (fM y443C)) y z →
      ∃ b b' : MonsterY443Derived,
        (cosetGraph y443H y443S).Adj ((1 : MonsterY443Derived) : MonsterY443Derived ⧸ y443H)
          (b : MonsterY443Derived ⧸ y443H) ∧
        (cosetGraph y443H y443S).Adj (b : MonsterY443Derived ⧸ y443H)
          (b' : MonsterY443Derived ⧸ y443H) ∧
        (cosetGraph y443H y443S).Adj (b' : MonsterY443Derived ⧸ y443H)
          ((1 : MonsterY443Derived) : MonsterY443Derived ⧸ y443H) ∧
        fM b • baseVertex (fM y443C) = y ∧ fM b' • baseVertex (fM y443C) = z :=
  y443_lift_of_trans h.inj' h.RH (Hbar_eq_centralizer h.order) (y443_adj h.cx_cube h.cy_conj)
    h.trans_long h.Vtri

theorem Y443CoverInputs.card_ker_le_two
    (h : Y443CoverInputs) : Nat.card fM.ker ≤ 2 :=
  CFSG.YGroups.Y443.card_ker_le_two h.inj h.order h.cx_cube h.cy_conj h.loc h.edge h.gen h.lift
    h.triangulable h.link h.quad

theorem Y443CoverInputs.finite
    (h : Y443CoverInputs) : Finite MonsterY443Derived :=
  finite_monsterY443Derived h.inj h.order h.cx_cube h.cy_conj h.loc h.edge h.gen h.lift
    h.triangulable h.link h.quad

theorem Y443IvanovInputs.injective
    (h : Y443IvanovInputs) : Function.Injective fM :=
  fM_injective_of_ivanov h.inj h.order h.cx_cube h.cy_conj h.loc h.edge h.gen h.lift
    h.triangulable h.link h.quad h.schur

noncomputable def Y443IvanovInputs.equiv
    (h : Y443IvanovInputs) : MonsterY443Derived ≃* Gmat :=
  MulEquiv.ofBijective fM ⟨h.injective, fM_surjective_of_order h.order⟩

theorem fam_m_simplicity_of_ivanov
    (h : Y443IvanovInputs) : IsSimpleGroup MonsterY443Derived := by
  have := generated_rational_group_finite_simple.2.1
  exact h.equiv.isSimpleGroup

end CFSG.YGroups.Y443
