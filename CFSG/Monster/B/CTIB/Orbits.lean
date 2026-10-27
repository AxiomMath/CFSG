module

public import CFSG.Monster.B.CTIB.Words
public import CFSG.Monster.B.CTIB.Cert
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3027

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin Native ConjAct

@[expose] def qClass (t : Sbp) : Set Sbp := {u | ∃ e ∈ Qs, u = e⁻¹ * t * e}

@[expose] noncomputable def fuseGroup
    (k : ℕ) : Subgroup Sbp :=
  Subgroup.closure ((Qs : Set Sbp) ∪ centElt k '' {j | j < 15})

@[expose] def fClass
    (k : ℕ) (t : Sbp) : Set Sbp := {u | ∃ f ∈ fuseGroup k, u = f⁻¹ * t * f}

theorem orbit_closure_toConjAct (S : Set Sbp) (t : Sbp) :
    MulAction.orbit (Subgroup.closure (toConjAct '' S)) t =
      {u | ∃ g ∈ Subgroup.closure S, u = g⁻¹ * t * g} := by
  have hmap : Subgroup.closure (toConjAct '' S) =
      (Subgroup.closure S).map (toConjAct : Sbp ≃* ConjAct Sbp).toMonoidHom := by
    rw [MonoidHom.map_closure]
    rfl
  ext u
  constructor
  · rintro ⟨⟨c, hc⟩, rfl⟩
    rw [hmap] at hc
    obtain ⟨g, hg, rfl⟩ := hc
    refine ⟨g⁻¹, Subgroup.inv_mem _ hg, ?_⟩
    show toConjAct g • t = g⁻¹⁻¹ * t * g⁻¹
    rw [toConjAct_smul, inv_inv]
  · rintro ⟨g, hg, rfl⟩
    have hc : toConjAct g⁻¹ ∈ Subgroup.closure (toConjAct '' S) := by
      rw [hmap]; exact ⟨g⁻¹, Subgroup.inv_mem _ hg, rfl⟩
    refine ⟨⟨toConjAct g⁻¹, hc⟩, ?_⟩
    show toConjAct g⁻¹ • t = g⁻¹ * t * g
    rw [toConjAct_smul, inv_inv]

theorem qClass_eq_orbit
    (t : Sbp) :
    qClass t =
      MulAction.orbit (Subgroup.closure ((fun m => toConjAct (es m)) '' {m | m < 22})) t := by
  rw [show (fun m => toConjAct (es m)) '' {m | m < 22} = toConjAct '' (es '' {m | m < 22}) by
    rw [Set.image_image], orbit_closure_toConjAct, closure_es]
  rfl

@[expose] noncomputable def gensF
    (k m : ℕ) : ConjAct Sbp :=
  if m < 22 then toConjAct (es m) else toConjAct (centElt k (m - 22))⁻¹

theorem gensF_image
    (k : ℕ) : gensF k '' {m | m < 37} =
    toConjAct '' (es '' {m | m < 22} ∪ (fun j => (centElt k j)⁻¹) '' {j | j < 15}) := by
  ext c
  constructor
  · rintro ⟨m, hm, rfl⟩
    by_cases h : m < 22
    · exact ⟨es m, Or.inl ⟨m, h, rfl⟩, by rw [gensF, ite_eq_left h]⟩
    · exact ⟨(centElt k (m - 22))⁻¹, Or.inr ⟨m - 22, by simp at hm ⊢; omega, rfl⟩,
        by rw [gensF, ite_eq_right h]⟩
  · rintro ⟨y, hy | hy, rfl⟩
    · obtain ⟨m, hm, rfl⟩ := hy
      exact ⟨m, by simp at hm ⊢; omega, by rw [gensF, ite_eq_left (show m < 22 from hm)]⟩
    · obtain ⟨j, hj, rfl⟩ := hy
      refine ⟨j + 22, by simp at hj ⊢; omega, ?_⟩
      rw [gensF, ite_eq_right (by omega), Nat.add_sub_cancel]

theorem closure_gensF
    (k : ℕ) :
    Subgroup.closure (es '' {m | m < 22} ∪ (fun j => (centElt k j)⁻¹) '' {j | j < 15}) =
      fuseGroup k := by
  rw [Subgroup.closure_union, closure_es, fuseGroup, Subgroup.closure_union,
    Subgroup.closure_eq]
  congr 1
  rw [show (fun j => (centElt k j)⁻¹) '' {j | j < 15} = (centElt k '' {j | j < 15})⁻¹ by
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inv]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, by rw [inv_inv]⟩
    · rintro ⟨j, hj, h⟩; exact ⟨j, hj, by rw [h, inv_inv]⟩, Subgroup.closure_inv]

theorem fClass_eq_orbit
    (k : ℕ) (t : Sbp) :
    fClass k t = MulAction.orbit (Subgroup.closure (gensF k '' {m | m < 37})) t := by
  rw [gensF_image, orbit_closure_toConjAct, closure_gensF]
  rfl

theorem fuseGroup_le
    (k : ℕ) (hk : IsRank k) : fuseGroup k ≤ Jbar.op := by
  rw [fuseGroup, Subgroup.closure_le]
  rintro y (hy | ⟨j, hj, rfl⟩)
  · exact Ebar_le_Jbar hy
  · exact centElt_mem_Jbar hk hj

theorem Qs_le_fuseGroup
    (k : ℕ) : Qs ≤ fuseGroup k := fun _ hy =>
  Subgroup.subset_closure (Or.inl hy)

theorem liftImgsK_size
    {k : ℕ} (hk : IsRank k) : ((liftImgsK k).toArray).size = 22 := by
  rw [List.size_toArray, ← lift_len hk, ← lift_rows hk, List.length_map]

theorem es_inv (m : ℕ) : (es m)⁻¹ = es m := inv_eq_of_mul_eq_one_right (es_mul_self m)

theorem qconj_act
    {k : ℕ} (hk : IsRank k) {m : ℕ} (hm : m < 22) (a : ℕ) :
    cosetElt k (qconj gArr (liftImgsK k).toArray m a) = toConjAct (es m) • cosetElt k a := by
  rw [toConjAct_smul, cosetElt, cosetElt, qconj, ← qS_mul, ← qS_mul, qS_two_pow hm,
    liftImgsK_getD, ← conj_hs hk hm, es_inv]
  group

end CFSG.Monster.B.CTIB
