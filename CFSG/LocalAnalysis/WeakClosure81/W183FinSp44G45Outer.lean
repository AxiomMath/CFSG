module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G45OuterPhi
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G45OuterPV

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.Quasithin CFSG.Open Subgroup

private theorem w183finSp44_sclist_valid : SClist.all validB = true := by
  decide +kernel

private lemma w183finSp44_valid_of_sclist {x : El} (hx : x ∈ SClist) : validB x = true :=
  (List.all_eq_true.mp w183finSp44_sclist_valid) x hx

theorem classes_of_outer (A : Subgroup (MulAut S4)) (hel : IsElemAbelian 2 A)
    (h8 : 8 ≤ Nat.card A) (hout : ¬ A ≤ innAutOf S4) :
    ∃ (h : MulAut S4) (c : Nat), c < 4 ∧ autConj h A = outerRep c := by
  obtain ⟨h₁, hP, hφ⟩ := exists_conj_phi_le_Psub A hel hout
  have hel₁ : IsElemAbelian 2 (autConj h₁ A) :=
    hel.map (MulAut.conj h₁).toMonoidHom
  have hcard : Nat.card (autConj h₁ A) = Nat.card A :=
    Subgroup.card_map_of_injective (K := A) (f := (MulAut.conj h₁).toMonoidHom)
      (MulAut.conj h₁).injective
  obtain ⟨K, hSC, hinv, hcomm, hcl, hφK, hKcard, hmem⟩ :=
    exists_codes_of_le_Psub (autConj h₁ A) hel₁ hP hφ
  have h8K : 8 ≤ K.card := by rw [hKcard, hcard]; exact h8
  obtain ⟨r, hr, hKspan⟩ := phi_rows_complete_codes K hSC hinv hcomm hcl hφK h8K
  obtain ⟨hc4, hgvalid, hfwd, hbwd⟩ := rows_conj r hr
  refine ⟨autOf r.2.2 * h₁, r.2.1, hc4, ?_⟩
  have hmul : autConj (autOf r.2.2 * h₁) A =
      autConj (autOf r.2.2) (autConj h₁ A) :=
    (Subgroup.map_conj_map_conj A h₁ (autOf r.2.2)).symm
  rw [hmul]
  apply Subgroup.ext
  intro α
  rw [mem_outerRep_iff hc4 α]
  constructor
  · intro hα
    rw [autConj, Subgroup.mem_map] at hα
    obtain ⟨β, hβA, hβα⟩ := hα
    have hβα' : MulAut.conj (autOf r.2.2) β = α := hβα
    obtain ⟨x, hxK, hxβ⟩ := (hmem β).mp hβA
    have hxspan : x ∈ span2 (phiE :: r.1) := (hKspan x).mp hxK
    have hxval : validB x = true := w183finSp44_valid_of_sclist (hSC x hxK)
    refine ⟨conjE r.2.2 x, hfwd x hxspan, ?_⟩
    rw [← hβα', ← hxβ]
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    rw [← autOf_conjE hgvalid hxval]
  · rintro ⟨y, hy, hyα⟩
    obtain ⟨x, hxspan, hxconj⟩ := hbwd y hy
    have hxK : x ∈ K := (hKspan x).mpr hxspan
    have hxval : validB x = true := w183finSp44_valid_of_sclist (hSC x hxK)
    rw [autConj, Subgroup.mem_map]
    refine ⟨autOf x, (hmem (autOf x)).mpr ⟨x, hxK, rfl⟩, ?_⟩
    rw [← hyα]
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    rw [← autOf_conjE hgvalid hxval, hxconj]

theorem outer_case (A : Subgroup (MulAut S4)) (hel : IsElemAbelian 2 A) (h8 : 8 ≤ Nat.card A)
    (hout : ¬ A ≤ innAutOf S4) : ∃ y : MulAut S4, PairViolation A y := by
  obtain ⟨h, c, hc, hA⟩ := classes_of_outer A hel h8 hout
  obtain ⟨y, hy⟩ := pairViolation_outerRep hc
  have hcomp : (MulAut.conj h⁻¹ : MulAut (MulAut S4)).toMonoidHom.comp
      (MulAut.conj h : MulAut (MulAut S4)).toMonoidHom = MonoidHom.id _ := by
    ext a
    simp [MulAut.conj_apply, mul_assoc]
  have hAeq : (outerRep c).map (MulAut.conj h⁻¹ : MulAut (MulAut S4)).toMonoidHom = A := by
    rw [← hA, autConj, Subgroup.map_map, hcomp, Subgroup.map_id]
  exact ⟨(MulAut.conj h⁻¹ : MulAut (MulAut S4)) y,
    hAeq ▸ (pairViolation_map (MulAut.conj h⁻¹ : MulAut (MulAut S4)) (outerRep c) y).mpr hy⟩

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
