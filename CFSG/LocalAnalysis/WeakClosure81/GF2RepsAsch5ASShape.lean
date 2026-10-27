module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASAlm
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASIn
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASLie
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASL3
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Shape
public import CFSG.Quasithin.Background.RonanE114Lie

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt)
open CFSG.Blueprint (LieModel)

theorem quasithinIsSylowTwo_of_isSylowInTop {G : Type} [Group G] {T : Subgroup G}
    (h : IsSylowIn 2 T ⊤) : quasithinIsSylowTwo T :=
  ⟨h.2.1, by
    have h2 : ¬ 2 ∣ T.relIndex ⊤ := h.2.2
    rwa [Subgroup.relIndex_top_right] at h2⟩

theorem shapeInEAS_alt6_l3 :
    ShapeInEAS 1 (fun X _ => IsAlt X 6 ∨ IsL3 X 1) :=
  shapeInEAS_of_ambient_fstar (isoInvPred_or (isoInvPred_isAlt 6) (isoInvPred_lieModel _ _ _ _))
    fun Q _ _ _ _ _ _ _ hP => by
      have h := RonanE114.nParam_le_one_of_l32_or_alt6 (G := Q) (by
        rcases hP with h | h
        · exact Or.inr h
        · exact Or.inl (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h))
      exact (E1.nParam_le_iff Nat.one_pos).mp (by exact_mod_cast h)

theorem shapeInEAS_l2u3_four :
    ShapeInEAS 2 (fun X _ => IsL2 X 2 ∨ IsU3 X 2) :=
  shapeInEAS_of_ambient_fstar
    (isoInvPred_or (isoInvPred_lieModel _ _ _ _) (isoInvPred_lieModel _ _ _ _))
    fun Q _ _ _ hs _ hT hFT hP => by
      have h := nParam_le_of_lie_noSQ (n := 2) le_rfl hs (quasithinIsSylowTwo_of_isSylowInTop hT)
        hFT (by
          rcases hP with h | h
          · exact Or.inl (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)
          · exact Or.inr (Or.inl (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)))
      exact (E1.nParam_le_iff (by norm_num)).mp h

theorem shapeInEAS_l3sp4_four :
    ShapeInEAS 2 (fun X _ => IsL3 X 2 ∨ IsSp4 X 2) :=
  shapeInEAS_of_ambient_fstar
    (isoInvPred_or (isoInvPred_lieModel _ _ _ _) (isoInvPred_lieModel _ _ _ _))
    fun Q _ _ _ hs _ hT hFT hP => by
      have h := nParam_le_of_lie_noSQ (n := 2) le_rfl hs (quasithinIsSylowTwo_of_isSylowInTop hT)
        hFT (by
          rcases hP with h | h
          · exact Or.inr (Or.inr (Or.inl
              (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)))
          · exact Or.inr (Or.inr (Or.inr
              (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h))))
      exact (E1.nParam_le_iff (by norm_num)).mp h

theorem shapeInEAS_l2
    {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h5 : 5 < p ^ e) : ShapeInEAS 1 (fun X _ => F6.IsL2 p e X) :=
  shapeInEAS_of_ambient_fstar (isoInvPred_f6IsL2 p e) fun Q _ _ _ hs _ hT hFT hP =>
    (E1.nParam_le_iff Nat.one_pos).mp (by
      exact_mod_cast nParam_le_one_of_isPSL2_noSQ hs (quasithinIsSylowTwo_of_isSylowInTop hT) hFT
        hp hp2 h5 hP)

section L3

theorem shapeInEAS_l3_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp4 : p % 4 = 3) :
    ShapeInEAS 1 (fun X _ => LieModel X .PSL 3 p 1) :=
  shapeInEAS_of_ambient_fstar (isoInvPred_lieModel _ _ _ _) fun Q _ _ _ hs _ hT hFT hP =>
    (E1.nParam_le_iff Nat.one_pos).mp (by
      exact_mod_cast nParam_le_one_of_isPSL3_noSQ hs (quasithinIsSylowTwo_of_isSylowInTop hT) hFT
        hp hp2 hp4 (LieModel.statedClassicalModel_of_ne_zero (by norm_num) hP))

end L3

section U3

theorem shapeInEAS_u3_one {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    ShapeInEAS 1 (fun X _ => LieModel X .PSU 3 p 1) :=
  shapeInEAS_of_ambient_fstar (isoInvPred_lieModel _ _ _ _) fun Q _ _ _ hs _ hT hFT hP =>
    (E1.nParam_le_iff Nat.one_pos).mp (by
      exact_mod_cast nParam_le_one_of_isPSU3_noSQ hs (quasithinIsSylowTwo_of_isSylowInTop hT) hFT
        hp hp4 (LieModel.statedClassicalModel_of_ne_zero (by norm_num) hP))

end U3

theorem shapeInEAS_l3_pow (h : Asch4_11ASPow) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 2 ≤ f) : ShapeInEAS 1 (fun X _ => LieModel X .PSL 3 p f) :=
  shapeInEAS_of_ambient_fstar (isoInvPred_lieModel _ _ _ _) fun Q _ _ T hs hnab hT hFT hP =>
    h Q T p f hp hp2 hf hs hnab (Or.inl hP) hT hFT

theorem shapeInEAS_u3_pow (h : Asch4_11ASPow) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 2 ≤ f) : ShapeInEAS 1 (fun X _ => LieModel X .PSU 3 p f) :=
  shapeInEAS_of_ambient_fstar (isoInvPred_lieModel _ _ _ _) fun Q _ _ T hs hnab hT hFT hP =>
    h Q T p f hp hp2 hf hs hnab (Or.inr hP) hT hFT

section L3All

theorem shapeInEAS_l3 (h : Asch4_11ASPow) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h4 : f = 1 → p % 4 = 3) : ShapeInEAS 1 (fun X _ => LieModel X .PSL 3 p f) := by
  intro L₀ _ _ hs hnab hP A S hAS
  by_cases hf : f = 1
  · subst hf
    exact shapeInEAS_l3_one hp hp2 (h4 rfl) L₀ hs hnab hP A S hAS
  · exact shapeInEAS_l3_pow h hp hp2 (by have := hP.admissible.2.1; omega) L₀ hs hnab hP A S hAS

theorem shapeInEAS_u3 (h : Asch4_11ASPow) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h4 : f = 1 → p % 4 = 1) : ShapeInEAS 1 (fun X _ => LieModel X .PSU 3 p f) := by
  intro L₀ _ _ hs hnab hP A S hAS
  by_cases hf : f = 1
  · subst hf
    exact shapeInEAS_u3_one hp (h4 rfl) L₀ hs hnab hP A S hAS
  · exact shapeInEAS_u3_pow h hp hp2 (by have := hP.admissible.2.1; omega) L₀ hs hnab hP A S hAS

end L3All

end CFSG.LocalAnalysis.WeakClosure81

end
