
module

public import CFSG.Sporadic.Co1.Module.PairsCheckBase

public import CFSG.Sporadic.Co1.Module.Forms
public import CFSG.Sporadic.Co1.Module.PairsCheckInputs
public import Certificates.Certificate10076
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import Certificates.Certificate10076Base

public section

namespace CFSG.Sporadic.Co1.Module.Pairs

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Th.Native CFSG.Perm.Native

theorem pairsCheck_ok : pairsCheck = true :=
  Certificates.certificate10076

theorem pairsCheck_parts :
    (orbitOf 2 98280).pts[0]! = 2 ∧ labCheck dat = true ∧
    witnessCheck = true ∧ mclCheck = true := by
  have h := pairsCheck_ok
  unfold pairsCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem pts_zero :
    (orbitOf 2 98280).pts[0]! = 2 := pairsCheck_parts.1

theorem labs_spec : ∀ p < 98280, (labs dat)[p]! =
    tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
      ((orbitOf 2 98280).pts[0]! ^^^ (orbitOf 2 98280).pts[p]!) :=
  labCheck_spec pairsCheck_parts.2.1

theorem exists_stab_pt
    {p q : ℕ} (hp : p < 98280) (hq : q < 98280)
    (h : (labs dat)[p]! = (labs dat)[q]!) :
    ∃ g : NativeSporadic.Co1, g • v₂ = v₂ ∧ g • orbitVec 2 98280 p = orbitVec 2 98280 q := by
  obtain ⟨g, hg1, hg⟩ := subLab_orb CFSG.Sporadic.Co1.co1Facts (k := 3) rfl ⟨p, hp⟩ ⟨q, hq⟩
    (Fin.ext h)
  have h1 : P dat (g • (⟨p, hp⟩ : Fin dat.n)).val = g • P dat p :=
    P_smul co1BaseFacts g ⟨p, hp⟩
  have h0 : g • root CFSG.Sporadic.Co1.co1Facts = root CFSG.Sporadic.Co1.co1Facts :=
    lvl_one_fix CFSG.Sporadic.Co1.co1Facts hg1
  have h2 : P dat (g • root CFSG.Sporadic.Co1.co1Facts).val = g • P dat 0 :=
    P_smul co1BaseFacts g (root CFSG.Sporadic.Co1.co1Facts)
  rw [h0] at h2
  rw [hg] at h1
  obtain ⟨g', hg'⟩ := exists_co1_of_mem_Jmat g
  let g₁ : Jmat := g
  have hconv : ∀ v : Vec24, g' • v = g₁ • v := fun v => by
    rw [smul_eq_mulVec, ← hg']; rfl
  have hP0 : P dat 0 = v₂ := by
    show toVecD 24 (orbitOf 2 98280).pts[0]! = v₂
    rw [pts_zero, toVecD_v₂]
  refine ⟨g', ?_, ?_⟩
  · rw [hconv]
    have : g₁ • v₂ = v₂ := by rw [← hP0]; exact h2.symm
    exact this
  · rw [hconv]
    exact h1.symm

theorem toVecD_xor_pt (p : ℕ) :
    toVecD 24 ((orbitOf 2 98280).pts[0]! ^^^ (orbitOf 2 98280).pts[p]!) =
      v₂ + orbitVec 2 98280 p := by
  rw [toVecD_xor, pts_zero, toVecD_v₂]; rfl

theorem xor_pt_lt
    {p : ℕ} (hp : p < 98280) :
    (orbitOf 2 98280).pts[0]! ^^^ (orbitOf 2 98280).pts[p]! < 2 ^ 24 :=
  Nat.xor_lt_two_pow (by rw [pts_zero]; norm_num) ((vOrbitOK_facts orbitOK_v₂).2 p hp).1

theorem cls_eq
    {j : ℕ} (hj : j < 4) :
    cls j = orbitVec 2 98280 '' {p | p < 98280 ∧ (labs dat)[p]! = j} := by
  ext y
  simp only [cls, Set.mem_ofPred_eq, Set.mem_image, tyOrbC_eq, orbit_Co1_eq, orbit_v₂_eq]
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hy⟩
    have hp' : p < 98280 := hp
    refine ⟨p, ⟨hp', ?_⟩, rfl⟩
    rw [labs_spec p hp']
    refine (tyLab_spec _ (xor_pt_lt hp') j hj).2 ?_
    rw [toVecD_xor_pt]
    exact hy
  · rintro ⟨p, ⟨hp, hl⟩, rfl⟩
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    rw [labs_spec p hp] at hl
    have := (tyLab_spec _ (xor_pt_lt hp) j hj).1 hl
    rw [toVecD_xor_pt] at this
    exact this

theorem cls_trans
    {j : ℕ} (hj : j < 4) {y y' : Vec24} (hy : y ∈ cls j) (hy' : y' ∈ cls j) :
    ∃ g : NativeSporadic.Co1, g • v₂ = v₂ ∧ g • y = y' := by
  rw [cls_eq hj] at hy hy'
  obtain ⟨p, ⟨hp, hpl⟩, rfl⟩ := hy
  obtain ⟨q, ⟨hq, hql⟩, rfl⟩ := hy'
  exact exists_stab_pt hp hq (hpl.trans hql.symm)

theorem cls_ncard
    {j : ℕ} (hj : j < 4) : (cls j).ncard = dat.subSizes[j]! := by
  have hF := CFSG.Sporadic.Co1.co1Facts
  have hcard := card_subLab hF (k := 3) rfl ⟨j, hj⟩
  set F := Finset.univ.filter (fun p : Fin dat.n => subLab hF (k := 3) rfl p = ⟨j, hj⟩)
    with hFdef
  have hS : {p : ℕ | p < 98280 ∧ (labs dat)[p]! = j} =
      (fun p : Fin dat.n => p.val) '' ↑F := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and,
      hFdef]
    constructor
    · rintro ⟨hp, hl⟩
      exact ⟨⟨p, hp⟩, Fin.ext hl, rfl⟩
    · rintro ⟨p', hp', rfl⟩
      exact ⟨p'.isLt, congrArg Fin.val hp'⟩
  rw [cls_eq hj, hS, Set.image_image]
  have hinj : Function.Injective (fun p : Fin dat.n => orbitVec 2 98280 p.val) := by
    intro p q h
    exact Fin.ext ((orbit_spec orbitCheck_v₂).2.1 p p.isLt q q.isLt h)
  rw [Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset, hcard]

theorem exists_type4_adjacent :
    ∃ y : Vec24, y ∈ MulAction.orbit NativeSporadic.Co1 v₄ ∧
    v₂ + y ∈ MulAction.orbit NativeSporadic.Co1 v₄ := by
  have h := pairsCheck_parts.2.2.1
  unfold witnessCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have h1 := (tyLab_spec 24 (by norm_num) 1 (by norm_num)).1 h.1
  have h2 := (tyLab_spec (24 ^^^ 2) (by norm_num) 1 (by norm_num)).1 h.2
  have e : v₂ + toVecD 24 24 = toVecD 24 (24 ^^^ 2) := by
    rw [toVecD_xor, toVecD_v₂, add_comm]
  refine ⟨toVecD 24 24, ?_, ?_⟩
  · rw [orbit_Co1_eq]; exact h1
  · rw [orbit_Co1_eq, e]; exact h2

theorem mcl_facts :
    ∃ (x y w₀ : Vec24) (K : Subgroup NativeSporadic.Co1),
    x ∈ MulAction.orbit NativeSporadic.Co1 v₂ ∧ y ∈ MulAction.orbit NativeSporadic.Co1 v₂ ∧
    x + y ∈ MulAction.orbit NativeSporadic.Co1 v₃ ∧
    K ≤ MulAction.stabilizer NativeSporadic.Co1 x ⊓ MulAction.stabilizer NativeSporadic.Co1 y ∧
    w₀ ∈ adjSet x y ∧ (∀ w ∈ adjSet x y, ∃ g ∈ K, g • w₀ = w) ∧ (adjSet x y).ncard = 275 := by
  obtain ⟨m₁, hm₁⟩ := mcl_matrix 1
  obtain ⟨m₂, hm₂⟩ := mcl_matrix 2
  have hf : ∀ l < 2, ∀ x, (if l = 0 then m₁ else m₂) • toVecD 24 x =
      toVecD 24 (mclAct (mclRun 1) (mclRun 2) l x) := by
    intro l hl x
    by_cases h0 : l = 0
    · simp only [h0, ite_true, mclAct]; exact act_packed m₁ (mclRun 1) hm₁ x
    · simp only [h0, ite_false, mclAct]; exact act_packed m₂ (mclRun 2) hm₂ x
  have hc := pairsCheck_parts.2.2.2
  unfold mclCheck mclCheckOf at hc
  exact ⟨_, _, _, _, mclCheckT_spec (by norm_num) (by norm_num) (by norm_num) hc hf⟩

end CFSG.Sporadic.Co1.Module.Pairs
