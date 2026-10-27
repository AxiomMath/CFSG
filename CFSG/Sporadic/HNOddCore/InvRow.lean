
module

public import CFSG.Sporadic.HNOddCore.InvFixBase
public import CFSG.Sporadic.HNOddCore.SCheck
public import CFSG.Sporadic.HNOddCore.ChainUtil
public import CFSG.Sporadic.HNOddCore.OrbitCert
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

@[expose] def CJ
    (t : RH) : Subgroup JH := (Subgroup.centralizer {t}).comap jR

theorem mem_CJ
    {t : RH} {g : JH} : g ∈ CJ t ↔ jR g * t = t * jR g := by
  rw [CJ, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]

theorem CJ_jR
    (t : JH) : CJ (jR t) = Subgroup.centralizer {t} := by
  ext g
  rw [mem_CJ, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  exact jR_injective.eq_iff

theorem commute_of_thetaJ
    {a b : JH} (ha : a ∈ HJ) (hb : b ∈ HJ)
    (h : (thetaJ ⟨a, ha⟩ : Perm (Fin 12)) * thetaJ ⟨b, hb⟩ =
      (thetaJ ⟨b, hb⟩ : Perm (Fin 12)) * thetaJ ⟨a, ha⟩) : a * b = b * a := by
  rw [← thetaJ_mul a b ha hb, ← thetaJ_mul b a hb ha] at h
  have := congrArg Subtype.val (thetaJ.injective (Subtype.ext h))
  exact this

theorem jR_comm_cR
    {h : JH} (hh : h ∈ HJ)
    (hc : (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) * swap 0 1 =
      swap 0 1 * (thetaJ ⟨h, hh⟩ : Perm (Fin 12))) :
    jR h * cR = cR * jR h := by
  have e : (⟨conjC h, conjC_mem_HJ hh⟩ : HJ) = ⟨h, hh⟩ := thetaJ.injective (Subtype.ext (by
    rw [thetaJ_conjC h hh, ← hc, mul_assoc, swap01_mul_self, mul_one]))
  have e' : conjC h = h := Subtype.mk.inj e
  rw [cR_mul_jR, e']

theorem commute_of_prep {σ τ : Perm (Fin 12)} {a b : Array ℕ} (ha : PRep 12 a σ)
    (hb : PRep 12 b τ) (h : commOK a b = true) : σ * τ = τ * σ :=
  eq_of_peq (prep_pcomp ha hb) (prep_pcomp hb ha) h

theorem orbit_subset_of_invariant {G Y : Type*} [Group G] [MulAction G Y] {O : Set Y}
    (hO : ∀ g : G, ∀ y ∈ O, g • y ∈ O) {x y : Y} (hy : y ∈ O)
    (hxy : y ∈ MulAction.orbit G x) : MulAction.orbit G x ⊆ O := by
  rw [← MulAction.orbit_eq_iff.2 hxy]
  rintro _ ⟨g, rfl⟩
  exact hO g y hy

theorem inter_eq_empty_or {Y : Type*} {O P : Set Y} (h : (O ∩ P).Nonempty → P ⊆ O) :
    O ∩ P = ∅ ∨ O ∩ P = P := by
  by_cases hne : (O ∩ P).Nonempty
  · exact Or.inr (Set.inter_eq_right.2 (h hne))
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.1 hne)

theorem ncard_of_three_orbits {Y : Type*} [Finite Y] {O P₁ P₂ P₃ : Set Y}
    (hcov : O ⊆ P₁ ∪ P₂ ∪ P₃) (h12 : Disjoint P₁ P₂) (h13 : Disjoint P₁ P₃)
    (h23 : Disjoint P₂ P₃) (h1 : O ∩ P₁ = P₁) (h2 : O ∩ P₂ = ∅ ∨ O ∩ P₂ = P₂)
    (h3 : O ∩ P₃ = ∅ ∨ O ∩ P₃ = P₃) :
    O.ncard = P₁.ncard ∨ O.ncard = P₁.ncard + P₂.ncard ∨ O.ncard = P₁.ncard + P₃.ncard ∨
      O.ncard = P₁.ncard + P₂.ncard + P₃.ncard := by
  have hO : O = (O ∩ P₁) ∪ (O ∩ P₂) ∪ (O ∩ P₃) := by
    ext x
    constructor
    · intro hx
      rcases hcov hx with (h | h) | h
      · exact Or.inl (Or.inl ⟨hx, h⟩)
      · exact Or.inl (Or.inr ⟨hx, h⟩)
      · exact Or.inr ⟨hx, h⟩
    · rintro ((h | h) | h) <;> exact h.1
  have d12 : Disjoint (O ∩ P₁) (O ∩ P₂) :=
    Disjoint.mono Set.inter_subset_right Set.inter_subset_right h12
  have d3 : Disjoint ((O ∩ P₁) ∪ (O ∩ P₂)) (O ∩ P₃) :=
    Disjoint.union_left (Disjoint.mono Set.inter_subset_right Set.inter_subset_right h13)
      (Disjoint.mono Set.inter_subset_right Set.inter_subset_right h23)
  have hc : O.ncard = (O ∩ P₁).ncard + (O ∩ P₂).ncard + (O ∩ P₃).ncard := by
    conv_lhs => rw [hO]
    rw [Set.ncard_union_eq d3 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq d12 (Set.toFinite _) (Set.toFinite _)]
  rw [hc, h1]
  rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> rw [h2, h3] <;> simp

theorem ncard_of_two_orbits {Y : Type*} [Finite Y] {O P₁ P₂ : Set Y} (hcov : O ⊆ P₁ ∪ P₂)
    (h12 : Disjoint P₁ P₂) (h1 : O ∩ P₁ = P₁) (h2 : O ∩ P₂ = ∅ ∨ O ∩ P₂ = P₂) :
    O.ncard = P₁.ncard ∨ O.ncard = P₁.ncard + P₂.ncard := by
  have hO : O = (O ∩ P₁) ∪ (O ∩ P₂) := by
    ext x
    constructor
    · intro hx
      rcases hcov hx with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (h | h) <;> exact h.1
  have d12 : Disjoint (O ∩ P₁) (O ∩ P₂) :=
    Disjoint.mono Set.inter_subset_right Set.inter_subset_right h12
  have hc : O.ncard = (O ∩ P₁).ncard + (O ∩ P₂).ncard := by
    conv_lhs => rw [hO]
    rw [Set.ncard_union_eq d12 (Set.toFinite _) (Set.toFinite _)]
  rw [hc, h1]
  rcases h2 with h | h
  · left
    rw [h, Set.ncard_empty, add_zero]
  · right
    rw [h]

theorem mem_toList_iff {F : Array ℕ} (hF : PtList hnsData.n F) (x : X) :
    x.val ∈ F.toList ↔ ∃ k : Fin F.size, hF.pt k = x := by
  rw [Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, he⟩
    exact ⟨⟨k, hk⟩, Fin.ext (by rw [PtList.pt_val, getElem!_pos F k hk, he])⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    exact ⟨k, hk, by rw [PtList.pt_val, getElem!_pos F k hk]⟩

theorem fix_iff_listed
    {t : RH} {T : Array ℕ} {F : Array ℕ} (hT : PRep hnsData.n T (permR t))
    (h : fixListOK hnsData.n T F.toList = true) (hF : PtList hnsData.n F) :
    ∀ x : X, t • x = x ↔ ∃ k : Fin F.size, hF.pt k = x := fun x => by
  rw [← mem_toList_iff hF, ← (fixList_spec hT h).1 x]
  rfl

theorem card_fix_listed
    {t : RH} {T : Array ℕ} {F : Array ℕ} (hT : PRep hnsData.n T (permR t))
    (h : fixListOK hnsData.n T F.toList = true) :
    Nat.card {x : X // t • x = x} = F.size := by
  have := (fixList_spec hT h).2
  rw [Array.length_toList] at this
  rw [← this, ← card_fix_eq]
  rfl

end CFSG.Sporadic.HNOddCore
