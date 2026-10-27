module

public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
public import CFSG.GH74.QTGen4.DSGen4.Defs
public import CFSG.GroupTheory.SL2SylowTwo

import CFSG.RankThree.GF2n.QuadraticSection
import CFSG.RankThree.GF2n.NaturalDecomp
import CFSG.RankThree.GF2n.Tim78S48PhaseGen
import CFSG.GroupTheory.SupIndepFixedPointFree
import CFSG.Quasithin.Recognition.St84.Gen.NatSecQuot
import CFSG.Timmesfeld.Bridge.SL2FactsCoord
public import CFSG.GH74.QTGen4.DSGen4.Statements

public section

namespace CFSG.Quasithin.St84

open Matrix CFSG.Open CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne
open scoped MatrixGroups commutatorElement Pointwise

private def fixedAdd (K : Type) [Field K] (V : Type*) [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) : AddSubgroup V where
  carrier := {v | ∀ a ∈ A, a • v = v}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := fun {u v} hu hv a ha => by rw [smul_add, hu a ha, hv a ha]
  neg_mem' := fun {u} hu a ha => by rw [smul_neg, hu a ha]

private def commAdd (K : Type) [Field K] (V : Type*) [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) : AddSubgroup V :=
  AddSubgroup.closure {w | ∃ a ∈ A, ∃ v : V, w = a • v - v}

private theorem fixed_inf_sup_eq {K : Type} [Field K] {V : Type*} [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} {a S : AddSubgroup V}
    (hdis : Disjoint a S)
    (ha : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ a, g • v ∈ a)
    (hS : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ S, g • v ∈ S) :
    fixedAdd K V A ⊓ (a ⊔ S) = (fixedAdd K V A ⊓ a) ⊔ (fixedAdd K V A ⊓ S) := by
  apply le_antisymm
  · rintro v ⟨hvfix, hvaS⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := AddSubgroup.mem_sup.mp hvaS
    have hfixx : x ∈ fixedAdd K V A := by
      intro g hg
      have hdiff : g • x - x = y - g • y := by
        have h := hvfix g hg
        rw [smul_add] at h
        have h' : g • x - x - (y - g • y) = 0 := by
          rw [show g • x - x - (y - g • y) = (g • x + g • y) - (x + y) by
            abel, h, sub_self]
        exact sub_eq_zero.mp h'
      have hmem : g • x - x ∈ a ⊓ S :=
        ⟨a.sub_mem (ha g x hx) hx, by rw [hdiff]; exact S.sub_mem hy (hS g y hy)⟩
      rw [disjoint_iff.mp hdis, AddSubgroup.mem_bot, sub_eq_zero] at hmem
      exact hmem
    have hfixy : y ∈ fixedAdd K V A := by
      intro g hg
      have h := hvfix g hg
      rw [smul_add, hfixx g hg] at h
      exact add_left_cancel h
    exact AddSubgroup.mem_sup.mpr ⟨x, ⟨hfixx, hx⟩, y, ⟨hfixy, hy⟩, rfl⟩
  · refine sup_le ?_ ?_
    · exact le_inf inf_le_left (inf_le_right.trans le_sup_left)
    · exact le_inf inf_le_left (inf_le_right.trans le_sup_right)

private theorem fixed_inf_finset_sup_eq {K : Type} [Field K] {V : Type*} [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} {s : Finset (AddSubgroup V)}
    (hs : s.SupIndep id)
    (hinv : ∀ W ∈ s, ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ W, g • v ∈ W) :
    fixedAdd K V A ⊓ s.sup id = s.sup (fun W => fixedAdd K V A ⊓ W) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hdis : Disjoint a (s.sup id) := by
        have h := (Finset.supIndep_iff_disjoint_erase (s := insert a s) (f := id)).mp hs a
          (Finset.mem_insert_self a s)
        rwa [Finset.erase_insert ha] at h
      have hts : s.SupIndep id := hs.subset (Finset.subset_insert a s)
      have hmem : ∀ W ∈ s, ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ W, g • v ∈ W :=
        fun W hW => hinv W (Finset.mem_insert_of_mem hW)
      have hsupInv : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
          ∀ v ∈ s.sup id, g • v ∈ s.sup id :=
        CFSG.RankThree.GF2n.sup_isInv hmem
      have hinta : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
          ∀ v ∈ a, g • v ∈ a := hinv a (Finset.mem_insert_self a s)
      have ih' := ih hts hmem
      rw [Finset.sup_insert, Finset.sup_insert]
      change fixedAdd K V A ⊓ (a ⊔ s.sup id) =
        (fixedAdd K V A ⊓ a) ⊔ s.sup (fun W => fixedAdd K V A ⊓ W)
      rw [fixed_inf_sup_eq hdis hinta hsupInv, ih']

private theorem fixed_inf_natural_eq_map {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type*} [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} {W : AddSubgroup V}
    {θ : (Fin 2 → K) →+ V} (hinj : Function.Injective θ) (hrange : θ.range = W)
    (hθ : ∀ (x : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
      θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v) :
    fixedAdd K V A ⊓ W = (SL2Nat.fixedSub (F := K) A).toAddSubgroup.map θ := by
  apply le_antisymm
  · rintro w ⟨hwfix, hwW⟩
    have hwr : w ∈ θ.range := hrange ▸ hwW
    obtain ⟨u, rfl⟩ := hwr
    refine AddSubgroup.mem_map.mpr ⟨u, ?_, rfl⟩
    change u ∈ SL2Nat.fixedSub A
    rw [SL2Nat.mem_fixedSub]
    intro a ha
    rw [SL2Nat.lin_apply]
    apply hinj
    rw [hθ, hwfix a ha]
  · rintro w ⟨u, hu, rfl⟩
    refine ⟨?_, ?_⟩
    · have hu' : ∀ a ∈ A, (a : Matrix (Fin 2) (Fin 2) K) *ᵥ u = u := by
        intro a ha
        rw [← SL2Nat.lin_apply]
        exact (SL2Nat.mem_fixedSub).mp hu a ha
      change ∀ a ∈ A, a • θ u = θ u
      intro a ha
      rw [← hθ]
      exact congrArg θ (hu' a ha)
    · rw [← hrange]
      exact ⟨u, rfl⟩

private theorem card_sup_of_supIndep_map {V : Type*} [AddCommGroup V]
    (s : Finset (AddSubgroup V)) (f : AddSubgroup V → AddSubgroup V)
    (hs : s.SupIndep f) :
    Nat.card ↥(s.sup f) = ∏ W ∈ s, Nat.card ↥(f W) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hs1 : s.SupIndep f := hs.subset (Finset.subset_insert a s)
      have hdis : Disjoint (f a) (s.sup f) := by
        have h := (Finset.supIndep_iff_disjoint_erase (s := insert a s) (f := f)).mp hs a
          (Finset.mem_insert_self a s)
        rwa [Finset.erase_insert ha] at h
      rw [Finset.sup_insert, Finset.prod_insert ha,
        CFSG.RankThree.GF2n.Tim78.card_sup_of_disjoint (f a) (s.sup f) hdis, ih hs1]

private theorem natCard_fixed_inf_natural {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hA2 : IsPGroup 2 A)
    (hAcard : Nat.card A = Nat.card K) {W : AddSubgroup V} {θ : (Fin 2 → K) →+ V}
    (hinj : Function.Injective θ) (hrange : θ.range = W)
    (hθ : ∀ (x : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
      θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v) :
    Nat.card ↥(fixedAdd K V A ⊓ W) = Nat.card K := by
  rw [fixed_inf_natural_eq_map (K := K) (V := V) hinj hrange hθ]
  rw [AddSubgroup.card_map_of_injective (f := θ) hinj]
  have h : Nat.card ↥((SL2Nat.fixedSub (F := K) A).toAddSubgroup) =
      Nat.card ↥(SL2Nat.fixedSub (F := K) A) := rfl
  rw [h]
  exact SL2Nat.natCard_fixedSub_of_card hA2 hAcard

private theorem card_sup_natural {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Finite V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    (s : Finset (AddSubgroup V)) (hs : s.SupIndep id) (hsup : s.sup id = ⊤)
    (hW : ∀ W ∈ s, ∃ θ : (Fin 2 → K) →+ V, Function.Injective θ ∧ θ.range = W ∧
      ∀ (x : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
        θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v) :
    Nat.card V = (Nat.card K ^ 2) ^ s.card := by
  classical
  have hcard : ∀ W ∈ s, Nat.card W = Nat.card K ^ 2 := by
    intro W hWs
    obtain ⟨θ, hinj, hrange, -⟩ := hW W hWs
    have hθ : Nat.card ↥θ.range = Nat.card (Fin 2 → K) :=
      (Nat.card_congr (Equiv.ofInjective θ hinj)).symm
    rw [← hrange, hθ, Nat.card_fun, Nat.card_fin]
  calc Nat.card V = Nat.card ↥(s.sup id) := by rw [hsup, AddSubgroup.card_top]
    _ = ∏ W ∈ s, Nat.card W := CFSG.RankThree.GF2n.Tim78.card_sup_of_supIndep s hs
    _ = ∏ W ∈ s, Nat.card K ^ 2 := Finset.prod_congr rfl hcard
    _ = (Nat.card K ^ 2) ^ s.card := by rw [Finset.prod_const]

private theorem card_fixed_sup_natural {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Finite V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hA2 : IsPGroup 2 A)
    (hAcard : Nat.card A = Nat.card K) (s : Finset (AddSubgroup V))
    (hs : s.SupIndep id) (hsup : s.sup id = ⊤)
    (hW : ∀ W ∈ s, ∃ θ : (Fin 2 → K) →+ V, Function.Injective θ ∧ θ.range = W ∧
      ∀ (x : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
        θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v) :
    Nat.card ↥(fixedAdd K V A) = Nat.card K ^ s.card := by
  classical
  have hinv : ∀ W ∈ s, ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      ∀ v ∈ W, g • v ∈ W := by
    intro W hWs g v hv
    obtain ⟨θ, hinj, hrange, hθ⟩ := hW W hWs
    have hv' : v ∈ θ.range := hrange ▸ hv
    obtain ⟨u, rfl⟩ := hv'
    rw [← hrange]
    exact ⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ u, hθ g u⟩
  have hfix_eq : fixedAdd K V A = s.sup (fun W => fixedAdd K V A ⊓ W) := by
    have h := fixed_inf_finset_sup_eq (A := A) hs hinv
    rwa [hsup, inf_top_eq] at h
  rw [hfix_eq]
  rw [card_sup_of_supIndep_map s (fun W => fixedAdd K V A ⊓ W)
    (hs.antitone_fun fun W hWs => inf_le_right)]
  have hprod : ∀ W ∈ s, Nat.card ↥(fixedAdd K V A ⊓ W) = Nat.card K := by
    intro W hWs
    obtain ⟨θ, hinj, hrange, hθ⟩ := hW W hWs
    exact natCard_fixed_inf_natural (A := A) hA2 hAcard hinj hrange hθ
  rw [Finset.prod_congr rfl hprod, Finset.prod_const]

private theorem commSub_toAddSubgroup_eq_closure {F : Type} [Field F]
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
    (SL2Nat.commSub A).toAddSubgroup =
      AddSubgroup.closure {w : Fin 2 → F | ∃ a ∈ A, ∃ v : Fin 2 → F,
        w = SL2Nat.lin a v - v} := by
  let genSet : Set (Fin 2 → F) := {w | ∃ a ∈ A, ∃ v : Fin 2 → F,
    w = SL2Nat.lin a v - v}
  let C : AddSubgroup (Fin 2 → F) := AddSubgroup.closure genSet
  have hsmul : ∀ c : F, ∀ d ∈ genSet, c • d ∈ genSet := by
    rintro c d ⟨a, ha, v, rfl⟩
    refine ⟨a, ha, c • v, ?_⟩
    rw [smul_sub, (SL2Nat.lin a).map_smul]
  apply le_antisymm
  · show (SL2Nat.commSub A : Set (Fin 2 → F)) ⊆ C
    rw [SL2Nat.commSub]
    intro x hx
    change x ∈ (Submodule.span F genSet).toAddSubmonoid at hx
    rw [Submodule.span_eq_closure] at hx
    exact ((AddSubmonoid.closure_le (s := (Set.univ : Set F) • genSet)
      (S := C.toAddSubmonoid)).mpr fun y hy => by
      obtain ⟨c, -, d, hd, rfl⟩ := hy
      exact AddSubgroup.subset_closure (hsmul c d hd)) hx
  · intro x hx
    rw [SL2Nat.commSub]
    exact ((AddSubgroup.closure_le (K := (Submodule.span F genSet).toAddSubgroup)).mpr
      fun y hy => Submodule.subset_span hy) hx

private theorem fixed_inf_le_commAdd_of_natural {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hA2 : IsPGroup 2 A)
    (hAcard : Nat.card A = Nat.card K) {W : AddSubgroup V}
    {θ : (Fin 2 → K) →+ V} (hinj : Function.Injective θ) (hrange : θ.range = W)
    (hθ : ∀ (x : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
      θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v) :
    fixedAdd K V A ⊓ W ≤ commAdd K V A := by
  have hmap : (SL2Nat.commSub (F := K) A).toAddSubgroup.map θ =
      AddSubgroup.closure {w : V | ∃ a ∈ A, ∃ v ∈ W, a • v - v = w} := by
    rw [commSub_toAddSubgroup_eq_closure (A := A), AddMonoidHom.map_closure]
    congr 1
    ext w
    constructor
    · rintro ⟨d, ⟨a, ha, v, rfl⟩, rfl⟩
      have heq : θ (SL2Nat.lin a v - v) = a • θ v - θ v := by
        rw [map_sub, SL2Nat.lin_apply, hθ]
      rw [heq]
      exact ⟨a, ha, θ v, hrange ▸ ⟨v, rfl⟩, rfl⟩
    · rintro ⟨a, ha, v, hv, rfl⟩
      have hv' : v ∈ θ.range := hrange ▸ hv
      obtain ⟨u, rfl⟩ := hv'
      have heq : a • θ u - θ u = θ (SL2Nat.lin a u - u) := by
        rw [map_sub, SL2Nat.lin_apply, hθ]
      rw [heq]
      exact ⟨SL2Nat.lin a u - u, ⟨a, ha, u, rfl⟩, rfl⟩
  have hcommSub : (SL2Nat.commSub (F := K) A).toAddSubgroup =
      (SL2Nat.fixedSub (F := K) A).toAddSubgroup := by
    rw [SL2Nat.commSub_eq_fixedSub_of_card hA2 hAcard]
  have hlocal : AddSubgroup.closure {w : V | ∃ a ∈ A, ∃ v ∈ W, a • v - v = w} ≤
      commAdd K V A := by
    refine (AddSubgroup.closure_le (K := commAdd K V A)).mpr ?_
    rintro w ⟨a, ha, v, hv, rfl⟩
    exact AddSubgroup.subset_closure ⟨a, ha, v, rfl⟩
  have hloc_eq : AddSubgroup.closure {w : V | ∃ a ∈ A, ∃ v ∈ W, a • v - v = w} =
      fixedAdd K V A ⊓ W := by
    rw [← hmap, hcommSub, fixed_inf_natural_eq_map (K := K) (V := V) hinj hrange hθ]
  rwa [hloc_eq] at hlocal

private theorem commAdd_eq_fixedAdd_of_natural {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Finite V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hA2 : IsPGroup 2 A)
    (hAcard : Nat.card A = Nat.card K)
    (hquad : ∀ a ∈ A, ∀ a' ∈ A, ∀ v : V, a' • (a • v - v) = a • v - v)
    (s : Finset (AddSubgroup V)) (hs : s.SupIndep id) (hsup : s.sup id = ⊤)
    (hW : ∀ W ∈ s, ∃ θ : (Fin 2 → K) →+ V, Function.Injective θ ∧ θ.range = W ∧
      ∀ (x : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
        θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v) :
    commAdd K V A = fixedAdd K V A := by
  classical
  have hcomm_le : commAdd K V A ≤ fixedAdd K V A := by
    rw [commAdd]
    refine (AddSubgroup.closure_le (K := fixedAdd K V A)).mpr ?_
    rintro w ⟨a, ha, v, rfl⟩
    change ∀ a' ∈ A, a' • (a • v - v) = a • v - v
    intro a' ha'
    exact hquad a ha a' ha' v
  have hloc_le : ∀ W ∈ s, fixedAdd K V A ⊓ W ≤ commAdd K V A := by
    intro W hWs
    obtain ⟨θ, hinj, hrange, hθ⟩ := hW W hWs
    exact fixed_inf_le_commAdd_of_natural (A := A) hA2 hAcard hinj hrange hθ
  have hpart : ∀ W ∈ s, commAdd K V A ⊓ W = fixedAdd K V A ⊓ W := by
    intro W hWs
    apply le_antisymm
    · exact le_inf (inf_le_left.trans hcomm_le) inf_le_right
    · exact le_inf (hloc_le W hWs) inf_le_right
  have hinv : ∀ W ∈ s, ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      ∀ v ∈ W, g • v ∈ W := by
    intro W hWs g v hv
    obtain ⟨θ, hinj, hrange, hθ⟩ := hW W hWs
    have hv' : v ∈ θ.range := hrange ▸ hv
    obtain ⟨u, rfl⟩ := hv'
    rw [← hrange]
    exact ⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ u, hθ g u⟩
  have hfix_eq : fixedAdd K V A = s.sup (fun W => fixedAdd K V A ⊓ W) := by
    have h := fixed_inf_finset_sup_eq (A := A) hs hinv
    rwa [hsup, inf_top_eq] at h
  refine le_antisymm hcomm_le ?_
  rw [hfix_eq]
  calc s.sup (fun W => fixedAdd K V A ⊓ W)
      = s.sup (fun W => commAdd K V A ⊓ W) := by
          apply Finset.sup_congr rfl
          intro W hWs
          exact (hpart W hWs).symm
    _ ≤ commAdd K V A := Finset.sup_le fun W hWs => inf_le_left

private theorem natCard_toSubgroup {V : Type*} [AddGroup V] (S : AddSubgroup V) :
    Nat.card ↥(S.toSubgroup) = Nat.card S := by
  refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd ?_)
  intro a
  rw [Multiplicative.mem_toSubgroup]
  rfl

private def sectionPiHom {G : Type} [Group G] {K : Type} [Field K]
    {L E Z : Subgroup G} {φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K}
    (S : CFSG.RankThree.GF2n.SectionModule L E Z φ) : ↥E →* Multiplicative S.W where
  toFun e := Multiplicative.ofAdd (S.π e)
  map_one' := by rw [S.map_one]; rfl
  map_mul' e f := by rw [S.map_mul]; rfl

private theorem sectionPiHom_ker {G : Type} [Group G] {K : Type} [Field K]
    {L E Z : Subgroup G} {φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K}
    (S : CFSG.RankThree.GF2n.SectionModule L E Z φ) :
    (sectionPiHom S).ker = Z.subgroupOf E := by
  ext e
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact (S.eq_zero_iff e).mp (Multiplicative.ofAdd.injective h)
  · intro h
    change Multiplicative.ofAdd (S.π e) = 1
    rw [(S.eq_zero_iff e).mpr h]
    rfl

private theorem sectionPiHom_surjective {G : Type} [Group G] {K : Type} [Field K]
    {L E Z : Subgroup G} {φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K}
    (S : CFSG.RankThree.GF2n.SectionModule L E Z φ) :
    Function.Surjective (sectionPiHom S) := by
  intro q
  obtain ⟨e, he⟩ := S.surjective (Multiplicative.toAdd q)
  refine ⟨e, ?_⟩
  change Multiplicative.ofAdd (S.π e) = q
  rw [he]
  rfl

private theorem natCard_map_eq_relIndex {G : Type} [Group G] {K : Type} [Field K]
    {L E Z : Subgroup G} {φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K}
    (S : CFSG.RankThree.GF2n.SectionModule L E Z φ) {F : Subgroup G}
    (hFE : F ≤ E) :
    Nat.card ↥((F.subgroupOf E).map (sectionPiHom S)) = Z.relIndex F := by
  classical
  let F' : Subgroup ↥E := F.subgroupOf E
  let f : ↥F' →* Multiplicative S.W := (sectionPiHom S).comp F'.subtype
  have hker : f.ker = (Z.subgroupOf E).subgroupOf F' := by
    ext x
    change sectionPiHom S (x : ↥E) = 1 ↔ ((x : ↥E) : G) ∈ Z
    rw [← MonoidHom.mem_ker (f := sectionPiHom S), sectionPiHom_ker S,
      Subgroup.mem_subgroupOf]
  have hrange : f.range = F'.map (sectionPiHom S) := by
    rw [show f = (sectionPiHom S).comp F'.subtype from rfl, MonoidHom.range_comp,
      Subgroup.range_subtype]
  have hsub : (Z.subgroupOf E).subgroupOf F' = (Z.subgroupOf F).comap
      (Subgroup.subgroupOfEquivOfLe hFE).toMonoidHom := by
    ext x
    exact Iff.rfl
  have hindex : f.ker.index = (Z.subgroupOf F).index := by
    rw [hker, hsub]
    exact Subgroup.index_comap_of_surjective (H := Z.subgroupOf F)
      (f := (Subgroup.subgroupOfEquivOfLe hFE).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hFE).surjective
  calc
    Nat.card ↥((F.subgroupOf E).map (sectionPiHom S)) = Nat.card ↥f.range := by
      rw [hrange]
    _ = f.ker.index := (Subgroup.index_ker f).symm
    _ = (Z.subgroupOf F).index := hindex
    _ = Z.relIndex F := rfl

private theorem map_relCent_eq_fixed {G : Type} [Group G] {K : Type} [Field K]
    {L E Z T : Subgroup G} {φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K}
    (S : CFSG.RankThree.GF2n.SectionModule L E Z φ)
    (hAX : ∀ a ∈ L, ∀ x ∈ E, a * x * a⁻¹ ∈ E)
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G)) (hTle : T ≤ L)
    (hUpper : (T.subgroupOf L).map φ = upperUnipotent K) :
    ((relCent E Z T).subgroupOf E).map (sectionPiHom S) =
      AddSubgroup.toSubgroup (fixedAdd K S.W (upperUnipotent K)) := by
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    rw [Multiplicative.mem_toSubgroup]
    change ∀ a ∈ upperUnipotent K, a • S.π e = S.π e
    intro a ha
    rw [← hUpper] at ha
    obtain ⟨t, ht, hta⟩ := Subgroup.mem_map.mp ha
    rw [← hta]
    exact (S.smul_eq_iff_commutator_mem hAX t e).mpr (by
      have h1 : ⁅(e : G), (t : G)⁆ ∈ Z :=
        ((mem_relCent hEZ).mp (Subgroup.mem_subgroupOf.mp he)).2 (t : G)
          (Subgroup.mem_subgroupOf.mp ht)
      simpa [commutatorElement_inv] using Z.inv_mem h1)
  · intro hx
    rw [Multiplicative.mem_toSubgroup] at hx
    obtain ⟨e, he⟩ := S.surjective (Multiplicative.toAdd x)
    refine ⟨e, ?_, ?_⟩
    · change (e : G) ∈ relCent E Z T
      rw [mem_relCent hEZ]
      refine ⟨e.2, fun t ht => ?_⟩
      have hmemA : φ ⟨t, hTle ht⟩ ∈ upperUnipotent K := by
        rw [← hUpper]
        exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr ht)
      have hfix := hx (φ ⟨t, hTle ht⟩) hmemA
      rw [← he] at hfix
      have hcomm := (S.smul_eq_iff_commutator_mem hAX ⟨t, hTle ht⟩ e).mp hfix
      simpa [commutatorElement_inv] using Z.inv_mem hcomm
    · change Multiplicative.ofAdd (S.π e) = x
      rw [he]
      rfl

private theorem sectionPiHom_commutator {G : Type} [Group G] {K : Type} [Field K]
    {L E Z T : Subgroup G} {φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K}
    (S : CFSG.RankThree.GF2n.SectionModule L E Z φ)
    (hAX : ∀ a ∈ L, ∀ x ∈ E, a * x * a⁻¹ ∈ E)
    (hKE : ⁅T, E⁆ ≤ E) (t : ↥L) (ht : (t : G) ∈ T) (e : ↥E) :
    sectionPiHom S ⟨⁅(t : G), (e : G)⁆, hKE
      (Subgroup.commutator_mem_commutator ht e.2)⟩ =
      Multiplicative.ofAdd (φ t • S.π e - S.π e) := by
  let y : ↥E := ⟨(t : G) * (e : G) * (t : G)⁻¹, hAX t t.2 e e.2⟩
  have hval : ((y * e⁻¹ : ↥E) : G) = ⁅(t : G), (e : G)⁆ := by
    simp [y, commutatorElement_def, mul_assoc]
  have hc : (⟨⁅(t : G), (e : G)⁆, hKE
      (Subgroup.commutator_mem_commutator ht e.2)⟩ : ↥E) = y * e⁻¹ :=
    Subtype.ext hval.symm
  calc
    sectionPiHom S ⟨⁅(t : G), (e : G)⁆, hKE
        (Subgroup.commutator_mem_commutator ht e.2)⟩ = sectionPiHom S (y * e⁻¹) := by
      rw [hc]
    _ = sectionPiHom S y * (sectionPiHom S e)⁻¹ := by rw [map_mul, map_inv]
    _ = Multiplicative.ofAdd (S.π y - S.π e) := by
      rw [sub_eq_add_neg]
      rfl
    _ = Multiplicative.ofAdd (φ t • S.π e - S.π e) := by rw [S.smul_eq t e y rfl]

private theorem map_commutator_eq_comm {G : Type} [Group G] {K : Type} [Field K]
    {L E Z T : Subgroup G} {φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K}
    (S : CFSG.RankThree.GF2n.SectionModule L E Z φ)
    (hAX : ∀ a ∈ L, ∀ x ∈ E, a * x * a⁻¹ ∈ E) (hL : L ≤ Subgroup.normalizer (E : Set G))
    (hTle : T ≤ L) (hUpper : (T.subgroupOf L).map φ = upperUnipotent K) :
    ((⁅E, T⁆).subgroupOf E).map (sectionPiHom S) =
      AddSubgroup.toSubgroup (commAdd K S.W (upperUnipotent K)) := by
  classical
  let C : Subgroup (Multiplicative S.W) :=
    AddSubgroup.toSubgroup (commAdd K S.W (upperUnipotent K))
  have hKE : ⁅T, E⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro t ht e he
    have htL : t ∈ L := hTle ht
    have hconj : t * e * t⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hL htL) e).mp he
    rw [commutatorElement_def]
    exact E.mul_mem hconj (E.inv_mem he)
  have hle : ((⁅T, E⁆).subgroupOf E).map (sectionPiHom S) ≤ C := by
    rw [Subgroup.map_le_iff_le_comap]
    have hKle : ⁅T, E⁆ ≤ (C.comap (sectionPiHom S)).map E.subtype := by
      rw [Subgroup.commutator_def]
      refine (Subgroup.closure_le (K := (C.comap (sectionPiHom S)).map E.subtype)).mpr ?_
      rintro g ⟨t, ht, e, he, rfl⟩
      let tL : ↥L := ⟨t, hTle ht⟩
      let eE : ↥E := ⟨e, he⟩
      have hmemE : ⁅t, e⁆ ∈ E :=
        hKE (Subgroup.commutator_mem_commutator ht he)
      have hmemA : φ tL ∈ upperUnipotent K := by
        rw [← hUpper]
        exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr ht)
      have hgen : φ tL • S.π eE - S.π eE ∈ commAdd K S.W (upperUnipotent K) :=
        AddSubgroup.subset_closure ⟨φ tL, hmemA, S.π eE, rfl⟩
      refine Subgroup.mem_map.mpr ⟨⟨⁅t, e⁆, hmemE⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap, Multiplicative.mem_toSubgroup]
      rw [sectionPiHom_commutator (S := S) hAX hKE tL ht eE]
      exact hgen
    have hmap : (⁅T, E⁆).subgroupOf E ≤ C.comap (sectionPiHom S) := by
      have hle' : ((⁅T, E⁆).subgroupOf E).map E.subtype ≤
          (C.comap (sectionPiHom S)).map E.subtype := by
        rwa [Subgroup.map_subgroupOf_eq_of_le hKE]
      have hle'' := (Subgroup.map_le_iff_le_comap (f := E.subtype)).mp hle'
      rwa [Subgroup.comap_map_eq_self_of_injective E.subtype_injective] at hle''
    exact hmap
  have hge : C ≤ ((⁅T, E⁆).subgroupOf E).map (sectionPiHom S) := by
    change AddSubgroup.toSubgroup (commAdd K S.W (upperUnipotent K)) ≤
      ((⁅T, E⁆).subgroupOf E).map (sectionPiHom S)
    rw [commAdd, AddSubgroup.toSubgroup_closure]
    refine (Subgroup.closure_le (K := ((⁅T, E⁆).subgroupOf E).map (sectionPiHom S))).mpr ?_
    rintro x hx
    obtain ⟨a, haA, v, hw⟩ := hx
    have hx' : x = Multiplicative.ofAdd (a • v - v) := by
      rw [show x = Multiplicative.ofAdd (Multiplicative.toAdd x) from rfl, hw]
    rw [hx']
    have ha_map : a ∈ (T.subgroupOf L).map φ := by
      rw [hUpper]
      exact haA
    obtain ⟨t, ht, hta⟩ := Subgroup.mem_map.mp ha_map
    obtain ⟨e, he⟩ := S.surjective v
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    have hmemE : ⁅(t : G), (e : G)⁆ ∈ E :=
      hKE (Subgroup.commutator_mem_commutator htT e.2)
    refine Subgroup.mem_map.mpr ⟨⟨⁅(t : G), (e : G)⁆, hmemE⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.commutator_mem_commutator htT e.2)
    · rw [sectionPiHom_commutator (S := S) hAX hKE t htT e, he, hta]
  rw [Subgroup.commutator_comm E T]
  exact le_antisymm hle hge

private theorem z_le_relCent {G : Type} [Group G] {E Z T : Subgroup G}
    (hZE : Z ≤ E) (hEZ : E ≤ Subgroup.normalizer (Z : Set G))
    (hTZ : T ≤ Subgroup.normalizer (Z : Set G)) : Z ≤ relCent E Z T := by
  intro z hz
  rw [mem_relCent hEZ]
  refine ⟨hZE hz, fun t ht => ?_⟩
  have hconj : t * z * t⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hTZ ht) z).mp hz
  rw [commutatorElement_def]
  have hconj' : t * z⁻¹ * t⁻¹ ∈ Z := by
    have := Z.inv_mem hconj
    simpa [mul_assoc] using this
  simpa [mul_assoc] using Z.mul_mem hz hconj'

private theorem relIndex_relCent_eq_natCard_fixed {G : Type} [Group G] {K : Type} [Field K]
    {L E Z T : Subgroup G} {φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K}
    (S : CFSG.RankThree.GF2n.SectionModule L E Z φ)
    (hAX : ∀ a ∈ L, ∀ x ∈ E, a * x * a⁻¹ ∈ E)
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G))
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G)) (hZE : Z ≤ E) (hTle : T ≤ L)
    (hUpper : (T.subgroupOf L).map φ = upperUnipotent K) :
    Z.relIndex (relCent E Z T) = Nat.card ↥(fixedAdd K S.W (upperUnipotent K)) := by
  have hZle : Z ≤ relCent E Z T :=
    z_le_relCent hZE hEZ (hTle.trans hLZ)
  have hrelE : relCent E Z T ≤ E := fun _ h => h.1
  have h := natCard_map_eq_relIndex (S := S) hrelE
  rw [map_relCent_eq_fixed (S := S) hAX hEZ hTle hUpper, natCard_toSubgroup] at h
  exact h.symm

private theorem commutator_sup_eq_relCent {G : Type} [Group G] {K : Type} [Field K]
    {L E Z T : Subgroup G} {φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K}
    (S : CFSG.RankThree.GF2n.SectionModule L E Z φ)
    (hAX : ∀ a ∈ L, ∀ x ∈ E, a * x * a⁻¹ ∈ E)
    (hL : L ≤ Subgroup.normalizer (E : Set G))
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G))
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G)) (hZE : Z ≤ E) (hTle : T ≤ L)
    (hUpper : (T.subgroupOf L).map φ = upperUnipotent K)
    (hcomm_eq : commAdd K S.W (upperUnipotent K) = fixedAdd K S.W (upperUnipotent K)) :
    ⁅E, T⁆ ⊔ Z = relCent E Z T := by
  have hKE : ⁅E, T⁆ ≤ E := by
    rw [Subgroup.commutator_comm E T, Subgroup.commutator_le]
    intro t ht e he
    have hconj : t * e * t⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hL (hTle ht)) e).mp he
    rw [commutatorElement_def]
    exact E.mul_mem hconj (E.inv_mem he)
  have hZle : Z ≤ relCent E Z T :=
    z_le_relCent hZE hEZ (hTle.trans hLZ)
  have hrelE : relCent E Z T ≤ E := fun _ h => h.1
  have hmapComm := map_commutator_eq_comm (S := S) hAX hL hTle hUpper
  have hmapRel := map_relCent_eq_fixed (S := S) hAX hEZ hTle hUpper
  have himg : ((⁅E, T⁆).subgroupOf E).map (sectionPiHom S) =
      ((relCent E Z T).subgroupOf E).map (sectionPiHom S) := by
    rw [hmapComm, hmapRel, hcomm_eq]
  have hpre := congrArg (Subgroup.comap (sectionPiHom S)) himg
  rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, sectionPiHom_ker] at hpre
  rw [← Subgroup.subgroupOf_sup hKE hZE,
    ← Subgroup.subgroupOf_sup hrelE hZE, sup_eq_left.mpr hZle] at hpre
  have h := Subgroup.subgroupOf_inj.mp hpre
  rw [inf_eq_left.mpr (sup_le hKE hZE), inf_eq_left.mpr hrelE] at h
  exact h

private theorem section_generated_of_fixed {G : Type} [Group G] {K : Type} [Field K]
    {L E Z T : Subgroup G} {φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K}
    (S : CFSG.RankThree.GF2n.SectionModule L E Z φ)
    (hAX : ∀ a ∈ L, ∀ x ∈ E, a * x * a⁻¹ ∈ E)
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G)) (hZE : Z ≤ E)
    (hL : L ≤ Subgroup.normalizer (E : Set G))
    (hUpper : (T.subgroupOf L).map φ = upperUnipotent K)
    (hgen : ∀ Y : Subgroup G, Z ≤ Y → Y ≤ E →
      L ≤ Subgroup.normalizer (Y : Set G) → relCent E Z T ≤ Y → Y = E) :
    ∀ U : AddSubgroup S.W,
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ U, g • v ∈ U) →
      (∀ v : S.W, (∀ a ∈ upperUnipotent K, a • v = v) → v ∈ U) → U = ⊤ := by
  intro U hU hfixU
  let Y : Subgroup G :=
    { carrier := {y | ∃ e : ↥E, (e : G) = y ∧ S.π e ∈ U}
      one_mem' := ⟨1, rfl, by rw [S.map_one]; exact U.zero_mem⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨e₁, rfl, hπ₁⟩ ⟨e₂, rfl, hπ₂⟩
        exact ⟨e₁ * e₂, rfl, by rw [S.map_mul]; exact U.add_mem hπ₁ hπ₂⟩
      inv_mem' := by
        rintro y ⟨e, rfl, hπ⟩
        exact ⟨e⁻¹, rfl, by rw [S.map_inv]; exact U.neg_mem hπ⟩ }
  have hZY : Z ≤ Y := by
    intro z hz
    exact ⟨⟨z, hZE hz⟩, rfl, by
      rw [(S.eq_zero_iff _).mpr hz]
      exact U.zero_mem⟩
  have hYE : Y ≤ E := by
    rintro y ⟨e, rfl, -⟩
    exact e.2
  have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨e, rfl, hπ⟩
      have hconjE : (l : G) * (e : G) * (l : G)⁻¹ ∈ E :=
        (Subgroup.mem_normalizer_iff.mp (hL hl) (e : G)).mp e.2
      refine ⟨⟨(l : G) * (e : G) * (l : G)⁻¹, hconjE⟩, rfl, ?_⟩
      rw [← S.smul_eq ⟨l, hl⟩ e ⟨_, hconjE⟩ rfl]
      exact hU (φ ⟨l, hl⟩) _ hπ
    · rintro ⟨e, he, hπ⟩
      have hconjE : (l : G)⁻¹ * (e : G) * (l : G) ∈ E := by
        have h := (Subgroup.mem_normalizer_iff.mp
          (hL (L.inv_mem hl)) (e : G)).mp e.2
        simpa using h
      refine ⟨⟨(l : G)⁻¹ * (e : G) * (l : G), hconjE⟩, ?_, ?_⟩
      · change (l : G)⁻¹ * (e : G) * (l : G) = y
        rw [he]
        group
      · rw [← S.smul_eq ⟨l⁻¹, L.inv_mem hl⟩ e ⟨_, hconjE⟩ (by group)]
        exact hU (φ ⟨l⁻¹, L.inv_mem hl⟩) _ hπ
  have hrelY : relCent E Z T ≤ Y := by
    intro y hy
    rw [mem_relCent hEZ] at hy
    obtain ⟨hyE, hycomm⟩ := hy
    have hfixY : ∀ a ∈ upperUnipotent K, a • S.π ⟨y, hyE⟩ = S.π ⟨y, hyE⟩ := by
      intro a ha
      rw [← hUpper] at ha
      obtain ⟨t, ht, hta⟩ := Subgroup.mem_map.mp ha
      rw [← hta]
      exact (S.smul_eq_iff_commutator_mem hAX t ⟨y, hyE⟩).mpr (by
        have h1 : ⁅y, (t : G)⁆ ∈ Z := hycomm (t : G) (Subgroup.mem_subgroupOf.mp ht)
        simpa [commutatorElement_inv] using Z.inv_mem h1)
    exact ⟨⟨y, hyE⟩, rfl, hfixU _ hfixY⟩
  have hY : Y = E := hgen Y hZY hYE hLY hrelY
  rw [eq_top_iff]
  intro v _
  obtain ⟨e, rfl⟩ := S.surjective v
  have heY : (e : G) ∈ Y := by rw [hY]; exact e.2
  obtain ⟨e', he', hπ⟩ := heY
  have heq : e' = e := Subtype.ext he'
  rwa [heq] at hπ

private theorem exists_quadratic_section {G : Type} [Group G] {L E Z T : Subgroup G}
    [Finite ↥L] [Finite ↥E] {n : ℕ} (hq : IsL2Quot n (oTwoQuot ↥L))
    (hsec : IsElemSec Z E)
    (hL : L ≤ Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hcore : ∀ x ∈ pCoreOf 2 L, ∀ e ∈ E, ⁅x, e⁆ ∈ Z)
    (hcent : relCent E Z L = Z) (hT : IsSylowTwoOf T L)
    (hquad : ∀ t ∈ T, ∀ t' ∈ T, ∀ e ∈ E, ⁅t, ⁅t', e⁆⁆ ∈ Z)
    (hgen : ∀ Y : Subgroup G, Z ≤ Y → Y ≤ E →
      L ≤ Subgroup.normalizer (Y : Set G) → relCent E Z T ≤ Y → Y = E) :
    ∃ (α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (S : CFSG.RankThree.GF2n.SectionModule L E Z α),
      Function.Surjective α ∧ α.ker = (pCoreOf 2 L).subgroupOf L ∧
      (T.subgroupOf L).map α = upperUnipotent (GaloisField 2 n) ∧
      Finite S.W ∧
      (∀ v : S.W, (∀ x : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        x • v = v) → v = 0) ∧
      (∀ a ∈ upperUnipotent (GaloisField 2 n),
        ∀ a' ∈ upperUnipotent (GaloisField 2 n), ∀ v : S.W,
          a' • (a • v - v) = a • v - v) ∧
      (∀ U : AddSubgroup S.W,
        (∀ g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
          ∀ v ∈ U, g • v ∈ U) →
        (∀ v : S.W, (∀ a ∈ upperUnipotent (GaloisField 2 n), a • v = v) → v ∈ U) →
        U = ⊤) := by
  classical
  let K := GaloisField 2 n
  obtain ⟨α, hαsurj, hαker, hUpper⟩ :=
    CFSG.GroupTheory.exists_SL2_hom_map_sylowTwo_eq_upperUnipotent hq hT
  have hEZ : E ≤ Subgroup.normalizer (Z : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((Subgroup.commutator_mono le_rfl hsec.1).trans hsec.2.1)
  have hAX : ∀ a ∈ L, ∀ x ∈ E, a * x * a⁻¹ ∈ E :=
    fun a ha x hx => (Subgroup.mem_normalizer_iff.mp ((hL.trans inf_le_left) ha) x).mp hx
  have hAC : ∀ a ∈ L, ∀ x ∈ Z, a * x * a⁻¹ ∈ Z :=
    fun a ha x hx => (Subgroup.mem_normalizer_iff.mp ((hL.trans inf_le_right) ha) x).mp hx
  obtain ⟨S⟩ :=
    CFSG.RankThree.GF2n.exists_sectionModule α hαsurj hsec.1
      (fun x hx y hy => (Subgroup.commutator_le.mp hsec.2.1) x hx y hy) hAX hAC
      (fun a ha x hx => by
        have hmem : a ∈ α.ker := ha
        rw [hαker] at hmem
        exact hcore (a : G) (Subgroup.mem_subgroupOf.mp hmem) x hx)
  have hfinW : Finite S.W := Finite.of_surjective S.π S.surjective
  have hfix : ∀ v : S.W, (∀ x : Matrix.SpecialLinearGroup (Fin 2) K, x • v = v) → v = 0 := by
    intro v hv
    obtain ⟨x, rfl⟩ := S.surjective v
    have hcomm : ∀ l : ↥L, ⁅(x : G), (l : G)⁆ ∈ Z := by
      intro l
      have h1 : ⁅(l : G), (x : G)⁆ ∈ Z :=
        (S.smul_eq_iff_commutator_mem hAX l x).mp (hv (α l))
      simpa [commutatorElement_inv] using Z.inv_mem h1
    have hxZ : (x : G) ∈ Z := by
      rw [← hcent, mem_relCent hEZ]
      exact ⟨x.2, fun l hl => hcomm ⟨l, hl⟩⟩
    rw [← (S.eq_zero_iff x).mpr hxZ]
  have hquadA : ∀ a ∈ upperUnipotent K, ∀ a' ∈ upperUnipotent K, ∀ v : S.W,
      a' • (a • v - v) = a • v - v := by
    have h := S.quadratic (A := L) (C := Z) (X := E) (Q := T) hAX hT.1
      (fun q hq q' hq' x hx => hquad q' hq' q hq x hx)
    rwa [hUpper] at h
  have hgenW : ∀ U : AddSubgroup S.W,
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ U, g • v ∈ U) →
      (∀ v : S.W, (∀ a ∈ upperUnipotent K, a • v = v) → v ∈ U) → U = ⊤ :=
    section_generated_of_fixed (S := S) hAX hEZ hsec.1 (hL.trans inf_le_left) hUpper hgen
  exact ⟨α, S, hαsurj, hαker, hUpper, hfinW, hfix, hquadA, hgenW⟩

private theorem natural_fixed_eq_zero {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) V]
    (g : Matrix.SpecialLinearGroup (Fin 2) K) (hg : g ≠ 1) (hodd : Odd (orderOf g))
    {θ : (Fin 2 → K) →+ V} (hinj : Function.Injective θ)
    (hθ : ∀ (x : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
      θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v)
    {v : V} (hv : v ∈ θ.range) (hfix : g • v = v) : v = 0 := by
  obtain ⟨u, rfl⟩ := hv
  have hmat : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ u = u := by
    apply hinj
    rw [hθ, hfix]
  have hu0 : u = 0 := by
    by_contra hu0
    exact hg (SL2Nat.eq_one_of_odd_order_of_fixed hu0 hodd hmat)
  rw [hu0, map_zero]

theorem exists_relIndex_eq_two_pow_mul_of_quadratic {G : Type} [Group G]
    {L E Z T : Subgroup G} [Finite ↥L] [Finite ↥E] {n : ℕ} (hn : 1 ≤ n)
    (hq : IsL2Quot n (oTwoQuot ↥L)) (hsec : IsElemSec Z E)
    (hL : L ≤ Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hcore : ∀ x ∈ pCoreOf 2 L, ∀ e ∈ E, ⁅x, e⁆ ∈ Z)
    (hcent : relCent E Z L = Z) (hT : IsSylowTwoOf T L)
    (hquad : ∀ t ∈ T, ∀ t' ∈ T, ∀ e ∈ E, ⁅t, ⁅t', e⁆⁆ ∈ Z)
    (hgen : ∀ Y : Subgroup G, Z ≤ Y → Y ≤ E →
      L ≤ Subgroup.normalizer (Y : Set G) → relCent E Z T ≤ Y → Y = E) :
    ∃ k : ℕ, Z.relIndex E = 2 ^ (2 * n * k) ∧
      Z.relIndex (relCent E Z T) = 2 ^ (n * k) ∧ ⁅E, T⁆ ⊔ Z = relCent E Z T := by
  classical
  obtain ⟨α, S, hαsurj, hαker, hUpper, hfinW, hfix, hquadA, hgenW⟩ :=
    exists_quadratic_section hq hsec hL hcore hcent hT hquad hgen
  haveI : Finite S.W := hfinW
  let K := GaloisField 2 n
  let A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := upperUnipotent K
  have hA2 : IsPGroup 2 A :=
    CFSG.Timmesfeld.Bridge.RootClosure.isPGroup_upperUnipotent (by omega : n ≠ 0)
  have hAcard : Nat.card A = Nat.card K :=
    CFSG.Timmesfeld.RankOne.card_upperUnipotent K
  have hn1 : 1 ≤ n := hn
  have hn0 : n ≠ 0 := by omega
  have hcardK : Nat.card K = 2 ^ n := by
    dsimp [K]
    exact GaloisField.card 2 n hn0
  have hAX : ∀ a ∈ L, ∀ x ∈ E, a * x * a⁻¹ ∈ E :=
    fun a ha x hx => (Subgroup.mem_normalizer_iff.mp ((hL.trans inf_le_left) ha) x).mp hx
  have hEZ : E ≤ Subgroup.normalizer (Z : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((Subgroup.commutator_mono le_rfl hsec.1).trans hsec.2.1)
  obtain ⟨s, hs_ind, hs_top, hs_nat⟩ :=
    CFSG.RankThree.GF2n.exists_supIndep_natural (K := K) (V := S.W) hfix hquadA
      (L := fixedAdd K S.W A) (fun w hw => hw) hgenW
  have hnatural : ∀ W ∈ s, ∃ θ : (Fin 2 → K) →+ S.W, Function.Injective θ ∧
      θ.range = W ∧ ∀ (x : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
        θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v := by
    intro W hWs
    obtain ⟨-, -, -, θ, hinj, hrange, hθ⟩ := hs_nat W hWs
    exact ⟨θ, hinj, hrange, hθ⟩
  have hcardV := card_sup_natural (K := K) (V := S.W) s hs_ind hs_top hnatural
  have hmapE : (E.subgroupOf E).map (sectionPiHom S) = ⊤ := by
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (sectionPiHom_surjective S)]
  have hcardE := natCard_map_eq_relIndex (S := S) (F := E) le_rfl
  rw [hmapE, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd] at hcardE
  have hcardIdx : Z.relIndex E = (Nat.card K ^ 2) ^ s.card := by
    rw [← hcardE, hcardV]
  have hEidx : Z.relIndex E = 2 ^ (2 * n * s.card) := by
    rw [hcardIdx, hcardK]
    calc ((2 ^ n) ^ 2) ^ s.card = 2 ^ (n * 2 * s.card) := by rw [pow_mul, pow_mul]
      _ = 2 ^ (2 * n * s.card) := by congr 1; ring
  have hcardFix := card_fixed_sup_natural (K := K) (V := S.W) (A := A) hA2 hAcard
    s hs_ind hs_top hnatural
  have hrelIdx := relIndex_relCent_eq_natCard_fixed (S := S) hAX
    (hL.trans inf_le_right) hEZ hsec.1 hT.1 hUpper
  have hrelIdx' : Z.relIndex (relCent E Z T) = 2 ^ (n * s.card) := by
    rw [hrelIdx, hcardFix, hcardK, pow_mul]
  have hcomm_eq := commAdd_eq_fixedAdd_of_natural (K := K) (V := S.W) (A := A)
    hA2 hAcard hquadA s hs_ind hs_top hnatural
  have hcommRel := commutator_sup_eq_relCent (S := S) hAX (hL.trans inf_le_left)
    (hL.trans inf_le_right) hEZ hsec.1 hT.1 hUpper hcomm_eq
  exact ⟨s.card, hEidx, hrelIdx', hcommRel⟩

theorem fixFree_of_quadratic {G : Type} [Group G]
    {L E Z T : Subgroup G} [Finite ↥L] [Finite ↥E] {n : ℕ}
    (hq : IsL2Quot n (oTwoQuot ↥L)) (hsec : IsElemSec Z E)
    (hL : L ≤ Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hcore : ∀ x ∈ pCoreOf 2 L, ∀ e ∈ E, ⁅x, e⁆ ∈ Z)
    (hcent : relCent E Z L = Z) (hT : IsSylowTwoOf T L)
    (hquad : ∀ t ∈ T, ∀ t' ∈ T, ∀ e ∈ E, ⁅t, ⁅t', e⁆⁆ ∈ Z)
    (hgen : ∀ Y : Subgroup G, Z ≤ Y → Y ≤ E →
      L ≤ Subgroup.normalizer (Y : Set G) → relCent E Z T ≤ Y → Y = E) :
    ∀ l ∈ L, Odd (orderOf l) → l ≠ 1 → ∀ e ∈ E, ⁅e, l⁆ ∈ Z → e ∈ Z := by
  classical
  obtain ⟨α, S, hαsurj, hαker, hUpper, hfinW, hfix, hquadA, hgenW⟩ :=
    exists_quadratic_section hq hsec hL hcore hcent hT hquad hgen
  haveI : Finite S.W := hfinW
  let K := GaloisField 2 n
  let A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := upperUnipotent K
  have hAX : ∀ a ∈ L, ∀ x ∈ E, a * x * a⁻¹ ∈ E :=
    fun a ha x hx => (Subgroup.mem_normalizer_iff.mp ((hL.trans inf_le_left) ha) x).mp hx
  obtain ⟨s, hs_ind, hs_top, hs_nat⟩ :=
    CFSG.RankThree.GF2n.exists_supIndep_natural (K := K) (V := S.W) hfix hquadA
      (L := fixedAdd K S.W A) (fun w hw => hw) hgenW
  intro l hl hodd hl1 e heE hcomm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcoreP : IsPGroup 2 (pCoreOf 2 L) := by
    change IsPGroup 2 ((pCore 2 ↥L).map L.subtype)
    exact (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2).map L.subtype
  have hαlne : α ⟨l, hl⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨l, hl⟩ : ↥L) ∈ α.ker := h1
    rw [hαker] at hmem
    have hlO : l ∈ pCoreOf 2 L := Subgroup.mem_subgroupOf.mp hmem
    have hone : (⟨l, hlO⟩ : ↥(pCoreOf 2 L)) = 1 := by
      refine CFSG.GroupTheory.SuzukiTwoGroup.eq_one_of_pow_eq_one_of_odd hcoreP hodd ?_
      exact Subtype.ext (by simp [pow_orderOf_eq_one])
    exact hl1 (congrArg Subtype.val hone)
  have hαlodd : Odd (orderOf (α ⟨l, hl⟩)) := by
    have hordl : orderOf (⟨l, hl⟩ : ↥L) = orderOf l := Subgroup.orderOf_mk l hl
    exact Odd.of_dvd_nat (hordl ▸ hodd) (orderOf_map_dvd α ⟨l, hl⟩)
  let gK : S.W →+ S.W :=
    (DistribMulAction.toAddMonoidEnd (Matrix.SpecialLinearGroup (Fin 2) K) S.W) (α ⟨l, hl⟩)
  have hgK : ∀ w, gK w = α ⟨l, hl⟩ • w := fun w => rfl
  have hinv : ∀ W ∈ s, ∀ v ∈ W, gK v ∈ W := by
    intro W hWs v hv
    rw [hgK]
    exact (hs_nat W hWs).1 (α ⟨l, hl⟩) v hv
  have hfixW : ∀ W ∈ s, ∀ v ∈ W, gK v = v → v = 0 := by
    intro W hWs v hv hgv
    obtain ⟨-, -, -, θ, hinj, hrange, hθ⟩ := hs_nat W hWs
    exact natural_fixed_eq_zero (α ⟨l, hl⟩) hαlne hαlodd hinj hθ (hrange ▸ hv)
      (by rwa [hgK] at hgv)
  have hfixe : gK (S.π ⟨e, heE⟩) = S.π ⟨e, heE⟩ := by
    rw [hgK]
    exact (S.smul_eq_iff_commutator_mem hAX ⟨l, hl⟩ ⟨e, heE⟩).mpr (by
      show ⁅(l : G), (e : G)⁆ ∈ Z
      rw [← commutatorElement_inv]
      exact Z.inv_mem hcomm)
  have hπe : S.π ⟨e, heE⟩ = 0 :=
    CFSG.GroupTheory.eq_zero_of_mem_finset_sup_of_fixedPointFree gK hs_ind hinv hfixW
      (w := S.π ⟨e, heE⟩) (by rw [hs_top]; exact AddSubgroup.mem_top _) hfixe
  exact (S.eq_zero_iff ⟨e, heE⟩).mp hπe

end CFSG.Quasithin.St84
