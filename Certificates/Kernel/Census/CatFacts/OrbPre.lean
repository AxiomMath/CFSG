module

public import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
public import CFSG.GH74.KGroups.PermCheck
public import Mathlib.GroupTheory.Perm.DomMulAct

public section

namespace CertificateChecks.KernelCatFacts

open CFSG.Certificates CFSG.Certificates.Kernel.PkEnum CFSG.GH74.KGroups

@[expose] def labOK {n : Nat} (Q : RawSchreierDatum n) (lab : Fin n → Nat) : Bool :=
  Q.original.toList.all fun g => (List.finRange n).all fun i => lab (g i) == lab i

@[expose] def preT {n : Nat} (lab : Fin n → Nat) (gens : List (Equiv.Perm (Fin n)))
    (x : Equiv.Perm (Fin n)) : Bool :=
  gens.all fun q => (List.finRange n).all fun j => lab (x (q j)) == lab (x j)

theorem lab_of_mem {n : Nat} {Q : RawSchreierDatum n} {lab : Fin n → Nat}
    (hl : labOK Q lab = true) {σ : Equiv.Perm (Fin n)} (h : σ ∈ Q.originalSubgroup) :
    ∀ i, lab (σ i) = lab i := by
  induction h using Subgroup.closure_induction with
  | mem g hg =>
    intro i
    have h1 := List.all_eq_true.1 hl g hg
    exact beq_iff_eq.1 (List.all_eq_true.1 h1 i (List.mem_finRange i))
  | one => intro i; rfl
  | mul a b _ _ ha hb => intro i; rw [Equiv.Perm.mul_apply, ha, hb]
  | inv a _ ha =>
    intro i
    have h1 := ha (a⁻¹ i)
    have h2 : a (a⁻¹ i) = i := Equiv.apply_symm_apply a i
    rw [h2] at h1
    exact h1.symm

theorem lab_of_siftP {n : Nat} {Q : RawSchreierDatum n} (hQ : ValidSchreier Q)
    {lab : Fin n → Nat} (hl : labOK Q lab = true) {σ : Equiv.Perm (Fin n)}
    (h : siftP Q σ 0 = true) : ∀ i, lab (σ i) = lab i :=
  lab_of_mem hl ((mem_iff_sift Q hQ σ).2 (by rw [sift_eq_siftP]; exact h))

theorem all_siftP_false {n : Nat} {Q : RawSchreierDatum n} (hQ : ValidSchreier Q)
    {lab : Fin n → Nat} (hl : labOK Q lab = true) {gens : List (Equiv.Perm (Fin n))}
    {x : Equiv.Perm (Fin n)} (hp : preT lab gens x = false) :
    (gens.all fun q => siftP Q (x * q * x⁻¹) 0) = false := by
  unfold preT at hp
  rw [List.all_eq_false] at hp ⊢
  obtain ⟨q, hq, hq2⟩ := hp
  refine ⟨q, hq, fun hs => hq2 ?_⟩
  rw [List.all_eq_true]
  intro j _
  have h1 := lab_of_siftP hQ hl hs (x j)
  have h2 : x⁻¹ (x j) = j := Equiv.symm_apply_apply x j
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h2] at h1
  exact beq_iff_eq.2 h1

theorem preT_apply {n : Nat} {lab : Fin n → Nat} {gens : List (Equiv.Perm (Fin n))}
    {x : Equiv.Perm (Fin n)} (h : preT lab gens x = true) {q : Equiv.Perm (Fin n)} (hq : q ∈ gens)
    (j : Fin n) : lab (x (q j)) = lab (x j) :=
  beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 h q hq) j (List.mem_finRange j))

theorem mem_of_stab {n k : Nat} {W : RawSchreierDatum n} (hW : ValidSchreier W)
    (f : Fin n → Fin k)
    (hc : ((elemsV W).filter fun y => (List.finRange n).all fun i => f (y i) == f i).length =
      ∏ i, (Fintype.card {a // f a = i}).factorial)
    {y : Equiv.Perm (Fin n)} (hy : ∀ i, f (y i) = f i) : y ∈ W.originalSubgroup := by
  classical
  rw [← mem_elemsT W hW]
  rw [← elemsT_eq_elemsV] at hc
  have hp : ∀ g : Equiv.Perm (Fin n),
      ((List.finRange n).all fun i => f (g i) == f i) = true ↔ f ∘ g = f := by
    intro g
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq, funext_iff,
      Function.comp_apply]
  have hnd := (nodup_elemsT W hW).filter fun y => (List.finRange n).all fun i => f (y i) == f i
  have hsub : ((elemsT W).filter fun y => (List.finRange n).all fun i => f (y i) == f i).toFinset ⊆
      Finset.univ.filter (fun g : Equiv.Perm (Fin n) => f ∘ g = f) := by
    intro g hg
    rw [List.mem_toFinset, List.mem_filter] at hg
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hp g).1 hg.2⟩
  have hst := DomMulAct.stabilizer_card f
  rw [Fintype.card_subtype] at hst
  have hcard : (Finset.univ.filter (fun g : Equiv.Perm (Fin n) => f ∘ g = f)).card ≤
      ((elemsT W).filter fun y => (List.finRange n).all fun i => f (y i) == f i).toFinset.card := by
    rw [List.toFinset_card_of_nodup hnd, hc, ← hst]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hy' : y ∈ Finset.univ.filter (fun g : Equiv.Perm (Fin n) => f ∘ g = f) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, funext hy⟩
  rw [← heq, List.mem_toFinset] at hy'
  exact (List.mem_filter.1 hy').1

theorem closure_all {n : Nat} (Q : RawSchreierDatum n) {P : Equiv.Perm (Fin n) → Prop} (h1 : P 1)
    (hmul : ∀ a b, P a → P b → P (a * b)) (hg : ∀ g ∈ Q.original.toList, P g ∧ P g⁻¹)
    {x : Equiv.Perm (Fin n)} (hx : x ∈ Q.originalSubgroup) : P x :=
  Subgroup.closure_induction'' (p := fun x _ => P x) (fun g hg' => (hg g hg').1)
    (fun g hg' => (hg g hg').2) h1 (fun a b _ _ ha hb => hmul a b ha hb) hx

theorem length_filter_of {α : Type*} {l l' : List α} {p : α → Bool} (hl : l.Nodup)
    (hall : ∀ x, x ∈ l) (hl' : l'.Nodup) (h : ∀ x, p x = true ↔ x ∈ l') :
    (l.filter p).length = l'.length :=
  ((List.perm_ext_iff_of_nodup (hl.filter p) hl').2 fun x => by
    rw [List.mem_filter, ← h]
    exact ⟨fun h1 => h1.2, fun h1 => ⟨hall x, h1⟩⟩).length_eq

end CertificateChecks.KernelCatFacts

end
