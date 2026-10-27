module

public import Certificates.Data.TcRes
public import CFSG.Blueprint.Chevalley
public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDefs

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley

theorem tc_foldl_range_add (f : ℕ → ℤ) (n : ℕ) :
    (List.range n).foldl (fun s j => s + f j) 0 = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp

end CFSG.StandardType.TableCRes

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley

theorem tcrBasisV_ofFn (τ : Tag) (j : Fin τ.rank) :
    tcrBasisV τ.rank j.val = List.ofFn (Pi.single j (1 : ℤ) : Fin τ.rank → ℤ) := by
  apply List.ext_getElem
  · simp [tcrBasisV]
  · intro m h1 h2
    simp [tcrBasisV, Pi.single_apply, Fin.ext_iff]

theorem tcr_getD_ofFn {n : ℕ} (γ : Fin n → ℤ) (j : Fin n) : (List.ofFn γ).getD j.val 0 = γ j := by
  simp [List.getD_eq_getElem?_getD]

section Good

variable {τ : Tag} {S : TcrSys}

theorem TcrGood.rv_spec (hG : TcrGood τ S) {i : ℕ} (hi : i < S.tcrN) :
    IsRoot τ (tcrRv S τ i) ∧ S.roots[i]! = List.ofFn (tcrRv S τ i) := by
  have hmem : S.roots[i]! ∈ S.roots.toList := by
    have : i < S.roots.size := hi
    rw [getElem!_pos S.roots i this]
    exact Array.getElem_mem_toList _
  obtain ⟨γ, hγ, hr⟩ := hG.gen _ hmem
  have : tcrRv S τ i = γ := by
    funext j
    simp only [tcrRv, hr, tcr_getD_ofFn]
  exact ⟨this ▸ hγ, by rw [this]; exact hr⟩

theorem TcrGood.rv_inj (hG : TcrGood τ S) {i j : ℕ} (hi : i < S.tcrN) (hj : j < S.tcrN)
    (h : tcrRv S τ i = tcrRv S τ j) : i = j := by
  rcases hG.spec.f3 i hi j hj with h1 | h1
  · exact h1
  · exfalso
    apply h1
    rw [(hG.rv_spec hi).2, (hG.rv_spec hj).2, h]

end Good

theorem tcrFormL_ofFn {τ : Tag} {cartanArr : Array Int}
    (hc : ∀ i j : Fin τ.rank, cartanArr[τ.rank * i.val + j.val]! = τ.cartan i j)
    (hsym : ∀ i j : Fin τ.rank, τ.symmetrizedCartan i j = τ.cartan i j)
    (u v : Fin τ.rank → ℤ) :
    tcrFormL cartanArr τ.rank (List.ofFn u) (List.ofFn v) =
      iform u v := by
  unfold tcrFormL
  simp only [tc_foldl_range_add]
  rw [Finset.sum_range]
  unfold iform
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range, tcr_getD_ofFn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tcr_getD_ofFn, hc, hsym]
  ring

section Tables

variable {τ : Tag} {S : TcrSys}

theorem TcrGood.ip_eq (hG : TcrGood τ S) {i j : ℕ} (hi : i < S.tcrN) (hj : j < S.tcrN) :
    (S.ip[i]!)[j]! = iform (tcrRv S τ i) (tcrRv S τ j) := by
  rw [(hG.spec.f11 i hi).2 j hj]
  have h1 := (hG.rv_spec hi).2
  have h2 := (hG.rv_spec hj).2
  rw [h1, h2, hG.rank]
  exact tcrFormL_ofFn hG.cartan hG.sym _ _

theorem tcr_vsubmul_getD {n : ℕ} (a b : Fin n → ℤ) (c : ℤ) (j : Fin n) :
    (tcrVsubmul (List.ofFn a) c (List.ofFn b)).getD j.val 0 = a j - c * b j := by
  simp [tcrVsubmul, List.getD_eq_getElem?_getD]

theorem TcrGood.refl_spec (hG : TcrGood τ S) {g v : ℕ} (hg : g < S.tcrN) (hv : v < S.tcrN) :
    (S.refl[g]!)[v]! < S.tcrN ∧
      tcrRv S τ ((S.refl[g]!)[v]!) =
        tcrRv S τ v - iform (tcrRv S τ v) (tcrRv S τ g) • tcrRv S τ g := by
  obtain ⟨h1, h2⟩ := (hG.spec.f13 g hg).2 v hv
  refine ⟨h1, ?_⟩
  funext j
  have hip := hG.ip_eq hv hg
  have hvr := (hG.rv_spec hv).2
  have hgr := (hG.rv_spec hg).2
  have e1 : tcrRv S τ ((S.refl[g]!)[v]!) j =
      (tcrVsubmul S.roots[v]! (S.ip[v]!)[g]! S.roots[g]!).getD j.val 0 := by
    simp only [tcrRv, h2]
  rw [e1, hip, hvr, hgr, tcr_vsubmul_getD]
  simp

theorem TcrGood.basis_spec (hG : TcrGood τ S) (j : Fin τ.rank) :
    S.basis[j.val]! = j.val ∧ tcrRv S τ j.val = Pi.single j 1 := by
  have hj : j.val < S.rank := by rw [hG.rank]; exact j.2
  obtain ⟨h1, h2⟩ := hG.spec.f14 j.val hj
  refine ⟨h1, ?_⟩
  funext k
  have : tcrRv S τ j.val k = (S.roots[j.val]!).getD k.val 0 := rfl
  rw [this, h2, hG.rank, tcrBasisV_ofFn, tcr_getD_ofFn]

theorem TcrGood.tcrPos_iff (hG : TcrGood τ S) {i : ℕ} (hi : i < S.tcrN) :
    S.posFlag[i]! = true ↔ ∀ j, 0 ≤ tcrRv S τ i j := by
  rw [hG.spec.f15 i hi, (hG.rv_spec hi).2]
  simp [List.all_eq_true, List.mem_ofFn]

end Tables

section Perm

variable {τ : Tag} {S : TcrSys}

theorem TcrGood.iform_self
    (hG : TcrGood τ S) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    iform β β = 2 := by
  obtain ⟨i, hi⟩ := iform_self_of_isRoot hβ
  rw [hi, hG.sym1]
  norm_num

theorem TcrGood.refl_rootReflection
    (hG : TcrGood τ S) {g v : ℕ} (hg : g < S.tcrN) (hv : v < S.tcrN) :
    tcrRv S τ ((S.refl[g]!)[v]!) = rootReflection (tcrRv S τ g) • tcrRv S τ v := by
  obtain ⟨-, h⟩ := hG.refl_spec hg hv
  rw [h, rootReflection_smul (hG.rv_spec hg).1]
  have hc : corootPair (tcrRv S τ g) (tcrRv S τ v) = iform (tcrRv S τ v) (tcrRv S τ g) := by
    have h1 := corootPair_mul (hG.rv_spec hg).1 (tcrRv S τ v)
    rw [hG.iform_self (hG.rv_spec hg).1] at h1
    rw [iform_comm]
    linarith
  rw [hc]

theorem TcrGood.tcrRank_le (hG : TcrGood τ S) {k : ℕ} (hk : k < S.rank) : k < S.tcrN := by
  by_contra h
  have h1 := (hG.spec.f14 k hk).2
  have h2 : (S.roots[k]!).length = S.rank := by rw [h1]; simp [tcrBasisV]
  rw [getElem!_neg S.roots k h] at h2
  have h3 : (default : List ℤ) = [] := rfl
  rw [h3] at h2
  simp at h2
  omega

theorem tc_foldl_range_succ {α : Type*} (f : α → ℕ → α) (a : α) (m : ℕ) :
    (List.range (m + 1)).foldl f a = f ((List.range m).foldl f a) m := by
  rw [List.range_succ, List.foldl_append]
  rfl

end Perm

end CFSG.StandardType.TableCRes

end
