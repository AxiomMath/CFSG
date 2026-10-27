
module

public import CFSG.Sporadic.Th.Max3.RelationsBase
import all CFSG.Sporadic.Th.Max3.RelationsBase

public import CFSG.Sporadic.Th.Max3.Data
public meta import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native

@[expose] noncomputable def nfAt (k : Fin 512) : J :=
  nfN (k.val % 2) fun i => k.val / 2 ^ (i.val + 1) % 2

private theorem nf_eq_nfAt (s : ZMod 2) (v : Fin 8 → ZMod 2) :
    nf s v = nfAt ⟨nfIdx s v, nfIdx_lt s v⟩ := by
  rw [nf_eq_nfN, nfAt]
  congr 1
  · exact (nfIdx_mod s v).symm
  · funext i
    exact (nfIdx_div s v i).symm

theorem x_mem_M :
    x ∈ M := Subgroup.subset_closure (Set.mem_insert _ _)

theorem y_mem_M :
    y ∈ M := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem wordProd_mem_M (w : List Gen) : wordProd w ∈ M := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hg
  cases l
  · exact x_mem_M
  · exact y_mem_M

theorem z_mem_M : z ∈ M := Subgroup.pow_mem _ (wordProd_mem_M _) _

theorem q_mem_M
    (i : Fin 8) : q i ∈ M := Subgroup.pow_mem _ (wordProd_mem_M _) _

theorem z_mem_Q :
    z ∈ Q := Subgroup.subset_closure (Set.mem_insert _ _)

theorem q_mem_Q (i : Fin 8) : q i ∈ Q :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨i, rfl⟩)

theorem nf_mem_Q (s : ZMod 2) (v : Fin 8 → ZMod 2) : nf s v ∈ Q :=
  Q.mul_mem (Subgroup.pow_mem _ z_mem_Q _)
    (Subgroup.list_prod_mem _ fun g hg => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
      exact Subgroup.pow_mem _ (q_mem_Q i) _)

theorem Q_le_M : Q ≤ M := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | ⟨i, rfl⟩)
  · exact z_mem_M
  · exact q_mem_M i

private theorem conj_mem_Q
    {t : J} (hz : t * z * t⁻¹ ∈ Q) (hq : ∀ i, t * q i * t⁻¹ ∈ Q)
    {g : J} (hg : g ∈ Q) : t * g * t⁻¹ ∈ Q := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | ⟨i, rfl⟩
    · exact hz
    · exact hq i
  | one => simp
  | mul g h _ _ hg hh =>
    have e : t * (g * h) * t⁻¹ = (t * g * t⁻¹) * (t * h * t⁻¹) := by group
    rw [e]
    exact Q.mul_mem hg hh
  | inv g _ hg =>
    have e : t * g⁻¹ * t⁻¹ = (t * g * t⁻¹)⁻¹ := by group
    rw [e]
    exact Q.inv_mem hg

private theorem mem_normalizer_of_pow
    {t : J} {n : ℕ} (hn : t ^ (n + 1) = 1)
    (h : ∀ g ∈ Q, t * g * t⁻¹ ∈ Q) : t ∈ Subgroup.normalizer (Q : Set J) := by
  have hinv : t⁻¹ = t ^ n := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hn)
  have hpow : ∀ m : ℕ, ∀ g ∈ Q, t ^ m * g * (t ^ m)⁻¹ ∈ Q := by
    intro m
    induction m with
    | zero => intro g hg; simpa using hg
    | succ m ih =>
      intro g hg
      have e : t ^ (m + 1) * g * (t ^ (m + 1))⁻¹ = t * (t ^ m * g * (t ^ m)⁻¹) * t⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rw [e]
      exact h _ (ih g hg)
  have htn : (t ^ n)⁻¹ = t := by
    rw [← hinv, inv_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨h g, fun hg => ?_⟩
  have h1 := hpow n _ hg
  have e : t ^ n * (t * g * t⁻¹) * (t ^ n)⁻¹ = g := by
    rw [← hinv, inv_inv]
    group
  rwa [e] at h1

end CFSG.Sporadic.Th.Max3
