module

public import CFSG.LocalAnalysis.StandardType.GGDRootModel
public import CFSG.LieType.Universal.Spin.Roots.TypeD
public import CFSG.LocalAnalysis.StandardType.GGForkIndefLattice

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

private def dro_lift {n : ℕ} (γ : Fin n → ℤ) : ℕ → ℤ :=
  fun j => if h : j < n then γ ⟨j, h⟩ else 0

private theorem dro_lift_fin {n : ℕ} (γ : Fin n → ℤ) :
    (fun i : Fin n => dro_lift γ i) = γ := by
  funext i
  simp only [dro_lift, dif_pos i.isLt]

private theorem dro_ggDeps_toStdD {n : ℕ} (hn : 3 ≤ n) (u : ℕ → ℤ) {k : ℕ} (hk : k < n) :
    ggDeps n u k = toStdD n (fun i : Fin n => u i) ⟨k, hk⟩ := by
  rcases eq_or_ne k 0 with h0 | h0
  · subst h0
    rw [ggDeps, toStdD]
    dsimp only
    split_ifs <;> omega
  · have hkpos : 0 < k := Nat.pos_of_ne_zero h0
    by_cases h3 : k + 3 ≤ n
    · rw [ggDeps, toStdD]
      dsimp only
      split_ifs <;> omega
    · by_cases h2 : k + 2 = n
      · have hk2 : k = n - 2 := by omega
        subst k
        rw [ggDeps, toStdD]
        dsimp only
        have e1 : n - 2 - 1 = n - 3 := by omega
        have e2 : n - 2 + 1 = n - 1 := by omega
        split_ifs <;> first | omega | (rw [e1, e2]; ring)
      · have hk1 : k = n - 1 := by omega
        subst k
        rw [ggDeps, toStdD]
        dsimp only
        have e1 : n - 1 - 1 = n - 2 := by omega
        split_ifs <;> first | omega | (rw [e1]; ring)

private theorem dro_sum_ggSRefl {n : ℕ} (k j : Fin n) (m : Option (Fin n) → ℤ)
    (hm : m none = 0) :
    (∑ o, ggAttachCartan (CartanMatrix.D n) k (some j) o * m o) =
      ∑ i : Fin n, CartanMatrix.D n j i * m (some i) := by
  rw [Fintype.sum_option, ggAttachCartan_some_none, hm, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ggAttachCartan_some_some]

private theorem dro_sRefl_none {n : ℕ} (k j : Fin n) (m : Option (Fin n) → ℤ)
    (hm : m none = 0) :
    ggSRefl (ggAttachCartan (CartanMatrix.D n) k) (some j) m none = 0 := by
  rw [ggSRefl]
  simp [Pi.sub_apply, hm]

private theorem dro_sRefl_some {n : ℕ} (k j : Fin n) (m : Option (Fin n) → ℤ)
    (hm : m none = 0) :
    (fun l : Fin n => ggSRefl (ggAttachCartan (CartanMatrix.D n) k) (some j) m (some l)) =
      reflection (CartanMatrix.D n) j (fun l : Fin n => m (some l)) := by
  funext l
  have hs : (Pi.single (some j) (1 : ℤ) : Option (Fin n) → ℤ) (some l) =
      (Pi.single j (1 : ℤ) : Fin n → ℤ) l := by
    by_cases h : l = j
    · subst h
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne (by simpa using h), Pi.single_eq_of_ne h]
  rw [reflection_apply, ggSRefl, dro_sum_ggSRefl k j m hm]
  simp only [Pi.sub_apply, Pi.smul_apply]
  rw [hs]

private theorem dro_roots_single {n : ℕ} (i : Fin n) :
    Pi.single i (1 : ℤ) ∈ roots (isFiniteType_cartanD n) ∅ := by
  refine Or.inl ⟨1, i, ?_⟩
  rw [map_one, Module.End.one_apply]

private theorem dro_roots_reflection {n : ℕ} (j : Fin n) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD n) ∅) :
    reflection (CartanMatrix.D n) j γ ∈ roots (isFiniteType_cartanD n) ∅ := by
  have h := weylAction_mem_roots (isFiniteType_cartanD n)
    ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple j) hγ
  rw [weylAction_simple] at h
  rwa [← cartanD_eq]

private theorem dro_ggDRoot_of_roots {n : ℕ} (hn : 5 ≤ n) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD n) ∅) : GGDRoot n (dro_lift γ) := by
  rw [rootsD_eq n (by omega)] at hγ
  obtain ⟨a, b, s, t, hab, hs, ht, he⟩ := hγ
  refine ⟨a.val, b.val, a.isLt, b.isLt, fun h => hab (Fin.ext h), s, t, hs, ht, ?_⟩
  intro k
  by_cases hk : k < n
  · rw [dro_ggDeps_toStdD (by omega : 3 ≤ n) (dro_lift γ) hk, dro_lift_fin γ, he]
    simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
  · have h0 : ggDeps n (dro_lift γ) k = 0 := by
      rw [ggDeps]
      split_ifs <;> omega
    rw [h0]
    have ha' : k ≠ a.val := by omega
    have hb' : k ≠ b.val := by omega
    simp [ha', hb']

private theorem dro_aux {n : ℕ} (k i : Fin n) (ψ : List (Fin n)) :
    (ggSWord (ggAttachCartan (CartanMatrix.D n) k) (ψ.map some)
      (Pi.single (some i) 1)) none = 0 ∧
      (fun l : Fin n => ggSWord (ggAttachCartan (CartanMatrix.D n) k) (ψ.map some)
        (Pi.single (some i) 1) (some l)) ∈ roots (isFiniteType_cartanD n) ∅ := by
  induction ψ with
  | nil =>
    refine ⟨?_, ?_⟩
    · simp only [List.map_nil, ggSWord]
      simp
    · simp only [List.map_nil, ggSWord]
      have h : (fun l : Fin n => (Pi.single (some i) (1 : ℤ) : Option (Fin n) → ℤ) (some l)) =
          Pi.single i 1 := by
        funext l
        simp [Pi.single_apply]
      rw [h]
      exact dro_roots_single i
  | cons j ψ' ih =>
    obtain ⟨hm0, hmroots⟩ := ih
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, ggSWord]
      exact dro_sRefl_none k j _ hm0
    · simp only [List.map_cons, ggSWord]
      rw [dro_sRefl_some k j _ hm0]
      exact dro_roots_reflection j hmroots

theorem ggDRoot_of_mem_ggLCoroots {n : ℕ} (hn : 5 ≤ n) (k : Fin n)
    {v : Option (Fin n) → ℤ} (hv : v ∈ ggLCoroots (ggAttachCartan (CartanMatrix.D n) k)) :
    v none = 0 ∧ GGDRoot n (fun i => if h : i < n then v (some ⟨i, h⟩) else 0) := by
  obtain ⟨ψ, i, rfl⟩ := hv
  obtain ⟨h0, hroots⟩ := dro_aux k i ψ
  exact ⟨h0, dro_ggDRoot_of_roots hn hroots⟩

end CFSG.StandardType
