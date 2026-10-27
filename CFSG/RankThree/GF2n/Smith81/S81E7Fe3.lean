module

public import CFSG.RankThree.GF2n.Smith81.S81E7Bruhat
public import CFSG.LieType.CurtisTits.Perfect

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
open scoped commutatorElement


variable {K : Type} [Field K]

@[expose] def IsRootEltG (g : ↥(e7Data_valid.minGroup K)) : Prop :=
  ∃ (h : ↥(e7Data_valid.minGroup K)) (γ : Fin (Tag.rank .E7) → ℤ) (c : K), IsRoot .E7 γ ∧ c ≠ 0 ∧
    g = h * e7Data_valid.xm K γ c * h⁻¹

@[expose] def letter (i : ℕ) : Fin (Tag.rank .E7) := ⟨i % 7, Nat.mod_lt _ (by decide)⟩

@[expose] def applyWord (ω : List ℕ) (v : Fin (Tag.rank .E7) → ℤ) : Fin (Tag.rank .E7) → ℤ :=
  ω.foldl (fun v i => reflect .E7 (letter i) v) v

@[expose] def wordTable : List (List ℕ) :=
  [[2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0], [3, 4, 5, 6, 2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [3, 4, 5, 6, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 5, 6, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0], [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0], [1, 3, 4, 5, 6, 2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 5, 6, 2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [2, 3, 4, 5, 6, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 5, 6, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [3, 4, 5, 6, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 6, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0], [1, 3, 4, 5, 6, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 5, 6, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 6, 2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [2, 3, 4, 5, 6, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 6, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [6, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [0, 2, 3, 4, 5, 6, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0], [5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0], [2, 1, 3, 4, 5, 6, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 6, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [6, 2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [2, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [6, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [0, 2, 1, 3, 4, 5, 6, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [0, 2, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0], [6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0], [2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 6, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [6, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [2, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [0, 2, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0], [6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0], [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0], [3, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [6, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [2, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [0, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [0, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 6, 4, 5, 3, 4, 1, 3, 2, 0], [6, 4, 5, 2, 3, 4, 1, 3, 2, 0], [3, 4, 5, 2, 3, 4, 1, 3, 2, 0], [3, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [6, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [3, 0, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [6, 4, 5, 3, 4, 1, 3, 2, 0], [6, 5, 2, 3, 4, 1, 3, 2, 0], [4, 5, 2, 3, 4, 1, 3, 2, 0], [4, 3, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 0, 2, 3, 4, 1, 3, 2, 0], [2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 3, 0, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [6, 5, 3, 4, 1, 3, 2, 0], [4, 5, 3, 4, 1, 3, 2, 0], [5, 2, 3, 4, 1, 3, 2, 0], [4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [0, 2, 3, 4, 1, 3, 2, 0], [4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [6, 5, 4, 1, 3, 2, 0], [5, 3, 4, 1, 3, 2, 0], [2, 3, 4, 1, 3, 2, 0], [5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [6, 5, 4, 3, 2, 0], [5, 4, 1, 3, 2, 0], [3, 4, 1, 3, 2, 0], [1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 4, 3, 2, 0], [4, 1, 3, 2, 0], [1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 3, 2, 0], [1, 3, 2, 0], [5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [3, 2, 0], [4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [2, 0], [3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [0], [2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [], [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]]

theorem wordTable_correct : ∀ k : Fin 126,
    applyWord (wordTable.getD k []) ((Tag.rootCertificate .E7).root k) = theta := by
  unfold applyWord wordTable letter
  decide +kernel

theorem exists_word_to_theta {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    ∃ ω : List ℕ, applyWord ω γ = theta := by
  obtain ⟨k, hk, hkγ⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hγ
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  have hk126 : k < 126 := by omega
  subst hkγ
  exact ⟨wordTable.getD k [], wordTable_correct ⟨k, hk126⟩⟩

theorem exists_conj_of_word [CharP K 2] (ω : List ℕ) :
    ∀ v : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 v → applyWord ω v = theta →
      ∃ g : ↥(e7Data_valid.minGroup K), ∀ c : K,
        g * e7Data_valid.xm K v c * g⁻¹ = e7Data_valid.xm K theta c := by
  induction ω with
  | nil =>
    intro v _ hv
    have hvt : v = theta := hv
    subst hvt
    exact ⟨1, fun c => by simp⟩
  | cons i ω ih =>
    intro v hv hvw
    have hvw' : applyWord ω (reflect .E7 (letter i) v) = theta := hvw
    have hv' : IsRoot .E7 (reflect .E7 (letter i) v) := IsRoot.reflect (letter i) hv
    obtain ⟨g', hg'⟩ := ih (reflect .E7 (letter i) v) hv' hvw'
    obtain ⟨σ, hσ, hconj⟩ := e7Data_valid.nm_conj_xm K hv (letter i)
    have hσ1 : σ = 1 := by
      rcases hσ with h | h
      · exact h
      · rw [h]
        exact CharTwo.neg_eq (1 : K)
    refine ⟨g' * e7Data_valid.nm K (letter i), fun c => ?_⟩
    have hcj : e7Data_valid.nm K (letter i) * e7Data_valid.xm K v c *
        (e7Data_valid.nm K (letter i))⁻¹ =
        e7Data_valid.xm K (reflect .E7 (letter i) v) c := by
      rw [hconj c, hσ1, one_mul]
    have key : g' * e7Data_valid.nm K (letter i) * e7Data_valid.xm K v c *
        (g' * e7Data_valid.nm K (letter i))⁻¹ =
        g' * (e7Data_valid.nm K (letter i) * e7Data_valid.xm K v c *
          (e7Data_valid.nm K (letter i))⁻¹) * g'⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    rw [key, hcj]
    exact hg' c

theorem exists_conj_to_theta [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    ∃ g : ↥(e7Data_valid.minGroup K), ∀ c : K,
      g * e7Data_valid.xm K γ c * g⁻¹ = e7Data_valid.xm K theta c := by
  obtain ⟨ω, hω⟩ := exists_word_to_theta hγ
  exact exists_conj_of_word ω γ hγ hω

theorem fe3_uni_comm_xm_theta {u : ↥(e7Data_valid.minGroup K)} (hu : u ∈ Uni K) (d : K) :
    u * e7Data_valid.xm K theta d = e7Data_valid.xm K theta d * u := by
  have hu' : u ∈ ⨆ γ ∈ {γ | γ ∈ (e7Datum K).roots ∧ 0 < ht γ}, (e7Datum K).rootGroup γ := hu
  refine Subgroup.iSup_induction _
    (C := fun v => v * e7Data_valid.xm K theta d = e7Data_valid.xm K theta d * v) hu' ?_ ?_ ?_
  · intro γ x hx
    by_cases hγ : γ ∈ {γ | γ ∈ (e7Datum K).roots ∧ 0 < ht γ}
    · rw [iSup_pos hγ] at hx
      obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hx
      obtain ⟨hγr, hγp⟩ : γ ∈ (e7Datum K).roots ∧ 0 < ht γ := hγ
      have hr : IsRoot .E7 γ := (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1 hγr
      have hβp : 0 < CFSG.Blueprint.Chevalley.height (τ := .E7) γ := hγp
      have hne : γ + theta ≠ 0 := by
        intro h0
        have hsum : CFSG.Blueprint.Chevalley.height (τ := .E7) (γ + theta)
            = CFSG.Blueprint.Chevalley.height (τ := .E7) γ
              + CFSG.Blueprint.Chevalley.height (τ := .E7) theta := by
          simp [CFSG.Blueprint.Chevalley.height, Finset.sum_add_distrib]
        have hz : CFSG.Blueprint.Chevalley.height (τ := .E7) (γ + theta) = 0 := by
          rw [h0]
          simp [CFSG.Blueprint.Chevalley.height]
        have hθ : 0 < CFSG.Blueprint.Chevalley.height (τ := .E7) theta :=
          CFSG.SeitzReduction.height_highRoot_pos .E7
        omega
      have hnot : ¬ IsRoot .E7 (γ + theta) := by
        have h := CFSG.SeitzReduction.not_isRoot_nsmul_add_nsmul_highRoot (τ := .E7) hβp le_rfl le_rfl
        simpa using h
      exact commutatorElement_eq_one_iff_mul_comm.1
        ((e7Data_valid.commutator_xm K hr isRoot_theta hne).2 hnot c d)
    · rw [iSup_neg hγ, Subgroup.mem_bot] at hx
      subst hx
      simp
  · simp
  · intro x y hx hy
    have hx' : x * e7Data_valid.xm K theta d = e7Data_valid.xm K theta d * x := hx
    have hy' : y * e7Data_valid.xm K theta d = e7Data_valid.xm K theta d * y := hy
    show x * y * e7Data_valid.xm K theta d = e7Data_valid.xm K theta d * (x * y)
    calc x * y * e7Data_valid.xm K theta d
        = x * (y * e7Data_valid.xm K theta d) := mul_assoc _ _ _
      _ = x * (e7Data_valid.xm K theta d * y) := by rw [hy']
      _ = (x * e7Data_valid.xm K theta d) * y := (mul_assoc _ _ _).symm
      _ = (e7Data_valid.xm K theta d * x) * y := by rw [hx']
      _ = e7Data_valid.xm K theta d * (x * y) := mul_assoc _ _ _

theorem fe3_tor_conj_xm_theta {t : ↥(e7Data_valid.minGroup K)} (htor : t ∈ Tor K) :
    ∃ s : K, s ≠ 0 ∧ ∀ c : K,
      t * e7Data_valid.xm K theta c * t⁻¹ = e7Data_valid.xm K theta (s * c) := by
  refine Subgroup.iSup_induction (fun i => e7Data_valid.torus K i)
    (C := fun t => ∃ s : K, s ≠ 0 ∧ ∀ c : K,
      t * e7Data_valid.xm K theta c * t⁻¹ = e7Data_valid.xm K theta (s * c)) htor ?_ ?_ ?_
  · intro i x hx
    obtain ⟨s, rfl⟩ := (e7Data_valid.mem_torus K).1 hx
    exact ⟨((s ^ MinData.toWeight theta i : Kˣ) : K), Units.ne_zero _,
      fun c => e7Data_valid.hm_conj_xm K isRoot_theta i s c⟩
  · exact ⟨1, one_ne_zero, fun c => by simp⟩
  · rintro x y ⟨sx, hsx, hx⟩ ⟨sy, hsy, hy⟩
    refine ⟨sx * sy, mul_ne_zero hsx hsy, fun c => ?_⟩
    calc x * y * e7Data_valid.xm K theta c * (x * y)⁻¹
        = x * (y * e7Data_valid.xm K theta c * y⁻¹) * x⁻¹ := by group
      _ = x * e7Data_valid.xm K theta (sy * c) * x⁻¹ := by rw [hy c]
      _ = e7Data_valid.xm K theta (sx * (sy * c)) := hx _
      _ = e7Data_valid.xm K theta (sx * sy * c) := by rw [mul_assoc]

theorem fe3_isRootEltG_conj_theta [CharP K 2] {x : ↥(e7Data_valid.minGroup K)}
    (hx : IsRootEltG x) :
    ∃ p : ↥(e7Data_valid.minGroup K), ∃ c : K, c ≠ 0 ∧
      x = p * e7Data_valid.xm K theta c * p⁻¹ := by
  unfold IsRootEltG at hx
  obtain ⟨h, γ, c, hγ, hc, rfl⟩ := hx
  obtain ⟨g, hg⟩ := exists_conj_to_theta (K := K) hγ
  refine ⟨h * g⁻¹, c, hc, ?_⟩
  rw [← hg c]
  group

theorem fe3_xm_mul_self_eq_one [CharP K 2] (γ : Fin (Tag.rank .E7) → ℤ) (c : K) :
    e7Data_valid.xm K γ c * e7Data_valid.xm K γ c = 1 := by
  have h2 : c + c = 0 := by
    have h2' : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    rw [← two_mul, h2', zero_mul]
  rw [← e7Data_valid.xm_add K γ c c, h2, e7Data_valid.xm_zero]

theorem fe3_pow_four_of_involutions {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y * y = 1) (hz : ⁅x, y⁆ * ⁅x, y⁆ = 1) :
    (x * y) ^ 4 = 1 := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hzd : ⁅x, y⁆ = (x * y) ^ 2 := by
    rw [commutatorElement_def, hxi, hyi, pow_two]
    simp only [mul_assoc]
  calc (x * y) ^ 4 = (x * y) ^ 2 * (x * y) ^ 2 := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
    _ = ⁅x, y⁆ * ⁅x, y⁆ := by rw [hzd]
    _ = 1 := hz

theorem fe3_conj_pow_four_eq_one {G : Type*} [Group G] {e z : G}
    (h : (e * z * e⁻¹) ^ 4 = 1) : z ^ 4 = 1 := by
  rw [conj_pow] at h
  calc z ^ 4 = e⁻¹ * (e * z ^ 4 * e⁻¹) * e := by group
    _ = 1 := by
        rw [h]
        group

theorem fe3_eq_one_of_odd_orderOf_pow_four {G : Type*} [Group G] {z : G}
    (ho : Odd (orderOf z)) (h4 : z ^ 4 = 1) : z = 1 := by
  have hdvd : orderOf z ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hle : orderOf z ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have h1 : orderOf z = 1 := by
    obtain ⟨k, hk⟩ := ho
    generalize orderOf z = n at hk hle hdvd ⊢
    interval_cases n <;> omega
  exact orderOf_eq_one_iff.1 h1

theorem bor_conj_xm_theta {b : ↥(e7Data_valid.minGroup K)} (hb : b ∈ Bor K) (c : K) :
    ∃ c' : K, b * e7Data_valid.xm K theta c * b⁻¹ = e7Data_valid.xm K theta c' ∧ (c ≠ 0 → c' ≠ 0) := by
  obtain ⟨u, hu, t, htor, rfl⟩ := bor_eq_mul hb
  obtain ⟨s, hs, hts⟩ := fe3_tor_conj_xm_theta htor
  refine ⟨s * c, ?_, fun hc => mul_ne_zero hs hc⟩
  calc u * t * e7Data_valid.xm K theta c * (u * t)⁻¹
      = u * (t * e7Data_valid.xm K theta c * t⁻¹) * u⁻¹ := by group
    _ = u * e7Data_valid.xm K theta (s * c) * u⁻¹ := by rw [hts c]
    _ = e7Data_valid.xm K theta (s * c) := by
        rw [mul_inv_eq_iff_eq_mul]
        exact fe3_uni_comm_xm_theta hu (s * c)

theorem nW_conj_xm_theta (w : W7 K) (c : K) :
    ∃ (γ' : Fin (Tag.rank .E7) → ℤ) (c' : K), IsRoot .E7 γ' ∧
      nW K w * e7Data_valid.xm K theta c * (nW K w)⁻¹ = e7Data_valid.xm K γ' c' ∧
      (c ≠ 0 → c' ≠ 0) := by
  have hθ : theta ∈ (e7Datum K).roots :=
    (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).2 isRoot_theta
  have hact : ((e7Datum K).rootGroup theta).map (MulAut.conj (nW K w)).toMonoidHom
      = _ := CFSG.LieType.Steinberg.actsAs_nrep (e7Datum_isCTGroupDatum K) w theta hθ
  have hmem : nW K w * e7Data_valid.xm K theta c * (nW K w)⁻¹ ∈
      ((e7Datum K).rootGroup theta).map (MulAut.conj (nW K w)).toMonoidHom :=
    Subgroup.mem_map_of_mem (MulAut.conj (nW K w)).toMonoidHom
      (e7Data_valid.xm_mem_rootGroup K theta c)
  rw [hact] at hmem
  obtain ⟨c', hc'⟩ := (e7Data_valid.mem_rootGroup K).1 hmem
  have hγ' := (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1
    (CFSG.LieType.CurtisTits.weylAction_mem_roots hθ w)
  refine ⟨_, c', hγ', hc'.symm, fun hc hc0 => hc ?_⟩
  subst hc0
  rw [e7Data_valid.xm_zero] at hc'
  have h1 : e7Data_valid.xm K theta c = 1 := by
    calc e7Data_valid.xm K theta c
        = (nW K w)⁻¹ * (nW K w * e7Data_valid.xm K theta c * (nW K w)⁻¹) * nW K w := by group
      _ = (nW K w)⁻¹ * 1 * nW K w := by rw [← hc']
      _ = 1 := by group
  exact e7Data_valid.xm_injective K isRoot_theta (h1.trans (e7Data_valid.xm_zero K theta).symm)

theorem xm_pair_pow_four [CharP K 2] {γ δ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (hδ : IsRoot .E7 δ) (hne : γ + δ ≠ 0) (c d : K) :
    (e7Data_valid.xm K γ c * e7Data_valid.xm K δ d) ^ 4 = 1 := by
  apply fe3_pow_four_of_involutions (fe3_xm_mul_self_eq_one γ c) (fe3_xm_mul_self_eq_one δ d)
  by_cases hr : IsRoot .E7 (γ + δ)
  · obtain ⟨σ, -, hσ⟩ := (e7Data_valid.commutator_xm K hγ hδ hne).1 hr
    rw [hσ c d]
    exact fe3_xm_mul_self_eq_one (γ + δ) (σ * c * d)
  · rw [(e7Data_valid.commutator_xm K hγ hδ hne).2 hr c d, mul_one]

theorem fe3_conj_core [CharP K 2] {x y : ↥(e7Data_valid.minGroup K)} (hx : IsRootEltG x)
    (hy : IsRootEltG y) (ho : Odd (orderOf (x * y))) (h1 : x * y ≠ 1) :
    ∃ e : ↥(e7Data_valid.minGroup K), ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧
      e * x * e⁻¹ = e7Data_valid.xm K theta a ∧ e * y * e⁻¹ = e7Data_valid.xm K (-theta) b := by
  obtain ⟨p, a, ha, rfl⟩ := fe3_isRootEltG_conj_theta hx
  obtain ⟨q, d, hd, rfl⟩ := fe3_isRootEltG_conj_theta hy
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hg⟩ := bruhat_decomp (p⁻¹ * q)
  obtain ⟨d', hconj₂, hdd⟩ := bor_conj_xm_theta hb₂ d
  obtain ⟨γ', c'', hγ', hconjW, hcc⟩ := nW_conj_xm_theta w d'
  obtain ⟨a', hconj₁, haa⟩ := bor_conj_xm_theta (inv_mem hb₁) a
  have hq : q = p * (b₁ * nW K w * b₂) := by
    rw [← hg, mul_inv_cancel_left]
  have hx_e : b₁⁻¹ * p⁻¹ * (p * e7Data_valid.xm K theta a * p⁻¹) * (b₁⁻¹ * p⁻¹)⁻¹
      = e7Data_valid.xm K theta a' := by
    rw [← hconj₁]
    group
  have hy_e : b₁⁻¹ * p⁻¹ * (q * e7Data_valid.xm K theta d * q⁻¹) * (b₁⁻¹ * p⁻¹)⁻¹
      = e7Data_valid.xm K γ' c'' := by
    rw [hq]
    calc b₁⁻¹ * p⁻¹ * (p * (b₁ * nW K w * b₂) * e7Data_valid.xm K theta d
          * (p * (b₁ * nW K w * b₂))⁻¹) * (b₁⁻¹ * p⁻¹)⁻¹
        = nW K w * (b₂ * e7Data_valid.xm K theta d * b₂⁻¹) * (nW K w)⁻¹ := by group
      _ = nW K w * e7Data_valid.xm K theta d' * (nW K w)⁻¹ := by rw [hconj₂]
      _ = e7Data_valid.xm K γ' c'' := hconjW
  by_cases hne : theta + γ' = 0
  · have hγ'eq : γ' = -theta := by
      funext j
      have hj := congrFun hne j
      simp only [Pi.add_apply, Pi.zero_apply] at hj
      simp only [Pi.neg_apply]
      omega
    subst hγ'eq
    exact ⟨b₁⁻¹ * p⁻¹, a', c'', haa ha, hcc (hdd hd), hx_e, hy_e⟩
  · exfalso
    have hprod : e7Data_valid.xm K theta a' * e7Data_valid.xm K γ' c'' =
        b₁⁻¹ * p⁻¹ * (p * e7Data_valid.xm K theta a * p⁻¹ * (q * e7Data_valid.xm K theta d * q⁻¹))
          * (b₁⁻¹ * p⁻¹)⁻¹ := by
      rw [← hx_e, ← hy_e]
      group
    have h4 := xm_pair_pow_four (K := K) isRoot_theta hγ' hne a' c''
    rw [hprod] at h4
    exact h1 (fe3_eq_one_of_odd_orderOf_pow_four ho (fe3_conj_pow_four_eq_one h4))

end CFSG.RankThree.GF2n.Smith81.E7Model
