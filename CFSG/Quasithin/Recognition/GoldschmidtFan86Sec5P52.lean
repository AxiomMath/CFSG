module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P52C
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P52D
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalChar
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Defs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem prod_Ico_ite (t b : ℤ) (hb : b ≤ t) (P : ℤ → Prop) [DecidablePred P] (A B : ℕ) :
    ∏ j ∈ Finset.Ico 1 (t - b + 1).toNat, (if P (t - j) then A else B) =
      A ^ {i : ℤ | b ≤ i ∧ i < t ∧ P i}.ncard * B ^ {i : ℤ | b ≤ i ∧ i < t ∧ ¬ P i}.ncard := by
  have key : ∀ Q : ℤ → Prop, [DecidablePred Q] →
      {i : ℤ | b ≤ i ∧ i < t ∧ Q i}.ncard =
        ((Finset.Ico 1 (t - b + 1).toNat).filter (fun j : ℕ => Q (t - j))).card := by
    intro Q _
    have hset : {i : ℤ | b ≤ i ∧ i < t ∧ Q i} = (fun j : ℕ => t - (j : ℤ)) ''
        (↑((Finset.Ico 1 (t - b + 1).toNat).filter (fun j : ℕ => Q (t - j))) : Set ℕ) := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨(t - i).toNat, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
        rwa [show t - ((t - i).toNat : ℤ) = i by omega]
      · rintro ⟨j, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
        exact ⟨by omega, by omega, h3⟩
    rw [hset, Set.ncard_image_of_injective _ (by intro j k h; simpa using h), Set.ncard_coe_finset]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, key P, key (fun i => ¬ P i)]

theorem fan52 (F : FanTree Γ G) :
    Fan40 F → ∀ (ℓ : Line Γ) (z : G) (a b tL tR : ℤ), z ∈ ℓ.ZZ → ℓ.IsCoreFix z a b tL tR →
      ∀ x ∈ MulAction.stabilizer G (ℓ.vert tR), orderOf x = valence Γ (ℓ.vert tR) →
      (∀ β β' : V, Γ.Adj β β' → valence Γ β ≠ 3 →
        (Subgroup.centralizer ({x} : Set G)).relIndex (nbrStab Γ G (ℓ.vert tR)) ≤
          2 ^ (2 * {i : ℤ | b ≤ i ∧ i < tR ∧ valence Γ (ℓ.vert i) = 3}.ncard) *
            (nbrStab Γ G β).relIndex (MulAction.stabilizer G β ⊓ MulAction.stabilizer G β') ^
              (2 * {i : ℤ | b ≤ i ∧ i < tR ∧ valence Γ (ℓ.vert i) ≠ 3}.ncard)) ∧
      ∀ ε : V, Γ.Adj ε (ℓ.vert tR) →
        Nat.card (nbrStab Γ G ε) ≤
          ((Subgroup.centralizer ({x} : Set G)).relIndex (nbrStab Γ G (ℓ.vert tR)) *
            (nbrStab Γ G (ℓ.vert tR)).relIndex
              (MulAction.stabilizer G ε ⊓ MulAction.stabilizer G (ℓ.vert tR))) ^ valence Γ ε := by
  classical
  intro _h40 ℓ z a b tL tR hz hc x hx hxo
  obtain ⟨hzz, -⟩ := hz
  obtain ⟨hfix, hcore⟩ := hc
  obtain ⟨hab, hcfix, hcen, -, -⟩ := hcore
  have hfa := (hfix a).1 (hcfix a le_rfl hab.le)
  have hfb := (hfix b).1 (hcfix b hab.le le_rfl)
  refine ⟨fun β β' hββ' hβ3 => ?_, fun ε hε => F.fan52_eps hε hx hxo⟩
  set v : ℕ → V := fun j => ℓ.vert (tR - j) with hv
  have hadj : ∀ j, Γ.Adj (v j) (v (j + 1)) := fun j => by
    have e1 : v (j + 1) = ℓ.vert (tR - j - 1) := by simp only [hv]; congr 1; push_cast; ring
    rw [e1]
    exact ℓ.adj_pred (tR - j)
  have hnb : ∀ j, v j ≠ v (j + 2) := fun j => by
    have e1 : v (j + 2) = ℓ.vert (tR - j - 1 - 1) := by simp only [hv]; congr 1; push_cast; ring
    have e2 : v j = ℓ.vert (tR - j - 1 + 1) := by simp only [hv]; congr 1; ring
    rw [e1, e2]
    exact (ℓ.vert_pred_ne_succ _).symm
  have h0 : v 0 = ℓ.vert tR := by simp [hv]
  set m : ℕ := (tR - b + 1).toNat with hm
  have hm1 : 1 ≤ m := by omega
  have hzfix : ∀ j, j ≤ m → z • v j = v j := fun j hj => (hfix (tR - j)).2 ⟨by omega, by omega⟩
  have hzc : ∀ g : G, g • v (m - 1) = v (m - 1) → g • v m = v m → g * z = z * g := by
    intro g h1 h2
    have e1 : v (m - 1) = ℓ.vert b := by simp only [hv]; congr 1; omega
    have e2 : v m = ℓ.vert (b - 1) := by simp only [hv]; congr 1; omega
    rw [e1] at h1
    rw [e2] at h2
    exact (hcen (b - 1) (by omega) (by omega)).2 g ⟨MulAction.mem_stabilizer_iff.2 h2,
      MulAction.mem_stabilizer_iff.2 (by rw [show b - 1 + 1 = b by omega]; exact h1)⟩
  have hzK : z ∉ nbrStab Γ G (v 0) := by
    intro hK
    rw [h0] at hK
    have := (hfix (tR + 1)).1 (mem_nbrStab.1 hK _ (ℓ.adj tR))
    omega
  have hx' : x ∈ MulAction.stabilizer G (v 0) := by rw [h0]; exact hx
  have hxo' : orderOf x = Fan86.valence Γ (v 0) := by rw [h0]; exact hxo
  set h : ℕ := (nbrStab Γ G β).relIndex (MulAction.stabilizer G β ⊓ MulAction.stabilizer G β')
    with hh
  let f : ℕ → ℕ := fun j => if Fan86.valence Γ (v j) = 3 then 2 else h
  have hf : ∀ j, 1 ≤ j → j < m → (nbrStab Γ G (v j)).relIndex
      (MulAction.stabilizer G (v j) ⊓ MulAction.stabilizer G (v (j - 1))) ≤ f j := by
    intro j hj1 hjm
    have hadj1 : Γ.Adj (v j) (v (j - 1)) := by
      have := (hadj (j - 1)).symm
      rwa [show j - 1 + 1 = j by omega] at this
    by_cases h3 : Fan86.valence Γ (v j) = 3
    · simp only [f, h3, ↓reduceIte]
      exact (F.relIndex_nbrStab_eq_two hadj1 h3).le
    · simp only [f, h3, ↓reduceIte]
      have hp1 : Fan86.valence Γ (v j) = 3 ∨ Fan86.valence Γ (v j) = 5 := F.valence _
      have hp2 : Fan86.valence Γ β = 3 ∨ Fan86.valence Γ β = 5 := F.valence _
      exact (F.relIndex_edge_eq hββ' hadj1 (by omega)).le
  have key := F.fan52_ray hadj hnb hm1 hzz hzfix hzc hzK hx' hxo' f hf
  rw [h0] at key
  have hprod : ∏ j ∈ Finset.Ico 1 m, f j =
      2 ^ {i : ℤ | b ≤ i ∧ i < tR ∧ Fan86.valence Γ (ℓ.vert i) = 3}.ncard *
        h ^ {i : ℤ | b ≤ i ∧ i < tR ∧ ¬ Fan86.valence Γ (ℓ.vert i) = 3}.ncard :=
    prod_Ico_ite tR b (by omega) (fun i => Fan86.valence Γ (ℓ.vert i) = 3) 2 h
  refine key.trans (le_of_eq ?_)
  rw [hprod, mul_pow, ← pow_mul, ← pow_mul, mul_comm _ 2, mul_comm _ 2]

end CFSG.Quasithin.Fan86
