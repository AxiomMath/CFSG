module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Vec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Module QuadraticMap CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] noncomputable def s16c1G_qMul (x : Multiplicative V₀) : ZMod 2 :=
  qModel true (Multiplicative.toAdd x)

theorem s16c1G_polarQ_qMul (x y : Multiplicative V₀) :
    polarQ s16c1G_qMul x y =
      polar (qModel true) (Multiplicative.toAdd x) (Multiplicative.toAdd y) := rfl

@[expose] def s16c1G_deg2 (a b : ℕ) : Prop := vec a = 0 ∨ vec b = 0 ∨ vec a = vec b

instance (a b : ℕ) : Decidable (s16c1G_deg2 a b) := by
  unfold s16c1G_deg2
  infer_instance

@[expose] def s16c1G_deg3 (a b c : ℕ) : Prop :=
  vec c = 0 ∨ vec c = vec a ∨ vec c = vec b ∨ vec c = vec a + vec b

instance (a b c : ℕ) : Decidable (s16c1G_deg3 a b c) := by
  unfold s16c1G_deg3
  infer_instance

@[expose] def s16c1G_chk3 (a b : ℕ) : Prop :=
  ∀ c < 64, qB true c = false → qB true (a ^^^ c) = false → qB true (b ^^^ c) = false →
    qB true (a ^^^ b ^^^ c) = false → s16c1G_deg3 a b c

instance (a b : ℕ) : Decidable (s16c1G_chk3 a b) := by
  unfold s16c1G_chk3
  infer_instance

@[expose] def s16c1G_chk2 (a : ℕ) : Prop :=
  qB true a = false → ∀ b < 64, qB true b = false → qB true (a ^^^ b) = false →
    (s16c1G_deg2 a b ∨ s16c1G_chk3 a b)

instance (a : ℕ) : Decidable (s16c1G_chk2 a) := by
  unfold s16c1G_chk2
  infer_instance

theorem s16c1G_chk2_all : ∀ a < 64, s16c1G_chk2 a := by
  decide +kernel

theorem s16c1G_noLagr_check : ∀ a < 64, qB true a = false → ∀ b < 64, qB true b = false →
    qB true (a ^^^ b) = false → ∀ c < 64, qB true c = false → qB true (a ^^^ c) = false →
    qB true (b ^^^ c) = false → qB true (a ^^^ b ^^^ c) = false →
    (vec a = 0 ∨ vec b = 0 ∨ vec a = vec b ∨ vec c = 0 ∨ vec c = vec a ∨ vec c = vec b ∨
      vec c = vec a + vec b) := by
  intro a ha hqa b hb hqb hqab c hc hqc hqac hqbc hqabc
  rcases s16c1G_chk2_all a ha hqa b hb hqb hqab with h | h
  · rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases h c hc hqc hqac hqbc hqabc with h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem s16c1G_card_mul : Nat.card (Multiplicative V₀) = 64 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative V₀ ≃ V₀), Nat.card_eq_fintype_card]
  decide +kernel

theorem s16c1G_rk_top_model : rk ↥(⊤ : Subgroup (Multiplicative V₀)) = 6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rk
  rw [Subgroup.card_top, s16c1G_card_mul, show (64 : ℕ) = 2 ^ 6 by norm_num,
    padicValNat.prime_pow]

theorem s16c1G_card_eight {U : Subgroup (Multiplicative V₀)}
    (h : 2 * rk ↥U = rk ↥(⊤ : Subgroup (Multiplicative V₀))) : Nat.card U = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [s16c1G_rk_top_model] at h
  have hdvd : Nat.card U ∣ 2 ^ 6 := by
    have h1 := Subgroup.card_subgroup_dvd_card U
    rwa [s16c1G_card_mul, show (64 : ℕ) = 2 ^ 6 by norm_num] at h1
  obtain ⟨i, -, hUi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hrk : rk ↥U = i := by
    unfold rk
    rw [hUi, padicValNat.prime_pow]
  have hi3 : i = 3 := by omega
  rw [hUi, hi3]
  norm_num

theorem s16c1G_no_totSing {U : Subgroup (Multiplicative V₀)}
    (hU : ∀ u ∈ U, s16c1G_qMul u = 0) (hcard : Nat.card U = 8) : False := by
  classical
  have hncard : (U : Set (Multiplicative V₀)).ncard = 8 := by
    rw [← hcard]
    exact (Nat.card_coe_set_eq _).symm
  obtain ⟨u₁, hu₁U, hu₁⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (s := ({1} : Set (Multiplicative V₀))) (t := (U : Set (Multiplicative V₀)))
    (by rw [Set.ncard_singleton, hncard]; norm_num)
  obtain ⟨u₂, hu₂U, hu₂⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (s := ({1, u₁} : Set (Multiplicative V₀))) (t := (U : Set (Multiplicative V₀)))
    (by
      have c1 := Set.ncard_insert_le (1 : Multiplicative V₀) ({u₁} : Set (Multiplicative V₀))
      rw [Set.ncard_singleton] at c1
      omega)
  obtain ⟨u₃, hu₃U, hu₃⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (s := ({1, u₁, u₂, u₁ * u₂} : Set (Multiplicative V₀))) (t := (U : Set (Multiplicative V₀)))
    (by
      have c0 : ({u₁ * u₂} : Set (Multiplicative V₀)).ncard = 1 := Set.ncard_singleton _
      have c1 := Set.ncard_insert_le u₂ ({u₁ * u₂} : Set (Multiplicative V₀))
      have c2 := Set.ncard_insert_le u₁ ({u₂, u₁ * u₂} : Set (Multiplicative V₀))
      have c3 := Set.ncard_insert_le (1 : Multiplicative V₀)
        ({u₁, u₂, u₁ * u₂} : Set (Multiplicative V₀))
      omega)
  have hn1 : u₁ ≠ 1 := fun h => hu₁ (by simp [h])
  have hn2 : u₂ ≠ 1 := fun h => hu₂ (by simp [h])
  have hn2' : u₂ ≠ u₁ := fun h => hu₂ (by simp [h])
  have hn3 : u₃ ≠ 1 := fun h => hu₃ (by simp [h])
  have hn3a : u₃ ≠ u₁ := fun h => hu₃ (by simp [h])
  have hn3b : u₃ ≠ u₂ := fun h => hu₃ (by simp [h])
  have hn3c : u₃ ≠ u₁ * u₂ := fun h => hu₃ (by simp [h])
  obtain ⟨a, ha, haeq⟩ := s16c1G_exists_vec (Multiplicative.toAdd u₁)
  obtain ⟨b, hb, hbeq⟩ := s16c1G_exists_vec (Multiplicative.toAdd u₂)
  obtain ⟨c, hc, hceq⟩ := s16c1G_exists_vec (Multiplicative.toAdd u₃)
  have hq : ∀ u ∈ U, ∀ n : ℕ, vec n = Multiplicative.toAdd u → qB true n = false := by
    intro u hu n hn
    apply s16c1G_qB_eq_false
    have h := hU u hu
    rw [s16c1G_qMul, ← hn] at h
    exact h
  have hqa : qB true a = false := hq u₁ hu₁U a haeq
  have hqb : qB true b = false := hq u₂ hu₂U b hbeq
  have hqc : qB true c = false := hq u₃ hu₃U c hceq
  have hqab : qB true (a ^^^ b) = false := hq (u₁ * u₂) (U.mul_mem hu₁U hu₂U) _
    (by rw [s16c1G_vec_xor, haeq, hbeq]; rfl)
  have hqac : qB true (a ^^^ c) = false := hq (u₁ * u₃) (U.mul_mem hu₁U hu₃U) _
    (by rw [s16c1G_vec_xor, haeq, hceq]; rfl)
  have hqbc : qB true (b ^^^ c) = false := hq (u₂ * u₃) (U.mul_mem hu₂U hu₃U) _
    (by rw [s16c1G_vec_xor, hbeq, hceq]; rfl)
  have hqabc : qB true (a ^^^ b ^^^ c) = false :=
    hq (u₁ * u₂ * u₃) (U.mul_mem (U.mul_mem hu₁U hu₂U) hu₃U) _
      (by rw [s16c1G_vec_xor, s16c1G_vec_xor, haeq, hbeq, hceq]; rfl)
  have hinj : ∀ x y : Multiplicative V₀, Multiplicative.toAdd x = Multiplicative.toAdd y →
      x = y := fun x y h => Multiplicative.toAdd.injective h
  rcases s16c1G_noLagr_check a ha hqa b hb hqb hqab c hc hqc hqac hqbc hqabc with
    h | h | h | h | h | h | h
  · exact hn1 (hinj _ 1 (by rw [← haeq, h]; rfl))
  · exact hn2 (hinj _ 1 (by rw [← hbeq, h]; rfl))
  · exact hn2' (hinj _ _ (by rw [← haeq, ← hbeq, h]))
  · exact hn3 (hinj _ 1 (by rw [← hceq, h]; rfl))
  · exact hn3a (hinj _ _ (by rw [← haeq, ← hceq, h]))
  · exact hn3b (hinj _ _ (by rw [← hbeq, ← hceq, h]))
  · exact hn3c (hinj _ _ (by rw [← hceq, h, haeq, hbeq]; rfl))

theorem s16c1G_isMinusQuadF2_qMul : IsMinusQuadF2 s16c1G_qMul := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro x y z
    rw [s16c1G_polarQ_qMul, s16c1G_polarQ_qMul, s16c1G_polarQ_qMul]
    exact QuadraticMap.polar_add_left (qModel true) _ _ _
  · intro x y z
    rw [s16c1G_polarQ_qMul, s16c1G_polarQ_qMul, s16c1G_polarQ_qMul]
    exact QuadraticMap.polar_add_right (qModel true) _ _ _
  · intro x hx
    by_contra hcon
    push Not at hcon
    apply hx
    have h0 : Multiplicative.toAdd x = 0 := by
      refine (qModel_nondegenerate true).1 _ (fun y => ?_)
      rw [QuadraticMap.polarBilin_apply_apply]
      have h := hcon (Multiplicative.ofAdd y)
      rwa [s16c1G_polarQ_qMul] at h
    exact Multiplicative.toAdd.injective h0
  · rintro ⟨U, hU, hrk⟩
    exact s16c1G_no_totSing hU (s16c1G_card_eight hrk)

theorem s16c1G_isMinusQuadF2_comp {W W' : Type} [CommGroup W] [CommGroup W'] (β : W ≃* W')
    {Q' : W' → ZMod 2} (h : IsMinusQuadF2 Q') : IsMinusQuadF2 (fun x => Q' (β x)) := by
  obtain ⟨⟨⟨h1, h2⟩, hnd⟩, hno⟩ := h
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro x y z
    have h := h1 (β x) (β y) (β z)
    simpa [polarQ, map_mul] using h
  · intro x y z
    have h := h2 (β x) (β y) (β z)
    simpa [polarQ, map_mul] using h
  · intro x hx
    obtain ⟨y, hy⟩ := hnd (β x) (fun h => hx (β.injective (by rw [h, map_one])))
    refine ⟨β.symm y, ?_⟩
    simpa [polarQ] using hy
  · rintro ⟨U, hU, hrk⟩
    refine hno ⟨U.map β.toMonoidHom, ?_, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact hU u hu
    · have e1 : rk ↥(U.map β.toMonoidHom) = rk ↥U := by
        unfold rk
        rw [Subgroup.card_map_of_injective (f := β.toMonoidHom) β.injective]
      have e2 : rk ↥(⊤ : Subgroup W') = rk ↥(⊤ : Subgroup W) := by
        unfold rk
        rw [Subgroup.card_top, Subgroup.card_top, Nat.card_congr β.toEquiv]
      rw [e1, e2]
      exact hrk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
