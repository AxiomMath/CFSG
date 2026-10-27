module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalExtTwist
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalExtGlue
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointVertex


public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private theorem sup_zpowers_eq_of_relIndex_eq_two_u4Id {S₀ : Subgroup G} {τ : G}
    (hS₀S : S₀ ≤ S) (hidx : S₀.relIndex S = 2) (hτS : τ ∈ S) (hτS₀ : τ ∉ S₀) :
    S₀ ⊔ Subgroup.zpowers τ = S := by
  have hle : S₀ ⊔ Subgroup.zpowers τ ≤ S := sup_le hS₀S ((Subgroup.zpowers_le).mpr hτS)
  refine le_antisymm hle ?_
  have hmul := Subgroup.relIndex_mul_relIndex S₀ (S₀ ⊔ Subgroup.zpowers τ) S le_sup_left hle
  rw [hidx] at hmul
  have hne : S₀.relIndex (S₀ ⊔ Subgroup.zpowers τ) ≠ 1 := fun h1 =>
    hτS₀ ((Subgroup.relIndex_eq_one.mp h1) (Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)))
  have hdvd : S₀.relIndex (S₀ ⊔ Subgroup.zpowers τ) ∣ 2 := ⟨_, hmul.symm⟩
  have h2 : S₀.relIndex (S₀ ⊔ Subgroup.zpowers τ) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left hne
  rw [h2] at hmul
  exact Subgroup.relIndex_eq_one.mp (by omega)

theorem isU4ExtTwo_of_u4qLocalData_of_card (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    IsU4ExtTwo f (f112Amalgam L1 L2 S) := by
  have R := hD.extension_reduction hH hf hS2
  obtain ⟨K, _, hU, Φ, τ, b₀, hτS, hτ1, hτ2, hb₀, hθ1, hθ2⟩ := hD.exists_twist_of_ext hf hH hS2
  have hS₀B : S ⊓ L1 ≤ bigB L1 L2 (S ⊓ L1) := le_sup_right
  have hS₀P1 : S ⊓ L1 ≤ L1 ⊔ bigB L1 L2 (S ⊓ L1) := hS₀B.trans le_sup_right
  have hS₀P2 : S ⊓ L1 ≤ L2 ⊔ bigB L1 L2 (S ⊓ L1) := hS₀B.trans le_sup_right
  have hSτ : S ⊓ L1 ⊔ Subgroup.zpowers τ = S :=
    sup_zpowers_eq_of_relIndex_eq_two_u4Id inf_le_left R.relIndex_eq hτS fun h => hτ1 (hS₀P1 h)
  have hτsq : τ ^ 2 ∈ (L1 ⊔ bigB L1 L2 (S ⊓ L1)) ⊓ (L2 ⊔ bigB L1 L2 (S ⊓ L1)) := by
    have hidx : ((S ⊓ L1).subgroupOf S).index = 2 := R.relIndex_eq
    have h := Subgroup.sq_mem_of_index_two hidx ⟨τ, hτS⟩
    rw [Subgroup.mem_subgroupOf] at h
    have h' : τ ^ 2 ∈ S ⊓ L1 := by simpa using h
    exact ⟨hS₀P1 h', hS₀P2 h'⟩
  have hsup : ∀ P : Subgroup G, S ⊓ L1 ≤ P → P ⊔ S = P ⊔ Subgroup.zpowers τ := by
    intro P hP
    rw [← hSτ, ← sup_assoc, sup_eq_left.mpr hP]
  have hP1 : L1 ⊔ bigB L1 L2 S = L1 ⊔ bigB L1 L2 (S ⊓ L1) ⊔ Subgroup.zpowers τ := by
    rw [R.sup_bigB_left, hsup _ hS₀P1]
  have hP2 : L2 ⊔ bigB L1 L2 S = L2 ⊔ bigB L1 L2 (S ⊓ L1) ⊔ Subgroup.zpowers τ := by
    rw [R.sup_bigB_right, hsup _ hS₀P2]
  have hinf : (L1 ⊔ bigB L1 L2 (S ⊓ L1) ⊔ Subgroup.zpowers τ) ⊓
      (L2 ⊔ bigB L1 L2 (S ⊓ L1) ⊔ Subgroup.zpowers τ) =
      (L1 ⊔ bigB L1 L2 (S ⊓ L1)) ⊓ (L2 ⊔ bigB L1 L2 (S ⊓ L1)) ⊔ Subgroup.zpowers τ := by
    rw [← hP1, ← hP2, parabolic_inf_parabolic (hD.hyp111R hf hH),
      parabolic_inf_parabolic (R.data.hyp111R hf R.hyp), R.bigB_eq, hsup _ hS₀B]
  have h := isU4ExtTwo_of_amalgamIso_of_conj hU Φ (R.le_normalizer_sup_left hτS)
    (R.le_normalizer_sup_right hτS) hτ1 hτ2 hτsq hinf hb₀ hθ1 hθ2
  show IsU4ExtTwo f (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S))
  rw [hP1, hP2]
  exact h

theorem isAmalgamOfGroup_psu4_or_isU4ExtTwo (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 4 f) ∨
      IsU4ExtTwo f (f112Amalgam L1 L2 S) := by
  rcases hD.card_S with hS | hS
  · exact Or.inl (isAmalgamOfGroup_psu4_of_u4qLocalData_of_card hf hH hD hS)
  · exact Or.inr (isU4ExtTwo_of_u4qLocalData_of_card hf hH hD hS)

end CFSG.Quasithin.F112R.St84

end
