module

public import CFSG.Quasithin.EmptyFaithful.E22QWit
public import CFSG.Quasithin.EmptyFaithful.E22QTypeI
public import CFSG.Quasithin.EmptyFaithful.E22QTypeIII
public import CFSG.Quasithin.EmptyFaithful.E22QSwap
public import CFSG.Quasithin.EmptyFaithful.E22QInnerTypeII
public import CFSG.Quasithin.EmptyFaithful.E22QTypeIIo

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b

variable {G : Type} [Group G] [Finite G]

theorem card_ge_four_of_ne_two {A : Subgroup G} (hAab : IsElemAbelian 2 A) (hA1 : A ≠ ⊥)
    (hA2 : Nat.card A ≠ 2) : 4 ≤ Nat.card A := by
  have hp : IsPGroup 2 A := fun g => ⟨1, Subtype.ext (by simpa using hAab.2 g g.2)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rcases n with _ | _ | n
  · exact absurd (Subgroup.card_eq_one.mp (by simpa using hn)) hA1
  · exact absurd (by simpa using hn) hA2
  · rw [hn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem exists_mem_inf_normalizer {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ : G}
    (h : Wr p T M J₁ J₂ z₁) {A : Subgroup G} (hAT : A ≤ T) (hAab : IsElemAbelian 2 A)
    (hA4 : 4 ≤ Nat.card A) : A ⊓ Subgroup.normalizer (J₁ : Set G) ≠ ⊥ := by
  classical
  intro hbot
  have : Fintype ↥A := Fintype.ofFinite ↥A
  have h3 : 2 < (Finset.univ : Finset ↥A).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega
  obtain ⟨a, -, b, -, c, -, hab, hac, hbc⟩ := Finset.two_lt_card.mp h3
  have key : ∀ a b : ↥A, a ≠ 1 → b ≠ 1 → a ≠ b → False := by
    intro a b ha hb hab
    have hsq : ∀ x : ↥A, (x : G) * x = 1 := fun x => by
      have := hAab.2 x x.2
      simpa [pow_two] using this
    have hswap : ∀ x : ↥A, x ≠ 1 → conjSub (x : G) J₁ = J₂ := by
      intro x hx
      rcases h.perm x (hAT x.2) with h1 | h1
      · exfalso
        apply hx
        have hmem : (x : G) ∈ A ⊓ Subgroup.normalizer (J₁ : Set G) :=
          ⟨x.2, conjSub_eq_iff_mem_normalizer.mp h1⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact Subtype.ext hmem
      · exact h1
    have h1 := hswap a ha
    have h2 := hswap b hb
    have hab' : conjSub ((a : G) * b) J₁ = J₁ := by
      rw [conjSub_mul, h2]
      have : conjSub (a : G) J₂ = J₁ := by
        rw [← h1, ← conjSub_mul, hsq a, conjSub_one]
      exact this
    have hmem : ((a : G) * b) ∈ A ⊓ Subgroup.normalizer (J₁ : Set G) :=
      ⟨A.mul_mem a.2 b.2, conjSub_eq_iff_mem_normalizer.mp hab'⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hab
    have hb' : (b : G) = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right hmem
    have ha' : (a : G) = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right (hsq a)
    exact Subtype.ext (hb'.trans ha'.symm).symm
  by_cases ha1 : a = 1
  · exact key b c (fun h => hab (ha1.trans h.symm)) (fun h => hac (ha1.trans h.symm)) hbc
  · by_cases hb1 : b = 1
    · exact key a c ha1 (fun h => hbc (hb1.trans h.symm)) hac
    · exact key a b ha1 hb1 hab

theorem wrInEFor {p : ℕ}
    {T M J₁ J₂ : Subgroup G} {z₁ : G} (h : Wr p T M J₁ J₂ z₁) : E1.InEFor 1 ⊤ T := by
  have WL : WitnessL2 p := witnessL2 h.p_prime h.p_mod h.p_ge
  refine inEFor_of_star h ?_
  intro Ω hΩ A hA hAT hA1
  have hAab := hΩ.isElemAbelian A hA
  by_cases hR : T ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (J₁ : Set G)
  · obtain ⟨K, hK, hKM⟩ := typeI WL h hAT hAab hA1 hR
    exact ⟨A, hA, hAT, K, hK, hKM⟩
  · by_cases hA2 : Nat.card A = 2
    · exact ⟨A, hA, hAT, ⊤, swap_witness h hAT hA2 hR,
        fun hle => h.coatom.1 (top_le_iff.mp hle)⟩
    · have hA4 := card_ge_four_of_ne_two hAab hA1 hA2
      by_cases hAS : A ≤ Subgroup.normalizer (J₁ : Set G)
      · by_cases hAX : A ≤ J₁ ⊔ J₂
        · exact typeII_inner h (fun hAT' hab' hA1' hR' => typeI WL h hAT' hab' hA1' hR') hΩ hA hAT
            hAab hA4 hR hAX
        · obtain ⟨K, hK, hKM⟩ := typeII_outer h hAT hAab hA4 hR hAS hAX
          exact ⟨A, hA, hAT, K, hK, hKM⟩
      · obtain ⟨z, hzA, hzS⟩ : ∃ z ∈ A, z ∉ Subgroup.normalizer (J₁ : Set G) := by
          by_contra hcon
          push Not at hcon
          exact hAS hcon
        obtain ⟨K, hK, hKM⟩ := typeIII WL h hAT hAab hzA hzS
          (exists_mem_inf_normalizer h hAT hAab hA4)
        exact ⟨A, hA, hAT, K, hK, hKM⟩

theorem wrCore : WrCore := by
  intro p G _ _ T M J₁ J₂ z₁ h
  exact wrInEFor h

end CFSG.Quasithin.E2.E22N
