module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalChar

public section

namespace CFSG.Quasithin.Fan86

namespace P71

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem units_invol_eq {p : ℕ} (hp : p = 5) (a b : (ZMod p)ˣ) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  subst hp
  revert a b
  decide

theorem exists_order_five (F : FanTree Γ G) {α u₁ u₂ : V} (h5 : Fan86.valence Γ α = 5)
    (h1 : Γ.Adj α u₁) (h2 : Γ.Adj α u₂) {s t : G} (hs : s ∈ MulAction.stabilizer G α)
    (ht : t ∈ MulAction.stabilizer G α) (hs2 : s * s = 1) (ht2 : t * t = 1)
    (hsu₁ : s • u₁ = u₁) (hsu₂ : s • u₂ ≠ u₂) (htu₂ : t • u₂ = u₂) (htu₁ : t • u₁ ≠ u₁) :
    ∃ x ∈ Subgroup.closure ({s, t} : Set G), orderOf x = 5 := by
  have hp : (Fan86.valence Γ α).Prime := F.valence_isPrime α
  have : Fact (Fan86.valence Γ α).Prime := ⟨hp⟩
  obtain ⟨x, hx, hxo⟩ := F.exists_orderOf_eq_valence α
  obtain ⟨ψ, hψ⟩ := F.exists_conjChar hx hxo
  let S : MulAction.stabilizer G α := ⟨s, hs⟩
  let T' : MulAction.stabilizer G α := ⟨t, ht⟩
  have hS2 : S * S = 1 := Subtype.ext hs2
  have hT2 : T' * T' = 1 := Subtype.ext ht2
  have hSne : ψ S ≠ 1 := by
    intro h
    have := (hψ S).2 ⟨h, u₁, h1, hsu₁⟩
    exact hsu₂ (mem_nbrStab.1 this u₂ h2)
  have hTne : ψ T' ≠ 1 := by
    intro h
    have := (hψ T').2 ⟨h, u₂, h2, htu₂⟩
    exact htu₁ (mem_nbrStab.1 this u₁ h1)
  have hS2' : ψ S ^ 2 = 1 := by rw [pow_two, ← map_mul, hS2, map_one]
  have hT2' : ψ T' ^ 2 = 1 := by rw [pow_two, ← map_mul, hT2, map_one]
  have hST : ψ S = ψ T' := units_invol_eq h5 _ _ hS2' hT2' hSne hTne
  have hY : ψ (S * T') = 1 := by rw [map_mul, ← hST, ← pow_two, hS2']
  have hYnb : ((S * T' : MulAction.stabilizer G α) : G) ∉ nbrStab Γ G α := by
    intro h
    have := mem_nbrStab.1 h u₂ h2
    have e : ((S * T' : MulAction.stabilizer G α) : G) • u₂ = s • u₂ := by
      show (s * t) • u₂ = s • u₂
      rw [mul_smul, htu₂]
    exact hsu₂ (e ▸ this)
  have hYfix : ∀ a, Γ.Adj α a → (s * t) • a ≠ a := by
    intro a ha hfix
    exact hYnb ((hψ (S * T')).2 ⟨hY, a, ha, hfix⟩)
  have hYst : (s * t) ∈ MulAction.stabilizer G α := (S * T').2
  obtain ⟨j, hj⟩ := F.exists_pow_smul_eq hx hxo h1
    (F.adj_smul_of_mem_stabilizer hYst h1 : Γ.Adj α ((s * t) • u₁))
  have hxp : x ^ 5 = 1 := by rw [← h5, ← hxo]; exact pow_orderOf_eq_one x
  let X : MulAction.stabilizer G α := ⟨x, hx⟩
  have hX5 : ψ X ^ 5 = 1 := by
    rw [← map_pow]
    have : X ^ 5 = 1 := Subtype.ext hxp
    rw [this, map_one]
  have hX4 : ψ X ^ 4 = 1 := units_pow_four (Or.inr h5) (ψ X)
  have hX : ψ X = 1 := by
    have := pow_succ (ψ X) 4
    rw [hX4, show (4 + 1 : ℕ) = 5 from rfl, hX5, one_mul] at this
    exact this.symm
  have hxj : x ^ j ∈ MulAction.stabilizer G α := pow_mem hx j
  let G₀ : MulAction.stabilizer G α := (X ^ j)⁻¹ * (S * T')
  have hG₀u : (G₀ : G) • u₁ = u₁ := by
    show ((x ^ j)⁻¹ * (s * t)) • u₁ = u₁
    rw [mul_smul, ← hj, inv_smul_smul]
  have hG₀ψ : ψ G₀ = 1 := by rw [map_mul, map_inv, map_pow, hX, one_pow, inv_one, one_mul, hY]
  have hG₀K := (hψ G₀).2 ⟨hG₀ψ, u₁, h1, hG₀u⟩
  have hact : ∀ w, Γ.Adj α w → (s * t) • w = x ^ j • w := by
    intro w hw
    have := mem_nbrStab.1 hG₀K w hw
    have e : ((x ^ j)⁻¹ * (s * t)) • w = w := this
    rw [mul_smul, inv_smul_eq_iff] at e
    exact e
  have hact_pow : ∀ k : ℕ, ∀ w, Γ.Adj α w → (s * t) ^ k • w = (x ^ j) ^ k • w := by
    intro k
    induction k with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      rw [pow_succ, pow_succ, mul_smul ((s * t) ^ k) (s * t) w, hact w hw,
        mul_smul ((x ^ j) ^ k) (x ^ j) w]
      exact ih _ (F.adj_smul_of_mem_stabilizer hxj hw)
  have hfin := F.loc_finite α
  have hpos : 0 < orderOf (s * t) := by
    have := orderOf_pos (S * T')
    rwa [← Subgroup.orderOf_coe] at this
  have hxjn : (x ^ j) ^ orderOf (s * t) ∈ nbrStab Γ G α := by
    refine mem_nbrStab.2 fun w hw => ?_
    rw [← hact_pow _ w hw, pow_orderOf_eq_one, one_smul]
  have hdvd5 : 5 ∣ j * orderOf (s * t) := by
    have hker : (⟨(x ^ j) ^ orderOf (s * t), pow_mem hxj _⟩ : MulAction.stabilizer G α) ∈
        (F.localHom α).ker := (F.mem_ker_localHom α _).2 hxjn
    have h1' : (F.localHom α X) ^ (j * orderOf (s * t)) = 1 := by
      have e : (⟨(x ^ j) ^ orderOf (s * t), pow_mem hxj _⟩ : MulAction.stabilizer G α) =
          X ^ (j * orderOf (s * t)) := Subtype.ext (by simp [X, pow_mul])
      rw [e] at hker
      simpa [map_pow] using hker
    have := orderOf_dvd_of_pow_eq_one h1'
    rwa [F.orderOf_localHom hx hxo, h5] at this
  have hj5 : ¬ 5 ∣ j := by
    intro hd
    obtain ⟨k, rfl⟩ := hd
    apply hYfix u₁ h1
    rw [← hj, pow_mul, hxp, one_pow, one_smul]
  have hn5 : 5 ∣ orderOf (s * t) :=
    ((Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).1 hdvd5).resolve_left hj5
  obtain ⟨k, hk⟩ := hn5
  have hk0 : 0 < k := by omega
  refine ⟨(s * t) ^ k, pow_mem (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))) k, ?_⟩
  rw [orderOf_pow_of_dvd (by omega) ⟨5, by omega⟩, hk]
  exact Nat.mul_div_cancel 5 hk0

end P71

end CFSG.Quasithin.Fan86
