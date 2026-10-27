module

public import CFSG.Quasithin.Recognition.St84.Sec7Setup

import CFSG.Quasithin.Recognition.St84.Gen.Sec6LeafGen

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable (X : Setup Γ G)

private theorem exists_adj_ne_two (i : ℤ) :
    ∃ ω : V, Γ.Adj (X.vert i) ω ∧ ω ≠ X.vert (i - 1) ∧ ω ≠ X.vert (i + 1) := by
  classical
  have hleft : Γ.Adj (X.vert i) (X.vert (i - 1)) := by
    have h := (X.adj (i - 1)).symm
    rwa [show i - 1 + 1 = i by omega] at h
  have hne : X.vert (i - 1) ≠ X.vert (i + 1) := by
    intro h
    have := X.vert_injective h
    omega
  have hcard := ncard_neighborSet_diff_two X.hyp hleft (X.adj i) hne
  have hfin : (Γ.neighborSet (X.vert i) \ {X.vert (i - 1), X.vert (i + 1)}).Finite :=
    (X.hyp.finite_neighborSet (X.vert i)).sdiff
  have hn1 : 1 ≤ X.n i := (X.hyp.valency (X.vert i)).1
  have hpos : 0 < (Γ.neighborSet (X.vert i) \ {X.vert (i - 1), X.vert (i + 1)}).ncard := by
    rw [show (Γ.neighborSet (X.vert i) \ {X.vert (i - 1), X.vert (i + 1)}).ncard =
      2 ^ X.n i - 1 from hcard]
    exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  obtain ⟨ω, hω⟩ := (Set.ncard_pos hfin).mp hpos
  refine ⟨ω, ?_, ?_, ?_⟩
  · have hω' : ω ∈ Γ.neighborSet (X.vert i) := hω.1
    rwa [SimpleGraph.mem_neighborSet] at hω'
  · intro h
    exact hω.2 (by simp [h])
  · intro h
    exact hω.2 (by simp [h])

theorem isCyclic_Ki (i : ℤ) : IsCyclic ↥(X.Ki i) := by
  classical
  obtain ⟨S, K', -, hKmap, hKS, hsup⟩ := X.exists_torusSylow i
  have hN : IsLocL2 Γ G (X.vert i) (X.n i) (X.L i) := X.hyp.isLocL2_oTwoPrime (X.vert i)
  have hcyc := hN.torus_cyclic X.hyp.adj_smul (X.hyp.finite_stab (X.vert i))
    (X.hyp.valency (X.vert i)).2 (X.hyp.valency (X.vert i)).1 S K' hKS hsup
  haveI : IsCyclic K' := hcyc.1
  rw [show X.Ki i = K'.map (X.L i).subtype from hKmap.symm]
  exact isCyclic_of_surjective
    (Subgroup.equivMapOfInjective K' (X.L i).subtype (X.L i).subtype_injective)
    (Subgroup.equivMapOfInjective K' (X.L i).subtype (X.L i).subtype_injective).surjective

theorem Ki_mul_comm_gen (i : ℤ) {a b : G} (ha : a ∈ X.Ki i) (hb : b ∈ X.Ki i) :
    a * b = b * a := by
  haveI : IsCyclic ↥(X.Ki i) := X.isCyclic_Ki i
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(X.Ki i)) ⟨b, hb⟩)

theorem exists_Ki_smul_eq_of_commute (i : ℤ) {k : G} (hk : k ∈ X.Gi i)
    (hk₁ : k • X.vert (i - 1) = X.vert (i - 1))
    (hk₂ : k • X.vert (i + 1) = X.vert (i + 1))
    (hcomm : ∀ c ∈ X.Ki i, ∀ w : V, Γ.Adj (X.vert i) w → (k * c) • w = (c * k) • w) :
    ∃ c ∈ X.Ki i, ∀ w : V, Γ.Adj (X.vert i) w → c • w = k • w := by
  classical
  obtain ⟨ω₀, hω₀adj, hω₀1, hω₀2⟩ := X.exists_adj_ne_two i
  have hkfix : k • X.vert i = X.vert i := MulAction.mem_stabilizer_iff.mp hk
  have hkadj : Γ.Adj (X.vert i) (k • ω₀) := by
    rw [← hkfix]
    exact (X.hyp.adj_smul k (X.vert i) ω₀).mpr hω₀adj
  have hkinv1 : k⁻¹ • X.vert (i - 1) = X.vert (i - 1) := by
    simpa using congrArg (fun x => k⁻¹ • x) hk₁.symm
  have hkinv2 : k⁻¹ • X.vert (i + 1) = X.vert (i + 1) := by
    simpa using congrArg (fun x => k⁻¹ • x) hk₂.symm
  have hkω1 : k • ω₀ ≠ X.vert (i - 1) := by
    intro h
    apply hω₀1
    have h' := congrArg (fun x => k⁻¹ • x) h
    rwa [inv_smul_smul, hkinv1] at h'
  have hkω2 : k • ω₀ ≠ X.vert (i + 1) := by
    intro h
    apply hω₀2
    have h' := congrArg (fun x => k⁻¹ • x) h
    rwa [inv_smul_smul, hkinv2] at h'
  obtain ⟨c₀, hc₀Ki, hc₀⟩ :=
    X.Ki_transitive_gen i hω₀adj hkadj hω₀1 hω₀2 hkω1 hkω2
  refine ⟨c₀, hc₀Ki, ?_⟩
  intro w hw
  by_cases hw1 : w = X.vert (i - 1)
  · subst w
    rw [X.K_fix c₀ hc₀Ki.1 (i - 1), hk₁]
  by_cases hw2 : w = X.vert (i + 1)
  · subst w
    rw [X.K_fix c₀ hc₀Ki.1 (i + 1), hk₂]
  obtain ⟨c, hcKi, hc⟩ := X.Ki_transitive_gen i hω₀adj hw hω₀1 hω₀2 hw1 hw2
  calc
    c₀ • w = c₀ • (c • ω₀) := by rw [hc]
    _ = (c₀ * c) • ω₀ := by rw [mul_smul]
    _ = (c * c₀) • ω₀ := by rw [X.Ki_mul_comm_gen i hcKi hc₀Ki]
    _ = c • (c₀ • ω₀) := by rw [mul_smul]
    _ = c • (k • ω₀) := by rw [hc₀]
    _ = (c * k) • ω₀ := by rw [mul_smul]
    _ = (k * c) • ω₀ := by rw [hcomm c hcKi ω₀ hω₀adj]
    _ = k • (c • ω₀) := by rw [mul_smul]
    _ = k • w := by rw [hc]

theorem Ki_inf_fixSet (i : ℤ) :
    X.Ki i ⊓ fixSet G (Γ.neighborSet (X.vert i)) = ⊥ := by
  classical
  by_cases hn : 2 ≤ X.n i
  · refine le_bot_iff.mp ?_
    intro c hc
    obtain ⟨hcKi, hcFix⟩ := Subgroup.mem_inf.mp hc
    by_contra hc1
    obtain ⟨ω, hωadj, hω1, hω2⟩ := X.exists_adj_ne_two i
    have hfix : c • ω = ω :=
      (Fan86.mem_fixSet.mp hcFix) ω (by rwa [SimpleGraph.mem_neighborSet])
    obtain h | h := (X.torus_fixed i hn hcKi hc1 ω hωadj).mp hfix
    · exact hω1 h
    · exact hω2 h
  · have hn1 : X.n i = 1 := by
      have h1 : 1 ≤ X.n i := (X.hyp.valency (X.vert i)).1
      have h2 : X.n i < 2 := Nat.lt_of_not_ge hn
      omega
    have hcard : Nat.card ↥(X.Ki i) = 1 := by
      rw [X.card_Ki i, hn1]
      norm_num
    have hbot : X.Ki i = ⊥ := Subgroup.eq_bot_of_card_eq (X.Ki i) hcard
    rw [hbot]
    simp

theorem exists_Ki_smul_eq_of_mem_K (hK : ∀ a ∈ X.K, ∀ b ∈ X.K, a * b = b * a) (i : ℤ)
    {k : G} (hk : k ∈ X.K) :
    ∃ c ∈ X.Ki i, ∀ w : V, Γ.Adj (X.vert i) w → c • w = k • w := by
  refine X.exists_Ki_smul_eq_of_commute i (X.K_le_Gi i hk) (X.K_fix k hk (i - 1))
    (X.K_fix k hk (i + 1)) ?_
  intro c hc w _
  rw [hK k hk c hc.1]

theorem card_K_eq_mul (hK : ∀ a ∈ X.K, ∀ b ∈ X.K, a * b = b * a) (i : ℤ) :
    Nat.card ↥X.K = (2 ^ X.n i - 1) *
      Nat.card ↥(X.K ⊓ fixSet G (Γ.neighborSet (X.vert i))) := by
  classical
  set N : Subgroup G := X.K ⊓ fixSet G (Γ.neighborSet (X.vert i)) with hN
  have hNle : N ≤ X.K := inf_le_left
  have hKiN : X.Ki i ⊓ N = ⊥ := by
    refine le_bot_iff.mp ?_
    calc X.Ki i ⊓ N ≤ X.Ki i ⊓ fixSet G (Γ.neighborSet (X.vert i)) :=
          inf_le_inf le_rfl inf_le_right
      _ = ⊥ := X.Ki_inf_fixSet i
  have hmul_mem : ∀ c : ↥(X.Ki i), ∀ d : ↥N, (c : G) * (d : G) ∈ X.K :=
    fun c d => X.K.mul_mem c.2.1 d.2.1
  let f : ↥(X.Ki i) × ↥N → ↥X.K := fun x =>
    ⟨(x.1 : G) * (x.2 : G), hmul_mem x.1 x.2⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨c₁, d₁⟩ ⟨c₂, d₂⟩ h
    have h' : (c₁ : G) * (d₁ : G) = (c₂ : G) * (d₂ : G) := congrArg Subtype.val h
    have heq : (c₂ : G)⁻¹ * (c₁ : G) = (d₂ : G) * (d₁ : G)⁻¹ := by
      calc (c₂ : G)⁻¹ * (c₁ : G)
          = (c₂ : G)⁻¹ * ((c₁ : G) * (d₁ : G)) * (d₁ : G)⁻¹ := by group
        _ = (c₂ : G)⁻¹ * ((c₂ : G) * (d₂ : G)) * (d₁ : G)⁻¹ := by rw [h']
        _ = (d₂ : G) * (d₁ : G)⁻¹ := by group
    have hmem : (c₂ : G)⁻¹ * (c₁ : G) ∈ X.Ki i ⊓ N := by
      refine ⟨(X.Ki i).mul_mem ((X.Ki i).inv_mem c₂.2) c₁.2, ?_⟩
      rw [heq]
      exact N.mul_mem d₂.2 (N.inv_mem d₁.2)
    rw [hKiN, Subgroup.mem_bot] at hmem
    have hc : (c₁ : G) = (c₂ : G) := (inv_mul_eq_one.mp hmem).symm
    have hd : (d₁ : G) = (d₂ : G) := by
      rw [hc] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext hc) (Subtype.ext hd)
  have hf_surj : Function.Surjective f := by
    intro k
    obtain ⟨c, hcKi, hc⟩ := X.exists_Ki_smul_eq_of_mem_K hK i k.2
    refine ⟨(⟨c, hcKi⟩, ⟨c⁻¹ * (k : G), ?_⟩), ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨X.K.mul_mem (X.K.inv_mem hcKi.1) k.2, ?_⟩
      rw [Fan86.mem_fixSet]
      intro w hw
      show (c⁻¹ * (k : G)) • w = w
      rw [mul_smul, ← hc w hw, inv_smul_smul]
    · apply Subtype.ext
      exact mul_inv_cancel_left c (k : G)
  have hcard : Nat.card (↥(X.Ki i) × ↥N) = Nat.card ↥X.K :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  calc Nat.card ↥X.K = Nat.card (↥(X.Ki i) × ↥N) := hcard.symm
    _ = Nat.card ↥(X.Ki i) * Nat.card ↥N := Nat.card_prod _ _
    _ = (2 ^ X.n i - 1) * Nat.card ↥N := by rw [X.card_Ki i]

end Setup

end CFSG.Quasithin.St84
