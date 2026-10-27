module

public import CFSG.Quasithin.EmptyFaithful.S153EB6I
public import CFSG.Quasithin.EmptyFaithful.S153EB6G

public section

namespace CFSG.Quasithin

namespace S153EB6

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

structure ModelFacts (V : Type) [CommGroup V] (G Kb : Subgroup (MulAut V)) (a : MulAut V) : Prop where
  fix3 : ∀ p : V, ∃ g ∈ G, orderOf g = 3 ∧ g p = p
  simple : ∀ M : Subgroup (MulAut V), M ≤ Kb → (∀ k ∈ Kb, ∀ m ∈ M, k * m * k⁻¹ ∈ M) → M ≠ ⊥ → M = Kb
  case : (G = ⊤ ∧ Nat.card V = 8 ∧ Kb = G) ∨ ∃ g ∈ G, orderOf g = 3 ∧ g * a = a * g

section Lift

variable {W : Type} [CommGroup W] {H K : Subgroup (MulAut W)} {a : MulAut W} {U : Subgroup W}

@[expose] noncomputable def indResK (hC : Ctx H K a) (hS : SumCtx K a U) : ↥K →* MulAut ↥U :=
  (indRes hC hS).comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Subgroup.zpowers a))

theorem indResK_eq_one_iff (hC : Ctx H K a) (hS : SumCtx K a U) {k : ↥K} :
    indResK hC hS k = 1 ↔ ∀ u ∈ U, (k : MulAut W) u = u :=
  resX_eq_one_iff (hC.le_stab hS)

theorem mem_indK_iff (hC : Ctx H K a) (hS : SumCtx K a U) {g : MulAut ↥U} :
    g ∈ indK hC hS ↔ ∃ k : ↥K, indResK hC hS k = g := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨Subgroup.inclusion le_sup_left k, k.2, rfl⟩

end Lift

section UseA

variable {W : Type} [CommGroup W] {H K : Subgroup (MulAut W)} {a : MulAut W}

theorem mem_Kb_of_order_three {V : Type} [CommGroup V] {G Kb : Subgroup (MulAut V)} {a : MulAut V}
    (hI : Induced V G Kb a) {g : MulAut V} (hg : g ∈ G) (hg3 : orderOf g = 3) : g ∈ Kb := by
  have h3 : g ^ 3 = 1 := by rw [← hg3]; exact pow_orderOf_eq_one g
  have h1 : (g ^ 2) ^ 2 = g := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h3, one_mul]
  rw [← h1]
  exact Kb.pow_mem (hI.sq g hg) 2

theorem Nk_eq_bot_of_model (hC : Ctx H K a) {W₁ W₂ : Subgroup W} (hsup : W₁ ⊔ W₂ = ⊤)
    (hS₁ : SumCtx K a W₁) (hS₂ : SumCtx K a W₂)
    (hI₂ : Induced ↥W₂ (indG hC hS₂) (indK hC hS₂) (indA hC hS₂))
    (hMF₂ : ModelFacts ↥W₂ (indG hC hS₂) (indK hC hS₂) (indA hC hS₂))
    (h3 : ∀ h ∈ H, orderOf h = 3 →
      ∃ r ∈ commV (Subgroup.zpowers a), h r ∉ commV (Subgroup.zpowers a)) :
    ∀ n ∈ Nk K W₁, n = 1 := by
  intro n₀ hn₀
  by_contra hn₀1
  set ρ := indResK hC hS₂ with hρ
  let M : Subgroup (MulAut ↥W₂) := ((Nk K W₁).subgroupOf K).map ρ
  have hMK : M ≤ indK hC hS₂ := by
    rintro _ ⟨n, -, rfl⟩
    exact (mem_indK_iff hC hS₂).2 ⟨n, rfl⟩
  have hMnorm : ∀ k ∈ indK hC hS₂, ∀ m ∈ M, k * m * k⁻¹ ∈ M := by
    intro g hg m hm
    obtain ⟨k₁, rfl⟩ := (mem_indK_iff hC hS₂).1 hg
    obtain ⟨n, hn, rfl⟩ := hm
    refine ⟨k₁ * n * k₁⁻¹, Nk_conj_mem hS₁.KU k₁.2 hn, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hMne : M ≠ ⊥ := by
    intro hbot
    have : ρ ⟨n₀, hn₀.1⟩ ∈ M := ⟨⟨n₀, hn₀.1⟩, hn₀, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    have h2 := (indResK_eq_one_iff hC hS₂).1 this
    exact hn₀1 (Nk_inf_eq_bot hsup hn₀ ⟨hn₀.1, h2⟩)
  have hMeq : M = indK hC hS₂ := hMF₂.simple M hMK hMnorm hMne
  obtain ⟨p, hp⟩ : ∃ p : ↥W₂, ∀ w ∈ commV (Subgroup.zpowers (indA hC hS₂)), w = 1 ∨ w = p := by
    obtain ⟨y, hy1, hyu⟩ :=
      (Nat.card_eq_two_iff' (1 : ↥(commV (Subgroup.zpowers (indA hC hS₂))))).1 hI₂.card
    refine ⟨(y : ↥W₂), fun w hw => ?_⟩
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (congrArg Subtype.val (hyu ⟨w, hw⟩ (fun h' => hw1 (congrArg Subtype.val h'))))
  obtain ⟨g, hgG, hg3, hgp⟩ := hMF₂.fix3 p
  have hgK : g ∈ indK hC hS₂ := mem_Kb_of_order_three hI₂ hgG hg3
  rw [← hMeq] at hgK
  obtain ⟨n, hn, hng⟩ := hgK
  have hn'N : (n : MulAut W) ∈ Nk K W₁ := hn
  have hn'H : (n : MulAut W) ∈ H := hC.KH n.2
  have hgpow : g ^ 3 = 1 := by rw [← hg3]; exact pow_orderOf_eq_one g
  have hn'3 : orderOf (n : MulAut W) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h1 : n ^ 3 = 1 := by
      have h2 : ρ (n ^ 3) = 1 := by rw [map_pow, hng, hgpow]
      have h4 := (indResK_eq_one_iff hC hS₂).1 h2
      apply Subtype.ext
      refine Nk_inf_eq_bot hsup (K := K) (x := ((n ^ 3 : ↥K) : MulAut W)) ?_ ⟨(n ^ 3).2, h4⟩
      exact (Nk K W₁).pow_mem hn'N 3
    refine orderOf_eq_prime (by simpa using congrArg Subtype.val h1) ?_
    intro h1'
    have : n = 1 := Subtype.ext h1'
    rw [this, map_one] at hng
    rw [← hng, orderOf_one] at hg3
    omega
  have hfix₁ : ∀ r ∈ commIn153 (Subgroup.zpowers a) W₁, (n : MulAut W) r = r := fun r hr =>
    hn'N.2 r (commIn_le hC.a2 hS₁.aU hr)
  have hfix₂ : ∀ r ∈ commIn153 (Subgroup.zpowers a) W₂, (n : MulAut W) r = r := by
    intro r hr
    rw [← map_commV_indA hC hS₂] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    have hgq : g q = q := by
      rcases hp q hq with rfl | rfl
      · exact map_one g
      · exact hgp
    have := congrArg (fun x : ↥W₂ => (x : W)) hgq
    rw [← hng] at this
    exact this
  have hF : commV (Subgroup.zpowers a) ≤ fixV (Subgroup.zpowers (n : MulAut W)) := by
    refine (commV_le_sup hsup hC.a2 hS₁.aU hS₂.aU).trans (sup_le (fun r hr => ?_) (fun r hr => ?_))
    · exact G64.fixV_zpowers_iff.2 (hfix₁ r hr)
    · exact G64.fixV_zpowers_iff.2 (hfix₂ r hr)
  obtain ⟨r, hr, hnr⟩ := h3 _ hn'H hn'3
  exact hnr (by rw [G64.fixV_zpowers_iff.1 (hF hr)]; exact hr)

end UseA

end S153EB6

end CFSG.Quasithin
