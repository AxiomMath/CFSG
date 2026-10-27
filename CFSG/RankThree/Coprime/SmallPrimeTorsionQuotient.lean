module

public import CFSG.RankThree.PGroups.RankTwoTorsionExponent

public section

namespace CFSG.RankThree.Coprime

open Subgroup CFSG
open scoped commutatorElement

universe u

section Omega

variable {A B : Type*} [Group A] [Group B] {p : ℕ}

theorem map_omega₁_le (f : A →* B) :
    (omega₁ A (p := p)).map f ≤ omega₁ B (p := p) := by
  rw [omega₁, omega, omega₁, omega, MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨x, hx, rfl⟩
  change f x ^ (p ^ 1) = 1
  rw [← map_pow, show x ^ (p ^ 1) = 1 from hx, map_one]

theorem card_omega₁_le_of_injective [Finite B] (f : A →* B) (hf : Function.Injective f) :
    Nat.card (omega₁ A (p := p)) ≤ Nat.card (omega₁ B (p := p)) := by
  rw [← Subgroup.card_map_of_injective hf]
  exact Subgroup.card_le_of_le (map_omega₁_le f)

theorem card_omega₁_eq_of_mulEquiv [Finite A] [Finite B] (e : A ≃* B) :
    Nat.card (omega₁ A (p := p)) = Nat.card (omega₁ B (p := p)) :=
  le_antisymm (card_omega₁_le_of_injective e.toMonoidHom e.injective)
    (card_omega₁_le_of_injective e.symm.toMonoidHom e.symm.injective)

omit [Group B] in
theorem omega₁_eq_top_of_pow_eq_one (h : ∀ x : A, x ^ p = 1) : omega₁ A (p := p) = ⊤ := by
  rw [eq_top_iff, omega₁, omega]
  intro x _
  exact subset_closure (by simpa using h x)

end Omega

theorem pow_eq_one_and_card_eq_of_minimal_torsion {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {R : Type*} [Group R] [Finite R] (hR : IsPGroup p R)
    (hΩ : p ^ 2 < Nat.card (omega₁ R (p := p)))
    (hsub : ∀ V : Subgroup R, V ≠ ⊤ → Nat.card (omega₁ V (p := p)) ≤ p ^ 2) :
    (∀ x : R, x ^ p = 1) ∧ Nat.card R = p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have key : ∀ V : Subgroup R, (∀ x ∈ V, x ^ p = 1) → p ^ 2 < Nat.card V → V = ⊤ := by
    intro V hV hcard
    by_contra hne
    have h1 := hsub V hne
    rw [omega₁_eq_top_of_pow_eq_one (fun x : V => Subtype.ext (by simpa using hV x x.2)),
      Subgroup.card_top] at h1
    omega
  by_cases hrank : pRank p R ≤ 2
  · obtain ⟨-, hS, hScard⟩ :=
      CFSG.RankThree.PGroups.rank_two_large_prime_torsion_exponent hp hp3 hR hrank
    have htop := key _ hS hΩ
    refine ⟨fun x => hS x (htop ▸ mem_top x), ?_⟩
    rw [← Subgroup.card_top (G := R), ← htop]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hR.to_subgroup (omega₁ R (p := p)))
    rw [hk] at hΩ hScard ⊢
    have h1 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hΩ
    have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hScard
    rw [show k = 3 by omega]
  · rw [not_le] at hrank
    obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup R)
    have hrank' : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup R) := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
      omega
    have h3 : p ^ 3 ∣ Nat.card E := by
      rw [hEcard]
      exact Nat.pow_dvd_pow p hrank'
    obtain ⟨E3, hE3⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p h3
    set F := E3.map E.subtype with hF
    have hFp : ∀ x ∈ F, x ^ p = 1 := by
      rintro _ ⟨x, -, rfl⟩
      exact hE.2 x x.2
    have hFcard : Nat.card F = p ^ 3 := by
      rw [hF, Subgroup.card_map_of_injective E.subtype_injective, hE3]
    have htop := key F hFp (by
      rw [hFcard]
      exact Nat.pow_lt_pow_right hp.one_lt (by norm_num))
    exact ⟨fun x => hFp x (htop ▸ mem_top x),
      by rw [← Subgroup.card_top (G := R), ← htop, hFcard]⟩

theorem false_of_small_torsion_central_quotient {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {P : Type u} [Group P] [Finite P] (hP : IsPGroup p P)
    (hΩ : Nat.card (omega₁ P (p := p)) ≤ p ^ 2) (T : Subgroup P) [T.Normal]
    (hTcard : Nat.card T = p) (hRexp : ∀ x : P ⧸ T, x ^ p = 1)
    (hRcard : Nat.card (P ⧸ T) = p ^ 3) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hp1 := hp.one_lt
  have hPcard : Nat.card P = p ^ 4 := by
    rw [T.card_eq_card_quotient_mul_card_subgroup, hRcard, hTcard]
    ring
  have hnc : ¬ IsCyclic P := by
    intro hcyc
    have : IsCyclic (P ⧸ T) :=
      isCyclic_of_surjective (QuotientGroup.mk' T) (QuotientGroup.mk'_surjective T)
    have h2 : Monoid.exponent (P ⧸ T) ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one hRexp
    rw [IsCyclic.exponent_eq_card, hRcard] at h2
    have h3 := Nat.le_of_dvd hp.pos h2
    have h4 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp1 (by norm_num)
    rw [pow_one] at h4
    omega
  have : Fact (IsPGroup p P) := ⟨hP⟩
  obtain ⟨B, -, hBcard, hB⟩ := CFSG.lemma_4_5_a (by omega : p ≠ 2) hnc
  set Ω := omega₁ P (p := p) with hΩdef
  have hBΩ : B ≤ Ω := by
    have := hB
    exact elementaryAbelian_le_omega₁
  have hΩcard : Nat.card Ω = p ^ 2 := le_antisymm hΩ (hBcard ▸ Subgroup.card_le_of_le hBΩ)
  have : Ω.Characteristic := omega₁_characteristic P
  have hQcard : Nat.card (P ⧸ Ω) = p ^ 2 := by
    have h := Ω.card_eq_card_quotient_mul_card_subgroup
    rw [hPcard, hΩcard] at h
    have h' : Nat.card (P ⧸ Ω) * p ^ 2 = p ^ 2 * p ^ 2 := by rw [← h]; ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h'
  have := IsPGroup.isMulCommutative_of_card_eq_prime_sq hQcard
  have hcomm : commutator P ≤ Ω := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have h1 : (QuotientGroup.mk' Ω) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm' _ _
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hγ : (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥ :=
    CFSG.RankThree.lowerCentralSeries_three_eq_bot_of_card_le_pow_four hP hPcard.le
  obtain ⟨hset, -, hθ⟩ :=
    CFSG.RankThree.omega_one_eq_torsion_and_powHom_of_class_three hp hp3 hP hγ
  obtain ⟨θ, hθx⟩ := hθ hcomm
  have hθx' : ∀ x, θ x = x ^ p := fun x => congrFun hθx x
  have hker : θ.ker = Ω := by
    ext x
    rw [MonoidHom.mem_ker, hθx', ← SetLike.mem_coe, hset]
    rfl
  have hrange : θ.range ≤ T := by
    rintro _ ⟨x, rfl⟩
    rw [hθx']
    have h := hRexp (x : P ⧸ T)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
    exact h
  have h1 : Nat.card (P ⧸ θ.ker) = Nat.card θ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv
  rw [hker, hQcard] at h1
  have h2 := Subgroup.card_le_of_le hrange
  rw [← h1, hTcard] at h2
  have h3 : p < p ^ 2 := by nlinarith
  omega


theorem small_prime_torsion_quotient_bound {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {P : Type u} [Group P] [Finite P] (hP : IsPGroup p P)
    (hΩ : Nat.card (omega₁ P (p := p)) ≤ p ^ 2) (N : Subgroup P) [N.Normal] :
    Nat.card (omega₁ (P ⧸ N) (p := p)) ≤ p ^ 2 := by
  suffices key : ∀ (n : ℕ) (P : Type u) [Group P] [Finite P], Nat.card P = n → IsPGroup p P →
      Nat.card (omega₁ P (p := p)) ≤ p ^ 2 → ∀ N : Subgroup P, [N.Normal] →
        Nat.card (omega₁ (P ⧸ N) (p := p)) ≤ p ^ 2 from key _ P rfl hP hΩ N
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P _ _ hn hP hΩ N hN
  have : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨N₀, -, hN₀⟩ := Finite.exists_le_minimal
    (p := fun M : Subgroup P => ∃ _ : M.Normal, p ^ 2 < Nat.card (omega₁ (P ⧸ M) (p := p)))
    (a := N) ⟨hN, hcon⟩
  obtain ⟨hN₀n, hN₀c⟩ := hN₀.prop
  have := hN₀n
  have hN₀bot : N₀ ≠ ⊥ := by
    rintro rfl
    have h := card_omega₁_eq_of_mulEquiv (p := p) (QuotientGroup.quotientBot (G := P))
    omega
  obtain ⟨hdvd, -⟩ := CFSG.SectionRank.Ccomm.normal_inf_center_card hP hN₀bot
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set T := zpowers (t : P) with hT
  have hTZ : T ≤ N₀ ⊓ center P := zpowers_le.mpr t.2
  have hTN₀ : T ≤ N₀ := hTZ.trans inf_le_left
  have : T.Normal := Subgroup.normal_of_le_center (hTZ.trans inf_le_right)
  have hTcard : Nat.card T = p := by rw [hT, Nat.card_zpowers, Subgroup.orderOf_coe, ht]
  have hRlt : Nat.card (P ⧸ T) < n := by
    rw [← hn, T.card_eq_card_quotient_mul_card_subgroup, hTcard]
    have : 0 < Nat.card (P ⧸ T) := Nat.card_pos
    nlinarith [hp.one_lt]
  by_cases hTeq : T = N₀
  ·
    have hRc : p ^ 2 < Nat.card (omega₁ (P ⧸ T) (p := p)) := by
      rwa [card_omega₁_eq_of_mulEquiv (p := p) (QuotientGroup.quotientMulEquivOfEq hTeq)]
    have hsub : ∀ V : Subgroup (P ⧸ T), V ≠ ⊤ → Nat.card (omega₁ V (p := p)) ≤ p ^ 2 := by
      intro V hV
      set U := V.comap (QuotientGroup.mk' T) with hU
      have hUlt : U < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro h
        apply hV
        rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective T) V, ← hU,
          h, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective T)]
      have hUcard : Nat.card U < n := by
        rw [← hn, ← Subgroup.card_top (G := P)]
        exact Subgroup.card_lt_of_lt hUlt
      have hUΩ : Nat.card (omega₁ U (p := p)) ≤ p ^ 2 :=
        (card_omega₁_le_of_injective U.subtype U.subtype_injective).trans hΩ
      have : (T.subgroupOf U).Normal := Subgroup.normal_subgroupOf
      have h := ih _ hUcard U rfl (hP.to_subgroup U) hUΩ (T.subgroupOf U)
      rw [card_omega₁_eq_of_mulEquiv (p := p) (CFSG.quotientSubgroupRangeEquiv U T)] at h
      have hmap : U.map (QuotientGroup.mk' T) = V :=
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective T) V
      rwa [card_omega₁_eq_of_mulEquiv (p := p) (MulEquiv.subgroupCongr hmap)] at h
    obtain ⟨hRexp, hRcard⟩ := pow_eq_one_and_card_eq_of_minimal_torsion hp hp3
      (hP.to_quotient T) hRc hsub
    exact false_of_small_torsion_central_quotient hp hp3 hP hΩ T hTcard hRexp hRcard
  ·
    have hΩT : Nat.card (omega₁ (P ⧸ T) (p := p)) ≤ p ^ 2 := by
      by_contra h
      rw [not_le] at h
      exact hTeq (le_antisymm hTN₀ (hN₀.le_of_le ⟨inferInstance, h⟩ hTN₀))
    have : (N₀.map (QuotientGroup.mk' T)).Normal :=
      hN₀n.map _ (QuotientGroup.mk'_surjective T)
    have h := ih _ hRlt (P ⧸ T) rfl (hP.to_quotient T) hΩT (N₀.map (QuotientGroup.mk' T))
    rw [card_omega₁_eq_of_mulEquiv (p := p)
      (QuotientGroup.quotientQuotientEquivQuotient T N₀ hTN₀)] at h
    omega

end CFSG.RankThree.Coprime
