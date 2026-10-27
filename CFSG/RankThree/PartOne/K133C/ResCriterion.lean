module

public import CFSG.RankThree.PartOne.K133C.Transport
public import CFSG.RankThree.PartOne.K133C.InnerPlane

public section

namespace CFSG.RankThree.PartOne.K133C

open CFSG CFSG.RankThree.PartOne.K133 CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def RadAut (X : Type) [Group X] : Prop :=
  ∀ u : X, orderOf u = 2 → ∃ R : Subgroup (MulAut X), R ≤ inner X ∧ IsPGroup 2 R ∧
    (∀ β ∈ Subgroup.centralizer ({MulAut.conj u} : Set (MulAut X)),
      β ∈ Subgroup.normalizer (R : Set (MulAut X))) ∧
    IsPGroup 2 (Subgroup.centralizer (R : Set (MulAut X)))

theorem goodResV_of_radAut {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : Subgroup.center X = ⊥) (h : RadAut X) : GoodResV p X := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro Ē hE hEc hR
  obtain ⟨C, hCĒ, hCc, Kb, -, -, -, ⟨V, hVK, hVel, hVc⟩, hfix⟩ := hR
  have hcinj := conj_injective_of_center_bot hZ
  have hVne : V ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hVc
    omega
  obtain ⟨u, huV, hu1⟩ : ∃ u ∈ V, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hVne ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hu2 : orderOf u = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (A := V) u huV) hu1
  obtain ⟨R, hRinn, hR2, hnorm, hcent⟩ := h u hu2
  set S : Subgroup X := R.comap (MulAut.conj : X →* MulAut X) with hSdef
  have hS2 : IsPGroup 2 S := by
    intro x
    obtain ⟨k, hk⟩ := hR2 ⟨MulAut.conj (x : X), x.2⟩
    refine ⟨k, Subtype.ext (hcinj ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hfixu : ∀ φ ∈ C, φ u = u := fun φ hφ => hfix φ hφ u (hVK huV)
  have hcomm : ∀ φ ∈ C, φ ∈ Subgroup.centralizer ({MulAut.conj u} : Set (MulAut X)) := by
    intro φ hφ
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := conj_map_aut φ u
    rw [hfixu φ hφ] at h1
    calc φ * MulAut.conj u = (φ * MulAut.conj u * φ⁻¹) * φ := by group
      _ = MulAut.conj u * φ := by rw [← h1]
  have hstab : ∀ φ ∈ C, ∀ s ∈ S, φ s ∈ S := by
    intro φ hφ s hs
    have hn := (Subgroup.mem_normalizer_iff.1 (hnorm φ (hcomm φ hφ)) (MulAut.conj s)).1 hs
    show MulAut.conj (φ s) ∈ R
    rw [conj_map_aut]
    exact hn
  have hCne : C ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hCc
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  obtain ⟨φ, hφC, hφ1⟩ : ∃ φ ∈ C, φ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hCne ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hφp : φ ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (A := Ē) φ (hCĒ hφC)
  have hφord : orderOf φ = p := orderOf_eq_prime hφp hφ1
  have hmove : ∃ s ∈ S, φ s ≠ s := by
    by_contra hno
    push Not at hno
    have hφcent : φ ∈ Subgroup.centralizer (R : Set (MulAut X)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      obtain ⟨x, rfl⟩ := hRinn hr
      have hx : x ∈ S := hr
      have h1 := hno x hx
      have h2 := conj_map_aut φ x
      rw [h1] at h2
      calc MulAut.conj x * φ = (φ * MulAut.conj x * φ⁻¹) * φ := by rw [← h2]
        _ = φ * MulAut.conj x := by group
    obtain ⟨k, hk⟩ := hcent ⟨φ, hφcent⟩
    have hk' : φ ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hdvd : p ∣ 2 ^ k := hφord ▸ orderOf_dvd_of_pow_eq_one hk'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  obtain ⟨s, hsS, hsne⟩ := hmove
  exact Or.inr ⟨C, hCĒ, hCc, S, hS2, hstab, φ, hφC, s, hsS, hsne⟩


theorem RadAut.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : RadAut Y) : RadAut X := by
  intro u hu2
  have hu2' : orderOf (e u) = 2 := by
    have h1 : orderOf (e.toMonoidHom u) = orderOf u := orderOf_injective _ e.injective u
    rw [hu2] at h1
    exact h1
  obtain ⟨R, hRinn, hR2, hnorm, hcent⟩ := h (e u) hu2'
  set Ψ : MulAut X ≃* MulAut Y := MulAut.congr e with hΨ
  refine ⟨R.comap Ψ.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨y, hy⟩ := hRinn (show Ψ r ∈ R from hr)
    refine ⟨e.symm y, Ψ.injective ?_⟩
    rw [hΨ, congr_conj, MulEquiv.apply_symm_apply]
    exact hy
  · exact hR2.comap_of_injective Ψ.toMonoidHom Ψ.injective
  · intro β hβ
    have hβ' : Ψ β ∈ Subgroup.centralizer ({MulAut.conj (e u)} : Set (MulAut Y)) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hβ ⊢
      have := congrArg Ψ hβ
      rw [map_mul, map_mul, hΨ, congr_conj] at this
      exact this
    have hn := hnorm _ hβ'
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro x
    have := hn (Ψ x)
    show Ψ x ∈ R ↔ Ψ (β * x * β⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact this
  · intro x
    have hxc : Ψ (x : MulAut X) ∈ Subgroup.centralizer (R : Set (MulAut Y)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hr' : Ψ.symm r ∈ R.comap Ψ.toMonoidHom := by
        show Ψ (Ψ.symm r) ∈ R
        rw [MulEquiv.apply_symm_apply]
        exact hr
      have := Subgroup.mem_centralizer_iff.1 x.2 (Ψ.symm r) hr'
      have h2 := congrArg Ψ this
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2
    obtain ⟨k, hk⟩ := hcent ⟨Ψ x, hxc⟩
    have h1 : (Ψ (x : MulAut X)) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h2 : Ψ ((x : MulAut X) ^ (2 ^ k)) = 1 := by rw [map_pow]; exact h1
    have h3 : (x : MulAut X) ^ (2 ^ k) = 1 := Ψ.injective (by rw [h2, map_one])
    exact ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h3)⟩

end CFSG.RankThree.PartOne.K133C
