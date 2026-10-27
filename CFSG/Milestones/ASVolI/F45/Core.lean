module

public import CFSG.Milestones.ASVolI.F4Sylow
public import CFSG.Milestones.ASVolI.F45.D4
public import CFSG.Milestones.ASVolI.F4Reductions
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Polygon
import all CFSG.Milestones.ASVolI.F4Reductions

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

@[expose] def burnsideF45_LieFactsKind (κ : GLKind) : Prop :=
  ∀ (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (hyp : HypF_4_4 κ p f Gp M₁ M₂)
    (hp : p.Prime), (burnsideF45_setting hyp hp (burnsideF45_three_le_m κ)).Facts45L

@[expose] def burnsideF45_LieFactsAll : Prop :=
  ∀ κ : GLKind, κ.IsLie → burnsideF45_LieFactsKind κ

theorem burnsideF45_lieFactsAll_of_classical
    (hL3 : burnsideF45_LieFactsKind .L3) (hSp4 : burnsideF45_LieFactsKind .Sp4)
    (hU4 : burnsideF45_LieFactsKind .U4) (hU5 : burnsideF45_LieFactsKind .U5) :
    burnsideF45_LieFactsAll := by
  intro κ hκ
  cases κ
  · exact hL3
  · exact hSp4
  · exact fun p f E _ Gp M₁ M₂ hyp hp => burnsideF45_facts45L_G2 hyp hp _
  · exact fun p f E _ Gp M₁ M₂ hyp hp => burnsideF45_facts45L_D4tw hyp hp _
  · exact fun p f E _ Gp M₁ M₂ hyp hp => burnsideF45_facts45L_F4tw hyp hp _
  · exact hU4
  · exact hU5
  · exact absurd rfl hκ.1
  · exact absurd rfl hκ.2

theorem burnsideF45_p_eq_two {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ = .G2d ∨ κ = .Tits) : p = 2 := by
  rcases hκ with rfl | rfl
  · exact hyp.model.1
  · exact hyp.model.1

theorem burnsideF45_isLie_or (κ : GLKind) : κ.IsLie ∨ (κ = .G2d ∨ κ = .Tits) := by
  cases κ <;> simp [GLKind.IsLie]

section C1


theorem burnsideF45_C1 (hL : burnsideF45_LieFactsAll) {κ : GLKind} {p f : ℕ} {E : Type}
    [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) :
    IsGenPolygon (incl M₁ M₂).graph κ.m := by
  rcases burnsideF45_isLie_or κ with hκ | hκ
  · exact (hL κ hκ p f E Gp M₁ M₂ hyp (burnsideF4a_prime_of_isGenLie hyp.model)).poly
  · have hp := burnsideF45_p_eq_two hyp hκ
    subst hp
    exact burnsideF45_clause1_two κ f E Gp M₁ M₂ hyp

end C1

theorem burnsideF45_polygon_m_eq {V : Type*} {Γ : SimpleGraph V} {m m' : ℕ}
    (h : IsGenPolygon Γ m) (h' : IsGenPolygon Γ m') : m = m' := by
  obtain ⟨u, v, huv⟩ := h.diam_eq
  obtain ⟨u', v', huv'⟩ := h'.diam_eq
  have h1 := h'.diam_le u v
  have h2 := h.diam_le u' v'
  omega

theorem burnsideF45_relIndex_mod {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {H B P : Subgroup E} (hBP : B ≤ P) (hPH : P ≤ H)
    (hS : ∃ S : Subgroup E, ChF.IsSylowOf p S H ∧ B = H ⊓ Subgroup.normalizer (S : Set E)) :
    B.relIndex P % p = 1 := by
  obtain ⟨S, ⟨hSH, hSp, hSidx⟩, hB⟩ := hS
  haveI : Fact p.Prime := ⟨hp⟩
  have hSB : S ≤ B := by
    rw [hB]; exact le_inf hSH Subgroup.le_normalizer
  have hSP : S ≤ P := hSB.trans hBP
  have h1 : IsPGroup p (S.subgroupOf P) := hSp.comap_subtype
  have hdvd : S.relIndex P ∣ S.relIndex H :=
    ⟨P.relIndex H, (Subgroup.relIndex_mul_relIndex S P H hSP hPH).symm⟩
  have h2 : ¬ p ∣ (S.subgroupOf P).index := fun h => hSidx (h.trans hdvd)
  let T : Sylow p ↥P := h1.toSylow h2
  have hN : Subgroup.normalizer (T : Set ↥P) = B.subgroupOf P := by
    ext x
    show x ∈ Subgroup.normalizer ((S.subgroupOf P : Subgroup ↥P) : Set ↥P) ↔ x ∈ B.subgroupOf P
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_subgroupOf, hB, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff]
    constructor
    · intro hx
      refine ⟨hPH x.2, fun y => ?_⟩
      constructor
      · intro hy
        exact (hx ⟨y, hSP hy⟩).1 hy
      · intro hy
        have hyP : y ∈ P := by
          have hxinv : (x : E)⁻¹ * ((x : E) * y * (x : E)⁻¹) * (x : E) ∈ P :=
            P.mul_mem (P.mul_mem (P.inv_mem x.2) (hSP hy)) x.2
          simpa [mul_assoc] using hxinv
        exact (hx ⟨y, hyP⟩).2 hy
    · rintro ⟨-, hx⟩ y
      exact hx y
  have hcard : Nat.card (Sylow p ↥P) = B.relIndex P := by
    rw [Sylow.card_eq_index_normalizer T, hN]; rfl
  have hmod : Nat.card (Sylow p ↥P) ≡ 1 [MOD p] := card_sylow_modEq_one p ↥P
  have h1p : 1 % p = 1 := Nat.mod_eq_of_lt hp.one_lt
  have := hmod
  unfold Nat.ModEq at this
  rw [hcard, h1p] at this
  exact this

theorem burnsideF45_witness_top {κ' : GLKind} {p' f' : ℕ} {E : Type} [Group E]
    [hE : IsSimpleGroup E] {Gp' M₁ M₂ : Subgroup E} (hyp' : HypF_4_4 κ' p' f' Gp' M₁ M₂) :
    Gp' = ⊤ := by
  haveI := hyp'.normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Gp' with h | h
  · exfalso
    have hc := hyp'.centralizer_trivial
    rw [h, Subgroup.coe_bot, Subgroup.centralizer_singleton_one] at hc
    obtain ⟨a, b, hab⟩ := hE.exists_pair_ne
    exact hab (by
      have ha : a ∈ (⊤ : Subgroup E) := Subgroup.mem_top a
      have hb : b ∈ (⊤ : Subgroup E) := Subgroup.mem_top b
      rw [hc] at ha hb
      rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb])
  · exact h

section C57


theorem burnsideF45_C7 (hL : burnsideF45_LieFactsAll) {κ : GLKind} {p f : ℕ} {E : Type}
    [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) :
    IsLieExtAmalgam M₁ M₂ → ∀ u : (incl M₁ M₂).Γ, (incl M₁ M₂).PathTrans u (κ.m + 1) := by
  rintro ⟨κ', p', f', Gp', hκ', hyp'⟩ u
  have hS := hL κ' hκ' p' f' E Gp' M₁ M₂ hyp' (burnsideF4a_prime_of_isGenLie hyp'.model)
  have hm : κ'.m = κ.m := burnsideF45_polygon_m_eq hS.poly (burnsideF45_C1 hL hyp)
  have := hS.trans u
  rwa [show (burnsideF45_setting hyp' (burnsideF4a_prime_of_isGenLie hyp'.model)
    (burnsideF45_three_le_m κ')).m = κ'.m from rfl, hm] at this

@[expose] def burnsideF45_C5Body (κ : GLKind) (p : ℕ) {E : Type} [Group E]
    (Gp M₁ M₂ : Subgroup E) (u v : (incl M₁ M₂).Γ) : Prop :=
  IsComplementIn (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v) (Qu p Gp (incl M₁ M₂) u)
    (stv (incl M₁ M₂) u) ∧
  IsComplementIn (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v) (Qu p Gp (incl M₁ M₂) v)
    (stv (incl M₁ M₂) v) ∧
  (∃ L₁ L₂ : Subgroup (incl M₁ M₂).G0, L₁ ≤ stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v ∧
    L₂ ≤ stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v ∧
    IsComplementIn L₁ (Qu p Gp (incl M₁ M₂) u) (GpIn Gp (incl M₁ M₂) ⊓ stv (incl M₁ M₂) u) ∧
    IsComplementIn L₂ (Qu p Gp (incl M₁ M₂) v) (GpIn Gp (incl M₁ M₂) ⊓ stv (incl M₁ M₂) v)) ∧
  ∀ q₁ ∈ (incl M₁ M₂).geods κ.m u v, ∀ q₂ ∈ (incl M₁ M₂).geods κ.m u v, q₁ ≠ q₂ →
    ∀ r₁ ∈ (incl M₁ M₂).geods κ.m u v, ∀ r₂ ∈ (incl M₁ M₂).geods κ.m u v, r₁ ≠ r₂ →
      ∃ g ∈ stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v, g • q₁ = r₁ ∧ g • q₂ = r₂

theorem burnsideF45_C5_lie (hL : burnsideF45_LieFactsAll) {κ : GLKind} {p f : ℕ} {E : Type}
    [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ.IsLie) :
    ∀ u v : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.dist u v = κ.m →
      burnsideF45_C5Body κ p Gp M₁ M₂ u v :=
  (burnsideF45_clauses_of_facts45L hyp _ _
    (hL κ hκ p f E Gp M₁ M₂ hyp (burnsideF4a_prime_of_isGenLie hyp.model))).2.1

theorem burnsideF45_C5 (hL : burnsideF45_LieFactsAll)
    (hsimple : ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ p f Gp M₁ M₂ → (κ = .G2d ∨ κ = .Tits) → IsSimpleGroup E)
    {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) :
    IsLieExtAmalgam M₁ M₂ → ∀ u v : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.dist u v = κ.m →
      burnsideF45_C5Body κ p Gp M₁ M₂ u v := by
  intro hext
  rcases burnsideF45_isLie_or κ with hκ | hκ
  · exact burnsideF45_C5_lie hL hyp hκ
  · obtain ⟨κ', p', f', Gp', hκ', hyp'⟩ := hext
    haveI : Finite E := hyp.finite
    haveI := hsimple κ p f E Gp M₁ M₂ hyp hκ
    have hGp : Gp = ⊤ := hyp.canonical hκ
    have hp : p = 2 := burnsideF45_p_eq_two hyp hκ
    have hGp' : Gp' = ⊤ := burnsideF45_witness_top hyp'
    have hp'prime := burnsideF4a_prime_of_isGenLie hyp'.model
    have hP' := burnsideF45_parabolics hyp'.toHypF_4_4g
    have hq2 : (RankTwoAmalgam.ofSubgroups M₁ M₂).qTwo = 2 := by
      rcases hκ with rfl | rfl
      · exact (burnsideF45_q_G2d hyp hGp).2
      · exact (burnsideF45_q_Tits hyp hGp).2
    have hidx : (M₁ ⊓ M₂).relIndex M₂ = 3 := by
      have h := burnsideF45_qTwo_eq M₁ M₂
      omega
    have hmod : (M₁ ⊓ M₂).relIndex M₂ % p' = 1 := by
      obtain ⟨hS', -, -, hmax'⟩ := hP'
      obtain ⟨hBP, hPH, -, -⟩ := (hmax' (Gp' ⊓ M₂)).2 (Or.inr rfl)
      have h := burnsideF45_relIndex_mod hp'prime hBP hPH hS'
      rwa [hGp', top_inf_eq, top_inf_eq] at h
    rw [hidx] at hmod
    have hp'2 : p' = 2 := by
      have h3 : p' ∣ 3 - 1 := (Nat.modEq_iff_dvd' (by omega)).mp
        (by unfold Nat.ModEq; rw [hmod, Nat.mod_eq_of_lt hp'prime.one_lt])
      have h2 : p' ∣ 2 := by simpa using h3
      exact (Nat.prime_dvd_prime_iff_eq hp'prime Nat.prime_two).mp h2
    subst hp hp'2 hGp hGp'
    have hS := hL κ' hκ' 2 f' E ⊤ M₁ M₂ hyp' hp'prime
    have hm : κ'.m = κ.m := burnsideF45_polygon_m_eq hS.poly (burnsideF45_C1 hL hyp)
    intro u v huv
    have h := (burnsideF45_clauses_of_facts45L hyp' _ _ hS).2.1 u v (hm ▸ huv)
    unfold burnsideF45_C5Body
    rw [← hm]
    exact h

theorem burnsideF45_LieFacts (hL : burnsideF45_LieFactsAll)
    (hsimple : ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ p f Gp M₁ M₂ → (κ = .G2d ∨ κ = .Tits) → IsSimpleGroup E) :
    burnsideF4b_LieFacts := by
  intro κ p f E _ Gp M₁ M₂ hyp hext
  exact ⟨burnsideF45_C7 hL hyp hext, fun u v huv => (burnsideF45_C5 hL hsimple hyp hext u v huv).1⟩

end C57

end CFSG.ASVolI
