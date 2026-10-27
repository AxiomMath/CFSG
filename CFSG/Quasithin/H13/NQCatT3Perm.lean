module

public import CFSG.Quasithin.H13.NQCatT3Red

public section

namespace CFSG.Quasithin.H13.NQCat.T3

open CFSG.Quasithin.H13.NQCat.T513 CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

theorem oddInner_of_card_le {G : Type} [Group G] [Finite G] (hc : Subgroup.center G = ⊥)
    (hA : Nat.card (MulAut G) ≤ 2 * Nat.card G) :
    ∀ α : MulAut G, Odd (orderOf α) → ∃ g : G, α = MulAut.conj g := by
  intro α hα
  have : Finite (MulAut G) := Finite.of_injective _ DFunLike.coe_injective
  have hinj := conj_injective_of_center hc
  have hI : Nat.card (MulAut.conj : G →* MulAut G).range = Nat.card G :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have h1 := Subgroup.card_mul_index (MulAut.conj : G →* MulAut G).range
  rw [hI] at h1
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hi : (MulAut.conj : G →* MulAut G).range.index ≤ 2 := by
    by_contra hlt
    have : 3 * Nat.card G ≤ Nat.card (MulAut G) := by
      rw [← h1, mul_comm]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  have hi0 : (MulAut.conj : G →* MulAut G).range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨g, hg⟩ : α ∈ (MulAut.conj : G →* MulAut G).range := by
    rcases (show (MulAut.conj : G →* MulAut G).range.index = 1 ∨
        (MulAut.conj : G →* MulAut G).range.index = 2 by omega) with h | h
    · rw [Subgroup.index_eq_one.mp h]
      exact Subgroup.mem_top α
    · exact mem_of_odd_of_index_two h hα
  exact ⟨g, hg.symm⟩

theorem isPerfect_of_center_eq_bot {G : Type*} [Group G] [IsSimpleGroup G]
    (hc : Subgroup.center G = ⊥) : Group.IsPerfect G := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_pair_ne G
    have hz : a⁻¹ * b ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : ⁅g, a⁻¹ * b⁆ ∈ commutator G :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top _)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    rw [hc, Subgroup.mem_bot, inv_mul_eq_one] at hz
    exact hab hz
  · exact h

theorem oddInner_of_mulEquiv {G P : Type*} [Group G] [Group P] (ψ : P ≃* G)
    (h : ∀ α : MulAut G, Odd (orderOf α) → ∃ g : G, α = MulAut.conj g) :
    ∀ α : MulAut P, Odd (orderOf α) → ∃ x : P, α = MulAut.conj x := by
  intro α hα
  obtain ⟨y, hy⟩ := h (MulAut.congr ψ α) (by rwa [MulEquiv.orderOf_eq])
  refine ⟨ψ.symm y, MulEquiv.ext fun z => ?_⟩
  have h1 := congrArg (fun f : MulAut G => ψ.symm (f (ψ z))) hy
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply, map_mul, map_inv] at h1
  rw [MulAut.conj_apply]
  exact h1

variable {A : Type} [Group A] [Finite A] {Q R S B D : Subgroup A}
variable {P : Type} [Group P] (e : ↥Q ⧸ Subgroup.center ↥Q ≃* P)

theorem pImg_B_eq (h : Star513 Q R S B D) {b : A} (hb : b ∈ B)
    (hb3 : orderOf (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩) = 3) :
    pImg Q e B = Subgroup.zpowers (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩) := by
  have : Finite P := Finite.of_surjective _ (toP_surjective Q e)
  have hBQ : B ≤ Q := fun y hy => h.R_le (h.hall_B.1 hy).1
  have hle : Subgroup.zpowers (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩) ≤ pImg Q e B :=
    Subgroup.zpowers_le.mpr (toP_mem_pImg Q e _ hb)
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, hb3]
  have h1 : Nat.card (pImg Q e B) ∣ Nat.card B := by
    have := Subgroup.card_map_dvd (B.subgroupOf Q) (toP Q e)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv] at this
  rw [card_B h] at h1
  exact Nat.le_of_dvd (by norm_num) h1

omit [Finite A] in
theorem perm_B (h : Star513 Q R S B D) :
    ∀ t ∈ pImg Q e (S ⊓ Q), ∀ y ∈ pImg Q e B, ∃ y' ∈ pImg Q e B, ∃ t' ∈ pImg Q e (S ⊓ Q),
      t * y = y' * t' := by
  intro t ht y hy
  obtain ⟨s, hsQ, hsS, rfl⟩ := (mem_pImg Q e).1 ht
  obtain ⟨c, hcQ, hcB, rfl⟩ := (mem_pImg Q e).1 hy
  have hsc : s * c ∈ (S : Set A) * (B : Set A) := Set.mul_mem_mul hsS.1 hcB
  rw [← h.perm_B] at hsc
  obtain ⟨c', hc'B, s', hs'S, hcs⟩ := hsc
  have hcs' : c' * s' = s * c := hcs
  have hc'Q : c' ∈ Q := h.R_le (h.hall_B.1 hc'B).1
  have hs'Q : s' ∈ Q := by
    have : s' = c'⁻¹ * (s * c) := by rw [← hcs']; group
    rw [this]
    exact Q.mul_mem (Q.inv_mem hc'Q) (Q.mul_mem hsQ hcQ)
  refine ⟨toP Q e ⟨c', hc'Q⟩, toP_mem_pImg Q e _ hc'B, toP Q e ⟨s', hs'Q⟩,
    toP_mem_pImg Q e _ (Subgroup.mem_inf.mpr ⟨hs'S, hs'Q⟩), ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hcs'.symm

variable (hcen : Subgroup.center P = ⊥)
  (hinn : ∀ α : MulAut P, Odd (orderOf α) → ∃ x, α = MulAut.conj x)
include hcen hinn

theorem card_sup_three (h : Star513 Q R S B D)
    (hD3 : ∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)) {b : A} (hb : b ∈ B)
    (hb3 : orderOf (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩) = 3) :
    Nat.card ↥((iPart Q e D ⊔ Subgroup.zpowers (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩)) ⊔
        pImg Q e (S ⊓ Q)) =
      Nat.card ↥(iPart Q e D ⊔ Subgroup.zpowers (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩)) *
        Nat.card ↥(pImg Q e (S ⊓ Q)) := by
  have : Finite P := Finite.of_surjective _ (toP_surjective Q e)
  set y := toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩ with hy
  set E := iPart Q e D ⊔ Subgroup.zpowers y with hE
  have hyN : y ∈ Subgroup.normalizer (iPart Q e D : Set P) := toP_mem_normalizer_iPart e h hb
  have hEset : (E : Set P) = (iPart Q e D : Set P) * (Subgroup.zpowers y : Set P) := by
    apply coe_sup_of_perm
    intro k hk x hx
    refine ⟨k * x * k⁻¹, ?_, k, hk, by group⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact (Subgroup.mem_normalizer_iff.mp (zpow_mem hyN n) x).mp hx
  have hpermD := perm_D e hinn h hcen
  have hpermB := perm_B e h
  rw [pImg_B_eq e h hb hb3] at hpermB
  have hperm : ∀ t ∈ pImg Q e (S ⊓ Q), ∀ z ∈ E, ∃ z' ∈ E, ∃ t' ∈ pImg Q e (S ⊓ Q),
      t * z = z' * t' := by
    intro t ht z hz
    have hz' : z ∈ (E : Set P) := hz
    rw [hEset] at hz'
    obtain ⟨x, hx, k, hk, hxk⟩ := hz'
    have hxk' : x * k = z := hxk
    obtain ⟨x', hx', t₁, ht₁, h1⟩ := hpermD t ht x hx
    obtain ⟨k', hk', t₂, ht₂, h2⟩ := hpermB t₁ ht₁ k hk
    refine ⟨x' * k', Subgroup.mul_mem _ (Subgroup.mem_sup_left hx')
      (Subgroup.mem_sup_right hk'), t₂, ht₂, ?_⟩
    rw [← hxk']
    calc t * (x * k) = (t * x) * k := by group
      _ = x' * (t₁ * k) := by rw [h1]; group
      _ = x' * k' * t₂ := by rw [h2]; group
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, k, hxk⟩ := iPart_eq_zpowers e hcen hinn h hD3
  have hD3' : IsPGroup 3 ↥(iPart Q e D) := by
    rw [hx]
    have hdvd : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hxk
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hy3 : IsPGroup 3 ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb3, pow_one])
  have hE3 : IsPGroup 3 ↥E := hD3'.to_sup_of_normal_left' hy3 (Subgroup.zpowers_le.mpr hyN)
  obtain ⟨hT2, -⟩ := pImg_SQ e h
  obtain ⟨m, hm⟩ := hE3.exists_card_eq
  obtain ⟨n, hn⟩ := hT2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card E) (Nat.card (pImg Q e (S ⊓ Q))) := by
    rw [hm, hn]
    exact Nat.Coprime.pow m n (by norm_num)
  exact card_sup_of_perm hperm hcop

end CFSG.Quasithin.H13.NQCat.T3
