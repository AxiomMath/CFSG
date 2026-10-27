module

public import CFSG.Quasithin.Background.HM22Out
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22

public section

namespace CFSG.Quasithin.H.Mathieu.M22Row

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu.M22Link CFSG.Blueprint

theorem card_le_of_isHat
    {X : Type} [Group X] (hX : IsHat X (NativeSporadic.Carrier .M22)) {E : Subgroup X}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 ^ 4 := by
  obtain ⟨-, hZ3, ⟨e₀⟩⟩ := hX
  let e : X ⧸ Subgroup.center X ≃* ↥NativeSporadic.M22 := e₀
  let ι : ↥E →* ↥NativeSporadic.M22 :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center X)).comp E.subtype)
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : X) ∈ Subgroup.center X := by
      have h2 : QuotientGroup.mk' (Subgroup.center X) (x : X) = 1 := by
        apply e.injective
        rw [map_one]
        exact hx
      exact (QuotientGroup.eq_one_iff _).mp h2
    have hz2 : (⟨x, h1⟩ : ↥(Subgroup.center X)) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact hsq _ x.2)
    have h3 : orderOf (⟨x, h1⟩ : ↥(Subgroup.center X)) ∣ 3 := hZ3 ▸ orderOf_dvd_natCard _
    have h4 : orderOf (⟨x, h1⟩ : ↥(Subgroup.center X)) ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
    have h5 : orderOf (⟨x, h1⟩ : ↥(Subgroup.center X)) = 1 :=
      Nat.dvd_one.mp (by simpa using Nat.dvd_gcd h3 h4)
    have h6 := congrArg Subtype.val (orderOf_eq_one_iff.mp h5)
    exact Subtype.ext h6
  have hrange := CFSG.QuasithinUnique.Setup.X1.m22_rank_le ι.range
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ι (Subtype.ext (hcomm _ a.2 _ b.2)))
    (by
      rintro _ ⟨a, rfl⟩
      rw [← map_mul, show a * a = 1 from Subtype.ext (hsq _ a.2), map_one])
  rwa [← Nat.card_range_of_injective hinj]

section Normalizer

variable {Y : Type} [Group Y] {L : Subgroup Y}

theorem mem_or_inv
    [Finite L]
    (hL : IsHat ↥L (NativeSporadic.Carrier .M22))
    (hC : Subgroup.centralizer (L : Set Y) ≤ L) {x : Y}
    (hx : x ∈ Subgroup.normalizer (L : Set Y)) :
    x ∈ L ∨ ∀ c ∈ Subgroup.center ↥L, x * (c : Y) * x⁻¹ = ((c : Y))⁻¹ := by
  have hα : ∀ g : ↥L, ((L.normalizerMonoidHom ⟨x, hx⟩ g : ↥L) : Y) = x * g * x⁻¹ := fun g =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨x, hx⟩ g
  by_cases hinn : ∃ k : ↥L, L.normalizerMonoidHom ⟨x, hx⟩ = MulAut.conj k
  · left
    obtain ⟨k, hk⟩ := hinn
    have hkx : (k : Y)⁻¹ * x ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 := hα ⟨g, hg⟩
      rw [hk, MulAut.conj_apply] at h1
      have h2 : (k : Y) * g * (k : Y)⁻¹ = x * g * x⁻¹ := h1
      calc g * ((k : Y)⁻¹ * x) = (k : Y)⁻¹ * ((k : Y) * g * (k : Y)⁻¹) * x := by group
        _ = (k : Y)⁻¹ * (x * g * x⁻¹) * x := by rw [h2]
        _ = (k : Y)⁻¹ * x * g := by group
    have hx' : x = k * ((k : Y)⁻¹ * x) := by group
    rw [hx']
    exact L.mul_mem k.2 (hC hkx)
  · right
    push Not at hinn
    have : Group.IsPerfect ↥L := hL.1.1
    have hq : CFSG.Open.IsQuasisimple ↥L := ⟨Group.IsPerfect.commutator_eq_top, hL.1.2.1⟩
    intro c hc
    have h := kg82HatM22Out_holds ↥L hq hL.2.1 hL.2.2 (L.normalizerMonoidHom ⟨x, hx⟩) hinn c hc
    rw [← hα c, h]
    rfl

variable {z : Y}

theorem mem_of_comm (hz1 : z ≠ z⁻¹)
    (hdi : ∀ x ∈ Subgroup.normalizer (L : Set Y), x ∈ L ∨ x * z * x⁻¹ = z⁻¹) {x : Y}
    (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hxz : x * z = z * x) : x ∈ L := by
  rcases hdi x hx with h | h
  · exact h
  · exfalso
    apply hz1
    rw [← h, hxz, mul_inv_cancel_right]

theorem mem_of_odd (hz1 : z ≠ z⁻¹)
    (hdi : ∀ x ∈ Subgroup.normalizer (L : Set Y), x ∈ L ∨ x * z * x⁻¹ = z⁻¹) {x : Y}
    (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hodd : Odd (orderOf x)) : x ∈ L := by
  rcases hdi x hx with h | h
  · exact h
  · exfalso
    have hinv : x * z⁻¹ * x⁻¹ = z := by
      rw [← inv_inj, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, ← mul_assoc, ← h]
    have key : ∀ n : ℕ, x ^ (2 * n + 1) * z * (x ^ (2 * n + 1))⁻¹ = z⁻¹ := by
      intro n
      induction n with
      | zero => simpa using h
      | succ n ih =>
        have e : x ^ (2 * (n + 1) + 1) = x * (x * x ^ (2 * n + 1)) := by
          rw [← mul_assoc, ← pow_two, ← pow_add]
          ring_nf
        rw [e, mul_inv_rev, mul_inv_rev]
        calc x * (x * x ^ (2 * n + 1)) * z * ((x ^ (2 * n + 1))⁻¹ * x⁻¹ * x⁻¹)
            = x * (x * (x ^ (2 * n + 1) * z * (x ^ (2 * n + 1))⁻¹) * x⁻¹) * x⁻¹ := by group
          _ = z⁻¹ := by rw [ih, hinv, h]
    obtain ⟨n, hn⟩ := hodd
    have h1 := key n
    rw [← hn, pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
    exact hz1 h1

theorem card_le_two_mul [Finite Y] (hz1 : z ≠ z⁻¹)
    (hdi : ∀ x ∈ Subgroup.normalizer (L : Set Y), x ∈ L ∨ x * z * x⁻¹ = z⁻¹) {H : Subgroup Y}
    (hH : H ≤ Subgroup.normalizer (L : Set Y)) : Nat.card H ≤ 2 * Nat.card ↥(H ⊓ L) := by
  by_cases hHL : H ≤ L
  · rw [inf_eq_left.mpr hHL]
    omega
  obtain ⟨a, haH, haL⟩ := Set.not_subset.mp hHL
  have hinvz : ∀ y ∈ H, y ∉ L → y * z * y⁻¹ = z⁻¹ := fun y hy hyL =>
    (hdi y (hH hy)).resolve_left hyL
  let f : ↥(H ⊓ L) ⊕ ↥(H ⊓ L) → ↥H := fun s => match s with
    | Sum.inl e => ⟨e, e.2.1⟩
    | Sum.inr e => ⟨a * e, H.mul_mem haH e.2.1⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    by_cases hyL : y ∈ L
    · exact ⟨Sum.inl ⟨y, hy, hyL⟩, rfl⟩
    · have hay : a⁻¹ * y ∈ L := by
        apply mem_of_comm hz1 hdi (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hH haH)) (hH hy))
        have h1 := hinvz a haH haL
        have h2 := hinvz y hy hyL
        have h1' : a * z⁻¹ * a⁻¹ = z := by
          have h := congrArg (fun t => t⁻¹) h1
          simp only [mul_inv_rev, inv_inv] at h
          rw [mul_assoc]
          exact h
        have h3 : a⁻¹ * z * a = z⁻¹ := by
          calc a⁻¹ * z * a = a⁻¹ * (a * z⁻¹ * a⁻¹) * a := by rw [h1']
            _ = z⁻¹ := by group
        calc a⁻¹ * y * z = a⁻¹ * (y * z * y⁻¹) * y := by group
          _ = a⁻¹ * z⁻¹ * y := by rw [h2]
          _ = (a⁻¹ * z * a)⁻¹ * (a⁻¹ * y) := by group
          _ = z * (a⁻¹ * y) := by rw [h3, inv_inv]
      refine ⟨Sum.inr ⟨a⁻¹ * y, H.mul_mem (H.inv_mem haH) hy, hay⟩, ?_⟩
      apply Subtype.ext
      show a * (a⁻¹ * y) = y
      group
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_sum, ← two_mul] at this

end Normalizer

end CFSG.Quasithin.H.Mathieu.M22Row
