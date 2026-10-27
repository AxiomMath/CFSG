module

public import CFSG.Quasithin.Background.HM22RowTwo
public import CFSG.Quasithin.Background.HM22RowOdd
public import CFSG.Quasithin.Background.HM22RowHat
public import CFSG.Quasithin.Background.HMathieuFacts22Base

public section

namespace CFSG.Quasithin.H.Mathieu.M22Row

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu.H12Cert CFSG.Blueprint Matrix

theorem prime_dvd_card {p : ℕ} (hp : p.Prime) (h : p ∣ 1330560) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
  have e : (1330560 : ℕ) = 2 ^ 7 * 3 ^ 3 * 5 * 7 * 11 := by norm_num
  rw [e] at h
  have hd : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h11
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h7
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h5
      · rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
        · exact Or.inl (hd 2 Nat.prime_two (hp.dvd_of_dvd_pow h2))
        · exact Or.inr (Or.inl (hd 3 Nat.prime_three (hp.dvd_of_dvd_pow h3)))
      · exact Or.inr (Or.inr (Or.inl (hd 5 (by norm_num) h5)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hd 7 (by norm_num) h7))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hd 11 (by norm_num) h11))))

variable {V : Type} [CommGroup V] [Finite V]

theorem le_rkIdx_of_card_le (hV : ∀ v : V, v ^ 2 = 1) (hc : Nat.card V = 4096) {H : Subgroup V}
    {j : ℕ} (hH : Nat.card H ≤ 2 ^ j) : 12 - j ≤ rkIdx H := by
  have h1 := rk_add_rkIdx H
  have h2 : rk V = 12 := by
    rw [rk, hc, show (4096 : ℕ) = 2 ^ 12 by norm_num, padicValNat.prime_pow]
  have h3 : rk H ≤ j := by
    rw [card_eq_two_pow hV H] at hH
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hH
  omega

theorem rk_le_of_card_le {A : Subgroup (MulAut V)} (hA : ∀ a ∈ A, a ^ 2 = 1) {k : ℕ}
    (h : Nat.card A ≤ 2 ^ k) : rk ↥A ≤ k := by
  have : Finite (MulAut V) := MulEquiv.finite_left
  have hp : IsPGroup 2 ↥A := fun a => ⟨1, Subtype.ext (by simpa using hA _ a.2)⟩
  rw [card_eq_two_pow_of_isPGroup hp] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

section Model

variable {L : Subgroup (MulAut V)}

omit [Finite V] in
theorem card_fixV_eq {ψ : ↥G ≃* ↥L} {θ : V ≃* Multiplicative (Fin 12 → ZMod 2)}
    (hψθ : ∀ (g : ↥G) (w : V), Multiplicative.toAdd (θ (((ψ g : ↥L) : MulAut V) w)) =
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
        (Multiplicative.toAdd (θ w))) (g : ↥G) :
    Nat.card (fixV (Subgroup.zpowers ((ψ g : ↥L) : MulAut V))) =
      Nat.card {u : Fin 12 → ZMod 2 //
        ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u = u} := by
  refine Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.toAdd (θ v), ?_⟩
      invFun := fun u => ⟨θ.symm (Multiplicative.ofAdd u.1), ?_⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp) }
  · rw [← hψθ, mem_fixV_zpowers_iff.mp v.2]
  · rw [mem_fixV_zpowers_iff]
    apply θ.injective
    apply Multiplicative.toAdd.injective
    rw [hψθ, MulEquiv.apply_symm_apply, toAdd_ofAdd, u.2]

theorem model_facts
    (hV : ∀ v : V, v ^ 2 = 1) (h : Mhat22Twelve L ⊤ ⊥) :
    (∀ b ∈ L, b * b = 1 → b ≠ 1 → Nat.card (fixV (Subgroup.zpowers b)) ≤ 256) ∧
      (∀ b ∈ L, ∀ b' ∈ L, b * b = 1 → b' * b' = 1 → b ≠ 1 → b' ≠ 1 → b * b' = b' * b →
        b ≠ b' → ∃ v : V, b v = v ∧ b' v ≠ v) ∧
      ∀ y ∈ L, ∀ p : ℕ, orderOf y = p → (p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11) →
        Nat.card (fixV (Subgroup.zpowers y)) ≤ 16 := by
  obtain ⟨ψ, θ, hψθ⟩ := H12Pf.exists_model_of_mhat22Twelve hV h
  have hψ : ∀ b (hb : b ∈ L), ((ψ (ψ.symm ⟨b, hb⟩) : ↥L) : MulAut V) = b := fun b hb => by
    rw [MulEquiv.apply_symm_apply]
  have hone : ∀ b (hb : b ∈ L), b ≠ 1 → ((ψ.symm ⟨b, hb⟩ : ↥G) : GL (Fin 12) (ZMod 2)) ≠ 1 :=
    fun b hb hb1 h1 => hb1 (by
      have h2 : ψ.symm ⟨b, hb⟩ = 1 := Subtype.ext h1
      have h3 := congrArg (fun t => ((ψ t : ↥L) : MulAut V)) h2
      simpa only [MulEquiv.apply_symm_apply, map_one, OneMemClass.coe_one] using h3)
  have hsq : ∀ b (hb : b ∈ L), b * b = 1 →
      ((ψ.symm ⟨b, hb⟩ : ↥G) : GL (Fin 12) (ZMod 2)) *
        ((ψ.symm ⟨b, hb⟩ : ↥G) : GL (Fin 12) (ZMod 2)) = 1 := fun b hb hb2 => by
    have h1 : (⟨b, hb⟩ : ↥L) * ⟨b, hb⟩ = 1 := Subtype.ext hb2
    rw [← Subgroup.coe_mul, ← map_mul, h1, map_one]
    rfl
  refine ⟨fun b hb hb2 hb1 => ?_, fun b hb b' hb' hb2 hb'2 hb1 hb'1 hbb' hne => ?_,
    fun y hy p hyp hp => ?_⟩
  · rw [← hψ b hb, card_fixV_eq hψθ]
    exact card_fix_le_of_inv (ψ.symm ⟨b, hb⟩).2 (hsq b hb hb2) (hone b hb hb1)
  · have hcomm : ((ψ.symm ⟨b, hb⟩ : ↥G) : GL (Fin 12) (ZMod 2)) *
        ((ψ.symm ⟨b', hb'⟩ : ↥G) : GL (Fin 12) (ZMod 2)) =
        ((ψ.symm ⟨b', hb'⟩ : ↥G) : GL (Fin 12) (ZMod 2)) *
          ((ψ.symm ⟨b, hb⟩ : ↥G) : GL (Fin 12) (ZMod 2)) := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
      congr 2
      exact Subtype.ext hbb'
    have hne' : ((ψ.symm ⟨b, hb⟩ : ↥G) : GL (Fin 12) (ZMod 2)) ≠
        ((ψ.symm ⟨b', hb'⟩ : ↥G) : GL (Fin 12) (ZMod 2)) := fun h1 => hne (by
      have h2 := congrArg (fun t => ((ψ t : ↥L) : MulAut V)) (Subtype.ext h1 :
        ψ.symm ⟨b, hb⟩ = ψ.symm ⟨b', hb'⟩)
      simpa only [MulEquiv.apply_symm_apply] using h2)
    obtain ⟨u, hu, hu'⟩ := exists_fix_of_inv (ψ.symm ⟨b, hb⟩).2 (ψ.symm ⟨b', hb'⟩).2
      (hsq b hb hb2) (hsq b' hb' hb'2) (hone b hb hb1) (hone b' hb' hb'1) hcomm hne'
    have key : ∀ c (hc : c ∈ L), (c (θ.symm (Multiplicative.ofAdd u)) =
        θ.symm (Multiplicative.ofAdd u) ↔
        (((ψ.symm ⟨c, hc⟩ : ↥G) : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
          u = u) := by
      intro c hc
      have h2 := hψθ (ψ.symm ⟨c, hc⟩) (θ.symm (Multiplicative.ofAdd u))
      rw [hψ c hc, MulEquiv.apply_symm_apply, toAdd_ofAdd] at h2
      constructor
      · intro h1
        rw [← h2, h1, MulEquiv.apply_symm_apply, toAdd_ofAdd]
      · intro h1
        rw [h1] at h2
        apply θ.injective
        apply Multiplicative.toAdd.injective
        rw [h2, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    exact ⟨θ.symm (Multiplicative.ofAdd u), (key b hb).mpr hu, fun h1 => hu' ((key b' hb').mp h1)⟩
  · rw [← hψ y hy, card_fixV_eq hψθ]
    refine card_fix_le_of_orderOf (ψ.symm ⟨y, hy⟩).2 ?_ hp
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hyp]

end Model

section Setting

variable {L : Subgroup (MulAut V)}

theorem exists_center_gen
    (hV : ∀ v : V, v ^ 2 = 1) (h : Mhat22Twelve L ⊤ ⊥) :
    ∃ z ∈ L, (∀ v, z (z (z v)) = v) ∧ (∀ v, z v = v → v = 1) ∧ z ≠ z⁻¹ ∧
      (∀ g ∈ L, g * z = z * g) ∧
      ∀ x ∈ Subgroup.normalizer (L : Set (MulAut V)), x ∈ L ∨ x * z * x⁻¹ = z⁻¹ := by
  have hL := H12Pf.isHat_of_mhat22Twelve h
  have hcV := H12Pf.card_eq_of_mhat22Twelve h
  have : Finite (MulAut V) := MulEquiv.finite_left
  have : Nontrivial ↥(Subgroup.center ↥L) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hL.2.1]
    norm_num
  obtain ⟨⟨z0, hz0⟩, hz01⟩ := exists_ne (1 : ↥(Subgroup.center ↥L))
  have hz01' : z0 ≠ 1 := fun h1 => hz01 (Subtype.ext h1)
  have hz03 : z0 ^ 3 = 1 := by
    have h1 := (pow_card_eq_one' : (⟨z0, hz0⟩ : ↥(Subgroup.center ↥L)) ^
      Nat.card ↥(Subgroup.center ↥L) = 1)
    rw [hL.2.1] at h1
    exact congrArg Subtype.val h1
  have hz3 : ∀ v, (z0 : MulAut V) ((z0 : MulAut V) ((z0 : MulAut V) v)) = v := by
    intro v
    have h1 : ((z0 ^ 3 : ↥L) : MulAut V) = 1 := by rw [hz03]; rfl
    rw [Subgroup.coe_pow, pow_three] at h1
    have h2 := congrArg (fun f : MulAut V => f v) h1
    simpa only [MulAut.mul_apply, MulAut.one_apply] using h2
  have hzinv : (z0 : MulAut V) ≠ (z0 : MulAut V)⁻¹ := by
    intro h1
    have h2 : z0 = z0⁻¹ := Subtype.ext h1
    have h3 : z0 ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 2 [h2]
      exact mul_inv_cancel z0
    apply hz01'
    calc z0 = z0 ^ 3 * (z0 ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz03, h3, inv_one, one_mul]
  have : Group.IsPerfect ↥L := hL.1.1
  have hq : CFSG.Open.IsQuasisimple ↥L := ⟨Group.IsPerfect.commutator_eq_top, hL.1.2.1⟩
  have hC0 := M22Link.kg82HatM22Twelve_holds ↥L hq hL.2.1 hL.2.2 V (by rw [hcV]; norm_num) hV
    L.subtype L.subtype_injective
  rw [Subgroup.range_subtype] at hC0
  have hC : Subgroup.centralizer (L : Set (MulAut V)) ≤ L := by
    rw [hC0]
    exact Subgroup.map_subtype_le _
  refine ⟨z0, z0.2, hz3, H12Pf.fpf_of_mhat22Twelve hV h hz0 hz01', hzinv, fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz0 ⟨g, hg⟩), fun x hx => ?_⟩
  exact (mem_or_inv hL hC hx).imp id fun h1 => h1 z0 hz0

variable {z : MulAut V}

omit [Finite V] in
theorem card_le_of_le_L
    (hL : IsHat ↥L (NativeSporadic.Carrier .M22)) {E : Subgroup (MulAut V)} (hEL : E ≤ L)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 ^ 4 := by
  have h1 := card_le_of_isHat hL (E := E.subgroupOf L)
    (fun x hx y hy => Subtype.ext (hc _ hx _ hy)) (fun x hx => Subtype.ext (hs _ hx))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv] at h1

theorem card_le_of_le_normalizer
    (hL : IsHat ↥L (NativeSporadic.Carrier .M22)) (hz1 : z ≠ z⁻¹)
    (hdi : ∀ x ∈ Subgroup.normalizer (L : Set (MulAut V)), x ∈ L ∨ x * z * x⁻¹ = z⁻¹)
    {E : Subgroup (MulAut V)} (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 ^ 5 := by
  have : Finite (MulAut V) := MulEquiv.finite_left
  have h1 := card_le_two_mul hz1 hdi hEN
  have h2 := card_le_of_le_L hL (inf_le_right : E ⊓ L ≤ L)
    (fun x hx y hy => hc x (Subgroup.mem_inf.mp hx).1 y (Subgroup.mem_inf.mp hy).1)
    (fun x hx => hs x (Subgroup.mem_inf.mp hx).1)
  calc Nat.card E ≤ 2 * Nat.card ↥(E ⊓ L) := h1
    _ ≤ 2 * 2 ^ 4 := Nat.mul_le_mul_left _ h2
    _ = 2 ^ 5 := by norm_num

variable {M : Subgroup (MulAut V)}

theorem pRank_le_five
    (hL : IsHat ↥L (NativeSporadic.Carrier .M22)) (hz1 : z ≠ z⁻¹)
    (hdi : ∀ x ∈ Subgroup.normalizer (L : Set (MulAut V)), x ∈ L ∨ x * z * x⁻¹ = z⁻¹)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V))) : CFSG.Open.pRank 2 M ≤ 5 := by
  have : Finite (MulAut V) := MulEquiv.finite_left
  obtain ⟨E, hEM, hE, hEc⟩ := exists_isElemAbelian_card_pRank M
  have hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => by
    have := @mul_comm' (↥E) _ hE.1 ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hs : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← pow_two]; exact hE.2 x hx
  have h1 := card_le_of_le_normalizer hL hz1 hdi (hEM.trans hMN) hc hs
  rw [hEc] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

theorem eight_le_betaH (hV : ∀ v : V, v ^ 2 = 1) (hc : Nat.card V = 4096) (hz1 : z ≠ z⁻¹)
    (hdi : ∀ x ∈ Subgroup.normalizer (L : Set (MulAut V)), x ∈ L ∨ x * z * x⁻¹ = z⁻¹)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V))) (hLc : Nat.card L = 1330560)
    (hodd : ∀ y ∈ L, ∀ p : ℕ, orderOf y = p → (p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11) →
      Nat.card (fixV (Subgroup.zpowers y)) ≤ 16) :
    (8 : ℕ∞) ≤ betaH M := by
  have : Finite (MulAut V) := MulEquiv.finite_left
  rw [le_betaH_iff_isPGroup]
  intro U _ hnp
  obtain ⟨p, hp, hp2, hpd⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card ↥(M ⊓ centSub U) := by
    by_contra hcon
    push Not at hcon
    apply hnp
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [IsPGroup.iff_card]
    exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      fun {d} hd hdd => by_contra fun h1 => hcon d hd h1 hdd⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpd
  have hyM : (x : MulAut V) ∈ M := (Subgroup.mem_inf.mp x.2).1
  have hyU : (x : MulAut V) ∈ centSub U := (Subgroup.mem_inf.mp x.2).2
  have hyp : orderOf (x : MulAut V) = p := by rw [Subgroup.orderOf_coe, hx]
  have hyL : (x : MulAut V) ∈ L :=
    mem_of_odd hz1 hdi (hMN hyM) (by rw [hyp]; exact hp.odd_of_ne_two hp2)
  have hpL : p ∣ 1330560 := by
    rw [← hLc, ← hyp, ← Subgroup.orderOf_mk (x : MulAut V) hyL]
    exact orderOf_dvd_natCard _
  have hp' : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
    rcases prime_dvd_card hp hpL with h1 | h1
    · exact absurd h1 hp2
    · exact h1
  have h1 := hodd _ hyL p hyp hp'
  have h2 := le_rkIdx_of_card_le hV hc (j := 4) (by simpa using h1)
  have h3 := rkIdx_anti (fun u hu => mem_fixV_zpowers_iff.mpr (hyU u hu) :
    U ≤ fixV (Subgroup.zpowers (x : MulAut V)))
  have h4 : (8 : ℕ) ≤ rkIdx U := by omega
  exact_mod_cast h4

theorem exists_ne_of_two_lt_card {X : Type*} [Group X] {A : Subgroup X} (hA : 2 < Nat.card A)
    (b : X) : ∃ b' ∈ A, b' ≠ 1 ∧ b' ≠ b := by
  classical
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective fun x : ↥A => decide ((x : X) = 1) := by
    intro x y hxy
    simp only [decide_eq_decide] at hxy
    apply Subtype.ext
    by_cases hx : (x : X) = 1
    · rw [hx, hxy.mp hx]
    · rw [hcon _ x.2 hx, hcon _ y.2 fun hy => hx (hxy.mpr hy)]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

omit [Finite V] in
theorem inv_apply_eq (hz3 : ∀ v, z (z (z v)) = v) (w : V) : z⁻¹ w = z (z w) := by
  have h := hz3 (z⁻¹ w)
  rw [MulAut.apply_inv_self V z w] at h
  exact h.symm

theorem alphaH_eq_one_of_mhat22
    (hV : ∀ v : V, v ^ 2 = 1) (hc : Nat.card V = 4096)
    (hL : IsHat ↥L (NativeSporadic.Carrier .M22)) (hz3 : ∀ v, z (z (z v)) = v)
    (hzf : ∀ v, z v = v → v = 1) (hz1 : z ≠ z⁻¹) (hzc : ∀ g ∈ L, g * z = z * g)
    (hdi : ∀ x ∈ Subgroup.normalizer (L : Set (MulAut V)), x ∈ L ∨ x * z * x⁻¹ = z⁻¹)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hinv : ∀ b ∈ L, b * b = 1 → b ≠ 1 → Nat.card (fixV (Subgroup.zpowers b)) ≤ 256)
    (hne : ∀ b ∈ L, ∀ b' ∈ L, b * b = 1 → b' * b' = 1 → b ≠ 1 → b' ≠ 1 → b * b' = b' * b →
      b ≠ b' → ∃ v : V, b v = v ∧ b' v ≠ v) :
    alphaH M = 1 := by
  have : Finite (MulAut V) := MulEquiv.finite_left
  apply alphaH_eq_one_of_not_isFOneModule
  rintro ⟨A, ⟨hAM, hA1, hAc, hAs⟩, hoff⟩
  have hAs' : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← pow_two]; exact hAs a ha
  have hfixle : ∀ b ∈ A, fixV A ≤ fixV (Subgroup.zpowers b) := fun b hb v hv =>
    mem_fixV_zpowers_iff.mpr (hv b hb)
  have hrk5 := rk_le_of_card_le hAs (card_le_of_le_normalizer hL hz1 hdi (hAM.trans hMN) hAc hAs')
  obtain ⟨⟨b, hbA⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
  by_cases hAL : A ≤ L
  ·
    have hrk4 := rk_le_of_card_le hAs (card_le_of_le_L hL hAL hAc hAs')
    have hb := hinv b (hAL hbA) (hAs' b hbA) hb1'
    by_cases hA2 : Nat.card A ≤ 2
    · have hrk1 := rk_le_of_card_le hAs (k := 1) (by simpa using hA2)
      have h1 := le_rkIdx_of_card_le hV hc (j := 8)
        ((Subgroup.card_le_of_le (hfixle b hbA)).trans (by simpa using hb))
      omega
    · obtain ⟨b', hb'A, hb'1, hb'b⟩ := exists_ne_of_two_lt_card (A := A) (by omega) b
      obtain ⟨v, hv, hv'⟩ := hne b (hAL hbA) b' (hAL hb'A) (hAs' b hbA) (hAs' b' hb'A) hb1' hb'1
        (hAc b hbA b' hb'A) (Ne.symm hb'b)
      have hlt : fixV A < fixV (Subgroup.zpowers b) := by
        refine lt_of_le_of_ne (hfixle b hbA) fun heq => hv' ?_
        have h1 : v ∈ fixV A := heq ▸ mem_fixV_zpowers_iff.mpr hv
        exact h1 b' hb'A
      have hcard := Subgroup.card_lt_of_lt hlt
      obtain ⟨j, hj⟩ := exists_card_eq_four_pow hV hz3 hzf (fixV A) fun x hx a ha => by
        rw [← MulAut.mul_apply, hzc a (hAL ha), MulAut.mul_apply, hx a ha]
      have hj3 : j ≤ 3 := by
        have h4 : 4 ^ j < 4 ^ 4 := by
          rw [← hj]
          calc Nat.card ↥(fixV A) < Nat.card ↥(fixV (Subgroup.zpowers b)) := hcard
            _ ≤ 256 := hb
            _ = 4 ^ 4 := by norm_num
        have h5 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h4
        omega
      have h6 : Nat.card ↥(fixV A) ≤ 2 ^ 6 := by
        rw [hj]
        calc 4 ^ j ≤ 4 ^ 3 := Nat.pow_le_pow_right (by norm_num) hj3
          _ = 2 ^ 6 := by norm_num
      have h7 := le_rkIdx_of_card_le hV hc h6
      omega
  ·
    obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hAL
    have haz : a * z * a⁻¹ = z⁻¹ := (hdi a (hMN (hAM haA))).resolve_left haL
    have ha2 : ∀ v, a (a v) = v := fun v => by
      have h2 := congrArg (fun f : MulAut V => f v) (hAs' a haA)
      simpa only [MulAut.mul_apply, MulAut.one_apply] using h2
    have hazv : ∀ v, a (z v) = z (z (a v)) := fun v => by
      have h1 : a * z = z⁻¹ * a := by
        calc a * z = (a * z * a⁻¹) * a := by group
          _ = z⁻¹ * a := by rw [haz]
      have h2 := congrArg (fun f : MulAut V => f v) h1
      simp only [MulAut.mul_apply] at h2
      rw [h2, inv_apply_eq hz3]
    by_cases hA0 : A ⊓ L = ⊥
    ·
      have hA2 : Nat.card A ≤ 2 := by
        have h1 := card_le_two_mul hz1 hdi (hAM.trans hMN) (H := A)
        rw [hA0, Subgroup.card_bot] at h1
        exact h1
      have hrk1 := rk_le_of_card_le hAs (k := 1) (by simpa using hA2)
      have hsq := card_eq_sq_fix hV hz3 hzf ha2 hazv ⊤ (fun _ _ => trivial) fun _ _ => trivial
      rw [Subgroup.card_top, hc, top_inf_eq] at hsq
      have h64 : Nat.card ↥(fixV (Subgroup.zpowers a)) ≤ 2 ^ 6 := by
        have h1 : Nat.card ↥(fixV (Subgroup.zpowers a)) ^ 2 ≤ (2 ^ 6) ^ 2 := by
          rw [← hsq]
          norm_num
        exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
      have h1 := le_rkIdx_of_card_le hV hc ((Subgroup.card_le_of_le (hfixle a haA)).trans h64)
      omega
    ·
      obtain ⟨⟨b0, hb0⟩, hb01⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA0
      have hb0A := (Subgroup.mem_inf.mp hb0).1
      have hb0L := (Subgroup.mem_inf.mp hb0).2
      have hb0c := hinv b0 hb0L (hAs' b0 hb0A) fun h1 => hb01 (Subtype.ext h1)
      have hXz : ∀ x ∈ fixV (A ⊓ L), z x ∈ fixV (A ⊓ L) := fun x hx c hc => by
        rw [← MulAut.mul_apply, hzc c (Subgroup.mem_inf.mp hc).2, MulAut.mul_apply, hx c hc]
      have hXa : ∀ x ∈ fixV (A ⊓ L), a x ∈ fixV (A ⊓ L) := fun x hx c hc => by
        rw [← MulAut.mul_apply, hAc c (Subgroup.mem_inf.mp hc).1 a haA, MulAut.mul_apply,
          hx c hc]
      have hsq := card_eq_sq_fix hV hz3 hzf ha2 hazv (fixV (A ⊓ L)) hXz hXa
      have hle : fixV A ≤ fixV (A ⊓ L) ⊓ fixV (Subgroup.zpowers a) := fun v hv =>
        ⟨fun c hc => hv c (Subgroup.mem_inf.mp hc).1, hfixle a haA hv⟩
      have hXb : fixV (A ⊓ L) ≤ fixV (Subgroup.zpowers b0) := fun v hv =>
        mem_fixV_zpowers_iff.mpr (hv b0 hb0)
      have h16 : Nat.card ↥(fixV A) ≤ 2 ^ 4 := by
        have h1 : Nat.card ↥(fixV A) ^ 2 ≤ (2 ^ 4) ^ 2 := by
          calc Nat.card ↥(fixV A) ^ 2
              ≤ Nat.card ↥(fixV (A ⊓ L) ⊓ fixV (Subgroup.zpowers a)) ^ 2 :=
                Nat.pow_le_pow_left (Subgroup.card_le_of_le hle) 2
            _ = Nat.card ↥(fixV (A ⊓ L)) := hsq.symm
            _ ≤ Nat.card ↥(fixV (Subgroup.zpowers b0)) := Subgroup.card_le_of_le hXb
            _ ≤ (2 ^ 4) ^ 2 := by simpa using hb0c
        exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
      have h1 := le_rkIdx_of_card_le hV hc h16
      omega

end Setting

theorem row721M22Hat
    (hV : ∀ v : V, v ^ 2 = 1) {L M : Subgroup (MulAut V)}
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V))) (h : Mhat22Twelve L ⊤ ⊥) :
    CFSG.Open.pRank 2 M ≤ 5 ∧ (8 : ℕ∞) ≤ betaH M ∧ alphaH M = 1 := by
  have hL := H12Pf.isHat_of_mhat22Twelve h
  have hc := H12Pf.card_eq_of_mhat22Twelve h
  obtain ⟨z, -, hz3, hzf, hz1, hzc, hdi⟩ := exists_center_gen hV h
  obtain ⟨hinv, hne, hodd⟩ := model_facts hV h
  have hLc : Nat.card L = 1330560 := by
    obtain ⟨ψ, -, -⟩ := H12Pf.exists_model_of_mhat22Twelve hV h
    rw [← Nat.card_congr ψ.toEquiv, card_G]
  exact ⟨pRank_le_five hL hz1 hdi hMN, eight_le_betaH hV hc hz1 hdi hMN hLc hodd,
    alphaH_eq_one_of_mhat22 hV hc hL hz3 hzf hz1 hzc hdi hMN hinv hne⟩

end CFSG.Quasithin.H.Mathieu.M22Row
