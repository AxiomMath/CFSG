module

public import CFSG.Quasithin.H13.J4TypeDefs
public import CFSG.Quasithin.EmptyFaithful.S152VM22
public import CFSG.Quasithin.EmptyFaithful.S152VKc
public import CFSG.Quasithin.EmptyFaithful.S152VL2b

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

namespace S152V

theorem conj_mem_oPrimeResidualOf {G : Type} [Group G] {p : ℕ} {H : Subgroup G} (c : ↥H) {a : G}
    (ha : a ∈ oPrimeResidualOf p H) : (c : G) * a * (c : G)⁻¹ ∈ oPrimeResidualOf p H := by
  change a ∈ Subgroup.closure {x : G | x ∈ H ∧ ∃ k : ℕ, orderOf x = p ^ k} at ha
  change (c : G) * a * (c : G)⁻¹ ∈ Subgroup.closure {x : G | x ∈ H ∧ ∃ k : ℕ, orderOf x = p ^ k}
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨hxH, k, hk⟩ := hx
    refine Subgroup.subset_closure ⟨H.mul_mem (H.mul_mem c.2 hxH) (H.inv_mem c.2), k, ?_⟩
    rw [← hk, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  | one => simp
  | mul x y _ _ ihx ihy =>
    have e : (c : G) * (x * y) * (c : G)⁻¹ = ((c : G) * x * (c : G)⁻¹) * ((c : G) * y * (c : G)⁻¹) := by
      group
    rw [e]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ih =>
    have e : (c : G) * x⁻¹ * (c : G)⁻¹ = ((c : G) * x * (c : G)⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ih

theorem oPrimeResidualOf_le {G : Type} [Group G] (p : ℕ) (H : Subgroup G) : oPrimeResidualOf p H ≤ H :=
  (Subgroup.closure_le H).2 fun _ hx => hx.1

theorem exists_surjective_oPrimeResidual {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {C : Type} [Group C] (φ : ↥H ≃* C)
    (hX : CFSG.Quasithin.H13.J4.IsAutTripleM22 (C ⧸ CFSG.pCore 2 C)) :
    ∃ f : ↥(oPrimeResidualOf 3 H) →* NativeSporadic.Carrier .M22, Function.Surjective f := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfinM : Finite H13.J4.M22 := CFSG.Sporadic.Mathieu.fam_m22_simplicity.1
  have hsimple : IsSimpleGroup H13.J4.M22 := isSimpleGroup_M22
  obtain ⟨Z, -, -, hidx, -, -, -, ψ, θ, hψs, -, hcomp, hθs, -, -⟩ := hX
  let ρ : ↥H →* C ⧸ CFSG.pCore 2 C := (QuotientGroup.mk' (CFSG.pCore 2 C)).comp φ.toMonoidHom
  have hρs : Function.Surjective ρ := (QuotientGroup.mk'_surjective _).comp φ.surjective
  have hDodd : ∀ y : C ⧸ CFSG.pCore 2 C, Odd (orderOf y) → y ∈ Subgroup.centralizer (Z : Set _) :=
    fun y hy => mem_of_mul_self_mem_of_odd (by simpa [pow_two] using Subgroup.sq_mem_of_index_two hidx y) hy
  have hAH : oPrimeResidualOf 3 H ≤ H := oPrimeResidualOf_le 3 H
  let ρ' : ↥(oPrimeResidualOf 3 H) →* C ⧸ CFSG.pCore 2 C := ρ.comp (Subgroup.inclusion hAH)
  have hρ'D : ∀ a : ↥(oPrimeResidualOf 3 H), ρ' a ∈ Subgroup.centralizer (Z : Set _) := by
    have hle : oPrimeResidualOf 3 H ≤
        ((Subgroup.centralizer (Z : Set _)).comap ρ).map H.subtype := by
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      obtain ⟨hxH, k, hk⟩ := hx
      refine ⟨⟨x, hxH⟩, ?_, rfl⟩
      show ρ ⟨x, hxH⟩ ∈ Subgroup.centralizer (Z : Set _)
      apply hDodd
      have h1 : orderOf (ρ ⟨x, hxH⟩) ∣ orderOf (⟨x, hxH⟩ : ↥H) := orderOf_map_dvd ρ _
      have h2 : orderOf (⟨x, hxH⟩ : ↥H) = 3 ^ k := by rw [Subgroup.orderOf_mk]; exact hk
      rw [h2] at h1
      exact Odd.of_dvd_nat (Odd.pow ⟨1, by norm_num⟩) h1
    intro a
    obtain ⟨h, hh, hha⟩ := hle a.2
    have hh' : h = Subgroup.inclusion hAH a := Subtype.ext hha
    show ρ (Subgroup.inclusion hAH a) ∈ Subgroup.centralizer (Z : Set _)
    rw [← hh']
    exact hh
  let ρ'' : ↥(oPrimeResidualOf 3 H) →* ↥(Subgroup.centralizer (Z : Set (C ⧸ CFSG.pCore 2 C))) :=
    ρ'.codRestrict _ hρ'D
  let f : ↥(oPrimeResidualOf 3 H) →* H13.J4.M22 := ψ.comp ρ''
  refine ⟨f, ?_⟩
  have hnormal : f.range.Normal := by
    refine ⟨fun y hy m' => ?_⟩
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨g, hg⟩ := hθs (MulAut.conj m')
    obtain ⟨c, hc⟩ := hρs g
    let a' : ↥(oPrimeResidualOf 3 H) :=
      ⟨(c : G) * (a : G) * (c : G)⁻¹, conj_mem_oPrimeResidualOf c a.2⟩
    have hρa' : ρ' a' = g * ρ' a * g⁻¹ := by
      show ρ (Subgroup.inclusion hAH a') = g * ρ (Subgroup.inclusion hAH a) * g⁻¹
      have : Subgroup.inclusion hAH a' = c * Subgroup.inclusion hAH a * c⁻¹ := Subtype.ext rfl
      rw [this, map_mul, map_mul, map_inv, hc]
    have hmem : g * (ρ'' a : C ⧸ CFSG.pCore 2 C) * g⁻¹ ∈ Subgroup.centralizer (Z : Set _) := by
      have : g * (ρ'' a : C ⧸ CFSG.pCore 2 C) * g⁻¹ = ρ' a' := by rw [hρa']; rfl
      rw [this]
      exact hρ'D a'
    have key := hcomp g (ρ'' a) hmem
    have hρ''a' : ρ'' a' = ⟨g * (ρ'' a : C ⧸ CFSG.pCore 2 C) * g⁻¹, hmem⟩ :=
      Subtype.ext (by show ρ' a' = _; rw [hρa']; rfl)
    refine ⟨a', ?_⟩
    show ψ (ρ'' a') = m' * ψ (ρ'' a) * m'⁻¹
    rw [hρ''a', ← key, hg]
    simp [MulAut.conj_apply]
  have hne : f.range ≠ ⊥ := by
    have h3 : 3 ∣ Nat.card H13.J4.M22 := by
      have hc : Nat.card H13.J4.M22 = 443520 := card_M22
      rw [hc]; norm_num
    obtain ⟨m₀, hm₀⟩ := exists_prime_orderOf_dvd_card' 3 h3
    obtain ⟨d₀, hd₀⟩ := hψs m₀
    obtain ⟨c₀, hc₀⟩ := hρs (d₀ : C ⧸ CFSG.pCore 2 C)
    have hn0 : orderOf c₀ ≠ 0 := (orderOf_pos c₀).ne'
    obtain ⟨e, n', hn', hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
    have hn'0 : n' ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hn
      exact hn0 hn
    have hdvd : n' ∣ orderOf c₀ := ⟨3 ^ e, by rw [hn, mul_comm]⟩
    have hord : orderOf (c₀ ^ n') = 3 ^ e := by
      rw [orderOf_pow_of_dvd hn'0 hdvd, hn, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hn'0)]
    have hmemA : ((c₀ ^ n' : ↥H) : G) ∈ oPrimeResidualOf 3 H :=
      Subgroup.subset_closure ⟨(c₀ ^ n').2, e, by rw [Subgroup.orderOf_coe, hord]⟩
    let a₁ : ↥(oPrimeResidualOf 3 H) := ⟨((c₀ ^ n' : ↥H) : G), hmemA⟩
    have hρa₁ : (ρ'' a₁ : C ⧸ CFSG.pCore 2 C) = (d₀ : C ⧸ CFSG.pCore 2 C) ^ n' := by
      show ρ (Subgroup.inclusion hAH a₁) = _
      have : Subgroup.inclusion hAH a₁ = c₀ ^ n' := Subtype.ext rfl
      rw [this, map_pow, hc₀]
    have hρa₁' : ρ'' a₁ = d₀ ^ n' := Subtype.ext (by rw [hρa₁]; rfl)
    have hfa₁ : f a₁ = m₀ ^ n' := by
      show ψ (ρ'' a₁) = _
      rw [hρa₁', map_pow, hd₀]
    intro hbot
    have h1 : f a₁ = 1 := by
      have : f a₁ ∈ f.range := ⟨a₁, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    rw [hfa₁] at h1
    exact hn' (hm₀ ▸ orderOf_dvd_of_pow_eq_one h1)
  have htop : f.range = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal f.range with h | h
    · exact absurd h hne
    · exact h
  exact MonoidHom.range_eq_top.1 htop

end S152V

end CFSG.Quasithin
