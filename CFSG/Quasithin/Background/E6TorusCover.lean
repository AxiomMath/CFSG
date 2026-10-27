module

public import CFSG.Quasithin.Background.E6TorusFacts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

namespace TorusCover

variable {X X' : Type} [Group X] [Group X'] [Finite X] {φ : X →* X'}

omit [Finite X] in
theorem eq_one_of_pow_two_pow {K : Subgroup X} (hK : Odd (Nat.card K)) {k : X} (hk : k ∈ K)
    {m : ℕ} (h : k ^ 2 ^ m = 1) : k = 1 := by
  have h1 : orderOf k ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf k ∣ Nat.card K := by
    have := orderOf_dvd_natCard (⟨k, hk⟩ : K)
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨i, -, hik⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hodd : Odd (orderOf k) := Odd.of_dvd_nat hK h2
  rw [hik] at hodd
  have hi : i = 0 := by
    by_contra hi
    rw [Nat.odd_pow_iff hi] at hodd
    exact absurd hodd (by decide)
  rw [hi, pow_zero] at hik
  exact orderOf_eq_one_iff.1 hik

omit [Finite X] in
theorem conj_central {z : X} (hz : z ∈ Subgroup.center X) (g : X) : z * g * z⁻¹ = g := by
  rw [← Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]

omit [Finite X] in
theorem conj_of_central {z : X} (hz : z ∈ Subgroup.center X) (g : X) : g * z * g⁻¹ = z := by
  rw [Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]

omit [Finite X] in
theorem conj_mem_of_map (hker : φ.ker ≤ Subgroup.center X) (hodd : Odd (Nat.card φ.ker))
    {S : Subgroup X} (hS2 : IsPGroup 2 S) {x : X}
    (hx : φ x ∈ Subgroup.normalizer ((S.map φ : Subgroup X') : Set X')) {s : X} (hs : s ∈ S) :
    x * s * x⁻¹ ∈ S := by
  have h1 : φ (x * s * x⁻¹) ∈ S.map φ := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hx (φ s)).1 (Subgroup.mem_map_of_mem φ hs)
  obtain ⟨s', hs', he⟩ := Subgroup.mem_map.1 h1
  have hkK : s'⁻¹ * (x * s * x⁻¹) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  have hts : x * s * x⁻¹ = s' * (s'⁻¹ * (x * s * x⁻¹)) := by rw [mul_inv_cancel_left]
  obtain ⟨m₁, hm₁⟩ := hS2 ⟨s, hs⟩
  obtain ⟨m₂, hm₂⟩ := hS2 ⟨s', hs'⟩
  have hm₁' : s ^ 2 ^ m₁ = 1 := congrArg Subtype.val hm₁
  have hm₂' : s' ^ 2 ^ m₂ = 1 := congrArg Subtype.val hm₂
  have hN1 : (x * s * x⁻¹) ^ 2 ^ (m₁ + m₂) = 1 := by
    rw [conj_pow, pow_add, pow_mul, hm₁', one_pow, mul_one, mul_inv_cancel]
  have hN2 : s' ^ 2 ^ (m₁ + m₂) = 1 := by
    rw [pow_add, mul_comm, pow_mul, hm₂', one_pow]
  have hcomm : Commute s' (s'⁻¹ * (x * s * x⁻¹)) :=
    Subgroup.mem_center_iff.1 (hker hkK) s'
  have hk1 : (s'⁻¹ * (x * s * x⁻¹)) ^ 2 ^ (m₁ + m₂) = 1 := by
    have h := hN1
    rw [hts, hcomm.mul_pow, hN2, one_mul] at h
    exact h
  have hk' := eq_one_of_pow_two_pow hodd hkK hk1
  rw [hts, hk', mul_one]
  exact hs'

omit [Finite X] in
theorem mem_normalizer_of_map (hker : φ.ker ≤ Subgroup.center X) (hodd : Odd (Nat.card φ.ker))
    {S : Subgroup X} (hS2 : IsPGroup 2 S) {x : X}
    (hx : φ x ∈ Subgroup.normalizer ((S.map φ : Subgroup X') : Set X')) :
    x ∈ Subgroup.normalizer (S : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_of_map hker hodd hS2 hx hh, fun hh => ?_⟩
  have hx' : φ x⁻¹ ∈ Subgroup.normalizer ((S.map φ : Subgroup X') : Set X') := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hx
  have h1 := conj_mem_of_map hker hodd hS2 hx' hh
  have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
  rwa [e] at h1

omit [Finite X] in
theorem comap_mul_comm (hker : φ.ker ≤ Subgroup.center X) {Y : Subgroup X'} (hY : IsCyclic ↥Y)
    {a b : X} (ha : a ∈ Y.comap φ) (hb : b ∈ Y.comap φ) : a * b = b * a := by
  let f : ↥(Y.comap φ) →* ↥Y :=
    (φ.comp (Y.comap φ).subtype).codRestrict Y (fun x => x.2)
  have hf : f.ker ≤ Subgroup.center ↥(Y.comap φ) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hx1 : (x : X) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val ((MonoidHom.mem_ker).1 hx)
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hker hx1) g)
  have := f.isMulCommutative_of_isCyclic_of_ker_le_center hf
  exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

omit [Finite X] in
theorem mul_comm_of_inv (hker : φ.ker ≤ Subgroup.center X) (hodd : Odd (Nat.card φ.ker))
    {u p w : X} (hc : u * p * u⁻¹ * p⁻¹ ∈ φ.ker) (hu : u * (w * u * w⁻¹) ∈ φ.ker)
    (hp : p⁻¹ * (w * p * w⁻¹) ∈ φ.ker) : u * p = p * u := by
  set c := u * p * u⁻¹ * p⁻¹ with hcdef
  have hcc : ∀ g, g * c = c * g := Subgroup.mem_center_iff.1 (hker hc)
  have hA : u * p * u⁻¹ = c * p := by rw [hcdef]; group
  have hB : u⁻¹ * p * u = c⁻¹ * p := by
    have e : p = u⁻¹ * (u * p * u⁻¹) * u := by group
    rw [hA] at e
    have e2 : u⁻¹ * (c * p) * u = c * (u⁻¹ * p * u) := by
      rw [← mul_assoc, hcc u⁻¹]
      group
    rw [e2] at e
    calc u⁻¹ * p * u = c⁻¹ * (c * (u⁻¹ * p * u)) := by group
      _ = c⁻¹ * p := by rw [← e]
  set k₁ := u * (w * u * w⁻¹) with hk₁
  set k₂ := p⁻¹ * (w * p * w⁻¹) with hk₂
  have hk₁c : ∀ g, g * k₁ = k₁ * g := Subgroup.mem_center_iff.1 (hker hu)
  have hk₂c : ∀ g, g * k₂ = k₂ * g := Subgroup.mem_center_iff.1 (hker hp)
  have ewu : w * u * w⁻¹ = u⁻¹ * k₁ := by rw [hk₁, inv_mul_cancel_left]
  have ewp : w * p * w⁻¹ = p * k₂ := by rw [hk₂, mul_inv_cancel_left]
  have hC : u⁻¹ * p * u = c * p := by
    have e1 : w * (u * p * u⁻¹) * w⁻¹ =
        (w * u * w⁻¹) * (w * p * w⁻¹) * (w * u * w⁻¹)⁻¹ := by group
    rw [hA, ewu, ewp] at e1
    have e2 : w * (c * p) * w⁻¹ = c * (p * k₂) := by
      rw [← ewp, ← mul_assoc, hcc w]
      group
    have e3 : (u⁻¹ * k₁) * (p * k₂) * (u⁻¹ * k₁)⁻¹ = (u⁻¹ * p * u) * k₂ := by
      rw [hk₁c u⁻¹]
      have e4 : k₁ * u⁻¹ * (p * k₂) * (k₁ * u⁻¹)⁻¹ = k₁ * (u⁻¹ * (p * k₂) * u) * k₁⁻¹ := by
        group
      rw [e4, conj_central (hker hu)]
      have e5 : u⁻¹ * (p * k₂) * u = u⁻¹ * p * (k₂ * u) := by group
      rw [e5, ← hk₂c u]
      group
    rw [e2, e3] at e1
    calc u⁻¹ * p * u = (u⁻¹ * p * u) * k₂ * k₂⁻¹ := by group
      _ = c * (p * k₂) * k₂⁻¹ := by rw [e1]
      _ = c * p := by group
  have hcc' : c⁻¹ = c := mul_right_cancel (hB.symm.trans hC)
  have hc2 : c ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    nth_rewrite 2 [← hcc']
    exact mul_inv_cancel c
  have hc1 := eq_one_of_pow_two_pow hodd hc hc2
  have e : u * p = c * (p * u) := by rw [hcdef]; group
  rw [e, hc1, one_mul]

end TorusCover

open TorusCover in
theorem e22TorusCover_of_facts (h : E22TorusFacts) : E22TorusCover := by
  intro X X' _ _ _ φ n hsurj hker hodd hn htype S hS
  have : Finite X' := Finite.of_surjective φ hsurj
  set S' := S.map φ with hS'def
  have hS' : IsSylowTwoOf S' ⊤ := by
    refine ⟨le_top, hS.2.1.map φ, ?_⟩
    have h1 : ¬ 2 ∣ S.index := by
      have := hS.2.2
      rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    exact fun h2 => h1 (h2.trans (Subgroup.index_map_dvd S hsurj))
  obtain ⟨Y₀, Y₀', w₀, hY₀N, hY₀'N, hNle, hY₀c, hY₀'c, hY₀card, hcomm₀, hw₀N, hw₀inv,
    hw₀cen⟩ := h X' n hn htype S' hS'
  set P := Y₀.comap φ with hPdef
  set P' := Y₀'.comap φ with hP'def
  obtain ⟨w, hw⟩ := hsurj w₀
  have hS2 : IsPGroup 2 S := hS.2.1
  have hNS : ∀ x, φ x ∈ Subgroup.normalizer (S' : Set X') →
      x ∈ Subgroup.normalizer (S : Set X) := fun x hx => mem_normalizer_of_map hker hodd hS2 hx
  have hmap : ∀ x ∈ Subgroup.normalizer (S : Set X),
      φ x ∈ Subgroup.normalizer (S' : Set X') := fun x hx =>
    Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ hx)
  have hPN : P ≤ Subgroup.normalizer (S : Set X) := fun x hx => hNS x (hY₀N hx)
  have hP'N : P' ≤ Subgroup.normalizer (S : Set X) := fun x hx => hNS x (hY₀'N hx)
  have hKP : φ.ker ≤ P := fun k hk => by
    rw [hPdef, Subgroup.mem_comap, (MonoidHom.mem_ker).1 hk]
    exact Y₀.one_mem
  have hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    comap_mul_comm hker hY₀c ha hb
  have hP'c : ∀ a ∈ P', ∀ b ∈ P', a * b = b * a := fun a ha b hb =>
    comap_mul_comm hker hY₀'c ha hb
  have hwP : ∀ x ∈ P, x * (w * x * w⁻¹) ∈ φ.ker := fun x hx => by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hw, hw₀inv _ hx, mul_inv_cancel]
  have hPP' : ∀ u ∈ P, ∀ p ∈ P', u * p = p * u := by
    intro u hu p hp
    refine mul_comm_of_inv hker hodd (w := w) ?_ (hwP u hu) ?_
    · rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm₀ _ hu _ hp]
      group
    · rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hw, hw₀cen _ hp,
        inv_mul_cancel]
  have hdec : ∀ a ∈ Subgroup.normalizer (S : Set X),
      ∃ d : X, d ∈ Subgroup.normalizer (S : Set X) ∧ (∃ u ∈ P, ∃ p ∈ P', d = u * p) ∧
        ∃ s ∈ S, a = d * s := by
    intro a ha
    have h2 := hNle (hmap a ha)
    have hY₀Y₀' : Y₀ ≤ Subgroup.normalizer (Y₀' : Set X') := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hcomm₀ y hy z hz).symm
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (sup_le hY₀N hY₀'N), Subgroup.coe_mul_of_left_le_normalizer_right _ _ hY₀Y₀'] at h2
    obtain ⟨_, ⟨y₀, hy₀, y₀', hy₀', rfl⟩, s₀, hs₀, he⟩ := h2
    obtain ⟨u, rfl⟩ := hsurj y₀
    obtain ⟨p, rfl⟩ := hsurj y₀'
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hs₀
    have he' : φ u * φ p * φ s = φ a := he
    obtain ⟨k, hkdef⟩ : ∃ k, k = (u * p * s)⁻¹ * a := ⟨_, rfl⟩
    have hk : k ∈ φ.ker := by
      rw [hkdef, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, he', inv_mul_cancel]
    have hu' : u * k ∈ P := P.mul_mem hy₀ (hKP hk)
    refine ⟨u * k * p, ?_, ⟨u * k, hu', p, hy₀', rfl⟩, s, hs, ?_⟩
    · exact Subgroup.mul_mem _ (hPN hu') (hP'N hy₀')
    · have hkc : ∀ g, g * k = k * g := Subgroup.mem_center_iff.1 (hker hk)
      have e1 : a = u * p * s * k := by rw [hkdef, mul_inv_cancel_left]
      calc a = u * p * s * k := e1
        _ = u * k * p * s := by
          rw [mul_assoc (u * p) s k, hkc s, ← mul_assoc, mul_assoc u p k, hkc p, ← mul_assoc]
  refine ⟨?_, ?_⟩
  ·
    intro a ha b hb
    obtain ⟨d₁, hd₁, ⟨u₁, hu₁, p₁, hp₁, rfl⟩, s₁, hs₁, rfl⟩ := hdec a ha
    obtain ⟨d₂, hd₂, ⟨u₂, hu₂, p₂, hp₂, rfl⟩, s₂, hs₂, rfl⟩ := hdec b hb
    have hd : u₁ * p₁ * (u₂ * p₂) = u₂ * p₂ * (u₁ * p₁) := by
      calc u₁ * p₁ * (u₂ * p₂) = u₁ * (p₁ * u₂) * p₂ := by group
        _ = u₁ * (u₂ * p₁) * p₂ := by rw [hPP' u₂ hu₂ p₁ hp₁]
        _ = (u₁ * u₂) * (p₁ * p₂) := by group
        _ = (u₂ * u₁) * (p₂ * p₁) := by rw [hPc u₁ hu₁ u₂ hu₂, hP'c p₁ hp₁ p₂ hp₂]
        _ = u₂ * (u₁ * p₂) * p₁ := by group
        _ = u₂ * (p₂ * u₁) * p₁ := by rw [hPP' u₁ hu₁ p₂ hp₂]
        _ = u₂ * p₂ * (u₁ * p₁) := by group
    set d₁ := u₁ * p₁ with hd₁def
    set d₂ := u₂ * p₂ with hd₂def
    have key : d₁ * s₁ * (d₂ * s₂) * (d₁ * s₁)⁻¹ * (d₂ * s₂)⁻¹ =
        (d₁ * s₁ * d₁⁻¹) * ((d₁ * d₂) * (s₂ * s₁⁻¹) * (d₁ * d₂)⁻¹) *
          ((d₁ * d₂ * d₁⁻¹) * s₂⁻¹ * (d₁ * d₂ * d₁⁻¹)⁻¹) * (d₁ * d₂ * d₁⁻¹ * d₂⁻¹) := by
      group
    have hc : d₁ * d₂ * d₁⁻¹ * d₂⁻¹ = 1 := by rw [hd]; group
    rw [key, hc, mul_one]
    have hN := fun (g : X) (hg : g ∈ Subgroup.normalizer (S : Set X)) (t : X) (ht : t ∈ S) =>
      (Subgroup.mem_normalizer_iff.1 hg t).1 ht
    refine S.mul_mem (S.mul_mem (hN d₁ hd₁ s₁ hs₁) (hN _ (Subgroup.mul_mem _ hd₁ hd₂) _
      (S.mul_mem hs₂ (S.inv_mem hs₁)))) (hN _ ?_ _ (S.inv_mem hs₂))
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hd₁ hd₂) (Subgroup.inv_mem _ hd₁)
  ·
    let Yh : Subgroup X :=
      { carrier := {y | y ∈ P ∧ w * y * w⁻¹ = y⁻¹}
        one_mem' := ⟨P.one_mem, by group⟩
        mul_mem' := fun {x y} hx hy => ⟨P.mul_mem hx.1 hy.1, by
          calc w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) := by group
            _ = x⁻¹ * y⁻¹ := by rw [hx.2, hy.2]
            _ = (x * y)⁻¹ := by rw [hPc x hx.1 y hy.1, mul_inv_rev]⟩
        inv_mem' := fun {x} hx => ⟨P.inv_mem hx.1, by
          calc w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ := by group
            _ = x⁻¹⁻¹ := by rw [hx.2]⟩ }
    have hYhP : Yh ≤ P := fun y hy => hy.1
    let ψ : ↥Yh →* ↥Y₀ := (φ.comp Yh.subtype).codRestrict Y₀ (fun y => y.2.1)
    have hinj : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro y hy
      have hyK : (y : X) ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val hy
      have hy1 : w * (y : X) * w⁻¹ = y := conj_of_central (hker hyK) w
      have hy2 : (y : X) ^ 2 ^ 1 = 1 := by
        rw [pow_one, sq]
        have h3 := y.2.2
        rw [hy1] at h3
        nth_rewrite 2 [h3]
        exact mul_inv_cancel _
      exact Subtype.ext (eq_one_of_pow_two_pow hodd hyK hy2)
    have hsurj' : Function.Surjective ψ := by
      rintro ⟨y₀, hy₀⟩
      obtain ⟨x, rfl⟩ := hsurj y₀
      have hxP : x ∈ P := hy₀
      set k := x * (w * x * w⁻¹) with hkdef
      have hk : k ∈ φ.ker := hwP x hxP
      obtain ⟨r, hr⟩ := hodd
      set z := k ^ r with hzdef
      have hz : z ∈ φ.ker := Subgroup.pow_mem _ hk r
      have hkz : k * z = z⁻¹ := by
        have h1 : k ^ Nat.card φ.ker = 1 := by
          have := pow_card_eq_one' (G := φ.ker) (x := ⟨k, hk⟩)
          exact congrArg Subtype.val this
        rw [hr] at h1
        rw [hzdef, ← mul_inv_eq_one, inv_inv, ← pow_succ', ← pow_add]
        rw [show r + 1 + r = 2 * r + 1 by ring]
        exact h1
      have hwx : w * x * w⁻¹ = x⁻¹ * k := by rw [hkdef, inv_mul_cancel_left]
      have hxz : x * z ∈ Yh := by
        refine ⟨P.mul_mem hxP (hKP hz), ?_⟩
        have hzc : ∀ g, g * z = z * g := Subgroup.mem_center_iff.1 (hker hz)
        calc w * (x * z) * w⁻¹ = (w * x * w⁻¹) * (w * z * w⁻¹) := by group
          _ = x⁻¹ * k * z := by rw [hwx, conj_of_central (hker hz)]
          _ = x⁻¹ * z⁻¹ := by rw [mul_assoc, hkz]
          _ = (x * z)⁻¹ := by
            rw [mul_inv_rev, ← Subgroup.mem_center_iff.1 (hker (Subgroup.inv_mem _ hz)) x⁻¹]
      refine ⟨⟨x * z, hxz⟩, Subtype.ext ?_⟩
      show φ (x * z) = φ x
      rw [map_mul, (MonoidHom.mem_ker).1 hz, mul_one]
    let e : ↥Yh ≃* ↥Y₀ := MulEquiv.ofBijective ψ ⟨hinj, hsurj'⟩
    refine ⟨Yh, w, hYhP.trans hPN, ?_, ?_, ?_, fun y hy => hy.2⟩
    · have := hY₀c
      exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    · rw [Nat.card_congr e.toEquiv, hY₀card]
    · intro hwN
      exact hw₀N (hw ▸ hmap w hwN)

end E2

end CFSG.Quasithin
