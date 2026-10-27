module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Aut1
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Aut2
public import CFSG.Quasithin.EmptyFaithful.S151bW3Five

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

namespace SixData151b

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

theorem stab₂_of_stab₁ (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256) {g : MulAut W}
    (hg : ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) (hs : S.Stab₁ g) : S.Stab₂ g := by
  rcases S.stab_or_swap hW hg with h | h
  · exact h.2
  · exact absurd hs (S.not_stab₁_of_swap hcard h)

theorem mem_zpowers_a₁_conj (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256) {g : MulAut W}
    (hg : ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) (hs : S.Stab₁ g ∧ S.Stab₂ g) :
    g * S.a₁ * g⁻¹ ∈ Subgroup.zpowers S.a₁ := by
  have h := S.swap.mem_zpowers_a₂_conj hW hcard (g := g) (fun z hz => ?_) ⟨hs.2, hs.1⟩
  · rwa [swap_a₂] at h
  · rw [sup_comm] at hz ⊢
    exact hg z hz

theorem false_of_fix_W₁_order_three (hW : ∀ w : W, w ^ 2 = 1) {Mb : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) (hτ : S.τ ∈ Mb)
    (hNoE9 : ¬ ∃ E : Subgroup (MulAut W), E ≤ Mb ∧ IsElemAbelian 3 E ∧ Nat.card E = 9)
    {c : MulAut W} (hc : c ∈ Mb) (hc₁ : ∀ w ∈ S.W₁, c w = w) (hc₂ : S.Stab₂ c)
    (hc3 : orderOf c = 3) : False := by
  have hswap : S.Swap₁₂ S.τ := S.swap_of_conj hW (hnorm _ hτ) S.τ₁₂
  have hτ₂ : ∀ w ∈ S.W₂, S.τ⁻¹ w ∈ S.W₁ := fun w hw => S.swap_inv_mem_W₂ hswap hw
  have hτ₁ : ∀ w ∈ S.W₁, S.τ⁻¹ w ∈ S.W₂ := fun w hw =>
    S.swap.swap_inv_mem_W₂ (g := S.τ) ⟨hswap.2, hswap.1⟩ hw
  set d : MulAut W := S.τ * c * S.τ⁻¹ with hd
  have hdW₂ : ∀ w ∈ S.W₂, d w = w := by
    intro w hw
    show S.τ (c (S.τ⁻¹ w)) = w
    rw [hc₁ _ (hτ₂ w hw)]
    exact MulAut.apply_inv_self W S.τ w
  have hdW₁ : ∀ w ∈ S.W₁, d w ∈ S.W₁ := by
    intro w hw
    show S.τ (c (S.τ⁻¹ w)) ∈ S.W₁
    exact hswap.2 _ ((hc₂ _).mp (hτ₁ w hw))
  have hcd : c * d = d * c := S.commute_of_fix_W₁_W₂ hc₁ (fun w hw => (hc₂ w).mp hw) hdW₂ hdW₁
  have hdMb : d ∈ Mb := Mb.mul_mem (Mb.mul_mem hτ hc) (Mb.inv_mem hτ)
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hd3 : orderOf d = 3 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [hd, conj_pow, hc3']; group
    · intro hd1
      have h' : S.τ⁻¹ * d * S.τ = c := by rw [hd]; group
      rw [hd1, mul_one, inv_mul_cancel] at h'
      rw [← h', orderOf_one] at hc3
      omega
  have hx₁ : ∀ x ∈ Subgroup.zpowers c, ∀ w ∈ S.W₁, x w = w := fun x hx w hw =>
    mem_centSub.mp ((Subgroup.zpowers_le.mpr (mem_centSub.mpr hc₁) :
      Subgroup.zpowers c ≤ centSub S.W₁) hx) w hw
  have hy₂ : ∀ x ∈ Subgroup.zpowers d, ∀ w ∈ S.W₂, x w = w := fun x hx w hw =>
    mem_centSub.mp ((Subgroup.zpowers_le.mpr (mem_centSub.mpr hdW₂) :
      Subgroup.zpowers d ≤ centSub S.W₂) hx) w hw
  exact hNoE9 (exists_elemAbelian_nine_of_commute151b hc hdMb hcd hc3 hd3 fun x hxc hxd =>
    S.eq_one_of_fix_W₁_W₂ (hx₁ x hxc) (hy₂ x hxd))

theorem eq_zpowers_a₂_of_fix (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {Mb : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) (hτ : S.τ ∈ Mb)
    (hNoE9 : ¬ ∃ E : Subgroup (MulAut W), E ≤ Mb ∧ IsElemAbelian 3 E ∧ Nat.card E = 9)
    {F : Subgroup (MulAut W)} (hFM : F ≤ Mb) (hF₁ : ∀ f ∈ F, ∀ w ∈ S.W₁, f w = w)
    (hF₂ : ∀ f ∈ F, f * S.a₂ = S.a₂ * f) (ha₂ : S.a₂ ∈ F) : F = Subgroup.zpowers S.a₂ := by
  have hst₁ : ∀ f ∈ F, S.Stab₁ f := by
    intro f hf w
    refine ⟨fun hw => by rw [hF₁ f hf w hw]; exact hw, fun hfw => ?_⟩
    have h1 : f w = w := f.injective (hF₁ f hf _ hfw)
    rw [← h1]
    exact hfw
  have hst₂ : ∀ f ∈ F, S.Stab₂ f := fun f hf =>
    S.stab₂_of_stab₁ hW hcard (hnorm f (hFM hf)) (hst₁ f hf)
  have hfree : ∀ f ∈ F, ∀ w ∈ S.W₂, w ≠ 1 → f w = w → f = 1 := by
    intro f hf w hw hw1 hfw
    have h2 := S.swap.fix_W₁_of_commute hW hcard (g := f) (by rw [swap_a₁]; exact hF₂ f hf)
      hw hw1 hfw
    exact S.eq_one_of_fix_W₁_W₂ (hF₁ f hf) fun v hv => h2 v hv
  have hno2 : ∀ c ∈ F, c ^ 2 = 1 → c = 1 := by
    intro c hc hc2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcs : c ∈ stabSub S.W₂ := mem_stabSub.mpr fun u => (hst₂ c hc u).symm
    obtain ⟨z, hz, hz1, hzfix⟩ := S.swap.exists_fixed_W₁ hW hcard
      (isPGroup_zpowers_of_pow_eq_one151b hc2) fun g hg u =>
        (mem_stabSub.mp ((Subgroup.zpowers_le.mpr hcs : Subgroup.zpowers c ≤ _) hg) u).symm
    exact hfree c hc z hz hz1 (hzfix c (Subgroup.mem_zpowers c))
  have hle15 : Nat.card F ≤ 15 := by
    obtain ⟨w₀, hw₀, hw₀1⟩ : ∃ w ∈ S.W₂, w ≠ 1 := by
      by_contra hcon
      have hbot : S.W₂ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun x hx =>
        by_contra fun hx1 => hcon ⟨x, hx, hx1⟩
      have h1 := Subgroup.card_eq_one.mpr hbot
      have h16 := S.card_W₂ hcard
      omega
    let φ : Option F → S.W₂ := fun o => o.elim 1 fun f => ⟨f.1 w₀, (hst₂ f.1 f.2 w₀).mp hw₀⟩
    have hφ : Function.Injective φ := by
      intro o₁ o₂ h
      rcases o₁ with _ | f₁ <;> rcases o₂ with _ | f₂
      · rfl
      · exfalso
        have h1 : f₂.1 w₀ = 1 := (congrArg Subtype.val h).symm
        exact hw₀1 (f₂.1.injective (h1.trans (map_one f₂.1).symm))
      · exfalso
        have h1 : f₁.1 w₀ = 1 := congrArg Subtype.val h
        exact hw₀1 (f₁.1.injective (h1.trans (map_one f₁.1).symm))
      · have h' : f₁.1 w₀ = f₂.1 w₀ := congrArg Subtype.val h
        have hmem : f₂.1⁻¹ * f₁.1 ∈ F := F.mul_mem (F.inv_mem f₂.2) f₁.2
        have hfix : (f₂.1⁻¹ * f₁.1) w₀ = w₀ := by
          show f₂.1⁻¹ (f₁.1 w₀) = w₀
          rw [h']
          exact MulAut.inv_apply_self W f₂.1 w₀
        have h1 : f₂.1 = f₁.1 := inv_mul_eq_one.mp (hfree _ hmem w₀ hw₀ hw₀1 hfix)
        exact congrArg some (Subtype.ext h1.symm)
    have := Nat.card_le_card_of_injective φ hφ
    rw [Finite.card_option, S.card_W₂ hcard] at this
    omega
  have hle : Subgroup.zpowers S.a₂ ≤ F := Subgroup.zpowers_le.mpr ha₂
  have hdvd5 : 5 ∣ Nat.card F := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, S.orderOf_a₂_five] at this
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hF5 : Nat.card F = 5 := by
    have hcases : Nat.card F = 5 ∨ Nat.card F = 10 ∨ Nat.card F = 15 := by omega
    rcases hcases with h | h | h
    · exact h
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (h ▸ (by norm_num : 2 ∣ 10))
      have hxo : orderOf (x : MulAut W) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
      have hx2 : (x : MulAut W) ^ 2 = 1 := by
        have := pow_orderOf_eq_one (x : MulAut W)
        rwa [hxo] at this
      have h1 := hno2 x x.2 hx2
      rw [h1, orderOf_one] at hxo
      omega
    · exfalso
      have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (h ▸ (by norm_num : 3 ∣ 15))
      have hxo : orderOf (x : MulAut W) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
      exact S.false_of_fix_W₁_order_three hW hnorm hτ hNoE9 (hFM x.2) (hF₁ x x.2) (hst₂ x x.2) hxo
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, S.orderOf_a₂_five, hF5])).symm

theorem odd_mem_zpowers_a₂ (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {Mb : Subgroup (MulAut W)} (hA : S.A₁ ⊔ S.A₂ ≤ Mb)
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) (hτ : S.τ ∈ Mb)
    (hNoE9 : ¬ ∃ E : Subgroup (MulAut W), E ≤ Mb ∧ IsElemAbelian 3 E ∧ Nat.card E = 9)
    {g : MulAut W} (hg : g ∈ Mb) (hs : S.Stab₁ g) {z : W} (hz : z ∈ S.W₁) (hz1 : z ≠ 1)
    (hfix : g z = z) (hodd : Odd (orderOf g)) : g ∈ Subgroup.zpowers S.a₂ := by
  have hs₂ : S.Stab₂ g := S.stab₂_of_stab₁ hW hcard (hnorm g hg) hs
  have hc₁ : g * S.a₁ = S.a₁ * g := commute_of_conj_odd_five151b S.orderOf_a₁_five
    (S.mem_zpowers_a₁_conj hW hcard (hnorm g hg) ⟨hs, hs₂⟩) hodd
  have hc₂ : g * S.a₂ = S.a₂ * g := commute_of_conj_odd_five151b S.orderOf_a₂_five
    (S.mem_zpowers_a₂_conj hW hcard (hnorm g hg) ⟨hs, hs₂⟩) hodd
  have hgW₁ := S.fix_W₁_of_commute hW hcard hc₁ hz hz1 hfix
  have key := S.eq_zpowers_a₂_of_fix hW hcard hnorm hτ hNoE9
    (F := Mb ⊓ centSub S.W₁ ⊓ Subgroup.centralizer {S.a₂}) (inf_le_left.trans inf_le_left)
    (fun f hf w hw => mem_centSub.mp hf.1.2 w hw)
    (fun f hf => Subgroup.mem_centralizer_singleton_iff.mp hf.2)
    ⟨⟨hA (Subgroup.mem_sup_right S.a₂_mem), mem_centSub.mpr fun w hw => S.a₂_fix_W₁ hw⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  rw [← key]
  exact ⟨⟨hg, mem_centSub.mpr hgW₁⟩, Subgroup.mem_centralizer_singleton_iff.mpr hc₂⟩

end SixData151b

end CFSG.Quasithin
