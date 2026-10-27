module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148VONCent2
import CFSG.RankThree.PartTwo.Sec14.Ronan148VJ2Syl
import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJExcl

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree.Native.ONTriple Subgroup
open scoped commutatorElement

section Action


theorem exists_inner_of_ON {Q : Type} [Group Q] {Jq : Subgroup Q} (ψ : ↥Jq ≃* GM) {a : Q}
    (haN : a ∈ normalizer (Jq : Set Q)) (ha3 : a ^ 3 = 1)
    (haZ : ∀ z ∈ center ↥Jq, a * (z : Q) = (z : Q) * a) :
    ∃ g ∈ Jq, g ^ 3 = 1 ∧ a * g = g * a ∧ ∀ x ∈ Jq, a * x * a⁻¹ = g * x * g⁻¹ := by
  set β : MulAut ↥Jq := Jq.normalizerMonoidHom ⟨a, haN⟩ with hβ
  have hβx : ∀ x : ↥Jq, ((β x : ↥Jq) : Q) = a * (x : Q) * a⁻¹ := fun x => rfl
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec13.ON134.aut_inner ψ β fun z hz => by
    apply Subtype.ext
    rw [hβx, haZ z hz, mul_inv_cancel_right]
  have hconj : ∀ x ∈ Jq, a * x * a⁻¹ = (g : Q) * x * (g : Q)⁻¹ := by
    intro x hx
    have h := congrArg Subtype.val (hg ⟨x, hx⟩)
    rw [hβx] at h
    simpa using h
  have hag : a * (g : Q) = (g : Q) * a := by
    have h := hconj g g.2
    calc a * (g : Q) = a * (g : Q) * a⁻¹ * a := by group
      _ = (g : Q) * (g : Q) * (g : Q)⁻¹ * a := by rw [h]
      _ = (g : Q) * a := by group
  have hg3 : g ^ 3 ∈ center ↥Jq := by
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    have h3 : ∀ y ∈ Jq, (g : Q) ^ 3 * y * ((g : Q) ^ 3)⁻¹ = a ^ 3 * y * (a ^ 3)⁻¹ := by
      intro y hy
      have e1 := hconj y hy
      have e2 := hconj (a * y * a⁻¹) (by
        have := (mem_normalizer_iff.mp haN y).mp hy
        exact this)
      have e3 := hconj (a * (a * y * a⁻¹) * a⁻¹) (by
        have h1 := (mem_normalizer_iff.mp haN y).mp hy
        exact (mem_normalizer_iff.mp haN _).mp h1)
      calc (g : Q) ^ 3 * y * ((g : Q) ^ 3)⁻¹ =
          (g : Q) * ((g : Q) * ((g : Q) * y * (g : Q)⁻¹) * (g : Q)⁻¹) * (g : Q)⁻¹ := by
            rw [pow_three]; group
        _ = a * (a * (a * y * a⁻¹) * a⁻¹) * a⁻¹ := by rw [← e1, ← e2, ← e3]
        _ = a ^ 3 * y * (a ^ 3)⁻¹ := by rw [pow_three]; group
    have h := h3 x x.2
    rw [ha3, one_mul, inv_one, mul_one] at h
    have : (g : Q) ^ 3 * x = x * (g : Q) ^ 3 := by
      calc (g : Q) ^ 3 * x = (g : Q) ^ 3 * x * ((g : Q) ^ 3)⁻¹ * (g : Q) ^ 3 := by group
        _ = x * (g : Q) ^ 3 := by rw [h]
    simpa using this.symm
  have hZ3 : (g ^ 3) ^ 3 = 1 := by
    rw [CFSG.RankThree.PartTwo.Sec13.ON134.mem_center_iff_model ψ] at hg3
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hg3
    apply ψ.injective
    rw [map_pow, ← hk, map_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [relG.xcube]
  have hg9 : g ^ 3 ^ 2 = 1 := by rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul]; exact hZ3
  have hg3' : g ^ 3 = 1 := CFSG.RankThree.PartTwo.Sec13.ON134.pow_three_eq_one ψ hg9
  refine ⟨g, g.2, ?_, hag, hconj⟩
  have := congrArg Subtype.val hg3'
  simpa using this

theorem exists_noncentral_and_sup_eq_of_ON {Q : Type} [Group Q] [Finite Q] {Aq Jq : Subgroup Q}
    (hAab : ∀ x ∈ Aq, ∀ y ∈ Aq, x * y = y * x) (hA3 : ∀ a ∈ Aq, a ^ 3 = 1)
    (hF3 : ∀ w : Q, w ∈ centralizer (Aq : Set Q) → w ^ 3 = 1 → w ∈ Aq) (hA27 : Nat.card Aq = 27)
    (hAJ : Aq ≤ normalizer (Jq : Set Q)) (ψ : ↥Jq ≃* GM) (hZ3 : Nat.card (center ↥Jq) = 3)
    {dq : Q} (hdA : dq ∈ Aq) (hdJ : dq ∈ Jq) (hd1 : dq ≠ 1) (hdC : ∀ x ∈ Jq, dq * x = x * dq) :
    (∃ j ∈ Aq ⊓ Jq, ∃ y ∈ Jq, j * y ≠ y * j) ∧
      Aq ⊓ centralizer (Jq : Set Q) ⊔ Aq ⊓ Jq = Aq := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set d' : ↥Jq := ⟨dq, hdJ⟩ with hd'
  have hd'Z : d' ∈ center ↥Jq := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hdC g g.2).symm
  have hd'1 : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hZd : center ↥Jq = zpowers d' :=
    (CFSG.RankThree.PartTwo.Sec14.Ronan148J.zpowers_eq_of_card_three hZ3 hd'Z hd'1).symm
  have hcen : ∀ z ∈ center ↥Jq, ∃ k : ℤ, (z : Q) = dq ^ k := by
    intro z hz
    rw [hZd] at hz
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hz
    exact ⟨k, by rw [← hk]; simp [hd']⟩
  have haZ : ∀ a ∈ Aq, ∀ z ∈ center ↥Jq, a * (z : Q) = (z : Q) * a := by
    intro a ha z hz
    obtain ⟨k, hk⟩ := hcen z hz
    rw [hk]
    exact (Commute.zpow_right (hAab a ha dq hdA) k).eq
  have hinner := fun {a : Q} (ha : a ∈ Aq) => exists_inner_of_ON ψ (hAJ ha) (hA3 a ha) (haZ a ha)
  have hd3 : dq ^ 3 = 1 := hA3 dq hdA
  have hcard3 : Nat.card (zpowers dq) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hgen : ∀ {u v : Q}, u ∈ Aq → v ∈ Aq → u ∉ zpowers dq → v ∉ zpowers dq ⊔ zpowers u →
      zpowers dq ⊔ zpowers u ⊔ zpowers v = Aq := by
    intro u v hu hv hud hvE
    have h9 := CFSG.RankThree.PartTwo.Sec14.Ronan148J.card_zpowers_sup_zpowers_eq_nine
      (hAab dq hdA u hu) hd3 hd1 (hA3 u hu) hud
    refine j2Syl_eq_of_nine_lt hA27 h9 le_sup_left
      (sup_le (sup_le (zpowers_le.mpr hdA) (zpowers_le.mpr hu)) (zpowers_le.mpr hv))
      (mem_sup_right (mem_zpowers v)) hvE
  have hex : ∀ {E : Subgroup Q}, Nat.card E < 27 → ∃ u ∈ Aq, u ∉ E := by
    intro E hE
    by_contra hall
    push Not at hall
    have := card_le_of_le (fun u hu => hall u hu : Aq ≤ E)
    omega
  have hcomm : ∀ {u v x : Q}, u ∈ Aq → v ∈ Aq → u ∉ zpowers dq →
      v ∉ zpowers dq ⊔ zpowers u → x * dq = dq * x → x * u = u * x → x * v = v * x →
      x ∈ centralizer (Aq : Set Q) := by
    intro u v x hu hv hud hvE hxd hxu hxv
    have hle : zpowers dq ⊔ zpowers u ⊔ zpowers v ≤ centralizer ({x} : Set Q) := by
      refine sup_le (sup_le ?_ ?_) ?_ <;> rw [zpowers_le, mem_centralizer_singleton_iff]
      · exact hxd.symm
      · exact hxu.symm
      · exact hxv.symm
    rw [hgen hu hv hud hvE] at hle
    rw [mem_centralizer_iff]
    intro a ha
    exact (mem_centralizer_singleton_iff.mp (hle ha))
  obtain ⟨a₁, ha₁, ha₁d⟩ := hex (E := zpowers dq) (by rw [hcard3]; norm_num)
  have h9₁ := CFSG.RankThree.PartTwo.Sec14.Ronan148J.card_zpowers_sup_zpowers_eq_nine
    (hAab dq hdA a₁ ha₁) hd3 hd1 (hA3 a₁ ha₁) ha₁d
  obtain ⟨a₂, ha₂, ha₂E⟩ := hex (E := zpowers dq ⊔ zpowers a₁) (by rw [h9₁]; norm_num)
  obtain ⟨g₁, hg₁J, hg₁3, ha₁g₁, hc₁⟩ := hinner ha₁
  obtain ⟨g₂, hg₂J, hg₂3, ha₂g₂, hc₂⟩ := hinner ha₂
  have hcomm12 : ∀ y ∈ Jq, g₁ * g₂ * y * (g₁ * g₂)⁻¹ = g₂ * g₁ * y * (g₂ * g₁)⁻¹ := by
    intro y hy
    have hya₂ : a₂ * y * a₂⁻¹ ∈ Jq := (mem_normalizer_iff.mp (hAJ ha₂) y).mp hy
    have hg₁y : g₁ * y * g₁⁻¹ ∈ Jq := Jq.mul_mem (Jq.mul_mem hg₁J hy) (Jq.inv_mem hg₁J)
    calc g₁ * g₂ * y * (g₁ * g₂)⁻¹ = g₁ * (g₂ * y * g₂⁻¹) * g₁⁻¹ := by group
      _ = a₁ * (a₂ * y * a₂⁻¹) * a₁⁻¹ := by rw [← hc₂ y hy, ← hc₁ _ hya₂]
      _ = a₁ * a₂ * y * (a₁ * a₂)⁻¹ := by group
      _ = a₂ * a₁ * y * (a₂ * a₁)⁻¹ := by rw [hAab a₁ ha₁ a₂ ha₂]
      _ = a₂ * (a₁ * y * a₁⁻¹) * a₂⁻¹ := by group
      _ = g₂ * (g₁ * y * g₁⁻¹) * g₂⁻¹ := by rw [hc₁ y hy, hc₂ _ hg₁y]
      _ = g₂ * g₁ * y * (g₂ * g₁)⁻¹ := by group
  have h12 : (⟨g₁, hg₁J⟩ : ↥Jq) * ⟨g₂, hg₂J⟩ * (⟨g₁, hg₁J⟩ : ↥Jq)⁻¹ * (⟨g₂, hg₂J⟩ : ↥Jq)⁻¹ ∈
      center ↥Jq := by
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    have hy : (g₂ * g₁)⁻¹ * (x : Q) * (g₂ * g₁) ∈ Jq :=
      Jq.mul_mem (Jq.mul_mem (Jq.inv_mem (Jq.mul_mem hg₂J hg₁J)) x.2) (Jq.mul_mem hg₂J hg₁J)
    have h := hcomm12 _ hy
    have key : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ * (x : Q) * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹)⁻¹ = (x : Q) := by
      calc g₁ * g₂ * g₁⁻¹ * g₂⁻¹ * (x : Q) * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹)⁻¹
          = g₁ * g₂ * ((g₂ * g₁)⁻¹ * (x : Q) * (g₂ * g₁)) * (g₁ * g₂)⁻¹ := by group
        _ = g₂ * g₁ * ((g₂ * g₁)⁻¹ * (x : Q) * (g₂ * g₁)) * (g₂ * g₁)⁻¹ := h
        _ = (x : Q) := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    symm
    calc g₁ * g₂ * g₁⁻¹ * g₂⁻¹ * (x : Q)
        = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ * (x : Q) * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹)⁻¹ *
          (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) := by group
      _ = (x : Q) * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) := by rw [key]
  obtain ⟨x, hx3, hxZ, hx1, hx2⟩ := Sec4.Ronan148V.exists_centralizer_two ψ (k₁ := ⟨g₁, hg₁J⟩)
    (k₂ := ⟨g₂, hg₂J⟩) (Subtype.ext (by simpa using hg₁3)) (Subtype.ext (by simpa using hg₂3)) h12
  have hxg₁ : (x : Q) * g₁ = g₁ * x := by simpa using congrArg Subtype.val hx1
  have hxg₂ : (x : Q) * g₂ = g₂ * x := by simpa using congrArg Subtype.val hx2
  have hxa : ∀ {a g : Q}, (∀ y ∈ Jq, a * y * a⁻¹ = g * y * g⁻¹) → (x : Q) * g = g * x →
      (x : Q) * a = a * x := by
    intro a g hc hxg
    have h := hc x x.2
    have : g * (x : Q) * g⁻¹ = x := by rw [← hxg, mul_inv_cancel_right]
    rw [this] at h
    calc (x : Q) * a = a * (x : Q) * a⁻¹ * a := by rw [h]
      _ = a * x := by group
  have hxA : (x : Q) ∈ centralizer (Aq : Set Q) :=
    hcomm ha₁ ha₂ ha₁d ha₂E (hdC x x.2).symm (hxa hc₁ hxg₁) (hxa hc₂ hxg₂)
  have hxAq : (x : Q) ∈ Aq := hF3 _ hxA (by simpa using congrArg Subtype.val hx3)
  have hxnc : ∃ y ∈ Jq, (x : Q) * y ≠ y * x := by
    by_contra hall
    push Not at hall
    apply hxZ
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hall g g.2).symm
  refine ⟨⟨x, ⟨hxAq, x.2⟩, hxnc⟩, ?_⟩
  have hxd : (x : Q) ∉ zpowers dq := by
    intro h
    obtain ⟨y, hy, hxy⟩ := hxnc
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    apply hxy
    rw [← hk]
    exact (Commute.zpow_left (hdC y hy) k).eq
  have h9x := CFSG.RankThree.PartTwo.Sec14.Ronan148J.card_zpowers_sup_zpowers_eq_nine
    (hAab dq hdA x hxAq) hd3 hd1 (hA3 x hxAq) hxd
  obtain ⟨a, ha, haE⟩ := hex (E := zpowers dq ⊔ zpowers (x : Q)) (by rw [h9x]; norm_num)
  obtain ⟨g, hgJ, hg3, hag, hc⟩ := hinner ha
  have hgx : g * (x : Q) = (x : Q) * g := by
    have h := hc x x.2
    have hax : a * (x : Q) * a⁻¹ = x := by rw [hAab a ha x hxAq, mul_inv_cancel_right]
    rw [hax] at h
    calc g * (x : Q) = g * (x : Q) * g⁻¹ * g := by group
      _ = (x : Q) * g := by rw [← h]
  have hgA : g ∈ centralizer (Aq : Set Q) :=
    hcomm hxAq ha hxd haE (hdC g hgJ).symm hgx hag.symm
  have hgAq : g ∈ Aq := hF3 g hgA hg3
  set c := a * g⁻¹ with hcdef
  have hcA : c ∈ Aq := Aq.mul_mem ha (Aq.inv_mem hgAq)
  have hcC : c ∈ centralizer (Jq : Set Q) := by
    rw [mem_centralizer_iff]
    intro y hy
    have hy' : g⁻¹ * y * g ∈ Jq := Jq.mul_mem (Jq.mul_mem (Jq.inv_mem hgJ) hy) hgJ
    have h := hc _ hy'
    have h2 : c * y * c⁻¹ = y := by
      calc c * y * c⁻¹ = a * (g⁻¹ * y * g) * a⁻¹ := by rw [hcdef]; group
        _ = g * (g⁻¹ * y * g) * g⁻¹ := h
        _ = y := by group
    calc y * c = c * y * c⁻¹ * c := by rw [h2]
      _ = c * y := by group
  have ha' : a ∈ Aq ⊓ centralizer (Jq : Set Q) ⊔ Aq ⊓ Jq := by
    have hacg : a = c * g := by rw [hcdef]; group
    rw [hacg]
    exact mul_mem (mem_sup_left ⟨hcA, hcC⟩) (mem_sup_right ⟨hgAq, hgJ⟩)
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  calc Aq = zpowers dq ⊔ zpowers (x : Q) ⊔ zpowers a := (hgen hxAq ha hxd haE).symm
    _ ≤ Aq ⊓ centralizer (Jq : Set Q) ⊔ Aq ⊓ Jq := by
      refine sup_le (sup_le ?_ ?_) (zpowers_le.mpr ha')
      · exact zpowers_le.mpr (mem_sup_right ⟨hdA, hdJ⟩)
      · exact zpowers_le.mpr (mem_sup_right ⟨hxAq, x.2⟩)

end Action

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
