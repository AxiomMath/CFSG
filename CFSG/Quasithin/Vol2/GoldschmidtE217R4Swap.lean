module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R4L27
public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Prod
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer

namespace E217R4

theorem eq_one_of_central_L27 {K : Type*} [Group K] [Finite K] (hK : L27 K) {x : K}
    (hx : ∀ y : K, y * x = x * y) : x = 1 := by
  by_contra hx1
  have := hK.simple
  have hcenter : Subgroup.center K = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · exfalso
      have hxc : x ∈ Subgroup.center K := Subgroup.mem_center_iff.2 hx
      rw [h, Subgroup.mem_bot] at hxc
      exact hx1 hxc
    · exact h
  have hcomm : ∀ y w : K, y * w = w * y := fun y w => by
    have hw : w ∈ Subgroup.center K := by
      rw [hcenter]
      exact Subgroup.mem_top w
    exact Subgroup.mem_center_iff.1 hw y
  obtain ⟨D, hD, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup K) ≤ ⊤)
    (IsPGroup.of_card (n := 0) (by simp))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD8 := hK.card2 D hD
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 2 (by
    rw [hD8]
    norm_num)
  have hz2 : (z : K) * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz, pow_two] at this
    exact congrArg Subtype.val this
  have hz1 : (z : K) ≠ 1 := fun h => by
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    omega
  have h8 := hK.cent2 (z : K) hz2 hz1
  have htop : Subgroup.centralizer ({(z : K)} : Set K) = ⊤ :=
    eq_top_iff.2 fun y _ => Subgroup.mem_centralizer_singleton_iff.2 (hcomm y z)
  rw [htop, Subgroup.card_top] at h8
  obtain ⟨a, ha3, ha1, -⟩ := hK.inv3 (z : K) hz2 hz1
  have h3 : orderOf a ∣ Nat.card K := orderOf_dvd_natCard a
  rw [orderOf_eq_prime ha3 ha1, h8] at h3
  omega

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem map_conj_eq_of_swap {K₁ K₂ : Subgroup Γ} {t : Γ} (hKn : (K₁ ⊔ K₂).Normal)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hd : K₁ ⊓ K₂ = ⊥) (hL₁ : L27 ↥K₁)
    (hL₂ : L27 ↥K₂) (hK₂ : K₂ = K₁.map (MulAut.conj t).toMonoidHom) :
    K₂.map (MulAut.conj t).toMonoidHom = K₁ := by
  set f : Γ →* Γ := (MulAut.conj t).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj t).injective
  set L : Subgroup Γ := K₂.map f with hL
  have hLN : L ≤ K₁ ⊔ K₂ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hKn.conj_mem y (Subgroup.mem_sup_right hy) t
  have hNK₁ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set Γ) := by
    refine sup_le Subgroup.le_normalizer ?_
    exact (show K₂ ≤ Subgroup.centralizer (K₁ : Set Γ) from fun b hb =>
      Subgroup.mem_centralizer_iff.2 fun a ha => hc a ha b hb).trans
      (Subgroup.centralizer_le_normalizer _)
  have hNK₂ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set Γ) := by
    refine sup_le ?_ Subgroup.le_normalizer
    exact (show K₁ ≤ Subgroup.centralizer (K₂ : Set Γ) from fun a ha =>
      Subgroup.mem_centralizer_iff.2 fun b hb => (hc a ha b hb).symm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hLs : IsSimpleGroup ↥L :=
    haveI := hL₂.simple
    (K₂.equivMapOfInjective f hfinj).symm.isSimpleGroup
  have hcardL : Nat.card L = Nat.card K₂ := Subgroup.card_map_of_injective hfinj
  have hcard₂ : Nat.card K₂ = Nat.card K₁ := by
    rw [hK₂]
    exact Subgroup.card_map_of_injective hfinj
  have hLnorm : ∀ n ∈ K₁ ⊔ K₂, ∀ l ∈ L, n * l * n⁻¹ ∈ L := by
    intro n hn l hl
    obtain ⟨y, hy, rfl⟩ := hl
    have hn' : t⁻¹ * n * t ∈ K₁ ⊔ K₂ := by
      have := hKn.conj_mem n hn t⁻¹
      simpa using this
    refine ⟨(t⁻¹ * n * t) * y * (t⁻¹ * n * t)⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hNK₂ hn') y).1 hy
    · show t * ((t⁻¹ * n * t) * y * (t⁻¹ * n * t)⁻¹) * t⁻¹ = n * (t * y * t⁻¹) * n⁻¹
      group
  have hnormal : ∀ K : Subgroup Γ, (K₁ ⊔ K₂ ≤ Subgroup.normalizer (K : Set Γ)) →
      ((L ⊓ K).subgroupOf L).Normal := by
    intro K hK
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 hn.1) (L.inv_mem g.2), ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 (hK (hLN g.2)) (n : Γ)).1 hn.2
    simpa using this
  have hK₁ne : Nontrivial ↥K₁ := hL₁.simple.toNontrivial
  have hK₁ne' : K₁ ≠ ⊥ := fun h => by
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥K₁)
    apply ha
    apply Subtype.ext
    have : (a : Γ) ∈ (⊥ : Subgroup Γ) := h ▸ a.2
    exact this
  have hn₁ := hnormal K₁ hNK₁
  have hn₂ := hnormal K₂ hNK₂
  have hdec : ∀ c ∈ K₁ ⊔ K₂, ∃ x ∈ K₁, ∃ y ∈ K₂, x * y = c := fun c hc' =>
    exists_mul_of_mem_sup hc hc'
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ K₁).subgroupOf L) with h₁ | h₁
  swap
  ·
    have hLK₁ : L ≤ K₁ := fun x hx => by
      have hmem : (⟨x, hx⟩ : ↥L) ∈ (L ⊓ K₁).subgroupOf L := by
        rw [h₁]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hmem).2
    exact Subgroup.eq_of_le_of_card_ge hLK₁ (by rw [hcardL, hcard₂])
  exfalso
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ K₂).subgroupOf L) with h₂ | h₂
  swap
  ·
    have hLK₂ : L ≤ K₂ := fun x hx => by
      have hmem : (⟨x, hx⟩ : ↥L) ∈ (L ⊓ K₂).subgroupOf L := by
        rw [h₂]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hmem).2
    have hLeq : L = K₂ := Subgroup.eq_of_le_of_card_ge hLK₂ (by rw [hcardL])
    have hmapeq : K₂.map f = K₂ := hL.symm.trans hLeq
    have hK12 : K₁ = K₂ := Subgroup.map_injective hfinj (hK₂.symm.trans hmapeq.symm)
    apply hK₁ne'
    rw [← hd, ← hK12, inf_idem]
  have hcomm : ∀ (K : Subgroup Γ), K₁ ⊔ K₂ ≤ Subgroup.normalizer (K : Set Γ) →
      (∀ x ∈ L ⊓ K, x = 1) → K ≤ K₁ ⊔ K₂ → ∀ l ∈ L, ∀ k ∈ K, l * k = k * l := by
    intro K hK hx hKN l hl k hk
    have h1 : l * k * l⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hK (hLN hl)) k).1 hk
    have h2 : k * l⁻¹ * k⁻¹ ∈ L := hLnorm k (hKN hk) l⁻¹ (L.inv_mem hl)
    have h3 : l * k * l⁻¹ * k⁻¹ = 1 := hx _ ⟨by
      have : l * k * l⁻¹ * k⁻¹ = l * (k * l⁻¹ * k⁻¹) := by group
      rw [this]
      exact L.mul_mem hl h2, K.mul_mem h1 (K.inv_mem hk)⟩
    calc l * k = (l * k * l⁻¹ * k⁻¹) * (k * l) := by group
      _ = k * l := by rw [h3, one_mul]
  have h1' : ∀ x ∈ L ⊓ K₁, x = 1 := fun x hx => by
    have hmem : (⟨x, hx.1⟩ : ↥L) ∈ (L ⊓ K₁).subgroupOf L := hx
    rw [h₁, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have h2' : ∀ x ∈ L ⊓ K₂, x = 1 := fun x hx => by
    have hmem : (⟨x, hx.1⟩ : ↥L) ∈ (L ⊓ K₂).subgroupOf L := hx
    rw [h₂, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hLK₁c := hcomm K₁ hNK₁ h1' le_sup_left
  have hLK₂c := hcomm K₂ hNK₂ h2' le_sup_right
  have hL1 : ∀ l ∈ L, l = 1 := by
    intro l hl
    obtain ⟨x, hx, y, hy, rfl⟩ := hdec l (hLN hl)
    have hx1 : x = 1 := by
      have := eq_one_of_central_L27 hL₁ (x := (⟨x, hx⟩ : ↥K₁)) (fun k => Subtype.ext (by
        have h1 := hLK₁c (x * y) hl k k.2
        have h2 : y * k = k * y := (hc k k.2 y hy).symm
        have h3 : (x * k) * y = (k * x) * y := by
          calc (x * k) * y = x * (k * y) := by rw [mul_assoc]
            _ = x * (y * k) := by rw [h2]
            _ = (x * y) * k := by rw [mul_assoc]
            _ = k * (x * y) := h1
            _ = (k * x) * y := by rw [mul_assoc]
        exact (mul_right_cancel h3).symm))
      exact congrArg Subtype.val this
    have hy1 : y = 1 := by
      have := eq_one_of_central_L27 hL₂ (x := (⟨y, hy⟩ : ↥K₂)) (fun k => Subtype.ext (by
        have h1 := hLK₂c (x * y) hl k k.2
        have h2 : x * k = k * x := hc x hx k k.2
        have h3 : x * (y * k) = x * (k * y) := by
          calc x * (y * k) = (x * y) * k := by rw [mul_assoc]
            _ = k * (x * y) := h1
            _ = (k * x) * y := by rw [mul_assoc]
            _ = (x * k) * y := by rw [h2]
            _ = x * (k * y) := by rw [mul_assoc]
        exact (mul_left_cancel h3).symm))
      exact congrArg Subtype.val this
    rw [hx1, hy1, one_mul]
  have hLn : Nontrivial ↥L := hLs.toNontrivial
  obtain ⟨l, hl⟩ := exists_ne (1 : ↥L)
  exact hl (Subtype.ext (hL1 l l.2))

end E217R4

end CFSG.Quasithin
