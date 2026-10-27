module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open

theorem commute_of_le_sup {Q : Type*} [Group Q] {A B : Subgroup Q}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have hA' : A ≤ centralizer ((A ⊔ B : Subgroup Q) : Set Q) := by
    intro a ha
    have h1 : A ⊔ B ≤ centralizer ({a} : Set Q) := by
      refine sup_le (fun a' ha' => ?_) (fun b hb => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact (hA a ha a' ha').symm
      · rw [mem_centralizer_singleton_iff]
        exact (hAB a ha b hb).symm
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.1 (h1 hy)
  have hB' : B ≤ centralizer ((A ⊔ B : Subgroup Q) : Set Q) := by
    intro b hb
    have h1 : A ⊔ B ≤ centralizer ({b} : Set Q) := by
      refine sup_le (fun a ha => ?_) (fun b' hb' => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact hAB a ha b hb
      · rw [mem_centralizer_singleton_iff]
        exact (hB b hb b' hb').symm
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.1 (h1 hy)
  intro x hx y hy
  exact (mem_centralizer_iff.1 ((sup_le hA' hB') hy)) x hx

theorem pow_eq_one_of_le_sup {Q : Type*} [Group Q] {A B : Subgroup Q} {p : ℕ}
    (hc : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x)
    (hA : ∀ a ∈ A, a ^ p = 1) (hB : ∀ b ∈ B, b ^ p = 1) : ∀ x ∈ A ⊔ B, x ^ p = 1 := by
  intro x hx
  have key : ∀ x ∈ closure ((A : Set Q) ∪ B), x ^ p = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact hA y hy
      · exact hB y hy
    | one => exact one_pow p
    | mul y z hy hz ihy ihz =>
      have hy' : y ∈ A ⊔ B := by rw [sup_eq_closure]; exact hy
      have hz' : z ∈ A ⊔ B := by rw [sup_eq_closure]; exact hz
      rw [(Commute.mul_pow (hc y hy' z hz') p), ihy, ihz, one_mul]
    | inv y hy ihy => rw [inv_pow, ihy, inv_one]
  rw [sup_eq_closure] at hx
  exact key x hx

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_of_commute_mod {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {E F N : Subgroup G} (hN : IsPGroup 2 N)
    (hEN : E ≤ normalizer (N : Set G)) (hFN : F ≤ normalizer (N : Set G))
    (hE : IsElemAbelian p E) (hF : IsElemAbelian p F)
    (hEF : ∀ e ∈ E, ∀ f ∈ F, e * f * e⁻¹ * f⁻¹ ∈ N)
    (hint : ∀ e ∈ E, ∀ f ∈ F, ∀ n ∈ N, e = f * n → e = 1) :
    ∃ P : Subgroup G, P ≤ E ⊔ F ⊔ N ∧ IsElemAbelian p P ∧
      Nat.card E * Nat.card F ≤ Nat.card P := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := E ⊔ F ⊔ N with hH
  have hEH : E ≤ H := le_sup_left.trans le_sup_left
  have hFH : F ≤ H := le_sup_right.trans le_sup_left
  have hNH : N ≤ H := le_sup_right
  have hHN : H ≤ normalizer (N : Set G) := sup_le (sup_le hEN hFN) le_normalizer
  have hn : (N.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHN
  set π : ↥H →* ↥H ⧸ N.subgroupOf H := QuotientGroup.mk' (N.subgroupOf H) with hπ
  have hπN : ∀ x : ↥H, π x = 1 ↔ (x : G) ∈ N := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hNp : ∀ x ∈ N, x ^ p = 1 → x = 1 := by
    intro x hx hxp
    obtain ⟨k, hk⟩ := hN ⟨x, hx⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hxp) (orderOf_dvd_of_pow_eq_one hk')
    have hcop : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  set A : Subgroup (↥H ⧸ N.subgroupOf H) := (E.subgroupOf H).map π with hA
  set B : Subgroup (↥H ⧸ N.subgroupOf H) := (F.subgroupOf H).map π with hB
  have hcA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have hc := hE.1.is_comm.comm (⟨x, mem_subgroupOf.1 hx⟩ : E) ⟨y, mem_subgroupOf.1 hy⟩
    have hc' : (x : G) * y = y * x := by simpa using congrArg Subtype.val hc
    exact Subtype.ext hc'
  have hcB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have hc := hF.1.is_comm.comm (⟨x, mem_subgroupOf.1 hx⟩ : F) ⟨y, mem_subgroupOf.1 hy⟩
    have hc' : (x : G) * y = y * x := by simpa using congrArg Subtype.val hc
    exact Subtype.ext hc'
  have hcAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h1 : π (x * y * x⁻¹ * y⁻¹) = 1 :=
      (hπN _).2 (hEF _ (mem_subgroupOf.1 hx) _ (mem_subgroupOf.1 hy))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π x * π y = (π x * π y * (π x)⁻¹ * (π y)⁻¹) * (π y * π x) := by group
      _ = π y * π x := by rw [h1, one_mul]
  have hsup : E.subgroupOf H ⊔ F.subgroupOf H ⊔ N.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hEH,
      inf_eq_left.2 hFH, inf_eq_left.2 hNH, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hNbot : (N.subgroupOf H).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
  have hAB : A ⊔ B = ⊤ := by
    have h1 : (E.subgroupOf H ⊔ F.subgroupOf H ⊔ N.subgroupOf H).map π = ⊤ := by
      rw [hsup, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
      exact QuotientGroup.mk'_surjective _
    rw [Subgroup.map_sup, Subgroup.map_sup, hNbot, sup_bot_eq] at h1
    exact h1
  have hcomm := commute_of_le_sup hcA hcB hcAB
  have hcQ : ∀ x y : ↥H ⧸ N.subgroupOf H, x * y = y * x := fun x y =>
    hcomm x (hAB ▸ mem_top x) y (hAB ▸ mem_top y)
  have hApow : ∀ a ∈ A, a ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ p = 1 := Subtype.ext (by simpa using hE.2 _ (mem_subgroupOf.1 hx))
    rw [this, map_one]
  have hBpow : ∀ b ∈ B, b ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ p = 1 := Subtype.ext (by simpa using hF.2 _ (mem_subgroupOf.1 hx))
    rw [this, map_one]
  have hexp : ∀ x : ↥H ⧸ N.subgroupOf H, x ^ p = 1 := fun x =>
    pow_eq_one_of_le_sup hcomm hApow hBpow x (hAB ▸ mem_top x)
  have hcardQ : Nat.card E * Nat.card F ≤ Nat.card (↥H ⧸ N.subgroupOf H) := by
    let f : ↥E × ↥F → ↥H ⧸ N.subgroupOf H := fun x =>
      π ⟨x.1, hEH x.1.2⟩ * π ⟨x.2, hFH x.2.2⟩
    have hf : Function.Injective f := by
      rintro ⟨e₁, f₁⟩ ⟨e₂, f₂⟩ h
      simp only [f] at h
      have h1 : π (⟨e₂, hEH e₂.2⟩⁻¹ * ⟨e₁, hEH e₁.2⟩ * (⟨f₂, hFH f₂.2⟩ * ⟨f₁, hFH f₁.2⟩⁻¹)⁻¹) =
          1 := by
        rw [map_mul, map_mul, map_inv, map_inv, map_mul, map_inv]
        calc (π ⟨e₂, hEH e₂.2⟩)⁻¹ * π ⟨e₁, hEH e₁.2⟩ *
              (π ⟨f₂, hFH f₂.2⟩ * (π ⟨f₁, hFH f₁.2⟩)⁻¹)⁻¹ =
            (π ⟨e₂, hEH e₂.2⟩)⁻¹ * (π ⟨e₁, hEH e₁.2⟩ * π ⟨f₁, hFH f₁.2⟩) *
              (π ⟨f₂, hFH f₂.2⟩)⁻¹ := by group
          _ = (π ⟨e₂, hEH e₂.2⟩)⁻¹ * (π ⟨e₂, hEH e₂.2⟩ * π ⟨f₂, hFH f₂.2⟩) *
              (π ⟨f₂, hFH f₂.2⟩)⁻¹ := by rw [h]
          _ = 1 := by group
      have hm := (hπN _).1 h1
      set m : G := (e₂ : G)⁻¹ * e₁ * ((f₂ : G) * (f₁ : G)⁻¹)⁻¹ with hmdef
      have hm' : m ∈ N := hm
      have hfN : (f₂ : G) * (f₁ : G)⁻¹ ∈ normalizer (N : Set G) :=
        hFN (mul_mem f₂.2 (inv_mem f₁.2))
      have hn' : ((f₂ : G) * (f₁ : G)⁻¹)⁻¹ * m * ((f₂ : G) * (f₁ : G)⁻¹) ∈ N := by
        have := (mem_normalizer_iff.1 (inv_mem hfN) m).1 hm'
        simpa using this
      have he : (e₂ : G)⁻¹ * e₁ = 1 := by
        refine hint _ (mul_mem (inv_mem e₂.2) e₁.2) _ (mul_mem f₂.2 (inv_mem f₁.2)) _ hn' ?_
        rw [hmdef]
        group
      have he' : e₁ = e₂ := Subtype.ext (by
        have := congrArg (fun x => (e₂ : G) * x) he
        simpa using this)
      subst he'
      have h2 : π ⟨f₁, hFH f₁.2⟩ = π ⟨f₂, hFH f₂.2⟩ := mul_left_cancel h
      have h3 : π (⟨f₂, hFH f₂.2⟩⁻¹ * ⟨f₁, hFH f₁.2⟩) = 1 := by
        rw [map_mul, map_inv, h2, inv_mul_cancel]
      have h4 : (f₂ : G)⁻¹ * f₁ ∈ N := (hπN _).1 h3
      have h5 : ((f₂ : G)⁻¹ * f₁) ^ p = 1 := hF.2 _ (mul_mem (inv_mem f₂.2) f₁.2)
      have h6 := hNp _ h4 h5
      have hf' : f₁ = f₂ := Subtype.ext (by
        have := congrArg (fun x => (f₂ : G) * x) h6
        simpa using this)
      rw [hf']
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod] at this
  have hQp : IsPGroup p (↥H ⧸ N.subgroupOf H) := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
  obtain ⟨b, hb⟩ := hQp.exists_card_eq
  have hN' : IsPGroup 2 (N.subgroupOf H) := hN.of_equiv (subgroupOfEquivOfLe hNH).symm
  obtain ⟨a, ha⟩ := hN'.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (N.subgroupOf H)) (N.subgroupOf H).index := by
    rw [ha, Subgroup.index, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2))
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hKN : ∀ x ∈ K, x ∈ N.subgroupOf H → x = 1 := by
    intro x hxK hxN
    have := hK.disjoint
    rw [disjoint_iff] at this
    have hx : x ∈ N.subgroupOf H ⊓ K := ⟨hxN, hxK⟩
    rw [this] at hx
    exact hx
  have hcardK : Nat.card K = Nat.card (↥H ⧸ N.subgroupOf H) := by
    have h1 := hK.card_mul_card
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H)
    have hpos : 0 < Nat.card (N.subgroupOf H) := Nat.card_pos
    rw [h2, mul_comm (Nat.card (↥H ⧸ N.subgroupOf H))] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have hKcomm : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
    intro x hx y hy
    have h1 : π (x * y * x⁻¹ * y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcQ (π x) (π y)]
      group
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ N.subgroupOf H := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have h3 := hKN _ (mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)) h2
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h3, one_mul]
  have hKexp : ∀ x ∈ K, x ^ p = 1 := by
    intro x hx
    have h1 : π (x ^ p) = 1 := by rw [map_pow, hexp]
    have h2 : x ^ p ∈ N.subgroupOf H := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    exact hKN _ (pow_mem hx p) h2
  refine ⟨K.map H.subtype, map_subtype_le K, ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨k₁, hk₁, h1⟩ := mem_map.1 x.2
    obtain ⟨k₂, hk₂, h2⟩ := mem_map.1 y.2
    show (x : G) * y = y * x
    rw [← h1, ← h2, ← map_mul, ← map_mul, hKcomm k₁ hk₁ k₂ hk₂]
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := mem_map.1 hg
    rw [← map_pow, hKexp k hk, map_one]
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hcardK]
    exact hcardQ

end CFSG.Quasithin.H13.U3
