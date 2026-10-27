module

public import CFSG.Quasithin.Vol2.GoldschmidtF431q2NFAux

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431.G2Two

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem nfCard_sup_mul_card_inf {H N : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (H ⊔ N : Subgroup G) * Nat.card (H ⊓ N : Subgroup G) =
      Nat.card H * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N))
  have h3 : Nat.card (N.subgroupOf H) = Nat.card (H ⊓ N : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right, inf_comm N H]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ N ≤ H)).toEquiv
  have h4 : Nat.card (N.subgroupOf (H ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv
  have h5 := Nat.card_congr e.toEquiv
  rw [h1, h3.symm, ← h4, h2, ← h5]
  ring

theorem not_isConj_of_nfGen {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) {T Q : Subgroup G} {c : ℕ}
    (hT : IsSylowTwoOf T (Subgroup.centralizer ({z} : Set G))) (hQT : Q ≤ T)
    (hTQ : ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ Q)
    (hnum : 2 * c * Nat.card T ≤ Nat.card Q * Nat.card Q)
    (hQn : ∀ h ∈ Subgroup.centralizer ({z} : Set G), ∀ q ∈ Q, h * q * h⁻¹ ∈ Q)
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z)
    (hQsq : ∀ x ∈ Q, x * x = 1 ∨ x * x = z)
    (hQab : ∀ A : Subgroup G, A ≤ Q → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      (∀ x ∈ A, x * x = 1) → Nat.card A ≤ c)
    (O : G → Prop)
    (hOinv : ∀ h ∈ Subgroup.centralizer ({z} : Set G), ∀ v, O v → O (h * v * h⁻¹))
    (hOt : ∀ v, O v → ∃ t ∈ T, t * v * t⁻¹ * v⁻¹ ≠ 1 ∧ t * v * t⁻¹ * v⁻¹ ≠ z)
    {v : G} (hv : O v) (hvQ : v ∈ Q) (hvz : v ≠ z)
    (hpair : ∃ a ∈ Q, ∃ b ∈ Q, a * v = v * a ∧ b * v = v * b ∧ a * b * a⁻¹ * b⁻¹ = z) :
    ¬ IsConj z v := by
  classical
  intro hconj
  obtain ⟨g, hc⟩ := isConj_iff.1 hconj
  have hQH : Q ≤ Subgroup.centralizer ({z} : Set G) := hQT.trans hT.1
  have hzc : ∀ q ∈ Q, q * z = z * q := fun q hq => (mem_centralizer_singleton.1 (hQH hq)).symm
  set Q' := conjSub g Q with hQ'
  set T' := conjSub g T with hT'
  have hCeq : ∀ h : G, h ∈ Subgroup.centralizer ({v} : Set G) ↔
      g⁻¹ * h * g ∈ Subgroup.centralizer ({z} : Set G) := by
    intro h
    rw [← hc]
    exact mem_centralizer_conj
  have hCT : IsSylowTwoOf T' (Subgroup.centralizer ({v} : Set G)) := by
    have h1 := F7.isSylowTwoOf_conj hT g
    have h2 : conjSub g (Subgroup.centralizer ({z} : Set G)) =
        Subgroup.centralizer ({v} : Set G) := by
      ext h
      rw [mem_conjSub, hCeq]
    rwa [h2] at h1
  have hQ'n : ∀ h ∈ Subgroup.centralizer ({v} : Set G), ∀ q ∈ Q', h * q * h⁻¹ ∈ Q' := by
    intro h hh q hq
    have h0 := (hCeq h).1 hh
    have hq0 := mem_conjSub.1 hq
    have h1 := hQn _ h0 _ hq0
    have e : h * q * h⁻¹ =
        g * ((g⁻¹ * h * g) * (g⁻¹ * q * g) * (g⁻¹ * h * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact mul_mem_conjSub h1
  have hQ'comm : ∀ x ∈ Q', ∀ y ∈ Q', x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = v := by
    intro x hx y hy
    have hx0 := mem_conjSub.1 hx
    have hy0 := mem_conjSub.1 hy
    have e : x * y * x⁻¹ * y⁻¹ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ *
        (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
    rw [e]
    rcases hQcomm _ hx0 _ hy0 with h | h
    · left; rw [h]; group
    · right; rw [h, hc]
  have hQ'sq : ∀ x ∈ Q', x * x = 1 ∨ x * x = v := by
    intro x hx
    have hx0 := mem_conjSub.1 hx
    have e : x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    rw [e]
    rcases hQsq _ hx0 with h | h
    · left; rw [h]; group
    · right; rw [h, hc]
  have hTQ' : ∀ x ∈ T', ∀ y ∈ T', x * y * x⁻¹ * y⁻¹ ∈ Q' := by
    intro x hx y hy
    have h1 := hTQ _ (mem_conjSub.1 hx) _ (mem_conjSub.1 hy)
    have e : x * y * x⁻¹ * y⁻¹ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ *
        (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact mul_mem_conjSub h1
  obtain ⟨a, haQ, b, hbQ, hav, hbv, hab⟩ := hpair
  have haC : a ∈ Subgroup.centralizer ({v} : Set G) := mem_centralizer_singleton.2 hav.symm
  have hbC : b ∈ Subgroup.centralizer ({v} : Set G) := mem_centralizer_singleton.2 hbv.symm
  set U : Subgroup G := Subgroup.closure ({a, b} : Set G) with hU
  have hUQ : U ≤ Q := by
    rw [hU, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact haQ
    · rw [Set.mem_singleton_iff.1 hx]; exact hbQ
  have hUC : U ≤ Subgroup.centralizer ({v} : Set G) := by
    rw [hU, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact haC
    · rw [Set.mem_singleton_iff.1 hx]; exact hbC
  have hU2 : IsPGroup 2 U := hT.2.1.to_le (hUQ.trans hQT)
  obtain ⟨m, hmC, hUm⟩ := F7.isSylowTwoOf_exists_conj_le hCT hUC hU2
  have haT' : m⁻¹ * a * m ∈ T' :=
    mem_conjSub.1 (hUm (Subgroup.subset_closure (Set.mem_insert _ _)))
  have hbT' : m⁻¹ * b * m ∈ T' :=
    mem_conjSub.1 (hUm (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
  have hmz : m⁻¹ * z * m ∈ Q' := by
    have h1 := hTQ' _ haT' _ hbT'
    have e : m⁻¹ * z * m = (m⁻¹ * a * m) * (m⁻¹ * b * m) * (m⁻¹ * a * m)⁻¹ * (m⁻¹ * b * m)⁻¹ := by
      calc m⁻¹ * z * m = m⁻¹ * (a * b * a⁻¹ * b⁻¹) * m := by rw [hab]
        _ = _ := by group
    rw [e]
    exact h1
  have hzQ' : z ∈ Q' := by
    have h1 := hQ'n m hmC _ hmz
    have e : m * (m⁻¹ * z * m) * m⁻¹ = z := by group
    rwa [e] at h1
  set H := Subgroup.centralizer ({z} : Set G) with hHdef
  set R : Subgroup G := Q' ⊓ H with hR
  have hQ'card : Nat.card Q' = Nat.card Q := by rw [hQ', card_conjSub]
  have hvne : ∀ q ∈ Q', q ∉ H → q * z * q⁻¹ * z⁻¹ = v := by
    intro q hq hqH
    rcases hQ'comm q hq z hzQ' with h | h
    · exfalso
      apply hqH
      have h1 : q * z * q⁻¹ = z := mul_inv_eq_one.1 h
      have h2 : q * z = z * q := by
        calc q * z = (q * z * q⁻¹) * q := by group
          _ = z * q := by rw [h1]
      exact mem_centralizer_singleton.2 h2.symm
    · exact h
  have hRcard : Nat.card Q' ≤ 2 * Nat.card R := by
    refine card_le_two_mul_inf_centralizer (c := z) (w := v) fun x hx => ?_
    by_cases hxH : x ∈ H
    · exact Or.inl hxH
    · right
      calc x * z * x⁻¹ = (x * z * x⁻¹ * z⁻¹) * z := by group
        _ = v * z := by rw [hvne x hx hxH]
  have hD : ∀ x ∈ Q ⊓ Q', ∀ y ∈ Q ⊓ Q', x * y = y * x := by
    intro x hx y hy
    have h1 := hQcomm x hx.1 y hy.1
    have h2 := hQ'comm x hx.2 y hy.2
    have hxy : x * y * x⁻¹ * y⁻¹ = 1 := by
      rcases h1 with h1 | h1
      · exact h1
      · rcases h2 with h2 | h2
        · rw [h1] at h2; exact absurd h2 hz1
        · rw [h1] at h2; exact absurd h2.symm hvz
    have h3 : x * y * x⁻¹ = y := mul_inv_eq_one.1 hxy
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [h3]
  have hDsq : ∀ x ∈ Q ⊓ Q', x * x = 1 := by
    intro x hx
    rcases hQsq x hx.1 with h1 | h1
    · exact h1
    · rcases hQ'sq x hx.2 with h2 | h2
      · exact h2
      · rw [h1] at h2; exact absurd h2.symm hvz
  have hDcard : Nat.card (Q ⊓ Q' : Subgroup G) ≤ c := hQab _ inf_le_left hD hDsq
  have hRQc : Nat.card (R ⊓ Q : Subgroup G) ≤ c := by
    have hle : (R ⊓ Q : Subgroup G) ≤ Q ⊓ Q' := fun x hx => ⟨hx.2, hx.1.1⟩
    exact (Subgroup.card_le_of_le hle).trans hDcard
  have hRN : R ≤ Subgroup.normalizer (Q : Set G) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hQn r hr.2 q hq, fun hq => ?_⟩
    have h1 := hQn r⁻¹ (H.inv_mem hr.2) _ hq
    simpa [mul_assoc] using h1
  have hprod := nfCard_sup_mul_card_inf hRN
  have hR2 : IsPGroup 2 R :=
    (F7.isPGroup_conjSub (g := g) hT.2.1).to_le (inf_le_left.trans (conjSub_mono g hQT))
  obtain ⟨h, hhH, hRh⟩ := F7.isSylowTwoOf_exists_conj_le hT (inf_le_right : R ≤ H) hR2
  have hQh : Q ≤ conjSub h T := by
    intro q hq
    refine mem_conjSub.2 (hQT ?_)
    have := hQn h⁻¹ (H.inv_mem hhH) q hq
    simpa using this
  set T₁ := conjSub h T with hT₁
  have hT₁card : Nat.card T₁ = Nat.card T := by rw [hT₁, card_conjSub]
  have hRQ_le : R ⊔ Q ≤ T₁ := sup_le hRh hQh
  have hge : Nat.card T₁ ≤ Nat.card (R ⊔ Q : Subgroup G) := by
    by_contra hlt
    push Not at hlt
    rw [hT₁card] at hlt
    have hRc : Nat.card Q ≤ 2 * Nat.card R := by rw [← hQ'card]; exact hRcard
    have hbpos : 0 < Nat.card (R ⊓ Q : Subgroup G) := Nat.card_pos
    have i1 := Nat.mul_le_mul_right (Nat.card Q) hRc
    have i2 := Nat.mul_le_mul_left (Nat.card (R ⊔ Q : Subgroup G)) hRQc
    have i3 := Nat.mul_le_mul_right c (Nat.succ_le_of_lt hlt)
    nlinarith
  have hRQeq : R ⊔ Q = T₁ := Subgroup.eq_of_le_of_card_ge hRQ_le hge
  have hRW : R ≤ commSub z v hz2 := by
    intro r hr
    refine ⟨hr.2, Or.inl ?_⟩
    have h0 := mem_conjSub.1 hr.1
    have hcomm : r * v = v * r := by
      have h1 := hzc _ h0
      calc r * v = g * ((g⁻¹ * r * g) * z) * g⁻¹ := by rw [← hc]; group
        _ = g * (z * (g⁻¹ * r * g)) * g⁻¹ := by rw [h1]
        _ = v * r := by rw [← hc]; group
    calc r * v * r⁻¹ * v⁻¹ = (v * r) * r⁻¹ * v⁻¹ := by rw [hcomm]
      _ = 1 := by group
  have hQW : Q ≤ commSub z v hz2 := fun q hq => ⟨hQH hq, hQcomm q hq v hvQ⟩
  have hT₁W : T₁ ≤ commSub z v hz2 := hRQeq ▸ sup_le hRW hQW
  obtain ⟨t, htT, hne1, hnez⟩ := hOt (h⁻¹ * v * h)
    (by simpa using hOinv h⁻¹ (H.inv_mem hhH) v hv)
  have htT₁ : h * t * h⁻¹ ∈ T₁ := mul_mem_conjSub htT
  rcases comm_conj hhH (hT₁W htT₁).2 with h1 | h1
  · exact hne1 h1
  · exact hnez h1

end CFSG.Quasithin.D4Hex
