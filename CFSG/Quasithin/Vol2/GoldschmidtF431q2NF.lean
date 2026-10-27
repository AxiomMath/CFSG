module

public import CFSG.Quasithin.Vol2.GoldschmidtF431q2NFAux

public section

namespace CFSG.Quasithin.H13.F431.G2Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem not_isConj_of_nf {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) {T Q : Subgroup G}
    (hT : IsSylowTwoOf T (Subgroup.centralizer ({z} : Set G))) (hQT : Q ≤ T)
    (hTcard : Nat.card T = 64) (hQcard : Nat.card Q = 32)
    (hQn : ∀ h ∈ Subgroup.centralizer ({z} : Set G), ∀ q ∈ Q, h * q * h⁻¹ ∈ Q)
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z)
    (hQab : ∀ A : Subgroup G, A ≤ Q → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → Nat.card A ≤ 8)
    (O : G → Prop)
    (hOinv : ∀ h ∈ Subgroup.centralizer ({z} : Set G), ∀ v, O v → O (h * v * h⁻¹))
    (hOt : ∀ v, O v → ∃ t ∈ T, t * v * t⁻¹ * v⁻¹ ≠ 1 ∧ t * v * t⁻¹ * v⁻¹ ≠ z)
    {v : G} (hv : O v) (hvQ : v ∈ Q) (hvz : v ≠ z)
    (hpair : ∃ a ∈ Q, ∃ b ∈ Q, a * v = v * a ∧ b * v = v * b ∧ a * b * a⁻¹ * b⁻¹ = z) :
    ¬ IsConj z v := by
  classical
  intro hconj
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hQH : Q ≤ Subgroup.centralizer ({z} : Set G) := hQT.trans hT.1
  have hzc : ∀ q ∈ Q, q * z = z * q := fun q hq => (mem_centralizer_singleton.1 (hQH hq)).symm
  set Q' := conjSub c Q with hQ'
  set T' := conjSub c T with hT'
  have hCeq : ∀ h : G, h ∈ Subgroup.centralizer ({v} : Set G) ↔
      c⁻¹ * h * c ∈ Subgroup.centralizer ({z} : Set G) := by
    intro h
    rw [← hc]
    exact mem_centralizer_conj
  have hCT : IsSylowTwoOf T' (Subgroup.centralizer ({v} : Set G)) := by
    have h1 := F7.isSylowTwoOf_conj hT c
    have h2 : conjSub c (Subgroup.centralizer ({z} : Set G)) =
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
        c * ((c⁻¹ * h * c) * (c⁻¹ * q * c) * (c⁻¹ * h * c)⁻¹) * c⁻¹ := by group
    rw [e]
    exact mul_mem_conjSub h1
  have hQ'comm : ∀ x ∈ Q', ∀ y ∈ Q', x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = v := by
    intro x hx y hy
    have hx0 := mem_conjSub.1 hx
    have hy0 := mem_conjSub.1 hy
    have e : x * y * x⁻¹ * y⁻¹ = c * ((c⁻¹ * x * c) * (c⁻¹ * y * c) * (c⁻¹ * x * c)⁻¹ *
        (c⁻¹ * y * c)⁻¹) * c⁻¹ := by group
    rw [e]
    rcases hQcomm _ hx0 _ hy0 with h | h
    · left; rw [h]; group
    · right; rw [h, hc]
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
  have hT'card : Nat.card T' = 2 * Nat.card Q' := by
    rw [hT', hQ', card_conjSub, card_conjSub, hTcard, hQcard]
  have hQ'T' : Q' ≤ T' := conjSub_mono c hQT
  have hmz : m⁻¹ * z * m ∈ Q' := by
    have h1 := comm_mem_of_index_two hQ'T' hT'card _ haT' _ hbT'
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
  have hQ'card : Nat.card Q' = 32 := by rw [hQ', card_conjSub, hQcard]
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
  have hDcard : Nat.card (Q ⊓ Q' : Subgroup G) ≤ 8 := hQab _ inf_le_left hD
  have hRnQ : ¬ R ≤ Q := by
    intro hRQ
    have hRD : R ≤ Q ⊓ Q' := le_inf hRQ inf_le_left
    have := Subgroup.card_le_of_le hRD
    omega
  obtain ⟨r, hrR, hrQ⟩ := IsConcreteLE.not_le_iff_exists.1 hRnQ
  have hR2 : IsPGroup 2 R :=
    (F7.isPGroup_conjSub (g := c) hT.2.1).to_le (inf_le_left.trans (conjSub_mono c hQT))
  obtain ⟨h, hhH, hRh⟩ := F7.isSylowTwoOf_exists_conj_le hT (inf_le_right : R ≤ H) hR2
  have hQh : Q ≤ conjSub h T := by
    intro q hq
    refine mem_conjSub.2 (hQT ?_)
    have := hQn h⁻¹ (H.inv_mem hhH) q hq
    simpa using this
  set T₁ := conjSub h T with hT₁
  have hT₁card : Nat.card T₁ = 64 := by rw [hT₁, card_conjSub, hTcard]
  have hRQ_le : R ⊔ Q ≤ T₁ := sup_le hRh hQh
  have hRQcard : Nat.card (R ⊔ Q : Subgroup G) = 64 := by
    have hne : Q ≠ R ⊔ Q := by
      intro hEq
      apply hrQ
      rw [hEq]
      exact Subgroup.mem_sup_left hrR
    have hge : 32 < Nat.card (R ⊔ Q : Subgroup G) := by
      by_contra hle
      push Not at hle
      exact hne (Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hQcard]; exact hle))
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_right : Q ≤ R ⊔ Q)
    have hle64 := Subgroup.card_le_of_le hRQ_le
    rw [hQcard] at hk
    rw [hT₁card] at hle64
    omega
  have hRQeq : R ⊔ Q = T₁ :=
    Subgroup.eq_of_le_of_card_ge hRQ_le (by rw [hRQcard, hT₁card])
  have hRW : R ≤ commSub z v hz2 := by
    intro r hr
    refine ⟨hr.2, Or.inl ?_⟩
    have h0 := mem_conjSub.1 hr.1
    have hcomm : r * v = v * r := by
      have h1 := hzc _ h0
      calc r * v = c * ((c⁻¹ * r * c) * z) * c⁻¹ := by rw [← hc]; group
        _ = c * (z * (c⁻¹ * r * c)) * c⁻¹ := by rw [h1]
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

end CFSG.Quasithin.H13.F431.G2Two
