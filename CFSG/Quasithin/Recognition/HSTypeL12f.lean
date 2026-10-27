module

public import CFSG.Quasithin.Recognition.HSTypeL12e
public import CFSG.Quasithin.Recognition.HSTypeL12d

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

theorem perm_five_odd_invol_comm : ∀ σ : Equiv.Perm (Fin 5), σ * σ = 1 →
    Equiv.Perm.sign σ = -1 →
    ∃ τ : Equiv.Perm (Fin 5), τ * τ * τ = 1 ∧ τ ≠ 1 ∧ σ * τ = τ * σ := by
  decide +kernel

theorem exists_comm_eq_of_card_mul_le [Finite G] {Q : Subgroup G} {s : G}
    (hcomm : ∀ r ∈ Q, s * r * s⁻¹ * r⁻¹ ∈ Q ⊓ Subgroup.centralizer ({s} : Set G))
    (hcard : Nat.card ↥(Q ⊓ Subgroup.centralizer ({s} : Set G)) *
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({s} : Set G)) ≤ Nat.card Q)
    {c : G} (hc : c ∈ Q ⊓ Subgroup.centralizer ({s} : Set G)) :
    ∃ r ∈ Q, c = s * r * s⁻¹ * r⁻¹ := by
  classical
  have := Fintype.ofFinite G
  set C := Q ⊓ Subgroup.centralizer ({s} : Set G) with hCdef
  set QF : Finset G := Finset.univ.filter (· ∈ Q) with hQF
  set CF : Finset G := Finset.univ.filter (· ∈ C) with hCF
  set F : G → G := fun r => s * r * s⁻¹ * r⁻¹ with hF
  have hQcard : QF.card = Nat.card Q := by
    rw [hQF, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hCcard : CF.card = Nat.card C := by
    rw [hCF, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : QF.image F ⊆ CF := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcomm r (Finset.mem_filter.mp hr).2⟩
  have hfib : ∀ b ∈ QF.image F, (QF.filter fun x => F x = b).card ≤ CF.card := by
    intro b hb
    obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.mp hb
    have hr₀Q : r₀ ∈ Q := (Finset.mem_filter.mp hr₀).2
    calc (QF.filter fun x => F x = F r₀).card ≤ (CF.image (r₀ * ·)).card := by
          apply Finset.card_le_card
          intro r hr
          obtain ⟨hrQF, hrF⟩ := Finset.mem_filter.mp hr
          have hrQ : r ∈ Q := (Finset.mem_filter.mp hrQF).2
          refine Finset.mem_image.mpr ⟨r₀⁻¹ * r, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Q.mul_mem (Q.inv_mem hr₀Q) hrQ, ?_⟩, by group⟩
          refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
          have h1 : s * r * s⁻¹ * r⁻¹ = s * r₀ * s⁻¹ * r₀⁻¹ := hrF
          have h2 : r * s⁻¹ * r⁻¹ = r₀ * s⁻¹ * r₀⁻¹ := by
            have := congrArg (s⁻¹ * ·) h1
            simpa [mul_assoc] using this
          calc r₀⁻¹ * r * s = r₀⁻¹ * (r * s⁻¹ * r⁻¹)⁻¹ * r := by group
            _ = r₀⁻¹ * (r₀ * s⁻¹ * r₀⁻¹)⁻¹ * r := by rw [h2]
            _ = s * (r₀⁻¹ * r) := by group
      _ ≤ CF.card := Finset.card_image_le
  have h1 := Finset.card_le_mul_card_image QF CF.card hfib
  have h2 := Finset.card_le_card hsub
  rw [hQcard, hCcard] at h1
  rw [hCcard] at h2
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have h3 : Nat.card C ≤ (QF.image F).card := by
    by_contra hlt
    push Not at hlt
    have := Nat.mul_lt_mul_of_pos_left hlt hCpos
    omega
  have heq : QF.image F = CF := Finset.eq_of_subset_of_card_le hsub (by rw [hCcard]; exact h3)
  have hcF : c ∈ QF.image F := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  obtain ⟨r, hr, hrc⟩ := Finset.mem_image.mp hcF
  exact ⟨r, (Finset.mem_filter.mp hr).2, hrc.symm⟩

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem exists_orderOf_three_lift [Finite G] (h : HSSetting z V)
    {φ : ↥(hsH z) →* Equiv.Perm (Fin 5)} (hφ : Function.Surjective φ)
    (hker : φ.ker = (hsQ z).subgroupOf (hsH z)) {τ : Equiv.Perm (Fin 5)}
    (hτ3 : τ * τ * τ = 1) (hτ1 : τ ≠ 1) :
    ∃ y : ↥(hsH z), orderOf (y : G) = 3 ∧ φ y = τ := by
  have hkerQ : ∀ g : ↥(hsH z), φ g = 1 ↔ (g : G) ∈ hsQ z := by
    intro g
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  obtain ⟨h₀, hh₀⟩ := hφ τ
  have hτ64 : τ ^ 64 = τ := by
    have : τ ^ 3 = 1 := by rw [pow_succ, pow_succ, pow_one]; exact hτ3
    calc τ ^ 64 = (τ ^ 3) ^ 21 * τ := by rw [← pow_mul, ← pow_succ]
      _ = τ := by rw [this, one_pow, one_mul]
  have hφy : φ (h₀ ^ 64) = τ := by rw [map_pow, hh₀, hτ64]
  have hy3 : ((h₀ : G) ^ 64) ^ 3 = 1 := by
    have h3Q : (h₀ : G) ^ 3 ∈ hsQ z := by
      have : φ (h₀ ^ 3) = 1 := by rw [map_pow, hh₀, pow_succ, pow_succ, pow_one]; exact hτ3
      have := (hkerQ (h₀ ^ 3)).mp this
      simpa using this
    have h64 := pow_card_eq_one' (G := ↥(hsQ z)) (x := ⟨_, h3Q⟩)
    rw [h.card_Q] at h64
    have := congrArg Subtype.val h64
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [← pow_mul, show 64 * 3 = 3 * 64 by norm_num, pow_mul]
    exact this
  have hy1 : (h₀ : G) ^ 64 ≠ 1 := by
    intro h1
    apply hτ1
    rw [← hφy]
    have : h₀ ^ 64 = 1 := Subtype.ext (by simpa using h1)
    rw [this, map_one]
  refine ⟨h₀ ^ 64, ?_, hφy⟩
  rw [Subgroup.coe_pow]
  exact orderOf_eq_prime hy3 hy1

theorem sign_eq_neg_one_of_not_mem_K [Finite G] (h : HSSetting z V)
    {φ : ↥(hsH z) →* Equiv.Perm (Fin 5)} (hker : φ.ker = (hsQ z).subgroupOf (hsH z))
    {a : ↥(hsH z)} (haK : (a : G) ∉ hsK z) : Equiv.Perm.sign (φ a) = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign (φ a)) with h1 | h1
  · exfalso
    apply haK
    have hA : φ a ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.mpr h1
    rw [← h.map_K_eq_alternating φ hker] at hA
    obtain ⟨k, hk, hka⟩ := hA
    have hk1 : φ (k⁻¹ * a) = 1 := by rw [map_mul, map_inv, hka, inv_mul_cancel]
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf] at hk1
    have := (hsK z).mul_mem (Subgroup.mem_subgroupOf.mp hk) (h.Q_le_K hk1)
    simpa using this
  · exact h1

theorem exists_three_comm_of_not_mem_K [Finite G] (h : HSSetting z V) {a : G}
    (ha : a ∈ hsH z) (haK : a ∉ hsK z) (ha2 : a * a ∈ hsQ z) :
    ∃ y ∈ hsH z, orderOf y = 3 ∧ y * a * y⁻¹ * a⁻¹ ∈ hsQ z := by
  obtain ⟨φ, hφ, hker⟩ := h.one.quot
  have hkerQ : ∀ g : ↥(hsH z), φ g = 1 ↔ (g : G) ∈ hsQ z := by
    intro g
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  set a' : ↥(hsH z) := ⟨a, ha⟩
  have hσ2 : φ a' * φ a' = 1 := by
    rw [← map_mul, hkerQ]
    exact ha2
  obtain ⟨τ, hτ3, hτ1, hστ⟩ :=
    perm_five_odd_invol_comm (φ a') hσ2 (h.sign_eq_neg_one_of_not_mem_K hker haK)
  obtain ⟨y, hyo, hφy⟩ := h.exists_orderOf_three_lift hφ hker hτ3 hτ1
  refine ⟨y, y.2, hyo, ?_⟩
  have : φ (y * a' * y⁻¹ * a'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hφy, ← hστ]
    group
  exact (hkerQ _).mp this

theorem inv_of_not_mem_K [Finite G] (h : HSSetting z V) {s : G} (hsH : s ∈ hsH z)
    (hsK : s ∉ hsK z) {u : G} (hu : u ∈ hsZQ z) : s * u * s⁻¹ = u⁻¹ := by
  rcases h.mem_K_or_inverts hsH with hK | hinv
  · exact absurd hK hsK
  · exact hinv u hu

theorem comm_conj_invol [Finite G] (h : HSSetting z V) {s : G} (hsH : s ∈ hsH z)
    (hsK : s ∉ hsK z) (hss : s * s = 1) {q : G} (hq : q ∈ hsQ z) :
    q * (s * q * s⁻¹) = (s * q * s⁻¹) * q := by
  have hs2 : s * s ∈ hsQ z := by rw [hss]; exact (hsQ z).one_mem
  obtain ⟨y, hyH, hyo, hy⟩ := h.exists_three_comm_of_not_mem_K hsH hsK hs2
  exact h.comm_conj_of_three hsH hs2 hyH hyo hy hq

theorem invol_comm_mem_centralizer [Finite G] (h : HSSetting z V) {s : G} (hsH : s ∈ hsH z)
    (hsK : s ∉ hsK z) (hss : s * s = 1) {q : G} (hq : q ∈ hsQ z) :
    (s * q * s⁻¹ * q⁻¹) * (s * q * s⁻¹ * q⁻¹) = 1 ∧
      s * q * s⁻¹ * q⁻¹ ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G) := by
  have hc := h.comm_conj_invol hsH hsK hss hq
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  have hqq : (q * q) * s = s * (q * q) :=
    comm_of_eq_one_or_z (h.mul_self_eq_one_or_z hq) hsH
  have hcq : q⁻¹ * (s * q * s⁻¹) = (s * q * s⁻¹) * q⁻¹ := by
    calc q⁻¹ * (s * q * s⁻¹) = q⁻¹ * ((s * q * s⁻¹) * q) * q⁻¹ := by group
      _ = q⁻¹ * (q * (s * q * s⁻¹)) * q⁻¹ := by rw [hc]
      _ = (s * q * s⁻¹) * q⁻¹ := by group
  have hsq : (s * q * s⁻¹ * q⁻¹) * (s * q * s⁻¹ * q⁻¹) = 1 := by
    calc (s * q * s⁻¹ * q⁻¹) * (s * q * s⁻¹ * q⁻¹)
        = s * q * s⁻¹ * (q⁻¹ * (s * q * s⁻¹)) * q⁻¹ := by group
      _ = s * q * s⁻¹ * ((s * q * s⁻¹) * q⁻¹) * q⁻¹ := by rw [hcq]
      _ = s * (q * q) * s⁻¹ * (q * q)⁻¹ := by group
      _ = 1 := by rw [← hqq]; group
  refine ⟨hsq, (hsQ z).mul_mem (conj_mem_Q hsH hq) ((hsQ z).inv_mem hq),
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have e1 : s * (s * q * s⁻¹ * q⁻¹) * s⁻¹ = q * s * q⁻¹ * s := by
    calc s * (s * q * s⁻¹ * q⁻¹) * s⁻¹ = (s * s) * q * s⁻¹ * q⁻¹ * s⁻¹ := by group
      _ = q * s * q⁻¹ * s := by rw [hss, one_mul, hsinv]
  have e2 : (s * q * s⁻¹ * q⁻¹)⁻¹ = q * s * q⁻¹ * s := by
    calc (s * q * s⁻¹ * q⁻¹)⁻¹ = q * s * q⁻¹ * s⁻¹ := by group
      _ = q * s * q⁻¹ * s := by rw [hsinv]
  have hinv' : (s * q * s⁻¹ * q⁻¹)⁻¹ = s * q * s⁻¹ * q⁻¹ := inv_eq_of_mul_eq_one_left hsq
  have hfix : s * (s * q * s⁻¹ * q⁻¹) * s⁻¹ = s * q * s⁻¹ * q⁻¹ := by rw [e1, ← e2, hinv']
  calc s * q * s⁻¹ * q⁻¹ * s = s * (s * q * s⁻¹ * q⁻¹) * s⁻¹ * s := by rw [hfix]
    _ = s * (s * q * s⁻¹ * q⁻¹) := by group

theorem centralizer_invol_inf_ZQ [Finite G] (h : HSSetting z V) {s : G} (hsH : s ∈ hsH z)
    (hsK : s ∉ hsK z) :
    hsQ z ⊓ Subgroup.centralizer ({s} : Set G) ⊓ hsZQ z = Subgroup.zpowers z := by
  refine le_antisymm ?_ ?_
  · rintro u ⟨⟨-, hus⟩, huZ⟩
    have h1 := h.inv_of_not_mem_K hsH hsK huZ
    have hus' : u * s = s * u := Subgroup.mem_centralizer_singleton_iff.mp hus
    rw [← hus', mul_inv_cancel_right] at h1
    by_cases hu1 : u = 1
    · rw [hu1]
      exact (Subgroup.zpowers z).one_mem
    · have huu : u * u = 1 := by
        calc u * u = u * u⁻¹ := by rw [← h1]
          _ = 1 := mul_inv_cancel u
      rw [h.eq_z_of_mem_ZQ huZ huu hu1]
      exact Subgroup.mem_zpowers z
  · rw [Subgroup.zpowers_le]
    exact ⟨⟨h.mem_Q, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hsH).symm⟩, h.z_mem_ZQ⟩

theorem centralizer_invol_sup_ZQ [Finite G] (h : HSSetting z V) {s : G} (hsH : s ∈ hsH z)
    (hsK : s ∉ hsK z) (hss : s * s = 1) :
    hsQ z ⊓ Subgroup.centralizer ({s} : Set G) ⊔ hsZQ z = hsFixQ z s := by
  have hsQ' : s ∉ hsQ z := fun hsQ => hsK (h.Q_le_K hsQ)
  have hs2 : s * s ∈ hsQ z := by rw [hss]; exact (hsQ z).one_mem
  refine le_antisymm (sup_le ?_ (h.ZQ_le_fixQ hsH)) ?_
  · rintro c ⟨hcQ, hcs⟩
    refine ⟨hcQ, ?_⟩
    rw [← Subgroup.mem_centralizer_singleton_iff.mp hcs, mul_inv_cancel_right, mul_inv_cancel]
    exact (hsZQ z).one_mem
  · intro d hd
    obtain ⟨q, hq, u, hu, rfl⟩ := h.exists_comm_mul_of_mem_fixQ hsH hsQ' hs2 hd
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (h.invol_comm_mem_centralizer hsH hsK hss
      hq).2) (Subgroup.mem_sup_right hu)

theorem card_centralizer_invol [Finite G] (h : HSSetting z V) {s : G} (hsH : s ∈ hsH z)
    (hsK : s ∉ hsK z) (hss : s * s = 1) :
    Nat.card ↥(hsQ z ⊓ Subgroup.centralizer ({s} : Set G)) = 8 := by
  have hsQ' : s ∉ hsQ z := fun hsQ => hsK (h.Q_le_K hsQ)
  have hs2 : s * s ∈ hsQ z := by rw [hss]; exact (hsQ z).one_mem
  have hle : hsQ z ⊓ Subgroup.centralizer ({s} : Set G) ≤
      Subgroup.normalizer (hsZQ z : Set G) :=
    (inf_le_left.trans h.Q_le_H).trans h.H_le_normalizer_ZQ
  have hprod := card_sup_mul_card_inf_of_le_normalizer hle
  rw [h.centralizer_invol_sup_ZQ hsH hsK hss, h.centralizer_invol_inf_ZQ hsH hsK,
    h.card_fixQ_eq hsH hsQ' hs2, Nat.card_zpowers, h.orderOf_z, h.card_ZQ] at hprod
  omega

theorem mul_self_of_mem_centralizer_invol [Finite G] (h : HSSetting z V) {s : G}
    (hsH : s ∈ hsH z) (hsK : s ∉ hsK z) (hss : s * s = 1) {c : G}
    (hc : c ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G)) : c * c = 1 := by
  have hsQ' : s ∉ hsQ z := fun hsQ => hsK (h.Q_le_K hsQ)
  have hs2 : s * s ∈ hsQ z := by rw [hss]; exact (hsQ z).one_mem
  have hcD : c ∈ hsFixQ z s := by
    rw [← h.centralizer_invol_sup_ZQ hsH hsK hss]
    exact Subgroup.mem_sup_left hc
  obtain ⟨q, hq, u, hu, hcu⟩ := h.exists_comm_mul_of_mem_fixQ hsH hsQ' hs2 hcD
  obtain ⟨hsq2, hsqC⟩ := h.invol_comm_mem_centralizer hsH hsK hss hq
  set x := s * q * s⁻¹ * q⁻¹ with hx
  have hcs : s * c * s⁻¹ = c := by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp hc.2, mul_inv_cancel_right]
  have hxs : s * x * s⁻¹ = x := by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp hsqC.2, mul_inv_cancel_right]
  have hus := h.inv_of_not_mem_K hsH hsK hu
  have huu : u * u = 1 := by
    have : s * c * s⁻¹ = x * u⁻¹ := by
      rw [hcu]
      calc s * (x * u) * s⁻¹ = (s * x * s⁻¹) * (s * u * s⁻¹) := by group
        _ = x * u⁻¹ := by rw [hxs, hus]
    rw [hcs, hcu] at this
    have h1 : u = u⁻¹ := mul_left_cancel this
    calc u * u = u * u⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel u
  have hxu : x * u = u * x := Subgroup.mem_centralizer_iff.mp hu.2 x hsqC.1
  rw [hcu]
  calc x * u * (x * u) = (x * x) * (u * u) := by
        rw [show x * u * (x * u) = x * (u * x) * u by group, ← hxu]; group
    _ = 1 := by rw [hsq2, huu, one_mul]

theorem exists_comm_eq_of_invol [Finite G] (h : HSSetting z V) {s : G} (hsH : s ∈ hsH z)
    (hsK : s ∉ hsK z) (hss : s * s = 1) {c : G}
    (hc : c ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G)) :
    ∃ r ∈ hsQ z, c = s * r * s⁻¹ * r⁻¹ :=
  exists_comm_eq_of_card_mul_le (fun r hr => (h.invol_comm_mem_centralizer hsH hsK hss hr).2)
    (by rw [h.card_centralizer_invol hsH hsK hss, h.card_Q]) hc

theorem exists_conj_eq_mul_of_invol [Finite G] (h : HSSetting z V) {s : G} (hsH : s ∈ hsH z)
    (hsK : s ∉ hsK z) (hss : s * s = 1) {b : G}
    (hb : b ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G)) :
    ∃ r ∈ hsQ z, s * b = r * s * r⁻¹ := by
  obtain ⟨r, hr, rfl⟩ := h.exists_comm_eq_of_invol hsH hsK hss hb
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  refine ⟨r, hr, ?_⟩
  calc s * (s * r * s⁻¹ * r⁻¹) = (s * s) * r * s⁻¹ * r⁻¹ := by group
    _ = r * s * r⁻¹ := by rw [hss, one_mul, hsinv]

theorem exists_conj_mul_ZQ_of_invol [Finite G] (h : HSSetting z V) {s : G} (hsH : s ∈ hsH z)
    (hsQ' : s ∉ hsQ z) (hss : s * s = 1) {q : G} (hq : q ∈ hsQ z)
    (hsq : s * q * (s * q) = 1) : ∃ r ∈ hsQ z, ∃ u ∈ hsZQ z, s * q = r * (s * u) * r⁻¹ := by
  have hs2 : s * s ∈ hsQ z := by rw [hss]; exact (hsQ z).one_mem
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  have hqD : q ∈ hsFixQ z s := by
    refine ⟨hq, ?_⟩
    have h1 : s * q * s⁻¹ = q⁻¹ := by
      rw [hsinv]
      calc s * q * s = (s * q * (s * q)) * q⁻¹ := by group
        _ = q⁻¹ := by rw [hsq, one_mul]
    rw [h1, ← mul_inv_rev]
    exact (hsZQ z).inv_mem (h.mem_ZQ_of_eq_one_or_z (h.mul_self_eq_one_or_z hq))
  obtain ⟨r, hr, u, hu, rfl⟩ := h.exists_comm_mul_of_mem_fixQ hsH hsQ' hs2 hqD
  refine ⟨r, hr, u, hu, ?_⟩
  have hur : u * r⁻¹ = r⁻¹ * u :=
    (Subgroup.mem_centralizer_iff.mp hu.2 _ ((hsQ z).inv_mem hr)).symm
  calc s * (s * r * s⁻¹ * r⁻¹ * u) = (s * s) * r * s⁻¹ * (r⁻¹ * u) := by group
    _ = r * s * (u * r⁻¹) := by rw [hss, one_mul, hsinv, hur]
    _ = r * (s * u) * r⁻¹ := by group

theorem exists_conj_of_invol_mul [Finite G] (h : HSSetting z V) {s : G} (hsH : s ∈ hsH z)
    (hsK : s ∉ hsK z) (hss : s * s = 1) {w : G} (hwZ : w ∈ hsZQ z)
    (hwz : w ∉ Subgroup.zpowers z) {q : G} (hq : q ∈ hsQ z) (hsq : s * q * (s * q) = 1) :
    ∃ r ∈ hsQ z, s * q = r * s * r⁻¹ ∨ s * q = r * (s * w) * r⁻¹ := by
  obtain ⟨r, hr, u, hu, hsqu⟩ :=
    h.exists_conj_mul_ZQ_of_invol hsH (fun hsQ => hsK (h.Q_le_K hsQ)) hss hq hsq
  have hzC : z ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G) :=
    ⟨h.mem_Q, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hsH).symm⟩
  obtain ⟨r', hr', hr'z⟩ := h.exists_conj_eq_mul_of_invol hsH hsK hss hzC
  have hw1 : w ≠ 1 := fun h1 => hwz (h1 ▸ (Subgroup.zpowers z).one_mem)
  have hwz' : w ≠ z := fun h1 => hwz (h1 ▸ Subgroup.mem_zpowers z)
  have hww : w * w = z := by
    rcases h.z_eq_or_sq_of_mem_ZQ hwZ hw1 with h1 | h1
    · exact absurd h1.symm hwz'
    · exact h1.symm
  have hwr' : w * r'⁻¹ = r'⁻¹ * w :=
    (Subgroup.mem_centralizer_iff.mp hwZ.2 _ ((hsQ z).inv_mem hr')).symm
  have hwinv : w⁻¹ = z * w := by
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left h.z_mul_z
    calc w⁻¹ = (w * w)⁻¹ * w := by group
      _ = z * w := by rw [hww, hzinv]
  rcases h.mem_ZQ_eq hwZ hwz hu with hu1 | huw | huz | huw'
  · exact ⟨r, hr, Or.inl (by rw [hsqu, hu1, mul_one])⟩
  · exact ⟨r, hr, Or.inr (by rw [hsqu, huw])⟩
  · refine ⟨r * r', (hsQ z).mul_mem hr hr', Or.inl ?_⟩
    rw [hsqu, huz, hr'z]
    group
  · refine ⟨r * r', (hsQ z).mul_mem hr hr', Or.inr ?_⟩
    rw [hsqu, huw', hwinv]
    calc r * (s * (z * w)) * r⁻¹ = r * ((s * z) * w) * r⁻¹ := by group
      _ = r * ((r' * s * r'⁻¹) * w) * r⁻¹ := by rw [hr'z]
      _ = r * (r' * s * (r'⁻¹ * w)) * r⁻¹ := by group
      _ = r * (r' * s * (w * r'⁻¹)) * r⁻¹ := by rw [hwr']
      _ = r * r' * (s * w) * (r * r')⁻¹ := by group

end HSSetting

end CFSG.Quasithin.HSType
