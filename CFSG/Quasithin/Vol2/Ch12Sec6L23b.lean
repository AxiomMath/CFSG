module

public import CFSG.Quasithin.Vol2.Ch12Sec4A5Sum
public import CFSG.Quasithin.H13.A5Z1367i

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin Equiv A5Mod

namespace S126L23b

@[expose] def Klein (p q : Perm (Fin 5)) : Prop :=
  p ∈ invs5 ∧ q ∈ invs5 ∧ p ≠ 1 ∧ q ≠ 1 ∧ p ≠ q ∧ p * q = q * p ∧ p ∈ alt5 ∧ q ∈ alt5

instance (p q : Perm (Fin 5)) : Decidable (Klein p q) := by
  unfold Klein
  infer_instance

theorem no_order_four : ∀ p ∈ alt5, p ^ 4 = 1 → p * p = 1 := by
  decide +kernel

theorem klein_facts : ∀ p ∈ invs5, ∀ q ∈ invs5, Klein p q →
    [1, p, q, p * q].Nodup ∧ p * q ∈ alt5 ∧ (1 : Perm (Fin 5)) ∈ alt5 := by
  decide +kernel

theorem exists_three : ∀ p ∈ invs5, ∀ q ∈ invs5, Klein p q → ∃ c ∈ alt5, c ≠ 1 ∧ c * c * c = 1 ∧
    ∀ e ∈ [1, p, q, p * q], c⁻¹ * e * c ∈ [1, p, q, p * q] := by
  decide +kernel

theorem not_normal : ∀ p ∈ invs5, ∀ q ∈ invs5, Klein p q →
    ∃ g ∈ alt5, g * p * g⁻¹ ∉ [1, p, q, p * q] := by
  decide +kernel

theorem card_fix : ∀ p ∈ invs5, p ∈ alt5 → p ≠ 1 →
    (ev5.filter fun x => act5 p x = x).card = 4 := by
  decide +kernel

theorem not_quad : ∀ p ∈ invs5, ∀ q ∈ invs5, Klein p q →
    ∃ x ∈ ev5, act5 q (act5 p x + x) ≠ act5 p x + x := by
  decide +kernel

theorem odd15 : ∀ f : Perm (Fin 5), f ^ 15 = 1 → f ^ 3 = 1 ∨ f ^ 5 = 1 := by
  decide +kernel

theorem five_even : ∀ f : Perm (Fin 5), f ^ 5 = 1 → f ∈ alt5 := by
  decide +kernel

theorem card_ev5 : ev5.card = 16 := by
  decide

theorem mem_alt5_iff {p : Perm (Fin 5)} : p ∈ alt5 ↔ p ∈ alternatingGroup (Fin 5) := by
  rw [mem_alt5, Perm.mem_alternatingGroup]

theorem length_le_card {S : Subgroup (Perm (Fin 5))} {l : List (Perm (Fin 5))} (hl : l.Nodup)
    (hS : ∀ x ∈ l, x ∈ S) : l.length ≤ Nat.card S := by
  classical
  have h1 : l.toFinset ⊆ (S : Set (Perm (Fin 5))).toFinset := fun x hx => by
    simpa using hS x (List.mem_toFinset.1 hx)
  have h2 := Finset.card_le_card h1
  rw [List.toFinset_card_of_nodup hl, Set.toFinset_card, ← Nat.card_eq_fintype_card] at h2
  exact h2

theorem not_two_dvd_index {S : Subgroup (Perm (Fin 5))} (hS2 : IsPGroup 2 S)
    (h4 : 4 < Nat.card S) : ¬ 2 ∣ S.index := by
  obtain ⟨n, hn⟩ := hS2.exists_card_eq
  have h120 : S.index * Nat.card S = 120 := by
    rw [Subgroup.index_mul_card, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hdvd : 2 ^ n ∣ 120 := ⟨S.index, by rw [← hn, ← h120, mul_comm]⟩
  have hn3 : n ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ∣ 120 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at this
  have hn3' : 3 ≤ n := by
    by_contra h
    have : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hn] at h4
    omega
  have hn' : n = 3 := le_antisymm hn3 hn3'
  rw [hn, hn'] at h120
  have : S.index = 15 := by omega
  rw [this]
  decide

theorem mem_alt5_of_conj {S : Subgroup (Perm (Fin 5))} (hS2 : IsPGroup 2 S) {p q : Perm (Fin 5)}
    (hpI : p ∈ invs5) (hqI : q ∈ invs5) (hK : Klein p q) (hpS : p ∈ S) (hqS : q ∈ S)
    (hSE : ∀ s ∈ S, s ∈ alt5 → s ∈ [1, p, q, p * q]) {c : Perm (Fin 5)} (hc1 : c ≠ 1)
    (hc3 : c * c * c = 1) (hcE : ∀ e ∈ [1, p, q, p * q], c⁻¹ * e * c ∈ [1, p, q, p * q])
    {s : Perm (Fin 5)} (hs : s ∈ S) (hcs : c⁻¹ * s * c ∈ S) : s ∈ alt5 := by
  classical
  by_contra hsA
  obtain ⟨hnd, hpqA, h1A⟩ := klein_facts p hpI q hqI hK
  have hEmemS : ∀ e ∈ [1, p, q, p * q], e ∈ S := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    exacts [S.one_mem, hpS, hqS, S.mul_mem hpS hqS]
  have hsign : ∀ x ∈ S, x ∉ alt5 → s⁻¹ * x ∈ alt5 := by
    intro x hx hxA
    rw [mem_alt5] at hsA hxA ⊢
    rw [map_mul, map_inv]
    rcases Int.units_eq_one_or (Perm.sign s) with h | h
    · exact absurd h hsA
    rcases Int.units_eq_one_or (Perm.sign x) with h' | h'
    · exact absurd h' hxA
    rw [h, h']
    rfl
  have hle : ∀ x ∈ S, c⁻¹ * x * c ∈ S := by
    intro x hx
    by_cases hxA : x ∈ alt5
    · exact hEmemS _ (hcE x (hSE x hx hxA))
    · have h1 := hSE _ (S.mul_mem (S.inv_mem hs) hx) (hsign x hx hxA)
      have e : c⁻¹ * x * c = (c⁻¹ * s * c) * (c⁻¹ * (s⁻¹ * x) * c) := by group
      rw [e]
      exact S.mul_mem hcs (hEmemS _ (hcE _ h1))
  have hcN : c⁻¹ ∈ Subgroup.normalizer (S : Set (Perm (Fin 5))) := by
    have hmap : S.map (MulAut.conj c⁻¹).toMonoidHom ≤ S := by
      rintro _ ⟨x, hx, rfl⟩
      simpa using hle x hx
    have hcard : Nat.card (S.map (MulAut.conj c⁻¹).toMonoidHom) = Nat.card S :=
      Nat.card_congr (Subgroup.equivMapOfInjective S _ (MulAut.conj c⁻¹).injective).toEquiv.symm
    have heq := Subgroup.eq_of_le_of_card_ge hmap hcard.ge
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : c⁻¹ * x * c⁻¹⁻¹ ∈ S.map (MulAut.conj c⁻¹).toMonoidHom := ⟨x, hx, by simp⟩
      rwa [heq] at this
    · intro hx
      rw [← heq] at hx
      obtain ⟨y, hy, hye⟩ := hx
      have : y = x := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hye
        exact mul_left_cancel (mul_right_cancel hye)
      rwa [← this]
  have hnd5 : [1, p, q, p * q, s].Nodup := by
    have hsl : s ∉ [1, p, q, p * q] := by
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      exacts [hsA h1A, hsA hK.2.2.2.2.2.2.1, hsA hK.2.2.2.2.2.2.2, hsA hpqA]
    rw [show [1, p, q, p * q, s] = [1, p, q, p * q] ++ [s] by rfl, List.nodup_append]
    exact ⟨hnd, List.nodup_singleton s, fun a ha b hb => by
      rw [List.mem_singleton] at hb
      subst hb
      exact fun h => hsl (h ▸ ha)⟩
  have h5 := length_le_card hnd5 (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [S.one_mem, hpS, hqS, S.mul_mem hpS hqS, hs])
  have hidx := not_two_dvd_index hS2 (by
    simp only [List.length_cons, List.length_nil] at h5
    omega)
  have hord : orderOf c⁻¹ = 3 := by
    rw [orderOf_inv]
    refine orderOf_eq_prime ?_ hc1
    rw [pow_three, ← mul_assoc]
    exact hc3
  exact A5.factSylowNormS5 S hS2 hidx c⁻¹ hcN hord


theorem card_A5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem card_le_four {P : Subgroup (Perm (Fin 5))} (hP2 : IsPGroup 2 P)
    (hPA : P ≤ alternatingGroup (Fin 5)) : Nat.card P ≤ 4 := by
  obtain ⟨n, hn⟩ := hP2.exists_card_eq
  have hdvd : 2 ^ n ∣ 60 := by
    rw [← hn, ← card_A5]
    exact Subgroup.card_dvd_of_le hPA
  have hn2 : n ≤ 2 := by
    by_contra h
    have : 2 ^ 3 ∣ 60 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at this
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    _ = 4 := by norm_num

theorem isSylowTwoOf_map' {Γ Δ : Type*} [Group Γ] [Group Δ] {H S : Subgroup Γ}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S H) (ρ : ↥H →* Δ) :
    CFSG.QuasithinUnique.IsSylowTwoOf ((S.subgroupOf H).map ρ) ρ.range := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨Subgroup.map_le_range ρ _, hS2.map ρ, ?_⟩
  have h1 : ((S.subgroupOf H).map ρ).subgroupOf ρ.range =
      (S.subgroupOf H).map ρ.rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  show ¬ 2 ∣ (((S.subgroupOf H).map ρ).subgroupOf ρ.range).index
  rw [h1]
  intro hd
  apply hS.2.2
  exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

theorem klein_of_card_four {E : Subgroup (Perm (Fin 5))} (hEA : E ≤ alternatingGroup (Fin 5))
    (h4 : Nat.card E = 4) :
    ∃ p ∈ invs5, ∃ q ∈ invs5, Klein p q ∧ p ∈ E ∧ q ∈ E ∧ ∀ x ∈ E, x ∈ [1, p, q, p * q] := by
  classical
  have hexp : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥E) ^ 4 = 1 := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥E)
      rw [h4] at this
      exact orderOf_dvd_iff_pow_eq_one.1 this
    have h2 : x ^ 4 = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    exact no_order_four x (mem_alt5_iff.2 (hEA hx)) h2
  have hinv : ∀ x ∈ E, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hexp x hx)
  obtain ⟨p, hpE, hp1⟩ : ∃ p ∈ E, p ≠ 1 := by
    by_contra h
    push Not at h
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 h
    rw [this, Subgroup.card_bot] at h4
    omega
  obtain ⟨q, hqE, hq1, hqp⟩ : ∃ q ∈ E, q ≠ 1 ∧ q ≠ p := by
    by_contra h
    push Not at h
    have h2 := length_le_card (l := [1, p]) (by simp [Ne.symm hp1])
      (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        exacts [E.one_mem, hpE])
    have hsub : ∀ x ∈ E, x ∈ ([1, p] : List (Perm (Fin 5))) := by
      intro x hx
      by_cases hx1 : x = 1
      · simp [hx1]
      · simp [h x hx hx1]
    have h3 : Nat.card E ≤ 2 := by
      have : (E : Set (Perm (Fin 5))).toFinset ⊆ ([1, p] : List (Perm (Fin 5))).toFinset := by
        intro x hx
        simp only [Set.mem_toFinset, SetLike.mem_coe] at hx
        exact List.mem_toFinset.2 (hsub x hx)
      have h5 := Finset.card_le_card this
      rw [Set.toFinset_card, ← Nat.card_eq_fintype_card] at h5
      exact h5.trans (List.toFinset_card_le _)
    omega
  have hpI : p ∈ invs5 := mem_invs5.2 (hexp p hpE)
  have hqI : q ∈ invs5 := mem_invs5.2 (hexp q hqE)
  have hcomm : p * q = q * p := by
    have h1 := hexp _ (E.mul_mem hpE hqE)
    have h2 : p * q = (p * q)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2, mul_inv_rev, hinv q hqE, hinv p hpE]
  have hK : Klein p q := ⟨hpI, hqI, hp1, hq1, Ne.symm hqp, hcomm,
    mem_alt5_iff.2 (hEA hpE), mem_alt5_iff.2 (hEA hqE)⟩
  refine ⟨p, hpI, q, hqI, hK, hpE, hqE, fun x hx => ?_⟩
  by_contra hxl
  obtain ⟨hnd, -, -⟩ := klein_facts p hpI q hqI hK
  have hnd5 : [1, p, q, p * q, x].Nodup := by
    rw [show [1, p, q, p * q, x] = [1, p, q, p * q] ++ [x] by rfl, List.nodup_append]
    exact ⟨hnd, List.nodup_singleton x, fun a ha b hb => by
      rw [List.mem_singleton] at hb
      subst hb
      exact fun h => hxl (h ▸ ha)⟩
  have h5 := length_le_card hnd5 (fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    exacts [E.one_mem, hpE, hqE, E.mul_mem hpE hqE, hx])
  simp only [List.length_cons, List.length_nil] at h5
  omega

theorem mem_of_mem_alt5 {S E : Subgroup (Perm (Fin 5))} (hS2 : IsPGroup 2 S) (hES : E ≤ S)
    (hEA : E ≤ alternatingGroup (Fin 5)) (h4 : Nat.card E = 4) :
    ∀ s ∈ S, s ∈ alt5 → s ∈ E := by
  have hle : E ≤ S ⊓ alternatingGroup (Fin 5) := le_inf hES hEA
  have hc := card_le_four (hS2.to_inf_left (K := alternatingGroup (Fin 5))) inf_le_right
  have heq : E = S ⊓ alternatingGroup (Fin 5) := Subgroup.eq_of_le_of_card_ge hle (by omega)
  intro s hs hsA
  rw [heq]
  exact ⟨hs, mem_alt5_iff.1 hsA⟩


variable {G : Type} [Group G] [Finite G]

theorem exists_sigma {H K VH W : Subgroup G} (d : Data K W) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (h2K : ∀ h ∈ H, ∃ j : ℕ, h ^ 2 ^ j ∈ K)
    (hred : IsTwoReducedIn H VH) (hWV : W ≤ VH)
    (hCW : K ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (VH : Set G)) :
    ∃ σ : ↥H →* Perm (Fin 5),
      (∀ h : ↥H, σ h = 1 ↔ (h : G) ∈ Subgroup.centralizer (VH : Set G)) ∧
      ∀ h : ↥H, (h : G) ∈ K → σ h = d.qG h := by
  classical
  obtain ⟨-, hHVH, -, hred'⟩ := hred
  have hCVW : Subgroup.centralizer (VH : Set G) ≤ Subgroup.centralizer (W : Set G) :=
    Subgroup.centralizer_le hWV
  have hconjC : ∀ h ∈ H, ∀ x ∈ Subgroup.centralizer (VH : Set G),
      h * x * h⁻¹ ∈ Subgroup.centralizer (VH : Set G) := by
    intro h hh x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro v hv
    have hv' : h⁻¹ * v * h⁻¹⁻¹ ∈ VH := (Subgroup.mem_normalizer_iff.1 (hHVH (inv_mem hh)) v).1 hv
    have h1 := hx _ hv'
    calc v * (h * x * h⁻¹) = h * ((h⁻¹ * v * h⁻¹⁻¹) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * v * h⁻¹⁻¹)) * h⁻¹ := by rw [h1]
      _ = h * x * h⁻¹ * v := by group
  have hHC : ∀ h ∈ H, ∀ k ∈ K, k ∈ Subgroup.centralizer (W : Set G) →
      h * k * h⁻¹ ∈ Subgroup.centralizer (W : Set G) := fun h hh k hk hkW =>
    hCVW (hconjC h hh k (hCW ⟨hk, hkW⟩))
  have hex : ∀ h : ↥H, ∃ σ : Perm (Fin 5), ∀ k ∈ K,
      d.qG ((h : G) * k * (h : G)⁻¹) = σ * d.qG k * σ⁻¹ := fun h =>
    d.exists_perm (hHK h.2) (hHC h h.2)
  choose σ hσ using hex
  have hσmul : ∀ h₁ h₂ : ↥H, σ (h₁ * h₂) = σ h₁ * σ h₂ := by
    intro h₁ h₂
    refine d.perm_unique (hσ (h₁ * h₂)) (fun k hk => ?_)
    have hk₂ : (h₂ : G) * k * (h₂ : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hHK h₂.2) k).1 hk
    rw [show ((h₁ * h₂ : ↥H) : G) * k * ((h₁ * h₂ : ↥H) : G)⁻¹ =
      (h₁ : G) * ((h₂ : G) * k * (h₂ : G)⁻¹) * (h₁ : G)⁻¹ by simp only [Subgroup.coe_mul]; group,
      hσ h₁ _ hk₂, hσ h₂ k hk]
    group
  have hσone : σ 1 = 1 := by
    have h1 := hσmul 1 1
    rw [mul_one] at h1
    exact (mul_eq_left.1 h1.symm)
  let σH : ↥H →* Perm (Fin 5) :=
    { toFun := σ, map_one' := hσone, map_mul' := hσmul }
  have hσH : ∀ h, σH h = σ h := fun h => rfl
  have hσK : ∀ h : ↥H, (h : G) ∈ K → σ h = d.qG h := by
    intro h hhK'
    refine d.perm_unique (hσ h) (fun k hk => ?_)
    rw [d.qG_mul (K.mul_mem hhK' hk) (K.inv_mem hhK'), d.qG_mul hhK' hk, d.qG_inv hhK']
  refine ⟨σH, fun h => ?_, hσK⟩
  rw [hσH]
  constructor
  · intro h1
    let D := σH.ker.map H.subtype
    have hDH : D ≤ H := fun x hx => by
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
      exact y.2
    have hHD : H ≤ Subgroup.normalizer (D : Set G) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hn
        refine Subgroup.mem_map.2 ⟨⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹, ?_, rfl⟩
        rw [MonoidHom.mem_ker] at hy ⊢
        rw [map_mul, map_mul, hy, mul_one, map_inv, mul_inv_cancel]
      · intro hn
        obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.1 hn
        refine Subgroup.mem_map.2 ⟨⟨x, hx⟩⁻¹ * y * ⟨x, hx⟩, ?_, ?_⟩
        · rw [MonoidHom.mem_ker] at hy ⊢
          rw [map_mul, map_mul, hy, mul_one, map_inv, inv_mul_cancel]
        · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hye ⊢
          rw [hye]
          group
    have hD2 : ∀ x ∈ D, ∃ j : ℕ, x ^ 2 ^ j ∈ Subgroup.centralizer (VH : Set G) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨j, hj⟩ := h2K y y.2
      refine ⟨j, ?_⟩
      have h2 : σ (y ^ 2 ^ j) = 1 := by
        rw [← hσH, map_pow, (MonoidHom.mem_ker).1 hy, one_pow]
      rw [hσK _ (by simpa using hj)] at h2
      have h3 := (d.qG_eq_one_iff (by simpa using hj)).1 (by simpa using h2)
      exact hCW ⟨by simpa using hj, by simpa using h3⟩
    have hDC := hred' D hDH hHD hD2
    exact hDC (Subgroup.mem_map.2 ⟨h, (MonoidHom.mem_ker).2 h1, rfl⟩)
  · intro hC
    refine (d.perm_unique (hσ h) (fun k hk => ?_)).trans rfl
    rw [one_mul, inv_one, mul_one]
    have hk' : (h : G) * k * (h : G)⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.1 (hHK h.2) k).1 hk) (K.inv_mem hk)
    have hkC : (h : G) * k * (h : G)⁻¹ * k⁻¹ ∈ Subgroup.centralizer (VH : Set G) := by
      rw [show (h : G) * k * (h : G)⁻¹ * k⁻¹ = (h : G) * (k * (h : G)⁻¹ * k⁻¹) by group]
      exact Subgroup.mul_mem _ hC (hconjC k (hKH hk) _ (inv_mem hC))
    have h1 := (d.qG_eq_one_iff hk').2 (hCVW hkC)
    have hk'' : (h : G) * k * (h : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hHK h.2) k).1 hk
    rw [d.qG_mul hk'' (K.inv_mem hk), d.qG_inv hk, mul_inv_eq_one] at h1
    exact h1

omit [Finite G] in
theorem exists_K_of_alt5 {H K VH W : Subgroup G} (d : Data K W) (hKH : K ≤ H)
    {σ : ↥H →* Perm (Fin 5)}
    (hσker : ∀ h : ↥H, σ h = 1 ↔ (h : G) ∈ Subgroup.centralizer (VH : Set G))
    (hσK : ∀ h : ↥H, (h : G) ∈ K → σ h = d.qG h) {a : ↥H} (ha : σ a ∈ alt5) :
    ∃ k ∈ K, d.qG k = σ a ∧ (a : G) * k⁻¹ ∈ Subgroup.centralizer (VH : Set G) := by
  obtain ⟨k, hk, hkq⟩ := d.exists_qG_eq ha
  refine ⟨k, hk, hkq, ?_⟩
  have h1 : σ (a * (⟨k, hKH hk⟩ : ↥H)⁻¹) = 1 := by
    rw [map_mul, map_inv, hσK ⟨k, hKH hk⟩ hk, hkq, mul_inv_cancel]
  have := (hσker _).1 h1
  simpa using this

end S126L23b

end CFSG.Quasithin.H13
