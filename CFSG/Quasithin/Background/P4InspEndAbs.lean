module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.GroupTheory.Sylow
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.Quasithin.G11.P4InspEnd

open Equiv

theorem p4inspend_s5_klein_aux : ∀ a : Perm (Fin 5), (a ≠ 1 ∧ a * a = 1) →
    ∀ b : Perm (Fin 5), (b ≠ 1 ∧ a ≠ b ∧ b * b = 1 ∧ a * b = b * a) →
      ∀ s : Perm (Fin 5), (s * a = a * s ∧ s * b = b * s) →
        (s = 1 ∨ s = a ∨ s = b ∨ s = a * b) := by
  decide +kernel

theorem p4inspend_s5_klein {a b s : Perm (Fin 5)} (ha1 : a ≠ 1) (ha2 : a * a = 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hb2 : b * b = 1) (habc : a * b = b * a) (hsa : s * a = a * s)
    (hsb : s * b = b * s) : s = 1 ∨ s = a ∨ s = b ∨ s = a * b :=
  p4inspend_s5_klein_aux a ⟨ha1, ha2⟩ b ⟨hb1, hab, hb2, habc⟩ s ⟨hsa, hsb⟩

theorem p4inspend_two_ne_one {P : Type*} [Group P] (h : 2 < Nat.card P) :
    ∃ x y : P, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype P := Fintype.ofFinite P
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h
  by_cases ha : a = 1
  · exact ⟨b, c, by rw [ha] at hab; exact hab.symm, by rw [ha] at hac; exact hac.symm, hbc⟩
  · by_cases hb : b = 1
    · exact ⟨a, c, ha, by rw [hb] at hbc; exact hbc.symm, hac⟩
    · exact ⟨a, b, ha, hb, hab⟩

@[expose] def p4inspendConj {G : Type*} [Group G] (K : Subgroup G) (q : G)
    (hq : ∀ k ∈ K, q * k * q⁻¹ ∈ K) (hq' : ∀ k ∈ K, q⁻¹ * k * q ∈ K) : ↥K ≃* ↥K where
  toFun k := ⟨q * k * q⁻¹, hq k k.2⟩
  invFun k := ⟨q⁻¹ * k * q, hq' k k.2⟩
  left_inv k := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv k := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

theorem p4inspend_aut_alt {K : Type*} [Group K] {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (φ : K ≃* ↥(alternatingGroup (Fin n))) (α : K ≃* K) :
    ∃ σ : Perm (Fin n), ∀ k : K,
      ((φ (α k) : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) =
        σ * ((φ k : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) * σ⁻¹ := by
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn
    hn6).2 (φ.symm.trans (α.trans φ))
  refine ⟨σ, fun k => ?_⟩
  have h := congrArg (fun f : MulAut ↥(alternatingGroup (Fin n)) =>
    ((f (φ k) : ↥(alternatingGroup (Fin n))) : Perm (Fin n))) hσ
  simp only [MulAut.conjNormal_apply] at h
  rw [h]
  simp

theorem p4inspend_card_sylow_five {K : Type*} [Group K] (e : K ≃* ↥(alternatingGroup (Fin 5)))
    (P : Sylow 2 K) : Nat.card ↥(P : Subgroup K) = 4 := by
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card K = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  rw [Sylow.card_eq_multiplicity, hK, Nat.factorization_def _ Nat.prime_two]
  have h60 : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
  rw [h60, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem p4inspend_alt_order4 {n : ℕ} (hn : n = 6 ∨ n = 8) :
    ∃ x : ↥(alternatingGroup (Fin n)), x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  rcases hn with rfl | rfl
  · refine ⟨⟨swap (0 : Fin 6) 1 * swap 1 2 * swap 2 3 * swap 4 5,
      Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩, ?_, ?_⟩
    · apply Subtype.ext
      show (swap (0 : Fin 6) 1 * swap 1 2 * swap 2 3 * swap 4 5) ^ 4 = 1
      decide
    · intro h
      have := congrArg Subtype.val h
      revert this
      show (swap (0 : Fin 6) 1 * swap 1 2 * swap 2 3 * swap 4 5) ^ 2 ≠ 1
      decide
  · refine ⟨⟨swap (0 : Fin 8) 1 * swap 1 2 * swap 2 3 * swap 4 5,
      Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩, ?_, ?_⟩
    · apply Subtype.ext
      show (swap (0 : Fin 8) 1 * swap 1 2 * swap 2 3 * swap 4 5) ^ 4 = 1
      decide
    · intro h
      have := congrArg Subtype.val h
      revert this
      show (swap (0 : Fin 8) 1 * swap 1 2 * swap 2 3 * swap 4 5) ^ 2 ≠ 1
      decide

theorem p4inspend_Q_le {G : Type*} [Group G] (K Q : Subgroup G) (P : Subgroup ↥K)
    (φ : ↥K ≃* ↥(alternatingGroup (Fin 5)))
    (hcent : ∀ r : G, (∀ k ∈ K, r * k = k * r) → r = 1)
    (hnorm : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ ∈ K)
    (hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hQ2 : ∀ a ∈ Q, a * a = 1)
    (hPQ : ∀ s ∈ P, ((s : ↥K) : G) ∈ Q) (hP : 2 < Nat.card ↥P) :
    ∀ q ∈ Q, ∃ s ∈ P, ((s : ↥K) : G) = q := by
  intro q hq
  let αq : ↥K ≃* ↥K := p4inspendConj K q (hnorm q hq)
    (fun k hk => by simpa using hnorm q⁻¹ (Q.inv_mem hq) k hk)
  have hαq : ∀ k : ↥K, ((αq k : ↥K) : G) = q * k * q⁻¹ := fun k => rfl
  obtain ⟨σ, hσ'⟩ := p4inspend_aut_alt (n := 5) le_rfl (by norm_num) φ αq
  have hσP : ∀ s : ↥K, s ∈ P →
      σ * ((φ s : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) =
        ((φ s : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) * σ := by
    intro s hs
    have hqs : q * (s : G) = (s : G) * q := hQc q hq s (hPQ s hs)
    have hfix : αq s = s := by
      apply Subtype.ext
      rw [hαq]
      calc q * (s : G) * q⁻¹ = (s : G) * q * q⁻¹ := by rw [hqs]
        _ = s := by group
    have h := hσ' s
    rw [hfix] at h
    calc σ * ((φ s : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5))
        = σ * ((φ s : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) * σ⁻¹ * σ := by group
      _ = ((φ s : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) * σ := by rw [← h]
  obtain ⟨x, y, hx1, hy1, hxy⟩ := p4inspend_two_ne_one hP
  have hxQ : ((x : ↥K) : G) ∈ Q := hPQ x x.2
  have hyQ : ((y : ↥K) : G) ∈ Q := hPQ y y.2
  have hxx : (x : ↥K) * (x : ↥K) = 1 := by
    apply Subtype.ext
    exact hQ2 _ hxQ
  have hyy : (y : ↥K) * (y : ↥K) = 1 := by
    apply Subtype.ext
    exact hQ2 _ hyQ
  have hxyc : (x : ↥K) * (y : ↥K) = (y : ↥K) * (x : ↥K) := by
    apply Subtype.ext
    exact hQc _ hxQ _ hyQ
  have hcoe : ∀ z : ↥K, ((φ z : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) = 1 → z = 1 := by
    intro z hz
    apply φ.injective
    apply Subtype.ext
    simpa using hz
  have hsel : ∃ s : ↥K, s ∈ P ∧
      σ = ((φ s : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) := by
    have hk := p4inspend_s5_klein
      (a := ((φ (x : ↥K) : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)))
      (b := ((φ (y : ↥K) : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5))) (s := σ)
      (fun h => hx1 (Subtype.ext (hcoe _ h))) (by
        have := congrArg (fun z : ↥K => ((φ z : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5))) hxx
        simpa using this)
      (fun h => hy1 (Subtype.ext (hcoe _ h))) (by
        intro h
        apply hxy
        apply Subtype.ext
        apply φ.injective
        exact Subtype.ext h) (by
        have := congrArg (fun z : ↥K => ((φ z : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5))) hyy
        simpa using this) (by
        have := congrArg (fun z : ↥K => ((φ z : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5))) hxyc
        simpa using this) (hσP x x.2) (hσP y y.2)
    rcases hk with h | h | h | h
    · exact ⟨1, P.one_mem, by simpa using h⟩
    · exact ⟨x, x.2, h⟩
    · exact ⟨y, y.2, h⟩
    · refine ⟨x * y, P.mul_mem x.2 y.2, ?_⟩
      rw [h]
      simp
  obtain ⟨s, hsP, hsσ⟩ := hsel
  refine ⟨s, hsP, ?_⟩
  have hr : (s : G)⁻¹ * q = 1 := by
    apply hcent
    intro k hk
    let k' : ↥K := ⟨k, hk⟩
    have h1 : φ (αq k') = φ (s * k' * s⁻¹) := by
      apply Subtype.ext
      rw [hσ' k', hsσ]
      simp
    have h2 : αq k' = s * k' * s⁻¹ := φ.injective h1
    have h3 : q * k * q⁻¹ = (s : G) * k * (s : G)⁻¹ := by
      have := congrArg (fun z : ↥K => (z : G)) h2
      simpa [hαq] using this
    calc (s : G)⁻¹ * q * k = (s : G)⁻¹ * (q * k * q⁻¹) * q := by group
      _ = (s : G)⁻¹ * ((s : G) * k * (s : G)⁻¹) * q := by rw [h3]
      _ = k * ((s : G)⁻¹ * q) := by group
  exact inv_mul_eq_one.1 hr

theorem p4inspend_card_le_sq {K : Type*} [Group K] [Finite K] (P C : Subgroup K) (α : K ≃* K)
    (hC : ∀ x, x ∈ C ↔ x ∈ P ∧ α x = x) (hP : ∀ s ∈ P, α s ∈ P) (hα2 : ∀ s, α (α s) = s)
    (hord : ∀ s ∈ P, (s⁻¹ * α s) * (s⁻¹ * α s) = 1) :
    Nat.card ↥P ≤ Nat.card ↥C * Nat.card ↥C := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hfix : ∀ s ∈ P, s⁻¹ * α s ∈ C := by
    intro s hs
    refine (hC _).2 ⟨P.mul_mem (P.inv_mem hs) (hP s hs), ?_⟩
    have h1 : α (s⁻¹ * α s) = (s⁻¹ * α s)⁻¹ := by
      rw [map_mul, map_inv, hα2]
      group
    rw [h1]
    exact inv_eq_of_mul_eq_one_right (hord s hs)
  let f : ↥P → ↥C := fun s => ⟨(s : K)⁻¹ * α s, hfix s s.2⟩
  have hfiber : ∀ c ∈ (Finset.univ : Finset ↥C),
      (Finset.univ.filter (fun a : ↥P => f a = c)).card ≤ Nat.card ↥C := by
    intro c _
    by_cases hne : (Finset.univ.filter (fun a : ↥P => f a = c)).Nonempty
    · obtain ⟨a₀, ha₀⟩ := hne
      have ha₀c : f a₀ = c := (Finset.mem_filter.1 ha₀).2
      have hmem : ∀ a : ↥P, f a = c → (a : K) * (a₀ : K)⁻¹ ∈ C := by
        intro a hac
        have e : (a : K)⁻¹ * α a = (a₀ : K)⁻¹ * α a₀ := by
          have := congrArg Subtype.val (hac.trans ha₀c.symm)
          exact this
        refine (hC _).2 ⟨P.mul_mem a.2 (P.inv_mem a₀.2), ?_⟩
        have e2 : α a = (a : K) * ((a₀ : K)⁻¹ * α a₀) := by
          rw [← e]
          group
        rw [map_mul, map_inv, e2]
        group
      let g : ↥P → ↥C := fun a =>
        if h : f a = c then ⟨(a : K) * (a₀ : K)⁻¹, hmem a h⟩ else 1
      have hinj : Set.InjOn g ↑(Finset.univ.filter (fun a : ↥P => f a = c)) := by
        intro a ha b hb hab
        have ha' : f a = c := (Finset.mem_filter.1 ha).2
        have hb' : f b = c := (Finset.mem_filter.1 hb).2
        simp only [g, ha', hb', dite_true] at hab
        have := congrArg Subtype.val hab
        apply Subtype.ext
        simpa using this
      have := Finset.card_le_card_of_injOn g (fun a _ => Finset.mem_univ _) hinj
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
      exact this
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Nat.zero_le _
  have key := Finset.card_le_mul_card_image_of_maps_to (s := (Finset.univ : Finset ↥P))
    (t := (Finset.univ : Finset ↥C)) (f := f) (fun a _ => Finset.mem_univ _) (Nat.card ↥C) hfiber
  rw [Finset.card_univ, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at key
  exact key

theorem p4inspend_no_order4 {K : Type*} [Group K] [Finite K] (P : Sylow 2 K)
    (hP : ∀ s ∈ P, s * s = 1) (x : K) (h4 : x ^ 4 = 1) (h2 : x ^ 2 ≠ 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf x = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) (by simpa using h2) (by simpa using h4)
    simpa using this
  have hpg : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.iff_card.2 ⟨2, ?_⟩
    rw [Nat.card_zpowers, hord]
    norm_num
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q P
  have hxQ : x ∈ (Q : Subgroup K) := hQ (Subgroup.mem_zpowers x)
  have hmem : g * x * g⁻¹ ∈ ((g • Q : Sylow 2 K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (Q : Subgroup K) hxQ
  rw [hg] at hmem
  have hsq := hP _ hmem
  apply h2
  have h' : x ^ 2 = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by
    rw [pow_two]
    group
  rw [h', hsq]
  group

end CFSG.Quasithin.G11.P4InspEnd
