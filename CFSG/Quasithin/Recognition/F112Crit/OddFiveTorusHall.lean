module

public import CFSG.Quasithin.Recognition.F112Crit.HallIndex

public section

namespace CFSG.Quasithin.F112Crit

open Subgroup

variable {G : Type*} [Group G]

theorem exists_relIndex_eq_two_pow_of_le {X K H : Subgroup G} (hXK : X ≤ K) (hKH : K ≤ H)
    {k : ℕ} (hk : X.relIndex H = 2 ^ k) : ∃ m : ℕ, X.relIndex K = 2 ^ m := by
  have hdvd : X.relIndex K ∣ 2 ^ k := by
    rw [← hk]
    exact ⟨K.relIndex H, (Subgroup.relIndex_mul_relIndex X K H hXK hKH).symm⟩
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨m, hm⟩

variable [Finite G]

theorem odd_relIndex_inf_of_normal_two {T H K : Subgroup G} (hTH : T ≤ H)
    (hHT : H ≤ normalizer (T : Set G)) (hodd : Odd (T.relIndex H)) (hKH : K ≤ H) :
    Odd ((T ⊓ K).relIndex K) := by
  have hKN : K ≤ normalizer (T : Set G) := hKH.trans hHT
  rw [Subgroup.inf_relIndex_right]
  rw [← CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer (A := K) (B := T) hKN]
  exact hodd.of_dvd_nat
    ⟨(K ⊔ T).relIndex H, (Subgroup.relIndex_mul_relIndex T (K ⊔ T) H le_sup_right
      (sup_le hKH hTH)).symm⟩

theorem card_eq_relIndex_of_hall {T H X : Subgroup G} (hTH : T ≤ H) (hT : IsPGroup 2 T)
    (hodd : Odd (T.relIndex H)) (hXH : X ≤ H) (hX : Odd (Nat.card X)) {k : ℕ}
    (hk : X.relIndex H = 2 ^ k) : Nat.card X = T.relIndex H := by
  have hcardT := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex hTH
  have hcardX := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex hXH
  rw [hk] at hcardX
  have heq : Nat.card T * T.relIndex H = Nat.card X * 2 ^ k := hcardT.symm.trans hcardX
  have hTc : Nat.Coprime (T.relIndex H) (2 ^ k) :=
    (Nat.coprime_two_right.mpr hodd).pow_right k
  have hTdvd : T.relIndex H ∣ Nat.card X :=
    hTc.dvd_of_dvd_mul_right (by rw [← heq]; exact dvd_mul_left _ _)
  obtain ⟨a, ha⟩ := hT.exists_card_eq
  have hXc : Nat.Coprime (Nat.card X) (2 ^ a) :=
    (Nat.coprime_two_right.mpr hX).pow_right a
  have hXdvd : Nat.card X ∣ T.relIndex H :=
    hXc.dvd_of_dvd_mul_left (by rw [← ha, heq]; exact dvd_mul_right _ _)
  exact Nat.dvd_antisymm hXdvd hTdvd

theorem exists_mem_mul_normalizer_of_hall {T K X : Subgroup G} (hTK : T ≤ K)
    (hKT : K ≤ normalizer (T : Set G)) (hT : IsPGroup 2 T) (hodd : Odd (T.relIndex K))
    (hXK : X ≤ K) (hX : Odd (Nat.card X)) {k : ℕ} (hk : X.relIndex K = 2 ^ k) {g : G}
    (hg : g ∈ normalizer (K : Set G)) : ∃ c ∈ K, c⁻¹ * g ∈ normalizer (X : Set G) := by
  let Y : Subgroup G := X.map (MulAut.conj g).toMonoidHom
  have hYK : Y ≤ K := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hgx : g * x * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hg x).mp (hXK hx)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hgx
  have hYcard : Nat.card Y = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hXeq : Nat.card X = T.relIndex K := card_eq_relIndex_of_hall hTK hT hodd hXK hX hk
  have hYeq : Nat.card Y = T.relIndex K := by rw [hYcard, hXeq]
  obtain ⟨c, hcK, hc⟩ := exists_conj_hall_of_normal_two hTK hKT hT hodd hXK hYK hXeq hYeq
  refine ⟨c, hcK, ?_⟩
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have hy : (MulAut.conj g).toMonoidHom x ∈ Y := Subgroup.mem_map_of_mem _ hx
  have hcy := (hc ((MulAut.conj g).toMonoidHom x)).mp hy
  have h1 : (c⁻¹ * g) * x * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * x * g⁻¹) * c := by group
  rw [h1]
  change c⁻¹ * (g * x * g⁻¹) * c ∈ X
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hcy

theorem exists_conj_le_of_hall {T H X K : Subgroup G} (hTH : T ≤ H)
    (hHT : H ≤ normalizer (T : Set G)) (hT : IsPGroup 2 T) (hodd : Odd (T.relIndex H))
    (hXH : X ≤ H) (hX : Odd (Nat.card X)) {k : ℕ} (hk : X.relIndex H = 2 ^ k) (hKH : K ≤ H)
    {m : ℕ} (hm : K.relIndex H = 2 ^ m) : ∃ c ∈ H, ∀ x ∈ X, c * x * c⁻¹ ∈ K := by
  have hKN : K ≤ normalizer (T : Set G) := hKH.trans hHT
  have hTinf : IsPGroup 2 ↥(T ⊓ K) := hT.to_inf_left
  have hoddInf : Odd ((T ⊓ K).relIndex K) :=
    odd_relIndex_inf_of_normal_two hTH hHT hodd hKH
  have hKNinf : K ≤ normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    intro k hk
    exact CFSG.QuasithinUnique.C5.mem_normalizer_inf (hKN hk) (Subgroup.le_normalizer hk)
  obtain ⟨X', hX'K, hX'card⟩ :=
    exists_hall_of_normal_two (T := T ⊓ K) (H := K) inf_le_right hKNinf hTinf hoddInf
  have hX'H : X' ≤ H := hX'K.trans hKH
  have hX'odd : Odd (Nat.card X') := hX'card ▸ hoddInf
  obtain ⟨a, ha⟩ := hTinf.exists_card_eq
  have hcardInf : Nat.card ↥(T ⊓ K) = X'.relIndex K := by
    have h1 := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex hX'K
    have h2 := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex
      (inf_le_right : T ⊓ K ≤ K)
    rw [hX'card] at h1
    have hpos : 0 < (T ⊓ K).relIndex K :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := (T ⊓ K).subgroupOf K))
    have heq : (T ⊓ K).relIndex K * X'.relIndex K =
        (T ⊓ K).relIndex K * Nat.card ↥(T ⊓ K) :=
      (h1.symm.trans h2).trans (mul_comm (Nat.card ↥(T ⊓ K)) ((T ⊓ K).relIndex K))
    exact (Nat.eq_of_mul_eq_mul_left hpos heq).symm
  have hX'rel : X'.relIndex H = X'.relIndex K * K.relIndex H :=
    (Subgroup.relIndex_mul_relIndex X' K H hX'K hKH).symm
  have hX'pow : X'.relIndex H = 2 ^ (a + m) := by
    rw [hX'rel, ← hcardInf, ha, hm, ← pow_add]
  have hXeq : Nat.card X = T.relIndex H := card_eq_relIndex_of_hall hTH hT hodd hXH hX hk
  have hX'eq : Nat.card X' = T.relIndex H :=
    card_eq_relIndex_of_hall hTH hT hodd hX'H hX'odd (k := a + m) hX'pow
  obtain ⟨c, hcH, hc⟩ :=
    exists_conj_hall_of_normal_two hTH hHT hT hodd hXH hX'H hXeq hX'eq
  refine ⟨c, hcH, ?_⟩
  intro x hx
  have hxX : c⁻¹ * (c * x * c⁻¹) * c ∈ X := by
    rwa [show c⁻¹ * (c * x * c⁻¹) * c = x from by group]
  exact hX'K ((hc (c * x * c⁻¹)).mpr hxX)

end CFSG.Quasithin.F112Crit

end
