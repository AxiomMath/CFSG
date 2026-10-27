module

public import CFSG.Milestones.ASVolI.J4
public import CFSG.Sporadic.Schreier.RuJ49Facts
public import CFSG.Milestones.ASVolI.J4Hexagon
public import CFSG.Sporadic.Schreier.RuJ49Sl2Facts
public import CFSG.Sporadic.Schreier.RuInvClasses
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Sporadic.Schreier.RuLGroup
public import CFSG.Sporadic.Schreier.RuIso
public import CFSG.Quasithin.Recognition.RuTypeJ47k
public import CFSG.Quasithin.Recognition.RuTypeJ11
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuCert
public import CFSG.Quasithin.Vol2.TwoF4F48Cert

public section

namespace CFSG.ASVolI

open CFSG.Open

theorem burnsideJ49B_fin12_step : ∀ a b c : Fin 12, (b - a = 1 ∨ a - b = 1) →
    (c - b = 1 ∨ b - c = 1) → c ≠ a → c - b = b - a := by
  decide

theorem burnsideJ49B_fin12_add_two (i : Fin 12) : i + 2 ≠ i := by
  revert i
  decide

open Fin.CommRing Fin.NatCast in
theorem burnsideJ49B_aut_cycle12 (σ : SimpleGraph.cycleGraph 12 ≃g SimpleGraph.cycleGraph 12) :
    (∃ c : Fin 12, ∀ i, σ i = i + c) ∨ (∃ c : Fin 12, ∀ i, σ i = c - i) := by
  have hadj : ∀ a b : Fin 12, (SimpleGraph.cycleGraph 12).Adj a b ↔ (b - a = 1 ∨ a - b = 1) := by
    intro a b
    rw [SimpleGraph.cycleGraph_adj]
    exact or_comm
  have hσadj : ∀ a b : Fin 12, (b - a = 1 ∨ a - b = 1) → (σ b - σ a = 1 ∨ σ a - σ b = 1) := by
    intro a b h
    exact (hadj _ _).1 (σ.map_rel_iff.2 ((hadj a b).2 h))
  have hone : ∀ i : Fin 12, (i + 1) - i = 1 ∨ i - (i + 1) = 1 := fun i => Or.inl (by simp)
  set δ : Fin 12 := σ 1 - σ 0 with hδ
  have hstep : ∀ n : ℕ, σ ((n : Fin 12) + 1) - σ (n : Fin 12) = δ := by
    intro n
    induction n with
    | zero => simp [hδ]
    | succ n ih =>
      have h1 := hσadj _ _ (hone (n : Fin 12))
      have h2 := hσadj _ _ (hone ((n : Fin 12) + 1))
      have hne : σ ((n : Fin 12) + 1 + 1) ≠ σ (n : Fin 12) := by
        intro h
        have := σ.injective h
        have h3 : (n : Fin 12) + 1 + 1 = (n : Fin 12) + 2 := by ring
        rw [h3] at this
        exact burnsideJ49B_fin12_add_two _ this
      have := burnsideJ49B_fin12_step _ _ _ h1 h2 hne
      rw [Nat.cast_succ, this, ih]
  have hval : ∀ n : ℕ, σ (n : Fin 12) = σ 0 + n • δ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hstep n
      rw [Nat.cast_succ, succ_nsmul, ← add_assoc, ← ih]
      rw [← this]
      ring
  have hall : ∀ i : Fin 12, σ i = σ 0 + (i.val) • δ := by
    intro i
    have := hval i.val
    simpa using this
  have h01 := hσadj 0 1 (by left; decide)
  rcases h01 with h | h
  · left
    refine ⟨σ 0, fun i => ?_⟩
    rw [hall i]
    have hδ1 : δ = 1 := by rw [hδ]; simpa using h
    rw [hδ1]
    simp [add_comm]
  · right
    refine ⟨σ 0, fun i => ?_⟩
    rw [hall i]
    have hδ1 : δ = -1 := by
      rw [hδ]
      have : σ 1 - σ 0 = -(σ 0 - σ 1) := by ring
      rw [this, h]
    rw [hδ1]
    simp [sub_eq_add_neg]

section Five

variable {G : Type} [Group G]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_card_zpowers_five {t : G} (h5 : t ^ 5 = 1) (h1 : t ≠ 1) :
    Nat.card (Subgroup.zpowers t) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Nat.card_zpowers, orderOf_eq_prime h5 h1]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_inf_eq_bot {X Y : Subgroup G} (hX : Nat.card X = 5) (hY : Nat.card Y = 5)
    (hne : X ≠ Y) : X ⊓ Y = ⊥ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have : Finite Y := Nat.finite_of_card_ne_zero (by rw [hY]; norm_num)
  have hd : Nat.card (X ⊓ Y : Subgroup G) ∣ 5 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : X ⊓ Y ≤ X)
    rwa [hX] at this
  rcases (Nat.dvd_prime Nat.prime_five).1 hd with h1 | h5
  · exact (Subgroup.card_eq_one).1 h1
  · exfalso
    have hXe : X ⊓ Y = X := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h5, hX])
    have hYe : X ⊓ Y = Y := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h5, hY])
    exact hne (hXe.symm.trans hYe)

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_eq_one_of_mem_two {X Y : Subgroup G} (hX : Nat.card X = 5)
    (hY : Nat.card Y = 5) (hne : X ≠ Y) {x : G} (hx : x ∈ X) (hy : x ∈ Y) : x = 1 := by
  have := burnsideJ49B_inf_eq_bot hX hY hne
  have h : x ∈ X ⊓ Y := ⟨hx, hy⟩
  rw [this] at h
  exact h

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_comm_zpowers_iff {a b : G} :
    ⁅Subgroup.zpowers a, Subgroup.zpowers b⁆ = ⊥ ↔ a * b = b * a := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  constructor
  · intro h
    have ha : a ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := h (Subgroup.mem_zpowers a)
    exact (Subgroup.mem_centralizer_iff.1 ha b (Subgroup.mem_zpowers b)).symm
  · intro h
    refine Subgroup.zpowers_le.2 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_left (show Commute b a from h.symm) n)).eq

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_mem_normalizer_zpowers {w x : G} [Finite G] (hx5 : x ^ 5 = 1)
    (h : w * x * w⁻¹ = x ∨ w * x * w⁻¹ = x ^ 4) :
    w ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  refine CFSG.ASVolI.RuChoice.mem_normalizer fun y hy => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← conj_zpow]
  rcases h with h | h
  · rw [h]; exact Subgroup.zpow_mem_zpowers _ _
  · rw [h, ← zpow_natCast, ← zpow_mul]; exact Subgroup.zpow_mem_zpowers _ _

end Five

section CfgSec

variable {G : Type} [Group G] {t : ℕ → G} {z y u i1 i2 r s : G}

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_lab_cases (z u : G) (k : ℕ) :
    (labG z u k = z ∧ labG z u (k + 1) = u ∧ labG z u (k + 2) = u * z) ∨
    (labG z u k = u ∧ labG z u (k + 1) = u * z ∧ labG z u (k + 2) = z) ∨
    (labG z u k = u * z ∧ labG z u (k + 1) = z ∧ labG z u (k + 2) = u) := by
  unfold labG
  have h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h with h | h | h
  · left
    have h1 : (k + 1) % 3 = 1 := by omega
    have h2 : (k + 2) % 3 = 2 := by omega
    simp [h, h1, h2]
  · right; left
    have h1 : (k + 1) % 3 = 2 := by omega
    have h2 : (k + 2) % 3 = 0 := by omega
    simp [h, h1, h2]
  · right; right
    have h1 : (k + 1) % 3 = 0 := by omega
    have h2 : (k + 2) % 3 = 1 := by omega
    simp [h, h1, h2]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_lab_sq (hC : Cfg t z y u i1 i2 r s) (k : ℕ) :
    labG z u k * labG z u k = 1 := by
  rcases burnsideJ49B_lab_cases z u k with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
  · rw [h]; exact hC.z_sq
  · rw [h]; exact hC.u_sq
  · rw [h]
    calc u * z * (u * z) = u * (z * u) * z := by group
      _ = u * (u * z) * z := by rw [hC.comm]
      _ = (u * u) * (z * z) := by group
      _ = 1 := by rw [hC.u_sq, hC.z_sq]; group

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_lab_inv (hC : Cfg t z y u i1 i2 r s) (k : ℕ) :
    (labG z u k)⁻¹ = labG z u k := inv_eq_of_mul_eq_one_right (burnsideJ49B_lab_sq hC k)

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_lab_three (z u : G) (j k : ℕ) :
    labG z u j = labG z u k ∨ labG z u j = labG z u (k + 1) ∨ labG z u j = labG z u (k + 2) := by
  unfold labG
  have hj : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hj with hj | hj | hj <;> rcases hk with hk | hk | hk <;>
    simp [hj, hk, show (k + 1) % 3 = (k % 3 + 1) % 3 by omega,
      show (k + 2) % 3 = (k % 3 + 2) % 3 by omega]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_lab_normalizes [Finite G] (hC : Cfg t z y u i1 i2 r s) {k : ℕ} (hk : k < 12)
    (j : ℕ) : labG z u j ∈ Subgroup.normalizer (Subgroup.zpowers (t k) : Set G) := by
  rcases burnsideJ49B_lab_three z u j k with h | h | h
  · rw [h]
    refine burnsideJ49B_mem_normalizer_zpowers (hC.x_pow k hk) (Or.inl ?_)
    rw [hC.x_cent k hk]; group
  · rw [h]
    refine burnsideJ49B_mem_normalizer_zpowers (hC.x_pow k hk) (Or.inr ?_)
    rw [burnsideJ49B_lab_inv hC, hC.x_inv1 k hk]
  · rw [h]
    refine burnsideJ49B_mem_normalizer_zpowers (hC.x_pow k hk) (Or.inr ?_)
    rw [burnsideJ49B_lab_inv hC, hC.x_inv2 k hk]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_z_eq_lab (z u : G) : z = labG z u 0 := by simp [labG]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_u_eq_lab (z u : G) : u = labG z u 1 := by simp [labG]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_X_mem [Finite G] (hC : Cfg t z y u i1 i2 r s) {k : ℕ} (hk : k < 12) :
    Subgroup.zpowers (t k) ∈ EInv5Ru z u := by
  refine ⟨burnsideJ49B_card_zpowers_five (hC.x_pow k hk) (hC.x_ne k hk), ?_⟩
  refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
  · rw [burnsideJ49B_u_eq_lab z u]; exact burnsideJ49B_lab_normalizes hC hk 1
  · rw [burnsideJ49B_z_eq_lab z u]; exact burnsideJ49B_lab_normalizes hC hk 0

end CfgSec

section Gen

variable {G : Type} [Group G] {t : ℕ → G} {z y u i1 i2 r s : G}

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_isConj_lab (hzu : IsConj z u) (hzuz : IsConj z (u * z)) (j : ℕ) :
    IsConj z (labG z u j) := by
  rcases burnsideJ49B_lab_cases z u j with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
  · rw [h]
  · rw [h]; exact hzu
  · rw [h]; exact hzuz

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_comm_zpowers {w x : G} (h : w * x = x * w) {y : G}
    (hy : y ∈ Subgroup.zpowers x) : w * y = y * w := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact (Commute.zpow_right (show Commute w x from h) n).eq

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_inv_zpowers {w x : G} (h : w * x * w⁻¹ = x⁻¹) {y : G}
    (hy : y ∈ Subgroup.zpowers x) : w * y * w⁻¹ = y⁻¹ := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← conj_zpow, h, inv_zpow]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_gen [Finite G] (hC : Cfg t z y u i1 i2 r s)
    (hLS : ∀ (c : G) (Bc : Subgroup G), IsConj z c → Nat.card Bc = 5 →
      Bc ≤ Subgroup.centralizer ({c} : Set G) → burnsideJ48_LS z c Bc)
    (hzu : IsConj z u) (hzuz : IsConj z (u * z)) {k j : ℕ} (hk : k < 12) (hj : j < 12)
    (hadj : t j * t k = t k * t j) (hinv : labG z u j * t k * labG z u j = t k ^ 4) :
    PFstar (Subgroup.zpowers (t k)) ⊓ Subgroup.centralizer ({labG z u j} : Set G) =
        Subgroup.zpowers (t j) ∧
      O5N (Subgroup.zpowers (t k)) ⊓ Subgroup.centralizer ({labG z u j} : Set G) =
        Subgroup.zpowers (t j) := by
  have hX : Nat.card (Subgroup.zpowers (t k)) = 5 :=
    burnsideJ49B_card_zpowers_five (hC.x_pow k hk) (hC.x_ne k hk)
  have hXc : Subgroup.zpowers (t k) ≤ Subgroup.centralizer ({labG z u k} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (burnsideJ49B_comm_zpowers (hC.x_cent k hk) hx).symm
  have LSX := hLS (labG z u k) (Subgroup.zpowers (t k)) (burnsideJ49B_isConj_lab hzu hzuz k) hX hXc
  have hi2 := burnsideJ49B_lab_sq hC j
  have hinv' : labG z u j * t k * (labG z u j)⁻¹ = (t k)⁻¹ := by
    rw [burnsideJ49B_lab_inv hC, hinv]
    have h5 := hC.x_pow k hk
    calc t k ^ 4 = t k ^ 4 * (t k * (t k)⁻¹) := by group
      _ = t k ^ 5 * (t k)⁻¹ := by group
      _ = (t k)⁻¹ := by rw [h5]; group
  have hiinv : ∀ x ∈ Subgroup.zpowers (t k), labG z u j * x * (labG z u j)⁻¹ = x⁻¹ :=
    fun x hx => burnsideJ49B_inv_zpowers hinv' hx
  have hcard := LSX.card_cent (labG z u j) (burnsideJ49B_isConj_lab hzu hzuz j) hi2 hiinv
  have hmemP : t j ∈ PFstar (Subgroup.zpowers (t k)) := by
    refine LSX.mem_P (t j) (fun y hy => ?_) (hC.x_pow j hj)
    exact (burnsideJ49B_comm_zpowers hadj hy)
  have hmemC : t j ∈ Subgroup.centralizer ({labG z u j} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hC.x_cent j hj).symm
  have hle : Subgroup.zpowers (t j) ≤
      PFstar (Subgroup.zpowers (t k)) ⊓ Subgroup.centralizer ({labG z u j} : Set G) :=
    Subgroup.zpowers_le.2 ⟨hmemP, hmemC⟩
  have hEq : PFstar (Subgroup.zpowers (t k)) ⊓ Subgroup.centralizer ({labG z u j} : Set G) =
      Subgroup.zpowers (t j) := by
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hcard, burnsideJ49B_card_zpowers_five (hC.x_pow j hj) (hC.x_ne j hj)]
  refine ⟨hEq, ?_⟩
  have hO5N : O5N (Subgroup.zpowers (t k)) = PFstar (Subgroup.zpowers (t k)) := LSX.pcore
  rw [hO5N]
  exact hEq

end Gen

section Ident

variable {G : Type} [Group G] [Finite G] {t : ℕ → G} {z y u i1 i2 r s : G}

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_X_inj (hC : Cfg t z y u i1 i2 r s) {k j : ℕ} (hk : k < 12) (hj : j < 12)
    (h : Subgroup.zpowers (t k) = Subgroup.zpowers (t j)) : k = j := by
  have key : ∀ i j : ℕ, i < 12 → j < 12 → i < j →
      Subgroup.zpowers (t i) = Subgroup.zpowers (t j) → False := by
    intro i j hi hj hij he
    have hmem : t j ∈ Subgroup.zpowers (t i) := he ▸ Subgroup.mem_zpowers _
    obtain ⟨n, hn⟩ := CFSG.Quasithin.RuType.exists_pow_of_mem_zpowers hmem
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have ho : orderOf (t i) = 5 := orderOf_eq_prime (hC.x_pow i hi) (hC.x_ne i hi)
    have hn' : t i ^ (n % 5) = t j := by
      rw [← hn, ← ho, pow_mod_orderOf]
    have hm : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
    rcases hm with hm | hm | hm | hm | hm
    · rw [hm, pow_zero] at hn'
      exact hC.x_ne j hj hn'.symm
    · exact hC.x_dist i hi j hj hij 0 (by norm_num) (by rw [hm] at hn'; simpa using hn'.symm)
    · exact hC.x_dist i hi j hj hij 1 (by norm_num) (by rw [hm] at hn'; simpa using hn'.symm)
    · exact hC.x_dist i hi j hj hij 2 (by norm_num) (by rw [hm] at hn'; simpa using hn'.symm)
    · exact hC.x_dist i hi j hj hij 3 (by norm_num) (by rw [hm] at hn'; simpa using hn'.symm)
  rcases lt_trichotomy k j with hlt | heq | hgt
  · exact (key k j hk hj hlt h).elim
  · exact heq
  · exact (key j k hj hk hgt h.symm).elim

variable (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)
  (hLS : ∀ (c : G) (Bc : Subgroup G), IsConj z c → Nat.card Bc = 5 →
    Bc ≤ Subgroup.centralizer ({c} : Set G) → burnsideJ48_LS z c Bc)
  (hzu : IsConj z u) (hzuz : IsConj z (u * z))
include hC hLS hzu hzuz

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_BvRu_u {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0)) :
    BvRu B5 u = Subgroup.zpowers (t 1) := by
  have := (burnsideJ49B_gen hC hLS hzu hzuz (k := 0) (j := 1) (by norm_num) (by norm_num)
    (by have := hC.x_adj 0 (by norm_num); simpa using this.symm)
    (by have := hC.x_inv1 0 (by norm_num); simpa using this)).1
  rw [← burnsideJ49B_u_eq_lab] at this
  rw [hB5]
  exact this

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_BvRu_uz {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0)) :
    BvRu B5 (u * z) = Subgroup.zpowers (t 11) := by
  have h := (burnsideJ49B_gen hC hLS hzu hzuz (k := 0) (j := 11) (by norm_num) (by norm_num)
    (by have := hC.x_adj 11 (by norm_num); simpa using this)
    (by have := hC.x_inv2 0 (by norm_num)
        have e : labG z u 11 = labG z u (0 + 2) := by simp [labG]
        rw [e]; exact this)).1
  have e : labG z u 11 = u * z := by simp [labG]
  rw [e] at h
  rw [hB5]
  exact h

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_BuzPRu {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0)) :
    BuzPRu B5 z u = Subgroup.zpowers (t 2) := by
  unfold BuzPRu
  rw [burnsideJ49B_BvRu_u hC hLS hzu hzuz hB5]
  have h := (burnsideJ49B_gen hC hLS hzu hzuz (k := 1) (j := 2) (by norm_num) (by norm_num)
    (by have := hC.x_adj 1 (by norm_num); simpa using this.symm)
    (by have := hC.x_inv1 1 (by norm_num); simpa using this)).2
  have e : labG z u 2 = u * z := by simp [labG]
  rw [e] at h
  exact h

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_BuPRu {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0)) :
    BuPRu B5 z u = Subgroup.zpowers (t 10) := by
  unfold BuPRu
  rw [burnsideJ49B_BvRu_uz hC hLS hzu hzuz hB5, inf_comm]
  have h := (burnsideJ49B_gen hC hLS hzu hzuz (k := 11) (j := 10) (by norm_num) (by norm_num)
    (by have := hC.x_adj 10 (by norm_num); simpa using this)
    (by have := hC.x_inv2 11 (by norm_num)
        have e : labG z u 10 = labG z u (11 + 2) := by simp [labG]
        rw [e]; exact this)).2
  have e : labG z u 10 = u := by simp [labG]
  rw [e] at h
  exact h

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_BzPRu {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0)) :
    BzPRu B5 z u = Subgroup.zpowers (t 9) := by
  unfold BzPRu
  rw [burnsideJ49B_BuPRu hC hLS hzu hzuz hB5]
  have h := (burnsideJ49B_gen hC hLS hzu hzuz (k := 10) (j := 9) (by norm_num) (by norm_num)
    (by have := hC.x_adj 9 (by norm_num); simpa using this)
    (by have := hC.x_inv2 10 (by norm_num)
        have e : labG z u 9 = labG z u (10 + 2) := by simp [labG]
        rw [e]; exact this)).2
  have e : labG z u 9 = z := by simp [labG]
  rw [e] at h
  exact h

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_B5uz {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0)) :
    O5N (BuzPRu B5 z u) ⊓ Subgroup.centralizer ({z} : Set G) = Subgroup.zpowers (t 3) := by
  rw [burnsideJ49B_BuzPRu hC hLS hzu hzuz hB5]
  have h := (burnsideJ49B_gen hC hLS hzu hzuz (k := 2) (j := 3) (by norm_num) (by norm_num)
    (by have := hC.x_adj 2 (by norm_num); simpa using this.symm)
    (by have := hC.x_inv1 2 (by norm_num); simpa using this)).2
  have e : labG z u 3 = z := by simp [labG]
  rw [e] at h
  exact h

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_Bset {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0)) :
    BsetRu B5 z u = {Subgroup.zpowers (t 0), Subgroup.zpowers (t 1), Subgroup.zpowers (t 11),
      Subgroup.zpowers (t 9), Subgroup.zpowers (t 10), Subgroup.zpowers (t 2)} := by
  unfold BsetRu
  rw [burnsideJ49B_BvRu_u hC hLS hzu hzuz hB5, burnsideJ49B_BvRu_uz hC hLS hzu hzuz hB5,
    burnsideJ49B_BzPRu hC hLS hzu hzuz hB5, burnsideJ49B_BuPRu hC hLS hzu hzuz hB5,
    burnsideJ49B_BuzPRu hC hLS hzu hzuz hB5, hB5]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_B5u_ne {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0)) :
    BzPRu B5 z u ≠ O5N (BuzPRu B5 z u) ⊓ Subgroup.centralizer ({z} : Set G) := by
  rw [burnsideJ49B_BzPRu hC hLS hzu hzuz hB5, burnsideJ49B_B5uz hC hLS hzu hzuz hB5]
  intro h
  have := burnsideJ49B_X_inj hC (by norm_num) (by norm_num) h
  omega

end Ident

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
@[expose] def burnsideJ49B_Nbr {G : Type} [Group G] (z u : G) : Prop :=
  ∀ Y Y' : Subgroup G, Y ∈ EInv5Ru z u → Y' ∈ EInv5Ru z u → Y ≠ Y' → ⁅Y, Y'⁆ = ⊥ →
    ∃ w ∈ ({z, u, u * z} : Set G), (∃ y ∈ Y, w * y ≠ y * w) ∧
      Y' = O5N Y ⊓ Subgroup.centralizer ({w} : Set G)

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_fin12_adj_of (i j : Fin 12)
    (h : j.val = (i.val + 1) % 12 ∨ j.val = (i.val + 11) % 12) : i - j = 1 ∨ j - i = 1 := by
  revert i j
  decide

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_fin12_adj_to (i j : Fin 12) (h : i - j = 1 ∨ j - i = 1) :
    j.val = (i.val + 1) % 12 ∨ i.val = (j.val + 1) % 12 := by
  revert i j
  decide

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_fin12_ne (i j : Fin 12) (h : i - j = 1 ∨ j - i = 1) : i ≠ j := by
  revert i j
  decide

section Basic

variable {G : Type} [Group G] [Finite G] {t : ℕ → G} {z y u i1 i2 r s : G}

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
omit [Finite G] in
theorem burnsideJ49B_commGraphOn_adj {S : Set (Subgroup G)} {a b : ↥S} :
    (commGraphOn S).Adj a b ↔ a ≠ b ∧ ⁅(a : Subgroup G), (b : Subgroup G)⁆ = ⊥ := by
  unfold commGraphOn
  rw [SimpleGraph.fromRel_adj]
  refine and_congr_right fun _ => ?_
  rw [Subgroup.commutator_comm (b : Subgroup G) (a : Subgroup G)]
  exact or_self_iff

variable (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)
include hC

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_adj_succ {k : ℕ} (hk : k + 1 < 12) :
    (commGraphOn (EInv5Ru z u)).Adj
      ⟨Subgroup.zpowers (t k), burnsideJ49B_X_mem hC (by omega)⟩
      ⟨Subgroup.zpowers (t (k + 1)), burnsideJ49B_X_mem hC hk⟩ := by
  rw [burnsideJ49B_commGraphOn_adj]
  refine ⟨?_, ?_⟩
  · intro h
    have := burnsideJ49B_X_inj hC (by omega) hk (congrArg Subtype.val h)
    omega
  · show ⁅Subgroup.zpowers (t k), Subgroup.zpowers (t (k + 1))⁆ = ⊥
    rw [burnsideJ49B_comm_zpowers_iff]
    have := hC.x_adj k (by omega)
    have e : (k + 1) % 12 = k + 1 := Nat.mod_eq_of_lt hk
    rwa [e] at this

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_reach : ∀ (k : ℕ) (hk : k < 12),
    (commGraphOn (EInv5Ru z u)).Reachable
      ⟨Subgroup.zpowers (t 0), burnsideJ49B_X_mem hC (by norm_num)⟩
      ⟨Subgroup.zpowers (t k), burnsideJ49B_X_mem hC hk⟩
  | 0, _ => SimpleGraph.Reachable.refl _
  | k + 1, hk => (burnsideJ49B_reach k (by omega)).trans
      (burnsideJ49B_adj_succ hC hk).reachable

end Basic

section Cycle

variable {G : Type} [Group G] [Finite G] {t : ℕ → G} {z y u i1 i2 r s : G}
  (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)
  (hLS : ∀ (c : G) (Bc : Subgroup G), IsConj z c → Nat.card Bc = 5 →
    Bc ≤ Subgroup.centralizer ({c} : Set G) → burnsideJ48_LS z c Bc)
  (hzu : IsConj z u) (hzuz : IsConj z (u * z)) (hnbr : burnsideJ49B_Nbr z u)
include hC hLS hzu hzuz hnbr

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_nbrs {k : ℕ} (hk : k < 12) {Y : Subgroup G} (hY : Y ∈ EInv5Ru z u)
    (hne : Y ≠ Subgroup.zpowers (t k)) (hc : ⁅Subgroup.zpowers (t k), Y⁆ = ⊥) :
    Y = Subgroup.zpowers (t ((k + 1) % 12)) ∨ Y = Subgroup.zpowers (t ((k + 11) % 12)) := by
  obtain ⟨w, hw, ⟨y0, hy0, hwy⟩, hYeq⟩ := hnbr _ Y (burnsideJ49B_X_mem hC hk) hY hne.symm hc
  have hwl : ∃ j, w = labG z u j := by
    rcases hw with rfl | rfl | rfl
    · exact ⟨0, by simp [labG]⟩
    · exact ⟨1, by simp [labG]⟩
    · exact ⟨2, by simp [labG]⟩
  obtain ⟨j, rfl⟩ := hwl
  rcases burnsideJ49B_lab_three z u j k with h | h | h
  · exfalso
    rw [h] at hwy
    exact hwy (burnsideJ49B_comm_zpowers (hC.x_cent k hk) hy0)
  · left
    have hj : (k + 1) % 12 < 12 := Nat.mod_lt _ (by norm_num)
    have hlab : labG z u ((k + 1) % 12) = labG z u (k + 1) := by
      unfold labG
      have : ((k + 1) % 12) % 3 = (k + 1) % 3 := by omega
      rw [this]
    have hgen := (burnsideJ49B_gen hC hLS hzu hzuz hk hj
      (by have := hC.x_adj k hk; exact this.symm)
      (by rw [hlab]; exact hC.x_inv1 k hk)).2
    rw [hYeq, h, ← hlab]
    exact hgen
  · right
    have hj : (k + 11) % 12 < 12 := Nat.mod_lt _ (by norm_num)
    have hlab : labG z u ((k + 11) % 12) = labG z u (k + 2) := by
      unfold labG
      have : ((k + 11) % 12) % 3 = (k + 2) % 3 := by omega
      rw [this]
    have hnext : ((k + 11) % 12 + 1) % 12 = k := by omega
    have hgen := (burnsideJ49B_gen hC hLS hzu hzuz hk hj
      (by have := hC.x_adj ((k + 11) % 12) hj; rw [hnext] at this; exact this)
      (by rw [hlab]; exact hC.x_inv2 k hk)).2
    rw [hYeq, h, ← hlab]
    exact hgen

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_cgon_eq {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0)) :
    CgonRu B5 z u = {Y | ∃ k < 12, Y = Subgroup.zpowers (t k)} := by
  ext Y
  constructor
  · rintro ⟨hB, hY, hreach⟩
    have hwalk : ∀ (a b : ↥(EInv5Ru z u)) (p : (commGraphOn (EInv5Ru z u)).Walk a b),
        (∃ k < 12, (a : Subgroup G) = Subgroup.zpowers (t k)) →
        (∃ k < 12, (b : Subgroup G) = Subgroup.zpowers (t k)) := by
      intro a b p
      induction p with
      | nil => exact id
      | cons h p ih =>
        rename_i a a' b
        intro ha
        refine ih ?_
        obtain ⟨k, hk, hak⟩ := ha
        rw [burnsideJ49B_commGraphOn_adj] at h
        obtain ⟨hne, hc⟩ := h
        have hne' : (a' : Subgroup G) ≠ Subgroup.zpowers (t k) := by
          intro h2
          exact hne (Subtype.ext (hak.trans h2.symm))
        have hc' : ⁅Subgroup.zpowers (t k), (a' : Subgroup G)⁆ = ⊥ := by rw [← hak]; exact hc
        rcases burnsideJ49B_nbrs hC hLS hzu hzuz hnbr hk a'.2 hne' hc' with h | h
        · exact ⟨(k + 1) % 12, Nat.mod_lt _ (by norm_num), h⟩
        · exact ⟨(k + 11) % 12, Nat.mod_lt _ (by norm_num), h⟩
    obtain ⟨p⟩ := hreach
    exact hwalk _ _ p ⟨0, by norm_num, hB5⟩
  · rintro ⟨k, hk, rfl⟩
    have hB : B5 ∈ EInv5Ru z u := hB5 ▸ burnsideJ49B_X_mem hC (by norm_num)
    refine ⟨hB, burnsideJ49B_X_mem hC hk, ?_⟩
    have := burnsideJ49B_reach hC k hk
    have e : (⟨B5, hB⟩ : ↥(EInv5Ru z u)) =
        ⟨Subgroup.zpowers (t 0), burnsideJ49B_X_mem hC (by norm_num)⟩ := Subtype.ext hB5
    rw [e]
    exact this

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_iso {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0)) :
    ∃ φ : commGraphOn (CgonRu B5 z u) ≃g SimpleGraph.cycleGraph 12,
      ∀ (k : ℕ) (hk : k < 12) (hmem : Subgroup.zpowers (t k) ∈ CgonRu B5 z u),
        φ ⟨Subgroup.zpowers (t k), hmem⟩ = ⟨k, hk⟩ := by
  have hmem : ∀ i : Fin 12, Subgroup.zpowers (t i.val) ∈ CgonRu B5 z u := fun i => by
    rw [burnsideJ49B_cgon_eq hC hLS hzu hzuz hnbr hB5]
    exact ⟨i.val, i.2, rfl⟩
  let f : Fin 12 → ↥(CgonRu B5 z u) := fun i => ⟨Subgroup.zpowers (t i.val), hmem i⟩
  have hinj : Function.Injective f := by
    intro i j h
    have := burnsideJ49B_X_inj hC i.2 j.2 (congrArg Subtype.val h)
    exact Fin.ext this
  have hsurj : Function.Surjective f := by
    rintro ⟨Y, hY⟩
    rw [burnsideJ49B_cgon_eq hC hLS hzu hzuz hnbr hB5] at hY
    obtain ⟨k, hk, rfl⟩ := hY
    exact ⟨⟨k, hk⟩, rfl⟩
  have hadjf : ∀ i j : Fin 12, (commGraphOn (CgonRu B5 z u)).Adj (f i) (f j) ↔
      (SimpleGraph.cycleGraph 12).Adj i j := by
    intro i j
    rw [burnsideJ49B_commGraphOn_adj, SimpleGraph.cycleGraph_adj]
    constructor
    · rintro ⟨hne, hc⟩
      have hne' : Subgroup.zpowers (t j.val) ≠ Subgroup.zpowers (t i.val) := by
        intro h
        exact hne (Subtype.ext h.symm)
      rcases burnsideJ49B_nbrs hC hLS hzu hzuz hnbr i.2 (burnsideJ49B_X_mem hC j.2) hne' hc with h | h
      · have := burnsideJ49B_X_inj hC j.2 (Nat.mod_lt _ (by norm_num)) h
        exact burnsideJ49B_fin12_adj_of i j (Or.inl this)
      · have := burnsideJ49B_X_inj hC j.2 (Nat.mod_lt _ (by norm_num)) h
        exact burnsideJ49B_fin12_adj_of i j (Or.inr this)
    · intro h
      refine ⟨fun e => burnsideJ49B_fin12_ne i j h (hinj e), ?_⟩
      show ⁅Subgroup.zpowers (t i.val), Subgroup.zpowers (t j.val)⁆ = ⊥
      rw [burnsideJ49B_comm_zpowers_iff]
      rcases burnsideJ49B_fin12_adj_to i j h with h1 | h1
      · have := hC.x_adj i.val i.2
        rwa [← h1] at this
      · have := (hC.x_adj j.val j.2).symm
        rwa [← h1] at this
  let e : Fin 12 ≃ ↥(CgonRu B5 z u) := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨⟨e.symm, ?_⟩, ?_⟩
  · intro a b
    obtain ⟨i, rfl⟩ := e.surjective a
    obtain ⟨j, rfl⟩ := e.surjective b
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact (hadjf i j).symm
  · intro k hk hmem
    show e.symm ⟨Subgroup.zpowers (t k), hmem⟩ = ⟨k, hk⟩
    rw [Equiv.symm_apply_eq]
    rfl

end Cycle

section Walks

variable {V : Type*} {Γ : SimpleGraph V}

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_walk2 {a b : V} (p : Γ.Walk a b) (hp : p.length = 2) :
    ∃ m, Γ.Adj a m ∧ Γ.Adj m b := by
  cases p with
  | nil => simp at hp
  | cons h p' =>
    cases p' with
    | nil => simp at hp
    | cons h' p'' =>
      cases p'' with
      | nil => exact ⟨_, h, h'⟩
      | cons h'' p''' => simp at hp

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_walk3 {a b : V} (p : Γ.Walk a b) (hp : p.length = 3) :
    ∃ m₁ m₂, Γ.Adj a m₁ ∧ Γ.Adj m₁ m₂ ∧ Γ.Adj m₂ b := by
  cases p with
  | nil => simp at hp
  | cons h p' =>
    cases p' with
    | nil => simp at hp
    | cons h' p'' =>
      cases p'' with
      | nil => simp at hp
      | cons h'' p''' =>
        cases p''' with
        | nil => exact ⟨_, _, h, h', h''⟩
        | cons h''' p'''' => simp at hp

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_dist_le_one {a b : V} (h : Γ.Adj a b) : Γ.dist a b ≤ 1 :=
  SimpleGraph.dist_le (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)

end Walks

section PTwo

variable {G : Type} [Group G]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_isPOnePlusTwo {N : Subgroup G} (hcard : Nat.card N = 125)
    (hexp : ∀ x ∈ N, x ^ 5 = 1) (hnab : ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a) :
    IsPOnePlusTwoGroup 5 ↥N := by
  refine ⟨by rw [hcard]; norm_num, ?_, ?_⟩
  · have hd : Monoid.exponent ↥N ∣ 5 := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      have := hexp x.1 x.2
      exact Subtype.ext (by simpa using this)
    rcases (Nat.dvd_prime Nat.prime_five).1 hd with h1 | h5
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hnab
      have hsub : Subsingleton ↥N := Monoid.exp_eq_one_iff.1 h1
      have := Subsingleton.elim ((⟨a, ha⟩ : ↥N) * ⟨b, hb⟩) (⟨b, hb⟩ * ⟨a, ha⟩)
      exact hab (congrArg Subtype.val this)
    · exact h5
  · obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩

end PTwo

section Dist

variable {G : Type} [Group G] [Finite G]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_comm_card_five {X : Subgroup G} (h : Nat.card X = 5) :
    ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  obtain ⟨x, -, -, -, hx⟩ := CFSG.Quasithin.RuType.exists_gen_of_card_five h
  intro a ha b hb
  obtain ⟨m, rfl⟩ := hx a ha
  obtain ⟨n, rfl⟩ := hx b hb
  exact ((Commute.refl x).pow_pow m n).eq

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_card_125 {N P : Subgroup G} (hNP : N ≤ P) (hP : Nat.card P = 125)
    (h5 : 5 ∣ Nat.card N) (hnab : ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a) : Nat.card N = 125 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hdvd : Nat.card N ∣ 5 ^ 3 := by
    have := Subgroup.card_dvd_of_le hNP
    rw [hP] at this
    simpa using this
  obtain ⟨j, hj, hjN⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hdvd
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  interval_cases j
  · rw [hjN] at h5; norm_num at h5
  · exfalso
    have hN5 : Nat.card N = 5 := by rw [hjN]; norm_num
    exact hab (burnsideJ49B_comm_card_five hN5 a ha b hb)
  · exfalso
    haveI : IsPGroup 5 N := IsPGroup.of_card (n := 2) hjN
    have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) hjN
    exact hab (congrArg Subtype.val (this.is_comm.comm (⟨a, ha⟩ : ↥N) ⟨b, hb⟩))
  · rw [hjN]; norm_num

end Dist

section Dist2

variable {G : Type} [Group G] [Finite G] {t : ℕ → G} {z y u i1 i2 r s : G}
  (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)
  (hLS : ∀ (c : G) (Bc : Subgroup G), IsConj z c → Nat.card Bc = 5 →
    Bc ≤ Subgroup.centralizer ({c} : Set G) → burnsideJ48_LS z c Bc)
  (hzu : IsConj z u) (hzuz : IsConj z (u * z))
include hC hLS hzu hzuz

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_LS_at {k : ℕ} (hk : k < 12) :
    burnsideJ48_LS z (labG z u k) (Subgroup.zpowers (t k)) := by
  refine hLS (labG z u k) _ (burnsideJ49B_isConj_lab hzu hzuz k)
    (burnsideJ49B_card_zpowers_five (hC.x_pow k hk) (hC.x_ne k hk)) ?_
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (burnsideJ49B_comm_zpowers (hC.x_cent k hk) hx).symm

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_sq_P {m : ℕ} (hm : m < 12) :
    IsPOnePlusTwoGroup 5 ↥(Subgroup.zpowers (t ((m + 1) % 12)) ⊔
      Subgroup.zpowers (t ((m + 11) % 12))) := by
  have LS := burnsideJ49B_LS_at hC hLS hzu hzuz hm
  have hj1 : (m + 1) % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hj2 : (m + 11) % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hmemP : ∀ j : ℕ, j < 12 → (t j * t m = t m * t j) → t j ∈ PFstar (Subgroup.zpowers (t m)) :=
    fun j hj hjm => LS.mem_P (t j) (fun y hy => burnsideJ49B_comm_zpowers hjm hy) (hC.x_pow j hj)
  have hadj1 : t ((m + 1) % 12) * t m = t m * t ((m + 1) % 12) :=
    (hC.x_adj m hm).symm
  have hadj2 : t ((m + 11) % 12) * t m = t m * t ((m + 11) % 12) := by
    have := hC.x_adj ((m + 11) % 12) hj2
    have hnext : ((m + 11) % 12 + 1) % 12 = m := by omega
    rw [hnext] at this
    exact this
  have hle : Subgroup.zpowers (t ((m + 1) % 12)) ⊔ Subgroup.zpowers (t ((m + 11) % 12)) ≤
      PFstar (Subgroup.zpowers (t m)) :=
    sup_le (Subgroup.zpowers_le.2 (hmemP _ hj1 hadj1)) (Subgroup.zpowers_le.2 (hmemP _ hj2 hadj2))
  have h5 : 5 ∣ Nat.card ↥(Subgroup.zpowers (t ((m + 1) % 12)) ⊔
      Subgroup.zpowers (t ((m + 11) % 12))) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Subgroup.zpowers (t ((m + 1) % 12)) ≤
      Subgroup.zpowers (t ((m + 1) % 12)) ⊔ Subgroup.zpowers (t ((m + 11) % 12)))
    rwa [burnsideJ49B_card_zpowers_five (hC.x_pow _ hj1) (hC.x_ne _ hj1)] at this
  have hnab : ∃ a ∈ Subgroup.zpowers (t ((m + 1) % 12)) ⊔ Subgroup.zpowers (t ((m + 11) % 12)),
      ∃ b ∈ Subgroup.zpowers (t ((m + 1) % 12)) ⊔ Subgroup.zpowers (t ((m + 11) % 12)),
        a * b ≠ b * a := by
    refine ⟨t ((m + 11) % 12), Subgroup.mem_sup_right (Subgroup.mem_zpowers _),
      t ((m + 1) % 12), Subgroup.mem_sup_left (Subgroup.mem_zpowers _), ?_⟩
    have := hC.x_nadj ((m + 11) % 12) hj2
    have e : ((m + 11) % 12 + 2) % 12 = (m + 1) % 12 := by omega
    rwa [e] at this
  have hcard := burnsideJ49B_card_125 hle LS.card_P h5 hnab
  exact burnsideJ49B_isPOnePlusTwo hcard (fun x hx => LS.exp x (hle hx)) hnab

end Dist2

section Distances

variable {G : Type} [Group G] [Finite G] {t : ℕ → G} {z y u i1 i2 r s : G}
  (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)
  (hLS : ∀ (c : G) (Bc : Subgroup G), IsConj z c → Nat.card Bc = 5 →
    Bc ≤ Subgroup.centralizer ({c} : Set G) → burnsideJ48_LS z c Bc)
  (hzu : IsConj z u) (hzuz : IsConj z (u * z)) (hnbr : burnsideJ49B_Nbr z u)
  {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0))
include hC hLS hzu hzuz hnbr hB5

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_cgon_X {Y : Subgroup G} (hY : Y ∈ CgonRu B5 z u) : Y ∈ EInv5Ru z u := by
  obtain ⟨-, hX, -⟩ := hY
  exact hX

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_dist2 (B1 B2 : ↥(CgonRu B5 z u))
    (hd : (commGraphOn (CgonRu B5 z u)).dist B1 B2 = 2) :
    IsPOnePlusTwoGroup 5 ↥((B1 : Subgroup G) ⊔ (B2 : Subgroup G)) := by
  have hreach : (commGraphOn (CgonRu B5 z u)).Reachable B1 B2 := by
    by_contra h
    have := SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.2 (Or.inr h)
    omega
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  obtain ⟨M, h1, h2⟩ := burnsideJ49B_walk2 p (by rw [hp, hd])
  rw [burnsideJ49B_commGraphOn_adj] at h1 h2
  have hM := (Set.ext_iff.1 (burnsideJ49B_cgon_eq hC hLS hzu hzuz hnbr hB5) M.1).1 M.2
  obtain ⟨m, hm, hMeq⟩ := hM
  have hne12 : B1 ≠ B2 := by
    intro h
    subst h
    simp at hd
  have n1 : (B1 : Subgroup G) = Subgroup.zpowers (t ((m + 1) % 12)) ∨
      (B1 : Subgroup G) = Subgroup.zpowers (t ((m + 11) % 12)) := by
    refine burnsideJ49B_nbrs hC hLS hzu hzuz hnbr hm (burnsideJ49B_cgon_X hC hLS hzu hzuz hnbr hB5 B1.2) ?_ ?_
    · intro h
      exact h1.1 (Subtype.ext (h.trans hMeq.symm))
    · rw [← hMeq, Subgroup.commutator_comm]
      exact h1.2
  have n2 : (B2 : Subgroup G) = Subgroup.zpowers (t ((m + 1) % 12)) ∨
      (B2 : Subgroup G) = Subgroup.zpowers (t ((m + 11) % 12)) := by
    refine burnsideJ49B_nbrs hC hLS hzu hzuz hnbr hm (burnsideJ49B_cgon_X hC hLS hzu hzuz hnbr hB5 B2.2) ?_ ?_
    · intro h
      exact h2.1 (Subtype.ext (hMeq.trans h.symm))
    · rw [← hMeq]
      exact h2.2
  rcases n1 with e1 | e1 <;> rcases n2 with e2 | e2
  · exact absurd (Subtype.ext (e1.trans e2.symm)) hne12
  · rw [e1, e2]
    exact burnsideJ49B_sq_P hC hLS hzu hzuz hm
  · rw [e1, e2, sup_comm]
    exact burnsideJ49B_sq_P hC hLS hzu hzuz hm
  · exact absurd (Subtype.ext (e1.trans e2.symm)) hne12

end Distances

section IPart

variable {G : Type} [Group G] {t : ℕ → G} {z y u i1 i2 r s : G} (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)
include hC

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_I_mem {x : G} (hx : x ∈ Subgroup.closure ({i1, i2} : Set G)) :
    ∃ p < 4, ∃ q < 4, x = i1 ^ p * i2 ^ q := by
  have hc : Commute i1 i2 := hC.i_comm
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with h | h
    · exact ⟨1, by norm_num, 0, by norm_num, by simp [h]⟩
    · rw [Set.mem_singleton_iff] at h
      exact ⟨0, by norm_num, 1, by norm_num, by simp [h]⟩
  | one => exact ⟨0, by norm_num, 0, by norm_num, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨p, hp, q, hq, rfl⟩ := ha
    obtain ⟨p', hp', q', hq', rfl⟩ := hb
    refine ⟨(p + p') % 4, Nat.mod_lt _ (by norm_num), (q + q') % 4, Nat.mod_lt _ (by norm_num), ?_⟩
    calc i1 ^ p * i2 ^ q * (i1 ^ p' * i2 ^ q') = i1 ^ p * (i2 ^ q * i1 ^ p') * i2 ^ q' := by group
      _ = i1 ^ p * (i1 ^ p' * i2 ^ q) * i2 ^ q' := by rw [(Commute.pow_pow hc.symm q p').eq]
      _ = i1 ^ (p + p') * i2 ^ (q + q') := by rw [pow_add, pow_add]; group
      _ = i1 ^ ((p + p') % 4) * i2 ^ ((q + q') % 4) := by
        rw [← pow_eq_pow_mod (p + p') hC.i1_pow, ← pow_eq_pow_mod (q + q') hC.i2_pow]
  | inv a _ ha =>
    obtain ⟨p, hp, q, hq, rfl⟩ := ha
    refine ⟨(4 - p) % 4, Nat.mod_lt _ (by norm_num), (4 - q) % 4, Nat.mod_lt _ (by norm_num), ?_⟩
    have h1 : (i1 ^ p)⁻¹ = i1 ^ (4 - p) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add, show p + (4 - p) = 4 by omega, hC.i1_pow]
    have h2 : (i2 ^ q)⁻¹ = i2 ^ (4 - q) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add, show q + (4 - q) = 4 by omega, hC.i2_pow]
    calc (i1 ^ p * i2 ^ q)⁻¹ = (i2 ^ q)⁻¹ * (i1 ^ p)⁻¹ := mul_inv_rev _ _
      _ = i2 ^ (4 - q) * i1 ^ (4 - p) := by rw [h1, h2]
      _ = i1 ^ (4 - p) * i2 ^ (4 - q) := (Commute.pow_pow hc.symm (4 - q) (4 - p)).eq
      _ = i1 ^ ((4 - p) % 4) * i2 ^ ((4 - q) % 4) := by
        rw [← pow_eq_pow_mod (4 - p) hC.i1_pow, ← pow_eq_pow_mod (4 - q) hC.i2_pow]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_I_inv {x : G} (hx : x ∈ Subgroup.closure ({i1, i2} : Set G))
    (hsq : x * x = 1) : x = 1 ∨ x = z ∨ x = u ∨ x = u * z := by
  obtain ⟨p, hp, q, hq, rfl⟩ := burnsideJ49B_I_mem hC hx
  exact hC.i_inv p hp q hq hsq

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_I_comm {x w : G} (hx : x ∈ Subgroup.closure ({i1, i2} : Set G))
    (hw : w ∈ Subgroup.closure ({i1, i2} : Set G)) : x * w = w * x := by
  obtain ⟨p, hp, q, hq, rfl⟩ := burnsideJ49B_I_mem hC hx
  obtain ⟨p', hp', q', hq', rfl⟩ := burnsideJ49B_I_mem hC hw
  have hc : Commute i1 i2 := hC.i_comm
  calc i1 ^ p * i2 ^ q * (i1 ^ p' * i2 ^ q') = i1 ^ p * (i2 ^ q * i1 ^ p') * i2 ^ q' := by group
    _ = i1 ^ p * (i1 ^ p' * i2 ^ q) * i2 ^ q' := by rw [(Commute.pow_pow hc.symm q p').eq]
    _ = i1 ^ (p + p') * i2 ^ (q + q') := by rw [pow_add, pow_add]; group
    _ = i1 ^ (p' + p) * i2 ^ (q' + q) := by rw [add_comm p p', add_comm q q']
    _ = i1 ^ p' * (i1 ^ p * i2 ^ q') * i2 ^ q := by rw [pow_add, pow_add]; group
    _ = i1 ^ p' * (i2 ^ q' * i1 ^ p) * i2 ^ q := by rw [(Commute.pow_pow hc p q').eq]
    _ = i1 ^ p' * i2 ^ q' * (i1 ^ p * i2 ^ q) := by group

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_z_mem_I : z ∈ Subgroup.closure ({i1, i2} : Set G) := by
  obtain ⟨p, hp, q, hq, e⟩ := hC.z_mem
  rw [e]
  exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
    (pow_mem (Subgroup.subset_closure (by simp)) _)

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_u_mem_I : u ∈ Subgroup.closure ({i1, i2} : Set G) := by
  obtain ⟨p, hp, q, hq, e⟩ := hC.u_mem
  rw [e]
  exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
    (pow_mem (Subgroup.subset_closure (by simp)) _)

end IPart

section EPart

variable {G : Type} [Group G]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
open scoped Pointwise in
theorem burnsideJ49B_mem_sup_comm {S T : Subgroup G} (hST : ∀ a ∈ S, ∀ b ∈ T, a * b = b * a)
    {g : G} (hg : g ∈ S ⊔ T) : ∃ s ∈ S, ∃ t ∈ T, s * t = g := by
  have hle : S ≤ Subgroup.normalizer (T : Set G) := fun s hs => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : s * h * s⁻¹ = h := by rw [hST s hs h hh]; group
      rw [this]; exact hh
    · intro hh
      have h1 : s⁻¹ * (s * h * s⁻¹) = (s * h * s⁻¹) * s⁻¹ := hST s⁻¹ (inv_mem hs) _ hh
      have : h = s * h * s⁻¹ := by
        calc h = s⁻¹ * (s * h * s⁻¹) * s := by group
          _ = ((s * h * s⁻¹) * s⁻¹) * s := by rw [h1]
          _ = s * h * s⁻¹ := by group
      rw [this]; exact hh
  have := Subgroup.coe_mul_of_left_le_normalizer_right S T hle
  have hg' : g ∈ ((S : Set G) * (T : Set G)) := by
    rw [← this]; exact hg
  obtain ⟨s, hs, t, ht, e⟩ := Set.mem_mul.mp hg'
  exact ⟨s, hs, t, ht, e⟩

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_zpowers_sq {x : G} (h : x * x = 1) {s : G} (hs : s ∈ Subgroup.zpowers x) :
    s = 1 ∨ s = x := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul]
    have : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h
    rw [this, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, zpow_one]
    have : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h
    rw [this, one_zpow, one_mul]

variable {t : ℕ → G} {z y u i1 i2 r s : G} (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)
include hC

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_E_mem {x : G} :
    x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers z ↔ x = 1 ∨ x = z ∨ x = u ∨ x = u * z := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := burnsideJ49B_mem_sup_comm (S := Subgroup.zpowers u)
      (T := Subgroup.zpowers z) (fun a ha b hb => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (Commute.zpow_zpow (show Commute u z from hC.comm) m n).eq) hx
    rcases burnsideJ49B_zpowers_sq hC.u_sq ha with rfl | rfl <;>
      rcases burnsideJ49B_zpowers_sq hC.z_sq hb with rfl | rfl
    · left; simp
    · right; left; simp
    · right; right; left; simp
    · right; right; right; rfl
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_uz_ne_one : u * z ≠ 1 := by
  intro h
  apply hC.u_ne_z
  have : u = z⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [this]
  exact inv_eq_of_mul_eq_one_right hC.z_sq

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_E_norm {n : G} (hn : n ∈ Subgroup.normalizer
    (Subgroup.closure ({i1, i2} : Set G) : Set G)) :
    ∀ e ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers z,
      n * e * n⁻¹ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers z := by
  have key : ∀ e : G, e ∈ Subgroup.closure ({i1, i2} : Set G) → e * e = 1 → e ≠ 1 →
      n * e * n⁻¹ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers z := by
    intro e he he2 he1
    have h1 : n * e * n⁻¹ ∈ Subgroup.closure ({i1, i2} : Set G) :=
      (Subgroup.mem_normalizer_iff.1 hn e).1 he
    have h2 : (n * e * n⁻¹) * (n * e * n⁻¹) = 1 := by
      calc (n * e * n⁻¹) * (n * e * n⁻¹) = n * (e * e) * n⁻¹ := by group
        _ = 1 := by rw [he2]; group
    rcases burnsideJ49B_I_inv hC h1 h2 with h | h | h | h
    · exfalso; apply he1
      have : e = n⁻¹ * (n * e * n⁻¹) * n := by group
      rw [this, h]; group
    · rw [h]; exact (burnsideJ49B_E_mem hC).2 (Or.inr (Or.inl rfl))
    · rw [h]; exact (burnsideJ49B_E_mem hC).2 (Or.inr (Or.inr (Or.inl rfl)))
    · rw [h]; exact (burnsideJ49B_E_mem hC).2 (Or.inr (Or.inr (Or.inr rfl)))
  intro e he
  rcases (burnsideJ49B_E_mem hC).1 he with rfl | rfl | rfl | rfl
  · simp only [mul_one, mul_inv_cancel]; exact one_mem _
  · exact key _ (burnsideJ49B_z_mem_I hC) hC.z_sq hC.z_ne
  · exact key _ (burnsideJ49B_u_mem_I hC) hC.u_sq hC.u_ne
  · refine key _ (mul_mem (burnsideJ49B_u_mem_I hC) (burnsideJ49B_z_mem_I hC)) ?_
      (burnsideJ49B_uz_ne_one hC)
    calc u * z * (u * z) = u * (z * u) * z := by group
      _ = u * (u * z) * z := by rw [hC.comm]
      _ = (u * u) * (z * z) := by group
      _ = 1 := by rw [hC.u_sq, hC.z_sq]; group

end EPart

section ConjPart

variable {G : Type} [Group G] {z u : G} {n : G}
  (hn : ∀ e ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers z,
    n * e * n⁻¹ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers z)
include hn

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_conj_X {Y : Subgroup G} (hY : Y ∈ EInv5Ru z u) :
    CFSG.conjugate Y n ∈ EInv5Ru z u := by
  refine ⟨by rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hY.1, ?_⟩
  intro e he
  have he' : n * e * n⁻¹ ∈ Subgroup.normalizer (Y : Set G) := hY.2 (hn e he)
  rw [Subgroup.mem_normalizer_iff] at he' ⊢
  intro h
  rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate, CFSG.ASVolI.RuChoice.fx_mem_conjugate]
  have := he' (n * h * n⁻¹)
  have e1 : n * h * n⁻¹ ∈ Y ↔ (n * e * n⁻¹) * (n * h * n⁻¹) * (n * e * n⁻¹)⁻¹ ∈ Y := this
  have e2 : (n * e * n⁻¹) * (n * h * n⁻¹) * (n * e * n⁻¹)⁻¹ = n * (e * h * e⁻¹) * n⁻¹ := by group
  rw [e2] at e1
  exact e1

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_reach_conj :
    ∀ (a b : ↥(EInv5Ru z u)), (commGraphOn (EInv5Ru z u)).Reachable a b →
      (commGraphOn (EInv5Ru z u)).Reachable
        ⟨CFSG.conjugate a.1 n, burnsideJ49B_conj_X hn a.2⟩
        ⟨CFSG.conjugate b.1 n, burnsideJ49B_conj_X hn b.2⟩ := by
  intro a b hab
  obtain ⟨p⟩ := hab
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h p ih =>
    rename_i a a' b
    refine SimpleGraph.Reachable.trans ?_ ih
    refine SimpleGraph.Adj.reachable ?_
    rw [burnsideJ49B_commGraphOn_adj] at h ⊢
    obtain ⟨hne, hc⟩ := h
    refine ⟨?_, ?_⟩
    · intro e
      apply hne
      refine Subtype.ext ?_
      have this : CFSG.conjugate a.1 n = CFSG.conjugate a'.1 n := Subtype.mk.inj e
      have h2 : CFSG.conjugate (CFSG.conjugate a.1 n) n⁻¹ =
          CFSG.conjugate (CFSG.conjugate a'.1 n) n⁻¹ := by rw [this]
      rwa [CFSG.ASVolI.RuChoice.fx_conjugate_conjugate, CFSG.ASVolI.RuChoice.fx_conjugate_conjugate,
        mul_inv_cancel, CFSG.ASVolI.RuChoice.fx_conjugate_one,
        CFSG.ASVolI.RuChoice.fx_conjugate_one] at h2
    · show ⁅CFSG.conjugate a.1 n, CFSG.conjugate a'.1 n⁆ = ⊥
      unfold CFSG.conjugate
      rw [← Subgroup.map_commutator]
      have hc' : ⁅a.1, a'.1⁆ = ⊥ := hc
      rw [hc', Subgroup.map_bot]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_cgon_conj {B5 : Subgroup G} {B1 : Subgroup G}
    (hB1 : B1 ∈ CgonRu B5 z u) (hB1' : CFSG.conjugate B1 n ∈ CgonRu B5 z u)
    {B : Subgroup G} (hB : B ∈ CgonRu B5 z u) : CFSG.conjugate B n ∈ CgonRu B5 z u := by
  obtain ⟨hB5, hX1, hr1⟩ := hB1
  obtain ⟨_, hX, hr⟩ := hB
  obtain ⟨_, hX1', hr1'⟩ := hB1'
  have hc := burnsideJ49B_reach_conj hn ⟨B1, hX1⟩ ⟨B, hX⟩ (hr1.symm.trans hr)
  exact ⟨hB5, burnsideJ49B_conj_X hn hX, hr1'.trans hc⟩

end ConjPart

section Sup

variable {G : Type} [Group G] [Finite G]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_inv_in_sup {a b ℓ : G} (ha5 : a ^ 5 = 1) (ha1 : a ≠ 1) (hb5 : b ^ 5 = 1)
    (hb1 : b ≠ 1) (hab : a * b = b * a) (hne : Subgroup.zpowers a ≠ Subgroup.zpowers b)
    (hℓa : ℓ * a * ℓ⁻¹ = a) (hℓb : ℓ * b * ℓ⁻¹ = b⁻¹) {Y : Subgroup G} (hY5 : Nat.card Y = 5)
    (hℓY : ℓ ∈ Subgroup.normalizer (Y : Set G))
    (hYle : Y ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    Y = Subgroup.zpowers a ∨ Y = Subgroup.zpowers b := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hA5 : Nat.card (Subgroup.zpowers a) = 5 := burnsideJ49B_card_zpowers_five ha5 ha1
  have hB5 : Nat.card (Subgroup.zpowers b) = 5 := burnsideJ49B_card_zpowers_five hb5 hb1
  have hoa : orderOf a = 5 := orderOf_eq_prime ha5 ha1
  have hob : orderOf b = 5 := orderOf_eq_prime hb5 hb1
  obtain ⟨y, hyY, hy5, hy1, -⟩ := CFSG.Quasithin.RuType.exists_gen_of_card_five hY5
  have hYeq : Subgroup.zpowers y = Y :=
    CFSG.Quasithin.RuType.zpowers_eq_of_card_five hY5 hyY hy5 hy1
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ w ∈ Subgroup.zpowers b, x * w = w * x := by
    intro x hx w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact (Commute.zpow_zpow (show Commute a b from hab) m n).eq
  obtain ⟨x1, hx1, x2, hx2, hyx⟩ := burnsideJ49B_mem_sup_comm hcomm (hYle hyY)
  obtain ⟨p, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx1
  obtain ⟨q, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx2
  have hconj : ℓ * y * ℓ⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 hℓY y).1 hyY
  have hx1c : ℓ * a ^ p * ℓ⁻¹ = a ^ p := by rw [← conj_zpow, hℓa]
  have hx2c : ℓ * b ^ q * ℓ⁻¹ = (b ^ q)⁻¹ := by rw [← conj_zpow, hℓb, inv_zpow]
  have hcy : ℓ * y * ℓ⁻¹ = a ^ p * (b ^ q)⁻¹ := by
    rw [← hyx]
    calc ℓ * (a ^ p * b ^ q) * ℓ⁻¹ = (ℓ * a ^ p * ℓ⁻¹) * (ℓ * b ^ q * ℓ⁻¹) := by group
      _ = a ^ p * (b ^ q)⁻¹ := by rw [hx1c, hx2c]
  rw [← hYeq] at hconj
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hconj
  rw [hcy, ← hyx] at hm
  have hcab : Commute (a ^ p) (b ^ q) := Commute.zpow_zpow (show Commute a b from hab) p q
  rw [hcab.mul_zpow, ← zpow_mul, ← zpow_mul] at hm
  have key : a ^ (p * (1 - m)) = b ^ (q * (m + 1)) := by
    have hca1 : Commute (a ^ (p * m)) (b ^ (q * m)) := Commute.zpow_zpow (show Commute a b from hab) _ _
    calc a ^ (p * (1 - m)) = a ^ p * (a ^ (p * m))⁻¹ := by
          rw [mul_sub, mul_one, zpow_sub]
      _ = (b ^ (q * m) * b ^ q) := by
          have h2 : a ^ p * (b ^ q)⁻¹ = a ^ (p * m) * b ^ (q * m) := hm.symm
          have h3 : a ^ p * (a ^ (p * m))⁻¹ = b ^ (q * m) * b ^ q := by
            calc a ^ p * (a ^ (p * m))⁻¹ = (a ^ (p * m))⁻¹ * (a ^ p * (b ^ q)⁻¹) * b ^ q := by
                  have hc2 : Commute (a ^ p) (a ^ (p * m))⁻¹ :=
                    ((Commute.zpow_zpow_self a p (p * m))).inv_right
                  calc a ^ p * (a ^ (p * m))⁻¹ = (a ^ (p * m))⁻¹ * a ^ p := hc2.eq
                    _ = (a ^ (p * m))⁻¹ * (a ^ p * (b ^ q)⁻¹) * b ^ q := by group
              _ = (a ^ (p * m))⁻¹ * (a ^ (p * m) * b ^ (q * m)) * b ^ q := by rw [h2]
              _ = b ^ (q * m) * b ^ q := by group
          exact h3
      _ = b ^ (q * (m + 1)) := by rw [mul_add, mul_one, zpow_add]
  have hinA : a ^ (p * (1 - m)) ∈ Subgroup.zpowers a := Subgroup.zpow_mem_zpowers _ _
  have hinB : a ^ (p * (1 - m)) ∈ Subgroup.zpowers b := key ▸ Subgroup.zpow_mem_zpowers _ _
  have h1 : a ^ (p * (1 - m)) = 1 :=
    burnsideJ49B_eq_one_of_mem_two hA5 hB5 hne hinA hinB
  have h2 : b ^ (q * (m + 1)) = 1 := by rw [← key]; exact h1
  have d1 : (5 : ℤ) ∣ p * (1 - m) := by
    have := (orderOf_dvd_iff_zpow_eq_one (G := G) (x := a) (i := p * (1 - m))).2 h1
    rwa [hoa] at this
  have d2 : (5 : ℤ) ∣ q * (m + 1) := by
    have := (orderOf_dvd_iff_zpow_eq_one (G := G) (x := b) (i := q * (m + 1))).2 h2
    rwa [hob] at this
  have hp5 := Int.Prime.dvd_mul' Nat.prime_five d1
  have hq5 := Int.Prime.dvd_mul' Nat.prime_five d2
  by_cases hp : (5 : ℤ) ∣ p
  ·
    right
    have hap : a ^ p = 1 := by
      have := (orderOf_dvd_iff_zpow_eq_one (G := G) (x := a) (i := p)).1 (by rwa [hoa])
      exact this
    rw [hap, one_mul] at hyx
    have hyB : y ∈ Subgroup.zpowers b := hyx ▸ Subgroup.zpow_mem_zpowers _ _
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [← hYeq]; exact Subgroup.zpowers_le.2 hyB
    · rw [hB5, hY5]
  · by_cases hq : (5 : ℤ) ∣ q
    · left
      have hbq : b ^ q = 1 := by
        have := (orderOf_dvd_iff_zpow_eq_one (G := G) (x := b) (i := q)).1 (by rwa [hob])
        exact this
      rw [hbq, mul_one] at hyx
      have hyA : y ∈ Subgroup.zpowers a := hyx ▸ Subgroup.zpow_mem_zpowers _ _
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [← hYeq]; exact Subgroup.zpowers_le.2 hyA
      · rw [hA5, hY5]
    · exfalso
      have e1 : (5 : ℤ) ∣ 1 - m := hp5.resolve_left hp
      have e2 : (5 : ℤ) ∣ m + 1 := hq5.resolve_left hq
      omega

end Sup

section E1

variable {G : Type} [Group G] [Finite G] {t : ℕ → G} {z y u i1 i2 r s : G}
  (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)
  (hLS : ∀ (c : G) (Bc : Subgroup G), IsConj z c → Nat.card Bc = 5 →
    Bc ≤ Subgroup.centralizer ({c} : Set G) → burnsideJ48_LS z c Bc)
  (hzu : IsConj z u) (hzuz : IsConj z (u * z)) (hnbr : burnsideJ49B_Nbr z u)
  {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0))
include hC hLS hzu hzuz hnbr hB5

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_gen_pres {n : G}
    (hnI : n ∈ Subgroup.normalizer (Subgroup.closure ({i1, i2} : Set G) : Set G))
    (hgen : (∃ B1 ∈ CgonRu B5 z u, n ∈ Subgroup.normalizer (B1 : Set G)) ∨
      (∃ B1 ∈ CgonRu B5 z u, ∃ B2 ∈ CgonRu B5 z u, ⁅B1, B2⁆ = ⊥ ∧
        n ∈ Subgroup.normalizer ((B1 ⊔ B2 : Subgroup G) : Set G))) :
    ∀ B ∈ CgonRu B5 z u, CFSG.conjugate B n ∈ CgonRu B5 z u := by
  have hnE := burnsideJ49B_E_norm hC hnI
  intro B hB
  rcases hgen with ⟨B1, hB1, hn1⟩ | ⟨B1, hB1, B2, hB2, hc, hn12⟩
  · refine burnsideJ49B_cgon_conj hnE hB1 ?_ hB
    rw [CFSG.ASVolI.RuChoice.fx_conjugate_eq_self hn1]
    exact hB1
  · by_cases heq : B1 = B2
    · subst heq
      refine burnsideJ49B_cgon_conj hnE hB1 ?_ hB
      have : n ∈ Subgroup.normalizer (B1 : Set G) := by simpa using hn12
      rw [CFSG.ASVolI.RuChoice.fx_conjugate_eq_self this]
      exact hB1
    · refine burnsideJ49B_cgon_conj hnE hB1 ?_ hB
      have hB1' := (Set.ext_iff.1 (burnsideJ49B_cgon_eq hC hLS hzu hzuz hnbr hB5) B1).1 hB1
      obtain ⟨j, hj, rfl⟩ := hB1'
      have hY := burnsideJ49B_conj_X hnE (burnsideJ49B_cgon_X hC hLS hzu hzuz hnbr hB5 hB1)
      have hle : CFSG.conjugate (Subgroup.zpowers (t j)) n ≤
          Subgroup.zpowers (t j) ⊔ B2 := by
        have := CFSG.ASVolI.RuChoice.fx_conjugate_eq_self hn12
        rw [← this]
        exact CFSG.ASVolI.RuChoice.fx_conjugate_mono n le_sup_left
      have hℓE : ∀ k : ℕ, labG z u k ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers z := by
        intro k
        rcases burnsideJ49B_lab_cases z u k with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> rw [h]
        · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
        · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
        · exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      have hB2' := (Set.ext_iff.1 (burnsideJ49B_cgon_eq hC hLS hzu hzuz hnbr hB5) B2).1 hB2
      obtain ⟨j', hj', rfl⟩ := hB2'
      have hne : Subgroup.zpowers (t j) ≠ Subgroup.zpowers (t j') := heq
      have hnbr' := burnsideJ49B_nbrs hC hLS hzu hzuz hnbr hj
        (burnsideJ49B_X_mem hC hj') (Ne.symm hne) hc
      have hinv : labG z u j * t j' * (labG z u j)⁻¹ = (t j')⁻¹ := by
        rw [burnsideJ49B_lab_inv hC]
        rcases hnbr' with h | h
        ·
          have e := burnsideJ49B_X_inj hC hj' (Nat.mod_lt _ (by norm_num)) h
          have hlab : labG z u j = labG z u (j' + 2) := by
            unfold labG
            have : j % 3 = (j' + 2) % 3 := by omega
            rw [this]
          rw [hlab, hC.x_inv2 j' hj']
          have h5 := hC.x_pow j' hj'
          calc t j' ^ 4 = t j' ^ 4 * (t j' * (t j')⁻¹) := by group
            _ = t j' ^ 5 * (t j')⁻¹ := by group
            _ = (t j')⁻¹ := by rw [h5]; group
        · have e := burnsideJ49B_X_inj hC hj' (Nat.mod_lt _ (by norm_num)) h
          have hlab : labG z u j = labG z u (j' + 1) := by
            unfold labG
            have : j % 3 = (j' + 1) % 3 := by omega
            rw [this]
          rw [hlab, hC.x_inv1 j' hj']
          have h5 := hC.x_pow j' hj'
          calc t j' ^ 4 = t j' ^ 4 * (t j' * (t j')⁻¹) := by group
            _ = t j' ^ 5 * (t j')⁻¹ := by group
            _ = (t j')⁻¹ := by rw [h5]; group
      have hcent : labG z u j * t j * (labG z u j)⁻¹ = t j := by
        rw [hC.x_cent j hj]; group
      have hsup := burnsideJ49B_inv_in_sup (hC.x_pow j hj) (hC.x_ne j hj) (hC.x_pow j' hj')
        (hC.x_ne j' hj') (by
          rcases hnbr' with h | h
          · have e := burnsideJ49B_X_inj hC hj' (Nat.mod_lt _ (by norm_num)) h
            have := hC.x_adj j hj
            rwa [← e] at this
          · have e := burnsideJ49B_X_inj hC hj' (Nat.mod_lt _ (by norm_num)) h
            have := (hC.x_adj j' hj').symm
            have e2 : (j' + 1) % 12 = j := by omega
            rwa [e2] at this) hne hcent hinv (Y := CFSG.conjugate (Subgroup.zpowers (t j)) n)
        hY.1 (hY.2 (hℓE j)) hle
      rcases hsup with h | h
      · rw [h]; exact hB1
      · rw [h]; exact hB2

end E1

section RS

variable {G : Type} [Group G] [Finite G]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_zpowers_pow {x : G} (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1) {m : ℕ} (hm : m < 4) :
    Subgroup.zpowers (x ^ (m + 1)) = Subgroup.zpowers x := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hK : Nat.card (Subgroup.zpowers x) = 5 := burnsideJ49B_card_zpowers_five hx5 hx1
  have hmem : x ^ (m + 1) ∈ Subgroup.zpowers x := pow_mem (Subgroup.mem_zpowers x) _
  have h5 : (x ^ (m + 1)) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hx5, one_pow]
  have ho : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  have h1 : x ^ (m + 1) ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf (by omega) (by rw [ho]; omega)
  exact CFSG.Quasithin.RuType.zpowers_eq_of_card_five hK hmem h5 h1

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_conj_zpowers_of {x y g c : G} (hy5 : y ^ 5 = 1) (hy1 : y ≠ 1)
    (h : x * g = g * c) {m : ℕ} (hm : m < 4) (hc : c = y ^ (m + 1)) :
    CFSG.conjugate (Subgroup.zpowers x) g = Subgroup.zpowers y := by
  rw [CFSG.ASVolI.RuChoice.fx_conjugate_zpowers]
  have : g⁻¹ * x * g = c := by
    calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
      _ = g⁻¹ * (g * c) := by rw [h]
      _ = c := by group
  rw [this, hc]
  exact burnsideJ49B_zpowers_pow hy5 hy1 hm

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_mem_normalizer_of_conj_eq {A : Subgroup G} {g : G}
    (h : CFSG.conjugate A g = A) : g ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : y ∈ CFSG.conjugate A g := by rw [h]; exact hy
    exact CFSG.ASVolI.RuChoice.fx_mem_conjugate.1 this
  · intro hy
    rw [← h]
    exact CFSG.ASVolI.RuChoice.fx_mem_conjugate.2 hy

variable {t : ℕ → G} {z y u i1 i2 r s : G} (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)
include hC

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_conj_r {k : ℕ} (hk : k < 12) :
    CFSG.conjugate (Subgroup.zpowers (t k)) r = Subgroup.zpowers (t ((12 - k) % 12)) := by
  obtain ⟨m, hm, e⟩ := hC.r_x k hk
  have hj : (12 - k) % 12 < 12 := Nat.mod_lt _ (by norm_num)
  exact burnsideJ49B_conj_zpowers_of (hC.x_pow _ hj) (hC.x_ne _ hj) e hm rfl

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_conj_s {k : ℕ} (hk : k < 12) :
    CFSG.conjugate (Subgroup.zpowers (t k)) s = Subgroup.zpowers (t ((13 - k) % 12)) := by
  obtain ⟨m, hm, e⟩ := hC.s_x k hk
  have hj : (13 - k) % 12 < 12 := Nat.mod_lt _ (by norm_num)
  exact burnsideJ49B_conj_zpowers_of (hC.x_pow _ hj) (hC.x_ne _ hj) e hm rfl

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_norm_I {g : G}
    (h1 : ∃ p < 4, ∃ q < 4, i1 * g = g * (i1 ^ p * i2 ^ q))
    (h2 : ∃ p < 4, ∃ q < 4, i2 * g = g * (i1 ^ p * i2 ^ q)) :
    g ∈ Subgroup.normalizer (Subgroup.closure ({i1, i2} : Set G) : Set G) := by
  have hmemI : ∀ p q : ℕ, i1 ^ p * i2 ^ q ∈ Subgroup.closure ({i1, i2} : Set G) := fun p q =>
    mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)
  have key : ∀ y ∈ Subgroup.closure ({i1, i2} : Set G),
      g⁻¹ * y * g ∈ Subgroup.closure ({i1, i2} : Set G) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with h | h
      · rw [h]
        obtain ⟨p, -, q, -, e⟩ := h1
        have : g⁻¹ * i1 * g = i1 ^ p * i2 ^ q := by
          calc g⁻¹ * i1 * g = g⁻¹ * (i1 * g) := by group
            _ = g⁻¹ * (g * (i1 ^ p * i2 ^ q)) := by rw [e]
            _ = i1 ^ p * i2 ^ q := by group
        rw [this]; exact hmemI p q
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        obtain ⟨p, -, q, -, e⟩ := h2
        have : g⁻¹ * i2 * g = i1 ^ p * i2 ^ q := by
          calc g⁻¹ * i2 * g = g⁻¹ * (i2 * g) := by group
            _ = g⁻¹ * (g * (i1 ^ p * i2 ^ q)) := by rw [e]
            _ = i1 ^ p * i2 ^ q := by group
        rw [this]; exact hmemI p q
    | one => simp
    | mul a b _ _ ha hb =>
      have : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
      rw [this]; exact mul_mem ha hb
    | inv a _ ha =>
      have : g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
      rw [this]; exact inv_mem ha
  have hle : CFSG.conjugate (Subgroup.closure ({i1, i2} : Set G)) g ≤
      Subgroup.closure ({i1, i2} : Set G) := by
    intro x hx
    have hx' := CFSG.ASVolI.RuChoice.fx_mem_conjugate.1 hx
    have := key _ hx'
    simpa [mul_assoc] using this
  have heq : CFSG.conjugate (Subgroup.closure ({i1, i2} : Set G)) g =
      Subgroup.closure ({i1, i2} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [CFSG.ASVolI.RuChoice.fx_card_conjugate])
  exact burnsideJ49B_mem_normalizer_of_conj_eq heq

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_r_normI :
    r ∈ Subgroup.normalizer (Subgroup.closure ({i1, i2} : Set G) : Set G) :=
  burnsideJ49B_norm_I hC hC.r_i1 hC.r_i2

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_s_normI :
    s ∈ Subgroup.normalizer (Subgroup.closure ({i1, i2} : Set G) : Set G) :=
  burnsideJ49B_norm_I hC hC.s_i1 hC.s_i2

end RS

section WPart

variable {G : Type} [Group G] [Finite G] {t : ℕ → G} {z y u i1 i2 r s : G}
  (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)
  (hLS : ∀ (c : G) (Bc : Subgroup G), IsConj z c → Nat.card Bc = 5 →
    Bc ≤ Subgroup.centralizer ({c} : Set G) → burnsideJ48_LS z c Bc)
  (hzu : IsConj z u) (hzuz : IsConj z (u * z)) (hnbr : burnsideJ49B_Nbr z u)
  {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0))
include hC hLS hzu hzuz hnbr hB5

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_X_cgon {k : ℕ} (hk : k < 12) :
    Subgroup.zpowers (t k) ∈ CgonRu B5 z u := by
  have := burnsideJ49B_cgon_eq hC hLS hzu hzuz hnbr hB5
  rw [this]
  exact ⟨k, hk, rfl⟩

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_E1 :
    ∀ w ∈ WBI (CgonRu B5 z u) (Subgroup.closure ({i1, i2} : Set G)), ∀ B ∈ CgonRu B5 z u,
      CFSG.conjugate B w ∈ CgonRu B5 z u := by
  have hgen : ∀ n : G, n ∈ ({w | ∃ B1 ∈ CgonRu B5 z u,
        w ∈ Subgroup.normalizer (Subgroup.closure ({i1, i2} : Set G) : Set G) ∧
          w ∈ Subgroup.normalizer (B1 : Set G)} ∪
      {w | ∃ B1 ∈ CgonRu B5 z u, ∃ B2 ∈ CgonRu B5 z u, ⁅B1, B2⁆ = ⊥ ∧
        w ∈ Subgroup.normalizer (Subgroup.closure ({i1, i2} : Set G) : Set G) ∧
          w ∈ Subgroup.normalizer ((B1 ⊔ B2 : Subgroup G) : Set G)} : Set G) →
      (∀ B ∈ CgonRu B5 z u, CFSG.conjugate B n ∈ CgonRu B5 z u) ∧
        (∀ B ∈ CgonRu B5 z u, CFSG.conjugate B n⁻¹ ∈ CgonRu B5 z u) := by
    intro n hn
    rcases hn with ⟨B1, hB1, hnI, hn1⟩ | ⟨B1, hB1, B2, hB2, hc, hnI, hn12⟩
    · refine ⟨burnsideJ49B_gen_pres hC hLS hzu hzuz hnbr hB5 hnI (Or.inl ⟨B1, hB1, hn1⟩),
        burnsideJ49B_gen_pres hC hLS hzu hzuz hnbr hB5 (inv_mem hnI)
          (Or.inl ⟨B1, hB1, inv_mem hn1⟩)⟩
    · exact ⟨burnsideJ49B_gen_pres hC hLS hzu hzuz hnbr hB5 hnI (Or.inr ⟨B1, hB1, B2, hB2, hc, hn12⟩),
        burnsideJ49B_gen_pres hC hLS hzu hzuz hnbr hB5 (inv_mem hnI)
          (Or.inr ⟨B1, hB1, B2, hB2, hc, inv_mem hn12⟩)⟩
  intro w hw
  unfold WBI at hw
  have key : (∀ B ∈ CgonRu B5 z u, CFSG.conjugate B w ∈ CgonRu B5 z u) ∧
      (∀ B ∈ CgonRu B5 z u, CFSG.conjugate B w⁻¹ ∈ CgonRu B5 z u) := by
    induction hw using Subgroup.closure_induction with
    | mem x hx => exact hgen x hx
    | one =>
      refine ⟨fun B hB => ?_, fun B hB => ?_⟩ <;> simpa [CFSG.ASVolI.RuChoice.fx_conjugate_one] using hB
    | mul a b _ _ ha hb =>
      refine ⟨fun B hB => ?_, fun B hB => ?_⟩
      · rw [← CFSG.ASVolI.RuChoice.fx_conjugate_conjugate]
        exact hb.1 _ (ha.1 B hB)
      · rw [mul_inv_rev, ← CFSG.ASVolI.RuChoice.fx_conjugate_conjugate]
        exact ha.2 _ (hb.2 B hB)
    | inv a _ ha =>
      exact ⟨fun B hB => by simpa using ha.2 B hB, fun B hB => by simpa using ha.1 B hB⟩
  exact key.1

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_r_mem_W :
    r ∈ WBI (CgonRu B5 z u) (Subgroup.closure ({i1, i2} : Set G)) := by
  refine Subgroup.subset_closure (Or.inl ⟨Subgroup.zpowers (t 0),
    burnsideJ49B_X_cgon hC hLS hzu hzuz hnbr hB5 (by norm_num),
    burnsideJ49B_r_normI hC, ?_⟩)
  refine burnsideJ49B_mem_normalizer_of_conj_eq ?_
  have := burnsideJ49B_conj_r hC (k := 0) (by norm_num)
  simpa using this

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_s_mem_W :
    s ∈ WBI (CgonRu B5 z u) (Subgroup.closure ({i1, i2} : Set G)) := by
  refine Subgroup.subset_closure (Or.inr ⟨Subgroup.zpowers (t 0),
    burnsideJ49B_X_cgon hC hLS hzu hzuz hnbr hB5 (by norm_num), Subgroup.zpowers (t 1),
    burnsideJ49B_X_cgon hC hLS hzu hzuz hnbr hB5 (by norm_num), ?_,
    burnsideJ49B_s_normI hC, ?_⟩)
  · rw [burnsideJ49B_comm_zpowers_iff]
    have := hC.x_adj 0 (by norm_num)
    simpa using this
  · refine burnsideJ49B_mem_normalizer_of_conj_eq ?_
    rw [CFSG.ASVolI.RuChoice.fx_conjugate_sup, burnsideJ49B_conj_s hC (k := 0) (by norm_num),
      burnsideJ49B_conj_s hC (k := 1) (by norm_num)]
    simp [sup_comm]

end WPart

section Dihedral

variable {G : Type} [Group G] [Finite G] {t : ℕ → G} {z y u i1 i2 r s : G}
  (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
include hC in
theorem burnsideJ49B_rot_one {k : ℕ} (hk : k < 12) :
    CFSG.conjugate (Subgroup.zpowers (t k)) (r * s) = Subgroup.zpowers (t ((k + 1) % 12)) := by
  rw [← CFSG.ASVolI.RuChoice.fx_conjugate_conjugate, burnsideJ49B_conj_r hC hk,
    burnsideJ49B_conj_s hC (Nat.mod_lt _ (by norm_num))]
  congr 2
  omega

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
include hC in
theorem burnsideJ49B_rot_pow (c : ℕ) {k : ℕ} (hk : k < 12) :
    CFSG.conjugate (Subgroup.zpowers (t k)) ((r * s) ^ c) =
      Subgroup.zpowers (t ((k + c) % 12)) := by
  induction c with
  | zero => simp [CFSG.ASVolI.RuChoice.fx_conjugate_one, Nat.mod_eq_of_lt hk]
  | succ c ih =>
    rw [pow_succ, ← CFSG.ASVolI.RuChoice.fx_conjugate_conjugate, ih,
      burnsideJ49B_rot_one hC (Nat.mod_lt _ (by norm_num))]
    congr 2
    omega

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
include hC in
theorem burnsideJ49B_refl_pow (c : ℕ) {k : ℕ} (hk : k < 12) :
    CFSG.conjugate (Subgroup.zpowers (t k)) (r * (r * s) ^ c) =
      Subgroup.zpowers (t ((12 - k + c) % 12)) := by
  rw [← CFSG.ASVolI.RuChoice.fx_conjugate_conjugate, burnsideJ49B_conj_r hC hk,
    burnsideJ49B_rot_pow hC c (Nat.mod_lt _ (by norm_num))]
  congr 2
  omega

variable
  (hLS : ∀ (c : G) (Bc : Subgroup G), IsConj z c → Nat.card Bc = 5 →
    Bc ≤ Subgroup.centralizer ({c} : Set G) → burnsideJ48_LS z c Bc)
  (hzu : IsConj z u) (hzuz : IsConj z (u * z)) (hnbr : burnsideJ49B_Nbr z u)
  {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0))
include hC hLS hzu hzuz hnbr hB5

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_E3 (σ : commGraphOn (CgonRu B5 z u) ≃g commGraphOn (CgonRu B5 z u)) :
    ∃ w ∈ WBI (CgonRu B5 z u) (Subgroup.closure ({i1, i2} : Set G)),
      ∀ B : ↥(CgonRu B5 z u), (σ B : Subgroup G) = CFSG.conjugate (B : Subgroup G) w := by
  obtain ⟨φ, hφ⟩ := burnsideJ49B_iso hC hLS hzu hzuz hnbr hB5
  have hr := burnsideJ49B_r_mem_W hC hLS hzu hzuz hnbr hB5
  have hs := burnsideJ49B_s_mem_W hC hLS hzu hzuz hnbr hB5
  set τ : SimpleGraph.cycleGraph 12 ≃g SimpleGraph.cycleGraph 12 :=
    φ.symm.trans (σ.trans φ) with hτ
  have hBk : ∀ B : ↥(CgonRu B5 z u), ∃ (k : ℕ) (hk : k < 12),
      (B : Subgroup G) = Subgroup.zpowers (t k) := by
    intro B
    have := (Set.ext_iff.1 (burnsideJ49B_cgon_eq hC hLS hzu hzuz hnbr hB5) B.1).1 B.2
    obtain ⟨k, hk, e⟩ := this
    exact ⟨k, hk, e⟩
  have hφB : ∀ B : ↥(CgonRu B5 z u), ∀ (k : ℕ) (hk : k < 12),
      (B : Subgroup G) = Subgroup.zpowers (t k) → φ B = ⟨k, hk⟩ := by
    intro B k hk e
    have : B = ⟨Subgroup.zpowers (t k), burnsideJ49B_X_cgon hC hLS hzu hzuz hnbr hB5 hk⟩ :=
      Subtype.ext e
    rw [this]
    exact hφ k hk _
  have hτB : ∀ B : ↥(CgonRu B5 z u), τ (φ B) = φ (σ B) := by
    intro B
    simp [hτ]
  have hσB : ∀ (B : ↥(CgonRu B5 z u)) (j : Fin 12), φ (σ B) = j →
      (σ B : Subgroup G) = Subgroup.zpowers (t j.val) := by
    intro B j hj
    have hmem := burnsideJ49B_X_cgon hC hLS hzu hzuz hnbr hB5 j.2
    have : φ ⟨Subgroup.zpowers (t j.val), hmem⟩ = j := hφ j.val j.2 hmem
    have h2 : σ B = ⟨Subgroup.zpowers (t j.val), hmem⟩ := φ.injective (hj.trans this.symm)
    rw [h2]
  rcases burnsideJ49B_aut_cycle12 τ with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine ⟨(r * s) ^ c.val, pow_mem (mul_mem hr hs) _, fun B => ?_⟩
    obtain ⟨k, hk, hBe⟩ := hBk B
    have h1 := hφB B k hk hBe
    have h2 : φ (σ B) = (⟨k, hk⟩ : Fin 12) + c := by rw [← hτB, h1, hc]
    rw [hσB B _ h2, hBe, burnsideJ49B_rot_pow hC _ hk]
    congr 2
  · refine ⟨r * (r * s) ^ c.val, mul_mem hr (pow_mem (mul_mem hr hs) _), fun B => ?_⟩
    obtain ⟨k, hk, hBe⟩ := hBk B
    have h1 := hφB B k hk hBe
    have h2 : φ (σ B) = c - (⟨k, hk⟩ : Fin 12) := by rw [← hτB, h1, hc]
    rw [hσB B _ h2, hBe, burnsideJ49B_refl_pow hC _ hk]
    congr 2

end Dihedral

section Kernel

variable {G : Type} [Group G] [Finite G] {t : ℕ → G} {z y u i1 i2 r s : G}
  (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)
include hC

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_cent_inv_false {k : ℕ} (hk : k < 12) {e : G} (he2 : e * e = 1)
    (hc : e * t k = t k * e) (hi : e * t k * e = t k ^ 4) : False := by
  have h1 : e * t k * e = t k := by
    calc e * t k * e = (t k * e) * e := by rw [hc]
      _ = t k * (e * e) := by group
      _ = t k := by rw [he2]; group
  have h4 : t k = t k ^ 4 := h1.symm.trans hi
  have h3 : t k ^ 3 = 1 := by
    have : t k * t k ^ 3 = t k * 1 := by
      calc t k * t k ^ 3 = t k ^ 4 := by group
        _ = t k := h4.symm
        _ = t k * 1 := by group
    exact mul_left_cancel this
  have := (pow_gcd_eq_one (a := t k)).mpr ⟨h3, hC.x_pow k hk⟩
  rw [show Nat.gcd 3 5 = 1 by norm_num, pow_one] at this
  exact hC.x_ne k hk this

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_cent_label {k : ℕ} (hk : k < 12) {j : ℕ}
    (h : labG z u j * t k = t k * labG z u j) : labG z u j = labG z u k := by
  rcases burnsideJ49B_lab_three z u j k with e | e | e
  · exact e
  · exfalso
    rw [e] at h
    have hi := hC.x_inv1 k hk
    exact burnsideJ49B_cent_inv_false hC hk (burnsideJ49B_lab_sq hC _) h hi
  · exfalso
    rw [e] at h
    have hi := hC.x_inv2 k hk
    exact burnsideJ49B_cent_inv_false hC hk (burnsideJ49B_lab_sq hC _) h hi

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_I_inv_lab {e : G} (he : e ∈ Subgroup.closure ({i1, i2} : Set G))
    (he2 : e * e = 1) (he1 : e ≠ 1) : ∃ j, e = labG z u j := by
  rcases burnsideJ49B_I_inv hC he he2 with h | h | h | h
  · exact absurd h he1
  · exact ⟨0, by rw [h]; simp [labG]⟩
  · exact ⟨1, by rw [h]; simp [labG]⟩
  · exact ⟨2, by rw [h]; simp [labG]⟩

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_lab_mem_I (j : ℕ) : labG z u j ∈ Subgroup.closure ({i1, i2} : Set G) := by
  rcases burnsideJ49B_lab_cases z u j with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> rw [h]
  · exact burnsideJ49B_z_mem_I hC
  · exact burnsideJ49B_u_mem_I hC
  · exact mul_mem (burnsideJ49B_u_mem_I hC) (burnsideJ49B_z_mem_I hC)

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_lab_ne_one (j : ℕ) : labG z u j ≠ 1 := by
  rcases burnsideJ49B_lab_cases z u j with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> rw [h]
  · exact hC.z_ne
  · exact hC.u_ne
  · exact burnsideJ49B_uz_ne_one hC

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_fix_label {w : G}
    (hwI : w ∈ Subgroup.normalizer (Subgroup.closure ({i1, i2} : Set G) : Set G)) {k : ℕ}
    (hk : k < 12) (hwk : w ∈ Subgroup.normalizer (Subgroup.zpowers (t k) : Set G)) :
    w * labG z u k = labG z u k * w := by
  set ℓ := labG z u k with hℓ
  have hℓ2 : ℓ * ℓ = 1 := burnsideJ49B_lab_sq hC k
  set e := w * ℓ * w⁻¹ with he
  have heI : e ∈ Subgroup.closure ({i1, i2} : Set G) :=
    (Subgroup.mem_normalizer_iff.1 hwI ℓ).1 (burnsideJ49B_lab_mem_I hC k)
  have he2 : e * e = 1 := by
    calc e * e = w * (ℓ * ℓ) * w⁻¹ := by rw [he]; group
      _ = 1 := by rw [hℓ2]; group
  have he1 : e ≠ 1 := by
    intro h
    apply burnsideJ49B_lab_ne_one hC k
    show ℓ = 1
    have : ℓ = w⁻¹ * e * w := by rw [he]; group
    rw [this, h]; group
  obtain ⟨j, hj⟩ := burnsideJ49B_I_inv_lab hC heI he2 he1
  have hec : e * t k = t k * e := by
    have hmem : w⁻¹ * t k * w ∈ Subgroup.zpowers (t k) :=
      (Subgroup.mem_normalizer_iff''.1 hwk (t k)).1 (Subgroup.mem_zpowers _)
    have hcomm := burnsideJ49B_comm_zpowers (hC.x_cent k hk) hmem
    calc e * t k = w * (ℓ * (w⁻¹ * t k * w)) * w⁻¹ := by rw [he]; group
      _ = w * ((w⁻¹ * t k * w) * ℓ) * w⁻¹ := by rw [hcomm]
      _ = t k * e := by rw [he]; group
  rw [hj] at hec
  have := burnsideJ49B_cent_label hC hk hec
  have hee : e = ℓ := by rw [hj, this]
  calc w * ℓ = (w * ℓ * w⁻¹) * w := by group
    _ = ℓ * w := by rw [← he, hee]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_I_norm_X {x : G} (hx : x ∈ Subgroup.closure ({i1, i2} : Set G)) {k : ℕ}
    (hk : k < 12) : x ∈ Subgroup.normalizer (Subgroup.zpowers (t k) : Set G) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := burnsideJ49B_I_mem hC hx
  obtain ⟨m, hm, e⟩ := hC.i_nx p hp q hq k hk
  refine CFSG.ASVolI.RuChoice.mem_normalizer fun y hy => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← conj_zpow]
  have : i1 ^ p * i2 ^ q * t k * (i1 ^ p * i2 ^ q)⁻¹ = t k ^ (m + 1) := by
    rw [e]; group
  rw [this, ← zpow_natCast, ← zpow_mul]
  exact Subgroup.zpow_mem_zpowers _ _

end Kernel

section Kernel2

variable {G : Type} [Group G] [Finite G] {t : ℕ → G} {z y u i1 i2 r s : G}
  (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)
  (hLS : ∀ (c : G) (Bc : Subgroup G), IsConj z c → Nat.card Bc = 5 →
    Bc ≤ Subgroup.centralizer ({c} : Set G) → burnsideJ48_LS z c Bc)
  (hzu : IsConj z u) (hzuz : IsConj z (u * z)) (hnbr : burnsideJ49B_Nbr z u)
  {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0))
include hC hLS hzu hzuz hnbr hB5

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_E2
    (hK : ∀ n : G, n ∈ Subgroup.normalizer (B5 : Set G) → n * z = z * n → n * u = u * n →
      n ∈ Subgroup.closure ({i1, i2} : Set G)) :
    {w | w ∈ WBI (CgonRu B5 z u) (Subgroup.closure ({i1, i2} : Set G)) ∧
      ∀ B ∈ CgonRu B5 z u, CFSG.conjugate B w = B} =
      ((Subgroup.closure ({i1, i2} : Set G) : Subgroup G) : Set G) := by
  ext w
  constructor
  · rintro ⟨hw, hfix⟩
    have hwI : w ∈ Subgroup.normalizer (Subgroup.closure ({i1, i2} : Set G) : Set G) := by
      have hle : WBI (CgonRu B5 z u) (Subgroup.closure ({i1, i2} : Set G)) ≤
          Subgroup.normalizer (Subgroup.closure ({i1, i2} : Set G) : Set G) := by
        unfold WBI
        rw [Subgroup.closure_le]
        rintro x (⟨B1, -, hxI, -⟩ | ⟨B1, -, B2, -, -, hxI, -⟩) <;> exact hxI
      exact hle hw
    have hX0 := hfix _ (burnsideJ49B_X_cgon hC hLS hzu hzuz hnbr hB5 (k := 0) (by norm_num))
    have hX1 := hfix _ (burnsideJ49B_X_cgon hC hLS hzu hzuz hnbr hB5 (k := 1) (by norm_num))
    have hN0 := burnsideJ49B_mem_normalizer_of_conj_eq hX0
    have hN1 := burnsideJ49B_mem_normalizer_of_conj_eq hX1
    have hz := burnsideJ49B_fix_label hC hwI (k := 0) (by norm_num) hN0
    have hu := burnsideJ49B_fix_label hC hwI (k := 1) (by norm_num) hN1
    have e0 : labG z u 0 = z := by simp [labG]
    have e1 : labG z u 1 = u := by simp [labG]
    rw [e0] at hz
    rw [e1] at hu
    exact hK w (by rw [hB5]; exact hN0) hz hu
  · intro hw
    have hB5mem : B5 ∈ CgonRu B5 z u := by
      have := burnsideJ49B_X_cgon hC hLS hzu hzuz hnbr hB5 (k := 0) (by norm_num)
      rwa [← hB5] at this
    have hwN : w ∈ Subgroup.normalizer (B5 : Set G) := by
      have := burnsideJ49B_I_norm_X hC hw (k := 0) (by norm_num)
      rwa [← hB5] at this
    refine ⟨?_, ?_⟩
    · exact Subgroup.subset_closure (Or.inl ⟨B5, hB5mem, Subgroup.le_normalizer hw, hwN⟩)
    · intro B hB
      obtain ⟨k, hk, rfl⟩ := (Set.ext_iff.1 (burnsideJ49B_cgon_eq hC hLS hzu hzuz hnbr hB5) B).1 hB
      exact CFSG.ASVolI.RuChoice.fx_conjugate_eq_self (burnsideJ49B_I_norm_X hC hw hk)

end Kernel2

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
@[expose] def burnsideJ49B_Concl {G : Type} [Group G] (B5 : Subgroup G) (z u : G)
    (I : Subgroup G) : Prop :=
  (BzPRu B5 z u ≠ O5N (BuzPRu B5 z u) ⊓ Subgroup.centralizer ({z} : Set G) ∧
        BsetRu B5 z u ⊆ CgonRu B5 z u ∧
        Nonempty (commGraphOn (CgonRu B5 z u) ≃g SimpleGraph.cycleGraph 12) ∧
        ∀ B1 B2 : ↥(CgonRu B5 z u),
          ((commGraphOn (CgonRu B5 z u)).dist B1 B2 = 2 →
            IsPOnePlusTwoGroup 5 ↥((B1 : Subgroup G) ⊔ (B2 : Subgroup G))) ∧
          ((commGraphOn (CgonRu B5 z u)).dist B1 B2 = 3 →
            CFSG.Quasithin.IsSL2 5 ↥((B1 : Subgroup G) ⊔ (B2 : Subgroup G)))) ∧
      ((∀ w ∈ WBI (CgonRu B5 z u) I, ∀ B ∈ CgonRu B5 z u,
          CFSG.conjugate B w ∈ CgonRu B5 z u) ∧
        {w | w ∈ WBI (CgonRu B5 z u) I ∧ ∀ B ∈ CgonRu B5 z u, CFSG.conjugate B w = B} =
          (I : Set G) ∧
        ∀ σ : commGraphOn (CgonRu B5 z u) ≃g commGraphOn (CgonRu B5 z u),
          ∃ w ∈ WBI (CgonRu B5 z u) I,
            ∀ B : ↥(CgonRu B5 z u), (σ B : Subgroup G) = CFSG.conjugate (B : Subgroup G) w)

section Wreath

theorem burnsideJ49B_Q_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = Multiplicative.ofAdd (1 : ZMod 2) := by
  revert q
  decide

theorem burnsideJ49B_W_center {x : WreathedTwoGroup 2}
    (hx : ∀ g : WreathedTwoGroup 2, g * x = x * g) :
    x.right = 1 ∧ ∀ q, x.left q = x.left 1 := by
  have hs := hx ⟨fun _ => 1, Multiplicative.ofAdd (1 : ZMod 2)⟩
  have ha := hx ⟨fun q => if q = 1 then Multiplicative.ofAdd (1 : ZMod 4) else 1, 1⟩
  rw [RegularWreathProduct.ext_iff] at hs ha
  obtain ⟨hs1, -⟩ := hs
  obtain ⟨ha1, -⟩ := ha
  constructor
  · rcases burnsideJ49B_Q_cases x.right with h | h
    · exact h
    · exfalso
      have := congrFun ha1 1
      simp [RegularWreathProduct.mul_left, h] at this
      revert this
      decide
  · intro q
    have h1 := congrFun hs1 q
    simp [RegularWreathProduct.mul_left] at h1
    rcases burnsideJ49B_Q_cases q with h | h
    · rw [h]
    · rw [h]
      have h2 := congrFun hs1 1
      simp [RegularWreathProduct.mul_left] at h2
      rw [h] at h1
      rw [inv_mul_cancel] at h1
      exact h1.symm

theorem burnsideJ49B_W_card : Nat.card (WreathedTwoGroup 2) = 32 := by
  have h := RegularWreathProduct.card (D := Multiplicative (ZMod (2 ^ 2)))
    (Q := Multiplicative (ZMod 2))
  have h1 : Nat.card (Multiplicative (ZMod (2 ^ 2))) = 4 := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod (2 ^ 2))), Nat.card_zmod]; norm_num
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod 2)), Nat.card_zmod]
  change Nat.card (Multiplicative (ZMod (2 ^ 2)) ≀ᵣ Multiplicative (ZMod 2)) = 32
  rw [h, h1, h2]
  norm_num

theorem burnsideJ49B_W_center_eq {x : WreathedTwoGroup 2}
    (hx : ∀ g : WreathedTwoGroup 2, g * x = x * g) :
    x = ⟨fun _ => x.left 1, 1⟩ := by
  obtain ⟨hr, hl⟩ := burnsideJ49B_W_center hx
  refine RegularWreathProduct.ext ?_ hr
  funext q
  exact hl q

theorem burnsideJ49B_W_card_center_le : Nat.card (Subgroup.center (WreathedTwoGroup 2)) ≤ 4 := by
  have hinj : Function.Injective
      (fun x : Subgroup.center (WreathedTwoGroup 2) => (x : WreathedTwoGroup 2).left 1) := by
    intro x y h
    have hx := burnsideJ49B_W_center_eq (x := (x : WreathedTwoGroup 2))
      (fun g => (Subgroup.mem_center_iff.1 x.2 g))
    have hy := burnsideJ49B_W_center_eq (x := (y : WreathedTwoGroup 2))
      (fun g => (Subgroup.mem_center_iff.1 y.2 g))
    apply Subtype.ext
    rw [hx, hy]
    simp only at h
    rw [h]
  have := Nat.card_le_card_of_injective _ hinj
  have h4 : Nat.card (Multiplicative (ZMod (2 ^ 2))) = 4 := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod (2 ^ 2))), Nat.card_zmod]; norm_num
  rw [h4] at this
  exact this

theorem burnsideJ49B_W_center_inv {x y : WreathedTwoGroup 2}
    (hx : ∀ g : WreathedTwoGroup 2, g * x = x * g) (hy : ∀ g : WreathedTwoGroup 2, g * y = y * g)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have ex := burnsideJ49B_W_center_eq hx
  have ey := burnsideJ49B_W_center_eq hy
  set a := x.left 1 with ha
  set b := y.left 1 with hb
  have ha2 : a * a = 1 := by
    have := congrArg (fun w : WreathedTwoGroup 2 => w.left 1) hx2
    rw [ex] at this
    simpa [RegularWreathProduct.mul_left] using this
  have hb2 : b * b = 1 := by
    have := congrArg (fun w : WreathedTwoGroup 2 => w.left 1) hy2
    rw [ey] at this
    simpa [RegularWreathProduct.mul_left] using this
  have ha1 : a ≠ 1 := by
    intro h
    apply hx1
    rw [ex, h]
    rfl
  have hb1 : b ≠ 1 := by
    intro h
    apply hy1
    rw [ey, h]
    rfl
  have key : ∀ c d : Multiplicative (ZMod (2 ^ 2)), c * c = 1 → d * d = 1 → c ≠ 1 → d ≠ 1 → c = d := by
    decide
  rw [ex, ey, key a b ha2 hb2 ha1 hb1]

theorem burnsideJ49B_W_abelian16 {I₁ I₂ : Subgroup (WreathedTwoGroup 2)}
    (h1 : ∀ a ∈ I₁, ∀ b ∈ I₁, a * b = b * a) (h2 : ∀ a ∈ I₂, ∀ b ∈ I₂, a * b = b * a)
    (c1 : Nat.card I₁ = 16) (c2 : Nat.card I₂ = 16) : I₁ = I₂ := by
  by_contra hne
  have hW := burnsideJ49B_W_card
  have hd : Nat.card (I₁ ⊔ I₂ : Subgroup (WreathedTwoGroup 2)) ∣ 32 := by
    have := Subgroup.card_subgroup_dvd_card (I₁ ⊔ I₂)
    rwa [hW] at this
  have hd1 : 16 ∣ Nat.card (I₁ ⊔ I₂ : Subgroup (WreathedTwoGroup 2)) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : I₁ ≤ I₁ ⊔ I₂)
    rwa [c1] at this
  have hsup : I₁ ⊔ I₂ = ⊤ := by
    have hc : Nat.card (I₁ ⊔ I₂ : Subgroup (WreathedTwoGroup 2)) = 16 ∨
        Nat.card (I₁ ⊔ I₂ : Subgroup (WreathedTwoGroup 2)) = 32 := by
      obtain ⟨k, hk⟩ := hd1
      have : k ≤ 2 := by
        have := Nat.le_of_dvd (by norm_num) hd
        omega
      have hpos : 0 < Nat.card (I₁ ⊔ I₂ : Subgroup (WreathedTwoGroup 2)) := Nat.card_pos
      interval_cases k
      · omega
      · left; omega
      · right; omega
    rcases hc with hc | hc
    · exfalso
      have e1 : I₁ = I₁ ⊔ I₂ := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hc, c1])
      have e2 : I₂ = I₁ ⊔ I₂ := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hc, c2])
      exact hne (e1.trans e2.symm)
    · exact Subgroup.eq_top_of_card_eq _ (by rw [hc, hW])
  have hle : (I₁ ⊓ I₂ : Subgroup (WreathedTwoGroup 2)) ≤ Subgroup.center (WreathedTwoGroup 2) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hcent : (I₁ ⊔ I₂ : Subgroup _) ≤ Subgroup.centralizer ({x} : Set (WreathedTwoGroup 2)) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]; exact (h1 x hx.1 a ha).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]; exact (h2 x hx.2 a ha).symm
    have hg : g ∈ Subgroup.centralizer ({x} : Set (WreathedTwoGroup 2)) := by
      apply hcent; rw [hsup]; exact Subgroup.mem_top g
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    exact hg
  have hidx1 : I₁.index = 2 := by
    have := Subgroup.card_mul_index I₁
    rw [c1, hW] at this
    omega
  have hidx2 : I₂.index = 2 := by
    have := Subgroup.card_mul_index I₂
    rw [c2, hW] at this
    omega
  have hidx : (I₁ ⊓ I₂).index ≤ I₁.index * I₂.index := Subgroup.index_inf_le
  rw [hidx1, hidx2] at hidx
  have hcm := Subgroup.card_mul_index (I₁ ⊓ I₂)
  rw [hW] at hcm
  have hpos : 0 < (I₁ ⊓ I₂).index := Nat.pos_of_ne_zero (fun h => by rw [h] at hcm; omega)
  have h8 : 8 ≤ Nat.card (I₁ ⊓ I₂ : Subgroup (WreathedTwoGroup 2)) := by
    generalize (I₁ ⊓ I₂ : Subgroup (WreathedTwoGroup 2)).index = i at hcm hidx hpos
    generalize Nat.card (I₁ ⊓ I₂ : Subgroup (WreathedTwoGroup 2)) = c at hcm ⊢
    interval_cases i <;> omega
  have := Subgroup.card_le_of_le hle
  have := burnsideJ49B_W_card_center_le
  omega

end Wreath

section Sylow

variable {A : Type} [Group A] [Finite A]

theorem burnsideJ49B_syl_conj {p : ℕ} [hp : Fact p.Prime] {N R S : Subgroup A} (hR : R ≤ N)
    (hS : S ≤ N) (hRp : IsPGroup p R) (hSp : IsPGroup p S) (hRi : ¬ p ∣ R.relIndex N)
    (hSi : ¬ p ∣ S.relIndex N) (hcard : Nat.card R = Nat.card S) :
    ∃ n ∈ N, S = CFSG.conjugate R n := by
  have hR' : IsPGroup p (R.subgroupOf N) := hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hR).symm
  have hS' : IsPGroup p (S.subgroupOf N) := hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hS).symm
  set PR := hR'.toSylow hRi
  set PS := hS'.toSylow hSi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N PR PS
  have hRc : ((PR : Sylow p N) : Subgroup N) = R.subgroupOf N := IsPGroup.toSylow_coe _ _
  have hSc : ((PS : Sylow p N) : Subgroup N) = S.subgroupOf N := IsPGroup.toSylow_coe _ _
  refine ⟨((g⁻¹ : N) : A), (g⁻¹ : N).2, ?_⟩
  have hle : S ≤ CFSG.conjugate R ((g⁻¹ : N) : A) := by
    intro x hx
    have hxN : x ∈ N := hS hx
    have hy' : (⟨x, hxN⟩ : N) ∈ ((g • PR : Sylow p N) : Subgroup N) := by
      rw [hg, hSc, Subgroup.mem_subgroupOf]
      exact hx
    rw [Sylow.coe_subgroup_smul, hRc, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Subgroup.mem_subgroupOf] at hy'
    have e : (((MulAut.conj g)⁻¹ • (⟨x, hxN⟩ : N) : N) : A) = (g : A)⁻¹ * x * g := by
      rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
      simp
    rw [e] at hy'
    rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate]
    simpa using hy'
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [CFSG.ASVolI.RuChoice.fx_card_conjugate, hcard])

end Sylow

section Abelian16

theorem burnsideJ49B_abelian16_unique {X : Type} [Group X] (ψ : X ≃* WreathedTwoGroup 2)
    {J₁ J₂ : Subgroup X} (h1 : ∀ a ∈ J₁, ∀ b ∈ J₁, a * b = b * a)
    (h2 : ∀ a ∈ J₂, ∀ b ∈ J₂, a * b = b * a) (c1 : Nat.card J₁ = 16) (c2 : Nat.card J₂ = 16) :
    J₁ = J₂ := by
  have key : J₁.map ψ.toMonoidHom = J₂.map ψ.toMonoidHom := by
    refine burnsideJ49B_W_abelian16 ?_ ?_ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, h1 a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, h2 a ha b hb]
    · rw [Subgroup.card_map_of_injective ψ.injective, c1]
    · rw [Subgroup.card_map_of_injective ψ.injective, c2]
  exact Subgroup.map_injective ψ.injective key

variable {A : Type} [Group A] [Finite A]

theorem burnsideJ49B_abelian16_in {S : Subgroup A} (hS : Nonempty (↥S ≃* WreathedTwoGroup 2))
    {I I' : Subgroup A} (hI : I ≤ S) (hI' : I' ≤ S) (h1 : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a)
    (h2 : ∀ a ∈ I', ∀ b ∈ I', a * b = b * a) (c1 : Nat.card I = 16) (c2 : Nat.card I' = 16) :
    I = I' := by
  obtain ⟨ψ⟩ := hS
  have key : I.subgroupOf S = I'.subgroupOf S := by
    refine burnsideJ49B_abelian16_unique ψ ?_ ?_ ?_ ?_
    · intro a ha b hb
      exact Subtype.ext (h1 a ha b hb)
    · intro a ha b hb
      exact Subtype.ext (h2 a ha b hb)
    · rw [CFSG.Quasithin.RuType.card_subgroupOf_of_le hI, c1]
    · rw [CFSG.Quasithin.RuType.card_subgroupOf_of_le hI', c2]
  have := (Subgroup.subgroupOf_inj (H₁ := I) (H₂ := I') (K := S)).1 key
  rwa [inf_eq_left.2 hI, inf_eq_left.2 hI'] at this

end Abelian16

section Syl32

variable {A : Type} [Group A] [Finite A] {N R : Subgroup A}
  (hR : R ≤ N) (hRc : Nat.card R = 32) (hRW : Nonempty (↥R ≃* WreathedTwoGroup 2))
  (hN : ¬ 64 ∣ Nat.card N)
include hR hRc hN

theorem burnsideJ49B_relIndex_odd {S : Subgroup A} (hS : S ≤ N) (hSc : Nat.card S = 32) :
    ¬ 2 ∣ S.relIndex N := by
  have h := CFSG.Quasithin.RuType.relIndex_mul_card_of_le hS
  rw [hSc] at h
  intro hd
  apply hN
  rw [← h]
  obtain ⟨k, hk⟩ := hd
  rw [hk]
  exact ⟨k, by ring⟩

theorem burnsideJ49B_exists_S32 {I : Subgroup A} (hI : I ≤ N) (hIc : Nat.card I = 16) :
    ∃ S : Subgroup A, S ≤ N ∧ I ≤ S ∧ Nat.card S = 32 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI2 : IsPGroup 2 (I.subgroupOf N) :=
    (IsPGroup.of_card (n := 4) (by rw [hIc]; norm_num)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hI).symm
  obtain ⟨Q, hQ⟩ := hI2.exists_le_sylow
  have hf : (Nat.card N).factorization 2 = 5 := by
    have hpos : Nat.card N ≠ 0 := Nat.card_pos.ne'
    have h32 : 2 ^ 5 ∣ Nat.card N := by
      have := Subgroup.card_dvd_of_le hR
      rw [hRc] at this
      simpa using this
    have h5 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).1 h32
    have h6 : ¬ 2 ^ 6 ∣ Nat.card N := by simpa using hN
    have h6' := mt (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).2 h6
    omega
  have hQc : Nat.card Q = 32 := by
    rw [Sylow.card_eq_multiplicity, hf]
    norm_num
  refine ⟨(Q : Subgroup N).map N.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro x hx
    have hxN : x ∈ N := hI hx
    have : (⟨x, hxN⟩ : N) ∈ (Q : Subgroup N) := hQ (Subgroup.mem_subgroupOf.2 hx)
    exact ⟨⟨x, hxN⟩, this, rfl⟩
  · rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact hQc

theorem burnsideJ49B_S32_conj {S : Subgroup A} (hS : S ≤ N) (hSc : Nat.card S = 32) :
    ∃ n ∈ N, S = CFSG.conjugate R n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact burnsideJ49B_syl_conj hR hS (IsPGroup.of_card (n := 5) (by rw [hRc]; norm_num))
    (IsPGroup.of_card (n := 5) (by rw [hSc]; norm_num))
    (burnsideJ49B_relIndex_odd hR hRc hN hR hRc) (burnsideJ49B_relIndex_odd hR hRc hN hS hSc)
    (by rw [hRc, hSc])

include hRW in
theorem burnsideJ49B_S32_iso {S : Subgroup A} (hS : S ≤ N) (hSc : Nat.card S = 32) :
    Nonempty (↥S ≃* WreathedTwoGroup 2) := by
  obtain ⟨n, -, hn⟩ := burnsideJ49B_S32_conj hR hRc hN hS hSc
  obtain ⟨ψ⟩ := hRW
  have e1 : ↥R ≃* ↥(CFSG.conjugate R n) := MulEquiv.subgroupMap (MulAut.conj n⁻¹) R
  have e2 : ↥(CFSG.conjugate R n) ≃* ↥S := MulEquiv.subgroupCongr hn.symm
  exact ⟨(e2.symm.trans e1.symm).trans ψ⟩

include hRW in
theorem burnsideJ49B_abelian16_conj {I₁ I₂ : Subgroup A} (h1 : I₁ ≤ N) (h2 : I₂ ≤ N)
    (a1 : ∀ a ∈ I₁, ∀ b ∈ I₁, a * b = b * a) (a2 : ∀ a ∈ I₂, ∀ b ∈ I₂, a * b = b * a)
    (c1 : Nat.card I₁ = 16) (c2 : Nat.card I₂ = 16) :
    ∃ n ∈ N, CFSG.conjugate I₁ n = I₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₁, hS₁N, hIS₁, hS₁c⟩ := burnsideJ49B_exists_S32 hR hRc hN h1 c1
  obtain ⟨S₂, hS₂N, hIS₂, hS₂c⟩ := burnsideJ49B_exists_S32 hR hRc hN h2 c2
  obtain ⟨n, hnN, hn⟩ := burnsideJ49B_syl_conj hS₁N hS₂N
    (IsPGroup.of_card (n := 5) (by rw [hS₁c]; norm_num))
    (IsPGroup.of_card (n := 5) (by rw [hS₂c]; norm_num))
    (burnsideJ49B_relIndex_odd hR hRc hN hS₁N hS₁c) (burnsideJ49B_relIndex_odd hR hRc hN hS₂N hS₂c)
    (by rw [hS₁c, hS₂c])
  refine ⟨n, hnN, ?_⟩
  have hle : CFSG.conjugate I₁ n ≤ S₂ := by
    rw [hn]
    exact CFSG.ASVolI.RuChoice.fx_conjugate_mono n hIS₁
  refine burnsideJ49B_abelian16_in (burnsideJ49B_S32_iso hR hRc hRW hN hS₂N hS₂c) hle hIS₂ ?_ a2
    (by rw [CFSG.ASVolI.RuChoice.fx_card_conjugate, c1]) c2
  intro a ha b hb
  rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate] at ha hb
  have := a1 _ ha _ hb
  have e : ∀ x : A, x = n⁻¹ * (n * x * n⁻¹) * n := fun x => by group
  rw [e a, e b]
  calc n⁻¹ * (n * a * n⁻¹) * n * (n⁻¹ * (n * b * n⁻¹) * n)
      = n⁻¹ * ((n * a * n⁻¹) * (n * b * n⁻¹)) * n := by group
    _ = n⁻¹ * ((n * b * n⁻¹) * (n * a * n⁻¹)) * n := by rw [this]
    _ = _ := by group

end Syl32

section KLemma

variable {A : Type} [Group A] [Finite A]

theorem burnsideJ49B_eq_one_of_sq {x : A} (h5 : x ^ 5 = 1) (h2 : x * x = 1) : x = 1 := by
  have h2' : x ^ 2 = 1 := by rw [pow_two]; exact h2
  have := (pow_gcd_eq_one (a := x)).mpr ⟨h2', h5⟩
  rwa [show Nat.gcd 2 5 = 1 by norm_num, pow_one] at this

theorem burnsideJ49B_K {z u : A} {B5 I N R : Subgroup A} (hz2 : z * z = 1) (hu2 : u * u = 1)
    (hzu : u ≠ z) (hz1 : z ≠ 1) (hu1 : u ≠ 1) (huz : u * z = z * u)
    (hNdef : N = Subgroup.normalizer (B5 : Set A) ⊓ Subgroup.centralizer ({z} : Set A))
    (hB5 : Nat.card B5 = 5) (hB5z : B5 ≤ Subgroup.centralizer ({z} : Set A))
    (hR : R ≤ N) (hRc : Nat.card R = 32) (hRW : Nonempty (↥R ≃* WreathedTwoGroup 2))
    (hN160 : Nat.card N ∣ 160) (hI : I ≤ N) (hIab : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a)
    (hIc : Nat.card I = 16) (huI : u ∈ I)
    (hu_inv : ∀ x ∈ B5, u * x * u⁻¹ = x⁻¹) :
    ∀ n ∈ N, n * u = u * n → n ∈ I := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hN64 : ¬ 64 ∣ Nat.card N := by
    intro h
    have h2 : 64 ∣ 160 := h.trans hN160
    omega
  set C : Subgroup A := N ⊓ Subgroup.centralizer ({u} : Set A) with hC
  have hIC : I ≤ C := fun x hx =>
    ⟨hI hx, Subgroup.mem_centralizer_singleton_iff.2 (hIab x hx u huI)⟩
  have hCN : C ≤ N := inf_le_left
  have hB5N : B5 ≤ N := fun x hx => by
    rw [hNdef]
    exact ⟨Subgroup.le_normalizer hx, hB5z hx⟩
  have hCnorm : C ≤ Subgroup.normalizer (B5 : Set A) := fun x hx => by
    have := hx.1
    rw [hNdef] at this
    exact this.1
  have hCB : C ⊓ B5 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨-, hxu⟩, hxB⟩ := hx
    rw [Subgroup.mem_bot]
    have h1 := hu_inv x hxB
    have h2 : u * x * u⁻¹ = x := by
      rw [← Subgroup.mem_centralizer_singleton_iff.1 hxu]; group
    rw [h2] at h1
    have h22 : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel x
    have hx5 : x ^ 5 = 1 := by
      have hd := Subgroup.orderOf_dvd_natCard B5 hxB
      rw [hB5] at hd
      exact orderOf_dvd_iff_pow_eq_one.1 hd
    exact burnsideJ49B_eq_one_of_sq hx5 h22
  have hCcard : Nat.card C ∣ 32 := by
    have h := CFSG.Quasithin.RuType.card_sup_mul_inf_of_normalizes hCnorm
    rw [hCB, Subgroup.card_bot, mul_one, hB5] at h
    have hle : C ⊔ B5 ≤ N := sup_le hCN hB5N
    have hd := Subgroup.card_dvd_of_le hle
    rw [h] at hd
    have h160 := hd.trans hN160
    have : Nat.card C * 5 ∣ 32 * 5 := by simpa using h160
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
  have h16 : 16 ≤ Nat.card C := by
    have := Subgroup.card_le_of_le hIC
    rwa [hIc] at this
  have hC16 : Nat.card C = 16 := by
    by_contra hne
    have hC32 : Nat.card C = 32 := by
      obtain ⟨m, hm, hmC⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (by simpa using hCcard : Nat.card C ∣ 2 ^ 5)
      interval_cases m <;> omega
    obtain ⟨ψ⟩ := burnsideJ49B_S32_iso hR hRc hRW hN64 hCN hC32
    have hzN : z ∈ N := by
      rw [hNdef]
      refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
      refine CFSG.ASVolI.RuChoice.mem_normalizer fun x hx => ?_
      have := Subgroup.mem_centralizer_singleton_iff.1 (hB5z hx)
      rw [show z * x * z⁻¹ = x by rw [← this]; group]
      exact hx
    have hzC : z ∈ C := ⟨hzN, Subgroup.mem_centralizer_singleton_iff.2 huz.symm⟩
    have huC : u ∈ C := hIC huI
    set x : ↥C := ⟨z, hzC⟩
    set y : ↥C := ⟨u, huC⟩
    have hcz : ∀ c : ↥C, c * x = x * c := fun c => by
      apply Subtype.ext
      have hcN : (c : A) ∈ N := hCN c.2
      rw [hNdef] at hcN
      exact Subgroup.mem_centralizer_singleton_iff.1 hcN.2
    have hcu : ∀ c : ↥C, c * y = y * c := fun c => by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 c.2.2
    have hxy : ψ x = ψ y := by
      refine burnsideJ49B_W_center_inv (fun g => ?_) (fun g => ?_) ?_ ?_ ?_ ?_
      · obtain ⟨c, rfl⟩ := ψ.surjective g
        rw [← map_mul, ← map_mul, hcz c]
      · obtain ⟨c, rfl⟩ := ψ.surjective g
        rw [← map_mul, ← map_mul, hcu c]
      · rw [← map_mul, ← map_one ψ]
        exact congrArg ψ (Subtype.ext hz2)
      · rw [← map_mul, ← map_one ψ]
        exact congrArg ψ (Subtype.ext hu2)
      · intro h
        exact hz1 (congrArg Subtype.val (ψ.injective (h.trans (map_one ψ).symm)))
      · intro h
        exact hu1 (congrArg Subtype.val (ψ.injective (h.trans (map_one ψ).symm)))
    exact hzu (congrArg Subtype.val (ψ.injective hxy)).symm
  have hIeq : I = C := Subgroup.eq_of_le_of_card_ge hIC (by rw [hC16, hIc])
  intro n hn hnu
  rw [hIeq]
  exact ⟨hn, Subgroup.mem_centralizer_singleton_iff.2 hnu⟩

end KLemma

section Bridge

variable {G : Type} [Group G] [Finite G] {z u : G}

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_LS_proj {c : G} {Bc : Subgroup G} (h : burnsideJ410_LS z c Bc) :
    burnsideJ48_LS z c Bc :=
  ⟨h.card_B, h.cent, h.card_P, h.exp, h.le_P, h.central, h.nonab, h.norm, h.pcore, h.inv_mod,
    h.card_cent, h.mem_P⟩

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_hLS (hL : burnsideJ410_Loc z u) :
    ∀ (c : G) (Bc : Subgroup G), IsConj z c → Nat.card Bc = 5 →
      Bc ≤ Subgroup.centralizer ({c} : Set G) → burnsideJ48_LS z c Bc :=
  fun c Bc hc hB hBc => burnsideJ49B_LS_proj (hL.LS c Bc hc hB hBc)

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_hnbr (hL : burnsideJ410_Loc z u) : burnsideJ49B_Nbr z u := by
  intro Y Y' hY hY' hne hc
  obtain ⟨v, hv, hvY, -⟩ := burnsideJ410_label_exists hL hY
  obtain ⟨w, hw, hwY', -⟩ := burnsideJ410_label_exists hL hY'
  obtain ⟨hwv, heq⟩ := burnsideJ410_nbr_eq hL hY hY' hne hc hv hvY hw hwY'
  refine ⟨w, hw, ?_, heq⟩
  by_contra hcon
  push Not at hcon
  have hwC : burnsideJ410_Cent w Y := by
    intro y hy
    have := hcon y hy
    calc w * y * w⁻¹ = (y * w) * w⁻¹ := by rw [this]
      _ = y := by group
  exact hwv (burnsideJ410_label_unique hL hY hw hv hwC hvY)

end Bridge

section SL2

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_isSL2_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Quasithin.IsSL2 5 A) : CFSG.Quasithin.IsSL2 5 B := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_isSL2_map {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (K : Subgroup A) (h : CFSG.Quasithin.IsSL2 5 ↥K) :
    CFSG.Quasithin.IsSL2 5 ↥(K.map f) :=
  burnsideJ49B_isSL2_of_equiv (Subgroup.equivMapOfInjective K f hf) h

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_isSL2_map_pair {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (a b : A)
    (h : CFSG.Quasithin.IsSL2 5 ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b)) :
    CFSG.Quasithin.IsSL2 5 ↥(Subgroup.zpowers (f a) ⊔ Subgroup.zpowers (f b)) := by
  have := burnsideJ49B_isSL2_map f hf _ h
  rwa [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at this

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_isSL2_conj {G : Type} [Group G] (K : Subgroup G) (w : G)
    (h : CFSG.Quasithin.IsSL2 5 ↥K) : CFSG.Quasithin.IsSL2 5 ↥(CFSG.conjugate K w) :=
  burnsideJ49B_isSL2_map (MulAut.conj w⁻¹).toMonoidHom (MulAut.conj w⁻¹).injective K h

end SL2

section Rot

variable {G : Type} [Group G] [Finite G] {t : ℕ → G} {z y u i1 i2 r s : G}
  (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
include hC in
theorem burnsideJ49B_sl2_rot
    (h0 : CFSG.Quasithin.IsSL2 5 ↥(Subgroup.zpowers (t 0) ⊔ Subgroup.zpowers (t 3))) {j : ℕ}
    (hj : j < 12) :
    CFSG.Quasithin.IsSL2 5 ↥(Subgroup.zpowers (t j) ⊔ Subgroup.zpowers (t ((j + 3) % 12))) := by
  have h := burnsideJ49B_isSL2_conj _ ((r * s) ^ j) h0
  rw [CFSG.ASVolI.RuChoice.fx_conjugate_sup, burnsideJ49B_rot_pow hC j (by norm_num : 0 < 12),
    burnsideJ49B_rot_pow hC j (by norm_num : 3 < 12)] at h
  have e1 : (0 + j) % 12 = j := by omega
  have e2 : (3 + j) % 12 = (j + 3) % 12 := by omega
  rw [e1, e2] at h
  exact h

end Rot

section Dist3

variable {G : Type} [Group G] [Finite G] {t : ℕ → G} {z y u i1 i2 r s : G}
  (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)
  (hLS : ∀ (c : G) (Bc : Subgroup G), IsConj z c → Nat.card Bc = 5 →
    Bc ≤ Subgroup.centralizer ({c} : Set G) → burnsideJ48_LS z c Bc)
  (hzu : IsConj z u) (hzuz : IsConj z (u * z)) (hnbr : burnsideJ49B_Nbr z u)
  {B5 : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0))
include hC hLS hzu hzuz hnbr hB5

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_dist3'
    (hSL : ∀ j < 12, CFSG.Quasithin.IsSL2 5
      ↥(Subgroup.zpowers (t j) ⊔ Subgroup.zpowers (t ((j + 3) % 12))))
    (B1 B2 : ↥(CgonRu B5 z u))
    (hd : (commGraphOn (CgonRu B5 z u)).dist B1 B2 = 3) :
    CFSG.Quasithin.IsSL2 5 ↥((B1 : Subgroup G) ⊔ (B2 : Subgroup G)) := by
  have hreach : (commGraphOn (CgonRu B5 z u)).Reachable B1 B2 := by
    by_contra h
    have := SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.2 (Or.inr h)
    omega
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  obtain ⟨M1, M2, h1, h2, h3⟩ := burnsideJ49B_walk3 p (by rw [hp, hd])
  have hne02 : B1 ≠ M2 := by
    intro h
    subst h
    have := burnsideJ49B_dist_le_one h3
    omega
  have hne13 : M1 ≠ B2 := by
    intro h
    subst h
    have := burnsideJ49B_dist_le_one h1
    omega
  rw [burnsideJ49B_commGraphOn_adj] at h1 h2 h3
  have hidx : ∀ B : ↥(CgonRu B5 z u), ∃ k, ∃ _ : k < 12,
      (B : Subgroup G) = Subgroup.zpowers (t k) := by
    intro B
    have := (Set.ext_iff.1 (burnsideJ49B_cgon_eq hC hLS hzu hzuz hnbr hB5) B.1).1 B.2
    obtain ⟨k, hk, e⟩ := this
    exact ⟨k, hk, e⟩
  have step : ∀ (k k' : ℕ), k < 12 → k' < 12 → Subgroup.zpowers (t k) ≠ Subgroup.zpowers (t k') →
      ⁅Subgroup.zpowers (t k), Subgroup.zpowers (t k')⁆ = ⊥ →
      k' = (k + 1) % 12 ∨ k' = (k + 11) % 12 := by
    intro k k' hk hk' hne hc
    rcases burnsideJ49B_nbrs hC hLS hzu hzuz hnbr hk (burnsideJ49B_X_mem hC hk') hne.symm hc
      with h | h
    · left; exact burnsideJ49B_X_inj hC hk' (Nat.mod_lt _ (by norm_num)) h
    · right; exact burnsideJ49B_X_inj hC hk' (Nat.mod_lt _ (by norm_num)) h
  obtain ⟨a, ha, hBa⟩ := hidx B1
  obtain ⟨b, hb, hMb⟩ := hidx M1
  obtain ⟨c, hc, hMc⟩ := hidx M2
  obtain ⟨d, hd', hBd⟩ := hidx B2
  have hab := step a b ha hb (by rw [← hBa, ← hMb]; exact fun h => h1.1 (Subtype.ext h))
    (by rw [← hBa, ← hMb]; exact h1.2)
  have hbc := step b c hb hc (by rw [← hMb, ← hMc]; exact fun h => h2.1 (Subtype.ext h))
    (by rw [← hMb, ← hMc]; exact h2.2)
  have hcd := step c d hc hd' (by rw [← hMc, ← hBd]; exact fun h => h3.1 (Subtype.ext h))
    (by rw [← hMc, ← hBd]; exact h3.2)
  have hac : a ≠ c := by
    intro h
    apply hne02
    apply Subtype.ext
    rw [hBa, hMc, h]
  have hbd : b ≠ d := by
    intro h
    apply hne13
    apply Subtype.ext
    rw [hMb, hBd, h]
  have hcase : d = (a + 3) % 12 ∨ a = (d + 3) % 12 := by omega
  rw [hBa, hBd]
  rcases hcase with e | e
  · rw [e]
    exact hSL a ha
  · have e' : Subgroup.zpowers (t a) = Subgroup.zpowers (t ((d + 3) % 12)) := by rw [← e]
    rw [e', sup_comm]
    exact hSL d hd'

end Dist3

section Main

variable {G : Type} [Group G] [Finite G] {t : ℕ → G} {z y u i1 i2 r s : G}
  (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)
  (hLS : ∀ (c : G) (Bc : Subgroup G), IsConj z c → Nat.card Bc = 5 →
    Bc ≤ Subgroup.centralizer ({c} : Set G) → burnsideJ48_LS z c Bc)
  (hzu : IsConj z u) (hzuz : IsConj z (u * z)) (hnbr : burnsideJ49B_Nbr z u)
  (hSL0 : CFSG.Quasithin.IsSL2 5 ↥(Subgroup.zpowers (t 0) ⊔ Subgroup.zpowers (t 3)))
  {B5 I : Subgroup G} (hB5 : B5 = Subgroup.zpowers (t 0))
  (hI : I = Subgroup.closure ({i1, i2} : Set G))
  (hK : ∀ n : G, n ∈ Subgroup.normalizer (B5 : Set G) → n * z = z * n → n * u = u * n → n ∈ I)
include hC hLS hzu hzuz hnbr hSL0 hB5 hI hK

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_main' : burnsideJ49B_Concl B5 z u I := by
  subst hI
  refine ⟨⟨burnsideJ49B_B5u_ne hC hLS hzu hzuz hB5, ?_, ?_, ?_⟩,
    ⟨burnsideJ49B_E1 hC hLS hzu hzuz hnbr hB5, burnsideJ49B_E2 hC hLS hzu hzuz hnbr hB5 hK,
      burnsideJ49B_E3 hC hLS hzu hzuz hnbr hB5⟩⟩
  · rw [burnsideJ49B_Bset hC hLS hzu hzuz hB5]
    intro Y hY
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY
    rcases hY with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact burnsideJ49B_X_cgon hC hLS hzu hzuz hnbr hB5 (by norm_num)
  · obtain ⟨φ, -⟩ := burnsideJ49B_iso hC hLS hzu hzuz hnbr hB5
    exact ⟨φ⟩
  · intro B1 B2
    exact ⟨burnsideJ49B_dist2 hC hLS hzu hzuz hnbr hB5 B1 B2,
      burnsideJ49B_dist3' hC hLS hzu hzuz hnbr hB5
        (fun j hj => burnsideJ49B_sl2_rot hC hSL0 hj) B1 B2⟩

end Main

section Model

open CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_gel_mem (k : ℕ) : gel k ∈ ruP := by
  unfold gel
  refine evalSigned_mem (H := ruP) (fun g hg => ?_) _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ruA0_mem
  · exact ruA1_mem

open CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.J49 in
@[expose] noncomputable def burnsideJ49B_gelP (k : ℕ) : ↥ruP := ⟨gel k, burnsideJ49B_gel_mem k⟩

open CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_cfgP :
    Cfg (fun k => burnsideJ49B_gelP k) (burnsideJ49B_gelP 12) (burnsideJ49B_gelP 13)
      (burnsideJ49B_gelP 16) (burnsideJ49B_gelP 14) (burnsideJ49B_gelP 15)
      (burnsideJ49B_gelP 17) (burnsideJ49B_gelP 18) :=
  Cfg.of_inj ruP.subtype Subtype.val_injective cfg_gel

open CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_involution_class
    {t : ↥ruP} (ht2 : t * t = 1) (ht1 : t ≠ 1) {y : ↥ruP} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hyt : y * t = t * y) : ∃ c : ↥ruP, (c : Equiv.Perm (Fin 4060)) * ruZ * (c : Equiv.Perm (Fin 4060))⁻¹ = (t : Equiv.Perm (Fin 4060)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf (t : Equiv.Perm (Fin 4060)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have := congrArg Subtype.val ht2
      simpa [pow_two] using this
    · exact fun h => ht1 (Subtype.ext h)
  have hmem : (t : Equiv.Perm (Fin 4060)) ∈ {x | x ∈ ruP ∧ orderOf x = 2} := ⟨t.2, ho⟩
  rw [ruInvolutions_eq] at hmem
  rcases hmem with ⟨g, hg, hgt⟩ | ⟨g, hg, hgt⟩
  · exact ⟨⟨g, hg⟩, hgt⟩
  · exfalso
    set y' : Equiv.Perm (Fin 4060) := g⁻¹ * (y : Equiv.Perm (Fin 4060)) * g with hy'
    have hy'P : y' ∈ ruP := ruP.mul_mem (ruP.mul_mem (ruP.inv_mem hg) y.2) hg
    have hcomm : y' * ruA0 = ruA0 * y' := by
      have h1 : (y : Equiv.Perm (Fin 4060)) * t = t * y := congrArg Subtype.val hyt
      rw [← hgt] at h1
      calc y' * ruA0 = g⁻¹ * (y * (g * ruA0 * g⁻¹)) * g := by rw [hy']; group
        _ = g⁻¹ * ((g * ruA0 * g⁻¹) * y) * g := by rw [h1]
        _ = ruA0 * y' := by rw [hy']; group
    have hyL : y' ∈ ruL := by
      rw [← ruCentralizer_a]
      exact ⟨hy'P, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
    have hord : orderOf y' = 3 := by
      refine orderOf_eq_prime ?_ ?_
      · have := congrArg Subtype.val hy3
        have e : y' ^ 3 = g⁻¹ * ((y : Equiv.Perm (Fin 4060)) ^ 3) * g := by
          have := conj_pow (a := g⁻¹) (b := (y : Equiv.Perm (Fin 4060))) (i := 3)
          rw [inv_inv] at this
          rw [hy']
          exact this
        rw [e]
        simpa using congrArg (fun w : Equiv.Perm (Fin 4060) => g⁻¹ * w * g) this
      · intro h
        apply hy1
        apply Subtype.ext
        have : (y : Equiv.Perm (Fin 4060)) = g * y' * g⁻¹ := by rw [hy']; group
        rw [this, h]
        simp
    have hdvd := Subgroup.orderOf_dvd_natCard ruL hyL
    rw [hord, card_ruL] at hdvd
    omega

end Model

section CfgConj

variable {G : Type} [Group G]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_conj_apply (g x : G) : (MulAut.conj g⁻¹).toMonoidHom (g * x * g⁻¹) = x := by
  simp [MulAut.conj_apply, mul_assoc]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_Cfg_conj {t : ℕ → G} {z y u i1 i2 r s : G} (g : G)
    (h : Cfg t z y u i1 i2 r s) :
    Cfg (fun k => g * t k * g⁻¹) (g * z * g⁻¹) (g * y * g⁻¹) (g * u * g⁻¹) (g * i1 * g⁻¹)
      (g * i2 * g⁻¹) (g * r * g⁻¹) (g * s * g⁻¹) := by
  refine Cfg.of_inj (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective ?_
  simp only [burnsideJ49B_conj_apply]
  exact h

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_zpowers_conj (g x : G) :
    Subgroup.zpowers (g * x * g⁻¹) = CFSG.conjugate (Subgroup.zpowers x) g⁻¹ := by
  rw [CFSG.ASVolI.RuChoice.fx_conjugate_zpowers]
  simp

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_closure_conj (g a b : G) :
    Subgroup.closure ({g * a * g⁻¹, g * b * g⁻¹} : Set G) =
      CFSG.conjugate (Subgroup.closure ({a, b} : Set G)) g⁻¹ := by
  unfold CFSG.conjugate
  rw [MonoidHom.map_closure, Set.image_pair]
  simp [MulAut.conj_apply]

end CfgConj

section CardI

variable {G : Type} [Group G] {t : ℕ → G} {z y u i1 i2 r s : G} (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t z y u i1 i2 r s)
include hC

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_card_I : Nat.card ↥(Subgroup.closure ({i1, i2} : Set G)) = 16 := by
  have hmem : ∀ p q : ℕ, i1 ^ p * i2 ^ q ∈ Subgroup.closure ({i1, i2} : Set G) := fun p q =>
    mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)
  let f : Fin 4 × Fin 4 → ↥(Subgroup.closure ({i1, i2} : Set G)) := fun pq =>
    ⟨i1 ^ pq.1.val * i2 ^ pq.2.val, hmem _ _⟩
  have hinj : Function.Injective f := by
    rintro ⟨p, q⟩ ⟨p', q'⟩ h
    have h' : i1 ^ p.val * i2 ^ q.val = i1 ^ p'.val * i2 ^ q'.val := congrArg Subtype.val h
    have key : ∀ a b a' b' : Fin 4, i1 ^ a.val * i2 ^ b.val = i1 ^ a'.val * i2 ^ b'.val →
        a.val * 4 + b.val < a'.val * 4 + b'.val → False := by
      intro a b a' b' he hlt
      exact hC.i_dist a.val a.2 b.val b.2 a'.val a'.2 b'.val b'.2 hlt he
    rcases lt_trichotomy (p.val * 4 + q.val) (p'.val * 4 + q'.val) with hlt | heq | hgt
    · exact (key p q p' q' h' hlt).elim
    · have h1 : p.val = p'.val := by omega
      have h2 : q.val = q'.val := by omega
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · exact (key p' q' p q h'.symm hgt).elim
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := burnsideJ49B_I_mem hC hx
    exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)]
  simp

end CardI

section CR

variable {G : Type} [Group G] [Finite G] {t0 : ℕ → G} {z0 y0 u0 i10 i20 r0 s0 : G}
  (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t0 z0 y0 u0 i10 i20 r0 s0)
  {z u : G} {B5 I N R : Subgroup G}
include hC

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_CR_B (hK25 : ¬ 5 ^ 2 ∣ Nat.card (Subgroup.centralizer ({z} : Set G)))
    (hB5c : Nat.card B5 = 5) (hB5z : B5 ≤ Subgroup.centralizer ({z} : Set G))
    {g : G} (hg : g * z0 * g⁻¹ = z) :
    ∃ g' : G, g' * z0 * g'⁻¹ = z ∧ Subgroup.zpowers (g' * t0 0 * g'⁻¹) = B5 := by
  have hCg := burnsideJ49B_Cfg_conj g hC
  rw [hg] at hCg
  have hB1c : Nat.card (Subgroup.zpowers (g * t0 0 * g⁻¹)) = 5 :=
    burnsideJ49B_card_zpowers_five (hCg.x_pow 0 (by norm_num)) (hCg.x_ne 0 (by norm_num))
  have hB1z : Subgroup.zpowers (g * t0 0 * g⁻¹) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h0 := hCg.x_cent 0 (by norm_num)
    rw [← burnsideJ49B_z_eq_lab] at h0
    exact (burnsideJ49B_comm_zpowers h0 hx).symm
  obtain ⟨h, hhK, hh⟩ := burnsideJ410_sylow_conj hK25 hB1c hB5c hB1z hB5z
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.1 hhK
  refine ⟨h⁻¹ * g, ?_, ?_⟩
  · calc h⁻¹ * g * z0 * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * z0 * g⁻¹) * h := by group
      _ = z := by rw [hg]; calc h⁻¹ * z * h = h⁻¹ * (z * h) := by group
                                _ = h⁻¹ * (h * z) := by rw [hhz]
                                _ = z := by group
  · have e : h⁻¹ * g * t0 0 * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * t0 0 * g⁻¹) * (h⁻¹)⁻¹ := by group
    rw [e, burnsideJ49B_zpowers_conj, inv_inv, hh]

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_CR_I
    (hNdef : N = Subgroup.normalizer (B5 : Set G) ⊓ Subgroup.centralizer ({z} : Set G))
    (hR : R ≤ N) (hRc : Nat.card R = 32) (hRW : Nonempty (↥R ≃* WreathedTwoGroup 2))
    (hN160 : Nat.card N ∣ 160)
    (hIN : I ≤ N) (hIab : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a) (hIc : Nat.card I = 16)
    {g : G} (hg : g * z0 * g⁻¹ = z) (hB : Subgroup.zpowers (g * t0 0 * g⁻¹) = B5) :
    ∃ g' : G, g' * z0 * g'⁻¹ = z ∧ Subgroup.zpowers (g' * t0 0 * g'⁻¹) = B5 ∧
      Subgroup.closure ({g' * i10 * g'⁻¹, g' * i20 * g'⁻¹} : Set G) = I := by
  have hCg := burnsideJ49B_Cfg_conj g hC
  rw [hg] at hCg
  have hN64 : ¬ 64 ∣ Nat.card N := fun h => by
    have := h.trans hN160
    omega
  set I1 := Subgroup.closure ({g * i10 * g⁻¹, g * i20 * g⁻¹} : Set G) with hI1
  have hI1N : I1 ≤ N := by
    intro x hx
    rw [hNdef]
    refine ⟨?_, ?_⟩
    · have := burnsideJ49B_I_norm_X hCg hx (k := 0) (by norm_num)
      beta_reduce at this
      rwa [hB] at this
    · obtain ⟨p, hp, q, hq, rfl⟩ := burnsideJ49B_I_mem hCg hx
      exact Subgroup.mem_centralizer_singleton_iff.2 (hCg.i_cz p hp q hq)
  obtain ⟨n, hnN, hn⟩ := burnsideJ49B_abelian16_conj hR hRc hRW hN64 hI1N hIN
    (fun a ha b hb => burnsideJ49B_I_comm hCg ha hb) hIab (burnsideJ49B_card_I hCg) hIc
  rw [hNdef] at hnN
  obtain ⟨hnB, hnz⟩ := hnN
  have hnz' : n * z = z * n := Subgroup.mem_centralizer_singleton_iff.1 hnz
  refine ⟨n⁻¹ * g, ?_, ?_, ?_⟩
  · calc n⁻¹ * g * z0 * (n⁻¹ * g)⁻¹ = n⁻¹ * (g * z0 * g⁻¹) * n := by group
      _ = z := by rw [hg]; calc n⁻¹ * z * n = n⁻¹ * (z * n) := by group
                                _ = n⁻¹ * (n * z) := by rw [hnz']
                                _ = z := by group
  · have e : n⁻¹ * g * t0 0 * (n⁻¹ * g)⁻¹ = n⁻¹ * (g * t0 0 * g⁻¹) * (n⁻¹)⁻¹ := by group
    rw [e, burnsideJ49B_zpowers_conj, inv_inv, hB]
    exact CFSG.ASVolI.RuChoice.fx_conjugate_eq_self hnB
  · have e1 : n⁻¹ * g * i10 * (n⁻¹ * g)⁻¹ = n⁻¹ * (g * i10 * g⁻¹) * (n⁻¹)⁻¹ := by group
    have e2 : n⁻¹ * g * i20 * (n⁻¹ * g)⁻¹ = n⁻¹ * (g * i20 * g⁻¹) * (n⁻¹)⁻¹ := by group
    rw [e1, e2, burnsideJ49B_closure_conj, inv_inv]
    exact hn

open CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_CR_U
    (huI : u ∈ I) (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z)
    {g : G} (hg : g * z0 * g⁻¹ = z) (hB : Subgroup.zpowers (g * t0 0 * g⁻¹) = B5)
    (hIg : Subgroup.closure ({g * i10 * g⁻¹, g * i20 * g⁻¹} : Set G) = I) :
    ∃ g' : G, g' * z0 * g'⁻¹ = z ∧ g' * u0 * g'⁻¹ = u ∧
      Subgroup.zpowers (g' * t0 0 * g'⁻¹) = B5 ∧
      Subgroup.closure ({g' * i10 * g'⁻¹, g' * i20 * g'⁻¹} : Set G) = I := by
  have hCg := burnsideJ49B_Cfg_conj g hC
  rw [hg] at hCg
  rw [← hIg] at huI
  rcases burnsideJ49B_I_inv hCg huI hu2 with h | h | h | h
  · exact absurd h hu1
  · exact absurd h huz
  · exact ⟨g, hg, h.symm, hB, hIg⟩
  ·
    set rg := g * r0 * g⁻¹ with hrg
    set ug := g * u0 * g⁻¹ with hug
    have hru : rg⁻¹ * ug * rg = ug * z := by
      have := hCg.r_u
      calc rg⁻¹ * ug * rg = rg⁻¹ * (ug * rg) := by group
        _ = rg⁻¹ * (rg * (ug * z)) := by rw [this]
        _ = ug * z := by group
    have hrz : rg⁻¹ * z * rg = z := by
      have := hCg.r_z
      calc rg⁻¹ * z * rg = rg⁻¹ * (z * rg) := by group
        _ = rg⁻¹ * (rg * z) := by rw [this]
        _ = z := by group
    refine ⟨rg⁻¹ * g, ?_, ?_, ?_, ?_⟩
    · calc rg⁻¹ * g * z0 * (rg⁻¹ * g)⁻¹ = rg⁻¹ * (g * z0 * g⁻¹) * rg := by group
        _ = z := by rw [hg]; exact hrz
    · calc rg⁻¹ * g * u0 * (rg⁻¹ * g)⁻¹ = rg⁻¹ * ug * rg := by rw [hug]; group
        _ = ug * z := hru
        _ = u := h.symm
    · have e : rg⁻¹ * g * t0 0 * (rg⁻¹ * g)⁻¹ = rg⁻¹ * (g * t0 0 * g⁻¹) * (rg⁻¹)⁻¹ := by group
      have hrB : CFSG.conjugate (Subgroup.zpowers (g * t0 0 * g⁻¹)) rg =
          Subgroup.zpowers (g * t0 0 * g⁻¹) := by
        have := burnsideJ49B_conj_r hCg (k := 0) (by norm_num)
        simpa using this
      rw [e, burnsideJ49B_zpowers_conj, inv_inv, hrB, hB]
    · have e1 : rg⁻¹ * g * i10 * (rg⁻¹ * g)⁻¹ = rg⁻¹ * (g * i10 * g⁻¹) * (rg⁻¹)⁻¹ := by group
      have e2 : rg⁻¹ * g * i20 * (rg⁻¹ * g)⁻¹ = rg⁻¹ * (g * i20 * g⁻¹) * (rg⁻¹)⁻¹ := by group
      have hrI := burnsideJ49B_r_normI hCg
      rw [hIg] at hrI
      rw [e1, e2, burnsideJ49B_closure_conj, inv_inv, hIg]
      exact CFSG.ASVolI.RuChoice.fx_conjugate_eq_self hrI

end CR

section Sylow2

variable {A : Type} [Group A] [Finite A]

theorem burnsideJ49B_sylow_card {K I : Subgroup A} (hK : Nat.card K = 80)
    (h : CFSG.ASVolI.ChIJK.IsSylowIn 2 I K) : Nat.card I = 16 := by
  obtain ⟨hIK, hIp, hidx⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hIp.exists_card_eq
  have hmul := CFSG.Quasithin.RuType.relIndex_mul_card_of_le hIK
  rw [hK, hn] at hmul
  have hidx' : ¬ 2 ∣ I.relIndex K := hidx
  generalize I.relIndex K = r at hmul hidx'
  have hn4 : n ≤ 4 := by
    have h1 : 2 ^ n ∣ 80 := ⟨r, by rw [← hmul, mul_comm]⟩
    by_contra hcon
    have : 2 ^ 5 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have h2 := this.trans h1
    omega
  interval_cases n
  · exfalso; apply hidx'; norm_num at hmul; omega
  · exfalso; apply hidx'; norm_num at hmul; omega
  · exfalso; apply hidx'; norm_num at hmul; omega
  · exfalso; apply hidx'; norm_num at hmul; omega
  · rw [hn]; norm_num

theorem burnsideJ49B_unique_sylow2 {b v : A} {K S1 S2 : Subgroup A} (hb5 : b ^ 5 = 1)
    (hb1 : b ≠ 1) (hbK : b ∈ K)
    (hKnorm : K ≤ Subgroup.normalizer (Subgroup.zpowers b : Set A)) (hK : Nat.card K = 80)
    (hS1 : S1 ≤ K) (hS2 : S2 ≤ K) (hc1 : Nat.card S1 = 16) (hc2 : Nat.card S2 = 16)
    (hv1 : v ∈ S1) (hv2 : v ∈ S2) (hvb : v * b * v⁻¹ = b⁻¹) (hv : v * v = 1) : S1 = S2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set P := Subgroup.zpowers b with hP
  have hPc : Nat.card P = 5 := burnsideJ49B_card_zpowers_five hb5 hb1
  have hPK : P ≤ K := Subgroup.zpowers_le.2 hbK
  have hS1P : S1 ⊓ P = ⊥ := by
    have h1 : Nat.card (S1 ⊓ P : Subgroup A) ∣ 16 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : S1 ⊓ P ≤ S1)
      rwa [hc1] at this
    have h2 : Nat.card (S1 ⊓ P : Subgroup A) ∣ 5 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : S1 ⊓ P ≤ P)
      rwa [hPc] at this
    have h3 := Nat.dvd_gcd h1 h2
    have : Nat.card (S1 ⊓ P : Subgroup A) = 1 := by simpa using h3
    exact Subgroup.card_eq_one.1 this
  have hS1norm : S1 ≤ Subgroup.normalizer (P : Set A) := hS1.trans hKnorm
  have hKeq : S1 ⊔ P = K := by
    have h := CFSG.Quasithin.RuType.card_sup_mul_inf_of_normalizes hS1norm
    rw [hS1P, Subgroup.card_bot, mul_one, hc1, hPc] at h
    refine Subgroup.eq_of_le_of_card_ge (sup_le hS1 hPK) ?_
    rw [hK, h]
  obtain ⟨n, hnK, hn⟩ := burnsideJ49B_syl_conj (p := 2) hS1 hS2
    (IsPGroup.of_card (n := 4) (by rw [hc1]; norm_num))
    (IsPGroup.of_card (n := 4) (by rw [hc2]; norm_num))
    (by
      have h := CFSG.Quasithin.RuType.relIndex_mul_card_of_le hS1
      rw [hc1, hK] at h
      have : S1.relIndex K = 5 := by omega
      rw [this]; norm_num)
    (by
      have h := CFSG.Quasithin.RuType.relIndex_mul_card_of_le hS2
      rw [hc2, hK] at h
      have : S2.relIndex K = 5 := by omega
      rw [this]; norm_num)
    (by rw [hc1, hc2])
  have hn' : n ∈ (↑(S1 ⊔ P) : Set A) := by rw [hKeq]; exact hnK
  rw [Subgroup.coe_mul_of_left_le_normalizer_right S1 P hS1norm] at hn'
  obtain ⟨s, hs, p, hp, rfl⟩ := hn'
  have hS2eq : S2 = CFSG.conjugate S1 p := by
    rw [hn, ← CFSG.ASVolI.RuChoice.fx_conjugate_conjugate,
      CFSG.ASVolI.RuChoice.fx_conjugate_eq_self (Subgroup.le_normalizer hs)]
  have hvp : p * v * p⁻¹ ∈ S1 := by
    have : v ∈ CFSG.conjugate S1 p := hS2eq ▸ hv2
    exact CFSG.ASVolI.RuChoice.fx_mem_conjugate.1 this
  have hinv : v * p * v⁻¹ = p⁻¹ := burnsideJ49B_inv_zpowers hvb hp
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have e1 : p * v * p⁻¹ = v * (p⁻¹ * p⁻¹) := by
    rw [hvi] at hinv
    have h1 : p * v = v * p⁻¹ := by
      calc p * v = (v * v) * p * v := by rw [hv, one_mul]
        _ = v * (v * p * v) := by group
        _ = v * p⁻¹ := by rw [hinv]
    calc p * v * p⁻¹ = v * p⁻¹ * p⁻¹ := by rw [h1]
      _ = v * (p⁻¹ * p⁻¹) := by group
  have hp2 : p⁻¹ * p⁻¹ ∈ S1 := by
    have h := S1.mul_mem (S1.inv_mem hv1) hvp
    rw [e1, inv_mul_cancel_left] at h
    exact h
  have hp2P : p⁻¹ * p⁻¹ ∈ P := mul_mem (inv_mem hp) (inv_mem hp)
  have hp2one : p⁻¹ * p⁻¹ = 1 := by
    have : p⁻¹ * p⁻¹ ∈ S1 ⊓ P := ⟨hp2, hp2P⟩
    rw [hS1P] at this
    exact this
  have hp5 : p ^ 5 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [← zpow_natCast, hb5]
  have hp1 : p = 1 := by
    have hpp : p * p = 1 := by
      have := congrArg (fun w => w⁻¹) hp2one
      simpa using this
    have h2 : p ^ 2 = 1 := by rw [pow_two]; exact hpp
    have := (pow_gcd_eq_one (a := p)).mpr ⟨h2, hp5⟩
    rwa [show Nat.gcd 2 5 = 1 by norm_num, pow_one] at this
  rw [hS2eq, hp1, CFSG.ASVolI.RuChoice.fx_conjugate_one]

end Sylow2

section SF1Abelian

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.J47 CFSG.QuasithinUnique CFSG.Sporadic.Schreier.Tits in
theorem burnsideJ49B_iEl_comm_iEl (p q : ℕ) :
    iEl p * iEl q = iEl q * iEl p := by
  rw [iEl_def, iEl_def]
  have h : Commute aaP abP := aaP_comm_abP
  exact ((((Commute.refl aaP).pow_pow _ _).mul_right (h.pow_pow _ _)).mul_left
    ((h.symm.pow_pow _ _).mul_right ((Commute.refl abP).pow_pow _ _))).eq

variable {G : Type} [Group G] {F1 F2 : Subgroup G}

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.J47 CFSG.QuasithinUnique CFSG.Sporadic.Schreier.Tits in
theorem burnsideJ49B_iG_comm_iG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (p q : ℕ) : iG e p * iG e q = iG e q * iG e p := by
  rw [iG, iG, ← map_mul, ← map_mul]
  exact hom1_congr e (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact burnsideJ49B_iEl_comm_iEl p q)

end SF1Abelian

section Normalize

variable {G : Type} [Group G] [Finite G]

open CFSG.Quasithin CFSG.Quasithin.RuType in
open CFSG.Quasithin.RuType.Sigma47 in
theorem burnsideJ49B_normalize
    {M : RuDataM G} (C : RuDataM.Conf47 M) {u' : G} {B5' : Subgroup G}
    (hu'F : u' ∈ C.F1) (hu'2 : u' * u' = 1) (hB5F : B5' ≤ C.F1) (hB5c : Nat.card B5' = 5)
    (hinv : ∀ x ∈ B5', u' * x * u'⁻¹ = x⁻¹) :
    ∃ h ∈ C.F1, (h * u' * h⁻¹ = C.u ∨ h * u' * h⁻¹ = C.u * M.z) ∧
      CFSG.conjugate B5' h⁻¹ = Subgroup.zpowers C.b := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxB, hx5, hx1, -⟩ := exists_gen_of_card_five hB5c
  have hxF : x ∈ C.F1 := hB5F hxB
  have hxo : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  obtain ⟨f, hfF, hfx⟩ := exists_conj_zpowers C.not_dvd_card_F1 C.b_mem hxF C.orderOf_b hxo
  obtain ⟨m, hm⟩ := exists_pow_of_mem_zpowers hfx
  have hxm : f⁻¹ * x * f = C.b ^ m := by
    rw [← hm, conj_pow]
    group
  have hbm1 : C.b ^ m ≠ 1 := by
    intro h
    apply hx1
    calc x = f * (f⁻¹ * x * f) * f⁻¹ := by group
      _ = 1 := by rw [hxm, h]; group
  set u'' := f⁻¹ * u' * f with hu''def
  have hu''bm : u'' * C.b ^ m * u''⁻¹ = (C.b ^ m)⁻¹ := by
    rw [← hxm]
    have h := hinv x hxB
    calc u'' * (f⁻¹ * x * f) * u''⁻¹ = f⁻¹ * (u' * x * u'⁻¹) * f := by rw [hu''def]; group
      _ = f⁻¹ * x⁻¹ * f := by rw [h]
      _ = (f⁻¹ * x * f)⁻¹ := by group
  obtain ⟨r, hr⟩ := RuDataM.Conf47.exists_pow_pow_eq C.b_pow_five hbm1
  have hu''b : u'' * C.b * u''⁻¹ = C.b⁻¹ := by
    calc u'' * C.b * u''⁻¹ = u'' * (C.b ^ m) ^ r * u''⁻¹ := by rw [hr]
      _ = (u'' * C.b ^ m * u''⁻¹) ^ r := by rw [conj_pow]
      _ = ((C.b ^ m)⁻¹) ^ r := by rw [hu''bm]
      _ = ((C.b ^ m) ^ r)⁻¹ := by rw [inv_pow]
      _ = C.b⁻¹ := by rw [hr]
  have hu''F : u'' ∈ C.F1 := mul_mem (mul_mem (inv_mem hfF) hu'F) hfF
  have hu''2 : u'' * u'' = 1 := by
    calc u'' * u'' = f⁻¹ * (u' * u') * f := by rw [hu''def]; group
      _ = 1 := by rw [hu'2]; group
  have hu''N : u'' ∈ C.NF1 := ⟨hu''F, RuDataM.mem_normalizer_of_inv hu''b⟩
  obtain ⟨n, hnN, hnS⟩ := exists_conj_mem_of_sylow (inf_le_left : C.SF1 ≤ C.NF1) C.isPGroup_SF1
    (by rw [C.relIndex_SF1]; norm_num) hu''N (by rw [pow_two]; exact hu''2)
  have hs2 : (n⁻¹ * u'' * n) * (n⁻¹ * u'' * n) = 1 := by
    calc (n⁻¹ * u'' * n) * (n⁻¹ * u'' * n) = n⁻¹ * (u'' * u'') * n := by group
      _ = 1 := by rw [hu''2]; group
  obtain ⟨p, hp, hpe⟩ := C.exists_iEl_eq hnS
  have hi := C.iEl_inv p hp (by rw [hpe]; exact hs2)
  rw [hpe] at hi
  have hnF : n ∈ C.F1 := hnN.1
  refine ⟨n⁻¹ * f⁻¹, mul_mem (inv_mem hnF) (inv_mem hfF), ?_, ?_⟩
  · have hconj : (n⁻¹ * f⁻¹) * u' * (n⁻¹ * f⁻¹)⁻¹ = n⁻¹ * u'' * n := by rw [hu''def]; group
    rw [hconj]
    rcases hi with h | h | h | h
    · exfalso
      apply C.b_ne_inv
      have hu''1 : u'' = 1 := by
        calc u'' = n * (n⁻¹ * u'' * n) * n⁻¹ := by group
          _ = 1 := by rw [h]; group
      rw [← hu''b, hu''1]
      group
    · exfalso
      apply C.b_ne_inv
      have hzn : M.z * n = n * M.z := M.Z_comm_H M.z_mem_Z (C.F1_le_H hnF)
      have hu''z : u'' = M.z := by
        calc u'' = n * (n⁻¹ * u'' * n) * n⁻¹ := by group
          _ = n * M.z * n⁻¹ := by rw [h]
          _ = (M.z * n) * n⁻¹ := by rw [hzn]
          _ = M.z := by group
      calc C.b = C.b * M.z * M.z⁻¹ := by group
        _ = M.z * C.b * M.z⁻¹ := by rw [C.b_comm_z]
        _ = u'' * C.b * u''⁻¹ := by rw [hu''z]
        _ = C.b⁻¹ := hu''b
    · exact Or.inl h
    · exact Or.inr h
  ·
    have hB5eq : Subgroup.zpowers x = B5' := zpowers_eq_of_card_five hB5c hxB hx5 hx1
    have hbcard : Nat.card (Subgroup.zpowers C.b) = 5 := by
      rw [Nat.card_zpowers, C.orderOf_b]
    have hbm5 : (C.b ^ m) ^ 5 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, C.b_pow_five, one_pow]
    have hzp : Subgroup.zpowers (C.b ^ m) = Subgroup.zpowers C.b :=
      zpowers_eq_of_card_five hbcard (pow_mem (Subgroup.mem_zpowers C.b) _) hbm5 hbm1
    have h1 : CFSG.conjugate B5' f = Subgroup.zpowers C.b := by
      rw [← hB5eq, CFSG.ASVolI.RuChoice.fx_conjugate_zpowers, hxm, hzp]
    have hnb : n ∈ Subgroup.normalizer (Subgroup.zpowers C.b : Set G) := hnN.2
    rw [show (n⁻¹ * f⁻¹)⁻¹ = f * n by group, ← CFSG.ASVolI.RuChoice.fx_conjugate_conjugate, h1]
    exact CFSG.ASVolI.RuChoice.fx_conjugate_eq_self hnb

end Normalize

section Conj

variable {G : Type} [Group G]

open CFSG.Quasithin CFSG.Quasithin.RuType in
theorem burnsideJ49B_conjugate_inf (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊓ B) g = CFSG.conjugate A g ⊓ CFSG.conjugate B g := by
  unfold CFSG.conjugate
  exact Subgroup.map_inf A B _ (MulAut.conj g⁻¹).injective

end Conj

section IFacts

open CFSG.Quasithin CFSG.Quasithin.RuType in
open CFSG.ASVolI.ChIJK in
theorem burnsideJ49B_I_facts {G : Type} [Group G] [Finite G]
    {L V T V2 B5 X : Subgroup G} {g v a z u : G} {I : Subgroup G}
    (hS : RuUSetup G L V T V2 B5 X g v a z u I) :
    I ≤ Subgroup.normalizer (B5 : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ∧
      (∀ a ∈ I, ∀ b ∈ I, a * b = b * a) ∧ Nat.card I = 16 := by
  have hRu := hS.setup.ru
  obtain ⟨M, y, -, hMT, hyT, -, -, -, -, -, -, hF1, -, -⟩ :=
    RuChoice.reduce hRu hS.setup.v2 hS.setup.g_mem.1 hS.setup.g_mem.2 hS.setup.v_mem.1
      hS.setup.v_mem.2 hS.setup.b5.1 hS.setup.b5.2 hS.setup.x3 hS.setup.a_choice
      hS.setup.a_norm hS.setup.q5_norm
  have hMT' : M.T = hRu.sylowT := Sylow.ext (hMT.trans hRu.coe_sylowT.symm)
  have hH : Nat.card (HRu T) = 2 ^ 11 * 120 := by
    rw [hRu.HRu_eq_ruH, ← hMT']
    exact M.toRuData.card_H
  have hzM : z = M.z := by
    refine burnsideJ410_eq_z M ?_
    rw [hMT', ← hRu.ZRu_eq_ruZ]
    exact hS.z_gen
  have hz2 : z * z = 1 := by rw [hzM]; exact M.z_mul_self
  have hB5c : Nat.card B5 = 5 := burnsideJ410_card_five hH hS.setup.b5.1
  obtain ⟨h, -, hu⟩ := hS.u_x4
  have hu2 : u * u = 1 := by
    rw [hu]
    have e : (h : G) * z * (h : G)⁻¹ * ((h : G) * z * (h : G)⁻¹) =
        (h : G) * (z * z) * (h : G)⁻¹ := by group
    rw [e, hz2]
    group
  have huF1 : u ∈ F1Ru L V V2 T a B5 := by
    unfold F1Ru
    exact Subgroup.mem_sup_left hS.u_TF
  have hB5F1 : B5 ≤ F1Ru L V V2 T a B5 := by
    unfold F1Ru
    exact le_sup_right
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hB5u : ∀ x ∈ B5, u * x * u⁻¹ = x⁻¹ := by
    intro x hx
    have h1 := hS.u_inv.2 x hx
    rw [hui] at h1 ⊢
    exact h1
  have hRuT : CFSG.Quasithin.RuType.IsTypeRu G := ⟨M.L, M.one, M.T, M.two⟩
  obtain ⟨e⟩ := CFSG.Quasithin.RuType.J47.exists_amalgamIso_of_case2F4
    (M.case2F4 CFSG.Quasithin.Fan86.hayashiFiveThree_proved'
      (CFSG.Quasithin.RuType.isQuasithinSub_of_isTypeRu hRuT _))
  obtain ⟨C, hCF1, hCcomm⟩ : ∃ C : RuDataM.Conf47 M, C.F1 = M.F1 ∧
      ∀ p q, C.iEl p * C.iEl q = C.iEl q * C.iEl p :=
    ⟨M.conf47 e, rfl, fun p q => burnsideJ49B_iG_comm_iG e p q⟩
  have hzF : M.z ∈ C.F1 := by
    rw [hCF1]
    exact M.Agrp_le_F1 (M.W_le_Agrp (M.U_le_W (M.V_le_U M.z_mem_V)))
  have hyT' : y ∈ (M.T : Subgroup G) := by rw [hMT]; exact hyT
  have hyz : y * M.z = M.z * y :=
    (M.Z_comm_H M.z_mem_Z (M.toRuData.T_le_H hyT')).symm
  have huC : u ∈ CFSG.conjugate M.F1 y := by rw [← hF1]; exact huF1
  have hB5C : B5 ≤ CFSG.conjugate M.F1 y := by rw [← hF1]; exact hB5F1
  have hu'F : y * u * y⁻¹ ∈ C.F1 := by
    rw [hCF1]; exact CFSG.ASVolI.RuChoice.fx_mem_conjugate.mp huC
  have hu'2 : (y * u * y⁻¹) * (y * u * y⁻¹) = 1 := by
    calc (y * u * y⁻¹) * (y * u * y⁻¹) = y * (u * u) * y⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hB5'F : CFSG.conjugate B5 y⁻¹ ≤ C.F1 := by
    rw [hCF1]
    intro x hx
    have h1 : y⁻¹ * x * y ∈ B5 := by
      have := CFSG.ASVolI.RuChoice.fx_mem_conjugate.mp hx
      simpa using this
    have h2 := CFSG.ASVolI.RuChoice.fx_mem_conjugate.mp (hB5C h1)
    have e : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
    rwa [e] at h2
  have hB5'c : Nat.card (CFSG.conjugate B5 y⁻¹) = 5 := by
    rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hB5c
  have hinv' : ∀ x ∈ CFSG.conjugate B5 y⁻¹, (y * u * y⁻¹) * x * (y * u * y⁻¹)⁻¹ = x⁻¹ := by
    intro x hx
    have h1 : y⁻¹ * x * y ∈ B5 := by
      have := CFSG.ASVolI.RuChoice.fx_mem_conjugate.mp hx
      simpa using this
    have h := hB5u _ h1
    calc (y * u * y⁻¹) * x * (y * u * y⁻¹)⁻¹ = y * (u * (y⁻¹ * x * y) * u⁻¹) * y⁻¹ := by group
      _ = y * (y⁻¹ * x * y)⁻¹ * y⁻¹ := by rw [h]
      _ = x⁻¹ := by group
  obtain ⟨h', hh'F, hh'u, hh'B⟩ := burnsideJ49B_normalize C hu'F hu'2 hB5'F hB5'c hinv'
  set G0 : G := h' * y with hG0
  have hB5G0 : CFSG.conjugate B5 G0⁻¹ = Subgroup.zpowers C.b := by
    have : CFSG.conjugate B5 G0⁻¹ = CFSG.conjugate (CFSG.conjugate B5 y⁻¹) h'⁻¹ := by
      rw [CFSG.ASVolI.RuChoice.fx_conjugate_conjugate]
      congr 1
      rw [hG0]
      group
    rw [this]
    exact hh'B
  have hF1G0 : CFSG.conjugate (F1Ru L V V2 T a B5) G0⁻¹ = C.F1 := by
    rw [hF1, CFSG.ASVolI.RuChoice.fx_conjugate_conjugate]
    have e1 : y * G0⁻¹ = h'⁻¹ := by rw [hG0]; group
    rw [e1, ← hCF1]
    exact CFSG.ASVolI.RuChoice.fx_conjugate_eq_self (Subgroup.le_normalizer (inv_mem hh'F))
  have hKconj : CFSG.conjugate (F1Ru L V V2 T a B5 ⊓ Subgroup.normalizer (B5 : Set G)) G0⁻¹ =
      C.NF1 := by
    rw [burnsideJ49B_conjugate_inf, hF1G0, ← CFSG.ASVolI.RuChoice.fx_normalizer_conjugate,
      hB5G0]
  have hK80 : Nat.card ↥(F1Ru L V V2 T a B5 ⊓ Subgroup.normalizer (B5 : Set G)) = 80 := by
    have := CFSG.ASVolI.RuChoice.fx_card_conjugate
      (F1Ru L V V2 T a B5 ⊓ Subgroup.normalizer (B5 : Set G)) G0⁻¹
    rw [hKconj, C.card_NF1] at this
    exact this.symm
  have hIc : Nat.card I = 16 := burnsideJ49B_sylow_card hK80 hS.I_syl.1
  set I'' := CFSG.conjugate I G0⁻¹ with hI''
  have hI''le : I'' ≤ C.NF1 := by
    rw [← hKconj]
    exact CFSG.ASVolI.RuChoice.fx_conjugate_mono G0⁻¹ hS.I_syl.1.1
  have hI''c : Nat.card I'' = 16 := by
    rw [hI'', CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hIc
  have hv : G0 * u * G0⁻¹ = C.u ∨ G0 * u * G0⁻¹ = C.u * M.z := by
    have : G0 * u * G0⁻¹ = h' * (y * u * y⁻¹) * h'⁻¹ := by rw [hG0]; group
    rw [this]
    exact hh'u
  have hvI'' : G0 * u * G0⁻¹ ∈ I'' := by
    rw [hI'', CFSG.ASVolI.RuChoice.fx_mem_conjugate]
    have : G0⁻¹ * (G0 * u * G0⁻¹) * (G0⁻¹)⁻¹ = u := by group
    rw [this]
    exact hS.I_syl.2
  have hvS : G0 * u * G0⁻¹ ∈ C.SF1 ∧ (G0 * u * G0⁻¹) * C.b * (G0 * u * G0⁻¹)⁻¹ = C.b⁻¹ ∧
      (G0 * u * G0⁻¹) * (G0 * u * G0⁻¹) = 1 := by
    rcases hv with h1 | h1
    · rw [h1]
      exact ⟨burnsideJ410_u_mem_SF1 C, C.u_inv_b, C.u_mul_self⟩
    · rw [h1]
      have hbz : C.b * M.z = M.z * C.b := C.b_comm_z
      have huz : C.u * M.z = M.z * C.u := C.u_comm_z
      refine ⟨mul_mem (burnsideJ410_u_mem_SF1 C) (burnsideJ410_z_mem_SF1 C hzF), ?_, ?_⟩
      · have hzi : M.z⁻¹ = M.z := M.z_inv47
        calc C.u * M.z * C.b * (C.u * M.z)⁻¹ = C.u * (M.z * C.b * M.z⁻¹) * C.u⁻¹ := by group
          _ = C.u * C.b * C.u⁻¹ := by rw [← hbz]; group
          _ = C.b⁻¹ := C.u_inv_b
      · calc C.u * M.z * (C.u * M.z) = C.u * (M.z * C.u) * M.z := by group
          _ = C.u * (C.u * M.z) * M.z := by rw [huz]
          _ = (C.u * C.u) * (M.z * M.z) := by group
          _ = 1 := by rw [C.u_mul_self, M.z_mul_self]; group
  have hb1 : C.b ≠ 1 := fun h1 => by
    have := C.orderOf_b
    rw [h1, orderOf_one] at this
    omega
  have hI''eq : I'' = C.SF1 :=
    burnsideJ49B_unique_sylow2 C.b_pow_five hb1
      (Subgroup.zpowers_le.1 C.zpowers_b_le_NF1) (fun x hx => hx.2) C.card_NF1 hI''le inf_le_left
      hI''c C.card_SF1 hvI'' hvS.1 hvS.2.1 hvS.2.2
  refine ⟨?_, ?_, hIc⟩
  · intro x hx
    refine ⟨(hS.I_syl.1.1 hx).2, ?_⟩
    have hf : x ∈ F1Ru L V V2 T a B5 := (hS.I_syl.1.1 hx).1
    rw [hF1, CFSG.ASVolI.RuChoice.fx_mem_conjugate] at hf
    have h1 : (y * x * y⁻¹) * M.z = M.z * (y * x * y⁻¹) :=
      (M.Z_comm_H M.z_mem_Z (M.F1_le_H hf)).symm
    have hy' : y⁻¹ * M.z * y = M.z := by
      calc y⁻¹ * M.z * y = y⁻¹ * (M.z * y) := by group
        _ = y⁻¹ * (y * M.z) := by rw [hyz]
        _ = M.z := by group
    have hxz : x * M.z = M.z * x := by
      calc x * M.z = x * (y⁻¹ * M.z * y) := by rw [hy']
        _ = y⁻¹ * ((y * x * y⁻¹) * M.z) * y := by group
        _ = y⁻¹ * (M.z * (y * x * y⁻¹)) * y := by rw [h1]
        _ = (y⁻¹ * M.z * y) * x := by group
        _ = M.z * x := by rw [hy']
    rw [hzM]
    exact Subgroup.mem_centralizer_singleton_iff.2 hxz
  · intro a ha b hb
    have ha' : G0 * a * G0⁻¹ ∈ C.SF1 := by
      rw [← hI''eq, hI'', CFSG.ASVolI.RuChoice.fx_mem_conjugate]
      have : G0⁻¹ * (G0 * a * G0⁻¹) * (G0⁻¹)⁻¹ = a := by group
      rw [this]; exact ha
    have hb' : G0 * b * G0⁻¹ ∈ C.SF1 := by
      rw [← hI''eq, hI'', CFSG.ASVolI.RuChoice.fx_mem_conjugate]
      have : G0⁻¹ * (G0 * b * G0⁻¹) * (G0⁻¹)⁻¹ = b := by group
      rw [this]; exact hb
    obtain ⟨p, -, hp⟩ := C.exists_iEl_eq ha'
    obtain ⟨q, -, hq⟩ := C.exists_iEl_eq hb'
    have hc := hCcomm p q
    rw [hp, hq] at hc
    calc a * b = G0⁻¹ * ((G0 * a * G0⁻¹) * (G0 * b * G0⁻¹)) * G0 := by group
      _ = G0⁻¹ * ((G0 * b * G0⁻¹) * (G0 * a * G0⁻¹)) * G0 := by rw [hc]
      _ = b * a := by group

end IFacts

section NFacts

open CFSG.Quasithin CFSG.Quasithin.RuType in
open CFSG.ASVolI.ChIJK in
theorem burnsideJ49B_N_facts {G : Type} [Group G] [Finite G]
    {L V T V2 B5 X : Subgroup G} {g v a z u : G} {I : Subgroup G}
    (hS : RuUSetup G L V T V2 B5 X g v a z u I) :
    ∃ R : Subgroup G, R ≤ Subgroup.normalizer (B5 : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ∧
      Nat.card R = 32 ∧ Nonempty (↥R ≃* WreathedTwoGroup 2) ∧
      Nat.card ↥(Subgroup.normalizer (B5 : Set G) ⊓ Subgroup.centralizer ({z} : Set G)) ∣ 160 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRu := hS.setup.ru
  obtain ⟨hL, hB5X, hcent⟩ := burnsideJ410_Loc_of_setup hS
  have hB5c : Nat.card B5 = 5 := hB5X.1
  have hB5z : B5 ≤ Subgroup.centralizer ({z} : Set G) := burnsideJ410_le_centralizer_of_cent hcent
  have hLS : burnsideJ410_LS z z B5 := hL.LS z B5 (IsConj.refl z) hB5c hB5z
  obtain ⟨R, hNR, -, -, ⟨ψ⟩, -, hzc⟩ := as_J_3_6 G L V T hRu z hS.z_gen B5 hS.setup.b5.1
  set P := PFstar B5 with hP
  set NB := Subgroup.normalizer (B5 : Set G) with hNB
  set N := NB ⊓ Subgroup.centralizer ({z} : Set G) with hN
  have hPc : Nat.card P = 125 := hLS.card_P
  have hPNB : P ≤ NB := Subgroup.map_subtype_le _
  have hRNB : R ≤ NB := by rw [hNR]; exact le_sup_right
  have hnormP : ∀ n ∈ NB, n ∈ Subgroup.normalizer (P : Set G) := fun n hn =>
    CFSG.ASVolI.RuChoice.mem_normalizer fun x hx => hLS.norm n hn x hx
  have hRc : Nat.card R = 32 := by
    rw [Nat.card_congr ψ.toEquiv]
    exact burnsideJ49B_W_card
  have hRN : R ≤ N := fun r hr =>
    ⟨hRNB hr, Subgroup.mem_centralizer_singleton_iff.2 (hzc r hr)⟩
  refine ⟨R, hRN, hRc, ⟨ψ⟩, ?_⟩
  have hRP : R ⊓ P = ⊥ := by
    have h1 : Nat.card (R ⊓ P : Subgroup G) ∣ 32 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : R ⊓ P ≤ R)
      rwa [hRc] at this
    have h2 : Nat.card (R ⊓ P : Subgroup G) ∣ 125 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : R ⊓ P ≤ P)
      rwa [hPc] at this
    have h3 := Nat.dvd_gcd h1 h2
    have : Nat.card (R ⊓ P : Subgroup G) = 1 := by simpa using h3
    exact Subgroup.card_eq_one.1 this
  have hNB4000 : Nat.card NB = 4000 := by
    have h := CFSG.Quasithin.RuType.card_sup_mul_inf_of_normalizes (fun r hr => hnormP r (hRNB hr) : R ≤ Subgroup.normalizer (P : Set G))
    rw [hRP, Subgroup.card_bot, mul_one, hRc, hPc] at h
    have e : NB = R ⊔ P := hNR.trans (sup_comm _ _)
    rw [e, h]
  have hNP : N ⊓ P ≤ B5 := by
    intro x hx
    obtain ⟨⟨-, hxz⟩, hxP⟩ := hx
    have hxc : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 hxz
    have h1 := hLS.inv_mod x hxP
    have hzx : z * x * z⁻¹ = x := by
      calc z * x * z⁻¹ = (x * z) * z⁻¹ := by rw [← hxc]
        _ = x := by group
    rw [hzx] at h1
    have h5 := hLS.exp x hxP
    have e : x = (x * x) ^ 3 := by
      calc x = x ^ 5 * x := by rw [h5, one_mul]
        _ = x ^ 6 := by rw [← pow_succ]
        _ = (x ^ 2) ^ 3 := by rw [← pow_mul]
        _ = (x * x) ^ 3 := by rw [pow_two]
    rw [e]
    exact Subgroup.pow_mem _ h1 3
  have hNnorm : N ≤ Subgroup.normalizer (P : Set G) := fun n hn => hnormP n hn.1
  have hsup : Nat.card ↥(N ⊔ P) ∣ 4000 := by
    have := Subgroup.card_dvd_of_le (sup_le (inf_le_left : N ≤ NB) hPNB)
    rwa [hNB4000] at this
  have hinf : Nat.card ↥(N ⊓ P) ∣ 5 := by
    have := Subgroup.card_dvd_of_le hNP
    rwa [hB5c] at this
  have hprod := CFSG.Quasithin.RuType.card_sup_mul_inf_of_normalizes hNnorm
  rw [hPc] at hprod
  have h20000 : Nat.card N * 125 ∣ 160 * 125 := by
    rw [← hprod]
    have := Nat.mul_dvd_mul hsup hinf
    simpa using this
  exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h20000

end NFacts

section CRMain

variable {G : Type} [Group G] [Finite G] {t0 : ℕ → G} {z0 y0 u0 i10 i20 r0 s0 : G}
  (hC : CFSG.Sporadic.RuSchreier.J49.Cfg t0 z0 y0 u0 i10 i20 r0 s0)
  {z u : G} {B5 I N R : Subgroup G}
include hC

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_CR (hz : IsConj z0 z)
    (hK25 : ¬ 5 ^ 2 ∣ Nat.card (Subgroup.centralizer ({z} : Set G)))
    (hB5c : Nat.card B5 = 5) (hB5z : B5 ≤ Subgroup.centralizer ({z} : Set G))
    (hNdef : N = Subgroup.normalizer (B5 : Set G) ⊓ Subgroup.centralizer ({z} : Set G))
    (hR : R ≤ N) (hRc : Nat.card R = 32) (hRW : Nonempty (↥R ≃* WreathedTwoGroup 2))
    (hN160 : Nat.card N ∣ 160)
    (hIN : I ≤ N) (hIab : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a) (hIc : Nat.card I = 16)
    (huI : u ∈ I) (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z) :
    ∃ g : G, g * z0 * g⁻¹ = z ∧ g * u0 * g⁻¹ = u ∧
      Subgroup.zpowers (g * t0 0 * g⁻¹) = B5 ∧
      Subgroup.closure ({g * i10 * g⁻¹, g * i20 * g⁻¹} : Set G) = I := by
  obtain ⟨g1, hg1⟩ := isConj_iff.1 hz
  obtain ⟨g2, hg2z, hg2B⟩ := burnsideJ49B_CR_B hC hK25 hB5c hB5z hg1
  obtain ⟨g3, hg3z, hg3B, hg3I⟩ :=
    burnsideJ49B_CR_I hC hNdef hR hRc hRW hN160 hIN hIab hIc hg2z hg2B
  exact burnsideJ49B_CR_U hC huI hu2 hu1 huz hg3z hg3B hg3I

end CRMain

section Final

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_isConj_P
    {G : Type} [Group G] (ζ : ↥ruP ≃* G) {z y0 : G}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hy3 : y0 ^ 3 = 1) (hy1 : y0 ≠ 1)
    (hyz : y0 * z = z * y0) :
    IsConj (ζ (burnsideJ49B_gelP 12)) z := by
  have hcfg := burnsideJ49B_cfgP
  obtain ⟨c1, hc1⟩ := burnsideJ49B_involution_class hcfg.z_sq hcfg.z_ne hcfg.y_cube hcfg.y_ne
    hcfg.y_comm
  have ht2 : ζ.symm z * ζ.symm z = 1 := by rw [← map_mul, hz2, map_one]
  have ht1 : ζ.symm z ≠ 1 := fun h => hz1 (by simpa using congrArg ζ h)
  have hy3' : (ζ.symm y0) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hy1' : ζ.symm y0 ≠ 1 := fun h => hy1 (by simpa using congrArg ζ h)
  have hyt : ζ.symm y0 * ζ.symm z = ζ.symm z * ζ.symm y0 := by
    rw [← map_mul, ← map_mul, hyz]
  obtain ⟨c2, hc2⟩ := burnsideJ49B_involution_class ht2 ht1 hy3' hy1' hyt
  have hconj : IsConj (burnsideJ49B_gelP 12) (ζ.symm z) := by
    refine isConj_iff.2 ⟨c2 * c1⁻¹, ?_⟩
    apply Subtype.ext
    have e1 : (burnsideJ49B_gelP 12 : Equiv.Perm (Fin 4060)) = (c1 : Equiv.Perm (Fin 4060)) * ruZ * (c1 : Equiv.Perm (Fin 4060))⁻¹ := hc1.symm
    show (c2 : Equiv.Perm (Fin 4060)) * (c1 : Equiv.Perm (Fin 4060))⁻¹ * (burnsideJ49B_gelP 12 : Equiv.Perm (Fin 4060)) * ((c2 : Equiv.Perm (Fin 4060)) * (c1 : Equiv.Perm (Fin 4060))⁻¹)⁻¹ = (ζ.symm z : Equiv.Perm (Fin 4060))
    rw [e1, ← hc2]
    group
  have := (isConj_iff.1 hconj)
  obtain ⟨c, hc⟩ := this
  refine isConj_iff.2 ⟨ζ c, ?_⟩
  have := congrArg ζ hc
  simpa using this

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.J49 in
theorem burnsideJ49B_sl2_P :
    CFSG.Quasithin.IsSL2 5
      ↥(Subgroup.zpowers (burnsideJ49B_gelP 0) ⊔ Subgroup.zpowers (burnsideJ49B_gelP 3)) := by
  obtain ⟨e⟩ := Sl2.exists_equiv_sl2
  have hmap : (Subgroup.zpowers (burnsideJ49B_gelP 0) ⊔ Subgroup.zpowers (burnsideJ49B_gelP 3)).map
      ruP.subtype = Subgroup.zpowers (gel 0) ⊔ Subgroup.zpowers (gel 3) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  exact ⟨(Subgroup.equivMapOfInjective _ ruP.subtype Subtype.val_injective).trans
    ((MulEquiv.subgroupCongr hmap).trans e)⟩

end Final

section Target

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.J49 in
open CFSG.ASVolI.ChIJK in
theorem as_J_4_9 : J_4_9 := by
  intro G _ _ L V T V2 B5 X g v a z u I hS
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRu := hS.setup.ru
  obtain ⟨hL, hB5X, hcent⟩ := burnsideJ410_Loc_of_setup hS
  obtain ⟨hIN, hIab, hIc⟩ := burnsideJ49B_I_facts hS
  obtain ⟨R, hRN, hRc, hRW, hN160⟩ := burnsideJ49B_N_facts hS
  have hB5c : Nat.card B5 = 5 := hB5X.1
  have hB5z : B5 ≤ Subgroup.centralizer ({z} : Set G) := burnsideJ410_le_centralizer_of_cent hcent
  obtain ⟨M, -, hMT⟩ := hRu.exists_ruDataM CFSG.Quasithin.RuType.stUnique
  have hH : Nat.card (HRu T) = 2 ^ 11 * 120 := by
    rw [hRu.HRu_eq_ruH, ← hMT]
    exact M.toRuData.card_H
  have hzM : z = M.z := by
    refine burnsideJ410_eq_z M ?_
    rw [hMT, ← hRu.ZRu_eq_ruZ]
    exact hS.z_gen
  have hCz : Nat.card ↥(Subgroup.centralizer ({z} : Set G)) = 2 ^ 11 * 120 := by
    rw [hzM, ← burnsideJ410_H_eq M]
    exact M.toRuData.card_H
  have hK25 : ¬ 5 ^ 2 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set G)) := by
    rw [hCz]; norm_num
  obtain ⟨x3, hx3⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer ({z} : Set G))) 3 (by rw [hCz]; norm_num)
  have hy3 : (x3 : G) ^ 3 = 1 := by
    have := pow_orderOf_eq_one x3
    rw [hx3] at this
    exact congrArg Subtype.val this
  have hy1 : (x3 : G) ≠ 1 := fun h => by
    have : x3 = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx3
    omega
  have hyz : (x3 : G) * z = z * (x3 : G) := Subgroup.mem_centralizer_singleton_iff.1 x3.2
  have hRuT : CFSG.Quasithin.RuType.IsTypeRu G := ⟨M.L, M.one, M.T, M.two⟩
  obtain ⟨ψ⟩ := CFSG.Quasithin.RuType.theorem_J11 CFSG.Quasithin.Fan86.hayashiFiveThree_proved'
    CFSG.Quasithin.H13.F45Ru.f45TwoF4 CFSG.Quasithin.H13.TwoF4F48.f48TwoF4 G hRuT
  let ζ : ↥ruP ≃* G := (ψ.trans ruEquivP).symm
  have hz : IsConj (ζ (burnsideJ49B_gelP 12)) z :=
    burnsideJ49B_isConj_P ζ hL.z_sq hL.z_ne hy3 hy1 hyz
  have hCfgζ : Cfg (fun k => ζ (burnsideJ49B_gelP k)) (ζ (burnsideJ49B_gelP 12))
      (ζ (burnsideJ49B_gelP 13)) (ζ (burnsideJ49B_gelP 16)) (ζ (burnsideJ49B_gelP 14))
      (ζ (burnsideJ49B_gelP 15)) (ζ (burnsideJ49B_gelP 17)) (ζ (burnsideJ49B_gelP 18)) := by
    refine Cfg.of_inj ζ.symm.toMonoidHom ζ.symm.injective ?_
    simpa using burnsideJ49B_cfgP
  have hu2 : u * u = 1 := hL.u_sq
  have hu1 : u ≠ 1 := burnsideJ410_u_ne_one hL
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hu_inv : ∀ x ∈ B5, u * x * u⁻¹ = x⁻¹ := by
    intro x hx
    have h1 := hS.u_inv.2 x hx
    rw [hui] at h1 ⊢
    exact h1
  have huI : u ∈ I := hS.I_syl.2
  obtain ⟨g0, hg0z, hg0u, hg0B, hg0I⟩ := burnsideJ49B_CR hCfgζ hz hK25 hB5c hB5z rfl hRN hRc hRW
    hN160 hIN hIab hIc huI hu2 hu1 hL.u_ne
  have hCfinal := burnsideJ49B_Cfg_conj g0 hCfgζ
  rw [hg0z, hg0u] at hCfinal
  have hSL0 : CFSG.Quasithin.IsSL2 5
      ↥(Subgroup.zpowers (g0 * ζ (burnsideJ49B_gelP 0) * g0⁻¹) ⊔
        Subgroup.zpowers (g0 * ζ (burnsideJ49B_gelP 3) * g0⁻¹)) := by
    have := burnsideJ49B_isSL2_map_pair ((MulAut.conj g0).toMonoidHom.comp ζ.toMonoidHom)
      ((MulAut.conj g0).injective.comp ζ.injective) (burnsideJ49B_gelP 0) (burnsideJ49B_gelP 3)
      burnsideJ49B_sl2_P
    have e0 : ((MulAut.conj g0).toMonoidHom.comp ζ.toMonoidHom) (burnsideJ49B_gelP 0) =
        g0 * ζ (burnsideJ49B_gelP 0) * g0⁻¹ := by simp [MulAut.conj_apply]
    have e3 : ((MulAut.conj g0).toMonoidHom.comp ζ.toMonoidHom) (burnsideJ49B_gelP 3) =
        g0 * ζ (burnsideJ49B_gelP 3) * g0⁻¹ := by simp [MulAut.conj_apply]
    rw [e0, e3] at this
    exact this
  have hK : ∀ n : G, n ∈ Subgroup.normalizer (B5 : Set G) → n * z = z * n → n * u = u * n →
      n ∈ I := by
    intro n hn hnz hnu
    exact burnsideJ49B_K hL.z_sq hu2 hL.u_ne hL.z_ne hu1 hL.comm rfl hB5c hB5z hRN hRc hRW hN160
      hIN hIab hIc huI hu_inv n ⟨hn, Subgroup.mem_centralizer_singleton_iff.2 hnz⟩ hnu
  exact burnsideJ49B_main' hCfinal (burnsideJ49B_hLS hL) hL.conj_u hL.conj_uz
    (burnsideJ49B_hnbr hL) hSL0 hg0B.symm hg0I.symm hK

end Target

end CFSG.ASVolI
