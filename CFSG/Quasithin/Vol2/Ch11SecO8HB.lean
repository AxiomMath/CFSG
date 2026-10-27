module

public import CFSG.Quasithin.Vol2.Ch5Sec1Hall
public import CFSG.Quasithin.Vol2.Ch11SecO8HA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Quasithin

namespace O8H

variable {G : Type} [Group G]

theorem relIndex_sup_eq {A B : Subgroup G} (h : A ≤ Subgroup.normalizer (B : Set G)) :
    B.relIndex (A ⊔ B) = B.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B h).toEquiv.symm

theorem sup_inf_eq_of_le_normalizer {P C W : Subgroup G} (hPW : P ≤ W)
    (hC : C ≤ Subgroup.normalizer (P : Set G)) : P ⊔ (C ⊓ W) = (P ⊔ C) ⊓ W := by
  refine le_antisymm (sup_le (le_inf le_sup_left hPW)
    (inf_le_inf_right W le_sup_right)) fun g hg => ?_
  obtain ⟨hgPC, hgW⟩ := hg
  have h1 : (g : G) ∈ ((P ⊔ C : Subgroup G) : Set G) := hgPC
  rw [Subgroup.coe_mul_of_right_le_normalizer_left P C hC] at h1
  obtain ⟨p, hp, c, hc, rfl⟩ := h1
  have hcW : c ∈ W := by
    have := W.mul_mem (W.inv_mem (hPW hp)) hgW
    simpa using this
  exact Subgroup.mul_mem_sup hp ⟨hc, hcW⟩

theorem inf_eq_bot_of_odd [Finite G] {P D : Subgroup G} (hP : IsPGroup 2 P)
    (hD : Odd (Nat.card D)) : P ⊓ D = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
  have hcop : Nat.Coprime (Nat.card P) (Nat.card D) := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hD)
  exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot

theorem coprime_of_odd [Finite G] {P Q : Subgroup G} (hP : IsPGroup 2 P)
    (h : Odd (P.relIndex Q)) : Nat.Coprime (Nat.card P) (P.relIndex Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
  rw [hk]
  exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr h)

theorem odd_relIndex_sup [Finite G] {A B : Subgroup G} (h : A ≤ Subgroup.normalizer (B : Set G))
    (hA : Odd (Nat.card A)) : Odd (B.relIndex (A ⊔ B)) := by
  rw [relIndex_sup_eq h]
  exact hA.of_dvd_nat (Subgroup.relIndex_dvd_card B A)

theorem complement_conj {P Q C : Subgroup G} {v : G} (hv : v ∈ P) (hPQ : P ≤ Q)
    (hQN : Q ≤ Subgroup.normalizer (P : Set G)) (hC : C ≤ Q) (hPC : P ⊓ C = ⊥)
    (hPCs : P ⊔ C = Q) :
    C.map (MulAut.conj v).toMonoidHom ≤ Q ∧ P ⊓ C.map (MulAut.conj v).toMonoidHom = ⊥ ∧
      P ⊔ C.map (MulAut.conj v).toMonoidHom = Q := by
  have hvQ : v ∈ Q := hPQ hv
  have hmap : ∀ K : Subgroup G, K.map (MulAut.conj v).toMonoidHom = CFSG.conjugate K v⁻¹ := by
    intro K
    simp [CFSG.conjugate]
  have hPv : P.map (MulAut.conj v).toMonoidHom = P := by
    rw [hmap, conjugate_eq_self_iff]
    exact inv_mem (hQN hvQ)
  have hQv : Q.map (MulAut.conj v).toMonoidHom = Q := by
    rw [hmap, conjugate_eq_self_iff]
    exact Subgroup.le_normalizer (inv_mem hvQ)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hQv]
    exact Subgroup.map_mono hC
  · rw [← hPv, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj v).injective, hPC, Subgroup.map_bot]
  · rw [← hPv, ← Subgroup.map_sup, hPCs, hQv]

theorem conj_mem_sup {P D X : Subgroup G} (hDP : D ≤ Subgroup.normalizer (P : Set G))
    (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hDX : ∀ d ∈ D, ∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ P) {x : G} (hx : x ∈ X) {g : G}
    (hg : g ∈ D ⊔ P) : x * g * x⁻¹ ∈ D ⊔ P := by
  have h1 : g ∈ ((D ⊔ P : Subgroup G) : Set G) := hg
  rw [sup_comm, Subgroup.coe_mul_of_right_le_normalizer_left P D hDP] at h1
  obtain ⟨p, hp, d, hd, rfl⟩ := h1
  have hxp : x * p * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hXP hx) p).mp hp
  have hxd : x * d * x⁻¹ * d⁻¹ ∈ P := by
    have := P.inv_mem (hDX d hd x hx)
    simpa [mul_assoc] using this
  have : x * (p * d) * x⁻¹ = (x * p * x⁻¹) * (x * d * x⁻¹ * d⁻¹) * d := by group
  rw [this]
  exact (D ⊔ P).mul_mem ((D ⊔ P).mul_mem (Subgroup.mem_sup_right hxp)
    (Subgroup.mem_sup_right hxd)) (Subgroup.mem_sup_left hd)

theorem le_normalizer_sup {P D X : Subgroup G} (hDP : D ≤ Subgroup.normalizer (P : Set G))
    (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hDX : ∀ d ∈ D, ∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ P) :
    X ≤ Subgroup.normalizer ((D ⊔ P : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_sup hDP hXP hDX hx, fun h => ?_⟩
  have := conj_mem_sup hDP hXP hDX (X.inv_mem hx) h
  simpa [mul_assoc] using this

theorem commutator_conj_mem {P D X : Subgroup G} (hDP : D ≤ Subgroup.normalizer (P : Set G))
    (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hDX : ∀ d ∈ D, ∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ P) {u d x : G} (hu : u ∈ P) (hd : d ∈ D)
    (hx : x ∈ X) : (u * d * u⁻¹) * x * (u * d * u⁻¹)⁻¹ * x⁻¹ ∈ P := by
  have h1 : u⁻¹ * (x * u * x⁻¹) ∈ P :=
    P.mul_mem (P.inv_mem hu) ((Subgroup.mem_normalizer_iff.mp (hXP hx) u).mp hu)
  have h2 : d * (u⁻¹ * (x * u * x⁻¹)) * d⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hDP hd) _).mp h1
  have h3 : x * u⁻¹ * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hXP hx) _).mp (P.inv_mem hu)
  have : (u * d * u⁻¹) * x * (u * d * u⁻¹)⁻¹ * x⁻¹ =
      u * (d * (u⁻¹ * (x * u * x⁻¹)) * d⁻¹) * (d * x * d⁻¹ * x⁻¹) * (x * u⁻¹ * x⁻¹) := by group
  rw [this]
  exact P.mul_mem (P.mul_mem (P.mul_mem hu h2) (hDX d hd x hx)) h3

theorem exists_conj_centralized [Finite G] {P D X : Subgroup G} (hP : IsPGroup 2 P)
    (hD : Odd (Nat.card D)) (hX : Odd (Nat.card X)) (hDP : D ≤ Subgroup.normalizer (P : Set G))
    (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hDX : ∀ d ∈ D, ∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ P) :
    ∃ u ∈ P,
      X ≤ Subgroup.centralizer ((D.map (MulAut.conj u).toMonoidHom : Subgroup G) : Set G) := by
  have hXN := le_normalizer_sup hDP hXP hDX
  set N := D ⊔ P with hN
  set Q := X ⊔ N with hQ
  have hPN : P ≤ N := le_sup_right
  have hNQ : N ≤ Q := le_sup_right
  have hPQ : P ≤ Q := hPN.trans hNQ
  have hNP : N ≤ Subgroup.normalizer (P : Set G) := sup_le hDP Subgroup.le_normalizer
  have hQP : Q ≤ Subgroup.normalizer (P : Set G) := sup_le hXP hNP
  have hodd : Odd (P.relIndex Q) := by
    rw [← Subgroup.relIndex_mul_relIndex P N Q hPN hNQ]
    exact (odd_relIndex_sup hDP hD).mul (odd_relIndex_sup hXN hX)
  obtain ⟨C, hCQ, hPC, hPCs, -, -⟩ :=
    H13.exists_complement_of_coprime hPQ hQP (coprime_of_odd hP hodd)
  set W := X ⊔ P with hW
  have hPW : P ≤ W := le_sup_right
  have hWQ : W ≤ Q := sup_le le_sup_left hPQ
  have hWP : W ≤ Subgroup.normalizer (P : Set G) := hWQ.trans hQP
  have hoddW : Odd (P.relIndex W) := odd_relIndex_sup hXP hX
  have hC₁P : P ⊓ (C ⊓ W) = ⊥ := le_bot_iff.mp (hPC ▸ inf_le_inf_left P inf_le_left)
  have hC₁s : P ⊔ (C ⊓ W) = W := by
    rw [sup_inf_eq_of_le_normalizer hPW (hCQ.trans hQP), hPCs, inf_eq_right.mpr hWQ]
  have hXPb : P ⊓ X = ⊥ := inf_eq_bot_of_odd hP hX
  have hXPs : P ⊔ X = W := sup_comm P X
  obtain ⟨v, hv, hXv⟩ := H13.exists_mem_conj_of_complements hPW hWP hP hoddW inf_le_right hC₁P
    hC₁s le_sup_left hXPb hXPs
  set C' := C.map (MulAut.conj v).toMonoidHom with hC'
  obtain ⟨hC'Q, hPC', hPC's⟩ := complement_conj hv hPQ hQP hCQ hPC hPCs
  have hXC' : X ≤ C' := by
    rw [hXv]
    exact Subgroup.map_mono inf_le_left
  set D' := C' ⊓ N with hD'
  have hD'P : P ⊓ D' = ⊥ := le_bot_iff.mp (hPC' ▸ inf_le_inf_left P inf_le_left)
  have hD's : P ⊔ D' = N := by
    rw [sup_inf_eq_of_le_normalizer hPN (hC'Q.trans hQP), hPC's, inf_eq_right.mpr hNQ]
  have hDPb : P ⊓ D = ⊥ := inf_eq_bot_of_odd hP hD
  have hDPs : P ⊔ D = N := sup_comm P D
  obtain ⟨u, hu, hDu⟩ := H13.exists_mem_conj_of_complements hPN hNP hP
    (odd_relIndex_sup hDP hD) le_sup_left hDPb hDPs inf_le_right hD'P hD's
  refine ⟨u, hu, fun x hx => Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  rw [← hDu] at hg
  have hgx : g * x * g⁻¹ * x⁻¹ ∈ D' := by
    have hxg : x * g⁻¹ * x⁻¹ ∈ D' := by
      refine ⟨C'.mul_mem (C'.mul_mem (hXC' hx) (C'.inv_mem hg.1)) (C'.inv_mem (hXC' hx)), ?_⟩
      exact conj_mem_sup hDP hXP hDX hx (N.inv_mem hg.2)
    have := D'.mul_mem hg hxg
    simpa [mul_assoc] using this
  have hgx' : g * x * g⁻¹ * x⁻¹ ∈ P := by
    have hg' : g ∈ D.map (MulAut.conj u).toMonoidHom := hDu ▸ hg
    obtain ⟨d, hd, rfl⟩ := hg'
    simpa [MulAut.conj_apply] using commutator_conj_mem hDP hXP hDX hu hd hx
  have h1 : g * x * g⁻¹ * x⁻¹ ∈ P ⊓ D' := ⟨hgx', hgx⟩
  rw [hD'P, Subgroup.mem_bot] at h1
  have : g * x = x * g := by
    have := congrArg (· * (x * g)) h1
    simpa [mul_assoc] using this
  exact this

end O8H

end CFSG.Quasithin.Vol2.Ch11.SecD
