module

public import CFSG.Quasithin.Background.B3Rank

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ} {k : Mod}

@[expose] def IsTinv (T : Subgroup (Gp n)) (S : Subgroup (Mod.V n k)) : Prop :=
  ∀ t ∈ T, ∀ s ∈ S, Mod.act n k t s ∈ S

@[expose] def Fm (T : Subgroup (Gp n)) (S : Subgroup (Mod.V n k)) : Subgroup (Mod.V n k) where
  carrier := {v | ∀ t ∈ T, Mod.act n k t v * v⁻¹ ∈ S}
  one_mem' := by
    intro t _
    simp
  mul_mem' := by
    intro v w hv hw t ht
    have h : Mod.act n k t (v * w) * (v * w)⁻¹ =
        (Mod.act n k t v * v⁻¹) * (Mod.act n k t w * w⁻¹) := by
      rw [map_mul, mul_inv, mul_mul_mul_comm]
    rw [h]
    exact S.mul_mem (hv t ht) (hw t ht)
  inv_mem' := by
    intro v hv t ht
    have h : Mod.act n k t v⁻¹ * (v⁻¹)⁻¹ = (Mod.act n k t v * v⁻¹)⁻¹ := by
      rw [map_inv, inv_inv, mul_inv, inv_inv]
    rw [h]
    exact S.inv_mem (hv t ht)

theorem mem_Fm {T : Subgroup (Gp n)} {S : Subgroup (Mod.V n k)} {v : Mod.V n k} :
    v ∈ Fm T S ↔ ∀ t ∈ T, Mod.act n k t v * v⁻¹ ∈ S := Iff.rfl

theorem le_Fm {T : Subgroup (Gp n)} {S : Subgroup (Mod.V n k)} (hS : IsTinv T S) : S ≤ Fm T S := by
  intro s hs t ht
  have h : Mod.act n k t s * s⁻¹ ∈ S := S.mul_mem (hS t ht s hs) (S.inv_mem hs)
  exact h

theorem Fm_isTinv {T : Subgroup (Gp n)} {S : Subgroup (Mod.V n k)} (hS : IsTinv T S) :
    IsTinv T (Fm T S) := by
  intro t' ht' v hv t ht
  have h1 : t'⁻¹ * t * t' ∈ T := T.mul_mem (T.mul_mem (T.inv_mem ht') ht) ht'
  have h2 := hv _ h1
  have h3 : Mod.act n k t (Mod.act n k t' v) * (Mod.act n k t' v)⁻¹ =
      Mod.act n k t' (Mod.act n k (t'⁻¹ * t * t') v * v⁻¹) := by
    rw [map_mul, map_inv]
    simp only [map_mul, MulAut.mul_apply, mul_assoc, map_inv]
    simp
  rw [h3]
  exact hS t' ht' _ h2

theorem card_sec_mul {K : Type*} [CommGroup K] (W N : Subgroup K) :
    Nat.card (Sec W N) * Nat.card ↥(N ⊓ W) = Nat.card ↥W := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf W)
  have h2 : Nat.card ↥(N.subgroupOf W) = Nat.card ↥(N ⊓ W) := by
    rw [← Subgroup.inf_subgroupOf_right N W]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ W ≤ W)).toEquiv
  rw [h2] at h1
  exact h1.symm

theorem exists_fixed_mod {T : Subgroup (Gp n)} (hT : IsPGroup 2 T) {S W : Subgroup (Mod.V n k)}
    (hS : IsTinv T S) (hW : IsTinv T W) (hSW : S < W) :
    ∃ w ∈ W, w ∉ S ∧ ∀ t ∈ T, Mod.act n k t w * w⁻¹ ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ' : ↥T →* MulAut (Mod.V n k) := (Mod.act n k).comp T.subtype
  have hWi : IsInv ρ' W := fun g w hw => hW g g.2 w hw
  have hSi : IsInv ρ' S := fun g w hw => hS g g.2 w hw
  let _inst : MulAction ↥T (Sec W S) := MulAction.compHom (Sec W S) (secAct ρ' hWi hSi)
  have hV2 : ∀ v : Mod.V n k, v ^ 2 = 1 := V_sq k
  have hcard := card_sec_mul W S
  have hSW' : S ⊓ W = S := inf_eq_left.2 hSW.le
  rw [hSW'] at hcard
  have hSc := card_eq_two_pow hV2 S
  have hWc := card_eq_two_pow hV2 W
  have hne : Nat.card ↥S ≠ Nat.card ↥W := by
    intro h
    exact hSW.ne (Subgroup.eq_of_le_of_card_ge hSW.le h.ge)
  have hdvd : 2 ∣ Nat.card (Sec W S) := by
    by_contra hnd
    have hodd : Nat.card (Sec W S) % 2 = 1 := by omega
    have h1 : Nat.card (Sec W S) ∣ 2 ^ rk ↥W := by
      rw [← hWc]
      exact ⟨Nat.card ↥S, hcard.symm⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    have hj0 : j = 0 := by
      by_contra hj0
      have : 2 ∣ Nat.card (Sec W S) := by
        rw [hj]
        exact dvd_pow_self 2 hj0
      omega
    rw [hj0, pow_zero] at hj
    rw [hj, one_mul] at hcard
    exact hne hcard
  have hfix1 : (1 : Sec W S) ∈ MulAction.fixedPoints ↥T (Sec W S) := by
    intro g
    show secAct ρ' hWi hSi g 1 = 1
    exact map_one _
  obtain ⟨b, hb, hb1⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Sec W S) hdvd hfix1
  induction b using QuotientGroup.induction_on with
  | H w =>
    refine ⟨(w : Mod.V n k), w.2, ?_, ?_⟩
    · intro hwS
      apply hb1
      symm
      rw [QuotientGroup.eq_one_iff]
      exact hwS
    · intro t ht
      have h1 : (⟨t, ht⟩ : ↥T) • (QuotientGroup.mk w : Sec W S) = QuotientGroup.mk w := hb ⟨t, ht⟩
      have h2 : (QuotientGroup.mk (restrictEquiv ρ' W hWi ⟨t, ht⟩ w) : Sec W S) = QuotientGroup.mk w :=
        h1
      rw [QuotientGroup.eq] at h2
      have h3 := S.inv_mem (show (((restrictEquiv ρ' W hWi ⟨t, ht⟩ w)⁻¹ * w : ↥W) : Mod.V n k) ∈ S from h2)
      simpa [restrictEquiv_apply, mul_comm, ρ'] using h3

theorem sup_zpowers_eq {A B : Subgroup (Mod.V n k)} {w : Mod.V n k} (hAB : A ≤ B) (hw : w ∈ B)
    (hwA : w ∉ A) (hcard : Nat.card B = 2 * Nat.card A) : A ⊔ Subgroup.zpowers w = B := by
  have hle : A ⊔ Subgroup.zpowers w ≤ B := sup_le hAB (Subgroup.zpowers_le.2 hw)
  have hAs : A ≤ A ⊔ Subgroup.zpowers w := le_sup_left
  have hlt : Nat.card A < Nat.card ↥(A ⊔ Subgroup.zpowers w) := by
    rcases lt_or_eq_of_le (Subgroup.card_le_of_le hAs) with h | h
    · exact h
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge hAs h.symm.le
      exact hwA (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hAs
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hc2 : 2 ≤ c := by
    by_contra hcc
    interval_cases c
    · omega
    · omega
  have : Nat.card B ≤ Nat.card ↥(A ⊔ Subgroup.zpowers w) := by
    rw [hcard, hc]
    nlinarith
  exact Subgroup.eq_of_le_of_card_ge hle this

theorem Fm_le_of_lt {T : Subgroup (Gp n)} (hT : IsPGroup 2 T) {C W : Subgroup (Mod.V n k)}
    (hC : IsTinv T C) (hW : IsTinv T W) (hCW : C < W)
    (hcard1 : Nat.card (Fm T C) = 2 * Nat.card C) : Fm T C ≤ W := by
  obtain ⟨w, hwW, hwC, hwT⟩ := exists_fixed_mod hT hC hW hCW
  have h1 : C ⊔ Subgroup.zpowers w = Fm T C :=
    sup_zpowers_eq (le_Fm hC) (fun t ht => hwT t ht) hwC hcard1
  rw [← h1]
  exact sup_le hCW.le (Subgroup.zpowers_le.2 hwW)

theorem eq_of_flag {T : Subgroup (Gp n)} (hT : IsPGroup 2 T) {C : Subgroup (Mod.V n k)}
    (hC : IsTinv T C) (hcard1 : Nat.card (Fm T C) = 2 * Nat.card C)
    (hcard2 : Nat.card (Fm T (Fm T C)) = 2 * Nat.card (Fm T C)) :
    (∀ W : Subgroup (Mod.V n k), C ≤ W → IsTinv T W → Nat.card W = 2 * Nat.card C →
      W = Fm T C) ∧
    (∀ W : Subgroup (Mod.V n k), C ≤ W → IsTinv T W → Nat.card W = 4 * Nat.card C →
      W = Fm T (Fm T C)) := by
  have hCpos : 0 < Nat.card C := Nat.card_pos
  constructor
  · intro W hCW hW hcard
    have hlt : C < W := lt_of_le_of_ne hCW (fun h => by rw [← h] at hcard; omega)
    have hle := Fm_le_of_lt hT hC hW hlt hcard1
    exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  · intro W hCW hW hcard
    have hlt : C < W := lt_of_le_of_ne hCW (fun h => by rw [← h] at hcard; omega)
    have hF1W := Fm_le_of_lt hT hC hW hlt hcard1
    have hF1inv : IsTinv T (Fm T C) := Fm_isTinv hC
    have hlt2 : Fm T C < W := lt_of_le_of_ne hF1W (fun h => by rw [h] at hcard1; omega)
    have hF2W := Fm_le_of_lt hT hF1inv hW hlt2 hcard2
    exact (Subgroup.eq_of_le_of_card_ge hF2W (by omega)).symm

end CFSG.Quasithin.B3
