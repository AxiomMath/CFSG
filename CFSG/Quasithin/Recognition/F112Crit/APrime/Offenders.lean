module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.Quasithin.A1b

variable {G : Type*} [Group G]

@[expose] def StarBound (E Q H : Subgroup G) : Prop :=
  ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
    (∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Q) → (∀ x ∈ P, x ^ 2 ∈ Q) → ¬ P ≤ Q →
    2 * (P ⊓ Q).relIndex P < (E ⊓ Subgroup.centralizer (P : Set G)).relIndex E

private theorem relIndex_zpowers_sq_le_two [Finite G] (y : G) :
    (Subgroup.zpowers (y ^ 2)).relIndex (Subgroup.zpowers y) ≤ 2 := by
  have hle : Subgroup.zpowers (y ^ 2) ≤ Subgroup.zpowers y :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) 2)
  have hcard := Subgroup.relIndex_mul_card (Subgroup.zpowers (y ^ 2)) (Subgroup.zpowers y)
  rw [inf_eq_left.mpr hle, Nat.card_zpowers, Nat.card_zpowers, orderOf_pow] at hcard
  have hkpos : 0 < orderOf y := orderOf_pos y
  have hgdvd : (orderOf y).gcd 2 ∣ orderOf y := Nat.gcd_dvd_left (orderOf y) 2
  have hgpos : 0 < (orderOf y).gcd 2 := Nat.pos_of_dvd_of_pos hgdvd hkpos
  have hgle : (orderOf y).gcd 2 ≤ orderOf y := Nat.le_of_dvd hkpos hgdvd
  have hdivpos : 0 < orderOf y / (orderOf y).gcd 2 := Nat.div_pos hgle hgpos
  have hidx : (Subgroup.zpowers (y ^ 2)).relIndex (Subgroup.zpowers y) = (orderOf y).gcd 2 := by
    refine Nat.mul_right_cancel (m := orderOf y / (orderOf y).gcd 2) hdivpos ?_
    rw [hcard]
    exact (Nat.div_mul_cancel hgdvd).symm.trans (Nat.mul_comm _ _)
  rw [hidx]
  exact Nat.gcd_le_right (orderOf y) (by norm_num)

private theorem relIndex_centralizer_le_two_mul_relIndex [Finite G] {E X Q Y : Subgroup G}
    (hXE : X ≤ E) (hXi : X.relIndex E ≤ 2)
    (hsub : X ⊓ Q ≤ E ⊓ Subgroup.centralizer (Y : Set G)) :
    (E ⊓ Subgroup.centralizer (Y : Set G)).relIndex E ≤ 2 * (X ⊓ Q).relIndex X := by
  have h1 : (E ⊓ Subgroup.centralizer (Y : Set G)).relIndex E ≤ (X ⊓ Q).relIndex E :=
    Subgroup.relIndex_le_of_le_left hsub Subgroup.index_ne_zero_of_finite
  have h2 : (X ⊓ Q).relIndex E = (X ⊓ Q).relIndex X * X.relIndex E :=
    (Subgroup.relIndex_mul_relIndex (X ⊓ Q) X E inf_le_left hXE).symm
  calc (E ⊓ Subgroup.centralizer (Y : Set G)).relIndex E
      ≤ (X ⊓ Q).relIndex E := h1
    _ = (X ⊓ Q).relIndex X * X.relIndex E := h2
    _ ≤ (X ⊓ Q).relIndex X * 2 := Nat.mul_le_mul (le_refl _) hXi
    _ = 2 * (X ⊓ Q).relIndex X := Nat.mul_comm _ 2

theorem StarBound.four_lt [Finite G] {E Q H P : Subgroup G} (hs : StarBound E Q H)
    (hPH : P ≤ H) (hP : IsPGroup 2 P) (hPQ : ¬ P ≤ Q) :
    4 < (E ⊓ Subgroup.centralizer (P : Set G)).relIndex E := by
  classical
  obtain ⟨x, hxP, hxQ⟩ := Set.not_subset.mp hPQ
  obtain ⟨n, hn⟩ := hP ⟨x, hxP⟩
  have hn' : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hex : ∃ m : ℕ, x ^ 2 ^ m ∈ Q := ⟨n, by rw [hn']; exact Q.one_mem⟩
  obtain ⟨N, hNspec, hNmin⟩ : ∃ N : ℕ, x ^ 2 ^ N ∈ Q ∧ ∀ m < N, x ^ 2 ^ m ∉ Q :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd (by simpa [h] using hNspec) hxQ
    · exact h
  let y : G := x ^ 2 ^ (N - 1)
  have hyP : y ∈ P := by
    simpa [y] using Subgroup.pow_mem P hxP (2 ^ (N - 1))
  have hyQ : y ∉ Q := by
    simpa [y] using hNmin (N - 1) (by omega)
  have hysq : y ^ 2 ∈ Q := by
    have hpow : 2 ^ (N - 1) * 2 = 2 ^ N := by
      rw [← pow_succ, Nat.sub_add_cancel hNpos]
    have hy2 : y ^ 2 = x ^ 2 ^ N := by
      show (x ^ 2 ^ (N - 1)) ^ 2 = x ^ 2 ^ N
      rw [← pow_mul, hpow]
    rw [hy2]
    exact hNspec
  have hle : Subgroup.zpowers y ≤ P := Subgroup.zpowers_le.mpr hyP
  have hP2 : IsPGroup 2 (Subgroup.zpowers y) :=
    hP.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hcomm : ∀ a ∈ Subgroup.zpowers y, ∀ b ∈ Subgroup.zpowers y,
      a * b * a⁻¹ * b⁻¹ ∈ Q := by
    intro a ha b hb
    have hab : a * b = b * a := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← hi, ← hj]
      exact (Commute.zpow_zpow_self y i j).eq
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 := by
      rw [hab]
      group
    rw [h1]
    exact Q.one_mem
  have hsq : ∀ a ∈ Subgroup.zpowers y, a ^ 2 ∈ Q := by
    intro a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    have ha2 : a ^ 2 = (y ^ 2) ^ k := by
      rw [← hk, ← zpow_natCast (y ^ k) 2, ← zpow_natCast y 2, ← zpow_mul, ← zpow_mul]
      congr 1
      ring
    rw [ha2]
    exact Subgroup.zpow_mem Q hysq k
  have hP'Q : ¬ Subgroup.zpowers y ≤ Q :=
    fun h => hyQ (h (Subgroup.mem_zpowers y))
  have hkey := hs (Subgroup.zpowers y) (hle.trans hPH) hP2 hcomm hsq hP'Q
  have hidx : (Subgroup.zpowers y ⊓ Q).relIndex (Subgroup.zpowers y) = 2 := by
    have hle2 : Subgroup.zpowers (y ^ 2) ≤ Subgroup.zpowers y ⊓ Q :=
      le_inf (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) 2))
        (Subgroup.zpowers_le.mpr hysq)
    have hlow : (Subgroup.zpowers y ⊓ Q).relIndex (Subgroup.zpowers y) ≤ 2 :=
      (Subgroup.relIndex_le_of_le_left hle2 Subgroup.index_ne_zero_of_finite).trans
        (relIndex_zpowers_sq_le_two y)
    have hne1 : (Subgroup.zpowers y ⊓ Q).relIndex (Subgroup.zpowers y) ≠ 1 := by
      intro h
      have hQ : Subgroup.zpowers y ≤ Q := (Subgroup.relIndex_eq_one.mp h).trans inf_le_right
      exact hyQ (hQ (Subgroup.mem_zpowers y))
    have hne0 : (Subgroup.zpowers y ⊓ Q).relIndex (Subgroup.zpowers y) ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    omega
  have h4 : 4 < (E ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G)).relIndex E := by
    have := hkey
    rw [hidx] at this
    omega
  have hmono : (E ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G)).relIndex E ≤
      (E ⊓ Subgroup.centralizer (P : Set G)).relIndex E :=
    Subgroup.relIndex_le_of_le_left
      (inf_le_inf_left E (Subgroup.centralizer_le fun z hz => hle hz))
      Subgroup.index_ne_zero_of_finite
  exact lt_of_lt_of_le h4 hmono

theorem StarBound.of_isElemAbelian [Finite G] {E Q H P : Subgroup G} (hs : StarBound E Q H)
    (hPH : P ≤ H) (hP : CFSG.Open.IsElemAbelian 2 P) (hPQ : ¬ P ≤ Q) :
    2 * (P ⊓ Q).relIndex P < (E ⊓ Subgroup.centralizer (P : Set G)).relIndex E := by
  refine hs P hPH hP.isPGroup ?_ ?_ hPQ
  · intro x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by
      rw [hP.comm hx hy]
      group
    rw [h1]
    exact Q.one_mem
  · intro x hx
    have h1 : x ^ 2 = 1 := by
      rw [pow_two]
      exact hP.mul_self_eq_one hx
    rw [h1]
    exact Q.one_mem

theorem StarBound.le_of_relIndex_le_four [Finite G] {E Q H P : Subgroup G} (hs : StarBound E Q H)
    (hPH : P ≤ H) (hP : IsPGroup 2 P)
    (hle : (E ⊓ Subgroup.centralizer (P : Set G)).relIndex E ≤ 4) : P ≤ Q := by
  by_contra hPQ
  have := hs.four_lt hPH hP hPQ
  omega

theorem no_mutual_offenders [Finite G] {Eγ Qγ Hγ Eν Qν Hν X Y : Subgroup G}
    (hsγ : StarBound Eγ Qγ Hγ) (hsν : StarBound Eν Qν Hν)
    (hEγ : CFSG.Open.IsElemAbelian 2 Eγ) (hEν : CFSG.Open.IsElemAbelian 2 Eν)
    (hcγ : Qγ ≤ Subgroup.centralizer (Eγ : Set G)) (hcν : Qν ≤ Subgroup.centralizer (Eν : Set G))
    (hX : X ≤ Eγ ⊓ Hν) (hY : Y ≤ Eν ⊓ Hγ) (hXi : X.relIndex Eγ ≤ 2) (hYi : Y.relIndex Eν ≤ 2) :
    X ≤ Qν ∧ Y ≤ Qγ := by
  have hXle : X ≤ Eγ := hX.trans inf_le_left
  have hXH : X ≤ Hν := hX.trans inf_le_right
  have hYle : Y ≤ Eν := hY.trans inf_le_left
  have hYH : Y ≤ Hγ := hY.trans inf_le_right
  have hXea : CFSG.Open.IsElemAbelian 2 X := hEγ.mono hXle
  have hYea : CFSG.Open.IsElemAbelian 2 Y := hEν.mono hYle
  have hC1 : (Eγ ⊓ Subgroup.centralizer (Y : Set G)).relIndex Eγ ≤
      2 * (X ⊓ Qν).relIndex X := by
    refine relIndex_centralizer_le_two_mul_relIndex hXle hXi ?_
    refine le_inf (inf_le_left.trans hXle) ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_iff.mp (hcν hz.2) w (hYle hw)
  have hC2 : (Eν ⊓ Subgroup.centralizer (X : Set G)).relIndex Eν ≤
      2 * (Y ⊓ Qγ).relIndex Y := by
    refine relIndex_centralizer_le_two_mul_relIndex hYle hYi ?_
    refine le_inf (inf_le_left.trans hYle) ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_iff.mp (hcγ hz.2) w (hXle hw)
  have hYQ : Y ≤ Qγ := by
    by_contra hYQ
    have ha_pos : 0 < (Y ⊓ Qγ).relIndex Y :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hlt1 : 2 * (Y ⊓ Qγ).relIndex Y < 2 * (X ⊓ Qν).relIndex X :=
      lt_of_lt_of_le (hsγ.of_isElemAbelian hYH hYea hYQ) hC1
    have hac : (Y ⊓ Qγ).relIndex Y < (X ⊓ Qν).relIndex X := by omega
    have hc_ne_one : (X ⊓ Qν).relIndex X ≠ 1 := by omega
    have hXQ : ¬ X ≤ Qν := by
      intro h
      apply hc_ne_one
      rw [inf_eq_left.mpr h, Subgroup.relIndex_self]
    have hlt2 : 2 * (X ⊓ Qν).relIndex X < 2 * (Y ⊓ Qγ).relIndex Y :=
      lt_of_lt_of_le (hsν.of_isElemAbelian hXH hXea hXQ) hC2
    omega
  refine ⟨?_, hYQ⟩
  by_contra hXQ
  have ha_one : (Y ⊓ Qγ).relIndex Y = 1 := by
    rw [inf_eq_left.mpr hYQ, Subgroup.relIndex_self]
  have hc_pos : 0 < (X ⊓ Qν).relIndex X :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hlt : 2 * (X ⊓ Qν).relIndex X < 2 * (Y ⊓ Qγ).relIndex Y :=
    lt_of_lt_of_le (hsν.of_isElemAbelian hXH hXea hXQ) hC2
  rw [ha_one, Nat.mul_one] at hlt
  omega

theorem relIndex_centralizer_le_two [Finite G] {V W E : Subgroup G} {f : G}
    (hW : W.relIndex V ≤ 2) (hfW : W ≤ Subgroup.centralizer ({f} : Set G))
    (hEV : E ≤ V) : (E ⊓ Subgroup.centralizer ({f} : Set G)).relIndex E ≤ 2 := by
  have h1 : (E ⊓ Subgroup.centralizer ({f} : Set G)).relIndex E ≤ (E ⊓ W).relIndex E :=
    Subgroup.relIndex_le_of_le_left (inf_le_inf_left E hfW) Subgroup.index_ne_zero_of_finite
  have h2 : (E ⊓ W).relIndex E ≤ W.relIndex E := by
    have := Subgroup.relIndex_inf_le (H := E) (K := W) (L := E)
    simpa using this
  have h3 : W.relIndex E ≤ W.relIndex V :=
    Subgroup.relIndex_le_of_le_right hEV Subgroup.index_ne_zero_of_finite
  exact h1.trans (h2.trans (h3.trans hW))

theorem relIndex_inf_conjSub_le_two [Finite G] {V W E : Subgroup G} {f : G}
    (hW : W.relIndex V ≤ 2) (hfW : W ≤ Subgroup.centralizer ({f} : Set G))
    (hEV : E ≤ V) : (E ⊓ CFSG.Quasithin.A1b.conjSub f E).relIndex E ≤ 2 := by
  have hle : E ⊓ Subgroup.centralizer ({f} : Set G) ≤ E ⊓ CFSG.Quasithin.A1b.conjSub f E := by
    refine le_inf inf_le_left ?_
    intro x hx
    have hxf : x * f = f * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hx' : x = f * x * f⁻¹ := by
      rw [← hxf]
      group
    rw [hx']
    exact mem_conjSub_of_mem (g := f) hx.1
  exact (Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite).trans
    (relIndex_centralizer_le_two hW hfW hEV)

end CFSG.Quasithin.F112Crit.APrime
