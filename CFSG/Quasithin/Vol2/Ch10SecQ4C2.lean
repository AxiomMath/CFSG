module

public import CFSG.Quasithin.Vol2.Ch10SecQ4C1
public import CFSG.Quasithin.Vol2.Ch10SecFLJ3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem alt5_conj_eq_inv {g p : ↥(alternatingGroup (Fin 5))} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hp2 : p ^ 2 = 1) (hp1 : p ≠ 1) (hpg : p * g * p⁻¹ ∈ Subgroup.zpowers g) :
    p * g * p⁻¹ = g⁻¹ := by
  have hog : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hpg
  rw [← zpow_mod_orderOf, hog] at hm
  have h0 : 0 ≤ m % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h3 : m % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  obtain h | h | h : m % ((3 : ℕ) : ℤ) = 0 ∨ m % ((3 : ℕ) : ℤ) = 1 ∨ m % ((3 : ℕ) : ℤ) = 2 := by
    omega
  · rw [h, zpow_zero] at hm
    exfalso
    apply hg1
    have : g = p⁻¹ * (p * g * p⁻¹) * p := by group
    rw [this, ← hm]
    group
  · rw [h, zpow_one] at hm
    exfalso
    apply alt5_involution_not_comm g p hg3 hg1 hp2 hp1
    calc p * g = (p * g * p⁻¹) * p := by group
      _ = g * p := by rw [← hm]
  · rw [h] at hm
    rw [← hm, zpow_two]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact hg3)

theorem map_conj_mem_zpowers {L : Subgroup G} {H : Type*} [Group H] (α : ↥L →* H) {p z : ↥L}
    (h : (p : G) * z * (p : G)⁻¹ ∈ Subgroup.zpowers (z : G)) :
    α p * α z * (α p)⁻¹ ∈ Subgroup.zpowers (α z) := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  have hm' : z ^ m = p * z * p⁻¹ := Subtype.ext (by simpa using hm)
  refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
  rw [← map_zpow, hm', map_mul, map_mul, map_inv]

theorem false_of_le_normalizer_zpowers {L P : Subgroup G} (hA : IsAltType L 5)
    (hP : IsSylowTwoOf P L) {z : G} (hzL : z ∈ L) (hz : orderOf z = 3)
    (hPz : P ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hαs, hαk, -⟩ := hA
  have hzo : orderOf (⟨z, hzL⟩ : ↥L) = 3 := by rw [Subgroup.orderOf_mk]; exact hz
  have hco : orderOf (α ⟨z, hzL⟩) = 3 := orderOf_alt_eq_three hαk hzo
  have hc3 : α ⟨z, hzL⟩ ^ 3 = 1 := hco ▸ pow_orderOf_eq_one _
  have hc1 : α ⟨z, hzL⟩ ≠ 1 := fun h => by rw [h, orderOf_one] at hco; omega
  set A := (P.subgroupOf L).map α with hAdef
  have hP2 : IsPGroup 2 (P.subgroupOf L) :=
    hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  have hA2 : IsPGroup 2 A := hP2.map α
  have hidx : ¬ 2 ∣ A.index := fun h => hP.2.2 (h.trans (Subgroup.index_map_dvd _ hαs))
  have hcard60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hmul := A.card_mul_index
  rw [hcard60] at hmul
  obtain ⟨k, hk⟩ := hA2.exists_card_eq
  rw [hk] at hmul
  have hk5 : k ≤ 5 := by
    by_contra hk5
    have h64 : 64 ≤ 2 ^ k :=
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < A.index := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hmul; omega)
    nlinarith
  have hA4 : Nat.card A = 4 := by
    rw [hk]
    interval_cases k <;> norm_num at hmul ⊢ <;> omega
  have hnorm : ∀ a ∈ A, a * α ⟨z, hzL⟩ * a⁻¹ ∈ Subgroup.zpowers (α ⟨z, hzL⟩) := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp ha
    have hpN := hPz (Subgroup.mem_subgroupOf.mp hp)
    exact map_conj_mem_zpowers α
      ((Subgroup.mem_normalizer_iff.mp hpN z).mp (Subgroup.mem_zpowers z))
  have hinv : ∀ a : ↥A, a ≠ 1 → (a : ↥(alternatingGroup (Fin 5))) ^ 2 = 1 ∧
      (a : ↥(alternatingGroup (Fin 5))) * α ⟨z, hzL⟩ * (a : ↥(alternatingGroup (Fin 5)))⁻¹ =
        (α ⟨z, hzL⟩)⁻¹ := by
    intro a ha1
    have h4 : (a : ↥(alternatingGroup (Fin 5))) ^ 4 = 1 := by
      have := pow_card_eq_one' (G := ↥A) (x := a)
      rw [hA4] at this
      simpa using congrArg Subtype.val this
    have h2 := alt5_pow_four _ h4
    have ha1' : (a : ↥(alternatingGroup (Fin 5))) ≠ 1 := fun h => ha1 (Subtype.ext h)
    exact ⟨h2, alt5_conj_eq_inv hc3 hc1 h2 ha1' (hnorm a a.2)⟩
  obtain ⟨a, b, ha1, hb1, hab⟩ := exists_two_ne_one_of_card_eq_four hA4
  obtain ⟨ha2, hac⟩ := hinv a ha1
  obtain ⟨hb2, hbc⟩ := hinv b hb1
  set a' : ↥(alternatingGroup (Fin 5)) := a.1
  set b' : ↥(alternatingGroup (Fin 5)) := b.1
  set c := α ⟨z, hzL⟩
  have hab' : a' * b' ≠ 1 := by
    intro h
    apply hab
    apply Subtype.ext
    have ha' : a'⁻¹ = a' := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two]
      exact ha2
    calc (a : ↥(alternatingGroup (Fin 5))) = a'⁻¹ := ha'.symm
      _ = b' := (eq_inv_of_mul_eq_one_right h).symm
  have hab2 : (a' * b') ^ 2 = 1 := by
    have h4 : (a' * b') ^ 4 = 1 := by
      have := pow_card_eq_one' (G := ↥A) (x := a * b)
      rw [hA4] at this
      simpa using congrArg Subtype.val this
    exact alt5_pow_four _ h4
  apply alt5_involution_not_comm c (a' * b') hc3 hc1 hab2 hab'
  have key : (a' * b') * c * (a' * b')⁻¹ = c := by
    calc (a' * b') * c * (a' * b')⁻¹ = a' * (b' * c * b'⁻¹) * a'⁻¹ := by group
      _ = a' * c⁻¹ * a'⁻¹ := by rw [hbc]
      _ = (a' * c * a'⁻¹)⁻¹ := by group
      _ = c := by rw [hac, inv_inv]
  calc a' * b' * c = (a' * b') * c * (a' * b')⁻¹ * (a' * b') := by group
    _ = c * (a' * b') := by rw [key]

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
