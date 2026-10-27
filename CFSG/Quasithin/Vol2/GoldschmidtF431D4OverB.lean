module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4OverU
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocT
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4OverBlocks

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Certificates

set_option linter.unusedSectionVars false


section Card

theorem finite_D' : Finite D :=
  Nat.finite_of_card_ne_zero (by rw [card_trialityGroup8]; norm_num)

theorem card_flag : Nat.card Flag = 7371 := by
  rw [← Nat.card_congr flagEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem stabilizer_flag0 : MulAction.stabilizer D flag0 = d4B := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  exact smul_flag0_iff g

theorem card_d4B : Nat.card d4B = 28672 := by
  have h1 := MulAction.index_stabilizer D flag0
  have horb : MulAction.orbit D flag0 = Set.univ :=
    Set.eq_univ_of_forall fun u => MulAction.mem_orbit_iff.2 (exists_smul_flag0_eq u)
  rw [horb, Set.ncard_univ, stabilizer_flag0, card_flag] at h1
  have h2 := Subgroup.card_mul_index d4B
  rw [h1, card_trialityGroup8] at h2
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h2.trans (by norm_num))

end Card

section Zeta

theorem array_eq_of_rep {n : ℕ} {a b : Array ℕ} (ha : a.size = n) (hb : b.size = n)
    {σ : Equiv.Perm (Fin n)} (h1 : Rep n a σ) (h2 : Rep n b σ) : a = b :=
  Array.ext (ha.trans hb.symm) fun i hi1 hi2 => by
    have := (h1 ⟨i, ha ▸ hi1⟩).trans (h2 ⟨i, ha ▸ hi1⟩).symm
    simpa [getElem!_pos, hi1, hi2] using this

theorem d4Zeta_not_comm_gen0 : d4Zeta * d4GenG 0 ≠ d4GenG 0 * d4Zeta := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := ovZeta_parts
  intro h
  apply h8
  have hz : Rep 819 (ptWordArr [3, 2, 4, 2]) (act d4Zeta) := rep_ptWordArr (by decide)
  have h1 := rep_compA hz (act_gen (j := 0) (by norm_num))
  have h2 := rep_compA (act_gen (j := 0) (by norm_num)) hz
  have hp : act d4Zeta * act (d4GenG 0) = act (d4GenG 0) * act d4Zeta := by
    rw [← map_mul, ← map_mul, h]
  rw [← hp] at h2
  exact array_eq_of_rep (by simp [compA]) (by simp [compA]) h1 h2

theorem d4Zeta_ne_one : d4Zeta ≠ 1 := by
  intro h
  exact d4Zeta_not_comm_gen0 (by rw [h]; simp)

theorem d4Zeta_mem_B' : d4Zeta ∈ d4B := d4Zeta_mem_B

variable (hs : IsSimpleGroup D)
include hs

theorem d4Zeta_normalizes :
    d4Zeta ∈ Subgroup.normalizer (d4U : Set D) := by
  have : Finite D := finite_D'
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  have key : d4U.map (MulAut.conj d4Zeta).toMonoidHom ≤ d4U := by
    rw [Subgroup.map_le_iff_le_comap, d4U, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 4 := by simpa [uGens_size] using hk
    obtain ⟨u, hu, hconj⟩ := zeta_conj_gen hs hk'
    show (MulAut.conj d4Zeta) (uGH k) ∈ d4U
    rw [MulAut.conj_apply, ← uGen_eq_uGH hk', hconj]
    exact hu
  have := key ⟨n, hn, rfl⟩
  simpa [MulAut.conj_apply] using this

theorem d4B_le_normalizer :
    d4B ≤ Subgroup.normalizer (d4U : Set D) := by
  have : Finite D := finite_D'
  set C : Subgroup D := Subgroup.normalizer (d4U : Set D) ⊓ d4B with hC
  have hUC : d4U ≤ C := le_inf Subgroup.le_normalizer d4U_le_d4B'
  have hzC : d4Zeta ∈ C := ⟨d4Zeta_normalizes hs, d4Zeta_mem_B'⟩
  have hdiv1 : 4096 ∣ Nat.card C := by
    have := Subgroup.card_dvd_of_le hUC
    rwa [card_d4U'] at this
  have hdiv2 : 7 ∣ Nat.card C := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have ho : orderOf d4Zeta = 7 := orderOf_eq_prime (d4Zeta_pow_seven hs) d4Zeta_ne_one
    have ho' : orderOf (⟨d4Zeta, hzC⟩ : C) = 7 := by rw [← Subgroup.orderOf_coe]; exact ho
    rw [← ho']
    exact orderOf_dvd_natCard _
  have h28 : 4096 * 7 ∣ Nat.card C := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hdiv1 hdiv2
  have hle : Nat.card C ≤ Nat.card d4B := Subgroup.card_le_of_le inf_le_right
  rw [card_d4B] at hle
  have hpos : 0 < Nat.card C := Nat.card_pos
  have h28' : Nat.card C = 28672 := by
    have := Nat.le_of_dvd hpos h28
    omega
  have hCB : C = d4B := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [card_d4B, h28'])
  rw [← hCB]
  exact inf_le_left

theorem normalizer_d4U_eq_d4B :
    Subgroup.normalizer (d4U : Set D) = d4B :=
  le_antisymm normalizer_d4U_le_d4B (d4B_le_normalizer hs)

end Zeta

section Centralizer

@[expose] def innU : Subgroup D where
  carrier := {g | ∃ u ∈ d4U, ∀ a ∈ d4U, g * a * g⁻¹ = u * a * u⁻¹}
  one_mem' := ⟨1, one_mem _, fun a _ => by simp⟩
  mul_mem' := by
    rintro g g' ⟨u, hu, hg⟩ ⟨u', hu', hg'⟩
    refine ⟨u * u', d4U.mul_mem hu hu', fun a ha => ?_⟩
    have hb : u' * a * u'⁻¹ ∈ d4U := d4U.mul_mem (d4U.mul_mem hu' ha) (d4U.inv_mem hu')
    calc g * g' * a * (g * g')⁻¹ = g * (g' * a * g'⁻¹) * g⁻¹ := by group
      _ = g * (u' * a * u'⁻¹) * g⁻¹ := by rw [hg' a ha]
      _ = u * (u' * a * u'⁻¹) * u⁻¹ := hg _ hb
      _ = u * u' * a * (u * u')⁻¹ := by group
  inv_mem' := by
    rintro g ⟨u, hu, hg⟩
    refine ⟨u⁻¹, d4U.inv_mem hu, fun a ha => ?_⟩
    have hb : u⁻¹ * a * u ∈ d4U := d4U.mul_mem (d4U.mul_mem (d4U.inv_mem hu) ha) hu
    have h1 : g * (u⁻¹ * a * u) * g⁻¹ = a := by rw [hg _ hb]; group
    calc g⁻¹ * a * g⁻¹⁻¹ = g⁻¹ * (g * (u⁻¹ * a * u) * g⁻¹) * g⁻¹⁻¹ := by rw [h1]
      _ = u⁻¹ * a * u⁻¹⁻¹ := by group

theorem pow_conj_eq {g u : D} (hg : ∀ a ∈ d4U, g * a * g⁻¹ = u * a * u⁻¹) (hu : u ∈ d4U) :
    ∀ n : ℕ, ∀ a ∈ d4U, g ^ n * a * (g ^ n)⁻¹ = u ^ n * a * (u ^ n)⁻¹
  | 0, a, _ => by simp
  | n + 1, a, ha => by
    have hb : u ^ n * a * (u ^ n)⁻¹ ∈ d4U :=
      d4U.mul_mem (d4U.mul_mem (d4U.pow_mem hu n) ha) (d4U.inv_mem (d4U.pow_mem hu n))
    calc g ^ (n + 1) * a * (g ^ (n + 1))⁻¹
        = g * (g ^ n * a * (g ^ n)⁻¹) * g⁻¹ := by rw [pow_succ']; group
      _ = g * (u ^ n * a * (u ^ n)⁻¹) * g⁻¹ := by rw [pow_conj_eq hg hu n a ha]
      _ = u * (u ^ n * a * (u ^ n)⁻¹) * u⁻¹ := hg _ hb
      _ = u ^ (n + 1) * a * (u ^ (n + 1))⁻¹ := by rw [pow_succ']; group

variable (hs : IsSimpleGroup D)
include hs

theorem mem_d4U_of_comm {x : D} (hxB : x ∈ d4B)
    (hc : ∀ u ∈ d4U, x * u = u * x) : x ∈ d4U := by
  have : Finite D := finite_D'
  set K := d4U ⊔ Subgroup.zpowers x with hK
  have hKB : K ≤ d4B := sup_le d4U_le_d4B' ((Subgroup.zpowers_le).2 hxB)
  have hKM : K ≤ innU := by
    apply sup_le
    · intro u hu
      exact ⟨u, hu, fun a _ => rfl⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨1, one_mem _, fun a ha => by simp [hc a ha]⟩
  have hd1 : 4096 ∣ Nat.card K := by
    have := Subgroup.card_dvd_of_le (le_sup_left : d4U ≤ K)
    rwa [card_d4U'] at this
  have hd2 : Nat.card K ∣ 28672 := by
    have := Subgroup.card_dvd_of_le hKB
    rwa [card_d4B] at this
  obtain ⟨m, hm⟩ := hd1
  have hm7 : m ∣ 7 := by
    rw [hm, show (28672 : ℕ) = 4096 * 7 by norm_num] at hd2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd2
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hm7 with rfl | rfl
  · have hKU : K = d4U := (Subgroup.eq_of_le_of_card_ge le_sup_left
      (by rw [card_d4U', hm])).symm
    rw [← hKU]
    exact (le_sup_right : Subgroup.zpowers x ≤ K) (Subgroup.mem_zpowers x)
  · exfalso
    have hKB' : K = d4B := Subgroup.eq_of_le_of_card_ge hKB (by rw [card_d4B, hm])
    have hzM : d4Zeta ∈ innU := hKM (hKB' ▸ d4Zeta_mem_B')
    obtain ⟨u, hu, hact⟩ := hzM
    have h7 := d4Zeta_pow_seven hs
    have hz4096 : d4Zeta ^ 4096 = d4Zeta := by
      rw [show (4096 : ℕ) = 7 * 585 + 1 by norm_num, pow_succ, pow_mul, h7, one_pow, one_mul]
    have hu4096 : u ^ 4096 = 1 := by
      have := pow_card_eq_one' (G := d4U) (x := ⟨u, hu⟩)
      rw [card_d4U'] at this
      exact congrArg Subtype.val this
    have hcomm : d4Zeta * d4GenG 0 * d4Zeta⁻¹ = d4GenG 0 := by
      have h0 : d4GenG 0 ∈ d4U := gen_mem_d4U (Or.inl rfl)
      have := pow_conj_eq hact hu 4096 _ h0
      rw [hz4096, hu4096] at this
      simpa using this
    apply d4Zeta_not_comm_gen0
    rw [mul_inv_eq_iff_eq_mul] at hcomm
    exact hcomm

theorem centralizer_d4U {x : D} (hc : ∀ u ∈ d4U, x * u = u * x) :
    x = 1 ∨ x = d4z := by
  have : Finite D := finite_D'
  have hxN : x ∈ Subgroup.normalizer (d4U : Set D) := by
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    have : x * n * x⁻¹ = n := by rw [mul_inv_eq_iff_eq_mul, hc n hn]
    rw [this]
    exact hn
  have hxB : x ∈ d4B := normalizer_d4U_le_d4B hxN
  have hxU : x ∈ d4U := mem_d4U_of_comm hs hxB hc
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · exact Or.inr (center_T_spec hxU (fun y hy => (hc y hy).symm) hx1)

theorem d4_hZH :
    ∀ x ∈ d4H, (∀ h ∈ d4H, h * x = x * h) → x = 1 ∨ x = d4z := by
  intro x hx hc
  apply centralizer_d4U hs
  intro u hu
  exact (hc u ((Subgroup.mem_inf.1 (d4U_le_d4B' hu)).1)).symm

end Centralizer

end CFSG.Quasithin.D4Hex
