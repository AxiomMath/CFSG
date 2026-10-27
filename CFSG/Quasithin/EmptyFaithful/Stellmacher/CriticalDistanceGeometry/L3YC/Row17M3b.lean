module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Row17M3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCM24Glue

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc
  CFSG.Quasithin.F134.J4E9 CFSG.Quasithin.KGC31 CFSG.Quasithin.Special2 CFSG.Quasithin.J4Fam
  CFSG.Quasithin.J4Rad CFSG.Quasithin.J4M3
open scoped commutatorElement

namespace Stellmacher.CD.L3YC.R17

section M3b


theorem Qg_le_commutator : Qg ≤ ⁅Qg, KL⁆ := by
  have hq : ∀ i : Fin 12, qF i ∈ ⁅Qg, KL⁆ := by
    intro i
    show qJ i ∈ _
    rw [qJ]
    exact Subgroup.commutator_mem_commutator (pJ_mem_Q i.2) xM_mem_KL
  have hV0 : eSub hv0 ≤ ⁅Qg, KL⁆ := by
    rw [eSub_eq_closure, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨i, j, e⟩ := v0_comm k
    rw [e, commutatorElement_def]
    exact (⁅Qg, KL⁆).mul_mem ((⁅Qg, KL⁆).mul_mem ((⁅Qg, KL⁆).mul_mem (hq i) (hq j))
      ((⁅Qg, KL⁆).inv_mem (hq i))) ((⁅Qg, KL⁆).inv_mem (hq j))
  refine sup_le ((Subgroup.closure_le _).mpr ?_) hV0
  rintro _ ⟨i, rfl⟩
  exact hq i

theorem exists_order_three_elt : ∃ x : ↥M3, x ^ 3 = 1 ∧ rho3 j4Facts x ≠ 1 := by
  classical
  have hM := j4Facts.mat
  have hpermcard : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hrho_top : (rho3 j4Facts).range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [card_range_rho3, hpermcard])
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 5), orderOf σ = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact exists_prime_orderOf_dvd_card' 3 (by rw [hpermcard]; norm_num)
  obtain ⟨m, hm⟩ : ∃ m : ↥M3, rho3 j4Facts m = σ := by
    have : σ ∈ (rho3 j4Facts).range := by rw [hrho_top]; trivial
    exact this
  obtain ⟨e, n', hn', hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos m).ne' 3 (by norm_num)
  set x₀ : ↥M3 := m ^ n' with hx₀
  have hρx : rho3 j4Facts x₀ ≠ 1 := by
    intro h
    rw [hx₀, map_pow, hm] at h
    exact hn' (hσ ▸ orderOf_dvd_of_pow_eq_one h)
  have hx3 : x₀ ^ 3 ^ e = 1 := by
    rw [hx₀, ← pow_mul, mul_comm, ← hn]
    exact pow_orderOf_eq_one m
  refine ⟨x₀, ?_, hρx⟩
  have h120 : ¬ 9 ∣ Nat.card (Equiv.Perm (Fin 5)) := by rw [hpermcard]; norm_num
  have h168 : ¬ 9 ∣ Nat.card (MulAut ↥V0) := by rw [card_mulAut_V0 hM]; norm_num
  have hρ3 : (rho3 j4Facts x₀) ^ 3 = 1 := by
    apply pow_three_of_three_power h120 (e := e)
    rw [← map_pow, hx3, map_one]
  have hα3 : (V0.normalizerMonoidHom x₀) ^ 3 = 1 := by
    apply pow_three_of_three_power h168 (e := e)
    rw [← map_pow, hx3, map_one]
  have hker : x₀ ^ 3 ∈ ((rho3 j4Facts).ker ⊓ V0.normalizerMonoidHom.ker : Subgroup ↥M3) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_pow]; exact hρ3
    · rw [MonoidHom.mem_ker, map_pow]; exact hα3
  obtain ⟨k, hk⟩ := isPGroup_ker_rho3_alpha3 j4Facts ⟨x₀ ^ 3, hker⟩
  have hk' : (x₀ ^ 3) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hk3 : (x₀ ^ 3) ^ 3 ^ e = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hx3, one_pow]
  have hord : orderOf (x₀ ^ 3) = 1 := by
    have h1 : orderOf (x₀ ^ 3) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h2 : orderOf (x₀ ^ 3) ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hk3
    exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow _ _ (by norm_num)) h1 h2
  exact orderOf_eq_one_iff.mp hord

theorem m3_row14conc [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] {B : Subgroup J} (hperf : ⁅B, B⁆ = B)
    (hN : P0 ≤ Subgroup.normalizer (B : Set J)) (hBM : B ⊔ P0 ≤ M3)
    (hq : IsPSL 3 2 1 (↥B ⧸ CFSG.pCore 2 ↥B)) :
    ∃ ω : J, Stellmacher.PU.L3YC.M24.Row14Conc B ω := by
  classical
  have hM := j4Facts.mat
  obtain ⟨hBeq, hmap, hpc⟩ := m3_structure hperf hN hBM hq
  obtain ⟨x₀, hx3, hρx⟩ := exists_order_three_elt
  refine ⟨(x₀ : J), ?_, ?_, ?_, ?_⟩
  · rw [hBeq]; exact M3_le_normalizer_KL x₀.2
  · have := congrArg Subtype.val hx3
    simpa using this
  · intro b hb
    rw [hmap]
    by_contra hcon
    push_neg at hcon
    have hbKL : b ∈ KL := hBeq ▸ hb
    have hbM : b ∈ M3 := KL_le_M3 hbKL
    set t : ↥M3 := (⟨b, hbM⟩ : ↥M3)⁻¹ * x₀ with ht
    have hρt : rho3 j4Facts t = rho3 j4Facts x₀ := by
      have hb1 : rho3 j4Facts ⟨b, hbM⟩ = 1 := (rho3_eq_one_iff ⟨b, hbM⟩).mpr hbKL
      rw [ht, map_mul, map_inv, hb1, inv_one, one_mul]
    have htQ : ∀ q ∈ Qg, (t : J) * q * (t : J)⁻¹ = q := by
      intro q hqQ
      have h1 := hcon q hqQ
      have htJ : (t : J) = b⁻¹ * (x₀ : J) := rfl
      rw [htJ]
      calc b⁻¹ * (x₀ : J) * q * (b⁻¹ * (x₀ : J))⁻¹ = b⁻¹ * ((x₀ : J) * q * (x₀ : J)⁻¹) * b := by
            group
        _ = b⁻¹ * (b * q * b⁻¹) * b := by rw [h1]
        _ = q := by group
    have hρt' : rho3 j4Facts t ≠ 1 := by rw [hρt]; exact hρx
    have he3 : (rho3 j4Facts t) ^ 3 ^ 1 = 1 := by
      rw [hρt, pow_one, ← map_pow, hx3, map_one]
    obtain ⟨s₀, ⟨e2, hs3⟩, hρs, hscomm⟩ := exists_three_part (rho3 j4Facts) hρt' he3
    have hsV : (s₀ : J) ∈ V0 := by
      apply centralizer_pCoreOf_M3_le
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [pCoreOf_M3_eq] at hg
      have hgM : g ∈ M3 := Q_le_M3 hg
      have h1 : t * (⟨g, hgM⟩ : ↥M3) * t⁻¹ = ⟨g, hgM⟩ := Subtype.ext (htQ g hg)
      have h2 := congrArg Subtype.val (hscomm _ h1)
      have h3 : (s₀ : J) * g * (s₀ : J)⁻¹ = g := h2
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3.symm
    have hs3J : (s₀ : J) ^ 3 ^ e2 = 1 := by
      have := congrArg Subtype.val hs3
      simpa using this
    have hs2 : (s₀ : J) ^ 2 = 1 := by rw [pow_two]; exact V0_sq hM _ hsV
    have hs1 : (s₀ : J) = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hs2, hs3J⟩
      have hg : Nat.gcd 2 (3 ^ e2) = 1 := Nat.Coprime.pow_right _ (by norm_num)
      rwa [hg, pow_one] at this
    exact hρs (by
      have : s₀ = 1 := Subtype.ext hs1
      rw [this, map_one])
  · apply le_antisymm (Subgroup.commutator_le_left _ _)
    have h1 : (⁅CFSG.pCore 2 ↥B, (⊤ : Subgroup ↥B)⁆).map B.subtype = ⁅Qg, B⁆ := by
      rw [Subgroup.map_commutator, hmap, Subgroup.map_top, Subgroup.range_subtype]
    rw [← Subgroup.map_le_map_iff_of_injective B.subtype_injective, h1, hmap, hBeq]
    exact Qg_le_commutator

end M3b

end Stellmacher.CD.L3YC.R17

end CFSG.Quasithin
