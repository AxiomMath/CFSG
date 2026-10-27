module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtElRestJ2Cent
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelCentralizers

public section

namespace CFSG.Quasithin.ModH

open CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier

section Generic

variable {M : Type*} [Group M]

theorem dvd_card_sup_zpowers [Finite M] {T : Subgroup M} (hTp : IsPGroup 2 T)
    (hT : Nat.card T = 128) {g : M} (hgp : IsPGroup 2 (Subgroup.zpowers g))
    (hg : ∀ t ∈ T, g * t = t * g) (hgT : g ∉ T) :
    256 ∣ Nat.card ↥(T ⊔ Subgroup.zpowers g) := by
  have hnorm : Subgroup.zpowers g ≤ Subgroup.normalizer (T : Set M) :=
    Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun h hh => (hg h hh).symm))
  have hK2 : IsPGroup 2 ↥(T ⊔ Subgroup.zpowers g) := hTp.to_sup_of_normal_left' hgp hnorm
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hK2
  have hlt : Nat.card T < Nat.card ↥(T ⊔ Subgroup.zpowers g) := by
    by_contra hge
    rw [not_lt] at hge
    have h := Subgroup.eq_of_le_of_card_ge (le_sup_left : T ≤ T ⊔ Subgroup.zpowers g) hge
    exact hgT (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  rw [hT, hj] at hlt
  have h7 : 2 ^ 7 < 2 ^ j := by simpa using hlt
  have hj8 : 8 ≤ j := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h7
  rw [hj, show (256 : ℕ) = 2 ^ 8 by norm_num]
  exact Nat.pow_dvd_pow 2 hj8

theorem exists_size_mul_card_cent [Finite M] {K : Subgroup M} {sizes : List ℕ}
    (hOF : OrderFourClassSizes K sizes) {x : M} (hx : x ∈ K) (hx4 : orderOf x = 4) :
    ∃ s ∈ sizes, s * Nat.card (centralizerIn K x) = Nat.card K := by
  obtain ⟨reps, -, hcov, -, hsz⟩ := hOF
  obtain ⟨rep, hrep, c, hc, rfl⟩ := hcov x hx hx4
  have hcent : Nat.card (centralizerIn K (c * rep * c⁻¹)) = Nat.card (centralizerIn K rep) := by
    rw [centralizerIn_conj K hc rep, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  refine ⟨(conjClass K rep).ncard, ?_, ?_⟩
  · rw [← hsz]
    exact List.mem_map_of_mem hrep
  · rw [hcent]
    exact ncard_conjClass_mul_card K rep

end Generic

theorem j2_sq_mem_P {r : Equiv.Perm (Fin 315)} (hrR : r ∈ R)
    (hrP : r ∉ P) : r * r ∈ P := by
  have hp : permU⁻¹ * r ∈ P := (mem_P_or_coset hrR).resolve_left hrP
  have e : r * r = (permU * (permU⁻¹ * r) * permU⁻¹) * (permU * permU) * (permU⁻¹ * r) := by
    group
  rw [e]
  exact P.mul_mem (P.mul_mem (permU_conj_mem _ hp) (by rw [permU_mul_self]; exact P.one_mem)) hp

theorem j2_no_outer_comm_sylow
    {Tm : Subgroup (Equiv.Perm (Fin 315))} (hTP : Tm ≤ P)
    (hT : Nat.card Tm = 128)
    (hCS : ∀ x y : Equiv.Perm (Fin 315), x ∈ Tm → y ∈ Tm → (∀ t ∈ Tm, x * t = t * x) →
      (∀ t ∈ Tm, y * t = t * y) → x = 1 ∨ y = 1 ∨ x = y)
    {r : Equiv.Perm (Fin 315)} (hrR : r ∈ R) (hrP : r ∉ P) (hr : ∀ t ∈ Tm, r * t = t * r) :
    False := by
  have hTp : IsPGroup 2 Tm := IsPGroup.of_card (n := 7) (by rw [hT]; norm_num)
  obtain ⟨-, -, hcover, -, -, -, -, -, -, hR3840, hOF, -, -, -, -, -, -⟩ :=
    ctss_j2_automorphism_involution_centralizers_exclude_small_normal_four_groups
  obtain ⟨-, -, -, hAm, hTm, hUn, -, -, -, -, -, -, -, -, -, -, -, -, hU336, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  have hsq := j2_sq_mem_P hrR hrP
  have hr2 : ∀ t ∈ Tm, (r * r) * t = t * (r * r) := fun t ht =>
    calc r * r * t = r * (r * t) := mul_assoc ..
      _ = r * (t * r) := by rw [hr t ht]
      _ = (r * t) * r := (mul_assoc ..).symm
      _ = (t * r) * r := by rw [hr t ht]
      _ = t * (r * r) := mul_assoc ..
  have hr2T : r * r ∈ Tm := j2_comm_sylow_mem hTP hT hsq hr2
  by_cases h1 : r * r = 1
  · have hr1 : r ≠ 1 := fun h => hrP (h ▸ P.one_mem)
    have hro : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact h1) hr1
    obtain ⟨rep, hrep, c, hc, hrc⟩ := hcover r hrR hro
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrep
    have hTle : Tm ≤ centralizerIn P r := fun t ht =>
      mem_centralizerIn.2 ⟨hTP ht, (hr t ht).symm⟩
    have h128 : 128 ∣ Nat.card (centralizerIn P r) := hT ▸ Subgroup.card_dvd_of_le hTle
    rcases hrep with rfl | rfl | rfl
    · exact hrP (by rw [hrc]; exact P.mul_mem (P.mul_mem hc hAm) (P.inv_mem hc))
    · exact hrP (by rw [hrc]; exact P.mul_mem (P.mul_mem hc hTm) (P.inv_mem hc))
    · have h := centralizerIn_conj P hc permU
      rw [← hrc] at h
      rw [h, Subgroup.card_map_of_injective (MulAut.conj c).injective, hU336] at h128
      exact absurd h128 (by norm_num)
  · have hyc : ∀ t ∈ Tm, (r * r) * t = t * (r * r) := hr2
    have hyy : (r * r) * (r * r) ∈ Tm := Tm.mul_mem hr2T hr2T
    have hyyc : ∀ t ∈ Tm, ((r * r) * (r * r)) * t = t * ((r * r) * (r * r)) := fun t ht =>
      calc r * r * (r * r) * t = r * r * (r * r * t) := mul_assoc ..
        _ = r * r * (t * (r * r)) := by rw [hyc t ht]
        _ = (r * r * t) * (r * r) := (mul_assoc ..).symm
        _ = (t * (r * r)) * (r * r) := by rw [hyc t ht]
        _ = t * ((r * r) * (r * r)) := mul_assoc ..
    have hy2 : (r * r) * (r * r) = 1 := by
      rcases hCS (r * r) ((r * r) * (r * r)) hr2T hyy hyc hyyc with h | h | h
      · exact absurd h h1
      · exact h
      · exfalso
        apply h1
        have : (r * r) * (r * r) = (r * r) * 1 := by rw [mul_one]; exact h.symm
        exact mul_left_cancel this
    have hyo : orderOf (r * r) = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) h1
    have hTley : Tm ≤ centralizerIn P (r * r) := fun t ht =>
      mem_centralizerIn.2 ⟨hTP ht, (hyc t ht).symm⟩
    have h128 : 128 ∣ Nat.card (centralizerIn P (r * r)) := hT ▸ Subgroup.card_dvd_of_le hTley
    obtain ⟨c, hc, hyc'⟩ := j2_exists_conj_permTwoA hsq hyo h128
    have hcR : c ∈ R := P_le_R hc
    have hr'R : c⁻¹ * r * c ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hcR) hrR) hcR
    have hr'P : c⁻¹ * r * c ∉ P := fun h => hrP (by
      have := P.mul_mem (P.mul_mem hc h) (P.inv_mem hc)
      rwa [show c * (c⁻¹ * r * c) * c⁻¹ = r by group] at this)
    have hTwoA : permTwoA = c⁻¹ * (r * r) * c := by rw [hyc']; group
    have hrcomm : r * (r * r) = (r * r) * r := by group
    have hr'z : (c⁻¹ * r * c) * permTwoA = permTwoA * (c⁻¹ * r * c) := by
      rw [hTwoA]
      calc c⁻¹ * r * c * (c⁻¹ * (r * r) * c) = c⁻¹ * (r * (r * r)) * c := by group
        _ = c⁻¹ * ((r * r) * r) * c := by rw [hrcomm]
        _ = c⁻¹ * (r * r) * c * (c⁻¹ * r * c) := by group
    have hr'D : c⁻¹ * r * c ∈ centralizerIn R permTwoA := mem_centralizerIn.2 ⟨hr'R, hr'z⟩
    have hr'4 : orderOf (c⁻¹ * r * c) = 4 := by
      have hsqe : (c⁻¹ * r * c) ^ 2 = permTwoA := by
        rw [hTwoA, sq]
        group
      have hord2 : permTwoA * permTwoA = 1 := by
        rw [hTwoA]
        calc c⁻¹ * (r * r) * c * (c⁻¹ * (r * r) * c) = c⁻¹ * ((r * r) * (r * r)) * c := by group
          _ = 1 := by rw [hy2]; group
      have hne : permTwoA ≠ 1 := fun h => h1 (by
        have : c⁻¹ * (r * r) * c = 1 := by rw [← hTwoA]; exact h
        have h' := congrArg (fun x => c * x * c⁻¹) this
        simpa [mul_assoc] using h')
      have h4 : (c⁻¹ * r * c) ^ 2 ^ 2 = 1 := by
        rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, hsqe, sq, hord2]
      have h2 : ¬ (c⁻¹ * r * c) ^ 2 ^ 1 = 1 := by
        rw [pow_one, hsqe]
        exact hne
      have := orderOf_eq_prime_pow (p := 2) h2 (by simpa using h4)
      simpa using this
    set Tm' : Subgroup (Equiv.Perm (Fin 315)) := Tm.map (MulAut.conj c⁻¹).toMonoidHom with hTm'
    have hTm'mem : ∀ x, x ∈ Tm' ↔ ∃ t ∈ Tm, c⁻¹ * t * c = x := by
      intro x
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, ht, by simp⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, ht, by simp⟩
    have hTm'c : Nat.card Tm' = 128 := by
      rw [hTm', Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hT]
    have hTm'P : Tm' ≤ P := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := (hTm'mem x).1 hx
      exact P.mul_mem (P.mul_mem (P.inv_mem hc) (hTP ht)) hc
    have hTm'D : Tm' ≤ centralizerIn R permTwoA := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := (hTm'mem x).1 hx
      refine mem_centralizerIn.2 ⟨R.mul_mem (R.mul_mem (R.inv_mem hcR) (P_le_R (hTP ht))) hcR, ?_⟩
      rw [hTwoA]
      calc c⁻¹ * t * c * (c⁻¹ * (r * r) * c) = c⁻¹ * (t * (r * r)) * c := by group
        _ = c⁻¹ * ((r * r) * t) * c := by rw [hyc t ht]
        _ = c⁻¹ * (r * r) * c * (c⁻¹ * t * c) := by group
    have hTm'r : ∀ x ∈ Tm', (c⁻¹ * r * c) * x = x * (c⁻¹ * r * c) := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := (hTm'mem x).1 hx
      calc c⁻¹ * r * c * (c⁻¹ * t * c) = c⁻¹ * (r * t) * c := by group
        _ = c⁻¹ * (t * r) * c := by rw [hr t ht]
        _ = c⁻¹ * t * c * (c⁻¹ * r * c) := by group
    have hTm'p : IsPGroup 2 Tm' := IsPGroup.of_card (n := 7) (by rw [hTm'c]; norm_num)
    have hgp : IsPGroup 2 (Subgroup.zpowers (c⁻¹ * r * c)) :=
      IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hr'4]; norm_num)
    have hdvd := dvd_card_sup_zpowers hTm'p hTm'c hgp hTm'r
      (fun h => hr'P (hTm'P h))
    have hle : Tm' ⊔ Subgroup.zpowers (c⁻¹ * r * c) ≤
        centralizerIn (centralizerIn R permTwoA) (c⁻¹ * r * c) := by
      refine sup_le (fun x hx => mem_centralizerIn.2 ⟨hTm'D hx, (hTm'r x hx).symm⟩) ?_
      rw [Subgroup.zpowers_le]
      exact mem_centralizerIn.2 ⟨hr'D, rfl⟩
    have hdvd' := hdvd.trans (Subgroup.card_dvd_of_le hle)
    obtain ⟨s, hs, hsmul⟩ := exists_size_mul_card_cent hOF hr'D hr'4
    rw [hR3840] at hsmul
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> omega

end CFSG.Quasithin.ModH
