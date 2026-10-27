module

public import CFSG.RankThree.PartOne.S12.Sec153Weyl
public import CFSG.RankThree.PartOne.S12.Sec125

public section

namespace CFSG.RankThree.PartOne.K156

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne

variable {G : Type} [Group G] {p : ℕ} {E : Subgroup G}

omit [Group G] in
theorem exists_fin_five_ne (a b c : Fin 5) : ∃ j : Fin 5, j ≠ a ∧ j ≠ b ∧ j ≠ c := by
  revert a b c
  decide

theorem rel_three (M : Sec153.ModData p E) (hEc : ∀ a b : ↥E, a * b = b * a) {x y z : Fin 5}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {a b c : ℤ}
    (h : M.v x ^ a * M.v y ^ b * M.v z ^ c = 1) : (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c := by
  classical
  let _ : CommGroup ↥E := Sec153.commE hEc
  obtain ⟨j, hjx, hjy, hjz⟩ := exists_fin_five_ne x y z
  set e : Fin 5 → ℤ := fun k =>
    (if k = x then a else 0) + (if k = y then b else 0) + (if k = z then c else 0) with he
  have hprod : M.v 0 ^ e 0 * M.v 1 ^ e 1 * M.v 2 ^ e 2 * M.v 3 ^ e 3 * M.v 4 ^ e 4 = 1 := by
    rw [← Fin.prod_univ_five (fun k => M.v k ^ e k)]
    have hsplit : ∀ k : Fin 5, M.v k ^ e k =
        (if k = x then M.v k ^ a else 1) * (if k = y then M.v k ^ b else 1) *
          (if k = z then M.v k ^ c else 1) := by
      intro k
      simp only [he, zpow_add]
      split_ifs <;> simp
    rw [Finset.prod_congr rfl fun k _ => hsplit k, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ x (fun k => M.v k ^ a),
      Finset.prod_ite_eq' Finset.univ y (fun k => M.v k ^ b),
      Finset.prod_ite_eq' Finset.univ z (fun k => M.v k ^ c)]
    simpa using h
  obtain ⟨m, hm⟩ := (M.rel e).1 hprod
  have hj : (p : ℤ) ∣ m := by
    have h0 : e j = 0 := by simp [he, hjx, hjy, hjz]
    have := hm j
    rw [h0] at this
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · have hex : e x = a := by simp [he, hxy, hxz]
    have := hm x
    rw [hex] at this
    simpa using dvd_add this hj
  · have hey : e y = b := by simp [he, hxy.symm, hyz]
    have := hm y
    rw [hey] at this
    simpa using dvd_add this hj
  · have hez : e z = c := by simp [he, hxz.symm, hyz.symm]
    have := hm z
    rw [hez] at this
    simpa using dvd_add this hj

omit [Group G] in
theorem grp_aux {M : Type*} [CommGroup M] (x y z : M) (k : ℤ)
    (h : (x * y⁻¹) ^ k = z * x⁻¹) : z ^ (1 : ℤ) * x ^ (-1 - k) * y ^ k = 1 := by
  have h1 : z ^ (1 : ℤ) * x ^ (-1 - k) * y ^ k = (z * x⁻¹) * ((x * y⁻¹) ^ k)⁻¹ := by
    simp only [mul_zpow, mul_inv_rev, inv_zpow', zpow_sub, zpow_neg, zpow_one, inv_inv]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [h1, h, mul_inv_cancel]

theorem mul_inv_mem_autMoved (φ : MulAut E) (e : ↥E) : φ e * e⁻¹ ∈ autMoved E φ :=
  Subgroup.subset_closure ⟨e, rfl⟩

variable [Finite G]

theorem not_torusHasTransvection_five (hMod : KFU5Mod) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) : ¬ torusHasTransvection p E := by
  classical
  have h := h15.h12
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have : Fact p.Prime := ⟨hp⟩
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => hEel.is_comm.comm a b
  have hEp : ∀ e : ↥E, e ^ p = 1 := fun e => Subtype.ext (by
    simpa using elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) (e : G) e.2)
  obtain ⟨M⟩ := Sec153.nonempty_modData hMod h15 hF hout
  rintro ⟨φ, hφW, hφ⟩
  have hφp : φ ^ p = 1 := Sec125.pow_eq_one_of_isAutTransvection hEel hφ
  have hφI : φ ∈ reflectionGroup p E :=
    M.mem_of_pPower hp hEc hEp hφW (a := 1) (by simpa using hφp)
  set σ : Equiv.Perm (Fin 5) := M.θ ⟨φ, hφI⟩ with hσ
  have hσ1 : σ ≠ 1 := by
    intro h1
    have h2 : (⟨φ, hφI⟩ : ↥(reflectionGroup p E)) = 1 := M.θ.injective (by rw [← hσ, h1, map_one])
    exact hφ.1 (congrArg Subtype.val h2)
  have hσp : σ ^ p = 1 := by
    have h2 : (⟨φ, hφI⟩ : ↥(reflectionGroup p E)) ^ p = 1 := Subtype.ext hφp
    rw [hσ, ← map_pow, h2, map_one]
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  have hp120 : p ∣ 120 := by
    have := orderOf_dvd_natCard σ
    rwa [hσord, Nat.card_perm, Nat.card_fin, show Nat.factorial 5 = 120 by decide] at this
  have hp5' : p = 5 := by
    have h120 : (120 : ℕ) = 2 ^ 3 * 3 * 5 := by norm_num
    rw [h120] at hp120
    rcases (Nat.Prime.dvd_mul hp).1 hp120 with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
        omega
      · have := Nat.le_of_dvd (by norm_num) h2
        omega
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h1
  have hσ5 : σ ^ 5 = 1 := hp5' ▸ hσp
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra hcon
    push Not at hcon
    exact hσ1 (Equiv.ext hcon)
  have hi2 : σ (σ i) ≠ i := by
    intro h2
    apply hi
    have h4 : (σ ^ 4) i = i := by
      have h22 : (σ ^ 2) i = i := by simpa [pow_two] using h2
      calc (σ ^ 4) i = (σ ^ 2 * σ ^ 2) i := by rw [← pow_add]
        _ = i := by rw [Equiv.Perm.mul_apply, h22, h22]
    have h5 : (σ ^ 5) i = σ i := by
      calc (σ ^ 5) i = (σ * σ ^ 4) i := by rw [← pow_succ']
        _ = σ i := by rw [Equiv.Perm.mul_apply, h4]
    rw [hσ5] at h5
    exact h5.symm
  have hi3 : σ (σ i) ≠ σ i := fun h2 => hi (σ.injective h2)
  have hperm : ∀ j : Fin 5, φ (M.v j) = M.v (σ j) := fun j => M.perm ⟨φ, hφI⟩ j
  have hmov0 : M.v (σ i) * (M.v i)⁻¹ ∈ autMoved E φ := by
    have := mul_inv_mem_autMoved φ (M.v i)
    rwa [hperm] at this
  have hmov1 : M.v (σ (σ i)) * (M.v (σ i))⁻¹ ∈ autMoved E φ := by
    have := mul_inv_mem_autMoved φ (M.v (σ i))
    rwa [hperm] at this
  let _ : CommGroup ↥E := Sec153.commE hEc
  have hne0 : (⟨M.v (σ i) * (M.v i)⁻¹, hmov0⟩ : ↥(autMoved E φ)) ≠ 1 := by
    intro h1
    have h2 : M.v (σ i) * (M.v i)⁻¹ = 1 := congrArg Subtype.val h1
    have := (rel_three M hEc (x := σ i) (y := i) (z := σ (σ i)) hi (by exact fun h => hi3 h.symm)
      (fun h => hi2 h.symm) (a := 1) (b := -1) (c := 0) (by simpa using h2)).1
    have h3 : (p : ℤ) ∣ 1 := by simpa using this
    have := Int.eq_one_of_dvd_one (by positivity) h3
    omega
  have hcard : Nat.card ↥(autMoved E φ) = p := hφ.2.1
  have hzp := zpowers_eq_top_of_prime_card hcard hne0
  have hmem : (⟨M.v (σ (σ i)) * (M.v (σ i))⁻¹, hmov1⟩ : ↥(autMoved E φ)) ∈
      Subgroup.zpowers (⟨M.v (σ i) * (M.v i)⁻¹, hmov0⟩ : ↥(autMoved E φ)) := by
    rw [hzp]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hk' : (M.v (σ i) * (M.v i)⁻¹) ^ k = M.v (σ (σ i)) * (M.v (σ i))⁻¹ :=
    congrArg Subtype.val hk
  have hrel : M.v (σ (σ i)) ^ (1 : ℤ) * M.v (σ i) ^ (-1 - k) * M.v i ^ k = 1 :=
    grp_aux _ _ _ k hk'
  have := (rel_three M hEc (x := σ (σ i)) (y := σ i) (z := i) hi3 hi2 hi
    (a := 1) (b := -1 - k) (c := k) hrel).1
  have h3 : (p : ℤ) ∣ 1 := by simpa using this
  have := Int.eq_one_of_dvd_one (by positivity) h3
  omega

end CFSG.RankThree.PartOne.K156
