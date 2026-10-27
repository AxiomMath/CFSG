module

public import CFSG.Quasithin.Vol2.Asc94.HeJ1
public import CFSG.Quasithin.Vol2.Asc94.HeM2
public import CFSG.Quasithin.Vol2.Asc94.TSModel1

public section

namespace CFSG.Quasithin.A94.He42SE

open CFSG.Quasithin.A94 CFSG.Quasithin.A94.L52

theorem gl2_order3_entry : ∀ g : HeJ.GL2, g ^ 3 = 1 → g ≠ 1 → g.val 1 0 = 1 := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem he42s4_gl3_order3_no_involution :
    ∀ A B : Matrix (Fin 3) (Fin 3) (ZMod 2), A * A * A = 1 → A ≠ 1 → B * B = 1 → B ≠ 1 →
      A * B ≠ B * A := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem he42s4_gl3_order7_no_involution :
    ∀ A B : Matrix (Fin 3) (Fin 3) (ZMod 2), A * A * A * A * A * A * A = 1 → A ≠ 1 →
      B * B = 1 → B ≠ 1 → A * B ≠ B * A := by
  decide +kernel

theorem piHom_ne_one_of_zC {x : L52.Hc} (h : L52.zC x 1 0 = 1) : L52.piHom x ≠ 1 := by
  intro hx
  have hb : L52.blk (L52.cm x) = 1 := congrArg Units.val hx
  have h02 : L52.cm x (L52.idx3 0) (L52.idx3 2) = 0 := by
    have h := congrFun (congrFun hb 0) 2
    rwa [L52.blk_apply, Matrix.one_apply_ne (show (0 : Fin 3) ≠ 2 by decide)] at h
  have h' : L52.cm x (L52.rIdx 1) (L52.cIdx 0) = 1 := h
  have e1 : L52.idx3 0 = L52.rIdx 1 := by decide
  have e2 : L52.idx3 2 = L52.cIdx 0 := by decide
  rw [e1, e2, h'] at h02
  exact absurd h02 (by decide)

theorem isPGroup_centralizer_of_piHom_ne_one {y : L52.Hc} (hy : L52.piHom y ≠ 1) (hy2 : y * y = 1) :
    IsPGroup 2 (Subgroup.centralizer ({y} : Set L52.Hc)) := by
  haveI : Finite L52.Hc := Nat.finite_of_card_ne_zero (by rw [L52.card_Hc]; norm_num)
  have hprime : ∀ {q : ℕ}, q.Prime →
      q ∣ Nat.card (Subgroup.centralizer ({y} : Set L52.Hc)) → q = 2 := by
    intro q hq hqd
    by_contra hq2
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨g, hg⟩ :=
      exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({y} : Set L52.Hc)) q hqd
    have hgq : orderOf (g : L52.Hc) = q := by rw [Subgroup.orderOf_coe, hg]
    have hdvd : q ∣ 21504 := by
      rw [← L52.card_Hc, ← hgq]
      exact orderOf_dvd_natCard _
    have hcases : q = 3 ∨ q = 7 := by
      have h21504 : (21504 : ℕ) = 2 ^ 10 * 3 * 7 := by norm_num
      rw [h21504] at hdvd
      rcases (Nat.Prime.dvd_mul hq).1 hdvd with h1 | h7
      · rcases (Nat.Prime.dvd_mul hq).1 h1 with h2 | h3
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h2)) hq2
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h3)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7)).1 h7)
    have hne : L52.piHom (g : L52.Hc) ≠ 1 := by
      intro h1
      have hmem : (g : L52.Hc) ∈ L52.Qh := MonoidHom.mem_ker.2 h1
      have hord : orderOf (⟨(g : L52.Hc), hmem⟩ : L52.Qh) = q := by
        rw [Subgroup.orderOf_mk, hgq]
      have hd : q ∣ 128 := by
        rw [← L52.card_Qh, ← hord]
        exact orderOf_dvd_natCard _
      have h128 : (128 : ℕ) = 2 ^ 7 := by norm_num
      rw [h128] at hd
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hd))
    have hcomm : (L52.piHom (g : L52.Hc) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (L52.piHom y : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        (L52.piHom y : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          (L52.piHom (g : L52.Hc) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.1 g.2]
    have hB2 : (L52.piHom y : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (L52.piHom y : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
      rw [← Units.val_mul, ← map_mul, hy2, map_one, Units.val_one]
    have hB1 : (L52.piHom y : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 := fun h => hy (Units.ext h)
    have hA1 : (L52.piHom (g : L52.Hc) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 :=
      fun h => hne (Units.ext h)
    rcases hcases with rfl | rfl
    · have hg3 : (g : L52.Hc) ^ 3 = 1 := by
        have h := pow_orderOf_eq_one (g : L52.Hc)
        rwa [hgq] at h
      have hA : (L52.piHom (g : L52.Hc)) ^ 3 = 1 := by
        rw [← map_pow, hg3, map_one]
      have hA' := congrArg Units.val hA
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_three'] at hA'
      exact he42s4_gl3_order3_no_involution _ _ hA' hA1 hB2 hB1 hcomm
    · have hg7 : (g : L52.Hc) ^ 7 = 1 := by
        have h := pow_orderOf_eq_one (g : L52.Hc)
        rwa [hgq] at h
      have hA : (L52.piHom (g : L52.Hc)) ^ 7 = 1 := by
        rw [← map_pow, hg7, map_one]
      have hA' := congrArg Units.val hA
      rw [Units.val_pow_eq_pow_val, Units.val_one] at hA'
      simp only [pow_succ, pow_zero, one_mul] at hA'
      exact he42s4_gl3_order7_no_involution _ _ hA' hA1 hB2 hB1 hcomm
  have hpos : Nat.card (Subgroup.centralizer ({y} : Set L52.Hc)) ≠ 0 := Nat.card_pos.ne'
  have hk := Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) hpos (fun hd hdvd => hprime hd hdvd)
  exact IsPGroup.iff_card.2 ⟨_, hk⟩

end CFSG.Quasithin.A94.He42SE
