module

public import CFSG.Quasithin.Vol2.Ch11SecOE3D
public import CFSG.Quasithin.Vol2.Ch11SecOE3C

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank Matrix
open scoped IsMulCommutative

theorem sylow_isCyclic_of_surjective {A B : Type*} [Group A] [Group B] [Finite A] {p : ℕ}
    [Fact p.Prime] {f : A →* B} (hf : Function.Surjective f)
    (h : ∀ P : Sylow p A, IsCyclic ↥(P : Subgroup A)) : ∀ Q : Sylow p B,
      IsCyclic ↥(Q : Subgroup B) := by
  intro Q
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hf p Q
  have := h P
  rw [Sylow.coe_mapSurjective]
  exact isCyclic_of_surjective (f.subgroupMap (P : Subgroup A)) (f.subgroupMap_surjective _)

theorem center_SL2_eq_bot {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨c, hc, hcx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hx
  have hc2 : c ^ 2 = 1 := by simpa using hc
  have hc1 : c = 1 := by
    have h1 : (c - 1) ^ 2 = 0 := by
      rw [sub_sq, hc2, mul_one, CharTwo.two_eq_zero, zero_mul, sub_zero, one_pow,
        CharTwo.add_self_eq_zero]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h1)
  rw [Subgroup.mem_bot]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [← hcx, hc1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem SL2_sylow_isCyclic {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (h7 : 7 ≤ Nat.card F) {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) :
    ∀ R : Sylow r (SpecialLinearGroup (Fin 2) F),
      IsCyclic ↥(R : Subgroup (SpecialLinearGroup (Fin 2) F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime r (Nat.card F) := by
    rw [hF]
    exact Nat.Coprime.pow_right m ((Nat.coprime_primes Fact.out Nat.prime_two).2 hr2)
  have hP := CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F hF h7 r hr2 hcop
  let e : SpecialLinearGroup (Fin 2) F ≃* ProjectiveSpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq center_SL2_eq_bot.symm))
  exact sylow_isCyclic_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective hP

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {T K I : Subgroup G} {r : ℕ} (h : Setting G T K I r)
include h

theorem not_concl701Four : ¬ Concl701Four T K I := by
  intro h4
  have h1 := h4.1
  rw [h.fsuL0_eq] at h1
  exact lt_irrefl K h1

theorem r_sq_dvd_card_autOn : r ^ 2 ∣ Nat.card ↥(autOn K (fsuV T I)) := by
  obtain ⟨-, -, ⟨E, -, hE⟩, -⟩ := h.shape_autOn
  rw [← hE]
  exact Subgroup.card_subgroup_dvd_card E

theorem not_sq_dvd_M24 (hdvd : r ^ 2 ∣ 244823040) : False := by
  have hr := h.prime
  have hr5 := h.five_le
  have h1 : r ^ 2 ∣ 8855 * 27648 := by norm_num; exact hdvd
  have hcop : Nat.Coprime (r ^ 2) 27648 := by
    have : Nat.Coprime r 27648 := by
      rw [show (27648 : ℕ) = 2 ^ 10 * 3 ^ 3 by norm_num]
      exact Nat.Coprime.mul_right
        (Nat.Coprime.pow_right 10 ((Nat.coprime_primes hr Nat.prime_two).2 (by omega)))
        (Nat.Coprime.pow_right 3 ((Nat.coprime_primes hr Nat.prime_three).2 (by omega)))
    exact Nat.Coprime.pow_left 2 this
  have h2 : r ^ 2 ∣ 8855 := hcop.dvd_of_dvd_mul_right h1
  have h3 : r ^ 2 ≤ 8855 := Nat.le_of_dvd (by norm_num) h2
  have h4 : r ≤ 94 := by nlinarith
  interval_cases r <;> norm_num at h2

theorem not_concl701J4 [IsMulCommutative ↥(fsuV T I)] :
    ¬ Concl701J4 T K I := by
  rintro ⟨-, -, -, -, ⟨π, hπ⟩, -⟩
  have hK : K ≤ fsuM T K := by
    rw [fsuM, h.fsuL0_eq]
    exact Subgroup.le_normalizer
  have hle : autOn K (fsuV T I) ≤ autOn (fsuM T K) (fsuV T I) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ hK)
  have h1 := Subgroup.card_dvd_of_le hle
  have h2 : Nat.card ↥(autOn (fsuM T K) (fsuV T I)) ∣ Nat.card ↥CFSG.Blueprint.NativeSporadic.M24 :=
    Subgroup.card_dvd_of_surjective (f := π) hπ.1
  rw [CFSG.Sporadic.Mathieu.card_M24] at h2
  exact h.not_sq_dvd_M24 (h.r_sq_dvd_card_autOn.trans (h1.trans h2))

theorem not_concl701Orth [IsMulCommutative ↥(fsuV T I)] : ¬ Concl701Orth T K I := by
  rintro ⟨n, hn, F, _, _, _, hF, π, hπ⟩
  have : Fact r.Prime := ⟨h.prime⟩
  have hF7 : 7 ≤ Nat.card F := by
    rw [hF]
    calc 7 ≤ 2 ^ (2 * 2) := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let e : ↥(autOn (fsuL0 T K) (fsuV T I)) ≃* ↥(autOn K (fsuV T I)) :=
    MulEquiv.subgroupCongr (congrArg (fun X => autOn X (fsuV T I)) h.fsuL0_eq)
  have hcyc := sylow_isCyclic_of_surjective
    (f := (e.toMonoidHom.comp π).comp (specialLinearGroupEquivStatedSL 2 F).toMonoidHom)
    (e.surjective.comp (hπ.1.comp (specialLinearGroupEquivStatedSL 2 F).surjective))
    (SL2_sylow_isCyclic hF hF7 (r := r) (by have := h.five_le; omega))
  have hle := CFSG.QuasithinUnique.Id2519.pRank_le_one_of_sylow_cyclic h.prime hcyc
  have h2 := two_le_pRank h.prime h.shape_autOn
  omega

end Setting

end CFSG.Quasithin.Vol2.Ch11.OE3
