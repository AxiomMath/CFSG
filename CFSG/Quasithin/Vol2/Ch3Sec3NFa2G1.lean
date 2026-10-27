module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Defs
public import CFSG.Models.PGLSimple

public section

namespace CFSG.Quasithin.H13.NFa2

theorem nfa2G1_not_dvd_two_pow_sub_one {q j : ℕ} (hq : q.Prime) (h24 : q % 24 = 11 ∨ q % 24 = 13)
    (hj1 : 1 ≤ j) (hj9 : j ≤ 9) : ¬ q ∣ 2 ^ j - 1 := by
  intro hd
  have h2j : 2 ^ 1 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
  have h2j9 : 2 ^ j ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hj9
  rw [pow_one] at h2j
  have h512 : (2 : ℕ) ^ 9 = 512 := by norm_num
  rw [h512] at h2j9
  have hpos : 0 < 2 ^ j - 1 := by omega
  have hqle : q ≤ 511 := by
    have := Nat.le_of_dvd hpos hd
    omega
  obtain ⟨k, hk⟩ : ∃ k, q = 24 * k + 11 ∨ q = 24 * k + 13 := ⟨q / 24, by omega⟩
  have hk21 : k ≤ 21 := by omega
  rcases hk with rfl | rfl <;> interval_cases k <;> interval_cases j <;> (norm_num at hd) <;>
    norm_num at hq

theorem nfa2_G1 : Leaf_G1 := by
  intro q hq h24 Kb _ hmodel X _ _ _ ρ hρ
  obtain ⟨-, hmatch⟩ := hmodel
  obtain ⟨K, hKf, hKfin, hKcard, ⟨eK⟩⟩ := hmatch
  have hq11 : 11 ≤ q := by omega
  have hKq : Nat.card K = q := by rw [hKcard, pow_one]
  haveI hsimP : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL (d := 2) K le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))
  have hsimKb : IsSimpleGroup Kb := eK.isSimpleGroup
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hsimKb.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hρ
      have hkker : k ∈ ρ.ker := by
        rw [h]
        exact Subgroup.mem_top k
      exact hk (MonoidHom.mem_ker.1 hkker)
  have hqKb : q ∣ Nat.card Kb := by
    rw [Nat.card_congr eK.toEquiv]
    haveI : Finite (CFSG.Open.StatedSL 2 K) := by
      haveI : Finite (Matrix.GeneralLinearGroup (Fin 2) K) :=
        Finite.of_injective
          (fun g : Matrix.GeneralLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K))
          (fun a b h => Units.ext h)
      infer_instance
    have hpd : ¬ q ∣ 2 := fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      omega
    have hdeg : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈ CFSG.Open.StatedSL 2 K →
        c ^ 2 = 1 := by
      intro c hc
      rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker,
        Matrix.GeneralLinearGroup.det_scalar] at hc
      simpa using hc
    have hndvd := CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf
      (CFSG.Open.StatedSL 2 K) (d := 2) hq hpd hdeg
    have hcard : Nat.card (CFSG.Open.StatedSL 2 K) = q * (q ^ 2 - 1) := by
      rw [CFSG.Open.StatedAPI.card_statedSL_two K, hKq]
    have hmul : Nat.card ((CFSG.Open.StatedScalars (Fin 2) K).subgroupOf (CFSG.Open.StatedSL 2 K))
        * ((CFSG.Open.StatedScalars (Fin 2) K).subgroupOf (CFSG.Open.StatedSL 2 K)).index
        = Nat.card (CFSG.Open.StatedSL 2 K) :=
      Subgroup.card_mul_index (H := (CFSG.Open.StatedScalars (Fin 2) K).subgroupOf
        (CFSG.Open.StatedSL 2 K))
    have h1 : q ∣ Nat.card ((CFSG.Open.StatedScalars (Fin 2) K).subgroupOf
        (CFSG.Open.StatedSL 2 K)) *
        ((CFSG.Open.StatedScalars (Fin 2) K).subgroupOf (CFSG.Open.StatedSL 2 K)).index := by
      rw [hmul, hcard]
      exact dvd_mul_right q _
    exact ((Nat.Prime.dvd_mul hq).1 h1).resolve_left hndvd
  have hKX : Nat.card Kb ∣ Nat.card (X ≃ₗ[ZMod 2] X) := Subgroup.card_dvd_of_injective ρ hinj
  have hGL : Nat.card (X ≃ₗ[ZMod 2] X) = ∏ i : Fin (Module.finrank (ZMod 2) X),
      (2 ^ Module.finrank (ZMod 2) X - 2 ^ (i : ℕ)) := by
    have eX : Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 2) X)) (ZMod 2) ≃*
        (X ≃ₗ[ZMod 2] X) :=
      (Matrix.GeneralLinearGroup.toLin' (Module.finBasis (ZMod 2) X)).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) X)
    rw [← Nat.card_congr eX.toEquiv, Matrix.card_GL_field, ZMod.card]
  have hqprod : q ∣ ∏ i : Fin (Module.finrank (ZMod 2) X),
      (2 ^ Module.finrank (ZMod 2) X - 2 ^ (i : ℕ)) := by
    rw [← hGL]
    exact dvd_trans hqKb hKX
  obtain ⟨i, -, hi⟩ := (hq.prime.dvd_finsetProd_iff _).1 hqprod
  by_contra hlt
  have hin : (i : ℕ) < Module.finrank (ZMod 2) X := i.2
  have hfac : 2 ^ Module.finrank (ZMod 2) X - 2 ^ (i : ℕ)
      = 2 ^ (i : ℕ) * (2 ^ (Module.finrank (ZMod 2) X - (i : ℕ)) - 1) := by
    have h1 : 2 ^ Module.finrank (ZMod 2) X
        = 2 ^ (i : ℕ) * 2 ^ (Module.finrank (ZMod 2) X - (i : ℕ)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h1, Nat.mul_sub_one]
  rw [hfac] at hi
  rcases (Nat.Prime.dvd_mul hq).1 hi with h2 | h2
  · have h2' := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h2)
    omega
  · exact nfa2G1_not_dvd_two_pow_sub_one hq h24 (by omega) (by omega) h2

end CFSG.Quasithin.H13.NFa2
