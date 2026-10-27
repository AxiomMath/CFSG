module

public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Quasithin

theorem exists_cComp_comm_not_le {Γ : Type} [Group Γ] [Finite Γ] {A : Subgroup Γ}
    (hA : IsPGroup 2 A) (hAO : ¬ A ≤ CFSG.pCore 2 Γ)
    (hF : ∀ p : ℕ, p.Prime → p ≠ 2 → A.map (QuotientGroup.mk' (CFSG.pCore 2 Γ)) ≤
      centralizer (CFSG.pCore p (Γ ⧸ CFSG.pCore 2 Γ) : Set (Γ ⧸ CFSG.pCore 2 Γ))) :
    ∃ K ∈ cComp (⊤ : Subgroup Γ), CFSG.IsComponent (K.map (QuotientGroup.mk' (CFSG.pCore 2 Γ))) ∧
      ¬ ⁅K, A⁆ ≤ CFSG.pCore 2 Γ := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 2 Γ with hO
  set π := QuotientGroup.mk' O with hπ
  set B := A.map π with hB
  have hB2 : IsPGroup 2 B := hA.map π
  have hBne : B ≠ ⊥ := by
    intro h
    apply hAO
    intro a ha
    have : π a ∈ B := mem_map_of_mem π ha
    rw [h, mem_bot] at this
    exact (QuotientGroup.eq_one_iff a).1 this
  have hO2X : CFSG.pCore 2 (Γ ⧸ O) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hBF : B ≤ centralizer (CFSG.fittingSubgroup (Γ ⧸ O) : Set (Γ ⧸ O)) := by
    rw [le_centralizer_iff, A36B.fitting_eq_iSup_primes]
    refine iSup_le fun q => ?_
    by_cases hq : (q : ℕ) = 2
    · have : CFSG.pCore (q : ℕ) (Γ ⧸ O) = ⊥ := by rw [hq]; exact hO2X
      rw [this]
      exact bot_le
    · exact le_centralizer_iff.1 (hF q q.2 hq)
  by_contra hcon
  push Not at hcon
  have hBE : B ≤ centralizer (CFSG.layer (Γ ⧸ O) : Set (Γ ⧸ O)) := by
    rw [le_centralizer_iff, CFSG.layer]
    refine sSup_le fun Kb hKb => ?_
    have hKb' := mem_cComp_top_of_isComponent hKb
    have hsolv : Group.IsSolvable O := by
      have : IsPGroup 2 O := CFSG.pCore_isPGroup
      have := this.isNilpotent
      infer_instance
    obtain ⟨K, hK, rfl⟩ := (cComp_quotient_bijOn O hsolv).surjOn hKb'
    have h1 := hcon K hK hKb
    have h3 : ⁅K.map π, B⁆ = ⊥ := by
      rw [hB, ← map_commutator, Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
      exact h1
    exact (commutator_eq_bot_iff_le_centralizer.1 h3)
  have hBFs : B ≤ centralizer (CFSG.generalizedFitting (Γ ⧸ O) : Set (Γ ⧸ O)) := by
    intro b hb
    rw [mem_centralizer_iff]
    intro x hx
    rw [CFSG.generalizedFitting] at hx
    have h1 : CFSG.fittingSubgroup (Γ ⧸ O) ⊔ CFSG.layer (Γ ⧸ O) ≤
        centralizer ({b} : Set (Γ ⧸ O)) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.1 (hBF hb)) y hy
      · rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.1 (hBE hb)) y hy
    exact mem_centralizer_singleton_iff.1 (h1 hx)
  have hBle : B ≤ CFSG.generalizedFitting (Γ ⧸ O) :=
    hBFs.trans (CFSG.centralizer_generalizedFitting_le _)
  set D := CFSG.generalizedFitting (Γ ⧸ O) ⊓
    centralizer (CFSG.generalizedFitting (Γ ⧸ O) : Set (Γ ⧸ O)) with hD
  have hBD : B ≤ D := le_inf hBle hBFs
  have hFsn : (CFSG.generalizedFitting (Γ ⧸ O)).Normal := by
    have h1 : (CFSG.layer (Γ ⧸ O)).Normal := by
      have := CFSG.LocalCores.layer_characteristic (G := Γ ⧸ O)
      infer_instance
    rw [CFSG.generalizedFitting]
    exact Subgroup.sup_normal _ _
  have hDn : D.Normal := by
    have := hFsn
    exact Subgroup.normal_inf_normal _ _
  have hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.1 hy.2) x hx.1
  let D₂ : Subgroup (Γ ⧸ O) :=
    { carrier := {x | x ∈ D ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}
      one_mem' := ⟨one_mem _, 0, by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, k, hk⟩ ⟨hy, l, hl⟩
        refine ⟨mul_mem hx hy, k + l, ?_⟩
        have hx' : x ^ 2 ^ (k + l) = 1 := by rw [pow_add, pow_mul, hk, one_pow]
        have hy' : y ^ 2 ^ (k + l) = 1 := by rw [add_comm, pow_add, pow_mul, hl, one_pow]
        rw [Commute.mul_pow (hDc x hx y hy), hx', hy', one_mul]
      inv_mem' := by
        rintro x ⟨hx, k, hk⟩
        exact ⟨inv_mem hx, k, by rw [inv_pow, hk, inv_one]⟩ }
  have hD₂n : D₂.Normal := ⟨fun x hx g => ⟨hDn.conj_mem x hx.1 g, hx.2.choose, by
    rw [conj_pow, hx.2.choose_spec]
    group⟩⟩
  have hD₂p : IsPGroup 2 D₂ := fun x => ⟨x.2.2.choose, Subtype.ext (by
    simpa using x.2.2.choose_spec)⟩
  have hD₂O : D₂ ≤ CFSG.pCore 2 (Γ ⧸ O) := le_sSup ⟨hD₂n, hD₂p⟩
  have hBD₂ : B ≤ D₂ := fun b hb => by
    obtain ⟨k, hk⟩ := hB2 ⟨b, hb⟩
    exact ⟨hBD hb, k, by simpa using congrArg Subtype.val hk⟩
  apply hBne
  rw [eq_bot_iff, ← hO2X]
  exact hBD₂.trans hD₂O

end CFSG.Quasithin.H13.U3
