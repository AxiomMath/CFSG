module

public import CFSG.Sporadic.Recognition.LyonsAS44Facts

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.McLAS

section Delta

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}
  {R T A : Subgroup (CentQuot (x₁ : G))} {Y : Fin 10 → CentQuot (x₁ : G)}

namespace LyData

theorem not_isConj_x₁_torus (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (k : ℤ) :
    ¬ IsConj (x₁ : G) ((x₁ : G) ^ k * (x₂ : G) * (x₃ : G)) := by
  intro hc
  have hw3 : (x₁ ^ k * x₂ ^ (1 : ℤ) * x₃ ^ (1 : ℤ)) ^ 3 = 1 := D.pow_three_torus S k 1 1
  have hwG : ((x₁ ^ k * x₂ ^ (1 : ℤ) * x₃ ^ (1 : ℤ) : ↥(centralizer ({t} : Set G))) : G) =
      (x₁ : G) ^ k * (x₂ : G) * (x₃ : G) := by simp
  rw [← hwG] at hc
  have hs := D.card_support_rho_eq_three S hw3 hc
  rw [rho_torus S] at hs
  have h3 := torus_three_cases k 1 1 hs
  rcases zpow_cases x1p_pow_three k with hk | hk | hk <;> rw [hk] at h3 <;>
    revert h3 <;> decide

omit [Finite G] in
theorem exists_lift_conj {u v : ↥(centralizer ({(x₁ : G)} : Set G))}
    (h : IsConj (projQ (x₁ : G) v) (projQ (x₁ : G) u)) :
    ∃ (m : ↥(centralizer ({(x₁ : G)} : Set G))) (k : ℤ),
      (u : G) = (m : G) * ((v : G) * (x₁ : G) ^ k) * (m : G)⁻¹ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  obtain ⟨m, rfl⟩ := projQ_surjective (x₁ : G) c
  have h1 : projQ (x₁ : G) (m * v * m⁻¹) = projQ (x₁ : G) u := by
    rw [map_mul, map_mul, map_inv]; exact hc
  have h2 : (m * v * m⁻¹)⁻¹ * u ∈ (projQ (x₁ : G)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  rw [ker_projQ] at h2
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h2
  have hk' : (x₁ : G) ^ k = ((m : G) * (v : G) * (m : G)⁻¹)⁻¹ * (u : G) := by
    have := congrArg Subtype.val hk
    simpa using this
  have hmx : (m : G) * (x₁ : G) ^ k = (x₁ : G) ^ k * (m : G) :=
    (Commute.zpow_right (show Commute (m : G) (x₁ : G) from
      mem_centralizer_singleton_iff.1 m.2) k).eq
  refine ⟨m, k, ?_⟩
  calc (u : G) = (m : G) * (v : G) * (m : G)⁻¹ * (x₁ : G) ^ k := by rw [hk']; group
    _ = (m : G) * ((v : G) * (x₁ : G) ^ k) * (m : G)⁻¹ := by
      calc (m : G) * (v : G) * (m : G)⁻¹ * (x₁ : G) ^ k
          = (m : G) * (v : G) * ((m : G)⁻¹ * (x₁ : G) ^ k) := by group
        _ = (m : G) * (v : G) * ((x₁ : G) ^ k * (m : G)⁻¹) := by
          congr 1
          have := congrArg (fun z => (m : G)⁻¹ * z * (m : G)⁻¹) hmx
          simpa [mul_assoc] using this.symm
        _ = (m : G) * ((v : G) * (x₁ : G) ^ k) * (m : G)⁻¹ := by group

omit [Finite G] in
theorem pow_three_of_isConj_x₁ (S : LyStd ρ x₁ x₂ x₃) {w : G} (hw : IsConj (x₁ : G) w) :
    w ^ 3 = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hw
  have hx3G : (x₁ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val S.pow₁
  rw [conj_pow, hx3G]
  group

theorem zpow_eq_one_of_isConj_x₂_mul (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {k : ℤ}
    (h : IsConj (x₁ : G) ((x₂ : G) * (x₁ : G) ^ k)) : (x₁ : G) ^ k = 1 := by
  have hmem : (x₂ : G) * (x₁ : G) ^ k ∈ Subgroup.closure ({(x₁ : G), (x₂ : G)} : Set G) :=
    Subgroup.mul_mem _ (subset_closure (by simp))
      (Subgroup.zpow_mem _ (subset_closure (by simp)) k)
  have hρ : ρ (x₂ * x₁ ^ k) = x2p * x1p ^ k := by rw [map_mul, map_zpow, S.rho₂, S.rho₁]
  have hG : ∀ w : ↥(centralizer ({t} : Set G)), (x₂ : G) * (x₁ : G) ^ k = (w : G) →
      x₂ * x₁ ^ k = w := fun w hw => Subtype.ext (by simpa using hw)
  rcases D.eq_of_isConj_mem_closure_two S hmem h with h1 | h1 | h1 | h1
  · exfalso
    have := congrArg ρ (hG x₁ h1)
    rw [hρ, S.rho₁] at this
    rcases zpow_cases x1p_pow_three k with hk | hk | hk <;> rw [hk] at this <;>
      revert this <;> decide
  · exfalso
    have h2 : (x₂ : G) * (x₁ : G) ^ k = ((x₁⁻¹ : ↥(centralizer ({t} : Set G))) : G) := by
      rw [h1]; simp
    have := congrArg ρ (hG _ h2)
    rw [hρ, map_inv, S.rho₁] at this
    rcases zpow_cases x1p_pow_three k with hk | hk | hk <;> rw [hk] at this <;>
      revert this <;> decide
  · simpa using h1
  · exfalso
    have h2 : (x₂ : G) * (x₁ : G) ^ k = ((x₂⁻¹ : ↥(centralizer ({t} : Set G))) : G) := by
      rw [h1]; simp
    have := congrArg ρ (hG _ h2)
    rw [hρ, map_inv, S.rho₂] at this
    rcases zpow_cases x1p_pow_three k with hk | hk | hk <;> rw [hk] at this <;>
      revert this <;> decide

theorem exists_conj_eq_x₂ (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (F : LyAFacts D S R T A Y)
    {u : ↥(centralizer ({(x₁ : G)} : Set G))} (hu : IsConj (x₁ : G) (u : G))
    (h1 : projQ (x₁ : G) u ≠ 1) :
    ∃ m : ↥(centralizer ({(x₁ : G)} : Set G)), (u : G) = (m : G) * (x₂ : G) * (m : G)⁻¹ := by
  have hu3 : (u : G) ^ 3 = 1 := pow_three_of_isConj_x₁ S hu
  have hq3 : projQ (x₁ : G) u ^ 3 = 1 := by
    rw [← map_pow]
    have : u ^ 3 = 1 := Subtype.ext (by simpa using hu3)
    rw [this, map_one]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf (projQ (x₁ : G) u) = 3 := orderOf_eq_prime hq3 h1
  have hcomm₂ : (x₂ : G) * (x₁ : G) = (x₁ : G) * (x₂ : G) := D.comm₂₁ S
  have hcomm₃ : (x₃ : G) * (x₁ : G) = (x₁ : G) * (x₃ : G) := D.comm₃₁ S
  have hcomm₂₃ : (x₃ : G) * (x₂ : G) = (x₂ : G) * (x₃ : G) := D.comm₃₂ S
  have hy : IsConj (projQ (x₁ : G) u) (D.x₂Q S) := by
    rcases F.classes _ hord with h | h
    · exact h
    · exfalso
      let v : ↥(centralizer ({(x₁ : G)} : Set G)) := D.x₂M S * D.x₃M S
      have hpv : projQ (x₁ : G) v = D.x₂Q S * D.x₃Q S := by
        rw [map_mul]; rfl
      obtain ⟨m, k, hmk⟩ := exists_lift_conj (u := u) (v := v) (by rw [hpv]; exact h.symm)
      have hvG : (v : G) = (x₂ : G) * (x₃ : G) := rfl
      have hx1k : (x₁ : G) ^ k * ((x₂ : G) * (x₃ : G)) = (x₂ : G) * (x₃ : G) * (x₁ : G) ^ k := by
        have h12 : Commute (x₁ : G) (x₂ : G) := hcomm₂.symm
        have h13 : Commute (x₁ : G) (x₃ : G) := hcomm₃.symm
        exact ((h12.zpow_left k).mul_right (h13.zpow_left k)).eq
      have hconj : IsConj ((x₂ : G) * (x₃ : G) * (x₁ : G) ^ k) (u : G) :=
        isConj_iff.2 ⟨m, by rw [hmk, hvG]⟩
      exact D.not_isConj_x₁_torus S k (by
        rw [mul_assoc, hx1k]
        exact hu.trans hconj.symm)
  obtain ⟨m, k, hmk⟩ := exists_lift_conj (u := u) (v := D.x₂M S) (by
    exact hy.symm)
  have hconj : IsConj ((x₂ : G) * (x₁ : G) ^ k) (u : G) :=
    isConj_iff.2 ⟨m, by rw [hmk]; rfl⟩
  have hk := D.zpow_eq_one_of_isConj_x₂_mul S (hu.trans hconj.symm)
  exact ⟨m, by rw [hmk]; show _ = _; rw [hk]; simp [LyData.x₂M]⟩

theorem eq_of_isConj_of_proj_eq (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (F : LyAFacts D S R T A Y) {u v : ↥(centralizer ({(x₁ : G)} : Set G))}
    (hu : IsConj (x₁ : G) (u : G)) (hv : IsConj (x₁ : G) (v : G))
    (h : projQ (x₁ : G) u = projQ (x₁ : G) v) (h1 : projQ (x₁ : G) u ≠ 1) : u = v := by
  obtain ⟨m, hm⟩ := D.exists_conj_eq_x₂ S F hu h1
  obtain ⟨m', hm'⟩ := D.exists_conj_eq_x₂ S F hv (h ▸ h1)
  have hmm : (QuotientGroup.mk (m'⁻¹ * m) : CentQuot (x₁ : G)) * D.x₂Q S =
      D.x₂Q S * QuotientGroup.mk (m'⁻¹ * m) := by
    have hu' : u = m * D.x₂M S * m⁻¹ := Subtype.ext (by simpa [LyData.x₂M] using hm)
    have hv' : v = m' * D.x₂M S * m'⁻¹ := Subtype.ext (by simpa [LyData.x₂M] using hm')
    have h2 : projQ (x₁ : G) (m * D.x₂M S * m⁻¹) = projQ (x₁ : G) (m' * D.x₂M S * m'⁻¹) := by
      rw [← hu', ← hv']; exact h
    simp only [map_mul, map_inv, projQ_apply] at h2
    change QuotientGroup.mk m * D.x₂Q S * (QuotientGroup.mk m)⁻¹ =
      QuotientGroup.mk m' * D.x₂Q S * (QuotientGroup.mk m')⁻¹ at h2
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    calc (QuotientGroup.mk m' : CentQuot (x₁ : G))⁻¹ * QuotientGroup.mk m * D.x₂Q S
        = (QuotientGroup.mk m')⁻¹ * (QuotientGroup.mk m * D.x₂Q S * (QuotientGroup.mk m)⁻¹) *
            QuotientGroup.mk m := by group
      _ = (QuotientGroup.mk m')⁻¹ * (QuotientGroup.mk m' * D.x₂Q S * (QuotientGroup.mk m')⁻¹) *
            QuotientGroup.mk m := by rw [h2]
      _ = D.x₂Q S * ((QuotientGroup.mk m')⁻¹ * QuotientGroup.mk m) := by group
  have hc := D.commute_of_mk_commute S hmm
  apply Subtype.ext
  rw [hm, hm']
  have hc' : (m' : G)⁻¹ * (m : G) * (x₂ : G) = (x₂ : G) * ((m' : G)⁻¹ * (m : G)) := by
    simpa using hc
  calc (m : G) * (x₂ : G) * (m : G)⁻¹
      = (m' : G) * ((m' : G)⁻¹ * (m : G) * (x₂ : G)) * (m : G)⁻¹ := by group
    _ = (m' : G) * ((x₂ : G) * ((m' : G)⁻¹ * (m : G))) * (m : G)⁻¹ := by rw [hc']
    _ = (m' : G) * (x₂ : G) * (m' : G)⁻¹ := by group

omit [Finite G] in
theorem exists_lift_isConj (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {q : CentQuot (x₁ : G)}
    (hq : IsConj (D.x₂Q S) q) :
    ∃ u : ↥(centralizer ({(x₁ : G)} : Set G)), projQ (x₁ : G) u = q ∧
      IsConj (x₁ : G) (u : G) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hq
  obtain ⟨m, rfl⟩ := projQ_surjective (x₁ : G) c
  refine ⟨m * D.x₂M S * m⁻¹, ?_, ?_⟩
  · rw [← hc, map_mul, map_mul, map_inv]; rfl
  · have h12 := D.isConj_x₁_x₂ S
    exact h12.trans (isConj_iff.2 ⟨(m : G), rfl⟩)

end LyData

end Delta

end CFSG.Sporadic.Recognition.LyonsSims
