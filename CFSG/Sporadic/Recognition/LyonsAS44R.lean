module

public import CFSG.Sporadic.Recognition.LyonsAS44Frattini
public import CFSG.Sporadic.Recognition.LyonsAS44Act
public import CFSG.Sporadic.Recognition.LyonsAS44Q8

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.McLAS
open scoped commutatorElement

section R

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}
  {R T A : Subgroup (CentQuot (x₁ : G))} {Y : Fin 10 → CentQuot (x₁ : G)}

namespace LyData

variable (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (F : LyAFacts D S R T A Y)

include D S F

omit [Finite G] in
theorem x₂Q_mem_R : D.x₂Q S ∈ R := by
  have h1 : D.x₂Q S ∈ zpowers (D.x₂Q S) := mem_zpowers _
  rw [← F.mcl.threeCore.comm] at h1
  exact commutator_le_of_le (le_refl R) (le_refl R) h1

omit [Finite G] in
theorem x₂_mem_RG : (x₂ : G) ∈ preimQ (x₁ : G) R :=
  mem_preimQ.2 ⟨mem_centralizer_singleton_iff.2 (D.comm₂₁ S), D.x₂Q_mem_R S F⟩

theorem threeCoreE_RG : ThreeCoreE (x₁ : G) (x₂ : G) (preimQ (x₁ : G) R) := by
  have hRs := F.mcl.threeCore
  have hQ := D.QE_eq_preimQ S
  have hcard : Nat.card ↥(preimQ (x₁ : G) R) = 729 := by
    rw [card_preimQ, orderOf_x₁ S, hRs.card]
  refine ⟨?_, ?_, ?_, hcard, ?_, x_mem_preimQ _, D.x₂_mem_RG S F⟩
  · rw [hQ]; exact preimQ_mono hRs.le_cent
  · intro g hg r hr
    rw [hQ] at hg
    obtain ⟨hgc, hgK⟩ := mem_preimQ.1 hg
    obtain ⟨hrc, hrK⟩ := mem_preimQ.1 hr
    have hmc : g * r * g⁻¹ ∈ centralizer ({(x₁ : G)} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgc hrc) (Subgroup.inv_mem _ hgc)
    refine mem_preimQ.2 ⟨hmc, ?_⟩
    have : (⟨g * r * g⁻¹, hmc⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) =
        ⟨g, hgc⟩ * ⟨r, hrc⟩ * ⟨g, hgc⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    exact hRs.normal _ hgK _ hrK
  · exact IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)
  · intro J hJQ hJn hJ3
    rw [hQ] at hJQ hJn
    have hJc : J ≤ centralizer ({(x₁ : G)} : Set G) := hJQ.trans (preimQ_le_centralizer _)
    rw [le_preimQ_iff hJc]
    refine hRs.max _ ?_ (imQ_normalized hJn) (imQ_isPGroup hJc hJ3)
    rw [← le_preimQ_iff hJc]
    exact hJQ

omit [Finite G] in
theorem mem_RG_or_AG_of_orderOf_three {w : G} (hw : w ∈ preimQ (x₁ : G) T)
    (hw3 : orderOf w = 3) : w ∈ preimQ (x₁ : G) R ∨ w ∈ preimQ (x₁ : G) A := by
  obtain ⟨hwM, hwT⟩ := mem_preimQ.1 hw
  by_cases h1 : projQ (x₁ : G) ⟨w, hwM⟩ = 1
  · have hker : (⟨w, hwM⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) ∈ (projQ (x₁ : G)).ker := h1
    rw [ker_projQ] at hker
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hker
    have hwj : w = (x₁ : G) ^ j := by
      have := congrArg Subtype.val hj
      simpa using this.symm
    left
    rw [hwj]
    exact Subgroup.zpow_mem _ (x_mem_preimQ R) j
  · have hw3' : w ^ 3 = 1 := by simpa [hw3] using pow_orderOf_eq_one w
    have hq3 : projQ (x₁ : G) ⟨w, hwM⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨w, hwM⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hw3')
      rw [this, map_one]
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hord : orderOf (projQ (x₁ : G) ⟨w, hwM⟩) = 3 := orderOf_eq_prime hq3 h1
    rcases F.mcl.order_three _ hwT hord with hR | hAA
    · exact Or.inl (mem_preimQ.2 ⟨hwM, hR⟩)
    · exact Or.inr (mem_preimQ.2 ⟨hwM, hAA⟩)


omit [Finite G] D F in
theorem eq_x₁_or_inv_of_proj_eq_one {w : G} (hwM : w ∈ centralizer ({(x₁ : G)} : Set G))
    (hwc : IsConj (x₁ : G) w) (h1 : projQ (x₁ : G) ⟨w, hwM⟩ = 1) :
    w = (x₁ : G) ∨ w = (x₁ : G)⁻¹ := by
  have hx3G := x₁_pow_three S
  have hker : (⟨w, hwM⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) ∈ (projQ (x₁ : G)).ker := h1
  rw [ker_projQ] at hker
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hker
  have hwj : w = (x₁ : G) ^ j := by
    have := congrArg Subtype.val hj
    simpa using this.symm
  rcases zpow_cases hx3G j with h | h | h
  · exfalso
    rw [hwj, h] at hwc
    have h1' : (x₁ : G) = 1 := isConj_one_left.1 hwc
    have h3 := orderOf_x₁ S
    rw [h1', orderOf_one] at h3
    exact absurd h3 (by norm_num)
  · exact Or.inl (hwj.trans h)
  · refine Or.inr ?_
    rw [hwj, h]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hx3G)

theorem deltaIn_RG_eq :
    deltaIn (x₁ : G) (preimQ (x₁ : G) R) = {zpowers (x₁ : G), zpowers (x₂ : G)} := by
  ext B
  rw [mem_deltaIn_iff]
  constructor
  · rintro ⟨w, hwc, hwR, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    obtain ⟨hwM, hwq⟩ := mem_preimQ.1 hwR
    by_cases h1 : projQ (x₁ : G) ⟨w, hwM⟩ = 1
    · left
      rcases eq_x₁_or_inv_of_proj_eq_one S hwM hwc h1 with h | h
      · rw [h]
      · rw [h]; exact zpowers_inv
    · right
      have hy := D.isConj_proj_of_isConj S F (u := ⟨w, hwM⟩) hwc h1
      have hv : IsConj (x₁ : G) ((D.x₂M S : ↥(centralizer ({(x₁ : G)} : Set G))) : G) :=
        D.isConj_x₁_x₂ S
      rcases F.mcl.weakly_closed _ hwq hy with h | h
      · have := D.eq_of_isConj_of_proj_eq S F (u := ⟨w, hwM⟩) (v := D.x₂M S) hwc hv h h1
        have hw2 : w = (x₂ : G) := congrArg Subtype.val this
        rw [hw2]
      · have hinv : IsConj (x₁ : G) (((⟨w, hwM⟩ : ↥(centralizer ({(x₁ : G)} : Set G)))⁻¹ :
            ↥(centralizer ({(x₁ : G)} : Set G))) : G) :=
          isConj_inv_of_isConj hwc (D.isConj_x₁_inv S F)
        have h' : projQ (x₁ : G) (⟨w, hwM⟩ : ↥(centralizer ({(x₁ : G)} : Set G)))⁻¹ =
            projQ (x₁ : G) (D.x₂M S) := by
          rw [map_inv, h, inv_inv]; rfl
        have := D.eq_of_isConj_of_proj_eq S F (u := (⟨w, hwM⟩ : ↥(centralizer
          ({(x₁ : G)} : Set G)))⁻¹) (v := D.x₂M S) hinv hv h' (by
            rw [map_inv]; exact inv_ne_one.2 h1)
        have hw2 : w⁻¹ = (x₂ : G) := congrArg Subtype.val this
        rw [← hw2]
        exact zpowers_inv.symm
  · rintro (rfl | rfl)
    · exact ⟨(x₁ : G), IsConj.refl _, x_mem_preimQ R, rfl⟩
    · exact ⟨(x₂ : G), D.isConj_x₁_x₂ S, D.x₂_mem_RG S F, rfl⟩


omit [Finite G] F in
theorem exists_eq_x₂_zpow_mul {u : ↥(centralizer ({(x₁ : G)} : Set G))}
    (hu : projQ (x₁ : G) u ∈ zpowers (D.x₂Q S)) :
    ∃ k j : ℤ, (u : G) = (x₂ : G) ^ k * (x₁ : G) ^ j := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hu
  have hp : projQ (x₁ : G) (D.x₂M S) = D.x₂Q S := rfl
  have h1 : ((D.x₂M S) ^ k)⁻¹ * u ∈ (projQ (x₁ : G)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hp, hk, inv_mul_cancel]
  rw [ker_projQ] at h1
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h1
  have hj' : (x₁ : G) ^ j = ((x₂ : G) ^ k)⁻¹ * (u : G) := by
    have := congrArg Subtype.val hj
    simpa [LyData.x₂M] using this
  refine ⟨k, j, ?_⟩
  rw [hj']
  group

omit [Finite G] F in
theorem exists_eq_x₂_mul_zpow {u : ↥(centralizer ({(x₁ : G)} : Set G))}
    (hu : projQ (x₁ : G) u = D.x₂Q S) : ∃ j : ℤ, (u : G) = (x₂ : G) * (x₁ : G) ^ j := by
  have hp : projQ (x₁ : G) (D.x₂M S) = D.x₂Q S := rfl
  have h1 : (D.x₂M S)⁻¹ * u ∈ (projQ (x₁ : G)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hp, hu, inv_mul_cancel]
  rw [ker_projQ] at h1
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h1
  have hj' : (x₁ : G) ^ j = (x₂ : G)⁻¹ * (u : G) := by
    have := congrArg Subtype.val hj
    simpa [LyData.x₂M] using this
  refine ⟨j, ?_⟩
  rw [hj']
  group

omit [Finite G] F in
theorem mem_EE_of_proj_mem_zpowers {u : ↥(centralizer ({(x₁ : G)} : Set G))}
    (hu : projQ (x₁ : G) u ∈ zpowers (D.x₂Q S)) : (u : G) ∈ EE (x₁ : G) (x₂ : G) := by
  obtain ⟨k, j, h⟩ := D.exists_eq_x₂_zpow_mul S hu
  rw [h]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (subset_closure (by simp)) k)
    (Subgroup.zpow_mem _ (subset_closure (by simp)) j)

theorem RG_center : preimQ (x₁ : G) R ⊓ centralizer ((preimQ (x₁ : G) R : Subgroup G) : Set G) =
    EE (x₁ : G) (x₂ : G) := by
  apply le_antisymm
  · rintro z ⟨hzR, hzC⟩
    obtain ⟨hzM, hzq⟩ := mem_preimQ.1 hzR
    have h1 : projQ (x₁ : G) ⟨z, hzM⟩ ∈ zpowers (D.x₂Q S) := by
      rw [← F.mcl.R_center]
      refine ⟨hzq, mem_centralizer_iff.2 fun r hr => ?_⟩
      obtain ⟨u, rfl⟩ := projQ_surjective (x₁ : G) r
      have huR : (u : G) ∈ preimQ (x₁ : G) R := (mem_preimQ_coe u).2 hr
      have h2 : u * ⟨z, hzM⟩ = ⟨z, hzM⟩ * u := Subtype.ext (mem_centralizer_iff.1 hzC _ huR)
      rw [← map_mul, ← map_mul, h2]
    exact D.mem_EE_of_proj_mem_zpowers S h1
  · refine (closure_le _).2 ?_
    intro g hg
    have hg' : g = (x₁ : G) ∨ g = (x₂ : G) := by simpa using hg
    have hle := (D.threeCoreE_RG S F).le
    rcases hg' with rfl | rfl
    · exact ⟨x_mem_preimQ R, mem_centralizer_iff.2 fun r hr =>
        mem_centralizer_singleton_iff.1 (preimQ_le_centralizer _ hr)⟩
    · exact ⟨D.x₂_mem_RG S F, mem_centralizer_iff.2 fun r hr => ((mem_QE.1 (hle hr)).2).symm⟩

omit [Finite G] in
theorem RG_pow_three_mem {r : G} (hr : r ∈ preimQ (x₁ : G) R) :
    r ^ 3 ∈ EE (x₁ : G) (x₂ : G) := by
  obtain ⟨hrM, hrq⟩ := mem_preimQ.1 hr
  have h1 : projQ (x₁ : G) ((⟨r, hrM⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) ^ 3) = 1 := by
    rw [map_pow]
    exact F.mcl.R_exp _ hrq
  have := D.mem_EE_of_proj_mem_zpowers S (u := (⟨r, hrM⟩ : ↥(centralizer
    ({(x₁ : G)} : Set G))) ^ 3) (by rw [h1]; exact one_mem _)
  simpa using this


theorem RG_comm_normalized {n : G} (hn : n ∈ normalizer (EE (x₁ : G) (x₂ : G) : Set G)) :
    ∀ w ∈ ⁅preimQ (x₁ : G) R, preimQ (x₁ : G) R⁆,
      n * w * n⁻¹ ∈ ⁅preimQ (x₁ : G) R, preimQ (x₁ : G) R⁆ := by
  have hle : (preimQ (x₁ : G) R).map (MulAut.conj n).toMonoidHom ≤ preimQ (x₁ : G) R := by
    rintro _ ⟨r, hr, rfl⟩
    exact normal_threeCoreE_normalizer (D.threeCoreE_RG S F) n hn r hr
  intro w hw
  have h : (⁅preimQ (x₁ : G) R, preimQ (x₁ : G) R⁆).map (MulAut.conj n).toMonoidHom ≤
      ⁅preimQ (x₁ : G) R, preimQ (x₁ : G) R⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact h ⟨w, hw, rfl⟩

theorem RG_commutator_eq :
    ⁅preimQ (x₁ : G) R, preimQ (x₁ : G) R⁆ = EE (x₁ : G) (x₂ : G) := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro r hr r' hr'
    obtain ⟨hrM, hrq⟩ := mem_preimQ.1 hr
    obtain ⟨hrM', hrq'⟩ := mem_preimQ.1 hr'
    have hc : projQ (x₁ : G) ⁅(⟨r, hrM⟩ : ↥(centralizer ({(x₁ : G)} : Set G))), ⟨r', hrM'⟩⁆ ∈
        zpowers (D.x₂Q S) := by
      rw [← F.mcl.threeCore.comm, map_commutatorElement]
      exact Subgroup.commutator_mem_commutator hrq hrq'
    exact D.mem_EE_of_proj_mem_zpowers S hc
  ·
    obtain ⟨a, b, -, -, -, -, -, -, hb1, hb2, -⟩ := D.exists_quaternion_lifts S
    obtain ⟨s₀, hs1, hs2, -, -⟩ := D.exists_swap S
    have hb1G : (b : G) * (x₁ : G) * (b : G)⁻¹ = (x₁ : G) := by
      simpa using congrArg Subtype.val hb1
    have hb2G : (b : G) * (x₂ : G) * (b : G)⁻¹ = (x₂ : G)⁻¹ := by
      simpa using congrArg Subtype.val hb2
    have hs1G : (s₀ : G) * (x₁ : G) * (s₀ : G)⁻¹ = (x₂ : G) := by
      simpa using congrArg Subtype.val hs1
    have hs2G : (s₀ : G) * (x₂ : G) * (s₀ : G)⁻¹ = (x₁ : G) := by
      simpa using congrArg Subtype.val hs2
    have hx₁E : (x₁ : G) ∈ EE (x₁ : G) (x₂ : G) := subset_closure (by simp)
    have hx₂E : (x₂ : G) ∈ EE (x₁ : G) (x₂ : G) := subset_closure (by simp)
    have hbN : (b : G) ∈ normalizer (EE (x₁ : G) (x₂ : G) : Set G) := by
      refine mem_normalizer_closure (S := ({(x₁ : G), (x₂ : G)} : Set G)) ?_
      intro g hg
      have hg' : g = (x₁ : G) ∨ g = (x₂ : G) := by simpa using hg
      rcases hg' with rfl | rfl
      · rw [hb1G]; exact hx₁E
      · rw [hb2G]; exact Subgroup.inv_mem _ hx₂E
    have hsN : (s₀ : G) ∈ normalizer (EE (x₁ : G) (x₂ : G) : Set G) := by
      refine mem_normalizer_closure (S := ({(x₁ : G), (x₂ : G)} : Set G)) ?_
      intro g hg
      have hg' : g = (x₁ : G) ∨ g = (x₂ : G) := by simpa using hg
      rcases hg' with rfl | rfl
      · rw [hs1G]; exact hx₂E
      · rw [hs2G]; exact hx₁E
    set RM : Subgroup ↥(centralizer ({(x₁ : G)} : Set G)) := R.comap (projQ (x₁ : G)) with hRM
    have hmapRM : RM.map (projQ (x₁ : G)) = R :=
      Subgroup.map_comap_eq_self_of_surjective (projQ_surjective (x₁ : G)) R
    have hWM : (⁅RM, RM⁆).map (projQ (x₁ : G)) = zpowers (D.x₂Q S) := by
      rw [Subgroup.map_commutator, hmapRM, F.mcl.threeCore.comm]
    have hWG : (⁅RM, RM⁆).map (centralizer ({(x₁ : G)} : Set G)).subtype =
        ⁅preimQ (x₁ : G) R, preimQ (x₁ : G) R⁆ := by
      rw [Subgroup.map_commutator]
      rfl
    obtain ⟨w', hw'W, hw'⟩ : ∃ w' ∈ ⁅RM, RM⁆, projQ (x₁ : G) w' = D.x₂Q S := by
      have : D.x₂Q S ∈ (⁅RM, RM⁆).map (projQ (x₁ : G)) := by
        rw [hWM]; exact mem_zpowers _
      exact this
    obtain ⟨j, hj⟩ := D.exists_eq_x₂_mul_zpow S hw'
    have hw'G : (w' : G) ∈ ⁅preimQ (x₁ : G) R, preimQ (x₁ : G) R⁆ := by
      rw [← hWG]; exact ⟨w', hw'W, rfl⟩
    rw [hj] at hw'G
    have hbw : (b : G) * ((x₂ : G) * (x₁ : G) ^ j) * (b : G)⁻¹ = (x₂ : G)⁻¹ * (x₁ : G) ^ j := by
      have e : (b : G) * ((x₂ : G) * (x₁ : G) ^ j) * (b : G)⁻¹ =
          ((b : G) * (x₂ : G) * (b : G)⁻¹) * ((b : G) * (x₁ : G) ^ j * (b : G)⁻¹) := by group
      rw [e, hb2G, ← conj_zpow, hb1G]
    have hbW := D.RG_comm_normalized S F hbN _ hw'G
    rw [hbw] at hbW
    have hsq : (x₂ : G) * (x₂ : G) ∈ ⁅preimQ (x₁ : G) R, preimQ (x₁ : G) R⁆ := by
      have := Subgroup.mul_mem _ hw'G (Subgroup.inv_mem _ hbW)
      have e : (x₂ : G) * (x₁ : G) ^ j * ((x₂ : G)⁻¹ * (x₁ : G) ^ j)⁻¹ = (x₂ : G) * (x₂ : G) := by
        group
      rwa [e] at this
    have hx₂3 : (x₂ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val S.pow₂
    have hx₂W : (x₂ : G) ∈ ⁅preimQ (x₁ : G) R, preimQ (x₁ : G) R⁆ := by
      have e : (x₂ : G) = (x₂ * x₂) * (x₂ * x₂) := by
        calc (x₂ : G) = (x₂ : G) ^ 3 * (x₂ : G) := by rw [hx₂3, one_mul]
          _ = (x₂ * x₂) * (x₂ * x₂) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [e]
      exact Subgroup.mul_mem _ hsq hsq
    have hx₁W : (x₁ : G) ∈ ⁅preimQ (x₁ : G) R, preimQ (x₁ : G) R⁆ := by
      have := D.RG_comm_normalized S F hsN _ hx₂W
      rwa [hs2G] at this
    refine (closure_le _).2 ?_
    intro g hg
    have hg' : g = (x₁ : G) ∨ g = (x₂ : G) := by simpa using hg
    rcases hg' with rfl | rfl
    · exact hx₁W
    · exact hx₂W


omit [Finite G] in
theorem EE_le_RG : EE (x₁ : G) (x₂ : G) ≤ preimQ (x₁ : G) R := by
  refine (closure_le _).2 ?_
  intro g hg
  have hg' : g = (x₁ : G) ∨ g = (x₂ : G) := by simpa using hg
  rcases hg' with rfl | rfl
  · exact x_mem_preimQ R
  · exact D.x₂_mem_RG S F

theorem RG_frattini :
    (frattini ↥(preimQ (x₁ : G) R)).map (preimQ (x₁ : G) R).subtype = EE (x₁ : G) (x₂ : G) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hle := D.EE_le_RG S F
  set N : Subgroup ↥(preimQ (x₁ : G) R) := (EE (x₁ : G) (x₂ : G)).subgroupOf (preimQ (x₁ : G) R)
    with hN
  have hNmap : N.map (preimQ (x₁ : G) R).subtype = EE (x₁ : G) (x₂ : G) :=
    Subgroup.map_subgroupOf_eq_of_le hle
  have hcomm : ⁅(⊤ : Subgroup ↥(preimQ (x₁ : G) R)), ⊤⁆ = N := by
    apply Subgroup.map_injective (preimQ (x₁ : G) R).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hNmap]
    exact D.RG_commutator_eq S F
  have hnormal : N.Normal := by
    rw [← hcomm]
    infer_instance
  have hpow : ∀ a : ↥(preimQ (x₁ : G) R), a ^ 3 ∈ N := by
    intro a
    rw [hN, Subgroup.mem_subgroupOf]
    exact D.RG_pow_three_mem S F a.2
  have hfr := frattini_eq_of_commutator_eq (p := 3) (D.threeCoreE_RG S F).isPGroup hcomm hpow
  rw [hfr, hNmap]

end LyData

end R

end CFSG.Sporadic.Recognition.LyonsSims
