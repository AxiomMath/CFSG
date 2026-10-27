module

public import CFSG.RankThree.PartOne.D4RC.Phi3

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ7
  CFSG.Timmesfeld.ARS
open scoped Matrix MatrixGroups Pointwise

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

theorem rcn_exists_fixed {G : Type*} [Group G] {A : Subgroup G} [Finite A] {y : G} {p : ℕ}
    [Fact p.Prime] (hy : y ^ p = 1) (hyA : conjSub A y = A) (hA : ¬ p ∣ Nat.card A - 1)
    (hA1 : 1 ≤ Nat.card A) : ∃ a ∈ A, a ≠ 1 ∧ y * a = a * y := by
  classical
  have : Fintype A := Fintype.ofFinite A
  set f : Equiv.Perm G := MulAut.toPerm G (MulAut.conj y) with hfdef
  have hfa : ∀ a, f a = y * a * y⁻¹ := fun a => rfl
  have hmem : ∀ a, a ∈ A ↔ f a ∈ A := fun a => by
    rw [hfa]
    constructor
    · intro ha
      rw [← hyA]
      exact ⟨a, ha, rfl⟩
    · intro ha
      rw [← hyA] at ha
      obtain ⟨b, hb, hba⟩ := ha
      have : b = a := by
        have h := hba
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
        exact mul_left_cancel (mul_right_cancel h)
      exact this ▸ hb
  set σ : Equiv.Perm A := f.subtypePerm (fun a => (hmem a).symm) with hσdef
  have hf : f ^ p = 1 := by
    rw [hfdef, ← map_pow, ← map_pow, hy, map_one, map_one]
  have hσ : σ ^ p ^ 1 = 1 := by
    rw [pow_one]
    refine Equiv.ext fun a => Subtype.ext ?_
    rw [hσdef, Equiv.Perm.subtypePerm_pow]
    simp only [Equiv.Perm.subtypePerm_apply, hf, Equiv.Perm.one_apply]
  have hmod := Equiv.Perm.card_compl_support_modEq hσ
  have h1 : (1 : A) ∈ σ.supportᶜ := by
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
    refine Subtype.ext ?_
    rw [hσdef, Equiv.Perm.subtypePerm_apply]
    change f 1 = 1
    rw [hfa, mul_one, mul_inv_cancel]
  have hcard : 1 < σ.supportᶜ.card := by
    by_contra hle
    push Not at hle
    have hc1 : σ.supportᶜ.card = 1 := le_antisymm hle (Finset.card_pos.2 ⟨1, h1⟩)
    rw [hc1] at hmod
    apply hA
    rw [Nat.card_eq_fintype_card]
    exact (Nat.modEq_iff_dvd' (by rwa [Nat.card_eq_fintype_card] at hA1)).1 hmod
  obtain ⟨a, ha, ha1⟩ := Finset.exists_mem_ne hcard 1
  refine ⟨a, a.2, fun h => ha1 (Subtype.ext h), ?_⟩
  rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at ha
  have h2 := congrArg Subtype.val ha
  rw [hσdef, Equiv.Perm.subtypePerm_apply] at h2
  have h3 : y * (a : G) * y⁻¹ = a := by
    rw [← hfa]
    exact h2
  calc y * a = y * a * y⁻¹ * y := by group
    _ = a * y := by rw [h3]

section NoFix

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

variable {F : RclFrame ℓ f K σ ε p L} {S : Sylow p 𝒞[K, σ]} {c : 𝒞[K, σ]}
  {E : Subgroup 𝒞[K, σ]}

theorem rcn_not_dvd (F : RclFrame ℓ f K σ ε p L) : ¬ p ∣ ℓ ^ f - 1 := by
  intro h
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ (Fact.out : ℓ.Prime).pos
  obtain ⟨m, hm⟩ := h
  have hq : ((ℓ ^ f : ℕ) : ℤ) = p * m + 1 := by
    have : ℓ ^ f = p * m + 1 := by omega
    rw [this]
    push_cast
    ring
  have hpd := F.hpd
  rw [hq] at hpd
  have h3 : (p : ℤ) ∣ 2 + ε := by
    have h2 : ((p : ℤ) * m + 1) ^ 2 + ε * ((p : ℤ) * m + 1) + 1 =
        p * (p * m ^ 2 + 2 * m + ε * m) + (2 + ε) := by ring
    rw [h2] at hpd
    exact (Int.dvd_add_right (Dvd.intro _ rfl)).1 hpd
  have hp3 := F.hp3
  rcases F.hε with rfl | rfl
  · have := Int.le_of_dvd (by norm_num) h3
    omega
  · have := Int.le_of_dvd (by norm_num) h3
    omega

theorem rcn_exists_regular (Ln : RceLines F S c E) :
    ∃ y ∈ E, y ≠ 1 ∧ ∀ k, y ∉ Subgroup.zpowers (Ln.x k) := by
  classical
  have hp := F.hp
  have hp5 : 5 ≤ p := by
    have h3 := F.hp3
    by_contra h
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by decide)
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [Ln.hEc]; exact pow_ne_zero 2 hp.ne_zero)
  have : Fintype E := Fintype.ofFinite E
  by_contra h
  push Not at h
  have hcov : (Finset.univ : Finset E) ⊆ Finset.univ.biUnion fun k : Fin 4 =>
      (Finset.univ.filter fun y : E => (y : 𝒞[K, σ]) ∈ Subgroup.zpowers (Ln.x k)) := by
    intro y _
    rw [Finset.mem_biUnion]
    by_cases hy1 : (y : 𝒞[K, σ]) = 1
    · exact ⟨0, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _,
        hy1 ▸ Subgroup.one_mem _⟩⟩
    · obtain ⟨k, hk⟩ := h y y.2 hy1
      exact ⟨k, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩⟩
  have hk : ∀ k : Fin 4, (Finset.univ.filter fun y : E =>
      (y : 𝒞[K, σ]) ∈ Subgroup.zpowers (Ln.x k)).card = p := by
    intro k
    have hle : Subgroup.zpowers (Ln.x k) ≤ E := Subgroup.zpowers_le.2 (Ln.hx k).1
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    calc Nat.card {y : E // (y : 𝒞[K, σ]) ∈ Subgroup.zpowers (Ln.x k)}
        = Nat.card ((Subgroup.zpowers (Ln.x k)).subgroupOf E) := rfl
      _ = Nat.card (Subgroup.zpowers (Ln.x k)) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
      _ = p := by rw [Nat.card_zpowers, (Ln.sp k).hx]
  have h1 := (Finset.card_le_card hcov).trans Finset.card_biUnion_le
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Ln.hEc] at h1
  simp only [hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  nlinarith

theorem rcn_sup_eq (Ln : RceLines F S c E) {j : Fin 4} (hj : j ≠ 0) :
    Subgroup.zpowers (Ln.x 0) ⊔ Subgroup.zpowers (Ln.x j) = E := by
  have hp := F.hp
  set H := Subgroup.zpowers (Ln.x 0) ⊔ Subgroup.zpowers (Ln.x j) with hH
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [Ln.hEc]; exact pow_ne_zero 2 hp.ne_zero)
  have hHE : H ≤ E :=
    sup_le (Subgroup.zpowers_le.2 (Ln.hx 0).1) (Subgroup.zpowers_le.2 (Ln.hx j).1)
  have : Finite H := Finite.of_injective _ (Subgroup.inclusion_injective hHE)
  have hdvd : Nat.card H ∣ p ^ 2 := Ln.hEc ▸ Subgroup.card_dvd_of_le hHE
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have h0 : Nat.card (Subgroup.zpowers (Ln.x 0)) = p := by
    rw [Nat.card_zpowers, (Ln.sp 0).hx]
  have hle0 : Subgroup.zpowers (Ln.x 0) ≤ H := le_sup_left
  have hpH : p ∣ Nat.card H := h0 ▸ Subgroup.card_dvd_of_le hle0
  have hne : Nat.card H ≠ p := by
    intro hHp
    have e1 : Subgroup.zpowers (Ln.x 0) = H :=
      Subgroup.eq_of_le_of_card_ge hle0 (by rw [hHp, h0])
    have hxj : Subgroup.zpowers (Ln.x j) ≤ Subgroup.zpowers (Ln.x 0) := e1 ▸ le_sup_right
    have : Finite (Subgroup.zpowers (Ln.x 0)) :=
      Finite.of_injective _ (Subgroup.inclusion_injective hle0)
    have hj0 : Subgroup.zpowers (Ln.x j) = Subgroup.zpowers (Ln.x 0) :=
      Subgroup.eq_of_le_of_card_ge hxj (by
        rw [Nat.card_zpowers, Nat.card_zpowers, (Ln.sp 0).hx, (Ln.sp j).hx])
    exact hj (Ln.hinj j 0 hj0)
  have hk2 : k = 2 := by
    rcases k with _ | _ | _ | k
    · rw [pow_zero] at hcard
      rw [hcard] at hpH
      exact absurd (Nat.le_of_dvd one_pos hpH) (by have := hp.two_le; omega)
    · exact absurd (by simpa using hcard) hne
    · rfl
    · omega
  exact Subgroup.eq_of_le_of_card_ge hHE (by rw [hcard, hk2, Ln.hEc])

theorem rcn_not_normalizes (Ln : RceLines F S c E) (D : RclAlgData F 0) {j : Fin 4}
    (hj : j ≠ 0) : conjSub (rcaA0 (Ln.sp 0) D) (Ln.x j) ≠ rcaA0 (Ln.sp 0) D := by
  classical
  intro hfix
  have hp := F.hp
  have : Fact p.Prime := ⟨hp⟩
  have hℓ : ℓ.Prime := Fact.out
  set A₀ := rcaA0 (Ln.sp 0) D with hA₀
  have hc : ∀ b ∈ A₀, Ln.x 0 * b = b * Ln.x 0 := fun b hb =>
    Subgroup.mem_centralizer_iff.1 (rclPx_le_centralizer (Ln.sp 0) (rcaA0_le (Ln.sp 0) D hb))
      (Ln.x 0) rfl
  have hfix0 : conjSub A₀ (Ln.x 0) = A₀ := by
    ext a
    rw [mem_conjSub]
    constructor
    · intro ha
      have h := hc _ ha
      have e1 : a = (Ln.x 0)⁻¹ * a * Ln.x 0 := by
        calc a = Ln.x 0 * ((Ln.x 0)⁻¹ * a * Ln.x 0) * (Ln.x 0)⁻¹ := by group
          _ = (Ln.x 0)⁻¹ * a * Ln.x 0 := by rw [h]; group
      rw [e1]
      exact ha
    · intro ha
      have h := hc _ ha
      have e1 : (Ln.x 0)⁻¹ * a * Ln.x 0 = a := by
        calc (Ln.x 0)⁻¹ * a * Ln.x 0 = (Ln.x 0)⁻¹ * (a * Ln.x 0) := by group
          _ = (Ln.x 0)⁻¹ * (Ln.x 0 * a) := by rw [h]
          _ = a := by group
      rw [e1]
      exact ha
  have hNE : E ≤ Subgroup.normalizer (A₀ : Set 𝒞[K, σ]) := by
    rw [← rcn_sup_eq Ln hj]
    exact sup_le (Subgroup.zpowers_le.2 (conjSub_eq_self_iff.1 hfix0))
      (Subgroup.zpowers_le.2 (conjSub_eq_self_iff.1 hfix))
  obtain ⟨y, hyE, hy1, hyreg⟩ := rcn_exists_regular Ln
  obtain ⟨b, hb, hker⟩ : ∃ b : Fin TwistTag.D4.tag.rank → Lˣ,
      rootDiagUnit TwistTag.D4.tag b = F.g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * F.g0 ∧
        rootCharKernel b = ∅ := by
    rcases Ln.hcover y hyE hy1 with ⟨k, hk⟩ | h
    · exact absurd hk (hyreg k)
    · exact h
  have hyord : orderOf y = p := orderOf_eq_prime (Ln.hEp y hyE) hy1
  have hodd := rcr_odd_card_centralizer F hyord hb hker
  have hcardA : Nat.card A₀ = ℓ ^ f := by
    rw [hA₀, rc3_card_rcaA0, card_fixSubfield_cube hℓ F.hf F.hK σ F.hσ]
  have : Finite A₀ := Nat.finite_of_card_ne_zero (by rw [hcardA]; exact pow_ne_zero _ hℓ.ne_zero)
  obtain ⟨a, ha, ha1, hya⟩ := rcn_exists_fixed (A := A₀) (Ln.hEp y hyE)
    (conjSub_eq_self_iff.2 (hNE hyE)) (by rw [hcardA]; exact rcn_not_dvd F)
    (by rw [hcardA]; exact Nat.one_le_pow _ _ hℓ.pos)
  have hac : a ∈ Subgroup.centralizer ({y} : Set 𝒞[K, σ]) :=
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact hya
  have hda : orderOf a ∣ ℓ ^ f := hcardA ▸ Subgroup.orderOf_dvd_natCard A₀ ha
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hℓ).1 hda
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact ha1 hk
  have h2 : ℓ ∣ Nat.card (Subgroup.centralizer ({y} : Set 𝒞[K, σ])) :=
    (dvd_pow_self ℓ hk0).trans (hk ▸ Subgroup.orderOf_dvd_natCard _ hac)
  rw [F.hℓ2] at h2
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

end NoFix

end CFSG.RankThree.PartOne.D4RC
