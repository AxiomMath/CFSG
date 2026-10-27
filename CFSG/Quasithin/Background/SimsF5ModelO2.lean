module

public import CFSG.Quasithin.Background.SimsF5Par
public import CFSG.Quasithin.Background.SimsF5Lin

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open scoped Pointwise

theorem o2_zDot_ne_one : zDot ≠ 1 := by
  intro h
  have h2 : eJ {0, 1, 2, 3} = eJ ∅ := h.trans mono_eJ_empty.symm
  have := mono_eJ_injective h2
  exact absurd this (by decide)

theorem exists_noncomm_MDot : ∃ a b : ↥MDot, a * b ≠ b * a := by
  by_contra h
  have h' : ∀ a b : ↥MDot, a * b = b * a := fun a b => by
    by_contra hab
    exact h ⟨a, b, hab⟩
  have hz : (⟨zDot, (Subgroup.mem_inf.1 zDot_mem_GDot).1⟩ : ↥MDot) ∈ Subgroup.center ↥MDot :=
    Subgroup.mem_center_iff.2 fun g => h' g _
  rw [center_MDot_eq_bot, Subgroup.mem_bot] at hz
  exact o2_zDot_ne_one (congrArg Subtype.val hz)

theorem Q2Dot_le_GDot : Q2Dot ≤ GDot := by
  intro g hg
  rw [← SetLike.mem_coe, Q2Dot_coe] at hg
  obtain ⟨J, hJ, hev, rfl⟩ := hg
  exact eJ_mem_GDot J hJ hev

theorem Q1Dot_le_GDot : Q1Dot ≤ GDot := by
  rw [Q1Dot_eq]
  intro g hg
  have h1 : g ∈ M1Dot := q8Hom_range_le hg
  obtain ⟨-, h6⟩ := Subgroup.mem_inf.1 (quat_q8_range_le_fix hg)
  exact Subgroup.mem_inf.2 ⟨h1.1, h6⟩

theorem o2_perm5_check : ∀ x : Equiv.Perm (Fin 5), x ≠ 1 → x ^ 8 = 1 →
    ∃ a b : Fin 5, (x * (Equiv.swap a b * x * (Equiv.swap a b)⁻¹)) ^ 8 ≠ 1 := by
  decide +kernel

theorem o2_pow_eight {N : Subgroup (Equiv.Perm (Fin 5))} (hp : IsPGroup 2 N)
    {x : Equiv.Perm (Fin 5)} (hx : x ∈ N) : x ^ 8 = 1 := by
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hc : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  have h120 : Nat.card N ∣ 120 := hc ▸ Subgroup.card_subgroup_dvd_card N
  have hn4 : n < 4 := by
    by_contra h
    have h16 : 2 ^ 4 ∣ 2 ^ n := Nat.pow_dvd_pow 2 (not_lt.1 h)
    rw [← hn] at h16
    have := h16.trans h120
    omega
  have h8 : Nat.card N ∣ 8 := by
    rw [hn]
    interval_cases n <;> norm_num
  have h1 : (⟨x, hx⟩ : ↥N) ^ Nat.card N = 1 := pow_card_eq_one'
  have h2 : x ^ Nat.card N = 1 := by
    have := congrArg Subtype.val h1
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using this
  obtain ⟨m, hm⟩ := h8
  rw [hm, pow_mul, h2, one_pow]

theorem o2_pCore_perm5 : CFSG.pCore 2 (Equiv.Perm (Fin 5)) = ⊥ := by
  haveI : (CFSG.pCore 2 (Equiv.Perm (Fin 5))).Normal := CFSG.pCore_normal
  have hp : IsPGroup 2 (CFSG.pCore 2 (Equiv.Perm (Fin 5))) := CFSG.pCore_isPGroup
  rw [eq_bot_iff]
  intro x hx
  by_contra hne
  rw [Subgroup.mem_bot] at hne
  obtain ⟨a, b, hg⟩ := o2_perm5_check x hne (o2_pow_eight hp hx)
  have hy : Equiv.swap a b * x * (Equiv.swap a b)⁻¹ ∈ CFSG.pCore 2 (Equiv.Perm (Fin 5)) :=
    this.conj_mem x hx _
  exact hg (o2_pow_eight hp ((CFSG.pCore 2 (Equiv.Perm (Fin 5))).mul_mem hx hy))

theorem o2_unique {σ τ : Equiv.Perm (Fin 5)} {q q' : GL6} (hq : q ∈ Q2Dot) (hq' : q' ∈ Q2Dot)
    (h : s5Hom σ * q = s5Hom τ * q') : σ = τ ∧ q = q' := by
  have h1 : (s5Hom τ)⁻¹ * s5Hom σ = q' * q⁻¹ := by
    calc (s5Hom τ)⁻¹ * s5Hom σ = (s5Hom τ)⁻¹ * (s5Hom σ * q) * q⁻¹ := by group
      _ = (s5Hom τ)⁻¹ * (s5Hom τ * q') * q⁻¹ := by rw [h]
      _ = q' * q⁻¹ := by group
  have h2 : (s5Hom τ)⁻¹ * s5Hom σ ∈ s5Hom.range ⊓ Q2Dot :=
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ ⟨τ, rfl⟩) ⟨σ, rfl⟩,
      h1 ▸ Subgroup.mul_mem _ hq' (Subgroup.inv_mem _ hq)⟩
  rw [s5Hom_range_inf, Subgroup.mem_bot, inv_mul_eq_one] at h2
  have hστ : σ = τ := (s5Hom_injective h2).symm
  subst hστ
  exact ⟨rfl, mul_left_cancel h⟩

@[expose] def o2Proj (g : ↥M2Dot) : Equiv.Perm (Fin 5) := Classical.choose (mono_M2Dot_decomp g.2)

theorem o2Proj_spec (g : ↥M2Dot) : ∃ q ∈ Q2Dot, (g : GL6) = s5Hom (o2Proj g) * q :=
  Classical.choose_spec (mono_M2Dot_decomp g.2)

theorem o2Proj_eq {g : ↥M2Dot} {σ : Equiv.Perm (Fin 5)} {q : GL6} (hq : q ∈ Q2Dot)
    (h : (g : GL6) = s5Hom σ * q) : o2Proj g = σ := by
  obtain ⟨q', hq', h'⟩ := o2Proj_spec g
  exact (o2_unique hq' hq (h'.symm.trans h)).1

@[expose] def o2ProjHom : ↥M2Dot →* Equiv.Perm (Fin 5) where
  toFun := o2Proj
  map_one' := o2Proj_eq (σ := 1) (q := 1) Q2Dot.one_mem (by simp)
  map_mul' g h := by
    obtain ⟨q, hq, hg⟩ := o2Proj_spec g
    obtain ⟨q', hq', hh⟩ := o2Proj_spec h
    have hconj : (s5Hom (o2Proj h))⁻¹ * q * s5Hom (o2Proj h) ∈ Q2Dot := by
      have hM : (s5Hom (o2Proj h))⁻¹ ∈ M2Dot := M2Dot.inv_mem (s5Hom_range_le ⟨o2Proj h, rfl⟩)
      simpa using mono_conj_mem_Q2Dot hM hq
    refine o2Proj_eq (q := (s5Hom (o2Proj h))⁻¹ * q * s5Hom (o2Proj h) * q')
      (Q2Dot.mul_mem hconj hq') ?_
    calc ((g * h : ↥M2Dot) : GL6) = (g : GL6) * h := rfl
      _ = s5Hom (o2Proj g) * q * (s5Hom (o2Proj h) * q') := by rw [← hg, ← hh]
      _ = s5Hom (o2Proj g * o2Proj h) *
          ((s5Hom (o2Proj h))⁻¹ * q * s5Hom (o2Proj h) * q') := by rw [map_mul]; group

theorem o2ProjHom_s5Hom (σ : Equiv.Perm (Fin 5)) :
    o2ProjHom ⟨s5Hom σ, s5Hom_range_le ⟨σ, rfl⟩⟩ = σ :=
  o2Proj_eq (q := 1) Q2Dot.one_mem (by simp)

theorem o2ProjHom_surjective : Function.Surjective o2ProjHom := fun σ =>
  ⟨_, o2ProjHom_s5Hom σ⟩

theorem o2ProjHom_ker : o2ProjHom.ker = Q2Dot.subgroupOf M2Dot := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    obtain ⟨q, hq, hg⟩ := o2Proj_spec g
    have h1 : o2Proj g = 1 := h
    rw [h1, map_one, one_mul] at hg
    rw [hg]
    exact hq
  · intro hg
    exact o2Proj_eq (σ := 1) (q := (g : GL6)) hg (by simp)

instance o2_Q2Dot_normal_inst : (Q2Dot.subgroupOf M2Dot).Normal := Q2Dot_normal

theorem M2Dot_quotient_Q2Dot :
    Nonempty (↥M2Dot ⧸ Q2Dot.subgroupOf M2Dot ≃* Equiv.Perm (Fin 5)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq o2ProjHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective o2ProjHom o2ProjHom_surjective)⟩

theorem o2_isPGroup_Q2Dot : IsPGroup 2 Q2Dot :=
  IsPGroup.of_card (n := 4) (by rw [mono_card_Q2Dot]; norm_num)

theorem o2_pCoreOf_M2Dot_le : pCoreOf 2 M2Dot ≤ Q2Dot := by
  rintro _ ⟨y, hy, rfl⟩
  have h1 : o2ProjHom y ∈ CFSG.pCore 2 (Equiv.Perm (Fin 5)) :=
    CFSG.LieType.BorelTits.map_pCore_le 2 o2ProjHom o2ProjHom_surjective ⟨y, hy, rfl⟩
  rw [o2_pCore_perm5, Subgroup.mem_bot] at h1
  have h2 : y ∈ o2ProjHom.ker := h1
  rw [o2ProjHom_ker] at h2
  exact Subgroup.mem_subgroupOf.1 h2

theorem pCoreOf_M2Dot : pCoreOf 2 M2Dot = Q2Dot :=
  le_antisymm o2_pCoreOf_M2Dot_le
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Q2Dot_le_M2Dot mono_M2Dot_le_normalizer
      o2_isPGroup_Q2Dot)

theorem o2_conj_mem_GDot {g h : GL6} (hg : g ∈ M0Dot) (hh : h ∈ GDot) : g * h * g⁻¹ ∈ GDot := by
  haveI : (GDot.subgroupOf M0Dot).Normal :=
    Subgroup.normal_of_index_eq_two index_GDot_subgroupOf_M0Dot
  have := (inferInstance : (GDot.subgroupOf M0Dot).Normal).conj_mem ⟨h, GDot_le_M0Dot hh⟩
    (Subgroup.mem_subgroupOf.2 hh) ⟨g, hg⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem o2_le_normalizer_GDot_inf {Mi : Subgroup GL6} (hMi : Mi ≤ M0Dot) :
    Mi ≤ Subgroup.normalizer ((GDot ⊓ Mi : Subgroup GL6) : Set GL6) := by
  have key : ∀ g ∈ Mi, ∀ h ∈ GDot ⊓ Mi, g * h * g⁻¹ ∈ GDot ⊓ Mi := fun g hg h hh =>
    ⟨o2_conj_mem_GDot (hMi hg) hh.1,
      Mi.mul_mem (Mi.mul_mem hg hh.2) (Mi.inv_mem hg)⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ (Mi.inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem o2_pCoreOf_eq_of_normal {A B : Subgroup GL6} (hAB : A ≤ B)
    (hnorm : B ≤ Subgroup.normalizer (A : Set GL6)) (hQ : pCoreOf 2 B ≤ A) :
    pCoreOf 2 A = pCoreOf 2 B := by
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans hAB) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A)
    exact hnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A)
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQ ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B)
    exact hAB.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B)

theorem pCoreOf_GDot_inf_M1Dot : pCoreOf 2 (GDot ⊓ M1Dot) = pCoreOf 2 M1Dot :=
  o2_pCoreOf_eq_of_normal inf_le_right (o2_le_normalizer_GDot_inf M1Dot_le_M0Dot)
    (le_inf Q1Dot_le_GDot (CFSG.LieType.BorelTits.pCoreOf_le 2 M1Dot))

theorem pCoreOf_GDot_inf_M2Dot : pCoreOf 2 (GDot ⊓ M2Dot) = pCoreOf 2 M2Dot :=
  o2_pCoreOf_eq_of_normal inf_le_right (o2_le_normalizer_GDot_inf M2Dot_le_M0Dot)
    (le_inf (pCoreOf_M2Dot ▸ Q2Dot_le_GDot) (CFSG.LieType.BorelTits.pCoreOf_le 2 M2Dot))

theorem o2_Q8sq_center : ∀ p : QuaternionGroup 2 × QuaternionGroup 2,
    (∀ p' : QuaternionGroup 2 × QuaternionGroup 2, p * p' * (p' * p)⁻¹ = 1 ∨
      p * p' * (p' * p)⁻¹ = (QuaternionGroup.a 2, QuaternionGroup.a 2)) →
    p = 1 ∨ p = (QuaternionGroup.a 2, 1) ∨ p = (1, QuaternionGroup.a 2) ∨
      p = (QuaternionGroup.a 2, QuaternionGroup.a 2) := by
  decide +kernel

theorem o2_Q8_a2_central :
    ∀ g : QuaternionGroup 2, g * QuaternionGroup.a 2 = QuaternionGroup.a 2 * g := by
  decide

theorem centerOf_Q1Dot : centerOf Q1Dot = Subgroup.zpowers zDot := by
  apply le_antisymm
  · rintro g ⟨hgQ, hgc⟩
    rw [Q1Dot_eq] at hgQ
    obtain ⟨p, rfl⟩ := hgQ
    have hcomm : ∀ p' : QuaternionGroup 2 × QuaternionGroup 2, p * p' * (p' * p)⁻¹ = 1 ∨
        p * p' * (p' * p)⁻¹ = (QuaternionGroup.a 2, QuaternionGroup.a 2) := by
      intro p'
      have h1 : q8Hom p' * q8Hom p = q8Hom p * q8Hom p' :=
        Subgroup.mem_centralizer_iff.1 hgc (q8Hom p') (by
          rw [Q1Dot_eq]
          exact ⟨p', rfl⟩)
      have h2 : q8Hom (p * p' * (p' * p)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, ← h1, mul_inv_cancel]
      exact quat_q8Hom_eq_one _ h2
    rcases o2_Q8sq_center p hcomm with rfl | rfl | rfl | rfl
    · rw [map_one]
      exact Subgroup.one_mem _
    · rw [q8Hom_a2_one]
      exact Subgroup.mem_zpowers _
    · rw [q8Hom_one_a2]
      exact Subgroup.mem_zpowers _
    · have : q8Hom (QuaternionGroup.a 2, QuaternionGroup.a 2) = 1 := by
        have h : ((QuaternionGroup.a 2, QuaternionGroup.a 2) :
            QuaternionGroup 2 × QuaternionGroup 2) =
            (QuaternionGroup.a 2, 1) * (1, QuaternionGroup.a 2) := by simp
        rw [h, map_mul, q8Hom_a2_one, q8Hom_one_a2, zDot_mul_self]
      rw [this]
      exact Subgroup.one_mem _
  · rw [Subgroup.zpowers_le]
    refine ⟨zDot_mem_Q1Dot, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Q1Dot_eq] at hh
    obtain ⟨p, rfl⟩ := hh
    have hc : p * (QuaternionGroup.a 2, (1 : QuaternionGroup 2)) =
        (QuaternionGroup.a 2, 1) * p := by
      obtain ⟨u, w⟩ := p
      exact Prod.ext (o2_Q8_a2_central u) (by simp)
    rw [← q8Hom_a2_one, ← map_mul, ← map_mul, hc]

theorem o2_exists_sep : ∀ k l : Fin 6, k ≠ l →
    ∃ J : Finset (Fin 6), J ⊆ Iset ∧ Even J.card ∧ (k ∈ J ↔ l ∉ J) := by
  decide +kernel

theorem o2_normalizer_line {g : GL6} (hg : g ∈ Subgroup.normalizer (Q2Dot : Set GL6))
    (i : Fin 6) :
    ∃ j : Fin 6, ∃ c : ZMod 3, c ≠ 0 ∧
      (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = c • xvec j := by
  set v : V6 := (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i with hv
  have hv0 : v ≠ 0 := by
    intro h
    have h0 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i =
        (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ 0 := by
      rw [Matrix.mulVec_zero]
      exact h
    exact mono_xvec_ne_zero i (mono_mulVec_inj g h0)
  have heig : ∀ J : Finset (Fin 6), J ⊆ Iset → Even J.card →
      ∃ c : ZMod 3, ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = c • v := by
    intro J hJ hev
    have hmem : g⁻¹ * eJ J * g⁻¹⁻¹ ∈ Q2Dot :=
      (Subgroup.mem_normalizer_iff.1 (inv_mem hg) (eJ J)).1 (mono_eJ_mem_Q2Dot hJ hev)
    obtain ⟨J', hJ'⟩ := mono_Q2Dot_elim hmem
    rw [inv_inv] at hJ'
    refine ⟨eJd J' i, ?_⟩
    have h1 : eJ J * g = g * eJ J' := by
      calc eJ J * g = g * (g⁻¹ * eJ J * g) := by group
        _ = g * eJ J' := by rw [hJ']
    rw [hv, Matrix.mulVec_mulVec, ← Units.val_mul, h1, Units.val_mul, ← Matrix.mulVec_mulVec,
      mono_eJ_mulVec_xvec, Matrix.mulVec_smul]
  have hsupp : ∀ k l : Fin 6, v k ≠ 0 → v l ≠ 0 → k = l := by
    intro k l hk hl
    by_contra hkl
    obtain ⟨J, hJ, hev, hiff⟩ := o2_exists_sep k l hkl
    obtain ⟨c, hc⟩ := heig J hJ hev
    rw [mono_eJ_mulVec] at hc
    have hk' := congrFun hc k
    have hl' := congrFun hc l
    simp only [Pi.smul_apply, smul_eq_mul] at hk' hl'
    have ek : eJd J k = c := mul_right_cancel₀ hk hk'
    have el : eJd J l = c := mul_right_cancel₀ hl hl'
    by_cases hkJ : k ∈ J
    · have hlJ : l ∉ J := hiff.1 hkJ
      rw [eJd_eq_neg_one_of_mem hkJ] at ek
      rw [eJd_eq_one_of_notMem hlJ] at el
      have : (-1 : ZMod 3) = 1 := ek.trans el.symm
      exact absurd this (by decide)
    · have hlJ : l ∈ J := by
        by_contra hlJ
        exact hkJ (hiff.2 hlJ)
      rw [eJd_eq_one_of_notMem hkJ] at ek
      rw [eJd_eq_neg_one_of_mem hlJ] at el
      have : (1 : ZMod 3) = -1 := ek.trans el.symm
      exact absurd this (by decide)
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hcon
    apply hv0
    funext k
    by_contra hk
    exact hcon ⟨k, hk⟩
  refine ⟨j, v j, hj, ?_⟩
  funext k
  by_cases hkj : k = j
  · subst hkj
    simp [mono_xvec_apply]
  · have : v k = 0 := by
      by_contra h
      exact hkj (hsupp k j h hj)
    simp [mono_xvec_apply, hkj, this]

theorem o2_normalizer_le_stabilizer {g : GL6}
    (hg : g ∈ Subgroup.normalizer (Q2Dot : Set GL6)) : g ∈ MulAction.stabilizer GL6 Lambda := by
  choose τ c hc hτ using o2_normalizer_line hg
  have hinj : Function.Injective τ := by
    intro i i' hii
    by_contra hne
    have h1 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (c i' • xvec i - c i • xvec i') =
        (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hτ i, hτ i', ← hii,
        smul_smul, smul_smul, mul_comm (c i') (c i), sub_self, Matrix.mulVec_zero]
    have h3 := congrFun (mono_mulVec_inj g h1) i
    simp [mono_xvec_apply, hne] at h3
    exact hc i' h3
  exact mono_mem_stabilizer_Lambda (Equiv.ofBijective τ (Finite.injective_iff_bijective.1 hinj))
    fun i => ⟨c i, hc i, hτ i⟩

theorem MDot_inf_normalizer_Q2Dot :
    MDot ⊓ Subgroup.normalizer (Q2Dot : Set GL6) = M2Dot := by
  apply le_antisymm
  · rintro g ⟨hM, hN⟩
    exact ⟨hM, o2_normalizer_le_stabilizer hN⟩
  · intro g hg
    exact ⟨hg.1, mono_M2Dot_le_normalizer hg⟩

theorem o2_orderOf_of_sq {G : Type*} [Group G] {x : G} (h : x * x = 1) :
    ∃ k : ℕ, orderOf x = 2 ^ k := by
  have h2 : x ^ 2 = 1 := by rw [pow_two]; exact h
  rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h2) with h1 | h1
  · exact ⟨0, by simpa using h1⟩
  · exact ⟨1, by simpa using h1⟩

theorem o2_mem_oPPrime {P : Subgroup GL6} {x : GL6} (hx : x ∈ P) (h2 : x * x = 1) :
    x ∈ oPPrime 2 P :=
  Subgroup.subset_closure ⟨hx, o2_orderOf_of_sq h2⟩

theorem o2_oPPrime_le (P : Subgroup GL6) : oPPrime 2 P ≤ P :=
  (Subgroup.closure_le P).2 fun _ hx => hx.1

theorem o2_s5Hom_mulVec_x6 (σ : Equiv.Perm (Fin 5)) :
    ((s5Hom σ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = monoSgn σ • x6 := by
  have h := s5Hom_mulVec_xvec σ 5
  rw [mono_scal_five, mono_ext_five] at h
  exact h

theorem o2_monoSgn_eq_one_iff (σ : Equiv.Perm (Fin 5)) :
    monoSgn σ = 1 ↔ Equiv.Perm.sign σ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [monoSgn, h]
  · rw [monoSgn, h]
    constructor
    · intro h1
      exact absurd h1 (by decide)
    · intro h1
      exact absurd h1 (by decide)

theorem o2_s5Hom_mem_GDot_iff (σ : Equiv.Perm (Fin 5)) :
    s5Hom σ ∈ GDot ↔ Equiv.Perm.sign σ = 1 := by
  rw [← o2_monoSgn_eq_one_iff, mem_GDot_iff]
  refine ⟨fun h => ?_, fun h => ⟨mono_s5Hom_mem_MDot σ, ?_⟩⟩
  · have h2 := h.2
    rw [o2_s5Hom_mulVec_x6] at h2
    have h3 := congrFun h2 5
    simpa [x6, mono_xvec_apply] using h3
  · rw [o2_s5Hom_mulVec_x6, h, one_smul]

@[expose] def o2Dbl : Set (Equiv.Perm (Fin 5)) := {σ | Equiv.Perm.sign σ = 1 ∧ σ ^ 2 = 1}

theorem o2Dbl_conj {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ o2Dbl) (g : Equiv.Perm (Fin 5)) :
    g * σ * g⁻¹ ∈ o2Dbl := by
  obtain ⟨h1, h2⟩ := hσ
  refine ⟨?_, by rw [conj_pow, h2, mul_one, mul_inv_cancel]⟩
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, h1, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h <;> simp [h]

theorem o2_closure_Dbl_normal : (Subgroup.closure o2Dbl).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (o2Dbl_conj hx g)
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem o2_alternating_le_closure : alternatingGroup (Fin 5) ≤ Subgroup.closure o2Dbl := by
  haveI := o2_closure_Dbl_normal
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hN : ((Subgroup.closure o2Dbl).subgroupOf (alternatingGroup (Fin 5))).Normal :=
    Subgroup.Normal.subgroupOf inferInstance _
  have hδ : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) ∈ o2Dbl := by
    refine ⟨?_, by decide⟩
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((Subgroup.closure o2Dbl).subgroupOf (alternatingGroup (Fin 5))) with h | h
  · exfalso
    have hmem : (⟨Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3,
        Equiv.Perm.mem_alternatingGroup.2 hδ.1⟩ : alternatingGroup (Fin 5)) ∈
        (Subgroup.closure o2Dbl).subgroupOf (alternatingGroup (Fin 5)) :=
      Subgroup.subset_closure hδ
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 5)) = 1 :=
      congrArg Subtype.val hmem
    exact absurd h1 (by decide)
  · intro σ hσ
    have : (⟨σ, hσ⟩ : alternatingGroup (Fin 5)) ∈
        (Subgroup.closure o2Dbl).subgroupOf (alternatingGroup (Fin 5)) := by
      rw [h]
      exact Subgroup.mem_top _
    exact this

theorem o2_s5Hom_mem_oPPrime {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ Subgroup.closure o2Dbl) :
    s5Hom σ ∈ oPPrime 2 (GDot ⊓ M2Dot) := by
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    refine o2_mem_oPPrime ⟨(o2_s5Hom_mem_GDot_iff x).2 hx.1, s5Hom_range_le ⟨x, rfl⟩⟩ ?_
    rw [← map_mul, ← pow_two, hx.2, map_one]
  | one =>
    rw [map_one]
    exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    rw [map_inv]
    exact Subgroup.inv_mem _ hx

theorem oPPrime_GDot_inf_M2Dot : oPPrime 2 (GDot ⊓ M2Dot) = GDot ⊓ M2Dot := by
  apply le_antisymm (o2_oPPrime_le _)
  intro g hg
  obtain ⟨σ, q, hq, rfl⟩ := mono_M2Dot_decomp hg.2
  obtain ⟨J, rfl⟩ := mono_Q2Dot_elim hq
  have hqP : eJ J ∈ GDot ⊓ M2Dot := ⟨Q2Dot_le_GDot hq, Q2Dot_le_M2Dot hq⟩
  have hqH : eJ J ∈ oPPrime 2 (GDot ⊓ M2Dot) := o2_mem_oPPrime hqP (mono_eJ_mul_self J)
  have hσG : s5Hom σ ∈ GDot := by
    have := GDot.mul_mem hg.1 (GDot.inv_mem hqP.1)
    simpa using this
  have hσ : σ ∈ alternatingGroup (Fin 5) :=
    Equiv.Perm.mem_alternatingGroup.2 ((o2_s5Hom_mem_GDot_iff σ).1 hσG)
  exact Subgroup.mul_mem _ (o2_s5Hom_mem_oPPrime (o2_alternating_le_closure hσ)) hqH

theorem o2_offdiag_zero {g : GL6}
    (hc : ∀ J : Finset (Fin 6), J ⊆ Iset → Even J.card → g * eJ J = eJ J * g) {k l : Fin 6}
    (hkl : k ≠ l) : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) k l = 0 := by
  obtain ⟨J, hJ, hev, hiff⟩ := o2_exists_sep k l hkl
  have h := congrArg (fun u : GL6 => (u : Matrix (Fin 6) (Fin 6) (ZMod 3)) k l) (hc J hJ hev)
  simp only [Units.val_mul] at h
  rw [show ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = Matrix.diagonal (eJd J) from rfl,
    Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  by_cases hk : k ∈ J
  · have hl : l ∉ J := hiff.1 hk
    rw [eJd_eq_neg_one_of_mem hk, eJd_eq_one_of_notMem hl] at h
    have key : ∀ a : ZMod 3, a * 1 = -1 * a → a = 0 := by decide
    exact key _ h
  · have hl : l ∈ J := by
      by_contra hl
      exact hk (hiff.2 hl)
    rw [eJd_eq_one_of_notMem hk, eJd_eq_neg_one_of_mem hl] at h
    have key : ∀ a : ZMod 3, a * -1 = 1 * a → a = 0 := by decide
    exact key _ h

theorem o2_diagonal_mulVec_xvec (d : Fin 6 → ZMod 3) (i : Fin 6) :
    Matrix.diagonal d *ᵥ xvec i = d i • xvec i := by
  funext k
  rw [Matrix.mulVec_diagonal]
  by_cases hk : k = i
  · subst hk
    simp [mono_xvec_apply]
  · simp [mono_xvec_apply, hk]

theorem o2_ext_eq {σ : Equiv.Perm (Fin 5)} {a b : Fin 5} (h : σ a = b) :
    monoExt σ (Fin.castSucc a) = Fin.castSucc b := by
  rw [mono_ext_castSucc, h]

theorem ctr_oPPrime_GDot_inf_M1Dot {w : GL6} (hw : w ∈ ctr (oPPrime 2 (GDot ⊓ M1Dot))) :
    w = 1 ∨ w = zDot := by
  obtain ⟨hwO, hwC⟩ := hw
  have hwP : w ∈ GDot ⊓ M1Dot := o2_oPPrime_le _ hwO
  have hcomm : ∀ x ∈ oPPrime 2 (GDot ⊓ M1Dot), x * w = w * x :=
    Subgroup.mem_centralizer_iff.1 hwC
  have hJ : ∀ J : Finset (Fin 6), J ⊆ Iset → Even J.card → w * eJ J = eJ J * w := by
    intro J hJ hev
    refine (hcomm (eJ J) (o2_mem_oPPrime ?_ (mono_eJ_mul_self J))).symm
    exact ⟨eJ_mem_GDot J hJ hev, quat_mem_M1Dot (eJ_mem_MDot J hJ hev) (mono_eJ_comm _ _)⟩
  have hκ : ∀ κ : Equiv.Perm (Fin 5), κ 4 = 4 → Equiv.Perm.sign κ = 1 → κ * κ = 1 →
      w * s5Hom κ = s5Hom κ * w := by
    intro κ h4 hs hk2
    refine (hcomm (s5Hom κ) (o2_mem_oPPrime
      ⟨(o2_s5Hom_mem_GDot_iff κ).2 hs, (mono_s5Hom_mem_M12 h4).1⟩ ?_)).symm
    rw [← map_mul, hk2, map_one]
  set d : Fin 6 → ZMod 3 := fun i => (w : Matrix (Fin 6) (Fin 6) (ZMod 3)) i i with hd
  have hdiag : (w : Matrix (Fin 6) (Fin 6) (ZMod 3)) = Matrix.diagonal d := by
    ext i j
    rw [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp [hd]
    · rw [if_neg hij]
      exact o2_offdiag_zero hJ hij
  have hperm : ∀ κ : Equiv.Perm (Fin 5), κ 4 = 4 → Equiv.Perm.sign κ = 1 → κ * κ = 1 →
      ∀ i : Fin 6, d (monoExt κ i) = d i := by
    intro κ h4 hs hk2 i
    have h := congrArg (fun m : GL6 => (m : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i)
      (hκ κ h4 hs hk2)
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec] at h
    rw [s5Hom_mulVec_xvec κ i, hdiag, o2_diagonal_mulVec_xvec d i, Matrix.mulVec_smul,
      Matrix.mulVec_smul, s5Hom_mulVec_xvec κ i, o2_diagonal_mulVec_xvec d (monoExt κ i),
      smul_smul, smul_smul] at h
    have h2 := congrFun h (monoExt κ i)
    simp only [Pi.smul_apply, smul_eq_mul, mono_xvec_apply, if_true, mul_one] at h2
    exact mul_left_cancel₀ (mono_scal_ne_zero κ i) (by rw [h2, mul_comm])
  have k1 : Equiv.Perm.sign (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) = 1 := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide
  have k2 : Equiv.Perm.sign (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3) = 1 := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide
  have e01 : d 1 = d 0 := by
    have h := hperm (Equiv.swap 0 1 * Equiv.swap 2 3) (by decide) k1 (by decide) 0
    have e : monoExt (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) 0 = 1 :=
      o2_ext_eq (a := 0) (b := 1) (by decide)
    rwa [e] at h
  have e23 : d 3 = d 2 := by
    have h := hperm (Equiv.swap 0 1 * Equiv.swap 2 3) (by decide) k1 (by decide) 2
    have e : monoExt (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) 2 = 3 :=
      o2_ext_eq (a := 2) (b := 3) (by decide)
    rwa [e] at h
  have e02 : d 2 = d 0 := by
    have h := hperm (Equiv.swap 0 2 * Equiv.swap 1 3) (by decide) k2 (by decide) 0
    have e : monoExt (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3) 0 = 2 :=
      o2_ext_eq (a := 0) (b := 2) (by decide)
    rwa [e] at h
  have h5 : d 5 = 1 := by
    have h := (mem_GDot_iff.1 hwP.1).2
    rw [hdiag] at h
    have h' : Matrix.diagonal d *ᵥ xvec 5 = xvec 5 := h
    rw [o2_diagonal_mulVec_xvec] at h'
    have := congrFun h' 5
    simpa [mono_xvec_apply] using this
  have hdet : d 0 * d 1 * d 2 * d 3 * d 4 * d 5 = 1 := by
    have := det_of_mem_MDot (Subgroup.mem_inf.1 hwP.1).1
    rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_six] at this
    exact this
  rw [e01, e23, e02, h5] at hdet
  have key : ∀ a b : ZMod 3, a * a * a * a * b * 1 = 1 → b = 1 ∧ (a = 1 ∨ a = -1) := by decide
  obtain ⟨hb, ha | ha⟩ := key _ _ hdet
  · left
    apply Units.ext
    rw [hdiag, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · exact ha
    · exact e01.trans ha
    · exact e02.trans ha
    · exact e23.trans (e02.trans ha)
    · exact hb
    · exact h5
  · right
    apply Units.ext
    rw [hdiag, show ((zDot : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) =
      Matrix.diagonal (eJd {0, 1, 2, 3}) from rfl]
    congr 1
    funext i
    fin_cases i
    · exact ha.trans (eJd_eq_neg_one_of_mem (by decide)).symm
    · exact (e01.trans ha).trans (eJd_eq_neg_one_of_mem (by decide)).symm
    · exact (e02.trans ha).trans (eJd_eq_neg_one_of_mem (by decide)).symm
    · exact (e23.trans (e02.trans ha)).trans (eJd_eq_neg_one_of_mem (by decide)).symm
    · exact hb.trans (eJd_eq_one_of_notMem (by decide)).symm
    · exact h5.trans (eJd_eq_one_of_notMem (by decide)).symm

theorem o2_index_GDot_inf {Mi : Subgroup GL6} (hMi : Mi ≤ M0Dot) (hf : fDot ∈ Mi) :
    ((GDot ⊓ Mi).subgroupOf Mi).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨fDot, hf⟩, fun b => ?_⟩
  have hbM : (b : GL6) ∈ MDot := (hMi b.2).1
  have hx : x6 ≠ -x6 := by decide
  have e1 : b ∈ (GDot ⊓ Mi).subgroupOf Mi ↔
      ((b : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = x6 := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_GDot_iff]
    exact ⟨fun h => h.1.2, fun h => ⟨⟨hbM, h⟩, b.2⟩⟩
  have e2 : b * ⟨fDot, hf⟩ ∈ (GDot ⊓ Mi).subgroupOf Mi ↔
      ((b : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = -x6 := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_GDot_iff]
    have hmul : (((b * ⟨fDot, hf⟩ : ↥Mi) : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 =
        -(((b : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6) := by
      show ((b : GL6) * fDot : GL6).val *ᵥ x6 = _
      rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      show _ *ᵥ (fMat *ᵥ x6) = _
      rw [fMat_mulVec_x6, Matrix.mulVec_smul, neg_one_smul]
    rw [hmul, neg_eq_iff_eq_neg]
    exact ⟨fun h => h.1.2, fun h => ⟨⟨MDot.mul_mem hbM fDot_mem_MDot, h⟩,
      Mi.mul_mem b.2 hf⟩⟩
  rw [e1, e2]
  rcases M0Dot_mulVec_x6 (hMi b.2) with h | h
  · refine Or.inr ⟨h, ?_⟩
    rw [h]
    exact hx
  · refine Or.inl ⟨h, ?_⟩
    rw [h]
    exact fun h' => hx h'.symm

theorem card_GDot_inf_M1Dot : Nat.card ↥(GDot ⊓ M1Dot) = 576 := by
  have h := Subgroup.card_mul_index ((GDot ⊓ M1Dot).subgroupOf M1Dot)
  rw [o2_index_GDot_inf M1Dot_le_M0Dot fDot_mem_M12Dot.1,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : GDot ⊓ M1Dot ≤ M1Dot)).toEquiv,
    card_M1Dot] at h
  omega

theorem card_GDot_inf_M2Dot : Nat.card ↥(GDot ⊓ M2Dot) = 960 := by
  have h := Subgroup.card_mul_index ((GDot ⊓ M2Dot).subgroupOf M2Dot)
  rw [o2_index_GDot_inf M2Dot_le_M0Dot fDot_mem_M12Dot.2,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : GDot ⊓ M2Dot ≤ M2Dot)).toEquiv,
    card_M2Dot] at h
  omega

theorem o2_conj_mem_centerOf {Q : Subgroup GL6} {g c : GL6}
    (hg : g ∈ Subgroup.normalizer (Q : Set GL6)) (hc : c ∈ centerOf Q) :
    g * c * g⁻¹ ∈ centerOf Q := by
  obtain ⟨hcQ, hcC⟩ := hc
  refine ⟨(Subgroup.mem_normalizer_iff.1 hg c).1 hcQ, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
  have hq' : g⁻¹ * q * g⁻¹⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) q).1 hq
  have h1 := Subgroup.mem_centralizer_iff.1 hcC _ hq'
  rw [inv_inv] at h1
  calc q * (g * c * g⁻¹) = g * ((g⁻¹ * q * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * q * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * q := by group

theorem o2_not_M0Dot_le_normalizer_M1 :
    ¬ M0Dot ≤ Subgroup.normalizer ((GDot ⊓ M1Dot : Subgroup GL6) : Set GL6) := by
  intro h
  have h1 : M0Dot ≤ Subgroup.normalizer (Q1Dot : Set GL6) := by
    have := h.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (GDot ⊓ M1Dot))
    rwa [pCoreOf_GDot_inf_M1Dot] at this
  have hzc : zDot ∈ centerOf Q1Dot := by
    rw [centerOf_Q1Dot]
    exact Subgroup.mem_zpowers _
  have h2 : M0Dot ≤ M1Dot := by
    intro g hg
    have hz : g * zDot * g⁻¹ ∈ centerOf Q1Dot := o2_conj_mem_centerOf (h1 hg) hzc
    rw [centerOf_Q1Dot] at hz
    have hg1 : g * zDot * g⁻¹ = zDot := by
      rcases mono_mem_zpowers_involution (G := GL6) zDot_mul_self hz with h0 | h0
      · exfalso
        apply o2_zDot_ne_one
        calc zDot = g⁻¹ * (g * zDot * g⁻¹) * g := by group
          _ = 1 := by rw [h0]; group
      · exact h0
    refine ⟨hg.1, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    rw [Set.mem_singleton_iff.1 hx]
    calc zDot * g = (g * zDot * g⁻¹) * g := by rw [hg1]
      _ = g * zDot := by group
  have := Subgroup.card_le_of_le h2
  rw [card_M0Dot, card_M1Dot] at this
  omega

theorem o2_not_M0Dot_le_normalizer_M2 :
    ¬ M0Dot ≤ Subgroup.normalizer ((GDot ⊓ M2Dot : Subgroup GL6) : Set GL6) := by
  intro h
  have h1 : M0Dot ≤ Subgroup.normalizer (Q2Dot : Set GL6) := by
    have := h.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (GDot ⊓ M2Dot))
    rwa [pCoreOf_GDot_inf_M2Dot, pCoreOf_M2Dot] at this
  have h2 : M0Dot ≤ M2Dot := by
    rw [← MDot_inf_normalizer_Q2Dot]
    exact le_inf (fun g hg => hg.1) h1
  have := Subgroup.card_le_of_le h2
  rw [card_M0Dot, card_M2Dot] at this
  omega

theorem o2_M0Dot_inf_normalizer {Mi : Subgroup GL6} (hMi : Mi ≤ M0Dot)
    (hmax : ∀ R' : Subgroup GL6, Mi < R' → R' ≤ M0Dot → R' = M0Dot)
    (hnot : ¬ M0Dot ≤ Subgroup.normalizer ((GDot ⊓ Mi : Subgroup GL6) : Set GL6)) :
    M0Dot ⊓ Subgroup.normalizer ((GDot ⊓ Mi : Subgroup GL6) : Set GL6) = Mi := by
  have hMN : Mi ≤ M0Dot ⊓ Subgroup.normalizer ((GDot ⊓ Mi : Subgroup GL6) : Set GL6) :=
    le_inf hMi (o2_le_normalizer_GDot_inf hMi)
  refine le_antisymm ?_ hMN
  by_contra hne
  have hlt := lt_of_le_not_ge hMN hne
  exact hnot (hmax _ hlt inf_le_left ▸ inf_le_right)

theorem M0Dot_inf_normalizer_GDot_inf_M1Dot :
    M0Dot ⊓ Subgroup.normalizer ((GDot ⊓ M1Dot : Subgroup GL6) : Set GL6) = M1Dot :=
  o2_M0Dot_inf_normalizer M1Dot_le_M0Dot
    ((maximal_overgroups_TDot M1Dot).2 (Or.inl rfl)).2.2.2 o2_not_M0Dot_le_normalizer_M1

theorem M0Dot_inf_normalizer_GDot_inf_M2Dot :
    M0Dot ⊓ Subgroup.normalizer ((GDot ⊓ M2Dot : Subgroup GL6) : Set GL6) = M2Dot :=
  o2_M0Dot_inf_normalizer M2Dot_le_M0Dot
    ((maximal_overgroups_TDot M2Dot).2 (Or.inr rfl)).2.2.2 o2_not_M0Dot_le_normalizer_M2

end

end CFSG.Quasithin.SimsF5
