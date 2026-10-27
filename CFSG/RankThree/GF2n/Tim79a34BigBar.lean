module

public import CFSG.RankThree.GF2n.Tim79a34BigEnd

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def WbarM (M V H : Subgroup G) : Subgroup (Mbar M) :=
  ((wOf V H).subgroupOf M).map (QuotientGroup.mk' ((inSubgroup (pCore 2) M).subgroupOf M))

theorem mem_WbarM_iff {M V H : Subgroup G} {x : Mbar M} :
    x ∈ WbarM M V H ↔ ∃ w : ↥M, (w : G) ∈ wOf V H ∧ (w : Mbar M) = x := by
  simp only [WbarM, Subgroup.mem_map, Subgroup.mem_subgroupOf, QuotientGroup.mk'_apply]

theorem pCore_two_mbar_eq_bot [Finite G] (M : Subgroup G) : pCore 2 (Mbar M) = ⊥ := by
  set N : Subgroup ↥M := (inSubgroup (pCore 2) M).subgroupOf M with hN
  have hN' : N = pCore 2 ↥M := by
    simp only [hN, inSubgroup, Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  set f := QuotientGroup.mk' N
  have hker : IsPGroup 2 f.ker := by
    rw [QuotientGroup.ker_mk']
    exact hN' ▸ pCore_isPGroup
  have hle0 : (pCore 2 (Mbar M)).comap f ≤ pCore 2 ↥M :=
    le_sSup ⟨(pCore_normal (p := 2) (G := Mbar M)).comap f,
      (pCore_isPGroup (p := 2) (G := Mbar M)).comap_of_ker_isPGroup f hker⟩
  have hle : (pCore 2 (Mbar M)).comap f ≤ N := le_of_le_of_eq hle0 hN'.symm
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  exact hle hx

theorem wOf_le_M_of_minCex [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) :
    wOf V H ≤ M := by
  have h1 : wOf V H ≤ Subgroup.normalizer (conjSubgroup (1 : G) V : Set G) := by
    intro w hw
    obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc.V_inf_wOf_ne_bot
    obtain ⟨haU, haW⟩ := Subgroup.mem_inf.mp ha
    have ha1' : a ≠ 1 := fun h' => ha1 (Subtype.ext h')
    have hcomm : w * a = a * w := hc.wOf_isElemAbelian.comm hw haW
    have := Tim77.mem_normalizer_of_commute_of_isTI hc.ti haU ha1' hcomm
    simpa [conjSubgroup_one] using this
  have h2 : Subgroup.normalizer (V : Set G) = M := hc.normalizer_eq
  simpa [conjSubgroup_one, h2] using h1

@[expose] def BigRbarIsoStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    ∀ n f : ℕ, 2 ≤ n → 2 ^ f = qBar V H →
      Nonempty (↥(StatedSp n (GaloisField 2 f)) ≃* XbarZ V H) →
      Nonempty (↥(RbarM M V H) ≃* StatedSp (n - 1) (GaloisField 2 f))

@[expose] def BigWbarCardStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    Nat.card ↥(WbarM M V H) = qBar V H

@[expose] def BigWbarCentralizesStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    WbarM M V H ≤ Subgroup.centralizer (RbarM M V H : Set (Mbar M))

@[expose] def BigWbarTIStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    IsTI (WbarM M V H)

@[expose] def BigEpsilonNormalizerLeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    Subgroup.normalizer (RbarM M V H : Set (Mbar M)) ≤
      Subgroup.normalizer (WbarM M V H : Set (Mbar M))

@[expose] def BigEpsilonNormalizerGeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    Subgroup.normalizer (WbarM M V H : Set (Mbar M)) ≤
      Subgroup.normalizer (RbarM M V H : Set (Mbar M))

@[expose] def BigEpsilonNormalizerStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    Subgroup.normalizer (RbarM M V H : Set (Mbar M)) =
      Subgroup.normalizer (WbarM M V H : Set (Mbar M))

theorem bigEpsilonNormalizerStatement_of_le_ge (hle : BigEpsilonNormalizerLeStatement)
    (hge : BigEpsilonNormalizerGeStatement) : BigEpsilonNormalizerStatement :=
  fun G _ _ M V Q P H hH => le_antisymm (hle G M V Q P H hH) (hge G M V Q P H hH)

@[expose] def BigEpsilonCentralizerStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    ∃ K : Subgroup (Mbar M), Odd (Nat.card K) ∧
      Subgroup.centralizer (RbarM M V H : Set (Mbar M)) = WbarM M V H ⊔ K

@[expose] def BigRegularStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    ∃ h : Mbar M, h ∈ Subgroup.normalizer (RbarM M V H : Set (Mbar M)) ∧
      ∀ b ∈ WbarM M V H, b ≠ 1 → ∀ b' ∈ WbarM M V H, b' ≠ 1 →
        ∃ k : ℕ, h ^ k * b * (h ^ k)⁻¹ = b'

theorem bigNormalStatement_of_bar (hC : BigWbarCardStatement)
    (hE : BigEpsilonNormalizerLeStatement) : BigNormalStatement := by
  intro G _ _ M V Q P H hH hnorm
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  haveI : (RbarM M V H).Normal := by
    rw [← hnorm]
    exact Subgroup.normalClosure_normal
  have hN1 : Subgroup.normalizer (RbarM M V H : Set (Mbar M)) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hN2 : Subgroup.normalizer (WbarM M V H : Set (Mbar M)) = ⊤ :=
    top_le_iff.mp (hN1 ▸ hE G M V Q P H hH)
  haveI : (WbarM M V H).Normal := Subgroup.normalizer_eq_top_iff.mp hN2
  have hpg : IsPGroup 2 ↥(WbarM M V H) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨w, hw, hwg⟩ := mem_WbarM_iff.mp g.2
    apply Subtype.ext
    simp only [pow_one, OneMemClass.coe_one]
    have hw2 : (w : G) * (w : G) = 1 := hc.wOf_isElemAbelian.mul_self_eq_one hw
    have : w * w = 1 := Subtype.ext hw2
    rw [pow_two, Subgroup.coe_mul, ← hwg, ← QuotientGroup.mk_mul, this]
    rfl
  have hle : WbarM M V H ≤ pCore 2 (Mbar M) := le_sSup ⟨inferInstance, hpg⟩
  rw [pCore_two_mbar_eq_bot M, le_bot_iff] at hle
  have h1 : Nat.card ↥(WbarM M V H) = 1 := by rw [hle]; simp
  have h2 := hC G M V Q P H hH
  have h3 := hH.q_big
  omega

theorem isTI_wbar_of_alpha_delta {M V H P : Subgroup G}
    (hPQ : P ≤ inSubgroup (pCore 2) M) (hPM : M ≤ Subgroup.normalizer (P : Set G))
    (hWM : wOf V H ≤ M)
    (hα : ∀ g ∈ M, ¬ ((wOf V H ⊔ P) ⊓ conjSubgroup g (wOf V H ⊔ P) ≤ P) →
      conjSubgroup g (wOf V H ⊔ P) = wOf V H ⊔ P)
    (hδ : ∀ g ∈ M, ∀ w ∈ wOf V H,
      g * w * g⁻¹ ∈ inSubgroup (pCore 2) M ⊔ wOf V H → g * w * g⁻¹ ∈ wOf V H ⊔ P) :
    IsTI (WbarM M V H) := by
  intro gb
  by_cases hbot : WbarM M V H ⊓ conjSubgroup gb (WbarM M V H) = ⊥
  · exact Or.inl hbot
  refine Or.inr (inf_eq_left.mpr ?_)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  obtain ⟨hxT, hxc⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨w, hwW, rfl⟩ := mem_WbarM_iff.mp hxT
  obtain ⟨w'', hw''W, hw''⟩ := mem_WbarM_iff.mp (mem_conjSubgroup.mp hxc)
  have hg' : ((g : G))⁻¹ ∈ M := M.inv_mem g.2
  have hq : ((w''⁻¹ * (g⁻¹ * w * g) : ↥M) : G) ∈ inSubgroup (pCore 2) M := by
    have h1 : ((w'' : ↥M) : Mbar M) = ((g⁻¹ * w * g : ↥M) : Mbar M) := by
      rw [hw'']
      simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h2 := (QuotientGroup.eq.mp h1)
    exact Subgroup.mem_subgroupOf.mp h2
  set q : G := ((w''⁻¹ * (g⁻¹ * w * g) : ↥M) : G) with hqdef
  have hconj : (g : G)⁻¹ * (w : G) * ((g : G)⁻¹)⁻¹ = (w'' : G) * q := by
    simp only [hqdef, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    group
  have hmem : (g : G)⁻¹ * (w : G) * ((g : G)⁻¹)⁻¹ ∈ inSubgroup (pCore 2) M ⊔ wOf V H := by
    rw [hconj]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hw''W) (Subgroup.mem_sup_left hq)
  have hu := hδ _ hg' _ hwW hmem
  have hnotP : ¬ ((wOf V H ⊔ P) ⊓ conjSubgroup ((g : G)⁻¹) (wOf V H ⊔ P) ≤ P) := by
    intro hle
    have hin : (g : G)⁻¹ * (w : G) * ((g : G)⁻¹)⁻¹ ∈
        (wOf V H ⊔ P) ⊓ conjSubgroup ((g : G)⁻¹) (wOf V H ⊔ P) := by
      refine ⟨hu, mem_conjSubgroup.mpr ?_⟩
      have e : ((g : G)⁻¹)⁻¹ * ((g : G)⁻¹ * (w : G) * ((g : G)⁻¹)⁻¹) * (g : G)⁻¹ = (w : G) := by
        group
      rw [e]
      exact Subgroup.mem_sup_left hwW
    have hP1 := hle hin
    have hwQ : (w : G) ∈ inSubgroup (pCore 2) M := by
      have h3 : (w : G) = ((g : G)⁻¹)⁻¹ * ((g : G)⁻¹ * (w : G) * ((g : G)⁻¹)⁻¹) * (g : G)⁻¹ := by
        group
      rw [h3]
      have h4 := mem_normalizer_iff_conjSubgroup_eq.mp (hPM g.2)
      have h5 : ((g : G)) * ((g : G)⁻¹ * (w : G) * ((g : G)⁻¹)⁻¹) * (g : G)⁻¹ ∈
          conjSubgroup (g : G) P := by
        rw [mem_conjSubgroup]
        have e2 : ((g : G))⁻¹ * ((g : G) * ((g : G)⁻¹ * (w : G) * ((g : G)⁻¹)⁻¹) * (g : G)⁻¹)
            * (g : G) = (g : G)⁻¹ * (w : G) * ((g : G)⁻¹)⁻¹ := by group
        rw [e2]
        exact hP1
      rw [h4] at h5
      simpa using hPQ h5
    apply hx1
    have : ((w : ↥M) : Mbar M) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hwQ
    exact Subtype.ext this
  have hcj := hα _ hg' hnotP
  intro t ht
  obtain ⟨v, hvW, rfl⟩ := mem_WbarM_iff.mp ht
  refine mem_conjSubgroup.mpr (mem_WbarM_iff.mpr ?_)
  have hv : (g : G)⁻¹ * (v : G) * ((g : G)⁻¹)⁻¹ ∈ conjSubgroup ((g : G)⁻¹) (wOf V H ⊔ P) := by
    rw [mem_conjSubgroup]
    have e : ((g : G)⁻¹)⁻¹ * ((g : G)⁻¹ * (v : G) * ((g : G)⁻¹)⁻¹) * (g : G)⁻¹ = (v : G) := by
      group
    rw [e]
    exact Subgroup.mem_sup_left hvW
  rw [hcj, sup_comm] at hv
  obtain ⟨p, hp, w₂, hw₂, hpw⟩ := exists_mul_of_mem_sup (V := P) (U := wOf V H)
    (fun x hx => hPM (hWM hx)) hv
  refine ⟨⟨w₂, hWM hw₂⟩, hw₂, ?_⟩
  have hpM : p ∈ M := (inSubgroup_pCore_two M).2.1 (hPQ hp)
  have hpQ : (⟨p, hpM⟩ : ↥M) ∈ (inSubgroup (pCore 2) M).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr (hPQ hp)
  have hprod : (g⁻¹ * v * g : ↥M) = ⟨p, hpM⟩ * ⟨w₂, hWM hw₂⟩ := by
    apply Subtype.ext
    have hpw' : (g : G)⁻¹ * (v : G) * (g : G) = p * w₂ := by simpa using hpw
    simpa using hpw'
  have hone : ((⟨p, hpM⟩ : ↥M) : Mbar M) = 1 := (QuotientGroup.eq_one_iff _).mpr hpQ
  have : ((g⁻¹ * v * g : ↥M) : Mbar M) = ((⟨w₂, hWM hw₂⟩ : ↥M) : Mbar M) := by
    rw [hprod, QuotientGroup.mk_mul, hone, one_mul]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
  exact this.symm

@[expose] def BigAlphaStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    ∀ g ∈ M, ¬ ((wOf V H ⊔ P) ⊓ conjSubgroup g (wOf V H ⊔ P) ≤ P) →
      conjSubgroup g (wOf V H ⊔ P) = wOf V H ⊔ P

@[expose] def BigDeltaStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    ∀ g ∈ M, ∀ w ∈ wOf V H, g * w * g⁻¹ ∈ Q ⊔ wOf V H → g * w * g⁻¹ ∈ wOf V H ⊔ P

theorem bigWbarTIStatement_of_alpha_delta (hα : BigAlphaStatement) (hδ : BigDeltaStatement) :
    BigWbarTIStatement := by
  intro G _ _ M V Q P H hH
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hQM : Q = inSubgroup (pCore 2) M := hc.hQ
  refine isTI_wbar_of_alpha_delta (V := V) (H := H) ?_ hc.M_le_normalizer_P
    (wOf_le_M_of_minCex hc) (hα G M V Q P H hH) ?_
  · rw [← hQM]
    exact hc.P_le_Q
  · rw [← hQM]
    exact hδ G M V Q P H hH

@[expose] def BigPQCommStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    (∀ q ∈ Q, ∀ x ∈ P, ⁅q, x⁆ ∈ V ⊓ wOf V H) ∧
      ∀ q ∈ Q, ∀ a ∈ V ⊓ wOf V H, q * a = a * q

@[expose] def BigPDerivedStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    (∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V ⊓ wOf V H) ∧ V ⊓ wOf V H ≤ ⁅P, P⁆

@[expose] def BigPOrderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    ∀ n f : ℕ, 2 ≤ n → 2 ^ f = qBar V H →
      Nonempty (↥(StatedSp n (GaloisField 2 f)) ≃* XbarZ V H) →
      Nat.card ↥P = 2 ^ (f * (4 * n - 2)) ∧ Nat.card ↥V = 2 ^ (2 * f)

@[expose] def BigRNontrivialStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∃ x ∈ P, ⁅r, x⁆ ∉ V

end CFSG.RankThree.GF2n.Tim79a
