module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestFrame
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestBasic
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYF3Exact
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split

open scoped Pointwise

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint

@[expose] noncomputable def e6rn_w2 : WeylGroup .E6 :=
  weylOfWord .E6 [2, 4, 3, 5, 4]

@[expose] noncomputable def e6rn_n2 :
    EC :=
  ⟨canonicalRep (coxeterSystem .E6) F2 e6rn_w2, canonicalRep_mem_adjointGroup _ F2 e6rn_w2⟩

theorem e6rn_w2_yA1 :
    e6rn_w2 • E6Pilot.yA1 = a5Root (blk 0 0) (blk 2 0) := by
  have hroot0 : Tag.E6.rootCertificate.root 0 = E6Pilot.yA1 := by
    simpa [E6Pilot.e6RepPos, E6Pilot.e6RepFrame, E6Pilot.yA1] using E6Pilot.e6RepPos_map 0
  rw [← hroot0]
  change weylOfWord .E6 [2, 4, 3, 5, 4] • Tag.E6.rootCertificate.root 0 = _
  rw [← (wordPos_spec (Tag.rootCertificate_check .E6) [2, 4, 3, 5, 4] (by decide +kernel)).2]
  exact RootCertificate.eq_of_ofFn_beq (by decide +kernel)

theorem e6rn_w2_yA4 :
    e6rn_w2 • E6Pilot.yA4 = a5Root (blk 0 1) (blk 2 1) := by
  have hroot3 : Tag.E6.rootCertificate.root 3 = E6Pilot.yA4 := by
    have h := E6Pilot.e6RepPos_map 1
    simp [E6Pilot.e6RepPos, E6Pilot.e6RepFrame, E6Pilot.yA4] at h
    exact h.2
  rw [← hroot3]
  change weylOfWord .E6 [2, 4, 3, 5, 4] • Tag.E6.rootCertificate.root 3 = _
  rw [← (wordPos_spec (Tag.rootCertificate_check .E6) [2, 4, 3, 5, 4] (by decide +kernel)).2]
  exact RootCertificate.eq_of_ofFn_beq (by decide +kernel)

theorem e6rn_w2_yLam : e6rn_w2 • E6Pilot.yLam = lamE := by
  rw [E6Pilot.yLam_eq.1, smul_add, e6rn_w2_yA1, e6rn_w2_yA4, lamE]
  decide +kernel

theorem e6rn_image_w2_yRadicalRoots :
    (fun γ => e6rn_w2 • γ) '' E6Pilot.yRadicalRoots = qRoots := by
  rw [E6Pilot.yRadicalRoots, qRoots,
    E6Pilot.image_smul_setOf_iform e6rn_w2 E6Pilot.yLam (fun n => 0 < n), e6rn_w2_yLam]

theorem e6rn_conj_n2_e6RepOne :
    e6rn_n2 * E6Pilot.e6Rep F2 1 * e6rn_n2⁻¹ = rOne 0 2 := by
  apply Subtype.ext
  change canonicalRep (coxeterSystem .E6) F2 e6rn_w2 *
      ((E6Pilot.e6RepFrame 1).map fun σ => pinnedX .E6 F2 σ 1).prod *
      (canonicalRep (coxeterSystem .E6) F2 e6rn_w2)⁻¹ =
    pinnedX .E6 F2 (a5Root (blk 0 0) (blk 2 0)) 1 *
      pinnedX .E6 F2 (a5Root (blk 0 1) (blk 2 1)) 1
  rw [E6Pilot.canonicalRep_mul_list_prod_mul_inv_of_charTwo e6rn_w2
    (F := E6Pilot.e6RepFrame 1) (fun α hα => (E6Pilot.e6RepFrame_perp 1 α hα).1)
    (fun _ => 1)]
  simp [E6Pilot.e6RepFrame, e6rn_w2_yA1, e6rn_w2_yA4]

private theorem e6rn_map_subgroupOf_conj {G : Type*} [Group G] {H A : Subgroup G} (hH : H ≤ A)
    (g : A) :
    (H.subgroupOf A).map (MulAut.conj g).toMonoidHom =
      (H.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf A := by
  change (MulAut.conj g) • (H.subgroupOf A) = (MulAut.conj (g : G) • H).subgroupOf A
  rw [Subgroup.conj_smul_subgroupOf hH g]

theorem e6rn_yRadical_map_eq_qE :
    (E6Pilot.yRadical F2).map (MulAut.conj e6rn_n2).toMonoidHom = qE := by
  have hstd : ∀ α ∈ E6Pilot.yRadicalRoots, IsRoot .E6 α := fun α hα => hα.1
  rw [E6Pilot.yRadical, qE,
    e6rn_map_subgroupOf_conj (E6Pilot.rootSpan_le_adjointGroup_E6 E6Pilot.yRadicalRoots) e6rn_n2]
  congr 1
  rw [show (e6rn_n2 : ModGL .E6 F2) = canonicalRep (coxeterSystem .E6) F2 e6rn_w2 from rfl,
    (canonical_weyl_root_transport .E6 F2).1 e6rn_w2 E6Pilot.yRadicalRoots hstd,
    e6rn_image_w2_yRadicalRoots]

private theorem e6rn_mem_sup_of_le_normalizer {G : Type*} [Group G] {Q M : Subgroup G}
    (h : M ≤ Subgroup.normalizer (Q : Set G)) {x : G} :
    x ∈ Q ⊔ M ↔ ∃ q ∈ Q, ∃ m ∈ M, q * m = x := by
  refine ⟨?_, fun ⟨q, hq, m, hm, hqm⟩ => hqm ▸ Subgroup.mul_mem_sup hq hm⟩
  intro hx
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨y, hy, 1, M.one_mem, by simp⟩
      · exact ⟨1, Q.one_mem, y, hy, by simp⟩
  | one => exact ⟨1, Q.one_mem, 1, M.one_mem, by simp⟩
  | mul a b _ _ iha ihb =>
      obtain ⟨q₁, hq₁, m₁, hm₁, rfl⟩ := iha
      obtain ⟨q₂, hq₂, m₂, hm₂, rfl⟩ := ihb
      refine ⟨q₁ * (m₁ * q₂ * m₁⁻¹), Q.mul_mem hq₁
        ((Subgroup.mem_normalizer_iff.mp (h hm₁) q₂).mp hq₂), m₁ * m₂,
        M.mul_mem hm₁ hm₂, ?_⟩
      group
  | inv a _ iha =>
      obtain ⟨q, hq, m, hm, rfl⟩ := iha
      refine ⟨m⁻¹ * q⁻¹ * m, ?_, m⁻¹, M.inv_mem hm, ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.mp (h (M.inv_mem hm)) q⁻¹).mp (Q.inv_mem hq)
      · group

private theorem e6rn_inf_sup_eq_of_le {G : Type*} [Group G] {A Q M : Subgroup G} (hQA : Q ≤ A)
    (hAM : A ≤ Q ⊔ M) (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) :
    A ⊓ (Q ⊔ M) = Q ⊔ (A ⊓ M) := by
  refine le_antisymm ?_ (sup_le (le_inf hQA le_sup_left)
    (le_inf inf_le_left (inf_le_right.trans le_sup_right)))
  intro x hx
  obtain ⟨hxA, hxQM⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨q, hq, m, hm, hqm⟩ := e6rn_mem_sup_of_le_normalizer hMQ |>.1 hxQM
  have hmA : m ∈ A := by
    have h1 : q⁻¹ * x ∈ A := A.mul_mem (A.inv_mem (hQA hq)) hxA
    have h2 : q⁻¹ * x = m := by rw [← hqm]; group
    rwa [h2] at h1
  rw [← hqm]
  exact Subgroup.mul_mem_sup hq (Subgroup.mem_inf.2 ⟨hmA, hm⟩)

private theorem e6rn_le_of_le_sup {G : Type*} [Group G] {p : ℕ} {Q M P : Subgroup G}
    (hQp : IsPGroup p Q) (hMnorm : M ≤ Subgroup.normalizer (Q : Set G))
    (hMin : ∀ N : Subgroup M, N.Normal → IsPGroup p N → N = ⊥)
    (hPp : IsPGroup p P) (hPH : P ≤ Q ⊔ M)
    (hPN : Q ⊔ M ≤ Subgroup.normalizer (P : Set G)) : P ≤ Q := by
  have hQN : Q ≤ Subgroup.normalizer (P : Set G) := le_sup_left.trans hPN
  have hPsup : IsPGroup p (P ⊔ Q : Subgroup G) := by
    have := IsPGroup.to_sup_of_normal_right' hQp hPp hQN
    rwa [sup_comm] at this
  have hMN : M ≤ Subgroup.normalizer ((P ⊔ Q : Subgroup G) : Set G) :=
    (le_inf (le_sup_right.trans hPN) hMnorm).trans
      (Subgroup.inf_normalizer_le_normalizer_sup P Q)
  have hle : (P ⊔ Q : Subgroup G) ≤ Q ⊔ M := sup_le hPH le_sup_left
  set N : Subgroup G := (P ⊔ Q) ⊓ M with hNdef
  have hNp : IsPGroup p N := hPsup.to_le inf_le_left
  have hNnorm : (N.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hxPQ, hxM⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.mp (hMN hm) x).mp hxPQ,
        M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm)⟩
    · intro hx
      obtain ⟨hxPQ, hxM⟩ := Subgroup.mem_inf.1 hx
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.mp (hMN hm) x).mpr hxPQ, ?_⟩
      have h2 : m⁻¹ * (m * x * m⁻¹) * m = x := by group
      rw [← h2]
      exact M.mul_mem (M.mul_mem (M.inv_mem hm) hxM) hm
  have hNbot : N.subgroupOf M = ⊥ := hMin (N.subgroupOf M) hNnorm (IsPGroup.comap_subtype hNp)
  have hNbot' : N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxM : x ∈ M := (Subgroup.mem_inf.1 hx).2
    have hx' : (⟨x, hxM⟩ : M) ∈ N.subgroupOf M := Subgroup.mem_subgroupOf.2 hx
    rw [hNbot] at hx'
    simpa using hx'
  have hmod : (P ⊔ Q : Subgroup G) = Q ⊔ N := by
    rw [hNdef]
    calc (P ⊔ Q : Subgroup G) = (P ⊔ Q) ⊓ (Q ⊔ M) := (inf_eq_left.2 hle).symm
      _ = Q ⊔ ((P ⊔ Q) ⊓ M) := e6rn_inf_sup_eq_of_le (le_sup_right : Q ≤ P ⊔ Q) hle hMnorm
  have hsupQ : (P ⊔ Q : Subgroup G) = Q := by rw [hmod, hNbot', sup_bot_eq]
  exact le_sup_left.trans hsupQ.le

private theorem e6rn_pCoreOf_sup_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q M : Subgroup G} (hQp : IsPGroup p Q) (hMnorm : M ≤ Subgroup.normalizer (Q : Set G))
    (hMin : ∀ N : Subgroup M, N.Normal → IsPGroup p N → N = ⊥) :
    CFSG.Open.pCoreOf p (Q ⊔ M) = Q := by
  refine le_antisymm (e6rn_le_of_le_sup hQp hMnorm hMin
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup p (Q ⊔ M))
    (CFSG.LieType.BorelTits.pCoreOf_le p (Q ⊔ M))
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p (Q ⊔ M))) ?_
  exact CFSG.LieType.BorelTits.le_pCoreOf p le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le Subgroup.le_normalizer hMnorm)) hQp

theorem e6rn_pCoreOf_perfectCore_centralizer_e6RepOne :
    CFSG.Open.pCoreOf 2 (CFSG.Quasithin.perfectCore
        (Subgroup.centralizer ({E6Pilot.e6Rep F2 1} : Set EC))) = E6Pilot.yRadical F2 := by
  have hcardF2 : Nat.card F2 = 2 := by
    rw [show F2 = GaloisField 2 1 from rfl, GaloisField.card 2 1 (by norm_num), pow_one]
  have h := E6Pilot.factF3y_lieModel (K := F2) (f := 1) (by rw [hcardF2]; norm_num)
  rw [h.1]
  exact e6rn_pCoreOf_sup_eq h.2.1 h.2.2.1 h.2.2.2.2.1

private theorem e6rn_map_centralizer_conj (g x : EC) :
    (Subgroup.centralizer ({x} : Set EC)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * x * g⁻¹} : Set EC) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [hz]
      _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
        _ = x * (g⁻¹ * y * g) := by group
    · group

private theorem e6rn_pCoreOf_conj (g x : EC) :
    CFSG.Open.pCoreOf 2 (CFSG.Quasithin.perfectCore
        (Subgroup.centralizer ({g * x * g⁻¹} : Set EC)))
      = (CFSG.Open.pCoreOf 2 (CFSG.Quasithin.perfectCore
          (Subgroup.centralizer ({x} : Set EC)))).map (MulAut.conj g).toMonoidHom := by
  haveI : Finite EC := by
    haveI : Finite (ModGL .E6 F2) := finite_modGL
    exact Finite.of_injective Subtype.val Subtype.val_injective
  rw [← e6rn_map_centralizer_conj g x,
    ← CFSG.Quasithin.map_perfectCore (MulAut.conj g).toMonoidHom
      (Subgroup.centralizer ({x} : Set EC))]
  exact CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g)
    (CFSG.Quasithin.perfectCore (Subgroup.centralizer ({x} : Set EC)))

theorem e6rn_pCoreOf_perfectCore_centralizer_rOne :
    CFSG.Open.pCoreOf 2 (CFSG.Quasithin.perfectCore
        (Subgroup.centralizer ({rOne 0 2} : Set EC))) = qE := by
  rw [← e6rn_conj_n2_e6RepOne, e6rn_pCoreOf_conj e6rn_n2 (E6Pilot.e6Rep F2 1),
    e6rn_pCoreOf_perfectCore_centralizer_e6RepOne, e6rn_yRadical_map_eq_qE]

private abbrev e6rn_ra : Fin Tag.E6.rank → ℤ := a5Root (blk 0 0) (blk 2 0)
private abbrev e6rn_rb : Fin Tag.E6.rank → ℤ := a5Root (blk 0 1) (blk 2 1)
private abbrev e6rn_rc : Fin Tag.E6.rank → ℤ := a5Root (blk 0 1) (blk 2 0)
private abbrev e6rn_rd : Fin Tag.E6.rank → ℤ := a5Root (blk 0 0) (blk 2 1)
private abbrev e6rn_m1 : Fin Tag.E6.rank → ℤ := a5Root (blk 0 0) (blk 0 1)
private abbrev e6rn_m2 : Fin Tag.E6.rank → ℤ := a5Root (blk 0 1) (blk 0 0)

private theorem e6rn_xr_mul_self
    (β : Fin Tag.E6.rank → ℤ) : xr β * xr β = 1 := by
  apply Subtype.ext
  change pinnedX .E6 F2 β 1 * pinnedX .E6 F2 β 1 = (1 : ModGL .E6 F2)
  rw [← pinnedX_add]
  have h2 : (1 : F2) + 1 = 0 := by
    rw [show (1 : F2) + 1 = (2 : F2) by norm_num, CharTwo.two_eq_zero]
  rw [h2, pinnedX_zero]

private theorem e6rn_xr_commute_of_iform
    {γ δ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ)
    (hδ : IsRoot .E6 δ) (h : 0 ≤ iform γ δ) : xr γ * xr δ = xr δ * xr γ := by
  apply Subtype.ext
  exact classD4_commute_pinnedX E6Pilot.e6_simplyLaced hγ hδ h (1 : F2) (1 : F2)

private theorem e6rn_xr_conj_of_iform
    {γ δ ε : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ)
    (hδ : IsRoot .E6 δ) (h : iform γ δ = -1) (hε : γ + δ = ε) :
    xr γ * xr δ * (xr γ)⁻¹ = xr ε * xr δ := by
  apply Subtype.ext
  exact classD4_conj_pinnedX E6Pilot.e6_simplyLaced (R := F2) CharTwo.two_eq_zero hγ hδ h hε

private theorem e6rn_mem_normalizer_subgroupOf {G : Type*} [Group G] {K A : Subgroup G} {g : A}
    (h : (g : G) ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (K.subgroupOf A : Set A) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro x
  simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using h (x : G)

private theorem e6rn_ne_of_level_zero_pos {μ ν : Fin Tag.E6.rank → ℤ}
    (hμ : iform μ lamE = 0) (hν : 0 < iform ν lamE) : μ ≠ ν := by
  intro h
  rw [← h, hμ] at hν
  exact (lt_irrefl 0) hν

private theorem e6rn_ne_neg_of_level_zero_pos {μ ν : Fin Tag.E6.rank → ℤ}
    (hμ : iform μ lamE = 0) (hν : 0 < iform ν lamE) : μ ≠ -ν := by
  intro h
  have h' := hμ
  rw [h, iform_neg_left] at h'
  omega

private theorem e6rn_xr_level0_mem_normalizer_rootSpan
    {μ : Fin Tag.E6.rank → ℤ}
    (hμ : IsRoot .E6 μ) (hμ0 : iform μ lamE = 0) :
    (xr μ : ModGL .E6 F2) ∈
      Subgroup.normalizer (rootSpan .E6 F2 qRoots : Set (ModGL .E6 F2)) := by
  rw [rootSpan_eq_closure]
  have key : ∀ s ∈ {g : ModGL .E6 F2 | ∃ γ ∈ qRoots, ∃ c : F2, pinnedX .E6 F2 γ c = g},
      (xr μ : ModGL .E6 F2) * s * (xr μ : ModGL .E6 F2)⁻¹ ∈
        Subgroup.closure {g : ModGL .E6 F2 | ∃ γ ∈ qRoots, ∃ c : F2,
          pinnedX .E6 F2 γ c = g} := by
    rintro s ⟨γ, hγ, c, rfl⟩
    have hne : μ ≠ γ := e6rn_ne_of_level_zero_pos hμ0 hγ.2
    have hne' : μ ≠ -γ := e6rn_ne_neg_of_level_zero_pos hμ0 hγ.2
    change (pinnedX .E6 F2 μ 1 * pinnedX .E6 F2 γ c * (pinnedX .E6 F2 μ 1)⁻¹) ∈
      Subgroup.closure {g : ModGL .E6 F2 | ∃ γ ∈ qRoots, ∃ c : F2,
        pinnedX .E6 F2 γ c = g}
    rcases E6Pilot.conj_pinnedX_cases (K := F2) hμ hγ.1 hne hne' (1 : F2) c with ⟨hr, he⟩ | he
    · rw [he]
      have hmem : μ + γ ∈ qRoots :=
        ⟨hr, by rw [iform_add_left, hμ0, zero_add]; exact hγ.2⟩
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure ⟨μ + γ, hmem, 1 * c, rfl⟩)
        (Subgroup.subset_closure ⟨γ, hγ, c, rfl⟩)
    · rw [he]
      exact Subgroup.subset_closure ⟨γ, hγ, c, rfl⟩
  have h2 : (xr μ : ModGL .E6 F2)⁻¹ = (xr μ : ModGL .E6 F2) := by
    change (pinnedX .E6 F2 μ 1)⁻¹ = pinnedX .E6 F2 μ 1
    rw [pinnedX_neg, CharTwo.neg_eq (1 : F2)]
  refine E6Pilot.mem_normalizer_closure_of_conj (g := (xr μ : ModGL .E6 F2)) ?_ ?_
  · exact key
  · intro s hs
    simpa [h2] using key s hs

private theorem e6rn_xr_level0_mem_normalizer_qE
    {μ : Fin Tag.E6.rank → ℤ}
    (hμ : IsRoot .E6 μ) (hμ0 : iform μ lamE = 0) :
    xr μ ∈ Subgroup.normalizer (qE : Set EC) :=
  e6rn_mem_normalizer_subgroupOf (K := rootSpan .E6 F2 qRoots) (A := adjointGroup .E6 F2)
    (g := xr μ) (e6rn_xr_level0_mem_normalizer_rootSpan hμ hμ0)

theorem e6rn_cOmegaE_zero_mem_normalizer_qE :
    cOmegaE 0 ∈ Subgroup.normalizer (qE : Set EC) := by
  have hm1 : IsRoot .E6 e6rn_m1 := isRoot_a5Root (by decide)
  have hm2 : IsRoot .E6 e6rn_m2 := isRoot_a5Root (by decide)
  have hm10 : iform e6rn_m1 lamE = 0 := by decide +kernel
  have hm20 : iform e6rn_m2 lamE = 0 := by decide +kernel
  change xr (a5Root (blk 0 0) (blk 0 1)) * xr (a5Root (blk 0 1) (blk 0 0)) ∈
    Subgroup.normalizer (qE : Set EC)
  exact Subgroup.mul_mem _ (e6rn_xr_level0_mem_normalizer_qE hm1 hm10)
    (e6rn_xr_level0_mem_normalizer_qE hm2 hm20)

private theorem e6rn_mul_self_of_commute {G : Type*} [Group G] {a b : G} (h : a * b = b * a)
    (ha : a * a = 1) (hb : b * b = 1) : (a * b) * (a * b) = 1 := by
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← h]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, mul_one]

private theorem e6rn_rOne_sq :
    rOne 0 2 * rOne 0 2 = 1 := by
  have ha := isRoot_a5Root (show (0:Fin 6) ≠ 4 by decide)
  have hb := isRoot_a5Root (show (1:Fin 6) ≠ 5 by decide)
  have hcomm : xr e6rn_ra * xr e6rn_rb = xr e6rn_rb * xr e6rn_ra :=
    e6rn_xr_commute_of_iform ha hb (by decide +kernel)
  exact e6rn_mul_self_of_commute hcomm (e6rn_xr_mul_self _) (e6rn_xr_mul_self _)

private theorem e6rn_rOmega_sq :
    rOmega 0 2 * rOmega 0 2 = 1 := by
  have hrd := isRoot_a5Root (show (0:Fin 6) ≠ 5 by decide)
  have hrc := isRoot_a5Root (show (1:Fin 6) ≠ 4 by decide)
  have hrb := isRoot_a5Root (show (1:Fin 6) ≠ 5 by decide)
  have hdc : xr e6rn_rd * xr e6rn_rc = xr e6rn_rc * xr e6rn_rd :=
    e6rn_xr_commute_of_iform hrd hrc (by decide +kernel)
  have ha : (xr e6rn_rd * xr e6rn_rc) * (xr e6rn_rd * xr e6rn_rc) = 1 :=
    e6rn_mul_self_of_commute hdc (e6rn_xr_mul_self _) (e6rn_xr_mul_self _)
  have hdrb : xr e6rn_rd * xr e6rn_rb = xr e6rn_rb * xr e6rn_rd :=
    e6rn_xr_commute_of_iform hrd hrb (by decide +kernel)
  have hcrb : xr e6rn_rc * xr e6rn_rb = xr e6rn_rb * xr e6rn_rc :=
    e6rn_xr_commute_of_iform hrc hrb (by decide +kernel)
  have hcomm : (xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb = xr e6rn_rb * (xr e6rn_rd * xr e6rn_rc) := by
    calc (xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb = xr e6rn_rd * (xr e6rn_rc * xr e6rn_rb) := by group
      _ = xr e6rn_rd * (xr e6rn_rb * xr e6rn_rc) := by rw [hcrb]
      _ = (xr e6rn_rd * xr e6rn_rb) * xr e6rn_rc := by group
      _ = (xr e6rn_rb * xr e6rn_rd) * xr e6rn_rc := by rw [hdrb]
      _ = xr e6rn_rb * (xr e6rn_rd * xr e6rn_rc) := by group
  change (xr e6rn_rd * xr e6rn_rc * xr e6rn_rb) * (xr e6rn_rd * xr e6rn_rc * xr e6rn_rb) = 1
  exact e6rn_mul_self_of_commute hcomm ha (e6rn_xr_mul_self _)

private theorem e6rn_rOmega_rOne :
    rOmega 0 2 * rOne 0 2 = rOne 0 2 * rOmega 0 2 := by
  have hra := isRoot_a5Root (show (0:Fin 6) ≠ 4 by decide)
  have hrb := isRoot_a5Root (show (1:Fin 6) ≠ 5 by decide)
  have hrc := isRoot_a5Root (show (1:Fin 6) ≠ 4 by decide)
  have hrd := isRoot_a5Root (show (0:Fin 6) ≠ 5 by decide)
  have hda : xr e6rn_rd * xr e6rn_ra = xr e6rn_ra * xr e6rn_rd :=
    e6rn_xr_commute_of_iform hrd hra (by decide +kernel)
  have hca : xr e6rn_rc * xr e6rn_ra = xr e6rn_ra * xr e6rn_rc :=
    e6rn_xr_commute_of_iform hrc hra (by decide +kernel)
  have hba : xr e6rn_rb * xr e6rn_ra = xr e6rn_ra * xr e6rn_rb :=
    e6rn_xr_commute_of_iform hrb hra (by decide +kernel)
  have hdb : xr e6rn_rd * xr e6rn_rb = xr e6rn_rb * xr e6rn_rd :=
    e6rn_xr_commute_of_iform hrd hrb (by decide +kernel)
  have hcb : xr e6rn_rc * xr e6rn_rb = xr e6rn_rb * xr e6rn_rc :=
    e6rn_xr_commute_of_iform hrc hrb (by decide +kernel)
  have hXra : ((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb) * xr e6rn_ra =
      xr e6rn_ra * ((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb) := by
    calc ((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb) * xr e6rn_ra
        = xr e6rn_rd * (xr e6rn_rc * (xr e6rn_rb * xr e6rn_ra)) := by group
      _ = xr e6rn_rd * (xr e6rn_rc * (xr e6rn_ra * xr e6rn_rb)) := by rw [hba]
      _ = xr e6rn_rd * (xr e6rn_ra * (xr e6rn_rc * xr e6rn_rb)) := by
            rw [show xr e6rn_rc * (xr e6rn_ra * xr e6rn_rb) =
                (xr e6rn_rc * xr e6rn_ra) * xr e6rn_rb by group, hca]
            group
      _ = (xr e6rn_rd * xr e6rn_ra) * (xr e6rn_rc * xr e6rn_rb) := by group
      _ = (xr e6rn_ra * xr e6rn_rd) * (xr e6rn_rc * xr e6rn_rb) := by rw [← hda]
      _ = xr e6rn_ra * ((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb) := by group
  have hXrb : ((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb) * xr e6rn_rb =
      xr e6rn_rb * ((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb) := by
    calc ((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb) * xr e6rn_rb
        = xr e6rn_rd * xr e6rn_rc := by rw [mul_assoc, e6rn_xr_mul_self, mul_one]
      _ = xr e6rn_rb * ((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb) := by
        rw [show xr e6rn_rb * ((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb) =
            xr e6rn_rd * xr e6rn_rc by
          calc xr e6rn_rb * ((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb)
              = (xr e6rn_rb * xr e6rn_rd) * xr e6rn_rc * xr e6rn_rb := by group
            _ = (xr e6rn_rd * xr e6rn_rb) * xr e6rn_rc * xr e6rn_rb := by rw [← hdb]
            _ = xr e6rn_rd * (xr e6rn_rb * xr e6rn_rc) * xr e6rn_rb := by group
            _ = xr e6rn_rd * (xr e6rn_rc * xr e6rn_rb) * xr e6rn_rb := by rw [← hcb]
            _ = xr e6rn_rd * xr e6rn_rc := by
              rw [show xr e6rn_rd * (xr e6rn_rc * xr e6rn_rb) * xr e6rn_rb =
                  xr e6rn_rd * (xr e6rn_rc * (xr e6rn_rb * xr e6rn_rb)) by group,
                e6rn_xr_mul_self, mul_one]]
  calc ((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb) * (xr e6rn_ra * xr e6rn_rb)
      = ((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb) * xr e6rn_ra * xr e6rn_rb := by group
    _ = xr e6rn_ra * ((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb) * xr e6rn_rb := by rw [hXra]
    _ = xr e6rn_ra * (((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb) * xr e6rn_rb) := by group
    _ = xr e6rn_ra * (xr e6rn_rb * ((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb)) := by rw [hXrb]
    _ = (xr e6rn_ra * xr e6rn_rb) * ((xr e6rn_rd * xr e6rn_rc) * xr e6rn_rb) := by group

private theorem e6rn_rOneMul_sq :
    (rOne 0 2 * rOmega 0 2) * (rOne 0 2 * rOmega 0 2) = 1 := by
  rw [show rOne 0 2 * rOmega 0 2 = rOmega 0 2 * rOne 0 2 from e6rn_rOmega_rOne.symm]
  exact e6rn_mul_self_of_commute e6rn_rOmega_rOne e6rn_rOmega_sq e6rn_rOne_sq

private theorem e6rn_rE_cases
    {r : EC} (hr : r ∈ rE) :
    r = 1 ∨ r = rOne 0 2 ∨ r = rOmega 0 2 ∨ r = rOne 0 2 * rOmega 0 2 := by
  have h11 : rOne 0 2 * rOne 0 2 = 1 := e6rn_rOne_sq
  have h22 : rOmega 0 2 * rOmega 0 2 = 1 := e6rn_rOmega_sq
  have h21 : rOmega 0 2 * rOne 0 2 = rOne 0 2 * rOmega 0 2 := e6rn_rOmega_rOne
  have h112 : rOne 0 2 * (rOne 0 2 * rOmega 0 2) = rOmega 0 2 := by
    rw [← mul_assoc, h11, one_mul]
  have h221 : rOmega 0 2 * (rOne 0 2 * rOmega 0 2) = rOne 0 2 := by
    rw [← mul_assoc, h21, mul_assoc, h22, mul_one]
  have h121 : (rOne 0 2 * rOmega 0 2) * rOne 0 2 = rOmega 0 2 := by
    rw [mul_assoc, h21, ← mul_assoc, h11, one_mul]
  have h122 : (rOne 0 2 * rOmega 0 2) * rOmega 0 2 = rOne 0 2 := by
    rw [mul_assoc, h22, mul_one]
  have h1212 : (rOne 0 2 * rOmega 0 2) * (rOne 0 2 * rOmega 0 2) = 1 := e6rn_rOneMul_sq
  rw [rE] at hr
  induction hr using Subgroup.closure_induction with
  | mem y hy =>
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul a b _ _ iha ihb =>
      rcases iha with rfl | rfl | rfl | rfl <;> rcases ihb with rfl | rfl | rfl | rfl
      · rw [one_mul]; exact Or.inl rfl
      · rw [one_mul]; exact Or.inr (Or.inl rfl)
      · rw [one_mul]; exact Or.inr (Or.inr (Or.inl rfl))
      · rw [one_mul]; exact Or.inr (Or.inr (Or.inr rfl))
      · rw [mul_one]; exact Or.inr (Or.inl rfl)
      · exact Or.inl h11
      · exact Or.inr (Or.inr (Or.inr rfl))
      · rw [h112]; exact Or.inr (Or.inr (Or.inl rfl))
      · rw [mul_one]; exact Or.inr (Or.inr (Or.inl rfl))
      · rw [h21]; exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl h22
      · rw [h221]; exact Or.inr (Or.inl rfl)
      · rw [mul_one]; exact Or.inr (Or.inr (Or.inr rfl))
      · rw [h121]; exact Or.inr (Or.inr (Or.inl rfl))
      · rw [h122]; exact Or.inr (Or.inl rfl)
      · exact Or.inl h1212
  | inv a _ iha =>
      rcases iha with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · rw [inv_eq_of_mul_eq_one_right h11]; exact Or.inr (Or.inl rfl)
      · rw [inv_eq_of_mul_eq_one_right h22]; exact Or.inr (Or.inr (Or.inl rfl))
      · rw [inv_eq_of_mul_eq_one_right h1212]; exact Or.inr (Or.inr (Or.inr rfl))

theorem e6rn_delta_conj_rOne :
    cOmegaE 0 * rOne 0 2 * (cOmegaE 0)⁻¹ = rOmega 0 2 := by
  have hra := isRoot_a5Root (show (0:Fin 6) ≠ 4 by decide)
  have hrb := isRoot_a5Root (show (1:Fin 6) ≠ 5 by decide)
  have hrc := isRoot_a5Root (show (1:Fin 6) ≠ 4 by decide)
  have hrd := isRoot_a5Root (show (0:Fin 6) ≠ 5 by decide)
  have hm1 := isRoot_a5Root (show (0:Fin 6) ≠ 1 by decide)
  have hm2 := isRoot_a5Root (show (1:Fin 6) ≠ 0 by decide)
  have h1a : xr e6rn_m2 * xr e6rn_ra * (xr e6rn_m2)⁻¹ = xr e6rn_rc * xr e6rn_ra :=
    e6rn_xr_conj_of_iform hm2 hra (by decide +kernel) (by decide +kernel)
  have h1b : xr e6rn_m2 * xr e6rn_rb * (xr e6rn_m2)⁻¹ = xr e6rn_rb := by
    have hc : xr e6rn_m2 * xr e6rn_rb = xr e6rn_rb * xr e6rn_m2 :=
      e6rn_xr_commute_of_iform hm2 hrb (by decide +kernel)
    calc xr e6rn_m2 * xr e6rn_rb * (xr e6rn_m2)⁻¹
        = xr e6rn_rb * xr e6rn_m2 * (xr e6rn_m2)⁻¹ := by rw [hc]
      _ = xr e6rn_rb := by group
  have h2a : xr e6rn_m1 * xr e6rn_rc * (xr e6rn_m1)⁻¹ = xr e6rn_ra * xr e6rn_rc :=
    e6rn_xr_conj_of_iform hm1 hrc (by decide +kernel) (by decide +kernel)
  have h2b : xr e6rn_m1 * xr e6rn_ra * (xr e6rn_m1)⁻¹ = xr e6rn_ra := by
    have hc : xr e6rn_m1 * xr e6rn_ra = xr e6rn_ra * xr e6rn_m1 :=
      e6rn_xr_commute_of_iform hm1 hra (by decide +kernel)
    calc xr e6rn_m1 * xr e6rn_ra * (xr e6rn_m1)⁻¹
        = xr e6rn_ra * xr e6rn_m1 * (xr e6rn_m1)⁻¹ := by rw [hc]
      _ = xr e6rn_ra := by group
  have h2c : xr e6rn_m1 * xr e6rn_rb * (xr e6rn_m1)⁻¹ = xr e6rn_rd * xr e6rn_rb :=
    e6rn_xr_conj_of_iform hm1 hrb (by decide +kernel) (by decide +kernel)
  have hstep1 : xr e6rn_m2 * (xr e6rn_ra * xr e6rn_rb) * (xr e6rn_m2)⁻¹ =
      xr e6rn_rc * xr e6rn_ra * xr e6rn_rb := by
    rw [show xr e6rn_m2 * (xr e6rn_ra * xr e6rn_rb) * (xr e6rn_m2)⁻¹ =
        (xr e6rn_m2 * xr e6rn_ra * (xr e6rn_m2)⁻¹) *
          (xr e6rn_m2 * xr e6rn_rb * (xr e6rn_m2)⁻¹) by group, h1a, h1b]
  have hstep2 : xr e6rn_m1 * (xr e6rn_rc * xr e6rn_ra * xr e6rn_rb) * (xr e6rn_m1)⁻¹ =
      xr e6rn_ra * xr e6rn_rc * xr e6rn_ra * xr e6rn_rd * xr e6rn_rb := by
    rw [show xr e6rn_m1 * (xr e6rn_rc * xr e6rn_ra * xr e6rn_rb) * (xr e6rn_m1)⁻¹ =
        (xr e6rn_m1 * xr e6rn_rc * (xr e6rn_m1)⁻¹) *
          (xr e6rn_m1 * xr e6rn_ra * (xr e6rn_m1)⁻¹) *
            (xr e6rn_m1 * xr e6rn_rb * (xr e6rn_m1)⁻¹) by group, h2a, h2b, h2c]
    group
  have hcra : xr e6rn_rc * xr e6rn_ra = xr e6rn_ra * xr e6rn_rc :=
    e6rn_xr_commute_of_iform hrc hra (by decide +kernel)
  have hcrd : xr e6rn_rc * xr e6rn_rd = xr e6rn_rd * xr e6rn_rc :=
    e6rn_xr_commute_of_iform hrc hrd (by decide +kernel)
  change (xr e6rn_m1 * xr e6rn_m2) * (xr e6rn_ra * xr e6rn_rb) * (xr e6rn_m1 * xr e6rn_m2)⁻¹ =
    xr e6rn_rd * xr e6rn_rc * xr e6rn_rb
  rw [show (xr e6rn_m1 * xr e6rn_m2) * (xr e6rn_ra * xr e6rn_rb) * (xr e6rn_m1 * xr e6rn_m2)⁻¹ =
      xr e6rn_m1 * (xr e6rn_m2 * (xr e6rn_ra * xr e6rn_rb) * (xr e6rn_m2)⁻¹) *
        (xr e6rn_m1)⁻¹ by group, hstep1, hstep2]
  calc xr e6rn_ra * xr e6rn_rc * xr e6rn_ra * xr e6rn_rd * xr e6rn_rb
      = xr e6rn_ra * (xr e6rn_rc * xr e6rn_ra) * xr e6rn_rd * xr e6rn_rb := by group
    _ = xr e6rn_ra * (xr e6rn_ra * xr e6rn_rc) * xr e6rn_rd * xr e6rn_rb := by rw [hcra]
    _ = (xr e6rn_ra * xr e6rn_ra) * (xr e6rn_rc * xr e6rn_rd * xr e6rn_rb) := by group
    _ = xr e6rn_rc * xr e6rn_rd * xr e6rn_rb := by rw [e6rn_xr_mul_self, one_mul]
    _ = xr e6rn_rd * xr e6rn_rc * xr e6rn_rb := by rw [hcrd]

theorem e6rn_delta_conj_rOmega :
    cOmegaE 0 * rOmega 0 2 * (cOmegaE 0)⁻¹ = rOne 0 2 * rOmega 0 2 := by
  have hra := isRoot_a5Root (show (0:Fin 6) ≠ 4 by decide)
  have hrb := isRoot_a5Root (show (1:Fin 6) ≠ 5 by decide)
  have hrc := isRoot_a5Root (show (1:Fin 6) ≠ 4 by decide)
  have hrd := isRoot_a5Root (show (0:Fin 6) ≠ 5 by decide)
  have hm1 := isRoot_a5Root (show (0:Fin 6) ≠ 1 by decide)
  have hm2 := isRoot_a5Root (show (1:Fin 6) ≠ 0 by decide)
  have h1d : xr e6rn_m2 * xr e6rn_rd * (xr e6rn_m2)⁻¹ = xr e6rn_rb * xr e6rn_rd :=
    e6rn_xr_conj_of_iform hm2 hrd (by decide +kernel) (by decide +kernel)
  have h1c : xr e6rn_m2 * xr e6rn_rc * (xr e6rn_m2)⁻¹ = xr e6rn_rc := by
    have hc : xr e6rn_m2 * xr e6rn_rc = xr e6rn_rc * xr e6rn_m2 :=
      e6rn_xr_commute_of_iform hm2 hrc (by decide +kernel)
    calc xr e6rn_m2 * xr e6rn_rc * (xr e6rn_m2)⁻¹
        = xr e6rn_rc * xr e6rn_m2 * (xr e6rn_m2)⁻¹ := by rw [hc]
      _ = xr e6rn_rc := by group
  have h1b : xr e6rn_m2 * xr e6rn_rb * (xr e6rn_m2)⁻¹ = xr e6rn_rb := by
    have hc : xr e6rn_m2 * xr e6rn_rb = xr e6rn_rb * xr e6rn_m2 :=
      e6rn_xr_commute_of_iform hm2 hrb (by decide +kernel)
    calc xr e6rn_m2 * xr e6rn_rb * (xr e6rn_m2)⁻¹
        = xr e6rn_rb * xr e6rn_m2 * (xr e6rn_m2)⁻¹ := by rw [hc]
      _ = xr e6rn_rb := by group
  have h2b : xr e6rn_m1 * xr e6rn_rb * (xr e6rn_m1)⁻¹ = xr e6rn_rd * xr e6rn_rb :=
    e6rn_xr_conj_of_iform hm1 hrb (by decide +kernel) (by decide +kernel)
  have h2d : xr e6rn_m1 * xr e6rn_rd * (xr e6rn_m1)⁻¹ = xr e6rn_rd := by
    have hc : xr e6rn_m1 * xr e6rn_rd = xr e6rn_rd * xr e6rn_m1 :=
      e6rn_xr_commute_of_iform hm1 hrd (by decide +kernel)
    calc xr e6rn_m1 * xr e6rn_rd * (xr e6rn_m1)⁻¹
        = xr e6rn_rd * xr e6rn_m1 * (xr e6rn_m1)⁻¹ := by rw [hc]
      _ = xr e6rn_rd := by group
  have h2c : xr e6rn_m1 * xr e6rn_rc * (xr e6rn_m1)⁻¹ = xr e6rn_ra * xr e6rn_rc :=
    e6rn_xr_conj_of_iform hm1 hrc (by decide +kernel) (by decide +kernel)
  have hstep1 : xr e6rn_m2 * (xr e6rn_rd * xr e6rn_rc * xr e6rn_rb) * (xr e6rn_m2)⁻¹ =
      xr e6rn_rb * xr e6rn_rd * xr e6rn_rc * xr e6rn_rb := by
    rw [show xr e6rn_m2 * (xr e6rn_rd * xr e6rn_rc * xr e6rn_rb) * (xr e6rn_m2)⁻¹ =
        (xr e6rn_m2 * xr e6rn_rd * (xr e6rn_m2)⁻¹) *
          (xr e6rn_m2 * xr e6rn_rc * (xr e6rn_m2)⁻¹) *
            (xr e6rn_m2 * xr e6rn_rb * (xr e6rn_m2)⁻¹) by group, h1d, h1c, h1b]
  have hstep2 : xr e6rn_m1 * (xr e6rn_rb * xr e6rn_rd * xr e6rn_rc * xr e6rn_rb) *
        (xr e6rn_m1)⁻¹ =
      xr e6rn_rd * xr e6rn_rb * xr e6rn_rd * xr e6rn_ra * xr e6rn_rc * xr e6rn_rd * xr e6rn_rb := by
    have expand : xr e6rn_m1 * (xr e6rn_rb * xr e6rn_rd * xr e6rn_rc * xr e6rn_rb) *
          (xr e6rn_m1)⁻¹ =
        (xr e6rn_m1 * xr e6rn_rb * (xr e6rn_m1)⁻¹) *
          (xr e6rn_m1 * xr e6rn_rd * (xr e6rn_m1)⁻¹) *
            (xr e6rn_m1 * xr e6rn_rc * (xr e6rn_m1)⁻¹) *
              (xr e6rn_m1 * xr e6rn_rb * (xr e6rn_m1)⁻¹) := by group
    rw [expand, h2b, h2d, h2c]
    group
  have hdr : xr e6rn_rd * xr e6rn_ra = xr e6rn_ra * xr e6rn_rd :=
    e6rn_xr_commute_of_iform hrd hra (by decide +kernel)
  have hbr : xr e6rn_rb * xr e6rn_ra = xr e6rn_ra * xr e6rn_rb :=
    e6rn_xr_commute_of_iform hrb hra (by decide +kernel)
  have hrb' : xr e6rn_rb * xr e6rn_rd = xr e6rn_rd * xr e6rn_rb :=
    e6rn_xr_commute_of_iform hrb hrd (by decide +kernel)
  have hrc' : xr e6rn_rb * xr e6rn_rc = xr e6rn_rc * xr e6rn_rb :=
    e6rn_xr_commute_of_iform hrb hrc (by decide +kernel)
  have hac : xr e6rn_rc * xr e6rn_rd = xr e6rn_rd * xr e6rn_rc :=
    e6rn_xr_commute_of_iform hrc hrd (by decide +kernel)
  change (xr e6rn_m1 * xr e6rn_m2) * (xr e6rn_rd * xr e6rn_rc * xr e6rn_rb) *
      (xr e6rn_m1 * xr e6rn_m2)⁻¹ =
    (xr e6rn_ra * xr e6rn_rb) * (xr e6rn_rd * xr e6rn_rc * xr e6rn_rb)
  calc (xr e6rn_m1 * xr e6rn_m2) * (xr e6rn_rd * xr e6rn_rc * xr e6rn_rb) *
        (xr e6rn_m1 * xr e6rn_m2)⁻¹
      = xr e6rn_m1 * (xr e6rn_m2 * (xr e6rn_rd * xr e6rn_rc * xr e6rn_rb) *
          (xr e6rn_m2)⁻¹) * (xr e6rn_m1)⁻¹ := by group
    _ = xr e6rn_m1 * (xr e6rn_rb * xr e6rn_rd * xr e6rn_rc * xr e6rn_rb) *
          (xr e6rn_m1)⁻¹ := by rw [hstep1]
    _ = xr e6rn_rd * xr e6rn_rb * xr e6rn_rd * xr e6rn_ra * xr e6rn_rc * xr e6rn_rd *
          xr e6rn_rb := by rw [hstep2]
    _ = (xr e6rn_ra * xr e6rn_rb) * (xr e6rn_rd * xr e6rn_rc * xr e6rn_rb) := by
      have hA : xr e6rn_rd * xr e6rn_rb * xr e6rn_rd = xr e6rn_rb := by
        rw [show xr e6rn_rd * xr e6rn_rb * xr e6rn_rd =
            (xr e6rn_rd * xr e6rn_rb) * xr e6rn_rd by group,
          hrb'.symm, mul_assoc, e6rn_xr_mul_self, mul_one]
      have hL : xr e6rn_rd * xr e6rn_rb * xr e6rn_rd * xr e6rn_ra * xr e6rn_rc *
          xr e6rn_rd * xr e6rn_rb = xr e6rn_ra * xr e6rn_rd * xr e6rn_rc := by
        rw [show xr e6rn_rd * xr e6rn_rb * xr e6rn_rd * xr e6rn_ra * xr e6rn_rc *
              xr e6rn_rd * xr e6rn_rb =
            (xr e6rn_rd * xr e6rn_rb * xr e6rn_rd) * (xr e6rn_ra * xr e6rn_rc) *
              (xr e6rn_rd * xr e6rn_rb) by group, hA]
        rw [show xr e6rn_rb * (xr e6rn_ra * xr e6rn_rc) * (xr e6rn_rd * xr e6rn_rb) =
            (xr e6rn_rb * xr e6rn_ra) * xr e6rn_rc * (xr e6rn_rd * xr e6rn_rb) by group,
          hbr]
        rw [show (xr e6rn_ra * xr e6rn_rb) * xr e6rn_rc * (xr e6rn_rd * xr e6rn_rb) =
            xr e6rn_ra * (xr e6rn_rb * xr e6rn_rc) * (xr e6rn_rd * xr e6rn_rb) by group,
          hrc']
        rw [show xr e6rn_ra * (xr e6rn_rc * xr e6rn_rb) * (xr e6rn_rd * xr e6rn_rb) =
            xr e6rn_ra * xr e6rn_rc * (xr e6rn_rb * xr e6rn_rd) * xr e6rn_rb by group,
          hrb']
        rw [show xr e6rn_ra * xr e6rn_rc * (xr e6rn_rd * xr e6rn_rb) * xr e6rn_rb =
            xr e6rn_ra * (xr e6rn_rc * xr e6rn_rd) * (xr e6rn_rb * xr e6rn_rb) by group,
          e6rn_xr_mul_self, mul_one, hac]
        group
      have hR : xr e6rn_ra * (xr e6rn_rb * (xr e6rn_rd * (xr e6rn_rc * xr e6rn_rb))) =
          xr e6rn_ra * xr e6rn_rd * xr e6rn_rc := by
        rw [show xr e6rn_ra * (xr e6rn_rb * (xr e6rn_rd * (xr e6rn_rc * xr e6rn_rb))) =
            xr e6rn_ra * (xr e6rn_rb * xr e6rn_rd) * xr e6rn_rc * xr e6rn_rb by group,
          hrb']
        rw [show xr e6rn_ra * (xr e6rn_rd * xr e6rn_rb) * xr e6rn_rc * xr e6rn_rb =
            xr e6rn_ra * xr e6rn_rd * (xr e6rn_rb * xr e6rn_rc) * xr e6rn_rb by group,
          hrc']
        rw [show xr e6rn_ra * xr e6rn_rd * (xr e6rn_rc * xr e6rn_rb) * xr e6rn_rb =
            xr e6rn_ra * xr e6rn_rd * xr e6rn_rc * (xr e6rn_rb * xr e6rn_rb) by group,
          e6rn_xr_mul_self, mul_one]
      rw [show (xr e6rn_ra * xr e6rn_rb) * (xr e6rn_rd * xr e6rn_rc * xr e6rn_rb) =
          xr e6rn_ra * (xr e6rn_rb * (xr e6rn_rd * (xr e6rn_rc * xr e6rn_rb))) by group]
      rw [hR]
      exact hL

theorem e6rn_pCoreOf_perfectCore_centralizer_rOmega :
    CFSG.Open.pCoreOf 2 (CFSG.Quasithin.perfectCore
        (Subgroup.centralizer ({rOmega 0 2} : Set EC))) = qE := by
  have hconj := e6rn_pCoreOf_conj (cOmegaE 0) (rOne 0 2)
  rw [e6rn_delta_conj_rOne, e6rn_pCoreOf_perfectCore_centralizer_rOne] at hconj
  rw [hconj]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp e6rn_cOmegaE_zero_mem_normalizer_qE

theorem e6rn_pCoreOf_perfectCore_centralizer_rOneMul :
    CFSG.Open.pCoreOf 2 (CFSG.Quasithin.perfectCore
        (Subgroup.centralizer ({rOne 0 2 * rOmega 0 2} : Set EC))) = qE := by
  have hconj := e6rn_pCoreOf_conj (cOmegaE 0) (rOmega 0 2)
  rw [e6rn_delta_conj_rOmega, e6rn_pCoreOf_perfectCore_centralizer_rOmega] at hconj
  rw [hconj]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp e6rn_cOmegaE_zero_mem_normalizer_qE

theorem normalizer_rE_le_normalizer_qE :
    Subgroup.normalizer (rE : Set EC) ≤ Subgroup.normalizer (qE : Set EC) := by
  have hra : IsRoot .E6 e6rn_ra := isRoot_a5Root (by decide)
  have hrb : IsRoot .E6 e6rn_rb := isRoot_a5Root (by decide)
  have hne : e6rn_ra ≠ e6rn_rb := by decide +kernel
  have hrne : rOne 0 2 ≠ 1 := by
    intro h
    have hval := congrArg Subtype.val h
    change pinnedX .E6 F2 e6rn_ra 1 * pinnedX .E6 F2 e6rn_rb 1 = 1 at hval
    have h1 : ((List.map fun σ => pinnedX .E6 F2 σ ((fun _ => (1 : F2)) σ))
        [e6rn_ra, e6rn_rb]).prod =
        ((List.map fun σ => pinnedX .E6 F2 σ ((fun _ => (0 : F2)) σ))
        [e6rn_ra, e6rn_rb]).prod := by
      simpa [pinnedX_zero] using hval
    exact one_ne_zero (pinnedX_list_prod_injective
      [e6rn_ra, e6rn_rb] (by simpa [List.nodup_cons] using hne)
      (by
        intro α hα
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
        rcases hα with rfl | rfl
        · exact ⟨hra, by decide +kernel⟩
        · exact ⟨hrb, by decide +kernel⟩)
      (fun _ => 1) (fun _ => 0) h1 e6rn_ra (by simp))
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hr : g * rOne 0 2 * g⁻¹ ∈ rE :=
    (Subgroup.mem_normalizer_iff.mp hg (rOne 0 2)).mp (Subgroup.subset_closure (Or.inl rfl))
  have hrne' : g * rOne 0 2 * g⁻¹ ≠ 1 := by
    intro h
    apply hrne
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [mul_assoc] using this
  rcases e6rn_rE_cases hr with h1 | h1 | h1 | h1
  · exact absurd h1 hrne'
  · have hconj := e6rn_pCoreOf_conj g (rOne 0 2)
    rw [h1] at hconj
    simp only [e6rn_pCoreOf_perfectCore_centralizer_rOne] at hconj
    exact hconj.symm
  · have hconj := e6rn_pCoreOf_conj g (rOne 0 2)
    rw [h1] at hconj
    simp only [e6rn_pCoreOf_perfectCore_centralizer_rOne,
      e6rn_pCoreOf_perfectCore_centralizer_rOmega] at hconj
    exact hconj.symm
  · have hconj := e6rn_pCoreOf_conj g (rOne 0 2)
    rw [h1] at hconj
    simp only [e6rn_pCoreOf_perfectCore_centralizer_rOne,
      e6rn_pCoreOf_perfectCore_centralizer_rOneMul] at hconj
    exact hconj.symm

end CFSG.StandardType.GGSixE6Two
