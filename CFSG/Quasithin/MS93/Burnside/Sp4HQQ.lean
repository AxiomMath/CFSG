module

public import CFSG.Quasithin.MS93.Burnside.Sp4HGal
public import CFSG.Quasithin.MS93.Burnside.Sp4HZst
import CFSG.Quasithin.MS93.S33LamW

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Count

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F]

theorem burnsideSp4H_card_le_card_map_mul {A V Z : Subgroup G} {α : ↥A →* MSP.Sp4 F}
    (c : MSP.NatCoord A V Z α) (H : Subgroup G) :
    Nat.card (MSP.V4 F) ≤ Nat.card ((H.subgroupOf V).map c.toVec) * H.relIndex V := by
  set K : Subgroup ↥V := H.subgroupOf V
  have h1 := Subgroup.relIndex_mul_card (H := c.toVec.ker) (K := K)
  rw [Subgroup.relIndex_ker] at h1
  have hker : Nat.card ↥(c.toVec.ker ⊓ K) ≤ Nat.card ↥(V ⊓ Z) := by
    have hle : c.toVec.ker ⊓ K ≤ Z.subgroupOf V := by
      rw [c.ker_eq]
      exact inf_le_left
    calc Nat.card ↥(c.toVec.ker ⊓ K) ≤ Nat.card ↥(Z.subgroupOf V) := Subgroup.card_le_of_le hle
      _ = Nat.card ↥(V ⊓ Z) := by
        rw [← Subgroup.inf_subgroupOf_left, inf_comm]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hK : Nat.card K * H.relIndex V = Nat.card ↥V := by
    have := Subgroup.relIndex_mul_card (H := H) (K := V)
    rw [mul_comm, ← this]
    congr 1
    have e1 : Nat.card K = Nat.card ↥((H ⊓ V).subgroupOf V) := by
      rw [Subgroup.inf_subgroupOf_right]
    rw [e1, inf_comm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hZ : 0 < Nat.card ↥(V ⊓ Z) := Nat.card_pos
  have key : Nat.card ↥(V ⊓ Z) * Nat.card (MSP.V4 F) ≤
      Nat.card ↥(V ⊓ Z) * (Nat.card (K.map c.toVec) * H.relIndex V) := by
    rw [← c.card_eq, ← hK, ← h1]
    calc Nat.card ↥(K.map c.toVec) * Nat.card ↥(c.toVec.ker ⊓ K) * H.relIndex V
        ≤ Nat.card ↥(K.map c.toVec) * Nat.card ↥(V ⊓ Z) * H.relIndex V :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hker)
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left key hZ

theorem burnsideSp4H_exists_vec_eq_of_card [Finite F] {A V Z : Subgroup G}
    {α : ↥A →* MSP.Sp4 F} (c : MSP.NatCoord A V Z α) {H : Subgroup G}
    {S : Submodule F (MSP.V4 F)} (hHS : ∀ u : ↥V, (u : G) ∈ H → c.vec u ∈ S)
    (hcard : Nat.card S ≤ Nat.card ((H.subgroupOf V).map c.toVec)) :
    ∀ w ∈ S, ∃ u : ↥V, (u : G) ∈ H ∧ c.vec u = w := by
  have hmem : ∀ x : ↥((H.subgroupOf V).map c.toVec),
      Multiplicative.toAdd (x : Multiplicative (MSP.V4 F)) ∈ S := by
    rintro ⟨_, u, hu, rfl⟩
    exact hHS u (Subgroup.mem_subgroupOf.1 hu)
  let f : ↥((H.subgroupOf V).map c.toVec) → ↥S := fun x => ⟨_, hmem x⟩
  have hf : Function.Injective f := fun x y hxy =>
    Subtype.ext (Multiplicative.toAdd.injective (congrArg Subtype.val hxy :))
  have hle := Nat.card_le_card_of_injective f hf
  have hbij := (Nat.bijective_iff_injective_and_card f).2 ⟨hf, le_antisymm hle hcard⟩
  intro w hw
  obtain ⟨⟨_, u, hu, rfl⟩, hx⟩ := hbij.2 ⟨w, hw⟩
  exact ⟨u, Subgroup.mem_subgroupOf.1 hu, congrArg Subtype.val hx⟩

theorem burnsideSp4H_eq_zero_of_trichotomy {E : Type} [AddCommGroup E] [Module F E]
    (hF : ∃ l : F, l ≠ 0 ∧ l ≠ -1) {w : E} (hw : ∀ l : F, w = 0 ∨ l • w = 0 ∨ w + l • w = 0) :
    w = 0 := by
  obtain ⟨l, hl0, hl1⟩ := hF
  rcases hw l with h0 | h0 | h0
  · exact h0
  · exact (smul_eq_zero.1 h0).resolve_left hl0
  · have : (1 + l) • w = 0 := by rw [add_smul, one_smul, h0]
    rcases smul_eq_zero.1 this with h1 | h1
    · exact absurd (eq_neg_of_add_eq_zero_right h1) hl1
    · exact h1

end Count

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideSp4H_exists_vec_eq (h : PUHyp M T L)
    {μ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) μ (baseA _))
    {F : Type} [Field F] [Fintype F] {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F)}
    (c : MSP.NatCoord (L ⊔ pCoreOf 2 M) (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G))
      φ)
    {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p)
    (hpe : ((S33.pre h.le (ZM _ μ)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ = MSP.xPoint p)
    (hrel : (Qv _ μ).relIndex (ZM (puAmalgam h.le) (baseA _)) = Fintype.card F) :
    ∀ v ∈ MSP.perp p, ∃ u : ↥(Uq M T L), (u : G) ∈ S33.pre h.le (Qv _ μ) ∧ c.vec u = v := by
  have h20 := h.hyp20
  have hKM : L ⊔ pCoreOf 2 M ≤ M := sup_le h.L_le (pCoreOf_le' M)
  have hAV : L ⊔ pCoreOf 2 M ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    hKM.trans (le_normalizer_Uq h.le_normalizer)
  have hHS : ∀ u : ↥(Uq M T L), (u : G) ∈ S33.pre h.le (Qv _ μ) → c.vec u ∈ MSP.perp p := by
    intro u hu
    rw [← MSP.fixSp_xPoint hp, ← hpe]
    refine c.vec_mem_fixSp hAV _ u fun b hb => ?_
    obtain ⟨x, hx, hxb⟩ := (S33.mem_pre_iff' h.le).1 (Subgroup.mem_subgroupOf.1 hb)
    obtain ⟨y, hy, hyu⟩ := (S33.mem_pre_iff' h.le).1 hu
    have h1 := Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hc.1 hx) _ hy
    rw [← map_mul, ← map_mul] at h1
    have h2 := congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)
    simp only [Subgroup.coe_mul] at h2
    rw [← hxb, ← hyu]
    exact h2.symm
  have hidx : (S33.pre h.le (Qv _ μ)).relIndex (Uq M T L) ≤ Fintype.card F := by
    calc (S33.pre h.le (Qv _ μ)).relIndex (Uq M T L)
        ≤ (S33.pre h.le (Qv _ μ)).relIndex (Z0q M T) :=
          Subgroup.relIndex_le_of_le_right (Uq_le_Z0q h.L_le) Subgroup.index_ne_zero_of_finite
      _ = (Qv _ μ).relIndex (ZM (puAmalgam h.le) (baseA _)) := by
          rw [S33.relIndex_pre h.le _ (Z0q_le M T), ← puAmalgam.zm_baseA]
      _ = Fintype.card F := hrel
  have hcnt := burnsideSp4H_card_le_card_map_mul c (S33.pre h.le (Qv _ μ))
  have hFn : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hperp : Nat.card (MSP.perp p) = Fintype.card F ^ 3 := by
    rw [Module.natCard_eq_pow_finrank (K := F), hFn]
    have := MSP.finrank_perp p
    rw [show Module.finrank F p = 1 from hp] at this
    congr 1
    omega
  refine burnsideSp4H_exists_vec_eq_of_card c hHS ?_
  rw [hperp]
  rw [MSP.card_V4, hFn] at hcnt
  have h4 : Fintype.card F ^ 4 ≤
      Nat.card (((S33.pre h.le (Qv _ μ)).subgroupOf (Uq M T L)).map c.toVec) *
        Fintype.card F :=
    hcnt.trans (Nat.mul_le_mul_left _ hidx)
  have e4 : Fintype.card F ^ 4 = Fintype.card F ^ 3 * Fintype.card F := by ring
  rw [e4] at h4
  exact Nat.le_of_mul_le_mul_right h4 hq

theorem burnsideSp4H_mem_xPoint_of_psub (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    {μ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) μ (baseA _))
    {F : Type} [Field F] [Fintype F] (hF : ∃ l : F, l ≠ 0 ∧ l ≠ -1)
    {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F)}
    (c : MSP.NatCoord (L ⊔ pCoreOf 2 M) (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G))
      φ)
    {p : Submodule F (MSP.V4 F)}
    (hsurj : ∀ v ∈ MSP.perp p, ∃ u : ↥(Uq M T L), (u : G) ∈ S33.pre h.le (Qv _ μ) ∧ c.vec u = v)
    {γ δ : Vtx (puAmalgam h.le)} (hμγ : (puAmalgam h.le).treeGraph.Adj μ γ)
    (hγδ : (puAmalgam h.le).treeGraph.Adj γ δ) (z₀ : ↥(L ⊔ pCoreOf 2 M))
    (hz : (puAmalgam h.le).ofA ⟨z₀, sup_le h.L_le (pCoreOf_le' M) z₀.2⟩ ∈
      burnsideSp4A_psub h γ δ) :
    φ z₀ ∈ MSP.xPoint p := by
  have h20 := h.hyp20
  have hKM : L ⊔ pCoreOf 2 M ≤ M := sup_le h.L_le (pCoreOf_le' M)
  have hAV : L ⊔ pCoreOf 2 M ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    hKM.trans (le_normalizer_Uq h.le_normalizer)
  have hδM : IsMVtx _ δ := by
    have h1 := (isMVtx_iff_of_adj _ hμγ).mp hc.1
    have h2 := isMVtx_iff_of_adj _ hγδ
    tauto
  have hQμγ : Qv (puAmalgam h.le) μ ≤ Qv _ γ := qv_le_qv _ h20 hc.1 hμγ
  set e : ↥(Uq M T L) →* (puAmalgam h.le).Universal :=
    (puAmalgam h.le).ofA.comp (Subgroup.inclusion (Uq_le h.L_le)) with he
  have hmemA : ∀ u : ↥(Uq M T L), (u : G) ∈ S33.pre h.le (Qv _ μ) ↔ e u ∈ Qv _ μ :=
    fun u => S33.mem_pre_iff h.le (Subgroup.inclusion (Uq_le h.L_le) u)
  have hconj : ∀ u : ↥(Uq M T L), (z₀ : G) * u * (z₀ : G)⁻¹ ∈ Uq M T L := fun u =>
    (Subgroup.mem_normalizer_iff.1 (hAV z₀.2) u).1 u.2
  have hzero : ∀ u : ↥(Uq M T L), e u ∈ Qv _ μ → e u ∈ S34F.flat h δ →
      MSP.mat (φ z₀) *ᵥ c.vec u - c.vec u = 0 := by
    intro u huQ huF
    have hcen := Subgroup.mem_centralizer_iff.mp hz.2 (e u)
      (Subgroup.mem_inf.2 ⟨hQμγ huQ, huF⟩)
    rw [he, MonoidHom.comp_apply, ← map_mul, ← map_mul] at hcen
    have h1 := congrArg Subtype.val ((puAmalgam h.le).ofA_injective hcen)
    simp only [Subgroup.coe_mul, Subgroup.coe_inclusion] at h1
    rw [← c.vec_commutator z₀ u (hconj u), c.vec_eq_zero_iff]
    have h2 : (z₀ : G) * u * (z₀ : G)⁻¹ * (u : G)⁻¹ = 1 := by
      rw [← h1, mul_inv_cancel_right, mul_inv_cancel]
    show (z₀ : G) * u * (z₀ : G)⁻¹ * (u : G)⁻¹ ∈ _
    rw [h2]
    exact one_mem _
  have hpair : ∀ u u' : ↥(Uq M T L), e u ∈ Qv _ μ → e u' ∈ Qv _ μ → e u ∉ S34F.flat h δ →
      e u' ∉ S34F.flat h δ →
        (MSP.mat (φ z₀) *ᵥ c.vec u - c.vec u) + (MSP.mat (φ z₀) *ᵥ c.vec u' - c.vec u') = 0 := by
    intro u u' huQ hu'Q huF hu'F
    have hsq : ∀ w : ↥(Uq M T L), e w ^ 2 = 1 := fun w => by
      rw [← map_pow]
      have : w ^ 2 = 1 := Subtype.ext (by simpa using Sp4L.uq_sq h w.2)
      rw [this, map_one]
    have hprod := burnsideSp4H_mul_mem_flat h hU hδM hγδ.symm (hQμγ huQ) (hQμγ hu'Q)
      (hsq u) (hsq u') huF hu'F
    rw [← map_mul] at hprod
    have h1 := hzero (u * u') (by rw [map_mul]; exact mul_mem huQ hu'Q) hprod
    rw [c.vec_mul, Matrix.mulVec_add] at h1
    rw [← h1]
    abel
  refine MSP.mem_fixer.2 fun v hv => ?_
  have hv0 : MSP.mat (φ z₀) *ᵥ v - v = 0 := by
    refine burnsideSp4H_eq_zero_of_trichotomy hF fun l => ?_
    obtain ⟨u, huA, rfl⟩ := hsurj v hv
    obtain ⟨u', hu'A, hu'⟩ := hsurj (l • c.vec u) (Submodule.smul_mem _ l hv)
    have hl : l • (MSP.mat (φ z₀) *ᵥ c.vec u - c.vec u) =
        MSP.mat (φ z₀) *ᵥ c.vec u' - c.vec u' := by
      rw [hu', Matrix.mulVec_smul, smul_sub]
    rw [hl]
    rw [hmemA] at huA hu'A
    by_cases huF : e u ∈ S34F.flat h δ
    · exact Or.inl (hzero u huA huF)
    by_cases hu'F : e u' ∈ S34F.flat h δ
    · exact Or.inr (Or.inl (hzero u' hu'A hu'F))
    exact Or.inr (Or.inr (hpair u u' huA hu'A huF hu'F))
  exact sub_eq_zero.mp hv0

theorem burnsideSp4H_map_pre_zstar_le_xPoint (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {μ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo (puAmalgam h.le) (baseA _) μ 1 = baseB _)
    {F : Type} [Field F] [Fintype F] (hF : ∃ l : F, l ≠ 0 ∧ l ≠ -1)
    {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F)}
    (hφ : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L)
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) φ false 1)
    {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p)
    (hpe : ((S33.pre h.le (ZM _ μ)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ = MSP.xPoint p)
    (hrel : (Qv _ μ).relIndex (ZM (puAmalgam h.le) (baseA _)) = Fintype.card F) :
    ((S33.pre h.le (burnsideSp4A_zstar h μ)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ ≤
      MSP.xPoint p := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hφ
  have hKM : L ⊔ pCoreOf 2 M ≤ M := sup_le h.L_le (pCoreOf_le' M)
  have hμK := pre_zm_le_flat_sp h hU hc hμβ
  have hsurj := burnsideSp4H_exists_vec_eq h hc c hp hpe hrel
  obtain ⟨-, -, -, -, hEim⟩ := S33.pre_zm_props h hc
  set Kp : Subgroup G := ((MSP.xPoint p).comap φ).map (L ⊔ pCoreOf 2 M).subtype with hKp
  have hZK : burnsideSp4A_zstar h μ ≤ imM h.le (L ⊔ pCoreOf 2 M) := by
    have := burnsideSp4H_zstar_le_flat h hU hb hc hμβ
    rwa [S34F.flat, puTrans_baseA h.le (S34F.flat_subgroupOf_normal h)] at this
  have hle : burnsideSp4A_zstar h μ ≤ imM h.le Kp := by
    refine sup_le ?_ (iSup₂_le fun γ hγ => iSup₂_le fun δ hδ => ?_)
    · rw [← hEim]
      refine imM_mono h.le fun x hx => ?_
      refine ⟨⟨x, hμK hx⟩, ?_, rfl⟩
      show φ ⟨x, hμK hx⟩ ∈ MSP.xPoint p
      rw [← hpe]
      exact ⟨⟨x, hμK hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    · intro z hzP
      obtain ⟨m, hm, rfl⟩ := hZK (burnsideSp4A_psub_le_zstar h hγ hδ hzP)
      have hmK : (m : G) ∈ L ⊔ pCoreOf 2 M := Subgroup.mem_subgroupOf.1 hm
      have hz' : (puAmalgam h.le).ofA ⟨((⟨m, hmK⟩ : ↥(L ⊔ pCoreOf 2 M)) : G),
          hKM (⟨m, hmK⟩ : ↥(L ⊔ pCoreOf 2 M)).2⟩ ∈ burnsideSp4A_psub h γ δ := hzP
      have hφm := burnsideSp4H_mem_xPoint_of_psub h hU hc hF c hsurj hγ hδ ⟨m, hmK⟩ hz'
      exact ⟨m, Subgroup.mem_subgroupOf.2 ⟨⟨m, hmK⟩, hφm, rfl⟩, rfl⟩
  have hWK : S33.pre h.le (burnsideSp4A_zstar h μ) ≤ Kp := S33.pre_le_of_le_imM h hle
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨y', hy', hyy'⟩ := hWK (Subgroup.mem_subgroupOf.1 hy)
  have : y' = y := Subtype.ext hyy'
  rw [← this]
  exact hy'

end CFSG.Quasithin.MS93.S4L
