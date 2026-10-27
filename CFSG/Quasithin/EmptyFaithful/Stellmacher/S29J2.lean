module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S29Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S29Count
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.ZvCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53Push

namespace F53.Stellmacher.S29

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α a₂ a₃ β : Geo H M}

namespace S29Step7

theorem thompsonJ_eq_of_le {R T : Subgroup G} (hJ : thompsonJ T ≤ R) (hRT : R ≤ T) :
    thompsonJ R = thompsonJ T := by
  apply le_antisymm
  · refine iSup₂_le fun A hA => le_thompsonJ_of_isMax ?_
    exact (isMaxElemAbelian_iff_of_thompsonJ_le hJ hRT).mp hA
  · refine iSup₂_le fun A hA => le_thompsonJ_of_isMax ?_
    exact (isMaxElemAbelian_iff_of_thompsonJ_le hJ hRT).mpr hA

theorem normalizes_of_le_core {X T : Subgroup G} (hT : IsSylowTwoOf T X)
    (hJ : thompsonJ T ≤ pCoreOf 2 X) :
    X ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧
      X ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJ T) : Set G) := by
  have hJeq := thompsonJ_eq_of_le hJ (pCoreOf_le_of_sylow hT)
  refine ⟨?_, ?_⟩
  · rw [← hJeq]; exact le_normalizer_thompsonJ_core X
  · rw [← hJeq]; exact le_normalizer_omegaOneCenter_core X

theorem oTwoRes_eq_pResidualOf (X : Subgroup G) : oTwoRes X = pResidualOf 2 X := by
  rw [← oTwoUpper_eq_pResidualOf]
  unfold oTwoRes oTwoUpper
  congr 1
  ext x
  constructor
  · rintro ⟨hx, m, hm, hxm⟩
    exact ⟨hx, Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hxm)⟩
  · rintro ⟨hx, ho⟩
    exact ⟨hx, orderOf x, ho, pow_orderOf_eq_one x⟩

omit [Finite G] in
theorem mul_mul_inv_mem_conjSub {g x : G} {Y : Subgroup G} (hx : x ∈ Y) :
    g * x * g⁻¹ ∈ conjSub g Y := by
  rw [mem_conjSub]
  simpa [mul_assoc] using hx

theorem inf_le_Qv (hs : Sit29 H M S α a₂ a₃ β) (hR : Zv α ⊓ Zv a₂ = Zv β)
    (hcard : 4 ≤ Nat.card ↥(Zv α ⊓ Subgroup.centralizer
      (thompsonJ (stab α ⊓ stab β) : Set G)))
    (hsubW : Zv α ⊓ Subgroup.centralizer (thompsonJ (stab α ⊓ stab β) : Set G) ≤
      omegaOneCenterOf (thompsonJ (stab α ⊓ stab β)))
    (hcomm : ∀ k ∈ pResidualOf 2 (stab α) ⊓ (stab α ⊓ stab β),
      ∀ w ∈ omegaOneCenterOf (thompsonJ (stab α ⊓ stab β)),
        k * w * k⁻¹ * w⁻¹ ∈ Zv α ⊓ Subgroup.centralizer ((stab α ⊓ stab β : Subgroup G) : Set G))
    (hNW : stab β ≤ Subgroup.normalizer
      (omegaOneCenterOf (thompsonJ (stab α ⊓ stab β)) : Set G)) :
    pResidualOf 2 (stab α) ⊓ (stab α ⊓ stab β) ≤ Qv β := by
  rintro k ⟨hkL, hkα, hkβ⟩
  by_contra hkQ
  obtain ⟨hc2, hc3⟩ := hs.Zv_conj_swap hkα hkβ hkQ
  have hedge := EmptyFaithful.Stellmacher.OrdinaryProofs.Zv_inf_centralizer_edge_eq
    hs.amalg hs.adj hs.hz
  obtain ⟨w', hw'C, hw'Z⟩ : ∃ w' ∈ Zv α ⊓ Subgroup.centralizer
      (thompsonJ (stab α ⊓ stab β) : Set G), w' ∉ Zv β := by
    by_contra hall
    push Not at hall
    have hle : Zv α ⊓ Subgroup.centralizer (thompsonJ (stab α ⊓ stab β) : Set G) ≤ Zv β :=
      fun x hx => hall x hx
    have h2 := Subgroup.card_le_of_le hle
    rw [hs.card_Zv_right] at h2
    omega
  obtain ⟨g, hgβ, hgα⟩ := stab_transitive_on_nbrs hs.n₁ hs.n₂
  set w : G := g * w' * g⁻¹ with hw
  have hwW : w ∈ omegaOneCenterOf (thompsonJ (stab α ⊓ stab β)) :=
    (Subgroup.mem_normalizer_iff.mp (hNW hgβ) w').mp (hsubW hw'C)
  have hwZ2 : w ∈ Zv a₂ := by
    have h1 : w ∈ conjSub (g : G) (Zv α) := mul_mul_inv_mem_conjSub hw'C.1
    rwa [Sit29.Zv_conj g α, hgα] at h1
  have hwβ : w ∉ Zv β := fun h =>
    hw'Z ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hs.amalg β hgβ) w').mpr h)
  have hcβ : k * w * k⁻¹ * w⁻¹ ∈ Zv β := by
    rw [← hedge]; exact hcomm k ⟨hkL, hkα, hkβ⟩ w hwW
  have hk3 : k * w * k⁻¹ ∈ Zv a₃ := by
    rw [← hc2]; exact mul_mul_inv_mem_conjSub hwZ2
  have hk2 : k * w * k⁻¹ ∈ Zv a₂ := by
    have h1 : k * w * k⁻¹ = (k * w * k⁻¹ * w⁻¹) * w := by group
    rw [h1]
    exact Subgroup.mul_mem _ ((hs.Zv_right_le_R hcβ).2) hwZ2
  have hkR : k * w * k⁻¹ ∈ Zv β := by
    rw [← hR, hs.R_eq₂]
    exact ⟨hk2, hk3⟩
  apply hwβ
  have h1 : w = (k * w * k⁻¹ * w⁻¹)⁻¹ * (k * w * k⁻¹) := by group
  rw [h1]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcβ) hkR

end S29Step7

open S29Step7 in
theorem step7 (hs : Sit29 H M S α a₂ a₃ β) (hR : Zv α ⊓ Zv a₂ = Zv β)
    (hJ : thompsonJ (stab α ⊓ stab β) ≤ Qv β) : False := by
  have hβn : β ∈ nbrs α := hs.adj
  have hT : IsSylowTwoOf (stab α ⊓ stab β) (stab α) := sylow_stab_inf_left hs.amalg hβn
  have hTβ : IsSylowTwoOf (stab α ⊓ stab β) (stab β) := sylow_stab_inf_right hs.amalg hβn
  have hQT : Qv β ≤ stab α ⊓ stab β := by
    rw [inf_comm]; exact Qv_le_inf hs.amalg hs.n₁
  have hJne : thompsonJ (stab α ⊓ stab β) ≠ ⊥ :=
    CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hT.2.1 (inf_stab_ne_bot hs.amalg hβn)
  obtain ⟨hNJβ, hNWβ⟩ := normalizes_of_le_core hTβ hJ
  have hJα : ¬ thompsonJ (stab α ⊓ stab β) ≤ pCoreOf 2 (stab α) := fun h =>
    hJne (eq_bot_of_normalizes_both hs.amalg hs.adj (thompsonJ_le_self _)
      (normalizes_of_le_core hT h).1 hNJβ)
  have hC : Zv α ⊓ Subgroup.centralizer (pResidualOf 2 (stab α) : Set G) = ⊥ := by
    have h := EmptyFaithful.Stellmacher.OrdinaryProofs.Zv_inf_centralizer_oTwoRes_eq_bot
      hs.amalg hs.adj hs.hz
    rwa [oTwoRes_eq_pResidualOf] at h
  have hZX : Zv α ≤ stab α := (Zv_le_Qv hs.amalg α).trans (pCoreOf_le 2 _)
  obtain ⟨hcard, hsubW, hcomm⟩ :=
    step7_counting hT (quot_stab_five hs.amalg hs.vα) hs.hmod hZX hC hJα
  have h7g := inf_le_Qv hs hR hcard hsubW hcomm hNWβ
  set L : Subgroup G := pResidualOf 2 (stab α) with hL
  set U : Subgroup G := L ⊔ Qv β with hU
  have hQU : Qv β ≤ U := le_sup_right
  have hUs : U ≤ stab α :=
    sup_le (pResidualOf_le_self _) (Qv_le_stab_of_mem_nbrs hs.amalg hs.n₁)
  have hsyl : IsSylowTwoOf (Qv β ⊓ U) U := by
    rw [inf_eq_left.mpr hQU]
    refine ⟨hQU, pCoreOf_isPGroup 2 _, ?_⟩
    have hn : Qv β ≤ Subgroup.normalizer (L : Set G) :=
      (Qv_le_stab_of_mem_nbrs hs.amalg hs.n₁).trans (le_normalizer_pResidualOf _)
    have h1 := relIndex_sup_eq_relIndex_inf hn
    have h2 : L ⊓ Qv β = L ⊓ (stab α ⊓ stab β) :=
      le_antisymm (inf_le_inf_left _ hQT) (le_inf inf_le_left (h7g))
    rw [h2] at h1
    have h3 : ((Qv β).subgroupOf U).index = (L ⊓ (stab α ⊓ stab β)).relIndex L := h1
    rw [h3]
    exact relIndex_residual_inf_sylow hT
  have hZU : Zv α ≤ U := hs.Zv_le_Qv_right.trans hQU
  have hzle : Zv β ≤ pCoreOf 2 U := by
    have hp : IsPGroup 2 (Zv α) := fun g =>
      ⟨1, Subtype.ext (by simpa using (isElemAbelian_Zv hs.amalg α).2 g.1 g.2)⟩
    have hn : U ≤ Subgroup.normalizer (Zv α : Set G) :=
      hUs.trans (stab_le_normalizer_Zv hs.amalg α)
    exact hs.Zv_right_le.trans (le_pCoreOf_of_le_normalizer hZU hn hp)
  have hgen : U ⊔ (stab α ⊓ stab β) = stab α :=
    le_antisymm (sup_le hUs inf_le_left)
      ((pResidualOf_sup_eq_of_sylow hT).symm.le.trans (sup_le_sup_right le_sup_left _))
  have hsit : F53.SitSigma α β U := ⟨hs.adj, hUs, hsyl, hzle, hgen⟩
  have hZα : Zv α ≤ centerOf (stab α) := hs.h26 hs.b1 α β U hsit hQU
  have hbot := centerOf_eq_bot_of_Zv_central hs.amalg hs.n₁ hs.hz
  exact Zv_ne_bot hs.amalg α (le_bot_iff.mp (hbot ▸ hZα))

end F53.Stellmacher.S29

end CFSG.Quasithin
