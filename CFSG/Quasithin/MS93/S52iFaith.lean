module

public import CFSG.Quasithin.MS93.S5Q2Par
public import CFSG.Quasithin.MS93.S5AKer
public import CFSG.Quasithin.MS93.S38ETypes
public import CFSG.Quasithin.MS93.MSPLevi
public import CFSG.Quasithin.MS93.S36SpEType
public import CFSG.Quasithin.MS93.S38ESecMod

public section

namespace CFSG.Quasithin.MS93.S52i

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Sp4

variable {F : Type} [Field F]

theorem center_sp4_eq_bot [CharP F 2] : Subgroup.center (MSP.Sp4 F) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  refine MSP.ext_mulVec fun v => ?_
  rw [MSP.mat_one, Matrix.one_mulVec]
  by_cases hv : v = 0
  · rw [hv, Matrix.mulVec_zero]
  · exact MSP.mulVec_eq_of_commute_transv hv (Subgroup.mem_center_iff.1 hz (MSP.transv v 1)).symm

theorem isSimpleGroup_sp4 [CharP F 2] (hF : 4 ≤ Nat.card F) : IsSimpleGroup (MSP.Sp4 F) := by
  have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F (by norm_num)
    (Or.inl (Or.inr hF))
  have hs : IsSimpleGroup (↥(StatedSp 2 F) ⧸ Subgroup.center ↥(StatedSp 2 F)) := hq.2.1
  have e : (↥(StatedSp 2 F) ⧸ Subgroup.center ↥(StatedSp 2 F)) ≃* MSP.Sp4 F :=
    (QuotientGroup.quotientMulEquivOfEq center_sp4_eq_bot).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem eq_bot_of_normal_of_not_le_commutator [Finite F] (c : ZMod 2 ≃+* F)
    {N : Subgroup (MSP.Sp4 F)} (hN : N.Normal) (hD : ¬ commutator (MSP.Sp4 F) ≤ N) : N = ⊥ := by
  have : CharP F 2 := MSP.charP_of_ringEquiv c
  set θ := B5FinSp.theta c
  set N' := N.comap θ.toMonoidHom with hN'
  have hN'n : N'.Normal := hN.comap _
  have hsimp : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hN'' : (N'.subgroupOf (alternatingGroup (Fin 6))).Normal := Subgroup.Normal.subgroupOf hN'n _
  have hinf : ∀ g ∈ N, g ∈ commutator (MSP.Sp4 F) → g = 1 := by
    intro g hgN hgD
    obtain ⟨σ, rfl⟩ := θ.surjective g
    rw [MSP.mem_commutator_iff_sign c, MulEquiv.symm_apply_apply] at hgD
    have hσA : σ ∈ alternatingGroup (Fin 6) := Equiv.Perm.mem_alternatingGroup.2 hgD
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (N'.subgroupOf (alternatingGroup (Fin 6))) with hbot | htop
    · have h1 : (⟨σ, hσA⟩ : alternatingGroup (Fin 6)) ∈ N'.subgroupOf (alternatingGroup (Fin 6)) :=
        hgN
      rw [hbot] at h1
      have h2 : σ = 1 := congrArg Subtype.val ((Subgroup.mem_bot).1 h1)
      rw [h2, map_one]
    · exfalso
      apply hD
      intro g' hg'
      obtain ⟨τ, rfl⟩ := θ.surjective g'
      rw [MSP.mem_commutator_iff_sign c, MulEquiv.symm_apply_apply] at hg'
      have hτA : τ ∈ alternatingGroup (Fin 6) := Equiv.Perm.mem_alternatingGroup.2 hg'
      have h1 : (⟨τ, hτA⟩ : alternatingGroup (Fin 6)) ∈
          N'.subgroupOf (alternatingGroup (Fin 6)) := by
        rw [htop]
        exact Subgroup.mem_top _
      exact h1
  rw [eq_bot_iff]
  intro n hn
  rw [← center_sp4_eq_bot (F := F), Subgroup.mem_center_iff]
  intro g
  have hc : ⁅n, g⁆ ∈ N := by
    have e : ⁅n, g⁆ = n * (g * n⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact N.mul_mem hn (hN.conj_mem n⁻¹ (N.inv_mem hn) g)
  have hc1 := hinf _ hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top n)
    (Subgroup.mem_top g))
  exact (commutatorElement_eq_one_iff_mul_comm.1 hc1).symm

end Sp4

section Data

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem ker_le_ker_of_isIrrRep (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {S : Type} [CommGroup S] {ρ : ↥M →* MulAut S} (hρ : S38E.IsIrrRep L ρ) : ρ.ker ≤ a.ker := by
  have : CharP F 2 := S5.IsSp4Data.charP hd
  set K : Subgroup G := ρ.ker.map M.subtype with hK
  have hKM : K.subgroupOf M = ρ.ker :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective ρ.ker
  have hQK : pCoreOf 2 M ≤ K := fun q hq =>
    ⟨⟨q, pCoreOf_le' M hq⟩, MonoidHom.mem_ker.2 (hρ.pCore _ hq), rfl⟩
  set N := ρ.ker.map a with hNdef
  have hNn : N.Normal := (MonoidHom.normal_ker ρ).map a hd.2.2.1
  have hNim : S5.imSp a K = N := by rw [S5.imSp, hKM]
  have hLN : ¬ S5.imSp a L ≤ N := by
    intro hle
    have hLK := S5.IsSp4Data.L_le_of_imSp_le hd h hQK (hle.trans hNim.ge)
    obtain ⟨l, hlL, hl1⟩ := hρ.ne
    obtain ⟨m, hm, hml⟩ := hLK hlL
    apply hl1
    have : m = l := Subtype.ext hml
    rw [← this]
    exact hm
  have hNbot : N = ⊥ := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by have := hd.1; omega
      have hF2 : Nat.card F = 2 := by rw [S5.IsSp4Data.nat_card_eq hd, pow_one]
      obtain ⟨c⟩ := MSP.nonempty_ringEquiv_of_card_two hF2
      refine eq_bot_of_normal_of_not_le_commutator c hNn fun hD => hLN ?_
      rw [S5.imSp, S5Q2.map_L_eq_commutator h hd]
      exact hD
    · have hF4 : 4 ≤ Nat.card F := by
        rw [S5.IsSp4Data.nat_card_eq hd]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      have := isSimpleGroup_sp4 (F := F) hF4
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
      · exact hb
      · exfalso
        exact hLN (by rw [ht]; exact le_top)
  intro m hm
  have : a m ∈ N := ⟨m, hm, rfl⟩
  rw [hNbot] at this
  exact this

theorem card_imSp_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {S : Type} [CommGroup S] {ρ : ↥M →* MulAut S} (hρ : S38E.IsIrrRep L ρ) (E : Subgroup G) :
    Nat.card (S5.imSp a E) ≤ Nat.card ((E.subgroupOf M).map ρ) := by
  rw [S5.imSp, S38E.card_map_eq_relIndex_ker, S38E.card_map_eq_relIndex_ker]
  refine Subgroup.relIndex_le_of_le_left (ker_le_ker_of_isIrrRep h hd hρ) ?_
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

theorem card_lstar_of_sp4Data (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) :
    (k = 1 ∧ Nat.card (S32.Lstar L) = 360) ∨
      (2 ≤ k ∧ Nat.card (S32.Lstar L) = CFSG.Open.ordBC 2 (2 ^ k)) := by
  have : CharP F 2 := S5.IsSp4Data.charP hd
  set f : ↥L →* ↥(StatedSp 2 F) := a.comp (Subgroup.inclusion h.L_le) with hf
  have hO : CFSG.pCore 2 ↥L ≤ f.ker := by
    intro y hy
    have hyM : (y : G) ∈ pCoreOf 2 M :=
      pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer (mem_pCoreOf_of_mem_pCore_two hy)
    obtain ⟨m, hm, hmy⟩ := S5.IsSp4Data.pCoreOf_le_kerG hd h hyM
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply]
    have : Subgroup.inclusion h.L_le y = m := Subtype.ext hmy.symm
    rw [this]
    exact hm
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by have := hd.1; omega
    refine Or.inl ⟨rfl, ?_⟩
    have hF2 : Nat.card F = 2 := by rw [S5.IsSp4Data.nat_card_eq hd, pow_one]
    obtain ⟨c⟩ := MSP.nonempty_ringEquiv_of_card_two hF2
    have hrange : f.range = commutator (MSP.Sp4 F) := by
      rw [← S5Q2.map_L_eq_commutator h hd, hf, MonoidHom.range_comp]
      congr 1
      ext m
      constructor
      · rintro ⟨l, rfl⟩
        exact Subgroup.mem_subgroupOf.2 l.2
      · intro hm
        exact ⟨⟨m, Subgroup.mem_subgroupOf.1 hm⟩, rfl⟩
    set f' : ↥L →* ↥(commutator (MSP.Sp4 F)) := f.codRestrict _ (fun l => hrange ▸ ⟨l, rfl⟩)
    have hf's : Function.Surjective f' := by
      rintro ⟨g, hg⟩
      rw [← hrange] at hg
      obtain ⟨l, rfl⟩ := hg
      exact ⟨l, rfl⟩
    have hO' : CFSG.pCore 2 ↥L ≤ f'.ker := fun y hy => by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact hO hy
    set θ := B5FinSp.theta c
    have hmap : (alternatingGroup (Fin 6)).map θ.toMonoidHom = commutator (MSP.Sp4 F) := by
      ext g
      constructor
      · rintro ⟨σ, hσ, rfl⟩
        rw [MSP.mem_commutator_iff_sign c]
        show Equiv.Perm.sign (θ.symm (θ σ)) = 1
        rw [MulEquiv.symm_apply_apply]
        exact Equiv.Perm.mem_alternatingGroup.1 hσ
      · intro hg
        rw [MSP.mem_commutator_iff_sign c] at hg
        exact ⟨θ.symm g, Equiv.Perm.mem_alternatingGroup.2 hg, θ.apply_symm_apply g⟩
    have e : ↥(alternatingGroup (Fin 6)) ≃* ↥(commutator (MSP.Sp4 F)) :=
      (θ.subgroupMap (alternatingGroup (Fin 6))).trans (MulEquiv.subgroupCongr hmap)
    have hQ : ∃ x : ↥(commutator (MSP.Sp4 F)), x ≠ 1 := by
      obtain ⟨σ, hσ⟩ : ∃ σ : ↥(alternatingGroup (Fin 6)), σ ≠ 1 :=
        ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
          fun h1 => absurd (congrArg (fun τ : alternatingGroup (Fin 6) =>
            (τ : Equiv.Perm (Fin 6)) 0) h1) (by decide)⟩
      exact ⟨e σ, fun h1 => hσ (e.injective (h1.trans (map_one e).symm))⟩
    rw [S38E.card_lstar_of_surjective h f' hf's hO' hQ]
    exact card_quot_of_equiv_alt6 e
  · refine Or.inr ⟨hk, ?_⟩
    have : Finite F := Finite.of_fintype F
    have hα : Function.Surjective f := by
      intro y
      have hy : y ∈ (L.subgroupOf M).map a := (S5B.map_L_eq_top h hd hk).symm ▸ Subgroup.mem_top y
      obtain ⟨m, hm, rfl⟩ := hy
      exact ⟨⟨m, Subgroup.mem_subgroupOf.1 hm⟩, rfl⟩
    exact S36E.card_lstar_of_sp4 h (S5.IsSp4Data.nat_card_eq hd) hk hα hO

end Data

end CFSG.Quasithin.MS93.S52i
