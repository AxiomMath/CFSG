module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJLink
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace CommonJ

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {R : Type} [Group R] {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {γ : ↥Bs →* R}

theorem ggCommonJ_of_nativeRow (hcfg : GGConfig p B Bs x L D J) (hB : B = Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hR : Subgroup.center R = ⊥)
    (hγ : GGGammaHatSpec θ γ) {m : ℕ} (hm : 3 ≤ m)
    (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))) (i0 : Fin (m + 1))
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (m + 1) p i0)
    {H : Type} [Group H] (e : R ≃* H) {SD SS : LargeEvenLabel → Prop}
    (hrow : GGSecFiveBNativeRow H p m SD SS) :
    (GGSecFiveBCoordDense eta i0 D ∧ ∃ labJ, SD labJ ∧ LargeEvenInLambda2 labJ ∧
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧
        (labJ = ⟨.twA, 3, 1⟩ → Subgroup.center ↥L = ⊥ → LargeEvenSmall J)) ∨
      (GGSecFiveBCoordSparse eta i0 D ∧ ∃ labJ, SS labJ ∧ LargeEvenInLambda2 labJ ∧
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) := by
  obtain ⟨hp, hBs_ea, hxBs, -, -⟩ := hcfg.tableB_facts
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  obtain ⟨hpre, -⟩ := hcfg.2.2
  have hDleB : D ≤ B := hpre.1
  have hDleBs : D ≤ Bs := hB ▸ hDleB
  have hD_ea : IsElemAbelian p D := hpre.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  let xb : ↥Bs := ⟨x, hxBs⟩
  have hxeta_off : ∀ j, j ≠ i0 → eta xb j = 1 := fun j hj =>
    eta_x_eq_one hcfg hB eta i0 hA xb rfl hj
  have hxeta0 : eta xb i0 ≠ 1 := by
    intro h0
    have hfun : eta xb = 1 := by
      funext j
      by_cases hj : j = i0
      · subst hj
        simpa using h0
      · simpa using hxeta_off j hj
    have hxb1 : xb = 1 := eta.injective (by simpa using hfun)
    have : (xb : G) = 1 := by rw [hxb1]; rfl
    exact hx1 this
  let f : ↥Bs →* Multiplicative (ZMod p) :=
    (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) i0).comp eta.toMonoidHom
  let D' : Subgroup ↥Bs := D.subgroupOf Bs
  let g : ↥D' →* Multiplicative (ZMod p) := f.comp D'.subtype
  have hxD' : xb ∈ D' := by
    rw [Subgroup.mem_subgroupOf]
    exact hxD
  let x' : ↥D' := ⟨xb, hxD'⟩
  have hgx : g x' = eta xb i0 := rfl
  have hx'ker : x' ∉ g.ker := by
    rw [MonoidHom.mem_ker, hgx]
    exact hxeta0
  have hrangeZ : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hD'card : Nat.card ↥D' = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleBs).toEquiv]
    exact hDcard
  have hker_card : Nat.card g.ker = p := by
    have hcard := Subgroup.card_ker_mul_card_range g
    rw [hD'card] at hcard
    have hdvd : Nat.card g.range ∣ p := by
      have h := Subgroup.card_subgroup_dvd_card g.range
      rwa [hrangeZ] at h
    have hne : g.range ≠ ⊥ := by
      intro hbot
      have hmem : g x' ∈ g.range := MonoidHom.mem_range.mpr ⟨x', rfl⟩
      have h1 : g x' = 1 := by
        rw [hbot] at hmem
        simpa using hmem
      exact hx'ker (MonoidHom.mem_ker.mpr h1)
    have hne1 : Nat.card g.range ≠ 1 := fun h1 =>
      hne (Subgroup.eq_bot_of_card_eq (H := g.range) h1)
    have hrange : Nat.card g.range = p := ((hp.dvd_iff_eq hne1).1 hdvd).symm
    rw [hrange, pow_two] at hcard
    exact Nat.eq_of_mul_eq_mul_right hp.pos hcard
  have hone : 1 < Nat.card g.ker := by rw [hker_card]; exact hp.one_lt
  have hne_ker : g.ker ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot (H := g.ker)).mp hone
  obtain ⟨z0, hz0ne⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := g.ker)).mp hne_ker
  let z0' : ↥D' := (z0 : ↥D')
  let z0b : ↥Bs := (z0' : ↥Bs)
  have hz0'ne : z0' ≠ 1 := fun h => hz0ne (Subtype.ext h)
  have hz0bne : z0b ≠ 1 := fun h => hz0'ne (Subtype.ext h)
  have hz0eta : eta z0b i0 = 1 := by
    have h1 : g z0' = 1 := MonoidHom.mem_ker.mp z0.2
    simpa [g, f, z0', z0b] using h1
  have hz0'ker : z0' ∈ g.ker := z0.2
  have hz0bD : (z0b : G) ∈ D := by
    simpa [z0b, z0'] using Subgroup.mem_subgroupOf.mp z0'.2
  have hz0order : orderOf z0' = p := by
    have hdvd : orderOf z0' ∣ p := by
      rw [← hker_card]
      exact Subgroup.orderOf_dvd_natCard g.ker hz0'ker
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h (by rw [orderOf_eq_one_iff]; exact hz0'ne)
    · exact h
  have hzp_eq : Subgroup.zpowers z0' = g.ker := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz0'ker) ?_
    rw [Nat.card_zpowers, hz0order, hker_card]
  have hxbpow : xb ^ p = 1 := by
    apply Subtype.ext
    simpa using hD_ea.2 x hxD
  have hz0pow : z0b ^ p = 1 := by
    have h1 : z0' ^ p = 1 := by simpa [hz0order] using pow_orderOf_eq_one z0'
    have := congrArg (fun w : ↥D' => (w : ↥Bs)) h1
    simpa [z0', z0b] using this
  have hz0bx : (z0b : G) ∉ Subgroup.zpowers x := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : xb ^ k = z0b := by
      apply Subtype.ext
      simpa using hk
    have hxk : (eta xb i0) ^ k = 1 := by
      have h1 : (eta xb) ^ k = eta z0b := by
        rw [← map_zpow, hk']
      have h2 := congrFun h1 i0
      simpa [hz0eta] using h2
    have hadvd : orderOf (eta xb i0) ∣ p := by
      simpa [hrangeZ] using orderOf_dvd_natCard (eta xb i0)
    have hane : eta xb i0 ≠ 1 := hxeta0
    have haorder : orderOf (eta xb i0) = p := by
      rcases hp.eq_one_or_self_of_dvd _ hadvd with h | h
      · exact absurd h (by rw [orderOf_eq_one_iff]; exact hane)
      · exact h
    have hpdvdk : (p : ℤ) ∣ k := by
      rw [← haorder]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hxk
    obtain ⟨d, hd⟩ := hpdvdk
    have hxbpowz : xb ^ (p : ℤ) = 1 := by
      rw [zpow_natCast]
      exact hxbpow
    have hxpow : xb ^ k = 1 := by
      rw [hd, zpow_mul, hxbpowz, one_zpow]
    exact hz0bne (hk'.symm.trans hxpow)
  let T : Subgroup H := γ.range.map e.toMonoidHom
  have hT_ea : IsElemAbelian p T := by
    have htop : IsElemAbelian p (⊤ : Subgroup ↥Bs) := by
      simpa using hBs_ea.subgroupOf Bs
    have hγ_ea : IsElemAbelian p γ.range := by
      simpa [MonoidHom.range_eq_map] using htop.map γ
    simpa [T] using hγ_ea.map e.toMonoidHom
  have hT_card : Nat.card T = p ^ m := by
    have hγcard := card_range_gammaHat hcfg hB hBsN hR hγ (n := m + 1) eta
    change Nat.card ↥(γ.range.map e.toMonoidHom) = p ^ m
    rw [Subgroup.card_map_of_injective e.injective]
    simpa using hγcard
  set Jbar : Subgroup R := (J.subgroupOf L).map (ggQuotHom θ) with hJbar
  set J' : Subgroup H := Jbar.map e.toMonoidHom with hJ'
  have hcardJ : Nat.card ↥(γ.range ⊓ Subgroup.centralizer (Jbar : Set R)) = p := by
    simpa [hJbar] using card_range_inf_centralizer_J hcfg hB hBsN hR hγ
  have hcompR : CFSG.Assembly.IsComponentOf Jbar
      (Subgroup.centralizer ({γ z0b} : Set R)) := by
    simpa [hJbar] using isComponentOf_map_J hcfg hB hBsN hR hγ hz0bD hz0bx
  have hcompOpen : CFSG.Open.IsComponentOf J'
      (Subgroup.centralizer ({e (γ z0b)} : Set H)) := by
    have hcompRopen : CFSG.Open.IsComponentOf Jbar
        (Subgroup.centralizer ({γ z0b} : Set R)) :=
      CFSG.Assembly.isComponentOf_iff_open.mp hcompR
    have h1 := isComponentOf_map_mulEquiv e hcompRopen
    rw [← hJ'] at h1
    rw [CFSG.Walter.map_centralizer_singleton_mulEquiv] at h1
    exact h1
  let t : ↥T :=
    ⟨e (γ z0b), Subgroup.mem_map.mpr
      ⟨γ z0b, MonoidHom.mem_range.mpr ⟨z0b, rfl⟩, rfl⟩⟩
  have ht : (t : H) = e (γ z0b) := rfl
  have hcomp : CFSG.Assembly.IsComponentOf J'
      (Subgroup.centralizer ({(t : H)} : Set H)) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr (by simpa [ht] using hcompOpen)
  have hcardT : Nat.card ↥(T ⊓ Subgroup.centralizer (J' : Set H)) = p := by
    have hmapinf : (γ.range ⊓ Subgroup.centralizer (Jbar : Set R)).map e.toMonoidHom
        = T ⊓ Subgroup.centralizer (J' : Set H) := by
      rw [Subgroup.map_inf _ _ _ e.injective]
      simp only [T]
      rw [CFSG.Walter.map_centralizer_mulEquiv]
      congr 1
    rw [← hmapinf, Subgroup.card_map_of_injective e.injective, hcardJ]
  obtain ⟨Θ, hΘ, hAt⟩ := hrow T hT_ea hT_card
  have hzpow : ∀ z : ↥Bs, (z : G) ∈ D → z ≠ 1 → eta z i0 = 1 →
      ∃ c : ℕ, z = z0b ^ c ∧ ¬ p ∣ c := by
    intro z hzD hz1 hzi0
    have hzD' : z ∈ D' := by
      rw [Subgroup.mem_subgroupOf]
      exact hzD
    let z' : ↥D' := ⟨z, hzD'⟩
    have hz'ker : z' ∈ g.ker := by
      rw [MonoidHom.mem_ker]
      simpa [g, f, z'] using hzi0
    have hz'mem : z' ∈ Subgroup.zpowers z0' := by rw [hzp_eq]; exact hz'ker
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz'mem
    have hk' : z0b ^ k = z := by
      have h := congrArg (fun w : ↥D' => (w : ↥Bs)) hk
      simpa [z0', z0b, z'] using h
    have hmod : z0b ^ k = z0b ^ (k % (p : ℤ)) :=
      zpow_eq_zpow_emod k (by rw [zpow_natCast]; exact hz0pow)
    let c : ℕ := (k % (p : ℤ)).toNat
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.pos.ne'
    have hc : (c : ℤ) = k % (p : ℤ) := by
      simp [c, Int.toNat_of_nonneg (Int.emod_nonneg k hpz)]
    have hcz : z0b ^ c = z := by
      rw [← zpow_natCast, hc, ← hmod, hk']
    refine ⟨c, hcz.symm, ?_⟩
    intro hpc
    obtain ⟨d, hd⟩ := hpc
    have h1 : z0b ^ c = 1 := by
      rw [hd, pow_mul, hz0pow, one_pow]
    rw [hcz] at h1
    exact hz1 h1
  rcases hAt t J' hcomp hcardT with
    ⟨hdense0, lab, hSD, hlab2, hlabQ, hcent⟩ | ⟨hsparse0, lab, hSS, hlab2, hlabQ⟩
  · left
    have hdense0' : GGCoordDense (fun j => eta z0b (i0.succAbove j)) :=
      ((ggCoord_iff_of_signedCoords hcfg hB hBsN hR hγ hm eta i0 hA e hΘ
        z0b t ht).1.mp hdense0)
    have hlabel : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) := by
      have h1 : GGHasLabel lab (↥Jbar ⧸ Subgroup.center ↥Jbar) :=
        ggHasLabel_quotCenter_of_mulEquiv
          (Subgroup.equivMapOfInjective Jbar e.toMonoidHom e.injective).symm hlabQ
      let eJ := Classical.choice (nonempty_centerQuot_J θ hcfg)
      exact ggHasLabel_of_mulEquiv eJ.symm h1
    refine ⟨?_, lab, hSD, hlab2, hlabel, ?_⟩
    · refine (ggSecFiveBCoordDense_iff eta i0 D).2 ?_
      intro z hzD hz1 hzi0
      obtain ⟨c, hzc, hpc⟩ := hzpow z hzD hz1 hzi0
      have hcoord : (fun j => eta z (i0.succAbove j)) =
          (fun j => eta z0b (i0.succAbove j)) ^ c := by
        have h1 : eta z = (eta z0b) ^ c := by rw [hzc, map_pow]
        funext j
        simpa [Pi.pow_apply] using congrFun h1 (i0.succAbove j)
      rw [hcoord]
      exact (ggCoordDense_pow hp hpc).2 hdense0'
    · intro hlabEq hZL
      have hcentJ' : Subgroup.center ↥J' = ⊥ := hcent hlabEq
      have heJ : ↥J ≃* ↥J' := by
        let e1 := Classical.choice (nonempty_J_of_center_eq_bot θ hcfg hZL)
        exact e1.trans (Subgroup.equivMapOfInjective Jbar e.toMonoidHom e.injective)
      have hcentJ : Subgroup.center ↥J = ⊥ := by
        have hmap := Subgroup.map_center_eq heJ
        rw [hcentJ'] at hmap
        exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center ↥J)
          heJ.injective).1 hmap
      have hU : LargeEvenIsU42 (↥J ⧸ Subgroup.center ↥J) := by
        have hlabEq' : GGHasLabel ⟨.twA, 3, 1⟩ (↥J ⧸ Subgroup.center ↥J) :=
          hlabEq ▸ hlabel
        unfold GGHasLabel at hlabEq'
        unfold LargeEvenIsU42
        simp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hlabEq'
        obtain ⟨K, hK, hKf, hKcard, hcont⟩ := hlabEq'
        exact ⟨K, hK, hKf, by simpa using hKcard, hcont⟩
      have hq : ↥J ⧸ Subgroup.center ↥J ≃* ↥J :=
        (QuotientGroup.quotientMulEquivOfEq hcentJ).trans QuotientGroup.quotientBot
      obtain ⟨K, hK, hKf, hKcard, hcont⟩ := hU
      exact Or.inl ⟨K, hK, hKf, hKcard, hcont.map fun φ => hq.symm.trans φ⟩
  · right
    have hsparse0' : GGCoordSparse (fun j => eta z0b (i0.succAbove j)) :=
      ((ggCoord_iff_of_signedCoords hcfg hB hBsN hR hγ hm eta i0 hA e hΘ
        z0b t ht).2.mp hsparse0)
    have hlabel : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) := by
      have h1 : GGHasLabel lab (↥Jbar ⧸ Subgroup.center ↥Jbar) :=
        ggHasLabel_quotCenter_of_mulEquiv
          (Subgroup.equivMapOfInjective Jbar e.toMonoidHom e.injective).symm hlabQ
      let eJ := Classical.choice (nonempty_centerQuot_J θ hcfg)
      exact ggHasLabel_of_mulEquiv eJ.symm h1
    refine ⟨?_, lab, hSS, hlab2, hlabel⟩
    refine (ggSecFiveBCoordSparse_iff eta i0 D).2 ?_
    intro z hzD hz1 hzi0
    obtain ⟨c, hzc, hpc⟩ := hzpow z hzD hz1 hzi0
    have hcoord : (fun j => eta z (i0.succAbove j)) =
        (fun j => eta z0b (i0.succAbove j)) ^ c := by
      have h1 : eta z = (eta z0b) ^ c := by rw [hzc, map_pow]
      funext j
      simpa [Pi.pow_apply] using congrFun h1 (i0.succAbove j)
    rw [hcoord]
    exact (ggCoordSparse_pow hp hpc).2 hsparse0'

theorem ggCommonJ_marking_of_nativeRow (hcfg : GGConfig p B Bs x L D J) (hB : B = Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hR : Subgroup.center R = ⊥)
    (hγ : GGGammaHatSpec θ γ) {m : ℕ} (hm : 3 ≤ m)
    (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))) (i0 : Fin (m + 1))
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (m + 1) p i0)
    {H : Type} [Group H] (e : R ≃* H) {SD SS : LargeEvenLabel → Prop}
    (hrow : GGSecFiveBNativeRow H p m SD SS) :
    (GGSecFiveBCoordDense eta i0 D ∧ LargeEvenMarking J (fun labJ _ _ _ _ _ => SD labJ ∧
        (labJ = ⟨.twA, 3, 1⟩ → Subgroup.center ↥L = ⊥ → LargeEvenSmall J))) ∨
      (GGSecFiveBCoordSparse eta i0 D ∧ LargeEvenMarking J (fun labJ _ _ _ _ _ => SS labJ)) := by
  have hq : CFSG.Assembly.IsQuasisimple J := hcfg.2.2.1.2.2.2.2.2.1.2.2
  rcases ggCommonJ_of_nativeRow hcfg hB hBsN hR hγ hm eta i0 hA e hrow with
    ⟨hdense, lab, hSD, hlab2, hlabQ, hsmall⟩ | ⟨hsparse, lab, hSS, hlab2, hlabQ⟩
  · left
    refine ⟨hdense, ?_⟩
    refine largeEvenMarking_mono ?_ (largeEvenMarking_of_hasLabel hq hlab2 hlabQ)
    intro lab' R' _ I F θ' h
    cases h
    exact ⟨hSD, hsmall⟩
  · right
    refine ⟨hsparse, ?_⟩
    refine largeEvenMarking_mono ?_ (largeEvenMarking_of_hasLabel hq hlab2 hlabQ)
    intro lab' R' _ I F θ' h
    cases h
    exact hSS

end CommonJ

end CFSG.StandardType

end
