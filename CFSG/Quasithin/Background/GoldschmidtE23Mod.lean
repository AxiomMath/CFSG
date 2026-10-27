module

public import CFSG.Quasithin.Background.GoldschmidtE23Split
public import CFSG.Quasithin.Background.GoldschmidtE23Shape

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique G6

namespace GE23

section Split

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}

theorem exists_perm_pair {n : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : Equiv.Perm (Fin n), g a = c ∧ g b = d := by
  classical
  by_cases hac : a = c
  · subst hac
    refine ⟨Equiv.swap b d, ?_, ?_⟩
    · exact Equiv.swap_apply_of_ne_of_ne hab hcd
    · exact Equiv.swap_apply_left _ _
  · set g₁ : Equiv.Perm (Fin n) := Equiv.swap a c with hg₁
    have h1 : g₁ a = c := Equiv.swap_apply_left _ _
    have hb' : g₁ b ≠ c := fun h => hab (g₁.injective (h.trans h1.symm)).symm
    refine ⟨Equiv.swap (g₁ b) d * g₁, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, h1, Equiv.swap_apply_of_ne_of_ne hb'.symm hcd]
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem block_split (hB : B69.BlkCtx X T M)
    (hk2 : ∀ {H : Subgroup (MulAut V)} {k : ℕ}, SymBlk X H k → k = 2)
    {H : Subgroup (MulAut V)} (hH : H ∈ B69.blkFamily X) {U : Subgroup V} (hWU : commV H ≤ U)
    (hUinv : ∀ s ∈ H, ∀ u ∈ U, s u ∈ U) :
    ∀ u ∈ U, ∃ w ∈ commV H, ∃ c ∈ U, (∀ s ∈ H, s c = c) ∧ u = w * c := by
  have htriv : ∀ s ∈ H, ∀ u : V, s u * u⁻¹ ∈ commV H := by
    obtain ⟨L, hL, rfl⟩ := B69.mem_blkFamily.1 hH
    intro s hs u
    rw [commV_blk hB hL]
    exact B69.blk_le_centQuot hB.hV hB.hctx hL (hB.hact L hL) hs u
  have hdec : ∀ {K W : Subgroup V} {A : Subgroup (MulAut V)}, W ≤ U → (W ⊔ K = ⊤) →
      ∀ u ∈ U, ∃ w ∈ W, ∃ c ∈ U ⊓ K, u = w * c := by
    intro K W A hWU' hWK u hu
    have : u ∈ W ⊔ K := by rw [hWK]; exact Subgroup.mem_top u
    obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.1 this
    exact ⟨w, hw, c, ⟨by simpa using U.mul_mem (U.inv_mem (hWU' hw)) hu, hc⟩, rfl⟩
  rcases block_type hB hH with hN | ⟨k, hS⟩
  ·
    obtain ⟨L, e, hL, hblk, hHL, he, -, A, hA, hLA, hsyl⟩ := hN
    subst hHL
    have hW₀ : commV H ∈ IrrPlus H (⊤ : Subgroup V) :=
      B69.commV_mem_irrPlus hB.hV hB.hctx hA hL hLA
    obtain ⟨hsup, -⟩ := B69.eq_sup_fixV_of_shape hB.hV hA hL.2.2 hLA hW₀
      (hB.hctx A H hA hL hLA (commV H) hW₀)
    refine split_of_odd_index hB.hV hsyl.2.2 hUinv (fun s hs u _ => htriv s hs u) ?_
    intro u hu
    obtain ⟨w, hw, c, hc, rfl⟩ := hdec (A := A) hWU hsup u hu
    exact ⟨w, hw, c, hc.1, fun a ha => hc.2 a ha, rfl⟩
  ·
    have hk := hk2 hS
    subst hk
    obtain ⟨L, A, hL, hA, hLA, hblk, rfl, hk, π, hπs, hreal, hLeq, ⟨i₀, j₀, hij, hAsw⟩⟩ := hS
    have hcomm : commV (L ⊔ A) = commV L := by
      rw [← hblk]
      exact commV_blk hB hL
    have hW₀ : commV L ∈ IrrPlus L (⊤ : Subgroup V) :=
      B69.commV_mem_irrPlus hB.hV hB.hctx hA hL hLA
    obtain ⟨hsup, -⟩ := B69.eq_sup_fixV_of_shape hB.hV hA hL.2.2 hLA hW₀
      (hB.hctx A L hA hL hLA (commV L) hW₀)
    obtain ⟨θ, β₀, hθ, hβ, hrange, hker⟩ := Ch3z.isSymCore_of_realizes' hreal
    have hequiv : ∀ (σ : Equiv.Perm (Fin 5)) (y : ↥(coreMod 5)),
        β₀ (coreAct 5 σ y) = ((π σ : ↥(L ⊔ A)) : MulAut V) (β₀ y) := by
      intro σ y
      have h1 := hβ (π σ) y
      have h2 : θ (π σ) = σ := by rw [← hθ σ, MulEquiv.apply_symm_apply]
      rw [h2] at h1
      exact h1
    have hWinv : ∀ s ∈ L ⊔ A, ∀ w ∈ commV L, s w ∈ commV L := by
      intro s hs w hw
      obtain ⟨σ, hσ⟩ := hπs ⟨s, hs⟩
      rw [← hrange] at hw
      obtain ⟨y, rfl⟩ := hw
      have : s (β₀ y) = β₀ (coreAct 5 σ y) := by
        rw [hequiv, hσ]
      rw [this, ← hrange]
      exact ⟨_, rfl⟩
    refine split_sym hπs hequiv (hcomm.trans hrange.symm) (hcomm ▸ hWU) ?_
    intro i u hu
    obtain ⟨g, hg1, hg2⟩ := exists_perm_pair hij (Fin.castSucc_lt_succ (i := i)).ne
    have hgS : ((π g : ↥(L ⊔ A)) : MulAut V) ∈ L ⊔ A := (π g).2
    have hgS' : ((π g : ↥(L ⊔ A)) : MulAut V)⁻¹ ∈ L ⊔ A := (L ⊔ A).inv_mem hgS
    have hu' : ((π g : ↥(L ⊔ A)) : MulAut V)⁻¹ u ∈ U := hUinv _ hgS' u hu
    obtain ⟨w', hw', c', hc', hu'eq⟩ := hdec (A := A) (hcomm ▸ hWU) hsup _ hu'
    have ha₀ : ((π (Equiv.swap i₀ j₀) : ↥(L ⊔ A)) : MulAut V) ∈ A :=
      hAsw.ge ⟨Equiv.swap i₀ j₀, Subgroup.mem_zpowers _, rfl⟩
    refine ⟨((π g : ↥(L ⊔ A)) : MulAut V) w', ?_, ((π g : ↥(L ⊔ A)) : MulAut V) c', ?_, ?_, ?_⟩
    · rw [hcomm]
      exact hWinv _ hgS w' hw'
    · exact hUinv _ hgS c' hc'.1
    · have hτ : Equiv.swap (Fin.castSucc i) i.succ =
          g * Equiv.swap i₀ j₀ * g⁻¹ := by
        rw [← Equiv.swap_apply_apply, hg1, hg2]
      rw [hτ, map_mul, map_mul, map_inv]
      show ((π g : ↥(L ⊔ A)) : MulAut V) (((π (Equiv.swap i₀ j₀) : ↥(L ⊔ A)) : MulAut V)
        (((π g : ↥(L ⊔ A)) : MulAut V)⁻¹ (((π g : ↥(L ⊔ A)) : MulAut V) c'))) = _
      rw [MulAut.inv_apply_self, hc'.2 _ ha₀]
    · have := congrArg (fun z => ((π g : ↥(L ⊔ A)) : MulAut V) z) hu'eq
      simpa using this

theorem blocks_split (hB : B69.BlkCtx X T M) (h : MinParabolic X T M) (hFF : IsFFModule X)
    (hk2 : ∀ {H : Subgroup (MulAut V)} {k : ℕ}, SymBlk X H k → k = 2) :
    ∀ 𝓘 : Finset (Subgroup (MulAut V)), (∀ H ∈ 𝓘, H ∈ B69.blkFamily X) →
      ∀ v : V, ∃ w ∈ ⨆ H ∈ 𝓘, commV H, ∃ c ∈ fixV (⨆ H ∈ 𝓘, H), v = w * c := by
  classical
  have hsc := B69.structConcl_of_blkCtx hB h hFF
  intro 𝓘
  induction 𝓘 using Finset.induction_on with
  | empty =>
    intro _ v
    refine ⟨1, Subgroup.one_mem _, v, ?_, (one_mul v).symm⟩
    intro s hs
    have : s = 1 := by simpa using hs
    rw [this]
    rfl
  | insert H₀ 𝓘 hH₀ ih =>
    intro hmem v
    have hH₀m : H₀ ∈ B69.blkFamily X := hmem H₀ (Finset.mem_insert_self _ _)
    have hmem' : ∀ H ∈ 𝓘, H ∈ B69.blkFamily X := fun H hH =>
      hmem H (Finset.mem_insert_of_mem hH)
    have hne : ∀ H ∈ 𝓘, H ≠ H₀ := fun H hH heq => hH₀ (heq ▸ hH)
    obtain ⟨w, hw, c, hc, rfl⟩ := ih hmem' v
    have hcent : (⨆ H ∈ 𝓘, H) ≤ Subgroup.centralizer (H₀ : Set (MulAut V)) := by
      refine iSup₂_le fun H hH a ha => ?_
      refine Subgroup.mem_centralizer_iff.2 fun b hb => ?_
      exact (hsc.2.2.1 H (hmem' H hH) H₀ hH₀m (hne H hH) a ha b hb).symm
    have hWU : commV H₀ ≤ fixV (⨆ H ∈ 𝓘, H) := by
      have : (⨆ H ∈ 𝓘, H) ≤ centSub (commV H₀) := by
        refine iSup₂_le fun H hH y hy u hu => ?_
        exact commSub_eq_bot_iff.1 (hsc.2.2.2.2.2.2.1 H₀ hH₀m H (hmem' H hH) (hne H hH).symm)
          hu y hy
      intro u hu y hy
      exact this hy u hu
    have hUinv : ∀ s ∈ H₀, ∀ u ∈ fixV (⨆ H ∈ 𝓘, H), s u ∈ fixV (⨆ H ∈ 𝓘, H) := by
      intro s hs u hu y hy
      have hyc : y * s = s * y := by
        have := Subgroup.mem_centralizer_iff.1 (hcent hy) s hs
        exact this.symm
      calc y (s u) = (y * s) u := rfl
        _ = (s * y) u := by rw [hyc]
        _ = s (y u) := rfl
        _ = s u := by rw [hu y hy]
    obtain ⟨w₁, hw₁, c₁, hc₁, hc₁fix, hceq⟩ := block_split hB hk2 hH₀m hWU hUinv c hc
    refine ⟨w * w₁, ?_, c₁, ?_, ?_⟩
    · rw [Finset.iSup_insert]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hw) (Subgroup.mem_sup_left hw₁)
    · rw [Finset.iSup_insert]
      intro s hs
      have hle : H₀ ⊔ (⨆ H ∈ 𝓘, H) ≤ MulAction.stabilizer (MulAut V) c₁ :=
        sup_le (fun s hs' => hc₁fix s hs') (fun s hs' => hc₁ s hs')
      exact hle hs
    · rw [hceq]
      group

theorem isSolvable_kerIn_ambient (h : MinParabolic X T M) : Group.IsSolvable ↥(kerIn M X) := by
  have hsol : Group.IsSolvable ↥(kerIn (M.subgroupOf X) ⊤) := h.subgroupOf.isSolvable_kerIn
  rw [B6.kerIn_subgroupOf_top] at hsol
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe (MinParabolic.kerIn_le_H h)).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe (MinParabolic.kerIn_le_H h)).surjective

theorem twoResidual_le_components (hB : B69.BlkCtx X T M) (h : MinParabolic X T M)
    (hFF : IsFFModule X) (hns : ¬ Group.IsSolvable ↥X) :
    twoResidual X ≤ ⨆ (L : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L X), L := by
  classical
  set N : Subgroup (MulAut V) := ⨆ (L : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L X), L
    with hN
  have hNX : N ≤ X := iSup₂_le fun L hL => hL.1
  have key : ∀ g ∈ X, B6.conjSub g N ≤ N := fun g hg => by
    rw [hN]
    simp only [OrderIso.map_iSup]
    exact iSup₂_le fun L hL =>
      le_iSup₂_of_le (f := fun (L : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L X) => L)
        (B6.conjSub g L) (B113.isComponentOf_conj hL hg) le_rfl
  have hNn : X ≤ Subgroup.normalizer (N : Set (MulAut V)) := fun g hg =>
    B6.mem_normalizer_of_conjSub_le (key g hg) (key g⁻¹ (X.inv_mem hg))
  rcases h.le_kerIn_or_twoResidual_le hNX hNn with hJ | hK
  · exfalso
    obtain ⟨A₀, hA₀⟩ := (B1_7 hB.hV hFF).1
    obtain ⟨L₀, hL₀, -⟩ := B69.exists_component_of_nonsolvable hB.hV hB.hP4 h hB.hO2 hns hA₀
    have hLN : L₀ ≤ kerIn M X := (le_iSup₂_of_le (f := fun (L : Subgroup (MulAut V))
      (_ : CFSG.Open.IsComponentOf L X) => L) L₀ hL₀ le_rfl).trans hJ
    have : Group.IsSolvable ↥L₀ := by
      have := isSolvable_kerIn_ambient h
      exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLN)
        (Subgroup.inclusion_injective hLN)
    have hperf : Group.IsPerfect ↥L₀ := Group.isPerfect_def.mpr hL₀.2.2.1
    have hnt : Nontrivial ↥L₀ := CFSG.ComponentClassification.Quasisimple.nontrivial hL₀.2.2
    exact Group.IsPerfect.not_isSolvable ↥L₀ this
  · exact hK

theorem inf_le_fixV_twoResidual (hB : B69.BlkCtx X T M) (h : MinParabolic X T M)
    (hFF : IsFFModule X) (hns : ¬ Group.IsSolvable ↥X) {H : Subgroup (MulAut V)}
    (hH : H ∈ B69.blkFamily X) :
    commV H ⊓ (fixV (twoResidual X) ⊔
        ⨆ H' ∈ B69.blkFamily X, ⨆ (_ : H' ≠ H), commV H') ≤ fixV (twoResidual X) := by
  classical
  have hsc := B69.structConcl_of_blkCtx hB h hFF
  rintro w ⟨hwH, hw⟩
  obtain ⟨c, hc, w', hw', hcw⟩ := Subgroup.mem_sup.1 hw
  have hother : ∀ H' ∈ B69.blkFamily X, H' ≠ H → ∀ y ∈ H', ∀ z ∈ commV H, y z = z := by
    intro H' hH' hne y hy z hz
    exact commSub_eq_bot_iff.1 (hsc.2.2.2.2.2.2.1 H hH H' hH' (Ne.symm hne)) hz y hy
  have hacts : ∀ y ∈ H, ∀ z ∈ ⨆ H' ∈ B69.blkFamily X, ⨆ (_ : H' ≠ H), commV H', y z = z := by
    intro y hy z hz
    have hle : (⨆ H' ∈ B69.blkFamily X, ⨆ (_ : H' ≠ H), commV H') ≤ fixV H := by
      refine iSup₂_le fun H' hH' => iSup_le fun hne => ?_
      exact commSub_eq_bot_iff.1 (hsc.2.2.2.2.2.2.1 H' hH' H hH hne)
    exact hle hz y hy
  have hcomp : ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L X → ∀ l ∈ L, l w = w := by
    intro L hL l hl
    have hLK : L ≤ twoResidual X := component_le_twoResidual hL
    by_cases hbl : B69.blk X L = H
    · have hlH : l ∈ H := hbl ▸ B69.le_blk_self hl
      rw [← hcw, map_mul, hc l (hLK hl), hacts l hlH w' hw']
    · exact hother (B69.blk X L) (B69.mem_blkFamily.2 ⟨L, hL, rfl⟩) hbl l
        (B69.le_blk_self hl) w hwH
  have hN : (⨆ (L : Subgroup (MulAut V)) (_ : CFSG.Open.IsComponentOf L X), L) ≤
      MulAction.stabilizer (MulAut V) w :=
    iSup₂_le fun L hL l hl => hcomp L hL l hl
  intro k hk
  exact hN (twoResidual_le_components hB h hFF hns hk)

end Split

end GE23

end CFSG.Quasithin
