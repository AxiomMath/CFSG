module

public import CFSG.Quasithin.Background.C124YZJR
public import CFSG.Quasithin.Background.C124YZGen

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YZ

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G]

theorem exists_starZ3 {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
    (E : Entry X T V L R m hV) {N : ℕ} {Q : Type} [Group Q] [Finite Q]
    {act : Perm (Fin m) →* MulAut Q} (MF : ModelFacts m Q act N)
    (hN : Nat.card ↥(autI hV R) ≤ N)
    (π : ↥(alternatingGroup (Fin m)) →* ↥(autI hV L)) (hπ : Function.Injective π)
    (ι : ↥(autI hV X) →* Perm (Fin m)) (hι : Function.Injective ι)
    (hιπ : ∀ γ : ↥(alternatingGroup (Fin m)),
      ι (Subgroup.inclusion (autI_mono hV (le_of_mem_cComp E.comp)) (π γ)) = γ)
    (β : ↥(commV (autI hV L)) →* Q) (hβs : Function.Surjective β)
    (hβe : ∀ (g : ↥(autI hV X)) (u : ↥(commV (autI hV L)))
      (hu : (g : MulAut (IntMod V hV)) (u : IntMod V hV) ∈ commV (autI hV L)),
      β ⟨(g : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩ = act (ι g) (β u)) :
    ∃ Ys, StarZ3 X V L R hV Ys := by
  classical
  have hVX : V ≤ X := E.red.1
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := E.red.2.1
  have hLX : L ≤ X := le_of_mem_cComp E.comp
  have hRX : R ≤ X := E.RT.trans E.sylow.1
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := hRX.trans hXN
  have hVR : V ≤ R := (le_pCoreOf_of_reduced E.red).trans E.QR
  have hRp : IsPGroup 2 R := E.sylow.2.1.to_le E.RT
  have hLsXs : autI hV L ≤ autI hV X := autI_mono hV hLX
  have hXsN := autI_normalizes hV E.normal
  have hUinv : ∀ g ∈ autI hV X, ∀ u ∈ commV (autI hV L), g u ∈ commV (autI hV L) :=
    fun g hg u hu => apply_mem_commV (hXsN hg) hu
  have hAn : ∀ A : Subgroup G, IsMaxElemAbelian R A → autI hV A ≤ autI hV R :=
    fun A hA => autI_mono hV hA.1
  have hAX : ∀ A : Subgroup G, IsMaxElemAbelian R A → autI hV A ≤ autI hV X :=
    fun A hA => (hAn A hA).trans (autI_mono hV hRX)
  set Dx := autI hV (thompsonJ R) with hDx
  set D' := Bmap ι Dx with hD'
  obtain ⟨hSG, hpD', hcardD, hfixD⟩ := jr_facts E MF hN ι hι β hβs hβe
  have hDxR : Dx ≤ autI hV R := autI_mono hV (thompsonJ_le R)
  have hDxne : Dx ≠ ⊥ := fun h =>
    E.hJ ((autI_eq_bot_iff hV ((thompsonJ_le R).trans hRN)).1 h)
  have hD'ne : D' ≠ ⊥ := by
    intro h
    apply hDxne
    refine eq_bot_iff.2 fun g hg => ?_
    have hgX : g ∈ autI hV X := (hDxR.trans (autI_mono hV hRX)) hg
    have h1 : ι ⟨g, hgX⟩ ∈ D' := mem_Bmap.2 ⟨⟨g, hgX⟩, hg, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have := hι (h1.trans (map_one ι).symm)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  obtain ⟨a, b, hab, hswap⟩ : ∃ a b : Fin m, a ≠ b ∧ swap a b ∈ D' := by
    obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD'ne
    have : ∃ x, d x ≠ x := by
      by_contra hcon
      push Not at hcon
      exact hd1 (Subtype.ext (Equiv.ext hcon))
    obtain ⟨x, hx⟩ := this
    exact ⟨x, d x, Ne.symm hx, (hSG d hd x).resolve_left hx⟩
  obtain ⟨c, hc⟩ := MF.exists_fixed D' hSG hpD' hcardD
  have hca : a ≠ c := by
    intro h
    have := hc _ hswap
    rw [← h, swap_apply_left] at this
    exact hab this.symm
  have hcb : b ≠ c := by
    intro h
    have := hc _ hswap
    rw [← h, swap_apply_right] at this
    exact hab this
  have hq : MF.pairModel.pq a b ∈ fixAct act D' := MF.pairModel.pq_mem_fixAct hSG hpD' hab hswap
  have hSle : autI hV (baum R) ≤ Dx := by
    intro s hs
    have hsX : s ∈ autI hV X := autI_mono hV (inf_le_left.trans hRX) hs
    have hmemD : ι ⟨s, hsX⟩ ∈ D' := by
      refine MF.pairModel.mem_of_fix hSG hpD' (MF.trichotomy D' hSG hpD' hD'ne hcardD) _ ?_
      intro q hq
      obtain ⟨u, rfl⟩ := hβs q
      have hsu : s (u : IntMod V hV) = u := autI_baum_fix hV hVR hRN hs (hfixD u hq)
      have h1 := hβe ⟨s, hsX⟩ u (hUinv s hsX u u.2)
      rw [← h1]
      congr 1
      exact Subtype.ext hsu
    obtain ⟨g, hg, hgι⟩ := mem_Bmap.1 hmemD
    have hgs : (g : MulAut (IntMod V hV)) = s := congrArg Subtype.val (hι hgι)
    rw [← hgs]
    exact hg
  have hSeq : autI hV (baum R) = Dx :=
    le_antisymm hSle (autI_mono hV (thompsonJ_le_baum R))
  have hy3alt : swap a b * swap a c ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hca]
    decide
  let π' : ↥(alternatingGroup (Fin m)) →* MulAut (IntMod V hV) := (autI hV L).subtype.comp π
  have hπ' : Function.Injective π' := Subtype.val_injective.comp hπ
  set Ys : Subgroup (MulAut (IntMod V hV)) :=
    ((Subgroup.zpowers (swap a b * swap a c)).subgroupOf (alternatingGroup (Fin m))).map π'
    with hYs
  have hYsL : Ys ≤ autI hV L := by
    rintro _ ⟨γ, -, rfl⟩
    exact (π γ).2
  have hcardY : Nat.card ↥Ys = 3 := by
    rw [hYs, Subgroup.card_map_of_injective hπ',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 hy3alt)).toEquiv,
      Nat.card_zpowers]
    exact (Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hca hcb).orderOf
  have hy3a : (swap a b * swap a c) a = c := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hca) (Ne.symm hcb)]
  have hy3b : (swap a b * swap a c) b = a := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hab) hcb.symm.symm, swap_apply_right]
  have hnotcent : ¬ fixV Dx ≤ fixV Ys := by
    obtain ⟨u₀, hu₀⟩ := hβs (MF.pairModel.pq a b)
    intro hle
    have hu₀fix := hle (hfixD u₀ (by rw [hu₀]; exact hq))
    have hmemY : π' ⟨swap a b * swap a c, hy3alt⟩ ∈ Ys :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers _))
    have hfix1 := hu₀fix _ hmemY
    set g : ↥(autI hV X) := Subgroup.inclusion hLsXs (π ⟨swap a b * swap a c, hy3alt⟩) with hg
    have hgu : (g : MulAut (IntMod V hV)) (u₀ : IntMod V hV) ∈ commV (autI hV L) := by
      rw [show (g : MulAut (IntMod V hV)) (u₀ : IntMod V hV) = u₀ from hfix1]
      exact u₀.2
    have h1 := hβe g u₀ hgu
    have h2 : β ⟨(g : MulAut (IntMod V hV)) (u₀ : IntMod V hV), hgu⟩ = β u₀ :=
      congrArg β (Subtype.ext hfix1)
    rw [h2, hg, hιπ, hu₀, MF.pairModel.act_pq, hy3a, hy3b] at h1
    rcases MF.pairModel.mem_of_eq a b c a hab (Ne.symm hca) h1.symm with h | h
    · exact hca h.symm
    · exact hcb h.symm
  have hSnorm : autI hV (baum R) ≤ Subgroup.normalizer (Ys : Set (MulAut (IntMod V hV))) := by
    rw [hSeq]
    intro s hs
    have hsX : s ∈ autI hV X := (hDxR.trans (autI_mono hV hRX)) hs
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨γ, hγ, rfl⟩ := hy
    set σ := ι ⟨s, hsX⟩ with hσ
    have hσD : σ ∈ D' := mem_Bmap.2 ⟨⟨s, hsX⟩, hs, rfl⟩
    have hconj := conj_threeCycle_mem hab hca hcb (hSG.apply_mem_pair hpD' hab hswap hσD)
      (hSG.apply_mem_pair hpD' (Ne.symm hab) (by rwa [swap_comm]) hσD).symm (hc σ hσD)
    have hγ' : σ * (γ : Perm (Fin m)) * σ⁻¹ ∈ Subgroup.zpowers (swap a b * swap a c) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hγ)
      rw [← hk, ← conj_zpow]
      exact Subgroup.zpow_mem _ hconj k
    let γ' : ↥(alternatingGroup (Fin m)) :=
      ⟨σ * (γ : Perm (Fin m)) * σ⁻¹, (alternatingGroup.normal (α := Fin m)).conj_mem γ γ.2 σ⟩
    have hmem : π' γ' ∈ Ys := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hγ')
    have heq : s * π' γ * s⁻¹ = π' γ' := by
      have h1 : (⟨s, hsX⟩ : ↥(autI hV X)) * Subgroup.inclusion hLsXs (π γ) * ⟨s, hsX⟩⁻¹ =
          Subgroup.inclusion hLsXs (π γ') := by
        apply hι
        rw [map_mul, map_mul, map_inv, hιπ, hιπ]
      exact congrArg Subtype.val h1
    rw [heq]
    exact hmem
  have hιsurj : Function.Surjective ι := by
    intro σ
    obtain ⟨g₀, -, hg₀⟩ := mem_Bmap.1 hswap
    by_cases hsg : σ ∈ alternatingGroup (Fin m)
    · exact ⟨Subgroup.inclusion hLsXs (π ⟨σ, hsg⟩), hιπ ⟨σ, hsg⟩⟩
    · have hsgn : σ * swap a b ∈ alternatingGroup (Fin m) := by
        rw [Equiv.Perm.mem_alternatingGroup] at hsg ⊢
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · exact absurd h hsg
        · rw [h]
          decide
      refine ⟨Subgroup.inclusion hLsXs (π ⟨σ * swap a b, hsgn⟩) * g₀, ?_⟩
      rw [map_mul, hιπ, hg₀]
      simp
  have hYsX : Ys ≤ autI hV X := hYsL.trans hLsXs
  have hgen : autI hV X = Ys ⊔ (autI hV X ⊓
      Subgroup.normalizer (autI hV (baum R) : Set (MulAut (IntMod V hV)))) := by
    refine le_antisymm ?_ (sup_le hYsX inf_le_left)
    set M := Ys ⊔ (autI hV X ⊓
      Subgroup.normalizer (autI hV (baum R) : Set (MulAut (IntMod V hV)))) with hM
    have hMtop : (M.subgroupOf (autI hV X)).map ι = ⊤ := by
      rw [eq_top_iff, ← zpowers_sup_normalizer_eq_top hSG hpD' hab hca hcb hswap hc]
      refine sup_le (Subgroup.zpowers_le.2 ?_) ?_
      · refine ⟨Subgroup.inclusion hLsXs (π ⟨swap a b * swap a c, hy3alt⟩), ?_, hιπ _⟩
        exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _
          (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers _))))
      · intro σ hσ
        obtain ⟨g, rfl⟩ := hιsurj σ
        refine ⟨g, Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right ⟨g.2, ?_⟩), rfl⟩
        rw [hSeq]
        refine Subgroup.mem_normalizer_fintype fun d hd => ?_
        have hdX : d ∈ autI hV X := (hDxR.trans (autI_mono hV hRX)) hd
        have h1 : ι ⟨d, hdX⟩ ∈ D' := mem_Bmap.2 ⟨⟨d, hdX⟩, hd, rfl⟩
        have h2 : ι g * ι ⟨d, hdX⟩ * (ι g)⁻¹ ∈ D' :=
          (Subgroup.mem_normalizer_iff.1 hσ (ι ⟨d, hdX⟩)).1 h1
        obtain ⟨g'', hg'', hg''ι⟩ := mem_Bmap.1 h2
        have h3 : g'' = g * ⟨d, hdX⟩ * g⁻¹ := hι (by rw [hg''ι, map_mul, map_mul, map_inv])
        have h4 : (g'' : MulAut (IntMod V hV)) =
            (g : MulAut (IntMod V hV)) * d * (g : MulAut (IntMod V hV))⁻¹ :=
          congrArg Subtype.val h3
        rw [← h4]
        exact hg''
    intro g hg
    have h5 : ι ⟨g, hg⟩ ∈ (M.subgroupOf (autI hV X)).map ι := by
      rw [hMtop]
      trivial
    obtain ⟨g', hg', hg'ι⟩ := h5
    have h6 : g' = ⟨g, hg⟩ := hι hg'ι
    rw [h6] at hg'
    exact Subgroup.mem_subgroupOf.1 hg'
  exact ⟨Ys, ⟨⟨hYsL, hnotcent, hgen⟩, hcardY, hSnorm⟩⟩

end CFSG.Quasithin.C124.YZ
