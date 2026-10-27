module

public import CFSG.Quasithin.Background.C124Interface
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.C124BlkTransfer

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem permWeight_sub_mem {m : ℕ} (σ : Equiv.Perm (Fin m)) {x y : ↥(evenWeight m)}
    (h : -x + y ∈ constWeight m) : -permWeight m σ x + permWeight m σ y ∈ constWeight m := by
  intro i j
  have := h (σ⁻¹ i) (σ⁻¹ j)
  simpa [permWeight] using this

theorem exists_isAltBlockTypeWith {G : Type} [Group G] [Finite G] {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) {n : ℕ} (hn : 0 < n) (hL : L ≤ Subgroup.normalizer (V : Set G))
    (hker : pCoreOf 2 L = L ⊓ Subgroup.centralizer (V : Set G)) (hVL : ⁅V, L⁆ ≤ blockU L)
    (hU : blockU L = ⁅V, L⁆ ⊔ blockZ L) (π : ↥(alternatingGroup (Fin n)) →* ↥(autI hV L))
    (hπ : (FFModel.altDn n).RealizesVia (autI hV L) (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) π) (hinj : Function.Injective π) :
    ∃ α : ↥L →* alternatingGroup (Fin n), IsAltBlockTypeWith L n α := by
  let eπ : ↥(alternatingGroup (Fin n)) ≃* ↥(autI hV L) := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  let α : ↥L →* alternatingGroup (Fin n) := eπ.symm.toMonoidHom.comp (starHom hV L hL)
  obtain ⟨β, hβs, hβk, hβe⟩ := exists_blockHomOfEquiv hV hL hVL hU (FFModel.altDn n) π hπ
    (altQuotEquiv n hn)
  refine ⟨α, ?_, ?_, β, hβs, hβk, ?_⟩
  · exact eπ.symm.surjective.comp (starHom_surjective hV hL)
  · rw [MonoidHom.ker_comp_of_injective _ eπ.symm.toMonoidHom eπ.symm.injective]
    exact ker_starHom_eq_pCore hV hL hker
  · intro ℓ u v hv x hx
    set γ : ↥(alternatingGroup (Fin n)) := eπ.symm (starHom hV L hL ℓ) with hγ
    have hπγ : π γ = starHom hV L hL ℓ := eπ.apply_symm_apply _
    obtain ⟨m, hm⟩ := altHeartHom_surjective n (β u)
    have hmu : β u = altQuotEquiv n hn (QuotientGroup.mk m) := hm.symm
    have hact : (FFModel.altDn n).act γ (m : G6.PermMod n) ∈ (FFModel.altDn n).sec :=
      G6.permAct_mem_coreMod _ m.2
    have h1 := hβe ℓ γ hπγ u v m hact hv hmu
    have h2 : Multiplicative.toAdd (β v) = (QuotientAddGroup.mk
        (permWeight n (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (coreEvenEquiv n m))) :
          AltHeart n) := by
      rw [h1]
      rfl
    show (QuotientAddGroup.mk (permWeight n (γ : Equiv.Perm (Fin n)) x) : AltHeart n) =
      Multiplicative.toAdd (β v)
    rw [h2]
    have h3 : (QuotientAddGroup.mk x : AltHeart n) =
        QuotientAddGroup.mk (Multiplicative.toAdd (coreEvenEquiv n m)) := by
      rw [hx, hmu]
      rfl
    rw [QuotientAddGroup.eq] at h3 ⊢
    exact permWeight_sub_mem _ h3

theorem spec4cAlt5_holds : Spec4cAlt5 := by
  intro G _ _ X T V L R m hV hE hC hB
  have hL : L ≤ Subgroup.normalizer (V : Set G) := (le_of_mem_cComp hE.comp).trans hE.red.2.1
  obtain ⟨-, π, hπ, hinj⟩ := hC
  obtain ⟨α, hα⟩ := exists_isAltBlockTypeWith hV (by norm_num : 0 < 5) hL hB.ker hB.VL_le hB.U_eq
    π hπ hinj
  exact (isAltType_iff_exists_isAltBlockTypeWith (by decide : Odd 5)).2 ⟨α, hα⟩

theorem spec4cAlt6_holds : Spec4cAlt6 := by
  intro G _ _ X T V L R m hV hE hC hB
  have hL : L ≤ Subgroup.normalizer (V : Set G) := (le_of_mem_cComp hE.comp).trans hE.red.2.1
  obtain ⟨-, π, hπ, hinj⟩ := hC
  obtain ⟨α, hα⟩ := exists_isAltBlockTypeWith hV (by norm_num : 0 < 6) hL hB.ker hB.VL_le hB.U_eq
    π hπ hinj
  exact ⟨hB.short, α, hα⟩

theorem spec4cAlt7_holds : Spec4cAlt7 := by
  intro G _ _ X T V L R m hV hE hC hB
  have hL : L ≤ Subgroup.normalizer (V : Set G) := (le_of_mem_cComp hE.comp).trans hE.red.2.1
  obtain ⟨-, π, hπ, hinj⟩ := hC
  obtain ⟨α, hα⟩ := exists_isAltBlockTypeWith hV (by norm_num : 0 < 7) hL hB.ker hB.VL_le hB.U_eq
    π hπ hinj
  exact (isAltType_iff_exists_isAltBlockTypeWith (by decide : Odd 7)).2 ⟨α, hα⟩

end CFSG.Quasithin.C124
