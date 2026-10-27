module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm13_10.FiveCentralB
public import CFSG.Quasithin.Background.Asc81cPfTrans1
public import CFSG.Quasithin.Background.ConjTransportRk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

private theorem commSub_top_sup_eq_top_of_swap {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L K : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hcL : IsComponentOf L Y) (hcK : IsComponentOf K Y)
    (haL : IsAlt ↥L 5) (haK : IsAlt ↥K 5) (hne : L ≠ K)
    (hXn : ((L ⊔ K).subgroupOf Y).Normal)
    (hsw : ∃ g ∈ Y, K = L.map (MulAut.conj g).toMonoidHom) :
    commSub (⊤ : Subgroup W) (L ⊔ K) = ⊤ := by
  have hH : L ⊔ K = ⨆ X ∈ conjSet L Y, X := by
    rw [iSup_conjSet_eq_biSup_conj, iSup_conj_eq_of_swap hcL hcK haL haK hne rfl hXn hsw]
  have htop := commV_eq_top hW hO2 hB hcL hH
  rw [commV_eq_commSub] at htop
  exact htop

theorem w4Thm13_10_normalizing_core {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L K : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hcL : IsComponentOf L Y) (hcK : IsComponentOf K Y)
    (haL : IsAlt ↥L 5) (haK : IsAlt ↥K 5) (hne : L ≠ K)
    (hXn : ((L ⊔ K).subgroupOf Y).Normal)
    (hsw : ∃ g ∈ Y, K = L.map (MulAut.conj g).toMonoidHom) {t : MulAut W}
    (htm : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3)
    (htL : L.map (MulAut.conj t).toMonoidHom = L) (hnc : ∃ x ∈ L, t * x ≠ x * t) :
    commSub (commSub (⊤ : Subgroup W) K) L = ⊥ ∧
      ∀ c ∈ Y, (∀ x ∈ L ⊔ K, c * x = x * c) → c ^ 5 = 1 → c = 1 := by
  have hcomm : ∀ a ∈ L, ∀ b ∈ K, a * b = b * a :=
    fun a ha b hb => B69.components_mul_comm_of_ne hcK hcL hne.symm a ha b hb
  have hfirst : commSub (commSub (⊤ : Subgroup W) K) L = ⊥ :=
    commSub_eq_bot_iff.mpr
      (commSub_le_fixV_of_isAlt_five_pair hW haL haK hcomm
        (Subgroup.mem_normalizer_iff_map_conj_eq.mpr htL) hnc htm)
  have htop : commSub (⊤ : Subgroup W) (L ⊔ K) = ⊤ :=
    commSub_top_sup_eq_top_of_swap hW hO2 hB hcL hcK haL haK hne hXn hsw
  refine ⟨hfirst, ?_⟩
  intro c _ hcX hc5
  have hcL : ∀ x ∈ L, c * x = x * c := fun x hx => hcX x (Subgroup.mem_sup_left hx)
  have h1 : commSub (⊤ : Subgroup W) (Subgroup.zpowers c) ≤ fixV L :=
    commSub_le_fixV_of_commute_of_isAlt_five hW haL
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr htL) hnc htm hc5 hcL
  obtain ⟨g, hg, rfl⟩ := hsw
  set t' : MulAut W := MulAut.conj g t with ht'def
  have hz : (Subgroup.zpowers t).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers t' := by
    simpa only [ht'def, MulEquiv.coe_toMonoidHom] using
      MonoidHom.map_zpowers (MulAut.conj g).toMonoidHom t
  have ht'm : rkIdx (fixV (Subgroup.zpowers t')) ≤ 3 := by
    rw [← hz, ConjTransport.rkIdx_fixV_map_conj]
    exact htm
  have ht'K : t' ∈ Subgroup.normalizer
      ((L.map (MulAut.conj g).toMonoidHom) : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe,
      B19.map_conj_map_conj]
    have ht'g : t' * g = g * t := by
      rw [ht'def, MulAut.conj_apply]
      group
    rw [ht'g, ← B19.map_conj_map_conj, htL]
  have hncK : ∃ x ∈ L.map (MulAut.conj g).toMonoidHom, t' * x ≠ x * t' := by
    obtain ⟨x, hxL, hxne⟩ := hnc
    refine ⟨MulAut.conj g x, Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hxL, ?_⟩
    intro h
    apply hxne
    have h2 := congrArg (fun z => MulAut.conj g⁻¹ z) h
    simpa [ht'def, MulAut.conj_apply, mul_assoc] using h2
  have hcK : ∀ x ∈ L.map (MulAut.conj g).toMonoidHom, c * x = x * c :=
    fun x hx => hcX x (Subgroup.mem_sup_right hx)
  have h2 : commSub (⊤ : Subgroup W) (Subgroup.zpowers c) ≤
      fixV (L.map (MulAut.conj g).toMonoidHom) :=
    commSub_le_fixV_of_commute_of_isAlt_five hW haK ht'K hncK ht'm hc5 hcK
  have h3 : commSub (⊤ : Subgroup W) (Subgroup.zpowers c) ≤
      fixV (L ⊔ L.map (MulAut.conj g).toMonoidHom) := by
    rw [Asc81c.Pf.fixV_sup]
    exact le_inf h1 h2
  exact eq_one_of_commSub_le_fixV htop hcX h3

theorem w4Thm13_10_normalizing {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L K : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hcL : IsComponentOf L Y) (hcK : IsComponentOf K Y)
    (haL : IsAlt ↥L 5) (haK : IsAlt ↥K 5) (hne : L ≠ K)
    (hXn : ((L ⊔ K).subgroupOf Y).Normal)
    (hsw : ∃ g ∈ Y, K = L.map (MulAut.conj g).toMonoidHom) {t : MulAut W}
    (ht2 : orderOf t = 2) (htm : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3)
    (htL : L.map (MulAut.conj t).toMonoidHom = L)
    (htK : K.map (MulAut.conj t).toMonoidHom = K) :
    commSub (commSub (⊤ : Subgroup W) L) K = ⊥ ∧
      ∀ c ∈ Y, (∀ x ∈ L ⊔ K, c * x = x * c) → c ^ 5 = 1 → c = 1 := by
  have hcommut : ⁅L, K⁆ = ⊥ := B69.components_commute_of_ne hcL hcK hne
  by_cases hncL : ∃ x ∈ L, t * x ≠ x * t
  · have hcore := w4Thm13_10_normalizing_core hW hO2 hB hcL hcK haL haK hne hXn hsw
      htm htL hncL
    refine ⟨?_, hcore.2⟩
    rw [s13_commSub_comm L K hcommut ⊤]
    exact hcore.1
  · by_cases hncK : ∃ x ∈ K, t * x ≠ x * t
    · have hsw' : ∃ g ∈ Y, L = K.map (MulAut.conj g).toMonoidHom := by
        obtain ⟨g, hg, hg2⟩ := hsw
        refine ⟨g⁻¹, Y.inv_mem hg, ?_⟩
        rw [hg2, B19.map_conj_map_conj, inv_mul_cancel]
        rw [show (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) by
          ext x
          simp]
        exact (Subgroup.map_id L).symm
      have hcore := w4Thm13_10_normalizing_core hW hO2 hB hcK hcL haK haL hne.symm
        (by simpa only [sup_comm] using hXn) hsw' htm htK hncK
      refine ⟨hcore.1, ?_⟩
      intro c hcY hcX hc5
      exact hcore.2 c hcY (fun x hx => hcX x (by simpa only [sup_comm] using hx)) hc5
    · exfalso
      have hcLt : ∀ x ∈ L, t * x = x * t := by
        intro x hx
        by_contra h
        exact hncL ⟨x, hx, h⟩
      have hcKt : ∀ x ∈ K, t * x = x * t := by
        intro x hx
        by_contra h
        exact hncK ⟨x, hx, h⟩
      have hLle : commSub (⊤ : Subgroup W) L ≤ fixV (Subgroup.zpowers t) := by
        refine commSub_le_fixV_zpowers_of_commute hW hcLt ?_
        rw [dMinDeg_eq_four_of_isAlt_five haL]
        omega
      have hKle : commSub (⊤ : Subgroup W) K ≤ fixV (Subgroup.zpowers t) := by
        refine commSub_le_fixV_zpowers_of_commute hW hcKt ?_
        rw [dMinDeg_eq_four_of_isAlt_five haK]
        omega
      have htop : commSub (⊤ : Subgroup W) (L ⊔ K) = ⊤ :=
        commSub_top_sup_eq_top_of_swap hW hO2 hB hcL hcK haL haK hne hXn hsw
      have hle : commSub (⊤ : Subgroup W) (L ⊔ K) ≤ fixV (Subgroup.zpowers t) := by
        rw [Asc81c.Pf.commSub_sup]
        exact sup_le hLle hKle
      have hfix : fixV (Subgroup.zpowers t) = ⊤ := top_le_iff.mp (htop ▸ hle)
      have ht1 : t = 1 := by
        ext v
        have hv : v ∈ fixV (Subgroup.zpowers t) := hfix ▸ Subgroup.mem_top v
        exact mem_fixV.mp hv t (Subgroup.mem_zpowers t)
      rw [ht1, orderOf_one] at ht2
      omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10
