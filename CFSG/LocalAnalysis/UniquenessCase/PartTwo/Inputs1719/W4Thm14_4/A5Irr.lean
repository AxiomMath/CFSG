module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5ModGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57M5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.NaturalTransport
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13AltModule
public import CFSG.Quasithin.Background.FFC4Res
public import CFSG.Quasithin.Background.G2A5
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise Matrix

theorem ne_bot_of_isAlt_five {G : Type} [Group G] {L : Subgroup G}
    (h : IsAlt ↥L 5) : L ≠ ⊥ := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 5))
  haveI : IsSimpleGroup ↥L := (MulEquiv.isSimpleGroup_congr e).mpr ‹_›
  exact (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance

theorem isPerfect_of_isAlt_five {G : Type} [Group G] {L : Subgroup G}
    (h : IsAlt ↥L 5) : Group.IsPerfect ↥L := by
  obtain ⟨e⟩ := h
  have hA5 : Group.IsPerfect ↥(alternatingGroup (Fin 5)) :=
    Group.isPerfect_def.2 (commutator_alternatingGroup_eq_top (by simp))
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem exists_moves_of_commSub_ne_bot {W : Type} [CommGroup W] {I : Subgroup W}
    {L : Subgroup (MulAut W)} (h : commSub I L ≠ ⊥) : ∃ l ∈ L, ∃ u ∈ I, l u ≠ u := by
  by_contra hcon
  push Not at hcon
  exact h (commSub_eq_bot_iff.mpr fun u hu l hl => hcon l hl u hu)

theorem a5_faithful_of_moves {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} (hL : IsAlt ↥L 5) (hI : StableUnder L I)
    (hmv : ∃ l ∈ L, ∃ u ∈ I, l u ≠ u) : ∀ l ∈ L, (∀ u ∈ I, l u = u) → l = 1 := by
  obtain ⟨e⟩ := hL
  haveI : IsSimpleGroup ↥L :=
    (MulEquiv.isSimpleGroup_congr e).mpr
      (alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 5)))
  have hLI : L ≤ stabSub I := B1.le_stabSub_of_invariant hI
  intro l hl hfix
  have hk : (⟨l, hl⟩ : ↥L) ∈ (FFC.resG hLI).ker := by
    rw [MonoidHom.mem_ker]
    ext u
    simpa [FFC.resG_apply] using hfix (u : W) u.2
  have hne : (FFC.resG hLI).ker ≠ ⊤ := by
    intro htop
    obtain ⟨l', hl', u, hu, hlu⟩ := hmv
    have : (⟨l', hl'⟩ : ↥L) ∈ (FFC.resG hLI).ker := by rw [htop]; exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at this
    apply hlu
    have := congrArg (fun φ : MulAut ↥I => ((φ ⟨u, hu⟩ : ↥I) : W)) this
    simpa [FFC.resG_apply] using this
  have hbot := IsSimpleGroup.eq_bot_or_eq_top_of_normal (FFC.resG hLI).ker
  rcases hbot with h | h
  · have : (⟨l, hl⟩ : ↥L) = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact hk
    simpa using congrArg Subtype.val this
  · exact absurd h hne

theorem isIrrOn_of_mem_irrSet {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} (hfix : fixV L = ⊥) (hI : I ∈ irrSet L) :
    IsIrrOn L I ⊥ ∧ ∃ l ∈ L, ∃ u ∈ I, l u ≠ u := by
  have hIrr : IsIrrOn L I (I ⊓ fixV L) := hI.2
  have hinf : I ⊓ fixV L = ⊥ := by rw [hfix, inf_bot_eq]
  have hIne : I ≠ ⊥ := by
    intro h
    have hlt := hIrr.1
    rw [h] at hlt
    simp at hlt
  refine ⟨by rwa [hinf] at hIrr, ?_⟩
  exact exists_moves_of_commSub_ne_bot (by rw [hI.1]; exact hIne)

theorem a5_irr_classification {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {I : Subgroup W} (hL : IsAlt ↥L 5) (hI : IsIrrOn L I ⊥)
    (hmv : ∃ l ∈ L, ∃ u ∈ I, l u ≠ u) :
    Nat.card ↥I = 16 ∧ (BinaryNaturalSL L I ⊥ 2 2 ∨ AlternatingNatural L I ⊥ 5) := by
  classical
  obtain ⟨φ⟩ := hL
  have hLI : L ≤ stabSub I := B1.le_stabSub_of_invariant hI.2.1
  have hinj : ∀ l ∈ L, (∀ u ∈ I, l u = u) → l = 1 :=
    a5_faithful_of_moves ⟨φ⟩ hI.2.1 hmv
  let ee : ↥(autSub L I) ≃* alternatingGroup (Fin 5) :=
    (FFC.resEquiv hLI hinj).symm.trans φ
  letI : MulDistribMulAction ↥(autSub L I) ↥I :=
    MulDistribMulAction.compHom ↥I (Subgroup.subtype (autSub L I))
  have hIne : I ≠ ⊥ := bot_lt_iff_ne_bot.mp hI.1
  haveI : Nontrivial ↥I := (Subgroup.nontrivial_iff_ne_bot I).mpr hIne
  have hact : ∃ (γ : ↥(autSub L I)) (u : ↥I), γ • u * u⁻¹ ∉ (⊥ : Subgroup ↥I) := by
    obtain ⟨l, hl, u, hu, hlu⟩ := hmv
    have hmem : FFC.resG hLI ⟨l, hl⟩ ∈ autSub L I := by
      rw [FFC.autSub_eq_range hLI]
      exact ⟨⟨l, hl⟩, rfl⟩
    refine ⟨⟨FFC.resG hLI ⟨l, hl⟩, hmem⟩, ⟨u, hu⟩, ?_⟩
    rw [Subgroup.mem_bot]
    intro h
    apply hlu
    have h' : (⟨FFC.resG hLI ⟨l, hl⟩, hmem⟩ : ↥(autSub L I)) • (⟨u, hu⟩ : ↥I) = ⟨u, hu⟩ :=
      mul_inv_eq_one.mp h
    have := congrArg (fun v : ↥I => (v : W)) h'
    simpa [FFC.resG_apply] using this
  have hZne : (⊥ : Subgroup ↥I) ≠ ⊤ := bot_ne_top
  have hirr : ∀ K : Subgroup ↥I, (⊥ : Subgroup ↥I) ≤ K →
      (∀ γ : ↥(autSub L I), ∀ k ∈ K, γ • k ∈ K) → K = ⊥ ∨ K = ⊤ := by
    intro K _ hKinv
    let J : Subgroup W := K.map I.subtype
    have hJle : J ≤ I := Subgroup.map_subtype_le K
    have hJstab : StableUnder L J := by
      intro l hl j hj
      obtain ⟨k, hk, rfl⟩ := hj
      have hmem : FFC.resG hLI ⟨l, hl⟩ ∈ autSub L I := by
        rw [FFC.autSub_eq_range hLI]
        exact ⟨⟨l, hl⟩, rfl⟩
      have hkk : (⟨FFC.resG hLI ⟨l, hl⟩, hmem⟩ : ↥(autSub L I)) • k ∈ K :=
        hKinv ⟨FFC.resG hLI ⟨l, hl⟩, hmem⟩ k hk
      refine ⟨(⟨FFC.resG hLI ⟨l, hl⟩, hmem⟩ : ↥(autSub L I)) • k, hkk, ?_⟩
      simp [FFC.resG_apply]
    rcases hI.2.2.2 J hJstab bot_le hJle with hJ | hJ
    · left
      rw [eq_bot_iff]
      intro k hk
      have : (k : W) ∈ J := ⟨k, hk, rfl⟩
      rw [hJ] at this
      exact Subtype.ext (Subgroup.mem_bot.mp this)
    · right
      rw [eq_top_iff]
      intro k _
      have : (k : W) ∈ J := by rw [hJ]; exact k.2
      obtain ⟨k', hk', hval⟩ := this
      have hkk' : k' = k := Subtype.ext hval
      rwa [hkk'] at hk'
  rcases CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod.plumbing
      (fun a b : ↥I => mul_comm a b)
      (fun u => Subtype.ext (by simpa [pow_two] using hW (u : W))) (⊥ : Subgroup ↥I)
      (fun _ z hz => by rw [Subgroup.mem_bot] at hz; simp [hz]) ee.toMonoidHom ee.surjective
      (fun γ hγ u => by
        rw [Subgroup.mem_bot]
        have hγ1 : γ = 1 := ee.injective (by simpa using hγ)
        rw [hγ1]
        exact mul_inv_cancel u) hirr hZne hact with
    ⟨β, hβs, hβk, -⟩ | ⟨α₂, β, -, -, hβs, hβk, -⟩
  · have hinjβ : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).mp hβk
    have hcardtgt : Nat.card (Multiplicative ↥(CFSG.QuasithinUnique.evenWeight 5)) = 16 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
      decide +kernel
    have hcard16 : Nat.card ↥I = 16 := by
      rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hinjβ, hβs⟩).toEquiv]
      exact hcardtgt
    have hcls := CFSG.QuasithinUnique.B42A57.m5_classification
      (fun s : ↥I => Subtype.ext (by simpa [pow_two] using hW (s : W))) hcard16
      (autSub L I) ee
    rcases hcls with hN | hO
    · exact ⟨hcard16, Or.inl (Thm14_5.binaryNaturalSL_of_autSub hLI hinj hN)⟩
    · exact ⟨hcard16, Or.inr (Thm14_5.realizes_of_autSub hLI hinj hO)⟩
  · have hinjβ : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).mp hβk
    let F4' := CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod.F4
    have hF4 : Nat.card F4' = 4 :=
      CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod.F4.card_F4
    have hcardtgt : Nat.card (Multiplicative (Fin 2 → F4')) = 16 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hF4, Nat.card_fin]
      norm_num
    have hcard16 : Nat.card ↥I = 16 := by
      rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hinjβ, hβs⟩).toEquiv]
      exact hcardtgt
    have hcls := CFSG.QuasithinUnique.B42A57.m5_classification
      (fun s : ↥I => Subtype.ext (by simpa [pow_two] using hW (s : W))) hcard16
      (autSub L I) ee
    rcases hcls with hN | hO
    · exact ⟨hcard16, Or.inl (Thm14_5.binaryNaturalSL_of_autSub hLI hinj hN)⟩
    · exact ⟨hcard16, Or.inr (Thm14_5.realizes_of_autSub hLI hinj hO)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
