module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatIrr
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartTwo (altHeart evenWeightPerm)
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct altAct_mk altHeart_endo_eq_zero_or_id)

variable {W : Type} [CommGroup W]

private theorem s16h_constWeight_eq_evenWeightOnes (m : ℕ) :
    CFSG.Quasithin.constWeight m = CFSG.RankThree.PartTwo.evenWeightOnes m := by
  ext x
  rw [CFSG.RankThree.PartTwo.evenWeightOnes, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.mem_zmultiples_iff]
  constructor
  · intro hx
    by_cases hm : Nonempty (Fin m)
    · obtain ⟨i₀⟩ := hm
      refine ⟨((x : Fin m → ZMod 2) i₀).val, funext fun i => ?_⟩
      simp [CFSG.RankThree.PartTwo.allOnes, hx i i₀]
    · refine ⟨0, funext fun i => ?_⟩
      exact absurd ⟨i⟩ hm
  · rintro ⟨k, hk⟩
    have hi : ∀ i, (x : Fin m → ZMod 2) i = (k : ZMod 2) := fun i => by
      rw [← hk]
      simp [CFSG.RankThree.PartTwo.allOnes]
    intro i j
    exact (hi i).trans (hi j).symm

private noncomputable def s16h_heartEquivAlt (m : ℕ) :
    CFSG.Quasithin.AltHeart m ≃+ altHeart m :=
  QuotientAddGroup.quotientAddEquivOfEq (s16h_constWeight_eq_evenWeightOnes m)

private theorem s16h_heartEquivAlt_mk {m : ℕ}
    (x : ↥(CFSG.QuasithinUnique.evenWeight m)) :
    s16h_heartEquivAlt m (QuotientAddGroup.mk x : CFSG.Quasithin.AltHeart m) =
      (QuotientAddGroup.mk x : altHeart m) :=
  QuotientAddGroup.quotientAddEquivOfEq_mk _ x

private theorem s16h_heartEquivAlt_hAct {m : ℕ} (σ : Equiv.Perm (Fin m))
    (y : CFSG.Quasithin.AltHeart m) :
    s16h_heartEquivAlt m (CFSG.Quasithin.C41Pf.AltN.hAct m σ y) =
      altAct σ (s16h_heartEquivAlt m y) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [CFSG.Quasithin.C41Pf.AltN.hAct_mk]
  simp only [s16h_heartEquivAlt_mk, altAct_mk]
  rw [show CFSG.Quasithin.permWeight m σ x =
      evenWeightPerm σ x from Subtype.ext (funext fun _ => rfl)]

private theorem s16h_altHeart5_endo (g : CFSG.Quasithin.AltHeart 5 →+ CFSG.Quasithin.AltHeart 5)
    (hg : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v,
      g (CFSG.Quasithin.C41Pf.AltN.hAct 5 σ v) =
        CFSG.Quasithin.C41Pf.AltN.hAct 5 σ (g v)) :
    g = 0 ∨ g = AddMonoidHom.id _ := by
  let c := s16h_heartEquivAlt 5
  let gR : altHeart 5 →+ altHeart 5 := c.toAddMonoidHom.comp (g.comp c.symm.toAddMonoidHom)
  have hgR : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v, gR (altAct σ v) = altAct σ (gR v) := by
    intro σ hσ v
    have hc : c.symm (altAct σ v) = CFSG.Quasithin.C41Pf.AltN.hAct 5 σ (c.symm v) := by
      apply c.injective
      rw [AddEquiv.apply_symm_apply, s16h_heartEquivAlt_hAct, AddEquiv.apply_symm_apply]
    change c (g (c.symm (altAct σ v))) = altAct σ (c (g (c.symm v)))
    rw [hc, hg σ hσ (c.symm v), s16h_heartEquivAlt_hAct]
  rcases altHeart_endo_eq_zero_or_id (show 5 ≤ 5 by norm_num) gR hgR with h0 | hid
  · left
    apply AddMonoidHom.ext
    intro v
    have h := congrArg (fun h : altHeart 5 →+ altHeart 5 => h (c v)) h0
    change c (g (c.symm (c v))) = 0 at h
    rw [AddEquiv.symm_apply_apply] at h
    exact c.injective (h.trans (map_zero c).symm)
  · right
    apply AddMonoidHom.ext
    intro v
    have h := congrArg (fun h : altHeart 5 →+ altHeart 5 => h (c v)) hid
    change c (g (c.symm (c v))) = c v at h
    rw [AddEquiv.symm_apply_apply] at h
    exact c.injective h

theorem s16h_simpleScalar_alt5 [Finite W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hs : UC22.IsAlt ↥L 5) (h : AlternatingNatural L U Z 5) :
    s16h_SimpleScalar L U Z := by
  have hnat : AlternatingNatural L U Z 5 := h
  obtain ⟨π, hπ⟩ := h
  obtain ⟨hπs, hZU, hkersec, hUinv, hZinv, hsecinv, hkerinv, β, hβs, hβk, hβe⟩ := hπ
  have hshape : SumOfNatShape L U Z 1 := by
    refine ⟨5, Or.inr (Or.inr (Or.inr (Or.inr ⟨hs, ?_⟩)))⟩
    refine ⟨fun _ => U, fun _ => hZU, ?_, ?_, fun _ => hnat⟩
    · intro j
      have hempty : (⨆ (j' : Fin 1) (_ : j' ≠ j), U) = ⊥ := by
        apply iSup_eq_bot.2
        intro j'
        apply iSup_eq_bot.2
        intro hj
        exact (hj (Subsingleton.elim j' j)).elim
      rw [hempty, sup_bot_eq]
      exact inf_le_right
    · have hone : (⨆ _ : Fin 1, U) = U :=
        le_antisymm (iSup_le fun _ => le_rfl) (le_iSup (fun _ : Fin 1 => U) 0)
      rw [hone]
      exact sup_eq_right.2 hZU
  refine ⟨SumOfNatShape.isIrrOn hq hshape, ?_⟩
  intro f hf
  let e : (↥(G6.coreMod 5) ⧸
      ((FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec)) ≃*
      Multiplicative (CFSG.Quasithin.AltHeart 5) :=
    CFSG.Quasithin.C124.altQuotEquiv 5 (by norm_num)
  let β' : ↥U →* Multiplicative (CFSG.Quasithin.AltHeart 5) := e.toMonoidHom.comp β
  have hβ'k : ∀ u : ↥U, β' u = 1 ↔ (u : W) ∈ Z := by
    intro u
    change e (β u) = 1 ↔ (u : W) ∈ Z
    rw [e.map_eq_one_iff, hβk u]
  have hβ'ker : β'.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, hβ'k u, Subgroup.mem_subgroupOf]
  have hβ'surj : Function.Surjective β' := e.surjective.comp hβs
  let βbar : Sec U Z ≃* Multiplicative (CFSG.Quasithin.AltHeart 5) :=
    (QuotientGroup.quotientMulEquivOfEq hβ'ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective β' hβ'surj)
  have hβbar_mk : ∀ u : ↥U, βbar (QuotientGroup.mk u) = β' u := fun u => rfl
  have hβ'e : ∀ (γ : ↥(alternatingGroup (Fin 5))) (u : ↥U)
      (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ U),
      β' ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ =
        Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct 5 (γ : Equiv.Perm (Fin 5))
          (Multiplicative.toAdd (β' u))) := by
    intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hmu : β u = QuotientGroup.mk m := hm.symm
    have hsec : (FFModel.altDn 5).act γ (m : (FFModel.altDn 5).Amb) ∈
        (FFModel.altDn 5).sec := hsecinv γ m m.2
    have h1 := hβe γ u m hu hsec hmu
    change e (β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩) =
      Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct 5 (γ : Equiv.Perm (Fin 5))
        (Multiplicative.toAdd (e (β u))))
    rw [h1, hmu]
    rfl
  have hmembU : ∀ γ : ↥(alternatingGroup (Fin 5)),
      ((π γ : ↥L) : MulAut W) ∈ stabSub U := fun γ =>
    mem_stabSub_of_invariant (hUinv (π γ)) fun u hu => by
      have h := hUinv ((π γ)⁻¹) u hu
      simpa using h
  have hUγ : ∀ γ : ↥(alternatingGroup (Fin 5)),
      resHom U ⟨((π γ : ↥L) : MulAut W), hmembU γ⟩ ∈ stabSub (Z.subgroupOf U) := by
    intro γ
    rw [mem_stabSub]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, resHom_apply]
    constructor
    · intro hx
      have h2 := hZinv ((π γ)⁻¹) _ hx
      simpa using h2
    · intro hx
      exact hZinv (π γ) _ hx
  let gact (γ : ↥(alternatingGroup (Fin 5))) : MulAut (Sec U Z) :=
    quotHom (Z.subgroupOf U) ⟨resHom U ⟨((π γ : ↥L) : MulAut W), hmembU γ⟩, hUγ γ⟩
  have hgact_mem : ∀ γ : ↥(alternatingGroup (Fin 5)), gact γ ∈ autSec L U Z := by
    intro γ
    rw [CFSG.Quasithin.B1Red.mem_autSec_iff]
    exact ⟨⟨((π γ : ↥L) : MulAut W), hmembU γ⟩, (π γ).2, hUγ γ, rfl⟩
  have hβbar_g : ∀ (γ : ↥(alternatingGroup (Fin 5))) (x : Sec U Z),
      βbar (gact γ x) =
        Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct 5 (γ : Equiv.Perm (Fin 5))
          (Multiplicative.toAdd (βbar x))) := by
    intro γ x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : gact γ (QuotientGroup.mk u) =
        QuotientGroup.mk (resHom U ⟨((π γ : ↥L) : MulAut W), hmembU γ⟩ u) := by
      rw [quotHom_mk]
    rw [h1, hβbar_mk, hβbar_mk]
    exact hβ'e γ u (resHom U ⟨((π γ : ↥L) : MulAut W), hmembU γ⟩ u).2
  let gadd : CFSG.Quasithin.AltHeart 5 →+ CFSG.Quasithin.AltHeart 5 :=
    { toFun := fun v => Multiplicative.toAdd (βbar (f (βbar.symm (Multiplicative.ofAdd v))))
      map_zero' := by
        change Multiplicative.toAdd (βbar (f (βbar.symm (Multiplicative.ofAdd 0)))) = 0
        rw [ofAdd_zero, map_one, map_one, map_one, toAdd_one]
      map_add' := fun v w => by
        simp only [ofAdd_add, map_mul, toAdd_mul] }
  have hgadd : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v,
      gadd (CFSG.Quasithin.C41Pf.AltN.hAct 5 σ v) =
        CFSG.Quasithin.C41Pf.AltN.hAct 5 σ (gadd v) := by
    intro σ hσ v
    obtain ⟨u, hu⟩ : ∃ u : ↥U, βbar (QuotientGroup.mk u) = Multiplicative.ofAdd v := by
      obtain ⟨x, hx⟩ := βbar.surjective (Multiplicative.ofAdd v)
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨u, hx⟩
    have hu' : QuotientGroup.mk u = βbar.symm (Multiplicative.ofAdd v) := by
      rw [← hu, MulEquiv.symm_apply_apply]
    have h1 : βbar (gact ⟨σ, hσ⟩ (QuotientGroup.mk u)) =
        Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct 5 σ v) := by
      have hh := hβbar_g ⟨σ, hσ⟩ (QuotientGroup.mk u)
      rw [hu, toAdd_ofAdd] at hh
      exact hh
    have h2 : βbar.symm (Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct 5 σ v)) =
        gact ⟨σ, hσ⟩ (QuotientGroup.mk u) := by
      rw [← h1, MulEquiv.symm_apply_apply]
    have h3 : βbar (f (βbar.symm (Multiplicative.ofAdd v))) =
        Multiplicative.ofAdd (gadd v) := by
      change βbar (f (βbar.symm (Multiplicative.ofAdd v))) = Multiplicative.ofAdd
        (Multiplicative.toAdd (βbar (f (βbar.symm (Multiplicative.ofAdd v)))))
      rw [ofAdd_toAdd]
    have h4 : Multiplicative.toAdd (βbar (f (QuotientGroup.mk u))) = gadd v := by
      rw [hu', h3, toAdd_ofAdd]
    change Multiplicative.toAdd (βbar (f (βbar.symm (Multiplicative.ofAdd
        (CFSG.Quasithin.C41Pf.AltN.hAct 5 σ v))))) =
      CFSG.Quasithin.C41Pf.AltN.hAct 5 σ (Multiplicative.toAdd
        (βbar (f (βbar.symm (Multiplicative.ofAdd v)))))
    rw [h2, hf (gact ⟨σ, hσ⟩) (hgact_mem ⟨σ, hσ⟩)]
    rw [h3, hβbar_g ⟨σ, hσ⟩ (f (QuotientGroup.mk u)), h4]
    simp only [toAdd_ofAdd]
  rcases s16h_altHeart5_endo gadd hgadd with hg0 | hgid
  · left
    apply MonoidHom.ext
    intro x
    change f x = 1
    have h : Multiplicative.toAdd (βbar (f x)) = 0 := by
      have h := congrArg (fun g : CFSG.Quasithin.AltHeart 5 →+ CFSG.Quasithin.AltHeart 5 =>
        g (Multiplicative.toAdd (βbar x))) hg0
      change Multiplicative.toAdd (βbar (f (βbar.symm (Multiplicative.ofAdd
        (Multiplicative.toAdd (βbar x)))))) = 0 at h
      rwa [ofAdd_toAdd, MulEquiv.symm_apply_apply] at h
    have h2 : βbar (f x) = 1 := Multiplicative.toAdd.injective (h.trans toAdd_one.symm)
    exact βbar.injective (by rw [map_one]; exact h2)
  · right
    apply MonoidHom.ext
    intro x
    have h : Multiplicative.toAdd (βbar (f x)) = Multiplicative.toAdd (βbar x) := by
      have h := congrArg (fun g : CFSG.Quasithin.AltHeart 5 →+ CFSG.Quasithin.AltHeart 5 =>
        g (Multiplicative.toAdd (βbar x))) hgid
      change Multiplicative.toAdd (βbar (f (βbar.symm (Multiplicative.ofAdd
        (Multiplicative.toAdd (βbar x)))))) = Multiplicative.toAdd (βbar x) at h
      rwa [ofAdd_toAdd, MulEquiv.symm_apply_apply] at h
    exact βbar.injective (Multiplicative.toAdd.injective h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
