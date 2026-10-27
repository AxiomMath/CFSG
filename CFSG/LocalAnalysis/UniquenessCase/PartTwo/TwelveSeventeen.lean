module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFifteen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKbar
import CFSG.LocalAnalysis.UniquenessCase.UC22P22n
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace TwelveSeventeen

theorem preTil_sup (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (S₁ S₂ : Subgroup (Vtil V₀ V hV)) :
    preTil V₀ V hV (S₁ ⊔ S₂) = preTil V₀ V hV S₁ ⊔ preTil V₀ V hV S₂ := by
  unfold preTil
  rw [← Subgroup.comap_sup_eq (mkTil V₀ V hV) S₁ S₂ (mkTil_surjective V₀ V hV), Subgroup.map_sup]

theorem imgTil_bot (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    imgTil V₀ V hV ⊥ = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨x, hx, rfl⟩ := (mem_imgTil V₀ V hV ⊥ q).1 hq
  have h1 : x = 1 := IntMod.val_injective (by rw [IntMod.val_one]; exact mem_bot.1 hx)
  rw [h1, map_one]
  exact one_mem _

theorem mem_preTil_conj {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : M ≤ stabTil V₀ V) {S : Subgroup (Vtil V₀ V hV)}
    (hS : StableUnder (Mbar M V₀ V hV) S) {m g : G} (hm : m ∈ M)
    (hg : g ∈ preTil V₀ V hV S) : m * g * m⁻¹ ∈ preTil V₀ V hV S := by
  obtain ⟨x, rfl, hx⟩ := (mem_preTil V₀ V hV S).1 hg
  have hmV : m * x.val * m⁻¹ ∈ V :=
    (mem_normalizer_iff.1 (stabTil_le_normalizer V₀ V (hMs hm)) x.val).1 x.val_mem
  rw [mem_preTil_iff_of_mem V₀ V hV S hmV]
  have hEq : IntMod.mk hV ⟨m * x.val * m⁻¹, hmV⟩ = actStab V₀ V hV ⟨m, hMs hm⟩ x :=
    IntMod.val_injective (by rw [actStab_apply_val]; rfl)
  rw [hEq, ← actTil_mk]
  exact hS _ (actTil_mem_barSub V₀ V hV hm (hMs hm)) _ hx

theorem le_normalizer_preTil {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : M ≤ stabTil V₀ V) {S : Subgroup (Vtil V₀ V hV)}
    (hS : StableUnder (Mbar M V₀ V hV) S) :
    M ≤ normalizer (preTil V₀ V hV S : Set G) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro g
  refine ⟨fun hg => mem_preTil_conj hV hMs hS hm hg, fun hg => ?_⟩
  have := mem_preTil_conj hV hMs hS (inv_mem hm) hg
  simpa [mul_assoc] using this

theorem inf_centralizer_preTil_le {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h0 : V₀ = ⊥) (hMs : M ≤ stabTil V₀ V) {S : Subgroup (Vtil V₀ V hV)}
    (hS : ∀ y ∈ Mbar M V₀ V hV, (∀ u ∈ S, y u = u) → y = 1) :
    M ⊓ centralizer (preTil V₀ V hV S : Set G) ≤ centralizer (V : Set G) := by
  rintro m ⟨hm, hmc⟩
  have h1 : actTil V₀ V hV ⟨m, hMs hm⟩ = 1 := by
    apply hS _ (actTil_mem_barSub V₀ V hV hm (hMs hm))
    intro u hu
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV u
    have hx : x.val ∈ preTil V₀ V hV S := (mem_preTil V₀ V hV S).2 ⟨x, rfl, hu⟩
    have hxc : m * x.val = x.val * m := ((mem_centralizer_iff.1 hmc) x.val hx).symm
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
    show m * x.val * m⁻¹ * (x.val)⁻¹ ∈ V₀
    rw [hxc, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  rw [mem_centralizer_iff]
  intro v hv
  have h2 : m * v * m⁻¹ * v⁻¹ ∈ V₀ := (actTil_eq_one_iff V₀ V hV ⟨m, hMs hm⟩).1 h1 v hv
  rw [h0, mem_bot] at h2
  have h3 : m * v * m⁻¹ * v⁻¹ = 1 := h2
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3.symm

theorem isIndivisible (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    IsIndivisible (Mbar D.M V₀ V h.isElemAbelian) := by
  intro U₁ U₂ hU₁ hU₂ hU
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hVc : InCalV D.M V := h.inCalV
  have key : ∀ U : Subgroup (Vtil V₀ V h.isElemAbelian),
      StableUnder (Mbar D.M V₀ V h.isElemAbelian) U → preTil V₀ V h.isElemAbelian U ≠ ⊥ →
        InCalV D.M (preTil V₀ V h.isElemAbelian U) := fun U hU hne =>
    ⟨hne, (preTil_le V₀ V h.isElemAbelian U).trans hVc.2.1,
      le_normalizer_preTil h.isElemAbelian hMs hU,
      uc22p22n_isElemAbelian_of_le (preTil_le V₀ V h.isElemAbelian U) hVc.2.2.2⟩
  have htop : ∀ U : Subgroup (Vtil V₀ V h.isElemAbelian),
      V = preTil V₀ V h.isElemAbelian U → U = ⊤ := fun U hUV => by
    rw [← imgTil_preTil V₀ V h.isElemAbelian U, ← hUV, s15_Infra_imgTil_top]
  by_cases h₁ : preTil V₀ V h.isElemAbelian U₁ = ⊥
  · right
    have hb : U₁ = ⊥ := by rw [← imgTil_preTil V₀ V h.isElemAbelian U₁, h₁, imgTil_bot]
    rwa [hb, bot_sup_eq] at hU
  by_cases h₂ : preTil V₀ V h.isElemAbelian U₂ = ⊥
  · left
    have hb : U₂ = ⊥ := by rw [← imgTil_preTil V₀ V h.isElemAbelian U₂, h₂, imgTil_bot]
    rwa [hb, sup_bot_eq] at hU
  have hVsup : V = preTil V₀ V h.isElemAbelian U₁ ⊔ preTil V₀ V h.isElemAbelian U₂ := by
    rw [← preTil_sup, hU, preTil_top]
  rcases twelve_fifteen D hx h61 h127 h1214 h (key U₁ hU₁ h₁) (key U₂ hU₂ h₂) hVsup with he | he
  · exact Or.inl (htop U₁ he)
  · exact Or.inr (htop U₂ he)

theorem eq_top_of_faithful (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (hM1 : Mbar D.M V₀ V h.isElemAbelian ≠ ⊥)
    {U : Subgroup (Vtil V₀ V h.isElemAbelian)}
    (hU : StableUnder (Mbar D.M V₀ V h.isElemAbelian) U)
    (hf : ∀ y ∈ Mbar D.M V₀ V h.isElemAbelian, (∀ u ∈ U, y u = u) → y = 1) : U = ⊤ := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  by_cases h0 : V₀ = ⊥
  · rcases h.1 with ⟨hWs, -⟩ | ⟨h0', -, -⟩
    · have hTI : ¬ CFSG.CGT.Timmesfeld75.IsTI V := (twelve_nine D h127 h).1
      have hW := TwelveFifteen.inCalW_of_le D hx h61 hWs.1 hTI
        (preTil_le V₀ V h.isElemAbelian U) (le_normalizer_preTil h.isElemAbelian hMs hU)
        (inf_centralizer_preTil_le h.isElemAbelian h0 hMs hf)
      have he := hWs.2 _ hW (preTil_le V₀ V h.isElemAbelian U)
      rw [← imgTil_preTil V₀ V h.isElemAbelian U, he, s15_Infra_imgTil_top]
    · exact absurd h0 h0'.1.1
  · rcases s15_Kbar_irreducible h h0 U hU with hb | ht
    · exfalso
      apply hM1
      rw [eq_bot_iff]
      intro y hy
      rw [mem_bot]
      refine hf y hy fun u hu => ?_
      rw [hb, mem_bot] at hu
      rw [hu, map_one]
    · exact ht

theorem isBasicModule (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hM1 : Mbar D.M V₀ V h.isElemAbelian ≠ ⊥) :
    IsBasicModule (Mbar D.M V₀ V h.isElemAbelian) := by
  exact ⟨isIndivisible D hx h61 h127 h1214 h,
    fun _ hU hf => eq_top_of_faithful D hx h61 h127 h hM1 hU hf⟩

end TwelveSeventeen

theorem twelve_seventeen (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (X : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))) (hX1 : X ≠ ⊥)
    (hXM : X ≤ Mbar D.M V₀ V h.isElemAbelian)
    (hXn : (X.subgroupOf (Mbar D.M V₀ V h.isElemAbelian)).Normal)
    (hXs : Odd (Nat.card X) ∨ ∃ K ∈ compBar D.M V₀ V h.isElemAbelian,
      X = ⨆ φ ∈ Mbar D.M V₀ V h.isElemAbelian, K.map (MulAut.conj φ).toMonoidHom) :
    IrrSpanTrans (Mbar D.M V₀ V h.isElemAbelian) X := by
  have hM1 : Mbar D.M V₀ V h.isElemAbelian ≠ ⊥ := fun hb => hX1 (le_bot_iff.1 (hXM.trans hb.le))
  have key := WeakClosure81.w4Lem12_5_holds (Vtil V₀ V h.isElemAbelian)
    (s15_Infra_vtil_sq_eq_one V₀ V h.isElemAbelian)
    (Mbar D.M V₀ V h.isElemAbelian)
    (fun _ hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D h hP hN h2)
    (TwelveSeventeen.isBasicModule D hx h61 h127 h1214 h hM1) X hX1 hXM hXn
  rcases hXs with hodd | ⟨K, hK, hXK⟩
  · exact key.1 hodd
  · exact (key.2 K hK hXK).1

theorem r1217_of_twelve_seventeen (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1214 : F12.R1214 D) : R1217 D := by
  intro V₀ V h X hX1 hXM hXn hXs
  exact (twelve_seventeen D hx h61 h127 h1214 h X hX1 hXM hXn hXs).1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
