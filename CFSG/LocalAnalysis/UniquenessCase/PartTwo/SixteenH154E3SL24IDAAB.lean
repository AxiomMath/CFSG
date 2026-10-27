module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24CoverCA
public import CFSG.Milestones.ASVolI.I2Natural
public import CFSG.Quasithin.H13.VolII16Restrict
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Rows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Table

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Open Subgroup CFSG.ASVolI CFSG.ASVolI.ChIJK

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_sl24_mk_eq_iff {K : Type} [Field K]
    (a b : ↥(i23NaturalModel 1 K).sec) :
    (QuotientGroup.mk a : ↥(i23NaturalModel 1 K).sec ⧸
      (i23NaturalModel 1 K).ker.subgroupOf (i23NaturalModel 1 K).sec) =
      QuotientGroup.mk b ↔ a = b := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  show ((a⁻¹ * b : ↥(i23NaturalModel 1 K).sec) : (i23NaturalModel 1 K).Amb) ∈
    (⊥ : Subgroup (i23NaturalModel 1 K).Amb) ↔ a = b
  rw [Subgroup.mem_bot, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_one]
  exact Subtype.ext_iff.symm

theorem s16h_sl24_i23SectionMap_of_coord {K : Type} [Field K] {L : Subgroup (MulAut W)}
    (hU : ∀ l ∈ L, ∀ u ∈ commSub ⊤ L, l u ∈ commSub ⊤ L)
    {π : ↥(StatedSL 2 K) →* ↥L}
    {β : ↥(commSub ⊤ L) →* StdMod (Fin 2) K}
    (hπ : Function.Surjective π) (hβs : Function.Surjective β)
    (hβk : β.ker = (commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L))
    (hβe : ∀ (γ : ↥(StatedSL 2 K)) (u : ↥(commSub ⊤ L))
      (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ commSub ⊤ L),
      β ⟨_, hu⟩ = natAct (StatedSL 2 K) γ (β u)) :
    ∃ (β' : ↥(commSub ⊤ L) →* ↥(i23NaturalModel 1 K).sec ⧸
        (i23NaturalModel 1 K).ker.subgroupOf (i23NaturalModel 1 K).sec),
      Function.Surjective β' ∧
      I23SectionMap (i23NaturalModel 1 K)
        ((CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).range)
        ((commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L))
        ((CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).rangeRestrict.comp π) β' := by
  classical
  let L' : Subgroup (MulAut ↥(commSub ⊤ L)) :=
    (CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).range
  let mark : ↥(StatedSL 2 K) →* ↥L' :=
    (CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).rangeRestrict.comp π
  let φ : ↥(commSub ⊤ L) →* ↥(i23NaturalModel 1 K).sec :=
    { toFun := fun u => ⟨β u, Subgroup.mem_top _⟩
      map_one' := by apply Subtype.ext; exact map_one β
      map_mul' := fun a b => by apply Subtype.ext; exact map_mul β a b }
  let β' : ↥(commSub ⊤ L) →* ↥(i23NaturalModel 1 K).sec ⧸
      (i23NaturalModel 1 K).ker.subgroupOf (i23NaturalModel 1 K).sec :=
    (QuotientGroup.mk' _).comp φ
  have hβ'val : ∀ u : ↥(commSub ⊤ L), β' u = QuotientGroup.mk (φ u) := fun u => rfl
  have hφval : ∀ u : ↥(commSub ⊤ L),
      ((φ u : ↥(i23NaturalModel 1 K).sec) : (i23NaturalModel 1 K).Amb) = β u := fun u => rfl
  have hsurj : Function.Surjective β' := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective y
    obtain ⟨u, hu⟩ := hβs (x : (i23NaturalModel 1 K).Amb)
    refine ⟨u, ?_⟩
    rw [hβ'val, ← hx]
    congr 1
    exact Subtype.ext hu
  have hker' : β'.ker = (commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L) := by
    ext u
    rw [MonoidHom.mem_ker, hβ'val, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      show (i23NaturalModel 1 K).ker = ⊥ from rfl, Subgroup.mem_bot]
    change (β u : (i23NaturalModel 1 K).Amb) = 1 ↔
      u ∈ (commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L)
    rw [← MonoidHom.mem_ker, hβk]
  have hsecstab : ∀ (γ : (i23NaturalModel 1 K).Gam) (v : (i23NaturalModel 1 K).Amb),
      v ∈ (i23NaturalModel 1 K).sec → (i23NaturalModel 1 K).act γ v ∈
        (i23NaturalModel 1 K).sec := fun γ v _ => Subgroup.mem_top _
  have hkerstab : ∀ (γ : (i23NaturalModel 1 K).Gam) (v : (i23NaturalModel 1 K).Amb),
      v ∈ (i23NaturalModel 1 K).ker → (i23NaturalModel 1 K).act γ v ∈
        (i23NaturalModel 1 K).ker := by
    intro γ v hv
    rw [show (i23NaturalModel 1 K).ker = ⊥ from rfl, Subgroup.mem_bot] at hv ⊢
    subst hv
    show natAct (StatedSL 2 K) γ 1 = 1
    simp [natAct]
  have hequi : ∀ (γ : (i23NaturalModel 1 K).Gam) (vector : ↥(commSub ⊤ L))
      (native : ↥(i23NaturalModel 1 K).sec)
      (hNative : (i23NaturalModel 1 K).act γ (native : (i23NaturalModel 1 K).Amb) ∈
        (i23NaturalModel 1 K).sec),
      β' vector = QuotientGroup.mk native →
        β' ((mark γ : MulAut ↥(commSub ⊤ L)) vector) = QuotientGroup.mk
          ⟨(i23NaturalModel 1 K).act γ (native : (i23NaturalModel 1 K).Amb), hNative⟩ := by
    intro γ vector native hNative hqv
    rw [hβ'val] at hqv ⊢
    rw [s16h_sl24_mk_eq_iff] at hqv ⊢
    have hval : (native : (i23NaturalModel 1 K).Amb) = β vector :=
      (congrArg Subtype.val hqv).symm.trans (hφval vector)
    have hmem : ((π γ : ↥L) : MulAut W) (vector : W) ∈ commSub ⊤ L :=
      hU (π γ) (π γ).2 (vector : W) vector.2
    have hmark : (mark γ : MulAut ↥(commSub ⊤ L)) vector =
        ⟨((π γ : ↥L) : MulAut W) (vector : W), hmem⟩ := Subtype.ext rfl
    rw [hmark]
    apply Subtype.ext
    show β ⟨_, hmem⟩ = (i23NaturalModel 1 K).act γ (native : (i23NaturalModel 1 K).Amb)
    rw [hβe γ vector hmem, hval]
    rfl
  have hmarksurj : Function.Surjective mark :=
    (MonoidHom.rangeRestrict_surjective
      (CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU)).comp hπ
  exact ⟨β', hsurj, hmarksurj, hsurj, hker', bot_le, hsecstab, hkerstab, hequi⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
