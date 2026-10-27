module

public import CFSG.Sporadic.Fi22.LH.Transport
public import CFSG.Fischer.Uniq.F24Hyperoval

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

theorem IsLocally351.conj
    (hP : Pair X E) (g : X) {T : Set X} (hT : IsLocally351 E T) :
    IsLocally351 E ((fun x => g * x * g⁻¹) '' T) := by
  have hstar : ∀ s, (fun x => g * x * g⁻¹) '' T ∩ LocalClass E (g * s * g⁻¹) =
      (fun x => g * x * g⁻¹) '' (T ∩ LocalClass E s) := by
    intro s
    rw [image_conj_inter, Pair.image_conj_localClass hP]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Pair.conj_mem hP (hT.subset hx) g
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    exact ⟨s * t * s, hT.closed s hs t ht, by group⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [hstar]
    exact (hT.nonempty s hs).image _
  · rintro _ ⟨s, hs, rfl⟩
    rw [hstar, ← imgIn_starConjEquiv hP g s (U := T ∩ LocalClass E s) Set.inter_subset_right]
    refine (hT.locally s hs).transport (starConjEquiv hP g s)
      (fun x y => (conj_commute_iff g x y).symm) (fun x y => ?_) fun x hx => Pair.mul_self hP hx.1
    refine ⟨LocalPoints.mul_mul_mem_localClass hP x y, ?_⟩
    simp only [starConjEquiv_val]
    group

theorem IsLocally351.not_star_muSet
    (hHF : HyperovalFacts) (hF : F22 Y F) (hE : Pair X E)
    (hloc : ∀ f ∈ E, Nonempty (LocalPoints (pairModel hF.1) E f)) {T : Set X}
    (hT : IsLocally351 E T) {d c : X} (hdT : d ∈ T) (hc : c ∈ E) (hcd : d * c ≠ c * d)
    (hstar : T ∩ LocalClass E d = LocalClass E d ∩ LocalClass E c) : False := by
  have hdE : d ∈ E := hT.subset hdT
  obtain ⟨t, htT, htd⟩ := hT.nonempty d hdT
  have htc : t ∈ LocalClass E c := by
    have h : t ∈ T ∩ LocalClass E d := ⟨htT, htd⟩
    rw [hstar] at h
    exact h.2
  obtain ⟨t', ⟨ht'T, ht'd⟩, ht't⟩ := (hT.locally d hdT).nonempty t ⟨htT, htd⟩
  have ht'c : t' ∈ LocalClass E c := by
    have h : t' ∈ T ∩ LocalClass E d := ⟨ht'T, ht'd⟩
    rw [hstar] at h
    exact h.2
  have hdt : d ∈ LocalClass E t := ⟨hdE, fun h => htd.2.1 h.symm, htd.2.2.symm⟩
  have hct : c ∈ LocalClass E t := ⟨hc, fun h => htc.2.1 h.symm, htc.2.2.symm⟩
  have ht't' : t' ∈ LocalClass E t := ⟨ht't.1.1, ht't.2.1, ht't.2.2⟩
  obtain ⟨Lt⟩ := hloc t htd.1
  have hV := (hT.locally t htT).transport Lt.χ Lt.comm
    (fun x y => ⟨LocalPoints.mul_mul_mem_localClass hE x y, congrArg Subtype.val (Lt.tau x y _)⟩)
    fun x hx => Pair.mul_self hE hx.1
  set V : Set X := T ∩ LocalClass E t
  set s' : Y := (Lt.χ ⟨t', ht't'⟩ : Y)
  have hs'V : s' ∈ imgIn Lt.χ V := ⟨⟨t', ht't'⟩, ⟨ht'T, ht't'⟩, rfl⟩
  have hW := hV.hyperoval s' hs'V
  obtain ⟨Lp⟩ := F22.nonempty_localPoints hF (Lt.χ ⟨t', ht't'⟩).2
  have hdt' : (d : X) ∈ LocalClass E t' := ⟨hdE, fun h => ht'd.2.1 h.symm, ht'd.2.2.symm⟩
  have hct' : (c : X) ∈ LocalClass E t' := ⟨hc, fun h => ht'c.2.1 h.symm, ht'c.2.2.symm⟩
  have hpW : (Lt.χ ⟨d, hdt⟩ : Y) ∈ imgIn Lt.χ V ∩ LocalClass F s' :=
    ⟨⟨⟨d, hdt⟩, ⟨hdT, hdt⟩, rfl⟩,
      (Lt.mem_localClass_iff hF.1 ⟨t', ht't'⟩ ⟨d, hdt⟩).1 hdt'⟩
  have hq : (Lt.χ ⟨c, hct⟩ : Y) ∈ LocalClass F s' :=
    (Lt.mem_localClass_iff hF.1 ⟨t', ht't'⟩ ⟨c, hct⟩).1 hct'
  have hpq : (Lt.χ ⟨d, hdt⟩ : Y) * Lt.χ ⟨c, hct⟩ ≠ Lt.χ ⟨c, hct⟩ * Lt.χ ⟨d, hdt⟩ :=
    fun h => hcd ((Lt.comm ⟨d, hdt⟩ ⟨c, hct⟩).2 h)
  apply IsHyperovalIn.not_linear hHF hF.1 Lp hW hpW hq hpq
  intro x hxs hxp
  obtain ⟨y, hy⟩ := Lt.χ.surjective ⟨x, hxs.1⟩
  have hxy : x = (Lt.χ y : Y) := by rw [hy]
  rw [hxy] at hxp ⊢
  have hyd : (y : X) ∈ LocalClass E d := (Lt.mem_localClass_iff hF.1 ⟨d, hdt⟩ y).2 hxp
  have hyt' : (y : X) ∈ LocalClass E t' := by
    rw [hxy] at hxs
    exact (Lt.mem_localClass_iff hF.1 ⟨t', ht't'⟩ y).2 hxs
  have hmem : (Lt.χ y : Y) ∈ imgIn Lt.χ V ∩ LocalClass F s' ↔ (y : X) ∈ T := by
    rw [Set.mem_inter_iff, val_mem_imgIn_iff]
    constructor
    · rintro ⟨h, -⟩
      exact h.1
    · intro h
      exact ⟨⟨h, y.2⟩, (Lt.mem_localClass_iff hF.1 ⟨t', ht't'⟩ y).1 hyt'⟩
  rw [hmem]
  have hTd : (y : X) ∈ T ↔ (y : X) ∈ LocalClass E c := by
    constructor
    · intro h
      have h' : (y : X) ∈ T ∩ LocalClass E d := ⟨h, hyd⟩
      rw [hstar] at h'
      exact h'.2
    · intro h
      have h' : (y : X) ∈ LocalClass E d ∩ LocalClass E c := ⟨hyd, h⟩
      rw [← hstar] at h'
      exact h'.1
  refine hTd.trans (Iff.trans ?_ (Lt.comm y ⟨c, hct⟩))
  constructor
  · exact fun h => h.2.2
  · intro h
    refine ⟨y.2.1, fun e => hcd ?_, h⟩
    rw [← e]
    exact hyd.2.2.symm

end CFSG.Fischer
