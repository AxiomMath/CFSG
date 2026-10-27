module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2LU4Weyl
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeNF
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSuzFaithful

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTorusNoLineTwo_commutator_twF4Eight {p : ℕ} (hp : p.Prime) {G : Type} [Group G]
    (hZG : Subgroup.center G = ⊥) (hs : IsSimpleGroup ↥(commutator G))
    (hna : ∃ a b : ↥(commutator G), a * b ≠ b * a)
    (hpK : ∀ g : G, g ^ p = 1 → g ∈ commutator G)
    (hcp : GGCenterPrime p ↥(commutator G)) (hW : GGSCWeylIrredTwoLU4 p ↥(commutator G)) :
    GGTorusNoLineTwo p ↥(commutator G)
      (Set.range (MulAut.conjNormal : G →* MulAut ↥(commutator G))) := by
  classical
  have hZT : Subgroup.center ↥(commutator G) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(commutator G)) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hna
      have ha : a ∈ Subgroup.center ↥(commutator G) := h ▸ Subgroup.mem_top a
      exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab
  have hC : ∀ c : G, (∀ t ∈ commutator G, c * t = t * c) → c = 1 := fun c hc =>
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.eq_one_of_centralizes_commutator hZG
      (fun n hn hcomm => by
        have hmem : (⟨n, hn⟩ : ↥(commutator G)) ∈ Subgroup.center ↥(commutator G) :=
          Subgroup.mem_center_iff.mpr fun m => Subtype.ext (hcomm m m.2).symm
        rw [hZT, Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem) hc
  refine ggTorusNoLineTwo_of_scWeylIrredTwoLU4 hp hZT ?_ hcp hW
  rintro _ ⟨c, rfl⟩ hcp1
  have hcp' : c ^ p = 1 := by
    refine hC _ fun t ht => ?_
    have h1 := congrArg (fun α : MulAut ↥(commutator G) => ((α ⟨t, ht⟩ : ↥(commutator G)) : G))
      hcp1
    simp only [← map_pow, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc c ^ p * t = c ^ p * t * (c ^ p)⁻¹ * c ^ p := by group
      _ = t * c ^ p := by rw [h1]
  refine ⟨⟨c, hpK c hcp'⟩, ?_⟩
  ext t
  simp [MulAut.conjNormal_apply, MulAut.conj_apply]

theorem ggFixDataTwo_twF4Eight_of_fixSub {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} {f : MulAut R} (hZ : Subgroup.center R = ⊥)
    (hI : ∀ φ ∈ I, φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    {G : Type} [Group G] (ψ : ↥(ggFixSub f) ≃* G) (hZG : Subgroup.center G = ⊥)
    (hs : IsSimpleGroup ↥(commutator G)) (hna : ∃ a b : ↥(commutator G), a * b ≠ b * a)
    (hpK : ∀ g : G, g ^ p = 1 → g ∈ commutator G) (h2 : 2 ∣ Nat.card ↥(commutator G))
    (hcp : GGCenterPrime p ↥(commutator G)) (hW : GGSCWeylIrredTwoLU4 p ↥(commutator G)) :
    GGFixDataTwo p 0 I f := by
  classical
  have hZT : Subgroup.center ↥(commutator G) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(commutator G)) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hna
      have ha : a ∈ Subgroup.center ↥(commutator G) := h ▸ Subgroup.mem_top a
      exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab
  have hC : ∀ c : G, (∀ t ∈ commutator G, c * t = t * c) → c = 1 := fun c hc =>
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.eq_one_of_centralizes_commutator hZG
      (fun n hn hcomm => by
        have hmem : (⟨n, hn⟩ : ↥(commutator G)) ∈ Subgroup.center ↥(commutator G) :=
          Subgroup.mem_center_iff.mpr fun m => Subtype.ext (hcomm m m.2).symm
        rw [hZT, Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem) hc
  have hle : ∀ {g : R}, g ∈ ggFixDer f → g ∈ ggFixSub f := fun hg => ggFixDer_le_ggFixSub f hg
  have hmemK : ∀ (h : R) (hh : h ∈ ggFixSub f), h ∈ ggFixDer f ↔ ψ ⟨h, hh⟩ ∈ commutator G := by
    intro h hh
    have e1 : (commutator ↥(ggFixSub f)).map (ggFixSub f).subtype = ggFixDer f :=
      Subgroup.map_subtype_commutator _
    have e2 : (commutator ↥(ggFixSub f)).map ψ.toMonoidHom = commutator G := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.2 ψ.surjective]
    constructor
    · intro hK
      rw [← e1] at hK
      obtain ⟨s, hs', hseq⟩ := hK
      have hs₁ : s = ⟨h, hh⟩ := Subtype.ext hseq
      subst hs₁
      rw [← e2]
      exact ⟨_, hs', rfl⟩
    · intro hG
      rw [← e2] at hG
      obtain ⟨s, hs', hseq⟩ := hG
      have hs₁ : s = ⟨h, hh⟩ := ψ.injective hseq
      subst hs₁
      rw [← e1]
      exact ⟨_, hs', rfl⟩
  let θ₀ : ↥(ggFixDer f) ≃* ↥(commutator G) :=
    { toFun := fun x => ⟨ψ ⟨x, hle x.2⟩, (hmemK x (hle x.2)).1 x.2⟩
      invFun := fun t => ⟨(ψ.symm t : R), (hmemK _ (ψ.symm t).2).2 (by simp)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun t => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change ψ (⟨x, hle x.2⟩ * ⟨y, hle y.2⟩) = _
        rw [map_mul]
        rfl) }
  have hθ : ∀ x : ↥(ggFixDer f), ((θ₀ x : ↥(commutator G)) : G) = ψ ⟨x, hle x.2⟩ :=
    fun _ => rfl
  have key : ∀ φ ∈ I, φ * f = f * φ → ∃ (r : R) (hr : r ∈ ggFixSub f), φ = MulAut.conj r := by
    intro φ hφI hφ
    obtain ⟨r, rfl⟩ := hI φ hφI
    exact ⟨r, mem_ggFixSub.mpr
      (CFSG.RankThree.PartOne.KE.fixes_of_commute_conj hZ f r hφ.symm), rfl⟩
  have hgeom : GGFixGeom I f (Set.range (MulAut.conjNormal : G →* MulAut ↥(commutator G))) θ₀ := by
    refine ⟨fun φ hφI hφ => ?_, fun φ hφI hφ htriv => ?_⟩
    · obtain ⟨r, hr, rfl⟩ := key φ hφI hφ
      refine ⟨MulAut.conjNormal (ψ ⟨r, hr⟩), ⟨_, rfl⟩, fun g hg => Subtype.ext ?_⟩
      rw [MulAut.conjNormal_apply, hθ, hθ, ← map_inv, ← map_mul, ← map_mul]
      rfl
    · obtain ⟨r, hr, rfl⟩ := key φ hφI hφ
      have hc : ψ ⟨r, hr⟩ = 1 := by
        refine hC _ fun t ht => ?_
        obtain ⟨x, hx⟩ := θ₀.surjective ⟨t, ht⟩
        have ht' : t = ψ ⟨x, hle x.2⟩ := by rw [← hθ, hx]
        have hrx : r * (x : R) = x * r := by
          have h1 : r * x * r⁻¹ = x := htriv x x.2
          calc r * (x : R) = r * x * r⁻¹ * r := by group
            _ = x * r := by rw [h1]
        rw [ht', ← map_mul, ← map_mul]
        exact congrArg ψ (Subtype.ext hrx)
      have hr1 : (⟨r, hr⟩ : ↥(ggFixSub f)) = 1 := ψ.injective (by rw [hc, map_one])
      have hr1' : r = 1 := congrArg Subtype.val hr1
      rw [hr1', map_one]
  exact ⟨↥(commutator G), inferInstance, Set.range MulAut.conjNormal, θ₀, hs, hna, hgeom,
    TypeA.ggTorusLift_zero h2, ggTorusNoLineTwo_commutator_twF4Eight hp hZG hs hna hpK hcp hW⟩

theorem largeEvenLabelAll_fieldKLevelComp_twF4Eight_of_fixDataTwo {p r : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hRK : LargeEvenLabelAll lab (GGNbrWeylRowKnown p r))
    (hcyc : LargeEvenLabelAll lab (GGRawFieldCycW p))
    (hconj : LargeEvenLabelAll lab (GGRawFieldConj p))
    (hcen : LargeEvenLabelAll lab GGRawFieldCentral)
    (hinn : LargeEvenLabelAll lab (GGRawInnField p))
    (hstd : LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ f ∈ F, orderOf f = p → GGFixDataTwo p r I f) :
    LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  have hAll := largeEvenLabelAll_and hRK (largeEvenLabelAll_and hcyc (largeEvenLabelAll_and hconj
    (largeEvenLabelAll_and hcen (largeEvenLabelAll_and hinn hstd))))
  refine largeEvenLabelAll_fieldKLevelComp_of_row hRK (hAll.mono ?_)
  rintro R _ I F ⟨⟨hInn, -, hin⟩, hcy, hc, hce, hi, hst⟩ hs hna
  refine ggTorusFieldTransferTwo hp hInn (hin hs hna) (hcy hs hna) ?_
  intro x hx hxI hxp
  obtain ⟨J, -, hJ, -, -, -, -⟩ := hcy hs hna
  have hnorm := ggRawFieldNorm_of_central hce hi hs hna
  subst hJ
  obtain ⟨u, hu, f, hf, rfl⟩ := ggClosure_union_eq_mul hnorm x hx
  obtain ⟨f', hf', u', hu', hf'p, he⟩ := hc hs hna u hu f hf hxI hxp
  obtain ⟨R₀, _, I₀, θ₀, hs₀, hna₀, hgeom, hlift, hline⟩ := hst hs hna f' hf' hf'p
  rw [he]
  obtain ⟨θ, hθ⟩ := ggFixGeom_conj hu' hgeom
  exact ⟨R₀, inferInstance, I₀, θ, hs₀, hna₀, hθ, hlift, hline⟩

end CFSG.StandardType

end
