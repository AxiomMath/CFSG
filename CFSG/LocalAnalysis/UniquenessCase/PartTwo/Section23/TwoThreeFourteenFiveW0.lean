module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeCaseB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeTransportModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem imgTil_map_conj {A W : Subgroup G} (hA : IsElemAbelian 2 A) (hWA : W ≤ A)
    {g : G} (hg : g ∈ stabTil (⊥ : Subgroup G) A) :
    imgTil (⊥ : Subgroup G) A hA (W.map (MulAut.conj g).toMonoidHom) =
      (imgTil (⊥ : Subgroup G) A hA W).map
        (actTil (⊥ : Subgroup G) A hA ⟨g, hg⟩).toMonoidHom := by
  ext q
  rw [mem_imgTil, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨w, hw, hval⟩ := Subgroup.mem_map.1 ha
    refine ⟨mkTil (⊥ : Subgroup G) A hA (IntMod.mk hA ⟨w, hWA hw⟩), ?_, ?_⟩
    · exact (mem_imgTil (⊥ : Subgroup G) A hA W _).2
        ⟨IntMod.mk hA ⟨w, hWA hw⟩, hw, rfl⟩
    · change actTil (⊥ : Subgroup G) A hA ⟨g, hg⟩
          (mkTil (⊥ : Subgroup G) A hA (IntMod.mk hA ⟨w, hWA hw⟩)) = mkTil (⊥) A hA a
      rw [actTil_mk]
      congr 1
      apply IntMod.val_injective
      rw [actStab_apply_val]
      simpa [MulAut.conj_apply, IntMod.mk, IntMod.val] using hval
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_imgTil (⊥ : Subgroup G) A hA W y).1 hy
    refine (mem_imgTil (⊥ : Subgroup G) A hA
      (W.map (MulAut.conj g).toMonoidHom) _).2
      ⟨actStab (⊥ : Subgroup G) A hA ⟨g, hg⟩ x, ?_, ?_⟩
    · rw [actStab_apply_val]
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    · change mkTil (⊥ : Subgroup G) A hA
          (actStab (⊥ : Subgroup G) A hA ⟨g, hg⟩ x) =
        actTil (⊥ : Subgroup G) A hA ⟨g, hg⟩ (mkTil (⊥ : Subgroup G) A hA x)
      exact (actTil_mk (⊥ : Subgroup G) A hA ⟨g, hg⟩ x).symm

theorem imgTil_conjClosure_le_iSup {A S H : Subgroup G} (hA : IsElemAbelian 2 A)
    (hS : S ≤ A) (hH : H ≤ Subgroup.normalizer (A : Set G)) :
    (⨆ k ∈ barSub (⊥ : Subgroup G) A hA H,
        (imgTil (⊥ : Subgroup G) A hA S).map
          (k : MulAut (Vtil (⊥ : Subgroup G) A hA)).toMonoidHom) ≤
      imgTil (⊥ : Subgroup G) A hA (conjClosure H S) := by
  refine iSup₂_le fun k hk => ?_
  obtain ⟨g, hgH, hk⟩ := (mem_barSub (⊥ : Subgroup G) A hA H k).1 hk
  rw [← hk, ← imgTil_map_conj hA hS g.2]
  refine Subgroup.map_mono (Subgroup.subgroupOf_mono A ?_)
  intro x hx
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hx
  exact (le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf H S) => K)
    (S.map (MulAut.conj (g : G)).toMonoidHom) ⟨(g : G), hgH, rfl⟩ le_rfl)
    (Subgroup.mem_map_of_mem _ hs)

theorem imgTil_conjClosure_ge_iSup {A S H : Subgroup G} (hA : IsElemAbelian 2 A)
    (hS : S ≤ A) (hH : H ≤ Subgroup.normalizer (A : Set G)) :
    imgTil (⊥ : Subgroup G) A hA (conjClosure H S) ≤
      ⨆ k ∈ barSub (⊥ : Subgroup G) A hA H,
        (imgTil (⊥ : Subgroup G) A hA S).map
          (k : MulAut (Vtil (⊥ : Subgroup G) A hA)).toMonoidHom := by
  rw [imgTil, Subgroup.map_le_iff_le_comap]
  let P : Subgroup (IntMod A hA) :=
    (⨆ k ∈ barSub (⊥ : Subgroup G) A hA H,
      (imgTil (⊥ : Subgroup G) A hA S).map
        (k : MulAut (Vtil (⊥ : Subgroup G) A hA)).toMonoidHom).comap
      (mkTil (⊥ : Subgroup G) A hA)
  have hUP : conjClosure H S ≤ P.map (valHom A hA) := by
    rw [← quasithin_conjClosure_eq, Quasithin.conjClosure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨h, hh, s, hs, rfl⟩
    have hmemA : h * s * h⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hH hh) s).1 (hS hs)
    refine Subgroup.mem_map.mpr ⟨IntMod.mk hA ⟨h * s * h⁻¹, hmemA⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hstab : h ∈ stabTil (⊥ : Subgroup G) A :=
      Subgroup.mem_inf.mpr
        ⟨hH hh, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top h⟩
    have heq : mkTil (⊥ : Subgroup G) A hA (IntMod.mk hA ⟨h * s * h⁻¹, hmemA⟩) =
        actTil (⊥ : Subgroup G) A hA ⟨h, hstab⟩
          (mkTil (⊥ : Subgroup G) A hA (IntMod.mk hA ⟨s, hS hs⟩)) := by
      rw [actTil_mk]
      congr 1
    rw [heq]
    exact (le_iSup₂_of_le (f := fun k (_ : k ∈ barSub (⊥ : Subgroup G) A hA H) =>
        (imgTil (⊥ : Subgroup G) A hA S).map
          (k : MulAut (Vtil (⊥ : Subgroup G) A hA)).toMonoidHom)
      (actTil (⊥ : Subgroup G) A hA ⟨h, hstab⟩)
      ((mem_barSub (⊥ : Subgroup G) A hA H _).2 ⟨⟨h, hstab⟩, hh, rfl⟩) le_rfl)
      (Subgroup.mem_map_of_mem (actTil (⊥ : Subgroup G) A hA ⟨h, hstab⟩).toMonoidHom
        ((mem_imgTil (⊥ : Subgroup G) A hA S _).2
          ⟨IntMod.mk hA ⟨s, hS hs⟩, hs, rfl⟩))
  change (conjClosure H S).comap (valHom A hA) ≤ P
  calc (conjClosure H S).comap (valHom A hA)
      ≤ (P.map (valHom A hA)).comap (valHom A hA) := Subgroup.comap_mono hUP
    _ = P := Subgroup.comap_map_eq_self_of_injective
      (fun _ _ h => IntMod.val_injective h) P

theorem imgTil_conjClosure_eq_iSup {A S H : Subgroup G} (hA : IsElemAbelian 2 A)
    (hS : S ≤ A) (hH : H ≤ Subgroup.normalizer (A : Set G))
    {K : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))}
    (hK : K = barSub (⊥ : Subgroup G) A hA H)
    {W₀ : Subgroup (Vtil (⊥ : Subgroup G) A hA)}
    (hW₀ : W₀ = ⨆ k ∈ K, (imgTil (⊥ : Subgroup G) A hA S).map
      (k : MulAut (Vtil (⊥ : Subgroup G) A hA)).toMonoidHom) :
    W₀ = imgTil (⊥ : Subgroup G) A hA (conjClosure H S) := by
  subst hK hW₀
  exact le_antisymm (imgTil_conjClosure_le_iSup hA hS hH)
    (imgTil_conjClosure_ge_iSup hA hS hH)

theorem iSup_map_conj_eq_self {A H T : Subgroup G} (hA : IsElemAbelian 2 A)
    (hH : H ≤ stabTil (⊥ : Subgroup G) A) (hT : T ≤ stabTil (⊥ : Subgroup G) A)
    (hTH : T ≤ Subgroup.normalizer (H : Set G)) :
    (⨆ t ∈ barSub (⊥ : Subgroup G) A hA T,
        (barSub (⊥ : Subgroup G) A hA H).map (MulAut.conj t).toMonoidHom) =
      barSub (⊥ : Subgroup G) A hA H := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun t ht => ?_
    obtain ⟨g, hgT, ht⟩ := (mem_barSub (⊥ : Subgroup G) A hA T t).1 ht
    rw [← ht, ← TwelveTwentyThree.barSub_map_conj hA hH g.2,
      CFSG.Timmesfeld.RankOne.map_conj_eq_self_iff.mpr (hTH hgT)]
  · refine le_iSup₂_of_le (f := fun t (_ : t ∈ barSub (⊥ : Subgroup G) A hA T) =>
        (barSub (⊥ : Subgroup G) A hA H).map (MulAut.conj t).toMonoidHom)
      (1 : MulAut (Vtil (⊥ : Subgroup G) A hA))
      ((barSub (⊥ : Subgroup G) A hA T).one_mem) ?_
    apply le_of_eq
    ext x
    simp [MulAut.conj_apply]

theorem Hinf_barSub_eq {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A P : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hPL : P ≤ c.L)
    (hL0P : c.L0 = Hinf P) :
    Hinf (barSub (⊥ : Subgroup G) A hA P) =
      barSub (⊥ : Subgroup G) A hA c.L0 := by
  rw [Ctx23L.Hinf_barSub c hA hAN hPL, hL0P]

end CFSG.LocalAnalysis.UniquenessCase.UC22
