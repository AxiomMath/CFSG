module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OuterCyclic
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrder
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
public import CFSG.Quasithin.Vol2.Ch12Sec8OneSix
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Odd
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Semidihedral.Local (map_centralizer_eq_of_coprime)

@[expose] def K_U4RootLine : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), LieModel Y .PSU 4 2 n → 2 < 2 ^ n →
    ∀ r : ℕ, r.Prime → 3 < r → r ∣ 2 ^ n - 1 →
    ∀ E : Subgroup Y, IsElemAbelian r E → Nat.card E = r ^ 2 →
      ∃ B : Subgroup Y, B ≤ E ∧ Nat.card B = r ∧
        (∃ Y₀ : Subgroup Y, Y₀ ≤ Subgroup.centralizer (B : Set Y) ∧ IsL2 ↥Y₀ n) ∧
        ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n + 1 →
          2 ≤ CFSG.Open.pRank p (Subgroup.centralizer (B : Set Y)) ∧
            p ∣ Nat.card (Subgroup.centralizer (E : Set Y))

@[expose] def K_Sp4RootLine : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), LieModel Y .PSp 2 2 n → 2 < 2 ^ n →
    ∀ r : ℕ, r.Prime → 3 < r → r ∣ 2 ^ n - 1 →
    ∀ E : Subgroup Y, IsElemAbelian r E → Nat.card E = r ^ 2 →
      ∃ B : Subgroup Y, B ≤ E ∧ Nat.card B = r ∧
        (∃ Y₀ : Subgroup Y, Y₀ ≤ Subgroup.centralizer (B : Set Y) ∧ IsL2 ↥Y₀ n)

@[expose] def K_G2RootLine : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), LieModel Y .G2 0 2 n → 2 < 2 ^ n →
    ∀ r : ℕ, r.Prime → 3 < r → r ∣ 2 ^ n - 1 →
    ∀ E : Subgroup Y, IsElemAbelian r E → Nat.card E = r ^ 2 →
      ∃ B : Subgroup Y, B ≤ E ∧ Nat.card B = r ∧
        (∃ Y₀ : Subgroup Y, Y₀ ≤ Subgroup.centralizer (B : Set Y) ∧ IsL2 ↥Y₀ n)

theorem exists_rootLine_lift {G : Type} [Group G] [Finite G] {X : Subgroup G} {n r : ℕ}
    (hKU4 : K_U4RootLine) (hKSp4 : K_Sp4RootLine) (hKG2 : K_G2RootLine)
    (hshape : IsU4 (Bar2 X) n ∨ IsSp4 (Bar2 X) n ∨ IsG2 (Bar2 X) n) (hq : 2 < 2 ^ n)
    (hr : r.Prime) (hr3 : 3 < r) (hdvd : r ∣ 2 ^ n - 1)
    {E : Subgroup G} (hEX : E ≤ X) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) :
    ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = r ∧
      (∃ Yt : Subgroup G, Yt ≤ X ⊓ Subgroup.centralizer (B : Set G) ∧
        ∃ N₀ : Subgroup ↥Yt, ∃ _ : N₀.Normal, IsL2 (↥Yt ⧸ N₀) n) ∧
      (IsU4 (Bar2 X) n → ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n + 1 →
        2 ≤ CFSG.Open.pRank p (X ⊓ Subgroup.centralizer (B : Set G)) ∧
          p ∣ Nat.card ↥(X ⊓ Subgroup.centralizer (E : Set G))) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hN2 : IsPGroup 2 (CFSG.pCore 2 ↥X) := CFSG.pCore_isPGroup
  let π : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hπker : π.ker = CFSG.pCore 2 ↥X := QuotientGroup.ker_mk' _
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  let E' : Subgroup ↥X := E.subgroupOf X
  have hE'el : IsElemAbelian r E' := hEel.comap X.subtype_injective
  have hE'card : Nat.card E' = r ^ 2 := by
    rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv
  have hdisj : Disjoint E' (CFSG.pCore 2 ↥X) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
    rw [hE'card, hk]
    have hcop2 : Nat.Coprime r 2 := (Nat.Prime.coprime_iff_not_dvd hr).mpr (by
      rintro h2
      have := Nat.le_of_dvd (by norm_num) h2
      omega)
    exact (hcop2.pow_left 2).pow_right k
  have hĒel : IsElemAbelian r (E'.map π) := CFSG.SectionRank.isElemAbelian_map hE'el π
  have hĒcard : Nat.card (E'.map π) = r ^ 2 := by
    have h1 : Nat.card (E'.map π) = Nat.card E' :=
      CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_map_of_disjoint_ker π E' (by
        rw [hπker]; exact hdisj)
    rw [h1, hE'card]
  have hroot : ∃ Bb : Subgroup (Bar2 X), Bb ≤ E'.map π ∧ Nat.card Bb = r ∧
      (∃ Y₀ : Subgroup (Bar2 X), Y₀ ≤ Subgroup.centralizer (Bb : Set (Bar2 X)) ∧
        IsL2 ↥Y₀ n) ∧
      (IsU4 (Bar2 X) n → ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n + 1 →
        2 ≤ CFSG.Open.pRank p (Subgroup.centralizer (Bb : Set (Bar2 X))) ∧
          p ∣ Nat.card (Subgroup.centralizer (E'.map π : Set (Bar2 X)))) := by
    by_cases hU4 : IsU4 (Bar2 X) n
    · obtain ⟨Bb, hle, hcard, hY, hp⟩ :=
        hKU4 (Bar2 X) n hU4 hq r hr hr3 hdvd (E'.map π) hĒel hĒcard
      exact ⟨Bb, hle, hcard, hY, fun _ => hp⟩
    · have hrest : IsSp4 (Bar2 X) n ∨ IsG2 (Bar2 X) n := by
        rcases hshape with h | h | h
        · exact absurd h hU4
        · exact Or.inl h
        · exact Or.inr h
      rcases hrest with hSp | hG2
      · obtain ⟨Bb, hle, hcard, hY⟩ :=
          hKSp4 (Bar2 X) n hSp hq r hr hr3 hdvd (E'.map π) hĒel hĒcard
        exact ⟨Bb, hle, hcard, hY, fun h => absurd h hU4⟩
      · obtain ⟨Bb, hle, hcard, hY⟩ :=
          hKG2 (Bar2 X) n hG2 hq r hr hr3 hdvd (E'.map π) hĒel hĒcard
        exact ⟨Bb, hle, hcard, hY, fun h => absurd h hU4⟩
  obtain ⟨Bb, hBbE, hBbcard, ⟨Y₀, hY₀le, hY₀L2⟩, hpclause⟩ := hroot
  let B₀ : Subgroup ↥X := Bb.comap π ⊓ E'
  have hB₀le : B₀ ≤ E' := inf_le_right
  have hB₀map : B₀.map π = Bb := by
    refine le_antisymm ?_ ?_
    · calc (Bb.comap π ⊓ E').map π ≤ (Bb.comap π).map π := Subgroup.map_mono inf_le_left
        _ = Bb := Subgroup.map_comap_eq_self_of_surjective hπsurj Bb
    · intro b hb
      obtain ⟨e, he, rfl⟩ := hBbE hb
      exact Subgroup.mem_map.mpr ⟨e, ⟨hb, he⟩, rfl⟩
  have hB₀card : Nat.card B₀ = r := by
    have hd : Disjoint B₀ π.ker := by
      rw [hπker]
      exact Disjoint.mono hB₀le le_rfl hdisj
    have h1 : Nat.card (B₀.map π) = Nat.card B₀ :=
      CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_map_of_disjoint_ker π B₀ hd
    rw [hB₀map, hBbcard] at h1
    exact h1.symm
  let B : Subgroup G := B₀.map X.subtype
  have hBE : B ≤ E := by
    rintro x ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hB₀le hy)
  have hBcard : Nat.card B = r := by
    rw [Subgroup.card_map_of_injective (f := X.subtype) X.subtype_injective, hB₀card]
  have hNcop : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥X) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
    rw [hk]
    intro hdvd
    have h2 : r ∣ 2 := hr.dvd_of_dvd_pow hdvd
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hB₀r : IsPGroup r B₀ := (hE'el.mono hB₀le).isPGroup
  let C : Subgroup ↥X := Subgroup.centralizer (B₀ : Set ↥X)
  have hCmap : C.map π = Subgroup.centralizer (Bb : Set (Bar2 X)) := by
    have h := map_centralizer_eq_of_coprime (p := r) (N := CFSG.pCore 2 ↥X) (G := ↥X)
      hNcop B₀ hB₀r
    simpa [C, π, hB₀map] using h
  let D : Subgroup ↥X := C ⊓ Y₀.comap π
  let ψ : ↥D →* ↥Y₀ := (π.comp D.subtype).codRestrict Y₀ (fun x => x.2.2)
  have hψsurj : Function.Surjective ψ := by
    intro z
    have hz : (z : Bar2 X) ∈ C.map π := by rw [hCmap]; exact hY₀le z.2
    obtain ⟨c, hc, hcz⟩ := hz
    have hcY : c ∈ Y₀.comap π := by rw [Subgroup.mem_comap, hcz]; exact z.2
    exact ⟨⟨c, ⟨hc, hcY⟩⟩, Subtype.ext hcz⟩
  let eD : ↥D ≃* ↥(D.map X.subtype) :=
    Subgroup.equivMapOfInjective D X.subtype X.subtype_injective
  let Yt : Subgroup G := D.map X.subtype
  let φ : ↥Yt →* ↥Y₀ := ψ.comp eD.symm.toMonoidHom
  have hφsurj : Function.Surjective φ := hψsurj.comp eD.symm.surjective
  let N₀ : Subgroup ↥Yt := φ.ker
  have hYtle : Yt ≤ X ⊓ Subgroup.centralizer (B : Set G) := by
    refine le_inf (Subgroup.map_subtype_le D) ?_
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨hxC, -⟩ := hx
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact congrArg Subtype.val (hxC a ha)
  refine ⟨B, hBE, hBcard, ⟨Yt, hYtle, N₀, MonoidHom.normal_ker φ, ?_⟩, ?_⟩
  · have hq1 : ↥Yt ⧸ N₀ ≃* ↥Y₀ := QuotientGroup.quotientKerEquivOfSurjective φ hφsurj
    exact CFSG.Blueprint.LieModel.of_mulEquiv hq1.symm hY₀L2
  · intro hU4 p hp hp2 hpdvd
    have : Fact p.Prime := ⟨hp⟩
    have hpcl := hpclause hU4 p hp hp2 hpdvd
    refine ⟨?_, ?_⟩
    ·
      let f : ↥C →* ↥(C.map π) :=
        (π.comp C.subtype).codRestrict (C.map π) (fun x => Subgroup.mem_map_of_mem π x.2)
      have hf : Function.Surjective f := by
        rintro ⟨y, hy⟩
        obtain ⟨c, hc, rfl⟩ := hy
        exact ⟨⟨c, hc⟩, rfl⟩
      have h1 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(C.map π)) := by
        have h0 : 2 ≤ CFSG.Open.pRank p (C.map π) := by rw [hCmap]; exact hpcl.1
        rwa [← CFSG.Quasithin.pRank_top_subtype] at h0
      have h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥C) :=
        CFSG.Quasithin.H13.L128P.two_le_pRank_of_surjective' hp hp2 f hf h1
      rw [CFSG.Quasithin.pRank_top_subtype] at h2
      have h3 : 2 ≤ CFSG.Open.pRank p (C.map X.subtype) :=
        h2.trans (CFSG.SectionRank.pRank_le_map hp.one_lt X.subtype X.subtype_injective C)
      refine h3.trans (CFSG.SectionRank.pRank_mono hp.one_lt ?_)
      rintro y ⟨x, hx, rfl⟩
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro b hb
      obtain ⟨a, ha, rfl⟩ := hb
      exact congrArg Subtype.val (hx a ha)
    ·
      have hCE : (Subgroup.centralizer (E' : Set ↥X)).map π
          = Subgroup.centralizer (E'.map π : Set (Bar2 X)) := by
        have h := map_centralizer_eq_of_coprime (p := r) (N := CFSG.pCore 2 ↥X) (G := ↥X)
          hNcop E' hE'el.isPGroup
        simpa [π] using h
      have hdiv1 : p ∣ Nat.card (Subgroup.centralizer (E' : Set ↥X)) := by
        have hd := Subgroup.card_map_dvd (H := Subgroup.centralizer (E' : Set ↥X)) (f := π)
        rw [hCE] at hd
        exact hpcl.2.trans hd
      have hEmap : (Subgroup.centralizer (E' : Set ↥X)).map X.subtype
          = X ⊓ Subgroup.centralizer (E : Set G) := by
        ext x
        constructor
        · rintro ⟨c, hc, rfl⟩
          refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
          intro e he
          exact congrArg Subtype.val (hc ⟨e, hEX he⟩ he)
        · rintro ⟨hxX, hx⟩
          refine ⟨⟨x, hxX⟩, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
          intro e' he'
          exact Subtype.ext (hx (e' : G) (Subgroup.mem_subgroupOf.mp he'))
      have hcard : Nat.card ↥(X ⊓ Subgroup.centralizer (E : Set G))
          = Nat.card (Subgroup.centralizer (E' : Set ↥X)) := by
        rw [← hEmap,
          Subgroup.card_map_of_injective (K := Subgroup.centralizer (E' : Set ↥X))
            (f := X.subtype) X.subtype_injective]
      rw [hcard]
      exact hdiv1

theorem center_eq_bot_of_rootLineShape
    {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hq : 2 < 2 ^ n)
    (h : IsU4 Y n ∨ IsSp4 Y n ∨ IsG2 Y n) : Subgroup.center Y = ⊥ := by
  have hn : 1 ≤ n := by
    rcases Nat.lt_or_ge n 1 with h0 | h0
    · interval_cases n
      exact absurd hq (by norm_num)
    · exact h0
  rcases h with hU4 | hSp4 | hG2
  · have hmodel : CFSG.Open.StatedClassicalModel Y .PSU 4 2 n :=
      CFSG.Blueprint.LieModel.statedClassicalModel hU4 (by decide)
    have hord : Nat.card Y = CFSG.Open.ordTwistedA 3 (2 ^ n) :=
      (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.1 rfl
    have h4 : 4 ∣ Nat.card Y := by
      rw [hord]
      obtain ⟨r, -, hm⟩ :=
        (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 3) (g := n)
          (by norm_num) (by omega)).two
      rw [hm]
      refine dvd_mul_of_dvd_left ?_ r
      have h6 : 3 * (3 + 1) / 2 = 6 := by norm_num
      rw [h6]
      simpa using pow_dvd_pow (2 : ℕ) (by omega : 2 ≤ n * 6)
    have : IsSimpleGroup Y :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4
    exact CFSG.Quasithin.H13.center_eq_bot_of_isSimpleGroup_of_four_dvd h4
  · have hmodel : CFSG.Open.StatedClassicalModel Y .PSp 2 2 n :=
      CFSG.Blueprint.LieModel.statedClassicalModel hSp4 (by decide)
    have hord : Nat.card Y = CFSG.Open.ordBC 2 (2 ^ n) :=
      (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.2.1 rfl
    have h4 : 4 ∣ Nat.card Y := by
      rw [hord]
      obtain ⟨r, -, hm⟩ :=
        (CFSG.Timmesfeld.Orders.profile_ordBC (n := 2) (f := n) (by omega)).two
      rw [hm]
      refine dvd_mul_of_dvd_left ?_ r
      have h4' : 2 * 2 = 4 := by norm_num
      rw [h4']
      simpa using pow_dvd_pow (2 : ℕ) (by omega : 2 ≤ n * 4)
    have : IsSimpleGroup Y :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp4
    exact CFSG.Quasithin.H13.center_eq_bot_of_isSimpleGroup_of_four_dvd h4
  · obtain ⟨-, K, hKf, hKfin, -, ⟨e⟩⟩ :=
      CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2 (by decide)
    letI : Field K := hKf
    letI : Finite K := hKfin
    exact CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.center_eq_bot_of_mulEquiv e
      (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.center_adjointQuotient_eq_bot .G2 K)

theorem isCyclic_outer_of_rootLineShape
    {Y : Type} [Group Y] {n : ℕ} (h : IsU4 Y n ∨ IsSp4 Y n ∨ IsG2 Y n) :
    IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) := by
  rcases h with hU4 | hSp4 | hG2
  · exact isCyclic_outer_of_lieModel_PSU4 hU4
  · exact isCyclic_outer_of_lieModel_PSp4 hSp4
  · exact isCyclic_outer_of_lieModel_G2 hG2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
