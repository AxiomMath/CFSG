module

public import CFSG.RankThree.PartOne.HESS.NoSwap
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.RankThree.PartOne.HESS

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartOne.N143
open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor rt permSL IsZeta diagSL tSep)

section Act

variable {G : Type} [Group G]

theorem conjBy_mul' (g h : G) (S : Subgroup G) : conjBy (g * h) S = conjBy g (conjBy h S) := by
  ext x
  rw [Equivariance.mem_conjBy, Equivariance.mem_conjBy, Equivariance.mem_conjBy]
  simp [mul_assoc]

theorem conjBy_one' (S : Subgroup G) : conjBy (1 : G) S = S := by
  ext x
  rw [Equivariance.mem_conjBy]
  simp

variable [Finite G]

omit [Finite G] in
theorem actPair_mul {A : Subgroup G} {g h : G} (hg : g ∈ torusNormalizer A)
    (hh : h ∈ torusNormalizer A) (r : MulAut A × Subgroup G) :
    actPair A (g * h) r = actPair A g (actPair A h r) := by
  unfold actPair
  rw [piAut_mul hg hh, conjBy_mul']
  refine Prod.ext ?_ rfl
  show piAut A g * piAut A h * r.1 * (piAut A g * piAut A h)⁻¹ =
    piAut A g * (piAut A h * r.1 * (piAut A h)⁻¹) * (piAut A g)⁻¹
  group

omit [Finite G] in
theorem actPair_one (A : Subgroup G) (r : MulAut A × Subgroup G) : actPair A 1 r = r := by
  unfold actPair
  rw [piAut_one, conjBy_one']
  refine Prod.ext ?_ rfl
  show 1 * r.1 * (1 : MulAut A)⁻¹ = r.1
  group

end Act

section Tbar

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G} {f : ℕ}
  {P : Subgroup (MulAut A)} {z : MulAut A}

@[expose] def Tbar (A : Subgroup G) (P : Subgroup (MulAut A)) : Subgroup G where
  carrier := {g | g ∈ torusNormalizer A ∧ piAut A g ∈ P}
  mul_mem' := fun {g h} hg hh =>
    ⟨(torusNormalizer A).mul_mem hg.1 hh.1, by rw [piAut_mul hg.1 hh.1]; exact P.mul_mem hg.2 hh.2⟩
  one_mem' := ⟨(torusNormalizer A).one_mem, by rw [piAut_one]; exact P.one_mem⟩
  inv_mem' := fun {g} hg =>
    ⟨(torusNormalizer A).inv_mem hg.1, by rw [piAut_inv hg.1]; exact P.inv_mem hg.2⟩

omit [Finite G] in
theorem mem_Tbar {g : G} : g ∈ Tbar A P ↔ g ∈ torusNormalizer A ∧ piAut A g ∈ P := Iff.rfl

theorem HessSetup.cube_of_mem_Tbar (hS : HessSetup p A c L f P z) {g : G} (hg : g ∈ Tbar A P) :
    piAut A g ^ 3 = 1 := by
  have hX : piAut A g ∈ reflectionGroup p A := hS.spec.P_le hg.2
  exact (hS.spec.mem_P _ hX).1 hg.2

theorem HessSetup.fixes_roots_tbar (hS : HessSetup p A c L f P z) {g : G} (hg : g ∈ Tbar A P)
    {t : MulAut A} (ht : t ∈ reflectionSet p A) (hfix : piAut A g * t * (piAut A g)⁻¹ = t)
    {S : Subgroup G} (hSr : S ∈ RootSet A f p t) : conjBy g S = S :=
  hS.fixes_roots hg.1 (hS.cube_of_mem_Tbar hg) ht hfix hSr

end Tbar

section Rot

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G} {L : Subgroup G} {f : ℕ}
  {P : Subgroup (MulAut A)} {z : MulAut A} {K : Type} [Field K] [Finite K] [CharP K 2]
  {ρ : SL3 K →* G}

theorem JGood.torusImage_le {c' : G} {J : Subgroup G} (h : JGood p A c' J) :
    torusImage A J ≤ reflectionGroup p A := by
  have h1 := h.facts12.three.1
  rw [h1]
  exact Subgroup.closure_mono Set.inter_subset_left

theorem LineHyp.rot_mem_Tbar (hS : HessSetup p A c L f P z) {c' : G} (hL : LineHyp p A c' J f ρ) :
    ρ (permSL (finRotate 3)) ∈ Tbar A P := by
  refine ⟨hL.permSL_mem_normalizer _, ?_⟩
  have hX : piAut A (ρ (permSL (finRotate 3))) ∈ reflectionGroup p A := by
    refine JGood.torusImage_le hL.good ?_
    exact Sec12Three.mem_torusImage_iff.2 ⟨ρ (permSL (finRotate 3)), hL.permSL_mem_J _,
      hL.permSL_mem_normalizer _, (piAut_of_mem (hL.permSL_mem_normalizer _)).symm⟩
  refine (hS.spec.mem_P _ hX).2 ?_
  have h3 : (ρ (permSL (finRotate 3))) ^ 3 = 1 := by
    rw [← map_pow, permSL_pow_three _ (by decide), map_one]
  rw [← piAut_pow (hL.permSL_mem_normalizer _), h3, piAut_one]

end Rot

theorem rot_swap_cases : ∀ i j k l : Fin 3, i ≠ j → k ≠ l → Equiv.swap i j ≠ Equiv.swap k l →
    Equiv.swap (finRotate 3 i) (finRotate 3 j) = Equiv.swap k l ∨
    Equiv.swap (finRotate 3 (finRotate 3 i)) (finRotate 3 (finRotate 3 j)) = Equiv.swap k l := by
  decide

section Classes

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G} {f : ℕ}
  {P : Subgroup (MulAut A)} {z : MulAut A}

theorem HessSetup.exists_line_of_mem (hS : HessSetup p A c L f P z) {J : Subgroup G}
    (hJ : J ∈ thetaCompZeroStarE p A) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (ρ : SL3 K →* G) (c' : G),
      LineHyp p A c' J f ρ := by
  obtain ⟨c', hJg⟩ := hS.good J hJ
  obtain ⟨K, hKf, hKfin, hK, ρ, hρ⟩ := exists_psl3Data hS.griess hJg hS.f_dvd (hS.model J hJ)
  have hKc : CharP K 2 := charP_two_of_card hK
  exact ⟨K, hKf, hKfin, hKc, ρ, c', ⟨hJg, hρ, hK, hS.f_dvd⟩⟩

theorem HessSetup.tbar_transitive (hS : HessSetup p A c L f P z) {t x : MulAut A}
    (ht : t ∈ reflectionSet p A) (hx : x ∈ reflectionSet p A) :
    ∃ g ∈ Tbar A P, piAut A g * t * (piAut A g)⁻¹ = x := by
  by_cases htx : t = x
  · exact ⟨1, (Tbar A P).one_mem, by rw [piAut_one, htx]; group⟩
  · have hnc : t * x ≠ x * t := hS.ctx.hess t ht x hx htx
    obtain ⟨J, hJ, htJ, hxJ⟩ := hS.pair t ht x hx hnc
    obtain ⟨K, hKf, hKfin, hKc, ρ, c', hL⟩ := hS.exists_line_of_mem hJ
    obtain ⟨ht2, ht1⟩ := isAutReflection_sq ht.1
    obtain ⟨hx2, hx1⟩ := isAutReflection_sq hx.1
    obtain ⟨i, j, hij, rfl⟩ := hL.exists_nodeOf_eq htJ ht2 ht1
    obtain ⟨k, l, hkl, rfl⟩ := hL.exists_nodeOf_eq hxJ hx2 hx1
    have hr := hL.rot_mem_Tbar hS
    have hrot := hL.piAut_rot_nodeOf i j
    have hne : Equiv.swap i j ≠ Equiv.swap k l := fun h => htx (by simp only [nodeOf, h])
    rcases rot_swap_cases i j k l hij hkl hne with h | h
    · refine ⟨_, hr, ?_⟩
      rw [hrot]
      simp only [nodeOf, h]
    · refine ⟨_, (Tbar A P).mul_mem hr hr, ?_⟩
      have e : piAut A (ρ (permSL (finRotate 3)) * ρ (permSL (finRotate 3))) * nodeOf A ρ i j *
          (piAut A (ρ (permSL (finRotate 3)) * ρ (permSL (finRotate 3))))⁻¹ =
          piAut A (ρ (permSL (finRotate 3))) * (piAut A (ρ (permSL (finRotate 3))) * nodeOf A ρ i j *
            (piAut A (ρ (permSL (finRotate 3))))⁻¹) * (piAut A (ρ (permSL (finRotate 3))))⁻¹ := by
        rw [piAut_mul hr.1 hr.1]
        group
      rw [e, hrot, hL.piAut_rot_nodeOf (finRotate 3 i) (finRotate 3 j)]
      simp only [nodeOf, h]

@[expose] def ClassFnProps (p : ℕ) (A : Subgroup G) (f : ℕ) (P : Subgroup (MulAut A))
    (cls : MulAut A × Subgroup G → Bool) : Prop :=
  (∀ g ∈ torusNormalizer A, piAut A g ∈ P → ∀ r ∈ RootPairs p A f, cls (actPair A g r) = cls r) ∧
  (∀ t ∈ reflectionSet p A, ∀ S ∈ RootSet A f p t, ∀ S' ∈ RootSet A f p t, S ≠ S' →
    cls (t, S) ≠ cls (t, S')) ∧
  (∀ t ∈ reflectionSet p A, (∃ S ∈ RootSet A f p t, cls (t, S) = true) ∧
    ∃ S ∈ RootSet A f p t, cls (t, S) = false)

theorem HessSetup.exists_classFn (hS : HessSetup p A c L f P z) :
    ∃ cls : MulAut A × Subgroup G → Bool, ClassFnProps p A f P cls := by
  classical
  obtain ⟨c0, hL0⟩ := hS.good L hS.ctx.facts13.inZeroStar
  obtain ⟨t₀, ht₀, -⟩ := hL0.exists_reflection
  obtain ⟨S₁, S₂, hS12, hset⟩ := hS.rootSet_eq_two ht₀
  have hS₁ : S₁ ∈ RootSet A f p t₀ := by rw [hset]; exact Set.mem_insert _ _
  let r₀ : MulAut A × Subgroup G := (t₀, S₁)
  have hr₀ : r₀ ∈ RootPairs p A f := ⟨ht₀, hS₁⟩
  let orb : MulAut A × Subgroup G → Prop := fun r => ∃ g ∈ Tbar A P, actPair A g r₀ = r
  have hcls : ∀ r, decide (orb r) = true ↔ orb r := fun r => decide_eq_true_iff
  refine ⟨fun r => decide (orb r), ?_⟩
  have hinv : ∀ g ∈ torusNormalizer A, piAut A g ∈ P → ∀ r ∈ RootPairs p A f,
      decide (orb (actPair A g r)) = decide (orb r) := by
    intro g hgN hgP r hr
    have hg : g ∈ Tbar A P := ⟨hgN, hgP⟩
    rw [Bool.eq_iff_iff, hcls, hcls]
    constructor
    · rintro ⟨h, hh, e⟩
      refine ⟨g⁻¹ * h, (Tbar A P).mul_mem ((Tbar A P).inv_mem hg) hh, ?_⟩
      rw [actPair_mul ((torusNormalizer A).inv_mem hgN) hh.1, e, ← actPair_mul ((torusNormalizer A).inv_mem hgN) hgN,
        inv_mul_cancel, actPair_one]
    · rintro ⟨h, hh, e⟩
      refine ⟨g * h, (Tbar A P).mul_mem hg hh, ?_⟩
      rw [actPair_mul hgN hh.1, e]
  have hsame : ∀ t S S', orb (t, S) → orb (t, S') → t ∈ reflectionSet p A →
      S ∈ RootSet A f p t → S' = S := by
    rintro t S S' ⟨g, hg, e⟩ ⟨h, hh, e'⟩ ht hSr
    have ha : h * g⁻¹ ∈ Tbar A P := (Tbar A P).mul_mem hh ((Tbar A P).inv_mem hg)
    have hact : actPair A (h * g⁻¹) (t, S) = (t, S') := by
      rw [← e, ← actPair_mul ((torusNormalizer A).mul_mem hh.1 ((torusNormalizer A).inv_mem hg.1))
        hg.1, inv_mul_cancel_right, e']
    have h1 := congrArg Prod.fst hact
    have h2 := congrArg Prod.snd hact
    simp only [actPair] at h1 h2
    exact h2.symm.trans (hS.fixes_roots_tbar ha ht h1 hSr)
  have hex : ∀ t ∈ reflectionSet p A, ∃ S ∈ RootSet A f p t, orb (t, S) := by
    intro t ht
    obtain ⟨g, hg, hgt⟩ := hS.tbar_transitive ht₀ ht
    refine ⟨conjBy g S₁, ?_, g, hg, ?_⟩
    · have := hS.conjBy_mem_rootSet hg.1 ht₀ hS₁
      rwa [hgt] at this
    · simp only [actPair, r₀, hgt]
  have hsep : ∀ t ∈ reflectionSet p A, ∀ S ∈ RootSet A f p t, ∀ S' ∈ RootSet A f p t, S ≠ S' →
      decide (orb (t, S)) ≠ decide (orb (t, S')) := by
    intro t ht S hSr S' hS'r hne hdec
    rw [Bool.eq_iff_iff, hcls, hcls] at hdec
    by_cases hoS : orb (t, S)
    · exact hne (hsame t S S' hoS (hdec.1 hoS) ht hSr).symm
    · have hoS' : ¬ orb (t, S') := fun h => hoS (hdec.2 h)
      obtain ⟨S'', hS''r, hoS''⟩ := hex t ht
      obtain ⟨X, Y, hXY, hXYset⟩ := hS.rootSet_eq_two ht
      rw [hXYset] at hSr hS'r hS''r
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hSr hS'r hS''r
      have key : S'' = S ∨ S'' = S' := by
        rcases hSr with h1 | h1 <;> rcases hS'r with h2 | h2 <;> rcases hS''r with h3 | h3 <;>
          first
          | exact Or.inl (h3.trans h1.symm)
          | exact Or.inr (h3.trans h2.symm)
          | exact absurd (h1.trans h2.symm) hne
      rcases key with rfl | rfl
      · exact hoS hoS''
      · exact hoS' hoS''
  refine ⟨hinv, hsep, ?_⟩
  intro t ht
  obtain ⟨S, hSr, hoS⟩ := hex t ht
  obtain ⟨X, Y, hXY, hXYset⟩ := hS.rootSet_eq_two ht
  have hX : X ∈ RootSet A f p t := by rw [hXYset]; exact Set.mem_insert _ _
  have hY : Y ∈ RootSet A f p t := by
    rw [hXYset]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hd := hsep t ht X hX Y hY hXY
  refine ⟨⟨S, hSr, (hcls _).2 hoS⟩, ?_⟩
  by_cases hXo : orb (t, X)
  · refine ⟨Y, hY, ?_⟩
    exact Bool.eq_false_iff.2 fun h => hd (by rw [(hcls _).2 hXo]; exact (h : decide (orb (t, Y)) = true).symm)
  · exact ⟨X, hX, decide_eq_false hXo⟩

end Classes


end CFSG.RankThree.PartOne.HESS
