module

public import CFSG.Assembly.OrderReductions.PermutationReduction
public import CFSG.Quasithin.EmptyFaithful.R3c21A

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch59

open Equiv

theorem support_subset_of_mem_closure_threeCycles {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P : Finset Ω} {g : Perm Ω}
    (hg : g ∈ Subgroup.closure {h : Perm Ω | h.IsThreeCycle ∧ h.support ⊆ P}) :
    g.support ⊆ P := by
  classical
  refine Subgroup.closure_induction (p := fun y _ => y.support ⊆ P) ?_ ?_ ?_ ?_ hg
  · rintro h ⟨-, hsupp⟩
    exact hsupp
  · simp
  · intro x y _ _ hx hy
    exact (Equiv.Perm.support_mul_le x y).trans (Finset.union_subset hx hy)
  · intro x _ hx
    simpa [Equiv.Perm.support_inv] using hx

theorem isSolvable_closure_threeCycles_of_card_le_four {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P : Finset Ω} (hP : P.card ≤ 4) :
    Group.IsSolvable ↥(Subgroup.closure {g : Perm Ω | g.IsThreeCycle ∧ g.support ⊆ P}) := by
  classical
  let f : Perm {x : Ω // x ∈ P} →* Perm Ω := Equiv.Perm.ofSubtype (p := fun x => x ∈ P)
  have hperm : Group.IsSolvable (Perm {x : Ω // x ∈ P}) := by
    apply CFSG.OrderReductions.PermutationReduction.permutation_solvable_of_card_le_four
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hP
  have hrange : Group.IsSolvable ↥f.range :=
    @Group.isSolvable_of_surjective (Perm {x : Ω // x ∈ P}) (↥f.range) _ _
      f.rangeRestrict f.rangeRestrict_surjective hperm
  have hle : Subgroup.closure {g : Perm Ω | g.IsThreeCycle ∧ g.support ⊆ P} ≤ f.range := by
    rw [Subgroup.closure_le]
    rintro g ⟨-, hsupp⟩
    exact Equiv.Perm.mem_range_ofSubtype_iff.mpr hsupp
  exact @Group.isSolvable_of_isSolvable_injective
    (↥(Subgroup.closure {g : Perm Ω | g.IsThreeCycle ∧ g.support ⊆ P})) (↥f.range) _ _
    (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle) hrange

theorem commutator_closure_threeCycles_eq_bot {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P Q : Finset Ω} (hPQ : Disjoint P Q) :
    ⁅Subgroup.closure {g : Perm Ω | g.IsThreeCycle ∧ g.support ⊆ P},
      Subgroup.closure {g : Perm Ω | g.IsThreeCycle ∧ g.support ⊆ Q}⁆ = ⊥ := by
  classical
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  have haP := support_subset_of_mem_closure_threeCycles ha
  have hbQ := support_subset_of_mem_closure_threeCycles hb
  have hdisj : Equiv.Perm.Disjoint a b := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support, Finset.disjoint_left]
    intro x hxa hxb
    exact (Finset.disjoint_left.mp hPQ (haP hxa)) (hbQ hxb)
  have hcomm : a * b = b * a := (Equiv.Perm.Disjoint.commute hdisj).eq
  rw [Subgroup.mem_bot, commutatorElement_def, hcomm]
  group

theorem conj_mem_closure_threeCycles {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {ℬ : Finset (Finset Ω)} {g c : Perm Ω} {P : Finset Ω}
    (hgP : P.image g ∈ ℬ) (hc : c.IsThreeCycle) (hsupp : c.support ⊆ P) :
    g * c * g⁻¹ ∈
      Subgroup.closure {h : Perm Ω | h.IsThreeCycle ∧ ∃ Q ∈ ℬ, h.support ⊆ Q} := by
  refine Subgroup.subset_closure ⟨?_, P.image g, hgP, ?_⟩
  · rw [Equiv.Perm.IsThreeCycle, Equiv.Perm.cycleType_conj]
    exact hc
  · rw [Equiv.Perm.support_conj, Finset.map_eq_image]
    exact Finset.image_subset_iff.mpr fun x hx =>
      Finset.mem_image_of_mem g (hsupp hx)

theorem isSolvable_closure_threeCycles_sup {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {ℬ : Finset (Finset Ω)} (hℬ : (ℬ : Set (Finset Ω)).PairwiseDisjoint id)
    (h4 : ∀ P ∈ ℬ, P.card ≤ 4) {T : Subgroup (Perm Ω)} (hT : Group.IsSolvable ↥T)
    (hTℬ : ∀ g ∈ T, ∀ P ∈ ℬ, P.image g ∈ ℬ) :
    Group.IsSolvable
      ↥(Subgroup.closure {g : Perm Ω | g.IsThreeCycle ∧ ∃ P ∈ ℬ, g.support ⊆ P} ⊔ T) := by
  classical
  let NP : Finset Ω → Subgroup (Perm Ω) := fun P =>
    Subgroup.closure {g : Perm Ω | g.IsThreeCycle ∧ g.support ⊆ P}
  let S : Finset (Subgroup (Perm Ω)) := ℬ.image NP
  let N : Subgroup (Perm Ω) :=
    Subgroup.closure {g : Perm Ω | g.IsThreeCycle ∧ ∃ P ∈ ℬ, g.support ⊆ P}
  let G : Subgroup (Perm Ω) := N ⊔ T
  change Group.IsSolvable ↥G
  have hNP_solv : ∀ P ∈ ℬ, Group.IsSolvable ↥(NP P) := by
    intro P hP
    exact isSolvable_closure_threeCycles_of_card_le_four (h4 P hP)
  have hpair : (S : Set (Subgroup (Perm Ω))).Pairwise fun F F' => ⁅F, F'⁆ = ⊥ := by
    intro F hF F' hF' hne
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hF'
    have hPQ : P ≠ Q := by
      intro hPQ
      exact hne (by rw [hPQ])
    exact commutator_closure_threeCycles_eq_bot (hℬ hP hQ hPQ)
  have hSsolv : ∀ F ∈ S, Group.IsSolvable ↥F := by
    intro F hF
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hF
    exact hNP_solv P hP
  have hnormal : ∀ A ∈ S, ∀ B ∈ S, A ≤ Subgroup.normalizer (B : Set (Perm Ω)) := by
    intro A hA B hB
    by_cases hAB : A = B
    · subst hAB
      exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hpair hA hB hAB)).trans
        (Subgroup.centralizer_le_normalizer (B : Set (Perm Ω)))
  have hSupSolv : Group.IsSolvable ↥(S.sup id) := by
    rw [Finset.sup_eq_iSup]
    exact CFSG.Quasithin.R3c21.S0.isSolvable_biSup S hSsolv hnormal
  have hN_eq : N = S.sup id := by
    apply le_antisymm
    · change Subgroup.closure {g : Perm Ω | g.IsThreeCycle ∧ ∃ P ∈ ℬ, g.support ⊆ P} ≤
        S.sup id
      rw [Subgroup.closure_le]
      intro g hg
      obtain ⟨hc, P, hP, hsupp⟩ := hg
      exact Finset.le_sup (s := S) (f := id) (b := NP P)
        (Finset.mem_image.mpr ⟨P, hP, rfl⟩) (Subgroup.subset_closure ⟨hc, hsupp⟩)
    · refine Finset.sup_le ?_
      intro F hF
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hF
      change NP P ≤ N
      rw [Subgroup.closure_le]
      intro g hg
      exact Subgroup.subset_closure ⟨hg.1, P, hP, hg.2⟩
  have hN_solv : Group.IsSolvable ↥N := by
    rw [hN_eq]
    exact hSupSolv
  have hconj_for : ∀ {h : Perm Ω}, h ∈ T → ∀ {y : Perm Ω}, y ∈ N → h * y * h⁻¹ ∈ N := by
    intro h hh y hy
    change y ∈ Subgroup.closure {z : Perm Ω | z.IsThreeCycle ∧ ∃ P ∈ ℬ, z.support ⊆ P} at hy
    refine Subgroup.closure_induction (p := fun z _ => h * z * h⁻¹ ∈ N) ?_ ?_ ?_ ?_ hy
    · rintro c ⟨hc, P, hP, hsupp⟩
      exact conj_mem_closure_threeCycles (hTℬ h hh P hP) hc hsupp
    · simp
    · intro x y _ _ hx hy
      rw [show h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) by group]
      exact N.mul_mem hx hy
    · intro x _ hx
      rw [show h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ by group]
      exact N.inv_mem hx
  have hTN : T ≤ Subgroup.normalizer (N : Set (Perm Ω)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj_for hg hx
    · intro hx
      have hg' : g⁻¹ ∈ T := T.inv_mem hg
      have hx' : g⁻¹ * (g * x * g⁻¹) * g ∈ N := hconj_for hg' hx
      simpa [mul_assoc] using hx'
  have hNnormal : (N.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTN)
  have hsupG : N.subgroupOf G ⊔ T.subgroupOf G = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    change (N ⊔ T).subgroupOf (N ⊔ T) = ⊤
    rw [Subgroup.subgroupOf_self]
  have hN'solv : Group.IsSolvable ↥(N.subgroupOf G) := by
    let e : ↥(N.subgroupOf G) ≃* ↥N := Subgroup.subgroupOfEquivOfLe le_sup_left
    exact @solvable_of_solvable_injective (↥(N.subgroupOf G)) (↥N) _ _
      e.toMonoidHom e.injective hN_solv
  have hT'solv : Group.IsSolvable ↥(T.subgroupOf G) := by
    let e : ↥(T.subgroupOf G) ≃* ↥T := Subgroup.subgroupOfEquivOfLe le_sup_right
    exact @solvable_of_solvable_injective (↥(T.subgroupOf G)) (↥T) _ _
      e.toMonoidHom e.injective hT
  have hquot_surj : Function.Surjective
      ((QuotientGroup.mk' (N.subgroupOf G)).comp (T.subgroupOf G).subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf G) q
    have hx : x ∈ N.subgroupOf G ⊔ T.subgroupOf G := by
      rw [hsupG]
      exact Subgroup.mem_top x
    obtain ⟨n, hn, t, ht, hnt⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := N.subgroupOf G) (t := T.subgroupOf G)
        (hs := hNnormal)).mp hx
    have hn1 : QuotientGroup.mk' (N.subgroupOf G) n = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hn
    refine ⟨⟨t, ht⟩, ?_⟩
    change QuotientGroup.mk' (N.subgroupOf G) t =
      QuotientGroup.mk' (N.subgroupOf G) x
    rw [← hnt, map_mul, hn1, one_mul]
  have hquot_solv : Group.IsSolvable (↥G ⧸ N.subgroupOf G) :=
    @Group.isSolvable_of_surjective (↥(T.subgroupOf G)) (↥G ⧸ N.subgroupOf G) _ _
      ((QuotientGroup.mk' (N.subgroupOf G)).comp (T.subgroupOf G).subtype)
      hquot_surj hT'solv
  refine @Group.isSolvable_of_ker_le_range (↥G) _ (↥(N.subgroupOf G))
    (↥G ⧸ N.subgroupOf G) _ _ (N.subgroupOf G).subtype
    (QuotientGroup.mk' (N.subgroupOf G)) ?_ hN'solv hquot_solv
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

end CFSG.LocalAnalysis.WeakClosure81.Asch59
