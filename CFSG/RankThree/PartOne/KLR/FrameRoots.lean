module

public import CFSG.RankThree.PartOne.KLR.Frame
public import CFSG.RankThree.PartOne.KE.ConjRootSpan
public import CFSG.RankThree.PartOne.KE.LangDescent

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley

variable {L : Type} [Field L] [CharP L 2] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

omit [CharP L 2] in
theorem weylElement_eq_xyx (i : Fin ReeTag.F4.tag.rank) :
    weylElement ReeTag.F4.tag L i = xElement i 1 * yElement i (-1) * xElement i 1 := by
  have h := ReeTag.weylElementOf_eq (t := ReeTag.F4) (K := L) i 1
  simp only [inv_one, Units.val_one] at h
  exact h

theorem IsReeFrob.map_weylElement (hF : IsReeFrob a F) (i : Fin ReeTag.F4.tag.rank) :
    F (weylElement ReeTag.F4.tag L i) = weylElement ReeTag.F4.tag L (ReeTag.F4.perm i) := by
  rw [weylElement_eq_xyx, weylElement_eq_xyx, map_mul, map_mul, (hF i _).1, (hF i _).2]
  simp only [CharTwo.neg_eq, one_pow]

theorem IsReeFrob.map_weylElementOf (hF : IsReeFrob a F) (i : Fin ReeTag.F4.tag.rank) (u : Lˣ) :
    F (ReeTag.weylElementOf L i u) =
      ReeTag.weylElementOf L (ReeTag.F4.perm i) (u ^ ReeTag.F4.relationExponent a i) := by
  have hx : (u : L) ^ ReeTag.F4.relationExponent a i =
      ((u ^ ReeTag.F4.relationExponent a i : Lˣ) : L) := (Units.val_pow_eq_pow_val _ _).symm
  have hy : (-((u⁻¹ : Lˣ) : L)) ^ ReeTag.F4.relationExponent a i =
      -(((u ^ ReeTag.F4.relationExponent a i)⁻¹ : Lˣ) : L) := by
    rw [CharTwo.neg_eq, CharTwo.neg_eq, ← inv_pow, Units.val_pow_eq_pow_val]
  rw [ReeTag.weylElementOf_eq, ReeTag.weylElementOf_eq, map_mul, map_mul, (hF i _).1, (hF i _).2,
    hx, hy]

theorem IsReeFrob.map_torusElement (hF : IsReeFrob a F) (i : Fin ReeTag.F4.tag.rank) (u : Lˣ) :
    F (torusElement ReeTag.F4.tag L i u) =
      torusElement ReeTag.F4.tag L (ReeTag.F4.perm i) (u ^ ReeTag.F4.relationExponent a i) := by
  have h : ∀ (j : Fin ReeTag.F4.tag.rank) (v : Lˣ),
      torusElement ReeTag.F4.tag L j v =
        ReeTag.weylElementOf L j v * ReeTag.weylElementOf L j (-1) := fun _ _ => rfl
  have hneg : ((-1 : Lˣ) ^ ReeTag.F4.relationExponent a i) = -1 :=
    Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, CharTwo.neg_eq, one_pow])
  rw [h, h, map_mul, hF.map_weylElementOf, hF.map_weylElementOf, hneg]

theorem IsReeFrob.map_nrep (hF : IsReeFrob a F) (w : WeylGroup ReeTag.F4.tag) :
    F (nrep ReeTag.F4.tag L w) = nrep ReeTag.F4.tag L (ReeTag.F4.weylPerm w) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem ReeTag.F4.tag).exists_isReduced w
  rw [nrep_eq_prod _ _ hω, ReeTag.weylPerm_wordProd,
    nrep_eq_prod _ _ (ReeTag.isReduced_map_perm hω), map_list_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact hF.map_weylElement i

theorem IsReeFrob.mem_rootSubgroup (hF : IsReeFrob a F) {α : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : IsRoot ReeTag.F4.tag α) {g : adjointGroup ReeTag.F4.tag L}
    (hg : (g : ModGL ReeTag.F4.tag L) ∈ rootSubgroup ReeTag.F4.tag L α) :
    ((F g : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈
      rootSubgroup ReeTag.F4.tag L (ReeTag.F4.dualRoot α) := by
  obtain ⟨v, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hα
  have hjr : IsRoot ReeTag.F4.tag (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ j
  rw [← map_conj_rootSubgroup v hjr] at hg
  obtain ⟨y, hy, hgy⟩ := hg
  obtain ⟨c, rfl⟩ := CFSG.Blueprint.Chevalley.mem_rootSubgroup.1 hy
  rw [pinnedX_single] at hgy
  have hg' : g = nrep ReeTag.F4.tag L v * xElement j c * (nrep ReeTag.F4.tag L v)⁻¹ :=
    Subtype.ext (by rw [← hgy]; rfl)
  have hjr' : IsRoot ReeTag.F4.tag (Pi.single (ReeTag.F4.perm j) 1 :
      Fin ReeTag.F4.tag.rank → ℤ) := isRoot_single _ _
  rw [hg', map_mul, map_mul, map_inv, hF.map_nrep, (hF j c).1, ReeTag.dualRoot_smul v hjr,
    ReeTag.dualRoot_single, ← map_conj_rootSubgroup (ReeTag.F4.weylPerm v) hjr']
  refine ⟨xUnit ReeTag.F4.tag L (ReeTag.F4.perm j) (c ^ ReeTag.F4.relationExponent a j), ?_, rfl⟩
  exact CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨_, pinnedX_single _ _ _ _⟩

theorem IsReeFrob.mem_rootSpan (hF : IsReeFrob a F) {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α) {g : adjointGroup ReeTag.F4.tag L}
    (hg : (g : ModGL ReeTag.F4.tag L) ∈ rootSpan ReeTag.F4.tag L S) :
    ((F g : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈
      rootSpan ReeTag.F4.tag L (ReeTag.F4.dualRoot '' S) := by
  have hone : ∃ hx : (1 : ModGL ReeTag.F4.tag L) ∈ adjointGroup ReeTag.F4.tag L,
      ((F ⟨1, hx⟩ : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈
        rootSpan ReeTag.F4.tag L (ReeTag.F4.dualRoot '' S) := by
    refine ⟨one_mem _, ?_⟩
    have h1 : (⟨1, one_mem _⟩ : adjointGroup ReeTag.F4.tag L) = 1 := rfl
    rw [h1, map_one]
    exact one_mem _
  have hmem : ∃ hx : (g : ModGL ReeTag.F4.tag L) ∈ adjointGroup ReeTag.F4.tag L,
      ((F ⟨g, hx⟩ : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈
        rootSpan ReeTag.F4.tag L (ReeTag.F4.dualRoot '' S) := by
    refine Subgroup.iSup_induction (fun α => ⨆ (_ : α ∈ S), rootSubgroup ReeTag.F4.tag L α)
      (C := fun x => ∃ hx : x ∈ adjointGroup ReeTag.F4.tag L,
        ((F ⟨x, hx⟩ : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈
          rootSpan ReeTag.F4.tag L (ReeTag.F4.dualRoot '' S)) hg ?_ ?_ ?_
    · intro α x hx
      by_cases hα : α ∈ S
      · rw [iSup_pos hα] at hx
        have hxa : x ∈ adjointGroup ReeTag.F4.tag L := rootSubgroup_le_adjointGroup α hx
        refine ⟨hxa, ?_⟩
        have h1 := hF.mem_rootSubgroup (hS α hα) (g := ⟨x, hxa⟩) hx
        exact (le_iSup₂_of_le (f := fun β (_ : β ∈ ReeTag.F4.dualRoot '' S) =>
          rootSubgroup ReeTag.F4.tag L β) (ReeTag.F4.dualRoot α) ⟨α, hα, rfl⟩ le_rfl) h1
      · rw [iSup_neg hα, Subgroup.mem_bot] at hx
        subst hx
        exact hone
    · exact hone
    · rintro x y ⟨hx, hxm⟩ ⟨hy, hym⟩
      refine ⟨mul_mem hx hy, ?_⟩
      have : (⟨x * y, mul_mem hx hy⟩ : adjointGroup ReeTag.F4.tag L) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul]
      exact mul_mem hxm hym
  obtain ⟨hg', h⟩ := hmem
  exact h

end CFSG.RankThree.PartOne.KLR
