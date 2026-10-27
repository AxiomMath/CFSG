module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusBlockAuxStepD
public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusBlockAuxStepC
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenGen
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.Literature.GL52Transport

public section

namespace CFSG.StandardType.SuSplitRootGen

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.LieType.Universal.SpecialLinear Multiplicative
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.CALinearPlane
open scoped commutatorElement BigOperators

variable {F : Type} [Field F] {f m ε p : ℕ} {h : UnitaryFieldData 2 f F}
variable {E : Set (Multiplicative (Fin m → ZMod p))}

@[expose] noncomputable def posSet (a : HypIndex m ε)
    (E : Set (Multiplicative (Fin m → ZMod p))) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i =>
    ∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E →
      splitWeight (ε := ε) (.inl i) t = splitWeight (ε := ε) a t

@[expose] noncomputable def negSet (a : HypIndex m ε)
    (E : Set (Multiplicative (Fin m → ZMod p))) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i =>
    ∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E →
      splitWeight (ε := ε) (.inl i) t = -splitWeight (ε := ε) a t

theorem mem_posSet {a : HypIndex m ε} {i : Fin m} :
    i ∈ posSet a E ↔ ∀ t : Fin m → ZMod p,
      Multiplicative.ofAdd t ∈ E →
        splitWeight (ε := ε) (.inl i) t = splitWeight (ε := ε) a t := by
  classical
  rw [posSet, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

theorem mem_negSet {a : HypIndex m ε} {i : Fin m} :
    i ∈ negSet a E ↔ ∀ t : Fin m → ZMod p,
      Multiplicative.ofAdd t ∈ E →
        splitWeight (ε := ε) (.inl i) t = -splitWeight (ε := ε) a t := by
  classical
  rw [negSet, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

theorem disjoint_posSet_negSet (hp : p.Prime) (hp2 : p ≠ 2) {a : HypIndex m ε}
    (hz : ∃ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E ∧ splitWeight (ε := ε) a t ≠ 0) :
    Disjoint (posSet a E) (negSet a E) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Finset.disjoint_left]
  intro i hpos hneg
  obtain ⟨t, ht, hne⟩ := hz
  have h1 := (mem_posSet.mp hpos) t ht
  have h2 := (mem_negSet.mp hneg) t ht
  have hw : splitWeight (ε := ε) a t = -splitWeight (ε := ε) a t := h1.symm.trans h2
  have hxx : splitWeight (ε := ε) a t + splitWeight (ε := ε) a t = 0 :=
    (eq_neg_iff_add_eq_zero).mp hw
  have h2x : (2 : ZMod p) * splitWeight (ε := ε) a t = 0 := by
    rw [two_mul]
    exact hxx
  rcases mul_eq_zero.mp h2x with h | h
  · exact (two_ne_zero_zmod' hp hp2) h
  · exact hne h

theorem weightClass_union_partner_eq_pairCoords {a : HypIndex m ε}
    (hz : ∃ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E ∧ splitWeight (ε := ε) a t ≠ 0) :
    weightClass E a ∪ weightClassPartner E a =
      pairCoords (ε := ε) (posSet a E ∪ negSet a E) := by
  classical
  ext x
  rcases x with i | k | i
  · rw [Set.mem_union, weightClass, weightClassPartner, Set.mem_setOf_eq, Set.mem_setOf_eq,
      mem_pairCoords_inl, Finset.mem_union, ← mem_posSet, ← mem_negSet]
  ·
    constructor
    · intro hx
      rw [Set.mem_union] at hx
      rcases hx with h | h
      · obtain ⟨t, ht, hne⟩ := hz
        have h' : splitWeight (ε := ε) a t = 0 := by
          have h2 := (h t ht).symm
          simpa [splitWeight_z] using h2
        exact absurd h' hne
      · obtain ⟨t, ht, hne⟩ := hz
        have h' : splitWeight (ε := ε) a t = 0 := by
          have h2 := (h t ht).symm
          simp only [splitWeight_z] at h2
          exact neg_eq_zero.mp h2
        exact absurd h' hne
    · rintro (⟨j, hj, hx⟩ | ⟨j, hj, hx⟩) <;> exact absurd hx (by simp)
  ·
    constructor
    · intro hx
      rw [Set.mem_union] at hx
      rw [mem_pairCoords_inr_inr, Finset.mem_union]
      rcases hx with h | h
      · refine Or.inr ?_
        rw [mem_negSet]
        intro t ht
        have h' := h t ht
        rw [splitWeight_inr] at h'
        have h'' : t i = -splitWeight (ε := ε) a t := by
          simpa using congrArg Neg.neg h'
        simpa [splitWeight_inl] using h''
      · refine Or.inl ?_
        rw [mem_posSet]
        intro t ht
        have h' := h t ht
        rw [splitWeight_inr] at h'
        simpa [splitWeight_inl] using neg_injective h'
    · intro hx
      rw [mem_pairCoords_inr_inr, Finset.mem_union] at hx
      rcases hx with h | h
      ·
        rw [Set.mem_union]
        refine Or.inr ?_
        rw [weightClassPartner, Set.mem_setOf_eq]
        intro t ht
        have h' := (mem_posSet.mp h) t ht
        rw [splitWeight_inr]
        have h'' : t i = splitWeight (ε := ε) a t := by simpa [splitWeight_inl] using h'
        rw [h'']
      ·
        rw [Set.mem_union]
        refine Or.inl ?_
        rw [weightClass, Set.mem_setOf_eq]
        intro t ht
        have h' := (mem_negSet.mp h) t ht
        rw [splitWeight_inr]
        have h'' : t i = -splitWeight (ε := ε) a t := by simpa [splitWeight_inl] using h'
        rw [h'']
        simp

theorem signWeyl_inv_conj (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    (Neg : Finset (Fin m)) (t : Fin m → ZMod p) :
    (signWeyl (h := h) (ε := ε) Neg)⁻¹ * τ (Multiplicative.ofAdd t) *
        (signWeyl (h := h) (ε := ε) Neg) =
      τ (Multiplicative.ofAdd fun i => signVec (p := p) Neg i * t i) := by
  have hss : (fun i => signVec (p := p) Neg i * (signVec (p := p) Neg i * t i)) = t := by
    funext i
    rw [← mul_assoc, signVec_mul_self, one_mul]
  have h1 := signWeyl_conj (h := h) (ε := ε) hp hζ.pow_eq_one hτ Neg
    (fun i => signVec (p := p) Neg i * t i)
  rw [hss] at h1
  calc (signWeyl (h := h) (ε := ε) Neg)⁻¹ * τ (Multiplicative.ofAdd t) *
        (signWeyl (h := h) (ε := ε) Neg)
      = (signWeyl (h := h) (ε := ε) Neg)⁻¹ *
          ((signWeyl (h := h) (ε := ε) Neg) *
            τ (Multiplicative.ofAdd (fun i => signVec (p := p) Neg i * t i)) *
            (signWeyl (h := h) (ε := ε) Neg)⁻¹) *
          (signWeyl (h := h) (ε := ε) Neg) := by rw [h1]
    _ = τ (Multiplicative.ofAdd fun i => signVec (p := p) Neg i * t i) := by group

theorem nonempty_posSet_union_negSet {a : HypIndex m ε}
    (hz : ∃ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E ∧ splitWeight (ε := ε) a t ≠ 0) :
    (posSet (ε := ε) a E ∪ negSet (ε := ε) a E).Nonempty := by
  rcases a with i | k | i
  · exact ⟨i, Finset.mem_union_left _ (mem_posSet.mpr fun _ _ => rfl)⟩
  · obtain ⟨t, _, hne⟩ := hz
    rw [splitWeight_z] at hne
    exact absurd rfl hne
  · exact ⟨i, Finset.mem_union_right _ (mem_negSet.mpr fun _ _ => by simp)⟩

theorem conj_signWeyl_inv_mem_hypBlock_pair {S Neg : Finset (Fin m)}
    (hNegS : ∀ i ∈ Neg, i ∈ S) {g : hypSU h m ε}
    (hg : g ∈ hypBlock h (pairCoords (ε := ε) S)) :
    (MulAut.conj (signWeyl (h := h) (ε := ε) Neg)⁻¹) g ∈
      hypBlock h (pairCoords (ε := ε) S) := by
  classical
  let π : Equiv.Perm (HypIndex m ε) := weylPerm (ε := ε) (swapSet Neg)
  let P : Matrix (HypIndex m ε) (HypIndex m ε) F := signedPerm π (fun _ => (1 : F))
  let w : hypSU h m ε := signWeyl (h := h) (ε := ε) Neg
  let M : Matrix (HypIndex m ε) (HypIndex m ε) F :=
    (((g : hypSU h m ε) : GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F)
  have hwmat : (((w : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) = P := by
    simpa only [w, P, π] using signWeyl_matrix (h := h) (ε := ε) Neg
  have hM : IsHypBlockOn (pairCoords (ε := ε) S) M :=
    mem_hypBlock.mp hg
  have hπmul : π * π = 1 := by
    have h := weylPerm_swapSet_inv (ε := ε) Neg
    have h' : π⁻¹ = π := by simpa only [π] using h
    have h2 := inv_mul_cancel π
    rwa [h'] at h2
  have hPP : P * P = 1 := by
    rw [show P = signedPerm π (fun _ => (1 : F)) from rfl, signedPerm_mul_signedPerm,
      hπmul, signedPerm_one]
    simp [Matrix.diagonal_one]
  have hPinv : P⁻¹ = P := Matrix.inv_eq_right_inv hPP
  have hπmul' : ∀ x : HypIndex m ε, π (π x) = x := by
    intro x
    have h := congrArg (fun e : Equiv.Perm (HypIndex m ε) => e x) hπmul
    simpa using h
  have hπinl : ∀ i : Fin m, π (.inl i) = if i ∈ Neg then .inr (.inr i) else .inl i := by
    intro i
    simpa only [π] using weylPerm_swapSet_perm_inl (ε := ε) Neg i
  have hπinr : ∀ i : Fin m, π (.inr (.inr i)) = if i ∈ Neg then .inl i else .inr (.inr i) := by
    intro i
    simpa only [π] using weylPerm_swapSet_perm_inr_inr (ε := ε) Neg i
  have hπz : ∀ k : Fin ε, π (.inr (.inl k)) = .inr (.inl k) := by
    intro k
    simpa only [π] using weylPerm_inr_inl (ε := ε) (swapSet Neg) k
  have hπTsub : ∀ x ∈ pairCoords (ε := ε) S, π x ∈ pairCoords (ε := ε) S := by
    intro x hx
    rcases x with i | k | i
    · rw [hπinl i]
      by_cases hi : i ∈ Neg
      · rw [if_pos hi]
        exact mem_pairCoords_inr_inr.mpr (hNegS i hi)
      · rw [if_neg hi]
        exact mem_pairCoords_inl.mpr (mem_pairCoords_inl.mp hx)
    · rw [hπz k]
      exact absurd hx (inr_inl_not_mem_pairCoords (S := S))
    · rw [hπinr i]
      by_cases hi : i ∈ Neg
      · rw [if_pos hi]
        exact mem_pairCoords_inl.mpr (hNegS i hi)
      · rw [if_neg hi]
        exact mem_pairCoords_inr_inr.mpr (mem_pairCoords_inr_inr.mp hx)
  have hπT : π '' pairCoords (ε := ε) S = pairCoords (ε := ε) S := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      exact hπTsub y hy
    · intro x hx
      exact ⟨π x, hπTsub x hx, hπmul' x⟩
  have hconjmat : ((((MulAut.conj w⁻¹) g : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) = P⁻¹ * M * P := by
    rw [MulAut.conj_apply, inv_inv]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_inv]
    rw [hwmat]
  have hblock : IsHypBlockOn (pairCoords (ε := ε) S) (P * M * P⁻¹) := by
    have h := isHypBlockOn_signedPerm_conj (K := F) (r := m) (ε := ε) hM π
    rw [hπT] at h
    simpa only [P] using h
  rw [mem_hypBlock, hconjmat, hPinv]
  simpa only [hPinv] using hblock

theorem exists_eq_map_coordBlockSL_of_ne_zero_weight
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E : Set (Multiplicative (Fin m → ZMod p))} {J : Subgroup (hypSU h m ε)}
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer (τ '' E)))
    {a : HypIndex m ε} (hJle : J ≤ weightPairBlock (h := h) τ E a)
    (hz : ∃ t : Fin m → ZMod p,
      Multiplicative.ofAdd t ∈ E ∧ splitWeight (ε := ε) a t ≠ 0) :
    ∃ (S : Finset (Fin m)) (s : Fin m → ZMod p) (w : hypSU h m ε),
      (∀ i, s i = 1 ∨ s i = -1) ∧
      (∀ t : Fin m → ZMod p,
        w * τ (Multiplicative.ofAdd t) * w⁻¹ =
          τ (Multiplicative.ofAdd fun i => s i * t i)) ∧
      2 ≤ S.card ∧
      J = (coordBlockSL F S).map ((MulAut.conj w).toMonoidHom.comp (leviSU h ε)) := by
  classical
  let Pos : Finset (Fin m) := posSet (ε := ε) a E
  let Neg : Finset (Fin m) := negSet (ε := ε) a E
  let S : Finset (Fin m) := Pos ∪ Neg
  let s : Fin m → ZMod p := signVec (p := p) Neg
  let w : hypSU h m ε := signWeyl (h := h) (ε := ε) Neg
  let E' : Set (Fin m → ZMod p) :=
    {u | ∃ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E ∧ u = fun i => s i * t i}
  have hdisj : Disjoint Pos Neg := by
    simpa only [Pos, Neg] using disjoint_posSet_negSet (E := E) hp hp2 hz
  have hpair : weightClass E a ∪ weightClassPartner E a = pairCoords (ε := ε) S := by
    simpa only [S, Pos, Neg] using
      weightClass_union_partner_eq_pairCoords (E := E) hz
  have hweight : ∀ (t : Fin m → ZMod p) (i : Fin m),
      Multiplicative.ofAdd t ∈ E → i ∈ S → s i * t i = splitWeight (ε := ε) a t := by
    intro t i ht hi
    rcases Finset.mem_union.mp hi with hpos | hneg
    · have hsi : s i = 1 := by
        exact signVec_of_not_mem (Finset.disjoint_left.mp hdisj hpos)
      rw [hsi, one_mul]
      simpa only [splitWeight_inl] using (mem_posSet.mp hpos) t ht
    · have hsi : s i = -1 := signVec_of_mem hneg
      have hti : t i = -splitWeight (ε := ε) a t := by
        simpa only [splitWeight_inl] using (mem_negSet.mp hneg) t ht
      rw [hsi, hti]
      ring
  have hcommon : ∀ u ∈ E', ∀ i ∈ S, ∀ j ∈ S, u i = u j := by
    intro u hu i hi j hj
    obtain ⟨t, ht, rfl⟩ := hu
    exact (hweight t i ht hi).trans (hweight t j ht hj).symm
  have hSne : S.Nonempty := by
    simpa only [S, Pos, Neg] using nonempty_posSet_union_negSet (E := E) hz
  have hnonzero : ∃ u ∈ E', ∃ i ∈ S, u i ≠ 0 := by
    obtain ⟨i, hi⟩ := hSne
    obtain ⟨t, ht, hne⟩ := hz
    refine ⟨fun i => s i * t i, ⟨t, ht, rfl⟩, i, hi, ?_⟩
    change s i * t i ≠ 0
    rw [hweight t i ht hi]
    exact hne
  have hT : ∀ t : Fin m → ZMod p,
      w⁻¹ * τ (Multiplicative.ofAdd t) * w =
        τ (Multiplicative.ofAdd fun i => s i * t i) := by
    intro t
    simpa only [w, s] using signWeyl_inv_conj (h := h) (ε := ε) hp hζ hτ Neg t
  have hset : (MulAut.conj w⁻¹) '' (τ '' E) = τ '' (Multiplicative.ofAdd '' E') := by
    ext x
    constructor
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨Multiplicative.ofAdd (fun i => s i * t i), ?_, ?_⟩
      · exact ⟨fun i => s i * t i, ⟨t, ht, rfl⟩, rfl⟩
      · rw [MulAut.conj_apply, inv_inv]
        exact (hT t).symm
    · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
      obtain ⟨t, ht, rfl⟩ := hu
      refine ⟨τ (Multiplicative.ofAdd t), ⟨t, ht, rfl⟩, ?_⟩
      simpa only [MulAut.conj_apply, inv_inv] using hT t
  have hcent : (Subgroup.centralizer (τ '' E)).map (MulAut.conj w⁻¹).toMonoidHom =
      Subgroup.centralizer (τ '' (Multiplicative.ofAdd '' E')) := by
    rw [CFSG.Literature.GL52.map_centralizer_equiv, hset]
  let J' : Subgroup (hypSU h m ε) := J.map (MulAut.conj w⁻¹).toMonoidHom
  have hJ' : CFSG.Assembly.IsComponentOf J' (Subgroup.centralizer
      (τ '' (Multiplicative.ofAdd '' E'))) := by
    have h := CFSG.isComponentOf_map_mulEquiv (MulAut.conj w⁻¹)
      (CFSG.Assembly.isComponentOf_iff_open.mp hJ)
    have h' : CFSG.Open.IsComponentOf J' (Subgroup.centralizer
        (τ '' (Multiplicative.ofAdd '' E'))) := by
      rw [show J' = J.map (MulAut.conj w⁻¹).toMonoidHom from rfl]
      rwa [hcent] at h
    exact CFSG.Assembly.isComponentOf_iff_open.mpr h'
  have hJ'le : J' ≤ hypBlock h (pairCoords (ε := ε) S) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyblock : y ∈ hypBlock h (pairCoords (ε := ε) S) := by
      have h1 := (hJle hy).2
      rwa [hpair] at h1
    exact conj_signWeyl_inv_mem_hypBlock_pair (h := h) (ε := ε)
      (S := S) (Neg := Neg) (fun i hi => Finset.mem_union_right Pos hi) hyblock
  have hstepD : J' = (coordBlockSL F S).map (leviSU h ε) :=
    eq_map_coordBlockSL_of_isComponentOf hp hp2 hpq hζ hτ hcommon hnonzero hJ' hJ'le
  have h2S : 2 ≤ S.card := by
    by_contra hlt
    push Not at hlt
    have hbot : (coordBlockSL F S).map (leviSU h ε) = ⊥ := by
      rw [coordBlockSL_eq_bot_of_card_le_one (by omega), Subgroup.map_bot]
    have hJ'bot : J' = ⊥ := by rw [hstepD, hbot]
    exact LinSemisimple.false_of_isQuasisimple_of_commute hJ'.2.2 fun u hu v hv => by
      have hu1 : u = 1 := Subgroup.mem_bot.mp (hJ'bot ▸ hu)
      have hv1 : v = 1 := Subgroup.mem_bot.mp (hJ'bot ▸ hv)
      rw [hu1, hv1]
  refine ⟨S, s, w, ?_, ?_, h2S, ?_⟩
  · intro i
    change signVec (p := p) Neg i = 1 ∨ signVec (p := p) Neg i = -1
    unfold signVec
    split_ifs <;> norm_num
  · intro t
    simpa only [w, s] using signWeyl_conj (h := h) (ε := ε) hp hζ.pow_eq_one hτ Neg t
  · have hcomp : (MulAut.conj w).toMonoidHom.comp (MulAut.conj w⁻¹).toMonoidHom =
        MonoidHom.id (hypSU h m ε) := by
      apply MonoidHom.ext
      intro x
      change (MulAut.conj w) ((MulAut.conj w⁻¹) x) = x
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    have hback : J'.map (MulAut.conj w).toMonoidHom = J := by
      change (J.map (MulAut.conj w⁻¹).toMonoidHom).map (MulAut.conj w).toMonoidHom = J
      rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    rw [← hback, hstepD, Subgroup.map_map]

end CFSG.StandardType.SuSplitRootGen

end
