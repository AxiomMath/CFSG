module

public import CFSG.LieType.Ree.FixedPositiveBlocks
public import CFSG.LieType.Chevalley.AllRootWeylConjugation
public import CFSG.LieType.Chevalley.CLSOddDiagramFourGroup
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Words

variable {τ : Tag}

@[expose] def weylWordSignRoot (τ : Tag) :
    List (Fin τ.rank) → (Fin τ.rank → ℤ) → ℤ × (Fin τ.rank → ℤ)
  | [], γ => (1, γ)
  | i :: ω, γ => (allRootWeylSign τ i (weylWordSignRoot τ ω γ).2 * (weylWordSignRoot τ ω γ).1,
      reflect τ i (weylWordSignRoot τ ω γ).2)

theorem isRoot_weylWordSignRoot (ω : List (Fin τ.rank)) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : IsRoot τ (weylWordSignRoot τ ω γ).2 := by
  induction ω with
  | nil => exact hγ
  | cons i ω ih => exact IsRoot.reflect i ih

theorem conj_weylWord_pinnedX (R : Type*) [CommRing R] (ω : List (Fin τ.rank))
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : R) :
    (ω.map fun i => weylElt τ R i 1).prod * pinnedX τ R γ c *
        ((ω.map fun i => weylElt τ R i 1).prod)⁻¹ =
      pinnedX τ R (weylWordSignRoot τ ω γ).2 (((weylWordSignRoot τ ω γ).1 : R) * c) := by
  induction ω with
  | nil => simp [weylWordSignRoot]
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons]
    calc weylElt τ R i 1 * (ω.map fun i => weylElt τ R i 1).prod * pinnedX τ R γ c *
          (weylElt τ R i 1 * (ω.map fun i => weylElt τ R i 1).prod)⁻¹ =
        weylElt τ R i 1 * ((ω.map fun i => weylElt τ R i 1).prod * pinnedX τ R γ c *
          ((ω.map fun i => weylElt τ R i 1).prod)⁻¹) * (weylElt τ R i 1)⁻¹ := by group
      _ = _ := by
        rw [ih, weylElt_one_mul_pinnedX_mul_inv R i (isRoot_weylWordSignRoot ω hγ)]
        simp only [weylWordSignRoot, Int.cast_mul, mul_assoc]

theorem conj_torusList_pinnedX (R : Type*) [CommRing R] (L : List (Fin τ.rank × Rˣ))
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : R) :
    (L.map fun p => torusElt τ R p.1 p.2).prod * pinnedX τ R γ c *
        ((L.map fun p => torusElt τ R p.1 p.2).prod)⁻¹ =
      pinnedX τ R γ ((L.map fun p => ((p.2 ^ (∑ j, τ.cartan p.1 j * γ j) : Rˣ) : R)).prod * c) := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    calc torusElt τ R p.1 p.2 * (L.map fun p => torusElt τ R p.1 p.2).prod * pinnedX τ R γ c *
          (torusElt τ R p.1 p.2 * (L.map fun p => torusElt τ R p.1 p.2).prod)⁻¹ =
        torusElt τ R p.1 p.2 * ((L.map fun p => torusElt τ R p.1 p.2).prod * pinnedX τ R γ c *
          ((L.map fun p => torusElt τ R p.1 p.2).prod)⁻¹) * (torusElt τ R p.1 p.2)⁻¹ := by group
      _ = _ := by rw [ih, root_torus_conjugation p.1 hγ p.2, mul_assoc]

end Words

section Roots

@[expose] def fieldThreeRootA : Fin TwistTag.E6.tag.rank → ℤ := ![1, 0, 1, 1, 1, 1]

@[expose] def fieldThreeRootD : Fin TwistTag.E6.tag.rank → ℤ := ![0, 0, 1, 1, 1, 0]

@[expose] def fieldThreeRootB : Fin TwistTag.E6.tag.rank → ℤ := ![1, 0, 1, 1, 1, 0]

@[expose] def fieldThreeRootB' : Fin TwistTag.E6.tag.rank → ℤ := ![0, 0, 1, 1, 1, 1]

abbrev fieldThreeWordA : List (Fin TwistTag.E6.tag.rank) :=
  [⟨0, by decide⟩, ⟨5, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩]

abbrev fieldThreeWordD : List (Fin TwistTag.E6.tag.rank) := [⟨2, by decide⟩, ⟨4, by decide⟩]

abbrev fieldThreeWordB : List (Fin TwistTag.E6.tag.rank) :=
  [⟨2, by decide⟩, ⟨4, by decide⟩, ⟨3, by decide⟩, ⟨0, by decide⟩, ⟨5, by decide⟩]

theorem weylWordSignRoot_A :
    weylWordSignRoot TwistTag.E6.tag fieldThreeWordA (Pi.single ⟨3, by decide⟩ 1) =
      (1, fieldThreeRootA) := by decide

theorem weylWordSignRoot_D :
    weylWordSignRoot TwistTag.E6.tag fieldThreeWordD (Pi.single ⟨3, by decide⟩ 1) =
      (-1, fieldThreeRootD) := by decide

theorem weylWordSignRoot_B :
    weylWordSignRoot TwistTag.E6.tag fieldThreeWordB (Pi.single ⟨2, by decide⟩ 1) =
      (-1, fieldThreeRootB) := by decide

theorem weylWordSignRoot_B' :
    weylWordSignRoot TwistTag.E6.tag fieldThreeWordB (Pi.single ⟨4, by decide⟩ 1) =
      (1, fieldThreeRootB') := by decide

end Roots

section RootFacts

theorem isRoot_fieldThreeRootA : IsRoot TwistTag.E6.tag fieldThreeRootA := by
  have h := isRoot_weylWordSignRoot fieldThreeWordA (isRoot_single TwistTag.E6.tag ⟨3, by decide⟩)
  rwa [weylWordSignRoot_A] at h

theorem isRoot_fieldThreeRootD : IsRoot TwistTag.E6.tag fieldThreeRootD := by
  have h := isRoot_weylWordSignRoot fieldThreeWordD (isRoot_single TwistTag.E6.tag ⟨3, by decide⟩)
  rwa [weylWordSignRoot_D] at h

theorem isRoot_fieldThreeRootB : IsRoot TwistTag.E6.tag fieldThreeRootB := by
  have h := isRoot_weylWordSignRoot fieldThreeWordB (isRoot_single TwistTag.E6.tag ⟨2, by decide⟩)
  rwa [weylWordSignRoot_B] at h

theorem isRoot_fieldThreeRootB' : IsRoot TwistTag.E6.tag fieldThreeRootB' := by
  have h := isRoot_weylWordSignRoot fieldThreeWordB (isRoot_single TwistTag.E6.tag ⟨4, by decide⟩)
  rwa [weylWordSignRoot_B'] at h

theorem commute_pinnedX_of_check (R : Type) [CommRing R] {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hβ : IsRoot TwistTag.E6.tag β) (hne : α ≠ β)
    (hα0 : ∀ j, 0 ≤ α j) (hβ0 : ∀ j, 0 ≤ β j) (hk : 1 ≤ α ⟨2, by decide⟩)
    (hl : 1 ≤ β ⟨2, by decide⟩)
    (h : ∀ a < 8, ∀ b < 8, 1 ≤ a → 1 ≤ b →
      RootOps.isRootB TwistTag.E6.tag (a • α + b • β) = false) (c d : R) :
    Commute (pinnedX TwistTag.E6.tag R α c) (pinnedX TwistTag.E6.tag R β d) := by
  have hαp : 0 < height α := by
    have h1 : α ⟨2, by decide⟩ ≤ height α :=
      Finset.single_le_sum (fun j _ => hα0 j) (Finset.mem_univ _)
    omega
  have hβp : 0 < height β := by
    have h1 : β ⟨2, by decide⟩ ≤ height β :=
      Finset.single_le_sum (fun j _ => hβ0 j) (Finset.mem_univ _)
    omega
  exact CFSG.LieType.Ree.commute_pinnedX_of_not_isRoot R hα hβ hαp hβp hne
    (CFSG.LieType.Ree.forall_not_isRoot_of_check hα0 hβ0 hk hl h) c d

theorem commute_fieldThree (R : Type) [CommRing R] (c d : R) :
    Commute (pinnedX TwistTag.E6.tag R fieldThreeRootD c)
        (pinnedX TwistTag.E6.tag R fieldThreeRootA d) ∧
      Commute (pinnedX TwistTag.E6.tag R fieldThreeRootB c)
        (pinnedX TwistTag.E6.tag R fieldThreeRootA d) ∧
      Commute (pinnedX TwistTag.E6.tag R fieldThreeRootB' c)
        (pinnedX TwistTag.E6.tag R fieldThreeRootA d) ∧
      Commute (pinnedX TwistTag.E6.tag R fieldThreeRootB c)
        (pinnedX TwistTag.E6.tag R fieldThreeRootD d) ∧
      Commute (pinnedX TwistTag.E6.tag R fieldThreeRootB' c)
        (pinnedX TwistTag.E6.tag R fieldThreeRootD d) ∧
      Commute (pinnedX TwistTag.E6.tag R fieldThreeRootB' c)
        (pinnedX TwistTag.E6.tag R fieldThreeRootB d) :=
  ⟨commute_pinnedX_of_check R isRoot_fieldThreeRootD isRoot_fieldThreeRootA (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) c d,
    commute_pinnedX_of_check R isRoot_fieldThreeRootB isRoot_fieldThreeRootA (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) c d,
    commute_pinnedX_of_check R isRoot_fieldThreeRootB' isRoot_fieldThreeRootA (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) c d,
    commute_pinnedX_of_check R isRoot_fieldThreeRootB isRoot_fieldThreeRootD (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) c d,
    commute_pinnedX_of_check R isRoot_fieldThreeRootB' isRoot_fieldThreeRootD (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) c d,
    commute_pinnedX_of_check R isRoot_fieldThreeRootB' isRoot_fieldThreeRootB (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) c d⟩

end RootFacts

section Elements

variable {K : Type} [Field K]

@[expose] def fieldThreeN (c : Kˣ) : ModGL TwistTag.E6.tag K :=
  (([(⟨0, by decide⟩, c), (⟨5, by decide⟩, c ^ 3), (⟨2, by decide⟩, c), (⟨4, by decide⟩, c ^ 3)] :
    List (Fin TwistTag.E6.tag.rank × Kˣ)).map fun p => torusElt TwistTag.E6.tag K p.1 p.2).prod

@[expose] def fieldThreeZ : ModGL TwistTag.E6.tag K :=
  (([(⟨0, by decide⟩, -1), (⟨5, by decide⟩, -1), (⟨3, by decide⟩, -1)] :
    List (Fin TwistTag.E6.tag.rank × Kˣ)).map fun p => torusElt TwistTag.E6.tag K p.1 p.2).prod

theorem fieldThreeN_eq (c : Kˣ) :
    fieldThreeN c = torusElt TwistTag.E6.tag K ⟨0, by decide⟩ c *
      (torusElt TwistTag.E6.tag K ⟨5, by decide⟩ (c ^ 3) *
        (torusElt TwistTag.E6.tag K ⟨2, by decide⟩ c *
          torusElt TwistTag.E6.tag K ⟨4, by decide⟩ (c ^ 3))) := by
  simp [fieldThreeN]

theorem fieldThreeZ_eq : (fieldThreeZ : ModGL TwistTag.E6.tag K) =
    torusElt TwistTag.E6.tag K ⟨0, by decide⟩ (-1) *
      (torusElt TwistTag.E6.tag K ⟨5, by decide⟩ (-1) *
        torusElt TwistTag.E6.tag K ⟨3, by decide⟩ (-1)) := by
  simp [fieldThreeZ]

@[expose] def fieldThreeIotaGL (σ : K →+* K) (a b v : K) : ModGL TwistTag.E6.tag K :=
  pinnedX TwistTag.E6.tag K fieldThreeRootA a * (pinnedX TwistTag.E6.tag K fieldThreeRootD (-b) *
    (pinnedX TwistTag.E6.tag K fieldThreeRootB (-v) *
      pinnedX TwistTag.E6.tag K fieldThreeRootB' (σ v)))

theorem fieldThreeIotaGL_zero (σ : K →+* K) : fieldThreeIotaGL σ 0 0 0 = 1 := by
  simp [fieldThreeIotaGL, pinnedX_zero]

theorem fieldThreeIotaGL_add (σ : K →+* K) (a b v a' b' v' : K) :
    fieldThreeIotaGL σ (a + a') (b + b') (v + v') =
      fieldThreeIotaGL σ a b v * fieldThreeIotaGL σ a' b' v' := by
  have hc := fun c d : K => commute_fieldThree K c d
  have hR : Commute (pinnedX TwistTag.E6.tag K fieldThreeRootD (-b) *
      (pinnedX TwistTag.E6.tag K fieldThreeRootB (-v) *
        pinnedX TwistTag.E6.tag K fieldThreeRootB' (σ v)))
      (pinnedX TwistTag.E6.tag K fieldThreeRootA a') :=
    ((hc _ _).1.mul_left ((hc _ _).2.1.mul_left (hc _ _).2.2.1))
  have hS : Commute (pinnedX TwistTag.E6.tag K fieldThreeRootB (-v) *
      pinnedX TwistTag.E6.tag K fieldThreeRootB' (σ v))
      (pinnedX TwistTag.E6.tag K fieldThreeRootD (-b')) :=
    ((hc _ _).2.2.2.1.mul_left (hc _ _).2.2.2.2.1)
  have hT : Commute (pinnedX TwistTag.E6.tag K fieldThreeRootB' (σ v))
      (pinnedX TwistTag.E6.tag K fieldThreeRootB (-v')) := (hc _ _).2.2.2.2.2
  rw [fieldThreeIotaGL, fieldThreeIotaGL, fieldThreeIotaGL, hR.mul_mul_mul_comm,
    hS.mul_mul_mul_comm, hT.mul_mul_mul_comm, neg_add, neg_add, map_add, pinnedX_add, pinnedX_add,
    pinnedX_add, pinnedX_add]

theorem fieldThreeIotaGL_eq_one {σ : K →+* K} {a b v : K} (h : fieldThreeIotaGL σ a b v = 1) :
    a = 0 ∧ b = 0 ∧ v = 0 := by
  classical
  set L : List (Fin TwistTag.E6.tag.rank → ℤ) :=
    [fieldThreeRootA, fieldThreeRootD, fieldThreeRootB, fieldThreeRootB'] with hL
  have hnd : L.Nodup := by decide
  have hpos : ∀ γ ∈ L, IsRoot TwistTag.E6.tag γ ∧ 0 < height γ := by
    intro γ hγ
    simp only [hL, List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl
    · exact ⟨isRoot_fieldThreeRootA, by decide⟩
    · exact ⟨isRoot_fieldThreeRootD, by decide⟩
    · exact ⟨isRoot_fieldThreeRootB, by decide⟩
    · exact ⟨isRoot_fieldThreeRootB', by decide⟩
  set c : (Fin TwistTag.E6.tag.rank → ℤ) → K := fun γ =>
    if γ = fieldThreeRootA then a else if γ = fieldThreeRootD then -b else
      if γ = fieldThreeRootB then -v else σ v with hc
  have hDA : fieldThreeRootD ≠ fieldThreeRootA := by decide
  have hBA : fieldThreeRootB ≠ fieldThreeRootA := by decide
  have hB'A : fieldThreeRootB' ≠ fieldThreeRootA := by decide
  have hBD : fieldThreeRootB ≠ fieldThreeRootD := by decide
  have hB'D : fieldThreeRootB' ≠ fieldThreeRootD := by decide
  have hB'B : fieldThreeRootB' ≠ fieldThreeRootB := by decide
  have heq : (L.map fun γ => pinnedX TwistTag.E6.tag K γ (c γ)).prod =
      (L.map fun γ => pinnedX TwistTag.E6.tag K γ ((fun _ => (0 : K)) γ)).prod := by
    simp only [hL, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hc,
      ↓reduceIte, hDA, hBA, hB'A, hBD, hB'D, hB'B, pinnedX_zero]
    exact h
  have h1 := pinnedX_list_prod_injective L hnd hpos c (fun _ => 0) heq
  have ha := h1 fieldThreeRootA (by simp [hL])
  have hb := h1 fieldThreeRootD (by simp [hL])
  have hv := h1 fieldThreeRootB (by simp [hL])
  simp only [hc, ↓reduceIte, hDA, hBA, hBD] at ha hb hv
  exact ⟨ha, neg_eq_zero.1 hb, neg_eq_zero.1 hv⟩

end Elements

section Membership

variable {K : Type} [Field K] (σ : K →+* K)

abbrev fieldThreeW (K : Type) [Field K] (ω : List (Fin TwistTag.E6.tag.rank)) :
    ModGL TwistTag.E6.tag K :=
  (ω.map fun i => weylElt TwistTag.E6.tag K i 1).prod

theorem fieldThree_orbitWord :
    TwistTag.E6.orbitWord ⟨0, by decide⟩ = [⟨0, by decide⟩, ⟨5, by decide⟩] ∧
      TwistTag.E6.orbitWord ⟨1, by decide⟩ = [⟨2, by decide⟩, ⟨4, by decide⟩] ∧
      TwistTag.E6.orbitWord ⟨2, by decide⟩ = [⟨3, by decide⟩] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem canonicalRep_orbitReflection_mem (a : Fin TwistTag.E6.foldedTag.rank) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection a) ∈
      graphFixedRootGroup TwistTag.E6 K σ :=
  canonicalRep_mem_graphFixedRootGroup (TwistTag.E6.orbitReflection_mem a)

theorem fieldThreeW_mem_A :
    fieldThreeW K fieldThreeWordA ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  obtain ⟨h0, h1, -⟩ := fieldThree_orbitWord
  have e : fieldThreeW K fieldThreeWordA =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection ⟨0, by decide⟩) *
        canonicalRep (coxeterSystem TwistTag.E6.tag) K
          (TwistTag.E6.orbitReflection ⟨1, by decide⟩) := by
    rw [canonicalRep_orbitReflection TwistTag.E6, canonicalRep_orbitReflection TwistTag.E6, h0, h1]
    simp [fieldThreeW, mul_assoc]
  rw [e]
  exact mul_mem (canonicalRep_orbitReflection_mem σ _) (canonicalRep_orbitReflection_mem σ _)

theorem fieldThreeW_mem_D :
    fieldThreeW K fieldThreeWordD ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  obtain ⟨-, h1, -⟩ := fieldThree_orbitWord
  have e : fieldThreeW K fieldThreeWordD =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K
        (TwistTag.E6.orbitReflection ⟨1, by decide⟩) := by
    rw [canonicalRep_orbitReflection TwistTag.E6, h1]
  rw [e]
  exact canonicalRep_orbitReflection_mem σ _

theorem fieldThreeW_mem_B :
    fieldThreeW K fieldThreeWordB ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  obtain ⟨h0, h1, h2⟩ := fieldThree_orbitWord
  have e : fieldThreeW K fieldThreeWordB =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection ⟨1, by decide⟩) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K
          (TwistTag.E6.orbitReflection ⟨2, by decide⟩) *
            canonicalRep (coxeterSystem TwistTag.E6.tag) K
              (TwistTag.E6.orbitReflection ⟨0, by decide⟩)) := by
    rw [canonicalRep_orbitReflection TwistTag.E6, canonicalRep_orbitReflection TwistTag.E6,
      canonicalRep_orbitReflection TwistTag.E6, h0, h1, h2]
    simp [fieldThreeW, mul_assoc]
  rw [e]
  exact mul_mem (canonicalRep_orbitReflection_mem σ _)
    (mul_mem (canonicalRep_orbitReflection_mem σ _) (canonicalRep_orbitReflection_mem σ _))

theorem fieldThree_coe_orbitX_one (c : orbitField TwistTag.E6 K σ ⟨1, by decide⟩) :
    (orbitX TwistTag.E6 K σ ⟨1, by decide⟩ c : ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ (σ c) := by
  rw [coe_orbitX]
  have hc : (TwistTag.E6.orbit ⟨1, by decide⟩).card = 2 := by decide
  have hm : TwistTag.E6.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
  have hp : TwistTag.E6.perm ⟨2, by decide⟩ = ⟨4, by decide⟩ := by decide
  rw [hc, List.range_succ, List.range_succ, List.range_zero]
  simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, pow_zero, pow_one, hm, hp, Equiv.Perm.one_apply, RingHom.coe_one,
    id_eq]

theorem pinnedX_fieldThreeRootA_mem {a : K} (ha : σ a = a) :
    pinnedX TwistTag.E6.tag K fieldThreeRootA a ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  have hmem : a ∈ orbitField TwistTag.E6 K σ ⟨2, by decide⟩ := by
    rw [mem_orbitField, show (TwistTag.E6.orbit ⟨2, by decide⟩).card = 1 by decide, pow_one]
    exact ha
  have hx := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ
    (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 σ ⟨2, by decide⟩ ⟨a, hmem⟩)
  rw [coe_orbitX_of_card_eq_one (by decide),
    show TwistTag.E6.orbitMin ⟨2, by decide⟩ = ⟨3, by decide⟩ by decide, ← pinnedX_single] at hx
  have e := conj_weylWord_pinnedX K fieldThreeWordA
    (isRoot_single TwistTag.E6.tag ⟨3, by decide⟩) a
  rw [weylWordSignRoot_A, Int.cast_one, one_mul] at e
  rw [← e]
  exact mul_mem (mul_mem (fieldThreeW_mem_A σ) hx) (inv_mem (fieldThreeW_mem_A σ))

theorem pinnedX_fieldThreeRootD_mem {b : K} (hb : σ b = b) :
    pinnedX TwistTag.E6.tag K fieldThreeRootD (-b) ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  have hmem : b ∈ orbitField TwistTag.E6 K σ ⟨2, by decide⟩ := by
    rw [mem_orbitField, show (TwistTag.E6.orbit ⟨2, by decide⟩).card = 1 by decide, pow_one]
    exact hb
  have hx := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ
    (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 σ ⟨2, by decide⟩ ⟨b, hmem⟩)
  rw [coe_orbitX_of_card_eq_one (by decide),
    show TwistTag.E6.orbitMin ⟨2, by decide⟩ = ⟨3, by decide⟩ by decide, ← pinnedX_single] at hx
  have e := conj_weylWord_pinnedX K fieldThreeWordD
    (isRoot_single TwistTag.E6.tag ⟨3, by decide⟩) b
  rw [weylWordSignRoot_D, Int.cast_neg, Int.cast_one, neg_one_mul] at e
  rw [← e]
  exact mul_mem (mul_mem (fieldThreeW_mem_D σ) hx) (inv_mem (fieldThreeW_mem_D σ))

theorem pinnedX_fieldThreeRootB_mem (hσσ : ∀ c, σ (σ c) = c) (v : K) :
    pinnedX TwistTag.E6.tag K fieldThreeRootB (-v) *
        pinnedX TwistTag.E6.tag K fieldThreeRootB' (σ v) ∈
      graphFixedRootGroup TwistTag.E6 K σ := by
  have hmem : v ∈ orbitField TwistTag.E6 K σ ⟨1, by decide⟩ := by
    rw [mem_orbitField, show (TwistTag.E6.orbit ⟨1, by decide⟩).card = 2 by decide, pow_two]
    exact hσσ v
  have hx := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ
    (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 σ ⟨1, by decide⟩ ⟨v, hmem⟩)
  rw [fieldThree_coe_orbitX_one, ← pinnedX_single, ← pinnedX_single] at hx
  have e1 := conj_weylWord_pinnedX K fieldThreeWordB
    (isRoot_single TwistTag.E6.tag ⟨2, by decide⟩) v
  have e2 := conj_weylWord_pinnedX K fieldThreeWordB
    (isRoot_single TwistTag.E6.tag ⟨4, by decide⟩) (σ v)
  rw [weylWordSignRoot_B, Int.cast_neg, Int.cast_one, neg_one_mul] at e1
  rw [weylWordSignRoot_B', Int.cast_one, one_mul] at e2
  have e : pinnedX TwistTag.E6.tag K fieldThreeRootB (-v) *
      pinnedX TwistTag.E6.tag K fieldThreeRootB' (σ v) =
        fieldThreeW K fieldThreeWordB * (pinnedX TwistTag.E6.tag K (Pi.single ⟨2, by decide⟩ 1) v *
          pinnedX TwistTag.E6.tag K (Pi.single ⟨4, by decide⟩ 1) (σ v)) *
            (fieldThreeW K fieldThreeWordB)⁻¹ := by
    rw [← e1, ← e2]
    group
  rw [e]
  exact mul_mem (mul_mem (fieldThreeW_mem_B σ) hx) (inv_mem (fieldThreeW_mem_B σ))

theorem fieldThreeIotaGL_mem (hσσ : ∀ c, σ (σ c) = c) {a b : K} (ha : σ a = a) (hb : σ b = b)
    (v : K) : fieldThreeIotaGL σ a b v ∈ graphFixedRootGroup TwistTag.E6 K σ :=
  mul_mem (pinnedX_fieldThreeRootA_mem σ ha)
    (mul_mem (pinnedX_fieldThreeRootD_mem σ hb) (pinnedX_fieldThreeRootB_mem σ hσσ v))

end Membership

section Torus

variable {K : Type} [Field K]

@[expose] def fieldThreeNExp (γ : Fin TwistTag.E6.tag.rank → ℤ) : ℤ :=
  (∑ j, TwistTag.E6.tag.cartan ⟨0, by decide⟩ j * γ j) +
    3 * (∑ j, TwistTag.E6.tag.cartan ⟨5, by decide⟩ j * γ j) +
    (∑ j, TwistTag.E6.tag.cartan ⟨2, by decide⟩ j * γ j) +
    3 * (∑ j, TwistTag.E6.tag.cartan ⟨4, by decide⟩ j * γ j)

@[expose] def fieldThreeZExp (γ : Fin TwistTag.E6.tag.rank → ℤ) : ℤ :=
  (∑ j, TwistTag.E6.tag.cartan ⟨0, by decide⟩ j * γ j) +
    (∑ j, TwistTag.E6.tag.cartan ⟨5, by decide⟩ j * γ j) +
    (∑ j, TwistTag.E6.tag.cartan ⟨3, by decide⟩ j * γ j)

theorem fieldThreeNExp_values :
    fieldThreeNExp fieldThreeRootA = 4 ∧ fieldThreeNExp fieldThreeRootD = 0 ∧
      fieldThreeNExp fieldThreeRootB = 1 ∧ fieldThreeNExp fieldThreeRootB' = 3 := by
  decide

theorem fieldThreeZExp_values :
    fieldThreeZExp fieldThreeRootA = 2 ∧ fieldThreeZExp fieldThreeRootD = -2 ∧
      fieldThreeZExp fieldThreeRootB = 0 ∧ fieldThreeZExp fieldThreeRootB' = 0 ∧
      fieldThreeZExp (Pi.single ⟨1, by decide⟩ 1) = -1 := by
  decide

theorem fieldThreeN_conj (c : Kˣ) {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (x : K) :
    fieldThreeN c * pinnedX TwistTag.E6.tag K γ x * (fieldThreeN c)⁻¹ =
      pinnedX TwistTag.E6.tag K γ (((c ^ fieldThreeNExp γ : Kˣ) : K) * x) := by
  have e : ∀ s0 s5 s2 s4 : ℤ, c ^ s0 * ((c ^ 3) ^ s5 * (c ^ s2 * (c ^ 3) ^ s4)) =
      c ^ (s0 + 3 * s5 + s2 + 3 * s4) := by
    intro s0 s5 s2 s4
    rw [← zpow_natCast c 3, ← zpow_mul, ← zpow_mul, ← zpow_add, ← zpow_add, ← zpow_add]
    congr 1
    push_cast
    ring
  rw [fieldThreeN, conj_torusList_pinnedX K _ hγ]
  congr 2
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [fieldThreeNExp, ← e, Units.val_mul, Units.val_mul, Units.val_mul]

theorem fieldThreeZ_conj {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (x : K) :
    fieldThreeZ * pinnedX TwistTag.E6.tag K γ x * fieldThreeZ⁻¹ =
      pinnedX TwistTag.E6.tag K γ ((((-1 : Kˣ) ^ fieldThreeZExp γ : Kˣ) : K) * x) := by
  rw [fieldThreeZ, conj_torusList_pinnedX K _ hγ]
  congr 2
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [fieldThreeZExp, zpow_add, zpow_add, Units.val_mul, Units.val_mul, mul_assoc]

theorem fieldThreeZ_mul_self : (fieldThreeZ : ModGL TwistTag.E6.tag K) * fieldThreeZ = 1 := by
  have h : ∀ i : Fin TwistTag.E6.tag.rank,
      torusElt TwistTag.E6.tag K i (-1) * torusElt TwistTag.E6.tag K i (-1) = 1 := by
    intro i
    rw [torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_one]
    congr 1
    funext j
    rw [Pi.mul_apply, Pi.one_apply, ← mul_zpow, neg_one_mul, neg_neg, one_zpow]
  have hc := fun i j : Fin TwistTag.E6.tag.rank =>
    torusElt_mul_comm (τ := TwistTag.E6.tag) (R := K) i j (-1) (-1)
  rw [fieldThreeZ_eq]
  set A := torusElt TwistTag.E6.tag K ⟨0, by decide⟩ (-1)
  set B := torusElt TwistTag.E6.tag K ⟨5, by decide⟩ (-1)
  set C := torusElt TwistTag.E6.tag K ⟨3, by decide⟩ (-1)
  have hBC : Commute (B * C) A := (Commute.mul_left (hc _ _) (hc _ _))
  have hCB : Commute C B := hc _ _
  rw [hBC.mul_mul_mul_comm, hCB.mul_mul_mul_comm, h, h, h, one_mul, one_mul]

variable (σ : K →+* K)

theorem fieldThree_orbitUnitParam (u : Kˣ) :
    orbitUnitParam TwistTag.E6 σ ⟨0, by decide⟩ u ⟨0, by decide⟩ = u ∧
      orbitUnitParam TwistTag.E6 σ ⟨0, by decide⟩ u ⟨5, by decide⟩ =
        Units.map σ.toMonoidHom u ∧
      orbitUnitParam TwistTag.E6 σ ⟨1, by decide⟩ u ⟨2, by decide⟩ = u ∧
      orbitUnitParam TwistTag.E6 σ ⟨1, by decide⟩ u ⟨4, by decide⟩ =
        Units.map σ.toMonoidHom u := by
  have hm0 : TwistTag.E6.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
  have hm1 : TwistTag.E6.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
  have hp0 : TwistTag.E6.perm ⟨0, by decide⟩ = ⟨5, by decide⟩ := by decide
  have hp2 : TwistTag.E6.perm ⟨2, by decide⟩ = ⟨4, by decide⟩ := by decide
  have e0 := orbitUnitParam_pow TwistTag.E6 σ u (a := ⟨0, by decide⟩) (k := 0) (by decide)
  have e1 := orbitUnitParam_pow TwistTag.E6 σ u (a := ⟨0, by decide⟩) (k := 1) (by decide)
  have e2 := orbitUnitParam_pow TwistTag.E6 σ u (a := ⟨1, by decide⟩) (k := 0) (by decide)
  have e3 := orbitUnitParam_pow TwistTag.E6 σ u (a := ⟨1, by decide⟩) (k := 1) (by decide)
  rw [pow_zero, Equiv.Perm.one_apply, hm0] at e0
  rw [pow_one, pow_one, hm0, hp0] at e1
  rw [pow_zero, Equiv.Perm.one_apply, hm1] at e2
  rw [pow_one, pow_one, hm1, hp2] at e3
  refine ⟨?_, e1, ?_, e3⟩
  · rw [e0]
    ext
    rfl
  · rw [e2]
    ext
    rfl

theorem fieldThreeN_mem (hσ : ∀ c, σ c = c ^ 3) (hσσ : ∀ c, σ (σ c) = c) (c : Kˣ) :
    fieldThreeN c ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  have hmem : ∀ a : Fin TwistTag.E6.foldedTag.rank, (TwistTag.E6.orbit a).card = 2 →
      (c : K) ∈ orbitField TwistTag.E6 K σ a := fun a ha => by
    rw [mem_orbitField, ha, pow_two]
    exact hσσ c
  set u0 : (orbitField TwistTag.E6 K σ ⟨0, by decide⟩)ˣ :=
    Units.mk0 ⟨c, hmem _ (by decide)⟩ fun h => c.ne_zero (congrArg Subtype.val h)
  set u1 : (orbitField TwistTag.E6 K σ ⟨1, by decide⟩)ˣ :=
    Units.mk0 ⟨c, hmem _ (by decide)⟩ fun h => c.ne_zero (congrArg Subtype.val h)
  have h0 : orbitFieldUnit TwistTag.E6 σ u0 = c := Units.ext rfl
  have h1 : orbitFieldUnit TwistTag.E6 σ u1 = c := Units.ext rfl
  have h3 : Units.map σ.toMonoidHom c = c ^ 3 := Units.ext (by simp [hσ])
  obtain ⟨p0, p5, p2, p4⟩ := fieldThree_orbitUnitParam σ c
  obtain ⟨o0, o1, -⟩ := fieldThree_orbitWord
  have e : fieldThreeN c = (orbitH TwistTag.E6 K σ ⟨0, by decide⟩ u0 : ModGL TwistTag.E6.tag K) *
      orbitH TwistTag.E6 K σ ⟨1, by decide⟩ u1 := by
    rw [coe_orbitH_eq, coe_orbitH_eq, h0, h1, o0, o1]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [p0, p5, p2, p4, h3, fieldThreeN_eq, mul_assoc]
  rw [e]
  exact mul_mem (orbitH_mem_graphFixedRootGroup TwistTag.E6 σ _ _)
    (orbitH_mem_graphFixedRootGroup TwistTag.E6 σ _ _)

theorem fieldThreeZ_mem : (fieldThreeZ : ModGL TwistTag.E6.tag K) ∈
    graphFixedRootGroup TwistTag.E6 K σ := by
  obtain ⟨o0, -, o2⟩ := fieldThree_orbitWord
  have e : (fieldThreeZ : ModGL TwistTag.E6.tag K) =
      (orbitH TwistTag.E6 K σ ⟨0, by decide⟩ (-1) : ModGL TwistTag.E6.tag K) *
        orbitH TwistTag.E6 K σ ⟨2, by decide⟩ (-1) := by
    rw [coe_orbitH_neg_one, coe_orbitH_neg_one, o0, o2, fieldThreeZ_eq]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [e]
  exact mul_mem (orbitH_mem_graphFixedRootGroup TwistTag.E6 σ _ _)
    (orbitH_mem_graphFixedRootGroup TwistTag.E6 σ _ _)

@[expose] def fieldThreeIotaHom (k : Subfield K) :
    Multiplicative (k × k × K) →* ModGL TwistTag.E6.tag K where
  toFun x := fieldThreeIotaGL σ (x.toAdd.1 : K) (x.toAdd.2.1 : K) x.toAdd.2.2
  map_one' := fieldThreeIotaGL_zero σ
  map_mul' x y := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, Subfield.coe_add]
    exact fieldThreeIotaGL_add σ _ _ _ _ _ _

end Torus

theorem twisted_E6_field_three_native_four_dimensional_root_action (K : Type) [Field K]
    (hK : Nat.card K = 9) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 3) :
    (∃ c : Kˣ, orderOf c = 8) ∧ ∀ c : Kˣ, orderOf c = 8 →
      fieldThreeN c ∈ graphFixedRootGroup TwistTag.E6 K σ ∧
      fieldThreeZ ∈ graphFixedRootGroup TwistTag.E6 K σ ∧
      orderOf (fieldThreeZ : ModGL TwistTag.E6.tag K) = 2 ∧
      ∃ ι : Multiplicative ((⊥ : Subfield K) × (⊥ : Subfield K) × K) →*
          graphFixedRootGroup TwistTag.E6 K σ,
        Function.Injective ι ∧
        (∀ (a b : (⊥ : Subfield K)) (v : K),
          fieldThreeN c * (ι (Multiplicative.ofAdd (a, b, v)) : ModGL TwistTag.E6.tag K) *
              (fieldThreeN c)⁻¹ =
            (ι (Multiplicative.ofAdd (-a, b, (c : K) * v)) : ModGL TwistTag.E6.tag K)) ∧
        (∀ x, fieldThreeZ * (ι x : ModGL TwistTag.E6.tag K) =
          (ι x : ModGL TwistTag.E6.tag K) * fieldThreeZ) ∧
        Nat.card ι.range = 3 ^ 4 ∧ (∀ x ∈ ι.range, x ^ 3 = 1) ∧
        (∀ x ∈ ι.range, ∀ y ∈ ι.range, x * y = y * x) ∧
        Module.finrank (⊥ : Subfield K) K = 2 ∧
        LinearMap.det (LinearMap.mulLeft (⊥ : Subfield K) (c : K)) = -1 ∧
        IsUnit (LinearMap.mulLeft (⊥ : Subfield K) (c : K) - 1) ∧
        IsUnit (LinearMap.mulLeft (⊥ : Subfield K) (c : K) + 1) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (k := 2) (by norm_num) hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ, ← pow_mul, show 3 * 3 = Fintype.card K by rw [Fintype.card_eq_nat_card, hK],
      FiniteField.pow_card]
  have hfix : ∀ a : (⊥ : Subfield K), σ a = a := fun a => by
    rw [hσ]
    exact (Subfield.mem_bot_iff_pow_eq_self K 3).1 a.2
  have hne : (1 : K) ≠ -1 := fun h => by
    have h2 := (neg_one_eq_one_iff (R := K)).1 h.symm
    rw [ringChar.eq K 3] at h2
    norm_num at h2
  refine ⟨?_, fun c hc => ?_⟩
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
    exact ⟨g, by rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]⟩
  have hc4 : (c : K) ^ 4 = -1 := by
    have h8 : (c : K) ^ 4 * (c : K) ^ 4 = 1 := by
      rw [← pow_add, show 4 + 4 = orderOf c by rw [hc], ← Units.val_pow_eq_pow_val,
        pow_orderOf_eq_one, Units.val_one]
    rcases mul_self_eq_one_iff.1 h8 with h | h
    · exact absurd (Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one]))
        (pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hc]; norm_num) : c ^ 4 ≠ 1)
    · exact h
  have e : ∀ g x y u w : ModGL TwistTag.E6.tag K, g * (x * (y * (u * w))) * g⁻¹ =
      g * x * g⁻¹ * (g * y * g⁻¹ * (g * u * g⁻¹ * (g * w * g⁻¹))) := by
    intros
    group
  have hn : ∀ a b v : K, fieldThreeN c * fieldThreeIotaGL σ a b v * (fieldThreeN c)⁻¹ =
      fieldThreeIotaGL σ (-a) b (c * v) := by
    intro a b v
    obtain ⟨hA, hD, hB, hB'⟩ := fieldThreeNExp_values
    rw [fieldThreeIotaGL, e, fieldThreeN_conj c isRoot_fieldThreeRootA,
      fieldThreeN_conj c isRoot_fieldThreeRootD, fieldThreeN_conj c isRoot_fieldThreeRootB,
      fieldThreeN_conj c isRoot_fieldThreeRootB', hA, hD, hB, hB', fieldThreeIotaGL]
    have h1 : ((c ^ (4 : ℤ) : Kˣ) : K) * a = -a := by
      rw [zpow_ofNat, Units.val_pow_eq_pow_val, hc4, neg_one_mul]
    have h2 : ((c ^ (0 : ℤ) : Kˣ) : K) * -b = -b := by rw [zpow_zero, Units.val_one, one_mul]
    have h3 : ((c ^ (1 : ℤ) : Kˣ) : K) * -v = -(c * v) := by rw [zpow_one, mul_neg]
    have h4 : ((c ^ (3 : ℤ) : Kˣ) : K) * σ v = σ (c * v) := by
      rw [zpow_ofNat, Units.val_pow_eq_pow_val, hσ, hσ, mul_pow]
    rw [h1, h2, h3, h4]
  have hz : ∀ a b v : K, fieldThreeZ * fieldThreeIotaGL σ a b v * fieldThreeZ⁻¹ =
      fieldThreeIotaGL σ a b v := by
    intro a b v
    obtain ⟨hA, hD, hB, hB', -⟩ := fieldThreeZExp_values
    rw [fieldThreeIotaGL, e, fieldThreeZ_conj isRoot_fieldThreeRootA,
      fieldThreeZ_conj isRoot_fieldThreeRootD, fieldThreeZ_conj isRoot_fieldThreeRootB,
      fieldThreeZ_conj isRoot_fieldThreeRootB', hA, hD, hB, hB',
      Even.neg_one_zpow (by decide), Even.neg_one_zpow (by decide),
      Even.neg_one_zpow (by decide), Units.val_one, one_mul, one_mul, one_mul, one_mul]
  have hz2 : orderOf (fieldThreeZ : ModGL TwistTag.E6.tag K) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by rw [pow_two, fieldThreeZ_mul_self]) fun h1 => hne ?_
    have h := fieldThreeZ_conj (K := K) (isRoot_single TwistTag.E6.tag ⟨1, by decide⟩) 1
    rw [fieldThreeZExp_values.2.2.2.2, Odd.neg_one_zpow (by decide), h1, one_mul, inv_one,
      mul_one, Units.val_neg, Units.val_one, mul_one] at h
    exact pinnedX_injective TwistTag.E6.tag K _ h
  set ι := (fieldThreeIotaHom σ (⊥ : Subfield K)).codRestrict (graphFixedRootGroup TwistTag.E6 K σ)
    (fun x => fieldThreeIotaGL_mem σ hσσ (hfix _) (hfix _) _) with hι
  have hιv : ∀ x, (ι x : ModGL TwistTag.E6.tag K) =
      fieldThreeIotaGL σ (x.toAdd.1 : K) (x.toAdd.2.1 : K) x.toAdd.2.2 := fun x => rfl
  have hinj : Function.Injective ι := by
    refine (injective_iff_map_eq_one ι).2 fun x hx => ?_
    have h := congrArg Subtype.val hx
    rw [hιv] at h
    obtain ⟨ha, hb, hv⟩ := fieldThreeIotaGL_eq_one h
    rw [← toAdd_eq_zero]
    exact Prod.ext (Subtype.ext ha) (Prod.ext (Subtype.ext hb) hv)
  have h3 : ∀ w : (⊥ : Subfield K) × (⊥ : Subfield K) × K, 3 • w = 0 := by
    have hK3 : ∀ w : K, 3 • w = 0 := fun w => by
      rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    have hk3 : ∀ w : (⊥ : Subfield K), 3 • w = 0 := fun w =>
      Subtype.ext (by rw [AddSubmonoidClass.coe_nsmul]; exact hK3 _)
    exact fun w => Prod.ext (hk3 _) (Prod.ext (hk3 _) (hK3 _))
  have hT : ∀ u : K, LinearMap.mulLeft (⊥ : Subfield K) u = Algebra.lmul (⊥ : Subfield K) K u :=
    fun u => LinearMap.ext fun _ => rfl
  have hunit : ∀ u : K, u ≠ 0 → IsUnit (Algebra.lmul (⊥ : Subfield K) K u) := fun u hu =>
    Algebra.lmul_isUnit_iff.2 (IsUnit.mk0 u hu)
  refine ⟨fieldThreeN_mem σ hσ hσσ c, fieldThreeZ_mem σ, hz2, ι, hinj, fun a b v => ?_,
    fun x => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hιv, hιv]
    exact hn _ _ _
  · rw [hιv, ← mul_inv_eq_iff_eq_mul, hz]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    change Nat.card ((⊥ : Subfield K) × (⊥ : Subfield K) × K) = _
    rw [Nat.card_prod, Nat.card_prod, Subfield.card_bot K 3, hK]
    norm_num
  · rintro _ ⟨y, rfl⟩
    rw [← map_pow, show y ^ 3 = 1 by rw [← toAdd_eq_zero, toAdd_pow]; exact h3 _, map_one]
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · have h := Module.natCard_eq_pow_finrank (K := (⊥ : Subfield K)) (V := K)
    rw [hK, Subfield.card_bot K 3] at h
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ _ = 3 ^ 2 by rw [← h])
  · rw [hT, ← Algebra.norm_apply]
    apply (algebraMap (⊥ : Subfield K) K).injective
    rw [FiniteField.algebraMap_norm_eq_pow, hK, Subfield.card_bot K 3, map_neg, map_one,
      show (9 - 1) / (3 - 1) = 4 by norm_num]
    exact hc4
  · rw [hT, ← map_one (Algebra.lmul (⊥ : Subfield K) K), ← map_sub]
    refine hunit _ fun h => hne ?_
    have h1 : (c : K) = 1 := sub_eq_zero.1 h
    rw [← hc4, h1, one_pow]
  · rw [hT, ← map_one (Algebra.lmul (⊥ : Subfield K) K), ← map_add]
    refine hunit _ fun h => hne ?_
    have h1 : (c : K) = -1 := eq_neg_of_add_eq_zero_left h
    rw [← hc4, h1]
    norm_num

end CFSG.RankThree.Chevalley
