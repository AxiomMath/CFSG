module

public import CFSG.Timmesfeld.ARS.Sec4Lines
public import CFSG.Timmesfeld.ARS.Sec3Commuting
public import CFSG.Timmesfeld.ARS.Sec3Collinear
public import CFSG.Timmesfeld.ARS.Sec3Special

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

section Conj

variable (hR : IsRootClass R)
include hR

theorem centralSet_conjSub (X : Subgroup G) (g : G) :
    centralSet R (conjSub X g) = conjSet (centralSet R X) g := by
  ext E
  rw [mem_conjSet]
  constructor
  · rintro ⟨hE, hc⟩
    refine ⟨hR.conjSub_mem hE g⁻¹, ?_⟩
    have := hc.conjSub g⁻¹
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
  · rintro ⟨hE, hc⟩
    have hE' := hR.conjSub_mem hE g
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one] at hE'
    refine ⟨hE', ?_⟩
    have := hc.conjSub g
    rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at this

theorem omegaSet_conjSub (X : Subgroup G) (g : G) :
    omegaSet R (conjSub X g) = conjSet (omegaSet R X) g :=
  Sec3.setOf_opposite_conjSub hR X g

theorem rootClosure_conjSub (A : Subgroup G) (g : G) :
    rootClosure R (conjSub A g) = conjSet (rootClosure R A) g := by
  ext E
  rw [mem_conjSet]
  constructor
  · rintro ⟨hE, hc⟩
    refine ⟨hR.conjSub_mem hE g⁻¹, ?_⟩
    rw [centralSet_conjSub hR A g] at hc
    rw [centralSet_conjSub hR E g⁻¹, hc, conjSet_conjSet_inv]
  · rintro ⟨hE, hc⟩
    have hE' := hR.conjSub_mem hE g
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one] at hE'
    refine ⟨hE', ?_⟩
    rw [centralSet_conjSub hR E g⁻¹] at hc
    rw [centralSet_conjSub hR A g, ← hc, ← conjSet_mul, mul_inv_cancel, conjSet_one]

theorem conj_mem_rootElts_iff {x : G} (g : G) : g * x * g⁻¹ ∈ rootElts R ↔ x ∈ rootElts R := by
  constructor
  · rintro ⟨C, hC, hxC, hx1⟩
    refine ⟨conjSub C g⁻¹, hR.conjSub_mem hC g⁻¹, ?_, fun h => hx1 (by rw [h]; group)⟩
    rw [mem_conjSub, inv_inv]
    exact hxC
  · rintro ⟨C, hC, hxC, hx1⟩
    exact ⟨conjSub C g, hR.conjSub_mem hC g, conj_mem_conjSub g hxC,
      fun h => hx1 (conj_eq_one_iff.1 h)⟩

end Conj

section Block

variable {A B : Subgroup G}

theorem mem_rootClosure_self (hA : A ∈ R) : A ∈ rootClosure R A := ⟨hA, rfl⟩

theorem rootClosure_eq_of_mem (hB : B ∈ rootClosure R A) : rootClosure R B = rootClosure R A := by
  ext E
  exact ⟨fun ⟨hE, h⟩ => ⟨hE, h.trans hB.2⟩, fun ⟨hE, h⟩ => ⟨hE, h.trans hB.2.symm⟩⟩

theorem commuting_of_mem_rootClosure (hB : B ∈ rootClosure R A) {E : Subgroup G}
    (hE : E ∈ centralSet R A) : Commuting B E :=
  (hB.2.symm ▸ hE : E ∈ centralSet R B).2

theorem commuting_gen_rootClosure_of_mem_centralSet {E : Subgroup G} (hE : E ∈ centralSet R A) :
    Commuting (gen (rootClosure R A)) E :=
  (commuting_iff_le_centralizer.2 (gen_le fun _ hB =>
    commuting_iff_le_centralizer.1 (commuting_of_mem_rootClosure hB hE).symm)).symm

theorem mem_centralSet_of_mem_rootClosure (hR : IsRootClass R) (hA : A ∈ R)
    (hB : B ∈ rootClosure R A) : B ∈ centralSet R A :=
  ⟨hB.1, (commuting_of_mem_rootClosure hB ⟨hA, hR.commuting_self hA⟩).symm⟩

theorem commuting_gen_rootClosure (hR : IsRootClass R) (hA : A ∈ R) :
    Commuting (gen (rootClosure R A)) (gen (rootClosure R A)) :=
  commuting_gen_of_pairwise fun _ hB _ hC =>
    commuting_of_mem_rootClosure hB (mem_centralSet_of_mem_rootClosure hR hA hC)

theorem mul_self_of_mem_gen_rootClosure (hR : IsRootClass R) (hA : A ∈ R) {x : G}
    (hx : x ∈ gen (rootClosure R A)) : x * x = 1 := by
  have hc := commuting_gen_rootClosure hR hA
  refine (gen_induction (p := fun y => y ∈ gen (rootClosure R A) ∧ y * y = 1) hx
    (fun B hB y hy => ⟨le_gen hB hy, hR.mul_self B hB.1 y hy⟩) ⟨one_mem _, mul_one 1⟩
    fun y z ⟨hy, hyy⟩ ⟨hz, hzz⟩ => ⟨Subgroup.mul_mem _ hy hz, ?_⟩).2
  calc y * z * (y * z) = y * (z * y) * z := by group
    _ = y * (y * z) * z := by rw [(hc z hz y hy).eq]
    _ = 1 := by rw [← mul_assoc, hyy, one_mul, hzz]

theorem gen_rootClosure_le_stabSet (hR : IsRootClass R) (hA : A ∈ R) :
    gen (rootClosure R A) ≤ stabSet (rootClosure R A) := by
  refine gen_le fun _ hB t ht => ?_
  rw [mem_stabSet, ← rootClosure_conjSub hR, conjSub_of_forall_commute fun a ha =>
    (commuting_of_mem_rootClosure hB ⟨hA, hR.commuting_self hA⟩ t ht a ha)]

end Block

section Central

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
include hR hiso

omit [Finite G] in
theorem commuting_of_forall_commute {C E : Subgroup G} (hC : C ∈ R) (hE : E ∈ R) {x : G}
    (hx : x ∈ C) (hx1 : x ≠ 1) (h : ∀ e ∈ E, Commute x e) : Commuting C E := by
  by_cases hCE : C = E
  · rw [hCE]
    exact hR.commuting_self hE
  rcases hR.rel C hC E hE hCE with hc | ho | hs
  · exact hc
  · exact absurd h (ho.not_commute_of_mem hx hx1)
  · obtain ⟨e, he, he1⟩ := hR.exists_ne_one hE
    exact absurd (eq_one_of_commute_of_special hR hiso hC hE hs hx hx1 he (h e he)) he1

omit hiso in
theorem mem_rootClosure_of_centralSet_subset {A C : Subgroup G} (hA : A ∈ R) (hC : C ∈ R)
    (h : centralSet R A ⊆ centralSet R C) : C ∈ rootClosure R A := by
  obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hA hC
  refine ⟨hC, (Set.eq_of_subset_of_ncard_le h ?_ (Set.toFinite _)).symm⟩
  rw [centralSet_conjSub hR, conjSet, Set.ncard_image_of_injective _ fun _ _ h' =>
    map_conj_inj.1 h']

end Central

section OmegaSet

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
include hR hiso

omit [Finite G] hiso in
theorem mem_centralSet_union_psiSet_iff {X E : Subgroup G} (hX : X ∈ R) (hE : E ∈ R) :
    E ∈ centralSet R X ∪ psiSet R X ↔ ¬ Opposite X E := by
  constructor
  · rintro (⟨-, hc⟩ | ⟨-, hs⟩) ho
    · exact ho.not_commuting (hR.ne_bot X hX) hc
    · exact Special.not_opposite hR hX hs ho
  · intro ho
    by_cases hXE : X = E
    · exact Or.inl ⟨hE, hXE ▸ hR.commuting_self hX⟩
    rcases hR.rel X hX E hE hXE with h | h | h
    · exact Or.inl ⟨hE, h⟩
    · exact absurd h ho
    · exact Or.inr ⟨hE, h⟩

theorem omegaSet_subset_of_mem_rootClosure {A A' : Subgroup G} (hA : A ∈ R)
    (hA' : A' ∈ rootClosure R A) : omegaSet R A ⊆ omegaSet R A' := by
  rintro B ⟨hB, hAB⟩
  have hA'R := hA'.1
  have hAA' : Commuting A A' := (mem_centralSet_of_mem_rootClosure hR hA hA').2
  have hBnc : ¬ Commuting A' B := fun hc => hAB.not_commuting (hR.ne_bot A hA)
    (commuting_of_mem_rootClosure (mem_rootClosure_self hA) (hA'.2 ▸ ⟨hB, hc⟩ :
      B ∈ centralSet R A))
  refine ⟨hB, ?_⟩
  by_contra hno
  have hs : Special R A' B := by
    rcases (mem_centralSet_union_psiSet_iff hR hA'R hB).2 hno with h | h
    · exact absurd h.2 hBnc
    · exact h.2
  have hD := Sec3.commutator_mem_psiSet_of_commuting hR hiso hA hB hAB ⟨hA'R, hs.symm⟩ hAA'
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one hA
  have h1 : Commuting A (conjSub A' b) :=
    commuting_of_mem_rootClosure (mem_rootClosure_self hA)
      (hA'.2 ▸ ⟨hR.conjSub_mem hA'R b, commuting_conjSub_of_special hR hA'R hs hb⟩ :
        conjSub A' b ∈ centralSet R A)
  obtain ⟨a', ha', ha'1⟩ := hR.exists_ne_one hA'R
  have hcomm : Commute a ⁅b, a'⁆ := by
    have e1 : Commute a (b * a' * b⁻¹) := h1 a ha _ (conj_mem_conjSub b ha')
    have e2 : Commute a a' := hAA' a ha a' ha'
    have := e1.mul_right e2.inv_right
    rwa [show b * a' * b⁻¹ * a'⁻¹ = ⁅b, a'⁆ from (commutatorElement_def b a').symm] at this
  have hba' := eq_one_of_commute_of_special hR hiso hA hD.1 hD.2 ha ha1
    (Subgroup.commutator_mem_commutator hb ha') hcomm
  rw [commutatorElement_eq_one_iff_mul_comm] at hba'
  exact ha'1 (eq_one_of_commute_of_special hR hiso hB hA'R hs.symm hb hb1 ha' hba')

theorem omegaSet_eq_of_mem_rootClosure {A A' : Subgroup G} (hA : A ∈ R)
    (hA' : A' ∈ rootClosure R A) : omegaSet R A' = omegaSet R A :=
  Set.Subset.antisymm
    (omegaSet_subset_of_mem_rootClosure hR hiso hA'.1 (rootClosure_eq_of_mem hA' ▸
      mem_rootClosure_self hA))
    (omegaSet_subset_of_mem_rootClosure hR hiso hA hA')

theorem psiSet_eq_of_mem_rootClosure {A A' : Subgroup G} (hA : A ∈ R)
    (hA' : A' ∈ rootClosure R A) : psiSet R A' = psiSet R A := by
  have hΩ := omegaSet_eq_of_mem_rootClosure hR hiso hA hA'
  ext E
  constructor
  · rintro ⟨hE, hs⟩
    refine ⟨hE, ?_⟩
    rcases (mem_centralSet_union_psiSet_iff hR hA hE).2 fun ho =>
      Special.not_opposite hR hA'.1 hs (hΩ ▸ ⟨hE, ho⟩ : E ∈ omegaSet R A').2 with h | h
    · exact absurd (hA'.2 ▸ h : E ∈ centralSet R A').2 (hs.not_commuting hR)
    · exact h.2
  · rintro ⟨hE, hs⟩
    refine ⟨hE, ?_⟩
    rcases (mem_centralSet_union_psiSet_iff hR hA'.1 hE).2 fun ho =>
      Special.not_opposite hR hA hs (hΩ ▸ ⟨hE, ho⟩ : E ∈ omegaSet R A).2 with h | h
    · exact absurd (hA'.2 ▸ h : E ∈ centralSet R A).2 (hs.not_commuting hR)
    · exact h.2

theorem opposite_of_mem_rootClosure {A B A' B' : Subgroup G} (hA : A ∈ R) (hB : B ∈ R)
    (hAB : Opposite A B) (hA' : A' ∈ rootClosure R A) (hB' : B' ∈ rootClosure R B) :
    Opposite A' B' := by
  have h1 : Opposite A' B := (omegaSet_subset_of_mem_rootClosure hR hiso hA hA' ⟨hB, hAB⟩).2
  exact (omegaSet_subset_of_mem_rootClosure hR hiso hB hB' ⟨hA'.1, h1.symm⟩).2.symm

theorem commuting_of_omegaSet_eq {X Y C : Subgroup G} (hX : X ∈ R) (hY : Y ∈ R) (hC : C ∈ R)
    (hΩ : omegaSet R X = omegaSet R Y) (hYC : Commuting Y C) : Commuting X C := by
  by_contra hXC
  have hs : Special R X C := by
    rcases (mem_centralSet_union_psiSet_iff hR hX hC).2 fun ho =>
      ((hΩ ▸ ⟨hC, ho⟩ : C ∈ omegaSet R Y).2.not_commuting (hR.ne_bot Y hY)) hYC with h | h
    · exact absurd h.2 hXC
    · exact h.2
  have hFR : ⁅X, C⁆ ∈ R := hs.1
  have hFΛ : ⁅X, C⁆ ∈ lambdaSet R X :=
    mem_lambdaSet_comm hFR (mem_lambdaSet_commutator hR hiso hX hC hs).1
  obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hC
  have hY'R : conjSub X c ∈ R := hR.conjSub_mem hX c
  have hY'le : conjSub X c ≤ X ⊔ ⁅X, C⁆ :=
    (conjSub_le_commutator_sup hc).trans (sup_comm _ _).le
  have hY'X : conjSub X c ≠ X := Sec3.conjSub_ne_of_special hR hiso hC hX hs.symm hc hc1
  have hY'F : conjSub X c ≠ ⁅X, C⁆ := by
    intro e
    apply hXC
    have h1 : Commuting (conjSub X c) C := e ▸ hs.2.2
    have h2 := h1.conjSub c⁻¹
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one, conjSub_of_mem (C.inv_mem hc)] at h2
  have hΩY' : omegaSet R (conjSub X c) = omegaSet R Y := by
    rw [omegaSet_conjSub hR, hΩ, ← omegaSet_conjSub hR,
      conjSub_of_forall_commute fun y hy => (hYC y hy c hc).symm]
  obtain ⟨hXΛ, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hX hFΛ hY'R hY'le hX le_sup_left hY'X
  obtain ⟨U, hU, u, hu, hXu⟩ := exists_mem_lambdaSet_conjSub_eq hR hiso hY'R hXΛ hX le_sup_right
    hY'X.symm hFR (hsup ▸ le_sup_right) hY'F.symm
  have hfix : conjSub (conjSub X c) u = conjSub X c :=
    conjSub_of_forall_commute fun x hx => (hU.1.2.2 x hx u hu).symm
  have hΩu : conjSet (omegaSet R Y) u = omegaSet R Y := by
    rw [← hΩY', ← omegaSet_conjSub hR, hfix]
  have hΩF : omegaSet R ⁅X, C⁆ = omegaSet R X := by
    rw [← hXu, omegaSet_conjSub hR, hΩ, hΩu]
  apply not_subset_centralSet_union_psiSet hR hiso hX hFΛ
  intro E hE
  have hER : E ∈ R := by rcases hE with h | h <;> exact h.1
  rw [mem_centralSet_union_psiSet_iff hR hX hER] at hE
  rw [mem_centralSet_union_psiSet_iff hR hFR hER]
  intro ho
  exact hE (hΩF ▸ ⟨hER, ho⟩ : E ∈ omegaSet R X).2

theorem mem_rootClosure_of_omegaSet_eq {A D : Subgroup G} (hA : A ∈ R) (hD : D ∈ R)
    (hΩ : omegaSet R D = omegaSet R A) : D ∈ rootClosure R A := by
  refine ⟨hD, Set.Subset.antisymm (fun C hC => ?_) fun C hC => ?_⟩
  · exact ⟨hC.1, commuting_of_omegaSet_eq hR hiso hA hD hC.1 hΩ.symm hC.2⟩
  · exact ⟨hC.1, commuting_of_omegaSet_eq hR hiso hD hA hC.1 hΩ hC.2⟩

theorem rootClosure_eq_setOf_omegaSet_eq {A : Subgroup G} (hA : A ∈ R) :
    rootClosure R A = {D | D ∈ R ∧ omegaSet R D = omegaSet R A} :=
  Set.ext fun _ => ⟨fun hD => ⟨hD.1, omegaSet_eq_of_mem_rootClosure hR hiso hA hD⟩,
    fun ⟨hD, hΩ⟩ => mem_rootClosure_of_omegaSet_eq hR hiso hA hD hΩ⟩

end OmegaSet

end CFSG.Timmesfeld.ARS
