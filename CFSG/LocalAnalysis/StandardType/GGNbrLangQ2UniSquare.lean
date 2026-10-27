module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniLift
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagUnitary
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2BlockProj
import CFSG.GroupTheory.WeirSylow.UnitaryBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open (StatedSU)
open CFSG.StandardType.ClassicalBlocks (GUFull)

theorem unitaryFieldData_card_sq {k : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 k E) :
    Nat.card E = (2 ^ k) ^ 2 := by
  rw [hE.card, ← pow_mul, mul_comm]

theorem exists_unitaryFieldData_two {E : Type} [Field E] [Finite E] [CharP E 2] {Q : ℕ}
    (hE : Nat.card E = Q ^ 2) : ∃ k : ℕ, Q = 2 ^ k ∧ UnitaryFieldData 2 k E := by
  haveI : Fintype E := Fintype.ofFinite E
  obtain ⟨f, hQf, hUF⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData E (q := Q)
    (by rw [← Nat.card_eq_fintype_card]; exact hE)
  have h2 : ringChar E = 2 := ringChar.eq E 2
  rw [h2] at hQf hUF
  exact ⟨f, hQf, hUF⟩

theorem guFull_eq_unitGroup {m k : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 k E) :
    GUFull m (2 ^ k) E = TableB.unitGroup (ι := Fin m) hE.bar := by
  rw [GUFull]
  have hset : {A : GL (Fin m) E |
      Matrix.transpose ((A : Matrix (Fin m) (Fin m) E).map (· ^ 2 ^ k)) *
        (A : Matrix (Fin m) (Fin m) E) = 1} =
      (TableB.unitGroup (ι := Fin m) hE.bar : Set (GL (Fin m) E)) := by
    ext A
    rw [Set.mem_setOf_eq, SetLike.mem_coe, TableB.mem_unitGroup]
    have hmap : (A : Matrix (Fin m) (Fin m) E).map (· ^ 2 ^ k) =
        (A : Matrix (Fin m) (Fin m) E).map hE.bar := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, hE.bar_apply]
    rw [hmap]
  rw [hset, Subgroup.closure_eq]

@[expose] noncomputable def guFullEquivUnitGroup {m k : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData 2 k E) :
    ↥(GUFull m (2 ^ k) E) ≃* ↥(TableB.unitGroup (ι := Fin m) hE.bar) :=
  MulEquiv.subgroupCongr (guFull_eq_unitGroup hE)

theorem map_subgroupOf_unitaryFull_eq_largeEvenSU {H : Type} [Group H] {F : Subgroup H}
    {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2] (hEQ : Nat.card E = Q ^ 2)
    (e : ↥F ≃* ↥(GUFull m Q E)) {C0 : Subgroup H} (hC0 : IsComponentOf C0 F) :
    ((C0.subgroupOf F).map e.toMonoidHom).map (GUFull m Q E).subtype =
      LargeEvenSUGroup (Fin m) E Q := by
  apply eq_statedSU_of_isComponentOf_unitaryFull hEQ
  have hcomp : CFSG.IsComponent (C0.subgroupOf F) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hC0.1).1 hC0
  have hmap : CFSG.IsComponent ((C0.subgroupOf F).map e.toMonoidHom) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent e hcomp
  have htop : IsComponentOf ((C0.subgroupOf F).map e.toMonoidHom)
      (⊤ : Subgroup ↥(GUFull m Q E)) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_top_iff_native _).2 hmap
  have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
    (f := (GUFull m Q E).subtype) (GUFull m Q E).subtype_injective).2 htop
  rwa [Subgroup.map_top, Subgroup.range_subtype] at h

@[expose] noncomputable def componentEquivLargeEvenSUOfUnitaryFull {H : Type} [Group H]
    {F : Subgroup H} {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hEQ : Nat.card E = Q ^ 2) (e : ↥F ≃* ↥(GUFull m Q E)) {C0 : Subgroup H}
    (hC0 : IsComponentOf C0 F) : ↥C0 ≃* ↥(LargeEvenSUGroup (Fin m) E Q) :=
  (Subgroup.subgroupOfEquivOfLe hC0.1).symm.trans
    ((Subgroup.equivMapOfInjective (C0.subgroupOf F) e.toMonoidHom e.injective).trans
      ((Subgroup.equivMapOfInjective ((C0.subgroupOf F).map e.toMonoidHom)
          (GUFull m Q E).subtype (GUFull m Q E).subtype_injective).trans
        (MulEquiv.subgroupCongr (map_subgroupOf_unitaryFull_eq_largeEvenSU hEQ e hC0))))

theorem componentEquivLargeEvenSUOfUnitaryFull_coe {H : Type} [Group H] {F : Subgroup H}
    {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2] (hEQ : Nat.card E = Q ^ 2)
    (e : ↥F ≃* ↥(GUFull m Q E)) {C0 : Subgroup H} (hC0 : IsComponentOf C0 F) (x : ↥C0) :
    ((componentEquivLargeEvenSUOfUnitaryFull hEQ e hC0 x : ↥(LargeEvenSUGroup (Fin m) E Q)) :
        GL (Fin m) E) =
      ((e ⟨x, hC0.1 x.2⟩ : ↥(GUFull m Q E)) : GL (Fin m) E) := by
  simp only [componentEquivLargeEvenSUOfUnitaryFull, MulEquiv.trans_apply,
    MulEquiv.subgroupCongr_apply, Subgroup.coe_equivMapOfInjective_apply]
  rfl

theorem center_largeEvenSU_eq_scalars {m k : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData 2 k E) (hm : 3 ≤ m) (hmk : ¬ (m = 3 ∧ k = 1)) :
    Subgroup.center ↥(LargeEvenSUGroup (Fin m) E (2 ^ k)) =
      (LargeEvenScalars (Fin m) E).subgroupOf (LargeEvenSUGroup (Fin m) E (2 ^ k)) := by
  haveI := hE.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := k)
    (F := E) (n := m) (unitaryFieldData_card_sq hE) hm ?_).2
  intro h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  exact hmk ⟨h1, Nat.pow_right_injective (le_refl 2) (h2.trans (by norm_num : (2 : ℕ) = 2 ^ 1))⟩

@[expose] noncomputable def largeEvenSUQuotEquivProj {m k : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData 2 k E) (hm : 3 ≤ m) (hmk : ¬ (m = 3 ∧ k = 1)) :
    ↥(LargeEvenSUGroup (Fin m) E (2 ^ k)) ⧸ Subgroup.center ↥(LargeEvenSUGroup (Fin m) E (2 ^ k)) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin m) E (2 ^ k)) :=
  QuotientGroup.quotientMulEquivOfEq (center_largeEvenSU_eq_scalars hE hm hmk)

theorem largeEvenSUQuotEquivProj_mk {m k : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData 2 k E) (hm : 3 ≤ m) (hmk : ¬ (m = 3 ∧ k = 1))
    (l : ↥(LargeEvenSUGroup (Fin m) E (2 ^ k))) :
    largeEvenSUQuotEquivProj hE hm hmk (QuotientGroup.mk l) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin m) E (2 ^ k)) l :=
  rfl

theorem uniConj_largeEvenSUQuotEquivProj {m k : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData 2 k E) (hm : 3 ≤ m) (hmk : ¬ (m = 3 ∧ k = 1))
    (A : ↥(TableB.unitGroup (ι := Fin m) hE.bar))
    {l l' : ↥(LargeEvenSUGroup (Fin m) E (2 ^ k))}
    (h : (l' : GL (Fin m) E) = (A : GL (Fin m) E) * (l : GL (Fin m) E) * (A : GL (Fin m) E)⁻¹) :
    CFSG.HardMathSupport.C14Cl.uniConj hE m A
        (largeEvenSUQuotEquivProj hE hm hmk (QuotientGroup.mk l)) =
      largeEvenSUQuotEquivProj hE hm hmk (QuotientGroup.mk l') := by
  rw [largeEvenSUQuotEquivProj_mk, largeEvenSUQuotEquivProj_mk]
  change TableB.projConj (LargeEvenSUGroup (Fin m) E (2 ^ k))
      (Subgroup.inclusion (CFSG.HardMathSupport.C14Cl.uniGroup_le_normalizer hE) A)
      (QuotientGroup.mk l) = QuotientGroup.mk l'
  rw [TableB.projConj_mk]
  congr 1
  exact Subtype.ext h.symm

@[expose] noncomputable def unitaryBlockQuotientMarking {H : Type} [Group H] {F : Subgroup H}
    {m k : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 k E) (hm : 3 ≤ m)
    (hmk : ¬ (m = 3 ∧ k = 1)) (e : ↥F ≃* ↥(TableB.unitGroup (ι := Fin m) hE.bar))
    {C0 : Subgroup H} (hC0 : IsComponentOf C0 F) :
    ↥C0 ⧸ Subgroup.center ↥C0 ≃* LargeEvenProj (LargeEvenSUGroup (Fin m) E (2 ^ k)) :=
  haveI := hE.finite
  haveI := hE.charP
  (QuotientGroup.congr (Subgroup.center ↥C0)
      (Subgroup.center ↥(LargeEvenSUGroup (Fin m) E (2 ^ k)))
      (componentEquivLargeEvenSUOfUnitaryFull (unitaryFieldData_card_sq hE)
        (e.trans (guFullEquivUnitGroup hE).symm) hC0)
      (Subgroup.map_center_eq
        (componentEquivLargeEvenSUOfUnitaryFull (unitaryFieldData_card_sq hE)
          (e.trans (guFullEquivUnitGroup hE).symm) hC0))).trans
    (largeEvenSUQuotEquivProj hE hm hmk)

theorem unitaryBlockQuotientMarking_square {H : Type} [Group H] {F X : Subgroup H} {m k : ℕ}
    {E : Type} [Field E] (hE : UnitaryFieldData 2 k E) (hm : 3 ≤ m) (hmk : ¬ (m = 3 ∧ k = 1))
    (e : ↥F ≃* ↥(TableB.unitGroup (ι := Fin m) hE.bar)) {C0 : Subgroup H}
    (hC0 : IsComponentOf C0 F) (ρ : ↥X →* ↥F)
    (hρ : ∀ (g : ↥X) (c : ↥F), ((ρ g * c * (ρ g)⁻¹ : ↥F) : H) =
      (g : H) * (c : H) * (g : H)⁻¹)
    (g : ↥X) (c c' : ↥C0) (h : (c' : H) = (g : H) * (c : H) * (g : H)⁻¹) :
    CFSG.HardMathSupport.C14Cl.uniConj hE m (e (ρ g))
        (unitaryBlockQuotientMarking hE hm hmk e hC0 (QuotientGroup.mk c)) =
      unitaryBlockQuotientMarking hE hm hmk e hC0 (QuotientGroup.mk c') := by
  haveI := hE.finite
  haveI := hE.charP
  have hkey : ∀ x : ↥C0, unitaryBlockQuotientMarking hE hm hmk e hC0 (QuotientGroup.mk x) =
      largeEvenSUQuotEquivProj hE hm hmk (QuotientGroup.mk
        (componentEquivLargeEvenSUOfUnitaryFull (unitaryFieldData_card_sq hE)
          (e.trans (guFullEquivUnitGroup hE).symm) hC0 x)) := fun x => rfl
  rw [hkey, hkey]
  apply uniConj_largeEvenSUQuotEquivProj
  rw [componentEquivLargeEvenSUOfUnitaryFull_coe, componentEquivLargeEvenSUOfUnitaryFull_coe]
  have hcF : (⟨c', hC0.1 c'.2⟩ : ↥F) = ρ g * (⟨c, hC0.1 c.2⟩ : ↥F) * (ρ g)⁻¹ := by
    apply Subtype.ext
    exact h.trans (hρ g ⟨c, hC0.1 c.2⟩).symm
  rw [hcF, map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rfl

@[expose] def Q2UniBlockHom {H : Type} [Group H] (X J : Subgroup H) : Prop :=
  ∃ (a mD : ℕ) (D : Type) (_ : Field D) (hD : UnitaryFieldData 2 mD D)
    (ψ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin a) D (2 ^ mD)))
    (π : ↥X →* ↥(TableB.unitGroup (ι := Fin a) hD.bar)),
    ∀ (h : ↥X) (j j' : ↥J), (j' : H) = (h : H) * (j : H) * (h : H)⁻¹ →
      CFSG.HardMathSupport.C14Cl.uniConj hD a (π h) (ψ (QuotientGroup.mk j)) =
        ψ (QuotientGroup.mk j')

theorem q2UniBlockHom_of_unitaryBlock {H : Type} [Group H] {X F J : Subgroup H}
    (ρ : ↥X →* ↥F)
    (hρ : ∀ (g : ↥X) (c : ↥F), ((ρ g * c * (ρ g)⁻¹ : ↥F) : H) =
      (g : H) * (c : H) * (g : H)⁻¹)
    {a k : ℕ} {D : Type} [Field D] (hD : UnitaryFieldData 2 k D) (ha : 3 ≤ a)
    (hak : ¬ (a = 3 ∧ k = 1)) (e : ↥F ≃* ↥(TableB.unitGroup (ι := Fin a) hD.bar))
    (hJF : IsComponentOf J F) : Q2UniBlockHom X J := by
  refine ⟨a, k, D, inferInstance, hD, unitaryBlockQuotientMarking hD ha hak e hJF,
    e.toMonoidHom.comp ρ, ?_⟩
  intro h j j' hjj
  exact unitaryBlockQuotientMarking_square hD ha hak e hJF ρ hρ h j j' hjj

theorem Q2UniBlockHom.of_mulEquiv {R H : Type} [Group R] [Group H] (e : R ≃* H)
    {X J : Subgroup R} (h : Q2UniBlockHom (X.map e.toMonoidHom) (J.map e.toMonoidHom)) :
    Q2UniBlockHom X J := by
  obtain ⟨a, mD, D, hDf, hD, ψ, π, hπ⟩ := h
  let eJ : ↥J ≃* ↥(J.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective J e.toMonoidHom e.injective
  let eX : ↥X ≃* ↥(X.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective X e.toMonoidHom e.injective
  let eJc : ↥J ⧸ Subgroup.center ↥J ≃*
      ↥(J.map e.toMonoidHom) ⧸ Subgroup.center ↥(J.map e.toMonoidHom) :=
    QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)
  refine ⟨a, mD, D, hDf, hD, eJc.trans ψ, π.comp eX.toMonoidHom, ?_⟩
  intro h j j' hjj
  have hj : ((eJ j' : ↥(J.map e.toMonoidHom)) : H) =
      ((eX h : ↥(X.map e.toMonoidHom)) : H) * ((eJ j : ↥(J.map e.toMonoidHom)) : H) *
        ((eX h : ↥(X.map e.toMonoidHom)) : H)⁻¹ := by
    change e (j' : R) = e (h : R) * e (j : R) * (e (h : R))⁻¹
    rw [hjj, map_mul, map_mul, map_inv]
  exact hπ (eX h) (eJ j) (eJ j') hj

theorem q2UnitaryLift_of_blockHom {H : Type} [Group H] {X J : Subgroup H}
    (hblock : Q2UniBlockHom X J) (T : Subgroup H) (hT : IsMulCommutative T) (hTX : T ≤ X)
    (hTJ : ∀ t ∈ T, ∀ j ∈ J, t * j * t⁻¹ ∈ J)
    (M : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)))
    (hM : ∀ α ∈ M, ∃ t ∈ T, ∀ j j' : ↥J, (j' : H) = t * (j : H) * t⁻¹ →
      α (QuotientGroup.mk j) = QuotientGroup.mk j') :
    Q2UnitaryLift M := by
  obtain ⟨a, mD, D, hDf, hD, ψ, π, hπ⟩ := hblock
  haveI : IsMulCommutative T := hT
  haveI : IsMulCommutative (T.subgroupOf X) :=
    ⟨⟨fun x y => by
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun z : ↥T => (z : H))
        (mul_comm' (⟨((x : ↥X) : H), Subgroup.mem_subgroupOf.mp x.2⟩ : ↥T)
          (⟨((y : ↥X) : H), Subgroup.mem_subgroupOf.mp y.2⟩ : ↥T))
      exact this⟩⟩
  refine ⟨a, mD, D, hDf, hD, ψ, (T.subgroupOf X).map π, Subgroup.map_isMulCommutative _ _, ?_⟩
  intro α hα
  obtain ⟨t, ht, hαt⟩ := hM α hα
  have htX : (⟨t, hTX ht⟩ : ↥X) ∈ T.subgroupOf X := Subgroup.mem_subgroupOf.mpr ht
  refine ⟨π ⟨t, hTX ht⟩, Subgroup.mem_map_of_mem π htX, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := ψ.surjective x
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective y
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulEquiv.trans_apply]
  have hjj : ((⟨t * (j : H) * t⁻¹, hTJ t ht j j.2⟩ : ↥J) : H) = t * (j : H) * t⁻¹ := rfl
  rw [hαt j ⟨t * (j : H) * t⁻¹, hTJ t ht j j.2⟩ hjj]
  exact (hπ ⟨t, hTX ht⟩ j ⟨t * (j : H) * t⁻¹, hTJ t ht j j.2⟩ hjj).symm

theorem q2UnitaryLift_of_innerActor {H : Type} [Group H]
    (hconj : Function.Injective (MulAut.conj : H →* MulAut H))
    {A : Subgroup (MulAut H)} (hA : IsMulCommutative ↥A)
    (hAI : ∀ a ∈ A, a ∈ LargeEvenInnSet H) {u : MulAut H} (hu : u ∈ A) {J : Subgroup H}
    (hblock : ∀ s : H, MulAut.conj s = u → Q2UniBlockHom (Subgroup.centralizer ({s} : Set H)) J)
    (hAJ : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J)
    (M : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)))
    (hM : ∀ α ∈ M, ∃ a ∈ A, ∀ j j' : ↥J, (j' : H) = a (j : H) →
      α (QuotientGroup.mk j) = QuotientGroup.mk j') :
    Q2UnitaryLift M := by
  obtain ⟨s, hs⟩ := hAI u hu
  let T : Subgroup H := A.comap (MulAut.conj : H →* MulAut H)
  have hmemT : ∀ t : H, t ∈ T ↔ MulAut.conj t ∈ A := fun t => Iff.rfl
  have hsT : s ∈ T := (hmemT s).2 (by rw [hs]; exact hu)
  have hTcomm : IsMulCommutative T :=
    ⟨⟨fun x y => by
      apply Subtype.ext
      apply hconj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg (fun z : ↥A => (z : MulAut H))
        (mul_comm' (⟨MulAut.conj (x : H), (hmemT _).1 x.2⟩ : ↥A)
          (⟨MulAut.conj (y : H), (hmemT _).1 y.2⟩ : ↥A))⟩⟩
  have hTX : T ≤ Subgroup.centralizer ({s} : Set H) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg (fun z : ↥T => (z : H))
      (mul_comm' (⟨t, ht⟩ : ↥T) (⟨s, hsT⟩ : ↥T)))
  have hTJ : ∀ t ∈ T, ∀ j ∈ J, t * j * t⁻¹ ∈ J := by
    intro t ht j hj
    have h := hAJ (MulAut.conj t) ((hmemT t).1 ht) j hj
    rwa [MulAut.conj_apply] at h
  refine q2UnitaryLift_of_blockHom (hblock s hs) T hTcomm hTX hTJ M ?_
  intro α hα
  obtain ⟨a, ha, hrel⟩ := hM α hα
  obtain ⟨t, ht⟩ := hAI a ha
  refine ⟨t, (hmemT t).2 (by rw [ht]; exact ha), fun j j' hjj => hrel j j' ?_⟩
  rw [← ht, MulAut.conj_apply]
  exact hjj

theorem q2_block_projection_conj {H : Type} [Group H] {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : ι → Subgroup H) (C : Subgroup H) [Finite ↥C] (hle : ∀ i, G i ≤ C)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ G i, ∀ y ∈ G j, Commute x y)
    (hsup : ⨆ i, G i = C) (hcard : Nat.card ↥C = ∏ i, Nat.card ↥(G i)) (k : ι) :
    ∃ π : ↥C →* ↥(G k),
      (∀ (x : H) (hx : x ∈ G k), π ⟨x, hle k hx⟩ = ⟨x, hx⟩) ∧
      (∀ i, i ≠ k → ∀ (x : H) (hx : x ∈ G i), π ⟨x, hle i hx⟩ = 1) ∧
      ∀ (g : ↥C) (c : ↥(G k)),
        ((π g * c * (π g)⁻¹ : ↥(G k)) : H) = (g : H) * (c : H) * (g : H)⁻¹ := by
  obtain ⟨π, h1, h2⟩ := q2_block_projection G C hle hcomm hsup hcard k
  refine ⟨π, h1, h2, ?_⟩
  intro g c
  have hg : (g : H) ∈ ⨆ i, G i := by
    rw [hsup]
    exact g.2
  have key : ∃ hx : (g : H) ∈ C, ∀ c : ↥(G k),
      ((π ⟨(g : H), hx⟩ * c * (π ⟨(g : H), hx⟩)⁻¹ : ↥(G k)) : H) =
        (g : H) * (c : H) * (g : H)⁻¹ := by
    refine Subgroup.iSup_induction G (C := fun x => ∃ hx : x ∈ C, ∀ c : ↥(G k),
      ((π ⟨x, hx⟩ * c * (π ⟨x, hx⟩)⁻¹ : ↥(G k)) : H) = x * (c : H) * x⁻¹) hg ?_ ?_ ?_
    · intro i x hx
      refine ⟨hle i hx, fun c => ?_⟩
      by_cases hik : i = k
      · subst hik
        rw [h1 x hx]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      · rw [h2 i hik x hx]
        have hc := (hcomm i k hik x hx (c : H) c.2).eq
        simp only [one_mul, inv_one, mul_one]
        rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    · refine ⟨C.one_mem, fun c => ?_⟩
      have : (⟨1, C.one_mem⟩ : ↥C) = 1 := rfl
      rw [this, map_one]
      simp
    · rintro x y ⟨hxC, hx⟩ ⟨hyC, hy⟩
      refine ⟨C.mul_mem hxC hyC, fun c => ?_⟩
      have hxy : (⟨x * y, C.mul_mem hxC hyC⟩ : ↥C) = ⟨x, hxC⟩ * ⟨y, hyC⟩ := rfl
      rw [hxy, map_mul]
      have h3 := hx ((π ⟨y, hyC⟩ * c * (π ⟨y, hyC⟩)⁻¹ : ↥(G k)))
      have h4 := hy c
      calc ((π ⟨x, hxC⟩ * π ⟨y, hyC⟩ * c * (π ⟨x, hxC⟩ * π ⟨y, hyC⟩)⁻¹ : ↥(G k)) : H)
          = ((π ⟨x, hxC⟩ * (π ⟨y, hyC⟩ * c * (π ⟨y, hyC⟩)⁻¹) * (π ⟨x, hxC⟩)⁻¹ : ↥(G k)) : H) := by
            congr 1
            group
        _ = x * y * (c : H) * (x * y)⁻¹ := by
            rw [h3]
            simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4 ⊢
            rw [h4]
            group
  obtain ⟨hx, H⟩ := key
  exact H c

end CFSG.StandardType
