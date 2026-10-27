module

public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix
open scoped commutatorElement

namespace Stellmacher.CD.L3YC

section Lin

variable {F : Type} [Field F]

@[expose] def tvGL (i j : Fin 3) (h : i ≠ j) (c : F) : Matrix.GeneralLinearGroup (Fin 3) F :=
  ⟨transvection i j c, transvection i j (-c),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

theorem tvGL_val (i j : Fin 3) (h : i ≠ j) (c : F) :
    ((tvGL i j h c : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      transvection i j c := rfl

theorem tvGL_inv_val (i j : Fin 3) (h : i ≠ j) (c : F) :
    (((tvGL i j h c)⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      transvection i j (-c) := rfl

theorem tvGL_mem (i j : Fin 3) (h : i ≠ j) (c : F) : tvGL i j h c ∈ StatedSL 3 F :=
  Subgroup.subset_closure (by
    show ((tvGL i j h c : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1
    rw [tvGL_val]
    exact det_transvection_of_ne i j h c)

theorem transvection_mulVec_single (l j : Fin 3) (t : F) :
    (transvection l j t).mulVec (Pi.single j 1) = Pi.single j 1 + Pi.single l t := by
  ext m
  simp [transvection, Pi.single_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hm : l = m
  · simp [hm]
  · have : ¬ m = l := fun e => hm e.symm
    simp [hm, this]

theorem exists_moduleAct_eq (dual : Bool) (l j : Fin 3) (h : l ≠ j) (t : F) :
    ∃ γ : ↥(StatedSL 3 F),
      moduleAct dual (γ : Matrix.GeneralLinearGroup (Fin 3) F) = transvection l j t := by
  cases dual
  · exact ⟨⟨tvGL l j h t, tvGL_mem l j h t⟩, by simp [moduleAct, tvGL_val]⟩
  · refine ⟨⟨tvGL j l h.symm (-t), tvGL_mem _ _ _ _⟩, ?_⟩
    change (((tvGL j l h.symm (-t))⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).transpose = _
    rw [tvGL_inv_val, neg_neg]
    simp [transvection, Matrix.transpose_add, Matrix.transpose_single]

end Lin

section Cover

variable {G : Type} [Group G] {F : Type} [Field F]

theorem sum_single_single {k : ℕ} (f : Fin k → Fin 3 → F) :
    f = ∑ i, ∑ l, (Pi.single i (Pi.single l (f i l) : Fin 3 → F) : Fin k → Fin 3 → F) := by
  ext i m
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem commutator_sup_eq {A V Z : Subgroup G} {α : ↥A →* ↥(StatedSL 3 F)}
    (hα : Function.Surjective α) {dual : Bool} {k : ℕ}
    (h : IsSumOfNaturalModulesVia A V Z α dual k) : ⁅V, A⁆ ⊔ Z = V := by
  obtain ⟨hAN, hZV, β, hβs, hβk, hβact⟩ := h
  have hAV : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V := fun a ha v hv =>
    (Subgroup.mem_normalizer_iff.mp (hAN ha) v).mp hv
  apply le_antisymm
  · refine sup_le ?_ hZV
    refine Subgroup.commutator_le.mpr fun v hv a ha => ?_
    have h1 : a * v⁻¹ * a⁻¹ ∈ V := hAV a ha v⁻¹ (V.inv_mem hv)
    have e : ⁅v, a⁆ = v * (a * v⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact V.mul_mem hv h1
  · intro q hq
    let W : Subgroup (Multiplicative (Fin k → Fin 3 → F)) := (⁅V, A⁆.subgroupOf V).map β
    have hgen : ∀ (i : Fin k) (l : Fin 3) (t : F),
        Multiplicative.ofAdd (Pi.single i (Pi.single l t : Fin 3 → F) : Fin k → Fin 3 → F) ∈ W := by
      intro i l t
      obtain ⟨j, hjl⟩ : ∃ j : Fin 3, l ≠ j := ⟨l + 1, by revert l; decide⟩
      obtain ⟨u, hu⟩ :=
        hβs (Multiplicative.ofAdd (Pi.single i (Pi.single j (1 : F) : Fin 3 → F) : Fin k → Fin 3 → F))
      obtain ⟨γ, hγ⟩ := exists_moduleAct_eq dual l j hjl t
      obtain ⟨a, ha⟩ := hα γ
      have hmem : (a : G) * u * (a : G)⁻¹ ∈ V := hAV a a.2 u u.2
      let v : ↥V := ⟨a * u * a⁻¹, hmem⟩
      refine ⟨v * u⁻¹, ?_, ?_⟩
      · show ((v * u⁻¹ : ↥V) : G) ∈ ⁅V, A⁆
        have e : ((v * u⁻¹ : ↥V) : G) = (⁅(u : G), (a : G)⁆)⁻¹ := by
          simp [v, commutatorElement_def, mul_assoc]
        rw [e]
        exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator u.2 a.2)
      · rw [map_mul, map_inv]
        apply Multiplicative.toAdd.injective
        funext i'
        have h1 := hβact a u v rfl i'
        rw [ha, hγ] at h1
        have h2 : Multiplicative.toAdd (β u) = (Pi.single i (Pi.single j (1 : F) : Fin 3 → F) :
            Fin k → Fin 3 → F) := by rw [hu]; rfl
        simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply]
        rw [h1, h2]
        by_cases hi : i' = i
        · subst hi
          simp only [Pi.single_eq_same, toAdd_ofAdd]
          rw [transvection_mulVec_single]
          abel
        · simp [hi]
    have hall : ∀ x : Multiplicative (Fin k → Fin 3 → F), x ∈ W := by
      intro x
      have hx : x = Multiplicative.ofAdd (∑ i, ∑ l, (Pi.single i (Pi.single l
          (Multiplicative.toAdd x i l) : Fin 3 → F) : Fin k → Fin 3 → F)) := by
        rw [← sum_single_single]; rfl
      rw [hx, ofAdd_sum]
      refine Subgroup.prod_mem _ fun i _ => ?_
      rw [ofAdd_sum]
      exact Subgroup.prod_mem _ fun l _ => hgen i l _
    obtain ⟨c, hc, hcq⟩ := hall (β ⟨q, hq⟩)
    have hker : c⁻¹ * ⟨q, hq⟩ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcq, inv_mul_cancel]
    rw [hβk] at hker
    have hz : ((c⁻¹ * ⟨q, hq⟩ : ↥V) : G) ∈ Z := hker
    have hc' : (c : G) ∈ ⁅V, A⁆ := hc
    have e : q = (c : G) * ((c⁻¹ * ⟨q, hq⟩ : ↥V) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup hc' hz
