module

public import CFSG.Milestones.ASVolI.C135.P1

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL specialLinearGroupEquivStatedSL_coe)
open CFSG.Quasithin.H13.Ch4.C135 (slNat dualHom coe_dualHom coe_slNat moduleAct_false_eq
  moduleAct_true_eq)
open scoped Matrix commutatorElement

variable {G : Type} [Group G]

section Coords

variable {F : Type} [Field F]

@[expose] def burnsideC135_Kc (F : Type) [Field F] (i : Fin 2) :
    Subgroup (Multiplicative (Fin 2 → Fin 3 → F)) where
  carrier := {v | Multiplicative.toAdd v i = 0}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [toAdd_mul, Pi.add_apply, ha, hb, add_zero]
  one_mem' := rfl
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [toAdd_inv, Pi.neg_apply, ha, neg_zero]

@[expose] def burnsideC135_Wc {Q : Subgroup G} (β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F))
    (i : Fin 2) : Subgroup G :=
  ((burnsideC135_Kc F i).comap β).map Q.subtype

variable {Q : Subgroup G} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}

theorem burnsideC135_mem_Wc {i : Fin 2} {g : G} :
    g ∈ burnsideC135_Wc β i ↔ ∃ h : g ∈ Q, Multiplicative.toAdd (β ⟨g, h⟩) i = 0 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.2, hq⟩
  · rintro ⟨h, hq⟩
    exact ⟨⟨g, h⟩, hq, rfl⟩

theorem burnsideC135_Wc_le (i : Fin 2) : burnsideC135_Wc β i ≤ Q := fun _ hg =>
  (burnsideC135_mem_Wc.mp hg).1

@[expose] noncomputable def burnsideC135_βc (β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F))
    (i : Fin 2) : ↥(burnsideC135_Wc β i) →* Multiplicative (Fin 3 → F) :=
  (burnsideC135_proj F (1 - i)).comp (β.comp (Subgroup.inclusion (burnsideC135_Wc_le i)))

theorem burnsideC135_βc_apply (i : Fin 2) (w : ↥(burnsideC135_Wc β i)) :
    burnsideC135_βc β i w =
      Multiplicative.ofAdd (Multiplicative.toAdd (β ⟨w, burnsideC135_Wc_le i w.2⟩) (1 - i)) :=
  rfl

variable [Finite G] {L : Subgroup G} [Fintype F] [CharP F 2] {α : ↥L →* ↥(StatedSL 3 F)}

theorem burnsideC135_dualSplit_of_coords (hα : IsModO2Surj L α) {Q : Subgroup G}
    (h1 : IsSumOfNaturalModulesVia L (centerOf Q) ⊥ α false 1)
    {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hUQ : centerOf Q ≤ Q) (hβs : Function.Surjective β)
    (hβk : β.ker = (centerOf Q).subgroupOf Q)
    (hβeq : ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        (moduleAct true (α a : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i)) :
    ∃ βU : ↥(centerOf Q) →* Multiplicative (Fin 3 → F),
      burnsideC135_DSG Q L (burnsideC135_Wc β 1) (burnsideC135_Wc β 0)
        (slNat α) βU (burnsideC135_βc β 1) (burnsideC135_βc β 0) := by
  classical
  obtain ⟨hLU, -, β', hβ's, hβ'k, hβ'eq⟩ := h1
  let e1 : Multiplicative (Fin 1 → Fin 3 → F) →* Multiplicative (Fin 3 → F) :=
    AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ => Fin 3 → F) 0)
  have he1 : Function.Bijective e1 := by
    refine ⟨fun a b h => ?_, fun c => ⟨Multiplicative.ofAdd (fun _ => c), rfl⟩⟩
    apply Multiplicative.toAdd.injective
    funext i
    rw [Subsingleton.elim i 0]
    exact congrArg Multiplicative.toAdd h
  let βU : ↥(centerOf (Q)) →* Multiplicative (Fin 3 → F) := e1.comp β'
  have hcoord : ∀ (i : Fin 2) (x : Fin 3 → F), ∃ q : ↥(Q),
      Multiplicative.toAdd (β q) i = 0 ∧ Multiplicative.toAdd (β q) (1 - i) = x := by
    intro i x
    obtain ⟨q, hq⟩ := hβs (Multiplicative.ofAdd (fun j => if j = i then 0 else x))
    refine ⟨q, ?_, ?_⟩
    · rw [hq]; simp
    · rw [hq]
      have : (1 - i : Fin 2) ≠ i := by fin_cases i <;> decide
      simp [this]
  have hUW : ∀ i, centerOf (Q) ≤ burnsideC135_Wc β i := by
    intro i u hu
    refine burnsideC135_mem_Wc.mpr ⟨hUQ hu, ?_⟩
    have h1 : (⟨u, hUQ hu⟩ : ↥(Q)) ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf]
      exact hu
    rw [MonoidHom.mem_ker] at h1
    rw [h1]
    rfl
  have hker : ∀ (q : ↥(Q)), Multiplicative.toAdd (β q) 0 = 0 → Multiplicative.toAdd (β q) 1 = 0 →
      (q : G) ∈ centerOf (Q) := by
    intro q h0 h1
    have h2 : q ∈ β.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      funext j
      fin_cases j
      · exact h0
      · exact h1
    rw [hβk, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hconj : ∀ (l : ↥L) (q : ↥(Q)),
      Multiplicative.toAdd (β ⟨(l : G) * q * (l : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hLQ l.2) _).mp q.2⟩) =
      fun j => ((dualHom (slNat α l) : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β q) j := by
    intro l q
    funext j
    rw [hβeq l q _ rfl j, moduleAct_true_eq]
  have hnorm : ∀ i, L ≤ Subgroup.normalizer (burnsideC135_Wc β i : Set G) := by
    intro i
    refine burnsideC135_le_normalizer_of_conj fun l hl w hw => ?_
    obtain ⟨hwQ, hw0⟩ := burnsideC135_mem_Wc.mp hw
    refine burnsideC135_mem_Wc.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hLQ hl) _).mp hwQ, ?_⟩
    have := congrFun (hconj ⟨l, hl⟩ ⟨w, hwQ⟩) i
    rw [this, hw0, Matrix.mulVec_zero]
  refine ⟨βU, burnsideC135_slNat_surj hα.1, hLQ, hUW 1, hUW 0, burnsideC135_Wc_le 1,
    burnsideC135_Wc_le 0, ?_, ?_, hnorm 1, hnorm 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_antisymm (sup_le (burnsideC135_Wc_le 1) (burnsideC135_Wc_le 0)) fun q hq => ?_
    obtain ⟨q₁, hq₁1, hq₁0⟩ := hcoord 1 (Multiplicative.toAdd (β ⟨q, hq⟩) 0)
    have hq₁W : (q₁ : G) ∈ burnsideC135_Wc β 1 := burnsideC135_mem_Wc.mpr ⟨q₁.2, hq₁1⟩
    have hq₂W : (q₁ : G)⁻¹ * q ∈ burnsideC135_Wc β 0 := by
      refine burnsideC135_mem_Wc.mpr ⟨(Q).mul_mem ((Q).inv_mem q₁.2) hq, ?_⟩
      have e : (⟨(q₁ : G)⁻¹ * q, (Q).mul_mem ((Q).inv_mem q₁.2) hq⟩ : ↥(Q)) = q₁⁻¹ * ⟨q, hq⟩ := rfl
      rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply]
      have : (1 - 1 : Fin 2) = 0 := rfl
      rw [this] at hq₁0
      rw [hq₁0, neg_add_cancel]
    have e : q = (q₁ : G) * ((q₁ : G)⁻¹ * q) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq₁W) (Subgroup.mem_sup_right hq₂W)
  · refine le_antisymm (fun g hg => ?_) (le_inf (hUW 1) (hUW 0))
    obtain ⟨hgQ, hg1⟩ := burnsideC135_mem_Wc.mp hg.1
    obtain ⟨hgQ', hg0⟩ := burnsideC135_mem_Wc.mp hg.2
    exact hker ⟨g, hgQ⟩ hg0 hg1
  · exact he1.2.comp hβ's
  · rw [MonoidHom.ker_comp_of_injective β' e1 he1.1, hβ'k, Subgroup.bot_subgroupOf]
  · intro l u v huv
    show Multiplicative.toAdd (e1 (β' v)) = _
    have h := hβ'eq l u v huv 0
    rw [moduleAct_false_eq] at h
    exact h
  · intro x
    obtain ⟨q, hq1, hq0⟩ := hcoord 1 x
    refine ⟨⟨q, burnsideC135_mem_Wc.mpr ⟨q.2, hq1⟩⟩, ?_⟩
    rw [burnsideC135_βc_apply]
    apply Multiplicative.toAdd.injective
    exact hq0
  · refine Subgroup.ext fun w => ?_
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, burnsideC135_βc_apply]
    obtain ⟨hwQ, hw1⟩ := burnsideC135_mem_Wc.mp w.2
    constructor
    · intro h
      have h0 : Multiplicative.toAdd (β ⟨w, burnsideC135_Wc_le 1 w.2⟩) 0 = 0 :=
        congrArg Multiplicative.toAdd h
      exact hker _ h0 hw1
    · intro h
      have h1 : (⟨w, burnsideC135_Wc_le 1 w.2⟩ : ↥(Q)) ∈ β.ker := by
        rw [hβk, Subgroup.mem_subgroupOf]
        exact h
      rw [MonoidHom.mem_ker] at h1
      rw [h1]
      rfl
  · intro l u v huv
    rw [burnsideC135_βc_apply, burnsideC135_βc_apply, toAdd_ofAdd, toAdd_ofAdd]
    have e : (⟨v, burnsideC135_Wc_le 1 v.2⟩ : ↥(Q)) = ⟨(l : G) * (u : G) * (l : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hLQ l.2) _).mp (burnsideC135_Wc_le 1 u.2)⟩ :=
      Subtype.ext huv
    rw [e, hconj l ⟨u, burnsideC135_Wc_le 1 u.2⟩, coe_dualHom]
  · intro x
    obtain ⟨q, hq0, hq1⟩ := hcoord 0 x
    refine ⟨⟨q, burnsideC135_mem_Wc.mpr ⟨q.2, hq0⟩⟩, ?_⟩
    rw [burnsideC135_βc_apply]
    apply Multiplicative.toAdd.injective
    exact hq1
  · refine Subgroup.ext fun w => ?_
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, burnsideC135_βc_apply]
    obtain ⟨hwQ, hw0⟩ := burnsideC135_mem_Wc.mp w.2
    constructor
    · intro h
      have h1 : Multiplicative.toAdd (β ⟨w, burnsideC135_Wc_le 0 w.2⟩) 1 = 0 :=
        congrArg Multiplicative.toAdd h
      exact hker _ hw0 h1
    · intro h
      have h1 : (⟨w, burnsideC135_Wc_le 0 w.2⟩ : ↥(Q)) ∈ β.ker := by
        rw [hβk, Subgroup.mem_subgroupOf]
        exact h
      rw [MonoidHom.mem_ker] at h1
      rw [h1]
      rfl
  · intro l u v huv
    rw [burnsideC135_βc_apply, burnsideC135_βc_apply, toAdd_ofAdd, toAdd_ofAdd]
    have e : (⟨v, burnsideC135_Wc_le 0 v.2⟩ : ↥(Q)) = ⟨(l : G) * (u : G) * (l : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hLQ l.2) _).mp (burnsideC135_Wc_le 0 u.2)⟩ :=
      Subtype.ext huv
    rw [e, hconj l ⟨u, burnsideC135_Wc_le 0 u.2⟩, coe_dualHom]

end Coords

section Twist

variable {F : Type} [Field F]

@[expose] def burnsideC135_mix (M : Matrix (Fin 2) (Fin 2) F) :
    Multiplicative (Fin 2 → Fin 3 → F) →* Multiplicative (Fin 2 → Fin 3 → F) :=
  AddMonoidHom.toMultiplicative
    { toFun := fun v i => ∑ j, M i j • v j
      map_zero' := by funext i; simp
      map_add' := fun v w => by funext i; simp [smul_add, Finset.sum_add_distrib] }

theorem burnsideC135_mix_apply (M : Matrix (Fin 2) (Fin 2) F)
    (v : Multiplicative (Fin 2 → Fin 3 → F)) (i : Fin 2) :
    Multiplicative.toAdd (burnsideC135_mix M v) i = ∑ j, M i j • Multiplicative.toAdd v j := rfl

theorem burnsideC135_mix_mix (M M' : Matrix (Fin 2) (Fin 2) F)
    (v : Multiplicative (Fin 2 → Fin 3 → F)) :
    burnsideC135_mix M' (burnsideC135_mix M v) = burnsideC135_mix (M' * M) v := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [burnsideC135_mix_apply, burnsideC135_mix_apply]
  simp only [burnsideC135_mix_apply, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem burnsideC135_mix_one (v : Multiplicative (Fin 2 → Fin 3 → F)) :
    burnsideC135_mix (1 : Matrix (Fin 2) (Fin 2) F) v = v := by
  classical
  apply Multiplicative.toAdd.injective
  funext i
  rw [burnsideC135_mix_apply, Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_smul]
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

variable [Finite G] {L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)}

theorem burnsideC135_twist {Q U : Subgroup G} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}
    (hβs : Function.Surjective β) (hβk : β.ker = U.subgroupOf Q)
    (hβeq : ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        (moduleAct true (α a : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i))
    {M M' : Matrix (Fin 2) (Fin 2) F} (hM : M' * M = 1) (hM' : M * M' = 1) :
    Function.Surjective ((burnsideC135_mix M).comp β) ∧
      ((burnsideC135_mix M).comp β).ker = U.subgroupOf Q ∧
      ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
        Multiplicative.toAdd (((burnsideC135_mix M).comp β) v) i =
          (moduleAct true (α a : GL (Fin 3) F)).mulVec
            (Multiplicative.toAdd (((burnsideC135_mix M).comp β) u) i) := by
  have hinj : Function.Injective (burnsideC135_mix M) := by
    intro v w h
    have := congrArg (burnsideC135_mix M') h
    rwa [burnsideC135_mix_mix, burnsideC135_mix_mix, hM, burnsideC135_mix_one,
      burnsideC135_mix_one] at this
  refine ⟨?_, ?_, ?_⟩
  · intro v
    obtain ⟨q, hq⟩ := hβs (burnsideC135_mix M' v)
    refine ⟨q, ?_⟩
    rw [MonoidHom.comp_apply, hq, burnsideC135_mix_mix, hM', burnsideC135_mix_one]
  · rw [MonoidHom.ker_comp_of_injective β _ hinj, hβk]
  · intro a u v huv i
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, burnsideC135_mix_apply,
      burnsideC135_mix_apply, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hβeq a u v huv j, Matrix.mulVec_smul]

end Twist

end CFSG.ASVolI

end
