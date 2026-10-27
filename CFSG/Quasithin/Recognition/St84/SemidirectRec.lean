module

public import CFSG.GroupTheory.InternalSemidirectEquiv

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.GroupTheory

variable {G : Type*} [Group G]

@[expose] noncomputable def parAct {P Q : Subgroup G} (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    {M : Type*} [Group M] (χ : ↥Q ≃* M) : ↥P →* MulAut M :=
  (MulAut.congr χ).toMonoidHom.comp (conjHom Q P hPQ)

theorem parAct_apply {P Q : Subgroup G} {hPQ : P ≤ Subgroup.normalizer (Q : Set G)}
    {M : Type*} [Group M] {χ : ↥Q ≃* M} (p : ↥P) (m : M) :
    parAct hPQ χ p m =
      χ ⟨(p : G) * ((χ.symm m : ↥Q) : G) * (p : G)⁻¹,
        (hPQ p.2 ((χ.symm m : ↥Q) : G)).mp (χ.symm m).2⟩ :=
  rfl

theorem parAct_of_mem {P Q : Subgroup G} {hPQ : P ≤ Subgroup.normalizer (Q : Set G)}
    {M : Type*} [Group M] {χ : ↥Q ≃* M} {q : G} (hqQ : q ∈ Q) (hqP : q ∈ P) :
    parAct hPQ χ ⟨q, hqP⟩ = MulAut.conj (χ ⟨q, hqQ⟩) := by
  refine MulEquiv.ext fun m => ?_
  change χ (conjHom Q P hPQ ⟨q, hqP⟩ (χ.symm m)) = MulAut.conj (χ ⟨q, hqQ⟩) m
  rw [MulAut.conj_apply]
  conv_rhs => rw [← χ.apply_symm_apply m]
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem parAct_eq_one_iff {P Q : Subgroup G} {hPQ : P ≤ Subgroup.normalizer (Q : Set G)}
    {M : Type*} [Group M] {χ : ↥Q ≃* M} (p : ↥P) :
    parAct hPQ χ p = 1 ↔ (p : G) ∈ Subgroup.centralizer (Q : Set G) := by
  constructor
  · intro hp
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h := congrArg (fun f : MulAut M => f (χ ⟨q, hq⟩)) hp
    rw [parAct_apply] at h
    simp only [MulAut.one_apply] at h
    have h' : (⟨(p : G) * ((χ.symm (χ ⟨q, hq⟩) : ↥Q) : G) * (p : G)⁻¹,
        (hPQ p.2 ((χ.symm (χ ⟨q, hq⟩) : ↥Q) : G)).mp (χ.symm (χ ⟨q, hq⟩)).2⟩ : ↥Q) = ⟨q, hq⟩ :=
      χ.injective (by simpa using h)
    have hcoe : (p : G) * q * (p : G)⁻¹ = q := by simpa using congrArg Subtype.val h'
    calc q * (p : G) = ((p : G) * q * (p : G)⁻¹) * (p : G) := by rw [hcoe]
      _ = (p : G) * q := by rw [mul_assoc, inv_mul_cancel, mul_one]
  · intro hp
    refine MulEquiv.ext fun m => ?_
    rw [parAct_apply, MulAut.one_apply]
    conv_rhs => rw [← χ.apply_symm_apply m]
    congr 1
    apply Subtype.ext
    change (p : G) * ((χ.symm m : ↥Q) : G) * (p : G)⁻¹ = ((χ.symm m : ↥Q) : G)
    have hcomm : (p : G) * ((χ.symm m : ↥Q) : G) = ((χ.symm m : ↥Q) : G) * (p : G) :=
      (Subgroup.mem_centralizer_iff.mp hp ((χ.symm m : ↥Q) : G) (χ.symm m).2).symm
    calc (p : G) * ((χ.symm m : ↥Q) : G) * (p : G)⁻¹
        = ((χ.symm m : ↥Q) : G) * (p : G) * (p : G)⁻¹ := by rw [hcomm]
      _ = ((χ.symm m : ↥Q) : G) := by rw [mul_assoc, mul_inv_cancel, mul_one]

theorem parAct_trans {P Q : Subgroup G} {hPQ : P ≤ Subgroup.normalizer (Q : Set G)}
    {M : Type*} [Group M] {χ : ↥Q ≃* M} (g : MulAut M) (p : ↥P) :
    parAct hPQ (χ.trans g) p = g * parAct hPQ χ p * g⁻¹ := by
  have hcongr_trans : MulAut.congr (χ.trans g) = (MulAut.congr χ).trans (MulAut.congr g) := by
    ext φ
    simp [MulAut.congr, MulEquiv.trans_apply]
  have hcongr_self : MulAut.congr g = MulAut.conj g := by
    ext φ
    simp [MulAut.congr, MulAut.conj_apply, MulEquiv.trans_apply]
  have h1 : parAct hPQ (χ.trans g) p = (MulAut.congr (χ.trans g)) (conjHom Q P hPQ p) := rfl
  have h2 : parAct hPQ χ p = (MulAut.congr χ) (conjHom Q P hPQ p) := rfl
  rw [h1, h2, hcongr_trans, MulEquiv.trans_apply, hcongr_self, MulAut.conj_apply]

@[expose] noncomputable def restrictEquiv {G' : Type*} [Group G'] {P' Q' : Subgroup G'}
    {P Q : Subgroup G} (Φ : ↥P ≃* ↥P') (hQP : Q ≤ P)
    (hΦQ : ∀ x : ↥P, (x : G) ∈ Q ↔ (Φ x : G') ∈ Q') (hQ'P' : Q' ≤ P') :
    ↥Q ≃* ↥Q' := by
  classical
  have hmap : (Q.subgroupOf P).map (Φ : ↥P →* ↥P') = Q'.subgroupOf P' := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (hΦQ q).mp hq
    · intro hx
      refine ⟨Φ.symm ⟨x, hQ'P' hx⟩, (hΦQ (Φ.symm ⟨x, hQ'P' hx⟩)).mpr ?_, ?_⟩
      · have hx' : (x : G') ∈ Q' := hx
        simpa only [Φ.apply_symm_apply] using hx'
      · exact Φ.apply_symm_apply ⟨x, hQ'P' hx⟩
  exact (Subgroup.subgroupOfEquivOfLe hQP).symm.trans
    ((Φ.subgroupMap (Q.subgroupOf P)).trans
      ((MulEquiv.subgroupCongr hmap).trans (Subgroup.subgroupOfEquivOfLe hQ'P')))

theorem restrictEquiv_apply {G' : Type*} [Group G'] {P' Q' : Subgroup G'}
    {P Q : Subgroup G} (Φ : ↥P ≃* ↥P') (hQP : Q ≤ P)
    (hΦQ : ∀ x : ↥P, (x : G) ∈ Q ↔ (Φ x : G') ∈ Q') (hQ'P' : Q' ≤ P') (q : ↥Q) :
    ((restrictEquiv Φ hQP hΦQ hQ'P' q : ↥Q') : G') =
      Φ ⟨(q : G), hQP q.2⟩ := by
  classical
  simp [restrictEquiv]
  rfl

theorem nonempty_mulEquiv_semidirect {P Q A : Subgroup G} [Finite ↥P] (hQP : Q ≤ P)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hAP : A ≤ P) (hAQ : A ⊓ Q = ⊥)
    (hcard : Nat.card Q * Nat.card A = Nat.card P) {M : Type*} [Group M] (χ : ↥Q ≃* M)
    {H : Subgroup (MulAut M)} (e : ↥A ≃* ↥H)
    (he : ∀ a : ↥A, (e a : MulAut M) = parAct hPQ χ (Subgroup.inclusion hAP a)) :
    Nonempty (↥P ≃* M ⋊[H.subtype] ↥H) := by
  classical
  have hK : A ≤ Subgroup.normalizer (Q : Set G) := hAP.trans hPQ
  have hdisj : Disjoint Q A := by
    rw [disjoint_iff]
    rw [inf_comm]
    exact hAQ
  have hsup_le : Q ⊔ A ≤ P := sup_le hQP hAP
  have hcard_sup : Nat.card ↥(Q ⊔ A) = Nat.card Q * Nat.card A := by
    calc Nat.card ↥(Q ⊔ A) = Nat.card (↥Q ⋊[conjHom Q A hK] ↥A) :=
          (Nat.card_congr (semiEquivSup hK hdisj).toEquiv).symm
      _ = Nat.card Q * Nat.card A := SemidirectProduct.card
  have hsup : Q ⊔ A = P :=
    Subgroup.eq_of_le_of_card_ge hsup_le (by rw [hcard_sup, hcard])
  have hcongr : ∀ a : ↥A, (conjHom Q A hK a).trans χ = χ.trans (H.subtype (e a)) := by
    intro a
    ext m
    change χ ((conjHom Q A hK a) m) = (e a : MulAut M) (χ m)
    rw [he a, parAct_apply, MulEquiv.symm_apply_apply]
    rfl
  exact ⟨((semiEquivSup hK hdisj).trans
      (MulEquiv.subgroupCongr hsup)).symm.trans (SemidirectProduct.congr χ e hcongr)⟩

@[expose] def ActsAs {Q : Subgroup G} {M : Type*} [Group M] (χ : ↥Q ≃* M) (g : G) (α : MulAut M) :
    Prop :=
  ∀ x y : ↥Q, (y : G) = g * x * g⁻¹ → χ y = α (χ x)

theorem parAct_eq_of_actsAs {P Q : Subgroup G} {hPQ : P ≤ Subgroup.normalizer (Q : Set G)}
    {M : Type*} [Group M] {χ : ↥Q ≃* M} {g : G} (hg : g ∈ P) {α : MulAut M}
    (h : ActsAs χ g α) :
    parAct hPQ χ ⟨g, hg⟩ = α := by
  refine MulEquiv.ext fun m => ?_
  rw [parAct_apply]
  have h1 := h (χ.symm m)
    ⟨(g : G) * ((χ.symm m : ↥Q) : G) * (g : G)⁻¹,
      (hPQ hg ((χ.symm m : ↥Q) : G)).mp (χ.symm m).2⟩ rfl
  rwa [χ.apply_symm_apply] at h1

end CFSG.Quasithin.F112R.St84
