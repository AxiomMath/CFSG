module

public import CFSG.Quasithin.EmptyFaithful.S1422Center
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Quasithin

open CFSG.Open

theorem IsQ8Sq.of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) (h : IsQ8Sq P) :
    IsQ8Sq Q := by
  obtain ⟨hcard, A, B, ⟨hAB, hgen⟩, ⟨eA⟩, ⟨eB⟩⟩ := h
  refine ⟨by rw [← Nat.card_congr e.toEquiv, hcard], A.map e.toMonoidHom, B.map e.toMonoidHom,
    ⟨?_, ?_⟩, ⟨(e.subgroupMap A).symm.trans eA⟩, ⟨(e.subgroupMap B).symm.trans eB⟩⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (hAB ha) b hb
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    exact congrArg e this
  · rw [← Subgroup.map_sup, hgen, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.surjective

@[expose] noncomputable def pCoreEquiv {G : Type*} [Group G] (H : Subgroup G) :
    ↥(CFSG.pCore 2 ↥H) ≃* ↥(pCoreOf 2 H) :=
  (MulEquiv.subgroupCongr (CFSG.pCore_eq_open ↥H 2)).trans
    (Subgroup.equivMapOfInjective (CFSG.Open.pCore 2 ↥H) H.subtype H.subtype_injective)

theorem pCoreEquiv_coe {G : Type*} [Group G] (H : Subgroup G) (x : ↥(CFSG.pCore 2 ↥H)) :
    ((pCoreEquiv H x : ↥(pCoreOf 2 H)) : G) = (((x : ↥H)) : G) := rfl

theorem sq_central_of_q8 {P : Type*} [Group P] {A B : Subgroup P}
    (hAB : A ≤ Subgroup.centralizer (B : Set P)) (hgen : A ⊔ B = ⊤) (eA : A ≃* QuaternionGroup 2)
    (a : A) : ((a : P) ^ 2) ∈ Subgroup.center P := by
  have q8sq : ∀ q : QuaternionGroup 2, ∀ y : QuaternionGroup 2, q ^ 2 * y = y * q ^ 2 := by decide
  rw [Subgroup.mem_center_iff]
  intro g
  refine (central_of_commutes hAB hgen (w := (a : P) ^ 2) (fun a' ha' => ?_) (fun b hb => ?_) g).symm
  · have h1 : (a ^ 2) * (⟨a', ha'⟩ : A) = (⟨a', ha'⟩ : A) * a ^ 2 := by
      apply eA.injective
      simp only [map_mul, map_pow]
      exact q8sq _ _
    exact congrArg Subtype.val h1
  · have hba : Commute b (a : P) := Subgroup.mem_centralizer_iff.mp (hAB a.2) b hb
    have hbw : Commute b ((a : P) ^ 2) := hba.pow_right 2
    exact hbw.eq.symm

theorem comm_central_of_q8 {P : Type*} [Group P] {A B : Subgroup P}
    (hAB : A ≤ Subgroup.centralizer (B : Set P)) (hgen : A ⊔ B = ⊤) (eA : A ≃* QuaternionGroup 2)
    (a a' : A) : ((a : P) * a' * (a : P)⁻¹ * (a' : P)⁻¹) ∈ Subgroup.center P := by
  have q8comm : ∀ q r y : QuaternionGroup 2, (q * r * q⁻¹ * r⁻¹) * y = y * (q * r * q⁻¹ * r⁻¹) := by
    decide
  rw [Subgroup.mem_center_iff]
  intro g
  refine (central_of_commutes hAB hgen (w := (a : P) * a' * (a : P)⁻¹ * (a' : P)⁻¹)
    (fun c hc => ?_) (fun b hb => ?_) g).symm
  · have h1 : (a * a' * a⁻¹ * a'⁻¹) * (⟨c, hc⟩ : A) = (⟨c, hc⟩ : A) * (a * a' * a⁻¹ * a'⁻¹) := by
      apply eA.injective
      simp only [map_mul, map_inv]
      exact q8comm _ _ _
    exact congrArg Subtype.val h1
  · have hba : Commute b (a : P) := Subgroup.mem_centralizer_iff.mp (hAB a.2) b hb
    have hba' : Commute b (a' : P) := Subgroup.mem_centralizer_iff.mp (hAB a'.2) b hb
    have hbw : Commute b ((a : P) * a' * (a : P)⁻¹ * (a' : P)⁻¹) :=
      ((hba.mul_right hba').mul_right hba.inv_right).mul_right hba'.inv_right
    exact hbw.eq.symm

theorem card_center_of_centerOrderTwo {P : Type*} [Group P] (h : CenterOrderTwo P) :
    Nat.card (Subgroup.center P) = 2 := by
  obtain ⟨w, hw1, hwc, hu⟩ := h
  have hwm : w ∈ Subgroup.center P := Subgroup.mem_center_iff.mpr fun g => (hwc g).symm
  refine (Nat.card_eq_two_iff' (1 : Subgroup.center P)).mpr ⟨⟨w, hwm⟩, ?_, ?_⟩
  · exact fun h1 => hw1 (congrArg Subtype.val h1)
  · intro z hz
    have hz1 : (z : P) ≠ 1 := fun h1 => hz (Subtype.ext h1)
    have hzc : ∀ y : P, (z : P) * y = y * z := fun y => (Subgroup.mem_center_iff.mp z.2 y).symm
    rcases hu z hzc with h1 | h1
    · exact absurd h1 hz1
    · exact Subtype.ext h1

theorem isExtraspecial_of_isQ8Sq {P : Type*} [Group P] [Finite P] (h : IsQ8Sq P) :
    CFSG.IsExtraspecial 2 P := by
  have hc := centerOrderTwo_of_isQ8Sq h
  obtain ⟨-, A, B, ⟨hAB, hgen⟩, ⟨eA⟩, ⟨eB⟩⟩ := h
  have hBA : B ≤ Subgroup.centralizer (A : Set P) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hAB ha) y hy).symm
  have hgen' : B ⊔ A = ⊤ := by rw [sup_comm]; exact hgen
  let φ : A × B →* P := MonoidHom.noncommCoprod A.subtype B.subtype
    (fun a b => (Subgroup.mem_centralizer_iff.mp (hAB a.2) b b.2).symm)
  have hφ : ∀ p : A × B, φ p = (p.1 : P) * p.2 := fun _ => rfl
  have hφsurj : ∀ x : P, ∃ p : A × B, φ p = x := by
    intro x
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hAB (hgen ▸ Subgroup.mem_top x)
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hsq : ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
    intro x
    obtain ⟨⟨a, b⟩, rfl⟩ := hφsurj x
    rw [← map_pow]
    have : φ ((a, b) ^ 2) = (a : P) ^ 2 * (b : P) ^ 2 := by
      rw [Prod.pow_mk, hφ]
      rfl
    rw [this]
    exact Subgroup.mul_mem _ (sq_central_of_q8 hAB hgen eA a) (sq_central_of_q8 hBA hgen' eB b)
  have hcomm : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center P := by
    intro x y
    obtain ⟨⟨a, b⟩, rfl⟩ := hφsurj x
    obtain ⟨⟨a', b'⟩, rfl⟩ := hφsurj y
    have e : (a, b) * (a', b') * (a, b)⁻¹ * (a', b')⁻¹ =
        ((a * a' * a⁻¹ * a'⁻¹ : A), (b * b' * b⁻¹ * b'⁻¹ : B)) := rfl
    have key : φ (a, b) * φ (a', b') * (φ (a, b))⁻¹ * (φ (a', b'))⁻¹ =
        φ ((a, b) * (a', b') * (a, b)⁻¹ * (a', b')⁻¹) := by
      simp only [map_mul, map_inv]
    have : φ (a, b) * φ (a', b') * (φ (a, b))⁻¹ * (φ (a', b'))⁻¹ =
        ((a : P) * a' * (a : P)⁻¹ * (a' : P)⁻¹) * ((b : P) * b' * (b : P)⁻¹ * (b' : P)⁻¹) := by
      rw [key, e, hφ]
      rfl
    rw [this]
    exact Subgroup.mul_mem _ (comm_central_of_q8 hAB hgen eA a a')
      (comm_central_of_q8 hBA hgen' eB b b')
  refine ⟨card_center_of_centerOrderTwo hc, ?_, ?_⟩
  ·
    have : IsMulCommutative (P ⧸ Subgroup.center P) := ⟨⟨fun a b => by
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have := hcomm y⁻¹ x⁻¹
      simpa [mul_assoc] using this⟩⟩
    refine { exponent_dvd_p := ?_ }
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro g
    induction g using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hsq x
  ·
    obtain ⟨q, r, hqr⟩ : ∃ q r : QuaternionGroup 2, q * r ≠ r * q := by decide
    refine ⟨⟨(↑(eA.symm q : P) : P ⧸ Subgroup.center P), 1, ?_⟩⟩
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    have := Subgroup.mem_center_iff.mp h1 (eA.symm r : P)
    apply hqr
    have h2 : (eA.symm r : A) * eA.symm q = eA.symm q * eA.symm r := Subtype.ext this
    have h3 := congrArg eA h2
    simp only [map_mul, MulEquiv.apply_symm_apply] at h3
    exact h3.symm

end CFSG.Quasithin
