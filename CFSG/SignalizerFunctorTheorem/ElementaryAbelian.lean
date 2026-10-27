module

public import CFSG.LocalAnalysis.SignalizerFunctor.Helpers
public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryComplements
import CFSG.LocalAnalysis.SignalizerFunctor.RankTransport

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem

variable {G : Type*} [Group G]

private theorem exists_map_subtype {A E : Subgroup G} (hE : E ≤ A) :
    ∃ E' : Subgroup A, E'.map A.subtype = E :=
  ⟨E.subgroupOf A, by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hE]⟩

private abbrev commGroupOfIsMulCommutative (A : Subgroup G) [IsMulCommutative A] : CommGroup A :=
  { A.toGroup with mul_comm := mul_comm' }

private theorem disjoint_of_map_subtype_inf_eq_bot {A : Subgroup G} {E' F' : Subgroup A}
    (h : E'.map A.subtype ⊓ F'.map A.subtype = ⊥) : Disjoint E' F' := by
  rw [disjoint_iff, ← Subgroup.map_eq_bot_iff_of_injective _ A.subtype_injective,
    Subgroup.map_inf _ _ _ A.subtype_injective]
  exact h

theorem card_sup_of_le_elemAbelian [Finite G] {p : ℕ} {A E F : Subgroup G}
    (hA : IsElemAbelian p A) (hE : E ≤ A) (hF : F ≤ A) (hdisj : E ⊓ F = ⊥) :
    Nat.card (E ⊔ F : Subgroup G) = Nat.card E * Nat.card F := by
  have := hA.1
  let _ := commGroupOfIsMulCommutative A
  obtain ⟨E', rfl⟩ := exists_map_subtype hE
  obtain ⟨F', rfl⟩ := exists_map_subtype hF
  rw [← Subgroup.map_sup]
  simp only [Subgroup.card_map_of_injective A.subtype_injective]
  exact CFSG.SignalizerFunctor.Helpers.cardinality_sup_of_disjoint_commutative E' F'
    (disjoint_of_map_subtype_inf_eq_bot hdisj)

private theorem sup_inf_assoc_of_le_elemAbelian {p : ℕ} {A E F S : Subgroup G}
    (hA : IsElemAbelian p A) (hE : E ≤ A) (hF : F ≤ A) (hS : S ≤ A) (hES : E ≤ S) :
    (E ⊔ F) ⊓ S = E ⊔ F ⊓ S := by
  have := hA.1
  let _ := commGroupOfIsMulCommutative A
  obtain ⟨E', rfl⟩ := exists_map_subtype hE
  obtain ⟨F', rfl⟩ := exists_map_subtype hF
  obtain ⟨S', rfl⟩ := exists_map_subtype hS
  rw [Subgroup.map_le_map_iff_of_injective A.subtype_injective] at hES
  rw [← Subgroup.map_sup, ← Subgroup.map_inf _ _ _ A.subtype_injective,
    ← Subgroup.map_inf _ _ _ A.subtype_injective, ← Subgroup.map_sup, sup_inf_assoc_of_le F' hES]

theorem exists_complement_containing [Finite G] {p : ℕ} (hp : p.Prime) {A E R : Subgroup G}
    (hA : IsElemAbelian p A) (hE : E ≤ A) (hR : R ≤ A) (hdisj : E ⊓ R = ⊥) :
    ∃ F : Subgroup G, F ≤ A ∧ R ≤ F ∧ E ⊓ F = ⊥ ∧ E ⊔ F = A := by
  have := hA.1
  let _ := commGroupOfIsMulCommutative A
  obtain ⟨E', rfl⟩ := exists_map_subtype hE
  obtain ⟨R', rfl⟩ := exists_map_subtype hR
  obtain ⟨C, hC⟩ := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isCompl_exists p hp A
    (fun x => Subtype.ext (hA.2 x x.2)) (E' ⊔ R')
  have hdisj' : Disjoint E' (R' ⊔ C) :=
    (disjoint_of_map_subtype_inf_eq_bot hdisj).disjoint_sup_right_of_disjoint_sup_left hC.disjoint
  refine ⟨(R' ⊔ C).map A.subtype, Subgroup.map_subtype_le _, Subgroup.map_mono le_sup_left, ?_, ?_⟩
  · rw [← Subgroup.map_inf _ _ _ A.subtype_injective, disjoint_iff.mp hdisj', Subgroup.map_bot]
  · rw [← Subgroup.map_sup, ← sup_assoc, hC.sup_eq_top, Subgroup.map_top, Subgroup.subtype_range]

theorem card_mul_card_complement [Finite G] {p : ℕ} {A E F : Subgroup G}
    (hA : IsElemAbelian p A) (hE : E ≤ A) (hF : F ≤ A) (hdisj : E ⊓ F = ⊥) (hsup : E ⊔ F = A) :
    Nat.card E * Nat.card F = Nat.card A := by
  rw [← card_sup_of_le_elemAbelian hA hE hF hdisj, hsup]

theorem complement_large [Finite G] {p k : ℕ} (hp : p.Prime) {A E F : Subgroup G}
    (hA : IsElemAbelian p A) (hE : E ∈ signalizerFunctorEk p k A) (hF : F ≤ A)
    (hdisj : E ⊓ F = ⊥) (hsup : E ⊔ F = A) (hlarge : p ^ (k + 3) ≤ Nat.card A) :
    p ^ 3 ≤ Nat.card F := by
  have hcard := card_mul_card_complement hA hE.1 hF hdisj hsup
  rw [hE.2] at hcard
  rw [← hcard, pow_add] at hlarge
  exact Nat.le_of_mul_le_mul_left hlarge (pow_pos hp.pos k)

theorem sup_mem_Ek_succ [Finite G] {p k : ℕ} {A E R : Subgroup G}
    (hA : IsElemAbelian p A) (hE : E ∈ signalizerFunctorEk p k A)
    (hR : R ∈ signalizerFunctorEk p 1 A) (hdisj : E ⊓ R = ⊥) :
    E ⊔ R ∈ signalizerFunctorEk p (k + 1) A := by
  refine ⟨sup_le hE.1 hR.1, ?_⟩
  rw [card_sup_of_le_elemAbelian hA hE.1 hR.1 hdisj, hE.2, hR.2, pow_one, pow_succ]

private theorem card_zpowers_of_isElemAbelian {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hA : IsElemAbelian p A) {x : G} (hxA : x ∈ A) (hx : x ≠ 1) :
    Nat.card (Subgroup.zpowers x) = p := by
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hA.2 x hxA)) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx
  · rw [Nat.card_zpowers, h]

theorem inf_eq_bot_of_not_le {p : ℕ} (hp : p.Prime) {E R : Subgroup G} [Finite G]
    (hR : Nat.card R = p) (hRE : ¬ R ≤ E) : E ⊓ R = ⊥ := by
  have hdvd : Nat.card (E ⊓ R : Subgroup G) ∣ p := hR ▸ Subgroup.card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · exact absurd (inf_eq_right.mp (Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hR]))) hRE

theorem exists_rankOne_disjoint_of_ne [Finite G] {p k : ℕ} (hp : p.Prime) {A E E' : Subgroup G}
    (hA : IsElemAbelian p A) (hE : E ∈ signalizerFunctorEk p k A)
    (hE' : E' ∈ signalizerFunctorEk p k A) (hne : E ≠ E') :
    ∃ R ∈ signalizerFunctorEk p 1 A, R ≤ E' ∧ E ⊓ R = ⊥ := by
  have hnle : ¬ E' ≤ E := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge h (by rw [hE.2, hE'.2])).symm
  obtain ⟨x, hxE', hxE⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hcard := card_zpowers_of_isElemAbelian hp hA (hE'.1 hxE') (fun h => hxE (h ▸ E.one_mem))
  refine ⟨Subgroup.zpowers x,
    ⟨Subgroup.zpowers_le.mpr (hE'.1 hxE'), by rw [hcard, pow_one]⟩,
    Subgroup.zpowers_le.mpr hxE', ?_⟩
  exact inf_eq_bot_of_not_le hp hcard (fun h => hxE (h (Subgroup.mem_zpowers x)))

theorem exists_hyperplane_decomposition [Finite G] {p k : ℕ} (hp : p.Prime) {A S : Subgroup G}
    (hA : IsElemAbelian p A) (hS : S ∈ signalizerFunctorEk p (k + 1) A) :
    ∃ E ∈ signalizerFunctorEk p k A, E ≤ S ∧
      ∃ R ∈ signalizerFunctorEk p 1 A, R ≤ S ∧ E ⊓ R = ⊥ ∧ E ⊔ R = S := by
  obtain ⟨E, hES, hEcard⟩ :=
    CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty p k hp S
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hA hS.1)
      (by rw [hS.2]; exact Nat.pow_le_pow_right hp.pos k.le_succ)
  have hnle : ¬ S ≤ E := fun h => by
    have hle := Subgroup.card_le_of_le h
    rw [hS.2, hEcard] at hle
    exact absurd hle (not_le.mpr (Nat.pow_lt_pow_succ hp.one_lt))
  obtain ⟨x, hxS, hxE⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hcard := card_zpowers_of_isElemAbelian hp hA (hS.1 hxS) (fun h => hxE (h ▸ E.one_mem))
  have hRS : Subgroup.zpowers x ≤ S := Subgroup.zpowers_le.mpr hxS
  have hdisj : E ⊓ Subgroup.zpowers x = ⊥ :=
    inf_eq_bot_of_not_le hp hcard (fun h => hxE (h (Subgroup.mem_zpowers x)))
  refine ⟨E, ⟨hES.trans hS.1, hEcard⟩, hES, Subgroup.zpowers x,
    ⟨hRS.trans hS.1, by rw [hcard, pow_one]⟩, hRS, hdisj, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (sup_le hES hRS) ?_
  rw [card_sup_of_le_elemAbelian hA (hES.trans hS.1) (hRS.trans hS.1) hdisj, hEcard, hcard, hS.2,
    pow_succ]

theorem inf_complement_mem_E1 [Finite G] {p k : ℕ} (hp : p.Prime) {A E F S : Subgroup G}
    (hA : IsElemAbelian p A) (hE : E ∈ signalizerFunctorEk p k A) (hF : F ≤ A)
    (hdisj : E ⊓ F = ⊥) (hsup : E ⊔ F = A) (hS : S ∈ signalizerFunctorEk p (k + 1) A)
    (hES : E ≤ S) :
    S ⊓ F ∈ signalizerFunctorEk p 1 F ∧ E ⊔ (S ⊓ F) = S := by
  have hmod : E ⊔ S ⊓ F = S := by
    rw [inf_comm S F, ← sup_inf_assoc_of_le_elemAbelian hA hE.1 hF hS.1 hES, hsup]
    exact inf_eq_right.mpr hS.1
  refine ⟨⟨inf_le_right, ?_⟩, hmod⟩
  have hdisj' : E ⊓ (S ⊓ F) = ⊥ :=
    disjoint_iff.mp ((disjoint_iff.mpr hdisj).mono_right inf_le_right)
  have hcard := card_sup_of_le_elemAbelian hA hE.1 (inf_le_left.trans hS.1) hdisj'
  rw [hmod, hS.2, hE.2, pow_succ] at hcard
  rw [pow_one]
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos k) hcard).symm

theorem centralizer_sup (H K : Subgroup G) :
    Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) =
      Subgroup.centralizer (H : Set G) ⊓ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  ext x
  simp only [Subgroup.mem_centralizer_iff, Set.mem_union, SetLike.mem_coe, or_imp,
    forall_and, Subgroup.mem_inf]

end CFSG.SignalizerFunctorTheorem
