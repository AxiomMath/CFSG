module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneS
import CFSG.GroupTheory.OddInversion

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W} {p : ℕ}

theorem s13_pCore_facts (A : Subgroup (MulAut W)) (p : ℕ) :
    (∀ g ∈ A, ∀ x ∈ pCoreOf p A, g * x * g⁻¹ ∈ pCoreOf p A) ∧ pCoreOf p A ≤ A ∧
      IsPGroup p ↥(pCoreOf p A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg r hr
    rw [pCoreOf] at hr ⊢
    obtain ⟨o', ho', rfl⟩ := hr
    exact ⟨⟨g, hg⟩ * o' * ⟨g, hg⟩⁻¹, CFSG.pCore_normal.conj_mem o' ho' _, rfl⟩
  · rw [pCoreOf]
    exact Subgroup.map_subtype_le _
  · rw [pCoreOf]
    exact CFSG.pCore_isPGroup.map _

private theorem w16g_mem_normalizer_commutator_zpowers {G : Type*} [Group G] {K : Subgroup G}
    {g x : G} (hgK : g ∈ normalizer (K : Set G)) (hgx : g * x = x * g) :
    g ∈ normalizer ((⁅K, zpowers x⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hgK ⊢
  rw [map_commutator, hgK, MonoidHom.map_zpowers]
  congr 2
  change g * x * g⁻¹ = x
  rw [hgx, mul_inv_cancel_right]

private theorem w16g_eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {x : G}
    (hx : orderOf x = 2) {g : G} (hg : g ∈ zpowers x) : g = 1 ∨ g = x := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
  have hx2 : x ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, ← hx, pow_orderOf_eq_one]
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
  · left
    rw [hm, zpow_mul, hx2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, hx2, one_zpow, one_mul, zpow_one]

private theorem w16g_mem_commutator_zpowers_of_conj_eq_inv {G : Type*} [Group G]
    {K : Subgroup G} {x : G} (hodd : Odd (Nat.card K)) {h : G} (hhK : h ∈ K)
    (hh : x * h * x⁻¹ = h⁻¹) : h ∈ ⁅K, zpowers x⁆ := by
  obtain ⟨d, ⟨hdK, hd⟩, hd2⟩ :=
    OddInversion.exists_sq_eq_of_mem_invertedSet hodd (t := x) ⟨hhK, hh⟩
  have e : ⁅d⁻¹, x⁆ = h⁻¹ := by
    rw [commutatorElement_def, inv_inv, ← hd2]
    calc d⁻¹ * x * d * x⁻¹ = d⁻¹ * (x * d * x⁻¹) := by group
      _ = (d ^ 2)⁻¹ := by rw [hd, sq, mul_inv_rev]
  have : h⁻¹ ∈ ⁅K, zpowers x⁆ :=
    e ▸ commutator_mem_commutator (K.inv_mem hdK) (mem_zpowers x)
  simpa using inv_mem this

private theorem w16g_commutator_zpowers_le_of_mem_normalizer {G : Type*} [Group G]
    {E : Subgroup G} {t : G} (htE : t ∈ normalizer (E : Set G)) : ⁅E, zpowers t⁆ ≤ E := by
  rw [commutator_le]
  intro e he s hs
  have hsE : s ∈ normalizer (E : Set G) := (zpowers_le.mpr htE) hs
  have h1 : s * e⁻¹ * s⁻¹ ∈ E := (mem_normalizer_iff.mp hsE e⁻¹).mp (inv_mem he)
  have h2 : ⁅e, s⁆ = e * (s * e⁻¹ * s⁻¹) := by rw [commutatorElement_def]; group
  rw [h2]
  exact mul_mem he h1

private theorem w16g_conj_commutatorElement_eq_inv {G : Type*} [Group G] {t : G}
    (ht : orderOf t = 2) (e : G) : t * ⁅e, t⁆ * t⁻¹ = ⁅e, t⁆⁻¹ := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hti : t⁻¹ = t := OddInversion.inv_eq_self_of_orderOf_eq_two ht
  have key : (e * t * e⁻¹ * t) * (t * e * t * e⁻¹) = 1 := by
    calc (e * t * e⁻¹ * t) * (t * e * t * e⁻¹)
        = e * t * e⁻¹ * (t * t) * e * t * e⁻¹ := by group
      _ = e * t * e⁻¹ * e * t * e⁻¹ := by rw [htt, mul_one]
      _ = e * (t * t) * e⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  rw [commutatorElement_def, hti]
  calc t * (e * t * e⁻¹ * t) * t = t * e * t * e⁻¹ * (t * t) := by group
    _ = t * e * t * e⁻¹ := by rw [htt, mul_one]
    _ = (e * t * e⁻¹ * t)⁻¹ := (inv_eq_of_mul_eq_one_right key).symm

private theorem w16g_commutator_commutator_zpowers_eq {G : Type*} [Group G] {E : Subgroup G}
    (hE : Odd (Nat.card E)) {t : G} (ht : orderOf t = 2)
    (htE : t ∈ normalizer (E : Set G)) : ⁅⁅E, zpowers t⁆, zpowers t⁆ = ⁅E, zpowers t⁆ := by
  have hle := w16g_commutator_zpowers_le_of_mem_normalizer htE
  have htK : t ∈ normalizer ((⁅E, zpowers t⁆ : Subgroup G) : Set G) :=
    w16g_mem_normalizer_commutator_zpowers htE rfl
  refine le_antisymm (w16g_commutator_zpowers_le_of_mem_normalizer htK) ?_
  rw [commutator_le]
  intro e he s hs
  rcases w16g_eq_one_or_eq_of_mem_zpowers ht hs with rfl | rfl
  · rw [commutatorElement_one_right]
    exact one_mem _
  · exact w16g_mem_commutator_zpowers_of_conj_eq_inv
      (hE.of_dvd_nat (card_dvd_of_le hle))
      (commutator_mem_commutator he (mem_zpowers _)) (w16g_conj_commutatorElement_eq_inv ht e)

private theorem w16g_p_ne_two (h : Cfg133 A t p) : p ≠ 2 := by
  intro hp2
  have hbot : pCoreOf p A = ⊥ := by rw [hp2]; exact h.hO2
  have hcomm : ⁅pCoreOf p A, Subgroup.zpowers t⁆ = ⊥ := by
    rw [hbot, Subgroup.commutator_bot_left]
  exact h.hP hcomm

private theorem w16g_orderOf_t (h : Cfg133 A t p) : orderOf t = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime h.ht2 h.ht1

theorem s13_P_facts (h : Cfg133 A t p) :
    ⁅pCoreOf p A, Subgroup.zpowers t⁆ ≤ pCoreOf p A ∧
      IsPGroup p ↥(⁅pCoreOf p A, Subgroup.zpowers t⁆) ∧
      ⁅pCoreOf p A, Subgroup.zpowers t⁆ ≠ ⊥ ∧
      (∀ x ∈ ⁅pCoreOf p A, Subgroup.zpowers t⁆,
        t * x * t⁻¹ ∈ ⁅pCoreOf p A, Subgroup.zpowers t⁆) ∧
      ⁅⁅pCoreOf p A, Subgroup.zpowers t⁆, Subgroup.zpowers t⁆ =
        ⁅pCoreOf p A, Subgroup.zpowers t⁆ ∧
      (∀ y ∈ pCoreOf p A, ∀ x ∈ ⁅pCoreOf p A, Subgroup.zpowers t⁆,
        y * x * y⁻¹ ∈ ⁅pCoreOf p A, Subgroup.zpowers t⁆) := by
  have hOp : IsPGroup p ↥(pCoreOf p A) := (s13_pCore_facts A p).2.2
  have hnormO : t ∈ normalizer (pCoreOf p A : Set (MulAut W)) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact (s13_pCore_facts A p).1 t h.htA x hx
    · intro hx
      have h' := (s13_pCore_facts A p).1 t⁻¹ (A.inv_mem h.htA) (t * x * t⁻¹) hx
      have e : t⁻¹ * (t * x * t⁻¹) * (t⁻¹)⁻¹ = x := by group
      rwa [e] at h'
  have hle : ⁅pCoreOf p A, Subgroup.zpowers t⁆ ≤ pCoreOf p A :=
    w16g_commutator_zpowers_le_of_mem_normalizer hnormO
  have hPp : IsPGroup p ↥(⁅pCoreOf p A, Subgroup.zpowers t⁆) := hOp.to_le hle
  have htP : t ∈ normalizer ((⁅pCoreOf p A, Subgroup.zpowers t⁆ : Subgroup (MulAut W)) :
      Set (MulAut W)) := w16g_mem_normalizer_commutator_zpowers hnormO rfl
  haveI : Fact p.Prime := ⟨h.hp⟩
  have hOodd : Odd (Nat.card ↥(pCoreOf p A)) := by
    obtain ⟨k, hk⟩ := hOp.exists_card_eq
    rw [hk]
    exact (h.hp.odd_of_ne_two (w16g_p_ne_two h)).pow
  have hPcomm : ⁅⁅pCoreOf p A, Subgroup.zpowers t⁆, Subgroup.zpowers t⁆ =
      ⁅pCoreOf p A, Subgroup.zpowers t⁆ :=
    w16g_commutator_commutator_zpowers_eq hOodd (w16g_orderOf_t h) hnormO
  have hOnormP : ∀ y ∈ pCoreOf p A, ∀ x ∈ ⁅pCoreOf p A, Subgroup.zpowers t⁆,
      y * x * y⁻¹ ∈ ⁅pCoreOf p A, Subgroup.zpowers t⁆ := by
    intro y hy
    have hgen : ∀ o ∈ pCoreOf p A, ∀ s ∈ Subgroup.zpowers t,
        y * ⁅o, s⁆ * y⁻¹ ∈ ⁅pCoreOf p A, Subgroup.zpowers t⁆ := by
      intro o ho s hs
      have h1 : ⁅y * o, s⁆ ∈ ⁅pCoreOf p A, Subgroup.zpowers t⁆ :=
        commutator_mem_commutator ((pCoreOf p A).mul_mem hy ho) hs
      have h2 : ⁅y, s⁆ ∈ ⁅pCoreOf p A, Subgroup.zpowers t⁆ :=
        commutator_mem_commutator hy hs
      have heq : y * ⁅o, s⁆ * y⁻¹ = ⁅y * o, s⁆ * ⁅y, s⁆⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
        group
      rw [heq]
      exact (⁅pCoreOf p A, Subgroup.zpowers t⁆).mul_mem h1
        ((⁅pCoreOf p A, Subgroup.zpowers t⁆).inv_mem h2)
    intro x hx
    refine Subgroup.closure_induction
      (k := {g : MulAut W | ∃ o ∈ pCoreOf p A, ∃ s ∈ Subgroup.zpowers t, ⁅o, s⁆ = g})
      (p := fun x _ => y * x * y⁻¹ ∈ ⁅pCoreOf p A, Subgroup.zpowers t⁆) ?_ ?_ ?_ ?_ hx
    · intro g hg
      obtain ⟨o, ho, s, hs, rfl⟩ := hg
      exact hgen o ho s hs
    · simpa using (⁅pCoreOf p A, Subgroup.zpowers t⁆).one_mem
    · intro a b ha hb ha' hb'
      have heq : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [heq]
      exact (⁅pCoreOf p A, Subgroup.zpowers t⁆).mul_mem ha' hb'
    · intro a ha ha'
      have heq : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [heq]
      exact (⁅pCoreOf p A, Subgroup.zpowers t⁆).inv_mem ha'
  exact ⟨hle, hPp, h.hP, fun x hx => (mem_normalizer_iff.mp htP x).mp hx, hPcomm, hOnormP⟩

theorem s13_p_facts (h : Cfg133 A t p) : p ≠ 2 ∧ p ≤ 7 := by
  obtain ⟨hle, hPp, hPne, htP, hPcomm, -⟩ := s13_P_facts h
  have hW' : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact h.hW w
  exact ⟨w16g_p_ne_two h,
    (w4Lem13_1_holds W hW' t (w16g_orderOf_t h) h.hrk p
      (⁅pCoreOf p A, Subgroup.zpowers t⁆) h.hp hPp hPne htP hPcomm).1⟩

end CFSG.LocalAnalysis.WeakClosure81
