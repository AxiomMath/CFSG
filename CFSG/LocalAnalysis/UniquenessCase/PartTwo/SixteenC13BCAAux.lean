module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c13bcA_mem_stabSub_of_map_eq {T : Type*} [CommGroup T] {W : Subgroup T}
    {e : MulAut T} (h : W.map e.toMonoidHom = W) : e ∈ stabSub W := by
  intro u
  constructor
  · intro hu
    have hu' : e u ∈ W.map e.toMonoidHom := by rw [h]; exact hu
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu'
    have : w = u := e.injective hwu
    rw [← this]
    exact hw
  · intro hu
    have hu' : e u ∈ W.map e.toMonoidHom := Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    rwa [h] at hu'

theorem s16c13bcA_wBar_isPGroup (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    IsPGroup 2 ↥(barSub ⊥ V hV (E3.wClos V D.k D.T)) :=
  s15_LP_isPGroup_barSub hV
    (D.sylowM.isPGroup.to_le (E3.wClos_le_of_forall fun A hA => hA.1))

theorem s16c13bcA_wBar_le_mbar (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    barSub ⊥ V hV (E3.wClos V D.k D.T) ≤ Mbar D.M ⊥ V hV :=
  barSub_mono ⊥ V hV ((E3.wClos_le_of_forall fun A hA => hA.1).trans D.sylowM.le)

theorem s16c13bcA_insp_of_fixing (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V) {p : ℕ}
    (hp : p ∈ D.sig) {n : Vtil ⊥ V h.isElemAbelian} (hn1 : n ≠ 1)
    (hnfix : n ∈ fixV (barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T)))
    {X : Subgroup (MulAut (Vtil ⊥ V h.isElemAbelian))}
    (hXM : X ≤ Mbar D.M ⊥ V h.isElemAbelian) (hXp : IsPGroup p X) (hXc : ¬ IsCyclic X)
    (hXn : ∀ x ∈ X, x n = n) : Insp1613U D V := by
  refine s16c13bc_insp_of_stable D h hp (Ut := Subgroup.zpowers n) ?_ ?_ hXM hXp hXc ?_
  · intro h0
    exact hn1 (Subgroup.zpowers_eq_bot.1 h0)
  · rw [Subgroup.zpowers_le]
    exact hnfix
  · intro x hx u hu
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [map_zpow, hXn x hx]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers n) i

theorem s16c13bcA_pair_group {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} (hp : p.Prime) {a b : Γ}
    (hao : orderOf a = p) (hbo : orderOf b = p) (hab : a * b = b * a)
    (hne : b ∉ Subgroup.zpowers a) :
    IsPGroup p (Subgroup.closure {a, b}) ∧ ¬ IsCyclic (Subgroup.closure {a, b}) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha2 : a ^ p = 1 := hao ▸ pow_orderOf_eq_one a
  have hb2 : b ^ p = 1 := hbo ▸ pow_orderOf_eq_one b
  set X : Subgroup Γ := Subgroup.closure {a, b} with hX
  have hs : ∀ x ∈ ({a, b} : Set Γ), ∀ y ∈ ({a, b} : Set Γ), x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hab
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hab.symm
    · rw [Set.mem_singleton_iff] at hx hy
      subst hx
      subst hy
      rfl
  have hcl1 : ∀ x ∈ X, ∀ y ∈ ({a, b} : Set Γ), x * y = y * x := by
    intro x hx y hy
    have hle : X ≤ Subgroup.centralizer {y} := by
      rw [hX, Subgroup.closure_le]
      intro u hu
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hs u hu y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  have hcl : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    have hle : X ≤ Subgroup.centralizer {x} := by
      rw [hX, Subgroup.closure_le]
      intro u hu
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hcl1 x hx u hu).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm
  have hpow : ∀ x ∈ X, x ^ p = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem u hu =>
      rcases hu with rfl | hu
      · exact ha2
      · rw [Set.mem_singleton_iff] at hu
        subst hu
        exact hb2
    | one => exact one_pow p
    | mul u v hu hv ihu ihv =>
      have hc : Commute u v := hcl u hu v hv
      rw [hc.mul_pow, ihu, ihv, one_mul]
    | inv u hu ihu => rw [inv_pow, ihu, inv_one]
  have haX : a ∈ X := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbX : b ∈ X := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  refine ⟨?_, ?_⟩
  · rw [IsPGroup.iff_orderOf]
    intro g
    have hg' : g ^ p = 1 := Subtype.ext (hpow g g.2)
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hg') with h1 | h1
    · exact ⟨0, by simpa using h1⟩
    · exact ⟨1, by simpa using h1⟩
  · intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hgp : g ^ p = 1 := Subtype.ext (hpow g g.2)
    have hcard : Nat.card X ∣ p := by
      rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
      exact orderOf_dvd_of_pow_eq_one hgp
    have hale : Subgroup.zpowers a ≤ X := Subgroup.zpowers_le.2 haX
    have hacard : Nat.card (Subgroup.zpowers a) = p := by
      rw [Nat.card_zpowers, hao]
    have hle : Nat.card X ≤ Nat.card (Subgroup.zpowers a) := by
      rw [hacard]
      exact Nat.le_of_dvd hp.pos hcard
    exact hne ((Subgroup.eq_of_le_of_card_ge hale hle) ▸ hbX)

theorem s16c13bcA_insp_of_pair (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V) {p : ℕ}
    (hp : p ∈ D.sig) {a b : MulAut (Vtil ⊥ V h.isElemAbelian)}
    (ha : a ∈ Mbar D.M ⊥ V h.isElemAbelian) (hb : b ∈ Mbar D.M ⊥ V h.isElemAbelian)
    (hao : orderOf a = p) (hbo : orderOf b = p) (hab : a * b = b * a)
    (hne : b ∉ Subgroup.zpowers a) {n : Vtil ⊥ V h.isElemAbelian} (hn1 : n ≠ 1)
    (hnfix : n ∈ fixV (barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T)))
    (han : a n = n) (hbn : b n = n) : Insp1613U D V := by
  obtain ⟨hXp, hXc⟩ := s16c13bcA_pair_group (D.sig_prime p hp).1 hao hbo hab hne
  refine s16c13bcA_insp_of_fixing D h hp hn1 hnfix (X := Subgroup.closure {a, b}) ?_ hXp hXc ?_
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hb
  · intro x hx
    have hle : Subgroup.closure ({a, b} : Set (MulAut (Vtil ⊥ V h.isElemAbelian))) ≤
        MulAction.stabilizer (MulAut (Vtil ⊥ V h.isElemAbelian)) n := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | hy
      · exact han
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hbn
    exact hle hx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
