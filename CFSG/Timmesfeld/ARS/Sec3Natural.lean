module

public import CFSG.Timmesfeld.ARS.BasicTwoGroup
public import CFSG.Timmesfeld.ARS.NaturalModule
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Matrix
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec3

theorem opposite_conjSub {A B : Subgroup G} (h : Opposite A B) (g : G) :
    Opposite (conjSub A g) (conjSub B g) := by
  refine ⟨fun e => h.1 ((map_conj_inj).1 e), fun x hx hx1 => ?_, fun x hx hx1 => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := hx
    have ha1 : a ≠ 1 := fun h1 => hx1 (by rw [h1]; simp)
    obtain ⟨b, hb, hb1, hab⟩ := h.2.1 a ha ha1
    refine ⟨g * b * g⁻¹, conj_mem_conjSub g hb, fun h1 => hb1 (conj_eq_one_iff.1 h1), ?_⟩
    rw [← conjSub_mul, ← conjSub_mul, show g * b * g⁻¹ * g = g * b by group,
      show (MulAut.conj g).toMonoidHom a * g = g * a by simp, conjSub_mul, conjSub_mul B g a,
      hab]
  · obtain ⟨b, hb, rfl⟩ := hx
    have hb1 : b ≠ 1 := fun h1 => hx1 (by rw [h1]; simp)
    obtain ⟨a, ha, ha1, hab⟩ := h.2.2 b hb hb1
    refine ⟨g * a * g⁻¹, conj_mem_conjSub g ha, fun h1 => ha1 (conj_eq_one_iff.1 h1), ?_⟩
    rw [← conjSub_mul, ← conjSub_mul, show g * a * g⁻¹ * g = g * a by group,
      show (MulAut.conj g).toMonoidHom b * g = g * b by simp, conjSub_mul, conjSub_mul A g b,
      hab]

theorem special_conjSub (hR : IsRootClass R) {A B : Subgroup G} (h : Special R A B) (g : G) :
    Special R (conjSub A g) (conjSub B g) := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : ⁅conjSub A g, conjSub B g⁆ = conjSub ⁅A, B⁆ g := (Subgroup.map_commutator _ _ _).symm
  rw [Special, e]
  exact ⟨hR.conjSub_mem h1 g, h2.conjSub g, h3.conjSub g⟩

section Natural

variable [Finite G] {A B C : Subgroup G}

theorem special_conjSub_of_mem_lambdaSet (hR : IsRootClass R) (hA : A ∈ R)
    (hAB : Opposite A B) (hAC : C ∈ lambdaSet R A) (hBC : C ∈ psiSet R B) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) : Special R A (conjSub C b) := by
  have hCR : C ∈ R := hAC.1.1
  have hCb : conjSub C b ∈ R := hR.conjSub_mem hCR b
  obtain ⟨a, ha, -, hab⟩ := hAB.2.2 b hb hb1
  have hop : Opposite A (conjSub A b) := by
    have := opposite_conjSub hAB a
    rwa [conjSub_of_mem ha, hab] at this
  have hnc : ¬ Commuting A (conjSub C b) :=
    not_commuting_of_opposite_of_mem_lambdaSet hR hA hop (conjSub_mem_lambdaSet hR hAC b)
  have hcomm : Commuting (conjSub C b) C := by
    have h1 : Commuting (⁅C, B⁆ ⊔ C) C := by
      refine Commuting.sup_left ?_ (hR.commuting_self hCR)
      rw [Subgroup.commutator_comm]
      exact hBC.2.2.2
    exact h1.mono (conjSub_le_commutator_sup hb) le_rfl
  have hno : ¬ Opposite A (conjSub C b) := fun h =>
    not_commuting_of_opposite_of_mem_lambdaSet hR hCb h.symm hAC hcomm
  have hne : A ≠ conjSub C b := fun e => hnc (e ▸ hR.commuting_self hA)
  rcases hR.rel A hA _ hCb hne with h | h | h
  · exact absurd h hnc
  · exact absurd h hno
  · exact h

omit [Finite G] in
theorem commute_conj_of_mem_psiSet (hR : IsRootClass R) (hBC : C ∈ psiSet R B) {b c c' : G}
    (hb : b ∈ B) (hc : c ∈ C) (hc' : c' ∈ C) : Commute c' (b * c * b⁻¹) := by
  have h1 : Commuting (⁅C, B⁆ ⊔ C) C := by
    refine Commuting.sup_left ?_ (hR.commuting_self hBC.1)
    rw [Subgroup.commutator_comm]
    exact hBC.2.2.2
  exact (h1 _ (conjSub_le_commutator_sup hb (conj_mem_conjSub b hc)) c' hc').symm

theorem commutatorElement_conj_eq (hR : IsRootClass R) (hiso : NoIsolated R) (hA : A ∈ R)
    (hB : B ∈ R) (hAB : Opposite A B) (hAC : C ∈ lambdaSet R A) (hBC : C ∈ psiSet R B)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {b : G} (hb : b ∈ B) (hab : conjSub A b = conjSub B a)
    {c : G} (hc : c ∈ C) : ⁅b * c * b⁻¹, a⁆ = c⁻¹ := by
  have hCR : C ∈ R := hAC.1.1
  have hsqA := hR.mul_self A hA
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [conjSub_one] at hab
    apply hAB.1
    have : conjSub (conjSub B a) a⁻¹ = B := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
    rw [← this, ← hab, conjSub_of_mem (A.inv_mem ha)]
  have hsp := special_conjSub_of_mem_lambdaSet hR hA hAB hAC hBC hb hb1
  have hyC : b * c * b⁻¹ ∈ conjSub C b := conj_mem_conjSub b hc
  have ha2 : a * a = 1 := hsqA a ha
  have hb2 : b * b = 1 := hR.mul_self B hB b hb
  have hbraid : a * b * a = b * a * b := hAB.mul_mul_eq hsqA ha ha1 hb hab
  have hac : Commute a c := hAC.1.2.2 a ha c hc
  have hcy : Commute c (b * c * b⁻¹) := commute_conj_of_mem_psiSet hR hBC hb hc hc
  set y := b * c * b⁻¹ with hy
  set n := c * ⁅y, a⁆ with hn
  have hnA : ∀ a' ∈ A, Commute a' n := by
    intro a' ha'
    refine Commute.mul_right (hAC.1.2.2 a' ha' c hc) ?_
    have hmem : ⁅y, a⁆ ∈ ⁅A, conjSub C b⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hyC ha
    exact (hsp.2.1 _ hmem a' ha').symm
  have hnb : Commute b n := by
    have hc2 : c * c = 1 := hR.mul_self C hCR c hc
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
    have hyy : y = b * c * b := by rw [hy, hbinv]
    have hyinv : y⁻¹ = y := by rw [hyy, mul_inv_rev, mul_inv_rev, hbinv, hcinv, ← mul_assoc]
    have R1 : ∀ x, b * (a * (b * x)) = a * (b * (a * x)) := fun x => by
      calc b * (a * (b * x)) = (b * a * b) * x := by simp only [mul_assoc]
        _ = (a * b * a) * x := by rw [hbraid]
        _ = a * (b * (a * x)) := by simp only [mul_assoc]
    have R1' : b * (a * b) = a * (b * a) := by
      calc b * (a * b) = b * a * b := by simp only [mul_assoc]
        _ = a * b * a := by rw [hbraid]
        _ = a * (b * a) := by simp only [mul_assoc]
    have R2 : ∀ x, a * (c * (a * x)) = c * x := fun x => by
      calc a * (c * (a * x)) = (a * c) * a * x := by simp only [mul_assoc]
        _ = (c * a) * a * x := by rw [hac.eq]
        _ = c * (a * a) * x := by simp only [mul_assoc]
        _ = c * x := by rw [ha2, mul_one]
    have R3 : ∀ x, b * (c * (b * (c * x))) = c * (b * (c * (b * x))) := fun x => by
      have h := hcy.eq
      rw [hyy] at h
      calc b * (c * (b * (c * x))) = (b * c * b * c) * x := by simp only [mul_assoc]
        _ = (c * (b * c * b)) * x := by rw [h]
        _ = c * (b * (c * (b * x))) := by simp only [mul_assoc]
    rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul, hn, commutatorElement_def, hyinv, hainv,
      hbinv, hyy]
    simp only [mul_assoc]
    rw [R1', R1 (c * (a * (b * a))), R2 (b * a), R3 (a * (b * (c * (b * a))))]
  have hnX : n ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
    have hA' : A ≤ Subgroup.centralizer ({n} : Set G) := fun a' ha' =>
      Subgroup.mem_centralizer_singleton_iff.2 (hnA a' ha').eq
    have hb' : b ∈ Subgroup.centralizer ({n} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hnb.eq
    have hne : conjSub A 1 ≠ conjSub A b := by
      rw [conjSub_one, hab]
      intro e
      apply hAB.1
      have : conjSub (conjSub B a) a⁻¹ = B := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
      rw [← this, ← e, conjSub_of_mem (A.inv_mem ha)]
    have hS : A ⊔ B ≤ Subgroup.centralizer ({n} : Set G) := by
      rw [← hAB.sup_conjSub_eq hsqA (one_mem _) (Subgroup.mem_sup_right hb) hne, conjSub_one]
      exact sup_le hA' (conjSub_le hA' hb')
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hS hx)
  have hna : n * a ∈ rootElts R := by
    have hca : c * a ∈ A ⊔ C :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left ha)
    have hca1 : c * a ≠ 1 := by
      intro h1
      have : a ∈ A ⊓ C := ⟨ha, by rw [eq_inv_of_mul_eq_one_right h1]; exact C.inv_mem hc⟩
      rw [inf_eq_bot hR hiso hA hCR hAC.1.2.1.symm, Subgroup.mem_bot] at this
      exact ha1 this
    obtain ⟨E, hE, -, hcaE⟩ := hAC.2 _ hca hca1
    have he : n * a = y * (c * a) * y⁻¹ := by
      rw [hn, commutatorElement_def]
      calc c * (y * a * y⁻¹ * a⁻¹) * a = c * y * a * y⁻¹ := by group
        _ = y * c * a * y⁻¹ := by rw [hcy.eq]
        _ = y * (c * a) * y⁻¹ := by group
    rw [he]
    exact ⟨conjSub E y, hR.conjSub_mem hE y, conj_mem_conjSub y hcaE,
      fun h1 => hca1 (conj_eq_one_iff.1 h1)⟩
  have hnmem : n ∈ A ⊔ B := by
    by_contra hnX'
    exact ha1 (eq_one_of_mul_mem_rootElts hR hA hAB hnX hnX' (Subgroup.mem_sup_left ha) hna)
  have hn1 : n = 1 := hAB.eq_one_of_mem_centralizer hsqA hnmem hnX
  exact eq_inv_of_mul_eq_one_right hn1

theorem commutatorElement_commutatorElement_eq (hR : IsRootClass R) (hiso : NoIsolated R)
    (hA : A ∈ R) (hB : B ∈ R) (hAB : Opposite A B) (hAC : C ∈ lambdaSet R A)
    (hBC : C ∈ psiSet R B) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {b : G} (hb : b ∈ B)
    (hab : conjSub A b = conjSub B a) {c : G} (hc : c ∈ C) : ⁅a, ⁅b, c⁆⁆ = c := by
  have hk := commutatorElement_conj_eq hR hiso hA hB hAB hAC hBC ha ha1 hb hab hc
  have hac : Commute a c := hAC.1.2.2 a ha c hc
  set y := b * c * b⁻¹ with hy
  rw [commutatorElement_def] at hk
  have h1 : a * y⁻¹ * a⁻¹ = y⁻¹ * c⁻¹ := by
    calc a * y⁻¹ * a⁻¹ = y⁻¹ * (y * a * y⁻¹ * a⁻¹) := by group
      _ = y⁻¹ * c⁻¹ := by rw [hk]
  have h2 : a * y * a⁻¹ = c * y := by
    calc a * y * a⁻¹ = (a * y⁻¹ * a⁻¹)⁻¹ := by group
      _ = (y⁻¹ * c⁻¹)⁻¹ := by rw [h1]
      _ = c * y := by group
  have h3 : a * c⁻¹ * a⁻¹ = c⁻¹ := by rw [hac.inv_right.eq, mul_inv_cancel_right]
  have hd : ⁅b, c⁆ = y * c⁻¹ := by rw [commutatorElement_def, hy]
  rw [hd, commutatorElement_def]
  calc a * (y * c⁻¹) * a⁻¹ * (y * c⁻¹)⁻¹ = (a * y * a⁻¹) * (a * c⁻¹ * a⁻¹) * (c * y⁻¹) := by
        group
    _ = c := by rw [h2, h3]; group

omit [Finite G] in
theorem mem_sup_commutator_iff (hBC : C ∈ psiSet R B) {x : G} :
    x ∈ C ⊔ ⁅B, C⁆ ↔ ∃ c ∈ C, ∃ d ∈ ⁅B, C⁆, c * d = x := by
  have hle : ⁅B, C⁆ ≤ Subgroup.normalizer (C : Set G) :=
    (commuting_iff_le_centralizer.1 hBC.2.2.2.symm).trans (Subgroup.centralizer_le_normalizer _)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left C _ hle]
  constructor
  · rintro ⟨c, hc, d, hd, rfl⟩
    exact ⟨c, hc, d, hd, rfl⟩
  · rintro ⟨c, hc, d, hd, rfl⟩
    exact ⟨c, hc, d, hd, rfl⟩

variable (hR : IsRootClass R) (hiso : NoIsolated R) (hA : A ∈ R) (hB : B ∈ R)
  (hAB : Opposite A B) (hAC : C ∈ lambdaSet R A) (hBC : C ∈ psiSet R B)
include hR hiso hA hB hAB hAC hBC

theorem commutatorElement_mem_of_mem_commutator {a d : G} (ha : a ∈ A) (hd : d ∈ ⁅B, C⁆) :
    ⁅a, d⁆ ∈ C := by
  rcases eq_or_ne a 1 with rfl | ha1
  · rw [commutatorElement_one_left]
    exact C.one_mem
  obtain ⟨b, hb, hb1, hab⟩ := hAB.2.1 a ha ha1
  obtain ⟨c, hc, rfl⟩ := (bijOn_commutator hR hiso hB hAC.1.1 hBC.2 hb hb1).surjOn hd
  rw [commutatorElement_commutatorElement_eq hR hiso hA hB hAB hAC hBC ha ha1 hb hab hc]
  exact hc

theorem commutatorElement_mem_of_mem_sup {a x : G} (ha : a ∈ A) (hx : x ∈ C ⊔ ⁅B, C⁆) :
    ⁅a, x⁆ ∈ C := by
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_sup_commutator_iff hBC).1 hx
  have hmem := commutatorElement_mem_of_mem_commutator hR hiso hA hB hAB hAC hBC ha hd
  have hac : Commute a c := hAC.1.2.2 a ha c hc
  have e : ⁅a, c * d⁆ = c * ⁅a, d⁆ * c⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a * (c * d) * a⁻¹ * (c * d)⁻¹ = (a * c) * d * a⁻¹ * d⁻¹ * c⁻¹ := by group
      _ = (c * a) * d * a⁻¹ * d⁻¹ * c⁻¹ := by rw [hac.eq]
      _ = c * (a * d * a⁻¹ * d⁻¹) * c⁻¹ := by group
  rw [e, ((hR.commute hAC.1.1 hc hmem).eq), mul_inv_cancel_right]
  exact hmem

theorem conjSub_sup_commutator_le_of_mem_left {a : G} (ha : a ∈ A) :
    conjSub (C ⊔ ⁅B, C⁆) a ≤ C ⊔ ⁅B, C⁆ := by
  rintro _ ⟨x, hx, rfl⟩
  change a * x * a⁻¹ ∈ _
  rw [conj_eq_commutator_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left
    (commutatorElement_mem_of_mem_sup hR hiso hA hB hAB hAC hBC ha hx)) hx

omit [Finite G] hR hiso hA hB hAB hAC in
theorem conjSub_sup_commutator_le_of_mem_right {b : G} (hb : b ∈ B) :
    conjSub (C ⊔ ⁅B, C⁆) b ≤ C ⊔ ⁅B, C⁆ := by
  rw [conjSub, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · refine (conjSub_le_commutator_sup hb).trans (sup_le ?_ le_sup_left)
    rw [Subgroup.commutator_comm]
    exact le_sup_right
  · rw [← conjSub, conjSub_of_forall_commute fun d hd => (hBC.2.2.1 d hd b hb).symm]
    exact le_sup_right

theorem conjSub_sup_commutator_eq {x : G} (hx : x ∈ A ⊔ B) :
    conjSub (C ⊔ ⁅B, C⁆) x = C ⊔ ⁅B, C⁆ := by
  have hmem : ∀ g : G, conjSub (C ⊔ ⁅B, C⁆) g ≤ C ⊔ ⁅B, C⁆ →
      conjSub (C ⊔ ⁅B, C⁆) g⁻¹ ≤ C ⊔ ⁅B, C⁆ → g ∈ Subgroup.normalizer
        ((C ⊔ ⁅B, C⁆ : Subgroup G) : Set G) := by
    intro g h1 h2
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact h1 ⟨y, hy, rfl⟩
    · intro hy
      have := h2 ⟨_, hy, rfl⟩
      change g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ ∈ _ at this
      rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this
  have hle : A ⊔ B ≤ Subgroup.normalizer ((C ⊔ ⁅B, C⁆ : Subgroup G) : Set G) := by
    refine sup_le (fun a ha => hmem a ?_ ?_) (fun b hb => hmem b ?_ ?_)
    · exact conjSub_sup_commutator_le_of_mem_left hR hiso hA hB hAB hAC hBC ha
    · exact conjSub_sup_commutator_le_of_mem_left hR hiso hA hB hAB hAC hBC (A.inv_mem ha)
    · exact conjSub_sup_commutator_le_of_mem_right hBC hb
    · exact conjSub_sup_commutator_le_of_mem_right hBC (B.inv_mem hb)
  exact map_conj_eq_self_iff.2 (hle hx)

theorem mem_of_forall_commute_of_mem_sup {x : G} (hx : x ∈ C ⊔ ⁅B, C⁆)
    (hxA : ∀ a ∈ A, Commute a x) : x ∈ C := by
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_sup_commutator_iff hBC).1 hx
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one hA
  obtain ⟨b, hb, hb1, hab⟩ := hAB.2.1 a ha ha1
  obtain ⟨c', hc', rfl⟩ := (bijOn_commutator hR hiso hB hAC.1.1 hBC.2 hb hb1).surjOn hd
  have h1 : ⁅a, c * ⁅b, c'⁆⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hxA a ha).eq
  have hac : Commute a c := hAC.1.2.2 a ha c hc
  have e : ⁅a, c * ⁅b, c'⁆⁆ = c * ⁅a, ⁅b, c'⁆⁆ * c⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a * (c * ⁅b, c'⁆) * a⁻¹ * (c * ⁅b, c'⁆)⁻¹ =
        (a * c) * ⁅b, c'⁆ * a⁻¹ * ⁅b, c'⁆⁻¹ * c⁻¹ := by group
      _ = (c * a) * ⁅b, c'⁆ * a⁻¹ * ⁅b, c'⁆⁻¹ * c⁻¹ := by rw [hac.eq]
      _ = c * (a * ⁅b, c'⁆ * a⁻¹ * ⁅b, c'⁆⁻¹) * c⁻¹ := by group
  rw [e, commutatorElement_commutatorElement_eq hR hiso hA hB hAB hAC hBC ha ha1 hb hab hc',
    conj_eq_one_iff] at h1
  rw [h1]
  show c * ⁅b, 1⁆ ∈ C
  rw [commutatorElement_one_right, mul_one]
  exact hc

theorem eq_one_of_forall_commute_of_mem_sup {x : G} (hx : x ∈ C ⊔ ⁅B, C⁆)
    (hxX : ∀ g ∈ A ⊔ B, Commute g x) : x = 1 := by
  have hxC := mem_of_forall_commute_of_mem_sup hR hiso hA hB hAB hAC hBC hx
    fun a ha => hxX a (Subgroup.mem_sup_left ha)
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
  exact eq_one_of_commute_of_special hR hiso hB hAC.1.1 hBC.2 hb hb1 hxC
    (hxX b (Subgroup.mem_sup_right hb))

omit [Finite G] hiso hA hB hAB in
theorem commuting_sup_commutator : Commuting (C ⊔ ⁅B, C⁆) (C ⊔ ⁅B, C⁆) := by
  have hCR : C ∈ R := hAC.1.1
  have hD : Commuting ⁅B, C⁆ ⁅B, C⁆ := hR.commuting_self hBC.2.1
  refine Commuting.sup_left (Commuting.sup_right (hR.commuting_self hCR) hBC.2.2.2.symm)
    (Commuting.sup_right hBC.2.2.2 hD)

omit [Finite G] hA hB hAB in
theorem card_sup_commutator : Nat.card ↥(C ⊔ ⁅B, C⁆) = Nat.card C ^ 2 := by
  have hCR : C ∈ R := hAC.1.1
  have hle : ⁅B, C⁆ ≤ Subgroup.normalizer (C : Set G) :=
    (commuting_iff_le_centralizer.1 hBC.2.2.2.symm).trans (Subgroup.centralizer_le_normalizer _)
  have hne : C ≠ ⁅B, C⁆ := by
    have := hBC.2.symm.ne_commutator hR
    rwa [Subgroup.commutator_comm] at this
  have hdisj : Disjoint C ⁅B, C⁆ := disjoint_iff.2 (inf_eq_bot hR hiso hCR hBC.2.1 hne)
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer C _ hle hdisj,
    hR.card_eq hBC.2.1 hCR, sq]

theorem sup_commutator_eq_iSup : C ⊔ ⁅B, C⁆ = ⨆ x ∈ A ⊔ B, conjSub C x := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · have := le_iSup₂ (f := fun x (_ : x ∈ A ⊔ B) => conjSub C x) 1 (one_mem _)
      rwa [conjSub_one] at this
    · rw [Subgroup.commutator_le]
      intro b hb c hc
      rw [commutatorElement_def]
      have h1 : b * c * b⁻¹ ∈ ⨆ x ∈ A ⊔ B, conjSub C x :=
        le_iSup₂ (f := fun x (_ : x ∈ A ⊔ B) => conjSub C x) b (Subgroup.mem_sup_right hb)
          (conj_mem_conjSub b hc)
      have h2 : c⁻¹ ∈ ⨆ x ∈ A ⊔ B, conjSub C x := by
        have := le_iSup₂ (f := fun x (_ : x ∈ A ⊔ B) => conjSub C x) 1 (one_mem _)
        rw [conjSub_one] at this
        exact this (C.inv_mem hc)
      exact Subgroup.mul_mem _ h1 h2
  · refine iSup₂_le fun x hx => ?_
    rw [← conjSub_sup_commutator_eq hR hiso hA hB hAB hAC hBC hx]
    exact Subgroup.map_mono le_sup_left

theorem exists_isNaturalModule {K : Type*} [Field K] [Finite K] [CharP K 2]
    (φ : ↥(A ⊔ B) ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hφ : (A.subgroupOf (A ⊔ B)).map φ.toMonoidHom = upperUnipotent K) {w : G} (hw : w ∈ C)
    (hw1 : w ≠ 1) :
    ∃ θ : (Fin 2 → K) → G, IsNaturalModule φ θ ∧
      Set.range θ = ((C ⊔ ⁅B, C⁆ : Subgroup G) : Set G) ∧ θ ![1, 0] = w := by
  have hN := commuting_sup_commutator hR hAC hBC
  have hXN : ∀ x ∈ A ⊔ B, ∀ n ∈ C ⊔ ⁅B, C⁆, x * n * x⁻¹ ∈ C ⊔ ⁅B, C⁆ := fun x hx n hn => by
    rw [← conjSub_sup_commutator_eq hR hiso hA hB hAB hAC hBC hx]
    exact conj_mem_conjSub x hn
  obtain ⟨θ, hθ, hrange, he⟩ := exists_natural_of_quadratic_conj φ hφ
    (fun n hn m hm => hN n hn m hm) hXN
    (fun n hn hX => eq_one_of_forall_commute_of_mem_sup hR hiso hA hB hAB hAC hBC hn hX)
    (fun n hn a ha a' ha' =>
      hAC.1.2.2 a' ha' _ (commutatorElement_mem_of_mem_sup hR hiso hA hB hAB hAC hBC ha hn))
    (Subgroup.mem_sup_left hw) (fun a ha => hAC.1.2.2 a ha w hw) hw1
  refine ⟨θ, hθ, ?_, he⟩
  set S := Subgroup.closure (Set.range fun x : ↥(A ⊔ B) => (x : G) * w * (x : G)⁻¹) with hS
  have hSN : S ≤ C ⊔ ⁅B, C⁆ := by
    rw [hS, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    exact hXN x x.2 w (Subgroup.mem_sup_left hw)
  have hcardK : Nat.card K = Nat.card C := by
    rw [← card_upperUnipotent K, ← hφ, Subgroup.card_map_of_injective φ.injective,
      card_subgroupOf_of_le le_sup_left, hR.card_eq hA hAC.1.1]
  have hcardS : Nat.card S = Nat.card K ^ 2 := hθ.card_eq hrange.symm
  have hSeq : S = C ⊔ ⁅B, C⁆ := Subgroup.eq_of_le_of_card_ge hSN (by
    rw [card_sup_commutator hR hiso hAC hBC, hcardS, hcardK])
  rw [hrange, hSeq]

theorem sup_commutator_inf_eq_bot : (C ⊔ ⁅B, C⁆) ⊓ (A ⊔ B) = ⊥ := by
  obtain ⟨n, -, -, φ, hφA, -⟩ := hAB.exists_mulEquiv_SL2' hR hA
  obtain ⟨w, hw, hw1⟩ := hR.exists_ne_one hAC.1.1
  obtain ⟨θ, hθ, hrange, -⟩ :=
    exists_isNaturalModule hR hiso hA hB hAB hAC hBC φ hφA hw hw1
  have hN := commuting_sup_commutator hR hAC hBC
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have h1 : (⟨x, hx.2⟩ : ↥(A ⊔ B)) = 1 := hθ.eq_one_of_forall_commute fun v => by
    have hv : θ v ∈ C ⊔ ⁅B, C⁆ := by
      rw [← SetLike.mem_coe, ← hrange]
      exact ⟨v, rfl⟩
    exact hN x hx.1 _ hv
  exact congrArg Subtype.val h1

theorem sup_commutator_sup_eq : (C ⊔ ⁅B, C⁆) ⊔ (A ⊔ B) = A ⊔ B ⊔ C := by
  apply le_antisymm
  · rw [sup_commutator_eq_iSup hR hiso hA hB hAB hAC hBC]
    exact sup_le (iSup₂_le fun x hx => conjSub_le le_sup_right (le_sup_left (a := A ⊔ B) hx))
      le_sup_left
  · exact sup_le le_sup_right (le_sup_left.trans le_sup_left)

theorem setOf_mem_le_sup_eq :
    {D | D ∈ R ∧ D ≤ A ⊔ C} = insert C (Set.range fun n : ↥(C ⊔ ⁅B, C⁆) => conjSub A n) := by
  have hCR : C ∈ R := hAC.1.1
  ext E
  constructor
  · rintro ⟨hE, hEle⟩
    by_cases hEC : E = C
    · exact Or.inl hEC
    right
    obtain ⟨e, he, he1⟩ := hR.exists_ne_one hE
    have hleAC : C ≤ Subgroup.normalizer (A : Set G) :=
      (commuting_iff_le_centralizer.1 hAC.1.2.2).trans (Subgroup.centralizer_le_normalizer _)
    have hmem : e ∈ ((A ⊔ C : Subgroup G) : Set G) := hEle he
    rw [Subgroup.coe_mul_of_right_le_normalizer_left A C hleAC] at hmem
    obtain ⟨a, ha, c, hc, rfl⟩ := hmem
    dsimp only at he he1
    have ha1 : a ≠ 1 := by
      rintro rfl
      rw [one_mul] at he he1
      have : c ∈ E ⊓ C := ⟨he, hc⟩
      rw [inf_eq_bot hR hiso hE hCR hEC, Subgroup.mem_bot] at this
      exact he1 this
    obtain ⟨b, hb, -, hab⟩ := hAB.2.1 a ha ha1
    set n := b * c⁻¹ * b⁻¹ with hn
    have hnN : n ∈ C ⊔ ⁅B, C⁆ := by
      have h1 := conjSub_le_commutator_sup hb (conj_mem_conjSub b (C.inv_mem hc))
      rw [Subgroup.commutator_comm] at h1
      exact (sup_comm (⁅B, C⁆) C ▸ h1 :)
    have hk := commutatorElement_conj_eq hR hiso hA hB hAB hAC hBC ha ha1 hb hab (C.inv_mem hc)
    rw [inv_inv] at hk
    have hconj : n * a * n⁻¹ = a * c := by
      rw [conj_eq_commutator_mul, hk]
      exact (hAC.1.2.2 a ha c hc).eq.symm
    refine ⟨⟨n, hnN⟩, ?_⟩
    by_contra hne
    have : a * c ∈ conjSub A n ⊓ E := ⟨⟨a, ha, hconj⟩, he⟩
    rw [inf_eq_bot hR hiso (hR.conjSub_mem hA n) hE hne, Subgroup.mem_bot] at this
    exact he1 this
  · rintro (rfl | ⟨⟨n, hn⟩, rfl⟩)
    · exact ⟨hCR, le_sup_right⟩
    · refine ⟨hR.conjSub_mem hA n, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      change n * a * n⁻¹ ∈ A ⊔ C
      rw [conj_eq_commutator_mul]
      have h1 : ⁅n, a⁆ ∈ C := by
        rw [← commutatorElement_inv]
        exact C.inv_mem (commutatorElement_mem_of_mem_sup hR hiso hA hB hAB hAC hBC ha hn)
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left ha)

theorem exists_conj_eq_of_mem_sup {n n' : G} (hn : n ∈ C ⊔ ⁅B, C⁆) (hn1 : n ≠ 1)
    (hn' : n' ∈ C ⊔ ⁅B, C⁆) (hn'1 : n' ≠ 1) : ∃ x ∈ A ⊔ B, x * n * x⁻¹ = n' := by
  obtain ⟨k, -, -, φ, hφA, -⟩ := hAB.exists_mulEquiv_SL2' hR hA
  obtain ⟨w, hw, hw1⟩ := hR.exists_ne_one hAC.1.1
  obtain ⟨θ, hθ, hrange, -⟩ :=
    exists_isNaturalModule hR hiso hA hB hAB hAC hBC φ hφA hw hw1
  have hmem : ∀ y ∈ C ⊔ ⁅B, C⁆, ∃ v, θ v = y := fun y hy => by
    rw [← SetLike.mem_coe, ← hrange] at hy
    exact hy
  obtain ⟨u, rfl⟩ := hmem n hn
  obtain ⟨v, rfl⟩ := hmem n' hn'
  have hu : u ≠ 0 := fun h => hn1 (by rw [h, hθ.map_zero])
  have hv : v ≠ 0 := fun h => hn'1 (by rw [h, hθ.map_zero])
  obtain ⟨x, hx⟩ := hθ.exists_conj_eq hu hv
  exact ⟨x, x.2, hx⟩

theorem exists_mem_conjSub_of_mem_sup {n : G} (hn : n ∈ C ⊔ ⁅B, C⁆) (hn1 : n ≠ 1) :
    ∃ x ∈ A ⊔ B, n ∈ conjSub C x := by
  obtain ⟨w, hw, hw1⟩ := hR.exists_ne_one hAC.1.1
  obtain ⟨x, hx, rfl⟩ := exists_conj_eq_of_mem_sup hR hiso hA hB hAB hAC hBC
    (Subgroup.mem_sup_left hw) hw1 hn hn1
  exact ⟨x, hx, conj_mem_conjSub x hw⟩

theorem coveredBy_sup_commutator : CoveredBy R (C ⊔ ⁅B, C⁆) := by
  intro n hn hn1
  obtain ⟨x, hx, hnx⟩ := exists_mem_conjSub_of_mem_sup hR hiso hA hB hAB hAC hBC hn hn1
  refine ⟨conjSub C x, hR.conjSub_mem hAC.1.1 x, ?_, hnx⟩
  rw [← conjSub_sup_commutator_eq hR hiso hA hB hAB hAC hBC hx]
  exact Subgroup.map_mono le_sup_left

theorem eq_one_of_forall_commute_of_mem_sup_left {x : G} (hx : x ∈ A ⊔ B)
    (hxN : ∀ n ∈ C ⊔ ⁅B, C⁆, Commute x n) : x = 1 := by
  obtain ⟨k, -, -, φ, hφA, -⟩ := hAB.exists_mulEquiv_SL2' hR hA
  obtain ⟨w, hw, hw1⟩ := hR.exists_ne_one hAC.1.1
  obtain ⟨θ, hθ, hrange, -⟩ :=
    exists_isNaturalModule hR hiso hA hB hAB hAC hBC φ hφA hw hw1
  have h1 : (⟨x, hx⟩ : ↥(A ⊔ B)) = 1 := hθ.eq_one_of_forall_commute fun v => by
    have hv : θ v ∈ C ⊔ ⁅B, C⁆ := by
      rw [← SetLike.mem_coe, ← hrange]
      exact ⟨v, rfl⟩
    exact hxN _ hv
  exact congrArg Subtype.val h1

end Natural

end Sec3

open Sec3

theorem natural_module [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B C : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (hAB : Opposite A B)
    (hAC : C ∈ lambdaSet R A) (hBC : C ∈ psiSet R B) :
    ⁅B, C⁆ ∈ R ∧ C ⊔ ⁅B, C⁆ = (⨆ x ∈ A ⊔ B, conjSub C x) ∧
      Commuting (C ⊔ ⁅B, C⁆) (C ⊔ ⁅B, C⁆) ∧ Nat.card ↥(C ⊔ ⁅B, C⁆) = Nat.card A ^ 2 ∧
      (∀ x ∈ A ⊔ B, conjSub (C ⊔ ⁅B, C⁆) x = C ⊔ ⁅B, C⁆) ∧
      (C ⊔ ⁅B, C⁆) ⊓ (A ⊔ B) = ⊥ ∧ (C ⊔ ⁅B, C⁆) ⊔ (A ⊔ B) = A ⊔ B ⊔ C ∧
      (∀ n ∈ C ⊔ ⁅B, C⁆, (∀ a ∈ A, Commute a n) → n ∈ C) ∧
      (∀ {K : Type*} [Field K] [Finite K] [CharP K 2]
        (φ : ↥(A ⊔ B) ≃* Matrix.SpecialLinearGroup (Fin 2) K),
        (A.subgroupOf (A ⊔ B)).map φ.toMonoidHom = upperUnipotent K → ∀ w ∈ C, w ≠ 1 →
        ∃ θ : (Fin 2 → K) → G, IsNaturalModule φ θ ∧
          Set.range θ = ((C ⊔ ⁅B, C⁆ : Subgroup G) : Set G) ∧ θ ![1, 0] = w) ∧
      {D | D ∈ R ∧ D ≤ A ⊔ C} = insert C (Set.range fun n : ↥(C ⊔ ⁅B, C⁆) => conjSub A n) :=
  ⟨hBC.2.1, sup_commutator_eq_iSup hR hiso hA hB hAB hAC hBC,
    commuting_sup_commutator hR hAC hBC,
    by rw [card_sup_commutator hR hiso hAC hBC, hR.card_eq hAC.1.1 hA],
    fun _ hx => conjSub_sup_commutator_eq hR hiso hA hB hAB hAC hBC hx,
    sup_commutator_inf_eq_bot hR hiso hA hB hAB hAC hBC,
    sup_commutator_sup_eq hR hiso hA hB hAB hAC hBC,
    fun _ hn hnA => mem_of_forall_commute_of_mem_sup hR hiso hA hB hAB hAC hBC hn hnA,
    fun φ hφ _ hw hw1 => exists_isNaturalModule hR hiso hA hB hAB hAC hBC φ hφ hw hw1,
    setOf_mem_le_sup_eq hR hiso hA hB hAB hAC hBC⟩

end CFSG.Timmesfeld.ARS
