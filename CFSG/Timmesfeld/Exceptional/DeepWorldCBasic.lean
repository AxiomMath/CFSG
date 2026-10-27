module

public import CFSG.Timmesfeld.Exceptional.DeepMain

public section

namespace CFSG.Timmesfeld.Moufang

@[expose] def ExcWorldCInput : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → (∀ d ∈ D, rootSet D d = {d}) → NoLevi D →
    ExcNoPlane D → (∀ d ∈ D, (collinearSet D d).ncard = 10) →
    (∀ c ∈ D, ∀ p ∈ D, p ∉ nbhd D c 3 → ¬ Deep.ThreeNear D c p) →
    ∀ c ∈ D, ∀ p ∈ D, p ∈ nbhd D c 4 → p ∉ nbhd D c 3 → ∀ x : Fin 2 → G,
      (∀ i, x i ∈ collinearSet D p) → (∀ i, x i ∈ nbhd D c 3) → x 1 ≠ x 0 →
      x 1 ≠ p * x 0 → (∀ q ∈ Deep.offLines D p x, ¬ Commute (Deep.zEl p c x) q) → False

end CFSG.Timmesfeld.Moufang

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

theorem nbhd_subset_nbhd_succ {c d : G} (hc : c ∈ D) (hcd : Commute c d) :
    ∀ k, nbhd D c k ⊆ nbhd D d (k + 1)
  | 0 => by
    intro e he
    rw [nbhd_zero, Set.mem_singleton_iff] at he
    subst he
    exact mem_nbhd_succ_of_commute hc (mem_nbhd_self 0) hcd
  | k + 1 => by
    rintro e (he | ⟨heD, f, hf, hef⟩)
    · exact nbhd_mono (Nat.le_succ _) (nbhd_subset_nbhd_succ hc hcd k he)
    · exact mem_nbhd_succ_of_commute heD (nbhd_subset_nbhd_succ hc hcd k hf) hef

theorem mem_nbhd_comm {c d : G} (hc : c ∈ D) {k : ℕ} (h : d ∈ nbhd D c k) :
    c ∈ nbhd D d k := by
  induction k generalizing d with
  | zero =>
    rw [nbhd_zero, Set.mem_singleton_iff] at h
    subst h
    exact mem_nbhd_self 0
  | succ k ih =>
    rcases h with h | ⟨-, e, he, hde⟩
    · exact nbhd_mono (Nat.le_succ k) (ih h)
    · exact nbhd_subset_nbhd_succ (nbhd_subset hc k he) hde.symm k (ih he)

theorem conj_mem_nbhd (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (g : G) {c d : G} {k : ℕ}
    (h : d ∈ nbhd D c k) : g * d * g⁻¹ ∈ nbhd D (g * c * g⁻¹) k := by
  induction k generalizing d with
  | zero =>
    rw [nbhd_zero, Set.mem_singleton_iff] at h ⊢
    rw [h]
  | succ k ih =>
    rcases h with h | ⟨hd, e, he, hde⟩
    · exact Or.inl (ih h)
    · exact Or.inr ⟨hconj g d hd, g * e * g⁻¹, ih he, (Commute.conj_iff g).2 hde⟩

theorem conj_mem_nbhd_of_commute (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) {g c d : G}
    {k : ℕ} (hgc : Commute g c) (h : d ∈ nbhd D c k) : g * d * g⁻¹ ∈ nbhd D c k := by
  have := conj_mem_nbhd hconj g h
  rwa [hgc.eq, mul_inv_cancel_right] at this

theorem conj_mem_collinearSet (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (g : G) {d y : G}
    (hy : y ∈ collinearSet D d) : g * y * g⁻¹ ∈ collinearSet D (g * d * g⁻¹) := by
  obtain ⟨hyD, hdy, hdyD⟩ := hy
  refine ⟨hconj g y hyD, (Commute.conj_iff g).2 hdy, ?_⟩
  have := hconj g _ hdyD
  rwa [show g * (d * y) * g⁻¹ = g * d * g⁻¹ * (g * y * g⁻¹) by group] at this

theorem conj_mem_collinearSet_of_commute (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D)
    {g d y : G} (hgd : Commute g d) (hy : y ∈ collinearSet D d) :
    g * y * g⁻¹ ∈ collinearSet D d := by
  have := conj_mem_collinearSet hconj g hy
  rwa [hgd.eq, mul_inv_cancel_right] at this

theorem mem_collinearSet_symm {d y : G} (hd : d ∈ D) (hy : y ∈ collinearSet D d) :
    d ∈ collinearSet D y := by
  obtain ⟨-, hdy, hdyD⟩ := hy
  exact ⟨hd, hdy.symm, by rw [← hdy.eq]; exact hdyD⟩

theorem mul_mem_collinearSet_right (hD : IsRootInvolutionSet D) {d y : G} (hd : d ∈ D)
    (hy : y ∈ collinearSet D d) : d * y ∈ collinearSet D y := by
  obtain ⟨hyD, hdy, hdyD⟩ := hy
  refine ⟨hdyD, hdy.symm.mul_right (Commute.refl y), ?_⟩
  rw [← mul_assoc, ← hdy.eq, mul_assoc, hD.mul_self_eq_one hyD, mul_one]
  exact hd

structure FiveLineSetting (G : Type*) [Group G] (D : Set G) : Prop where
  hyp : Hyp G D
  sing : ∀ d ∈ D, rootSet D d = {d}
  noLevi : NoLevi D
  noPlane : ExcNoPlane D
  ten : ∀ d ∈ D, (collinearSet D d).ncard = 10
  noThreeNear : ∀ c ∈ D, ∀ p ∈ D, p ∉ nbhd D c 3 → ¬ ThreeNear D c p

namespace FiveLineSetting

variable (S : FiveLineSetting G D)
include S

theorem finite : Finite G := S.hyp.finite

theorem hclass : ∃ d₀ : G, D = {g | IsConj d₀ g} := S.hyp.isClass

theorem root : IsRootInvolutionSet D := S.hyp.root

theorem conj (g : G) {x : G} (hx : x ∈ D) : g * x * g⁻¹ ∈ D := S.hyp.conj_mem g hx

theorem noPolar : NoPolar D := by
  have := S.hyp.finite
  exact NoLevi.noPolar S.hyp.isClass S.hyp.root S.sing S.noLevi S.noPlane

theorem p1 : ExcP1 D := p1_of_noPolar_noPlane S.hyp S.noPolar S.noPlane

theorem commLambda : CommLambda D :=
  commLambda_of_noPolar_noPlane S.hyp.root (fun g _ hx => S.hyp.conj_mem g hx) S.noPolar
    S.noPlane

theorem mem_collinearSet_iff {d y : G} (hd : d ∈ D) :
    y ∈ collinearSet D d ↔ y ∈ D ∧ Commute d y ∧ y ≠ d := by
  constructor
  · rintro ⟨hy, hdy, hdyD⟩
    refine ⟨hy, hdy, fun h => S.root.ne_one hdyD ?_⟩
    rw [h, S.root.mul_self_eq_one hd]
  · rintro ⟨hy, hdy, hyd⟩
    exact ⟨hy, hdy, S.noPolar d hd y hy hdy (Ne.symm hyd)⟩

theorem orderOf_eq_four_of_mem_two {p u : G} (hp : p ∈ D) (hu2 : u ∈ nbhd D p 2)
    (hu1 : u ∉ nbhd D p 1) : orderOf (u * p) = 4 := by
  obtain ⟨huD, hup | h4⟩ := (mem_nbhd_two_iff S.root S.noLevi hp).1 hu2
  · exact absurd ((mem_nbhd_one_iff hp).2 ⟨huD, hup⟩) hu1
  · exact h4

theorem eq_sq_of_commute {p u x : G} (hp : p ∈ D) (huD : u ∈ D) (hu1 : u ∉ nbhd D p 1)
    (hx : x ∈ D) (hxp : Commute x p) (hxu : Commute x u) : x = (p * u) ^ 2 :=
  (NoLevi.sq_eq_of_commute S.root (fun g _ hy => S.conj g hy) S.noLevi S.noPolar S.noPlane hp
    huD hx hxp hxu fun h => hu1 ((mem_nbhd_one_iff hp).2 ⟨huD, h.symm⟩)).symm

theorem mem_two {p x v : G} (hp : p ∈ D) (hx : x ∈ collinearSet D p)
    (hv : v ∈ collinearSet D x) (hvp : v ≠ p) (hvpx : v ≠ p * x) :
    v ∈ nbhd D p 2 ∧ v ∉ nbhd D p 1 := by
  obtain ⟨hxD, hpx, hpxD⟩ := hx
  obtain ⟨hvD, hxv, hxvD⟩ := hv
  refine ⟨mem_nbhd_succ_of_commute hvD (mem_nbhd_succ_of_commute hxD (mem_nbhd_self 0)
    hpx.symm) hxv.symm, fun h1 => ?_⟩
  obtain ⟨-, hvp'⟩ := (mem_nbhd_one_iff hp).1 h1
  have hxp : x ≠ p := fun h => S.root.ne_one hpxD (by rw [h, S.root.mul_self_eq_one hp])
  rcases NoLevi.centralizer_cases S.root (fun g _ hy => S.conj g hy) S.noLevi S.noPolar
      S.noPlane hp hxD hvD hpx hvp'.symm hxp hvp with h | h | ⟨h4, -⟩
  · exact S.root.ne_one hxvD (by rw [h, S.root.mul_self_eq_one hxD])
  · exact hvpx h
  · exact not_commute_of_orderOf_eq_four (S.root.mul_self_eq_one hxD)
      (S.root.mul_self_eq_one hvD) h4 hxv

theorem mem_three {p u v : G} (hp : p ∈ D) (hu2 : u ∈ nbhd D p 2) (hu1 : u ∉ nbhd D p 1)
    (hv : v ∈ collinearSet D u) (hvx : v ≠ (p * u) ^ 2) (hvux : v ≠ u * (p * u) ^ 2) :
    v ∈ nbhd D p 3 ∧ v ∉ nbhd D p 2 := by
  have huD := nbhd_subset hp 2 hu2
  obtain ⟨hvD, huv, huvD⟩ := hv
  refine ⟨mem_nbhd_succ_of_commute hvD hu2 huv.symm, fun h2 => ?_⟩
  obtain ⟨-, hvp | h4⟩ := (mem_nbhd_two_iff S.root S.noLevi hp).1 h2
  · exact hvx (S.eq_sq_of_commute hp huD hu1 hvD hvp huv.symm)
  · have hc := commute_of_special_special S.hclass S.root S.sing S.commLambda S.noPolar
      S.noPlane huD hvD hp huv huvD (S.orderOf_eq_four_of_mem_two hp hu2 hu1) h4
    have e := S.eq_sq_of_commute hp huD hu1 huvD hc ((Commute.refl u).mul_left huv.symm)
    refine hvux ?_
    rw [← e, ← mul_assoc, S.root.mul_self_eq_one huD, one_mul]

theorem eq_of_mem_two_of_far {p w a u₁ u₂ : G} (hp : p ∈ D) (hw3 : w ∈ nbhd D p 3)
    (hw2 : w ∉ nbhd D p 2) (ha : a ∈ collinearSet D w) (ha3 : a ∉ nbhd D p 3)
    (hu₁ : u₁ ∈ collinearSet D w) (hu₁2 : u₁ ∈ nbhd D p 2) (hu₂ : u₂ ∈ collinearSet D w)
    (hu₂2 : u₂ ∈ nbhd D p 2) : u₂ = u₁ := by
  have hwD := nbhd_subset hp 3 hw3
  have h4 : ∀ {u : G}, u ∈ collinearSet D w → u ∈ nbhd D p 2 → orderOf (u * p) = 4 := by
    intro u hu hu2
    refine S.orderOf_eq_four_of_mem_two hp hu2 fun hu1 => hw2 ?_
    exact mem_nbhd_succ_of_commute hwD hu1 hu.2.1
  exact eq_of_not_threeNear S.hclass S.root S.noLevi S.noPolar S.noPlane S.p1 hp ha.1 ha3
    (mem_collinearSet_symm hwD ha) hw3 hu₁.1 hu₁.2.1 (h4 hu₁ hu₁2) hu₂.1 hu₂.2.1 (h4 hu₂ hu₂2)
    (S.noThreeNear p hp a ha.1 ha3)

theorem mem_four {p w u v : G} (hp : p ∈ D) (hw3 : w ∈ nbhd D p 3) (hw2 : w ∉ nbhd D p 2)
    (huniq : ∀ u' ∈ collinearSet D w, u' ∈ nbhd D p 2 → u' = u)
    (hv : v ∈ collinearSet D w) (hvu : v ≠ u) (hvwu : v ≠ w * u) :
    v ∈ nbhd D p 4 ∧ v ∉ nbhd D p 3 := by
  have hwD := nbhd_subset hp 3 hw3
  refine ⟨mem_nbhd_succ_of_commute hv.1 hw3 hv.2.1.symm, fun h3 => ?_⟩
  rcases special_of_mem_nbhd_three S.root S.noLevi S.noPolar S.p1 hp hwD hw3 hw2 hv h3 with
    h4 | h4
  · exact hvu (huniq v hv ((mem_nbhd_two_iff S.root S.noLevi hp).2 ⟨hv.1, Or.inr h4⟩))
  · have hwv := mul_mem_collinearSet S.root hwD hv
    have e := huniq _ hwv ((mem_nbhd_two_iff S.root S.noLevi hp).2 ⟨hwv.1, Or.inr h4⟩)
    refine hvwu ?_
    rw [← e, ← mul_assoc, S.root.mul_self_eq_one hwD, one_mul]

theorem not_mem_three_mul {c a y : G} (hc : c ∈ D) (ha : a ∈ D) (ha3 : a ∉ nbhd D c 3)
    (hy : y ∈ collinearSet D a) (hy3 : y ∈ nbhd D c 3) : a * y ∉ nbhd D c 3 := by
  intro hay3
  have hy2 : y ∉ nbhd D c 2 := fun h => ha3 (mem_nbhd_succ_of_commute ha h hy.2.1)
  have hq := mul_mem_collinearSet_right S.root ha hy
  rcases special_of_mem_nbhd_three S.root S.noLevi S.noPolar S.p1 hc hy.1 hy3 hy2 hq hay3 with
    h4 | h4
  · have h2 := (mem_nbhd_two_iff S.root S.noLevi hc).2 ⟨hy.2.2, Or.inr h4⟩
    exact ha3 (mem_nbhd_succ_of_commute ha h2 ((Commute.refl a).mul_right hy.2.1))
  · rw [show y * (a * y) = a by
      rw [← mul_assoc, ← hy.2.1.eq, mul_assoc, S.root.mul_self_eq_one hy.1, mul_one]] at h4
    exact ha3 (nbhd_mono (by norm_num) ((mem_nbhd_two_iff S.root S.noLevi hc).2
      ⟨ha, Or.inr h4⟩))

theorem threeNear_of_three {c a : G} (hc : c ∈ D) (ha : a ∈ D) (ha3 : a ∉ nbhd D c 3)
    {y : Fin 3 → G} (hy : ∀ i, y i ∈ collinearSet D a) (hy3 : ∀ i, y i ∈ nbhd D c 3)
    (hinj : ∀ i j, i ≠ j → y j ≠ y i) : ThreeNear D c a := by
  refine ⟨y, hy, hy3, fun i j hij => ⟨hinj i j hij, fun e => ?_⟩⟩
  exact S.not_mem_three_mul hc ha ha3 (hy i) (hy3 i) (e ▸ hy3 j)

end FiveLineSetting

end CFSG.Timmesfeld.Moufang.Deep
