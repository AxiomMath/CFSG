module

import all CFSG.LocalAnalysis.UniquenessCase.UC1K49Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreKModel
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49Count

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open scoped commutatorElement

open CFSG.GroupTheory.CoprimeSection

variable {G : Type} [Group G] [Finite G]

private abbrev K49P (I Q : Subgroup G) : Subgroup G := I ⊓ Q

private lemma Lc_le_I {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    {i : ℕ} (hxi : x ^ i ∈ X) : Lc L x i ≤ I :=
  conjugate_le_of_mem_normalizer (le_I h) (x_mem_normalizer_I h hxi)

private lemma Lc_inf_Q_eq_pCoreOf {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    {i : ℕ} (hxi : x ^ i ∈ X) : Lc L x i ⊓ Q = CFSG.Open.pCoreOf 2 (Lc L x i) :=
  conjugate_inf_pCoreOf_eq h hxi

private lemma Lc_comm_le_P {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    {i j : ℕ} (hxi : x ^ i ∈ X) (hxj : x ^ j ∈ X) (hne : Lc L x i ≠ Lc L x j) :
    ⁅Lc L x i, Lc L x j⁆ ≤ K49P I Q :=
  le_inf ((Subgroup.commutator_mono (Lc_le_I h hxi) (Lc_le_I h hxj)).trans
    ((Subgroup.commutator_le_sup I I).trans (le_of_eq (sup_idem I))))
    (commutator_conjugate_le h hxi hxj hne)

private lemma I_le_normalizer_K49P {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    I ≤ Subgroup.normalizer (K49P I Q : Set G) := by
  have h1 : I ≤ Subgroup.normalizer (I : Set G) := Subgroup.le_normalizer
  have h2 : I ≤ Subgroup.normalizer (Q : Set G) := (I_le_H h).trans (H_le_normalizer_Q h)
  exact (le_inf h1 h2).trans (Subgroup.inf_normalizer_le_normalizer_inf (H := I) (K := Q))

private lemma commutator_K49P_Lc_le_Q {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    {i : ℕ} (hi : x ^ i ∈ X) : ⁅K49P I Q, Lc L x i⁆ ≤ Q := by
  refine Subgroup.commutator_le.mpr fun p hp m hm => ?_
  have hPN : I ≤ Subgroup.normalizer (K49P I Q : Set G) := I_le_normalizer_K49P h
  have hmI : m ∈ I := Lc_le_I h hi hm
  have hmP : m * p * m⁻¹ ∈ K49P I Q :=
    (Subgroup.mem_normalizer_iff.mp (hPN hmI) p).mp hp
  have hmp : ⁅m, p⁆ ∈ K49P I Q := by
    have h1 := (K49P I Q).mul_mem hmP ((K49P I Q).inv_mem hp)
    rwa [commutatorElement_def]
  simpa only [commutatorElement_inv] using
    (inf_le_right : K49P I Q ≤ Q) ((K49P I Q).inv_mem hmp)

private lemma commutator_mem_Q_of_mem_sup {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} {i j k : ℕ} (hi : x ^ i ∈ X) (hj : x ^ j ∈ X) (hk : x ^ k ∈ X)
    (hij : Lc L x i ≠ Lc L x j) (hik : Lc L x i ≠ Lc L x k) (hjk : Lc L x j ≠ Lc L x k)
    {u : G} (huLi : u ∈ Lc L x i) (huSup : u ∈ Lc L x j ⊔ Lc L x k ⊔ K49P I Q) :
    ∀ m ∈ Lc L x i, ⁅u, m⁆ ∈ Q := by
  have hQn : H ≤ Subgroup.normalizer (Q : Set G) := H_le_normalizer_Q h
  have hLjH : Lc L x j ≤ H := Lc_le_H h hj
  have hLkH : Lc L x k ≤ H := Lc_le_H h hk
  have hPN : I ≤ Subgroup.normalizer (K49P I Q : Set G) := I_le_normalizer_K49P h
  have hLjLk_le_I : Lc L x j ⊔ Lc L x k ≤ I := sup_le (Lc_le_I h hj) (Lc_le_I h hk)
  have hnorm : Lc L x j ⊔ Lc L x k ≤ Subgroup.normalizer (K49P I Q : Set G) :=
    hLjLk_le_I.trans hPN
  obtain ⟨v, hv, p, hp, hvp⟩ := (mem_sup_of_le_normalizer hnorm).mp huSup
  have hLjNLk : Lc L x j ≤ Subgroup.normalizer (Lc L x k : Set G) :=
    conjugate_normalize_of_ne h hj hk hjk
  obtain ⟨lj, hlj, lk, hlk, hlk_eq⟩ := (mem_sup_of_le_normalizer hLjNLk).mp hv
  intro m hm
  have hikQ : ⁅lk, m⁆ ∈ Q :=
    (Subgroup.commutator_le.mp (commutator_conjugate_le h hk hi (Ne.symm hik))) lk hlk m hm
  have hijQ : ⁅lj, m⁆ ∈ Q :=
    (Subgroup.commutator_le.mp (commutator_conjugate_le h hj hi (Ne.symm hij))) lj hlj m hm
  have hpQ : ⁅p, m⁆ ∈ Q := (Subgroup.commutator_le.mp (commutator_K49P_Lc_le_Q h hi)) p hp m hm
  have hconjQ : lj * ⁅lk, m⁆ * lj⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hQn (hLjH hlj)) ⁅lk, m⁆).mp hikQ
  have hconjQ2 : (lj * lk) * ⁅p, m⁆ * (lj * lk)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hQn (H.mul_mem (hLjH hlj) (hLkH hlk))) ⁅p, m⁆).mp hpQ
  have heq : ⁅u, m⁆ = ((lj * lk) * ⁅p, m⁆ * (lj * lk)⁻¹) *
      (lj * ⁅lk, m⁆ * lj⁻¹) * ⁅lj, m⁆ := by
    rw [← hvp, ← hlk_eq]
    simp only [commutatorElement_mul_left_eq_conj_mul]
    group
  rw [heq]
  exact Q.mul_mem (Q.mul_mem hconjQ2 hconjQ) hijQ

private lemma inf_Lc_sup_Lc_Lc_P_le_pCoreOf {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} {i j k : ℕ} (hi : x ^ i ∈ X) (hj : x ^ j ∈ X) (hk : x ^ k ∈ X)
    (hij : Lc L x i ≠ Lc L x j) (hik : Lc L x i ≠ Lc L x k) (hjk : Lc L x j ≠ Lc L x k) :
    Lc L x i ⊓ (Lc L x j ⊔ Lc L x k ⊔ K49P I Q) ≤ CFSG.Open.pCoreOf 2 (Lc L x i) := by
  intro u hu
  have huLi : u ∈ Lc L x i := hu.1
  have huSup : u ∈ Lc L x j ⊔ Lc L x k ⊔ K49P I Q := hu.2
  have hcentral : ∀ m ∈ Lc L x i, ⁅u, m⁆ ∈ Q :=
    commutator_mem_Q_of_mem_sup h hi hj hk hij hik hjk huLi huSup
  have huQ : u ∈ Q :=
    mem_pCoreOf_of_centralizer_mod (isAlt_bar2_conjugate h.L_alt (x ^ i))
      (Lc_inf_Q_eq_pCoreOf h hi) (Lc_le_H h hi) huLi hcentral
  rw [← Lc_inf_Q_eq_pCoreOf h hi]
  exact Subgroup.mem_inf.mpr ⟨huLi, huQ⟩

private lemma mul_six_reorder {Γ : Type*} [Group Γ] {a b c a' b' c' : Γ}
    (ha'b : Commute a' b) (ha'c : Commute a' c) (hb'c : Commute b' c) :
    a * b * c * (a' * b' * c') = a * a' * (b * b') * (c * c') := by
  calc
    a * b * c * (a' * b' * c') = a * b * (c * a') * b' * c' := by group
    _ = a * b * (a' * c) * b' * c' := by rw [← ha'c.eq]
    _ = a * (b * a') * c * b' * c' := by group
    _ = a * (a' * b) * c * b' * c' := by rw [← ha'b.eq]
    _ = a * a' * b * (c * b') * c' := by group
    _ = a * a' * b * (b' * c) * c' := by rw [← hb'c.eq]
    _ = a * a' * (b * b') * (c * c') := by group

private noncomputable def prodThree {Γ : Type*} [Group Γ] (M : Fin 3 → Subgroup Γ)
    (hcomm : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ M i, ∀ y ∈ M j, Commute x y) :
    (M 0 × M 1 × M 2) →* Γ where
  toFun p := (p.1 : Γ) * (p.2.1 : Γ) * (p.2.2 : Γ)
  map_one' := by simp
  map_mul' p q := by
    have h := mul_six_reorder (a := (p.1 : Γ)) (b := (p.2.1 : Γ)) (c := (p.2.2 : Γ))
      (a' := (q.1 : Γ)) (b' := (q.2.1 : Γ)) (c' := (q.2.2 : Γ))
      (hcomm 0 1 (by decide) q.1 q.1.2 p.2.1 p.2.1.2)
      (hcomm 0 2 (by decide) q.1 q.1.2 p.2.2 p.2.2.2)
      (hcomm 1 2 (by decide) q.2.1 q.2.1.2 p.2.2 p.2.2.2)
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    exact h.symm

private lemma prodThree_eq_one {Γ : Type*} [Group Γ] {M : Fin 3 → Subgroup Γ}
    (hcomm : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ M i, ∀ y ∈ M j, Commute x y)
    (hinf : M 0 ⊓ (M 1 ⊔ M 2) = ⊥) (hinf12 : M 1 ⊓ M 2 = ⊥)
    {p : M 0 × M 1 × M 2} (hp : prodThree M hcomm p = 1) : p = 1 := by
  have hrel : (p.1 : Γ) * (p.2.1 : Γ) * (p.2.2 : Γ) = 1 := hp
  have hrel' : (p.1 : Γ) * ((p.2.1 : Γ) * (p.2.2 : Γ)) = 1 := by
    simpa only [mul_assoc] using hrel
  have h1eq : (p.1 : Γ) = ((p.2.1 : Γ) * (p.2.2 : Γ))⁻¹ :=
    eq_inv_of_mul_eq_one_left hrel'
  have h1mem : (p.1 : Γ) ∈ M 0 ⊓ (M 1 ⊔ M 2) := by
    refine ⟨p.1.2, ?_⟩
    rw [h1eq]
    exact (M 1 ⊔ M 2).inv_mem (Subgroup.mul_mem_sup p.2.1.2 p.2.2.2)
  rw [hinf, Subgroup.mem_bot] at h1mem
  have h1 : p.1 = 1 := Subtype.ext h1mem
  have hrel2 : (p.2.1 : Γ) * (p.2.2 : Γ) = 1 := by
    have := hrel'
    rw [h1] at this
    simpa only [Subgroup.coe_one, one_mul] using this
  have h2eq : (p.2.1 : Γ) = (p.2.2 : Γ)⁻¹ := eq_inv_of_mul_eq_one_left hrel2
  have h2mem : (p.2.1 : Γ) ∈ M 1 ⊓ M 2 := by
    refine ⟨p.2.1.2, ?_⟩
    rw [h2eq]
    exact (M 2).inv_mem p.2.2.2
  rw [hinf12, Subgroup.mem_bot] at h2mem
  have h2 : p.2.1 = 1 := Subtype.ext h2mem
  have h3 : p.2.2 = 1 := by
    have hh : (p.2.2 : Γ) = 1 := by
      have := hrel2
      rw [h2] at this
      simpa only [Subgroup.coe_one, one_mul] using this
    exact Subtype.ext hh
  exact Prod.ext h1 (Prod.ext h2 h3)

private lemma prodThree_injective {Γ : Type*} [Group Γ] {M : Fin 3 → Subgroup Γ}
    (hcomm : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ M i, ∀ y ∈ M j, Commute x y)
    (hinf : M 0 ⊓ (M 1 ⊔ M 2) = ⊥) (hinf12 : M 1 ⊓ M 2 = ⊥) :
    Function.Injective (prodThree M hcomm) := by
  intro p q hpq
  have h1 : prodThree M hcomm (p * q⁻¹) = 1 := by
    rw [map_mul, map_inv, hpq, mul_inv_cancel]
  have := prodThree_eq_one hcomm hinf hinf12 h1
  exact mul_inv_eq_one.mp this

private lemma factor_le_normalizer {Γ : Type*} [Group Γ] {M : Fin 3 → Subgroup Γ}
    (hcomm : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ M i, ∀ y ∈ M j, Commute x y)
    {i j : Fin 3} (hij : i ≠ j) : M i ≤ Subgroup.normalizer (M j : Set Γ) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h : y * x = x * y := (hcomm i j hij y hy x hx).eq
    have hyx : y * x * y⁻¹ = x := by
      calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [h]
        _ = x := by group
    rw [hyx]; exact hx
  · intro hx
    have h : Commute y (y * x * y⁻¹) := hcomm i j hij y hy (y * x * y⁻¹) hx
    have hxz : x = y * x * y⁻¹ := by
      calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
        _ = (y * x * y⁻¹) * y⁻¹ * y := by rw [h.inv_left.eq]
        _ = y * x * y⁻¹ := by group
    exact hxz.symm ▸ hx

private lemma prodThree_surjective {Γ : Type} [Group Γ] [Finite Γ] {M : Fin 3 → Subgroup Γ}
    (hcomm : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ M i, ∀ y ∈ M j, Commute x y)
    (htop : M 0 ⊔ M 1 ⊔ M 2 = ⊤) : Function.Surjective (prodThree M hcomm) := by
  intro x
  have hx : x ∈ M 0 ⊔ M 1 ⊔ M 2 := by rw [htop]; exact Subgroup.mem_top x
  have hN2 : M 0 ⊔ M 1 ≤ Subgroup.normalizer (M 2 : Set Γ) :=
    sup_le (factor_le_normalizer hcomm (i := 0) (j := 2) (by decide))
      (factor_le_normalizer hcomm (i := 1) (j := 2) (by decide))
  obtain ⟨v, hv, c, hc, hvc⟩ := (mem_sup_of_le_normalizer hN2).mp hx
  have hN1 : M 0 ≤ Subgroup.normalizer (M 1 : Set Γ) :=
    factor_le_normalizer hcomm (i := 0) (j := 1) (by decide)
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_of_le_normalizer hN1).mp hv
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩), by
    change (a : Γ) * (b : Γ) * (c : Γ) = x
    rw [← hvc, ← hab]⟩

private noncomputable def prodEquiv {Γ : Type} [Group Γ] [Finite Γ] {M : Fin 3 → Subgroup Γ}
    (hcomm : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ M i, ∀ y ∈ M j, Commute x y)
    (hinf : M 0 ⊓ (M 1 ⊔ M 2) = ⊥) (hinf12 : M 1 ⊓ M 2 = ⊥)
    (htop : M 0 ⊔ M 1 ⊔ M 2 = ⊤) : (M 0 × M 1 × M 2) ≃* Γ :=
  MulEquiv.ofBijective (prodThree M hcomm)
    ⟨prodThree_injective hcomm hinf hinf12, prodThree_surjective hcomm htop⟩

private def fixedSubgroup {Γ : Type*} [Group Γ] (θ : MulAut Γ) : Subgroup Γ where
  carrier := {u | θ u = u}
  one_mem' := map_one θ
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

private noncomputable def thetaRestrict {Γ : Type*} [Group Γ] {M : Fin 3 → Subgroup Γ}
    (θ : MulAut Γ) {i j : Fin 3} (h : (M i).map θ.toMonoidHom = M j) : M i →* M j where
  toFun m := ⟨θ (m : Γ), by
    have hm : θ (m : Γ) ∈ (M i).map θ.toMonoidHom :=
      Subgroup.mem_map_of_mem θ.toMonoidHom m.2
    rwa [h] at hm⟩
  map_one' := Subtype.ext (map_one θ)
  map_mul' a b := Subtype.ext (map_mul θ (a : Γ) (b : Γ))

private noncomputable def diagVec {Γ : Type*} [Group Γ] {M : Fin 3 → Subgroup Γ}
    (θ0 : M 0 →* M 1) (θ1 : M 1 →* M 2) : M 0 →* (M 0 × M 1 × M 2) where
  toFun m := (m, θ0 m, θ1 (θ0 m))
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [map_mul]

private lemma commute_rotate_left {Γ : Type*} [Group Γ] {a b c : Γ}
    (hab : Commute a b) (hac : Commute a c) : b * c * a = a * b * c := by
  calc b * c * a = b * (c * a) := by group
    _ = b * (a * c) := by rw [← hac.eq]
    _ = (b * a) * c := by group
    _ = (a * b) * c := by rw [← hab.eq]
    _ = a * b * c := by group

private noncomputable def shiftVec {Γ : Type*} [Group Γ] {M : Fin 3 → Subgroup Γ}
    (θ : MulAut Γ) (hθ0 : (M 0).map θ.toMonoidHom = M 1)
    (hθ1 : (M 1).map θ.toMonoidHom = M 2) (hθ2 : (M 2).map θ.toMonoidHom = M 0)
    (p : M 0 × M 1 × M 2) : M 0 × M 1 × M 2 :=
  (⟨θ (p.2.2 : Γ), by
      have hm : θ (p.2.2 : Γ) ∈ (M 2).map θ.toMonoidHom :=
        Subgroup.mem_map_of_mem θ.toMonoidHom p.2.2.2
      rwa [hθ2] at hm⟩,
    ⟨θ (p.1 : Γ), by
      have hm : θ (p.1 : Γ) ∈ (M 0).map θ.toMonoidHom :=
        Subgroup.mem_map_of_mem θ.toMonoidHom p.1.2
      rwa [hθ0] at hm⟩,
    ⟨θ (p.2.1 : Γ), by
      have hm : θ (p.2.1 : Γ) ∈ (M 1).map θ.toMonoidHom :=
        Subgroup.mem_map_of_mem θ.toMonoidHom p.2.1.2
      rwa [hθ1] at hm⟩)

private lemma theta_prodEquiv_apply {Γ : Type} [Group Γ] [Finite Γ] {M : Fin 3 → Subgroup Γ}
    (hcomm : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ M i, ∀ y ∈ M j, Commute x y)
    (hinf : M 0 ⊓ (M 1 ⊔ M 2) = ⊥) (hinf12 : M 1 ⊓ M 2 = ⊥)
    (htop : M 0 ⊔ M 1 ⊔ M 2 = ⊤)
    {θ : MulAut Γ} (hθ0 : (M 0).map θ.toMonoidHom = M 1)
    (hθ1 : (M 1).map θ.toMonoidHom = M 2) (hθ2 : (M 2).map θ.toMonoidHom = M 0)
    (p : M 0 × M 1 × M 2) :
    θ (prodEquiv hcomm hinf hinf12 htop p) =
      prodEquiv hcomm hinf hinf12 htop (shiftVec θ hθ0 hθ1 hθ2 p) := by
  have hΦ : ∀ q : M 0 × M 1 × M 2, prodEquiv hcomm hinf hinf12 htop q =
      (q.1 : Γ) * (q.2.1 : Γ) * (q.2.2 : Γ) := fun q => rfl
  simp only [hΦ]
  have hab : Commute (θ (p.2.2 : Γ)) (θ (p.1 : Γ)) :=
    hcomm 0 1 (by decide) (θ (p.2.2 : Γ)) (by
      have hm : θ (p.2.2 : Γ) ∈ (M 2).map θ.toMonoidHom :=
        Subgroup.mem_map_of_mem θ.toMonoidHom p.2.2.2
      rwa [hθ2] at hm) (θ (p.1 : Γ)) (by
      have hm : θ (p.1 : Γ) ∈ (M 0).map θ.toMonoidHom :=
        Subgroup.mem_map_of_mem θ.toMonoidHom p.1.2
      rwa [hθ0] at hm)
  have hac : Commute (θ (p.2.2 : Γ)) (θ (p.2.1 : Γ)) :=
    hcomm 0 2 (by decide) (θ (p.2.2 : Γ)) (by
      have hm : θ (p.2.2 : Γ) ∈ (M 2).map θ.toMonoidHom :=
        Subgroup.mem_map_of_mem θ.toMonoidHom p.2.2.2
      rwa [hθ2] at hm) (θ (p.2.1 : Γ)) (by
      have hm : θ (p.2.1 : Γ) ∈ (M 1).map θ.toMonoidHom :=
        Subgroup.mem_map_of_mem θ.toMonoidHom p.2.1.2
      rwa [hθ1] at hm)
  calc θ ((p.1 : Γ) * (p.2.1 : Γ) * (p.2.2 : Γ))
      = θ (p.1 : Γ) * θ (p.2.1 : Γ) * θ (p.2.2 : Γ) := by rw [map_mul, map_mul]
    _ = θ (p.2.2 : Γ) * θ (p.1 : Γ) * θ (p.2.1 : Γ) := commute_rotate_left hab hac
    _ = (shiftVec θ hθ0 hθ1 hθ2 p).1 * (shiftVec θ hθ0 hθ1 hθ2 p).2.1 *
        (shiftVec θ hθ0 hθ1 hθ2 p).2.2 := by rfl

private noncomputable def diagToFix {Γ : Type} [Group Γ] [Finite Γ] {M : Fin 3 → Subgroup Γ}
    (hcomm : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ M i, ∀ y ∈ M j, Commute x y)
    (hinf : M 0 ⊓ (M 1 ⊔ M 2) = ⊥) (hinf12 : M 1 ⊓ M 2 = ⊥)
    (htop : M 0 ⊔ M 1 ⊔ M 2 = ⊤)
    (θ : MulAut Γ) (hθ0 : (M 0).map θ.toMonoidHom = M 1)
    (hθ1 : (M 1).map θ.toMonoidHom = M 2) (hθ2 : (M 2).map θ.toMonoidHom = M 0)
    (hθ3 : ∀ u : Γ, θ (θ (θ u)) = u) : M 0 →* fixedSubgroup θ := by
  let θ0 : M 0 →* M 1 := thetaRestrict θ hθ0
  let θ1 : M 1 →* M 2 := thetaRestrict θ hθ1
  have hfix : ∀ m : M 0,
      shiftVec θ hθ0 hθ1 hθ2 (diagVec θ0 θ1 m) = diagVec θ0 θ1 m := by
    intro m
    apply Prod.ext
    · apply Subtype.ext
      show θ (θ (θ ((m : M 0) : Γ))) = (m : Γ)
      exact hθ3 (m : Γ)
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        rfl
  refine
    { toFun := fun m => ⟨prodEquiv hcomm hinf hinf12 htop (diagVec θ0 θ1 m), ?_⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [map_mul]) }
  show θ (prodEquiv hcomm hinf hinf12 htop (diagVec θ0 θ1 m)) =
    prodEquiv hcomm hinf hinf12 htop (diagVec θ0 θ1 m)
  rw [theta_prodEquiv_apply hcomm hinf hinf12 htop hθ0 hθ1 hθ2 (diagVec θ0 θ1 m), hfix m]

private lemma diagToFix_coe {Γ : Type} [Group Γ] [Finite Γ] {M : Fin 3 → Subgroup Γ}
    (hcomm : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ M i, ∀ y ∈ M j, Commute x y)
    (hinf : M 0 ⊓ (M 1 ⊔ M 2) = ⊥) (hinf12 : M 1 ⊓ M 2 = ⊥)
    (htop : M 0 ⊔ M 1 ⊔ M 2 = ⊤)
    (θ : MulAut Γ) (hθ0 : (M 0).map θ.toMonoidHom = M 1)
    (hθ1 : (M 1).map θ.toMonoidHom = M 2) (hθ2 : (M 2).map θ.toMonoidHom = M 0)
    (hθ3 : ∀ u : Γ, θ (θ (θ u)) = u) (m : M 0) :
    (diagToFix hcomm hinf hinf12 htop θ hθ0 hθ1 hθ2 hθ3 m : Γ) =
      prodEquiv hcomm hinf hinf12 htop
        (diagVec (thetaRestrict θ hθ0) (thetaRestrict θ hθ1) m) := rfl

private lemma diagToFix_injective {Γ : Type} [Group Γ] [Finite Γ] {M : Fin 3 → Subgroup Γ}
    (hcomm : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ M i, ∀ y ∈ M j, Commute x y)
    (hinf : M 0 ⊓ (M 1 ⊔ M 2) = ⊥) (hinf12 : M 1 ⊓ M 2 = ⊥)
    (htop : M 0 ⊔ M 1 ⊔ M 2 = ⊤)
    (θ : MulAut Γ) (hθ0 : (M 0).map θ.toMonoidHom = M 1)
    (hθ1 : (M 1).map θ.toMonoidHom = M 2) (hθ2 : (M 2).map θ.toMonoidHom = M 0)
    (hθ3 : ∀ u : Γ, θ (θ (θ u)) = u) :
    Function.Injective (diagToFix hcomm hinf hinf12 htop θ hθ0 hθ1 hθ2 hθ3) := by
  intro a b hab
  have h1 : prodEquiv hcomm hinf hinf12 htop
      (diagVec (thetaRestrict θ hθ0) (thetaRestrict θ hθ1) a) =
      prodEquiv hcomm hinf hinf12 htop
        (diagVec (thetaRestrict θ hθ0) (thetaRestrict θ hθ1) b) := Subtype.ext_iff.mp hab
  exact congrArg Prod.fst ((prodEquiv hcomm hinf hinf12 htop).injective h1)

private lemma diagToFix_surjective {Γ : Type} [Group Γ] [Finite Γ] {M : Fin 3 → Subgroup Γ}
    (hcomm : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ M i, ∀ y ∈ M j, Commute x y)
    (hinf : M 0 ⊓ (M 1 ⊔ M 2) = ⊥) (hinf12 : M 1 ⊓ M 2 = ⊥)
    (htop : M 0 ⊔ M 1 ⊔ M 2 = ⊤)
    (θ : MulAut Γ) (hθ0 : (M 0).map θ.toMonoidHom = M 1)
    (hθ1 : (M 1).map θ.toMonoidHom = M 2) (hθ2 : (M 2).map θ.toMonoidHom = M 0)
    (hθ3 : ∀ u : Γ, θ (θ (θ u)) = u) :
    Function.Surjective (diagToFix hcomm hinf hinf12 htop θ hθ0 hθ1 hθ2 hθ3) := by
  intro u
  let θ0 : M 0 →* M 1 := thetaRestrict θ hθ0
  let θ1 : M 1 →* M 2 := thetaRestrict θ hθ1
  let p : M 0 × M 1 × M 2 := (prodEquiv hcomm hinf hinf12 htop).symm (u : Γ)
  have hu : (u : Γ) = prodEquiv hcomm hinf hinf12 htop p := by
    simp only [p, MulEquiv.apply_symm_apply]
  have hshift : shiftVec θ hθ0 hθ1 hθ2 p = p := by
    apply (prodEquiv hcomm hinf hinf12 htop).injective
    rw [← theta_prodEquiv_apply hcomm hinf hinf12 htop hθ0 hθ1 hθ2 p, ← hu, u.2]
  have h1 : (p.1 : Γ) = θ (p.2.2 : Γ) := by
    have := congrArg (fun q : M 0 × M 1 × M 2 => (q.1 : Γ)) hshift
    simpa only [shiftVec] using this.symm
  have h2 : (p.2.1 : Γ) = θ (p.1 : Γ) := by
    have := congrArg (fun q : M 0 × M 1 × M 2 => (q.2.1 : Γ)) hshift
    simpa only [shiftVec] using this.symm
  have h3 : (p.2.2 : Γ) = θ (p.2.1 : Γ) := by
    have := congrArg (fun q : M 0 × M 1 × M 2 => (q.2.2 : Γ)) hshift
    simpa only [shiftVec] using this.symm
  have hp : p = diagVec θ0 θ1 p.1 := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        rw [h2]
        rfl
      · apply Subtype.ext
        rw [h3, h2]
        rfl
  refine ⟨p.1, ?_⟩
  apply Subtype.ext
  rw [diagToFix_coe, ← hp, hu]

private noncomputable def fixedPointsEquiv {Γ : Type} [Group Γ] [Finite Γ]
    {M : Fin 3 → Subgroup Γ}
    (hcomm : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ M i, ∀ y ∈ M j, Commute x y)
    (hinf : M 0 ⊓ (M 1 ⊔ M 2) = ⊥) (hinf12 : M 1 ⊓ M 2 = ⊥)
    (htop : M 0 ⊔ M 1 ⊔ M 2 = ⊤)
    (θ : MulAut Γ) (hθ0 : (M 0).map θ.toMonoidHom = M 1)
    (hθ1 : (M 1).map θ.toMonoidHom = M 2) (hθ2 : (M 2).map θ.toMonoidHom = M 0)
    (hθ3 : ∀ u : Γ, θ (θ (θ u)) = u) : M 0 ≃* fixedSubgroup θ :=
  MulEquiv.ofBijective (diagToFix hcomm hinf hinf12 htop θ hθ0 hθ1 hθ2 hθ3)
    ⟨diagToFix_injective hcomm hinf hinf12 htop θ hθ0 hθ1 hθ2 hθ3,
      diagToFix_surjective hcomm hinf hinf12 htop θ hθ0 hθ1 hθ2 hθ3⟩

private noncomputable def K49M (L : Subgroup G) (x : G) (I : Subgroup G) :
    Fin 3 → Subgroup (Bar2 I) :=
  fun i => ((Lc L x i.val).subgroupOf I).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I))

private noncomputable def K49Theta {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hxX : x ∈ X) : MulAut (Bar2 I) :=
  CFSG.RankThree.PartTwo.Sec19.Step1910Proof.quotAct
    ((h.X_le).trans (le_normalizer_I h)) ⟨x⁻¹, X.inv_mem hxX⟩

private lemma K49pow_mem_X {X : Subgroup G} {x : G} (hgen : X = Subgroup.zpowers x)
    (i : ℕ) : x ^ i ∈ X := by
  rw [hgen]
  exact Subgroup.npow_mem_zpowers x i

private lemma inf_I_Q_eq_pCoreOf {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    I ⊓ Q = CFSG.Open.pCoreOf 2 I := by
  refine le_antisymm ?_ ?_
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
    · have h1 : I ≤ Subgroup.normalizer (I : Set G) := Subgroup.le_normalizer
      have h2 : I ≤ Subgroup.normalizer (Q : Set G) := (I_le_H h).trans (H_le_normalizer_Q h)
      exact (le_inf h1 h2).trans (Subgroup.inf_normalizer_le_normalizer_inf (H := I) (K := Q))
    · exact (isPGroup_Q h).to_le inf_le_right
  · refine le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 I) ?_
    rw [h.Q_eq]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 I).trans (I_le_H h))
      ((le_normalizer_I h).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 I))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I)

private lemma K49Lc_ne {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3)
    {i j : Fin 3} (hij : i ≠ j) : Lc L x i.val ≠ Lc L x j.val := by
  obtain ⟨h01, h02, h12⟩ := conjugates_distinct h hxX hgen hord
  fin_cases i <;> fin_cases j <;>
    first
      | exact h01
      | exact h02
      | exact h12
      | exact fun hc => h01 hc.symm
      | exact fun hc => h02 hc.symm
      | exact fun hc => h12 hc.symm
      | exact absurd rfl hij

private lemma K49M_sup_top {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    K49M L x I 0 ⊔ K49M L x I 1 ⊔ K49M L x I 2 = ⊤ := by
  have hI : I = L ⊔ Lc L x 1 ⊔ Lc L x 2 := eq_sup_Lc h hxX hgen hord
  have h0 : K49M L x I 0 = (L.subgroupOf I).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) := by
    show ((Lc L x 0).subgroupOf I).map _ = _
    rw [show Lc L x 0 = L from by rw [Lc, pow_zero, conjugate_one]]
  have h1 : K49M L x I 1 =
      ((Lc L x 1).subgroupOf I).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) := rfl
  have h2 : K49M L x I 2 =
      ((Lc L x 2).subgroupOf I).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) := rfl
  rw [h0, h1, h2, ← Subgroup.map_sup, ← Subgroup.map_sup]
  have hsub : (L.subgroupOf I) ⊔ ((Lc L x 1).subgroupOf I) ⊔ ((Lc L x 2).subgroupOf I) =
      (⊤ : Subgroup ↥I) := by
    rw [← Subgroup.subgroupOf_sup (le_I h) (Lc_le_I h (K49pow_mem_X hgen 1)),
      ← Subgroup.subgroupOf_sup (sup_le (le_I h) (Lc_le_I h (K49pow_mem_X hgen 1)))
        (Lc_le_I h (K49pow_mem_X hgen 2)),
      ← hI, Subgroup.subgroupOf_self]
  rw [hsub]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

private lemma K49M_comm {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    ∀ i j : Fin 3, i ≠ j → ∀ a ∈ K49M L x I i, ∀ b ∈ K49M L x I j, Commute a b := by
  intro i j hij a ha b hb
  obtain ⟨ai, hai, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨bi, hbi, rfl⟩ := Subgroup.mem_map.mp hb
  have hai' : (ai : G) ∈ Lc L x i.val := hai
  have hbi' : (bi : G) ∈ Lc L x j.val := hbi
  have hxi : x ^ i.val ∈ X := K49pow_mem_X hgen i.val
  have hxj : x ^ j.val ∈ X := K49pow_mem_X hgen j.val
  have hne : Lc L x i.val ≠ Lc L x j.val := K49Lc_ne h hxX hgen hord hij
  have hcommP : ⁅(ai : G), (bi : G)⁆ ∈ CFSG.Open.pCoreOf 2 I := by
    rw [← inf_I_Q_eq_pCoreOf h]
    exact (Subgroup.commutator_le.mp (Lc_comm_le_P h hxi hxj hne)) ai hai' bi hbi'
  have hmemI : ⁅(ai : G), (bi : G)⁆ ∈ I := (CFSG.LieType.BorelTits.pCoreOf_le 2 I) hcommP
  have hcore : (⟨⁅(ai : G), (bi : G)⁆, hmemI⟩ : ↥I) ∈ CFSG.pCore 2 ↥I :=
    (mem_pCoreOf_iff hmemI).mp hcommP
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) (⟨⁅(ai : G), (bi : G)⁆, hmemI⟩ : ↥I) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hcore
  have h2 : ⁅(QuotientGroup.mk' (CFSG.pCore 2 ↥I)) ai,
      (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) bi⁆ = 1 := by
    rw [← map_commutatorElement]
    exact h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

private lemma conj_inv_mem_Lc_succ {L : Subgroup G} {x : G} {i : ℕ} {l : G}
    (hl : l ∈ Lc L x i) : x⁻¹ * l * x ∈ Lc L x (i + 1) := by
  have hmap : (Lc L x i).map (MulAut.conj x⁻¹).toMonoidHom = Lc L x (i + 1) := by
    show CFSG.conjugate (CFSG.conjugate L (x ^ i)) x = CFSG.conjugate L (x ^ (i + 1))
    rw [conjugate_conjugate, ← pow_succ]
  rw [← hmap]
  exact Subgroup.mem_map.mpr ⟨l, hl, by
    change (MulAut.conj x⁻¹) l = x⁻¹ * l * x
    rw [MulAut.conj_apply, inv_inv]⟩

private lemma exists_conj_inv_eq_of_mem_Lc_succ {L : Subgroup G} {x : G} {i : ℕ} {b : G}
    (hb : b ∈ Lc L x (i + 1)) : ∃ l ∈ Lc L x i, x⁻¹ * l * x = b := by
  have hmap : (Lc L x i).map (MulAut.conj x⁻¹).toMonoidHom = Lc L x (i + 1) := by
    show CFSG.conjugate (CFSG.conjugate L (x ^ i)) x = CFSG.conjugate L (x ^ (i + 1))
    rw [conjugate_conjugate, ← pow_succ]
  rw [← hmap] at hb
  obtain ⟨l, hl, hlb⟩ := Subgroup.mem_map.mp hb
  refine ⟨l, hl, ?_⟩
  rw [← hlb]
  change x⁻¹ * l * x = (MulAut.conj x⁻¹) l
  rw [MulAut.conj_apply, inv_inv]

private lemma K49Theta_mk {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (a : ↥I) :
    ∃ b : ↥I, (b : G) = x⁻¹ * (a : G) * x ∧
      K49Theta h hxX ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)) a) =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) b := by
  obtain ⟨b, hb, hθ⟩ := CFSG.RankThree.PartTwo.Sec19.Step1910Proof.quotAct_mk
    ((h.X_le).trans (le_normalizer_I h)) ⟨x⁻¹, X.inv_mem hxX⟩ a
  refine ⟨b, by simpa only [inv_inv] using hb, ?_⟩
  change CFSG.RankThree.PartTwo.Sec19.Step1910Proof.quotAct
    ((h.X_le).trans (le_normalizer_I h)) ⟨x⁻¹, X.inv_mem hxX⟩
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)) a) = (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) b
  exact hθ

private lemma K49M_map_theta_step {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) {i : ℕ} (hi : i < 3) (j : Fin 3)
    (hj : Lc L x (i + 1) = Lc L x j.val) :
    (K49M L x I ⟨i, hi⟩).map (K49Theta h hxX).toMonoidHom = K49M L x I j := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨u, hu, rfl⟩
    obtain ⟨a, haa, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨b, hb, hθ⟩ := K49Theta_mk h hxX a
    change (K49Theta h hxX) ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)) a) ∈ K49M L x I j
    rw [hθ]
    refine Subgroup.mem_map.mpr ⟨b, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, hb, ← hj]
    exact conj_inv_mem_Lc_succ haa
  · rintro y hy
    obtain ⟨b, hbb, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨l, hl, hlb⟩ := exists_conj_inv_eq_of_mem_Lc_succ (L := L) (x := x) (i := i)
      (by rw [hj]; exact hbb)
    obtain ⟨b', hb', hθ⟩ := K49Theta_mk h hxX ⟨l, (Lc_le_I h (K49pow_mem_X hgen i)) hl⟩
    have hb'b : b' = b := Subtype.ext (hb'.trans hlb)
    refine Subgroup.mem_map.mpr
      ⟨(QuotientGroup.mk' (CFSG.pCore 2 ↥I)) ⟨l, (Lc_le_I h (K49pow_mem_X hgen i)) hl⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr
        ⟨⟨l, (Lc_le_I h (K49pow_mem_X hgen i)) hl⟩,
          by rw [Subgroup.mem_subgroupOf]; exact hl, rfl⟩
    · change (K49Theta h hxX) ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)) ⟨l,
        (Lc_le_I h (K49pow_mem_X hgen i)) hl⟩) = (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) b
      rw [hθ, hb'b]

private lemma K49M_map_theta {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    (K49M L x I 0).map (K49Theta h hxX).toMonoidHom = K49M L x I 1 ∧
    (K49M L x I 1).map (K49Theta h hxX).toMonoidHom = K49M L x I 2 ∧
    (K49M L x I 2).map (K49Theta h hxX).toMonoidHom = K49M L x I 0 := by
  have hx3 : x ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  refine ⟨?_, ?_, ?_⟩
  · simpa using K49M_map_theta_step h hxX hgen (i := 0) (by norm_num) 1 rfl
  · simpa using K49M_map_theta_step h hxX hgen (i := 1) (by norm_num) 2 rfl
  · refine (K49M_map_theta_step h hxX hgen (i := 2) (by norm_num) 0 ?_).trans ?_
    · change CFSG.conjugate L (x ^ 3) = CFSG.conjugate L (x ^ (0 : Fin 3).val)
      rw [show (0 : Fin 3).val = 0 from rfl, hx3, pow_zero, conjugate_one]
    · rfl

private lemma K49Theta_cube {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hord : orderOf x = 3) :
    ∀ u : Bar2 I, K49Theta h hxX (K49Theta h hxX (K49Theta h hxX u)) = u := by
  have hx3 : x ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  have hxa3 : (⟨x⁻¹, X.inv_mem hxX⟩ : X) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, inv_pow, hx3, inv_one]
  have hθ3 : K49Theta h hxX ^ 3 = 1 := by
    change (CFSG.RankThree.PartTwo.Sec19.Step1910Proof.quotAct
      ((h.X_le).trans (le_normalizer_I h)) ⟨x⁻¹, X.inv_mem hxX⟩) ^ 3 = 1
    rw [← map_pow, hxa3, map_one]
  intro u
  show (K49Theta h hxX ^ 3) u = u
  rw [hθ3]
  rfl

private lemma K49M_inf_sup_eq_bot {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    K49M L x I i ⊓ (K49M L x I j ⊔ K49M L x I k) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  obtain ⟨hwi, hwjk⟩ := Subgroup.mem_inf.mp hw
  obtain ⟨a, haa, rfl⟩ := Subgroup.mem_map.mp hwi
  have haL : (a : G) ∈ Lc L x i.val := haa
  have hN : K49M L x I j ≤ Subgroup.normalizer (K49M L x I k : Set (Bar2 I)) :=
    factor_le_normalizer (K49M_comm h hxX hgen hord) hjk
  obtain ⟨wj, hwj, wk, hwk, hwjwk⟩ := (mem_sup_of_le_normalizer hN).mp hwjk
  obtain ⟨b, hbb, rfl⟩ := Subgroup.mem_map.mp hwj
  obtain ⟨c, hcc, rfl⟩ := Subgroup.mem_map.mp hwk
  have hbc : (b : G) * (c : G) ∈ Lc L x j.val ⊔ Lc L x k.val :=
    Subgroup.mul_mem_sup hbb hcc
  have heq : (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) a =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) (b * c) := by
    rw [map_mul]
    exact hwjwk.symm
  have hqcore : a⁻¹ * (b * c) ∈ CFSG.pCore 2 ↥I := QuotientGroup.eq.mp heq
  set q : ↥I := a⁻¹ * (b * c) with hqdef
  have hqmem : (q : G) ∈ CFSG.Open.pCoreOf 2 I := (mem_pCoreOf_iff q.2).mpr hqcore
  have hqP : (q : G) ∈ I ⊓ Q := by simpa only [inf_I_Q_eq_pCoreOf h] using hqmem
  have ha_eq : (a : G) = (b : G) * (c : G) * (q : G)⁻¹ := by
    rw [hqdef]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have ha_sup : (a : G) ∈ Lc L x j.val ⊔ Lc L x k.val ⊔ K49P I Q := by
    rw [ha_eq]
    exact Subgroup.mul_mem_sup hbc (Subgroup.inv_mem _ hqP)
  have hacore : (a : G) ∈ CFSG.Open.pCoreOf 2 (Lc L x i.val) :=
    inf_Lc_sup_Lc_Lc_P_le_pCoreOf h (K49pow_mem_X hgen i.val) (K49pow_mem_X hgen j.val)
      (K49pow_mem_X hgen k.val) (K49Lc_ne h hxX hgen hord hij) (K49Lc_ne h hxX hgen hord hik)
      (K49Lc_ne h hxX hgen hord hjk) ⟨haL, ha_sup⟩
  have haQ : (a : G) ∈ Q := by
    rw [← Lc_inf_Q_eq_pCoreOf h (K49pow_mem_X hgen i.val)] at hacore
    exact hacore.2
  have haI : (a : G) ∈ I := (Lc_le_I h (K49pow_mem_X hgen i.val)) haL
  have hapI : (a : G) ∈ CFSG.Open.pCoreOf 2 I := by
    rw [← inf_I_Q_eq_pCoreOf h]
    exact ⟨haI, haQ⟩
  exact (QuotientGroup.eq_one_iff _).mpr ((mem_pCoreOf_iff a.2).mp hapI)

private abbrev K49xK (I X : Subgroup G) (x : G) (hx : x ∈ X) : ↥(I ⊔ X) :=
  ⟨x, le_sup_right (a := I) (b := X) hx⟩

private abbrev K49iK (I X : Subgroup G) (i : ↥I) : ↥(I ⊔ X) :=
  ⟨i, le_sup_left (a := I) (b := X) i.2⟩

private lemma K49_CI_map_le_fixed {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) :
    ((Subgroup.centralizer (X : Set G) ⊓ I).subgroupOf I).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) ≤ fixedSubgroup (K49Theta h hxX) := by
  rintro u ⟨c, hc, rfl⟩
  have hcC : (c : G) ∈ Subgroup.centralizer (X : Set G) := (Subgroup.mem_inf.mp hc).1
  change (K49Theta h hxX) ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)) c) =
    (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) c
  obtain ⟨b, hb, hθ⟩ := K49Theta_mk h hxX c
  rw [hθ]
  have hbc : b = c := by
    apply Subtype.ext
    rw [hb]
    have hcc : (c : G) * x = x * (c : G) :=
      (Subgroup.mem_centralizer_iff.mp hcC x hxX).symm
    rw [mul_assoc, hcc, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hbc]

private lemma K49_fixed_commutator {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) {i : ↥I}
    (hi : K49Theta h hxX ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)) i) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) i) :
    x * (i : G) * x⁻¹ * (i : G)⁻¹ ∈ I ⊓ Q := by
  obtain ⟨b, hb, hθ⟩ := K49Theta_mk h hxX i
  have hbI : b * i⁻¹ ∈ CFSG.pCore 2 ↥I := by
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) b =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) i := by rw [← hθ]; exact hi
    simpa only [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem).mp h1
  have hbP : (b : G) * (i : G)⁻¹ ∈ I ⊓ Q := by
    rw [inf_I_Q_eq_pCoreOf h]
    exact (mem_pCoreOf_iff (I.mul_mem b.2 (I.inv_mem i.2))).mpr hbI
  have hq : x⁻¹ * (i : G) * x * (i : G)⁻¹ ∈ I ⊓ Q := by
    rw [hb] at hbP; exact hbP
  set K : Subgroup G := I ⊔ X
  have hXK : X ≤ K := le_sup_right
  have hKn : K ≤ Subgroup.normalizer (I ⊓ Q : Set G) :=
    (le_inf (sup_le Subgroup.le_normalizer ((h.X_le).trans (le_normalizer_I h)))
      ((sup_le (I_le_H h) h.X_le).trans (H_le_normalizer_Q h))).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := I) (K := Q))
  have hconj : x * (x⁻¹ * (i : G) * x * (i : G)⁻¹)⁻¹ * x⁻¹ ∈ I ⊓ Q :=
    (Subgroup.mem_normalizer_iff.mp (hKn (hXK hxX)) _).mp ((I ⊓ Q).inv_mem hq)
  convert hconj using 1
  group

private lemma centralizer_zpowers_map_of_commute {K H : Type*} [Group K] [Group H]
    (hom : K →* H) {x : K} {z : H} (hzx : Commute (hom x) z) :
    z ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup K).map hom : Set H) := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hs
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [← hn, map_zpow]
  exact (hzx.zpow_left n).eq

private lemma exists_centralizer_mul_inv_mem_of_zpowers {K : Type*} [Group K] [Finite K]
    {N : Subgroup K} [N.Normal] {x i : K} (hx3 : orderOf x = 3) (hN : IsPGroup 2 N)
    (hxi : x * i * x⁻¹ * i⁻¹ ∈ N) :
    ∃ e : K, e ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup K) : Set K) ∧
      e * i⁻¹ ∈ N := by
  let hom : K →* K ⧸ N := QuotientGroup.mk' N
  have hker : ¬ 3 ∣ Nat.card hom.ker := by
    rw [show hom.ker = N from QuotientGroup.ker_mk' N]
    obtain ⟨m, hm⟩ := hN.exists_card_eq
    rw [hm]
    intro h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  have hactor : IsPGroup 3 (Subgroup.zpowers x : Subgroup K) := by
    have hcard : Nat.card (Subgroup.zpowers x : Subgroup K) = 3 := by
      rw [Nat.card_zpowers, hx3]
    exact IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hmap :=
    CFSG.RankThreeEvenClassification.Helpers.centralizer_map_eq_of_pGroup_prime_complement_kernel
      3 Nat.prime_three hom (QuotientGroup.mk'_surjective N) hker (Subgroup.zpowers x) hactor
  let z : K ⧸ N := hom i
  have hconj : hom (x * i * x⁻¹) = hom i := by
    apply (QuotientGroup.eq_iff_div_mem).mpr
    simpa only [div_eq_mul_inv, mul_assoc] using hxi
  have hzx : Commute (hom x) z := by
    have hfix : hom x * z * (hom x)⁻¹ = z := by
      have h1 : hom x * z * (hom x)⁻¹ = hom (x * i * x⁻¹) := by
        rw [show z = hom i from rfl]
        simp only [map_mul, map_inv]
      rw [h1, hconj]
    calc hom x * z = (hom x * z * (hom x)⁻¹) * hom x := by group
      _ = z * hom x := by rw [hfix]
  have hzmem : z ∈ Subgroup.centralizer
      ((Subgroup.zpowers x : Subgroup K).map hom : Set (K ⧸ N)) :=
    centralizer_zpowers_map_of_commute hom hzx
  have hzLHS : z ∈ (Subgroup.centralizer (Subgroup.zpowers x : Subgroup K)).map hom := by
    rw [hmap]; exact hzmem
  obtain ⟨e, he, hez⟩ := Subgroup.mem_map.mp hzLHS
  refine ⟨e, he, ?_⟩
  have h := (QuotientGroup.eq_iff_div_mem).mp hez
  simpa only [div_eq_mul_inv] using h

private lemma K49_fixed_lift_exists {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hord : orderOf x = 3) {i : ↥I}
    (hxi : x * (i : G) * x⁻¹ * (i : G)⁻¹ ∈ I ⊓ Q) :
    ∃ e : ↥(I ⊔ X),
      e ∈ Subgroup.centralizer (Subgroup.zpowers (K49xK I X x hxX : ↥(I ⊔ X)) : Set _) ∧
      e * (K49iK I X i : ↥(I ⊔ X))⁻¹ ∈ (I ⊓ Q).subgroupOf (I ⊔ X) := by
  have hPK_le : I ⊓ Q ≤ I ⊔ X := inf_le_left.trans le_sup_left
  have hKn : I ⊔ X ≤ Subgroup.normalizer (I ⊓ Q : Set G) :=
    (le_inf (sup_le Subgroup.le_normalizer ((h.X_le).trans (le_normalizer_I h)))
      ((sup_le (I_le_H h) h.X_le).trans (H_le_normalizer_Q h))).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := I) (K := Q))
  haveI : ((I ⊓ Q).subgroupOf (I ⊔ X)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKn
  have hN2 : IsPGroup 2 ((I ⊓ Q).subgroupOf (I ⊔ X)) :=
    ((isPGroup_Q h).to_le inf_le_right).of_equiv (Subgroup.subgroupOfEquivOfLe hPK_le).symm
  have hx3 : orderOf (K49xK I X x hxX : ↥(I ⊔ X)) = 3 := by
    rw [Subgroup.orderOf_mk, hord]
  have hxiN : (K49xK I X x hxX : ↥(I ⊔ X)) * K49iK I X i *
      (K49xK I X x hxX : ↥(I ⊔ X))⁻¹ * K49iK I X i⁻¹ ∈
      (I ⊓ Q).subgroupOf (I ⊔ X) := by
    rw [Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hxi
  exact exists_centralizer_mul_inv_mem_of_zpowers hx3 hN2 hxiN

private lemma K49_fixed_lift_mem {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) {i : ↥I} {e : ↥(I ⊔ X)}
    (he : e ∈ Subgroup.centralizer (Subgroup.zpowers (K49xK I X x hxX : ↥(I ⊔ X)) : Set _))
    (heN : e * (K49iK I X i : ↥(I ⊔ X))⁻¹ ∈ (I ⊓ Q).subgroupOf (I ⊔ X)) :
    ∃ eI : ↥I, (eI : G) ∈ Subgroup.centralizer (X : Set G) ∧
      (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) eI =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) i := by
  have heqP : ((e * (K49iK I X i : ↥(I ⊔ X))⁻¹ : ↥(I ⊔ X)) : G) ∈ I ⊓ Q :=
    Subgroup.mem_subgroupOf.mp heN
  have heI : (e : G) ∈ I := by
    have he_eq : (e : G) =
        ((e * (K49iK I X i : ↥(I ⊔ X))⁻¹ : ↥(I ⊔ X)) : G) * (i : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [he_eq]; exact I.mul_mem heqP.1 i.2
  have heC : (e : G) ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (K49xK I X y hy : ↥(I ⊔ X)) ∈
        Subgroup.zpowers (K49xK I X x hxX : ↥(I ⊔ X)) := by
      rw [hgen] at hy
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp he _ hy')
  let eI : ↥I := ⟨(e : G), heI⟩
  have heP : eI * i⁻¹ ∈ CFSG.pCore 2 ↥I := by
    have hxmem : (e : G) * (i : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 I := by
      rw [← inf_I_Q_eq_pCoreOf h]
      exact ⟨by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using heqP.1,
        by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using heqP.2⟩
    change (⟨(e : G) * (i : G)⁻¹, I.mul_mem heI (I.inv_mem i.2)⟩ : ↥I) ∈ CFSG.pCore 2 ↥I
    exact (mem_pCoreOf_iff (I.mul_mem heI (I.inv_mem i.2))).mp hxmem
  refine ⟨eI, heC, ?_⟩
  exact (QuotientGroup.eq_iff_div_mem).mpr (by simpa only [div_eq_mul_inv] using heP)

private lemma K49_CI_image_eq_fixed {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    ((Subgroup.centralizer (X : Set G) ⊓ I).subgroupOf I).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) = fixedSubgroup (K49Theta h hxX) := by
  classical
  refine le_antisymm (K49_CI_map_le_fixed h hxX) ?_
  intro u hu
  obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I) u
  have hxi := K49_fixed_commutator h hxX hu
  obtain ⟨e, he, heN⟩ := K49_fixed_lift_exists h hxX hord hxi
  obtain ⟨eI, heC, heq⟩ := K49_fixed_lift_mem h hxX hgen he heN
  exact Subgroup.mem_map.mpr ⟨eI,
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨heC, eI.2⟩), heq⟩

private noncomputable def K49FixedEquiv {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    K49M L x I 0 ≃* fixedSubgroup (K49Theta h hxX) :=
  fixedPointsEquiv (K49M_comm h hxX hgen hord)
    (K49M_inf_sup_eq_bot h hxX hgen hord (i := 0) (j := 1) (k := 2)
      (by decide) (by decide) (by decide))
    (by
      rw [eq_bot_iff]
      have h := K49M_inf_sup_eq_bot h hxX hgen hord (i := 1) (j := 0) (k := 2)
        (by decide) (by decide) (by decide)
      rw [eq_bot_iff] at h
      intro w hw
      exact h (Subgroup.mem_inf.mpr ⟨hw.1, Subgroup.mem_sup_right hw.2⟩))
    (K49M_sup_top h hxX hgen hord)
    (K49Theta h hxX) (K49M_map_theta h hxX hgen hord).1
    (K49M_map_theta h hxX hgen hord).2.1 (K49M_map_theta h hxX hgen hord).2.2
    (K49Theta_cube h hxX hord)

private lemma L_inf_Q_eq_pCoreOf {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    L ⊓ Q = CFSG.Open.pCoreOf 2 L := by
  have h1 := conjugate_inf_pCoreOf_eq h (X.one_mem : (1 : G) ∈ X)
  simpa only [conjugate_one] using h1

private lemma K49M_zero_range {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) (x : G) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)).comp (Subgroup.inclusion (le_I h))).range =
      K49M L x I 0 := by
  have h0 : K49M L x I 0 =
      (L.subgroupOf I).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) := by
    show ((Lc L x 0).subgroupOf I).map _ = _
    rw [show Lc L x 0 = L from by rw [Lc, pow_zero, conjugate_one]]
  rw [h0]
  ext y
  constructor
  · rintro ⟨l, rfl⟩
    exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion (le_I h) l,
      Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have hi' : (i : G) ∈ L := Subgroup.mem_subgroupOf.mp hi
    refine ⟨⟨(i : G), hi'⟩, ?_⟩
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) ⟨(i : G), le_I h hi'⟩ =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) i
    rw [show (⟨(i : G), le_I h hi'⟩ : ↥I) = i from Subtype.ext rfl]

private lemma K49M_zero_ker {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) (x : G) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)).comp (Subgroup.inclusion (le_I h))).ker =
      CFSG.pCore 2 ↥L := by
  ext l
  rw [MonoidHom.mem_ker]
  constructor
  · intro hl
    have h1 : ((Subgroup.inclusion (le_I h) l : ↥I) : G) ∈ CFSG.Open.pCoreOf 2 I :=
      (mem_pCoreOf_iff (Subgroup.inclusion (le_I h) l).2).mpr
        ((QuotientGroup.eq_one_iff (Subgroup.inclusion (le_I h) l)).mp hl)
    rw [← inf_I_Q_eq_pCoreOf h] at h1
    have hLp : (l : G) ∈ CFSG.Open.pCoreOf 2 L := by
      rw [← L_inf_Q_eq_pCoreOf h]
      exact ⟨l.2, h1.2⟩
    exact (mem_pCoreOf_iff l.2).mp hLp
  · intro hl
    have hLp : (l : G) ∈ CFSG.Open.pCoreOf 2 L := (mem_pCoreOf_iff l.2).mpr hl
    rw [← L_inf_Q_eq_pCoreOf h] at hLp
    have h1 : ((Subgroup.inclusion (le_I h) l : ↥I) : G) ∈ CFSG.Open.pCoreOf 2 I := by
      rw [← inf_I_Q_eq_pCoreOf h]
      exact ⟨le_I h l.2, hLp.2⟩
    exact (QuotientGroup.eq_one_iff (Subgroup.inclusion (le_I h) l)).mpr
      ((mem_pCoreOf_iff (Subgroup.inclusion (le_I h) l).2).mp h1)

private noncomputable def K49M_zero_equiv_Bar2L {H X L Q I : Subgroup G}
    (h : Setup49 H X L Q I) (x : G) : K49M L x I 0 ≃* Bar2 L := by
  let φ : ↥L →* Bar2 I :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥I)).comp (Subgroup.inclusion (le_I h))
  have hrange : φ.range = K49M L x I 0 := K49M_zero_range h x
  have hker : φ.ker = CFSG.pCore 2 ↥L := K49M_zero_ker h x
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* K49M L x I 0 :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))
  exact e.symm

private lemma K49M_zero_isAlt {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) (x : G) :
    IsAlt (K49M L x I 0) 5 := by
  obtain ⟨eL⟩ := h.L_alt
  exact ⟨(K49M_zero_equiv_Bar2L h x).trans eL⟩

private lemma eq_bot_of_isPGroup_normal {X : Type} [Group X] [Finite X] (hX : IsAlt X 5)
    (N : Subgroup X) [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  obtain ⟨e⟩ := hX
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (α := Fin 5) (by simp [Nat.card_eq_fintype_card])
  have hmapbot : N.map e.toMonoidHom = ⊥ := by
    haveI : (N.map e.toMonoidHom).Normal :=
      (show N.Normal from inferInstance).map e.toMonoidHom e.surjective
    have h2 : IsPGroup 2 (N.map e.toMonoidHom) := hN.map e.toMonoidHom
    rcases Subgroup.Normal.eq_bot_or_eq_top (N.map e.toMonoidHom) with hbot | htop
    · exact hbot
    · exfalso
      have hp : IsPGroup 2 (alternatingGroup (Fin 5)) := by
        have htop2 : IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 5))) := htop ▸ h2
        exact htop2.of_equiv Subgroup.topEquiv
      obtain ⟨n, hn⟩ := hp.exists_card_eq
      have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [nat_card_alternatingGroup]
        norm_num [Nat.card_eq_fintype_card]
      rw [hcard] at hn
      have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 60)
      exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  exact (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) (H := N)
    e.injective).mp hmapbot

private lemma KI_eq_perfectCore (X I : Subgroup G) :
    KI X I = CFSG.Quasithin.perfectCore (Subgroup.centralizer (X : Set G) ⊓ I) := rfl

private abbrev K49CI (X I : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (X : Set G) ⊓ I

private abbrev K49CP (X I Q : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (X : Set G) ⊓ I ⊓ Q

private instance : Group.IsPerfect (alternatingGroup (Fin 5)) :=
  Group.isPerfect_def.mpr
    (commutator_alternatingGroup_eq_top (by simp [Nat.card_eq_fintype_card]))

private noncomputable def K49CItoFixed {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    ↥(K49CI X I) →* fixedSubgroup (K49Theta h hxX) :=
  MonoidHom.codRestrict
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)).comp
      (Subgroup.inclusion (inf_le_right : K49CI X I ≤ I)))
    (fixedSubgroup (K49Theta h hxX)) (fun c => by
      have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥I))
          (Subgroup.inclusion (inf_le_right : K49CI X I ≤ I) c) ∈
          ((K49CI X I).subgroupOf I).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) :=
        Subgroup.mem_map.mpr ⟨Subgroup.inclusion (inf_le_right : K49CI X I ≤ I) c,
          Subgroup.mem_subgroupOf.mpr c.2, rfl⟩
      rwa [K49_CI_image_eq_fixed h hxX hgen hord] at hmem)

private lemma K49CItoFixed_ker {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    (K49CItoFixed h hxX hgen hord).ker =
      (K49CP X I Q).subgroupOf (K49CI X I) := by
  ext c
  rw [MonoidHom.mem_ker]
  constructor
  · intro hc
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥I))
        (Subgroup.inclusion (inf_le_right : K49CI X I ≤ I) c) = 1 :=
      Subtype.ext_iff.mp (by
        simpa only [K49CItoFixed, MonoidHom.codRestrict_apply] using hc)
    have h2 : (c : G) ∈ CFSG.Open.pCoreOf 2 I :=
      (mem_pCoreOf_iff (Subgroup.mem_inf.mp c.2).2).mpr
        ((QuotientGroup.eq_one_iff (Subgroup.inclusion
          (inf_le_right : K49CI X I ≤ I) c)).mp h1)
    rw [← inf_I_Q_eq_pCoreOf h] at h2
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨c.2, h2.2⟩)
  · intro hc
    have hcQ : (c : G) ∈ Q := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc)).2
    apply Subtype.ext
    show (QuotientGroup.mk' (CFSG.pCore 2 ↥I))
      (Subgroup.inclusion (inf_le_right : K49CI X I ≤ I) c) = 1
    exact (QuotientGroup.eq_one_iff (Subgroup.inclusion
      (inf_le_right : K49CI X I ≤ I) c)).mpr
      ((mem_pCoreOf_iff (Subgroup.mem_inf.mp c.2).2).mp (by
        rw [← inf_I_Q_eq_pCoreOf h]
        exact ⟨(Subgroup.mem_inf.mp c.2).2, hcQ⟩))

private lemma K49CItoFixed_surjective {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    Function.Surjective (K49CItoFixed h hxX hgen hord) := by
  intro u
  have hu : (u : Bar2 I) ∈ ((K49CI X I).subgroupOf I).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) := by
    rw [K49_CI_image_eq_fixed h hxX hgen hord]
    exact u.2
  obtain ⟨i, hi, hiu⟩ := Subgroup.mem_map.mp hu
  refine ⟨⟨(i : G), Subgroup.mem_subgroupOf.mp hi⟩, Subtype.ext ?_⟩
  change (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) i = (u : Bar2 I)
  exact hiu

private lemma K49Fixed_isAlt {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    IsAlt (fixedSubgroup (K49Theta h hxX)) 5 := by
  obtain ⟨e⟩ := K49M_zero_isAlt h x
  exact ⟨(K49FixedEquiv h hxX hgen hord).symm.trans e⟩

private lemma K49Fixed_perfect {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    Group.IsPerfect (fixedSubgroup (K49Theta h hxX)) := by
  obtain ⟨e⟩ := K49Fixed_isAlt h hxX hgen hord
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

private lemma K49CI_le_KI_sup_CP {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    K49CI X I ≤ KI X I ⊔ K49CP X I Q := by
  haveI : Group.IsPerfect (fixedSubgroup (K49Theta h hxX)) := K49Fixed_perfect h hxX hgen hord
  have hsurj := K49CItoFixed_surjective h hxX hgen hord
  have hmap : (CFSG.Quasithin.perfectCore (⊤ : Subgroup ↥(K49CI X I))).map
      (K49CItoFixed h hxX hgen hord) = ⊤ := by
    rw [CFSG.Quasithin.map_perfectCore, Subgroup.map_top_of_surjective _ hsurj]
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect
      (Subgroup.isPerfect_iff.mp (Group.IsPerfect.top_iff.mpr inferInstance))
  intro c hc
  let c' : ↥(K49CI X I) := ⟨c, hc⟩
  have hc'mem : K49CItoFixed h hxX hgen hord c' ∈
      (CFSG.Quasithin.perfectCore (⊤ : Subgroup ↥(K49CI X I))).map
        (K49CItoFixed h hxX hgen hord) := by
    rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨k, hk, hkc⟩ := Subgroup.mem_map.mp hc'mem
  have hmem : k⁻¹ * c' ∈ (K49CP X I Q).subgroupOf (K49CI X I) := by
    rw [← K49CItoFixed_ker h hxX hgen hord, MonoidHom.mem_ker, map_mul, map_inv, hkc,
      inv_mul_cancel]
  have hck : c = (k : G) * ((k⁻¹ * c' : ↥(K49CI X I)) : G) := by
    have h1 : c' = k * (k⁻¹ * c') := by group
    have := congrArg (fun x : ↥(K49CI X I) => (x : G)) h1
    simpa [c'] using this
  rw [hck]
  refine Subgroup.mul_mem_sup ?_ (Subgroup.mem_subgroupOf.mp hmem)
  have hk' : (k : G) ∈ (CFSG.Quasithin.perfectCore (⊤ : Subgroup ↥(K49CI X I))).map
      (K49CI X I).subtype := Subgroup.mem_map_of_mem _ hk
  rw [CFSG.Quasithin.map_perfectCore, Subgroup.map_top, Subgroup.range_subtype] at hk'
  rwa [KI_eq_perfectCore]

private lemma KI_le_I (X I : Subgroup G) : KI X I ≤ I := by
  rw [KI_eq_perfectCore]
  exact (CFSG.Quasithin.perfectCore_le _).trans inf_le_right

private lemma KI_le_centralizer (X I : Subgroup G) :
    KI X I ≤ Subgroup.centralizer (X : Set G) := by
  rw [KI_eq_perfectCore]
  exact (CFSG.Quasithin.perfectCore_le _).trans inf_le_left

private lemma KI_perfect (X I : Subgroup G) : ⁅KI X I, KI X I⁆ = KI X I := by
  rw [KI_eq_perfectCore]
  exact CFSG.Quasithin.perfectCore_perfect _

private lemma KI_inf_Q_le_centralizer {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    KI X I ⊓ Q ≤ Subgroup.centralizer (X : Set G) :=
  inf_le_left.trans (KI_le_centralizer X I)

private lemma centralizer_Q_le_normalizer_KI {H X L Q I : Subgroup G}
    (h : Setup49 H X L Q I) :
    Q ⊓ Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (KI X I : Set G) := by
  have hQnI : Q ≤ Subgroup.normalizer (I : Set G) :=
    le_normalizer_I_of_le h (fun x => pCoreOf_le_normalizer_conjugate h x.2)
  have hTN : Q ⊓ Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) ⊓ I : Set G) :=
    (le_inf (inf_le_right.trans (Subgroup.le_normalizer : _ ≤
        Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G)))
      (inf_le_left.trans hQnI)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf
        (H := Subgroup.centralizer (X : Set G)) (K := I))
  rw [KI_eq_perfectCore]
  exact hTN.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore
    (Subgroup.centralizer (X : Set G) ⊓ I))

private lemma commutator_centralizer_Q_KI_le_inf {H X L Q I : Subgroup G}
    (h : Setup49 H X L Q I) :
    ⁅Q ⊓ Subgroup.centralizer (X : Set G), KI X I⁆ ≤ KI X I ⊓ Q := by
  have hKI_le_H : KI X I ≤ H := (KI_le_I X I).trans (I_le_H h)
  have hQn : H ≤ Subgroup.normalizer (Q : Set G) := H_le_normalizer_Q h
  have hleKI : ⁅Q ⊓ Subgroup.centralizer (X : Set G), KI X I⁆ ≤ KI X I := by
    refine Subgroup.commutator_le.mpr fun t ht k hk => ?_
    have hmem : t * k * t⁻¹ ∈ KI X I :=
      (Subgroup.mem_normalizer_iff.mp (centralizer_Q_le_normalizer_KI h ht) k).mp hk
    have := (KI X I).mul_mem hmem ((KI X I).inv_mem hk)
    rwa [commutatorElement_def]
  have hleQ : ⁅Q ⊓ Subgroup.centralizer (X : Set G), KI X I⁆ ≤ Q := by
    refine Subgroup.commutator_le.mpr fun t ht k hk => ?_
    have hconj : k * t * k⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hQn (hKI_le_H hk)) t).mp ht.1
    have hkt : ⁅k, t⁆ ∈ Q := by
      have := Q.mul_mem hconj (Q.inv_mem ht.1)
      rwa [commutatorElement_def]
    simpa only [commutatorElement_inv] using Q.inv_mem hkt
  exact le_inf hleKI hleQ

private lemma pCoreOf_subgroupOf_self (X I : Subgroup G) :
    (CFSG.Open.pCoreOf 2 (KI X I)).subgroupOf (KI X I) = CFSG.pCore 2 ↥(KI X I) := by
  rw [CFSG.Open.pCoreOf]
  exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective (KI X I))
    (CFSG.pCore 2 ↥(KI X I))

private noncomputable def K49KItoFixed {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    ↥(KI X I) →* fixedSubgroup (K49Theta h hxX) :=
  (K49CItoFixed h hxX hgen hord).comp
    (Subgroup.inclusion (le_inf (KI_le_centralizer X I) (KI_le_I X I)))

private lemma K49KItoFixed_ker {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    (K49KItoFixed h hxX hgen hord).ker = (KI X I ⊓ Q).subgroupOf (KI X I) := by
  ext c
  rw [MonoidHom.mem_ker]
  constructor
  · intro hc
    have h1 : Subgroup.inclusion (le_inf (KI_le_centralizer X I) (KI_le_I X I)) c ∈
        (K49CItoFixed h hxX hgen hord).ker := hc
    rw [K49CItoFixed_ker h hxX hgen hord] at h1
    have h1' : ((Subgroup.inclusion (le_inf (KI_le_centralizer X I) (KI_le_I X I)) c :
        ↥(K49CI X I)) : G) ∈ K49CP X I Q := Subgroup.mem_subgroupOf.mp h1
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨c.2, (Subgroup.mem_inf.mp h1').2⟩)
  · intro hc
    have hcQ : (c : G) ∈ Q := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc)).2
    change K49CItoFixed h hxX hgen hord
      (Subgroup.inclusion (le_inf (KI_le_centralizer X I) (KI_le_I X I)) c) = 1
    rw [← MonoidHom.mem_ker, K49CItoFixed_ker h hxX hgen hord]
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨(le_inf (KI_le_centralizer X I) (KI_le_I X I)) c.2, hcQ⟩)

private lemma K49KItoFixed_surjective {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    Function.Surjective (K49KItoFixed h hxX hgen hord) := by
  intro u
  obtain ⟨c, hc⟩ := K49CItoFixed_surjective h hxX hgen hord u
  have hle := K49CI_le_KI_sup_CP h hxX hgen hord c.2
  have hnorm : KI X I ≤ Subgroup.normalizer ((K49CP X I Q : Subgroup G) : Set G) :=
    (le_inf (KI_le_centralizer X I) (KI_le_I X I)).trans
      ((le_inf Subgroup.le_normalizer
        ((inf_le_right.trans (I_le_H h)).trans (H_le_normalizer_Q h))).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := K49CI X I) (K := Q)))
  obtain ⟨k, hk, p, hp, hkp⟩ := (mem_sup_of_le_normalizer hnorm).mp hle
  have hpker : K49CItoFixed h hxX hgen hord ⟨p, hp.1⟩ = 1 := by
    rw [← MonoidHom.mem_ker, K49CItoFixed_ker h hxX hgen hord]
    exact Subgroup.mem_subgroupOf.mpr hp
  have hc2 : c = Subgroup.inclusion (le_inf (KI_le_centralizer X I) (KI_le_I X I)) ⟨k, hk⟩ *
      ⟨p, hp.1⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]
    exact hkp.symm
  refine ⟨⟨k, hk⟩, ?_⟩
  change K49CItoFixed h hxX hgen hord
    (Subgroup.inclusion (le_inf (KI_le_centralizer X I) (KI_le_I X I)) ⟨k, hk⟩) = u
  rw [← hc, hc2, map_mul, hpker, mul_one]

private lemma K49KI_pCore_le_ker {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    CFSG.pCore 2 ↥(KI X I) ≤ (K49KItoFixed h hxX hgen hord).ker := by
  have hmapbot : ((CFSG.Open.pCoreOf 2 (KI X I)).subgroupOf (KI X I)).map
      (K49KItoFixed h hxX hgen hord) = ⊥ := by
    haveI : ((CFSG.Open.pCoreOf 2 (KI X I)).subgroupOf (KI X I)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (KI X I))
    haveI : (((CFSG.Open.pCoreOf 2 (KI X I)).subgroupOf (KI X I)).map
        (K49KItoFixed h hxX hgen hord)).Normal :=
      Subgroup.Normal.map inferInstance _ (K49KItoFixed_surjective h hxX hgen hord)
    refine eq_bot_of_isPGroup_normal (K49Fixed_isAlt h hxX hgen hord) _ ?_
    exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (KI X I)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 (KI X I))).symm).map
        (K49KItoFixed h hxX hgen hord)
  have hle : ((CFSG.Open.pCoreOf 2 (KI X I)).subgroupOf (KI X I)) ≤
      (K49KItoFixed h hxX hgen hord).ker :=
    (Subgroup.map_eq_bot_iff (H := (CFSG.Open.pCoreOf 2 (KI X I)).subgroupOf (KI X I))
      (f := K49KItoFixed h hxX hgen hord)).mp hmapbot
  rw [← pCoreOf_subgroupOf_self X I]
  exact hle

private lemma KI_inf_Q_eq_pCoreOf {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    KI X I ⊓ Q = CFSG.Open.pCoreOf 2 (KI X I) := by
  refine le_antisymm ?_ ?_
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
    · have h1 : KI X I ≤ Subgroup.normalizer (KI X I : Set G) := Subgroup.le_normalizer
      have h2 : KI X I ≤ Subgroup.normalizer (Q : Set G) :=
        ((KI_le_I X I).trans (I_le_H h)).trans (H_le_normalizer_Q h)
      exact (le_inf h1 h2).trans (Subgroup.inf_normalizer_le_normalizer_inf
        (H := KI X I) (K := Q))
    · exact (isPGroup_Q h).to_le inf_le_right
  · have hle := K49KI_pCore_le_ker h hxX hgen hord
    intro z hz
    have hzKI : z ∈ KI X I := (CFSG.LieType.BorelTits.pCoreOf_le 2 (KI X I)) hz
    have hzker : (⟨z, hzKI⟩ : ↥(KI X I)) ∈ (K49KItoFixed h hxX hgen hord).ker :=
      hle ((mem_pCoreOf_iff hzKI).mp hz)
    rw [K49KItoFixed_ker h hxX hgen hord] at hzker
    exact ⟨hzKI, (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hzker)).2⟩

private lemma Bar2KI_isAlt {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3) :
    IsAlt (Bar2 (KI X I)) 5 := by
  have hker_eq : CFSG.pCore 2 ↥(KI X I) = (K49KItoFixed h hxX hgen hord).ker := by
    rw [K49KItoFixed_ker h hxX hgen hord, KI_inf_Q_eq_pCoreOf h hxX hgen hord,
      pCoreOf_subgroupOf_self X I]
  obtain ⟨eA5⟩ := K49Fixed_isAlt h hxX hgen hord
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker_eq).trans
    ((QuotientGroup.quotientKerEquivOfSurjective (K49KItoFixed h hxX hgen hord)
      (K49KItoFixed_surjective h hxX hgen hord)).trans eA5)⟩

private lemma KI_le_normalizer_CP {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    KI X I ≤ Subgroup.normalizer ((K49CP X I Q : Subgroup G) : Set G) :=
  (le_inf (KI_le_centralizer X I) (KI_le_I X I)).trans
    ((le_inf Subgroup.le_normalizer
      ((inf_le_right.trans (I_le_H h)).trans (H_le_normalizer_Q h))).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := K49CI X I) (K := Q)))

private lemma K49CI_subgroupOf_KI_normal {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    ((KI X I).subgroupOf (K49CI X I)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (by
    rw [KI_eq_perfectCore]
    exact Subgroup.le_normalizer.trans
      (CFSG.Quasithin.normalizer_le_normalizer_perfectCore
        (Subgroup.centralizer (X : Set G) ⊓ I)))

private lemma K49CI_quot_KI_isPGroup {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord : orderOf x = 3)
    [hN : ((KI X I).subgroupOf (K49CI X I)).Normal] :
    IsPGroup 2 (↥(K49CI X I) ⧸ (KI X I).subgroupOf (K49CI X I)) := by
  refine ((isPGroup_Q h).to_le inf_le_right).of_surjective
    ((QuotientGroup.mk' ((KI X I).subgroupOf (K49CI X I))).comp
      (Subgroup.inclusion (inf_le_left : K49CP X I Q ≤ K49CI X I))) ?_
  intro g
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ g
  obtain ⟨k, hk, p, hp, hkp⟩ :=
    (mem_sup_of_le_normalizer (KI_le_normalizer_CP h)).mp
      (K49CI_le_KI_sup_CP h hxX hgen hord c.2)
  have hkCI : k ∈ K49CI X I := (le_inf (KI_le_centralizer X I) (KI_le_I X I)) hk
  have hk1 : (QuotientGroup.mk' ((KI X I).subgroupOf (K49CI X I)))
      (⟨k, hkCI⟩ : ↥(K49CI X I)) = 1 :=
    (QuotientGroup.eq_one_iff (⟨k, hkCI⟩ : ↥(K49CI X I))).mpr
      (Subgroup.mem_subgroupOf.mpr hk)
  refine ⟨⟨p, hp⟩, ?_⟩
  show (QuotientGroup.mk' ((KI X I).subgroupOf (K49CI X I)))
    (Subgroup.inclusion (inf_le_left : K49CP X I Q ≤ K49CI X I) ⟨p, hp⟩) =
    (QuotientGroup.mk' ((KI X I).subgroupOf (K49CI X I))) c
  rw [show Subgroup.inclusion (inf_le_left : K49CP X I Q ≤ K49CI X I) ⟨p, hp⟩ =
    (⟨p, hp.1⟩ : ↥(K49CI X I)) from Subtype.ext rfl]
  have hc_eq2 : c = (⟨k, hkCI⟩ : ↥(K49CI X I)) * ⟨p, hp.1⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hkp.symm
  rw [hc_eq2, map_mul, hk1, one_mul]

private lemma Z49_le_KI {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {A : Subgroup G}
    (hA : XReg49 X A) (hAI : A ≤ I) : Z49 X A ≤ KI X I := by
  obtain ⟨x, hxX, hgen, -, -, -⟩ := exists_generator49 h
  have hord : orderOf x = 3 := orderOf_eq_three_of_zpowers hgen h.card_X
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZle : Z49 X A ≤ K49CI X I :=
    le_inf inf_le_right (inf_le_left.trans hAI)
  haveI hN : ((KI X I).subgroupOf (K49CI X I)).Normal := K49CI_subgroupOf_KI_normal h
  have hP : IsPGroup 2 (↥(K49CI X I) ⧸ (KI X I).subgroupOf (K49CI X I)) :=
    K49CI_quot_KI_isPGroup h hxX hgen hord
  intro z hz
  by_contra hzKI
  let π := QuotientGroup.mk' ((KI X I).subgroupOf (K49CI X I))
  have hzCI : z ∈ K49CI X I := hZle hz
  have hgne : π ⟨z, hzCI⟩ ≠ 1 := by
    intro hcon
    exact hzKI (Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (⟨z, hzCI⟩ : ↥(K49CI X I))).mp hcon))
  have hz3 : z ^ 3 = 1 := by
    have hdvd : orderOf z ∣ 3 := by
      have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : Z49 X A)
      rwa [Subgroup.orderOf_mk, hA.2.2.2.2] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hpow : (π ⟨z, hzCI⟩) ^ 3 = 1 := by
    rw [← map_pow, show (⟨z, hzCI⟩ : ↥(K49CI X I)) ^ 3 = 1 from
      Subtype.ext (by simpa using hz3), map_one]
  have h3dvd : orderOf (π ⟨z, hzCI⟩) ∣ 3 := orderOf_dvd_of_pow_eq_one hpow
  have h2dvd : 2 ∣ orderOf (π ⟨z, hzCI⟩) := hP.dvd_orderOf hgne
  exact absurd (Nat.dvd_trans h2dvd h3dvd) (by norm_num)

private lemma centralizer_sup_eq_inf (H K : Subgroup G) :
    Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) =
      Subgroup.centralizer (H : Set G) ⊓ Subgroup.centralizer (K : Set G) := by
  ext g
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun h x hx => hx.elim (fun hx => h.1 x hx) (fun hx => h.2 x hx)⟩

theorem kbasic49 {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {A : Subgroup G}
    (hA : XReg49 X A) (hAI : A ≤ I) :
    ⁅KI X I, KI X I⁆ = KI X I ∧ IsAlt (Bar2 (KI X I)) 5 ∧
    KI X I ⊓ Q = CFSG.Open.pCoreOf 2 (KI X I) ∧
    Z49 X A ≤ KI X I ∧ KI X I ⊓ Q ≤ Subgroup.centralizer (X : Set G) ∧
    ⁅Q ⊓ Subgroup.centralizer (X : Set G), KI X I⁆ ≤ KI X I ⊓ Q := by
  obtain ⟨x, hxX, hgen, -, -, -⟩ := exists_generator49 h
  have hord : orderOf x = 3 := orderOf_eq_three_of_zpowers hgen h.card_X
  exact ⟨KI_perfect X I, Bar2KI_isAlt h hxX hgen hord,
    KI_inf_Q_eq_pCoreOf h hxX hgen hord, Z49_le_KI h hA hAI,
    KI_inf_Q_le_centralizer h, commutator_centralizer_Q_KI_le_inf h⟩

private lemma exists_Z49_generator {X A : Subgroup G} (hA : XReg49 X A) :
    ∃ z ∈ Z49 X A, z ≠ 1 ∧ orderOf z = 3 ∧ Z49 X A = Subgroup.zpowers z := by
  have hZcard : Nat.card (Z49 X A) = 3 := hA.2.2.2.2
  have hZne : Z49 X A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZcard
    omega
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hdvd : orderOf z ∣ 3 := by
    have h1 := orderOf_dvd_natCard (⟨z, hzZ⟩ : Z49 X A)
    rwa [Subgroup.orderOf_mk, hZcard] at h1
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hz3 : orderOf z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hz1'
    · exact h3
  have hZeq : Z49 X A = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ)
      (by rw [Nat.card_zpowers, hz3, hZcard])).symm
  exact ⟨z, hzZ, hz1', hz3, hZeq⟩

private lemma K49_T_setup {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {A : Subgroup G}
    {V : Subgroup G} (hVE : V = KI X I ⊓ Q) (hVK : V ≤ KI X I)
    (hZK : Z49 X A ≤ KI X I) :
    V ≤ Q ⊓ Subgroup.centralizer (X : Set G) ∧
    (Q ⊓ Subgroup.centralizer (X : Set G)) ≤ Subgroup.normalizer (V : Set G) ∧
    IsPGroup 2 ↥(Q ⊓ Subgroup.centralizer (X : Set G)) ∧
    Z49 X A ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ∧
    Z49 X A ≤ Subgroup.normalizer (V : Set G) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine le_inf ?_ ?_
    · rw [hVE]; exact inf_le_right
    · exact hVK.trans (KI_le_centralizer X I)
  · rw [hVE]
    exact (le_inf (centralizer_Q_le_normalizer_KI h)
      ((inf_le_left : _ ≤ Q).trans Subgroup.le_normalizer)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := KI X I) (K := Q))
  · exact (isPGroup_Q h).to_le inf_le_left
  · exact (le_inf (hZK.trans ((KI_le_I X I).trans ((I_le_H h).trans (H_le_normalizer_Q h))))
      ((hZK.trans (KI_le_centralizer X I)).trans (Subgroup.le_normalizer))).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := Q)
        (K := Subgroup.centralizer (X : Set G)))
  · rw [hVE]
    exact (le_inf (hZK.trans (Subgroup.le_normalizer))
      (hZK.trans ((KI_le_I X I).trans ((I_le_H h).trans (H_le_normalizer_Q h))))).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := KI X I) (K := Q))

private lemma K49_T_eq_centralizer_sup {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {A : Subgroup G} {V : Subgroup G} (hVE : V = KI X I ⊓ Q) (hZK : Z49 X A ≤ KI X I)
    (hZcard : Nat.card (Z49 X A) = 3)
    (hT2 : IsPGroup 2 ↥(Q ⊓ Subgroup.centralizer (X : Set G)))
    (hVT : V ≤ Q ⊓ Subgroup.centralizer (X : Set G))
    (hTNV : (Q ⊓ Subgroup.centralizer (X : Set G)) ≤ Subgroup.normalizer (V : Set G))
    (hZNT : Z49 X A ≤ Subgroup.normalizer
      ((Q ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    (hZNV : Z49 X A ≤ Subgroup.normalizer (V : Set G)) :
    Q ⊓ Subgroup.centralizer (X : Set G) =
      ((Q ⊓ Subgroup.centralizer (X : Set G)) ⊓ Subgroup.centralizer (Z49 X A : Set G)) ⊔ V := by
  refine le_antisymm ?_ (sup_le inf_le_left hVT)
  intro t ht
  have hcop : Nat.Coprime (Nat.card (Z49 X A))
      (Nat.card ↥(Q ⊓ Subgroup.centralizer (X : Set G))) := by
    obtain ⟨m, hm⟩ := hT2.exists_card_eq
    rw [hZcard, hm]
    exact Nat.Coprime.pow_right m (by norm_num)
  have hsolv : Group.IsSolvable ↥(Q ⊓ Subgroup.centralizer (X : Set G)) := by
    have := hT2.isNilpotent; infer_instance
  have hle : ⁅KI X I, Q ⊓ Subgroup.centralizer (X : Set G)⁆ ≤ KI X I ⊓ Q := by
    rw [Subgroup.commutator_comm]
    exact commutator_centralizer_Q_KI_le_inf h
  have hcentral : ∀ d ∈ Z49 X A, d * t * d⁻¹ * t⁻¹ ∈ V := by
    intro d hd
    have hmem : ⁅d, t⁆ ∈ KI X I ⊓ Q :=
      (Subgroup.commutator_le.mp hle) d (hZK hd) t ht
    rw [← hVE] at hmem
    simpa only [commutatorElement_def] using hmem
  exact (mem_centralizer_sup_iff hVT hTNV hZNT hZNV hcop hsolv ht).mp hcentral

private lemma K49_T_card {X Q : Subgroup G} {A V : Subgroup G}
    (hVcard : Nat.card V = 32)
    (hVZcard : Nat.card ↥(V ⊓ Subgroup.centralizer (Z49 X A : Set G)) = 8)
    (hVT : V ≤ Q ⊓ Subgroup.centralizer (X : Set G))
    (hTNV : (Q ⊓ Subgroup.centralizer (X : Set G)) ≤ Subgroup.normalizer (V : Set G))
    (hTsup : Q ⊓ Subgroup.centralizer (X : Set G) =
      ((Q ⊓ Subgroup.centralizer (X : Set G)) ⊓ Subgroup.centralizer (Z49 X A : Set G)) ⊔ V) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer (X : Set G)) =
      4 * Nat.card ↥((Q ⊓ Subgroup.centralizer (X : Set G)) ⊓
        Subgroup.centralizer (Z49 X A : Set G)) := by
  have hidx := index_centralizer_mul (D := Z49 X A)
    (N := Q ⊓ Subgroup.centralizer (X : Set G)) (M := V) hVT hTNV
  have hone : (((Q ⊓ Subgroup.centralizer (X : Set G)) ⊓
      Subgroup.centralizer (Z49 X A : Set G)) ⊔ V).relIndex
      (Q ⊓ Subgroup.centralizer (X : Set G)) = 1 := by
    rw [← hTsup, Subgroup.relIndex_self]
  rw [hone, mul_one] at hidx
  have hVEidx : (V ⊓ Subgroup.centralizer (Z49 X A : Set G)).relIndex V = 4 := by
    have h1 := Subgroup.relIndex_mul_card
      (H := V ⊓ Subgroup.centralizer (Z49 X A : Set G)) (K := V)
    rw [inf_eq_left.mpr inf_le_left, hVZcard, hVcard] at h1
    omega
  rw [hVEidx] at hidx
  have h1 := Subgroup.relIndex_mul_card
    (H := (Q ⊓ Subgroup.centralizer (X : Set G)) ⊓ Subgroup.centralizer (Z49 X A : Set G))
    (K := Q ⊓ Subgroup.centralizer (X : Set G))
  rw [inf_eq_left.mpr inf_le_left, hidx] at h1
  omega

private lemma K49_card_Q_eq {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {A : Subgroup G}
    (hA : XReg49 X A) (hAI : A ≤ I)
    (hT4 : Nat.card ↥(Q ⊓ Subgroup.centralizer (X : Set G)) =
      4 * Nat.card ↥(Q ⊓ Subgroup.centralizer ((X ⊔ Z49 X A : Subgroup G) : Set G))) :
    Nat.card Q = 64 * Nat.card ↥(Q ⊓ Subgroup.centralizer (Z49 X A : Set G)) := by
  have hcount := count49 hA (isPGroup_Q h)
    ((h.X_le).trans (H_le_normalizer_Q h)) ((hAI.trans (I_le_H h)).trans (H_le_normalizer_Q h))
  rw [hT4, mul_pow] at hcount
  have hcancel : Nat.card Q * Nat.card ↥(Q ⊓ Subgroup.centralizer
      ((X ⊔ Z49 X A : Subgroup G) : Set G)) ^ 3 =
      (64 * Nat.card ↥(Q ⊓ Subgroup.centralizer (Z49 X A : Set G))) *
        Nat.card ↥(Q ⊓ Subgroup.centralizer
          ((X ⊔ Z49 X A : Subgroup G) : Set G)) ^ 3 := by
    rw [hcount]
    ring
  exact Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos 3) hcancel

theorem kfacts49 (hI : Inputs49) {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    (hK : KI49 X I) {A : Subgroup G} (hA : XReg49 X A) (hAI : A ≤ I) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer (X : Set G)) =
      4 * Nat.card ↥(Q ⊓ Subgroup.centralizer ((X ⊔ Z49 X A : Subgroup G) : Set G)) ∧
    Nat.card Q = 64 * Nat.card ↥(Q ⊓ Subgroup.centralizer (Z49 X A : Set G)) := by
  classical
  obtain ⟨x, hxX, hgen, -, -, -⟩ := exists_generator49 h
  have hord : orderOf x = 3 := orderOf_eq_three_of_zpowers hgen h.card_X
  have hZK : Z49 X A ≤ KI X I := Z49_le_KI h hA hAI
  obtain ⟨V, hVK, -, hVq8, hVpc, -, -, -, -, hz8⟩ := kmodel49 hI hK (KI_perfect X I)
  have hVE : V = KI X I ⊓ Q := hVpc.trans (KI_inf_Q_eq_pCoreOf h hxX hgen hord).symm
  have hVcard : Nat.card V = 32 := hVq8.facts.1
  obtain ⟨z, hzZ, -, hz3, hZeq⟩ := exists_Z49_generator hA
  have hzK : z ∈ KI X I := hZK hzZ
  have hVZcard : Nat.card ↥(V ⊓ Subgroup.centralizer (Z49 X A : Set G)) = 8 := by
    rw [hZeq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hz8 z hzK hz3
  obtain ⟨hVT, hTNV, hT2, hZNT, hZNV⟩ := K49_T_setup h hVE hVK hZK
  have hTsup := K49_T_eq_centralizer_sup h hVE hZK hA.2.2.2.2 hT2 hVT hTNV hZNT hZNV
  have hTcard := K49_T_card hVcard hVZcard hVT hTNV hTsup
  have hTZeq : (Q ⊓ Subgroup.centralizer (X : Set G)) ⊓ Subgroup.centralizer (Z49 X A : Set G) =
      Q ⊓ Subgroup.centralizer ((X ⊔ Z49 X A : Subgroup G) : Set G) := by
    rw [centralizer_sup_eq_inf, inf_assoc]
  have hT4 : Nat.card ↥(Q ⊓ Subgroup.centralizer (X : Set G)) =
      4 * Nat.card ↥(Q ⊓ Subgroup.centralizer ((X ⊔ Z49 X A : Subgroup G) : Set G)) := by
    rw [← hTZeq]; exact hTcard
  exact ⟨hT4, K49_card_Q_eq h hA hAI hT4⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
