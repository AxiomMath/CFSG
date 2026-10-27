module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.RootBasic
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentT
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.OddTranspositions.PartThree.Wong.RootData

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] (D : RootData G)

private theorem orderOf_h1 : orderOf D.h1 = 4 := by
  rw [show D.h1 = D.i1 hM from rfl, orderOf_injective D.i1 D.inj1]
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hm0 h
  have hm' : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm' with rfl | rfl | rfl
  exacts [absurd h (by decide), absurd h (by decide), absurd h (by decide)]

private theorem orderOf_h2 : orderOf D.h2 = 4 := by
  rw [show D.h2 = D.i2 hM from rfl, orderOf_injective D.i2 D.inj2]
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hm0 h
  have hm' : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm' with rfl | rfl | rfl
  exacts [absurd h (by decide), absurd h (by decide), absurd h (by decide)]

private theorem h2_not_mem_zpowers_h1 : D.h2 ∉ zpowers D.h1 := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h : D.i1 (hM ^ k) = D.i2 hM := by
    rw [map_zpow]
    exact hk
  have heq : D.i1 (hM ^ k) * D.i2 1 = D.i1 1 * D.i2 hM := by
    simpa using h
  rcases D.prod_eq_iff.mp heq with ⟨-, h2⟩ | ⟨-, h2⟩
  · exact (by decide : hM ≠ 1) h2
  · exact (by decide : hM ≠ -1) h2

private theorem card_zpowers_h1 : Nat.card (zpowers D.h1) = 4 := by
  rw [Nat.card_zpowers, orderOf_h1]

private theorem card_zpowers_h2 : Nat.card (zpowers D.h2) = 4 := by
  rw [Nat.card_zpowers, orderOf_h2]

private theorem card_zpowers_t : Nat.card (zpowers D.t) = 2 := by
  rw [Nat.card_zpowers, D.orderOf_t]

private theorem card_inf_zpowers_h1_h2 [Finite G] :
    Nat.card (zpowers D.h1 ⊓ zpowers D.h2 : Subgroup G) = 2 := by
  have hge : 2 ≤ Nat.card (zpowers D.h1 ⊓ zpowers D.h2 : Subgroup G) := by
    have hle : zpowers D.t ≤ zpowers D.h1 ⊓ zpowers D.h2 := by
      refine le_inf (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · rw [← D.h1_sq]; exact pow_mem (mem_zpowers _) 2
      · rw [← D.h2_sq]; exact pow_mem (mem_zpowers _) 2
    calc 2 = Nat.card (zpowers D.t) := (card_zpowers_t D).symm
      _ ≤ Nat.card (zpowers D.h1 ⊓ zpowers D.h2 : Subgroup G) := Subgroup.card_le_of_le hle
  have hle4 : Nat.card (zpowers D.h1 ⊓ zpowers D.h2 : Subgroup G) ≤ 4 := by
    calc Nat.card (zpowers D.h1 ⊓ zpowers D.h2 : Subgroup G) ≤ Nat.card (zpowers D.h1) :=
          Subgroup.card_le_of_le inf_le_left
      _ = 4 := card_zpowers_h1 D
  have hne4 : Nat.card (zpowers D.h1 ⊓ zpowers D.h2 : Subgroup G) ≠ 4 := by
    intro hc
    have hIeq : zpowers D.h1 ⊓ zpowers D.h2 = zpowers D.h1 :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, card_zpowers_h1 D])
    have hle : zpowers D.h1 ≤ zpowers D.h2 := hIeq.symm ▸ inf_le_right
    have heq : zpowers D.h1 = zpowers D.h2 :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_zpowers_h2 D, card_zpowers_h1 D])
    exact h2_not_mem_zpowers_h1 D (heq ▸ Subgroup.mem_zpowers D.h2)
  have hcases : Nat.card (zpowers D.h1 ⊓ zpowers D.h2 : Subgroup G) = 2 ∨
      Nat.card (zpowers D.h1 ⊓ zpowers D.h2 : Subgroup G) = 3 ∨
      Nat.card (zpowers D.h1 ⊓ zpowers D.h2 : Subgroup G) = 4 := by omega
  rcases hcases with h | h | h
  · exact h
  · have hdvd : Nat.card (zpowers D.h1 ⊓ zpowers D.h2 : Subgroup G) ∣ 4 := by
      rw [← card_zpowers_h1 D]; exact Subgroup.card_dvd_of_le inf_le_left
    rw [h] at hdvd; norm_num at hdvd
  · exact absurd h hne4

private theorem card_H [Finite G] : Nat.card D.H = 8 := by
  have hsup : D.H = zpowers D.h1 ⊔ zpowers D.h2 := by
    rw [show D.H = closure {D.h1, D.h2} from rfl, Set.insert_eq, Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
  have hcent : zpowers D.h2 ≤ centralizer (zpowers D.h1 : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((D.commute hM hM).zpow_left j).zpow_right k |>.eq
  have hN : zpowers D.h2 ≤ Subgroup.normalizer (zpowers D.h1 : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hN
  rw [sup_comm, inf_comm, card_inf_zpowers_h1_h2 D, card_zpowers_h1 D, card_zpowers_h2 D] at h
  rw [hsup]
  omega


private theorem P1_le_i1 : D.P1 ≤ D.i1.range := by
  rintro _ ⟨a, rfl⟩
  exact ⟨thetaHom a, rfl⟩

private theorem P2_le_i2 : D.P2 ≤ D.i2.range := by
  rintro _ ⟨a, rfl⟩
  exact ⟨thetaHom a, rfl⟩

private theorem inf_P1_P2 : D.P1 ⊓ D.P2 = ⊥ := by
  have hle : D.P1 ⊓ D.P2 ≤ zpowers D.t := by
    have h := inf_le_inf (P1_le_i1 D) (P2_le_i2 D)
    rw [D.range_inf] at h
    exact h
  have hdvd1 : Nat.card (D.P1 ⊓ D.P2 : Subgroup G) ∣ 5 := by
    rw [← D.card_P1]; exact Subgroup.card_dvd_of_le inf_le_left
  have hdvd2 : Nat.card (D.P1 ⊓ D.P2 : Subgroup G) ∣ 2 := by
    rw [← card_zpowers_t D]; exact Subgroup.card_dvd_of_le hle
  have hone : Nat.card (D.P1 ⊓ D.P2 : Subgroup G) = 1 :=
    Nat.eq_one_of_dvd_coprimes (by norm_num) hdvd1 hdvd2
  rw [Subgroup.card_eq_one] at hone
  exact hone

private theorem card_R [Finite G] : Nat.card D.R = 25 := by
  have hcent : D.P2 ≤ centralizer (D.P1 : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨a, rfl⟩ := hh
    obtain ⟨b, rfl⟩ := hg
    exact (D.commute_q1_q2 a b).eq
  have hN : D.P2 ≤ Subgroup.normalizer (D.P1 : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hN
  rw [sup_comm, inf_comm, inf_P1_P2 D, D.card_P1, D.card_P2, Subgroup.card_bot, mul_one] at h
  rw [show D.R = D.P1 ⊔ D.P2 from rfl]
  omega

private theorem conj_thetaM_one_eq_or_neg (x : SL5) :
    (thetaM 1 * x = x * thetaM 1 ∨ thetaM 1 * x = -(x * thetaM 1)) →
      ∃ a : ZMod 5, x = thetaM a ∨ x = -thetaM a := by
  revert x
  decide +kernel

private theorem conj_thetaM_one_eq_or_neg' (x : SL5) :
    (x * thetaM 1 = thetaM 1 * x ∨ x * thetaM 1 = -(thetaM 1 * x)) →
      ∃ a : ZMod 5, x = thetaM a ∨ x = -thetaM a := by
  revert x
  decide +kernel

private theorem D1_le_A : D.D1 ≤ D.A := by
  rw [D.D1_eq_range]
  rintro _ ⟨a, rfl⟩
  exact ⟨thetaHom a, rfl⟩

private theorem D1_inf_closure_t_u : D.D1 ⊓ closure {D.t, D.u} = ⊥ := by
  rw [inf_comm]
  refine le_bot_iff.mp ?_
  calc closure {D.t, D.u} ⊓ D.D1 ≤ closure {D.t, D.u} ⊓ D.A :=
        inf_le_inf_left _ (D1_le_A D)
    _ = ⊥ := D.closure_t_u_inf_A

private theorem s_mul_t_mul_s_inv : D.s * D.t * D.s⁻¹ = D.t * D.u := by
  have ht : D.t * D.s * D.t = D.s⁻¹ := by
    have h := D.outer.conj_t
    rwa [D.t_inv] at h
  have hst : D.s * D.t = D.t * D.s⁻¹ := by
    calc D.s * D.t = (D.t * D.t) * (D.s * D.t) := by rw [D.t_mul_t, one_mul]
      _ = D.t * (D.t * D.s * D.t) := by group
      _ = D.t * D.s⁻¹ := by rw [ht]
  have hss : D.s⁻¹ * D.s⁻¹ = D.u := by
    rw [← pow_two, inv_pow, D.outer.sq, inv_eq_of_mul_eq_one_right D.u_mul_u]
  calc D.s * D.t * D.s⁻¹ = D.t * D.s⁻¹ * D.s⁻¹ := by rw [hst]
    _ = D.t * (D.s⁻¹ * D.s⁻¹) := by rw [mul_assoc]
    _ = D.t * D.u := by rw [hss]

private theorem s_mem_normalizer_closure_t_u [Finite G] :
    D.s ∈ normalizer (closure {D.t, D.u} : Set G) := by
  refine mem_normalizer_fintype fun z hz => ?_
  refine Subgroup.closure_induction
    (p := fun z _ => D.s * z * D.s⁻¹ ∈ closure {D.t, D.u}) ?_ ?_ ?_ ?_ hz
  · rintro z (rfl | rfl)
    · rw [s_mul_t_mul_s_inv]
      exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    · have hsu : D.s * D.u * D.s⁻¹ = D.u := by
        rw [← D.outer.sq]
        group
      rw [hsu]
      exact subset_closure (by simp)
  · rw [mul_one, mul_inv_cancel]
    exact one_mem _
  · intro x y hx hy hx' hy'
    have h : D.s * (x * y) * D.s⁻¹ = (D.s * x * D.s⁻¹) * (D.s * y * D.s⁻¹) := by group
    rw [h]
    exact mul_mem hx' hy'
  · intro x hx hx'
    have h : D.s * x⁻¹ * D.s⁻¹ = (D.s * x * D.s⁻¹)⁻¹ := by group
    rw [h]
    exact inv_mem hx'

private theorem closure_s_t_eq_sup : closure {D.s, D.t} = closure {D.t, D.u} ⊔ zpowers D.s := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers D.s)
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  · refine sup_le ?_ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · rw [← D.outer.sq]
      exact pow_mem (Subgroup.subset_closure (by simp)) 2

private theorem mem_closure_s_t_cases [Finite G] {c : G} (hc : c ∈ closure {D.s, D.t}) :
    c ∈ closure {D.t, D.u} ∨ ∃ c' ∈ closure {D.t, D.u}, c = c' * D.s := by
  rw [closure_s_t_eq_sup D] at hc
  have hle : zpowers D.s ≤ normalizer (closure {D.t, D.u} : Set G) :=
    Subgroup.zpowers_le.mpr (s_mem_normalizer_closure_t_u D)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle, Set.mem_mul] at hc
  obtain ⟨k, hkK, z, hz, rfl⟩ := hc
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
  · left
    rw [hm, zpow_mul, show D.s ^ (2:ℤ) = D.u by simpa using D.outer.sq]
    exact mul_mem hkK (zpow_mem (show D.u ∈ closure {D.t, D.u} from
      Subgroup.subset_closure (by simp)) m)
  · refine Or.inr ⟨k * D.u ^ m, ?_, ?_⟩
    · exact mul_mem hkK (zpow_mem (show D.u ∈ closure {D.t, D.u} from
        Subgroup.subset_closure (by simp)) m)
    · rw [hm, zpow_add, zpow_mul, show D.s ^ (2:ℤ) = D.u by simpa using D.outer.sq,
        zpow_one]
      group

private theorem d_thetaM_mem_D1 (a : ZMod 5) : D.d (thetaM a) ∈ D.D1 :=
  subset_closure ⟨a, rfl⟩

private theorem D1_le_centralizer_P1 : D.D1 ≤ centralizer (D.P1 : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨b, rfl⟩
  change D.d (thetaM b) ∈ Subgroup.centralizer (D.P1 : Set G)
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨a, rfl⟩
  rw [D.d_apply]
  exact ((Commute.all _ _).map D.q1).mul_right (D.commute_q1_q2 _ _) |>.eq

private theorem D1_le_centralizer_P2 : D.D1 ≤ centralizer (D.P2 : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨b, rfl⟩
  change D.d (thetaM b) ∈ Subgroup.centralizer (D.P2 : Set G)
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨a, rfl⟩
  rw [D.d_apply]
  exact (D.commute_q1_q2 _ _).symm.mul_right ((Commute.all _ _).map D.q2) |>.eq

private theorem t_mem_centralizer_A : D.t ∈ centralizer (D.A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨x, rfl⟩
  exact (D.d_commute_t x).eq

private theorem u_mem_centralizer_A : D.u ∈ centralizer (D.A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨x, rfl⟩
  exact (D.d_commute_u x).eq

private theorem centralizer_A_le_centralizer_D1 :
    centralizer (D.A : Set G) ≤ centralizer (D.D1 : Set G) :=
  Subgroup.centralizer_le (fun x hx => D1_le_A D hx)

private theorem closure_t_u_le_centralizer_A :
    closure {D.t, D.u} ≤ centralizer (D.A : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x (rfl | rfl)
  · exact t_mem_centralizer_A D
  · exact u_mem_centralizer_A D

private theorem closure_t_u_le_centralizer_D1 :
    closure {D.t, D.u} ≤ centralizer (D.D1 : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x (rfl | rfl)
  · exact centralizer_A_le_centralizer_D1 D (t_mem_centralizer_A D)
  · exact centralizer_A_le_centralizer_D1 D (u_mem_centralizer_A D)

private theorem i1_mem_sup_of_theta {x : SL5}
    (hx : ∃ a : ZMod 5, x = thetaM a ∨ x = -thetaM a) :
    D.i1 x ∈ D.P1 ⊔ zpowers D.t := by
  rcases hx with ⟨a, rfl | rfl⟩
  · exact Subgroup.mem_sup_left ⟨Multiplicative.ofAdd a, rfl⟩
  · rw [D.i1_neg]
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t))
      (Subgroup.mem_sup_left ⟨Multiplicative.ofAdd a, rfl⟩)

private theorem i2_mem_sup_of_theta {x : SL5}
    (hx : ∃ a : ZMod 5, x = thetaM a ∨ x = -thetaM a) :
    D.i2 x ∈ D.P2 ⊔ zpowers D.t := by
  rcases hx with ⟨a, rfl | rfl⟩
  · exact Subgroup.mem_sup_left ⟨Multiplicative.ofAdd a, rfl⟩
  · rw [D.i2_neg]
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t))
      (Subgroup.mem_sup_left ⟨Multiplicative.ofAdd a, rfl⟩)

private theorem P1_sup_zpowers_t_le : D.P1 ⊔ zpowers D.t ≤ D.R ⊔ closure {D.t, D.u} := by
  refine sup_le ?_ ?_
  · exact (le_sup_left : D.P1 ≤ D.P1 ⊔ D.P2).trans le_sup_left
  · exact (Subgroup.zpowers_le.mpr (subset_closure (by simp))).trans le_sup_right

private theorem P2_sup_zpowers_t_le : D.P2 ⊔ zpowers D.t ≤ D.R ⊔ closure {D.t, D.u} := by
  refine sup_le ?_ ?_
  · exact (le_sup_right : D.P2 ≤ D.P1 ⊔ D.P2).trans le_sup_left
  · exact (Subgroup.zpowers_le.mpr (subset_closure (by simp))).trans le_sup_right

private theorem mem_sup_of_mem_centralizer_D1_of_mem_K [Finite G] {g : G}
    (hgD1 : g ∈ centralizer (D.D1 : Set G)) (hgK : g ∈ D.K) :
    g ∈ D.R ⊔ closure {D.t, D.u} := by
  obtain ⟨x, y, rfl⟩ := D.mem_K_iff.mp hgK
  have hcomm : Commute (D.d (thetaM 1)) (D.i1 x * D.i2 y) :=
    mem_centralizer_iff.mp hgD1 (D.d (thetaM 1)) (d_thetaM_mem_D1 D 1)
  have hprod : D.i1 (x * thetaM 1) * D.i2 (y * thetaM 1) =
      D.i1 (thetaM 1 * x) * D.i2 (thetaM 1 * y) := by
    rw [← D.prod_mul_prod, ← D.prod_mul_prod]
    exact hcomm.eq.symm
  rcases D.prod_eq_iff.mp hprod with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact mul_mem
      (P1_sup_zpowers_t_le D
        (i1_mem_sup_of_theta D (conj_thetaM_one_eq_or_neg x (Or.inl hx))))
      (P2_sup_zpowers_t_le D
        (i2_mem_sup_of_theta D (conj_thetaM_one_eq_or_neg y (Or.inl hy))))
  · exact mul_mem
      (P1_sup_zpowers_t_le D
        (i1_mem_sup_of_theta D (conj_thetaM_one_eq_or_neg x (Or.inr hx))))
      (P2_sup_zpowers_t_le D
        (i2_mem_sup_of_theta D (conj_thetaM_one_eq_or_neg y (Or.inr hy))))

private theorem centralizer_D1_inf_centralizer_t [Finite G] :
    centralizer (D.D1 : Set G) ⊓ centralizer {D.t} = D.R ⊔ closure {D.t, D.u} := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgD1, hgt⟩ := Subgroup.mem_inf.mp hg
    rcases D.mem_centralizer_t_iff.mp hgt with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
    · exact mem_sup_of_mem_centralizer_D1_of_mem_K D hgD1 (D.mem_K_iff.mpr ⟨x, y, rfl⟩)
    · have huD1 : D.u ∈ centralizer (D.D1 : Set G) :=
        centralizer_A_le_centralizer_D1 D (u_mem_centralizer_A D)
      have hg' : D.i1 x * D.i2 y ∈ centralizer (D.D1 : Set G) := by
        have h : D.i1 x * D.i2 y = (D.i1 x * D.i2 y * D.u) * D.u := by
          rw [mul_assoc, D.u_mul_u, mul_one]
        rw [h]
        exact mul_mem hgD1 huD1
      have hmem := mem_sup_of_mem_centralizer_D1_of_mem_K D hg' (D.mem_K_iff.mpr ⟨x, y, rfl⟩)
      exact mul_mem hmem (Subgroup.mem_sup_right (subset_closure (by simp)))
  · refine sup_le (le_inf ?_ ?_) (le_inf (closure_t_u_le_centralizer_D1 D) ?_)
    · change D.P1 ⊔ D.P2 ≤ Subgroup.centralizer (D.D1 : Set G)
      exact sup_le (Subgroup.le_centralizer_iff.mp (D1_le_centralizer_P1 D))
        (Subgroup.le_centralizer_iff.mp (D1_le_centralizer_P2 D))
    · change D.P1 ⊔ D.P2 ≤ Subgroup.centralizer {D.t}
      refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr (D.t_commute_i1 (thetaM a.toAdd)).symm.eq
      · rintro _ ⟨a, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr (D.t_commute_i2 (thetaM a.toAdd)).symm.eq
    · refine (Subgroup.closure_le _).mpr ?_
      rintro x (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr D.t_commute_u.eq.symm

private theorem exists_psi_conj (y : SL5) :
    ∃ x' : SL5, psiM * (x' : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      (y : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM := by
  revert y
  decide +kernel

private theorem det_three_not_commute_thetaM_one (M : Matrix (Fin 2) (Fin 2) (ZMod 5)) :
    M.det = 3 → ¬ ((thetaM 1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) * M = M * thetaM 1 ∨
      (thetaM 1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) * M = -(M * thetaM 1)) := by
  revert M
  decide +kernel

private theorem closure_t_u_conj_d {c : G} (hc : c ∈ closure {D.t, D.u}) (y : SL5) :
    c⁻¹ * D.d y * c = D.d y := by
  have hcA : c ∈ centralizer (D.A : Set G) := closure_t_u_le_centralizer_A D hc
  have h := mem_centralizer_iff.mp hcA (D.d y) ⟨y, rfl⟩
  calc c⁻¹ * D.d y * c = c⁻¹ * (D.d y * c) := by rw [mul_assoc]
    _ = c⁻¹ * (c * D.d y) := by rw [h]
    _ = D.d y := by group

private theorem exists_mul_d_of_mem_centralizer_D1_inf_centralizer_u [Finite G] {g : G}
    (hg : g ∈ centralizer (D.D1 : Set G) ⊓ centralizer {D.u}) :
    ∃ x : SL5, ∃ c ∈ closure {D.s, D.t}, g = D.d x * c := by
  obtain ⟨-, hgu⟩ := Subgroup.mem_inf.mp hg
  have hgX : g ∈ D.X := hgu
  rw [D.outer.X_eq] at hgX
  have hB_le_X : closure {D.s, D.t} ≤ D.X := by
    rw [D.outer.X_eq]; exact le_sup_right
  have hB_N : closure {D.s, D.t} ≤ Subgroup.normalizer (D.A : Set G) :=
    hB_le_X.trans D.outer.X_le_normalizer_A
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hB_N,
    Set.mem_mul] at hgX
  obtain ⟨a, ha, c, hc, rfl⟩ := hgX
  obtain ⟨x, rfl⟩ := ha
  exact ⟨x, c, hc, rfl⟩

private theorem conj_d_theta_eq_of_mul_mem_centralizer_D1 {x : SL5} {c : G}
    (hc : c ∈ closure {D.t, D.u})
    (hcomm : Commute (D.d (thetaM 1)) (D.d x * c)) :
    D.d (x * thetaM 1 * x⁻¹) = D.d (thetaM 1) := by
  have hcA : c ∈ centralizer (D.A : Set G) := closure_t_u_le_centralizer_A D hc
  have hcθ : Commute c (D.d (thetaM 1)) :=
    (mem_centralizer_iff.mp hcA _ ⟨thetaM 1, rfl⟩).symm
  have hcθ_conj : c * D.d (thetaM 1) * c⁻¹ = D.d (thetaM 1) := by
    rw [hcθ.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hL : D.d x * c * D.d (thetaM 1) * (D.d x * c)⁻¹ =
      D.d (x * thetaM 1 * x⁻¹) := by
    calc D.d x * c * D.d (thetaM 1) * (D.d x * c)⁻¹
        = D.d x * (c * D.d (thetaM 1) * c⁻¹) * (D.d x)⁻¹ := by group
      _ = D.d x * D.d (thetaM 1) * (D.d x)⁻¹ := by rw [hcθ_conj]
      _ = D.d (x * thetaM 1 * x⁻¹) := by rw [map_mul, map_mul, map_inv]
  have hconj_g : D.d x * c * D.d (thetaM 1) * (D.d x * c)⁻¹ = D.d (thetaM 1) := by
    rw [← hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  rwa [hL] at hconj_g

private theorem thetaM_conj_eq_or_neg_of_d_conj_eq {x : SL5}
    (h : D.d (x * thetaM 1 * x⁻¹) = D.d (thetaM 1)) :
    x * thetaM 1 = thetaM 1 * x ∨ x * thetaM 1 = -(thetaM 1 * x) := by
  have hx1 : x * thetaM 1 * x⁻¹ = thetaM 1 ∨ x * thetaM 1 * x⁻¹ = -thetaM 1 := by
    have hone : D.d ((x * thetaM 1 * x⁻¹) * (thetaM 1)⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    rcases (diag_eq_one_iff D.inj1 D.inj2 D.orderOf_t D.range_inf).mp hone with h' | h'
    · left
      have := congrArg (fun z => z * thetaM 1) h'
      simpa [mul_assoc] using this
    · right
      have := congrArg (fun z => z * thetaM 1) h'
      simpa [mul_assoc] using this
  rcases hx1 with h' | h'
  · left
    have := congrArg (fun z => z * x) h'
    simpa [mul_assoc] using this
  · right
    have := congrArg (fun z => z * x) h'
    simpa [mul_assoc] using this

private theorem d_mem_D1_of_mul_mem_centralizer_D1 {x : SL5} {c : G}
    (hc : c ∈ closure {D.t, D.u})
    (hg : D.d x * c ∈ centralizer (D.D1 : Set G)) : D.d x ∈ D.D1 := by
  have hcomm : Commute (D.d (thetaM 1)) (D.d x * c) :=
    mem_centralizer_iff.mp hg _ (d_thetaM_mem_D1 D 1)
  have hconj := conj_d_theta_eq_of_mul_mem_centralizer_D1 D hc hcomm
  obtain ⟨a, ha⟩ := conj_thetaM_one_eq_or_neg' x
    (thetaM_conj_eq_or_neg_of_d_conj_eq D hconj)
  rcases ha with rfl | rfl
  · exact d_thetaM_mem_D1 D a
  · rw [D.d_neg]
    exact d_thetaM_mem_D1 D a

private theorem conj_s_d_theta_eq_of_mem_centralizer_D1 {x : SL5} {c' : G}
    (hc' : c' ∈ closure {D.t, D.u})
    (hcomm : Commute (D.d (thetaM 1)) (D.d x * (c' * D.s))) :
    D.s⁻¹ * D.d (x⁻¹ * thetaM 1 * x) * D.s = D.d (thetaM 1) := by
  have hconj_g : (D.d x * (c' * D.s))⁻¹ * (D.d (thetaM 1) * (D.d x * (c' * D.s))) =
      D.d (thetaM 1) := by
    rw [hcomm.eq]
    group
  have hL : (D.d x * (c' * D.s))⁻¹ * (D.d (thetaM 1) * (D.d x * (c' * D.s))) =
      D.s⁻¹ * D.d (x⁻¹ * thetaM 1 * x) * D.s := by
    calc (D.d x * (c' * D.s))⁻¹ * (D.d (thetaM 1) * (D.d x * (c' * D.s)))
        = D.s⁻¹ * (c'⁻¹ * ((D.d x)⁻¹ * D.d (thetaM 1) * D.d x) * c') * D.s := by group
      _ = D.s⁻¹ * (c'⁻¹ * D.d (x⁻¹ * thetaM 1 * x) * c') * D.s := by
            rw [show (D.d x)⁻¹ * D.d (thetaM 1) * D.d x = D.d (x⁻¹ * thetaM 1 * x) by
              rw [← map_inv, ← map_mul, ← map_mul]]
      _ = D.s⁻¹ * D.d (x⁻¹ * thetaM 1 * x) * D.s := by
            rw [closure_t_u_conj_d D hc' (x⁻¹ * thetaM 1 * x)]
  rw [← hL]
  exact hconj_g

private theorem psi_conj_matrix {x x' : SL5}
    (hx' : psiM * (x' : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      ((x⁻¹ * thetaM 1 * x : SL5) : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM) :
    ((x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM) *
      (x' : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      (thetaM 1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) *
        ((x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM) := by
  have hxy : x * (x⁻¹ * thetaM 1 * x) = thetaM 1 * x := by group
  have hcoecalc : (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) *
      ((x⁻¹ * thetaM 1 * x : SL5) : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      (thetaM 1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) *
        (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]
    exact congrArg (fun z : SL5 => (z : Matrix (Fin 2) (Fin 2) (ZMod 5))) hxy
  rw [Matrix.mul_assoc]
  rw [hx']
  rw [← Matrix.mul_assoc]
  rw [hcoecalc]
  rw [Matrix.mul_assoc]

private theorem false_of_conj_s_d_theta_eq {x : SL5}
    (h : D.s⁻¹ * D.d (x⁻¹ * thetaM 1 * x) * D.s = D.d (thetaM 1)) : False := by
  obtain ⟨x', hx'⟩ := exists_psi_conj (x⁻¹ * thetaM 1 * x)
  have hpsi := D.outer.psi (x⁻¹ * thetaM 1 * x) x' hx'
  have hdx' : D.d x' = D.d (thetaM 1) := by
    rw [← hpsi, h]
  have hx'sign : x' = thetaM 1 ∨ x' = -thetaM 1 := by
    have hone : D.d (x' * (thetaM 1)⁻¹) = 1 := by
      rw [map_mul, map_inv, hdx', mul_inv_cancel]
    rcases (diag_eq_one_iff D.inj1 D.inj2 D.orderOf_t D.range_inf).mp hone with h' | h'
    · left
      have := congrArg (fun z => z * thetaM 1) h'
      simpa using this
    · right
      have := congrArg (fun z => z * thetaM 1) h'
      simpa using this
  have hMx' := psi_conj_matrix hx'
  let M : Matrix (Fin 2) (Fin 2) (ZMod 5) :=
    (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM
  have hcond : (thetaM 1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) * M =
      M * thetaM 1 ∨
      (thetaM 1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) * M = -(M * thetaM 1) := by
    rcases hx'sign with h' | h'
    · left
      rw [h'] at hMx'
      exact hMx'.symm
    · right
      rw [h'] at hMx'
      rw [show ((-thetaM 1 : SL5) : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
        -(thetaM 1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) by
          rw [Matrix.SpecialLinearGroup.coe_neg]] at hMx'
      rw [mul_neg] at hMx'
      exact hMx'.symm
  have hdet : (((x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM)).det = 3 := by
    rw [Matrix.det_mul, show (x : Matrix (Fin 2) (Fin 2) (ZMod 5)).det = 1 from x.2,
      one_mul]
    decide
  exact absurd hcond (det_three_not_commute_thetaM_one _ hdet)

private theorem sup_D1_closure_t_u_le_centralizer_D1_inf_centralizer_u [Finite G] :
    D.D1 ⊔ closure {D.t, D.u} ≤ centralizer (D.D1 : Set G) ⊓ centralizer {D.u} := by
  refine sup_le (le_inf ?_ ?_) (le_inf (closure_t_u_le_centralizer_D1 D) ?_)
  · rw [D.D1_eq_range]
    haveI : IsMulCommutative (Multiplicative (ZMod 5)) :=
      IsMulCommutative.of_comm (fun a b => mul_comm a b)
    exact Subgroup.le_centralizer _
  · intro z hz
    rw [D.D1_eq_range] at hz
    obtain ⟨a, rfl⟩ := hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr (D.d_commute_u (thetaM a)).eq
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr D.t_commute_u.eq
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl

private theorem centralizer_D1_inf_centralizer_u [Finite G] :
    centralizer (D.D1 : Set G) ⊓ centralizer {D.u} = D.D1 ⊔ closure {D.t, D.u} := by
  refine le_antisymm ?_ (sup_D1_closure_t_u_le_centralizer_D1_inf_centralizer_u D)
  intro g hg
  obtain ⟨x, c, hc, rfl⟩ := exists_mul_d_of_mem_centralizer_D1_inf_centralizer_u D hg
  have hgD1 : D.d x * c ∈ centralizer (D.D1 : Set G) := hg.1
  have hcomm : Commute (D.d (thetaM 1)) (D.d x * c) :=
    mem_centralizer_iff.mp hgD1 _ (d_thetaM_mem_D1 D 1)
  rcases mem_closure_s_t_cases D hc with hcK | ⟨c', hc'K, rfl⟩
  · exact mul_mem (Subgroup.mem_sup_left (d_mem_D1_of_mul_mem_centralizer_D1 D hcK hgD1))
      (Subgroup.mem_sup_right hcK)
  · exact (false_of_conj_s_d_theta_eq D
      (conj_s_d_theta_eq_of_mem_centralizer_D1 D hc'K hcomm)).elim

private theorem map_conj_centralizer (c x : G) :
    (centralizer {x}).map (MulAut.conj c).toMonoidHom = centralizer {c * x * c⁻¹} := by
  ext g
  simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨k, hk, rfl⟩
    calc c * k * c⁻¹ * (c * x * c⁻¹) = c * (k * x) * c⁻¹ := by group
      _ = c * (x * k) * c⁻¹ := by rw [hk]
      _ = c * x * c⁻¹ * (c * k * c⁻¹) := by group
  · intro hg
    refine ⟨c⁻¹ * g * c, ?_, by group⟩
    calc c⁻¹ * g * c * x = c⁻¹ * (g * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * x * c⁻¹ * g) * c := by rw [hg]
      _ = x * (c⁻¹ * g * c) := by group

private theorem y_inv_conj_t : D.y⁻¹ * D.t * D.y = D.t * D.u := by
  simpa only [RootData.y] using D.outer.y_conj_t

private theorem y_conj_tu : D.y * (D.t * D.u) * D.y⁻¹ = D.t := by
  calc D.y * (D.t * D.u) * D.y⁻¹ = D.y * (D.y⁻¹ * D.t * D.y) * D.y⁻¹ := by
        rw [y_inv_conj_t D]
    _ = D.t := by group

private theorem y_inv_conj_u : D.y⁻¹ * D.u * D.y = D.u := by
  have hcomm : D.y * D.u = D.u * D.y := D.y_commute_u.eq
  calc D.y⁻¹ * D.u * D.y = D.y⁻¹ * (D.u * D.y) := by rw [mul_assoc]
    _ = D.y⁻¹ * (D.y * D.u) := by rw [← hcomm]
    _ = D.u := by group

private theorem map_closure_t_u_y [Finite G] :
    (closure {D.t, D.u}).map (MulAut.conj D.y⁻¹).toMonoidHom = closure {D.t, D.u} := by
  have hle : (closure {D.t, D.u}).map (MulAut.conj D.y⁻¹).toMonoidHom ≤
      closure {D.t, D.u} := by
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨w, (rfl | rfl), rfl⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [y_inv_conj_t D]
      exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [y_inv_conj_u D]
      exact subset_closure (by simp)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj D.y⁻¹).injective]

private theorem map_centralizer_D1_y :
    (centralizer (D.D1 : Set G)).map (MulAut.conj D.y⁻¹).toMonoidHom =
      centralizer (D.D1 : Set G) := by
  apply le_antisymm
  · rintro z ⟨r, hr, rfl⟩
    change r ∈ Subgroup.centralizer (D.D1 : Set G) at hr
    rw [Subgroup.mem_centralizer_iff] at hr ⊢
    intro d hd
    have hd' : D.y * d * D.y⁻¹ ∈ D.D1 :=
      (Subgroup.mem_normalizer_iff.mp D.outer.y_mem_normalizer d).mp hd
    have hrm := hr (D.y * d * D.y⁻¹) hd'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc d * (D.y⁻¹ * r * D.y) = D.y⁻¹ * ((D.y * d * D.y⁻¹) * r) * D.y := by group
      _ = D.y⁻¹ * (r * (D.y * d * D.y⁻¹)) * D.y := by rw [← hrm]
      _ = D.y⁻¹ * r * D.y * d := by group
  · intro z hz
    refine ⟨(MulAut.conj D.y) z, ?_, ?_⟩
    · change (MulAut.conj D.y) z ∈ Subgroup.centralizer (D.D1 : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hd' : D.y⁻¹ * d * D.y ∈ D.D1 := by
        have h := Subgroup.mem_map_of_mem (MulAut.conj D.y⁻¹).toMonoidHom hd
        rw [D.map_D1_y] at h
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using h
      have hz' := (Subgroup.mem_centralizer_iff.mp hz) (D.y⁻¹ * d * D.y) hd'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc d * (D.y * z * D.y⁻¹) = D.y * ((D.y⁻¹ * d * D.y) * z) * D.y⁻¹ := by group
        _ = D.y * (z * (D.y⁻¹ * d * D.y)) * D.y⁻¹ := by rw [← hz']
        _ = D.y * z * D.y⁻¹ * d := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group

private theorem centralizer_D1_inf_centralizer_tu [Finite G] :
    centralizer (D.D1 : Set G) ⊓ centralizer {D.t * D.u} =
      D.R.map (MulAut.conj D.y⁻¹).toMonoidHom ⊔ closure {D.t, D.u} := by
  have hmain : (centralizer (D.D1 : Set G) ⊓ centralizer {D.t}).map
      (MulAut.conj D.y⁻¹).toMonoidHom =
      centralizer (D.D1 : Set G) ⊓ centralizer {D.t * D.u} := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj D.y⁻¹).injective, map_centralizer_D1_y]
    have hy : D.y⁻¹ * D.t * (D.y⁻¹)⁻¹ = D.t * D.u := by
      rw [inv_inv]
      exact y_inv_conj_t D
    rw [map_conj_centralizer, hy]
  rw [← hmain, centralizer_D1_inf_centralizer_t D, Subgroup.map_sup, map_closure_t_u_y]

private theorem P1_eq_map : D.P1 = thetaHom.range.map D.i1 := by
  show (D.i1.comp thetaHom).range = thetaHom.range.map D.i1
  exact MonoidHom.range_comp D.i1 thetaHom

private theorem P2_eq_map : D.P2 = thetaHom.range.map D.i2 := by
  show (D.i2.comp thetaHom).range = thetaHom.range.map D.i2
  exact MonoidHom.range_comp D.i2 thetaHom


private theorem P2_le_normalizer_P1 : D.P2 ≤ Subgroup.normalizer (D.P1 : Set G) := by
  have hcent : D.P2 ≤ centralizer (D.P1 : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨a, rfl⟩ := hh
    obtain ⟨b, rfl⟩ := hg
    exact (D.commute_q1_q2 a b).eq
  exact hcent.trans (Subgroup.centralizer_le_normalizer _)

private theorem R_inf_i1_range : D.R ⊓ D.i1.range = D.P1 := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgR, hgL1⟩ := Subgroup.mem_inf.mp hg
    rw [show D.R = D.P1 ⊔ D.P2 from rfl] at hgR
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (P2_le_normalizer_P1 D), Set.mem_mul] at hgR
    obtain ⟨p1, hp1, p2, hp2, rfl⟩ := hgR
    have hp1L1 : p1 ∈ D.i1.range := P1_le_i1 D hp1
    have hp2L1 : p2 ∈ D.i1.range := by
      have : p2 = p1⁻¹ * (p1 * p2) := by group
      rw [this]
      exact mul_mem (inv_mem hp1L1) hgL1
    have hp2_inf : p2 ∈ D.P2 ⊓ zpowers D.t := by
      refine mem_inf.mpr ⟨hp2, ?_⟩
      have h2 : p2 ∈ D.i1.range ⊓ D.i2.range :=
        mem_inf.mpr ⟨hp2L1, P2_le_i2 D hp2⟩
      rwa [D.range_inf] at h2
    have hbot : D.P2 ⊓ zpowers D.t = ⊥ := by
      apply Subgroup.inf_eq_bot_of_coprime
      rw [D.card_P2, show Nat.card (zpowers D.t) = 2 by rw [Nat.card_zpowers, D.orderOf_t]]
      norm_num
    rw [hbot] at hp2_inf
    have hp2one : p2 = 1 := by simpa using hp2_inf
    simpa [hp2one] using hp1
  · intro g hg
    exact mem_inf.mpr ⟨Subgroup.mem_sup_left hg, P1_le_i1 D hg⟩

private theorem R_inf_i2_range : D.R ⊓ D.i2.range = D.P2 := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgR, hgL2⟩ := Subgroup.mem_inf.mp hg
    rw [show D.R = D.P1 ⊔ D.P2 from rfl, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ (P2_le_normalizer_P1 D),
      Set.mem_mul] at hgR
    obtain ⟨p1, hp1, p2, hp2, rfl⟩ := hgR
    have hp2L2 : p2 ∈ D.i2.range := P2_le_i2 D hp2
    have hp1L2 : p1 ∈ D.i2.range := by
      have : p1 = (p1 * p2) * p2⁻¹ := by group
      rw [this]
      exact mul_mem hgL2 (inv_mem hp2L2)
    have hp1_inf : p1 ∈ D.P1 ⊓ zpowers D.t := by
      refine mem_inf.mpr ⟨hp1, ?_⟩
      have h2 : p1 ∈ D.i1.range ⊓ D.i2.range :=
        mem_inf.mpr ⟨P1_le_i1 D hp1, hp1L2⟩
      rwa [D.range_inf] at h2
    have hbot : D.P1 ⊓ zpowers D.t = ⊥ := by
      apply Subgroup.inf_eq_bot_of_coprime
      rw [D.card_P1, show Nat.card (zpowers D.t) = 2 by rw [Nat.card_zpowers, D.orderOf_t]]
      norm_num
    rw [hbot] at hp1_inf
    have hp1one : p1 = 1 := by simpa using hp1_inf
    simpa [hp1one] using hp2
  · intro g hg
    exact mem_inf.mpr ⟨Subgroup.mem_sup_right hg, P2_le_i2 D hg⟩

private theorem normalizer_thetaM_range (x : SL5) :
    (∀ a : ZMod 5, ∃ b : ZMod 5, x * thetaM a * x⁻¹ = thetaM b) ↔
      ∃ a : ZMod 5, ∃ k : Fin 4, x = thetaM a * hM ^ (k : ℕ) := by
  revert x
  decide +kernel

private theorem normalizer_thetaM_range_of_mem {x : SL5}
    (hx : x ∈ Subgroup.normalizer (thetaHom.range : Set SL5)) :
    ∀ a : ZMod 5, ∃ b : ZMod 5, x * thetaM a * x⁻¹ = thetaM b := by
  intro a
  have ha : thetaM a ∈ thetaHom.range := ⟨Multiplicative.ofAdd a, rfl⟩
  obtain ⟨b, hb⟩ := (Subgroup.mem_normalizer_iff.mp hx (thetaM a)).mp ha
  exact ⟨b.toAdd, hb.symm⟩

private theorem i1_mem_sup_of_mem_normalizer [Finite G] {x : SL5}
    (hx : x ∈ Subgroup.normalizer (thetaHom.range : Set SL5)) :
    D.i1 x ∈ D.P1 ⊔ D.H := by
  obtain ⟨a, k, rfl⟩ := (normalizer_thetaM_range x).mp (normalizer_thetaM_range_of_mem hx)
  rw [map_mul, map_pow]
  have hh1 : D.h1 ∈ ({D.h1, D.h2} : Set G) := Set.mem_insert_iff.mpr (Or.inl rfl)
  refine mul_mem (Subgroup.mem_sup_left ⟨Multiplicative.ofAdd a, rfl⟩) ?_
  refine Subgroup.mem_sup_right ?_
  change D.i1 hM ^ (k : ℕ) ∈ closure {D.h1, D.h2}
  exact pow_mem (subset_closure hh1) (k : ℕ)

private theorem i2_mem_sup_of_mem_normalizer [Finite G] {x : SL5}
    (hx : x ∈ Subgroup.normalizer (thetaHom.range : Set SL5)) :
    D.i2 x ∈ D.P2 ⊔ D.H := by
  obtain ⟨a, k, rfl⟩ := (normalizer_thetaM_range x).mp (normalizer_thetaM_range_of_mem hx)
  rw [map_mul, map_pow]
  have hh2 : D.h2 ∈ ({D.h1, D.h2} : Set G) :=
    Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
  refine mul_mem (Subgroup.mem_sup_left ⟨Multiplicative.ofAdd a, rfl⟩) ?_
  refine Subgroup.mem_sup_right ?_
  change D.i2 hM ^ (k : ℕ) ∈ closure {D.h1, D.h2}
  exact pow_mem (subset_closure hh2) (k : ℕ)

private theorem i1_mem_normalizer_thetaHom_of_mem_normalizer_R [Finite G] {x y : SL5}
    (hgN : D.i1 x * D.i2 y ∈ normalizer (D.R : Set G)) :
    x ∈ Subgroup.normalizer (thetaHom.range : Set SL5) := by
  refine Subgroup.mem_normalizer_fintype fun u hu => ?_
  have huP1 : D.i1 u ∈ D.P1 := by
    rw [P1_eq_map D]
    exact Subgroup.mem_map_of_mem _ hu
  have hconj : (D.i1 x * D.i2 y) * D.i1 u * (D.i1 x * D.i2 y)⁻¹ =
      D.i1 (x * u * x⁻¹) := by
    rw [D.prod_inv]
    calc D.i1 x * D.i2 y * D.i1 u * (D.i1 x⁻¹ * D.i2 y⁻¹)
        = D.i1 (x * u) * D.i2 y * (D.i1 x⁻¹ * D.i2 y⁻¹) := by
            rw [show D.i1 u = D.i1 u * D.i2 1 by rw [map_one, mul_one],
              D.prod_mul_prod]
            simp only [map_one, mul_one]
      _ = D.i1 ((x * u) * x⁻¹) * D.i2 (y * y⁻¹) := by rw [D.prod_mul_prod]
      _ = D.i1 (x * u * x⁻¹) := by rw [mul_inv_cancel, map_one, mul_one]
  have hmemR : D.i1 (x * u * x⁻¹) ∈ D.R := by
    rw [← hconj]
    exact (Subgroup.mem_normalizer_iff.mp hgN (D.i1 u)).mp (Subgroup.mem_sup_left huP1)
  have hmemL1 : D.i1 (x * u * x⁻¹) ∈ D.i1.range := ⟨x * u * x⁻¹, rfl⟩
  have hmemP1 : D.i1 (x * u * x⁻¹) ∈ D.P1 := by
    rw [← R_inf_i1_range D]
    exact Subgroup.mem_inf.mpr ⟨hmemR, hmemL1⟩
  rw [P1_eq_map D] at hmemP1
  obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp hmemP1
  have : w = x * u * x⁻¹ := D.inj1 hw'
  rwa [this] at hw

private theorem i2_mem_normalizer_thetaHom_of_mem_normalizer_R [Finite G] {x y : SL5}
    (hgN : D.i1 x * D.i2 y ∈ normalizer (D.R : Set G)) :
    y ∈ Subgroup.normalizer (thetaHom.range : Set SL5) := by
  refine Subgroup.mem_normalizer_fintype fun u hu => ?_
  have huP2 : D.i2 u ∈ D.P2 := by
    rw [P2_eq_map D]
    exact Subgroup.mem_map_of_mem _ hu
  have hconj : (D.i1 x * D.i2 y) * D.i2 u * (D.i1 x * D.i2 y)⁻¹ =
      D.i2 (y * u * y⁻¹) := by
    rw [D.prod_inv]
    calc D.i1 x * D.i2 y * D.i2 u * (D.i1 x⁻¹ * D.i2 y⁻¹)
        = D.i1 x * D.i2 (y * u) * (D.i1 x⁻¹ * D.i2 y⁻¹) := by
            rw [show D.i2 u = D.i1 1 * D.i2 u by rw [map_one, one_mul],
              D.prod_mul_prod]
            simp only [mul_one]
      _ = D.i1 (x * x⁻¹) * D.i2 ((y * u) * y⁻¹) := by rw [D.prod_mul_prod]
      _ = D.i2 (y * u * y⁻¹) := by rw [mul_inv_cancel, map_one, one_mul]
  have hmemR : D.i2 (y * u * y⁻¹) ∈ D.R := by
    rw [← hconj]
    exact (Subgroup.mem_normalizer_iff.mp hgN (D.i2 u)).mp (Subgroup.mem_sup_right huP2)
  have hmemL2 : D.i2 (y * u * y⁻¹) ∈ D.i2.range := ⟨y * u * y⁻¹, rfl⟩
  have hmemP2 : D.i2 (y * u * y⁻¹) ∈ D.P2 := by
    rw [← R_inf_i2_range D]
    exact Subgroup.mem_inf.mpr ⟨hmemR, hmemL2⟩
  rw [P2_eq_map D] at hmemP2
  obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp hmemP2
  have : w = y * u * y⁻¹ := D.inj2 hw'
  rwa [this] at hw

private theorem mem_R_sup_H_of_mem_K_of_mem_normalizer_R [Finite G] {g : G}
    (hgK : g ∈ D.K) (hgN : g ∈ normalizer (D.R : Set G)) : g ∈ D.R ⊔ D.H := by
  obtain ⟨x, y, rfl⟩ := D.mem_K_iff.mp hgK
  have hxN := i1_mem_normalizer_thetaHom_of_mem_normalizer_R D hgN
  have hyN := i2_mem_normalizer_thetaHom_of_mem_normalizer_R D hgN
  have hxR : D.i1 x ∈ D.R ⊔ D.H :=
    (sup_le_sup (show D.P1 ≤ D.R from le_sup_left) le_rfl)
      (i1_mem_sup_of_mem_normalizer D hxN)
  have hyR : D.i2 y ∈ D.R ⊔ D.H :=
    (sup_le_sup (show D.P2 ≤ D.R from le_sup_right) le_rfl)
      (i2_mem_sup_of_mem_normalizer D hyN)
  exact mul_mem hxR hyR

private theorem h1_inv_mem_normalizer_P1 [Finite G] :
    D.h1⁻¹ ∈ Subgroup.normalizer (D.P1 : Set G) := by
  refine Subgroup.mem_normalizer_fintype ?_
  rintro _ ⟨a, rfl⟩
  refine ⟨Multiplicative.ofAdd (4 * a.toAdd), ?_⟩
  simpa [inv_inv] using (D.h1_conj_q1 a.toAdd).symm

private theorem h2_inv_mem_normalizer_P1 [Finite G] :
    D.h2⁻¹ ∈ Subgroup.normalizer (D.P1 : Set G) := by
  refine Subgroup.mem_normalizer_fintype ?_
  rintro _ ⟨a, rfl⟩
  refine ⟨a, ?_⟩
  simpa [inv_inv] using (D.h2_conj_q1 a).symm

private theorem h1_inv_mem_normalizer_P2 [Finite G] :
    D.h1⁻¹ ∈ Subgroup.normalizer (D.P2 : Set G) := by
  refine Subgroup.mem_normalizer_fintype ?_
  rintro _ ⟨a, rfl⟩
  refine ⟨a, ?_⟩
  simpa [inv_inv] using (D.h1_conj_q2 a).symm

private theorem h2_inv_mem_normalizer_P2 [Finite G] :
    D.h2⁻¹ ∈ Subgroup.normalizer (D.P2 : Set G) := by
  refine Subgroup.mem_normalizer_fintype ?_
  rintro _ ⟨a, rfl⟩
  refine ⟨Multiplicative.ofAdd (4 * a.toAdd), ?_⟩
  simpa [inv_inv] using (D.h2_conj_q2 a.toAdd).symm

private theorem h1_mem_normalizer_R [Finite G] :
    D.h1 ∈ Subgroup.normalizer (D.R : Set G) := by
  have h1 : Subgroup.map (↑(MulAut.conj D.h1)) D.P1 = D.P1 := by
    have := Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem (h1_inv_mem_normalizer_P1 D))
    simpa only [inv_inv] using this
  have h2 : Subgroup.map (↑(MulAut.conj D.h1)) D.P2 = D.P2 := by
    have := Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem (h1_inv_mem_normalizer_P2 D))
    simpa only [inv_inv] using this
  rw [show D.R = D.P1 ⊔ D.P2 from rfl]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, h1, h2]

private theorem h2_mem_normalizer_R [Finite G] :
    D.h2 ∈ Subgroup.normalizer (D.R : Set G) := by
  have h1 : Subgroup.map (↑(MulAut.conj D.h2)) D.P1 = D.P1 := by
    have := Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem (h2_inv_mem_normalizer_P1 D))
    simpa only [inv_inv] using this
  have h2 : Subgroup.map (↑(MulAut.conj D.h2)) D.P2 = D.P2 := by
    have := Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem (h2_inv_mem_normalizer_P2 D))
    simpa only [inv_inv] using this
  rw [show D.R = D.P1 ⊔ D.P2 from rfl]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, h1, h2]

private theorem H_le_normalizer_R [Finite G] :
    D.H ≤ Subgroup.normalizer (D.R : Set G) := by
  change closure {D.h1, D.h2} ≤ Subgroup.normalizer (D.R : Set G)
  refine (Subgroup.closure_le _).mpr ?_
  rintro x (rfl | rfl)
  · exact h1_mem_normalizer_R D
  · exact h2_mem_normalizer_R D

private theorem H_le_centralizer_t :
    D.H ≤ centralizer {D.t} := by
  change closure {D.h1, D.h2} ≤ Subgroup.centralizer {D.t}
  refine (Subgroup.closure_le _).mpr ?_
  rintro x (rfl | rfl)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (D.t_commute_i1 hM).symm.eq
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (D.t_commute_i2 hM).symm.eq

private theorem map_P1_u : D.P1.map (↑(MulAut.conj D.u)) = D.P2 := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨a, rfl⟩ := hw
    have h := D.u_conj_q1 a
    rw [D.u_inv] at h
    refine ⟨a, ?_⟩
    show D.q2 a = D.u * D.q1 a * D.u⁻¹
    rw [D.u_inv]
    exact h.symm
  · rintro ⟨a, rfl⟩
    refine ⟨D.q1 a, ⟨a, rfl⟩, ?_⟩
    have h := D.u_conj_q1 a
    rw [D.u_inv] at h
    show D.u * D.q1 a * D.u⁻¹ = D.q2 a
    rw [D.u_inv]
    exact h

private theorem map_P2_u : D.P2.map (↑(MulAut.conj D.u)) = D.P1 := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨a, rfl⟩ := hw
    have h := D.u_conj_q2 a
    rw [D.u_inv] at h
    refine ⟨a, ?_⟩
    show D.q1 a = D.u * D.q2 a * D.u⁻¹
    rw [D.u_inv]
    exact h.symm
  · rintro ⟨a, rfl⟩
    refine ⟨D.q2 a, ⟨a, rfl⟩, ?_⟩
    have h := D.u_conj_q2 a
    rw [D.u_inv] at h
    show D.u * D.q2 a * D.u⁻¹ = D.q1 a
    rw [D.u_inv]
    exact h

private theorem u_mem_normalizer_R :
    D.u ∈ Subgroup.normalizer (D.R : Set G) := by
  have h1 : Subgroup.map (↑(MulAut.conj D.u)) D.P1 = D.P2 := map_P1_u D
  have h2 : Subgroup.map (↑(MulAut.conj D.u)) D.P2 = D.P1 := map_P2_u D
  rw [show D.R = D.P1 ⊔ D.P2 from rfl, Subgroup.mem_normalizer_iff_map_conj_eq,
    Subgroup.map_sup, h1, h2, sup_comm]

private theorem normalizer_R_inf_centralizer_t [Finite G] :
    normalizer (D.R : Set G) ⊓ centralizer {D.t} = D.R ⊔ D.H ⊔ zpowers D.u := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgN, hgt⟩ := Subgroup.mem_inf.mp hg
    rcases D.mem_centralizer_t_iff.mp hgt with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
    · exact (le_sup_left : D.R ⊔ D.H ≤ D.R ⊔ D.H ⊔ zpowers D.u)
        (mem_R_sup_H_of_mem_K_of_mem_normalizer_R D (D.mem_K_iff.mpr ⟨x, y, rfl⟩) hgN)
    · have huN : D.u ∈ Subgroup.normalizer (D.R : Set G) := u_mem_normalizer_R D
      have hmemN : D.i1 x * D.i2 y ∈ Subgroup.normalizer (D.R : Set G) := by
        have h := mul_mem hgN huN
        rwa [mul_assoc, D.u_mul_u, mul_one] at h
      have hmem : D.i1 x * D.i2 y ∈ D.R ⊔ D.H :=
        mem_R_sup_H_of_mem_K_of_mem_normalizer_R D (D.mem_K_iff.mpr ⟨x, y, rfl⟩) hmemN
      exact mul_mem ((le_sup_left : D.R ⊔ D.H ≤ D.R ⊔ D.H ⊔ zpowers D.u) hmem)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.u))
  · refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
    · refine le_inf (sup_le Subgroup.le_normalizer (H_le_normalizer_R D)) ?_
      refine sup_le ?_ (H_le_centralizer_t D)
      change D.P1 ⊔ D.P2 ≤ Subgroup.centralizer {D.t}
      refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr (D.t_commute_i1 (thetaM a.toAdd)).symm.eq
      · rintro _ ⟨a, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr (D.t_commute_i2 (thetaM a.toAdd)).symm.eq
    · refine Subgroup.mem_inf.mpr ⟨u_mem_normalizer_R D, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr D.t_commute_u.symm.eq

private theorem R_le_centralizer_t : D.R ≤ centralizer {D.t} := by
  change D.P1 ⊔ D.P2 ≤ Subgroup.centralizer {D.t}
  refine sup_le ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (D.t_commute_i1 (thetaM a.toAdd)).symm.eq
  · rintro _ ⟨a, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (D.t_commute_i2 (thetaM a.toAdd)).symm.eq

private theorem centralizer_t_inf_t_mul_u :
    centralizer {D.t} ⊓ centralizer {D.t * D.u} = centralizer {D.t} ⊓ centralizer {D.u} := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have hu : Commute g D.u := by
      have h := (Commute.inv_right h1).mul_right h2
      rwa [show D.t⁻¹ * (D.t * D.u) = D.u by group] at h
    exact hu.eq
  · rintro ⟨h1, hu⟩
    exact ⟨h1, Commute.mul_right h1 hu⟩

private theorem map_R_le_centralizer_tu :
    D.R.map (MulAut.conj D.y⁻¹).toMonoidHom ≤ centralizer {D.t * D.u} := by
  intro z hz
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hr' := Subgroup.mem_centralizer_singleton_iff.mp (R_le_centralizer_t D hr)
  calc D.y⁻¹ * r * D.y * (D.t * D.u)
      = D.y⁻¹ * (r * (D.y * (D.t * D.u) * D.y⁻¹)) * D.y := by group
    _ = D.y⁻¹ * (r * D.t) * D.y := by rw [y_conj_tu D]
    _ = D.y⁻¹ * (D.t * r) * D.y := by rw [hr']
    _ = (D.y⁻¹ * D.t * D.y) * (D.y⁻¹ * r * D.y) := by group
    _ = (D.t * D.u) * (D.y⁻¹ * r * D.y) := by rw [y_inv_conj_t D]

private theorem D1_le_R : D.D1 ≤ D.R := by
  rw [D.D1_eq_range]
  rintro _ ⟨a, rfl⟩
  change D.q1 a * D.q2 a ∈ D.P1 ⊔ D.P2
  exact mul_mem (Subgroup.mem_sup_left ⟨a, rfl⟩) (Subgroup.mem_sup_right ⟨a, rfl⟩)

private theorem D1_le_map_R_y : D.D1 ≤ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom := by
  rw [← D.map_D1_y]
  exact Subgroup.map_mono (D1_le_R D)

private theorem card_R_inf_map_R_y_bounds [Finite G] :
    5 ≤ Nat.card (D.R ⊓ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom : Subgroup G) ∧
      Nat.card (D.R ⊓ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom : Subgroup G) ∣ 25 := by
  constructor
  · calc 5 = Nat.card D.D1 := D.card_D1.symm
      _ ≤ Nat.card (D.R ⊓ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom : Subgroup G) :=
          Subgroup.card_le_of_le (le_inf (D1_le_R D) (D1_le_map_R_y D))
  · rw [← card_R D]
    exact Subgroup.card_dvd_of_le inf_le_left

private theorem false_of_R_le_map_R_y [Finite G]
    (h : D.R ≤ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom) : False := by
  have hR_Ctu : D.R ≤ centralizer {D.t * D.u} :=
    h.trans (map_R_le_centralizer_tu D)
  have hR_Cu : D.R ≤ centralizer {D.u} := by
    intro r hr
    have h1 : r ∈ centralizer {D.t} := R_le_centralizer_t D hr
    have h2 : r ∈ centralizer {D.t * D.u} := hR_Ctu hr
    have hmem : r ∈ centralizer {D.t} ⊓ centralizer {D.t * D.u} := mem_inf.mpr ⟨h1, h2⟩
    rw [centralizer_t_inf_t_mul_u D] at hmem
    exact hmem.2
  have hP1_Cu : D.P1 ≤ centralizer {D.u} := fun p hp => hR_Cu (Subgroup.mem_sup_left hp)
  let a : Multiplicative (ZMod 5) := Multiplicative.ofAdd 1
  have ha1 : a ≠ 1 := by decide
  have hq1Cu : D.q1 a ∈ centralizer {D.u} := hP1_Cu ⟨a, rfl⟩
  have hcomm : D.q1 a * D.u = D.u * D.q1 a :=
    Subgroup.mem_centralizer_singleton_iff.mp hq1Cu
  have hq2 : D.q2 a = D.q1 a := by
    have h := D.u_conj_q1 a
    rw [D.u_inv] at h
    rw [← h, ← hcomm, mul_assoc, D.u_mul_u, mul_one]
  have hmem : D.q1 a ∈ D.P1 ⊓ D.P2 :=
    mem_inf.mpr ⟨⟨a, rfl⟩, by rw [← hq2]; exact ⟨a, rfl⟩⟩
  rw [inf_P1_P2 D] at hmem
  exact (D.q1_injective.ne ha1) (by simpa using hmem)

private theorem R_inf_map_D1 [Finite G] :
    D.R ⊓ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom = D.D1 := by
  obtain ⟨hge, hdvd⟩ := card_R_inf_map_R_y_bounds D
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp (show
    Nat.card (D.R ⊓ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom : Subgroup G) ∣ 5 ^ 2 by
      rw [show (5:ℕ) ^ 2 = 25 by norm_num]
      exact hdvd)
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk3 with rfl | rfl | rfl
  · exfalso
    rw [hk, pow_zero] at hge
    exact absurd hge (by norm_num)
  · exact (Subgroup.eq_of_le_of_card_ge (le_inf (D1_le_R D) (D1_le_map_R_y D))
      (by rw [hk, D.card_D1]; norm_num)).symm
  · exfalso
    have hIeqR : D.R ⊓ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom = D.R :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk]; rw [card_R D]; norm_num)
    have hR_le_Ry : D.R ≤ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom := by
      have h : D.R ⊓ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom ≤
          D.R.map (MulAut.conj D.y⁻¹).toMonoidHom := inf_le_right
      rw [hIeqR] at h
      exact h
    exact false_of_R_le_map_R_y D hR_le_Ry

theorem diagonal_unipotent_local_data [Finite G] :
    Nat.card D.P1 = 5 ∧ Nat.card D.P2 = 5 ∧ Nat.card D.D1 = 5 ∧ Nat.card D.D2 = 5 ∧
    Nat.card D.R = 25 ∧ Nat.card D.H = 8 ∧
    D.R ⊓ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom = D.D1 ∧
    D.D1 ⊓ closure {D.t, D.u} = ⊥ ∧
    centralizer (D.D1 : Set G) ⊓ centralizer {D.u} = D.D1 ⊔ closure {D.t, D.u} ∧
    centralizer (D.D1 : Set G) ⊓ centralizer {D.t} = D.R ⊔ closure {D.t, D.u} ∧
    centralizer (D.D1 : Set G) ⊓ centralizer {D.t * D.u} =
      D.R.map (MulAut.conj D.y⁻¹).toMonoidHom ⊔ closure {D.t, D.u} ∧
    normalizer (D.R : Set G) ⊓ centralizer {D.t} = D.R ⊔ D.H ⊔ zpowers D.u :=
  ⟨D.card_P1, D.card_P2, D.card_D1, D.card_D2, card_R D, card_H D,
    R_inf_map_D1 D, D1_inf_closure_t_u D, centralizer_D1_inf_centralizer_u D,
    centralizer_D1_inf_centralizer_t D, centralizer_D1_inf_centralizer_tu D,
    normalizer_R_inf_centralizer_t D⟩

end CFSG.OddTranspositions.PartThree.Wong.RootData
