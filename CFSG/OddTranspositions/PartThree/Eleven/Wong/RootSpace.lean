module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.RootComplement
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentLocal
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.OddCore
public import CFSG.GH74.GLS.SP.GenOrder
public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Tactic.Ring
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveGeneral
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83

public section

namespace CFSG.OddTranspositions.PartThree.Wong.RootData

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] (D : RootData G)

private theorem D1_le_R : D.D1 ≤ D.R := by
  rw [D.D1_eq_range]
  rintro _ ⟨a, rfl⟩
  change D.d (thetaM a.toAdd) ∈ D.P1 ⊔ D.P2
  rw [D.d_apply]
  exact mul_mem_sup ⟨a, rfl⟩ ⟨a, rfl⟩

private theorem R_le_centralizer_R : D.R ≤ centralizer (D.R : Set G) := by
  have hP1 : D.P1 ≤ centralizer (D.P1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    rw [← map_mul, ← map_mul, mul_comm]
  have hP2 : D.P2 ≤ centralizer (D.P1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hx
    exact (D.commute_q1_q2 a b).eq
  have hR1 : D.R ≤ centralizer (D.P1 : Set G) := sup_le hP1 hP2
  have h1 : D.P1 ≤ centralizer (D.R : Set G) := Subgroup.le_centralizer_iff.mp hR1
  have hP1' : D.P1 ≤ centralizer (D.P2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact (D.commute_q1_q2 a b).symm.eq
  have hP2' : D.P2 ≤ centralizer (D.P2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    rw [← map_mul, ← map_mul, mul_comm]
  have hR2 : D.R ≤ centralizer (D.P2 : Set G) := sup_le hP1' hP2'
  exact sup_le h1 (Subgroup.le_centralizer_iff.mp hR2)

private theorem t_mem_centralizer_R : D.t ∈ centralizer (D.R : Set G) := by
  have h1 : D.P1 ≤ centralizer {D.t} := by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (D.t_commute_i1 (thetaM a.toAdd)).symm.eq
  have h2 : D.P2 ≤ centralizer {D.t} := by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (D.t_commute_i2 (thetaM a.toAdd)).symm.eq
  have hR : D.R ≤ centralizer ({D.t} : Set G) := sup_le h1 h2
  have hR' : D.R ≤ centralizer (zpowers D.t : Set G) := by
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact mem_zpowers D.t |> fun h => Subgroup.le_centralizer_iff.mp hR' h

private theorem u_mem_normalizer_R : D.u ∈ normalizer (D.R : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (D.P1 ⊔ D.P2).map (MulAut.conj D.u).toMonoidHom = D.P1 ⊔ D.P2
  rw [Subgroup.map_sup]
  have h1 : D.P1.map (MulAut.conj D.u).toMonoidHom = D.P2 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := hy
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, D.u_inv]
      have h := D.u_conj_q1 a
      rw [D.u_inv] at h
      rw [h]
      exact ⟨a, rfl⟩
    · intro hx
      obtain ⟨a, rfl⟩ := hx
      refine ⟨D.q1 a, ⟨a, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, D.u_inv]
      have h := D.u_conj_q1 a
      rw [D.u_inv] at h
      exact h
  have h2 : D.P2.map (MulAut.conj D.u).toMonoidHom = D.P1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := hy
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, D.u_inv]
      have h := D.u_conj_q2 a
      rw [D.u_inv] at h
      rw [h]
      exact ⟨a, rfl⟩
    · intro hx
      obtain ⟨a, rfl⟩ := hx
      refine ⟨D.q2 a, ⟨a, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, D.u_inv]
      have h := D.u_conj_q2 a
      rw [D.u_inv] at h
      exact h
  rw [h1, h2, sup_comm]

private theorem closure_t_u_le_normalizer_R :
    closure {D.t, D.u} ≤ normalizer (D.R : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro g (rfl | rfl)
  · exact Subgroup.centralizer_le_normalizer _ (t_mem_centralizer_R D)
  · exact u_mem_normalizer_R D

private theorem card_R_eq [Finite G] : Nat.card D.R = 25 :=
  (diagonal_unipotent_local_data D).2.2.2.2.1

private theorem card_H_eq [Finite G] : Nat.card D.H = 8 :=
  (diagonal_unipotent_local_data D).2.2.2.2.2.1

private theorem NR_inf_centralizer_t_eq [Finite G] :
    normalizer (D.R : Set G) ⊓ centralizer {D.t} = D.R ⊔ D.H ⊔ zpowers D.u :=
  (diagonal_unipotent_local_data D).2.2.2.2.2.2.2.2.2.2.2

private theorem Q_normal_in_centralizer {x c : G} (hx : x ∈ D.Q)
    (hc : c ∈ centralizer (D.D1 : Set G)) : c * x * c⁻¹ ∈ D.Q := by
  change x ∈ (CFSG.oddCore (centralizer (D.D1 : Set G))).map
    (centralizer (D.D1 : Set G)).subtype at hx
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
  have hconj : (⟨c, hc⟩ : centralizer (D.D1 : Set G)) * k *
      (⟨c, hc⟩ : centralizer (D.D1 : Set G))⁻¹ ∈
      CFSG.oddCore (centralizer (D.D1 : Set G)) :=
    (CFSG.oddCore_normal (centralizer (D.D1 : Set G))).conj_mem k hk ⟨c, hc⟩
  exact Subgroup.mem_map.mpr ⟨_, hconj, rfl⟩

private theorem card_closure_t_u : Nat.card (closure {D.t, D.u}) = 4 :=
  card_closure_pair D.orderOf_t D.orderOf_u D.t_commute_u D.u_ne_t

private theorem closure_t_u_le_centralizer_D1 :
    closure {D.t, D.u} ≤ centralizer (D.D1 : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro g (rfl | rfl)
  · refine (Subgroup.mem_centralizer_iff).mpr ?_
    intro y hy
    rw [D.D1_eq_range] at hy
    obtain ⟨a, rfl⟩ := hy
    exact (D.d_commute_t (thetaM a.toAdd)).eq
  · refine (Subgroup.mem_centralizer_iff).mpr ?_
    intro y hy
    rw [D.D1_eq_range] at hy
    obtain ⟨a, rfl⟩ := hy
    exact (D.d_commute_u (thetaM a.toAdd)).eq

private theorem mem_normalizer_Q_of_mem_centralizer_D1 {g : G}
    (hg : g ∈ centralizer (D.D1 : Set G)) : g ∈ normalizer (D.Q : Set G) := by
  refine (Subgroup.mem_normalizer_iff).mpr ?_
  intro x
  constructor
  · intro hx
    exact Q_normal_in_centralizer D hx hg
  · intro hx
    have h := Q_normal_in_centralizer D hx (inv_mem hg)
    rwa [show g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x by group] at h

private theorem closure_t_u_le_normalizer_Q :
    closure {D.t, D.u} ≤ normalizer (D.Q : Set G) :=
  (closure_t_u_le_centralizer_D1 D).trans fun _ hg =>
    mem_normalizer_Q_of_mem_centralizer_D1 D hg

private theorem Q_inf_closure_t_u [Finite G] : D.Q ⊓ closure {D.t, D.u} = ⊥ := by
  refine Subgroup.inf_eq_bot_of_coprime ?_
  rw [show Nat.card D.Q = 125 from (odd_complement_of_diagonal_centralizer D).1,
    card_closure_t_u D]
  norm_num

private theorem card_centralizer_D1 [Finite G] :
    Nat.card (centralizer (D.D1 : Set G)) = 500 := by
  have hQ := (odd_complement_of_diagonal_centralizer D).1
  have hidx := (odd_complement_of_diagonal_centralizer D).2.1
  have h := Subgroup.relIndex_mul_card D.Q (centralizer (D.D1 : Set G))
  rw [inf_eq_left.mpr (Q_le_centralizer D), hQ, hidx] at h
  omega

private theorem centralizer_D1_eq [Finite G] :
    centralizer (D.D1 : Set G) = D.Q ⊔ closure {D.t, D.u} := by
  have hle : D.Q ⊔ closure {D.t, D.u} ≤ centralizer (D.D1 : Set G) :=
    sup_le (Q_le_centralizer D) (closure_t_u_le_centralizer_D1 D)
  have hcard : Nat.card ↥(D.Q ⊔ closure {D.t, D.u}) =
      Nat.card ↥(centralizer (D.D1 : Set G)) := by
    rw [CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot
      (closure_t_u_le_normalizer_Q D) (Q_inf_closure_t_u D),
      show Nat.card D.Q = 125 from (odd_complement_of_diagonal_centralizer D).1,
      card_closure_t_u D]
    exact (card_centralizer_D1 D).symm
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)).symm

private theorem centralizer_D1_set_eq [Finite G] :
    (centralizer (D.D1 : Set G) : Set G) =
      (D.Q : Set G) * (closure {D.t, D.u} : Set G) := by
  rw [centralizer_D1_eq D]
  exact Subgroup.coe_mul_of_right_le_normalizer_left D.Q (closure {D.t, D.u})
    (closure_t_u_le_normalizer_Q D)

private theorem D2_le_R : D.D2 ≤ D.R := by
  intro x hx
  obtain ⟨a, rfl⟩ := hx
  change D.q1 a * D.q2 a⁻¹ ∈ D.R
  exact mul_mem_sup ⟨a, rfl⟩ ⟨a⁻¹, rfl⟩

private theorem map_R_y_le_Q [Finite G] :
    D.R.map (MulAut.conj D.y⁻¹).toMonoidHom ≤ D.Q := by
  have hset := (odd_complement_of_diagonal_centralizer D).2.2.1
  intro x hx
  change x ∈ (D.Q : Set G)
  rw [hset, Set.mem_mul]
  exact ⟨x, hx, 1, one_mem _, mul_one x⟩

private theorem R_le_Q [Finite G] : D.R ≤ D.Q := by
  have hset := (odd_complement_of_diagonal_centralizer D).2.2.1
  intro x hx
  change x ∈ (D.Q : Set G)
  rw [hset, Set.mem_mul]
  exact ⟨1, one_mem _, x, hx, one_mul x⟩

private theorem P1_le_Q [Finite G] : D.P1 ≤ D.Q := (le_sup_left.trans (R_le_Q D))

private theorem P2_le_Q [Finite G] : D.P2 ≤ D.Q := (le_sup_right.trans (R_le_Q D))

private theorem P3_le_Q [Finite G] : D.P3 ≤ D.Q := by
  rw [D.P3_eq_map_D2]
  exact (Subgroup.map_mono (D2_le_R D)).trans (map_R_y_le_Q D)

private theorem isKleinFour_closure_t_u : IsKleinFour (closure {D.t, D.u}) :=
  CFSG.OddStandard.isKleinFour_of_card_four_of_mul_self (card_closure_t_u D) (by
    intro x
    apply Subtype.ext
    have h := sq_eq_one_of_mem_closure (G := G) (s := ({D.t, D.u} : Set G)) ?_ ?_ x.2
    · simpa [pow_two] using h
    · intro a ha b hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      exacts [Commute.refl _, D.t_commute_u, D.t_commute_u.symm, Commute.refl _]
    · rintro a (rfl | rfl)
      · rw [← D.orderOf_t, pow_orderOf_eq_one]
      · rw [← D.orderOf_u, pow_orderOf_eq_one])

private theorem map_conj_closure_t_u [Finite G] {f : G}
    (hf : f ∈ closure {D.t, D.u}) :
    (closure {D.t, D.u}).map (MulAut.conj f).toMonoidHom = closure {D.t, D.u} := by
  haveI hK4 : IsKleinFour (closure {D.t, D.u}) := isKleinFour_closure_t_u D
  haveI : Finite ↥(closure {D.t, D.u}) := Subtype.finite
  have hle : (closure {D.t, D.u}).map (MulAut.conj f).toMonoidHom ≤
      closure {D.t, D.u} := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hf hy) (Subgroup.inv_mem _ hf)
  exact Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective (K := closure {D.t, D.u})
      (f := (MulAut.conj f).toMonoidHom) (MulAut.conj f).injective).symm)

private theorem isSylowOf_two_centralizer_D1_of_card_four [Finite G] (P : Subgroup G)
    (hPle : P ≤ centralizer (D.D1 : Set G)) (hPcard : Nat.card P = 4) :
    CFSG.ABGLocalTools.IsSylowOf 2 P (centralizer (D.D1 : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.ABGLocalTools.isSylowOf_of_card hPle ?_
  rw [hPcard, card_centralizer_D1 D]
  norm_num [Nat.factorization]

private theorem isSylowOf_two_closure_t_u [Finite G] :
    CFSG.ABGLocalTools.IsSylowOf 2 (closure {D.t, D.u})
      (centralizer (D.D1 : Set G)) :=
  isSylowOf_two_centralizer_D1_of_card_four D _
    (closure_t_u_le_centralizer_D1 D) (card_closure_t_u D)

private theorem exists_conj_closure_t_u_of_le_centralizer_D1 [Finite G] (P : Subgroup G)
    (hPle : P ≤ centralizer (D.D1 : Set G)) (hPcard : Nat.card P = 4) :
    ∃ k ∈ centralizer (D.D1 : Set G),
      P = (closure {D.t, D.u}).map (MulAut.conj k⁻¹).toMonoidHom := by
  obtain ⟨k, hkC, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj
    (isSylowOf_two_centralizer_D1_of_card_four D P hPle hPcard)
    (isSylowOf_two_closure_t_u D)
  refine ⟨k, hkC, ?_⟩
  ext x
  constructor
  · intro hx
    have hfF : k * x * k⁻¹ ∈ closure {D.t, D.u} := by
      refine (hk (k * x * k⁻¹)).mpr ?_
      rwa [show k⁻¹ * (k * x * k⁻¹) * k = x by group]
    refine ⟨k * x * k⁻¹, hfF, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨y, hy, rfl⟩
    simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using (hk y).mp hy

private theorem exists_conj_closure_t_u_of_le_centralizer_R [Finite G] (P : Subgroup G)
    (hPle : P ≤ centralizer (D.R : Set G)) (hPcard : Nat.card P = 4) :
    ∃ q0 ∈ D.Q, P = (closure {D.t, D.u}).map (MulAut.conj q0).toMonoidHom := by
  have hPleC : P ≤ centralizer (D.D1 : Set G) :=
    hPle.trans (Subgroup.centralizer_le (fun x hx => D1_le_R D hx))
  obtain ⟨k, hkC, hPmap⟩ :=
    exists_conj_closure_t_u_of_le_centralizer_D1 D P hPleC hPcard
  change k ∈ (centralizer (D.D1 : Set G) : Set G) at hkC
  rw [centralizer_D1_set_eq D, Set.mem_mul] at hkC
  obtain ⟨q, hq, f, hf, rfl⟩ := hkC
  set q0 : G := f⁻¹ * q⁻¹ * f with hq0def
  have hq0Q : q0 ∈ D.Q := by
    have h := Q_normal_in_centralizer D (x := q⁻¹) (Subgroup.inv_mem _ hq)
      (closure_t_u_le_centralizer_D1 D (Subgroup.inv_mem _ hf))
    simpa [q0, mul_assoc] using h
  have hf0F : f⁻¹ ∈ closure {D.t, D.u} := Subgroup.inv_mem _ hf
  have hkq : (q * f)⁻¹ = q0 * f⁻¹ := by
    simp only [q0]
    group
  refine ⟨q0, hq0Q, ?_⟩
  rw [hPmap, hkq]
  calc (closure {D.t, D.u}).map (MulAut.conj (q0 * f⁻¹)).toMonoidHom
      = (closure {D.t, D.u}).map
          (((MulAut.conj q0).toMonoidHom).comp (MulAut.conj f⁻¹).toMonoidHom) := by
        congr 1
        ext x
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp,
          Function.comp_apply]
        group
    _ = ((closure {D.t, D.u}).map (MulAut.conj f⁻¹).toMonoidHom).map
          (MulAut.conj q0).toMonoidHom := by rw [Subgroup.map_map]
    _ = (closure {D.t, D.u}).map (MulAut.conj q0).toMonoidHom := by
          rw [map_conj_closure_t_u D hf0F]

private theorem conj_closure_t_u_not_le_centralizer_R [Finite G] {q0 : G}
    (hq0Q : q0 ∈ D.Q) :
    ¬ (closure {D.t, D.u}).map (MulAut.conj q0).toMonoidHom ≤
      centralizer (D.R : Set G) := by
  intro hle
  have hsP : q0 * D.u * q0⁻¹ ∈
      (closure {D.t, D.u}).map (MulAut.conj q0).toMonoidHom :=
    ⟨D.u, subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
  have hscomm : q0 * D.u * q0⁻¹ ∈ centralizer (D.R : Set G) := hle hsP
  have hmap_le : D.R.map (MulAut.conj q0⁻¹).toMonoidHom ≤
      D.Q ⊓ centralizer {D.u} := by
    refine le_inf ?_ ?_
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := hx
      exact D.Q.mul_mem (D.Q.mul_mem (D.Q.inv_mem hq0Q) (R_le_Q D hr))
        (by simpa [inv_inv] using hq0Q)
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := hx
      have hsr : (q0 * D.u * q0⁻¹) * r = r * (q0 * D.u * q0⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hscomm r hr).symm
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc (q0⁻¹ * r * q0) * D.u
          = q0⁻¹ * (r * (q0 * D.u * q0⁻¹)) * q0 := by group
        _ = q0⁻¹ * ((q0 * D.u * q0⁻¹) * r) * q0 := by rw [← hsr]
        _ = D.u * (q0⁻¹ * r * q0) := by group
  have hmapD1 : D.R.map (MulAut.conj q0⁻¹).toMonoidHom ≤ D.D1 := by
    rw [← (odd_complement_of_diagonal_centralizer D).2.2.2.2.1]
    exact hmap_le
  have hcardmap : Nat.card (D.R.map (MulAut.conj q0⁻¹).toMonoidHom) = 25 := by
    rw [Subgroup.card_map_of_injective (K := D.R)
      (f := (MulAut.conj q0⁻¹).toMonoidHom) (MulAut.conj q0⁻¹).injective]
    exact card_R_eq D
  have := Subgroup.card_le_of_le hmapD1
  rw [hcardmap, D.card_D1] at this
  omega

private theorem not_card_four_of_le_centralizer_R [Finite G] (P : Subgroup G)
    (hPle : P ≤ centralizer (D.R : Set G)) (hPcard : Nat.card P = 4) : False := by
  obtain ⟨q0, hq0Q, hPq0⟩ :=
    exists_conj_closure_t_u_of_le_centralizer_R D P hPle hPcard
  exact conj_closure_t_u_not_le_centralizer_R D hq0Q (hPq0 ▸ hPle)

private theorem relIndex_inf_centralizer_dvd_four [Finite G] :
    (D.Q ⊓ centralizer (D.R : Set G)).relIndex (centralizer (D.R : Set G)) ∣ 4 := by
  classical
  let C : Subgroup G := centralizer (D.D1 : Set G)
  let A : Subgroup C := (centralizer (D.R : Set G)).subgroupOf C
  let B : Subgroup C := D.Q.subgroupOf C
  have hleCR : centralizer (D.R : Set G) ≤ C :=
    Subgroup.centralizer_le (fun x hx => D1_le_R D hx)
  have hBnorm : B.Normal := by
    rw [show B = D.Q.subgroupOf C from rfl,
      Subgroup.normal_subgroupOf_iff_le_normalizer (Q_le_centralizer D)]
    intro c hc
    exact mem_normalizer_Q_of_mem_centralizer_D1 D hc
  haveI : B.Normal := hBnorm
  have hAB : A ⊓ B = (D.Q ⊓ centralizer (D.R : Set G)).subgroupOf C := by
    ext x
    simp [A, B, Subgroup.mem_subgroupOf, Subgroup.mem_inf, and_assoc, and_comm, and_left_comm]
  have hsub : (D.Q ⊓ centralizer (D.R : Set G)).relIndex (centralizer (D.R : Set G)) =
      ((D.Q ⊓ centralizer (D.R : Set G)).subgroupOf C).relIndex A :=
    (Subgroup.relIndex_subgroupOf hleCR).symm
  rw [hsub, ← hAB, Subgroup.inf_relIndex_left]
  have h1 : B.relIndex A = B.relIndex (A ⊔ B) :=
    (Subgroup.relIndex_sup_right (H := A) (K := B)).symm
  rw [h1]
  have h2 : B.relIndex (A ⊔ B) ∣ B.index :=
    Subgroup.relIndex_dvd_index_of_le (le_sup_right : B ≤ A ⊔ B)
  have h3 : B.index = 4 := (odd_complement_of_diagonal_centralizer D).2.1
  rwa [h3] at h2

private theorem t_notMem_inf_centralizer_R [Finite G] :
    D.t ∉ D.Q ⊓ centralizer (D.R : Set G) := by
  intro ht
  have h2 : orderOf D.t ∣ Nat.card D.Q :=
    Subgroup.orderOf_dvd_natCard D.Q ht.1
  rw [D.orderOf_t] at h2
  exact (Nat.not_even_iff_odd.mpr (odd_card_Q D)) (even_iff_two_dvd.mpr h2)

private theorem relIndex_inf_centralizer_eq_two [Finite G] :
    (D.Q ⊓ centralizer (D.R : Set G)).relIndex (centralizer (D.R : Set G)) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd := relIndex_inf_centralizer_dvd_four D
  have hne1 : (D.Q ⊓ centralizer (D.R : Set G)).relIndex
      (centralizer (D.R : Set G)) ≠ 1 := by
    intro h1
    have hle : centralizer (D.R : Set G) ≤ D.Q ⊓ centralizer (D.R : Set G) :=
      Subgroup.relIndex_eq_one.mp h1
    exact t_notMem_inf_centralizer_R D (hle (t_mem_centralizer_R D))
  have hne4 : (D.Q ⊓ centralizer (D.R : Set G)).relIndex
      (centralizer (D.R : Set G)) ≠ 4 := by
    intro h4
    have hcard : Nat.card (centralizer (D.R : Set G)) =
        4 * Nat.card ↥(D.Q ⊓ centralizer (D.R : Set G)) := by
      have h := Subgroup.relIndex_mul_card (D.Q ⊓ centralizer (D.R : Set G))
        (centralizer (D.R : Set G))
      rw [inf_eq_left.mpr inf_le_right, h4] at h
      omega
    have h4dvd : 4 ∣ Nat.card (centralizer (D.R : Set G)) := by
      rw [hcard]
      exact dvd_mul_right 4 _
    obtain ⟨H, hHcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(centralizer (D.R : Set G)))
      2 (n := 2) (by simpa using h4dvd)
    exact not_card_four_of_le_centralizer_R D (H.map (centralizer (D.R : Set G)).subtype)
      (Subgroup.map_subtype_le H) (by
        rw [Subgroup.card_map_of_injective (centralizer (D.R : Set G)).subtype_injective,
          hHcard]
        norm_num)
  have hdvd2 : (D.Q ⊓ centralizer (D.R : Set G)).relIndex
      (centralizer (D.R : Set G)) ∣ 2 ^ 2 := by simpa using hdvd
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2 with ⟨k, hk, hpow⟩
  interval_cases k
  · rw [pow_zero] at hpow
    exact absurd hpow hne1
  · rw [pow_one] at hpow
    exact hpow
  · rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at hpow
    exact absurd hpow hne4

private theorem centralizer_R_eq [Finite G] :
    centralizer (D.R : Set G) =
      (D.Q ⊓ centralizer (D.R : Set G)) ⊔ zpowers D.t := by
  set K : Subgroup G := D.Q ⊓ centralizer (D.R : Set G) with hKdef
  have hKle : K ≤ centralizer (D.R : Set G) := inf_le_right
  have htC : D.t ∈ centralizer (D.R : Set G) := t_mem_centralizer_R D
  have hKt : K ⊓ zpowers D.t = ⊥ := by
    have hodd : Odd (Nat.card K) :=
      (odd_card_Q D).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [Nat.card_zpowers, D.orderOf_t]
    exact (Nat.coprime_two_left.mpr hodd).symm
  have htN : zpowers D.t ≤ normalizer (K : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    have htC1 : D.t ∈ centralizer (D.D1 : Set G) :=
      closure_t_u_le_centralizer_D1 D (subset_closure (Set.mem_insert _ _))
    have htNQ : D.t ∈ normalizer (D.Q : Set G) :=
      mem_normalizer_Q_of_mem_centralizer_D1 D htC1
    have htNR : D.t ∈ normalizer (D.R : Set G) :=
      Subgroup.centralizer_le_normalizer _ htC
    have htNCR : D.t ∈ normalizer (centralizer (D.R : Set G) : Set G) :=
      CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer D.R htNR
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (D.Q ⊓ centralizer (D.R : Set G)).map (MulAut.conj D.t).toMonoidHom =
      D.Q ⊓ centralizer (D.R : Set G)
    rw [Subgroup.map_inf _ _ _ (MulAut.conj D.t).injective,
      show D.Q.map (MulEquiv.toMonoidHom (MulAut.conj D.t)) = D.Q from
        Subgroup.mem_normalizer_iff_map_conj_eq.mp htNQ,
      show (centralizer (D.R : Set G)).map (MulEquiv.toMonoidHom (MulAut.conj D.t)) =
          centralizer (D.R : Set G) from
        Subgroup.mem_normalizer_iff_map_conj_eq.mp htNCR]
  have hcard : Nat.card ↥(K ⊔ zpowers D.t) = Nat.card ↥(centralizer (D.R : Set G)) := by
    rw [CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot htN hKt, Nat.card_zpowers, D.orderOf_t]
    have h := Subgroup.relIndex_mul_card K (centralizer (D.R : Set G))
    rw [inf_eq_left.mpr hKle, relIndex_inf_centralizer_eq_two D] at h
    omega
  exact (Subgroup.eq_of_le_of_card_ge (sup_le hKle (Subgroup.zpowers_le.mpr htC))
    (le_of_eq hcard.symm)).symm

private theorem R_set_eq : (D.R : Set G) = (D.P1 : Set G) * (D.P2 : Set G) := by
  rw [show D.R = D.P1 ⊔ D.P2 from rfl]
  have hP2C : D.P2 ≤ centralizer (D.P1 : Set G) := by
    intro x hx
    refine (Subgroup.mem_centralizer_iff).mpr ?_
    intro y hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact (D.commute_q1_q2 b a).eq
  exact Subgroup.coe_mul_of_right_le_normalizer_left D.P1 D.P2
    (hP2C.trans (Subgroup.centralizer_le_normalizer _))

private theorem R_pow_five [Finite G] {x : G} (hx : x ∈ D.R) : x ^ 5 = 1 := by
  change x ∈ (D.R : Set G) at hx
  rw [R_set_eq D, Set.mem_mul] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨q, rfl⟩ := hb
  have hp5 : p ^ 5 = 1 := by
    simpa using pow_card_eq_one (x := p)
  have hq5 : q ^ 5 = 1 := by
    simpa using pow_card_eq_one (x := q)
  have hp : D.q1 p ^ 5 = 1 := by rw [← map_pow, hp5, map_one]
  have hq : D.q2 q ^ 5 = 1 := by rw [← map_pow, hq5, map_one]
  rw [(D.commute_q1_q2 p q).mul_pow, hp, hq, one_mul]

private theorem map_R_y_pow_five [Finite G] {x : G}
    (hx : x ∈ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom) : x ^ 5 = 1 := by
  obtain ⟨r, hr, rfl⟩ := hx
  rw [← map_pow, R_pow_five D hr, map_one]

private theorem R_commute {x y : G} (hx : x ∈ D.R) (hy : y ∈ D.R) : Commute x y :=
  (Subgroup.mem_centralizer_iff.mp (R_le_centralizer_R D hx) y hy).symm

private theorem map_R_y_commute {x y : G}
    (hx : x ∈ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom)
    (hy : y ∈ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom) : Commute x y := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact (R_commute D ha hb).map (MulAut.conj (D.y⁻¹)).toMonoidHom

private theorem commute_of_mem_Q [Finite G] (hQR : D.Q ≤ centralizer (D.R : Set G))
    {x y : G} (hx : x ∈ D.Q) (hy : y ∈ D.Q) : Commute x y := by
  have hset := (odd_complement_of_diagonal_centralizer D).2.2.1
  change x ∈ (D.Q : Set G) at hx
  change y ∈ (D.Q : Set G) at hy
  rw [hset, Set.mem_mul] at hx hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨c, hc, d, hd, rfl⟩ := hy
  have hac : Commute a c := map_R_y_commute D ha hc
  have hbd : Commute b d := R_commute D hb hd
  have hab : Commute a b := (Subgroup.mem_centralizer_iff.mp (hQR (map_R_y_le_Q D ha)) b hb).symm
  have had : Commute a d := (Subgroup.mem_centralizer_iff.mp (hQR (map_R_y_le_Q D ha)) d hd).symm
  have hcb : Commute c b := (Subgroup.mem_centralizer_iff.mp (hQR (map_R_y_le_Q D hc)) b hb).symm
  have hcd : Commute c d := (Subgroup.mem_centralizer_iff.mp (hQR (map_R_y_le_Q D hc)) d hd).symm
  have h1 : Commute a (c * d) := hac.mul_right had
  have h2 : Commute b (c * d) := hcb.symm.mul_right hbd
  exact h1.mul_left h2

private theorem pow_five_of_mem_Q [Finite G] (hQR : D.Q ≤ centralizer (D.R : Set G))
    {x : G} (hx : x ∈ D.Q) : x ^ 5 = 1 := by
  have hset := (odd_complement_of_diagonal_centralizer D).2.2.1
  change x ∈ (D.Q : Set G) at hx
  rw [hset, Set.mem_mul] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [(commute_of_mem_Q D hQR (map_R_y_le_Q D ha) (R_le_Q D hb)).mul_pow,
    map_R_y_pow_five D ha, R_pow_five D hb, mul_one]

private theorem t_conj_q3_of_mem {x : G} (hx : x ∈ D.P3) : D.t⁻¹ * x * D.t = x⁻¹ := by
  obtain ⟨b, hb⟩ := hx
  rw [← hb]
  have h := D.t_conj_q3 b.toAdd
  rw [show Multiplicative.ofAdd b.toAdd = b from rfl] at h
  rw [h]
  congr 1
  rw [← map_inv]
  congr 1

private theorem P1_inf_P3 [Finite G] : D.P1 ⊓ D.P3 = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨hx1, hx3⟩ := mem_inf.mp hx
  obtain ⟨a, rfl⟩ := hx1
  obtain ⟨b, hb⟩ := hx3
  have hfix : D.t⁻¹ * D.q1 a * D.t = D.q1 a := D.t_conj_q1 a
  have hinv : D.t⁻¹ * D.q1 a * D.t = (D.q1 a)⁻¹ := by
    rw [← hb]
    exact t_conj_q3_of_mem D ⟨b, rfl⟩
  have hxeq : D.q1 a = (D.q1 a)⁻¹ := hfix.symm.trans hinv
  have hsq : (D.q1 a) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hxeq]
    exact mul_inv_cancel _
  have hodd : Odd (orderOf (D.q1 a)) :=
    Odd.of_dvd_nat (by norm_num : Odd 5) (by
      have := Subgroup.orderOf_dvd_natCard D.P1 (show D.q1 a ∈ D.P1 from ⟨a, rfl⟩)
      rwa [D.card_P1] at this)
  have h2 : orderOf (D.q1 a) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rw [mem_bot]
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd hodd (h ▸ by norm_num)

private theorem R_inf_P3 [Finite G] : D.R ⊓ D.P3 = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨hxR, hx3⟩ := mem_inf.mp hx
  obtain ⟨b, hb⟩ := hx3
  have htx : x * D.t = D.t * x :=
    Subgroup.mem_centralizer_iff.mp (t_mem_centralizer_R D) x hxR
  have hfix : D.t⁻¹ * x * D.t = x := by
    rw [D.t_inv, ← htx, mul_assoc, D.t_mul_t, mul_one]
  have hinv : D.t⁻¹ * x * D.t = x⁻¹ := by
    rw [← hb]
    exact t_conj_q3_of_mem D ⟨b, rfl⟩
  have hxeq : x = x⁻¹ := hfix.symm.trans hinv
  have hsq : x ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hxeq]
    exact mul_inv_cancel _
  have hodd : Odd (orderOf x) :=
    Odd.of_dvd_nat (by norm_num : Odd 5) (orderOf_dvd_of_pow_eq_one (R_pow_five D hxR))
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rw [mem_bot]
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd hodd (h ▸ by norm_num)

private theorem R_inf_map_R_y [Finite G] :
    D.R ⊓ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom = D.D1 :=
  (diagonal_unipotent_local_data D).2.2.2.2.2.2.1

private theorem normalizer_R_le_normalizer_Q_of_inf_eq [Finite G]
    (hKQ : D.Q ⊓ centralizer (D.R : Set G) = D.Q) :
    normalizer (D.R : Set G) ≤ normalizer (D.Q : Set G) := by
  have hQR : D.Q ≤ centralizer (D.R : Set G) := by
    rw [← hKQ]
    exact inf_le_right
  have hidx : D.Q.relIndex (centralizer (D.R : Set G)) = 2 := by
    rw [← hKQ]
    exact relIndex_inf_centralizer_eq_two D
  have hconj_mem : ∀ h ∈ normalizer (D.R : Set G), ∀ x ∈ D.Q, h * x * h⁻¹ ∈ D.Q := by
    intro h hh x hx
    have hhC : h ∈ normalizer (centralizer (D.R : Set G) : Set G) :=
      CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer D.R hh
    have hxC : h * x * h⁻¹ ∈ centralizer (D.R : Set G) := by
      refine (Subgroup.mem_normalizer_iff.mp hhC x).mp ?_
      exact hQR hx
    have hodd : Odd (orderOf (h * x * h⁻¹)) := by
      rw [show h * x * h⁻¹ = (MulAut.conj h) x from rfl, MulEquiv.orderOf_eq]
      exact Odd.of_dvd_nat (by norm_num : Odd 125) (by
        have := Subgroup.orderOf_dvd_natCard D.Q hx
        rwa [show Nat.card D.Q = 125 from
          (odd_complement_of_diagonal_centralizer D).1] at this)
    exact mem_of_relIndex_eq_two_of_odd (K := D.Q)
      (C := centralizer (D.R : Set G)) hidx hxC hodd
  intro g hg
  refine (Subgroup.mem_normalizer_iff).mpr ?_
  intro x
  constructor
  · intro hx
    exact hconj_mem g hg x hx
  · intro hx
    have h := hconj_mem g⁻¹ (inv_mem hg) (g * x * g⁻¹) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x by group] at h

private theorem t_notMem_centralizer_Q [Finite G] :
    D.t ∉ centralizer (D.Q : Set G) := by
  intro ht
  have hRy_le : D.R.map (MulAut.conj D.y⁻¹).toMonoidHom ≤ D.R := by
    intro x hx
    have hxQ : x ∈ D.Q := map_R_y_le_Q D hx
    have hxt : x ∈ centralizer {D.t} :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp ht) x hxQ)
    have hxR : x ∈ D.Q ⊓ centralizer {D.t} := mem_inf.mpr ⟨hxQ, hxt⟩
    rwa [(odd_complement_of_diagonal_centralizer D).2.2.2.1] at hxR
  have hRy_D1 : D.R.map (MulAut.conj D.y⁻¹).toMonoidHom ≤ D.D1 := by
    intro x hx
    have hxR : x ∈ D.R := hRy_le hx
    have hxinf : x ∈ D.R ⊓ D.R.map (MulAut.conj D.y⁻¹).toMonoidHom :=
      mem_inf.mpr ⟨hxR, hx⟩
    rwa [R_inf_map_R_y D] at hxinf
  have hcard := Subgroup.card_le_of_le hRy_D1
  rw [Subgroup.card_map_of_injective (K := D.R)
    (f := (MulAut.conj D.y⁻¹).toMonoidHom) (MulAut.conj D.y⁻¹).injective,
    card_R_eq D, D.card_D1] at hcard
  omega

private theorem Q_le_centralizer_Q [Finite G]
    (hQR : D.Q ≤ centralizer (D.R : Set G)) :
    D.Q ≤ centralizer (D.Q : Set G) := by
  intro x hx
  refine (Subgroup.mem_centralizer_iff).mpr ?_
  intro y hy
  exact (commute_of_mem_Q D hQR hx hy).eq.symm

private theorem centralizer_Q_le_Q_of_inf_eq [Finite G]
    (hKQ : D.Q ⊓ centralizer (D.R : Set G) = D.Q) :
    centralizer (D.Q : Set G) ≤ D.Q := by
  have hQR : D.Q ≤ centralizer (D.R : Set G) := by
    rw [← hKQ]
    exact inf_le_right
  have hCR : centralizer (D.R : Set G) = D.Q ⊔ zpowers D.t := by
    rw [centralizer_R_eq D, hKQ]
  have htNQ : D.t ∈ normalizer (D.Q : Set G) :=
    mem_normalizer_Q_of_mem_centralizer_D1 D
      (closure_t_u_le_centralizer_D1 D (subset_closure (Set.mem_insert _ _)))
  intro x hx
  have hxC : x ∈ centralizer (D.R : Set G) :=
    Subgroup.centralizer_le (fun y hy => R_le_Q D hy) hx
  rw [hCR] at hxC
  change x ∈ ((D.Q ⊔ zpowers D.t : Subgroup G) : Set G) at hxC
  rw [Subgroup.coe_mul_of_right_le_normalizer_left D.Q (zpowers D.t)
    (Subgroup.zpowers_le.mpr htNQ)] at hxC
  obtain ⟨q, hq, s, hs, rfl⟩ := hxC
  rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_t).mp hs with rfl | rfl
  · simpa using hq
  · exfalso
    apply t_notMem_centralizer_Q D
    have hqC : q ∈ centralizer (D.Q : Set G) :=
      Q_le_centralizer_Q D hQR hq
    have htq : D.t = q⁻¹ * (q * D.t) := by group
    rw [htq]
    exact mul_mem (inv_mem hqC) hx

private theorem centralizer_Q_eq_of_inf_eq [Finite G]
    (hKQ : D.Q ⊓ centralizer (D.R : Set G) = D.Q) :
    centralizer (D.Q : Set G) = D.Q :=
  le_antisymm (centralizer_Q_le_Q_of_inf_eq D hKQ)
    (Q_le_centralizer_Q D (by rw [← hKQ]; exact inf_le_right))

private theorem P3_le_normalizer_R_of_centralizes [Finite G]
    (hQR : D.Q ≤ centralizer (D.R : Set G)) : D.P3 ≤ normalizer (D.R : Set G) := by
  intro x hx
  refine Subgroup.centralizer_le_normalizer _ ?_
  refine (Subgroup.mem_centralizer_iff).mpr ?_
  intro y hy
  exact (commute_of_mem_Q D hQR (P3_le_Q D hx) (R_le_Q D hy)).eq.symm

private theorem card_R_sup_P3_of_centralizes [Finite G]
    (hQR : D.Q ≤ centralizer (D.R : Set G)) : Nat.card ↥(D.R ⊔ D.P3) = 125 := by
  rw [CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot
    (P3_le_normalizer_R_of_centralizes D hQR) (R_inf_P3 D), card_R_eq D, D.card_P3]

private theorem Q_eq_R_sup_P3_of_centralizes [Finite G]
    (hQR : D.Q ≤ centralizer (D.R : Set G)) : D.Q = D.R ⊔ D.P3 := by
  have hle : D.R ⊔ D.P3 ≤ D.Q := sup_le (R_le_Q D) (P3_le_Q D)
  have hcard : Nat.card ↥(D.R ⊔ D.P3) = Nat.card ↥D.Q := by
    rw [card_R_sup_P3_of_centralizes D hQR,
      show Nat.card D.Q = 125 from (odd_complement_of_diagonal_centralizer D).1]
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)).symm

private theorem Q_set_eq_P1P2P3_of_centralizes [Finite G]
    (hQR : D.Q ≤ centralizer (D.R : Set G)) :
    (D.Q : Set G) = (D.P1 : Set G) * (D.P2 : Set G) * (D.P3 : Set G) := by
  have h1 : (D.Q : Set G) = (D.R : Set G) * (D.P3 : Set G) := by
    rw [Q_eq_R_sup_P3_of_centralizes D hQR]
    exact Subgroup.coe_mul_of_right_le_normalizer_left D.R D.P3
      (P3_le_normalizer_R_of_centralizes D hQR)
  rw [h1, R_set_eq D]

private theorem H_le_normalizer_R_inf_centralizer_t [Finite G] :
    D.H ≤ normalizer (D.R : Set G) ⊓ centralizer {D.t} := by
  rw [NR_inf_centralizer_t_eq D]
  exact (le_sup_right : D.H ≤ D.R ⊔ D.H).trans
    (le_sup_left : D.R ⊔ D.H ≤ (D.R ⊔ D.H) ⊔ zpowers D.u)

private theorem H_le_normalizer_Q_of_inf_eq [Finite G]
    (hKQ : D.Q ⊓ centralizer (D.R : Set G) = D.Q) :
    D.H ≤ normalizer (D.Q : Set G) :=
  (H_le_normalizer_R_inf_centralizer_t D).trans
    (inf_le_left.trans (normalizer_R_le_normalizer_Q_of_inf_eq D hKQ))

private theorem mem_P3_of_t_inv [Finite G]
    (hQR : D.Q ≤ centralizer (D.R : Set G)) {x : G} (hxQ : x ∈ D.Q)
    (hxinv : D.t⁻¹ * x * D.t = x⁻¹) : x ∈ D.P3 := by
  have hQeq := Q_eq_R_sup_P3_of_centralizes D hQR
  have hx : x ∈ (D.R : Set G) * (D.P3 : Set G) := by
    have hx' : x ∈ (D.Q : Set G) := hxQ
    rw [hQeq] at hx'
    change x ∈ ((D.R ⊔ D.P3 : Subgroup G) : Set G) at hx'
    rwa [Subgroup.coe_mul_of_right_le_normalizer_left D.R D.P3
      (P3_le_normalizer_R_of_centralizes D hQR)] at hx'
  rw [Set.mem_mul] at hx
  obtain ⟨r, hr, p, hp, rfl⟩ := hx
  have hcom : Commute r p := commute_of_mem_Q D hQR (R_le_Q D hr) (P3_le_Q D hp)
  have hrt : r * D.t = D.t * r :=
    Subgroup.mem_centralizer_iff.mp (t_mem_centralizer_R D) r hr
  have ht_r : D.t⁻¹ * r * D.t = r := by
    rw [D.t_inv, ← hrt, mul_assoc, D.t_mul_t, mul_one]
  have ht_p : D.t⁻¹ * p * D.t = p⁻¹ := t_conj_q3_of_mem D hp
  have hconv : D.t⁻¹ * (r * p) * D.t = r * p⁻¹ := by
    rw [show D.t⁻¹ * (r * p) * D.t =
      (D.t⁻¹ * r * D.t) * (D.t⁻¹ * p * D.t) by group, ht_r, ht_p]
  rw [hconv, mul_inv_rev, (hcom.inv_inv).eq.symm] at hxinv
  have hr_eq : r = r⁻¹ := mul_right_cancel hxinv
  have hr2 : r ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hr_eq]
    exact mul_inv_cancel _
  have hodd : Odd (orderOf r) :=
    Odd.of_dvd_nat (by norm_num : Odd 25) (by
      have := Subgroup.orderOf_dvd_natCard D.R hr
      rwa [card_R_eq D] at this)
  have hr1 : r = 1 := by
    have hdvd : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one hr2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd hodd (h ▸ by norm_num)
  simpa [hr1] using hp

private theorem H_conj_mem_P3_of_inf_eq [Finite G]
    (hKQ : D.Q ⊓ centralizer (D.R : Set G) = D.Q)
    {h x : G} (hh : h ∈ D.H) (hx : x ∈ D.P3) : h⁻¹ * x * h ∈ D.P3 := by
  have hQR : D.Q ≤ centralizer (D.R : Set G) := by
    rw [← hKQ]
    exact inf_le_right
  have hHNQ : D.H ≤ normalizer (D.Q : Set G) := H_le_normalizer_Q_of_inf_eq D hKQ
  have hHCt : D.H ≤ centralizer {D.t} :=
    (H_le_normalizer_R_inf_centralizer_t D).trans inf_le_right
  have hxQ : h⁻¹ * x * h ∈ D.Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem (hHNQ hh)) x).mp
      (P3_le_Q D hx)
  refine mem_P3_of_t_inv D hQR hxQ ?_
  have hth : D.t * h = h * D.t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hHCt hh)).symm
  have hth_inv : D.t⁻¹ * h⁻¹ = h⁻¹ * D.t⁻¹ := by
    have := hth
    have h1 : h⁻¹ * D.t⁻¹ = D.t⁻¹ * h⁻¹ := by
      rw [← mul_inv_rev, this, mul_inv_rev]
    exact h1.symm
  have hxt : D.t⁻¹ * x * D.t = x⁻¹ := t_conj_q3_of_mem D hx
  calc D.t⁻¹ * (h⁻¹ * x * h) * D.t
      = (D.t⁻¹ * h⁻¹) * x * (h * D.t) := by group
    _ = (h⁻¹ * D.t⁻¹) * x * (D.t * h) := by rw [hth_inv, hth]
    _ = h⁻¹ * (D.t⁻¹ * x * D.t) * h := by group
    _ = h⁻¹ * x⁻¹ * h := by rw [hxt]
    _ = (h⁻¹ * x * h)⁻¹ := by group

private theorem q3_ofAdd_pow (a : ZMod 5) :
    D.q3 (.ofAdd a) = (D.q3 (.ofAdd 1)) ^ a.val := by
  rw [← map_pow, ← ofAdd_nsmul]
  congr 1
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]

private theorem q3_pow_mul (a b : ZMod 5) :
    (D.q3 (.ofAdd a)) ^ b.val = D.q3 (.ofAdd (b * a)) := by
  rw [← map_pow, ← ofAdd_nsmul]
  congr 1
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]

private theorem eq_t_of_mem_sup_R_t [Finite G] {x : G}
    (hx : x ∈ D.R ⊔ zpowers D.t) (hx2 : x * x = 1) (hx1 : x ≠ 1) : x = D.t := by
  have htN : zpowers D.t ≤ normalizer (D.R : Set G) :=
    Subgroup.zpowers_le.mpr
      (Subgroup.centralizer_le_normalizer _ (t_mem_centralizer_R D))
  have hx' : x ∈ (D.R : Set G) * (zpowers D.t : Set G) := by
    have h := hx
    change x ∈ ((D.R ⊔ zpowers D.t : Subgroup G) : Set G) at h
    rwa [Subgroup.coe_mul_of_right_le_normalizer_left D.R (zpowers D.t) htN] at h
  rw [Set.mem_mul] at hx'
  obtain ⟨r, hr, s, hs, rfl⟩ := hx'
  have hlt : r * D.t = D.t * r :=
    Subgroup.mem_centralizer_iff.mp (t_mem_centralizer_R D) r hr
  have hr_one : r = 1 := by
    have hdvd2 : orderOf r ∣ 2 := by
      have hrr : r * r = 1 := by
        rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_t).mp hs with rfl | rfl
        · simpa using hx2
        · have h2 : (r * D.t) * (r * D.t) = r * r := by
            calc (r * D.t) * (r * D.t) = r * (D.t * r) * D.t := by group
              _ = r * (r * D.t) * D.t := by rw [← hlt]
              _ = r * r * (D.t * D.t) := by group
              _ = r * r := by rw [D.t_mul_t, mul_one]
          rwa [h2] at hx2
      exact orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hrr)
    have hdvd5 : orderOf r ∣ 5 :=
      orderOf_dvd_of_pow_eq_one (R_pow_five D hr)
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 2 5) hdvd2 hdvd5)
  rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_t).mp hs with rfl | rfl
  · exact absurd (by simp [hr_one]) hx1
  · simpa [hr_one] using rfl

private theorem normalizer_R_le_centralizer_t_of_inf_eq [Finite G]
    (hKR : D.Q ⊓ centralizer (D.R : Set G) = D.R) :
    normalizer (D.R : Set G) ≤ centralizer {D.t} := by
  intro g hg
  have hgNCR : g ∈ normalizer (centralizer (D.R : Set G) : Set G) :=
    CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer D.R hg
  have hconj_mem : g * D.t * g⁻¹ ∈ centralizer (D.R : Set G) := by
    refine (Subgroup.mem_normalizer_iff.mp hgNCR D.t).mp ?_
    exact t_mem_centralizer_R D
  have hconj_sq : (g * D.t * g⁻¹) * (g * D.t * g⁻¹) = 1 := by
    calc (g * D.t * g⁻¹) * (g * D.t * g⁻¹) = g * (D.t * D.t) * g⁻¹ := by group
      _ = 1 := by rw [D.t_mul_t]; group
  have hconj_ne1 : g * D.t * g⁻¹ ≠ 1 := by
    intro h
    have ht1 : D.t = 1 := by
      calc D.t = g⁻¹ * (g * D.t * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have h2 := D.orderOf_t
    rw [ht1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hCR : centralizer (D.R : Set G) = D.R ⊔ zpowers D.t := by
    rw [centralizer_R_eq D, hKR]
  have hconj_eq : g * D.t * g⁻¹ = D.t := by
    have hmem : g * D.t * g⁻¹ ∈ D.R ⊔ zpowers D.t := by
      rwa [← hCR]
    exact eq_t_of_mem_sup_R_t D hmem hconj_sq hconj_ne1
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  calc g * D.t = (g * D.t * g⁻¹) * g := by group
    _ = D.t * g := by rw [hconj_eq]

private theorem normalizer_R_eq_of_inf_eq [Finite G]
    (hKR : D.Q ⊓ centralizer (D.R : Set G) = D.R) :
    normalizer (D.R : Set G) = D.R ⊔ D.H ⊔ zpowers D.u := by
  calc normalizer (D.R : Set G) = normalizer (D.R : Set G) ⊓ centralizer {D.t} :=
        (inf_eq_left.mpr (normalizer_R_le_centralizer_t_of_inf_eq D hKR)).symm
    _ = D.R ⊔ D.H ⊔ zpowers D.u := NR_inf_centralizer_t_eq D

private theorem exists_isPGroup_five_gt_R_le_normalizer_R [Finite G] :
    ∃ M : Subgroup G, IsPGroup 5 M ∧ D.R < M ∧ M ≤ normalizer (D.R : Set G) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hQcard : Nat.card D.Q = 125 := (odd_complement_of_diagonal_centralizer D).1
  have hRltQ : D.R < D.Q := by
    refine lt_of_le_of_ne (R_le_Q D) ?_
    intro heq
    have hcard : Nat.card D.R = Nat.card D.Q := by rw [heq]
    rw [card_R_eq D, hQcard] at hcard
    omega
  have hQp : IsPGroup 5 D.Q :=
    IsPGroup.of_card (n := 3) (by rw [hQcard]; norm_num)
  exact ⟨D.Q ⊓ normalizer (D.R : Set G), hQp.to_le inf_le_left,
    CFSG.GroupTheory.FT63ChII.lt_inf_normalizer_of_lt (q := 5) hQp hRltQ, inf_le_right⟩

private theorem u_mem_normalizer_H [Finite G] :
    D.u ∈ normalizer (D.H : Set G) := by
  have h1h2 : (MulAut.conj D.u).toMonoidHom D.h1 = D.h2 := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, D.u_inv]
    change D.u * D.i1 hM * D.u = D.i2 hM
    have hswap := D.swap hM
    rwa [D.u_inv] at hswap
  have h2h1 : (MulAut.conj D.u).toMonoidHom D.h2 = D.h1 := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, D.u_inv]
    change D.u * D.i2 hM * D.u = D.i1 hM
    have hswap := D.u_conj_i2 hM
    rwa [D.u_inv] at hswap
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (closure {D.h1, D.h2}).map (MulAut.conj D.u).toMonoidHom = closure {D.h1, D.h2}
  rw [MonoidHom.map_closure, Set.image_pair, h1h2, h2h1, Set.pair_comm]

private theorem isPGroup_two_H_sup_zpowers_u [Finite G] :
    IsPGroup 2 (D.H ⊔ zpowers D.u : Subgroup G) :=
  IsPGroup.to_sup_of_normal_left' (H := D.H) (K := zpowers D.u)
    (IsPGroup.of_card (n := 3) (by rw [card_H_eq D]; norm_num))
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, D.orderOf_u]; norm_num))
    (Subgroup.zpowers_le.mpr (u_mem_normalizer_H D))

private theorem R_inf_H_sup_zpowers_u [Finite G] :
    D.R ⊓ (D.H ⊔ zpowers D.u) = ⊥ := by
  refine Subgroup.inf_eq_bot_of_coprime ?_
  haveI : Finite ↥(D.H ⊔ zpowers D.u) := Subtype.finite
  obtain ⟨m, hm⟩ :=
    (IsPGroup.iff_card (p := 2) (G := ↥(D.H ⊔ zpowers D.u))).mp
      (isPGroup_two_H_sup_zpowers_u D)
  rw [card_R_eq D, hm]
  exact Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 25 2)

private theorem card_normalizer_R_of_inf_eq [Finite G]
    (hKR : D.Q ⊓ centralizer (D.R : Set G) = D.R) :
    Nat.card (normalizer (D.R : Set G)) = 25 * Nat.card ↥(D.H ⊔ zpowers D.u) := by
  have hK2N : D.H ⊔ zpowers D.u ≤ normalizer (D.R : Set G) :=
    sup_le ((H_le_normalizer_R_inf_centralizer_t D).trans inf_le_left)
      (Subgroup.zpowers_le.mpr (u_mem_normalizer_R D))
  rw [normalizer_R_eq_of_inf_eq D hKR, sup_assoc,
    CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot hK2N (R_inf_H_sup_zpowers_u D), card_R_eq D]

private theorem Q_inf_centralizer_R_ne_R [Finite G] :
    D.Q ⊓ centralizer (D.R : Set G) ≠ D.R := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hKR
  obtain ⟨M, hMp, hRltM, hMleN⟩ := exists_isPGroup_five_gt_R_le_normalizer_R D
  have hcardNR := card_normalizer_R_of_inf_eq D hKR
  haveI : Finite ↥M := Subtype.finite
  haveI : Finite ↥(D.H ⊔ zpowers D.u) := Subtype.finite
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 5) (G := ↥M)).mp hMp
  obtain ⟨m, hm⟩ :=
    (IsPGroup.iff_card (p := 2) (G := ↥(D.H ⊔ zpowers D.u))).mp
      (isPGroup_two_H_sup_zpowers_u D)
  have hdvd : 5 ^ k ∣ 25 * 2 ^ m := by
    have h := Subgroup.card_dvd_of_le hMleN
    rw [hk, hcardNR, hm] at h
    exact h
  have hcop : Nat.Coprime (5 ^ k) (2 ^ m) :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 5 2)).pow_right m
  have hdvd25 : 5 ^ k ∣ 25 := hcop.dvd_of_dvd_mul_right hdvd
  have hlt : 25 < 5 ^ k := by
    have h := Subgroup.card_lt_of_lt hRltM
    rwa [card_R_eq D, hk] at h
  have hle : 5 ^ k ≤ 25 := Nat.le_of_dvd (by norm_num) hdvd25
  omega

private theorem exists_rho_h1_action [Finite G]
    (hKQ : D.Q ⊓ centralizer (D.R : Set G) = D.Q) :
    ∃ ρ : ZMod 5, D.q3 (.ofAdd ρ) = D.h1⁻¹ * D.q3 (.ofAdd 1) * D.h1 ∧
      ∀ a : ZMod 5,
        D.h1⁻¹ * D.q3 (.ofAdd a) * D.h1 = D.q3 (.ofAdd (ρ * a)) := by
  have h1H : D.h1 ∈ D.H := subset_closure (Set.mem_insert _ _)
  have h1P3 : D.h1⁻¹ * D.q3 (.ofAdd 1) * D.h1 ∈ D.P3 :=
    H_conj_mem_P3_of_inf_eq D hKQ h1H ⟨.ofAdd 1, rfl⟩
  obtain ⟨r, hr⟩ := h1P3
  let ρ : ZMod 5 := r.toAdd
  have hρ : D.q3 (.ofAdd ρ) = D.h1⁻¹ * D.q3 (.ofAdd 1) * D.h1 := by
    simpa [ρ] using hr
  refine ⟨ρ, hρ, ?_⟩
  intro a
  rw [q3_ofAdd_pow D a]
  have hpow : D.h1⁻¹ * (D.q3 (.ofAdd 1)) ^ a.val * D.h1 =
      (D.h1⁻¹ * D.q3 (.ofAdd 1) * D.h1) ^ a.val := by
    simpa [MulAut.conj_apply, inv_inv] using
      map_pow (MulAut.conj (D.h1⁻¹)).toMonoidHom (D.q3 (.ofAdd 1)) a.val
  rw [hpow, ← hρ, q3_pow_mul D ρ a, mul_comm a ρ]

private theorem h2_conj_q3_of_h1_action [Finite G] {ρ : ZMod 5}
    (h1scale : ∀ a : ZMod 5,
      D.h1⁻¹ * D.q3 (.ofAdd a) * D.h1 = D.q3 (.ofAdd (ρ * a))) :
    ∀ a : ZMod 5,
      D.h2⁻¹ * D.q3 (.ofAdd a) * D.h2 = D.q3 (.ofAdd (ρ * a)) := by
  have h2eq : D.h2 = D.u * D.h1 * D.u := by
    have hswap := D.swap hM
    rw [D.u_inv] at hswap
    exact hswap.symm
  intro a
  rw [h2eq]
  calc (D.u * D.h1 * D.u)⁻¹ * D.q3 (.ofAdd a) * (D.u * D.h1 * D.u)
      = D.u * (D.h1⁻¹ * (D.u * D.q3 (.ofAdd a) * D.u) * D.h1) * D.u := by
        simp only [mul_inv_rev, D.u_inv]
        group
    _ = D.u * (D.h1⁻¹ * D.q3 (.ofAdd (-a)) * D.h1) * D.u := by
        rw [show D.u * D.q3 (.ofAdd a) * D.u = D.q3 (.ofAdd (-a)) by
          simpa [D.u_inv] using D.u_conj_q3 a]
    _ = D.u * D.q3 (.ofAdd (ρ * (-a))) * D.u := by rw [h1scale]
    _ = D.q3 (.ofAdd (-(ρ * (-a)))) := by
        simpa [D.u_inv] using D.u_conj_q3 (ρ * (-a))
    _ = D.q3 (.ofAdd (ρ * a)) := by
        congr 1
        ring_nf

private theorem v_conj_q12 [Finite G] (a : ZMod 5) :
    D.v⁻¹ * D.q12 (.ofAdd a) * D.v = D.q12 (.ofAdd (-a)) := by
  rw [show D.v = D.h1 * D.h2 from rfl, D.q12_ofAdd]
  calc (D.h1 * D.h2)⁻¹ * (D.q1 (.ofAdd a) * D.q2 (.ofAdd (-a))) * (D.h1 * D.h2)
      = D.h2⁻¹ * ((D.h1⁻¹ * D.q1 (.ofAdd a) * D.h1) *
          (D.h1⁻¹ * D.q2 (.ofAdd (-a)) * D.h1)) * D.h2 := by group
    _ = D.h2⁻¹ * (D.q1 (.ofAdd (4 * a)) * D.q2 (.ofAdd (-a))) * D.h2 := by
        rw [D.h1_conj_q1, D.h1_conj_q2]
    _ = (D.h2⁻¹ * D.q1 (.ofAdd (4 * a)) * D.h2) *
          (D.h2⁻¹ * D.q2 (.ofAdd (-a)) * D.h2) := by group
    _ = D.q1 (.ofAdd (4 * a)) * D.q2 (.ofAdd (4 * (-a))) := by
        rw [D.h2_conj_q1, D.h2_conj_q2]
    _ = D.q12 (.ofAdd (-a)) := by
        rw [D.q12_ofAdd]
        have h4a : (4 : ZMod 5) * a = -a := by
          rw [show (4 : ZMod 5) = -1 by decide]
          simp
        have h4na : (4 : ZMod 5) * (-a) = a := by
          rw [show (4 : ZMod 5) = -1 by decide]
          simp
        rw [h4a, h4na]
        simp

private theorem v_mul_y_eq_y_mul_v [Finite G] : D.v * D.y = D.y * D.v := by
  have h : D.y⁻¹ * D.v * D.y = D.v := by
    simpa [y] using D.outer.y_conj_v
  calc D.v * D.y = D.y * (D.y⁻¹ * D.v * D.y) := by group
    _ = D.y * D.v := by rw [h]

private theorem v_conj_q3 [Finite G] (a : ZMod 5) :
    D.v⁻¹ * D.q3 (.ofAdd a) * D.v = D.q3 (.ofAdd (-a)) := by
  have hvy := v_mul_y_eq_y_mul_v D
  have hvy_inv : D.v⁻¹ * D.y⁻¹ = D.y⁻¹ * D.v⁻¹ := by
    have h1 : D.y⁻¹ * D.v⁻¹ = D.v⁻¹ * D.y⁻¹ := by
      rw [← mul_inv_rev, hvy, mul_inv_rev]
    exact h1.symm
  rw [D.q3_ofAdd]
  calc D.v⁻¹ * (D.y⁻¹ * D.q12 (.ofAdd a) * D.y) * D.v
      = (D.v⁻¹ * D.y⁻¹) * D.q12 (.ofAdd a) * (D.y * D.v) := by group
    _ = (D.y⁻¹ * D.v⁻¹) * D.q12 (.ofAdd a) * (D.v * D.y) := by rw [hvy_inv, hvy]
    _ = D.y⁻¹ * (D.v⁻¹ * D.q12 (.ofAdd a) * D.v) * D.y := by group
    _ = D.y⁻¹ * D.q12 (.ofAdd (-a)) * D.y := by rw [v_conj_q12]
    _ = D.q3 (.ofAdd (-a)) := by rw [D.q3_ofAdd]

private theorem v_conj_q3_eq_rho_sq [Finite G] {ρ : ZMod 5}
    (h1scale : ∀ a : ZMod 5,
      D.h1⁻¹ * D.q3 (.ofAdd a) * D.h1 = D.q3 (.ofAdd (ρ * a)))
    (h2scale : ∀ a : ZMod 5,
      D.h2⁻¹ * D.q3 (.ofAdd a) * D.h2 = D.q3 (.ofAdd (ρ * a)))
    (a : ZMod 5) :
    D.v⁻¹ * D.q3 (.ofAdd a) * D.v = D.q3 (.ofAdd (ρ * (ρ * a))) := by
  calc D.v⁻¹ * D.q3 (.ofAdd a) * D.v
      = D.h2⁻¹ * (D.h1⁻¹ * D.q3 (.ofAdd a) * D.h1) * D.h2 := by
        rw [show D.v = D.h1 * D.h2 from rfl]
        group
    _ = D.h2⁻¹ * D.q3 (.ofAdd (ρ * a)) * D.h2 := by rw [h1scale]
    _ = D.q3 (.ofAdd (ρ * (ρ * a))) := h2scale (ρ * a)

private theorem rho_sq_eq_neg_one [Finite G] {ρ : ZMod 5}
    (h1scale : ∀ a : ZMod 5,
      D.h1⁻¹ * D.q3 (.ofAdd a) * D.h1 = D.q3 (.ofAdd (ρ * a)))
    (h2scale : ∀ a : ZMod 5,
      D.h2⁻¹ * D.q3 (.ofAdd a) * D.h2 = D.q3 (.ofAdd (ρ * a))) :
    ρ ^ 2 = -1 := by
  have harg : D.q3 (Multiplicative.ofAdd (ρ * (ρ * 1))) =
      D.q3 (Multiplicative.ofAdd (-1)) := by
    rw [← v_conj_q3_eq_rho_sq D h1scale h2scale 1, v_conj_q3 D 1]
  have h := D.q3_injective harg
  have h' : ρ * (ρ * 1) = -1 := Multiplicative.ofAdd.injective (by simpa using h)
  simpa [pow_two] using h'

private theorem exists_rho [Finite G]
    (hKQ : D.Q ⊓ centralizer (D.R : Set G) = D.Q) :
    ∃ ρ : ZMod 5, ρ ^ 2 = -1 ∧ ∀ a : ZMod 5,
      D.h1⁻¹ * D.q3 (.ofAdd a) * D.h1 = D.q3 (.ofAdd (ρ * a)) ∧
      D.h2⁻¹ * D.q3 (.ofAdd a) * D.h2 = D.q3 (.ofAdd (ρ * a)) := by
  obtain ⟨ρ, hρ, h1scale⟩ := exists_rho_h1_action D hKQ
  have h2scale := h2_conj_q3_of_h1_action D h1scale
  exact ⟨ρ, rho_sq_eq_neg_one D h1scale h2scale,
    fun a => ⟨h1scale a, h2scale a⟩⟩

private theorem existsUnique_coordinates [Finite G]
    (hQR : D.Q ≤ centralizer (D.R : Set G)) :
    ∀ g ∈ D.Q, ∃! a : Fin 3 → ZMod 5,
      g = D.q1 (.ofAdd (a 0)) * D.q2 (.ofAdd (a 1)) * D.q3 (.ofAdd (a 2)) := by
  classical
  let φ : (Fin 3 → ZMod 5) → D.Q := fun a =>
    ⟨D.q1 (.ofAdd (a 0)) * D.q2 (.ofAdd (a 1)) * D.q3 (.ofAdd (a 2)), by
      exact D.Q.mul_mem (D.Q.mul_mem (P1_le_Q D ⟨_, rfl⟩) (P2_le_Q D ⟨_, rfl⟩))
        (P3_le_Q D ⟨_, rfl⟩)⟩
  have hsurj : Function.Surjective φ := by
    intro g
    have hg : (g : G) ∈ (D.Q : Set G) := g.2
    rw [Q_set_eq_P1P2P3_of_centralizes D hQR, Set.mem_mul] at hg
    obtain ⟨u, hu, p3, hp3, hg_eq⟩ := hg
    rw [Set.mem_mul] at hu
    obtain ⟨p1, hp1, p2, hp2, hu_eq⟩ := hu
    obtain ⟨a0, ha0⟩ := hp1
    obtain ⟨a1, ha1⟩ := hp2
    obtain ⟨a2, ha2⟩ := hp3
    refine ⟨![a0.toAdd, a1.toAdd, a2.toAdd], ?_⟩
    apply Subtype.ext
    show D.q1 a0 * D.q2 a1 * D.q3 a2 = (g : G)
    rw [ha0, ha1, ha2, hu_eq, hg_eq]
  have hcard : Nat.card (Fin 3 → ZMod 5) = Nat.card D.Q := by
    rw [show Nat.card D.Q = 125 from (odd_complement_of_diagonal_centralizer D).1]
    simp
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_surjective_and_card φ).mpr ⟨hsurj, hcard⟩
  intro g hg
  obtain ⟨a, ha, huniq⟩ := (Function.bijective_iff_existsUnique φ).mp hbij ⟨g, hg⟩
  refine ⟨a, ?_, ?_⟩
  · exact (congrArg Subtype.val ha).symm
  · intro b hb
    exact huniq b (Subtype.ext hb.symm)

theorem elementary_abelian_three_space [Finite G] :
    (∀ x ∈ D.Q, x ^ 5 = 1) ∧ (∀ x ∈ D.Q, ∀ x' ∈ D.Q, Commute x x') ∧
    centralizer (D.Q : Set G) = D.Q ∧ normalizer (D.R : Set G) ≤ normalizer (D.Q : Set G) ∧
    (∀ g ∈ D.Q, ∃! a : Fin 3 → ZMod 5,
      g = D.q1 (.ofAdd (a 0)) * D.q2 (.ofAdd (a 1)) * D.q3 (.ofAdd (a 2))) ∧
    ∃ ρ : ZMod 5, ρ ^ 2 = -1 ∧ ∀ a : ZMod 5,
      D.h1⁻¹ * D.q3 (.ofAdd a) * D.h1 = D.q3 (.ofAdd (ρ * a)) ∧
      D.h2⁻¹ * D.q3 (.ofAdd a) * D.h2 = D.q3 (.ofAdd (ρ * a)) := by
  classical
  have hQcard : Nat.card D.Q = 125 := (odd_complement_of_diagonal_centralizer D).1
  set K : Subgroup G := D.Q ⊓ centralizer (D.R : Set G) with hKdef
  have hRleK : D.R ≤ K := le_inf (R_le_Q D) (R_le_centralizer_R D)
  have hKleQ : K ≤ D.Q := inf_le_left
  have hKcases : Nat.card K = 25 ∨ Nat.card K = 125 := by
    have h25 : 25 ∣ Nat.card K := by
      have h := Subgroup.card_dvd_of_le hRleK
      rwa [card_R_eq D] at h
    have h125 : Nat.card K ∣ 125 := by
      have h := Subgroup.card_dvd_of_le hKleQ
      rwa [hQcard] at h
    obtain ⟨m, hm⟩ := h25
    have hm5 : m ∣ 5 := by
      have h : 25 * m ∣ 125 := by rwa [← hm]
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 25)).mp (by simpa using h)
    rcases (Nat.dvd_prime Nat.prime_five).mp hm5 with hm1 | hm5
    · left
      rw [hm, hm1, mul_one]
    · right
      rw [hm, hm5]
  by_cases hKR : K = D.R
  · exact (Q_inf_centralizer_R_ne_R D (by rwa [hKdef] at hKR)).elim
  · have hKQ : K = D.Q := by
      rcases hKcases with h25 | h125
      · exfalso
        apply hKR
        exact (Subgroup.eq_of_le_of_card_ge hRleK (by rw [h25, card_R_eq D])).symm
      · exact Subgroup.eq_of_le_of_card_ge hKleQ (by rw [h125, hQcard])
    have hQR : D.Q ≤ centralizer (D.R : Set G) := by
      rw [← hKQ]
      exact inf_le_right
    have hcommQ : ∀ x ∈ D.Q, ∀ x' ∈ D.Q, Commute x x' :=
      fun x hx x' hx' => commute_of_mem_Q D hQR hx hx'
    have hpowQ : ∀ x ∈ D.Q, x ^ 5 = 1 :=
      fun x hx => pow_five_of_mem_Q D hQR hx
    refine ⟨hpowQ, hcommQ, centralizer_Q_eq_of_inf_eq D hKQ,
      normalizer_R_le_normalizer_Q_of_inf_eq D hKQ, existsUnique_coordinates D hQR, ?_⟩
    obtain ⟨ρ, hρ2, hρ⟩ := exists_rho D hKQ
    exact ⟨ρ, hρ2, hρ⟩

end CFSG.OddTranspositions.PartThree.Wong.RootData
