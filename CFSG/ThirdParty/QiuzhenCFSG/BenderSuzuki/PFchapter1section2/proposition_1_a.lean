module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_6_b

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section2

open PFchapter1section1 PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 2, Proposition 1(a)
-/

private theorem proposition_1_a_exists_involution_of_even_card
    {G : Type*} [Group G] [Finite G] (L : Subgroup G)
    (hL_even : Even (Nat.card L)) :
    ∃ u : G, u ∈ L ∧ IsInvolution u := by
  classical
  have hL_even_card : Even (Nat.card L) := by
    simpa [Nat.card, Nat.card_coe_set_eq] using hL_even
  have htwo_dvd_card : 2 ∣ Nat.card L := even_iff_two_dvd.mp hL_even_card
  obtain ⟨u, hu_order⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 htwo_dvd_card
  refine ⟨u, u.property, ?_⟩
  constructor
  · intro hu_one
    have horder_one : orderOf u = 1 := by
      have : u = 1 := by
        ext
        exact hu_one
      simp [this]
    omega
  · have hpow : u ^ 2 = 1 := by
      simpa [hu_order] using pow_orderOf_eq_one u
    exact congrArg Subtype.val hpow

private theorem proposition_1_a_peterfalviKSet_one
    {G : Type*} [Group G] {D : Subgroup G} {t : G} :
    (1 : G) ∈ peterfalviKSet D t := by
  simp [peterfalviKSet, rightConjugateElem]

private theorem proposition_1_a_rightConjugate_self_of_mem_centralizer
    {G : Type*} [Group G] {X : Set G} {u x : G}
    (huC : u ∈ Subgroup.centralizer X) (hx : x ∈ X) :
    rightConjugateElem u x = u := by
  have hcomm : x * u = u * x :=
    (Subgroup.mem_centralizer_iff.mp huC) x hx
  calc
    rightConjugateElem u x = x⁻¹ * (u * x) := by
      rw [rightConjugateElem, mul_assoc]
    _ = x⁻¹ * (x * u) := by rw [← hcomm]
    _ = u := by group

private theorem proposition_1_a_map_K_to_involutions_injective
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t s : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s) :
    Function.Injective
      (fun k : {x : G // x ∈ peterfalviKSet D t} =>
        (⟨rightConjugateElem s (k : G),
          ((proposition_3 H D Q t hA1).2 s hsH hsI
              (rightConjugateElem s (k : G))).2
            ⟨k, k.property, rfl⟩⟩ :
          {x : G // x ∈ H ∧ IsInvolution x})) := by
  classical
  let S : Set G := {x : G | x ∈ H ∧ IsInvolution x}
  let phi : {x : G // x ∈ peterfalviKSet D t} → {x : G // x ∈ S} := fun k =>
    ⟨rightConjugateElem s (k : G), by
      simpa [S] using
        ((proposition_3 H D Q t hA1).2 s hsH hsI
            (rightConjugateElem s (k : G))).2
          ⟨k, k.property, rfl⟩⟩
  have hphi_surj : Function.Surjective phi := by
    rintro ⟨y, hyS⟩
    rcases ((proposition_3 H D Q t hA1).2 s hsH hsI y).1
        (by simpa [S] using hyS) with
      ⟨k, hkK, hk_eq⟩
    refine ⟨⟨k, hkK⟩, ?_⟩
    apply Subtype.ext
    simpa [phi, S] using hk_eq
  have hphi_inj : Function.Injective phi := by
    exact
      (hphi_surj.bijective_of_nat_card_le
        (by simpa [S] using le_of_eq (proposition_3 H D Q t hA1).1)).1
  intro x y hxy
  apply hphi_inj
  apply Subtype.ext
  exact congrArg Subtype.val hxy

private theorem proposition_1_a_fixed_cover_of_card_le_two
    {G Ω : Type*} [Group G] [MulAction G Ω] [Finite Ω]
    {X : Subgroup G} {a b z : Ω}
    (ha : a ∈ fixedPointsOfSubgroup G Ω X)
    (hb : b ∈ fixedPointsOfSubgroup G Ω X)
    (hz : z ∈ fixedPointsOfSubgroup G Ω X)
    (hab : a ≠ b)
    (hcard : Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X} ≤ 2) :
    z = a ∨ z = b := by
  classical
  by_contra hcover
  have hza : z ≠ a := by
    intro h
    exact hcover (Or.inl h)
  have hzb : z ≠ b := by
    intro h
    exact hcover (Or.inr h)
  let Fixed : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}
  let pa : Fixed := ⟨a, ha⟩
  let pb : Fixed := ⟨b, hb⟩
  let pz : Fixed := ⟨z, hz⟩
  have hcardFixed_le : Nat.card Fixed ≤ 2 := by
    simpa [Fixed] using hcard
  have hpa_ne_pb : pa ≠ pb := by
    intro h
    exact hab (congrArg Subtype.val h)
  have hpa_ne_pz : pa ≠ pz := by
    intro h
    exact hza (congrArg Subtype.val h).symm
  have hpb_ne_pz : pb ≠ pz := by
    intro h
    exact hzb (congrArg Subtype.val h).symm
  let f : Fin 3 → Fixed := fun i =>
    if i = 0 then pa else if i = 1 then pb else pz
  have hf_inj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, hpa_ne_pb, hpa_ne_pb.symm, hpa_ne_pz, hpa_ne_pz.symm,
        hpb_ne_pz, hpb_ne_pz.symm] at hij ⊢
  have hthree_le : 3 ≤ Nat.card Fixed := by
    haveI : Fintype Fixed := Fintype.ofFinite Fixed
    have hle := Fintype.card_le_of_injective f hf_inj
    simpa [Nat.card_eq_fintype_card] using hle
  omega

private theorem proposition_1_a_base_ne_t_inv_base
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t : G} (hA1 : HypothesisA1 G Ω H D Q t)
    {base : Ω} (hHbase : H = MulAction.stabilizer G base) :
    base ≠ t⁻¹ • base := by
  intro h
  have ht_inv_H : t⁻¹ ∈ H := by
    have ht_inv_stab : t⁻¹ ∈ MulAction.stabilizer G base := h.symm
    simpa [hHbase] using ht_inv_stab
  have htH : t ∈ H := by
    simpa using H.inv_mem ht_inv_H
  exact hA1.t_not_mem_H htH

private theorem proposition_1_a_D_fixes_base
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t d : G} (hA1 : HypothesisA1 G Ω H D Q t)
    {base : Ω} (hHbase : H = MulAction.stabilizer G base) (hd : d ∈ D) :
    d • base = base := by
  have hdH : d ∈ H := hA1.D_le_H hd
  have hdstab : d ∈ MulAction.stabilizer G base := by
    simpa [hHbase] using hdH
  simpa using hdstab

private theorem proposition_1_a_D_fixes_t_inv_base
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t d : G} (hA1 : HypothesisA1 G Ω H D Q t)
    {base : Ω} (hHbase : H = MulAction.stabilizer G base) (hd : d ∈ D) :
    d • (t⁻¹ • base) = t⁻¹ • base := by
  have hd' : d ∈ H ⊓ rightConjugate H t := by
    simpa [hA1.D_eq] using hd
  have hconj :
      rightConjugate H t = MulAction.stabilizer G (t⁻¹ • base) := by
    rw [hHbase]
    exact rightConjugate_stabilizer base t
  have hdstab : d ∈ MulAction.stabilizer G (t⁻¹ • base) := by
    simpa [hconj] using hd'.2
  simpa using hdstab

private theorem proposition_1_a_mem_fixed_of_mem_closure_singleton
    {G Ω : Type*} [Group G] [MulAction G Ω]
    {x g : G} {ω : Ω}
    (hgx : Commute g x) (hxω : x • ω = ω) :
    g • ω ∈ fixedPointsOfSubgroup G Ω (Subgroup.closure ({x} : Set G)) := by
  have hx_fixed : x • (g • ω) = g • ω := by
    calc
      x • (g • ω) = (x * g) • ω := by
        rw [mul_smul]
      _ = (g * x) • ω := by
        rw [← hgx.eq]
      _ = g • (x • ω) := by
        rw [mul_smul]
      _ = g • ω := by rw [hxω]
  have hclosure_le :
      Subgroup.closure ({x} : Set G) ≤ MulAction.stabilizer G (g • ω) := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl
    exact hx_fixed
  intro y hy
  exact hclosure_le hy

private theorem proposition_1_a_fixed_points_le_two_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA1 : HypothesisA1 G Ω H D Q t) :
    ∀ x : G, x ∈ peterfalviKSet D t → x ≠ 1 →
      Nat.card
          {ω : Ω // ω ∈
            fixedPointsOfSubgroup G Ω (Subgroup.closure ({x} : Set G))} ≤ 2 := by
  classical
  intro x hxK hxne
  by_contra hnot
  have hfixed :
      3 ≤ Nat.card
          {ω : Ω // ω ∈
            fixedPointsOfSubgroup G Ω (Subgroup.closure ({x} : Set G))} := by
    omega
  have hX_le_D : Subgroup.closure ({x} : Set G) ≤ D := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl
    exact hxK.1
  let C : Subgroup G :=
    Subgroup.centralizer (((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G))
  have hCQ_even : Even (Nat.card (α := (((C : Subgroup G) ⊓ Q : Subgroup G)))) := by
    simpa [C] using proposition_6_b H D Q (Subgroup.closure ({x} : Set G)) t hA1 hX_le_D
      hfixed
  rcases
    proposition_1_a_exists_involution_of_even_card
      ((C : Subgroup G) ⊓ Q)
      hCQ_even with
    ⟨u, huCQ, huI⟩
  have huH : u ∈ H := hA1.Q_le_H huCQ.2
  have hx_mem_closure : x ∈ Subgroup.closure ({x} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hux : rightConjugateElem u x = u :=
    proposition_1_a_rightConjugate_self_of_mem_centralizer huCQ.1 hx_mem_closure
  have hphi_inj :=
    proposition_1_a_map_K_to_involutions_injective H D Q t u hA1 huH huI
  have honeK : (1 : G) ∈ peterfalviKSet D t :=
    proposition_1_a_peterfalviKSet_one
  have hx_eq_one_sub :
      (⟨x, hxK⟩ : {x : G // x ∈ peterfalviKSet D t}) = ⟨1, honeK⟩ := by
    apply hphi_inj
    apply Subtype.ext
    simpa [hux, rightConjugateElem]
  exact hxne (congrArg Subtype.val hx_eq_one_sub)

private theorem proposition_1_a_centralizer_Q_bot_of_fixed_points_le_two_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA1 : HypothesisA1 G Ω H D Q t) :
    ∀ x : G, x ∈ peterfalviKSet D t → x ≠ 1 →
      Nat.card
          {ω : Ω // ω ∈
            fixedPointsOfSubgroup G Ω (Subgroup.closure ({x} : Set G))} ≤ 2 →
        Subgroup.centralizer ({x} : Set G) ⊓ Q = ⊥ := by
  classical
  intro x hxK hxne hfixed_le
  rw [eq_bot_iff]
  intro y hy
  have hxD : x ∈ D := hxK.1
  obtain ⟨base, hHbase⟩ := hA1.point_stabilizer
  let beta : Ω := t⁻¹ • base
  have hbase_fixed :
      base ∈ fixedPointsOfSubgroup G Ω (Subgroup.closure ({x} : Set G)) := by
    have hclosure_le :
        Subgroup.closure ({x} : Set G) ≤ MulAction.stabilizer G base := by
      rw [Subgroup.closure_le]
      intro z hz
      rcases hz with rfl
      exact proposition_1_a_D_fixes_base hA1 hHbase hxD
    intro z hz
    exact hclosure_le hz
  have hbeta_fixed :
      beta ∈ fixedPointsOfSubgroup G Ω (Subgroup.closure ({x} : Set G)) := by
    have hclosure_le :
        Subgroup.closure ({x} : Set G) ≤ MulAction.stabilizer G beta := by
      rw [Subgroup.closure_le]
      intro z hz
      rcases hz with rfl
      exact proposition_1_a_D_fixes_t_inv_base hA1 hHbase hxD
    intro z hz
    exact hclosure_le hz
  have hbase_ne_beta : base ≠ beta :=
    proposition_1_a_base_ne_t_inv_base hA1 hHbase
  have hyH : y ∈ H := hA1.Q_le_H hy.2
  have hy_base : y • base = base := by
    have hystab : y ∈ MulAction.stabilizer G base := by
      simpa [hHbase] using hyH
    simpa using hystab
  have hy_comm_x : Commute y x := by
    exact Subgroup.mem_centralizer_singleton_iff.mp hy.1
  have hy_beta_fixed :
      y • beta ∈ fixedPointsOfSubgroup G Ω (Subgroup.closure ({x} : Set G)) := by
    exact proposition_1_a_mem_fixed_of_mem_closure_singleton hy_comm_x
      (proposition_1_a_D_fixes_t_inv_base hA1 hHbase hxD)
  have hy_beta_cases :
      y • beta = base ∨ y • beta = beta :=
    proposition_1_a_fixed_cover_of_card_le_two hbase_fixed hbeta_fixed hy_beta_fixed
      hbase_ne_beta hfixed_le
  have hy_beta : y • beta = beta := by
    rcases hy_beta_cases with hyb | hyb
    · exfalso
      have hpre : y⁻¹ • (y • beta) = y⁻¹ • (y • base) := by
        rw [hyb, hy_base]
      have hbeta_base : beta = base := by
        simpa [smul_smul] using hpre
      exact hbase_ne_beta hbeta_base.symm
    · exact hyb
  have hy_right : y ∈ rightConjugate H t := by
    have hy_stab : y ∈ MulAction.stabilizer G beta := by
      simpa using hy_beta
    have hconj :
        rightConjugate H t = MulAction.stabilizer G beta := by
      dsimp [beta]
      rw [hHbase]
      exact rightConjugate_stabilizer base t
    simpa [hconj] using hy_stab
  have hyD : y ∈ D := by
    rw [hA1.D_eq]
    exact ⟨hyH, hy_right⟩
  have hy_bot : y ∈ (⊥ : Subgroup G) := by
    have hyQD : y ∈ Q ⊓ D := ⟨hy.2, hyD⟩
    exact hA1.Q_disjoint_D.le_bot hyQD
  simpa using hy_bot

public theorem proposition_1_a_of_mem_peterfalviKSet
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA1 : HypothesisA1 G Ω H D Q t) :
    ∀ x : G, x ∈ peterfalviKSet D t → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ⊓ Q = ⊥ := by
  exact fun x hxK hxne =>
    proposition_1_a_centralizer_Q_bot_of_fixed_points_le_two_obligation
      H D Q t hA1 x hxK hxne
      (proposition_1_a_fixed_points_le_two_obligation H D Q t hA1 x hxK hxne)

public theorem proposition_1_a
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q)) :
    ∀ x : G, x ∈ K → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ⊓ Q = ⊥ := by
  exact fun x hxK hxne =>
    proposition_1_a_of_mem_peterfalviKSet H D Q t hsec.hA.A1 x
      ((hsec.K_def x).mp hxK) hxne

end PFchapter1section2
end CFSG.BenderSuzuki
