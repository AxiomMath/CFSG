module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.SzN31

namespace SmD6GrpB

theorem mul_comm_of_card_dvd_nine {H : Type*} [Group H] (h : Nat.card H ∣ 9) (a b : H) :
    a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm, hmcard⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).1 (show Nat.card H ∣ 3 ^ 2 by simpa using h)
  interval_cases m
  · have hone : Nat.card H = 1 := by simpa using hmcard
    have : Subsingleton H := (Nat.card_eq_one_iff_unique.1 hone).1
    exact Subsingleton.elim _ _
  · have : IsCyclic H := isCyclic_of_prime_card (p := 3) (by simpa using hmcard)
    exact (inferInstance : IsMulCommutative H).is_comm.comm a b
  · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hmcard).is_comm.comm a b

theorem card_center_eq_three {G : Type*} [Group G] (hG : Nat.card G = 27)
    (hnc : ∃ u v : G, u * v ≠ v * u) : Nat.card (Subgroup.center G) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨u, v, huv⟩ := hnc
  have : Nontrivial G := ⟨⟨u, v, fun h => huv (h ▸ rfl)⟩⟩
  have hP : IsPGroup 3 G := IsPGroup.of_card (n := 3) (by rw [hG]; norm_num)
  have := hP.center_nontrivial
  have hdvd : Nat.card (Subgroup.center G) ∣ 3 ^ 3 := by
    simpa [hG] using Subgroup.card_subgroup_dvd_card (Subgroup.center G)
  obtain ⟨m, hm, hmcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have h1 : 1 < Nat.card (Subgroup.center G) := Finite.one_lt_card_iff_nontrivial.2 inferInstance
  interval_cases m
  · rw [pow_zero] at hmcard
    omega
  · simpa using hmcard
  · exfalso
    have hq : Nat.card (G ⧸ Subgroup.center G) = 3 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
      rw [hG, hmcard] at h
      omega
    have : IsCyclic (G ⧸ Subgroup.center G) := isCyclic_of_prime_card hq
    have hcomm :=
      (QuotientGroup.mk' (Subgroup.center G)).isMulCommutative_of_isCyclic_of_ker_le_center
        (by rw [QuotientGroup.ker_mk'])
    exact huv (hcomm.is_comm.comm u v)
  · exfalso
    have htop : Subgroup.center G = ⊤ :=
      (Subgroup.card_eq_iff_eq_top _).1 (by rw [hmcard, hG]; norm_num)
    have hu : u ∈ Subgroup.center G := htop ▸ Subgroup.mem_top u
    exact huv (Subgroup.mem_center_iff.1 hu v).symm

theorem card_centralizer_eq_nine {G : Type*} [Group G] (hG : Nat.card G = 27)
    (hnc : ∃ u v : G, u * v ≠ v * u) {u : G} (hu : u ∉ Subgroup.center G) :
    Nat.card (Subgroup.centralizer ({u} : Set G)) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have hZ := card_center_eq_three hG hnc
  have hle : Subgroup.center G ≤ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.center_le_centralizer _
  have h3 : 3 ∣ Nat.card (Subgroup.centralizer ({u} : Set G)) := by
    simpa [hZ] using Subgroup.card_dvd_of_le hle
  have hdvd : Nat.card (Subgroup.centralizer ({u} : Set G)) ∣ 3 ^ 3 := by
    simpa [hG] using Subgroup.card_subgroup_dvd_card (Subgroup.centralizer ({u} : Set G))
  obtain ⟨m, hm, hmcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have huC : u ∈ Subgroup.centralizer ({u} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  interval_cases m
  · rw [pow_zero] at hmcard
    omega
  · exfalso
    have heq : Subgroup.center G = Subgroup.centralizer ({u} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hmcard, hZ]; norm_num)
    exact hu (heq ▸ huC)
  · simpa using hmcard
  · exfalso
    have htop : Subgroup.centralizer ({u} : Set G) = ⊤ :=
      (Subgroup.card_eq_iff_eq_top _).1 (by rw [hmcard, hG]; norm_num)
    apply hu
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({u} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.1 hg

theorem closure_pair_eq_top {G : Type*} [Group G] (hG : Nat.card G = 27) {u v : G}
    (huv : u * v ≠ v * u) : Subgroup.closure ({u, v} : Set G) = ⊤ := by
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  by_contra hne
  have hd : Nat.card (Subgroup.closure ({u, v} : Set G)) ∣ 3 ^ 3 := by
    simpa [hG] using Subgroup.card_subgroup_dvd_card (Subgroup.closure ({u, v} : Set G))
  obtain ⟨m, hm, hmc⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  have hm3 : m ≠ 3 := by
    rintro rfl
    exact hne ((Subgroup.card_eq_iff_eq_top _).1 (by rw [hmc, hG]; norm_num))
  have hcard : Nat.card (Subgroup.closure ({u, v} : Set G)) ∣ 9 := by
    rw [hmc]
    exact (pow_dvd_pow 3 (by omega : m ≤ 2)).trans (by norm_num)
  have huH : u ∈ Subgroup.closure ({u, v} : Set G) := Subgroup.subset_closure (by simp)
  have hvH : v ∈ Subgroup.closure ({u, v} : Set G) := Subgroup.subset_closure (by simp)
  exact huv (congrArg Subtype.val (mul_comm_of_card_dvd_nine hcard ⟨u, huH⟩ ⟨v, hvH⟩))

theorem card_not_mem_add_card {G : Type*} [Group G] [Finite G] (C : Subgroup G) :
    Nat.card {v : G // v ∉ C} + Nat.card C = Nat.card G := by
  have h := Set.ncard_compl_add_ncard (C : Set G)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h
  exact h

theorem card_noncommuting_pairs {G : Type*} [Group G] (hG : Nat.card G = 27)
    (hnc : ∃ u v : G, u * v ≠ v * u) :
    Nat.card {p : G × G // p.1 * p.2 ≠ p.2 * p.1} = 432 := by
  classical
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype G := Fintype.ofFinite G
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun u v : G => u * v ≠ v * u),
    Nat.card_sigma]
  have hfib : ∀ u : G,
      Nat.card {v : G // u * v ≠ v * u} = if u ∈ Subgroup.center G then 0 else 18 := by
    intro u
    split_ifs with hu
    · have : IsEmpty {v : G // u * v ≠ v * u} :=
        ⟨fun v => v.2 (Subgroup.mem_center_iff.1 hu v.1).symm⟩
      exact Nat.card_of_isEmpty
    · have hC := card_centralizer_eq_nine hG hnc hu
      have e : {v : G // u * v ≠ v * u} ≃ {v : G // v ∉ Subgroup.centralizer ({u} : Set G)} :=
        Equiv.subtypeEquivRight fun v => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact ne_comm
      rw [Nat.card_congr e]
      have h := card_not_mem_add_card (Subgroup.centralizer ({u} : Set G))
      omega
  simp_rw [hfib]
  have hZ := card_center_eq_three hG hnc
  have h := card_not_mem_add_card (Subgroup.center G)
  rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, smul_eq_mul]
  have hcard : (Finset.univ.filter fun u : G => u ∉ Subgroup.center G).card = 24 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    omega
  rw [hcard]

theorem index_dvd_card_of_stabilizer_eq {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [Finite X] (H : Subgroup G) (hH : ∀ x : X, MulAction.stabilizer G x = H) :
    H.index ∣ Nat.card X := by
  have : Finite (Quotient (MulAction.orbitRel G X)) := Quotient.finite _
  have : Fintype (Quotient (MulAction.orbitRel G X)) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer G X), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  rw [hH, ← Subgroup.index_eq_card]

section Action

variable {Γ : Type*} [Group Γ] (P : Subgroup Γ) [P.Normal]

abbrev NCPairs : Type _ := {p : P × P // p.1 * p.2 ≠ p.2 * p.1}

instance : SMul Γ (NCPairs P) where
  smul γ p := ⟨(MulAut.conjNormal γ p.1.1, MulAut.conjNormal γ p.1.2), fun h =>
    p.2 ((MulAut.conjNormal γ).injective (by rw [map_mul, map_mul]; exact h))⟩

@[simp] theorem smul_fst (γ : Γ) (p : NCPairs P) :
    (γ • p).1.1 = MulAut.conjNormal γ p.1.1 := rfl

@[simp] theorem smul_snd (γ : Γ) (p : NCPairs P) :
    (γ • p).1.2 = MulAut.conjNormal γ p.1.2 := rfl

instance : MulAction Γ (NCPairs P) where
  one_smul p := Subtype.ext (Prod.ext (by simp) (by simp))
  mul_smul γ δ p := Subtype.ext (Prod.ext (by simp) (by simp))

theorem mem_stabilizer_iff (γ : Γ) (p : NCPairs P) :
    γ ∈ MulAction.stabilizer Γ p ↔ γ * p.1.1 = p.1.1 * γ ∧ γ * p.1.2 = p.1.2 * γ := by
  rw [MulAction.mem_stabilizer_iff]
  have key : ∀ x : P, MulAut.conjNormal γ x = x ↔ γ * x = x * γ := fun x => by
    rw [Subtype.ext_iff, MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul]
  constructor
  · intro h
    have h' : (MulAut.conjNormal γ p.1.1, MulAut.conjNormal γ p.1.2) = p.1 :=
      congrArg Subtype.val h
    exact ⟨(key _).1 (congrArg Prod.fst h'), (key _).1 (congrArg Prod.snd h')⟩
  · rintro ⟨h1, h2⟩
    exact Subtype.ext (Prod.ext ((key _).2 h1) ((key _).2 h2))

def centerImage : Subgroup Γ := (Subgroup.center P).map P.subtype

theorem stabilizer_eq (hP : Nat.card P = 27)
    (hC : ∀ g : Γ, (∀ x ∈ P, g * x = x * g) → g ∈ P) (p : NCPairs P) :
    MulAction.stabilizer Γ p = centerImage P := by
  ext γ
  rw [mem_stabilizer_iff]
  constructor
  · rintro ⟨ha, hb⟩
    have hall : ∀ x ∈ P, γ * x = x * γ := by
      intro x hx
      have hgen := closure_pair_eq_top hP p.2
      have hx' : (⟨x, hx⟩ : P) ∈ Subgroup.closure ({p.1.1, p.1.2} : Set P) := by
        rw [hgen]
        exact Subgroup.mem_top _
      have hle : Subgroup.closure ({p.1.1, p.1.2} : Set P) ≤
          (Subgroup.centralizer ({γ} : Set Γ)).comap P.subtype := by
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        · exact Subgroup.mem_centralizer_singleton_iff.2 ha.symm
        · exact Subgroup.mem_centralizer_singleton_iff.2 hb.symm
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx')).symm
    exact ⟨⟨γ, hC γ hall⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hall g g.2).symm, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨congrArg Subtype.val (Subgroup.mem_center_iff.1 hz p.1.1).symm,
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hz p.1.2).symm⟩

omit [P.Normal] in
theorem card_centerImage (hP : Nat.card P = 27) (hnc : ∃ u v : P, u * v ≠ v * u) :
    Nat.card (centerImage P) = 3 := by
  rw [centerImage, Subgroup.card_map_of_injective P.subtype_injective]
  exact card_center_eq_three hP hnc

end Action

end SmD6GrpB

theorem index_dvd_forty_eight {Γ : Type*} [Group Γ] [Finite Γ] (P : Subgroup Γ) [P.Normal]
    (hP : Nat.card P = 27) (hnc : ∃ u ∈ P, ∃ v ∈ P, u * v ≠ v * u)
    (hC : ∀ g : Γ, (∀ x ∈ P, g * x = x * g) → g ∈ P) :
    P.index ∣ 48 := by
  have hnc' : ∃ u v : P, u * v ≠ v * u := by
    obtain ⟨u, hu, v, hv, h⟩ := hnc
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, fun h' => h (congrArg Subtype.val h')⟩
  have hdvd : (SmD6GrpB.centerImage P).index ∣ Nat.card (SmD6GrpB.NCPairs P) :=
    SmD6GrpB.index_dvd_card_of_stabilizer_eq _ (SmD6GrpB.stabilizer_eq P hP hC)
  rw [SmD6GrpB.card_noncommuting_pairs hP hnc'] at hdvd
  have h1 := Subgroup.index_mul_card (SmD6GrpB.centerImage P)
  have h2 := Subgroup.index_mul_card P
  rw [SmD6GrpB.card_centerImage P hP hnc'] at h1
  rw [hP] at h2
  have h3 : (SmD6GrpB.centerImage P).index = 9 * P.index := by omega
  rw [h3] at hdvd
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 9) (show 9 * P.index ∣ 9 * 48 from hdvd)

end CFSG.Quasithin.SzN31
