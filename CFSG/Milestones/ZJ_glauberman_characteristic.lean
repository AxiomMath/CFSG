module

public import CFSG.Adapters.GlaubermanZJ

public section

universe u v w

namespace CFSG.Open

open CFSG.Open in
theorem _root_.CFSG.Milestones.zj_glauberman_characteristic_1
    (G : Type) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hcharp : Subgroup.centralizer (pCore p G : Set G) ≤ pCore p G)
    (S : Sylow p G)
    (hstable : ∀ (P : Subgroup G) [P.Normal], IsPGroup p P → StatedConjPStable p P) :
    ((Subgroup.center (thompsonSubgroup (S : Subgroup G))).map
        (thompsonSubgroup (S : Subgroup G)).subtype).Characteristic := by
  exact CFSG.Adapters.glauberman_zj_characteristic G p hp hodd hcharp S hstable

end CFSG.Open

namespace CFSG.Adapters

open scoped commutatorElement

theorem _root_.CFSG.Milestones.zj_glauberman_characteristic_2
    (G : Type) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hstable : CFSG.Open.IsPStable p G)
    (hconstrained : Subgroup.centralizer (CFSG.Open.pCore p G : Set G) ≤ CFSG.Open.pCore p G)
    (S : Sylow p G) :
    ((Subgroup.center (CFSG.Open.thompsonSubgroup (S : Subgroup G))).map
        (CFSG.Open.thompsonSubgroup (S : Subgroup G)).subtype).Normal := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  rw [leanEval_thompsonSubgroup_eq, ← centerIn_eq_map_center]
  change (thompsonCenter (G := G) (S : Subgroup G)).Normal
  have hbot : pPrimeCore p G = ⊥ := by
    have hle : pPrimeCore p G ≤ pCore p G :=
      (pPrimeCore_le_centralizer_of_normal_pgroup (G := G) p (pCore p G)
        (pCore_isPGroup (G := G) (p := p))).trans hconstrained
    obtain ⟨n, hcard⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (G := G) (p := p))
    have hcoprime : Nat.Coprime (Nat.card (pCore p G)) (Nat.card (pPrimeCore p G)) := by
      rw [hcard]
      exact (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n
    have hinf : pCore p G ⊓ pPrimeCore p G = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard hcoprime).eq_bot
    rwa [inf_eq_right.mpr hle] at hinf
  by_cases hOp : pCore p G = ⊥
  ·
    have hall : ∀ x : G, x = 1 := by
      intro x
      have hx : x ∈ Subgroup.centralizer (pCore p G : Set G) := by
        rw [hOp]
        exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
          simp [hh]
      simpa [hOp] using hconstrained hx
    have hZ : thompsonCenter (G := G) (S : Subgroup G) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).2 fun x _ => hall x
    rw [hZ]
    infer_instance
  have hpodd : p ≠ 2 := by
    rintro rfl
    exact absurd hodd (by decide)
  have hOp'p : Op_p'p p G = pCore p G := Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := G) (p := p) hbot
  have hconstrained : PConstrainedGroup (G := G) p := by
    intro Q _ hQ
    rw [hOp'p, hbot, bot_sup_eq] at hQ
    rw [hOp'p, hQ]
    exact hconstrained
  have hstable' : PStableGroup' (G := G) p := by
    intro Q A _hQn hQp hAp hAN hcomm
    let N : Subgroup G := Subgroup.normalizer (Q : Set G)
    let C : Subgroup G := Subgroup.centralizer (Q : Set G)
    have hCN : C ≤ N := by
      simpa using (centralizer_le_normalizer (G := G) Q)
    have : (C.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (H := C) (K := N) hCN).2
        (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (X := G) Q)
    let q := QuotientGroup.mk' (C.subgroupOf N)
    rw [Subgroup.map_le_iff_le_comap]
    intro a ha
    have haA : (a : G) ∈ A := ha
    obtain ⟨k, hk⟩ := hAp ⟨a, haA⟩
    have haPow : (a : G) ^ p ^ k = 1 := congrArg Subtype.val hk
    have hquad : ∀ y ∈ Q,
        (y * (a : G) * y⁻¹ * (a : G)⁻¹) * a =
          a * (y * (a : G) * y⁻¹ * (a : G)⁻¹) := by
      intro y hy
      have hm : ⁅⁅y, (a : G)⁆, (a : G)⁆ ∈ ⁅⁅Q, A⁆, A⁆ :=
        Subgroup.commutator_mem_commutator
          (Subgroup.commutator_mem_commutator hy haA) haA
      rw [hcomm, Subgroup.mem_bot] at hm
      simpa only [commutatorElement_def] using
        commutatorElement_eq_one_iff_mul_comm.mp hm
    obtain ⟨K, hKN, hKn, hCK, haK, hKp⟩ :=
      hstable Q hQp a (hAN haA) ⟨k, haPow⟩ hquad
    let D := (K.subgroupOf N).map q
    have hDn : D.Normal := Subgroup.Normal.map hKn q (QuotientGroup.mk'_surjective _)
    have hDp : IsPGroup p D := by
      intro x
      obtain ⟨y, hy, hxy⟩ := x.property
      obtain ⟨j, hj⟩ := hKp y hy
      refine ⟨j, Subtype.ext ?_⟩
      change (x : N ⧸ C.subgroupOf N) ^ p ^ j = 1
      rw [← hxy, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hj
    exact (le_sSup ⟨hDn, hDp⟩ : D ≤ pCore p (N ⧸ C.subgroupOf N)) ⟨a, haK, rfl⟩
  have hnormal := G_theorem_8_2_11 (G := G) (p := p) hpodd hOp hconstrained hstable' S
  rwa [hbot, sup_bot_eq] at hnormal

end CFSG.Adapters
