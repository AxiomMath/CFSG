module

public import CFSG.RankThree.PartTwo.Sec19.SeitzG2F4SU3
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofReeConj
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeCent

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ3 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial


theorem cj_map_equiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) (F : Subgroup A) (a : A) :
    (cj F a).map φ.toMonoidHom = cj (F.map φ.toMonoidHom) (φ a) := by
  ext y
  simp only [cj, Subgroup.mem_map, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨φ x, ⟨x, hx, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a * x * a⁻¹, ⟨x, hx, rfl⟩, by simp⟩

theorem cj_map_subtype {G : Type*} [Group G] (C : Subgroup G) (F₀ : Subgroup C) (t : C) :
    (cj F₀ t).map C.subtype = cj (F₀.map C.subtype) (t : G) := by
  ext y
  simp only [cj, Subgroup.mem_map, MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(x : G), ⟨x, hx, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨t * x * t⁻¹, ⟨x, hx, rfl⟩, by simp⟩


open CFSG.RankThree.PartTwo.Sec8 in
theorem reeGamma_planes_conj_three
    (a : ℕ) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (E E' : Subgroup (ReeTag.F4.reeGamma K a)) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hc : Nat.card E = 9) (hE' : CFSG.Open.IsElemAbelian 3 E') (hc' : Nat.card E' = 9) :
    ∃ g : ReeTag.F4.reeGamma K a, cj E g = E' := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨y, hy3, ⟨φ⟩⟩ := Item8KFacts2Proof.exists_centralizer_mulEquiv_unitarySU a K hK
  set C := Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)) with hC
  set K' := GaloisField 2 (2 * (2 * a + 1)) with hK'
  have h : UnitaryFieldData 2 (2 * a + 1) K' :=
    ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
  have hodd : Odd (2 * a + 1) := odd_two_mul_add_one a
  have key : ∀ E : Subgroup (ReeTag.F4.reeGamma K a), CFSG.Open.IsElemAbelian 3 E →
      Nat.card E = 9 → ∃ g : ReeTag.F4.reeGamma K a, cj E g ≤ C ∧
        ∃ S : Subgroup (unitarySU 2 (2 * a + 1) K' 3),
          (∀ x ∈ S, ∀ z ∈ S, x * z = z * x) ∧ (∀ x ∈ S, x ^ 3 = 1) ∧ Nat.card S = 9 ∧
          S = ((cj E g).subgroupOf C).map φ.toMonoidHom := by
    intro E hE hc
    have hcomm : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := by
      haveI := hE.1
      intro u hu v hv
      exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨u, hu⟩ : E) ⟨v, hv⟩)
    have hne : E ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hc
      omega
    obtain ⟨⟨x, hxE⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hx1' : x ≠ 1 := fun h' => hx1 (Subtype.ext h')
    have hx3 : x ^ 3 = 1 := hE.2 x hxE
    have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1'
    obtain ⟨g, hg⟩ := Item8KFacts3Ree.reeGamma_orderThree_conj a K hK x y hxord hy3
    have hFcomm : ∀ u ∈ cj E g, ∀ v ∈ cj E g, u * v = v * u := by
      intro u hu v hv
      have h1 := hcomm _ (mem_cj.1 hu) _ (mem_cj.1 hv)
      have h2 : g * ((g⁻¹ * u * g) * (g⁻¹ * v * g)) * g⁻¹ = u * v := by group
      have h3 : g * ((g⁻¹ * v * g) * (g⁻¹ * u * g)) * g⁻¹ = v * u := by group
      rw [← h2, ← h3, h1]
    have hFC : cj E g ≤ C := by
      intro z hz
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      have hy : y ∈ cj E g := by
        rw [mem_cj, ← hg]
        have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [e]
        exact hxE
      exact hFcomm _ hz _ hy
    refine ⟨g, hFC, ((cj E g).subgroupOf C).map φ.toMonoidHom, ?_, ?_, ?_, rfl⟩
    · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hFcomm _ hu _ hv)
    · rintro _ ⟨u, hu, rfl⟩
      rw [← map_pow]
      have : u ^ 3 = 1 := Subtype.ext (pow_eq_one_of_mem_cj hE.2 hu)
      rw [this, map_one]
    · rw [Subgroup.card_map_of_injective φ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv, card_cj, hc]
  obtain ⟨g, hgC, S, hSc, hSe, hSn, hSdef⟩ := key E hE hc
  obtain ⟨g', hgC', S', hSc', hSe', hSn', hSdef'⟩ := key E' hE' hc'
  obtain ⟨s, hs⟩ := su3_planes_conj h hodd S S' hSc hSe hSn hSc' hSe' hSn'
  set t : C := φ.symm s with ht
  have hmap : cj ((cj E g).subgroupOf C) t = (cj E' g').subgroupOf C := by
    apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [cj_map_equiv, ← hSdef, ht, MulEquiv.apply_symm_apply, hs, hSdef']
  have hFF : cj (cj E g) (t : ReeTag.F4.reeGamma K a) = cj E' g' := by
    have h1 := congrArg (Subgroup.map C.subtype) hmap
    rw [cj_map_subtype, Subgroup.map_subgroupOf_eq_of_le hgC,
      Subgroup.map_subgroupOf_eq_of_le hgC'] at h1
    exact h1
  refine ⟨g'⁻¹ * (t : ReeTag.F4.reeGamma K a) * g, ?_⟩
  calc cj E (g'⁻¹ * (t : ReeTag.F4.reeGamma K a) * g)
      = cj (cj E ((t : ReeTag.F4.reeGamma K a) * g)) g'⁻¹ := by
        rw [su3_cj_mul_cj, mul_assoc]
    _ = cj (cj (cj E g) (t : ReeTag.F4.reeGamma K a)) g'⁻¹ := by
        rw [su3_cj_mul_cj E g (t : ReeTag.F4.reeGamma K a)]
    _ = cj (cj E' g') g'⁻¹ := by rw [hFF]
    _ = E' := cj_cj


end CFSG.RankThree.PartTwo.Sec19
