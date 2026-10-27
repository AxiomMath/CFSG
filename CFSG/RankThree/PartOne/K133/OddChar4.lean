module

public import CFSG.RankThree.PartOne.K133.ProjUnip4
public import CFSG.RankThree.PartOne.K133.InnerRed
public import CFSG.RankThree.PartOne.CTP.SeitzToral
public import CFSG.RankThree.PartOne.LIT.RankProjective

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.RankThree.GroupTheory CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_natCast_of_card_eq_prime {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hcard : Nat.card K = p) (c : K) : ∃ k : ℕ, (k : K) = c := by
  have hbij : Function.Bijective (ZMod.castHom (dvd_refl p) K) :=
    (ZMod.castHom (dvd_refl p) K).injective.bijective_of_nat_card_le (by rw [hcard, Nat.card_zmod])
  obtain ⟨z, rfl⟩ := hbij.2 c
  refine ⟨z.val, ?_⟩
  rw [← map_natCast (ZMod.castHom (dvd_refl p) K) z.val, ZMod.natCast_zmod_val]

theorem exists_lift_elemAb_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    {p N : ℕ} (hp : p.Prime) (hN : ¬ p ∣ N) (M : Subgroup (GL ι K))
    (hZN : ∀ z : M, (z : GL ι K) ∈ StatedScalars ι K → z ^ N = 1)
    (A : Subgroup (StatedProj M)) (hA : IsElementaryAbelian p A) :
    ∃ E : Subgroup M, E.map (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf M)) = A ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ p = 1) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Z : Subgroup M := (StatedScalars ι K).subgroupOf M with hZ
  let π : M →* StatedProj M := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : ¬ p ∣ Nat.card π.ker := by
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hzK : (z : M) ∈ Z := by
      have h1 : π (z : M) = 1 := MonoidHom.mem_ker.1 z.2
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hzN : (z : M) ^ N = 1 := hZN z (Subgroup.mem_subgroupOf.1 hzK)
    have hzo : orderOf (z : M) = p := by rw [Subgroup.orderOf_coe, hz]
    exact hN (hzo ▸ orderOf_dvd_of_pow_eq_one hzN)
  obtain ⟨E', hE'map, hE'dis⟩ := CTP.SeitzToral.exists_lift_of_coprime_ker π hπ hker A
    (IsElementaryAbelian.isPGroup p A)
  have hE'mem : ∀ x ∈ E', π x ∈ A := fun x hx => hE'map ▸ ⟨x, hx, rfl⟩
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E' := E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha))
      (E'.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have hcm : π a * π b = π b * π a :=
        congrArg Subtype.val (hA.is_comm.comm ⟨π a, hE'mem a ha⟩ ⟨π b, hE'mem b hb⟩)
      rw [hcm]
      group
    have := Subgroup.disjoint_def.mp hE'dis hc hk
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hE'exp : ∀ a ∈ E', a ^ p = 1 := by
    intro a ha
    have hk : a ^ p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact elemPow_eq_one_of_isElementaryAbelian (π a) (hE'mem a ha)
    exact Subgroup.disjoint_def.mp hE'dis (E'.pow_mem ha p) hk
  exact ⟨E', hE'map, hE'comm, hE'exp⟩

theorem statedProj_card_le_of_bound {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    {p N k : ℕ} (hp : p.Prime) (hN : ¬ p ∣ N) (M : Subgroup (GL ι K))
    (hZN : ∀ z : M, (z : GL ι K) ∈ StatedScalars ι K → z ^ N = 1)
    (hb : ∀ E : Subgroup (GL ι K), E ≤ M → (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) → (∀ g ∈ E, g ^ p = 1) →
      Nat.card E ≤ p ^ k)
    (A : Subgroup (StatedProj M)) (hA : IsElementaryAbelian p A) : Nat.card A ≤ p ^ k := by
  classical
  obtain ⟨E, hEmap, hEcomm, hEexp⟩ := exists_lift_elemAb_statedProj hp hN M hZN A hA
  have hle : Nat.card (E.map M.subtype) ≤ p ^ k := by
    refine hb _ ?_ ?_ ?_
    · rintro _ ⟨a, -, rfl⟩
      exact a.2
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb', rfl⟩
      simpa using congrArg M.subtype (hEcomm a ha b hb')
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hEexp a ha, map_one]
  rw [Subgroup.card_map_of_injective M.subtype_injective] at hle
  rw [← hEmap]
  have hsurj : Function.Surjective
      (fun x : E => (⟨QuotientGroup.mk' ((StatedScalars ι K).subgroupOf M) x,
        Subgroup.mem_map_of_mem _ x.2⟩ : E.map (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf M)))) := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  exact (Nat.card_le_card_of_surjective _ hsurj).trans hle

theorem statedSL_det_eq_one {n : ℕ} {K : Type} [Field K] {g : GL (Fin n) K} (hg : g ∈ StatedSL n K) :
    (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hg

theorem statedSL_scalar_pow {n : ℕ} {K : Type} [Field K] (z : StatedSL n K)
    (hz : (z : GL (Fin n) K) ∈ StatedScalars (Fin n) K) : z ^ n = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  have hc : (z : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hz
  have := LIT.pow_card_eq_one_of_det (z : GL (Fin n) K) hc (statedSL_det_eq_one z.2)
  simpa using this

theorem goodRes_statedProj_four_char {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp5 : 5 ≤ p) (hK : ∀ c : K, ∃ k : ℕ, (k : K) = c) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = 4) (M : Subgroup (GL ι K)) [IsSimpleGroup (StatedProj M)]
    (hne : ∃ a b : StatedProj M, a * b ≠ b * a)
    (hOut : ∀ E : Subgroup (MulAut (StatedProj M)), IsElementaryAbelian p E → E ≤ inner (StatedProj M)) :
    GoodRes p (StatedProj M) := by
  have hp : p.Prime := Fact.out
  have hZ : Subgroup.center (StatedProj M) = ⊥ := center_eq_bot_of_simple_nonabelian hne
  refine goodRes_of_inner_noConfig_el hp hZ hOut ?_
  intro C hC hCc Kb hKs hKn hpKb hall
  exact statedProj_four_no_config hp5 hK hι M C hC hCc Kb hKn hall

end CFSG.RankThree.PartOne.K133
