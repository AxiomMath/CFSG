module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1Defs
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Comp
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Data
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Lift
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Sylow
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Five

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

section Certified


theorem residueR1PCore_of_five (hP2b : Item116P2b) (hP2c : Item116P2c) (h45 : Sec4.Item4_5)
    (h5 : FiveCaseCore) : ResidueR1PCore := by
  intro G _ _ A c L a R Y d h hT hR1 hbot
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hD8, n, hnW, hnc, hnd, hna⟩ := hR1
  have hs := h.toSec11Std hT
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have haA := h.a_mem
  have hcA : c ∈ A := h.mem_A
  have hdA : d ∈ A := by
    have h1 : d ∈ A ⊓ L := by
      rw [h.inf_eq_zpowers]
      exact Subgroup.mem_zpowers d
    exact (Subgroup.mem_inf.mp h1).1
  obtain ⟨S, y, hSθ, hS2, hSidx, hAS, hyθ, hyA, hn'S⟩ := exists_invariant_sylow_swap h hnW hna
  obtain ⟨n', hn'def⟩ : ∃ n' : G, n' = y⁻¹ * n := ⟨_, rfl⟩
  rw [← hn'def] at hn'S
  have hyc : ∀ x ∈ A, y * x * y⁻¹ = x := fun x hx => by
    rw [hyA x hx]
    group
  have hcongr : ∀ x ∈ A, n' * x * n'⁻¹ = n * x * n⁻¹ := by
    intro x hx
    have hnx : n * x * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hnW x).mp hx
    have hy1 : y * (n * x * n⁻¹) = (n * x * n⁻¹) * y := hyA _ hnx
    rw [hn'def]
    calc y⁻¹ * n * x * (y⁻¹ * n)⁻¹ = y⁻¹ * (n * x * n⁻¹) * y := by group
      _ = n * x * n⁻¹ := by
        rw [mul_assoc, ← hy1]
        group
  have hyN : y ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hyc x hx]
      exact hx
    · intro hx
      have h2 : y * (y * x * y⁻¹) * y⁻¹ = y * x * y⁻¹ := hyc _ hx
      have h3 : y * x * y⁻¹ = x := by
        calc y * x * y⁻¹ = y⁻¹ * (y * (y * x * y⁻¹) * y⁻¹) * y := by group
          _ = y⁻¹ * (y * x * y⁻¹) * y := by rw [h2]
          _ = x := by group
      rw [h3] at hx
      exact hx
  have hn'W : n' ∈ Subgroup.normalizer (A : Set G) := by
    rw [hn'def]
    exact mul_mem (inv_mem hyN) hnW
  have hn'c : n' * c * n'⁻¹ ∈ Subgroup.zpowers d := by
    rw [hcongr c hcA]
    exact hnc
  have hn'd : n' * d * n'⁻¹ ∈ Subgroup.zpowers c := by
    rw [hcongr d hdA]
    exact hnd
  have hn'a : n' * a * n'⁻¹ = a⁻¹ := by
    rw [hcongr a haA]
    exact hna
  have hna' : n' * a * n'⁻¹ ∈ Subgroup.zpowers a := by
    rw [hn'a]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  have hna1 : n' * a * n'⁻¹ ≠ 1 := fun h1 => h.a_ne_one (by
    calc a = n'⁻¹ * (n' * a * n'⁻¹) * n' := by group
      _ = 1 := by rw [h1]; group)
  have hn'C : n' ∈ Subgroup.normalizer
      ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
    refine GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq ?_
    rw [map_centralizer_singleton, MulAut.conj_apply]
    exact TheoremO.centralizer_eq_of_zpowers_eq
      (TheoremO.zpowers_eq_of_mem_of_ne_one (hexp a haA) hna' hna1)
  obtain ⟨J₁, J₂, hc1, hc2, hne, hZ1, hZ2, -, -, hJ₁eq, hJ₂eq⟩ :=
    aComponentData hP2b hP2c h45 h hT hD8 hn'W hn'c hn'd hn'a
  have hθH : thetaCent a ≤ Subgroup.centralizer ({a} : Set G) := Subgroup.map_subtype_le _
  have hHθ : Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer ((thetaCent a : Subgroup G) : Set G) :=
    Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta _)
  have hθs : Group.IsSolvable (thetaCent a) := k4_isSolvable_thetaCent a
  have hθ3 : ¬ 3 ∣ Nat.card (thetaCent a) := not_three_dvd_card_inSubgroup_theta _
  have hloc := hloc_of_localRank (G := G) (fun r hr h3 => h.localRank_lt r hr h3)
  have hKperf : ⁅sec11K L a, sec11K L a⁆ = sec11K L a :=
    Subgroup.isPerfect_iff.mp (Sec6.isPerfect_inSubgroup_perfectResidual _)
  have hKa : sec11K L a ≤ Subgroup.centralizer ({a} : Set G) :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  obtain ⟨K₁, hK₁H, hK₁S, hK₁perf, hK₁sup⟩ :=
    exists_perfect_lift_normalizer_sylow (p := 2) hθH hHθ hSθ hS2 hSidx hKa hKperf
  set K₂ : Subgroup G := K₁.map (MulAut.conj n').toMonoidHom with hK₂def
  set Kn : Subgroup G := (sec11K L a).map (MulAut.conj n').toMonoidHom with hKn
  have hK₂H : K₂ ≤ Subgroup.centralizer ({a} : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hn'C k).mp (hK₁H hk)
  have hKnH : Kn ≤ Subgroup.centralizer ({a} : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hn'C k).mp (hKa hk)
  have hK₂S : K₂ ≤ Subgroup.normalizer (S : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    exact mul_mem (mul_mem hn'S (hK₁S hk)) (inv_mem hn'S)
  have hK₂perf : ⁅K₂, K₂⁆ = K₂ := by
    rw [hK₂def, ← Subgroup.map_commutator, hK₁perf]
  have hθmap : (thetaCent a).map (MulAut.conj n').toMonoidHom = thetaCent a :=
    thetaCent_map_conj_local (hexp a haA) hna'
  have hK₂sup : K₂ ⊔ thetaCent a = Kn ⊔ thetaCent a := by
    have h1 := congrArg (Subgroup.map (MulAut.conj n').toMonoidHom) hK₁sup
    simp only [Subgroup.map_sup, hθmap] at h1
    exact h1
  have himg₁ : (K₁.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) = J₁ :=
    (map_thetaQuot_eq_of_sup_eq hK₁H hKa hK₁sup).trans hJ₁eq.symm
  have himg₂ : (K₂.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 (CAt a))) = J₂ :=
    (map_thetaQuot_eq_of_sup_eq hK₂H hKnH hK₂sup).trans hJ₂eq.symm
  have hcomm : ⁅J₁, J₂⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hc1 hc2).resolve_left hne
  have hinf : J₁ ⊓ J₂ = ⊥ := compJ3_inf_eq_bot hc1 hc2 hne hZ1
  have hcommθ : ⁅K₁, K₂⁆ ≤ thetaCent a :=
    commutator_le_theta_of_map_commutator_eq_bot hK₁H hK₂H (by rw [himg₁, himg₂]; exact hcomm)
  have hinfθ : (K₁ ⊔ thetaCent a) ⊓ (K₂ ⊔ thetaCent a) = thetaCent a :=
    inf_sup_theta_eq hK₁H hK₂H (by rw [himg₁, himg₂]; exact hinf)
  haveI hN₁ : ((thetaCent a).subgroupOf K₁).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hK₁H.trans hHθ)
  haveI hN₂ : ((thetaCent a).subgroupOf K₂).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hK₂H.trans hHθ)
  have hsimp₁ : IsSimpleGroup (K₁ ⧸ (thetaCent a).subgroupOf K₁) :=
    isSimple_quotient_of_map_eq hK₁H himg₁ (isSimpleGroup_of_component_center_bot hc1 hZ1)
  have hsimp₂ : IsSimpleGroup (K₂ ⧸ (thetaCent a).subgroupOf K₂) :=
    isSimple_quotient_of_map_eq hK₂H himg₂ (isSimpleGroup_of_component_center_bot hc2 hZ2)
  have hnt_d : ∃ s ∈ S, d * s * d⁻¹ ≠ s :=
    exists_not_centralize_d hP2b hP2c h45 h hT hD8 hn'W hn'c hn'd hn'a hSθ hS2 hSidx hAS hn'S
  have hdK : d ∈ sec11K L a :=
    TheoremO.mem_sec11K_d h45 hs h.inf_eq_zpowers h.not_mem_zpowers
  have hdsup : d ∈ K₁ ⊔ thetaCent a := by
    rw [hK₁sup]
    exact Subgroup.mem_sup_left hdK
  have hnt₁ : ∃ k ∈ K₁, ∃ s ∈ S, k * s * k⁻¹ ≠ s :=
    not_centralizes_of_mem_sup (hK₁H.trans hHθ) hK₁S hSθ hθ3 hdsup (hAS hdA) (hexp d hdA) hnt_d
  have hnt₂ : ∃ k ∈ K₂, ∃ s ∈ S, k * s * k⁻¹ ≠ s := by
    obtain ⟨k, hk, s, hs', hks⟩ := hnt₁
    refine ⟨n' * k * n'⁻¹, ⟨k, hk, rfl⟩, n' * s * n'⁻¹,
      (Subgroup.mem_normalizer_iff.mp hn'S s).mp hs', ?_⟩
    intro heq
    apply hks
    calc k * s * k⁻¹
        = n'⁻¹ * (n' * k * n'⁻¹ * (n' * s * n'⁻¹) * (n' * k * n'⁻¹)⁻¹) * n' := by group
      _ = n'⁻¹ * (n' * s * n'⁻¹) * n' := by rw [heq]
      _ = s := by group
  have h5₁ : 5 ∣ Nat.card (K₁ ⧸ (thetaCent a).subgroupOf K₁) :=
    five_dvd_card_quotient hloc hθH hHθ hθs hθ3 hbot hSθ hS2 hK₁H hK₁S hK₁perf hsimp₁ hnt₁
  have h5₂ : 5 ∣ Nat.card (K₂ ⧸ (thetaCent a).subgroupOf K₂) :=
    five_dvd_card_quotient hloc hθH hHθ hθs hθ3 hbot hSθ hS2 hK₂H hK₂S hK₂perf hsimp₂ hnt₂
  exact h5 G hloc (thetaCent a) (Subgroup.centralizer ({a} : Set G)) S K₁ K₂ hθH hHθ hθs hθ3 hbot
    hSθ hS2 hSidx hK₁H hK₁S hK₁perf hK₂H hK₂S hK₂perf hcommθ hinfθ hsimp₁ h5₁ hsimp₂ h5₂ hnt₁ hnt₂

end Certified

end CFSG.RankThree.PartTwo.Sec11
