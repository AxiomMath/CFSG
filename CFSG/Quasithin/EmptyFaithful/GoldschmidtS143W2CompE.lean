module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

open scoped Pointwise

namespace InspW2

theorem exists_conj_le_sylow {G : Type*} [Group G] [Finite G] {H T S : Subgroup G}
    (hT : IsSylowTwoOf T H) (hS : IsPGroup 2 S) (hSH : S ≤ H) :
    ∃ c ∈ H, ∀ s ∈ S, c * s * c⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTX : IsPGroup 2 (T.subgroupOf H) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  let PT : Sylow 2 ↥H := hTX.toSylow hT.2.2
  have hSX : IsPGroup 2 (S.subgroupOf H) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  obtain ⟨Q, hQ⟩ := hSX.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥H) Q PT
  refine ⟨(c : G), c.2, fun s hs => ?_⟩
  have hsQ : (⟨s, hSH hs⟩ : ↥H) ∈ (Q : Subgroup ↥H) := hQ (Subgroup.mem_subgroupOf.mpr hs)
  have h2 : c * ⟨s, hSH hs⟩ * c⁻¹ ∈ ((c • Q : Sylow 2 ↥H) : Subgroup ↥H) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨_, hsQ, rfl⟩
  rw [hc] at h2
  exact Subgroup.mem_subgroupOf.mp h2

section Z

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}
  {Z : Subgroup G}

theorem K0_inf_eq_bot (hf : Wp0 T d x) (hZn : ∀ u ∈ K0 T d x, ∀ k ∈ Z, u * k * u⁻¹ ∈ Z)
    (hz : d * d ∉ Z) : K0 T d x ⊓ Z = ⊥ := by
  by_contra hne
  have hN : ((K0 T d x ⊓ Z).subgroupOf (K0 T d x)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro n k hn hk
    exact ⟨(K0 T d x).mul_mem ((K0 T d x).mul_mem hk hn.1) ((K0 T d x).inv_mem hk),
      hZn k hk n hn.2⟩
  exact hz (hf.K0_contains_z _ inf_le_left hN hne).2

theorem Z_inf_Cw_le_Bw (h : Ctx T M g A t d x) (hf : Wp0 T d x)
    (hZn : ∀ u ∈ K0 T d x, ∀ k ∈ Z, u * k * u⁻¹ ∈ Z) (hz : d * d ∉ Z) :
    Z ⊓ Cw T d x ≤ Bw T d x := by
  rintro u ⟨huZ, huC⟩
  refine ⟨huC, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  have hK0n : ∀ u ∈ Cw T d x, ∀ k ∈ K0 T d x, u * k * u⁻¹ ∈ K0 T d x := fun u hu k hk =>
    (Subgroup.normal_subgroupOf_iff h.K0_le_Cw).mp hf.K0_normal k u hk hu
  have h1 : u * k * u⁻¹ * k⁻¹ ∈ K0 T d x :=
    (K0 T d x).mul_mem (hK0n u huC k hk) ((K0 T d x).inv_mem hk)
  have h2 : u * k * u⁻¹ * k⁻¹ ∈ Z := by
    have h3 : k * u⁻¹ * k⁻¹ ∈ Z := hZn k hk u⁻¹ (Z.inv_mem huZ)
    have e : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
    rw [e]; exact Z.mul_mem huZ h3
  have h4 : u * k * u⁻¹ * k⁻¹ ∈ K0 T d x ⊓ Z := ⟨h1, h2⟩
  rw [K0_inf_eq_bot hf hZn hz, Subgroup.mem_bot] at h4
  have h5 : u * k = k * u := by
    calc u * k = (u * k * u⁻¹ * k⁻¹) * (k * u) := by group
      _ = k * u := by rw [h4, one_mul]
  exact h5.symm

end Z

end InspW2

end S143

end CFSG.Quasithin
