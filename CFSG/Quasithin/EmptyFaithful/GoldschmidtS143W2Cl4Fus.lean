module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Cl4E0
public import CFSG.Quasithin.EmptyFaithful.R3c19A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}
  {L : Subgroup G}

theorem invol_mem_RQ (h : Ctx T M g A t d x) (hf : LocalFacts T d x)
    (hL : IsComponentIn L (Gw d x))
    (hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSU 3 3 1) {u : G}
    (hu : u ∈ Tw T d x ⊓ L) (hu2 : u * u = 1) (hu1 : u ≠ 1) : u ∈ rOf T M ⊔ qOf T := by
  by_contra hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzL : d * d ∈ L := E0_le_comp h hf hL hmod (z_mem_E0 h)
  obtain ⟨m, -, hmu⟩ :=
    R3c19.exists_conj_of_u33_subgroup hmod (d * d) hzL u hu.2 h.z_sq h.z_ne hu2 hu1
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  exact h.c21.not_fused u hu.1.1 hnot hord m (d * d) h.z_mem h.z_ne hmu

end InspW2

end S143

end CFSG.Quasithin
