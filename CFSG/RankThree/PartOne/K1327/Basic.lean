module

public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne.K1327

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartOne

variable {G : Type} [Group G]

@[expose] def Jof (p : ℕ) (R : Subgroup G) : Subgroup G :=
  pElementSubgroup p (Subgroup.centralizer (R : Set G))

@[expose] noncomputable def Vof (p : ℕ) (J : Subgroup G) : Subgroup G :=
  inSubgroup (aschbacherSolvableCore p) J

theorem Jof_def (p : ℕ) (R : Subgroup G) :
    Jof p R = pElementSubgroup p (Subgroup.centralizer (R : Set G)) := rfl

theorem Vof_le (p : ℕ) (J : Subgroup G) : Vof p J ≤ J := Subgroup.map_subtype_le _

theorem Vof_conj (p : ℕ) (J : Subgroup G) : ∀ j ∈ J, ∀ v ∈ Vof p J, j * v * j⁻¹ ∈ Vof p J := by
  intro j hj v hv
  obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.1 hv
  have hn := (aschbacherSolvableCore_normal p ↥J).conj_mem v' hv' ⟨j, hj⟩
  exact ⟨_, hn, rfl⟩

theorem Vof_solvable_coprime [Finite G] {p : ℕ} (hp : p.Prime) (J : Subgroup G) :
    Group.IsSolvable ↥(Vof p J) ∧ ¬ p ∣ Nat.card ↥(Vof p J) :=
  theta_solvable_and_not_dvd hp J

theorem mem_Jof {p : ℕ} {R : Subgroup G} {x : G} (hx : x ∈ Subgroup.centralizer (R : Set G))
    (k : ℕ) (hk : orderOf x = p ^ k) : x ∈ Jof p R :=
  Subgroup.subset_closure ⟨hx, k, hk⟩

theorem mem_Jof_of_pow {p : ℕ} (hp : p.Prime) {R : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.centralizer (R : Set G)) (hxp : x ^ p = 1) : x ∈ Jof p R := by
  have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact mem_Jof hx 0 (by rw [h]; simp)
  · exact mem_Jof hx 1 (by rw [h]; simp)

theorem conjBy_Jof {p : ℕ} {R : Subgroup G} {y : G} (hy : conjBy y R = R) :
    conjBy y (Jof p R) = Jof p R := by
  rw [Jof_def, ← Equivariance.pElementSubgroup_conjBy, ← Equivariance.centralizer_conjBy, hy]

theorem conjBy_Vof [Finite G] {p : ℕ} (hp : p.Prime) {J : Subgroup G} {y : G}
    (hy : conjBy y J = J) : conjBy y (Vof p J) = Vof p J := by
  unfold Vof
  rw [← inSubgroup_theta_conjBy hp, hy]

end CFSG.RankThree.PartOne.K1327
