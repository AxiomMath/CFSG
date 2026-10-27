module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem Ctx.u0_sq (h : Ctx T M g A t d x) : u0Of d x * u0Of d x = d * d :=
  u0Of_sq h.c h.hD h.hd4 h.hx h.hx3

theorem Ctx.u0_mem_oTwoUpper (h : Ctx T M g A t d x) : u0Of d x ∈ oTwoUpper (mcOf T) := by
  have hU := u0Of_mem_U h.c h.c18 h.hD h.hd4 h.hx h.hx3 h.hΓ
  rw [h.c18.a.u_eq] at hU
  exact pCoreOf_le 2 _ hU

theorem Ctx.u0_comm_d (h : Ctx T M g A t d x) : u0Of d x * d = d * u0Of d x :=
  Subgroup.mem_centralizer_singleton_iff.mp
    (oTwoUpper_le_centralizer_d h.c h.hD h.hd4 h.u0_mem_oTwoUpper)

theorem Ctx.u0_mem_Gw (h : Ctx T M g A t d x) : u0Of d x ∈ Gw d x := by
  rw [mem_Gw_iff, wOfX_eq_mul_u0Of]
  calc u0Of d x * (d * u0Of d x) = (u0Of d x * d) * u0Of d x := by group
    _ = (d * u0Of d x) * u0Of d x := by rw [h.u0_comm_d]
    _ = d * u0Of d x * u0Of d x := rfl

theorem Ctx.u0_mem_K0 (h : Ctx T M g A t d x) : u0Of d x ∈ K0 T d x :=
  ⟨h.u0_mem_oTwoUpper, h.u0_mem_Gw⟩

theorem Ctx.z_mem_K0 (h : Ctx T M g A t d x) : d * d ∈ K0 T d x := by
  rw [← h.u0_sq]; exact (K0 T d x).mul_mem h.u0_mem_K0 h.u0_mem_K0

theorem Ctx.u0_comm_w (h : Ctx T M g A t d x) : u0Of d x * wOfX d x = wOfX d x * u0Of d x :=
  mem_Gw_iff.mp h.u0_mem_Gw

theorem Ctx.orderOf_u0 (h : Ctx T M g A t d x) : orderOf (u0Of d x) = 4 := by
  have h4 : u0Of d x ^ 4 = 1 := by
    have e : u0Of d x ^ 4 = (u0Of d x * u0Of d x) * (u0Of d x * u0Of d x) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e, h.u0_sq]; exact h.z_sq
  have h2 : u0Of d x ^ 2 ≠ 1 := by rw [pow_two, h.u0_sq]; exact h.z_ne
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) (by simpa using h4)
  simpa using this

theorem Ctx.comm_z_of_mem_Cw (h : Ctx T M g A t d x) {u : G} (hu : u ∈ Cw T d x) :
    u * (d * d) = (d * d) * u :=
  (Subgroup.mem_centralizer_iff.mp hu.1 (d * d) h.z_mem).symm

theorem Ctx.Tw_le_Cw (h : Ctx T M g A t d x) : Tw T d x ≤ Cw T d x := by
  intro u hu
  refine ⟨?_, hu.2⟩
  refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
  rcases h.c.mem_Z_cases h.z_mem h.z_ne hv with hv1 | hv1
  · rw [hv1]; simp
  · rw [hv1]
    exact (Subgroup.mem_centralizer_iff.mp ((quasithinOmegaOneCenter_le_center T h.z_mem).2)
      u hu.1).symm

theorem Ctx.K0_le_Cw (_h : Ctx T M g A t d x) : K0 T d x ≤ Cw T d x := fun _ hk =>
  ⟨oTwoUpper_le (mcOf T) hk.1, hk.2⟩

theorem Ctx.z_comm_Tw (h : Ctx T M g A t d x) {u : G} (hu : u ∈ Tw T d x) :
    u * (d * d) = (d * d) * u :=
  h.comm_z_of_mem_Cw (h.Tw_le_Cw hu)

end InspW2

end S143

end CFSG.Quasithin
