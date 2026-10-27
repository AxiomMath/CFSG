module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Ctx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem Ctx.z_sq (h : Ctx T M g A t d x) : (d * d) * (d * d) = 1 := (dd_facts h.hd4).1

theorem Ctx.z_ne (h : Ctx T M g A t d x) : d * d ≠ 1 := (dd_facts h.hd4).2

theorem Ctx.z_mem (h : Ctx T M g A t d x) : d * d ∈ quasithinOmegaOneCenter T :=
  sq_mem_omegaOneCenter h.c h.hD h.hd4

theorem Ctx.w_sq (h : Ctx T M g A t d x) : wOfX d x * wOfX d x = 1 :=
  wOfX_sq h.c h.hD h.hd4 h.hx h.hx3

theorem Ctx.w_mem_T (h : Ctx T M g A t d x) : wOfX d x ∈ T := wOfX_mem_T h.c h.hD h.hx

theorem Ctx.z_comm_w (h : Ctx T M g A t d x) : (d * d) * wOfX d x = wOfX d x * (d * d) := by
  have hd : d ∈ dOf T M := h.hD ▸ Subgroup.mem_zpowers d
  have hzX : d * d ∈ Xgen T M :=
    (Xgen T M).mul_mem (le_Wgen (dOf_mem_delta h.c) hd) (le_Wgen (dOf_mem_delta h.c) hd)
  exact Xgen_comm h.c h.hD h.hd4 _ hzX _ (wOfX_mem_Xgen h.c h.hD h.hx)

theorem Ctx.w_ne (h : Ctx T M g A t d x) : wOfX d x ≠ 1 := by
  intro hw
  obtain ⟨s, hs⟩ := h.hN2
  rw [hw] at hs
  apply h.z_ne
  have : (1 : G) = d * d := by simpa using hs
  exact this.symm

theorem Ctx.x_comm_w (h : Ctx T M g A t d x) : x * wOfX d x * x⁻¹ = wOfX d x :=
  x_comm_wOfX h.c h.hD h.hd4 h.hx h.hx3

omit [Finite G] in
theorem mem_Gw_iff {y : G} : y ∈ Gw d x ↔ y * wOfX d x = wOfX d x * y :=
  Subgroup.mem_centralizer_singleton_iff

theorem Ctx.x_mem_Gw (h : Ctx T M g A t d x) : x ∈ Gw d x := by
  rw [mem_Gw_iff]
  have := h.x_comm_w
  calc x * wOfX d x = (x * wOfX d x * x⁻¹) * x := by group
    _ = wOfX d x * x := by rw [this]

theorem Ctx.z_mem_Gw (h : Ctx T M g A t d x) : d * d ∈ Gw d x := by
  rw [mem_Gw_iff]; exact h.z_comm_w

theorem Ctx.w_mem_Gw (_h : Ctx T M g A t d x) : wOfX d x ∈ Gw d x := by
  rw [mem_Gw_iff]

theorem Ctx.isPGroup_zpowers_w (h : Ctx T M g A t d x) :
    IsPGroup 2 ↥(Subgroup.zpowers (wOfX d x)) := by
  have hord : orderOf (wOfX d x) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact h.w_sq) h.w_ne
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; simp)

theorem lemma115Hyp_Gw (h : Ctx T M g A t d x) :
    Lemma115Hyp (Gw d x) (Tw T d x) (mcOf T) (d * d) := by
  have hz := h.z_mem
  have hzT : d * d ∈ T := (quasithinOmegaOneCenter_le_center T hz).1
  have hzcT : d * d ∈ Subgroup.centralizer (T : Set G) :=
    (quasithinOmegaOneCenter_le_center T hz).2
  have hQ := h.c.hyp.qtke
  exact lemma116 hQ.2.1 h.isPGroup_zpowers_w (by rw [Ne, Subgroup.zpowers_eq_bot]; exact h.w_ne)
    (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun h' hh' => by
        rw [Set.mem_singleton_iff] at hh'; subst hh'; rfl))
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers _))))
    (centralizer_singleton_le_normalizer_zpowers _) h.hSyl
    (isSylowTwoOf_of_quasithinIsSylowTwo h.c.hyp.sylow le_top) inf_le_left hzT hzcT h.z_ne
    (sq_eq_one_of_mem_omegaOneCenter T hz) h.c.hyp.mc_max
    (fun u hu => Subgroup.mem_centralizer_iff.mpr fun v hv => by
      rcases h.c.mem_Z_cases hz h.z_ne hv with hv1 | hv1
      · rw [hv1]; simp
      · rw [hv1]; exact (Subgroup.mem_centralizer_iff.mp hu (d * d) rfl))

end InspW2

end S143

end CFSG.Quasithin
