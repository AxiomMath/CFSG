module

public import CFSG.RankThree.GF2n.Smith81.S81QRD
public import CFSG.RankThree.GF2n.Smith81.S81KFix
public import CFSG.RankThree.GF2n.Smith81.S81Gen76D6
public import CFSG.RankThree.GF2n.Smith81.S81QRDMap

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81V

variable {K : Type} [Field K] {Γ : Type} [Group Γ]

theorem RootDatum.conj_mem_closure_range_u (R : RootDatum K Γ) (g : R.P) {y : Γ}
    (hy : y ∈ Subgroup.closure (Set.range R.u)) :
    (g : Γ) * y * (g : Γ)⁻¹ ∈ Subgroup.closure (Set.range R.u) := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    rw [← R.u_Ad]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  | one => simpa using one_mem _
  | mul x y _ _ hx hy =>
    have e : (g : Γ) * (x * y) * (g : Γ)⁻¹ = ((g : Γ) * x * (g : Γ)⁻¹) * ((g : Γ) * y * (g : Γ)⁻¹) := by
      group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : (g : Γ) * x⁻¹ * (g : Γ)⁻¹ = ((g : Γ) * x * (g : Γ)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

end CFSG.RankThree.GF2n.Smith81.S81V

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81Z CFSG.RankThree.GF2n.Smith81.D6X
  CFSG.RankThree.GF2n.Smith81.S81V

variable (K : Type) [Field K] [CharP K 2] [Finite K]

@[expose] def lamGEquivEAut0 : ↥(LamG K) ≃* ↥(EAut0 K) :=
  MulEquiv.ofBijective
    ((lamGHom K).codRestrict (EAut0 K) (fun x => by rw [← range_lamGHom]; exact ⟨x, rfl⟩))
    ⟨fun x y h => lamGHom_injective (congrArg Subtype.val h),
      fun y => by
        obtain ⟨x, hx⟩ : (y : W K ≃ₗ[K] W K) ∈ (lamGHom K).range := by
          rw [range_lamGHom]
          exact y.2
        exact ⟨x, Subtype.ext hx⟩⟩

variable {K}

variable (K)

@[expose] def d6RootDatum : RootDatum K ↥(EAut0 K) :=
  (rootDatumLam K).mapEquiv (lamGEquivEAut0 K)

variable {K}

theorem d6_coe_u (n : ND K) :
    (((d6RootDatum K).u n : ↥(EAut0 K)) : W K ≃ₗ[K] W K) = lamGHom K (uΛ n) := rfl

theorem d6_u_single (β : ↥Psi0) (b : K) :
    (((d6RootDatum K).u (Pi.single β b) : ↥(EAut0 K)) : W K ≃ₗ[K] W K) =
      vAut0 K (xuWUnit (mem_Psi0.1 β.2).1 b) := by
  have h : uΛ (Pi.single β b : ND K) = ⟨xE β.1 b, xE_mem_LamG (mem_Psi0.1 β.2).1 b⟩ :=
    Subtype.ext (uD_single β b)
  rw [d6_coe_u, h]
  exact lamGHom_xE (mem_Psi0.1 β.2).1 b

theorem d6_u_smul_n1 (t : K) :
    ((((d6RootDatum K).u (t • (d6RootDatum K).n₁) : ↥(EAut0 K))) : W K ≃ₗ[K] W K) =
      vAut0 K (xuWUnit alphaA2_mem_Perp t) := by
  have h0 : t • (n1D : ND K) = (Pi.single (⟨alphaA2, alphaA2_mem⟩ : ↥Psi0) t : ND K) := by
    funext δ
    by_cases hδ : δ = (⟨alphaA2, alphaA2_mem⟩ : ↥Psi0)
    · subst hδ
      simp [n1D]
    · simp [n1D, Pi.single_apply, hδ]
  have h : t • (d6RootDatum K).n₁ = (Pi.single (⟨alphaA2, alphaA2_mem⟩ : ↥Psi0) t : ND K) := h0
  rw [h]
  exact d6_u_single _ t

theorem d6_finrank_N : Module.finrank K (d6RootDatum K).N = 15 := by
  show Module.finrank K (↥Psi0 → K) = 15
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, card_Psi0]

theorem uD_mem_URge_Psi0 (n : ND K) : uD n ∈ URge K Psi0 1 := by
  unfold uD prodX
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
  by_cases hγ' : γ ∈ Psi0
  · exact xE_mem_URge hγ' (by
      have := (mem_Rd6.1 (Psi0_subset_Rd6 hγ')).2
      exact_mod_cast this) _
  · rw [extD_of_not_mem hγ']
    have : xE γ (0 : K) = 1 := e7Data_valid.xm_zero K γ
    rw [this]
    exact one_mem _

theorem closure_range_uΛ :
    Subgroup.closure (Set.range (uΛ : ND K → ↥(LamG K))) = (URge K Psi0 1).subgroupOf (LamG K) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨n, rfl⟩
    exact uD_mem_URge_Psi0 n
  · intro g hg
    have hg' : (g : Gp K) ∈ URge K Psi0 1 := hg
    have key : ∃ z : ↥(LamG K), (z : Gp K) = (g : Gp K) ∧
        z ∈ Subgroup.closure (Set.range (uΛ : ND K → ↥(LamG K))) := by
      refine URge_induction (C := fun y => ∃ z : ↥(LamG K), (z : Gp K) = y ∧
        z ∈ Subgroup.closure (Set.range (uΛ : ND K → ↥(LamG K)))) hg' ?_ ?_ ?_
      · intro α hα _ c
        refine ⟨uΛ (Pi.single ⟨α, hα⟩ c), uD_single ⟨α, hα⟩ c, ?_⟩
        exact Subgroup.subset_closure ⟨_, rfl⟩
      · exact ⟨1, rfl, one_mem _⟩
      · rintro x y ⟨x', hx', hx2⟩ ⟨y', hy', hy2⟩
        exact ⟨x' * y', by rw [← hx', ← hy']; rfl, mul_mem hx2 hy2⟩
    obtain ⟨z, hz, hzc⟩ := key
    have : z = g := Subtype.ext hz
    rw [← this]
    exact hzc

theorem closure_range_u :
    Subgroup.closure (Set.range (d6RootDatum K).u) = (rootRad0 K).subgroupOf (EAut0 K) := by
  have h1 : Set.range (d6RootDatum K).u = (lamGEquivEAut0 K) '' Set.range (uΛ : ND K → ↥(LamG K)) := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨uΛ n, ⟨n, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
  have h2 : Subgroup.closure ((lamGEquivEAut0 K) '' Set.range (uΛ : ND K → ↥(LamG K))) =
      (Subgroup.closure (Set.range (uΛ : ND K → ↥(LamG K)))).map (lamGEquivEAut0 K).toMonoidHom :=
    (MonoidHom.map_closure (lamGEquivEAut0 K).toMonoidHom _).symm
  rw [h1, h2, closure_range_uΛ]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h2 : lamGHom K y ∈ ((URge K (Rn fA2 Rd6) 1).subgroupOf (LamG K)).map (lamGHom K) := ⟨y, hy, rfl⟩
    rw [map_lamGHom_URge_A2] at h2
    exact h2
  · intro hx
    have hx' : (x : W K ≃ₗ[K] W K) ∈ ((URge K (Rn fA2 Rd6) 1).subgroupOf (LamG K)).map (lamGHom K) := by
      rw [map_lamGHom_URge_A2]
      exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    exact ⟨y, hy, Subtype.ext hyx⟩

theorem u_mem_rootRad0 (n : ND K) :
    (((d6RootDatum K).u n : ↥(EAut0 K)) : W K ≃ₗ[K] W K) ∈ rootRad0 K := by
  have h : (d6RootDatum K).u n ∈ Subgroup.closure (Set.range (d6RootDatum K).u) :=
    Subgroup.subset_closure ⟨n, rfl⟩
  rw [closure_range_u] at h
  exact h

theorem rootSet0_fix_p0 {s : W K ≃ₗ[K] W K} (hs : s ∈ rootSet0 K) : s (p0 K) = p0 K := by
  obtain ⟨γ, hγ, hpr, c, hs⟩ := hs
  have hn1 : ¬ (pr (a0 : Fin e7Data.d) γ = -1) := by rw [hpr]; norm_num
  apply emb_injective
  rw [hs, p0, emb_single, e7Data_valid.xu_apply, rootOp_single hγ.1, if_neg hn1, smul_zero, add_zero]

theorem rootRad0_fix_p0 {x : W K ≃ₗ[K] W K} (hx : x ∈ rootRad0 K) : x (p0 K) = p0 K := by
  have hle : rootRad0 K ≤ MulAction.stabilizer (W K ≃ₗ[K] W K) (p0 K) := by
    rw [rootRad0, Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, LinearEquiv.smul_def]
    exact rootSet0_fix_p0 hs
  have h := MulAction.mem_stabilizer_iff.1 (hle hx)
  rwa [LinearEquiv.smul_def] at h

theorem p0_ne_zero : p0 K ≠ 0 := by
  unfold p0
  exact Finsupp.single_ne_zero.2 one_ne_zero

theorem d6_P_le_StabP0 : (d6RootDatum K).P ≤ StabP0 K := by
  intro g hg
  have hfix : ∀ x ∈ rootRad0 K, x (((g : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K)) =
      ((g : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K) := by
    intro x hx
    have hx' : (⟨x, rootRad0_le_EAut0 hx⟩ : ↥(EAut0 K)) ∈
        Subgroup.closure (Set.range (d6RootDatum K).u) := by
      rw [closure_range_u]
      exact hx
    have h1 := RootDatum.conj_mem_closure_range_u (d6RootDatum K) ⟨g⁻¹, inv_mem hg⟩ hx'
    rw [closure_range_u] at h1
    have h2 := rootRad0_fix_p0 (Subgroup.mem_subgroupOf.1 h1)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, LinearEquiv.mul_apply] at h2
    have h3 := congrArg (fun v => ((g : ↥(EAut0 K)) : W K ≃ₗ[K] W K) v) h2
    simpa [LinearEquiv.coe_inv] using h3
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (fix_rootRad0 _ hfix)
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  rw [zero_smul] at hc
  exact p0_ne_zero ((LinearEquiv.map_eq_zero_iff _).1 hc.symm)

theorem d6_d_eq_d0Hom (c : Kˣ) :
    (((d6RootDatum K).d c : ↥(d6RootDatum K).P) : ↥(EAut0 K)) = d0Hom K c :=
  Subtype.ext rfl

theorem d6_s_apply_single (a : Idx0) :
    ((((d6RootDatum K).s : ↥(EAut0 K))) : W K ≃ₗ[K] W K) (Finsupp.single a 1) =
      Finsupp.single (sReflW 0 a) 1 := by
  apply emb_injective
  have h1 := lamGHom_induces (sD K) (Finsupp.single a 1)
  show emb K (lamGHom K (sD K) (Finsupp.single a 1)) = emb K (Finsupp.single (sReflW 0 a) 1)
  rw [h1, emb_single, emb_single, coe_sD]
  exact (IsMon.nm nodeA2).weight (a : Fin e7Data.d)

end CFSG.RankThree.GF2n.Smith81.D6Spin
