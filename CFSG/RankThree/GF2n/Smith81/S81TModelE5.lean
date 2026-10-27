module

public import CFSG.RankThree.GF2n.Smith81.S81TModelDef
public import CFSG.RankThree.GF2n.Smith81.S81TP2
public import CFSG.RankThree.GF2n.Smith81.S81TQf
public import CFSG.RankThree.GF2n.Smith81.S81TClass5
public import CFSG.RankThree.GF2n.Smith81.S81E5Uni

public section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


section E5

variable {K : Type} [Field K] [CharP K 2]

theorem closedL5 : ClosedL okD5 inL5 := fun _ _ _ _ _ => Iff.rfl

theorem mem_supported_univ (c : V K) :
    c ∈ Finsupp.supported K K {a : Fin e7Data.d | inL5 a} := by
  rw [Finsupp.mem_supported']
  intro x hx
  exact absurd trivial hx

theorem vAut_mem_EAut {u : (Module.End K (V K))ˣ} (hu : u ∈ EGrp K) : vAut K u ∈ EAut K :=
  Subgroup.mem_map_of_mem _ hu

theorem grpR5_le : GrpR K okD5 ≤ EGrp K := by
  rw [GrpR, Subgroup.closure_le]
  rintro g ⟨β, hβ, -, c, rfl⟩
  exact e7Data_valid.xu_mem K β c

theorem vAut_mul_comm {S : List Rt} {u : (Module.End K (V K))ˣ}
    (h : Commute (u : Module.End K (V K)) (tOp K S)) {t : V K ≃ₗ[K] V K}
    (ht : ∀ v, t v = tOp K S v) : vAut K u * t = t * vAut K u := by
  apply LinearEquiv.ext
  intro v
  have h1 : (u : Module.End K (V K)) (tOp K S v) = tOp K S ((u : Module.End K (V K)) v) :=
    LinearMap.congr_fun h.eq v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ht, ht, vAut_apply, vAut_apply, h1]

theorem Cw_iff {S : List Rt} {t : V K ≃ₗ[K] V K} (ht : ∀ v, t v = tOp K S v) {c : V K} :
    c ∈ CwE t ↔ NOp K S c = 0 := by
  show t c = c ↔ _
  rw [ht, NOp_eq, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem RangeL_subset_Rw {S : List Rt} {t : V K ≃ₗ[K] V K} (ht : ∀ v, t v = tOp K S v) {r : V K}
    (hr : r ∈ RangeL K S inL5) : r ∈ RwE t := by
  obtain ⟨w, -, rfl⟩ := hr
  refine ⟨w, ?_⟩
  rw [ht, NOp_eq, LinearMap.sub_apply, Module.End.one_apply]

theorem Rw_subset_range {S : List Rt} {t : V K ≃ₗ[K] V K} (ht : ∀ v, t v = tOp K S v) {r : V K}
    (hr : r ∈ RwE t) : r ∈ LinearMap.range (NOp K S) := by
  obtain ⟨w, rfl⟩ := hr
  refine ⟨w, ?_⟩
  rw [ht, NOp_eq, LinearMap.sub_apply, Module.End.one_apply]

theorem Rw_subset_range' {S : List Rt} {t : V K ≃ₗ[K] V K} (ht : ∀ v, t v = tOp K S v) {r : V K}
    (hr : r ∈ LinearMap.range (NOp K S)) : r ∈ RwE t := by
  obtain ⟨w, rfl⟩ := hr
  refine ⟨w, ?_⟩
  rw [ht, NOp_eq, LinearMap.sub_apply, Module.End.one_apply]

end E5

section E5inst

variable {K : Type} [Field K] [CharP K 2] [Finite K]

set_option maxRecDepth 20000 in
theorem involK12_E5 (hK4 : 4 ≤ Nat.card K) {S : List Rt} (hS : K12Cond okD5 inL5 S)
    {t : V K ≃ₗ[K] V K} (ht : ∀ v, t v = tOp K S v) :
    InvolK12 (EAut K) (w0 : V K) beta t := by
  have hSo : SOrth S := sOrth_of_K12 hS
  obtain ⟨-, -, -, -, hStar, hStar2, hTwo, hNM, hCl, hpar⟩ := hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    rw [ht]
    exact beta_tOp_eq_zero_of_even hSo hpar (fun a _ => trivial)
  · intro c hc
    have hC := (Cw_iff ht).1 hc
    obtain ⟨r, hr, hcl⟩ := cov_of_star2 hSo (okD := okD5) (inL := inL5) (fun β _ => trivial)
      closedL5 hStar2 (mem_supported_univ c) hC
    refine ⟨r, RangeL_subset_Rw ht hr, ?_⟩
    refine AddSubgroup.closure_mono ?_ hcl
    rintro v ⟨α, hα, -, hperp, c', -, hc', rfl⟩
    refine ⟨vAut K (e7Data_valid.xu K α 1),
      ⟨vAut_mem_EAut (e7Data_valid.xu_mem K α 1),
        vAut_mul_comm (xu_commute_tOp hα hSo.1 (fun β hβ => by rw [hperp β hβ]) 1) ht⟩,
      c', (Cw_iff ht).2 hc', ?_⟩
    rw [vAut_apply, e7Data_valid.xu_apply, one_smul]
    abel
  · refine ⟨{g | ∃ α : Rt, IsRoot .E7 α ∧ inAplus S α ∧ ∃ c₀ : K,
      g = vAut K (e7Data_valid.xu K α c₀)}, ?_, ?_, ?_⟩
    · rintro u ⟨α, hα, hA, c₀, rfl⟩
      exact ⟨vAut_mem_EAut (e7Data_valid.xu_mem K α c₀),
        vAut_mul_comm (xu_commute_tOp hα hSo.1
          (fun β hβ => by rcases hA.1 β hβ with h | h <;> omega) c₀) ht⟩
    · rintro u ⟨α, hα, hA, c₀, rfl⟩ c hc
      have hC := (Cw_iff ht).1 hc
      have h1 := heis_sub_mem hSo (okD := okD5) (inL := inL5) (fun β _ => trivial) closedL5 hα
        trivial hA (mem_supported_univ c) hC
      have h2 : c₀ • e7Data.rootOp K α c ∈ RangeL K S inL5 := Submodule.smul_mem _ c₀ h1
      have h3 := RangeL_subset_Rw ht h2
      have e : (vAut K (e7Data_valid.xu K α c₀)) c - c = c₀ • e7Data.rootOp K α c := by
        rw [vAut_apply, e7Data_valid.xu_apply]
        abel
      rw [e]
      exact h3
    · intro c hc hfix
      have hC := (Cw_iff ht).1 hc
      have hfix' : ∀ α : Rt, IsRoot .E7 α → okD5 α → inAplus S α →
          e7Data.rootOp K α c = 0 := by
        intro α hα _ hA
        have h := hfix (vAut K (e7Data_valid.xu K α 1)) ⟨α, hα, hA, 1, rfl⟩
        rw [vAut_apply, e7Data_valid.xu_apply, one_smul] at h
        simpa using h
      exact RangeL_subset_Rw ht (fix_heis_le hSo (okD := okD5) (inL := inL5) (fun β _ => trivial)
        closedL5 hStar (mem_supported_univ c) hC hfix')
  · intro S' hne hR hstab
    have hR' : ∀ s ∈ S', s ∈ LinearMap.range (NOp K S) := fun s hs => Rw_subset_range ht (hR s hs)
    have hstab' : ∀ a b : (Module.End K (V K))ˣ, a ∈ GrpR K okD5 → b ∈ GrpR K okD5 →
        Commute (a : Module.End K (V K)) (tOp K S) → Commute (b : Module.End K (V K)) (tOp K S) →
        ∀ s ∈ S', ((a * b * a⁻¹ * b⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) s ∈ S' := by
      intro a b ha hb hac hbc s hs
      have h := hstab (vAut K a) ⟨vAut_mem_EAut (grpR5_le ha), vAut_mul_comm hac ht⟩ (vAut K b)
        ⟨vAut_mem_EAut (grpR5_le hb), vAut_mul_comm hbc ht⟩ s hs
      have e : vAut K a * vAut K b * (vAut K a)⁻¹ * (vAut K b)⁻¹ = vAut K (a * b * a⁻¹ * b⁻¹) := by
        simp only [map_mul, map_inv]
      rw [e, vAut_apply] at h
      exact h
    obtain ⟨p, hpS, hp0, g, hg, hspan⟩ := P2_of_clique hSo (okD := okD5) (inL := inL5)
      (fun β _ => trivial) (fun γ _ => trivial) closedL5 hTwo hNM hCl hK4 hne
      (fun s _ => mem_supported_univ s) hR' hstab'
    have hp : p ∈ Submodule.span K {(g : Module.End K (V K)) (w0 : V K)} := by
      rw [← hspan]
      exact Submodule.mem_span_singleton_self p
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hp
    exact ⟨p, hpS, hp0, vAut K g, vAut_mem_EAut hg, c, by rw [vAut_apply]; exact hc.symm⟩

set_option maxRecDepth 20000 in
theorem involK3_E5 {S : List Rt} (hS : K3Cond okD5 inL5 S) {t : V K ≃ₗ[K] V K}
    (ht : ∀ v, t v = tOp K S v) : InvolK3 (EAut K) beta t := by
  have hSo : SOrth S := sOrth_of_K3 hS
  obtain ⟨-, -, -, -, hperp, b, -, hb⟩ := hS
  refine ⟨?_, ?_⟩
  · intro c hc
    have hC := (Cw_iff ht).1 hc
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (ker_NOp_le hSo (LinearMap.mem_ker.2 hC))
    have hz0 : z = 0 := by
      ext x
      rw [Finsupp.zero_apply]
      refine (Finsupp.mem_supported' K z).1 hz x (fun hx => ?_)
      obtain ⟨β, hβ, hne⟩ := hperp x trivial
      exact hne (hx β hβ)
    rw [hz0, add_zero] at hyz
    subst hyz
    exact Rw_subset_range' ht hy
  · exact ⟨Finsupp.single b 1, by rw [ht, beta_tOp_single_eq_one hSo hb]; exact one_ne_zero⟩

theorem involModel_E5 (hK4 : 4 ≤ Nat.card K) {S : List Rt} (hS : S ∈ e5Reps) {t : V K ≃ₗ[K] V K}
    (ht : ∀ v, t v = tOp K S v) :
    InvolK12 (EAut K) (w0 : V K) beta t ∨ InvolK3 (EAut K) beta t :=
  (e5Reps_cond S hS).elim (fun h => Or.inl (involK12_E5 hK4 h ht))
    (fun h => Or.inr (involK3_E5 h ht))

end E5inst

end CFSG.RankThree.GF2n.Smith81.MinuscT
