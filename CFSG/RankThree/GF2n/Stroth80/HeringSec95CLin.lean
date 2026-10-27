module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CSieg

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9

open Module

variable {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem finrank_map_add_finrank_inf_ker (f : E →ₗ[K] E) (N : Submodule K E) :
    finrank K (N.map f) + finrank K ↥(LinearMap.ker f ⊓ N) = finrank K N := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict N)
  have h1 : LinearMap.range (f.domRestrict N) = N.map f := LinearMap.range_domRestrict N f
  have h2 : finrank K ↥(LinearMap.ker (f.domRestrict N)) = finrank K ↥(LinearMap.ker f ⊓ N) := by
    rw [LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
      inf_comm]
  rw [h1, h2] at h
  exact h

variable {Γ : Type*} [Group Γ] {B : LinearMap.BilinForm K E} {Qf : E → K}
  {α : Γ →* (E ≃ₗ[K] E)} {U : Submodule K E} {b₀ : E}

theorem Siegel.finrank_fix_ge (hQ : IsQuadSpace B Qf) (hS : Siegel B Qf α U b₀)
    {Vs : Submodule K E} (hbV : b₀ ∈ Vs) (hV4 : finrank K Vs = 4) (hVU : ¬ Vs ≤ U) {n : ℕ}
    (hE : finrank K E = 2 * n) (g : Γ)
    (hg : ∀ e, (∀ v ∈ Vs, B v e = 0) → α g e - e ∈ Vs) :
    2 * n ≤ finrank K ↥(LinearMap.ker ((α g : E →ₗ[K] E) - 1)) + 6 := by
  classical
  set Ws : Submodule K E := B.orthogonal Vs with hWs
  have hWmem : ∀ e, e ∈ Ws ↔ ∀ v ∈ Vs, B v e = 0 := fun e =>
    LinearMap.BilinForm.mem_orthogonal_iff
  have hWdim : finrank K Ws = 2 * n - 4 := by
    rw [hWs, LinearMap.BilinForm.finrank_orthogonal hQ.nondegenerate, hE, hV4]
  have hUW : ¬ U ≤ Ws := by
    intro hUW
    apply hVU
    intro v hv
    apply hS.perp
    intro u hu
    rw [hQ.B_neg, (hWmem u).mp (hUW hu) v hv, neg_zero]
  set S : Submodule K E := Ws ⊔ U with hSdef
  have hSdim : 2 * n - 3 ≤ finrank K S := by
    have hlt : Ws < S := lt_of_le_of_ne le_sup_left (fun h => hUW (h ▸ le_sup_right))
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  let T : E →ₗ[K] E := (α g : E →ₗ[K] E) - 1
  have hTe : ∀ e, T e = α g e - e := fun e => by simp [T]
  have hTS : ∀ e ∈ S, T e ∈ Vs ⊓ U := by
    intro e he
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp he
    rw [map_add]
    refine (Vs ⊓ U).add_mem ?_ ?_
    · rw [hTe]
      exact ⟨hg w ((hWmem w).mp hw), hS.sub_mem_U hQ g ((hWmem w).mp hw b₀ hbV)⟩
    · obtain ⟨c, hc⟩ := hS.act g u hu
      have : T u = c • b₀ := by rw [hTe, hc]; abel
      rw [this]
      exact ⟨Vs.smul_mem c hbV, U.smul_mem c hS.mem⟩
  have hVUdim : finrank K ↥(Vs ⊓ U) ≤ 3 := by
    have hlt : Vs ⊓ U < Vs := lt_of_le_of_ne inf_le_left (fun h => hVU (h ▸ inf_le_right))
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  let Tr : ↥S →ₗ[K] E := T.domRestrict S
  have hrange : LinearMap.range Tr ≤ Vs ⊓ U := by
    rintro _ ⟨⟨e, he⟩, rfl⟩
    exact hTS e he
  have h1 := LinearMap.finrank_range_add_finrank_ker Tr
  have h2 : finrank K ↥(LinearMap.range Tr) ≤ 3 := (Submodule.finrank_mono hrange).trans hVUdim
  have h3 : finrank K ↥(LinearMap.ker Tr) ≤ finrank K ↥(LinearMap.ker T) := by
    let ι : ↥(LinearMap.ker Tr) →ₗ[K] ↥(LinearMap.ker T) :=
      LinearMap.codRestrict (LinearMap.ker T) (S.subtype ∘ₗ (LinearMap.ker Tr).subtype)
        (fun x => by
          have := x.2
          rw [LinearMap.mem_ker] at this ⊢
          exact this)
    refine LinearMap.finrank_le_finrank_of_injective (f := ι) ?_
    intro x y hxy
    have : ((x : ↥S) : E) = ((y : ↥S) : E) := congrArg (fun z : ↥(LinearMap.ker T) => (z : E)) hxy
    exact Subtype.ext (Subtype.ext this)
  have hker : finrank K ↥(LinearMap.ker T) =
      finrank K ↥(LinearMap.ker ((α g : E →ₗ[K] E) - 1)) := rfl
  omega

theorem finrank_fix_le_of_flag (hQ : IsQuadSpace B Qf) {n : ℕ} (hE : finrank K E = 2 * n)
    {Vs : Submodule K E} (hV4 : finrank K Vs = 4) (hVV : ∀ v ∈ Vs, ∀ v' ∈ Vs, B v v' = 0)
    (T : E ≃ₗ[K] E) (hT : ∀ e, Qf (T e) = Qf e)
    (hTV : ∀ v ∈ Vs, T v ∈ Vs) {A : Submodule K E} (hVA : Vs ≤ A)
    (hA : ∀ e, T e = e → (∀ v ∈ Vs, B v e = 0) → e ∈ A)
    (hf1 : finrank K ↥(LinearMap.ker ((T : E →ₗ[K] E) - 1) ⊓ Vs) ≤ 2) :
    finrank K ↥(LinearMap.ker ((T : E →ₗ[K] E) - 1)) ≤ finrank K A := by
  classical
  set F : Submodule K E := LinearMap.ker ((T : E →ₗ[K] E) - 1) with hF
  have hFmem : ∀ e, e ∈ F ↔ T e = e := fun e => by
    rw [hF, LinearMap.mem_ker]
    simp [sub_eq_zero]
  set Ws : Submodule K E := B.orthogonal Vs with hWs
  have hWmem : ∀ e, e ∈ Ws ↔ ∀ v ∈ Vs, B v e = 0 := fun e =>
    LinearMap.BilinForm.mem_orthogonal_iff
  have hVE : finrank K Vs ≤ finrank K E := Submodule.finrank_le Vs
  have hWdim : finrank K Ws = 2 * n - 4 := by
    rw [hWs, LinearMap.BilinForm.finrank_orthogonal hQ.nondegenerate, hE, hV4]
  have hVW : Vs ≤ Ws := fun v hv => (hWmem v).mpr fun v' hv' => hVV v' hv' v hv
  set Y : Submodule K E := Vs.map ((T : E →ₗ[K] E) - 1) with hY
  have hYdim := finrank_map_add_finrank_inf_ker ((T : E →ₗ[K] E) - 1) Vs
  rw [← hY, ← hF, hV4] at hYdim
  have hperp : finrank K ↥(B.orthogonal Y) = finrank K E - finrank K Y :=
    LinearMap.BilinForm.finrank_orthogonal hQ.nondegenerate Y
  have hFle : F ≤ B.orthogonal Y := by
    intro e he
    rw [hFmem] at he
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    rintro y ⟨v, hv, rfl⟩
    have h1 := hQ.B_iso T hT v e
    rw [he] at h1
    show B ((T : E →ₗ[K] E) v - v) e = 0
    rw [map_sub, LinearMap.sub_apply]
    simp only [LinearEquiv.coe_coe]
    rw [h1, sub_self]
  have hWle : Ws ≤ B.orthogonal Y := by
    intro e he
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    rintro y ⟨v, hv, rfl⟩
    show B ((T : E →ₗ[K] E) v - v) e = 0
    rw [map_sub, LinearMap.sub_apply]
    simp only [LinearEquiv.coe_coe]
    rw [(hWmem e).mp he _ (hTV v hv), (hWmem e).mp he v hv, sub_self]
  have hFWle : finrank K ↥(F ⊔ Ws) ≤ finrank K ↥(B.orthogonal Y) :=
    Submodule.finrank_mono (sup_le hFle hWle)
  have hsup1 := Submodule.finrank_sup_add_finrank_inf_eq F Ws
  have hsup2 := Submodule.finrank_sup_add_finrank_inf_eq (F ⊓ Ws) Vs
  have hinf2 : (F ⊓ Ws) ⊓ Vs = F ⊓ Vs := by
    rw [inf_assoc, inf_eq_right.mpr hVW]
  rw [hinf2] at hsup2
  have hSA : finrank K ↥((F ⊓ Ws) ⊔ Vs) ≤ finrank K A := by
    refine Submodule.finrank_mono (sup_le ?_ hVA)
    intro e he
    exact hA e ((hFmem e).mp he.1) ((hWmem e).mp he.2)
  rw [hV4] at hsup2
  have hYE : finrank K Y ≤ finrank K E := by
    have := Submodule.finrank_mono (show Y ≤ ⊤ from le_top)
    simpa using this
  omega

end CFSG.RankThree.GF2n.Stroth80.HS9
