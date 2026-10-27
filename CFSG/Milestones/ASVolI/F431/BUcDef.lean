module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutDatum
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieSub
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructLoc

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.H13.F431

@[expose] def burnsideF4m_UnCenterProp (m f : ℕ) : Prop :=
  ∀ (D : Type) [Group D], LieModel D .PSU m 2 f → ∀ A : LieAmalgamExt D,
    ¬ Odd (Nat.card ↥A.K / Nat.card D) →
    ∃ (T N : Subgroup ↥A.K) (z : ↥A.K), IsSylowTwoOf T ⊤ ∧ T ≤ A.Mb1 ∧ T ≤ A.Mb2 ∧
      ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ N, m * z * m⁻¹ = w

theorem burnsideF4m_unCenterProp_of_outLie {m f : ℕ} (h : F431UnOutLieProp m f) :
    burnsideF4m_UnCenterProp m f := by
  intro D _ hD A hev
  obtain ⟨T, S, g, z, t, V, hO | hO⟩ := h D hD A hev
  · exact ⟨T, A.Mb1, z, hO.sylow, hO.T_le, hO.T_le', hO.center_T⟩
  · exact ⟨T, A.Mb2, z, hO.sylow, hO.T_le', hO.T_le, hO.center_T⟩

open CFSG.Quasithin.H13.F431.D4q.Struct

@[expose] def burnsideF4m_UnCenterConcl {D : Type} [Group D] (A : LieAmalgamExt D) : Prop :=
  ∃ (T N : Subgroup ↥A.K) (z : ↥A.K), IsSylowTwoOf T ⊤ ∧ T ≤ A.Mb1 ∧ T ≤ A.Mb2 ∧
    ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ N, m * z * m⁻¹ = w

theorem burnsideF4m_unCenterConcl_of_kiso {D D' : Type} [Group D] [Group D']
    {A : LieAmalgamExt D} {A' : LieAmalgamExt D'} (L : KIso A A') :
    burnsideF4m_UnCenterConcl A' → burnsideF4m_UnCenterConcl A := by
  rintro ⟨T', N', z', hT, h1, h2, hc⟩
  set θ : ↥A'.K ≃* ↥A.K := L.ψ.symm with hθ
  refine ⟨T'.map θ.toMonoidHom, N'.map θ.toMonoidHom, θ z', ?_, ?_, ?_, ?_⟩
  · have h := (CFSG.QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv θ).2 hT
    rwa [Subgroup.map_top_of_surjective _ θ.surjective] at h
  · rw [← L.map_Mb1]
    exact Subgroup.map_mono h1
  · rw [← L.map_Mb2]
    exact Subgroup.map_mono h2
  · intro w hw hcw hw1
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.1 hw
    obtain ⟨m, hm, e⟩ := hc w₀ hw₀ (fun y hy => by
      apply θ.injective
      simpa using hcw (θ y) (Subgroup.mem_map_of_mem _ hy)) (fun h => hw1 (by simp [h]))
    exact ⟨θ m, Subgroup.mem_map_of_mem _ hm, by simpa using congrArg θ e⟩

theorem burnsideF4m_unCenterConcl_of_model {D : Type} [Group D] (A : LieAmalgamExt D)
    {T : Subgroup (MulAut D)} {z : MulAut D} (hT : IsSylowTwoOf T A.K)
    (h1 : T ≤ autStab A.P1) (h2 : T ≤ autStab A.P2) (hz : z ∈ A.K)
    (hc : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → w ≠ 1 → ∃ m ∈ A.K, m * z * m⁻¹ = w) :
    burnsideF4m_UnCenterConcl A := by
  have hTK : T ≤ A.K := hT.1
  refine ⟨T.subgroupOf A.K, ⊤, ⟨z, hz⟩, ?_, ?_, ?_, ?_⟩
  · have := (sub_isSylowTwoOf_iff A.K hTK le_rfl).2 hT
    rwa [Subgroup.subgroupOf_self] at this
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨A.K_le_Mbar (hTK hx), h1 hx⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨A.K_le_Mbar (hTK hx), h2 hx⟩
  · intro w hw hcw hw1
    rw [Subgroup.mem_subgroupOf] at hw
    obtain ⟨m, hm, e⟩ := hc (w : MulAut D) hw (fun y hy => by
      have := hcw ⟨y, hTK hy⟩ (by rw [Subgroup.mem_subgroupOf]; exact hy)
      exact congrArg Subtype.val this) (fun h => hw1 (Subtype.ext h))
    exact ⟨⟨m, hm⟩, Subgroup.mem_top _, Subtype.ext e⟩

end CFSG.Quasithin.H13.F431.Un
