module

public import CFSG.Sporadic.Co1Patterson.GlueCover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

variable {n : ℕ} {L : Type} [Group L] {act : L →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))}
  {qf : (Fin n → ZMod 2) → ZMod 2} {bil : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2}
  {H H' : Type} [Group H] [Group H'] {S : ExtraspecialTypeSystem n L act qf bil H}
  {S' : ExtraspecialTypeSystem n L act qf bil H'}

theorem exists_mulEquiv_compat_of_split (hb : Nondeg bil) [Finite H] [Finite H'] (G : Glue S S')
    (K : Subgroup G.Cover) (hζK : G.ζ ∉ K) (hK : K.map G.π = ⊤) :
    ∃ e : H ≃* H', ∀ x, S'.φ (e x) = S.φ x := by
  let mk : ↥G.P →* G.Cover := QuotientGroup.mk' G.Δ'
  let T : Subgroup ↥G.P := K.comap mk
  let ψ₁ : ↥T →* H := (MonoidHom.fst H H').comp (G.P.subtype.comp T.subtype)
  let ψ₂ : ↥T →* H' := (MonoidHom.snd H H').comp (G.P.subtype.comp T.subtype)
  have hker : ∀ t : ↥T, S.φ (t.1 : H × H').1 = 1 → (t.1 : H × H') ∈ G.Δ := by
    intro t ht
    have h1 : mk t.1 = 1 := by
      rcases G.π_eq_one_iff.1 (show G.π (mk t.1) = 1 from ht) with h | h
      · exact h
      · exact absurd (h ▸ t.2) hζK
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff t.1).1 h1)
  have hlift : ∀ g : ↥G.P, ∃ t : ↥T,
      (t.1 : H × H') = g ∨ (t.1 : H × H') = (g : H × H') * ((1 : H), S'.z) := by
    intro g
    have hg : G.π (mk g) ∈ K.map G.π := hK ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hkg⟩ := hg
    have hmem : (mk g)⁻¹ * k ∈ G.π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
    rw [G.π_ker] at hmem
    rcases (CFSG.Monster.GMS.mem_zpowers_iff_of_orderOf_two G.ζ_orderOf).1 hmem with h1 | h1
    · refine ⟨⟨g, ?_⟩, Or.inl rfl⟩
      show mk g ∈ K
      rw [inv_mul_eq_one.1 h1]
      exact hk
    · refine ⟨⟨g * ⟨((1 : H), S'.z), G.one_z_mem_P⟩, ?_⟩, Or.inr rfl⟩
      show mk (g * ⟨((1 : H), S'.z), G.one_z_mem_P⟩) ∈ K
      have e : mk ⟨((1 : H), S'.z), G.one_z_mem_P⟩ = G.ζ := G.mk_one_z
      rw [map_mul, e]
      have e2 : mk g * G.ζ = k := by
        rw [← h1]
        group
      rw [e2]
      exact hk
  have hψ₁inj : Function.Injective ψ₁ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨⟨a, b⟩, hP⟩, hT⟩ ht
    have ha : a = 1 := ht
    subst ha
    have hb' : b = 1 := G.eq_one_of_one_mem_Δ (hker ⟨⟨(1, b), hP⟩, hT⟩ (map_one S.φ))
    subst hb'
    rfl
  have hψ₂inj : Function.Injective ψ₂ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨⟨a, b⟩, hP⟩, hT⟩ ht
    have hb' : b = 1 := ht
    subst hb'
    have hφ : S.φ a = 1 := by
      have h := Glue.mem_P0.1 (G.P_le_P0 hP)
      rw [h, map_one]
    have ha : a = 1 := G.eq_one_of_mem_Δ_one (hker ⟨⟨(a, 1), hP⟩, hT⟩ hφ)
    subst ha
    rfl
  have hψ₁surj : Function.Surjective ψ₁ := by
    intro x
    obtain ⟨y, hy⟩ := G.exists_mem_P hb x
    obtain ⟨t, ht | ht⟩ := hlift ⟨(x, y), hy⟩
    · exact ⟨t, by simp [ψ₁, ht]⟩
    · exact ⟨t, by simp [ψ₁, ht]⟩
  have hψ₂surj : Function.Surjective ψ₂ := by
    intro y
    obtain ⟨x, hx⟩ := G.exists_mem_P_snd hb y
    have hzx : (S.z * x, y) ∈ G.P := by
      have h := mul_mem G.z1_mem_P hx
      rwa [Prod.mk_mul_mk, one_mul] at h
    obtain ⟨t', ht' | ht'⟩ := hlift ⟨(x, y), hx⟩
    · exact ⟨t', by simp [ψ₂, ht']⟩
    obtain ⟨t, ht | ht⟩ := hlift ⟨(S.z * x, y), hzx⟩
    · exact ⟨t, by simp [ψ₂, ht]⟩
    exfalso
    have h1 : ((t'⁻¹ * t : ↥T) : H × H') = (S.z, 1) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht, ht']
      ext
      · simp only [Prod.fst_mul, Prod.fst_inv, mul_one]
        rw [← S.z_comm x]
        group
      · simp
    have h2 := hker (t'⁻¹ * t) (by rw [h1]; exact S.φ_z)
    rw [h1] at h2
    exact G.z1_not_mem_Δ h2
  let e₁ := MulEquiv.ofBijective ψ₁ ⟨hψ₁inj, hψ₁surj⟩
  let e₂ := MulEquiv.ofBijective ψ₂ ⟨hψ₂inj, hψ₂surj⟩
  refine ⟨e₁.symm.trans e₂, fun x => ?_⟩
  have hP0 := Glue.mem_P0.1 (G.P_le_P0 (e₁.symm x).1.2)
  have h1 : ψ₁ (e₁.symm x) = x := e₁.apply_symm_apply x
  calc S'.φ ((e₁.symm.trans e₂) x) = S'.φ (((e₁.symm x : ↥T) : ↥G.P) : H × H').2 := rfl
    _ = S.φ (((e₁.symm x : ↥T) : ↥G.P) : H × H').1 := hP0.symm
    _ = S.φ x := congrArg S.φ h1

end CFSG.Sporadic.Co1Patterson
