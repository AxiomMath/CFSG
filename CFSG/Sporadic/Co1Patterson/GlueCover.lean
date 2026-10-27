module

public import CFSG.Sporadic.Co1Patterson.GlueNormal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

variable {n : ℕ} {L : Type} [Group L] {act : L →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))}
  {qf : (Fin n → ZMod 2) → ZMod 2} {bil : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2}
  {H H' : Type} [Group H] [Group H'] {S : ExtraspecialTypeSystem n L act qf bil H}
  {S' : ExtraspecialTypeSystem n L act qf bil H'}

namespace Glue

variable (G : Glue S S')

abbrev Δ' : Subgroup ↥G.P := G.Δ.subgroupOf G.P

instance Δ'_normal : G.Δ'.Normal :=
  (Subgroup.normal_subgroupOf_iff G.Δ_le_P).2 fun _ _ hh hk => G.conj_mem_Δ hk hh

abbrev Cover : Type := ↥G.P ⧸ G.Δ'

@[expose] noncomputable def π : G.Cover →* L :=
  QuotientGroup.lift G.Δ' ((S.φ.comp (MonoidHom.fst H H')).comp G.P.subtype) fun _ hx =>
    (mem_F.1 (G.mem_Δ.1 (Subgroup.mem_subgroupOf.1 hx)).1).1

theorem π_mk (g : ↥G.P) : G.π (QuotientGroup.mk g) = S.φ (g : H × H').1 := rfl

@[expose] def ζ : G.Cover := QuotientGroup.mk ⟨(S.z, 1), G.z1_mem_P⟩

theorem π_surj (hb : Nondeg bil) [Finite H] [Finite H'] : Function.Surjective G.π := by
  intro s
  obtain ⟨x, rfl⟩ := S.φ_surj s
  obtain ⟨y, hy⟩ := G.exists_mem_P hb x
  exact ⟨QuotientGroup.mk ⟨(x, y), hy⟩, rfl⟩

theorem mk_one_z : (QuotientGroup.mk ⟨((1 : H), S'.z), G.one_z_mem_P⟩ : G.Cover) = G.ζ := by
  have e : (⟨((1 : H), S'.z), G.one_z_mem_P⟩ : ↥G.P) =
      ⟨(S.z, 1), G.z1_mem_P⟩ * ⟨(S.z, S'.z), G.Δ_le_P G.zz_mem_Δ⟩ := by
    apply Subtype.ext
    simp [S.z_mul_self]
  have h1 : (QuotientGroup.mk ⟨(S.z, S'.z), G.Δ_le_P G.zz_mem_Δ⟩ : G.Cover) = 1 :=
    (QuotientGroup.eq_one_iff (⟨(S.z, S'.z), G.Δ_le_P G.zz_mem_Δ⟩ : ↥G.P)).2
      (Subgroup.mem_subgroupOf.2 G.zz_mem_Δ)
  rw [e, QuotientGroup.mk_mul, h1, mul_one]
  rfl

theorem π_ζ : G.π G.ζ = 1 := S.φ_z

theorem π_ker : G.π.ker = Subgroup.zpowers G.ζ := by
  refine le_antisymm (fun c hc => ?_) (Subgroup.zpowers_le.2 G.π_ζ)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  have h1 : S.φ (g : H × H').1 = 1 := hc
  have hgF := G.mem_F_of_mem_P g.2 h1
  rcases G.mem_Δ_or_z1_mul hgF with h | h
  · have : (QuotientGroup.mk g : G.Cover) = 1 :=
      (QuotientGroup.eq_one_iff g).2 (Subgroup.mem_subgroupOf.2 h)
    rw [this]
    exact one_mem _
  · have h2 : (QuotientGroup.mk (⟨(S.z, 1), G.z1_mem_P⟩ * g) : G.Cover) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 h)
    rw [QuotientGroup.mk_mul] at h2
    have h3 : (QuotientGroup.mk g : G.Cover) = G.ζ⁻¹ := eq_inv_of_mul_eq_one_right h2
    rw [h3]
    exact inv_mem (Subgroup.mem_zpowers _)

theorem ζ_mem_center : G.ζ ∈ Subgroup.center G.Cover := by
  rw [Subgroup.mem_center_iff]
  intro c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  show (QuotientGroup.mk g : G.Cover) * QuotientGroup.mk ⟨(S.z, 1), G.z1_mem_P⟩ = _
  rw [← QuotientGroup.mk_mul]
  show _ = (QuotientGroup.mk ⟨(S.z, 1), G.z1_mem_P⟩ : G.Cover) * QuotientGroup.mk g
  rw [← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext (z1_comm (g : H × H')).symm)

theorem ζ_orderOf : orderOf G.ζ = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · have e : (⟨(S.z, 1), G.z1_mem_P⟩ * ⟨(S.z, 1), G.z1_mem_P⟩ : ↥G.P) = 1 :=
      Subtype.ext (by simp [S.z_mul_self])
    show (QuotientGroup.mk ⟨(S.z, 1), G.z1_mem_P⟩ : G.Cover) ^ 2 = 1
    rw [pow_two, ← QuotientGroup.mk_mul, e]
    rfl
  · intro h
    exact G.z1_not_mem_Δ (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h))

theorem π_eq_one_iff {c : G.Cover} : G.π c = 1 ↔ c = 1 ∨ c = G.ζ := by
  rw [← MonoidHom.mem_ker, G.π_ker]
  exact CFSG.Monster.GMS.mem_zpowers_iff_of_orderOf_two G.ζ_orderOf

theorem ζ_ne_one : G.ζ ≠ 1 := fun h => by
  have := G.ζ_orderOf
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

end Glue

theorem exists_mulEquiv_of_split (hb : Nondeg bil) [Finite H] [Finite H'] (G : Glue S S')
    (K : Subgroup G.Cover) (hζK : G.ζ ∉ K) (hK : K.map G.π = ⊤) : Nonempty (H ≃* H') := by
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
  exact ⟨(MulEquiv.ofBijective ψ₁ ⟨hψ₁inj, hψ₁surj⟩).symm.trans
    (MulEquiv.ofBijective ψ₂ ⟨hψ₂inj, hψ₂surj⟩)⟩

end CFSG.Sporadic.Co1Patterson
