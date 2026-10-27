module

public import CFSG.Sporadic.Co1Patterson.GlueCover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

@[expose] def fibreProd {H E L : Type*} [Group H] [Group E] [Group L] (φ : H →* L)
    (π : E →* L) : Subgroup (H × E) :=
  MonoidHom.eqLocus (φ.comp (MonoidHom.fst H E)) (π.comp (MonoidHom.snd H E))

theorem mem_fibreProd {H E L : Type*} [Group H] [Group E] [Group L] {φ : H →* L}
    {π : E →* L} {g : H × E} : g ∈ fibreProd φ π ↔ φ g.1 = π g.2 := Iff.rfl

variable {n : ℕ} {L : Type} [Group L] {act : L →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))}
  {qf : (Fin n → ZMod 2) → ZMod 2} {bil : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2}
  {H H' : Type} [Group H] [Group H']

@[expose] def zζ (S : ExtraspecialTypeSystem n L act qf bil H) {E : Type*} [Group E]
    (π : E →* L) (ζ : E) (hζ : π ζ = 1) : fibreProd S.φ π :=
  ⟨(S.z, ζ), by rw [mem_fibreProd, S.φ_z, hζ]⟩

abbrev Twist (S : ExtraspecialTypeSystem n L act qf bil H) {E : Type*} [Group E] (π : E →* L)
    (ζ : E) (hζ : π ζ = 1) : Type _ :=
  fibreProd S.φ π ⧸ Subgroup.normalClosure {zζ S π ζ hζ}

variable (S : ExtraspecialTypeSystem n L act qf bil H)

theorem mem_normalClosure_zζ_iff {E : Type*} [Group E] {π : E →* L} {ζ : E} (hζ : π ζ = 1)
    (hζc : ∀ e, ζ * e = e * ζ) (hζ2 : ζ * ζ = 1) {x : fibreProd S.φ π} :
    x ∈ Subgroup.normalClosure {zζ S π ζ hζ} ↔ x = 1 ∨ x = zζ S π ζ hζ := by
  have hc : ∀ y : fibreProd S.φ π, zζ S π ζ hζ * y = y * zζ S π ζ hζ := fun y =>
    Subtype.ext (Prod.ext (S.z_comm _).symm (hζc _))
  have ho : orderOf (zζ S π ζ hζ) = 2 := by
    refine orderOf_eq_prime ?_ fun h => S.z_ne_one ?_
    · rw [pow_two]
      exact Subtype.ext (Prod.ext S.z_mul_self hζ2)
    · exact congrArg (fun y : fibreProd S.φ π => (y : H × E).1) h
  have hcen : Subgroup.zpowers (zζ S π ζ hζ) ≤ Subgroup.center (fibreProd S.φ π) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_center_iff.2 fun y => (hc y).symm)
  have hN : (Subgroup.zpowers (zζ S π ζ hζ)).Normal := ⟨fun y hy g => by
    rw [(Subgroup.mem_center_iff.1 (hcen hy) g), mul_inv_cancel_right]
    exact hy⟩
  constructor
  · intro hx
    have hx' : x ∈ Subgroup.zpowers (zζ S π ζ hζ) :=
      Subgroup.normalClosure_le_normal (by
        rintro _ rfl
        exact Subgroup.mem_zpowers _) hx
    exact (CFSG.Monster.GMS.mem_zpowers_iff_of_orderOf_two ho).1 hx'
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.subset_normalClosure rfl

theorem mk_eq_mk_iff_twist {E : Type*} [Group E] {π : E →* L} {ζ : E} (hζ : π ζ = 1)
    (hζc : ∀ e, ζ * e = e * ζ) (hζ2 : ζ * ζ = 1) {x y : fibreProd S.φ π} :
    (QuotientGroup.mk x : Twist S π ζ hζ) = QuotientGroup.mk y ↔
      y = x ∨ y = x * zζ S π ζ hζ := by
  rw [QuotientGroup.eq, mem_normalClosure_zζ_iff S hζ hζc hζ2, inv_mul_eq_one,
    inv_mul_eq_iff_eq_mul]
  exact or_congr eq_comm Iff.rfl

@[expose] def fibreEquiv {E E' : Type*} [Group E] [Group E'] (π : E →* L) (π' : E' →* L)
    (θ : E ≃* E') (h₀ : H) (hθ : ∀ e, π' (θ e) = S.φ h₀ * π e * (S.φ h₀)⁻¹) :
    fibreProd S.φ π ≃* fibreProd S.φ π' where
  toFun g := ⟨(h₀ * (g : H × E).1 * h₀⁻¹, θ (g : H × E).2), by
    rw [mem_fibreProd, hθ, map_mul, map_mul, map_inv, mem_fibreProd.1 g.2]⟩
  invFun g := ⟨(h₀⁻¹ * (g : H × E').1 * h₀, θ.symm (g : H × E').2), by
    have h := hθ (θ.symm (g : H × E').2)
    rw [MulEquiv.apply_symm_apply, ← mem_fibreProd.1 g.2] at h
    rw [mem_fibreProd, map_mul, map_mul, map_inv, h]
    group⟩
  left_inv g := by
    apply Subtype.ext
    ext
    · simp only
      group
    · simp
  right_inv g := by
    apply Subtype.ext
    ext
    · simp only
      group
    · simp
  map_mul' g g' := by
    apply Subtype.ext
    ext
    · simp only [Subgroup.coe_mul, Prod.fst_mul]
      group
    · simp

@[expose] noncomputable def twistEquiv {E E' : Type*} [Group E] [Group E'] (π : E →* L)
    (π' : E' →* L) {ζ : E} {ζ' : E'} (hζ : π ζ = 1) (hζ' : π' ζ' = 1) (θ : E ≃* E') (h₀ : H)
    (hθ : ∀ e, π' (θ e) = S.φ h₀ * π e * (S.φ h₀)⁻¹) (hθζ : θ ζ = ζ') :
    Twist S π ζ hζ ≃* Twist S π' ζ' hζ' :=
  QuotientGroup.congr _ _ (fibreEquiv S π π' θ h₀ hθ) (by
    rw [Subgroup.map_normalClosure _ _ (fibreEquiv S π π' θ h₀ hθ).surjective,
      Set.image_singleton]
    congr 2
    apply Subtype.ext
    ext
    · show h₀ * S.z * h₀⁻¹ = S.z
      rw [S.z_comm h₀, mul_inv_cancel_right]
    · exact hθζ)

variable {S} {S' : ExtraspecialTypeSystem n L act qf bil H'}

namespace Glue

variable (G : Glue S S')

@[expose] noncomputable def toFibre : ↥G.P →* fibreProd S.φ G.π :=
  MonoidHom.codRestrict (((MonoidHom.fst H H').comp G.P.subtype).prod (QuotientGroup.mk' G.Δ'))
    (fibreProd S.φ G.π) fun _ => rfl

theorem toFibre_injective : Function.Injective G.toFibre := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : (g : H × H').1 = 1 := congrArg (fun x : fibreProd S.φ G.π => (x : H × G.Cover).1) hg
  have h2 : (QuotientGroup.mk g : G.Cover) = 1 :=
    congrArg (fun x : fibreProd S.φ G.π => (x : H × G.Cover).2) hg
  have hΔ : (g : H × H') ∈ G.Δ := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff g).1 h2)
  obtain ⟨⟨a, b⟩, hgP⟩ := g
  simp only at h1
  subst h1
  have hb1 : b = 1 := G.eq_one_of_one_mem_Δ hΔ
  subst hb1
  rfl

theorem toFibre_surjective : Function.Surjective G.toFibre := by
  rintro ⟨⟨h, e⟩, he⟩
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective e
  have hφ : S.φ (h * ((g₀ : H × H').1)⁻¹) = 1 := by
    rw [map_mul, map_inv, mem_fibreProd.1 he]
    exact mul_inv_cancel _
  obtain ⟨c, hc⟩ := G.exists_mem_Δ_fst hφ
  refine ⟨⟨(h * ((g₀ : H × H').1)⁻¹, c), G.Δ_le_P hc⟩ * g₀, ?_⟩
  apply Subtype.ext
  ext
  · show h * ((g₀ : H × H').1)⁻¹ * (g₀ : H × H').1 = h
    group
  · show (QuotientGroup.mk (⟨(h * ((g₀ : H × H').1)⁻¹, c), G.Δ_le_P hc⟩ * g₀) : G.Cover) =
      QuotientGroup.mk g₀
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hc),
      one_mul]

@[expose] noncomputable def fibreMulEquiv : ↥G.P ≃* fibreProd S.φ G.π :=
  MulEquiv.ofBijective G.toFibre ⟨G.toFibre_injective, G.toFibre_surjective⟩

@[expose] noncomputable def fibreToSnd : fibreProd S.φ G.π →* H' :=
  ((MonoidHom.snd H H').comp G.P.subtype).comp G.fibreMulEquiv.symm.toMonoidHom

theorem fibreToSnd_surjective (hb : Nondeg bil) [Finite H] [Finite H'] :
    Function.Surjective G.fibreToSnd := by
  intro y
  obtain ⟨x, hx⟩ := G.exists_mem_P_snd hb y
  refine ⟨G.fibreMulEquiv ⟨(x, y), hx⟩, ?_⟩
  simp [fibreToSnd]

theorem fibreMulEquiv_z1 :
    G.fibreMulEquiv ⟨(S.z, 1), G.z1_mem_P⟩ = zζ S G.π G.ζ G.π_ζ := rfl

theorem ker_fibreToSnd :
    G.fibreToSnd.ker = Subgroup.normalClosure {zζ S G.π G.ζ G.π_ζ} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := G.fibreMulEquiv.surjective x
    have hg2 : (g : H × H').2 = 1 := by
      have := MonoidHom.mem_ker.1 hx
      simpa [fibreToSnd] using this
    obtain ⟨⟨a, b⟩, hgP⟩ := g
    simp only at hg2
    subst hg2
    rcases G.eq_of_mem_P_snd_one hgP with rfl | rfl
    · have : (⟨((1 : H), (1 : H')), hgP⟩ : ↥G.P) = 1 := rfl
      rw [this, map_one]
      exact one_mem _
    · rw [show (⟨(S.z, (1 : H')), hgP⟩ : ↥G.P) = ⟨(S.z, 1), G.z1_mem_P⟩ from rfl,
        fibreMulEquiv_z1]
      exact Subgroup.subset_normalClosure rfl
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ rfl
    rw [SetLike.mem_coe, MonoidHom.mem_ker, ← fibreMulEquiv_z1]
    simp [fibreToSnd]

end Glue

theorem nonempty_mulEquiv_twist (hb : Nondeg bil) [Finite H] [Finite H'] (G : Glue S S') :
    Nonempty (H' ≃* Twist S G.π G.ζ G.π_ζ) :=
  ⟨(QuotientGroup.quotientKerEquivOfSurjective _ (G.fibreToSnd_surjective hb)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq G.ker_fibreToSnd)⟩

end CFSG.Sporadic.Co1Patterson
