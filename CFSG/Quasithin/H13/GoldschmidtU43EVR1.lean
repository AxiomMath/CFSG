module

public import CFSG.Quasithin.H13.GoldschmidtU43EA6Syl3
public import CFSG.Quasithin.H13.GoldschmidtU43EV2

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

structure IsV3 (V₃ : Subgroup G) : Prop where
  le : V₃ ≤ S.Vg
  pgroup : IsPGroup 3 V₃
  max : ∀ T : Subgroup G, T ≤ S.Vg → IsPGroup 3 T → T ≤ V₃
  conj : ∀ c ∈ S.Cg1, ∀ x ∈ V₃, c * x * c⁻¹ ∈ V₃

theorem exists_isV3 (hAU : (S.A : G) ∈ Uz z) : ∃ V₃ : Subgroup G, S.IsV3 V₃ := by
  obtain ⟨V₃, hle, hP, hmax, hconj⟩ := S.exists_V3 hAU
  exact ⟨V₃, ⟨hle, hP, hmax, hconj⟩⟩

@[expose] noncomputable def rho3 (ρ : G) : G := S.a₂G⁻¹ * ρ * S.a₂G

@[expose] noncomputable def rho4 (ρ : G) : G := S.a₂G⁻¹ * S.rho2 ρ * S.a₂G

omit [Finite G] in
theorem a₂G_mul_a₂G : S.a₂G * S.a₂G = z := congrArg Subtype.val S.a₂_sq

omit [Finite G] in
theorem conj_a₂G_of_inv {x : G} (hx : z * x * z⁻¹ = x⁻¹) :
    S.a₂G * x * S.a₂G⁻¹ = (S.a₂G⁻¹ * x * S.a₂G)⁻¹ := by
  have e : S.a₂G * x * S.a₂G⁻¹ =
      S.a₂G⁻¹ * ((S.a₂G * S.a₂G) * x * (S.a₂G * S.a₂G)⁻¹) * S.a₂G := by group
  rw [e, S.a₂G_mul_a₂G, hx]
  group

omit [Finite G] in
theorem conj_a₂G_rho3 (ρ : G) : S.a₂G * S.rho3 ρ * S.a₂G⁻¹ = ρ := by
  unfold rho3
  group

omit [Finite G] in
theorem conj_a₂G_rho4 (ρ : G) : S.a₂G * S.rho4 ρ * S.a₂G⁻¹ = S.rho2 ρ := by
  unfold rho4
  group

omit [Finite G] in
theorem conj_a₂G_rho {ρ : G} (hρ : z * ρ * z⁻¹ = ρ⁻¹) : S.a₂G * ρ * S.a₂G⁻¹ = (S.rho3 ρ)⁻¹ :=
  S.conj_a₂G_of_inv hρ

omit [Finite G] in
theorem conj_a₂G_rho2 {ρ : G} (hρ : z * ρ * z⁻¹ = ρ⁻¹) :
    S.a₂G * S.rho2 ρ * S.a₂G⁻¹ = (S.rho4 ρ)⁻¹ :=
  S.conj_a₂G_of_inv (S.z_rho2 hρ)

section Sylow

variable {S} {V₃ : Subgroup G}

theorem Ag_le_V3 (hV : S.IsV3 V₃) (hAU : (S.A : G) ∈ Uz z) (r : S.Rho) : S.Ag r ≤ V₃ :=
  hV.max _ (S.Ag_le_Vg r hAU) (S.isPGroup_Ag r)

theorem Bg_le_V3 (hV : S.IsV3 V₃) (hAU : (S.A : G) ∈ Uz z) (r : S.Rho) : S.Bg r ≤ V₃ :=
  hV.max _ (S.Bg_le_Vg r hAU) (S.isPGroup_Bg r)

theorem rho_mem_Ag (r : S.Rho) : r.ρ ∈ S.Ag r := Subgroup.subset_closure (by simp)

theorem rho2_mem_Ag (r : S.Rho) : S.rho2 r.ρ ∈ S.Ag r := Subgroup.subset_closure (by simp)

theorem rho3_mem_Bg (r : S.Rho) : S.rho3 r.ρ ∈ S.Bg r := by
  refine (S.mem_Bg r).mpr ?_
  rw [S.conj_a₂G_rho3]
  exact S.rho_mem_Ag r

theorem rho4_mem_Bg (r : S.Rho) : S.rho4 r.ρ ∈ S.Bg r := by
  refine (S.mem_Bg r).mpr ?_
  rw [S.conj_a₂G_rho4]
  exact S.rho2_mem_Ag r

theorem exists_three_group (hV : S.IsV3 V₃) (hAU : (S.A : G) ∈ Uz z) (r : S.Rho) :
    ∃ Q : Subgroup G, IsPGroup 3 Q ∧ S.Mg ≤ Q ∧ V₃ ≤ Q := by
  have hσ₂C : (S.σ₂ : G) ∈ S.Cg1 := by
    rw [Cg1, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val S.σ₁σ₂_comm.symm
  have hnorm : Subgroup.zpowers (S.σ₂ : G) ≤ Subgroup.normalizer (V₃ : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hV.conj _ hσ₂C x hx
    · intro hx
      have := hV.conj _ (inv_mem hσ₂C) _ hx
      simpa [mul_assoc] using this
  have h3 : (S.σ₂ : G) ^ 3 = 1 := S.pow_three_Tg S.σ₂G_mem_Tg
  have h1 : (S.σ₂ : G) ≠ 1 := fun h => S.σ₂_ne_one (Subtype.ext h)
  have hp2 : IsPGroup 3 (Subgroup.zpowers (S.σ₂ : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime h3 h1]; norm_num)
  have hQ : IsPGroup 3 (Subgroup.zpowers (S.σ₂ : G) ⊔ V₃ : Subgroup G) :=
    hp2.to_sup_of_normal_right' hV.pgroup hnorm
  have hσQ : (S.σ₂ : G) ∈ Subgroup.zpowers (S.σ₂ : G) ⊔ V₃ :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hVQ : V₃ ≤ Subgroup.zpowers (S.σ₂ : G) ⊔ V₃ := le_sup_right
  refine ⟨_, hQ, ?_, hVQ⟩
  have hρ : r.ρ ∈ V₃ := S.Ag_le_V3 hV hAU r (S.rho_mem_Ag r)
  have hρ₂ : S.rho2 r.ρ ∈ V₃ := S.Ag_le_V3 hV hAU r (S.rho2_mem_Ag r)
  have hσ₁ : (S.σ₁ : G) ∈ V₃ := S.Ag_le_V3 hV hAU r (S.σ₁_mem_Ag r)
  have hσ₁Q : (S.σ₁ : G) ∈ Subgroup.zpowers (S.σ₂ : G) ⊔ V₃ := hVQ hσ₁
  refine (S.Mg_le_closure r).trans ?_
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl | rfl)
  · rw [sigG_eq]
    exact mul_mem hσ₁Q hσQ
  · rw [sigp_eq]
    exact mul_mem hσ₁Q (inv_mem hσQ)
  · exact hVQ hρ
  · exact hVQ hρ₂

end Sylow

theorem le_Ng_of_isPGroup (e : S.Nbar ≃* alternatingGroup (Fin 6)) {Q : Subgroup G}
    (hQ : IsPGroup 3 Q) (hMQ : S.Mg ≤ Q) : Q ≤ S.Ng := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 S.Nbar))
  obtain ⟨Qs, hQs⟩ := S.exists_sylow_preimage P e
  obtain ⟨Q', hQQ'⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Qs Q'
  have hmem : ∀ x ∈ (Q' : Subgroup G), g⁻¹ * x * g ∈ S.preimageNbar (P : Subgroup S.Nbar) := by
    intro x hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    rw [← hQs]
    simpa [MulAut.smul_def, mul_assoc] using hx
  set M₀ : Subgroup G := S.Mg.map (MulAut.conj g⁻¹).toMonoidHom with hM₀
  have hM₀S : M₀ ≤ S.preimageNbar (P : Subgroup S.Nbar) := by
    rintro _ ⟨m, hm, rfl⟩
    have := hmem m (hQQ' (hMQ hm))
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hab : ∀ a ∈ M₀, ∀ b ∈ M₀, a * b = b * a := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩
    show g⁻¹ * m * g⁻¹⁻¹ * (g⁻¹ * m' * g⁻¹⁻¹) = g⁻¹ * m' * g⁻¹⁻¹ * (g⁻¹ * m * g⁻¹⁻¹)
    have := S.abelian_Mg m hm m' hm'
    calc g⁻¹ * m * g⁻¹⁻¹ * (g⁻¹ * m' * g⁻¹⁻¹) = g⁻¹ * (m * m') * g⁻¹⁻¹ := by group
      _ = g⁻¹ * (m' * m) * g⁻¹⁻¹ := by rw [this]
      _ = g⁻¹ * m' * g⁻¹⁻¹ * (g⁻¹ * m * g⁻¹⁻¹) := by group
  have hcard : Nat.card M₀ = 81 := by
    rw [hM₀, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, S.card_Mg_eq_81]
  have heq : M₀ = S.Mg := S.unique_abelian_Msyl P e hM₀S hab hcard
  have hgN : g ∈ S.Ng := by
    rw [S.mem_Ng]
    intro x
    constructor
    · intro hx
      have hx' : x ∈ M₀ := by rw [heq]; exact hx
      obtain ⟨m, hm, hmx⟩ := hx'
      have : m = g * x * g⁻¹ := by
        have h' : g⁻¹ * m * g = x := by simpa [MulAut.conj_apply] using hmx
        rw [← h']
        group
      rw [← this]
      exact hm
    · intro hx
      have : x ∈ M₀ := ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩
      rwa [heq] at this
  intro x hx
  have h1 : g⁻¹ * x * g ∈ S.Ng := S.preimageNbar_le_Ng _ (hmem x (hQQ' hx))
  have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem hgN h1) (inv_mem hgN)

section Normalizer

variable {S} {V₃ : Subgroup G}

theorem V3_le_Ng (e : S.Nbar ≃* alternatingGroup (Fin 6)) (hV : S.IsV3 V₃)
    (hAU : (S.A : G) ∈ Uz z) (r : S.Rho) : V₃ ≤ S.Ng := by
  obtain ⟨Q, hQ, hMQ, hVQ⟩ := S.exists_three_group hV hAU r
  exact hVQ.trans (S.le_Ng_of_isPGroup e hQ hMQ)

theorem rho3_mem_V3 (hV : S.IsV3 V₃) (hAU : (S.A : G) ∈ Uz z) (r : S.Rho) :
    S.rho3 r.ρ ∈ V₃ := S.Bg_le_V3 hV hAU r (S.rho3_mem_Bg r)

theorem rho4_mem_V3 (hV : S.IsV3 V₃) (hAU : (S.A : G) ∈ Uz z) (r : S.Rho) :
    S.rho4 r.ρ ∈ V₃ := S.Bg_le_V3 hV hAU r (S.rho4_mem_Bg r)

theorem rho3_mem_Ng (e : S.Nbar ≃* alternatingGroup (Fin 6)) (hV : S.IsV3 V₃)
    (hAU : (S.A : G) ∈ Uz z) (r : S.Rho) : S.rho3 r.ρ ∈ S.Ng :=
  S.V3_le_Ng e hV hAU r (S.rho3_mem_V3 hV hAU r)

theorem rho4_mem_Ng (e : S.Nbar ≃* alternatingGroup (Fin 6)) (hV : S.IsV3 V₃)
    (hAU : (S.A : G) ∈ Uz z) (r : S.Rho) : S.rho4 r.ρ ∈ S.Ng :=
  S.V3_le_Ng e hV hAU r (S.rho4_mem_V3 hV hAU r)

end Normalizer

end JWSetup

end CFSG.Quasithin.H13.U43
