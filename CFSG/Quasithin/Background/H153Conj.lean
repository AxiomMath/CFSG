module

public import CFSG.Quasithin.Background.H153Defs
public import CFSG.Quasithin.Background.H153Sext

public section

open scoped Pointwise

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ZTrans

@[expose] def cjS (c : S24) : S24 ≃* S24 := (MulAut.conj c : S24 ≃* S24)

theorem cjS_apply (c x : S24) : cjS c x = c * x * c⁻¹ := rfl

theorem cjS_symm_apply (c x : S24) : (cjS c).symm x = c⁻¹ * x * c := by
  rw [MulEquiv.symm_apply_eq, cjS_apply]
  group

theorem AutPerm_map_cj {c : S24} (hc : c ∈ AutPerm) :
    AutPerm.map (cjS c).toMonoidHom = AutPerm := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact AutPerm.mul_mem (AutPerm.mul_mem hc hy) (AutPerm.inv_mem hc)
  · intro hx
    refine ⟨c⁻¹ * x * c, AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hc) hx) hc, ?_⟩
    show c * (c⁻¹ * x * c) * c⁻¹ = x
    group

theorem MY_conj {c : S24} (hc : c ∈ AutPerm) :
    MY M24g (c • S0) = (MY M24g S0).map (cjS c).toMonoidHom := by
  have h1 : MulAction.stabilizer S24 (c • S0) =
      (MulAction.stabilizer S24 S0).map (cjS c).toMonoidHom :=
    MulAction.stabilizer_smul_eq_stabilizer_map_conj c S0
  have h2 : M24g.map (cjS c).toMonoidHom = M24g := AutPerm_map_cj hc
  unfold MY
  rw [h1, Subgroup.map_inf _ _ _ (cjS c).injective, h2]

theorem KY_conj {c : S24} (hc : c ∈ AutPerm) :
    KY M24g (c • S0) = (KY M24g S0).map (cjS c).toMonoidHom := by
  unfold KY
  rw [MY_conj hc, pCoreOf_map_of_injective 2 _ (cjS c).injective]

theorem rImg_comp_conj {V : Type*} [CommGroup V] (ρ : ↥M24g →* MulAut V) (c : ↥M24g)
    (A : Subgroup S24) :
    rImg (ρ.comp (MulAut.conj c).toMonoidHom) A = rImg ρ (A.map (cjS (c : S24)).toMonoidHom) := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨c * a * c⁻¹, Subgroup.mem_subgroupOf.2 ⟨(a : S24), Subgroup.mem_subgroupOf.1 ha, rfl⟩,
      rfl⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a₀, ha₀, hab⟩ := Subgroup.mem_subgroupOf.1 hb
    have hab' : (c : S24) * a₀ * (c : S24)⁻¹ = (b : S24) := hab
    have ha₀' : a₀ = (c : S24)⁻¹ * (b : S24) * (c : S24) := by
      rw [← hab']
      group
    have hmem : (c : S24)⁻¹ * (b : S24) * (c : S24) ∈ M24g :=
      M24g.mul_mem (M24g.mul_mem (M24g.inv_mem c.2) b.2) c.2
    refine ⟨⟨(c : S24)⁻¹ * (b : S24) * (c : S24), hmem⟩, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · show (c : S24)⁻¹ * (b : S24) * (c : S24) ∈ A
      rw [← ha₀']
      exact ha₀
    · show ρ (c * ⟨(c : S24)⁻¹ * (b : S24) * (c : S24), hmem⟩ * c⁻¹) = ρ b
      congr 1
      apply Subtype.ext
      show (c : S24) * ((c : S24)⁻¹ * (b : S24) * (c : S24)) * (c : S24)⁻¹ = b
      group

theorem rho_comp_conj_apply {V : Type*} [CommGroup V] (ρ : ↥M24g →* MulAut V) (c γ : ↥M24g) :
    (ρ.comp (MulAut.conj c).toMonoidHom) γ = ρ (c * γ * c⁻¹) := by
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem isO23_map (φ : S24 ≃* S24) {G N : Subgroup S24} (h : IsO23' G N) :
    IsO23' (G.map φ.toMonoidHom) (N.map φ.toMonoidHom) := by
  obtain ⟨hNG, hNn, hcore, h3, hmax⟩ := h
  have hcore' : pCoreOf 2 (G.map φ.toMonoidHom) = (pCoreOf 2 G).map φ.toMonoidHom :=
    pCoreOf_map_of_injective 2 _ φ.injective G
  refine ⟨Subgroup.map_mono hNG, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨n, hn, rfl⟩
    exact ⟨g * n * g⁻¹, hNn g hg n hn, by simp⟩
  · rw [hcore']
    exact Subgroup.map_mono hcore
  · rintro _ ⟨n, hn, rfl⟩
    obtain ⟨k, hk⟩ := h3 n hn
    refine ⟨k, ?_⟩
    rw [hcore']
    exact ⟨n ^ 3 ^ k, hk, by simp⟩
  · intro N' hN'G hN'n hN'core hN'3
    set N'' := N'.map φ.symm.toMonoidHom with hN''
    have hmem : ∀ y : S24, y ∈ N' → φ.symm y ∈ N'' := fun y hy => ⟨y, hy, rfl⟩
    have h1 : N'' ≤ G := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨g, hg, hgy⟩ := hN'G hy
      have : φ.symm y = g := by rw [← hgy]; exact φ.symm_apply_apply g
      show φ.symm y ∈ G
      rw [this]
      exact hg
    have h2 : ∀ g ∈ G, ∀ n ∈ N'', g * n * g⁻¹ ∈ N'' := by
      intro g hg n hn
      obtain ⟨y, hy, rfl⟩ := hn
      have := hN'n (φ g) ⟨g, hg, rfl⟩ y hy
      have e : g * φ.symm y * g⁻¹ = φ.symm (φ g * y * (φ g)⁻¹) := by simp
      have h' : g * φ.symm y * g⁻¹ ∈ N'' := by
        rw [e]
        exact hmem _ this
      exact h'
    have h3' : pCoreOf 2 G ≤ N'' := by
      intro c hc
      have : φ c ∈ N' := hN'core (by rw [hcore']; exact ⟨c, hc, rfl⟩)
      have e : c = φ.symm (φ c) := (φ.symm_apply_apply c).symm
      rw [e]
      exact hmem _ this
    have h4 : ∀ n ∈ N'', ∃ k : ℕ, n ^ (3 ^ k) ∈ pCoreOf 2 G := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := hN'3 y hy
      rw [hcore'] at hk
      obtain ⟨c, hc, hcy⟩ := hk
      refine ⟨k, ?_⟩
      have : φ.symm (y ^ 3 ^ k) = c := by rw [← hcy]; exact φ.symm_apply_apply c
      show (φ.symm y) ^ 3 ^ k ∈ pCoreOf 2 G
      rw [← map_pow]
      exact this ▸ hc
    have h5 := hmax N'' h1 h2 h3' h4
    intro y hy
    refine ⟨φ.symm y, h5 (hmem y hy), ?_⟩
    exact φ.apply_symm_apply y

theorem exists_pi_map (φ : S24 ≃* S24) {G N : Subgroup S24}
    (h : ∃ π : ↥G →* Equiv.Perm (Fin 6), Function.Surjective π ∧ π.ker = N.subgroupOf G) :
    ∃ π : ↥(G.map φ.toMonoidHom) →* Equiv.Perm (Fin 6), Function.Surjective π ∧
      π.ker = (N.map φ.toMonoidHom).subgroupOf (G.map φ.toMonoidHom) := by
  obtain ⟨π₀, hs, hk⟩ := h
  let ψ : ↥(G.map φ.toMonoidHom) ≃* ↥G :=
    (G.equivMapOfInjective φ.toMonoidHom φ.injective).symm
  have hψ : ∀ x : ↥(G.map φ.toMonoidHom), ((ψ x : ↥G) : S24) = φ.symm (x : S24) := by
    intro x
    have h1 : ((G.equivMapOfInjective φ.toMonoidHom φ.injective (ψ x) :
        ↥(G.map φ.toMonoidHom)) : S24) = φ ((ψ x : ↥G) : S24) :=
      Subgroup.coe_equivMapOfInjective_apply G φ.toMonoidHom φ.injective _
    have h2 : G.equivMapOfInjective φ.toMonoidHom φ.injective (ψ x) = x :=
      (G.equivMapOfInjective φ.toMonoidHom φ.injective).apply_symm_apply x
    rw [h2] at h1
    rw [h1]
    exact (φ.symm_apply_apply _).symm
  refine ⟨π₀.comp ψ.toMonoidHom, hs.comp ψ.surjective, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have h1 : (π₀.comp ψ.toMonoidHom) x = 1 ↔ ψ x ∈ π₀.ker := Iff.rfl
  rw [h1, hk, Subgroup.mem_subgroupOf, hψ]
  constructor
  · intro hx
    exact ⟨_, hx, φ.apply_symm_apply _⟩
  · rintro ⟨y, hy, hyx⟩
    have : φ.symm (x : S24) = y := by rw [← hyx]; exact φ.symm_apply_apply y
    rw [this]
    exact hy

theorem isDualOfConj_conj {V : Type*} [CommGroup V] (ρ : ↥M24g →* MulAut V) (c : ↥M24g)
    {G K : Subgroup S24} {A B : Subgroup V}
    (h : IsDualOfConj' (ρ.comp (MulAut.conj c).toMonoidHom) G A B K) :
    IsDualOfConj' ρ (G.map (cjS (c : S24)).toMonoidHom) A B
      (K.map (cjS (c : S24)).toMonoidHom) := by
  obtain ⟨pr, h1, h2, h3, h4, h5, h6⟩ := h
  have hmemK : ∀ k : S24, k ∈ K.map (cjS (c : S24)).toMonoidHom ↔ (cjS (c : S24)).symm k ∈ K := by
    intro k
    constructor
    · rintro ⟨k₀, hk₀, rfl⟩
      simpa using hk₀
    · intro hk
      exact ⟨_, hk, (cjS (c : S24)).apply_symm_apply k⟩
  refine ⟨fun x k => pr x ((cjS (c : S24)).symm k), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx k hk k' hk'
    show pr x ((cjS (c : S24)).symm (k * k')) = _
    rw [map_mul]
    exact h1 x hx _ ((hmemK k).1 hk) _ ((hmemK k').1 hk')
  · intro x hx x' hx' k hk
    exact h2 x hx x' hx' _ ((hmemK k).1 hk)
  · intro x hx k hk
    exact h3 x hx _ ((hmemK k).1 hk)
  · intro x hx hxB
    obtain ⟨k₀, hk₀, hne⟩ := h4 x hx hxB
    refine ⟨cjS (c : S24) k₀, ⟨k₀, hk₀, rfl⟩, ?_⟩
    show pr x ((cjS (c : S24)).symm (cjS (c : S24) k₀)) ≠ 0
    rw [MulEquiv.symm_apply_apply]
    exact hne
  · intro k hk hk1
    obtain ⟨x, hx, hne⟩ := h5 _ ((hmemK k).1 hk) (by
      intro h'
      apply hk1
      have : (cjS (c : S24)).symm k = (cjS (c : S24)).symm 1 := by rw [h', map_one]
      exact (cjS (c : S24)).symm.injective (by rw [this, map_one]))
    exact ⟨x, hx, hne⟩
  · intro g hg x hx k hk
    obtain ⟨g₀, hg₀, hgg⟩ := hg
    have hgA : (g : S24) = (c : S24) * g₀ * (c : S24)⁻¹ := hgg.symm
    have hy : (c : S24)⁻¹ * (g : S24) * (c : S24) = g₀ := by rw [hgA]; group
    have hy' : (c : S24)⁻¹ * (g : S24) * (c : S24) ∈ AutPerm :=
      AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem c.2) g.2) c.2
    have hg' : ((⟨(c : S24)⁻¹ * (g : S24) * (c : S24), hy'⟩ : ↥M24g) : S24) ∈ G := by
      show (c : S24)⁻¹ * (g : S24) * (c : S24) ∈ G
      rw [hy]
      exact hg₀
    have e1 := h6 ⟨(c : S24)⁻¹ * (g : S24) * (c : S24), hy'⟩ hg' x hx
      ((cjS (c : S24)).symm k) ((hmemK k).1 hk)
    have e2 : (ρ.comp (MulAut.conj c).toMonoidHom) ⟨(c : S24)⁻¹ * (g : S24) * (c : S24), hy'⟩ =
        ρ g := by
      show ρ (c * ⟨(c : S24)⁻¹ * (g : S24) * (c : S24), hy'⟩ * c⁻¹) = ρ g
      congr 1
      apply Subtype.ext
      show (c : S24) * ((c : S24)⁻¹ * (g : S24) * (c : S24)) * (c : S24)⁻¹ = g
      group
    rw [e2] at e1
    have e3 : (cjS (c : S24)).symm ((g : S24) * k * (g : S24)⁻¹) =
        (c : S24)⁻¹ * (g : S24) * (c : S24) * (cjS (c : S24)).symm k *
          ((c : S24)⁻¹ * (g : S24) * (c : S24))⁻¹ := by
      rw [cjS_symm_apply, cjS_symm_apply]
      group
    show pr (ρ g x) ((cjS (c : S24)).symm ((g : S24) * k * (g : S24)⁻¹)) =
      pr x ((cjS (c : S24)).symm k)
    rw [e3]
    exact e1

end CFSG.Quasithin.H153
