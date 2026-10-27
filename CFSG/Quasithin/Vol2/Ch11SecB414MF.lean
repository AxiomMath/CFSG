module

public import CFSG.Quasithin.Vol2.Ch4Sec3L43L34

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

@[expose] def Concl (Γ V Z L X : Subgroup G) (F : Type) [Field F]
    (α : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))
    (K : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))) (k : ℕ) : Prop :=
  (k = 0 → UntwistedFixed V Z L X (α.ker.map Γ.subtype)) ∧
    (k ≠ 0 → TwistedFixed V Z L X (α.ker.map Γ.subtype)) ∧
    ∃ j : ℕ, j < 3 ∧ (j = 0 ↔ k = 0) ∧
      (j = 1 → ∀ v ∈ V, IsFixedMod X Z v →
        (∀ γ : ↥Γ, α γ ∈ pCoreOf 2 K → (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∈ Z) → v ∈ Z) ∧
      ∀ α₀' : ↥K →* ↥(StatedSL 2 F), Function.Surjective α₀' →
        α₀'.ker = (pCoreOf 2 K).subgroupOf K →
        ∀ α₀ : ↥L →* ↥(StatedSL 2 F),
          (∀ (l : ↥L) (γ : ↥Γ) (p : ↥K), (γ : G) = l →
            (p : GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) = α γ → α₀ l = α₀' p) →
        ∀ γx : ↥Γ, (γx : G) ∈ X → α γx ≠ 1 →
          ∃ μ : F, IsNatEigSection K (α γx) α₀' ⊥ (pCoreOf 2 K) μ ∧
            ∃ l : List (Subgroup G × Option F), IsLabSeries (L ⊔ X) L (γx : G) α₀ Z l V ∧
              labMultiset l = ({μ ^ (j + 1), (μ ^ j)⁻¹, μ ^ j * μ⁻¹} : Multiset F)

variable {Γ V Z L X : Subgroup G} {F : Type} [Field F]

theorem concl_of_iff {α : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)}
    {K : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))} {k k' : ℕ}
    (hk : k = 0 ↔ k' = 0) (h : Concl Γ V Z L X F α K k') : Concl Γ V Z L X F α K k := by
  obtain ⟨h1, h2, j, hj3, hj0, hj1, heig⟩ := h
  exact ⟨fun h0 => h1 (hk.mp h0), fun h0 => h2 (fun h' => h0 (hk.mpr h')), j, hj3,
    hj0.trans hk.symm, hj1, heig⟩

theorem pCoreOf_map_inj {X' X'' : Type*} [Group X'] [Group X''] (φ : X' →* X'')
    (hφ : Function.Injective φ) (A : Subgroup X') :
    pCoreOf 2 (A.map φ) = (pCoreOf 2 A).map φ := by
  let ψ : ↥A ≃* ↥(A.map φ) := A.equivMapOfInjective φ hφ
  unfold pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 ψ, Subgroup.map_map, Subgroup.map_map]
  rfl

noncomputable abbrev eqv {H H' : Type} [Group H] [Group H'] (φ : H ≃* H') (K : Subgroup H) :
    ↥K ≃* ↥(K.map φ.toMonoidHom) :=
  K.equivMapOfInjective φ.toMonoidHom φ.injective

theorem coe_eqv {H H' : Type} [Group H] [Group H'] (φ : H ≃* H') (K : Subgroup H) (k : ↥K) :
    ((eqv φ K k : ↥(K.map φ.toMonoidHom)) : H') = φ k := rfl

theorem isNatEigSection_of_map {H H' : Type} [Group H] [Group H'] (φ : H ≃* H')
    {K : Subgroup H} {x : H} {α₀ : ↥K →* ↥(StatedSL 2 F)} {C : Subgroup H} {a : F}
    (h : IsNatEigSection (K.map φ.toMonoidHom) (φ x)
      (α₀.comp (eqv φ K).symm.toMonoidHom) ⊥ (C.map φ.toMonoidHom) a) :
    IsNatEigSection K x α₀ ⊥ C a := by
  obtain ⟨β, hs, hk, hK, hx⟩ := h
  have e : ∀ k : ↥K, (α₀.comp (eqv φ K).symm.toMonoidHom) (eqv φ K k) = α₀ k :=
    fun k => by rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  refine ⟨β.comp (eqv φ C).toMonoidHom, hs.comp (eqv φ C).surjective,
    fun c => ?_, fun k c c' hc => ?_, fun c c' hc => ?_⟩
  · show β (eqv φ C c) = 1 ↔ (c : H) ∈ ⊥
    rw [hk, Subgroup.mem_bot, Subgroup.mem_bot, coe_eqv]
    exact φ.map_eq_one_iff
  · have := hK (eqv φ K k) (eqv φ C c) (eqv φ C c') (by
      simp only [coe_eqv, hc, map_mul, map_inv])
    rw [e] at this
    exact this
  · exact hx (eqv φ C c) (eqv φ C c') (by
      simp only [coe_eqv, hc, map_mul, map_inv])

theorem concl_of_mulEquiv
    (φ : (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) ≃*
      (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)))
    {α : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)}
    {K : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))} {k : ℕ}
    (h : Concl Γ V Z L X F (φ.toMonoidHom.comp α) (K.map φ.toMonoidHom) k) :
    Concl Γ V Z L X F α K k := by
  have hker : (φ.toMonoidHom.comp α).ker = α.ker := by
    ext γ
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact φ.map_eq_one_iff
  have hpc := pCoreOf_map_inj φ.toMonoidHom φ.injective K
  obtain ⟨h1, h2, j, hj3, hj0, hj1, heig⟩ := h
  rw [hker] at h1 h2
  refine ⟨h1, h2, j, hj3, hj0, fun hj v hv hfix hO => hj1 hj v hv hfix fun γ hγ => hO γ ?_, ?_⟩
  · rw [MonoidHom.comp_apply, hpc] at hγ
    obtain ⟨y, hy, hyγ⟩ := hγ
    rwa [← φ.injective hyγ]
  · intro α₀' hs hk α₀ hcomp γx hγx hγ1
    let α₀'' : ↥(K.map φ.toMonoidHom) →* ↥(StatedSL 2 F) :=
      α₀'.comp (eqv φ K).symm.toMonoidHom
    have he' : ∀ p' : ↥(K.map φ.toMonoidHom),
        φ (((eqv φ K).symm p' : ↥K) : _) = p' := fun p' => by
      have h1 := congrArg Subtype.val ((eqv φ K).apply_symm_apply p')
      rw [coe_eqv] at h1
      exact h1
    have hk'' :
        α₀''.ker = (pCoreOf 2 (K.map φ.toMonoidHom)).subgroupOf (K.map φ.toMonoidHom) := by
      ext p'
      simp only [α₀'', MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [← MonoidHom.mem_ker, hk, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hpc]
      constructor
      · intro h0
        exact ⟨_, h0, he' p'⟩
      · rintro ⟨y, hy, hyp⟩
        have : y = (((eqv φ K).symm p' : ↥K) : _) :=
          φ.injective (by rw [he' p']; exact hyp)
        rwa [← this]
    have hcomp'' : ∀ (l : ↥L) (γ : ↥Γ) (p' : ↥(K.map φ.toMonoidHom)), (γ : G) = l →
        (p' : GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) = (φ.toMonoidHom.comp α) γ →
        α₀ l = α₀'' p' := by
      intro l γ p' hγl hp'
      refine hcomp l γ ((eqv φ K).symm p') hγl (φ.injective ?_)
      rw [he' p', hp']
      rfl
    have hγ1' : (φ.toMonoidHom.comp α) γx ≠ 1 := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ne_eq, φ.map_eq_one_iff]
      exact hγ1
    obtain ⟨μ, hμ, l, hl, hlm⟩ := heig α₀'' (hs.comp (eqv φ K).symm.surjective) hk'' α₀
      hcomp'' γx hγx hγ1'
    refine ⟨μ, ?_, l, hl, hlm⟩
    rw [hpc] at hμ
    exact isNatEigSection_of_map φ hμ

end CFSG.Quasithin.H13.Ch4.B414.M
