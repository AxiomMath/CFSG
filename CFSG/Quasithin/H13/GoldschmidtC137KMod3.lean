module

public import CFSG.Quasithin.H13.GoldschmidtC137KMod2
public import CFSG.Quasithin.Background.GoldschmidtB69DeepN2c

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.B3 CFSG.Quasithin.S143
open CFSG.Quasithin.B42Alt6
open scoped IsMulCommutative

structure KModel (k : Mod) {S : Type*} [CommGroup S] (L : Subgroup (MulAut S)) where
  Θ : S ≃* Mod.V 6 k
  ρ : Equiv.Perm (Fin 6) →* MulAut S
  ρ_inj : Function.Injective ρ
  Θ_ρ : ∀ (σ : Equiv.Perm (Fin 6)) (v : S), Θ (ρ σ v) = Mod.act 6 k σ (Θ v)
  ρ_alt : (alternatingGroup (Fin 6)).map ρ = L
  le_range : ∀ g ∈ Subgroup.normalizer (L : Set (MulAut S)), ∃ σ, ρ σ = g

theorem map_mem_normalizer {A B : Type*} [Group A] [Group B] (θ : A ≃* B) {L : Subgroup A}
    {g : A} (hg : g ∈ Subgroup.normalizer (L : Set A)) :
    θ g ∈ Subgroup.normalizer ((L.map θ.toMonoidHom : Subgroup B) : Set B) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro y
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨g * l * g⁻¹, (hg l).1 hl, by simp [map_mul, map_inv]⟩
  · rintro ⟨l, hl, hly⟩
    have hl' : g⁻¹ * l * g ∈ L := by
      refine (hg (g⁻¹ * l * g)).2 ?_
      rw [show g * (g⁻¹ * l * g) * g⁻¹ = l by group]
      exact hl
    refine ⟨g⁻¹ * l * g, hl', ?_⟩
    have hly' : θ l = θ g * y * (θ g)⁻¹ := hly
    show θ (g⁻¹ * l * g) = y
    rw [map_mul, map_mul, map_inv, hly']
    group

noncomputable def KModel.ofEquiv {S : Type*} [CommGroup S] {k : Mod}
    (hk : k = Mod.ut0 ∨ k = Mod.u0) (Φ : S ≃* Mod.V 6 k) (L : Subgroup (MulAut S))
    (hL : L.map (MulAut.congr Φ).toMonoidHom = (alternatingGroup (Fin 6)).map (Mod.act 6 k)) :
    KModel k L where
  Θ := Φ
  ρ := (MulAut.congr Φ).symm.toMonoidHom.comp (Mod.act 6 k)
  ρ_inj := fun a b hab => act_injective (by norm_num) k ((MulAut.congr Φ).symm.injective hab)
  Θ_ρ := fun σ v => by simp
  ρ_alt := by
    rw [← Subgroup.map_map]
    show ((alternatingGroup (Fin 6)).map (Mod.act 6 k)).map (MulAut.congr Φ).symm.toMonoidHom = L
    rw [← hL, Subgroup.map_map]
    have : (MulAut.congr Φ).symm.toMonoidHom.comp (MulAut.congr Φ).toMonoidHom =
        MonoidHom.id _ := MonoidHom.ext fun x => (MulAut.congr Φ).symm_apply_apply x
    rw [this, Subgroup.map_id]
  le_range := fun g hg => by
    have h1 := map_mem_normalizer (MulAut.congr Φ) hg
    rw [hL] at h1
    obtain ⟨σ, hσ⟩ := normalizer_alt_act hk _ h1
    refine ⟨σ, ?_⟩
    show (MulAut.congr Φ).symm (Mod.act 6 k σ) = g
    rw [hσ]
    exact MulEquiv.symm_apply_apply _ _

noncomputable def KModel.ofModIso {S : Type*} [CommGroup S] {k : Mod}
    (hk : k = Mod.ut0 ∨ k = Mod.u0) (Φ : S ≃* Mod.V 6 k) (ρ₀ : LG 6 →* MulAut S)
    (hΦ : IsModIso ρ₀ (actL 6 k) Φ) (L : Subgroup (MulAut S))
    (hL : (⊤ : Subgroup (LG 6)).map ρ₀ = L) : KModel k L :=
  KModel.ofEquiv hk Φ L (by
    rw [← hL, Subgroup.map_map]
    have h1 : (MulAut.congr Φ).toMonoidHom.comp ρ₀ =
        (Mod.act 6 k).comp (alternatingGroup (Fin 6)).subtype :=
      MonoidHom.ext fun γ => MulEquiv.ext fun w => by
        show Φ (ρ₀ γ (Φ.symm w)) = Mod.act 6 k γ.1 w
        have := hΦ γ (Φ.symm w)
        rw [MulEquiv.apply_symm_apply] at this
        exact this
    rw [h1, ← MonoidHom.range_eq_map, MonoidHom.range_comp, Subgroup.range_subtype])

variable {G : Type} [Group G]

theorem n6Model_of_natural {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hnat : ∃ _ : IsMulCommutative ↥V, AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6) :
    Nonempty (N6Model (autI hV L)) := by
  obtain ⟨hc, π, hπ⟩ := hnat
  obtain ⟨Θ, hΘ⟩ := B69.exists_n6Equiv_of_altDn hπ
  have hρπ : ∀ (γ : ↥(alternatingGroup (Fin 6))) (w : ↥V),
      rhoOf Θ (γ : Equiv.Perm (Fin 6)) w = ((π γ : ↥(autOn L V)) : MulAut _) w := by
    intro γ w
    apply Θ.injective
    rw [rhoOf_apply]
    exact (hΘ γ w).symm
  have hρA : (alternatingGroup (Fin 6)).map (rhoOf Θ) = autOn L V := by
    ext x
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      have : rhoOf Θ γ = ((π ⟨γ, hγ⟩ : ↥(autOn L V)) : MulAut _) :=
        MulEquiv.ext fun w => hρπ ⟨γ, hγ⟩ w
      rw [this]
      exact (π ⟨γ, hγ⟩).2
    · intro hx
      obtain ⟨γ, hγ⟩ : ∃ γ : ↥(alternatingGroup (Fin 6)), π γ = ⟨x, hx⟩ := hπ.1 ⟨x, hx⟩
      refine ⟨γ, γ.2, ?_⟩
      have : rhoOf Θ γ = ((π γ : ↥(autOn L V)) : MulAut _) := MulEquiv.ext fun w => hρπ γ w
      rw [this, hγ]
  exact ⟨⟨Θ, rhoOf Θ, rhoOf_injective Θ, rhoOf_apply Θ, hρA⟩⟩

theorem model_of_natural {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hnat : ∃ _ : IsMulCommutative ↥V, AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6) :
    ∃ k, (k = Mod.ut0 ∨ k = Mod.u0) ∧ Nonempty (KModel k (autI hV L)) := by
  obtain ⟨N⟩ := n6Model_of_natural hV hnat
  have hΦ : ∀ (σ : Equiv.Perm (Fin 6)) (x : IntMod V hV),
      (N.Θ.trans n6ModEquiv) (N.ρ σ x) = Mod.act 6 Mod.ut0 σ ((N.Θ.trans n6ModEquiv) x) :=
    fun σ x => by
      show n6ModEquiv (N.Θ (N.ρ σ x)) = Mod.act 6 Mod.ut0 σ (n6ModEquiv (N.Θ x))
      rw [N.Θ_ρ]
      exact n6ToV_act_perm σ _
  refine ⟨Mod.ut0, Or.inl rfl, ⟨KModel.ofEquiv (Or.inl rfl) (N.Θ.trans n6ModEquiv) _ ?_⟩⟩
  have h2 : (MulAut.congr (N.Θ.trans n6ModEquiv)).toMonoidHom.comp N.ρ = Mod.act 6 Mod.ut0 :=
    MonoidHom.ext fun σ => MulEquiv.ext fun w => by
      show (N.Θ.trans n6ModEquiv) (N.ρ σ ((N.Θ.trans n6ModEquiv).symm w)) = _
      rw [hΦ, MulEquiv.apply_symm_apply]
  have h3 := congrArg (Subgroup.map (MulAut.congr (N.Θ.trans n6ModEquiv)).toMonoidHom) N.ρ_alt
  rw [Subgroup.map_map, h2] at h3
  exact h3.symm

end CFSG.Quasithin.H13.U3.GC137
