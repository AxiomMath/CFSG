module

public import CFSG.Quasithin.H13.GoldschmidtC137S6Frame
public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin1

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3
open CFSG.Quasithin.B42Alt6 CFSG.Quasithin.S143

variable {G : Type} [Group G]

theorem exists_conj_of_sylow_top_gc {Y : Type} [Group Y] [Finite Y] {S₁ S₂ : Subgroup Y}
    (h₁ : IsSylowTwoOf S₁ ⊤) (h₂ : IsSylowTwoOf S₂ ⊤) :
    ∃ g : Y, S₁.map (MulAut.conj g).toMonoidHom = S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ → ¬ 2 ∣ S.index := by
    intro S hS
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let P₁ : Sylow 2 Y := h₁.2.1.toSylow (hidx S₁ h₁)
  let P₂ : Sylow 2 Y := h₂.2.1.toSylow (hidx S₂ h₂)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P₁ P₂
  refine ⟨g, ?_⟩
  have h := congrArg (fun T : Sylow 2 Y => (T : Subgroup Y)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  exact h

theorem isSylowTwoOf_T6 : IsSylowTwoOf T6 ⊤ := by
  have h16 := card_T6
  refine ⟨le_top, IsPGroup.of_card (n := 4) (by rw [h16]; norm_num), ?_⟩
  have h1 := Subgroup.card_mul_index T6
  have h2 : Nat.card (Gp 6) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  rw [h16, h2] at h1
  have h3 : T6.index = 45 := by omega
  show ¬ 2 ∣ T6.relIndex ⊤
  rw [Subgroup.relIndex_top_right, h3]
  norm_num

theorem autI_le_normalizer_autI_gc {V A B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hAB : A ≤ normalizer (B : Set G)) :
    autI hV A ≤ normalizer (autI hV B : Set (MulAut (IntMod V hV))) := by
  have key : ∀ a : normalizer (V : Set G), (a : G) ∈ A → ∀ ψ ∈ autI hV B,
      convI hV a * ψ * (convI hV a)⁻¹ ∈ autI hV B := by
    intro a ha ψ hψ
    obtain ⟨b, hb, rfl⟩ := (mem_autI hV).1 hψ
    refine (mem_autI hV).2 ⟨a * b * a⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have h := (Subgroup.mem_normalizer_iff.1 (hAB ha) (b : G)).1 hb
    simpa using h
  intro φ hφ
  obtain ⟨a, ha, rfl⟩ := (mem_autI hV).1 hφ
  refine B6.mem_normalizer_of_forall_mem (fun ψ hψ => key a ha ψ hψ) fun ψ hψ => ?_
  have h := key a⁻¹ (by simpa using ha) ψ hψ
  simpa using h

namespace S6Ctx

variable [Finite G] {X T V L P M : Subgroup G} (h : S6Ctx X T V L P M)
include h

theorem autI_X_eq {k : Mod} (N : KModel k (autI h.hVe L)) :
    (⊤ : Subgroup (Gp 6)).map N.ρ = autI h.hVe X := by
  have hLX : autI h.hVe L ≤ autI h.hVe X := autI_mono h.hVe h.hLX
  have hrange : ∀ x ∈ autI h.hVe X, ∃ σ, N.ρ σ = x := fun x hx =>
    N.le_range x (autI_le_normalizer_autI_gc h.hVe h.hn hx)
  have hρA : ∀ γ ∈ alternatingGroup (Fin 6), N.ρ γ ∈ autI h.hVe L := fun γ hγ => by
    have : N.ρ γ ∈ (alternatingGroup (Fin 6)).map N.ρ := ⟨γ, hγ, rfl⟩
    rwa [N.ρ_alt] at this
  have hnin : ¬ autI h.hVe T ≤ autI h.hVe L := h.hnin
  apply le_antisymm
  · rintro _ ⟨σ, -, rfl⟩
    by_cases hσ : σ ∈ alternatingGroup (Fin 6)
    · exact hLX (hρA σ hσ)
    · obtain ⟨y, hyT, hyL⟩ := IsConcreteLE.not_le_iff_exists.1 hnin
      obtain ⟨τ, hτ⟩ := hrange y (autI_mono h.hVe h.hT.1 hyT)
      have hτA : τ ∉ alternatingGroup (Fin 6) := fun hτA => hyL (hτ ▸ hρA τ hτA)
      have hσA : σ * τ⁻¹ ∈ alternatingGroup (Fin 6) := by
        rw [Equiv.Perm.mem_alternatingGroup] at hσ hτA ⊢
        have h1 : Equiv.Perm.sign σ = -1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
          · exact absurd h1 hσ
          · exact h1
        have h2 : Equiv.Perm.sign τ = -1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h2 | h2
          · exact absurd h2 hτA
          · exact h2
        rw [map_mul, map_inv, h1, h2]
        decide
      have hρσ : N.ρ σ = N.ρ (σ * τ⁻¹) * y := by
        rw [← hτ, ← map_mul]
        congr 1
        group
      rw [hρσ]
      exact (autI h.hVe X).mul_mem (hLX (hρA _ hσA)) (autI_mono h.hVe h.hT.1 hyT)
  · intro x hx
    obtain ⟨σ, rfl⟩ := hrange x hx
    exact ⟨σ, trivial, rfl⟩

end S6Ctx

structure S6Frame [Finite G] {X T V L P M : Subgroup G} (h : S6Ctx X T V L P M) where
  k : Mod
  hk : k = Mod.ut0 ∨ k = Mod.u0
  Φ : IntMod V h.hVe ≃* Mod.V 6 k
  ρ : Gp 6 →* MulAut (IntMod V h.hVe)
  inj : Function.Injective ρ
  equiv : ∀ (σ : Gp 6) v, Φ (ρ σ v) = Mod.act 6 k σ (Φ v)
  hA : (alternatingGroup (Fin 6)).map ρ = autI h.hVe L
  hX : (⊤ : Subgroup (Gp 6)).map ρ = autI h.hVe X
  hT : T6.map ρ = autI h.hVe T

namespace S6Ctx

variable [Finite G] {X T V L P M : Subgroup G} (h : S6Ctx X T V L P M)
include h

theorem nonempty_frame : Nonempty (S6Frame h) := by
  obtain ⟨k, hk, ⟨N⟩⟩ := h.kmodel
  have hX := h.autI_X_eq N
  have hsyl : IsSylowTwoOf (autI h.hVe T) (autI h.hVe X) :=
    B2F.isSylowTwoOf_autI h.hVe h.hXN h.hT
  set K : Subgroup (Gp 6) := (autI h.hVe T).comap N.ρ with hK
  have hKmap : K.map N.ρ = autI h.hVe T := by
    apply Subgroup.map_comap_eq_self
    rw [MonoidHom.range_eq_map, hX]
    exact autI_mono h.hVe h.hT.1
  have hKsyl : IsSylowTwoOf K ⊤ := by
    refine ⟨le_top, hsyl.2.1.comap_of_injective N.ρ N.ρ_inj, ?_⟩
    have h1 := Subgroup.relIndex_map_map_of_injective (f := N.ρ) K ⊤ N.ρ_inj
    rw [hKmap, hX] at h1
    have h2 := hsyl.2.2
    show ¬ 2 ∣ K.relIndex ⊤
    rw [← h1]
    exact h2
  obtain ⟨c, hc⟩ := exists_conj_of_sylow_top_gc isSylowTwoOf_T6 hKsyl
  let ρ' : Gp 6 →* MulAut (IntMod V h.hVe) := N.ρ.comp (MulAut.conj c).toMonoidHom
  refine ⟨⟨k, hk, N.Θ.trans (Mod.act 6 k c⁻¹ : MulAut (Mod.V 6 k)), ρ', ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact N.ρ_inj.comp (MulAut.conj c).injective
  · intro σ v
    show (Mod.act 6 k c⁻¹ : MulAut (Mod.V 6 k)) (N.Θ (N.ρ (c * σ * c⁻¹) v)) =
      Mod.act 6 k σ ((Mod.act 6 k c⁻¹ : MulAut (Mod.V 6 k)) (N.Θ v))
    rw [N.Θ_ρ, ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    group
  · have hconj : (alternatingGroup (Fin 6)).map (MulAut.conj c).toMonoidHom =
        alternatingGroup (Fin 6) := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : y ∈ alternatingGroup (Fin 6) := hy
        rw [Equiv.Perm.mem_alternatingGroup] at hy' ⊢
        show Equiv.Perm.sign (c * y * c⁻¹) = 1
        rw [map_mul, map_mul, map_inv, hy', mul_one, mul_inv_cancel]
      · intro hx
        refine ⟨c⁻¹ * x * c, ?_, by show c * (c⁻¹ * x * c) * c⁻¹ = x; group⟩
        have hx' := hx
        rw [Equiv.Perm.mem_alternatingGroup] at hx' ⊢
        rw [map_mul, map_mul, map_inv, hx', mul_one, inv_mul_cancel]
    show (alternatingGroup (Fin 6)).map (N.ρ.comp (MulAut.conj c).toMonoidHom) = _
    rw [← Subgroup.map_map, hconj, N.ρ_alt]
  · show (⊤ : Subgroup (Gp 6)).map (N.ρ.comp (MulAut.conj c).toMonoidHom) = _
    rw [← Subgroup.map_map, Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective, hX]
  · show T6.map (N.ρ.comp (MulAut.conj c).toMonoidHom) = _
    rw [← Subgroup.map_map, hc, hKmap]

end S6Ctx

end CFSG.Quasithin.H13.U3.GC137
