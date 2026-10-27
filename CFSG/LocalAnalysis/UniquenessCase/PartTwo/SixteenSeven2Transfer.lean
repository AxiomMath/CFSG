module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c167_preTil_sup (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (S₁ S₂ : Subgroup (Vtil V₀ V hV)) :
    preTil V₀ V hV (S₁ ⊔ S₂) = preTil V₀ V hV S₁ ⊔ preTil V₀ V hV S₂ := by
  unfold preTil
  rw [← Subgroup.comap_sup_eq (mkTil V₀ V hV) S₁ S₂ (mkTil_surjective V₀ V hV),
    Subgroup.map_sup]

private theorem s16c167_preTil_inf (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (S T : Subgroup (Vtil V₀ V hV)) :
    preTil V₀ V hV (S ⊓ T) = preTil V₀ V hV S ⊓ preTil V₀ V hV T := by
  unfold preTil
  rw [Subgroup.comap_inf, Subgroup.map_inf _ _ (valHom V hV) IntMod.val_injective]

private theorem s16c167_rk_map_of_injective {A B : Type*} [Group A] [Group B]
    (ι : A →* B) (hι : Function.Injective ι) (H : Subgroup A) :
    rk ↥(H.map ι) = rk ↥H := by
  unfold rk
  rw [Subgroup.card_map_of_injective hι]

theorem s16c167_preTil_decomp {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (h0 : V₀ = ⊥)
    {Δt : Set (Subgroup (Vtil V₀ V hV))} (hn : Δt.ncard = 2) (hi : sSupIndep Δt)
    (hs : sSup Δt = ⊤) :
    ((preTil V₀ V hV) '' Δt).ncard = 2 ∧ (∀ I ∈ (preTil V₀ V hV) '' Δt, I ≤ V) ∧
      sSupIndep ((preTil V₀ V hV) '' Δt) ∧ sSup ((preTil V₀ V hV) '' Δt) = V := by
  subst h0
  obtain ⟨a, b, hab, rfl⟩ := Set.ncard_eq_two.1 hn
  have hpre_inj : Function.Injective (preTil (⊥ : Subgroup G) V hV) := by
    intro S T h
    have h' := congrArg (imgTil (⊥ : Subgroup G) V hV) h
    rwa [imgTil_preTil, imgTil_preTil] at h'
  have hpab : preTil (⊥ : Subgroup G) V hV a ≠ preTil (⊥ : Subgroup G) V hV b :=
    fun h => hab (hpre_inj h)
  have hdisab : a ⊓ b = ⊥ := by
    rw [← disjoint_iff]
    exact (sSupIndep_pair hab).1 hi
  have hdisj : Disjoint (preTil (⊥ : Subgroup G) V hV a)
      (preTil (⊥ : Subgroup G) V hV b) := by
    rw [disjoint_iff, ← s16c167_preTil_inf, hdisab, preTil_bot]
    simp
  rw [Set.image_pair]
  refine ⟨Set.ncard_pair hpab, ?_, (sSupIndep_pair hpab).2 hdisj, ?_⟩
  · rintro I (rfl | rfl)
    · exact preTil_le (⊥ : Subgroup G) V hV a
    · exact preTil_le (⊥ : Subgroup G) V hV b
  · have hsup : a ⊔ b = ⊤ := by rw [← sSup_pair]; exact hs
    rw [sSup_pair, ← s16c167_preTil_sup, hsup, preTil_top]

theorem s16c167_rk_preTil {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (h0 : V₀ = ⊥)
    (S : Subgroup (Vtil V₀ V hV)) : rk ↥(preTil V₀ V hV S) = rk ↥S := by
  subst h0
  have hinj : Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
    intro x y h
    exact IntMod.val_injective (mul_inv_eq_one.1
      (Subgroup.mem_bot.1 ((mkTil_eq_iff (⊥ : Subgroup G) V hV x y).1 h)))
  have hbij : Function.Bijective (mkTil (⊥ : Subgroup G) V hV) :=
    ⟨hinj, mkTil_surjective (⊥ : Subgroup G) V hV⟩
  let e : IntMod V hV ≃* Vtil (⊥ : Subgroup G) V hV :=
    MulEquiv.ofBijective (mkTil (⊥ : Subgroup G) V hV) hbij
  have hcomap : S.comap (mkTil (⊥ : Subgroup G) V hV) = S.map e.symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm' e S
  unfold preTil
  rw [hcomap]
  rw [s16c167_rk_map_of_injective (valHom V hV) IntMod.val_injective]
  rw [s16c167_rk_map_of_injective e.symm.toMonoidHom e.symm.injective]

theorem s16c167_conjSubgroup_preTil {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {m : G}
    (hm : m ∈ stabTil V₀ V) (S : Subgroup (Vtil V₀ V hV)) :
    conjSubgroup (preTil V₀ V hV S) m = preTil V₀ V hV
      (S.map (actTil V₀ V hV ⟨m⁻¹, (stabTil V₀ V).inv_mem hm⟩).toMonoidHom) := by
  have hinv : m⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem hm
  have hmV : m ∈ normalizer (V : Set G) := stabTil_le_normalizer V₀ V hm
  have hmV₀ : m ∈ normalizer (V₀ : Set G) := stabTil_le_normalizer₀ V₀ V hm
  ext x
  rw [mem_conjSubgroup_iff]
  constructor
  · intro hx
    obtain ⟨y, hy, hyS⟩ := (mem_preTil V₀ V hV S).1 hx
    have hxV : x ∈ V := by
      have h : m⁻¹ * y.val * m ∈ V :=
        (Subgroup.mem_normalizer_iff''.1 hmV y.val).1 y.val_mem
      have hyx : m⁻¹ * y.val * m = x := by rw [hy]; group
      rwa [hyx] at h
    refine (mem_preTil V₀ V hV
      (S.map (actTil V₀ V hV ⟨m⁻¹, hinv⟩).toMonoidHom)).2
      ⟨IntMod.mk hV ⟨x, hxV⟩, rfl, ?_⟩
    refine Subgroup.mem_map.2 ⟨mkTil V₀ V hV y, hyS, ?_⟩
    have hEq : actStab V₀ V hV (⟨m⁻¹, hinv⟩ : stabTil V₀ V) y =
        IntMod.mk hV ⟨x, hxV⟩ := by
      apply IntMod.val_injective
      rw [actStab_apply_val]
      show (m⁻¹) * y.val * (m⁻¹)⁻¹ = x
      rw [hy]; group
    change actTil V₀ V hV ⟨m⁻¹, hinv⟩ (mkTil V₀ V hV y) =
      mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩)
    rw [actTil_mk, hEq]
  · intro hx
    obtain ⟨y, hy, hyS⟩ := (mem_preTil V₀ V hV
      (S.map (actTil V₀ V hV ⟨m⁻¹, hinv⟩).toMonoidHom)).1 hx
    obtain ⟨s, hsS, hsφ⟩ := Subgroup.mem_map.1 hyS
    obtain ⟨u, rfl⟩ := mkTil_surjective V₀ V hV s
    change actTil V₀ V hV ⟨m⁻¹, hinv⟩ (mkTil V₀ V hV u) = mkTil V₀ V hV y at hsφ
    rw [actTil_mk] at hsφ
    have ht : (actStab V₀ V hV (⟨m⁻¹, hinv⟩ : stabTil V₀ V) u).val * y.val⁻¹ ∈ V₀ :=
      (mkTil_eq_iff V₀ V hV _ y).1 hsφ
    have hyV : x ∈ V := hy ▸ IntMod.val_mem y
    have hzV : m * x * m⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 hmV x).1 hyV
    refine (mem_preTil V₀ V hV S).2
      ⟨IntMod.mk hV ⟨m * x * m⁻¹, hzV⟩, rfl, ?_⟩
    have hzu : mkTil V₀ V hV (IntMod.mk hV ⟨m * x * m⁻¹, hzV⟩) =
        mkTil V₀ V hV u := by
      rw [mkTil_eq_iff]
      change m * x * m⁻¹ * u.val⁻¹ ∈ V₀
      have ht2 : (actStab V₀ V hV (⟨m⁻¹, hinv⟩ : stabTil V₀ V) u).val * x⁻¹ ∈ V₀ := by
        simpa [hy] using ht
      rw [actStab_apply_val] at ht2
      simp only [inv_inv] at ht2
      have hconj : m * (m⁻¹ * u.val * m * x⁻¹) * m⁻¹ ∈ V₀ :=
        (Subgroup.mem_normalizer_iff.1 hmV₀ _).1 ht2
      have hgoal : m * (m⁻¹ * u.val * m * x⁻¹) * m⁻¹ =
          (m * x * m⁻¹ * u.val⁻¹)⁻¹ := by
        group
      rw [hgoal] at hconj
      simpa using inv_mem hconj
    rwa [hzu]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
