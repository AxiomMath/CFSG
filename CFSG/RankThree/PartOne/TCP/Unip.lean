module

public import CFSG.GroupTheory.WeirSylow.Symplectic

public section

namespace CFSG.RankThree.PartOne.TCP

open CFSG.GroupTheory.WeirSylow Module

section

variable {F : Type} [Field F] {S : FormSpace F F}

@[expose] def unipGroup (B : LinearMap.BilinForm F S.V) (W : Submodule F S.V) :
    Subgroup (S.V ≃ₗ[F] S.V) where
  carrier := {g | (∀ v, g v - v ∈ W) ∧ ∀ v, (∀ w ∈ W, B v w = 0) → g v = v}
  one_mem' := ⟨fun v => by simp, fun v _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have := W.add_mem (ha1 (b v)) (hb1 v)
      simpa using this
    · change a (b v) = v
      rw [hb2 v hv, ha2 v hv]
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have := W.neg_mem (ha1 (a⁻¹ v))
      have e : a (a⁻¹ v) = v := a.apply_symm_apply v
      change a.symm v - v ∈ W
      have e' : a.symm v - v = -(a (a.symm v) - a.symm v) := by
        rw [a.apply_symm_apply]
        abel
      rw [e']
      exact this
    · change a.symm v = v
      rw [LinearEquiv.symm_apply_eq]
      exact (ha2 v hv).symm

end

theorem exists_unip_of_isotropic {F : Type} [Field F] [CharP F 2] {S : FormSpace F F}
    (hS : IsSymplecticSpace S) {W : Submodule F S.V} (hW0 : W ≠ ⊥)
    (hWiso : ∀ v ∈ W, ∀ w ∈ W, S.F v w = 0) {R : Subgroup S.isom}
    (hRW : ∀ r ∈ R, ∀ w ∈ W, (r : S.V ≃ₗ[F] S.V) w ∈ W) :
    ∃ U : Subgroup S.isom, U ≠ ⊥ ∧ IsPGroup 2 U ∧ R ≤ Subgroup.normalizer (U : Set S.isom) := by
  classical
  obtain ⟨B, hBF, hBalt, hBnd⟩ := hS
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hadd : ∀ x : S.V, x + x = 0 := fun x => by rw [← two_smul F x, h2, zero_smul]
  have hneg : ∀ x : S.V, -x = x := fun x => neg_eq_of_add_eq_zero_left (hadd x)
  have hsymm : ∀ x y, B x y = B y x := fun x y => by
    have h := hBalt (x + y)
    simp only [map_add, LinearMap.add_apply, hBalt x, hBalt y, zero_add, add_zero] at h
    linear_combination h - B y x * h2
  have hiso : ∀ g : S.isom, ∀ x y, B ((g : S.V ≃ₗ[F] S.V) x) ((g : S.V ≃ₗ[F] S.V) y) = B x y :=
    fun g x y => by rw [← hBF, ← hBF]; exact g.2 x y
  set U₀ : Subgroup (S.V ≃ₗ[F] S.V) := unipGroup B W with hU₀
  refine ⟨U₀.subgroupOf S.isom, ?_, ?_, ?_⟩
  ·
    obtain ⟨w₀, hw₀W, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hw₀w₀ : B w₀ w₀ = 0 := hBalt w₀
    let f : S.V →ₗ[F] S.V := LinearMap.id + (B.flip w₀).smulRight w₀
    have hf : ∀ v, f v = v + B v w₀ • w₀ := fun v => rfl
    have hff : Function.Involutive f := fun v => by
      have e : B (v + B v w₀ • w₀) w₀ = B v w₀ := by simp [hw₀w₀]
      show f (f v) = v
      rw [hf (f v), hf v, e, add_assoc, ← add_smul]
      have : (B v w₀ + B v w₀) = 0 := by rw [← two_mul, h2, zero_mul]
      rw [this, zero_smul, add_zero]
    let t : S.V ≃ₗ[F] S.V := LinearEquiv.ofInvolutive f hff
    have ht : ∀ v, t v = v + B v w₀ • w₀ := fun v => rfl
    have htB : ∀ x y, B (t x) (t y) = B x y := fun x y => by
      rw [ht, ht]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hw₀w₀, smul_eq_mul,
        mul_zero, add_zero, hsymm w₀ y]
      have h2' : B x w₀ * B y w₀ + B y w₀ * B x w₀ = 0 := by
        rw [mul_comm (B y w₀), ← two_mul, h2, zero_mul]
      linear_combination h2'
    have htiso : t ∈ S.isom := fun x y => by rw [hBF, hBF]; exact htB x y
    have htU : t ∈ U₀ := by
      refine ⟨fun v => ?_, fun v hv => ?_⟩
      · rw [ht, add_sub_cancel_left]
        exact W.smul_mem _ hw₀W
      · rw [ht, hv w₀ hw₀W, zero_smul, add_zero]
    intro hbot
    have hmem : (⟨t, htiso⟩ : S.isom) ∈ U₀.subgroupOf S.isom := htU
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : t = 1 := congrArg Subtype.val hmem
    have hex : ∃ v, B v w₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hw₀0 (hBnd.2 w₀ hcon)
    obtain ⟨v, hv⟩ := hex
    have h4 : v + B v w₀ • w₀ = v := by
      have := congrArg (fun g : S.V ≃ₗ[F] S.V => g v) h1
      simpa [ht] using this
    have h3 : B v w₀ • w₀ = 0 := by
      have := congrArg (fun x => x - v) h4
      simpa using this
    rcases smul_eq_zero.mp h3 with h | h
    · exact hv h
    · exact hw₀0 h
  ·
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨hg1, hg2⟩ := (Subgroup.mem_subgroupOf.mp g.2 : ((g : S.isom) :
      S.V ≃ₗ[F] S.V) ∈ U₀)
    have hγγ : ∀ v, ((g : S.isom) : S.V ≃ₗ[F] S.V) (((g : S.isom) : S.V ≃ₗ[F] S.V) v) = v := by
      intro v
      have hperp : ∀ w ∈ W, B (((g : S.isom) : S.V ≃ₗ[F] S.V) v - v) w = 0 := fun w hw => by
        rw [← hBF]
        exact hWiso _ (hg1 v) w hw
      have h5 := hg2 _ hperp
      rw [map_sub] at h5
      calc ((g : S.isom) : S.V ≃ₗ[F] S.V) (((g : S.isom) : S.V ≃ₗ[F] S.V) v)
          = (((g : S.isom) : S.V ≃ₗ[F] S.V) (((g : S.isom) : S.V ≃ₗ[F] S.V) v) -
            ((g : S.isom) : S.V ≃ₗ[F] S.V) v) + ((g : S.isom) : S.V ≃ₗ[F] S.V) v := by abel
        _ = (((g : S.isom) : S.V ≃ₗ[F] S.V) v - v) + ((g : S.isom) : S.V ≃ₗ[F] S.V) v := by
          rw [h5]
        _ = (((g : S.isom) : S.V ≃ₗ[F] S.V) v + ((g : S.isom) : S.V ≃ₗ[F] S.V) v) - v := by abel
        _ = v := by rw [hadd, zero_sub, hneg]
    rw [pow_one, sq]
    exact Subtype.ext (Subtype.ext (LinearEquiv.ext hγγ))
  ·
    have key : ∀ r ∈ R, ∀ u ∈ U₀.subgroupOf S.isom, r * u * r⁻¹ ∈ U₀.subgroupOf S.isom := by
      intro r hr u hu
      obtain ⟨hu1, hu2⟩ := (Subgroup.mem_subgroupOf.mp hu : ((u : S.isom) :
        S.V ≃ₗ[F] S.V) ∈ U₀)
      have hr1 : ∀ v, (r : S.V ≃ₗ[F] S.V) (((r⁻¹ : S.isom) : S.V ≃ₗ[F] S.V) v) = v :=
        fun v => congrArg (fun g : S.isom => (g : S.V ≃ₗ[F] S.V) v) (mul_inv_cancel r)
      refine Subgroup.mem_subgroupOf.mpr ⟨fun v => ?_, fun v hv => ?_⟩
      · have e : ((r * u * r⁻¹ : S.isom) : S.V ≃ₗ[F] S.V) v - v =
            (r : S.V ≃ₗ[F] S.V) ((u : S.V ≃ₗ[F] S.V) (((r⁻¹ : S.isom) : S.V ≃ₗ[F] S.V) v) -
              ((r⁻¹ : S.isom) : S.V ≃ₗ[F] S.V) v) := by
          rw [map_sub, hr1]
          rfl
        rw [e]
        exact hRW r hr _ (hu1 _)
      · have hv' : ∀ w ∈ W, B (((r⁻¹ : S.isom) : S.V ≃ₗ[F] S.V) v) w = 0 := fun w hw => by
          rw [← hiso r, hr1]
          exact hv _ (hRW r hr w hw)
        have h6 := hu2 _ hv'
        show (r : S.V ≃ₗ[F] S.V) ((u : S.V ≃ₗ[F] S.V) (((r⁻¹ : S.isom) : S.V ≃ₗ[F] S.V) v)) = v
        rw [h6, hr1]
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => key r hr u hu, fun hu => ?_⟩
    have h7 := key r⁻¹ (R.inv_mem hr) _ hu
    have e : r⁻¹ * (r * u * r⁻¹) * r⁻¹⁻¹ = u := by group
    rwa [e] at h7

end CFSG.RankThree.PartOne.TCP
