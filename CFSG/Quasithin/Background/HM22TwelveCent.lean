module

public import CFSG.Quasithin.Background.HM22TwelveModel
public import CFSG.Quasithin.Background.HM22LinkComm
public import CFSG.Quasithin.Vol2.Ch8Sec2KG

public section

namespace CFSG.Quasithin.H.Mathieu.M22Link

open CFSG.Quasithin Matrix
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem isQuasisimple_of_open' {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨h1⟩, h2, ?_⟩
  by_contra hc
  push Not at hc
  have hZ : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (Subgroup.center Q) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc _ _
  rw [h1] at hZ
  have hall : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (QuotientGroup.eq_one_iff x).mpr (hZ (Subgroup.mem_top x))
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  exact hab ((hall a).trans (hall b).symm)

theorem isHat_of_quasisimple {K : Type} [Group K] (hq : CFSG.Open.IsQuasisimple K)
    (hZ : Nat.card ↥(Subgroup.center K) = 3) (hM : IsSporadic .M22 (K ⧸ Subgroup.center K)) :
    IsHat K (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
  ⟨isQuasisimple_of_open' hq, hZ, hM⟩

theorem mem_center_of_mulEquiv {A B : Type*} [Group A] [Group B] (f : A ≃* B) {a : A}
    (ha : a ∈ Subgroup.center A) : f a ∈ Subgroup.center B := by
  rw [Subgroup.mem_center_iff] at ha ⊢
  intro b
  obtain ⟨c, rfl⟩ := f.surjective b
  rw [← map_mul, ← map_mul, ha c]

theorem kg82HatM22Twelve_holds :
    CFSG.Quasithin.H13.KG82HatM22Twelve := by
  intro K _ _ hKq hKZ hKM W _ _ hW hW2 ρ hρ
  let e : K ≃* ↥ρ.range := MonoidHom.ofInjective hρ
  have he : ∀ k : K, ((e k : ↥ρ.range) : MulAut W) = ρ k := fun _ => rfl
  have hL : IsHat ↥ρ.range (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    isHat_of_mulEquiv' e (isHat_of_quasisimple hKq hKZ hKM)
  obtain ⟨ψ, θ, hψθ⟩ := exists_model_of_isHat hW2 hW hL
  apply le_antisymm
  · intro φ hφ
    rw [Subgroup.mem_centralizer_iff] at hφ
    have hφψ : ∀ (g : ↥H12Cert.G) (x : W), ((ψ g : ↥ρ.range) : MulAut W) (φ x) =
        φ (((ψ g : ↥ρ.range) : MulAut W) x) := fun g x => by
      have h1 := hφ _ (ψ g).2
      have h2 := congrArg (fun χ : MulAut W => χ x) h1
      simpa only [MulAut.mul_apply] using h2
    let fa : (Fin 12 → ZMod 2) →+ (Fin 12 → ZMod 2) :=
      { toFun := fun v => Multiplicative.toAdd (θ (φ (θ.symm (Multiplicative.ofAdd v))))
        map_zero' := by simp
        map_add' := fun v v' => by simp [ofAdd_add] }
    have hfa : ∀ v, fa v = Multiplicative.toAdd (θ (φ (θ.symm (Multiplicative.ofAdd v)))) :=
      fun _ => rfl
    set A := LinearMap.toMatrix' (fa.toZModLinearMap 2) with hAdef
    have hA : ∀ v, A *ᵥ v = fa v := fun v => LinearMap.toMatrix'_mulVec _ v
    have hθψ : ∀ (g : ↥H12Cert.G) (v : Fin 12 → ZMod 2),
        θ.symm (Multiplicative.ofAdd (((g : GL (Fin 12) (ZMod 2)) :
          Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v)) =
        ((ψ g : ↥ρ.range) : MulAut W) (θ.symm (Multiplicative.ofAdd v)) := fun g v => by
      apply θ.injective
      apply Multiplicative.toAdd.injective
      rw [hψθ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd, toAdd_ofAdd]
    have hcomm : ∀ g ∈ H12Cert.G,
        A * ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
          ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) * A := by
      intro g hg
      refine sub_eq_zero.mp (eq_zero_of_mulVec_eq_zero fun v => ?_)
      rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hA, hA, hfa, hfa, hθψ ⟨g, hg⟩, ← hφψ,
        hψθ, sub_self]
    have hcen : ∃ g₀ : ↥H12Cert.G, g₀ ∈ Subgroup.center ↥H12Cert.G ∧
        A = (((g₀ : ↥H12Cert.G) : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) := by
      have hzc : (⟨H12Cert.zU, H12Cert.zU_mem⟩ : ↥H12Cert.G) ∈ Subgroup.center ↥H12Cert.G := by
        rw [Subgroup.mem_center_iff]
        intro x
        exact Subtype.ext (H12Cert.zU_comm x.2)
      rcases commutant_G hcomm with h | h | h | h
      · exfalso
        have : Nontrivial W := by
          rw [← Finite.one_lt_card_iff_nontrivial, hW]
          norm_num
        obtain ⟨w, hw⟩ := exists_ne (1 : W)
        apply hw
        have h1 := hA (Multiplicative.toAdd (θ w))
        rw [h, zero_mulVec, hfa, ofAdd_toAdd, MulEquiv.symm_apply_apply] at h1
        have h2 : θ (φ w) = 1 := Multiplicative.toAdd.injective h1.symm
        rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff] at h2
        exact h2
      · exact ⟨1, Subgroup.one_mem _, by rw [h]; rfl⟩
      · exact ⟨_, hzc, h⟩
      · exact ⟨_, Subgroup.mul_mem _ hzc hzc, h⟩
    obtain ⟨g₀, hg₀, hAg₀⟩ := hcen
    have hφg : φ = ((ψ g₀ : ↥ρ.range) : MulAut W) := by
      ext w
      apply θ.injective
      apply Multiplicative.toAdd.injective
      rw [hψθ, ← hAg₀, hA, hfa, ofAdd_toAdd, MulEquiv.symm_apply_apply]
    refine ⟨e.symm (ψ g₀), mem_center_of_mulEquiv e.symm (mem_center_of_mulEquiv ψ hg₀), ?_⟩
    rw [hφg, ← he, MulEquiv.apply_symm_apply]
  · rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz k]

end CFSG.Quasithin.H.Mathieu.M22Link
