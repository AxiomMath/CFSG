module

public import CFSG.Quasithin.EmptyFaithful.S152O4Iso

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S143

section DihThree

@[expose] def dihThreeHom : DihedralGroup 3 →* Equiv.Perm (Fin 3) where
  toFun
    | DihedralGroup.r i => (finRotate 3) ^ i.val
    | DihedralGroup.sr i => Equiv.swap 0 1 * (finRotate 3) ^ i.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem dihThreeHom_bijective : Function.Bijective dihThreeHom := by decide +kernel

@[expose] noncomputable def dihThreeEquivPerm : DihedralGroup 3 ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective dihThreeHom dihThreeHom_bijective

end DihThree

section OModel

open S152O4

theorem notTrans : ∀ γ : Gam, ¬ (∀ v : Vec, act γ v = transV v) := by decide +kernel

theorem transCount' : ∀ γ : Gam, (∀ v : Vec, act γ (transV (act γ (transV v))) = v) →
    Fintype.card {v : Vec // act γ (transV v) = v} = 8 := by decide +kernel

variable {W : Type} [CommGroup W]

theorem conjBack_inj' (c : W ≃* Vec) {f f' : MulAut Vec}
    (h : conjBack c f = conjBack c f') : f = f' := by
  ext v
  have := congrArg (fun φ : MulAut W => c (φ (c.symm v))) h
  simpa [conjBack_apply] using this

theorem card_fix_conjBack (c : W ≃* Vec) (f : MulAut Vec) :
    Nat.card {w : W // conjBack c f w = w} = Nat.card {m : Vec // f m = m} := by
  refine Nat.card_congr (Equiv.subtypeEquiv c.toEquiv fun v => ?_)
  constructor
  · intro h
    have := conjBack_apply c f v
    rw [h] at this
    exact this.symm
  · intro h
    apply c.injective
    rw [conjBack_apply]
    exact h

theorem exists_Omega (hexp : ∀ w : W, w * w = 1) (hcard : Nat.card W = 16) {q : W → ZMod 2}
    (hq : IsQuadraticFormOn q) (hn : IsNondegQuadratic q) (hp : IsPlusType q) :
    ∃ Ω : Subgroup (MulAut W), Ω ≤ orthogonalGroupOf q ∧
      Ω.relIndex (orthogonalGroupOf q) = 2 ∧ Nat.card ↥Ω = 36 ∧
      Nonempty (↥Ω ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
      ∀ g ∈ orthogonalGroupOf q, g * g = 1 → Nat.card {w : W // g w = w} ≤ 4 → g ∈ Ω := by
  obtain ⟨U₁, U₂, hinf, hsup, φ₁, φ₂, hqe⟩ :=
    S153.exists_decomposition_of_plusType hexp hcard hq hn hp
  let c : W ≃* Vec := (S1417.coordEquiv hinf hsup φ₁ φ₂).trans kappa
  have hqc : ∀ v, q v = detQ (c v) := by
    intro v
    rw [hqe v, quadOf_eq_qFloc hinf hsup φ₁ φ₂ v]
    exact qFloc_eq_detQ _
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType hexp hcard hq hn hp
  have hO72 : Nat.card (orthogonalGroupOf q) = 72 := hS.card_X
  have hOq : ∀ g : Gam, rhoV c g ∈ orthogonalGroupOf q := by
    intro g v
    rw [hqc, hqc, rhoV_apply, detQ_act]
  have hle : (rhoV c).range ≤ orthogonalGroupOf q := by
    rintro _ ⟨g, rfl⟩
    exact hOq g
  have hR36 : Nat.card (rhoV c).range = 36 := by
    rw [← card_Gam]
    exact (Nat.card_congr (MonoidHom.ofInjective (rhoV_injective c)).toEquiv).symm
  have hrel : (rhoV c).range.relIndex (orthogonalGroupOf q) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (rhoV c).range (orthogonalGroupOf q)
    rw [inf_eq_left.mpr hle, hR36, hO72] at h1
    omega
  set g₀ : MulAut W := conjBack c transV with hg₀
  have hg₀O : g₀ ∈ orthogonalGroupOf q := by
    intro v
    rw [hqc, hqc, hg₀, conjBack_apply, detQ_trans]
  have hg₀R : g₀ ∉ (rhoV c).range := by
    rintro ⟨γ, hγ⟩
    have h1 : conjBack c (rho γ) = conjBack c transV := hγ
    have h2 : rho γ = transV := conjBack_inj' c h1
    exact notTrans γ (fun v => by
      have := congrArg (fun f : MulAut Vec => f v) h2
      simpa [rho_apply] using this)
  refine ⟨(rhoV c).range, hle, hrel, hR36, ?_, ?_⟩
  · exact ⟨((MonoidHom.ofInjective (rhoV_injective c)).symm).trans
      (MulEquiv.prodCongr dihThreeEquivPerm dihThreeEquivPerm)⟩
  · intro g hgO hg2 hfix
    by_contra hgΩ
    have hidx : ((rhoV c).range.subgroupOf (orthogonalGroupOf q)).index = 2 := hrel
    have hmul := Subgroup.mul_mem_iff_of_index_two hidx
      (a := (⟨g, hgO⟩ : ↥(orthogonalGroupOf q))) (b := (⟨g₀, hg₀O⟩ : ↥(orthogonalGroupOf q))⁻¹)
    have hgΩ' : (⟨g, hgO⟩ : ↥(orthogonalGroupOf q)) ∉
        (rhoV c).range.subgroupOf (orthogonalGroupOf q) :=
      fun h => hgΩ (Subgroup.mem_subgroupOf.mp h)
    have hg₀Ω' : (⟨g₀, hg₀O⟩ : ↥(orthogonalGroupOf q))⁻¹ ∉
        (rhoV c).range.subgroupOf (orthogonalGroupOf q) := fun h =>
      hg₀R (Subgroup.mem_subgroupOf.mp ((Subgroup.inv_mem_iff _).mp h))
    have hprod : (⟨g, hgO⟩ : ↥(orthogonalGroupOf q)) * (⟨g₀, hg₀O⟩ : ↥(orthogonalGroupOf q))⁻¹ ∈
        (rhoV c).range.subgroupOf (orthogonalGroupOf q) :=
      hmul.mpr ⟨fun h => absurd h hgΩ', fun h => absurd h hg₀Ω'⟩
    obtain ⟨γ, hγ⟩ : g * g₀⁻¹ ∈ (rhoV c).range := Subgroup.mem_subgroupOf.mp hprod
    have hgeq : g = conjBack c (rho γ * transV) := by
      have h1 : g = rhoV c γ * g₀ := by
        have := congrArg (fun x => x * g₀) hγ
        simpa using this.symm
      rw [h1, conjBack_mul]
      rfl
    have hf2 : ∀ v : Vec, act γ (transV (act γ (transV v))) = v := by
      have h1 : conjBack c ((rho γ * transV) * (rho γ * transV)) = conjBack c 1 := by
        rw [conjBack_mul, ← hgeq, hg2, conjBack_one]
      have h2 := conjBack_inj' c h1
      intro v
      have := congrArg (fun f : MulAut Vec => f v) h2
      simpa [rho_apply] using this
    have hcard8 : Nat.card {w : W // g w = w} = 8 := by
      have h1 : Nat.card {w : W // g w = w} = Nat.card {m : Vec // (rho γ * transV) m = m} := by
        rw [hgeq]
        exact card_fix_conjBack c _
      have h3 : Nat.card {m : Vec // (rho γ * transV) m = m} =
          Nat.card {m : Vec // act γ (transV m) = m} :=
        Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl Vec) fun m => Iff.rfl)
      rw [h1, h3, Nat.card_eq_fintype_card]
      exact transCount' γ hf2
    omega

end OModel

end S143

end CFSG.Quasithin
