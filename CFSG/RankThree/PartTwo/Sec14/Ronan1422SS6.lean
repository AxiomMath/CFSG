module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

@[expose] noncomputable def mulEquivOfSurjOfKerEq {K X Y : Type*} [Group K] [Group X] [Group Y]
    (f : K →* X) (hf : Function.Surjective f) (g : K →* Y) (hg : Function.Surjective g)
    (hker : f.ker = g.ker) : X ≃* Y :=
  (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg))

theorem mulEquivOfSurjOfKerEq_apply {K X Y : Type*} [Group K] [Group X] [Group Y]
    (f : K →* X) (hf : Function.Surjective f) (g : K →* Y) (hg : Function.Surjective g)
    (hker : f.ker = g.ker) (k : K) :
    mulEquivOfSurjOfKerEq f hf g hg hker (f k) = g k := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f k) =
      (QuotientGroup.mk k : K ⧸ f.ker) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  unfold mulEquivOfSurjOfKerEq
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem isS6Type_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (θ : X ≃* Y) {α : MulAut X}
    {β : MulAut Y} (hθ : ∀ x, θ (α x) = β (θ x)) (h : IsS6Type Y β) : IsS6Type X α := by
  unfold IsS6Type at h ⊢
  obtain ⟨ψ, σ, hσ⟩ := h
  refine ⟨θ.trans ψ, σ, fun k => ?_⟩
  simp only [MulEquiv.trans_apply]
  rw [hθ k]
  exact hσ (θ k)

theorem isS6Type_of_surjective {K X Y : Type*} [Group K] [Group X] [Group Y]
    (f : K →* X) (hf : Function.Surjective f) (g : K →* Y) (hg : Function.Surjective g)
    (hker : f.ker = g.ker) (γ : K →* K) {α : MulAut X} {β : MulAut Y}
    (hα : ∀ k, α (f k) = f (γ k)) (hβ : ∀ k, β (g k) = g (γ k)) (h : IsS6Type Y β) :
    IsS6Type X α := by
  refine isS6Type_of_mulEquiv (mulEquivOfSurjOfKerEq f hf g hg hker) ?_ h
  intro x
  obtain ⟨k, rfl⟩ := hf x
  rw [hα k, mulEquivOfSurjOfKerEq_apply, mulEquivOfSurjOfKerEq_apply, hβ k]

theorem isS6Type_of_normalizes (hGL : KF1422GL42) {G : Type} [Group G] [Finite G]
    {K R : Subgroup G} (hKR : K ≤ Subgroup.normalizer (R : Set G))
    (f : ↥K →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hker : f.ker = R.subgroupOf K) (hR : CFSG.Assembly.IsElemAbelian 2 R)
    (hR16 : Nat.card R = 16) (hCR : K ⊓ Subgroup.centralizer (R : Set G) ≤ R)
    {w : G} (hwK : w ∈ Subgroup.normalizer (K : Set G))
    (hwR : w ∈ Subgroup.normalizer (R : Set G))
    {X : Type*} [Group X] (π : ↥K →* X) (hπ : Function.Surjective π)
    (hπker : π.ker = R.subgroupOf K) (α : MulAut X)
    (hα : ∀ k : ↥K, α (π k) = π (K.normalizerMonoidHom ⟨w, hwK⟩ k)) : IsS6Type X α := by
  have hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hR.1.is_comm.comm (⟨x, hx⟩ : ↥R) ⟨y, hy⟩)
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ↥K →* MulAut ↥R,
      ρ = R.normalizerMonoidHom.comp (Subgroup.inclusion hKR) := ⟨_, rfl⟩
  have hρk : ∀ k : ↥K, ρ k = R.normalizerMonoidHom ⟨(k : G), hKR k.2⟩ := fun k => by
    rw [hρdef]
    rfl
  have hρapp : ∀ (k : ↥K) (r : ↥R), ((ρ k) r : G) = (k : G) * r * (k : G)⁻¹ := by
    intro k r
    rw [hρk]
    exact Subgroup.normalizerMonoidHom_apply_apply_coe R ⟨(k : G), hKR k.2⟩ r
  have hρker : ρ.ker = R.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hk
      have hcent : (k : G) ∈ K ⊓ Subgroup.centralizer (R : Set G) := by
        refine ⟨k.2, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
        have h1 : ((ρ k) ⟨r, hr⟩ : G) = r :=
          congrArg (fun φ : MulAut ↥R => ((φ ⟨r, hr⟩ : ↥R) : G)) hk
        rw [hρapp] at h1
        exact (mul_inv_eq_iff_eq_mul.mp h1).symm
      exact hCR hcent
    · intro hk
      refine MulEquiv.ext fun r => Subtype.ext ?_
      show ((ρ k) r : G) = r
      rw [hρapp, hRc _ hk _ r.2, mul_inv_cancel_right]
  have hρ'surj : Function.Surjective ρ.rangeRestrict := MonoidHom.rangeRestrict_surjective ρ
  have hρ'ker : ρ.rangeRestrict.ker = f.ker := by
    rw [MonoidHom.ker_rangeRestrict, hρker, hker]
  have hiso : Nonempty (↥ρ.range ≃* alternatingGroup (Fin 6)) :=
    ⟨mulEquivOfSurjOfKerEq ρ.rangeRestrict hρ'surj f hf hρ'ker⟩
  have hconj : ∀ (w' : G) (hw'K : w' ∈ Subgroup.normalizer (K : Set G))
      (hw'R : w' ∈ Subgroup.normalizer (R : Set G)) (k : ↥K),
      R.normalizerMonoidHom ⟨w', hw'R⟩ * ρ k * (R.normalizerMonoidHom ⟨w', hw'R⟩)⁻¹ =
        ρ (K.normalizerMonoidHom ⟨w', hw'K⟩ k) := by
    intro w' hw'K hw'R k
    have hmem : (⟨w', hw'R⟩ : ↥(Subgroup.normalizer (R : Set G))) * ⟨(k : G), hKR k.2⟩ *
        (⟨w', hw'R⟩ : ↥(Subgroup.normalizer (R : Set G)))⁻¹ =
          ⟨(K.normalizerMonoidHom ⟨w', hw'K⟩ k : G),
            hKR (K.normalizerMonoidHom ⟨w', hw'K⟩ k).2⟩ := by
      apply Subtype.ext
      simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [hρk, hρk, ← map_inv, ← map_mul, ← map_mul, hmem]
  have hfwd : ∀ (w' : G) (hw'K : w' ∈ Subgroup.normalizer (K : Set G))
      (hw'R : w' ∈ Subgroup.normalizer (R : Set G)) (y : MulAut ↥R), y ∈ ρ.range →
        R.normalizerMonoidHom ⟨w', hw'R⟩ * y * (R.normalizerMonoidHom ⟨w', hw'R⟩)⁻¹ ∈
          ρ.range := by
    intro w' hw'K hw'R y hy
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hy
    exact MonoidHom.mem_range.mpr ⟨K.normalizerMonoidHom ⟨w', hw'K⟩ k,
      (hconj w' hw'K hw'R k).symm⟩
  have hwY : R.normalizerMonoidHom ⟨w, hwR⟩ ∈
      Subgroup.normalizer ((ρ.range : Subgroup (MulAut ↥R)) : Set (MulAut ↥R)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy' => hfwd w hwK hwR y hy', fun hy => ?_⟩
    have h2 := hfwd w⁻¹ (inv_mem hwK) (inv_mem hwR) _ hy
    have hinv : R.normalizerMonoidHom ⟨w⁻¹, inv_mem hwR⟩ =
        (R.normalizerMonoidHom ⟨w, hwR⟩)⁻¹ :=
      map_inv R.normalizerMonoidHom ⟨w, hwR⟩
    rw [hinv, inv_inv] at h2
    have h3 : (R.normalizerMonoidHom ⟨w, hwR⟩)⁻¹ *
        (R.normalizerMonoidHom ⟨w, hwR⟩ * y * (R.normalizerMonoidHom ⟨w, hwR⟩)⁻¹) *
          R.normalizerMonoidHom ⟨w, hwR⟩ = y := by
      group
    rw [h3] at h2
    exact h2
  have hβ : ∀ k : ↥K,
      (ρ.range.normalizerMonoidHom ⟨R.normalizerMonoidHom ⟨w, hwR⟩, hwY⟩) (ρ.rangeRestrict k) =
        ρ.rangeRestrict (K.normalizerMonoidHom ⟨w, hwK⟩ k) := by
    intro k
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hconj w hwK hwR k
  have hY := hGL G R hR hR16 ρ.range hiso (R.normalizerMonoidHom ⟨w, hwR⟩) hwY
  have hπρ : π.ker = ρ.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict, hρker, hπker]
  exact isS6Type_of_surjective π hπ ρ.rangeRestrict hρ'surj hπρ
    (K.normalizerMonoidHom ⟨w, hwK⟩).toMonoidHom hα hβ hY

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
