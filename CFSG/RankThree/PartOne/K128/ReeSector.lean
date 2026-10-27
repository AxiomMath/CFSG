module

public import CFSG.RankThree.PartOne.K128.TorusShape
public import CFSG.RankThree.PartOne.K128.ShapeEmbed
public import CFSG.RankThree.PartOne.KEXC.ReeModel
public import CFSG.RankThree.PartOne.KEXC.TorusParam

public section

namespace CFSG.RankThree.PartOne.K128

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.K1214

section Generic

theorem card_rootsOfUnity_pow {p e : ℕ} {L : Type*} [Field L] [IsAlgClosed L]
    (hpL : (p : L) ≠ 0) : Nat.card (rootsOfUnity (p ^ e) L) = p ^ e := by
  have hp0 : p ≠ 0 := fun h => hpL (by rw [h]; simp)
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp0⟩
  have : NeZero ((p ^ e : ℕ) : L) := ⟨by rw [Nat.cast_pow]; exact pow_ne_zero _ hpL⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity L (p ^ e)

theorem exists_injective_pi_of_rootsOfUnity_hom {p e : ℕ} (hp : p.Prime) {L : Type*} [Field L]
    [IsAlgClosed L] (hpL : (p : L) ≠ 0) {Γ : Type*} [Group Γ]
    (Ψ : (rootsOfUnity (p ^ e) L) × (rootsOfUnity (p ^ e) L) →* Γ) (hΨ : Function.Injective Ψ) :
    ∃ Ψ' : (Fin 2 → Multiplicative (ZMod (p ^ e))) →* Γ, Function.Injective Ψ' := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : IsCyclic (rootsOfUnity (p ^ e) L) := inferInstance
  obtain ⟨eR⟩ := nonempty_mulEquiv_zmod_of_card (G := rootsOfUnity (p ^ e) L)
    (card_rootsOfUnity_pow (e := e) hpL)
  exact ⟨Ψ.comp (((eR.symm.prodCongr eR.symm).toMonoidHom).comp
      (piFinTwoMulEquiv (Multiplicative (ZMod (p ^ e)))).toMonoidHom),
    hΨ.comp ((eR.symm.prodCongr eR.symm).injective.comp (piFinTwoMulEquiv _).injective)⟩

theorem sylowShape_of_rootsOfUnity_hom {p e : ℕ} (hp : p.Prime) {L : Type*} [Field L]
    [IsAlgClosed L] (hpL : (p : L) ≠ 0) {Γ : Type*} [Group Γ] [Finite Γ]
    (Ψ : (rootsOfUnity (p ^ e) L) × (rootsOfUnity (p ^ e) L) →* Γ) (hΨ : Function.Injective Ψ)
    (hle : (Nat.card Γ).factorization p ≤ 2 * e) : SylowShape p 2 e Γ := by
  obtain ⟨Ψ', hΨ'⟩ := exists_injective_pi_of_rootsOfUnity_hom hp hpL Ψ hΨ
  have hge : 2 * e ≤ (Nat.card Γ).factorization p := by
    have hcard : Nat.card Ψ'.range = p ^ (2 * e) := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hΨ').toEquiv, Nat.card_pi,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
      have hM : Nat.card (Multiplicative (ZMod (p ^ e))) = p ^ e := by
        rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (p ^ e)) ≃ ZMod (p ^ e)),
          Nat.card_zmod]
      rw [hM, ← pow_mul, mul_comm]
    have hdvd : p ^ (2 * e) ∣ Nat.card Γ := by
      rw [← hcard]
      exact Subgroup.card_subgroup_dvd_card _
    exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  exact sylowShape_of_injective hp Ψ' hΨ' (le_antisymm hle hge)

theorem isCyclic_of_rootsOfUnity_hom {p e : ℕ} (hp : p.Prime) {L : Type*} [Field L]
    [IsAlgClosed L] (hpL : (p : L) ≠ 0) {Γ : Type*} [Group Γ] [Finite Γ]
    (Ψ : (rootsOfUnity (p ^ e) L) →* Γ) (hΨ : Function.Injective Ψ)
    (hle : (Nat.card Γ).factorization p ≤ e) :
    ∀ P : Subgroup Γ, IsPGroup p P → IsCyclic P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  intro P hP
  have hTcard : Nat.card Ψ.range = p ^ e := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΨ).toEquiv]
    exact card_rootsOfUnity_pow (e := e) hpL
  have hT : p ^ (Nat.card Γ).factorization p ∣ Nat.card Ψ.range := by
    rw [hTcard]
    exact pow_dvd_pow p hle
  obtain ⟨c, hc⟩ := exists_conj_le_of_card_dvd Ψ.range hT hP
  have : IsCyclic Ψ.range := by
    have hc' : IsCyclic (rootsOfUnity (p ^ e) L) := inferInstance
    exact isCyclic_of_surjective (MonoidHom.ofInjective hΨ).toMonoidHom
      (MonoidHom.ofInjective hΨ).surjective
  exact isCyclic_of_injective
    (MonoidHom.codRestrict ((MulAut.conj c).toMonoidHom.comp P.subtype) Ψ.range
      fun y => hc y.1 y.2)
    fun y z h => Subtype.ext ((MulAut.conj c).injective (congrArg Subtype.val h))

end Generic

section Lang

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L]

omit [CharP L 2] [IsAlgClosed L] in
theorem exists_hom_reeGamma (D : ReeFrameData K L a) (w : WeylGroup ReeTag.F4.tag)
    {G₀ : Type*} [Group G₀] (φ : G₀ →* ModGL ReeTag.F4.tag L) (hφ : Function.Injective φ)
    (hφF : φ.range ≤ twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    ∃ Ψ : G₀ →* ReeTag.F4.reeGamma K a, Function.Injective Ψ := by
  classical
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hn
  have hnadj : n ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L w
  obtain ⟨h, hh⟩ := D.lang ⟨n, hnadj⟩
  have hFh : D.F h = h * ⟨n, hnadj⟩ := by
    rw [hh]
    group
  set g₀ : ModGL ReeTag.F4.tag L := (h : ModGL ReeTag.F4.tag L) with hg₀
  have hg₀adj : g₀ ∈ adjointGroup ReeTag.F4.tag L := h.2
  have hFg₀ : Fext D.F g₀ = g₀ * n := by
    rw [Fext_of_mem D.F hg₀adj]
    have : (⟨g₀, hg₀adj⟩ : adjointGroup ReeTag.F4.tag L) = h := rfl
    rw [this, hFh]
    rfl
  have hθ : ∀ z, ∃ γ : ReeTag.F4.reeGamma K a, thetaGamma L a γ = g₀ * φ z * g₀⁻¹ := by
    intro z
    obtain ⟨hadj, hfix⟩ := fixed_of_mem_twistedFixed D.F hg₀adj hFg₀ (hφF ⟨z, rfl⟩)
    exact D.exists_theta_of_fixed hadj hfix
  choose ψ hψ using hθ
  have hinjθ := thetaGamma_injective (K := K) L (a := a)
  let Ψ : G₀ →* ReeTag.F4.reeGamma K a :=
    { toFun := ψ
      map_one' := by
        apply hinjθ
        rw [hψ, map_one, map_one]
        group
      map_mul' := fun z z' => by
        apply hinjθ
        rw [map_mul (thetaGamma L a) (ψ z) (ψ z'), hψ (z * z'), hψ z, hψ z', map_mul φ z z']
        group }
  refine ⟨Ψ, fun z z' hzz => ?_⟩
  have h1 : g₀ * φ z * g₀⁻¹ = g₀ * φ z' * g₀⁻¹ := by
    rw [← hψ z, ← hψ z']
    exact congrArg _ hzz
  have h2 : φ z = φ z' := mul_left_cancel (mul_right_cancel h1)
  exact hφ h2

end Lang

end CFSG.RankThree.PartOne.K128
