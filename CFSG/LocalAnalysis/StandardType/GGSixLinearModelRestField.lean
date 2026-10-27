module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestFieldNorm
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace LinModel

variable {m : ℕ} {G : Type*} [Group G] {f : ℕ}
  {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G}

theorem prod_range_pow_apply_zero {M : Type*} [CommMonoid M] {p : ℕ} [Fact p.Prime]
    (hmp : m + 1 = p) {π : Equiv.Perm (Fin (m + 1))} (hcyc : π.IsCycle)
    (hsupp : π.support = Finset.univ) (hπp : π ^ p = 1) (a : Fin (m + 1) → M) :
    ∏ j ∈ Finset.range p, a ((π ^ j) 0) = ∏ i, a i := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hbij := cycleIdx_bijective (p := p) hmp hcyc hsupp hπp
  rw [← Fintype.prod_bijective _ hbij (fun j => a (cycleIdx π j)) a (fun _ => rfl)]
  symm
  refine Finset.prod_nbij' (fun j : ZMod p => j.val) (fun k : ℕ => (k : ZMod p))
    (fun j _ => Finset.mem_range.mpr (ZMod.val_lt j)) (fun _ _ => Finset.mem_univ _)
    (fun j _ => ZMod.natCast_zmod_val j) (fun k hk => ?_) (fun j _ => rfl)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hk)]

theorem exists_mem_ggInducedPairs_of_mem_normalizer_rootTorus (hf : f ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hmp : m + 1 = p)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {ω : (GaloisField 2 f)ˣ}
    (hω : IsPrimitiveRoot ω p)
    (hreal : ∀ l : Fin (m + 1), ∃ g : G,
      (g, InnerDiagA.diagGL (Pi.mulSingle l ω)) ∈ LinFusion.ggInducedPairs ψ)
    {Bs : Subgroup G} (hBs : rootTorus p ψ = Bs)
    (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) {y : G}
    (hy : y ∈ Subgroup.normalizer (ψ.range : Set G))
    (hyN : y ∈ Subgroup.normalizer (Bs : Set G)) (hyp : y ^ p = 1) :
    ∃ A : GL (Fin (m + 1)) (GaloisField 2 f), (y, A) ∈ LinFusion.ggInducedPairs ψ := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hm : 2 ≤ m := by have := hp.two_le; omega
  have hζ : IsPrimitiveRoot (ω : GaloisField 2 f) p := IsPrimitiveRoot.coe_units_iff.mpr hω
  have hαp : autOf hker hC ⟨y, hy⟩ ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨y, hy⟩ : Subgroup.normalizer (ψ.range : Set G)) ^ p = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hyp)
    rw [h1, map_one]
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := GaloisField 2 f) (n := m + 1)
    (by omega)).2 (autOf hker hC ⟨y, hy⟩)
  have hε0 : ε = 0 := HypSixTypeA.graph_exp_eq_zero (n := m + 1) (by omega)
    (hp.odd_of_ne_two hp2) hε (by rw [← hαeq]; exact hαp)
  subst hε0
  rw [pow_zero, mul_one] at hαeq
  have hpow := conjAut_mul_fieldAut_pow A σ p
  rw [← hαeq, hαp] at hpow
  obtain ⟨hσp, l₀, hl₀⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := GaloisField 2 f)
    (n := m + 1) (by omega) _ _ hpow.symm
  by_cases hσ1 : σ = 1
  · rw [hσ1, map_one, mul_one] at hαeq
    exact ⟨A, (autOf_eq_conjAut_iff hker hC hy A).mp hαeq⟩
  exfalso
  have hfix : ∀ x : GaloisField 2 f, x ^ p = 1 → σ x = x := fun x hx =>
    fieldAut_fixes_root hp hζ (k := 1) (by rw [pow_one]; exact hσp) hx
  obtain ⟨π, hπ⟩ := exists_isPermOf_of_autOf hker hC (hω.ne_one hp.one_lt) hω.pow_eq_one hreal
    hBs hfix hy hyN hαeq
  have hπp : π ^ p = 1 := by
    have h1 := isPermOf_twistNorm hπ σ p
    rw [← hl₀] at h1
    have h2 : IsPermOf ((GeneralLinearGroup.scalar (Fin (m + 1)) l₀ :
        GL (Fin (m + 1)) (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) 1 := by
      have := IsPermOf.scalar_mul (A := (1 : GL (Fin (m + 1)) (GaloisField 2 f)))
        (by rw [Units.val_one]; exact isPermOf_one) l₀
      rwa [mul_one] at this
    exact h1.unique h2
  by_cases hπ1 : π = 1
  · rw [hπ1] at hπ
    obtain ⟨a, ha⟩ := IsPermOf.exists_eq_diagGL hπ
    rw [ha] at hαeq
    exact false_of_autOf_eq_diag_field hker hC (by omega) hBs hom hσ1 hfix hy hyp hαeq
  have hord : orderOf π = p := orderOf_eq_prime hπp hπ1
  have hcyc : π.IsCycle := Equiv.Perm.isCycle_of_prime_order' (by rw [hord]; exact hp)
    (by rw [Fintype.card_fin, hord, hmp]; omega)
  have hsupp : π.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← hcyc.orderOf, hord, Fintype.card_fin, hmp]
  have hσl : σ (l₀ : GaloisField 2 f) = l₀ := by
    have h1 := twistNorm_succ' A σ p
    rw [twistNorm_succ, hσp, map_one_ringAut, ← hl₀, map_scalar_ringAut,
      (TypeA.PGLTor.commute_scalar l₀ A).eq] at h1
    have h2 := mul_left_cancel h1
    have h3 := congrArg (fun X : GL (Fin (m + 1)) (GaloisField 2 f) =>
      (X : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) 0 0) h2
    simpa [GeneralLinearGroup.coe_scalar] using h3
  obtain ⟨μ, hμ⟩ := exists_pow_eq_of_fixed hf hp hζ hσp hσ1 hσl
  have hne : ∀ i, (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) (π i) i ≠ 0 :=
    fun i => (hπ i (π i)).mpr rfl
  set a : Fin (m + 1) → (GaloisField 2 f)ˣ := fun i => Units.mk0 _ (hne i) with hadef
  have ha : ∀ i, (a i : GaloisField 2 f) =
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) (π i) i := fun i => rfl
  have hσu : ∀ x : (GaloisField 2 f)ˣ, ∃ c : (GaloisField 2 f)ˣ,
      σ (x : GaloisField 2 f) = x * c ^ p := by
    intro x
    obtain ⟨c, hc⟩ := exists_pow_eq_mul_of_fixes hf hp.pos hζ (hfix _ hζ.pow_eq_one)
      (x : GaloisField 2 f)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero, mul_zero] at hc
      exact x.ne_zero ((map_eq_zero σ).mp hc)
    exact ⟨Units.mk0 c hc0, by rw [hc]; rfl⟩
  obtain ⟨c, hc⟩ := exists_twistNorm_apply_eq hπ hσu a ha p 0
  rw [hπp, Equiv.Perm.one_apply, ← hl₀, GeneralLinearGroup.coe_scalar, scalar_apply,
    diagonal_apply_eq] at hc
  have hc' : l₀ = (∏ j ∈ Finset.range p, a ((π ^ j) 0)) * c ^ p := Units.ext (by
    rw [hc, Units.val_mul, Units.val_pow_eq_pow_val])
  have hdet : GeneralLinearGroup.det A = ∏ i, a i := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, det_eq_prod_of_isPermOf hπ, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => (ha i).symm
  have hdetp : GeneralLinearGroup.det A = (μ * c⁻¹) ^ p := by
    calc GeneralLinearGroup.det A = ∏ i, a i := hdet
      _ = ∏ j ∈ Finset.range p, a ((π ^ j) 0) :=
        (prod_range_pow_apply_zero hmp hcyc hsupp hπp a).symm
      _ = l₀ * (c ^ p)⁻¹ := by rw [hc', mul_inv_cancel_right]
      _ = (μ * c⁻¹) ^ p := by rw [← hμ, mul_pow, inv_pow]
  set A' := GeneralLinearGroup.scalar (Fin (m + 1)) (μ * c⁻¹)⁻¹ * A with hA'
  have hA'det : GeneralLinearGroup.det A' = 1 := by
    have hpm : ∀ u : (GaloisField 2 f)ˣ, u ^ (m + 1) = u ^ p := fun u => by rw [hmp]
    rw [hA', map_mul, det_scalar_eq, hpm, hdetp, inv_pow, inv_mul_cancel]
  set s : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) :=
    ⟨(A' : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)), by
      rw [← GeneralLinearGroup.val_det_apply, hA'det, Units.val_one]⟩ with hs
  have hsA : Matrix.SpecialLinearGroup.toGL s = A' := Units.ext rfl
  have hsN : ψ s ∈ Subgroup.normalizer (ψ.range : Set G) :=
    mem_normalizer_of_mem_ggInducedPairs (map_toGL_mem_ggInducedPairs ψ s)
  have hs' := (autOf_eq_conjAut_iff hker hC hsN _).mpr (map_toGL_mem_ggInducedPairs ψ s)
  have hy''N : (ψ s)⁻¹ * y ∈ Subgroup.normalizer (ψ.range : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hsN) hy
  have hα'' : autOf hker hC ⟨(ψ s)⁻¹ * y, hy''N⟩ =
      conjAut (m + 1) (GaloisField 2 f) (InnerDiagA.diagGL 1) *
        fieldAut (m + 1) (GaloisField 2 f) σ := by
    have h1 : (⟨(ψ s)⁻¹ * y, hy''N⟩ : Subgroup.normalizer (ψ.range : Set G)) =
        (⟨ψ s, hsN⟩)⁻¹ * ⟨y, hy⟩ := rfl
    rw [h1, map_mul, map_inv, hs', hsA, hαeq, hA', map_mul, conjAut_scalar, one_mul,
      LinFusion.diagGL_one, map_one, one_mul, inv_mul_cancel_left]
  have hy''p : ((ψ s)⁻¹ * y) ^ p = 1 := by
    have h1 : (autOf hker hC ⟨(ψ s)⁻¹ * y, hy''N⟩) ^ p = 1 := by
      rw [hα'', LinFusion.diagGL_one, map_one, one_mul, ← map_pow, hσp, map_one]
    have h2 : autOf hker hC (⟨(ψ s)⁻¹ * y, hy''N⟩ ^ p) = autOf hker hC 1 := by
      rw [map_pow, h1, map_one]
    have h3 := congrArg Subtype.val (autOf_injective hker hC h2)
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h3
  exact false_of_autOf_eq_diag_field hker hC (by omega) hBs hom hσ1 hfix hy''N hy''p hα''

theorem exists_mem_ggInducedPairs_of_dvd {G : Type} [Group G] [Finite G] {p f : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hmp : m + 1 = p) (hf : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hpf : p ∣ f) {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hBsM : Bs ≤ Subgroup.normalizer (ψ.range : Set G)) (hBsE : IsElemAbelian p Bs)
    (hBsI : ∀ b ∈ Bs, GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ b)
    (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hU : GGBstarUniqueIn p (Subgroup.normalizer (ψ.range : Set G)) Bs) {y : G}
    (hyM : y ∈ Subgroup.normalizer (ψ.range : Set G)) (hyp : y ^ p = 1) :
    ∃ A : GL (Fin (m + 1)) (GaloisField 2 f), (y, A) ∈ LinFusion.ggInducedPairs ψ := by
  have hp2 : p ≠ 2 := by omega
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hF]; exact hpq
  obtain ⟨ζ, hζ⟩ := TypeA.PGLTor.exists_isPrimitiveRoot_of_dvd hp hpF
  set ω : (GaloisField 2 f)ˣ := (hζ.isUnit hp.ne_zero).unit with hωdef
  have hω : IsPrimitiveRoot ω p := IsPrimitiveRoot.coe_units_iff.mp (by
    rw [hωdef, IsUnit.unit_spec]; exact hζ)
  obtain ⟨P, hBsD, hW⟩ := exists_frame_of_sl hp hp5 hmp hf hpq hker hC hBsM hBsE hBsI hom hU
  set ψ' := ψ.comp (InnerDiagA.conjSL P⁻¹) with hψ'
  have hker' := LinTorus.ker_comp_conjSL_le hker P⁻¹
  have hrange' : ψ'.range = ψ.range := LinTorus.range_comp_conjSL ψ P⁻¹
  have hC' : Subgroup.centralizer (ψ'.range : Set G) = ⊥ := by rw [hrange']; exact hC
  have hBs : rootTorus p ψ' = Bs := le_antisymm hW (le_rootTorus hker' hBsD hBsE.2)
  obtain ⟨ζ', hζ'⟩ := exists_pow_eq_of_sq_dvd hp
    (by rw [Nat.card_units, hF]; exact sq_dvd_two_pow_sub_one hp hp2 hpf hf hpq) hω.pow_eq_one
  have hpm : ∀ u : (GaloisField 2 f)ˣ, u ^ (m + 1) = u ^ p := fun u => by rw [hmp]
  have hreal : ∀ l : Fin (m + 1), ∃ g : G,
      (g, InnerDiagA.diagGL (Pi.mulSingle l ω)) ∈ LinFusion.ggInducedPairs ψ' := by
    intro l
    obtain ⟨g, -, hg⟩ := exists_mem_of_scalar ψ' (Pi.mulSingle l ω) ζ'⁻¹ (by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hpm,
        Finset.prod_pi_mulSingle', inv_pow, hζ']
      simp)
    exact ⟨g, hg⟩
  obtain ⟨g, hgM, hgN⟩ := exists_conj_mem_normalizer hp hBsE hBsM hU hyM hyp
  have hy'M : g⁻¹ * y * g ∈ Subgroup.normalizer (ψ.range : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgM) hyM) hgM
  have hy'M' : g⁻¹ * y * g ∈ Subgroup.normalizer (ψ'.range : Set G) := by rw [hrange']; exact hy'M
  have hy'p : (g⁻¹ * y * g) ^ p = 1 := by
    rw [show g⁻¹ * y * g = MulAut.conj g⁻¹ y by rw [MulAut.conj_apply, inv_inv], ← map_pow, hyp,
      map_one]
  obtain ⟨A', hA'⟩ := exists_mem_ggInducedPairs_of_mem_normalizer_rootTorus (by omega) hp hp2 hmp
    hker' hC' hω hreal hBs hom hy'M' hgN hy'p
  have hA'' := mem_ggInducedPairs_of_comp_conjSL_inv hA'
  have h1 := (autOf_eq_conjAut_iff hker hC hy'M _).mpr hA''
  have hI := AutPSL.inndiag_normal (n := m + 1) (K := GaloisField 2 f) (by omega)
  have h2 : autOf hker hC ⟨y, hyM⟩ = autOf hker hC ⟨g, hgM⟩ *
      autOf hker hC ⟨g⁻¹ * y * g, hy'M⟩ * (autOf hker hC ⟨g, hgM⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show y = g * (g⁻¹ * y * g) * g⁻¹
    group
  have h3 : autOf hker hC ⟨y, hyM⟩ ∈
      (AutPSL.inndiag : Subgroup (MulAut (projectiveSL (m + 1) (GaloisField 2 f)))) := by
    rw [h2, h1]
    exact hI.conj_mem _ ⟨_, rfl⟩ _
  obtain ⟨X, hX⟩ := h3
  exact ⟨X, (autOf_eq_conjAut_iff hker hC hyM X).mp hX.symm⟩

end LinModel

section Inputs

theorem ggSixLinearFieldOrderPInput_holds : GGSixLinearFieldOrderPInput := by
  intro G _ _ p Bs G₀ n f ψ hS hlin hpf y hyM hyp
  obtain ⟨hp5, hnp, hcase⟩ := hlin
  have hpq : p ∣ 2 ^ f - 1 := by
    rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (by decide)
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hS.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hrange
  obtain ⟨A, hA⟩ := LinModel.exists_mem_ggInducedPairs_of_dvd hS.prime hp5 hnp hadm.2.1 hpq hpf
    hker hS.2.2.1 hS.bstar_le hS.elem hS.2.2.2.1.2.2 hS.omega hS.unique hyM hyp
  exact LinModel.ggPsiInnerDiag_of_mem_ggInducedPairs (by omega) hker
    (hS.prime.odd_of_ne_two (by omega)) hA hyp

end Inputs

end CFSG.StandardType
