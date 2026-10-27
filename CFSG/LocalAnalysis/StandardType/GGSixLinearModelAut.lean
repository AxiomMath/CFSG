module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRank

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace LinModel

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]
  {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}

@[expose] noncomputable def autOf
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    Subgroup.normalizer (ψ.range : Set G) →* MulAut (projectiveSL (m + 1) F) :=
  (MulAut.congr (AutPSL.projEquiv hker hC)).symm.toMonoidHom.comp ψ.range.normalizerMonoidHom

variable (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
  (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)

include hker hC in
theorem autOf_injective : Function.Injective (autOf hker hC) := by
  have hφ : Function.Injective ψ.range.normalizerMonoidHom := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker, hC, Subgroup.bot_subgroupOf]
  exact (MulAut.congr (AutPSL.projEquiv hker hC)).symm.injective.comp hφ

include hker hC in
theorem autOf_apply_proj {g : G} (hg : g ∈ Subgroup.normalizer (ψ.range : Set G))
    (u u' : Matrix.SpecialLinearGroup (Fin (m + 1)) F) (h : g * ψ u * g⁻¹ = ψ u') :
    autOf hker hC ⟨g, hg⟩ (proj (m + 1) F u) = proj (m + 1) F u' := by
  change (AutPSL.projEquiv hker hC).symm (ψ.range.normalizerMonoidHom ⟨g, hg⟩
    (AutPSL.projEquiv hker hC (proj (m + 1) F u))) = proj (m + 1) F u'
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  change g * ψ u * g⁻¹ = ψ u'
  exact h

theorem slConjugation_eq_conjSL (A : GL (Fin (m + 1)) F)
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (m + 1) F A u =
      InnerDiagA.conjSL A u :=
  Subtype.ext (by rw [coe_slConjugation, InnerDiagA.coe_conjSL])

include hker hC in
theorem autOf_eq_conjAut_iff {g : G} (hg : g ∈ Subgroup.normalizer (ψ.range : Set G))
    (A : GL (Fin (m + 1)) F) :
    autOf hker hC ⟨g, hg⟩ = conjAut (m + 1) F A ↔ (g, A) ∈ LinFusion.ggInducedPairs ψ := by
  constructor
  · intro h u
    have key : autOf hker hC ⟨g, hg⟩ (proj (m + 1) F u) =
        proj (m + 1) F (InnerDiagA.conjSL A u) := by
      rw [h, conjAut_proj, slConjugation_eq_conjSL]
    change (AutPSL.projEquiv hker hC).symm (ψ.range.normalizerMonoidHom ⟨g, hg⟩
      (AutPSL.projEquiv hker hC (proj (m + 1) F u))) = _ at key
    rw [MulEquiv.symm_apply_eq] at key
    exact congrArg Subtype.val key
  · intro h
    ext x
    obtain ⟨u, rfl⟩ := proj_surjective (m + 1) F x
    rw [autOf_apply_proj hker hC hg u (InnerDiagA.conjSL A u) (LinFusion.mem_ggInducedPairs.mp h u),
      conjAut_proj, slConjugation_eq_conjSL]

theorem pow_mod_of_pow_eq_one {p : ℕ} {ω : F} (hω : ω ^ p = 1) (n : ℕ) : ω ^ n = ω ^ (n % p) := by
  conv_lhs => rw [← Nat.div_add_mod n p, pow_add, pow_mul, hω, one_pow, one_mul]

theorem fieldAut_fixes_root {p : ℕ} (hp : p.Prime) {ω : F} (hω : IsPrimitiveRoot ω p)
    {σ : F ≃+* F} {k : ℕ} (hσ : σ ^ (p ^ k) = 1) {x : F} (hx : x ^ p = 1) : σ x = x := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, hsp, hs⟩ := hω.eq_pow_of_pow_eq_one (ξ := σ ω)
    (by rw [← map_pow, hω.pow_eq_one, map_one])
  have hiter : ∀ j : ℕ, (σ ^ j) ω = ω ^ (s ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', RingAut.mul_apply, ih, map_pow, ← hs, ← pow_mul, pow_succ']
  have h1 : ω ^ 1 = ω ^ (s ^ (p ^ k) % p) := by
    rw [← pow_mod_of_pow_eq_one hω.pow_eq_one, ← hiter, hσ, pow_one]
    rfl
  have h2 : s ^ (p ^ k) % p = 1 :=
    (hω.pow_inj hp.one_lt (Nat.mod_lt _ hp.pos) h1).symm
  have h3 : (s : ZMod p) = 1 := by
    have h4 : ((s ^ (p ^ k) : ℕ) : ZMod p) = 1 := by
      rw [← ZMod.natCast_mod, h2, Nat.cast_one]
    rwa [Nat.cast_pow, ZMod.pow_card_pow] at h4
  have h5 : s = 1 := by
    have h6 : s % p = 1 % p := by
      rw [← ZMod.natCast_eq_natCast_iff', h3, Nat.cast_one]
    rwa [Nat.mod_eq_of_lt hsp, Nat.mod_eq_of_lt hp.one_lt] at h6
  obtain ⟨i, -, hi⟩ := hω.eq_pow_of_pow_eq_one hx
  rw [← hi, map_pow, ← hs, h5, pow_one]

include hker hC in
theorem exists_mem_ggInducedPairs_of_pow_pow_eq_one [Finite F] [CharP F 2] (hm : 2 ≤ m)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    (hreal : ∀ A : GL (Fin (m + 1)) F, ∃ g : G, (g, A) ∈ LinFusion.ggInducedPairs ψ)
    {Bs : Subgroup G} (hBs : rootTorus p ψ = Bs)
    (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {u : G} (hu : u ∈ Subgroup.normalizer (ψ.range : Set G)) {k : ℕ} (huk : u ^ (p ^ k) = 1) :
    ∃ A : GL (Fin (m + 1)) F, (u, A) ∈ LinFusion.ggInducedPairs ψ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := TypeA.PGLTor.exists_isPrimitiveRoot_of_dvd hp hpF
  set N := Subgroup.normalizer (ψ.range : Set G)
  set χ := autOf hker hC with hχdef
  set α := χ ⟨u, hu⟩ with hαdef
  have hαk : α ^ (p ^ k) = 1 := by
    rw [hαdef, ← map_pow]
    have : (⟨u, hu⟩ : N) ^ (p ^ k) = 1 := Subtype.ext (by simpa using huk)
    rw [this, map_one]
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := F) (n := m + 1) (by omega)).2 α
  have hε0 : ε = 0 := HypSixTypeA.graph_exp_eq_zero (n := m + 1) (by omega)
    ((hp.odd_of_ne_two hp2).pow) hε (by rw [← hαeq]; exact hαk)
  subst hε0
  rw [pow_zero, mul_one] at hαeq
  have hI := AutPSL.inndiag_normal (n := m + 1) (K := F) (by omega)
  have hmk : ∀ v : MulAut (projectiveSL (m + 1) F), ∀ B : GL (Fin (m + 1)) F, ∀ ρ : F ≃+* F,
      v = conjAut (m + 1) F B * fieldAut (m + 1) F ρ →
      (QuotientGroup.mk v : MulAut (projectiveSL (m + 1) F) ⧸ AutPSL.inndiag) =
        QuotientGroup.mk (fieldAut (m + 1) F ρ) := by
    intro v B ρ hv
    rw [hv, QuotientGroup.eq]
    have := hI.conj_mem _ (inv_mem (⟨B, rfl⟩ : conjAut (m + 1) F B ∈ AutPSL.inndiag))
      (fieldAut (m + 1) F ρ)⁻¹
    convert this using 1
    group
  have hσk : σ ^ (p ^ k) = 1 := by
    have h2 : (QuotientGroup.mk (fieldAut (m + 1) F (σ ^ (p ^ k))) :
        MulAut (projectiveSL (m + 1) F) ⧸ AutPSL.inndiag) = 1 := by
      rw [map_pow, QuotientGroup.mk_pow, ← hmk α A σ hαeq, ← QuotientGroup.mk_pow, hαk,
        QuotientGroup.mk_one]
    exact AutPSL.eq_one_of_fieldAut_mem (by omega) ((QuotientGroup.eq_one_iff _).mp h2)
  by_cases hσ1 : σ = 1
  · rw [hσ1, map_one, mul_one] at hαeq
    exact ⟨A, (autOf_eq_conjAut_iff hker hC hu A).mp hαeq⟩
  exfalso
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hσk)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, pow_zero, orderOf_eq_one_iff] at hj
      exact absurd hj hσ1
    · exact ⟨j - 1, by omega⟩
  set τ := σ ^ (p ^ i) with hτdef
  have hτp : τ ^ p = 1 := by
    rw [hτdef, ← pow_mul, ← pow_succ, ← hj, pow_orderOf_eq_one]
  have hτ1 : τ ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hj] at h1
    have h2 := Nat.le_of_dvd (pow_pos hp.pos _) h1
    have h3 := Nat.pow_lt_pow_right hp.one_lt (show i < i + 1 by omega)
    omega
  set u' := u ^ (p ^ i) with hu'def
  have hu' : u' ∈ N := Subgroup.pow_mem _ hu _
  have hαu' : χ ⟨u', hu'⟩ = α ^ (p ^ i) := by
    rw [hαdef, ← map_pow]
    rfl
  have hmk' : (QuotientGroup.mk (χ ⟨u', hu'⟩) : MulAut (projectiveSL (m + 1) F) ⧸
      AutPSL.inndiag) = QuotientGroup.mk (fieldAut (m + 1) F τ) := by
    rw [hαu', QuotientGroup.mk_pow, hmk α A σ hαeq, ← QuotientGroup.mk_pow, ← map_pow]
  rw [QuotientGroup.eq] at hmk'
  obtain ⟨A', hA'⟩ := hmk'
  obtain ⟨g₀, hg₀⟩ := hreal A'
  have hg₀N : g₀ ∈ N := mem_normalizer_of_mem_ggInducedPairs hg₀
  have hχg₀ : χ ⟨g₀, hg₀N⟩ = conjAut (m + 1) F A' :=
    (autOf_eq_conjAut_iff hker hC hg₀N A').mpr hg₀
  set g := u' * g₀ with hgdef
  have hgN : g ∈ N := Subgroup.mul_mem _ hu' hg₀N
  have hχg : χ ⟨g, hgN⟩ = fieldAut (m + 1) F τ := by
    have : (⟨g, hgN⟩ : N) = ⟨u', hu'⟩ * ⟨g₀, hg₀N⟩ := rfl
    rw [this, map_mul, hχg₀, hA', mul_inv_cancel_left]
  have hgp : g ^ p = 1 := by
    have h1 : χ (⟨g, hgN⟩ ^ p) = χ 1 := by
      rw [map_pow, hχg, ← map_pow, hτp, map_one, map_one]
    have h2 := congrArg Subtype.val (autOf_injective hker hC h1)
    simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using h2
  have hgC : g ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hBs] at hb
    obtain ⟨d, hd, hbd⟩ := hb
    have hbN : b ∈ N := mem_normalizer_of_mem_ggInducedPairs hbd
    have hχb : χ ⟨b, hbN⟩ = conjAut (m + 1) F (InnerDiagA.diagGL d) :=
      (autOf_eq_conjAut_iff hker hC hbN _).mpr hbd
    have hmapD : GeneralLinearGroup.map (τ : F →+* F) (InnerDiagA.diagGL d) =
        InnerDiagA.diagGL d := by
      apply Units.ext
      ext a c
      rw [GeneralLinearGroup.map_apply, diagGL_apply]
      split_ifs with hac
      · have hτk : τ ^ (p ^ 1) = 1 := by rw [pow_one]; exact hτp
        have hdp : ((d a : Fˣ) : F) ^ p = 1 := by
          rw [← Units.val_pow_eq_pow_val, hd a, Units.val_one]
        exact fieldAut_fixes_root hp hζ hτk hdp
      · exact map_zero _
    have h1 : χ (⟨g, hgN⟩ * ⟨b, hbN⟩ * (⟨g, hgN⟩)⁻¹) = χ ⟨b, hbN⟩ := by
      rw [map_mul, map_mul, map_inv, hχg, hχb,
        (standard_automorphism_transport (K := F) (n := m + 1)).2.2.1, hmapD]
    have h3 : g * b * g⁻¹ = b := congrArg Subtype.val (autOf_injective hker hC h1)
    calc b * g = g * b * g⁻¹ * g := by rw [h3]
      _ = g * b := by group
  have hgB := hom g hgC hgp
  rw [← hBs] at hgB
  obtain ⟨d, -, hgd⟩ := hgB
  have hχg' := (autOf_eq_conjAut_iff hker hC hgN (InnerDiagA.diagGL d)).mpr hgd
  rw [hχg] at hχg'
  exact hτ1 (AutPSL.eq_one_of_fieldAut_mem (by omega) ⟨_, hχg'.symm⟩)

end LinModel

end CFSG.StandardType
