module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derFixOrth
import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l48gL_eq_zero_or_one {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 2) (a : K) : a = 0 ∨ a = 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K ≤ 2 := by rw [← Nat.card_eq_fintype_card]; omega
  have hmem : a ∈ ({0, 1} : Finset K) := by
    rw [← Finset.univ_of_card_le_two (R := K) hcard]
    exact Finset.mem_univ a
  simpa using hmem

private lemma l48gL_poly {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    {P : Type*} [AddCommGroup P] [Module K P] [FiniteDimensional K P]
    (hP : Module.finrank K P = 2)
    (φ : P →ₗ[K] P) (hφ3 : ∀ w : P, φ (φ (φ w)) = w) (hfix : ∀ v : P, φ v = v → v = 0)
    (c : P →ₗ[K] P) (hc : c * φ = φ * c) :
    ∃ a b : K, c = a • 1 + b • φ := by
  haveI : Nontrivial P := Module.nontrivial_of_finrank_pos (by rw [hP]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : P)
  have h3v : φ (φ (φ v)) = v := hφ3 v
  have hsq : ∀ w : P, φ (φ w) + φ w + w = 0 := by
    intro w
    have h3 : φ (φ (φ w)) = w := hφ3 w
    have hfixu : φ (φ (φ w) + φ w + w) = φ (φ w) + φ w + w := by
      rw [map_add, map_add, h3]
      abel
    exact hfix _ hfixu
  have hspan : Submodule.span K ({v, φ v} : Set P) = ⊤ := by
    by_contra hne
    have hlt : Submodule.span K ({v, φ v} : Set P) < ⊤ := lt_of_le_of_ne le_top hne
    have hlt' : Module.finrank K (Submodule.span K ({v, φ v} : Set P)) < Module.finrank K P := by
      simpa using Submodule.finrank_lt_finrank_of_lt hlt
    rw [hP] at hlt'
    have h1 : Submodule.span K ({v} : Set P) ≤ Submodule.span K ({v, φ v} : Set P) :=
      Submodule.span_mono (by
        intro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst hx
        simp)
    have hle1 : 1 ≤ Module.finrank K (Submodule.span K ({v, φ v} : Set P)) := by
      have h := Submodule.finrank_mono h1
      rwa [finrank_span_singleton hv] at h
    have hfin1 : Module.finrank K (Submodule.span K ({v, φ v} : Set P)) = 1 := by omega
    have heq : Submodule.span K ({v, φ v} : Set P) = Submodule.span K ({v} : Set P) :=
      (Submodule.eq_of_le_of_finrank_eq h1 (by rw [hfin1, finrank_span_singleton hv])).symm
    have hmem : φ v ∈ Submodule.span K ({v} : Set P) := by
      rw [← heq]
      exact Submodule.subset_span (by simp)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have hφa : φ v = a • v := ha.symm
    have ha3 : a ^ 3 = 1 := by
      have h2 : φ (φ v) = (a * a) • v := by
        rw [hφa, map_smul, hφa, smul_smul]
      have h3 : φ (φ (φ v)) = (a * a * a) • v := by
        rw [h2, map_smul, hφa, smul_smul]
      have hzero : (a ^ 3 - 1) • v = 0 := by
        have h4 : a ^ 3 • v = v := by
          have h5 : a ^ 3 = a * a * a := by ring
          rw [h5, ← h3, h3v]
        rw [sub_smul, h4, one_smul, sub_self]
      rcases smul_eq_zero.mp hzero with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hφa
      exact hv (by rw [← h3v, hφa]; simp)
    have ha1 : a = 1 := by
      rcases l48gL_eq_zero_or_one hK a with h | h
      · exact absurd h ha0
      · exact h
    exact hv (hfix v (by rw [hφa, ha1, one_smul]))
  have hmem : c v ∈ Submodule.span K ({v, φ v} : Set P) := hspan ▸ Submodule.mem_top
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
  refine ⟨a, b, ?_⟩
  have h1 : c v = (a • (1 : P →ₗ[K] P) + b • φ) v := by
    rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.smul_apply]
    exact hab.symm
  have h2 : c (φ v) = (a • (1 : P →ₗ[K] P) + b • φ) (φ v) := by
    have hc' : c (φ v) = φ (c v) := by
      have := congrArg (fun f : P →ₗ[K] P => f v) hc
      simpa [Module.End.mul_apply] using this
    rw [hc', h1]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul]
  have heq : Set.EqOn c (a • (1 : P →ₗ[K] P) + b • φ) ({v, φ v} : Set P) := by
    intro z hz
    rcases hz with rfl | rfl
    · exact h1
    · exact h2
  ext w
  exact LinearMap.eqOn_span heq (hspan ▸ Submodule.mem_top)

private lemma l48gL_poly_commute {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    {P : Type*} [AddCommGroup P] [Module K P] [FiniteDimensional K P]
    (hP : Module.finrank K P = 2)
    (φ : P →ₗ[K] P) (hφ3 : ∀ w : P, φ (φ (φ w)) = w) (hfix : ∀ v : P, φ v = v → v = 0)
    {c d : P →ₗ[K] P} (hc : c * φ = φ * c) (hd : d * φ = φ * d) : c * d = d * c := by
  obtain ⟨a, b, rfl⟩ := l48gL_poly hK hP φ hφ3 hfix c hc
  obtain ⟨a', b', rfl⟩ := l48gL_poly hK hP φ hφ3 hfix d hd
  ext w
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    map_add, map_smul]
  module

private lemma l48gC_inv_comm {G : Type*} [Group G] {c g : G} (h : c * g = g * c) :
    c⁻¹ * g = g * c⁻¹ := by
  calc c⁻¹ * g = c⁻¹ * (g * c) * c⁻¹ := by group
    _ = c⁻¹ * (c * g) * c⁻¹ := by rw [h]
    _ = g * c⁻¹ := by group

private lemma l48gC_rep_mul_comm {K : Type} [Field K] [Finite K] [CharP K 2]
    {a b : LargeEvenProj (LargeEvenSpGroup K 4)} (h : a * b = b * a) :
    (SmallRule.spRep a : Module.End K (Fin 4 ⊕ Fin 4 → K)) *
        (SmallRule.spRep b : Module.End K (Fin 4 ⊕ Fin 4 → K)) =
      (SmallRule.spRep b : Module.End K (Fin 4 ⊕ Fin 4 → K)) *
        (SmallRule.spRep a : Module.End K (Fin 4 ⊕ Fin 4 → K)) := by
  have h1 : SmallRule.spRep a * SmallRule.spRep b =
      SmallRule.spRep b * SmallRule.spRep a := by
    rw [← map_mul, ← map_mul, h]
  have := congrArg
    (fun u : (Module.End K (Fin 4 ⊕ Fin 4 → K))ˣ =>
      (u : Module.End K (Fin 4 ⊕ Fin 4 → K))) h1
  simpa [Units.val_mul] using this

theorem ggB2der_sixfix_centralizer {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {g : LargeEvenProj (LargeEvenSpGroup K 4)} (hg3 : g ^ 3 = 1)
    {W : Submodule K (Fin 4 ⊕ Fin 4 → K)}
    (hWdef : W = SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g))
    (hW : Module.finrank K W = 6) :
    ggSpFixPerp W ≤ Subgroup.centralizer ({g} : Set (LargeEvenProj (LargeEvenSpGroup K 4))) ∧
      (∀ c ∈ Subgroup.centralizer ({g} : Set (LargeEvenProj (LargeEvenSpGroup K 4))),
        ∀ s ∈ ggSpFixPerp W, c * s * c⁻¹ ∈ ggSpFixPerp W) ∧
      ⁅Subgroup.centralizer ({g} : Set (LargeEvenProj (LargeEvenSpGroup K 4))),
        Subgroup.centralizer ({g} : Set (LargeEvenProj (LargeEvenSpGroup K 4)))⁆ ≤
          ggSpFixPerp W := by
  classical
  set B : LinearMap.BilinForm K (Fin 4 ⊕ Fin 4 → K) := SmallRule.spBilin K 4 with hBdef
  have hB_alt : B.IsAlt := by rw [hBdef]; exact CFSG.ClassicalGroups.Symplectic.spForm_isAlt
  have hB_nd : B.Nondegenerate := by rw [hBdef]; exact SmallRule.spBilin_nondegenerate
  have hB_refl : B.IsRefl := by rw [hBdef]; exact SmallRule.spBilin_isRefl
  set P : Submodule K (Fin 4 ⊕ Fin 4 → K) := B.orthogonal W with hPdef
  set SW : Subgroup (LargeEvenProj (LargeEvenSpGroup K 4)) := ggSpFixPerp W with hSWdef
  have hdecomp := ggB2der_fix_orth_decomp (K := K) (V := Fin 4 ⊕ Fin 4 → K)
    (G := LargeEvenProj (LargeEvenSpGroup K 4)) hK SmallRule.spRep B hB_nd hB_refl
    (fun r v w => by rw [hBdef]; exact SmallRule.spRep_isometry r v w) hg3
  obtain ⟨hcompl0, hWinv, hPinv, hPfix⟩ := hdecomp
  rw [← hWdef] at hcompl0 hWinv hPinv hPfix
  have hcompl : IsCompl W P := hcompl0
  have hV8 : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hsum : Module.finrank K W + Module.finrank K P = 8 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq W P
    rw [hcompl.sup_eq_top, hcompl.inf_eq_bot] at h
    simp only [finrank_top, finrank_bot, add_zero] at h
    rw [← h, hV8]
  have hP2 : Module.finrank K P = 2 := by omega
  have hmemW : ∀ v : Fin 4 ⊕ Fin 4 → K,
      v ∈ W → (SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)) v = v := by
    intro v hv
    rw [hWdef, SmallRule.mem_fixSpaceOf] at hv
    exact hv g (Subgroup.mem_zpowers g)
  have hSW_le_Rg :
      SW ≤ Subgroup.centralizer ({g} : Set (LargeEvenProj (LargeEvenSpGroup K 4))) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfixP : ∀ v ∈ P, (SmallRule.spRep s : Module.End K (Fin 4 ⊕ Fin 4 → K)) v = v := by
      intro v hv
      rw [hSWdef] at hs
      rw [hPdef] at hv
      exact hs v hv
    have hBW : ∀ y ∈ W, (SmallRule.spRep s : Module.End K (Fin 4 ⊕ Fin 4 → K)) y ∈ W := by
      intro y hy
      have hBy0 : ∀ p ∈ P, B ((SmallRule.spRep s : Module.End K (Fin 4 ⊕ Fin 4 → K)) y) p = 0 := by
        intro p hp
        have hsp : (SmallRule.spRep s : Module.End K (Fin 4 ⊕ Fin 4 → K)) p = p := hfixP p hp
        have h1 : B ((SmallRule.spRep s : Module.End K (Fin 4 ⊕ Fin 4 → K)) y)
            ((SmallRule.spRep s : Module.End K (Fin 4 ⊕ Fin 4 → K)) p) = B y p :=
          SmallRule.spRep_isometry s y p
        rw [hsp] at h1
        have h2 : B y p = 0 := by
          rw [hPdef] at hp
          exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hp) y hy
        rw [h1, h2]
      rw [← LinearMap.BilinForm.orthogonal_orthogonal hB_nd hB_alt.isRefl W, ← hPdef]
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro p hp
      rw [hB_alt.eq_iff]
      exact hBy0 p hp
    apply SmallRule.spRep_injective
    rw [map_mul, map_mul]
    refine Units.ext ?_
    simp only [Units.val_mul]
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ W ⊔ P := hcompl.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨w, hw, p, hp, rfl⟩ := Submodule.mem_sup.mp hv
    have hgp : (SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)) p ∈ P := hPinv g rfl p hp
    simp only [Module.End.mul_apply, map_add,
      hmemW w hw, hfixP ((SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)) p) hgp,
      hfixP p hp,
      hmemW ((SmallRule.spRep s : Module.End K (Fin 4 ⊕ Fin 4 → K)) w) (hBW w hw)]
  have hNRg : ∀ c ∈ Subgroup.centralizer ({g} : Set (LargeEvenProj (LargeEvenSpGroup K 4))),
      ∀ s ∈ SW, c * s * c⁻¹ ∈ SW := by
    intro c hc s hs
    intro v hv
    have hcg : c * g = g * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hcinv : c⁻¹ * g = g * c⁻¹ := l48gC_inv_comm hcg
    have hPcinv : ∀ x ∈ P,
        (SmallRule.spRep c⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K)) x ∈ P :=
      hPinv c⁻¹ hcinv
    have hsp : (SmallRule.spRep s : Module.End K (Fin 4 ⊕ Fin 4 → K))
          ((SmallRule.spRep c⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K)) v) =
        (SmallRule.spRep c⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K)) v :=
      hs _ (hPcinv v hv)
    have hcoe : (SmallRule.spRep (c * s * c⁻¹) : Module.End K (Fin 4 ⊕ Fin 4 → K)) =
        (SmallRule.spRep c : Module.End K (Fin 4 ⊕ Fin 4 → K)) *
          (SmallRule.spRep s : Module.End K (Fin 4 ⊕ Fin 4 → K)) *
          (SmallRule.spRep c⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K)) := by
      rw [map_mul, map_mul]
      simp only [Units.val_mul]
    have h1 : (SmallRule.spRep (c * s * c⁻¹) : Module.End K (Fin 4 ⊕ Fin 4 → K)) v =
        (SmallRule.spRep c : Module.End K (Fin 4 ⊕ Fin 4 → K))
          ((SmallRule.spRep s : Module.End K (Fin 4 ⊕ Fin 4 → K))
            ((SmallRule.spRep c⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K)) v)) := by
      rw [hcoe]
      simp only [Module.End.mul_apply]
    rw [h1, hsp]
    have hcancel : ∀ w : Fin 4 ⊕ Fin 4 → K,
        (SmallRule.spRep c : Module.End K (Fin 4 ⊕ Fin 4 → K))
          ((SmallRule.spRep c⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K)) w) = w := by
      intro w
      have hmul : (SmallRule.spRep c : Module.End K (Fin 4 ⊕ Fin 4 → K)) *
          (SmallRule.spRep c⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K)) = 1 := by
        rw [← Units.val_mul, map_inv, mul_inv_cancel, Units.val_one]
      rw [← Module.End.mul_apply, hmul, Module.End.one_apply]
    exact hcancel v
  have hRg_deriv : ⁅Subgroup.centralizer ({g} : Set (LargeEvenProj (LargeEvenSpGroup K 4))),
      Subgroup.centralizer ({g} : Set (LargeEvenProj (LargeEvenSpGroup K 4)))⁆ ≤ SW := by
    rw [Subgroup.commutator_le]
    intro c hc d hd
    have hcg : c * g = g * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hdg : d * g = g * d := Subgroup.mem_centralizer_singleton_iff.mp hd
    have hPc : ∀ x ∈ P, (SmallRule.spRep c : Module.End K (Fin 4 ⊕ Fin 4 → K)) x ∈ P :=
      hPinv c hcg
    have hPd : ∀ x ∈ P, (SmallRule.spRep d : Module.End K (Fin 4 ⊕ Fin 4 → K)) x ∈ P :=
      hPinv d hdg
    have hPg : ∀ x ∈ P, (SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)) x ∈ P :=
      hPinv g rfl
    have hcgE := l48gC_rep_mul_comm (K := K) hcg
    have hdgE := l48gC_rep_mul_comm (K := K) hdg
    have hsp3u : SmallRule.spRep g ^ 3 = 1 := by
      rw [← map_pow, hg3, map_one]
    have hsp3 : (SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)) ^ 3 = 1 := by
      have h := congrArg (fun u : (Module.End K (Fin 4 ⊕ Fin 4 → K))ˣ =>
        (u : Module.End K (Fin 4 ⊕ Fin 4 → K))) hsp3u
      simpa only [Units.val_one, Units.val_pow_eq_pow_val] using h
    have h3app : ∀ v : Fin 4 ⊕ Fin 4 → K,
        (SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K))
          ((SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K))
            ((SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)) v)) = v := by
      intro v
      have h := congrArg (fun f : Module.End K (Fin 4 ⊕ Fin 4 → K) => f v) hsp3
      rw [Module.End.pow_apply, Module.End.one_apply] at h
      simpa using h
    have hφP3 : ∀ w : P,
        ((SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPg)
          (((SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPg)
            (((SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPg) w)) = w := by
      intro w
      apply Subtype.ext
      simp only [LinearMap.coe_restrict_apply]
      exact h3app (w : Fin 4 ⊕ Fin 4 → K)
    have hfixP' : ∀ v : P,
        ((SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPg) v = v → v = 0 := by
      intro v hv
      apply Subtype.ext
      have hv' : (SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)) (v : Fin 4 ⊕ Fin 4 → K) =
          (v : Fin 4 ⊕ Fin 4 → K) := by
        have := congrArg (fun z : P => (z : Fin 4 ⊕ Fin 4 → K)) hv
        simpa only [LinearMap.coe_restrict_apply] using this
      exact hPfix (v : Fin 4 ⊕ Fin 4 → K) v.2 hv'
    have hcP : ((SmallRule.spRep c : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPc) *
          ((SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPg) =
        ((SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPg) *
          ((SmallRule.spRep c : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPc) := by
      refine LinearMap.ext fun x => ?_
      refine Subtype.ext ?_
      simp only [Module.End.mul_apply, LinearMap.coe_restrict_apply]
      have := congrArg (fun f : Module.End K (Fin 4 ⊕ Fin 4 → K) =>
        f (x : Fin 4 ⊕ Fin 4 → K)) hcgE
      simpa [Module.End.mul_apply] using this
    have hdP : ((SmallRule.spRep d : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPd) *
          ((SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPg) =
        ((SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPg) *
          ((SmallRule.spRep d : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPd) := by
      refine LinearMap.ext fun x => ?_
      refine Subtype.ext ?_
      simp only [Module.End.mul_apply, LinearMap.coe_restrict_apply]
      have := congrArg (fun f : Module.End K (Fin 4 ⊕ Fin 4 → K) =>
        f (x : Fin 4 ⊕ Fin 4 → K)) hdgE
      simpa [Module.End.mul_apply] using this
    have hcdP : ((SmallRule.spRep c : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPc) *
          ((SmallRule.spRep d : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPd) =
        ((SmallRule.spRep d : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPd) *
          ((SmallRule.spRep c : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPc) :=
      l48gL_poly_commute hK hP2
        ((SmallRule.spRep g : Module.End K (Fin 4 ⊕ Fin 4 → K)).restrict hPg)
        hφP3 hfixP' hcP hdP
    have hcommP : ∀ z ∈ P,
        (SmallRule.spRep c : Module.End K (Fin 4 ⊕ Fin 4 → K))
          ((SmallRule.spRep d : Module.End K (Fin 4 ⊕ Fin 4 → K)) z) =
        (SmallRule.spRep d : Module.End K (Fin 4 ⊕ Fin 4 → K))
          ((SmallRule.spRep c : Module.End K (Fin 4 ⊕ Fin 4 → K)) z) := by
      intro z hz
      have := congrArg (fun f : P →ₗ[K] P => ((f ⟨z, hz⟩ : P) : Fin 4 ⊕ Fin 4 → K)) hcdP
      simpa only [Module.End.mul_apply, LinearMap.coe_restrict_apply] using this
    intro v hv
    have hdv : (SmallRule.spRep d⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K)) v ∈ P :=
      hPinv d⁻¹ (l48gC_inv_comm hdg) v hv
    have hcdv : (SmallRule.spRep c⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K))
        ((SmallRule.spRep d⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K)) v) ∈ P :=
      hPinv c⁻¹ (l48gC_inv_comm hcg) _ hdv
    have hcc : ∀ w : Fin 4 ⊕ Fin 4 → K,
        (SmallRule.spRep c : Module.End K (Fin 4 ⊕ Fin 4 → K))
          ((SmallRule.spRep c⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K)) w) = w := by
      intro w
      have hmul : (SmallRule.spRep c : Module.End K (Fin 4 ⊕ Fin 4 → K)) *
          (SmallRule.spRep c⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K)) = 1 := by
        rw [← Units.val_mul, map_inv, mul_inv_cancel, Units.val_one]
      rw [← Module.End.mul_apply, hmul, Module.End.one_apply]
    have hdd : ∀ w : Fin 4 ⊕ Fin 4 → K,
        (SmallRule.spRep d : Module.End K (Fin 4 ⊕ Fin 4 → K))
          ((SmallRule.spRep d⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K)) w) = w := by
      intro w
      have hmul : (SmallRule.spRep d : Module.End K (Fin 4 ⊕ Fin 4 → K)) *
          (SmallRule.spRep d⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K)) = 1 := by
        rw [← Units.val_mul, map_inv, mul_inv_cancel, Units.val_one]
      rw [← Module.End.mul_apply, hmul, Module.End.one_apply]
    have hgoal : (SmallRule.spRep (c * d * c⁻¹ * d⁻¹) :
        Module.End K (Fin 4 ⊕ Fin 4 → K)) v = v := by
      have hcoe : (SmallRule.spRep (c * d * c⁻¹ * d⁻¹) :
            Module.End K (Fin 4 ⊕ Fin 4 → K)) =
          (SmallRule.spRep c : Module.End K (Fin 4 ⊕ Fin 4 → K)) *
            (SmallRule.spRep d : Module.End K (Fin 4 ⊕ Fin 4 → K)) *
            (SmallRule.spRep c⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K)) *
            (SmallRule.spRep d⁻¹ : Module.End K (Fin 4 ⊕ Fin 4 → K)) := by
        rw [map_mul, map_mul, map_mul]
        simp only [Units.val_mul]
      rw [hcoe]
      simp only [Module.End.mul_apply]
      rw [hcommP _ hcdv, hcc, hdd]
    exact hgoal
  refine ⟨hSW_le_Rg, ?_, hRg_deriv⟩
  intro c hc s hs
  exact hNRg c hc s hs

end CFSG.StandardType

end
