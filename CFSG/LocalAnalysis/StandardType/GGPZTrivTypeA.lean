module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosure
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBAutCard
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification TypeA

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pzta_exists_perm_of_conj_mem_normalizer {d p : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) {L' : Type} [Group L'] [Finite L']
    {φ' : Matrix.SpecialLinearGroup (Fin d) K →* L'} (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, TypeANbrDvd.ActsDiag φ' a t)
    (hfull : ∀ D : Matrix.SpecialLinearGroup (Fin d) K,
      (∃ t : Fin d → K, (D : Matrix (Fin d) (Fin d) K) = diagonal t) → D ^ p = 1 →
        MulAut.conj (φ' D) ∈ A)
    {s : Matrix.SpecialLinearGroup (Fin d) K}
    (hs : MulAut.conj (φ' s) ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ∃ σ : Equiv.Perm (Fin d), ∀ a ∈ A,
      MulAut.conj (φ' s) * a * (MulAut.conj (φ' s))⁻¹ =
        NbrInnerWeylA.permConj φ' σ * a * (NbrInnerWeylA.permConj φ' σ)⁻¹ := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (K := K) hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζinv : ζ ≠ ζ⁻¹ := ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hmono : ∀ i j : Fin d, i ≠ j → ∃ D : Fin d → K,
      (↑s : Matrix (Fin d) (Fin d) K) * diagonal (rootT ζ i j) =
        diagonal D * (↑s : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    set Dij : Matrix.SpecialLinearGroup (Fin d) K :=
      ⟨diagonal (rootT ζ i j), by rw [det_diagonal, prod_rootT hζ0 hij]⟩ with hDij
    have hDijm : (Dij : Matrix (Fin d) (Fin d) K) = diagonal (rootT ζ i j) := rfl
    have haij : MulAut.conj (φ' Dij) ∈ A :=
      hfull Dij ⟨rootT ζ i j, hDijm⟩
        (TypeANbrDvd.pow_eq_one_of_diagonal hDijm (rootT_pow hζ.pow_eq_one i j))
    have hbij : MulAut.conj (φ' s) * MulAut.conj (φ' Dij) * (MulAut.conj (φ' s))⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hs (MulAut.conj (φ' Dij))).mp haij
    obtain ⟨w, hwb⟩ := hdiag (MulAut.conj (φ' s) * MulAut.conj (φ' Dij) *
      (MulAut.conj (φ' s))⁻¹) hbij
    have hb_eq : MulAut.conj (φ' s) * MulAut.conj (φ' Dij) * (MulAut.conj (φ' s))⁻¹ =
        MulAut.conj (φ' (s * Dij * s⁻¹)) := by
      simp only [map_mul, map_inv]
    rw [hb_eq] at hwb
    obtain ⟨c, hc⟩ := TypeANbrDvd.exists_diagonal_of_actsDiag_conj hφker hwb
    refine ⟨fun k => c * w k, ?_⟩
    have hscaled : (↑(s * Dij * s⁻¹) : Matrix (Fin d) (Fin d) K) *
        (↑s : Matrix (Fin d) (Fin d) K) =
        (↑s : Matrix (Fin d) (Fin d) K) * (Dij : Matrix (Fin d) (Fin d) K) := by
      calc (↑(s * Dij * s⁻¹) : Matrix (Fin d) (Fin d) K) * (↑s : Matrix (Fin d) (Fin d) K)
          = ((↑s : Matrix (Fin d) (Fin d) K) * (Dij : Matrix (Fin d) (Fin d) K)) *
              (↑(s⁻¹) : Matrix (Fin d) (Fin d) K) * (↑s : Matrix (Fin d) (Fin d) K) := by
            rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
        _ = ((↑s : Matrix (Fin d) (Fin d) K) * (Dij : Matrix (Fin d) (Fin d) K)) *
              ((↑(s⁻¹) : Matrix (Fin d) (Fin d) K) * (↑s : Matrix (Fin d) (Fin d) K)) := by
            rw [Matrix.mul_assoc]
        _ = ((↑s : Matrix (Fin d) (Fin d) K) * (Dij : Matrix (Fin d) (Fin d) K)) * 1 := by
            rw [show (↑(s⁻¹) : Matrix (Fin d) (Fin d) K) *
                  (↑s : Matrix (Fin d) (Fin d) K) = 1 by
                rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
                  Matrix.SpecialLinearGroup.coe_one]]
        _ = (↑s : Matrix (Fin d) (Fin d) K) * (Dij : Matrix (Fin d) (Fin d) K) := by
            rw [Matrix.mul_one]
    have h1 := congrArg (fun M : Matrix (Fin d) (Fin d) K =>
      M * (↑s : Matrix (Fin d) (Fin d) K)) hc
    rw [hscaled, hDijm] at h1
    exact h1
  obtain ⟨π, hπ⟩ := exists_perm_mul_diagonal hζinv (Matrix.SpecialLinearGroup.toGL s)
    (fun i j hij => by
      obtain ⟨D, hD⟩ := hmono i j hij
      exact ⟨D, by simpa only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hD⟩)
  refine ⟨π⁻¹, fun a ha => ?_⟩
  obtain ⟨t, hat⟩ := hdiag a ha
  have hs' : (↑s : Matrix (Fin d) (Fin d) K) * diagonal t =
      diagonal (t ∘ π) * (↑s : Matrix (Fin d) (Fin d) K) := by
    simpa only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hπ t
  have hL : TypeANbrDvd.ActsDiag φ' (MulAut.conj (φ' s) * a * (MulAut.conj (φ' s))⁻¹) (t ∘ π) :=
    TypeANbrDvd.ActsDiag.conj_of_mul_diagonal hat hs'
  have hR : TypeANbrDvd.ActsDiag φ' (MulAut.conj (φ' (permSL π)) * a *
      (MulAut.conj (φ' (permSL π)))⁻¹) (t ∘ π) := hat.conj_perm π
  have hpc : NbrInnerWeylA.permConj φ' (π⁻¹) = MulAut.conj (φ' (permSL π)) := by
    show MulAut.conj (φ' (permSL (π⁻¹)⁻¹)) = MulAut.conj (φ' (permSL π))
    rw [inv_inv]
  rw [hpc]
  exact hL.unique hφ's hR

private theorem pzta_automizer_le_permAut {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) {L' : Type} [Group L'] [Finite L']
    {φ' : Matrix.SpecialLinearGroup (Fin d) K →* L'} (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, TypeANbrDvd.ActsDiag φ' a t)
    (hfull : ∀ D : Matrix.SpecialLinearGroup (Fin d) K,
      (∃ t : Fin d → K, (D : Matrix (Fin d) (Fin d) K) = diagonal t) → D ^ p = 1 →
        MulAut.conj (φ' D) ∈ A)
    (hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A ≤
      (TypeANbrDvd.permAut φ' A hN).range := by
  intro φ hφ
  obtain ⟨g, ⟨l, rfl⟩, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  obtain ⟨s, rfl⟩ := hφ's l
  obtain ⟨σ, hσ⟩ :=
    pzta_exists_perm_of_conj_mem_normalizer hp hp2 hpK hφ's hφker hdiag hfull hgN
  refine MonoidHom.mem_range.mpr ⟨σ, ?_⟩
  refine MulEquiv.ext fun b => Subtype.ext ?_
  rw [TypeANbrDvd.permAut_apply, ggConjAut_apply, hφg b]
  exact (hσ b b.2).symm


theorem ggPZ_automizer_typeA
    {G : Type} [Group G] [Finite G] {p l n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {J EJ : Subgroup G} (hl : 2 ≤ l) (hpq : p ∣ 2 ^ n - 1) (hpl : p ∣ l + 3)
    (hJ : GGHasLabel ⟨.A, l, n⟩ (↥J ⧸ Subgroup.center ↥J)) (hJq : IsQuasisimple ↥J)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J)) (hEJ : EJ ≤ J) (hE : IsElemAbelian p EJ)
    (hcard : Nat.card ↥EJ = p ^ l) :
    ∃ f : Equiv.Perm (Fin (l + 1)) →* MulAut ↥EJ, ggAutomizer J EJ ≤ f.range := by
  classical
  unfold GGHasLabel at hJ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hJ
  unfold LargeEvenRecipeLinear at hJ
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hJ
  let : Field K := hKfield
  let : Finite K := hKfin
  have : Group.IsPerfect ↥J := hJq.1
  have hp : p.Prime := Fact.out
  have hpK : p ∣ Nat.card K - 1 := by rw [hKcard]; exact hpq
  have hchar : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    refine charP_of_card_eq_prime_pow (R := K) (p := 2) (f := n) ?_
    rw [← Nat.card_eq_fintype_card, hKcard]
  let : CharP K 2 := hchar
  have hpd : ¬ p ∣ l + 1 := by
    intro h
    have h2 : p ∣ 2 := by
      have hh := Nat.dvd_sub hpl h
      rwa [show l + 3 - (l + 1) = 2 by omega] at hh
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hcop : Nat.Coprime p (l + 1) := hp.coprime_iff_not_dvd.mpr hpd
  let d := l + 1
  have hd0 : 0 < d := by omega
  have hcopd : Nat.Coprime p d := hcop
  let L' : Type := ↥J ⧸ Subgroup.center ↥J
  let ψ : L' →* projectiveSL d K := (TypeA.recipeEquiv d K).toMonoidHom.comp e.toMonoidHom
  let φ : Matrix.SpecialLinearGroup (Fin d) K →* L' :=
    e.symm.toMonoidHom.comp ((TypeA.recipeEquiv d K).symm.toMonoidHom.comp (proj d K))
  have hφψ : ∀ g : Matrix.SpecialLinearGroup (Fin d) K, ψ (φ g) = proj d K g := by
    intro g
    simp only [φ, ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨y, rfl⟩ := (TypeA.recipeEquiv d K).surjective x
    obtain ⟨z, rfl⟩ := e.surjective y
    exact ⟨z, rfl⟩
  have hφs : Function.Surjective φ := by
    intro x
    obtain ⟨y, rfl⟩ := e.symm.surjective x
    obtain ⟨z, rfl⟩ := (TypeA.recipeEquiv d K).symm.surjective y
    obtain ⟨w, rfl⟩ := proj_surjective d K z
    exact ⟨w, rfl⟩
  have hφker : ∀ g : Matrix.SpecialLinearGroup (Fin d) K, φ g = 1 → g ∈ scalars d K := by
    intro g hg
    have h1 : g ∈ (proj d K).ker :=
      MonoidHom.mem_ker.mpr (by rw [← hφψ g, hg, map_one])
    rwa [ker_proj] at h1
  have hker : ψ.ker ≤ Subgroup.center L' := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : e x = 1 := (TypeA.recipeEquiv d K).injective (by simpa [ψ] using hx)
    have hx1 : x = 1 := e.injective (by rw [hx', map_one])
    rw [hx1]
    exact Subgroup.one_mem _
  have hperf : commutator L' = ⊤ := by
    have hperfJ : (⁅(⊤ : Subgroup ↥J), ⊤⁆ : Subgroup ↥J) = ⊤ := hJq.1.commutator_eq_top
    have hmap := Subgroup.map_commutator (⊤ : Subgroup ↥J) (⊤ : Subgroup ↥J)
      (QuotientGroup.mk' (Subgroup.center ↥J))
    rw [hperfJ, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective (Subgroup.center ↥J))] at hmap
    exact hmap.symm
  let f0 : ↥EJ →* L' := (QuotientGroup.mk' (Subgroup.center ↥J)).comp (Subgroup.inclusion hEJ)
  let A : Subgroup (MulAut L') := f0.range.map (MulAut.conj : L' →* MulAut L')
  have hInt : (EJ.subgroupOf J) ⊓ Subgroup.center ↥J = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxEJ : ((x : ↥J) : G) ∈ EJ := Subgroup.mem_subgroupOf.mp hx.1
    have hxp : x ^ p = 1 := by
      apply Subtype.ext
      have := hE.2 ((x : ↥J) : G) hxEJ
      simpa using this
    have hxZ : x ∈ Subgroup.center ↥J := hx.2
    have hdiv : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hxp
    rcases (Nat.dvd_prime hp).mp hdiv with h1 | hp'
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      have hdivc : orderOf (⟨x, hxZ⟩ : ↥(Subgroup.center ↥J)) ∣
          Nat.card ↥(Subgroup.center ↥J) := orderOf_dvd_natCard _
      rw [← Subgroup.orderOf_coe (⟨x, hxZ⟩ : ↥(Subgroup.center ↥J))] at hdivc
      rw [hp'] at hdivc
      exact hZ hdivc
  have hf0_inj : Function.Injective f0 := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    have hx1 : (Subgroup.inclusion hEJ) x ∈ (EJ.subgroupOf J) ⊓ Subgroup.center ↥J := by
      refine ⟨Subgroup.mem_subgroupOf.mpr (by rw [Subgroup.coe_inclusion]; exact x.2), ?_⟩
      rw [← QuotientGroup.ker_mk' (Subgroup.center ↥J)]
      exact MonoidHom.mem_ker.mpr hx
    rw [hInt, Subgroup.mem_bot] at hx1
    exact Subgroup.inclusion_injective hEJ hx1
  have hZc : Subgroup.center L' = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot ↥J
  have hconj_inj : Function.Injective (MulAut.conj : L' →* MulAut L') := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    have hxc : x ∈ Subgroup.center L' := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := congrArg (fun f : MulAut L' => f y) hx
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      calc y * x = (x * y * x⁻¹) * x := by rw [h]
        _ = x * y := by group
    rw [hZc] at hxc
    exact hxc
  let hiso : ↥EJ ≃* ↥A :=
    (MonoidHom.ofInjective hf0_inj).trans (Subgroup.equivMapOfInjective f0.range _ hconj_inj)
  have hcardA : Nat.card ↥A = p ^ (d - 1) := by
    rw [show d - 1 = l by omega]
    calc Nat.card ↥A = Nat.card ↥(f0.range) := Subgroup.card_map_of_injective hconj_inj
      _ = Nat.card ↥EJ := (Nat.card_congr (MonoidHom.ofInjective hf0_inj).toEquiv).symm
      _ = p ^ l := hcard
  have hA : IsElemAbelian p A := by
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff]
      intro x y
      calc x * y = hiso (hiso.symm x * hiso.symm y) := by
            rw [map_mul, hiso.apply_symm_apply, hiso.apply_symm_apply]
        _ = hiso (hiso.symm y * hiso.symm x) :=
            congrArg hiso (hE.1.is_comm.comm (hiso.symm x) (hiso.symm y))
        _ = y * x := by rw [map_mul, hiso.apply_symm_apply, hiso.apply_symm_apply]
    · intro x hx
      have h1 : (hiso.symm ⟨x, hx⟩ : ↥EJ) ^ p = 1 := by
        apply Subtype.ext
        have hh := hE.2 ((hiso.symm ⟨x, hx⟩ : ↥EJ) : G) (hiso.symm ⟨x, hx⟩).2
        simpa using hh
      have h2 : (⟨x, hx⟩ : ↥A) ^ p = 1 := by
        rw [← hiso.apply_symm_apply (⟨x, hx⟩ : ↥A), ← map_pow, h1, map_one]
      simpa using congrArg Subtype.val h2
  have hAI : ∀ a ∈ A, ∃ φa ∈ Set.range (conjAut d K), ∀ l : L', φa (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨s, hs⟩ := proj_surjective d K (ψ (f0 x))
    refine ⟨conjAut d K (Matrix.SpecialLinearGroup.toGL s), ⟨s, rfl⟩, fun l => ?_⟩
    rw [LinearFlag.conjAut_toGL, hs, MulAut.conj_apply]
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hperfSL : commutator (Matrix.SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega : 3 ≤ d))).commutator_eq_top
  obtain ⟨φ', hφ's, hφ'ker, hdiag_data, hle, hfull_data⟩ :=
    TypeA.exists_diagonal_model hp hpK hd0 hcopd hperfSL hψ hker hperf hφs hφψ hA hAI
  have huniq : ∀ (a : MulAut L') (D : Matrix.SpecialLinearGroup (Fin d) K),
      (∀ s, a (φ' s) = φ' (D * s * D⁻¹)) → a = MulAut.conj (φ' D) := by
    intro a D hact
    ext l
    obtain ⟨s, rfl⟩ := hφ's l
    rw [hact s, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hdiag : ∀ a ∈ A, ∃ t : Fin d → K, TypeANbrDvd.ActsDiag φ' a t := by
    intro a ha
    obtain ⟨D, ⟨t, hDt⟩, hDp, hact⟩ := hdiag_data a ha
    exact ⟨t, by rw [huniq a D hact]; exact TypeANbrDvd.actsDiag_conj hDt⟩
  have hAcar : ∀ a ∈ A, ∃ D : Matrix.SpecialLinearGroup (Fin d) K,
      (∃ t : Fin d → K, (D : Matrix (Fin d) (Fin d) K) = diagonal t) ∧ D ^ p = 1 ∧
        a = MulAut.conj (φ' D) := by
    intro a ha
    obtain ⟨D, hD, hDp, hact⟩ := hdiag_data a ha
    exact ⟨D, hD, hDp, huniq a D hact⟩
  have hAfull : ∀ D : Matrix.SpecialLinearGroup (Fin d) K,
      (∃ t : Fin d → K, (D : Matrix (Fin d) (Fin d) K) = diagonal t) → D ^ p = 1 →
        MulAut.conj (φ' D) ∈ A := by
    intro D ⟨t, hDt⟩ hDp
    have ht : ∀ i, t i ^ p = 1 := fun i => by
      have h := congrArg (fun M : Matrix (Fin d) (Fin d) K => M i i)
        (show (((D ^ p : Matrix.SpecialLinearGroup (Fin d) K)) : Matrix (Fin d) (Fin d) K) =
          1 by rw [hDp]; rfl)
      simp only [Matrix.SpecialLinearGroup.coe_pow, hDt, diagonal_pow,
        Matrix.diagonal_apply_eq, Pi.pow_apply, Matrix.one_apply_eq] at h
      exact h
    have htp : ∏ i, t i = 1 := by
      have h := D.2
      rwa [hDt, det_diagonal] at h
    obtain ⟨a, ha, D', hD', hact⟩ := hfull_data hcardA t ht htp
    have hD'D : D' = D := Subtype.ext (hD'.trans hDt.symm)
    have haeq : a = MulAut.conj (φ' D) := by rw [huniq a D' hact, hD'D]
    rw [haeq] at ha
    exact ha
  have hstep : ∀ (τ : Equiv.Perm (Fin d)) (b : MulAut L'),
      b ∈ A → NbrInnerWeylA.permConj φ' τ * b * (NbrInnerWeylA.permConj φ' τ)⁻¹ ∈ A := by
    intro τ b hb
    obtain ⟨D, ⟨t, hDt⟩, hDp, rfl⟩ := hAcar b hb
    have hperm : NbrInnerWeylA.permConj φ' τ = MulAut.conj (φ' (permSL τ.symm)) := rfl
    have heq : MulAut.conj (φ' (permSL τ.symm)) * MulAut.conj (φ' D) *
        (MulAut.conj (φ' (permSL τ.symm)))⁻¹ =
        MulAut.conj (φ' (permSL τ.symm * D * (permSL τ.symm)⁻¹)) := by
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      rw [map_mul, map_mul, map_inv]
    rw [hperm, heq]
    exact hAfull (permSL τ.symm * D * (permSL τ.symm)⁻¹)
      ⟨t ∘ τ.symm, TypeA.coe_permSL_conj hDt τ.symm⟩ (by
      rw [← MulAut.conj_apply, ← map_pow, hDp, map_one])
  have hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    intro σ
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · exact hstep σ b
    · intro hb
      have h1 := hstep σ⁻¹ (NbrInnerWeylA.permConj φ' σ * b * (NbrInnerWeylA.permConj φ' σ)⁻¹) hb
      have h2 : NbrInnerWeylA.permConj φ' σ⁻¹ = (NbrInnerWeylA.permConj φ' σ)⁻¹ :=
        map_inv (NbrInnerWeylA.permConj φ') σ
      rw [h2] at h1
      convert h1 using 1
      group
  have hle' := pzta_automizer_le_permAut hp hp2 hpK hφ's hφ'ker hdiag hAfull hN
  refine ⟨((MulAut.congr hiso).symm).toMonoidHom.comp (TypeANbrDvd.permAut φ' A hN), ?_⟩
  intro φ hφ
  obtain ⟨g, hgJ, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  let gbar : L' := QuotientGroup.mk' (Subgroup.center ↥J) ⟨g, hgJ⟩
  have hconj_mem : ∀ (h : G) (hhJ : h ∈ J)
      (hhN : h ∈ Subgroup.normalizer (EJ : Set G)), ∀ b ∈ A,
      MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥J) ⟨h, hhJ⟩) * b *
        (MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥J) ⟨h, hhJ⟩))⁻¹ ∈ A := by
    intro h hhJ hhN b hb
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨x, rfl⟩ := hy
    have hxy : (⟨h, hhJ⟩ : ↥J) * (Subgroup.inclusion hEJ) x * (⟨h, hhJ⟩ : ↥J)⁻¹ =
        (Subgroup.inclusion hEJ) ⟨h * (x : G) * h⁻¹,
          (Subgroup.mem_normalizer_iff.mp hhN (x : G)).mp x.2⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion,
        Subgroup.coe_inclusion]
    have hmem : MulAut.conj (f0 ⟨h * (x : G) * h⁻¹,
        (Subgroup.mem_normalizer_iff.mp hhN (x : G)).mp x.2⟩) ∈ A :=
      Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    have hval : QuotientGroup.mk' (Subgroup.center ↥J) ⟨h, hhJ⟩ * f0 x *
        (QuotientGroup.mk' (Subgroup.center ↥J) ⟨h, hhJ⟩)⁻¹ =
        f0 ⟨h * (x : G) * h⁻¹, (Subgroup.mem_normalizer_iff.mp hhN (x : G)).mp x.2⟩ := by
      simp only [f0, MonoidHom.comp_apply]
      rw [← hxy]
      rw [map_mul, map_mul, map_inv]
    have heq : MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥J) ⟨h, hhJ⟩) *
        MulAut.conj (f0 x) *
        (MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥J) ⟨h, hhJ⟩))⁻¹ =
        MulAut.conj (f0 ⟨h * (x : G) * h⁻¹,
          (Subgroup.mem_normalizer_iff.mp hhN (x : G)).mp x.2⟩) := by
      rw [← map_mul, ← map_inv, ← map_mul, hval]
    rw [heq]
    exact hmem
  have hgN' : MulAut.conj gbar ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · exact hconj_mem g hgJ hgN b
    · intro hb
      have h1 := hconj_mem g⁻¹ (J.inv_mem hgJ) (Subgroup.inv_mem _ hgN)
        (MulAut.conj gbar * b * (MulAut.conj gbar)⁻¹) hb
      have h2 : QuotientGroup.mk' (Subgroup.center ↥J) ⟨g⁻¹, J.inv_mem hgJ⟩ = gbar⁻¹ := by
        rw [← map_inv]
        rfl
      rw [h2] at h1
      have h3 : MulAut.conj gbar⁻¹ = (MulAut.conj gbar)⁻¹ := map_inv _ _
      rw [h3] at h1
      convert h1 using 1
      group
  have hmem : ggConjAut A hgN' ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
    ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range) (Bs := A)
      (g := MulAut.conj gbar) (MonoidHom.mem_range.mpr ⟨gbar, rfl⟩) hgN'
  obtain ⟨σ, hσ⟩ := hle' hmem
  refine MonoidHom.mem_range.mpr ⟨σ, ?_⟩
  apply (MulAut.congr hiso).injective
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rw [hσ]
  symm
  have hiso_apply : ∀ x : ↥EJ, (hiso x : MulAut L') = MulAut.conj (f0 x) := by
    intro x
    rfl
  have hf0_conj : ∀ x : ↥EJ, f0 (φ x) = gbar * f0 x * gbar⁻¹ := by
    intro x
    have hx : ((φ x : ↥EJ) : G) = g * x * g⁻¹ := hφg x
    have hφx : φ x = ⟨g * ((x : ↥EJ) : G) * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp hgN ((x : ↥EJ) : G)).mp x.2⟩ :=
      Subtype.ext hx
    rw [hφx]
    simp only [f0, gbar, MonoidHom.comp_apply]
    have hsub : (Subgroup.inclusion hEJ) ⟨g * ((x : ↥EJ) : G) * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp hgN ((x : ↥EJ) : G)).mp x.2⟩ =
        (⟨g, hgJ⟩ : ↥J) * (Subgroup.inclusion hEJ) x * (⟨g, hgJ⟩ : ↥J)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    rw [← map_mul, ← map_inv, ← map_mul, ← hsub]
  refine MulEquiv.ext fun b => Subtype.ext ?_
  obtain ⟨x, rfl⟩ := hiso.surjective b
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    hiso_apply, hf0_conj, ggConjAut_apply, hiso_apply, map_mul, map_mul, map_inv]

end CFSG.StandardType

end
