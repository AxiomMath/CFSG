module

public import CFSG.Quasithin.EmptyFaithful.SzN10Norm
public import CFSG.Quasithin.EmptyFaithful.SzN10Torus
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InSL2
public import CFSG.Quasithin.EmptyFaithful.SzN7Star

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

section Two

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem szN10_pow72 (hh : Hyp15310 G T Mc M V₁ V₂ Yp t) {g : G} (hg : g ∈ M) :
    g ^ 72 ∈ Subgroup.centralizer (VZ T M : Set G) := by
  obtain ⟨hV, L₁, L₂, tb, hS, -⟩ := hh.decomp.model
  have hcard : Nat.card ↥(autI hV M) = 72 := hS.card_X
  have hgN : g ∈ Subgroup.normalizer (VZ T M : Set G) := hh.hyp.le_normalizer hg
  have hmem : convI hV ⟨g, hgN⟩ ∈ autI hV M := convI_mem_autI hV hg hgN
  have h1 : (⟨convI hV ⟨g, hgN⟩, hmem⟩ : ↥(autI hV M)) ^ 72 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have h2 : convI hV ⟨g, hgN⟩ ^ 72 = 1 := by
    have := congrArg Subtype.val h1
    simpa using this
  have h3 : convI hV ((⟨g, hgN⟩ : ↥(Subgroup.normalizer (VZ T M : Set G))) ^ 72) = 1 := by
    rw [map_pow]
    exact h2
  have h4 := (convI_eq_one_iff hV _).mp h3
  simpa using h4

theorem szN10_n_eq_two (ctx : Ctx15316 T Mc M V₁ V₂ Yp I L t)
    (hRL : IsSylowTwoOf (R153 T V₁ Yp ⊓ L) L) {n : ℕ} (hn : 1 < n) (hlin : IsLin2Type L n) :
    n = 2 := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := ctx.ctx.hyp
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ ctx.conc.1
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hLn : ¬ L ≤ M ⊓ I := ctx.conc.2.1
  have hHv : M = Subgroup.normalizer (VZ T M : Set G) := hh.hyp.isHv_of_inM' hh.hyp.inM
  obtain ⟨v₀, hv₀, hv₀L⟩ : ∃ v ∈ VZ T M, v ∉ Subgroup.centralizer (L : Set G) := by
    by_contra hall
    push Not at hall
    apply hLn
    refine le_inf ?_ hLle
    rw [hHv]
    intro l hl
    apply Subgroup.centralizer_le_normalizer
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hall v hv) l hl).symm
  obtain ⟨a₀, ha₀, c₀, hc₀, hvac⟩ := szN7_V_decomp ctx hRL hv₀
  have ha₀L : a₀ ∉ Subgroup.centralizer (L : Set G) := by
    intro h
    exact hv₀L (hvac ▸ Subgroup.mul_mem _ h hc₀.2)
  obtain ⟨F, hF, hFin, ⟨A⟩⟩ :=
    CFSG.QuasithinUnique.Lin2.exists_adapted (by omega : 0 < n) hlin hRL
  let u₀ : ↥(blockU L) := ⟨a₀, ha₀.1⟩
  have hβu₀ : A.β u₀ ≠ 1 := by
    intro h1
    have h2 : u₀ ∈ A.β.ker := h1
    rw [A.β_ker] at h2
    exact ha₀L (Subgroup.mem_subgroupOf.mp h2).2
  have hw0 : Multiplicative.toAdd (A.β u₀) ≠ 0 := fun h =>
    hβu₀ (Multiplicative.toAdd.injective (h.trans toAdd_one.symm))
  have key : ∀ s : Fˣ, s ^ 72 = 1 := by
    intro s
    obtain ⟨ℓ, hℓ⟩ := A.α_surj (szN10_diagHom s)
    have hℓN : (ℓ : G) ∈ Subgroup.normalizer ((R153 T V₁ Yp ⊓ L : Subgroup G) : Set G) := by
      rw [A.normalizer_iff ℓ, hℓ]
      exact szN10_diag_one_zero s
    have hℓM : (ℓ : G) ∈ M :=
      (szN10_normalizer_RL_le_MI ctx hRL hn hlin ⟨ℓ.2, hℓN⟩).1
    have h72 : (ℓ : G) ^ 72 ∈ Subgroup.centralizer (VZ T M : Set G) := szN10_pow72 hh hℓM
    have hℓ72L : (ℓ : G) ^ 72 ∈ L := Subgroup.pow_mem L ℓ.2 72
    have hcomm : (ℓ : G) ^ 72 * a₀ = a₀ * (ℓ : G) ^ 72 := by
      have h1 : v₀ * (ℓ : G) ^ 72 = (ℓ : G) ^ 72 * v₀ := Subgroup.mem_centralizer_iff.mp h72 v₀ hv₀
      have h2 : (ℓ : G) ^ 72 * c₀ = c₀ * (ℓ : G) ^ 72 :=
        Subgroup.mem_centralizer_iff.mp hc₀.2 _ hℓ72L
      rw [hvac] at h1
      have h3 : ((ℓ : G) ^ 72 * a₀) * c₀ = (a₀ * (ℓ : G) ^ 72) * c₀ := by
        calc ((ℓ : G) ^ 72 * a₀) * c₀ = (ℓ : G) ^ 72 * (a₀ * c₀) := by group
          _ = (a₀ * c₀) * (ℓ : G) ^ 72 := h1.symm
          _ = a₀ * (c₀ * (ℓ : G) ^ 72) := by group
          _ = a₀ * ((ℓ : G) ^ 72 * c₀) := by rw [h2]
          _ = (a₀ * (ℓ : G) ^ 72) * c₀ := by group
      exact mul_right_cancel h3
    have hconj : ((u₀ : ↥(blockU L)) : G) = (((ℓ ^ 72 : ↥L)) : G) * ((u₀ : ↥(blockU L)) : G) *
        (((ℓ ^ 72 : ↥L)) : G)⁻¹ := by
      show a₀ = (ℓ : G) ^ 72 * a₀ * ((ℓ : G) ^ 72)⁻¹
      rw [hcomm]
      group
    have hβ := A.β_equiv (ℓ ^ 72) u₀ u₀ hconj
    have hα : A.α (ℓ ^ 72) = szN10_diag (s ^ 72) := by
      rw [map_pow, hℓ]
      exact (map_pow szN10_diagHom s 72).symm
    rw [hα] at hβ
    exact szN10_diag_fix hw0 hβ.symm
  exact szN10_n_eq_two_of_pow_eq_one hn A.card_eq key

end Two

end CFSG.Quasithin
