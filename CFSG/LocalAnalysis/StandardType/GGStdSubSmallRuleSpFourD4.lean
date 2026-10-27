module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFourEnd

public section

namespace CFSG.StandardType.SpFour

open Module Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.TwoThree CFSG.Assembly TableB
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (StatedSp)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem exists_ne_one_fixing {x : StatedSp m K} {G : Subgroup (StatedSp m K)}
    (hGc : ∀ g ∈ G, ∀ h ∈ G, g * h = h * g) (hGx : ∀ g ∈ G, g * x = x * g)
    (hG3 : ∀ g ∈ G, g ^ 3 = 1) (hcard : 4 ≤ Nat.card G)
    (hW : LinearMap.ker (spEnd x - 1) ≠ ⊥) :
    ∃ g ∈ G, g ≠ 1 ∧ ∃ w ∈ LinearMap.ker (spEnd x - 1), w ≠ 0 ∧ spEnd g w = w := by
  classical
  by_contra hcon
  push Not at hcon
  haveI := SpFin.finite_statedSp_group (K := K) (m := m)
  obtain ⟨y₀, hy₀G, hy₀1⟩ : ∃ y₀ ∈ G, y₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : G = ⊥ := (Subgroup.eq_bot_iff_forall G).mpr h
    rw [this, Subgroup.card_bot] at hcard
    omega
  have hy₀3 : y₀ ^ 3 = 1 := hG3 y₀ hy₀G
  obtain ⟨z, hzG, hz⟩ : ∃ z ∈ G, z ∉ Subgroup.zpowers y₀ := by
    by_contra h
    push Not at h
    have hle : G ≤ Subgroup.zpowers y₀ := h
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime hy₀3 hy₀1] at this
    omega
  have hinv : ∀ g ∈ G, ∀ w ∈ LinearMap.ker (spEnd x - 1), spEnd g w ∈ LinearMap.ker (spEnd x - 1) :=
    fun g hg w hw => SpFin.fix_invariant (x₀ := spLin m K x) (g := spLin m K g)
      (by rw [← map_mul, ← map_mul, hGx g hg]) hw
  have hfp : ∀ u ∈ LinearMap.ker (spEnd x - 1), spEnd y₀ u = u → u = 0 := fun u hu h => by
    by_contra hu0
    exact hcon y₀ hy₀G hy₀1 u hu hu0 h
  obtain ⟨k, -, u, huW, hu0, hzu⟩ := exists_fixed_of_commute (x := spEnd y₀) (y := spEnd z)
    (spEnd_comm_iff.mp (hGc y₀ hy₀G z hzG)) (spEnd_pow hy₀3) (spEnd_pow (hG3 z hzG))
    (U := LinearMap.ker (spEnd x - 1)) (hinv y₀ hy₀G) (hinv z hzG) hfp hW
  rw [← spEnd_pow'] at hzu
  have hgG : (y₀ ^ k)⁻¹ * z ∈ G := G.mul_mem (G.inv_mem (G.pow_mem hy₀G k)) hzG
  have hg1 : (y₀ ^ k)⁻¹ * z ≠ 1 := by
    intro h
    apply hz
    have h1 : y₀ ^ k = z := inv_mul_eq_one.mp h
    rw [← h1]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y₀) k
  refine hcon _ hgG hg1 u huW hu0 ?_
  rw [spEnd_mul, Module.End.mul_apply, hzu, spEnd_inv_spEnd]

theorem spFixedDim_eq_six {x y₁ : StatedSp 4 K} (hx3 : x ^ 3 = 1) (hy₁3 : y₁ ^ 3 = 1)
    (hy₁1 : y₁ ≠ 1) (blocks₁ : SpPrimaryBlocks 2 1 3 y₁ (proj 4 K y₁))
    (hrk : finrank K (LinearMap.range (spEnd x - 1)) = 4)
    (hfixR : ∀ w ∈ LinearMap.range (spEnd x - 1), spEnd y₁ w = w) {u : Fin 4 ⊕ Fin 4 → K}
    (hu : u ∈ LinearMap.ker (spEnd x - 1)) (hu0 : u ≠ 0) (hy₁u : spEnd y₁ u = u) :
    spFixedDim y₁ = 6 := by
  have hx3' : spLin 4 K x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hy₁3' : spLin 4 K y₁ ^ 3 = 1 := by rw [← map_pow, hy₁3, map_one]
  have hy₁1' : spLin 4 K y₁ ≠ 1 := fun h => hy₁1 (spLin_injective (h.trans (map_one _).symm))
  set R := LinearMap.range (spEnd x - 1) with hR
  have hRu : R ⊓ Submodule.span K {u} = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ht.2
    rw [Submodule.mem_bot]
    by_cases hc0 : c = 0
    · rw [← hc, hc0, zero_smul]
    · exfalso
      have hu' : u ∈ R := by
        have h1 : c⁻¹ • t ∈ R := R.smul_mem _ ht.1
        rwa [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at h1
      have h2 : u ∈ LinearMap.ker (spEnd x - 1) ⊓ R := ⟨hu, hu'⟩
      rw [OddIso.ker_inf_range (p := 3) ⟨1, by norm_num⟩ (spEnd_pow hx3), Submodule.mem_bot] at h2
      exact hu0 h2
  have hsup : R ⊔ Submodule.span K {u} ≤ LinearMap.ker (spEnd y₁ - 1) := by
    refine sup_le (fun w hw => ?_) ?_
    · exact mem_ker_sub_one_iff.mpr (hfixR w hw)
    · exact (Submodule.span_singleton_le_iff_mem u _).mpr (mem_ker_sub_one_iff.mpr hy₁u)
  have h5 : finrank K ↥(R ⊔ Submodule.span K {u}) = 5 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq R (Submodule.span K {u})
    rw [hRu, finrank_bot, finrank_span_singleton hu0, hrk] at h1
    omega
  have h6 : 5 ≤ finrank K (LinearMap.ker (spEnd y₁ - 1)) := h5 ▸ Submodule.finrank_mono hsup
  have hsum : finrank K (LinearMap.ker (spEnd y₁ - 1)) +
      finrank K (LinearMap.range (spEnd y₁ - 1)) = 2 * 4 := by
    have h := Submodule.finrank_add_eq_of_isCompl (SpFin.isCompl_fix_rng hy₁3')
    rw [SpFin.finrank_spSpace 4] at h
    exact h
  have h7 : 1 ≤ finrank K (LinearMap.range (spEnd y₁ - 1)) :=
    Submodule.one_le_finrank_iff.mpr (SpFin.rng_ne_bot hy₁1')
  have hfix : finrank K (LinearMap.ker (spEnd y₁ - 1)) = spFixedDim y₁ := by
    rw [← blocks₁.fixed_eq]
    rfl
  obtain ⟨s, hs, -⟩ := blocks₁.rank
  have hs' : spFixedDim y₁ = 2 * s := hs
  omega

theorem false_of_four (hK : Nat.card K = 2) {Ã : Subgroup (StatedSp 4 K)}
    (hÃ : IsElemAbelian 3 Ã) (hcard : 3 ^ 3 ≤ Nat.card Ã)
    {T : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hT0 : T ≠ ⊥)
    (hTiso : ∀ u ∈ T, ∀ v ∈ T, spForm 4 K u v = 0) (hTÃ : ∀ a ∈ Ã, ∀ t ∈ T, spEnd a t ∈ T)
    {x : StatedSp 4 K} (hx : x ∈ Ã) (hx1 : x ≠ 1)
    (blocks : SpPrimaryBlocks 2 1 3 x (proj 4 K x)) (hd : spFixedDim x = 4)
    (hEN : EndNodeAt Ã x) (hRule : RuleAt Ã x) : False := by
  classical
  haveI := SpFin.finite_statedSp_group (K := K) (m := 4)
  have hx3 : x ^ 3 = 1 := hÃ.2 x hx
  have hx3' : spLin 4 K x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hbx : ∀ b ∈ Ã, b * x = x * b := fun b hb => TableB.IsElemAbelian.comm hÃ hb hx
  have hsum : finrank K (LinearMap.ker (spEnd x - 1)) +
      finrank K (LinearMap.range (spEnd x - 1)) = 2 * 4 := by
    have h := Submodule.finrank_add_eq_of_isCompl (SpFin.isCompl_fix_rng hx3')
    rw [SpFin.finrank_spSpace 4] at h
    exact h
  have hfix : finrank K (LinearMap.ker (spEnd x - 1)) = spFixedDim x := by
    rw [← blocks.fixed_eq]
    rfl
  have hrk : finrank K (LinearMap.range (spEnd x - 1)) = 4 := by omega
  have hDq : CFSG.IsQuasisimple ↥⁅spFixedFactor x, spFixedFactor x⁆ :=
    (spFixed_four_two hK blocks hd).1
  have hnorm : ∀ c ∈ Subgroup.centralizer ({x} : Set (StatedSp 4 K)),
      ∀ q ∈ ⁅spFixedFactor x, spFixedFactor x⁆,
        c * q * c⁻¹ ∈ ⁅spFixedFactor x, spFixedFactor x⁆ := by
    intro c hc q hq
    have hle : ⁅spFixedFactor x, spFixedFactor x⁆.map (MulAut.conj c).toMonoidHom ≤
        ⁅spFixedFactor x, spFixedFactor x⁆ := by
      rw [Subgroup.map_commutator]
      have hDc : (spFixedFactor x).map (MulAut.conj c).toMonoidHom ≤ spFixedFactor x := by
        rintro _ ⟨y, hy, rfl⟩
        exact spFixedFactor_conj hc hy
      exact Subgroup.commutator_mono hDc hDc
    exact hle ⟨q, hq, rfl⟩
  have hlay : layerC x = ⁅spFixedFactor x, spFixedFactor x⁆ :=
    SpFin.layer_eq_of_isComponentOf (SpFin.isComponentOf_of_normalized
      ((Subgroup.commutator_le_self _).trans (spFixedFactor_le_centralizer x)) hnorm hDq) hEN.1
  have hsmall : LargeEvenSmall (layerC x) := by
    obtain ⟨⟨e6⟩, -⟩ := spFixed_four_two_alt hK blocks hd
    rw [hlay]
    exact Or.inr ⟨e6⟩
  have hcent : ∀ s ∈ Ã, (∀ j ∈ ⁅spFixedFactor x, spFixedFactor x⁆, s * j = j * s) ↔
      s ∈ Subgroup.zpowers x := by
    intro s hs
    have h := hEN.2 s hs
    rw [hlay] at h
    exact h
  rcases lemI_sp hK (by norm_num) hÃ hcard hT0 hTiso hTÃ hx hx1 with ⟨b, hb, hbn, hbf⟩ | ⟨-, h9⟩
  · exact hbn ((hcent b hb).mp fun j hj => SpFin.commute_of_fix_fixedFactor hx3 blocks
      (hbx b hb) hbf (Subgroup.commutator_le_self _ hj))
  have hker0 : LinearMap.ker (spEnd x - 1) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hfix
    omega
  obtain ⟨y₁, hy₁G, hy₁1, u, hu, hu0, hy₁u⟩ := exists_ne_one_fixing
    (G := Ã ⊓ fixSub (LinearMap.range (spEnd x - 1)))
    (fun g hg h hh => TableB.IsElemAbelian.comm hÃ hg.1 hh.1)
    (fun g hg => hbx g hg.1) (fun g hg => hÃ.2 g hg.1) (by norm_num at h9 ⊢; omega) hker0
  have hy₁Ã : y₁ ∈ Ã := hy₁G.1
  have hy₁3 : y₁ ^ 3 = 1 := hÃ.2 y₁ hy₁Ã
  have blocks₁ := blocks_of_order_three hK (by norm_num) hy₁3 hy₁1
  have hd₁ := spFixedDim_eq_six hx3 hy₁3 hy₁1 blocks₁ hrk hy₁G.2 hu hu0 hy₁u
  have hEN₁ := endNodeAt_of_six hK hÃ hy₁Ã hy₁1 blocks₁ hd₁
  exact hRule ⟨y₁, hy₁Ã, hy₁1, hEN₁.1, hEN₁.2⟩ hsmall

end CFSG.StandardType.SpFour
