module

public import CFSG.Quasithin.Background.C124L2MP

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.L2P

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.LieType.BorelTits
  CFSG.Quasithin.C126.A5 CFSG.Quasithin.C124.L2
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_of_perfect_of_prod {Y N K' : Subgroup G} (hY : ⁅Y, Y⁆ = Y) (hK : K' ≤ Y)
    (hM : ⁅N, Y⁆ ≤ K') (hprod : ∀ y ∈ Y, ∃ n ∈ N, ∃ k ∈ K', y = n * k) : Y ≤ K' := by
  have hconj : ∀ n ∈ N, ∀ g ∈ K', n * g * n⁻¹ ∈ K' := by
    intro n hn g hg
    have h1 : ⁅n, g⁆ ∈ K' := hM (Subgroup.commutator_mem_commutator hn (hK hg))
    have h2 : n * g * n⁻¹ = ⁅n, g⁆ * g := by simp only [commutatorElement_def]; group
    rw [h2]
    exact K'.mul_mem h1 hg
  have hcomm : ∀ k ∈ K', ∀ n ∈ N, ⁅k, n⁆ ∈ K' := by
    intro k hk n hn
    rw [← commutatorElement_inv]
    exact K'.inv_mem (hM (Subgroup.commutator_mem_commutator hn (hK hk)))
  rw [← hY]
  refine Subgroup.commutator_le.2 fun y hy y' hy' => ?_
  obtain ⟨n, hn, k, hk, rfl⟩ := hprod y hy
  obtain ⟨n', hn', k', hk', rfl⟩ := hprod y' hy'
  have hkk : ⁅k, n' * k'⁆ ∈ K' := by
    have h1 : ⁅k, n' * k'⁆ = ⁅k, n'⁆ * (n' * ⁅k, k'⁆ * n'⁻¹) := by
      simp only [commutatorElement_def]; group
    have hkk' : ⁅k, k'⁆ ∈ K' := by
      simp only [commutatorElement_def]
      exact K'.mul_mem (K'.mul_mem (K'.mul_mem hk hk') (K'.inv_mem hk)) (K'.inv_mem hk')
    rw [h1]
    exact K'.mul_mem (hcomm k hk n' hn') (hconj n' hn' _ hkk')
  have hnk : ⁅n * k, n' * k'⁆ ∈ K' := by
    have h1 : ⁅n * k, n' * k'⁆ = n * ⁅k, n' * k'⁆ * n⁻¹ * ⁅n, n' * k'⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact K'.mul_mem (hconj n hn _ hkk) (hM (Subgroup.commutator_mem_commutator hn hy'))
  exact hnk

section Dickson

variable {Y V : Subgroup G} {F : Type} [Field F] [Finite F]

theorem minParabolic_of_sl2_perf {Y T V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hYN : Y ≤ Subgroup.normalizer (V : Set G)) (hTN : T ≤ Subgroup.normalizer (V : Set G))
    (hT2 : IsPGroup 2 T) (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hsyl : IsSylowTwoOf (T ⊓ Y) Y) (hperf : ⁅Y, Y⁆ = Y)
    (hC : ⁅Y ⊓ Subgroup.centralizer (V : Set G), Y⁆ ≤ T)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) (e : ↥(autI hV Y) ≃* SL(2, F))
    (hnorm : ¬ Y ≤ Subgroup.normalizer (T : Set G)) :
    ∃ M : Subgroup G, MinParabolic (Y ⊔ T) T M := by
  classical
  have hF4 : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  have hsylP : IsSylowTwoOf T (Y ⊔ T) := isSylowTwoOf_sup_of_normalizing hTY hT2 hsyl
  have hDs : IsSylowTwoOf (autI hV (T ⊓ Y)) (autI hV Y) := B2F.isSylowTwoOf_autI hV hYN hsyl
  have hTT : T ≤ Subgroup.normalizer ((T ⊓ Y : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTY ht⟩
  have hTn : autI hV T ≤ Subgroup.normalizer (autI hV (T ⊓ Y) : Set (MulAut (IntMod V hV))) :=
    autI_le_normalizer_of_le_normalizer hV hTT
  set B : Subgroup (MulAut (IntMod V hV)) :=
    Subgroup.normalizer (autI hV (T ⊓ Y) : Set (MulAut (IntMod V hV))) with hB
  set M₀ : Subgroup G := preI hV Y hYN B with hM₀
  have hM₀Y : M₀ ≤ Y := preI_le hV
  have hTYM₀ : T ⊓ Y ≤ M₀ := fun d hd =>
    (mem_preI hV).2 ⟨hd.2, Subgroup.le_normalizer (convI_mem_autI hV hd (hYN hd.2))⟩
  have hTM₀ : T ≤ Subgroup.normalizer (M₀ : Set G) := by
    have key : ∀ t ∈ T, ∀ y ∈ M₀, t * y * t⁻¹ ∈ M₀ := by
      intro t ht y hy
      obtain ⟨hyY, hyB⟩ := (mem_preI hV).1 hy
      have hty : t * y * t⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 (hTY ht) y).1 hyY
      refine (mem_preI hV).2 ⟨hty, ?_⟩
      have htB : convI hV ⟨t, hTN ht⟩ ∈ B := hTn (convI_mem_autI hV ht (hTN ht))
      have h1 : convHom hV Y hYN ⟨t * y * t⁻¹, hty⟩ =
          convI hV ⟨t, hTN ht⟩ * convHom hV Y hYN ⟨y, hyY⟩ * (convI hV ⟨t, hTN ht⟩)⁻¹ := by
        rw [convHom_apply, convHom_apply, ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [h1]
      exact B.mul_mem (B.mul_mem htB hyB) (B.inv_mem htB)
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key t ht y, fun hy => ?_⟩
    have := key t⁻¹ (T.inv_mem ht) _ hy
    simpa [mul_assoc] using this
  set M : Subgroup G := M₀ ⊔ T with hM
  have hTM : T ≤ M := le_sup_right
  have hMP : M ≤ Y ⊔ T := sup_le (hM₀Y.trans le_sup_left) le_sup_right
  have hmul : ((M₀ ⊔ T : Subgroup G) : Set G) = (M₀ : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left M₀ T hTM₀
  have hmax : ∀ K : Subgroup G, T ≤ K → K < Y ⊔ T → K ≤ M := by
    intro K hTK hKP
    have hdec : ∀ k ∈ K, ∃ y ∈ K ⊓ Y, ∃ t ∈ T, k = y * t := by
      intro k hk
      have hk' : k ∈ ((Y ⊔ T : Subgroup G) : Set G) := hKP.le hk
      rw [Subgroup.coe_mul_of_right_le_normalizer_left Y T hTY] at hk'
      obtain ⟨y, hy, t, ht, rfl⟩ := hk'
      refine ⟨y, ⟨?_, hy⟩, t, ht, rfl⟩
      have := K.mul_mem hk (K.inv_mem (hTK ht))
      simpa using this
    have hKYle : autI hV (K ⊓ Y) ≤ autI hV Y := autI_mono hV inf_le_right
    have hDK : autI hV (T ⊓ Y) ≤ autI hV (K ⊓ Y) := autI_mono hV (inf_le_inf_right Y hTK)
    rcases C126.Nat.sylow_dichotomy_of_equiv_sl2 (n := 2) (by norm_num) hF4 e hDs hKYle hDK
      with h | h
    · exfalso
      have hprod : ∀ y ∈ Y, ∃ n ∈ Y ⊓ Subgroup.centralizer (V : Set G), ∃ k ∈ K ⊓ Y,
          y = n * k := by
        intro y hy
        have hmem : convI hV ⟨y, hYN hy⟩ ∈ autI hV (K ⊓ Y) := by
          rw [h]
          exact convI_mem_autI hV hy (hYN hy)
        obtain ⟨k, hkK, hk⟩ := (mem_autI hV).1 hmem
        have h1 : convI hV (⟨y, hYN hy⟩ * k⁻¹) = 1 := by
          rw [map_mul, map_inv, ← hk, mul_inv_cancel]
        have h2 : y * (k : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
          (convI_eq_one_iff hV _).1 h1
        exact ⟨y * (k : G)⁻¹, ⟨Y.mul_mem hy (Y.inv_mem hkK.2), h2⟩, k, hkK, by group⟩
      have hM : ⁅Y ⊓ Subgroup.centralizer (V : Set G), Y⁆ ≤ K ⊓ Y :=
        le_inf (hC.trans hTK) ((Subgroup.commutator_mono inf_le_left le_rfl).trans hperf.le)
      have hYK : Y ≤ K :=
        (le_of_perfect_of_prod hperf inf_le_right hM hprod).trans inf_le_left
      exact absurd hKP (not_lt_of_ge (sup_le hYK hTK))
    · intro k hk
      obtain ⟨y, hy, t, ht, rfl⟩ := hdec k hk
      have hyM₀ : y ∈ M₀ := (mem_preI hV).2 ⟨hy.2, h (convI_mem_autI hV hy (hYN hy.2))⟩
      exact Subgroup.mul_mem_sup hyM₀ ht
  have hMP' : M < Y ⊔ T := by
    refine lt_of_le_of_ne hMP fun hEq => ?_
    have hYM : Y ≤ M := by
      rw [hEq]
      exact le_sup_left
    have hYM₀ : Y ≤ M₀ := by
      intro y hy
      have hy' : y ∈ ((M₀ ⊔ T : Subgroup G) : Set G) := hYM hy
      rw [hmul] at hy'
      obtain ⟨m, hm, t, ht, rfl⟩ := hy'
      have htY : t ∈ T ⊓ Y := ⟨ht, by simpa using Y.mul_mem (Y.inv_mem (hM₀Y hm)) hy⟩
      exact M₀.mul_mem hm (hTYM₀ htY)
    apply not_le_normalizer_sylow hV hF e hDs
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    exact ((mem_preI hV).1 (hYM₀ hg)).2
  have hTn' : ¬ Y ⊔ T ≤ Subgroup.normalizer (T : Set G) := fun h => hnorm (le_sup_left.trans h)
  exact ⟨M, CFSG.QuasithinUnique.Setup.minParabolic_of_uniqueMax hsylP hTn' hTM hMP' hmax⟩

end Dickson

end CFSG.Quasithin.C124.L2P
