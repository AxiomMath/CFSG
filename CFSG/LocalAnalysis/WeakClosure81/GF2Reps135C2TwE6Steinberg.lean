module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2TwE6Monomial
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SL2Block

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

theorem tw2e6_two_pow_le_finrank_steinberg {k : Type} [Field k] [Finite k] [CharP k 2]
    [Algebra K k] {m : ℕ} {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)}
    (hρ : IsSimpleRep ρ) {y : Fin m → k} {χ : ↥(TwistedE6.fixedGroup K σ) → k}
    {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J) (hJ : twN3 ∉ J)
    (hχ : ∀ h ∈ (twistedE6CoverData hf hK σ hσ).datum.H, χ h = 1)
    {d : orbitField TwistTag.E6 K σ twN0} (hd : d ≠ 0) :
    2 ^ (2 * f - 1) ≤ Module.finrank k (LinearMap.range (ρ (hatX hf hK σ hσ twN0 d) - 1)) := by
  classical
  let F := orbitField TwistTag.E6 K σ twN0
  let n1 : TwN := ⟨1, by decide⟩
  let n2 : TwN := ⟨2, by decide⟩
  let n3 : TwN := twN3
  let l123 : List TwN := [n1, n2, n3]
  let l0123 : List TwN := [twN0, n1, n2, n3]
  let w : relWeylTwist TwistTag.E6 := (relCs TwistTag.E6).wordProd l123
  let z : Fin m → k := ρ ((twistedE6CoverData hf hK σ hσ).nhatW w) y
  let π : Representation k (SL2 F) (Fin m → k) := ρ.comp (Rhat hf hK σ hσ twN0)
  have hlen : (relCs TwistTag.E6).length
      ((relCs TwistTag.E6).simple twN0 * w) = (relCs TwistTag.E6).length w + 1 := by
    rw [relCs_length, relCs_length]
    have hfold : foldedWeylEquiv TwistTag.E6
        ((relCs TwistTag.E6).simple twN0 * w) =
        (coxeterSystem TwistTag.E6.foldedTag).simple twN0 *
          (coxeterSystem TwistTag.E6.foldedTag).wordProd l123 := by
      dsimp only [w]
      rw [map_mul, relCs_simple, foldedWeylEquiv_orbitReflection, relCs_wordProd]
    have hw : foldedWeylEquiv TwistTag.E6 w =
        (coxeterSystem TwistTag.E6.foldedTag).wordProd l123 := by
      dsimp only [w]
      rw [relCs_wordProd]
    rw [hfold, hw]
    refine (length_simple_mul_eq_add_one_iff
      (w := (coxeterSystem TwistTag.E6.foldedTag).wordProd l123) twN0).2 ?_
    rw [← CoxeterSystem.wordProd_reverse, wordProd_reverse_smul]
    dsimp only [l123, n1, n2, n3]
    decide +kernel
  have hu : ∀ c : F, π (uSL c) z = z := by
    intro c
    have hbr : ((twistedE6CoverData hf hK σ hσ).nhatW w)⁻¹ *
        hatX hf hK σ hσ twN0 c * (twistedE6CoverData hf hK σ hσ).nhatW w ∈
        (twistedE6CoverData hf hK σ hσ).datum.U :=
      (twistedE6CoverData hf hK σ hσ).datum.nW_conj w twN0 hlen
        (hatX hf hK σ hσ twN0 c)
        ((twistedE6CoverRankOne hf hK σ hσ).x_mem twN0 c)
    calc
      π (uSL c) z = ρ (hatX hf hK σ hσ twN0 c)
          (ρ ((twistedE6CoverData hf hK σ hσ).nhatW w) y) := by
        dsimp only [π, z]
        simp only [MonoidHom.comp_apply]
        rw [Rhat_uSL]
      _ = ρ (hatX hf hK σ hσ twN0 c *
            (twistedE6CoverData hf hK σ hσ).nhatW w) y := by
        rw [act_mul]
      _ = ρ ((twistedE6CoverData hf hK σ hσ).nhatW w *
            (((twistedE6CoverData hf hK σ hσ).nhatW w)⁻¹ *
              hatX hf hK σ hσ twN0 c *
                (twistedE6CoverData hf hK σ hσ).nhatW w)) y := by
        congr 1
        group
      _ = ρ ((twistedE6CoverData hf hK σ hσ).nhatW w)
            (ρ (((twistedE6CoverData hf hK σ hσ).nhatW w)⁻¹ *
              hatX hf hK σ hσ twN0 c *
                (twistedE6CoverData hf hK σ hσ).nhatW w) y) := by
        rw [← act_mul]
      _ = ρ ((twistedE6CoverData hf hK σ hσ).nhatW w) y := by
        rw [((twistedE6CoverData hf hK σ hσ).datum.mem_fixU ρ).1 ht.1 _ hbr]
      _ = z := by
        dsimp only [z]
  have hh : ∀ t : Fˣ, π (HSL t) z = z := by
    intro t
    have hH : hatH hf hK σ hσ twN0 t ∈ (twistedE6CoverData hf hK σ hσ).datum.H :=
      (twistedE6CoverRankOne hf hK σ hσ).hh_mem twN0 t
    have hbr : ((twistedE6CoverData hf hK σ hσ).nhatW w)⁻¹ *
        hatH hf hK σ hσ twN0 t * (twistedE6CoverData hf hK σ hσ).nhatW w ∈
        (twistedE6CoverData hf hK σ hσ).datum.H :=
      (twistedE6CoverData hf hK σ hσ).datum.nW_normH w hH
    calc
      π (HSL t) z = ρ (hatH hf hK σ hσ twN0 t)
          (ρ ((twistedE6CoverData hf hK σ hσ).nhatW w) y) := by
        dsimp only [π, z]
        simp only [MonoidHom.comp_apply]
        rw [Rhat_HSL]
      _ = ρ (hatH hf hK σ hσ twN0 t *
            (twistedE6CoverData hf hK σ hσ).nhatW w) y := by
        rw [act_mul]
      _ = ρ ((twistedE6CoverData hf hK σ hσ).nhatW w *
            (((twistedE6CoverData hf hK σ hσ).nhatW w)⁻¹ *
              hatH hf hK σ hσ twN0 t *
                (twistedE6CoverData hf hK σ hσ).nhatW w)) y := by
        congr 1
        group
      _ = ρ ((twistedE6CoverData hf hK σ hσ).nhatW w)
            (ρ (((twistedE6CoverData hf hK σ hσ).nhatW w)⁻¹ *
              hatH hf hK σ hσ twN0 t *
                (twistedE6CoverData hf hK σ hσ).nhatW w) y) := by
        rw [← act_mul]
      _ = ρ ((twistedE6CoverData hf hK σ hσ).nhatW w)
            (χ (((twistedE6CoverData hf hK σ hσ).nhatW w)⁻¹ *
              hatH hf hK σ hσ twN0 t *
                (twistedE6CoverData hf hK σ hσ).nhatW w) • y) := by
        rw [ht.2.2.1 _ hbr]
      _ = χ (((twistedE6CoverData hf hK σ hσ).nhatW w)⁻¹ *
            hatH hf hK σ hσ twN0 t *
              (twistedE6CoverData hf hK σ hσ).nhatW w) •
            ρ ((twistedE6CoverData hf hK σ hσ).nhatW w) y := by
        rw [map_smul]
      _ = z := by
        rw [hχ _ hbr, one_smul]
  have hv : ∀ j : Fin TwistTag.E6.foldedTag.rank,
      reflect TwistTag.E6.foldedTag j (f4Weight twN3) ≠ f4Weight twN3 → j ∉ J := by
    intro j hj hmem
    have hjeq : j = twN3 := by
      by_contra hne
      exact hj (f4Weight_fixed twN3 j hne)
    exact hJ (hjeq ▸ hmem)
  let L : List (List TwN) := [l123, l0123]
  have hL : (L.map fun w => w.foldr (reflect TwistTag.E6.foldedTag) (f4Weight twN3)).Nodup := by
    dsimp only [L, l123, l0123, n1, n2, n3]
    decide +kernel
  have hLI := tw2e6_linearIndependent_translates hf hK σ hσ hρ ht (v := f4Weight twN3) hv L hL
  let i0 : Fin L.length := ⟨0, by decide⟩
  let i1 : Fin L.length := ⟨1, by decide⟩
  have hne01 : i0 ≠ i1 := by
    dsimp only [i0, i1, L]
    decide
  have hne0 : ρ ((twistedE6CoverData hf hK σ hσ).nhatW
        ((relCs TwistTag.E6).wordProd (L.get i0))) y ≠
      ρ ((twistedE6CoverData hf hK σ hσ).nhatW
        ((relCs TwistTag.E6).wordProd (L.get i1))) y :=
    hLI.injective.ne hne01
  have hL0 : L.get i0 = l123 := by
    dsimp only [L, i0]
    change (l123 :: l0123 :: []).get (0 : Fin 2) = l123
    rw [List.get_cons_zero]
  have hL1 : L.get i1 = l0123 := by
    dsimp only [L, i1]
    change (l123 :: l0123 :: []).get (Fin.succ (0 : Fin 1)) = l0123
    rw [List.get_cons_succ', List.get_cons_zero]
  have hR : Rhat hf hK σ hσ twN0 WSL = (twistedE6CoverData hf hK σ hσ).nhat twN0 := by
    refine Subtype.ext ?_
    rw [nhat_coe]
    rfl
  have hprod : (twistedE6CoverData hf hK σ hσ).nhat twN0 *
      (twistedE6CoverData hf hK σ hσ).nhatW ((relCs TwistTag.E6).wordProd l123) =
      (twistedE6CoverData hf hK σ hσ).nhatW ((relCs TwistTag.E6).wordProd l0123) := by
    rw [show (twistedE6CoverData hf hK σ hσ).nhat twN0 =
        (twistedE6CoverData hf hK σ hσ).nhatW ((relCs TwistTag.E6).wordProd [twN0]) from by
      rw [CoxeterSystem.wordProd_singleton]
      rfl]
    rw [twNhatW_wordProd (K := K) hf hK σ hσ (l := [twN0]),
      twNhatW_wordProd (K := K) hf hK σ hσ (l := l123),
      twNhatW_wordProd (K := K) hf hK σ hσ (l := l0123)]
    dsimp only [l123, l0123, n1, n2, n3]
    simp [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  have hf0 : ρ ((twistedE6CoverData hf hK σ hσ).nhatW
        ((relCs TwistTag.E6).wordProd (L.get i0))) y = z := by
    rw [hL0]
  have hf1 : ρ ((twistedE6CoverData hf hK σ hσ).nhatW
        ((relCs TwistTag.E6).wordProd (L.get i1))) y = π WSL z := by
    rw [hL1]
    calc
      ρ ((twistedE6CoverData hf hK σ hσ).nhatW
          ((relCs TwistTag.E6).wordProd l0123)) y =
          ρ ((twistedE6CoverData hf hK σ hσ).nhat twN0 *
            (twistedE6CoverData hf hK σ hσ).nhatW
              ((relCs TwistTag.E6).wordProd l123)) y := by
        rw [hprod]
      _ = ρ ((twistedE6CoverData hf hK σ hσ).nhat twN0)
            (ρ ((twistedE6CoverData hf hK σ hσ).nhatW
              ((relCs TwistTag.E6).wordProd l123)) y) := by
        rw [← act_mul]
      _ = ρ (Rhat hf hK σ hσ twN0 WSL) z := by
        rw [hR]
      _ = π WSL z := by
        dsimp only [π]
        simp only [MonoidHom.comp_apply]
  have hW : π WSL z ≠ z := by
    intro hEq
    apply hne0
    rw [hf0, hf1, hEq]
  have hsl2 := sl2_le_finrank_range_uSL_sub_one (F := F) (k := k) (V := Fin m → k)
    π hu hh hW hd
  have hπ : π (uSL d) = ρ (hatX hf hK σ hσ twN0 d) := by
    dsimp only [π]
    simp only [MonoidHom.comp_apply]
    rw [Rhat_uSL]
  rw [hπ] at hsl2
  have hcard : Nat.card F = 2 ^ (2 * f) := by
    dsimp only [F]
    rw [card_orbitField_e6 hf hK σ hσ twN0]
    have horb : (TwistTag.E6.orbit twN0).card = 2 := by decide +kernel
    rw [horb, ← pow_mul]
    congr 1
    ring
  have hhalf : Nat.card F / 2 = 2 ^ (2 * f - 1) := by
    rw [hcard]
    have h2f : 1 ≤ 2 * f := by omega
    have hpow : 2 ^ (2 * f) = 2 ^ (2 * f - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel h2f]
    rw [hpow, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
  rw [hhalf] at hsl2
  exact hsl2

end CFSG.LocalAnalysis.WeakClosure81
