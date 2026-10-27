module

public import CFSG.RankThree.PartOne.TCX.Tri.E2A1

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KLCE
open CFSG.RankThree.Classical (conjSL)

open CFSG.RankThree.PartOne.TCX.F4 (LayerClaimsF4)

open CFSG.LocalAnalysis.ComponentInitial (sl2_closure_upper_lower)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.TCX
open scoped MatrixGroups

section Claims

variable {p f' : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem layerClaims_of_sl2 (hp5 : 5 ≤ p) (hf' : 1 ≤ f') (hK : Nat.card K = 2 ^ (p * f'))
    {σ : K ≃+* K} (hσ1 : σ ≠ 1) {G : Type} [Group G] (α : MulAut G)
    (φ : SL(2, K) →* G) (hφ : Function.Injective φ)
    (hαφ : ∀ d, α (φ d) = φ (Matrix.SpecialLinearGroup.map σ.toRingHom d)) (Q : Subgroup G)
    (hQ : φ.range = Q) : LayerClaimsF4 p α Q := by
  obtain ⟨-, hmove, -, hmodel, hfix⟩ := sl_type_claims (m := 0) hp5 hf' hK hσ1 α φ hφ hαφ Q hQ
  refine ⟨?_, hmodel, hfix⟩
  subst hQ
  have hu : Matrix.SpecialLinearGroup.map σ.toRingHom (uSL (1 : K)) = uSL 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uSL]
  have hv : Matrix.SpecialLinearGroup.map σ.toRingHom (vSL (1 : K)) = vSL 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vSL]
  rintro e ⟨d₀, rfl⟩ hin
  have hcomm : ∀ d : SL(2, K), Matrix.SpecialLinearGroup.map σ.toRingHom d = d →
      d₀ * d = d * d₀ := by
    intro d hd
    have h1 := hin (φ d) ⟨d, rfl⟩
    rw [hαφ, hd] at h1
    apply hφ
    rw [map_mul, map_mul]
    calc φ d₀ * φ d = (φ d₀ * φ d * (φ d₀)⁻¹) * φ d₀ := by group
      _ = φ d * φ d₀ := by rw [← h1]
  have hd₀ : d₀ = 1 := eq_one_of_commute_transvections d₀ (hcomm _ hu) (hcomm _ hv)
  obtain ⟨g, hgQ, hg⟩ := hmove
  apply hg
  have := hin g hgQ
  rw [hd₀, map_one] at this
  simpa using this

end Claims

section PActDef

variable (L : Type) [Field L]

@[expose] def PAct (r s : Fin TwistTag.D4.tag.rank → ℤ) : Prop :=
  ∀ A : SL(2, L), triP L * rootSL2 TwistTag.D4.tag L r A * (triP L)⁻¹ =
    rootSL2 TwistTag.D4.tag L s A

end PActDef

section PAct

variable {L : Type} [Field L] [CharP L 2]

theorem triP_conj_rootSL2_gen {r : Fin TwistTag.D4.tag.rank → ℤ} (hr : IsRoot TwistTag.D4.tag r) :
    PAct L r (permLattice TwistTag.D4.perm r) := by
  intro B
  have hρr : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm r) :=
    hr.permLattice TwistTag.D4.cartan_perm
  have hneg : permLattice TwistTag.D4.perm (-r) = -permLattice TwistTag.D4.perm r := by
    funext i
    simp [permLattice]
  let f : SL(2, L) →* ModGL TwistTag.D4.tag L :=
    (MulAut.conj (triP L)).toMonoidHom.comp (rootSL2 TwistTag.D4.tag L r)
  have hfg : f = rootSL2 TwistTag.D4.tag L (permLattice TwistTag.D4.perm r) := by
    refine MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := L)) ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change triP L * rootSL2 TwistTag.D4.tag L r (uSL c) * (triP L)⁻¹ =
        rootSL2 TwistTag.D4.tag L (permLattice TwistTag.D4.perm r) (uSL c)
      rw [rootSL2_uSL_of_charTwo hr, rootSL2_uSL_of_charTwo hρr, triP_conj_pinnedX hr]
    · change triP L * rootSL2 TwistTag.D4.tag L r (vSL c) * (triP L)⁻¹ =
        rootSL2 TwistTag.D4.tag L (permLattice TwistTag.D4.perm r) (vSL c)
      rw [rootSL2_vSL_of_charTwo hr, rootSL2_vSL_of_charTwo hρr,
        triP_conj_pinnedX (IsRoot.neg hr), hneg]
  exact DFunLike.congr_fun hfg B

omit [CharP L 2] in
theorem PAct.pow_mod_one {p : ℕ} (hp : p % 3 = 1) {r t : Fin TwistTag.D4.tag.rank → ℤ}
    (h : PAct L r t) (A : SL(2, L)) :
    triP L ^ p * rootSL2 TwistTag.D4.tag L r A * (triP L ^ p)⁻¹ =
      rootSL2 TwistTag.D4.tag L t A := by
  rw [triP_pow_prime, hp, pow_one]
  exact h A

omit [CharP L 2] in
theorem PAct.pow_mod_two {p : ℕ} (hp : p % 3 = 2) {r s t : Fin TwistTag.D4.tag.rank → ℤ}
    (h₁ : PAct L r s) (h₂ : PAct L s t) (A : SL(2, L)) :
    triP L ^ p * rootSL2 TwistTag.D4.tag L r A * (triP L ^ p)⁻¹ =
      rootSL2 TwistTag.D4.tag L t A := by
  rw [triP_pow_prime, hp, pow_two]
  have e : triP L * triP L * rootSL2 TwistTag.D4.tag L r A * (triP L * triP L)⁻¹ =
      triP L * (triP L * rootSL2 TwistTag.D4.tag L r A * (triP L)⁻¹) * (triP L)⁻¹ := by group
  rw [e, h₁ A, h₂ A]

end PAct

section Lang

variable {L : Type} [Field L] [CharP L 2]

omit [CharP L 2] in
theorem map_toGL_wsl (σ : L →+* L) :
    Matrix.GeneralLinearGroup.map σ (Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L))) =
      Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) := by
  have h2 : Matrix.GeneralLinearGroup.map σ (Matrix.SpecialLinearGroup.toGL
      (WSL : SL(2, L))) = Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map σ (WSL : SL(2, L))) := by
    ext i j
    rfl
  rw [h2, map_wsl]

theorem toGL_wsl_mul_self :
    Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) *
      Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) = 1 := by
  rw [← map_mul, wsl_mul_self, map_one]

theorem toGL_wsl_pow_odd {k : ℕ} (hk : Odd k) :
    Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) ^ k =
      Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul, pow_two, toGL_wsl_mul_self, one_pow, one_mul]

variable [IsAlgClosed L]

omit [CharP L 2] [IsAlgClosed L] in
theorem a3_lang_data {Fr : L →+* L} (hFr : Function.Bijective Fr)
    (M₁ M₂ M₃ : GL (Fin 2) L) {k : Type} [Field k] [Finite k] [Algebra k L]
    (hk4 : 4 ≤ Nat.card k) {Fr₃ : L →+* L} (hFr₃ : ∀ c, Fr₃ c = c ^ Nat.card k)
    (hFr3eq : Fr.comp (Fr.comp Fr) = Fr₃) (Pm : GL (Fin 2) L)
    (hPm : Pm * Matrix.GeneralLinearGroup.map Fr₃ Pm⁻¹ =
      M₃ * Matrix.GeneralLinearGroup.map Fr (M₂ * Matrix.GeneralLinearGroup.map Fr M₁))
    (S₃ : Subgroup SL(2, L))
    (hS : S₃ = (Matrix.SpecialLinearGroup.map (algebraMap k L)).range.map (conjSL Pm)) :
    Finite S₃ ∧ (∀ B : SL(2, L), B ∈ S₃ ↔ twHom Fr M₃ (twHom Fr M₂ (twHom Fr M₁ B)) = B) ∧
      CFSG.IsQuasisimple S₃ ∧ CFSG.IsQuasisimple (S₃.map (twHom Fr M₁)) ∧
      CFSG.IsQuasisimple ((S₃.map (twHom Fr M₁)).map (twHom Fr M₂)) ∧
      Subgroup.centralizer ((S₃.map Matrix.SpecialLinearGroup.toGL :
        Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
          (Matrix.GeneralLinearGroup.scalar (Fin 2)).range ∧
      Subgroup.centralizer (((S₃.map (twHom Fr M₁)).map Matrix.SpecialLinearGroup.toGL :
        Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
          (Matrix.GeneralLinearGroup.scalar (Fin 2)).range ∧
      Subgroup.centralizer ((((S₃.map (twHom Fr M₁)).map (twHom Fr M₂)).map
        Matrix.SpecialLinearGroup.toGL : Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
          (Matrix.GeneralLinearGroup.scalar (Fin 2)).range := by
  classical
  subst hS
  obtain ⟨hfin₃, hq₃⟩ := sl2_conj_range_quasisimple (K := k) (L := L) hk4 Pm
  have hz₃ := sl2_conj_range_centralizer (K := k) (L := L) Pm
  have hq₂ := isQuasisimple_map_twHom (Fr := Fr) M₁ hq₃
  have hq₁ := isQuasisimple_map_twHom (Fr := Fr) M₂ hq₂
  have hz₂ := centralizer_map_twHom hFr M₁ hz₃
  have hz₁ := centralizer_map_twHom hFr M₂ hz₂
  refine ⟨hfin₃, fun B => ?_, hq₃, hq₂, hq₁, hz₃, hz₂, hz₁⟩
  rw [twHom_comp_three, hFr3eq, ← hPm]
  exact (sl2_twistedFixed_iff Fr₃ (frobenius_fixed_iff Fr₃ hFr₃) Pm B).symm

end Lang

section Iterate

variable {L : Type} [Field L]

theorem twHom_iterate [CharP L 2] {f₀ : ℕ} {J : GL (Fin 2) L}
    (hJ : Matrix.GeneralLinearGroup.map (iterateFrobenius L 2 f₀) J = J) (k : ℕ)
    (Z : SL(2, L)) :
    (⇑(twHom (iterateFrobenius L 2 f₀) J))^[k] Z =
      conjSL (J ^ k) (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 (f₀ * k)) Z) := by
  induction k generalizing Z with
  | zero =>
    rw [Function.iterate_zero, id_eq, pow_zero, Nat.mul_zero, iterateFrobenius_zero,
      CFSG.RankThree.Classical.conjSL_one]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, twHom_apply, map_conjSL_ringHom', map_map_sl2,
      ← CFSG.RankThree.Classical.conjSL_mul, show f₀ * (k + 1) = f₀ + f₀ * k by ring,
      iterateFrobenius_add, map_pow, hJ, pow_succ' J k]

end Iterate

end CFSG.RankThree.PartOne.TCX.Tri
