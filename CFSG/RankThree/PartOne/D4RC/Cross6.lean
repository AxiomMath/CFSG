module

public import CFSG.RankThree.PartOne.D4RC.Gram6U
public import CFSG.RankThree.PartOne.D4RC.CW6
import CFSG.RankThree.PartOne.KLCE.A2Model
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
import CFSG.RankThree.PartOne.KD4T.Certs
import CFSG.RankThree.PartOne.KE.StabGeneral
import CFSG.RankThree.PartOne.KLCE.Descent

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ7
  CFSG.SeitzReduction CFSG.Timmesfeld.ARS
open CFSG.RankThree.Classical2 (fixSubgroup unitarySet)

open MvPolynomial
open scoped Matrix MatrixGroups Pointwise

open scoped CFSG.ConvolutionPoints

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Fields

variable {L : Type} [Field L] [CharP L 2]

theorem rcx_mem_range_of_pow {k : Type} [Field k] (ι : k →+* L) {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card k = q) (hfix : ∀ a : k, ι a ^ q = ι a) {c : L} (hc : c ^ q = c) :
    ∃ a : k, ι a = c := by
  classical
  obtain ⟨hfin, hle⟩ := rcd_fixed_set_finite (L := L) hq
  have hsub : Set.range ι ⊆ {c : L | c ^ q = c} := by
    rintro _ ⟨a, rfl⟩
    exact hfix a
  have hcardr : (Set.range ι).ncard = q := by
    rw [Set.ncard_range_of_injective ι.injective, hcard]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcardr]; exact hle) hfin
  have hc' : c ∈ {c : L | c ^ q = c} := hc
  rw [← heq] at hc'
  exact hc'

theorem rcx_exists_omega [IsAlgClosed L] {f : ℕ} (hf : 1 ≤ f) :
    ∃ ω : L, ω ^ (2 ^ f) ^ 2 = ω ∧ ω ^ 2 ^ f ≠ ω := by
  classical
  obtain ⟨K₂, _, _, _, ι, hcard, hι⟩ :=
    CFSG.RankThree.PartOne.KLCE.exists_subfield_card (L := L) (n := 2 * f) (by omega)
  have hexp : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by rw [← pow_mul, mul_comm]
  by_contra h
  push Not at h
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  obtain ⟨hfin, hle⟩ := rcd_fixed_set_finite (L := L) hq
  have hsub : Set.range ι ⊆ {c : L | c ^ 2 ^ f = c} := by
    rintro _ ⟨a, rfl⟩
    exact h _ (by rw [hexp]; exact (hι _).2 ⟨a, rfl⟩)
  have h1 := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_range_of_injective ι.injective, hcard, ← hexp] at h1
  have h2 := h1.trans hle
  nlinarith

end Fields

section Cross

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]

variable {F : RclFrame 2 f K σ (-1) p L} {x : 𝒞[K, σ]} {i : Fin 4}

theorem rcx_map_conjSub (e : 𝒞[K, σ] ≃* twistedGroup σ.toRingHom) (g : 𝒞[K, σ]) :
    (conjSub ((Xh σ.toRingHom).map e.symm.toMonoidHom) g).map e.toMonoidHom =
      conjSub (Xh σ.toRingHom) (e g) := by
  simp only [Timmesfeld.ARS.conjSub, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun y => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem rcx_exists_not_opposite (hσ3 : ∀ c, σ (σ (σ c)) = c)
    [IsSimpleGroup (twistedGroup σ.toRingHom)]
    (e : 𝒞[K, σ] ≃* twistedGroup σ.toRingHom)
    (hcompat : ∀ k, (((e k : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL d4 K) =
      ((k : 𝒞[K, σ]) : ModGL d4 K))
    (sp : RclSpecial F x i) (D : RclAlgData F i) (z : 𝒞[K, σ]) :
    ∃ y ∈ rclPx sp, ¬ Opposite ((rcaA0 sp D).map e.toMonoidHom)
      ((conjSub (rcaA0 sp D) (z * y)).map e.toMonoidHom) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hf := F.hf
  have hq1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  obtain ⟨g, hA0, κ, -, hcol⟩ := rgt_exists_conj hσ3 e hcompat sp D
  obtain ⟨Cf, hC⟩ := rgu_entry rfl sp D hcol z
  have hcardF : Nat.card (fixSubfield σ) = 2 ^ f :=
    card_fixSubfield_cube Nat.prime_two F.hf F.hK σ F.hσ
  have : Finite (fixSubfield σ) := Nat.finite_of_card_ne_zero (by rw [hcardF]; positivity)
  have : Fintype (fixSubfield σ) := Fintype.ofFinite _
  have hfixF : ∀ a : fixSubfield σ,
      algebraMap (fixSubfield σ) L a ^ 2 ^ f = algebraMap (fixSubfield σ) L a := fun a => by
    have h1 : σ (a : K) = (a : K) := (mem_fixSubfield σ).1 a.2
    rw [F.hσ] at h1
    change algebraMap K L (a : K) ^ 2 ^ f = algebraMap K L (a : K)
    rw [← map_pow, h1]
  have hrange : ∀ c : L, c ^ 2 ^ f = c → ∃ a : fixSubfield σ, algebraMap (fixSubfield σ) L a = c :=
    fun c hc => rcx_mem_range_of_pow (algebraMap (fixSubfield σ) L) hq1 hcardF hfixF hc
  obtain ⟨ω, hω2, hω1⟩ := rcx_exists_omega (L := L) hf
  have hfrob : ∀ a b : L, (a + b) ^ 2 ^ f = a ^ 2 ^ f + b ^ 2 ^ f := fun a b =>
    add_pow_char_pow a b 2 f
  have hωq : (ω ^ 2 ^ f) ^ 2 ^ f = ω := by rw [← pow_mul, ← sq, hω2]
  obtain ⟨t, ht⟩ := hrange (ω + ω ^ 2 ^ f) (by rw [hfrob, hωq, add_comm])
  obtain ⟨nn, hnn⟩ := hrange (ω ^ 2 ^ f * ω) (by rw [mul_pow, hωq, mul_comm])
  let iL : Fin 3 → Fin 6 := fun a => ⟨a, by omega⟩
  let iR : Fin 3 → Fin 6 := fun a => ⟨a + 3, by omega⟩
  set aF := algebraMap (fixSubfield σ) L with haF
  let wv : (Fin 6 → fixSubfield σ) → Fin 3 → L := fun x a => aF (x (iL a)) + ω * aF (x (iR a))
  let W : Fin 3 → MvPolynomial (Fin 6) L := fun a => X (iL a) + C ω * X (iR a)
  let W' : Fin 3 → MvPolynomial (Fin 6) L := fun a => X (iL a) + C (ω ^ 2 ^ f) * X (iR a)
  let P : MvPolynomial (Fin 6) L := ∑ a, ∑ b, C (Cf a b) * (W a * W' b)
  let N : MvPolynomial (Fin 6) (fixSubfield σ) :=
    ∑ a, (X (iL a) ^ 2 + C t * (X (iL a) * X (iR a)) + C nn * X (iR a) ^ 2)
  have hevP : ∀ x, eval (aF ∘ x) P = ∑ a, ∑ b, Cf a b * (wv x a * wv x b ^ 2 ^ f) := by
    intro x
    simp only [P, W, W', wv, map_sum, map_mul, eval_C, map_add, eval_X, Function.comp_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hfrob, mul_pow, hfixF]
  have hevN : ∀ x, aF (eval x N) = ∑ a, wv x a ^ 2 ^ f * wv x a := by
    intro x
    simp only [N, wv, map_sum, map_add, map_mul, map_pow, eval_C, eval_X]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hfrob, mul_pow, hfixF, ht, hnn]
    ring
  have hWh : ∀ a, (W a).IsHomogeneous 1 := fun a =>
    (isHomogeneous_X _ _).add (isHomogeneous_C_mul_X _ _)
  have hWh' : ∀ a, (W' a).IsHomogeneous 1 := fun a =>
    (isHomogeneous_X _ _).add (isHomogeneous_C_mul_X _ _)
  have hPh : P.IsHomogeneous 2 :=
    IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ =>
      ((hWh a).mul (hWh' b)).C_mul _
  have hNh : N.IsHomogeneous 2 :=
    IsHomogeneous.sum _ _ _ fun a _ =>
      (((isHomogeneous_X_pow _ 2).add (((isHomogeneous_X _ _).mul
        (isHomogeneous_X _ _)).C_mul _)).add ((isHomogeneous_X_pow _ 2).C_mul _))
  have hN0 : eval 0 N = 0 := by simp [N]
  have hP0 : eval 0 P = 0 := by simp [P, W, W']
  have hwv0 : ∀ x : Fin 6 → fixSubfield σ, wv x = 0 → x = 0 := by
    intro x hx
    have hR : ∀ a, x (iR a) = 0 := by
      intro a
      by_contra hne
      have h := congrFun hx a
      simp only [wv, Pi.zero_apply] at h
      have hne' : aF (x (iR a)) ≠ 0 := (map_ne_zero aF).2 hne
      have hω : ω = aF (-(x (iL a)) / x (iR a)) := by
        rw [map_div₀, map_neg]
        field_simp
        linear_combination h
      apply hω1
      rw [hω]
      exact hfixF _
    have hL : ∀ a, x (iL a) = 0 := by
      intro a
      have h := congrFun hx a
      simp only [wv, Pi.zero_apply, hR a, map_zero, mul_zero, add_zero] at h
      exact (map_eq_zero aF).1 h
    funext j
    fin_cases j
    · exact hL 0
    · exact hL 1
    · exact hL 2
    · exact hR 0
    · exact hR 1
    · exact hR 2
  have hk2 : ∀ (x : Fin 6 → fixSubfield σ) a, wv x a ^ (2 ^ f) ^ 2 = wv x a := by
    intro x a
    have hsq : ∀ c : L, c ^ (2 ^ f) ^ 2 = (c ^ 2 ^ f) ^ 2 ^ f := fun c => by rw [sq, pow_mul]
    simp only [wv]
    rw [hsq]
    simp only [hfrob, mul_pow, hfixF, hωq]
  have hentry : ∀ x : Fin 6 → fixSubfield σ, eval x N = 0 → wv x ≠ 0 →
      ∃ X : ↥(fixSubgroup D.Φ'),
        algebraMap K L (rgEntry (((g⁻¹ * z * (rcaTheta sp D X : 𝒞[K, σ]) * g : 𝒞[K, σ]) :
          ModGL d4 K) : Module.End K (RootModule d4 K))) = eval (aF ∘ x) P := by
    intro x hx hx0
    have hiso : ∑ a, wv x a ^ 2 ^ f * wv x a = 0 := by rw [← hevN, hx, map_zero]
    obtain ⟨Y, hY, hYu⟩ := rgu_exists_unitary hf hx0 (hk2 x) hiso
    obtain ⟨X, hX⟩ := hC Y hY
    refine ⟨X, ?_⟩
    rw [← rgt_entry_triEmb, hX, hevP, hYu]
  have hfixed : ∀ k : 𝒞[K, σ], rgEntry ((k : ModGL d4 K) : Module.End K (RootModule d4 K)) ∈
      fixSubfield σ := fun k => by
    have h := rg_entry_fixed (σ := σ.toRingHom)
      (twistedGroup_le_twistFixed σ.toRingHom (e k).2)
    rw [hcompat] at h
    exact (mem_fixSubfield σ).2 h
  have hrat : ∀ x : Fin 6 → fixSubfield σ, eval x N = 0 →
      ∃ a : fixSubfield σ, eval (aF ∘ x) P = aF a := by
    intro x hx
    by_cases hx0 : wv x = 0
    · refine ⟨0, ?_⟩
      rw [hevP, hx0, map_zero]
      simp only [Pi.zero_apply, zero_pow (pow_ne_zero f two_ne_zero), mul_zero,
        Finset.sum_const_zero]
    · obtain ⟨X, hX⟩ := hentry x hx hx0
      exact ⟨⟨_, hfixed _⟩, hX.symm⟩
  obtain ⟨x0, hx00, hNx, hPx⟩ :=
    rcw_exists_zero hNh.totalDegree_le hPh.totalDegree_le hN0 hP0 hrat
  have hwv : wv x0 ≠ 0 := fun h => hx00 (hwv0 x0 h)
  obtain ⟨X, hX⟩ := hentry x0 hNx hwv
  rw [hPx, map_eq_zero] at hX
  refine ⟨(rcaTheta sp D X : 𝒞[K, σ]), (rcaTheta sp D X).2, fun hop => ?_⟩
  rw [hA0, rcx_map_conjSub, ← Timmesfeld.ARS.conjSub_mul, rcx_map_conjSub] at hop
  have hσ' : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := hσ3
  have h0 := rg_opposite_entry_ne_zero hσ' hop
  apply h0
  rw [← map_inv, ← map_mul, hcompat]
  rw [show (g⁻¹ * (z * (rcaTheta sp D X : 𝒞[K, σ]) * g) : 𝒞[K, σ]) =
    g⁻¹ * z * (rcaTheta sp D X : 𝒞[K, σ]) * g by group]
  exact hX

end Cross

end CFSG.RankThree.PartOne.D4RC
