module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndDvdBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndDvdComb
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndNode

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.CALinearPlane CFSG.ComponentClassification CFSG.Assembly

variable {d p : ℕ} {K : Type} [Field K]

section Act

variable {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}

theorem transvection_eq_of_map_eq (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) {k l : Fin d}
    (hkl : k ≠ l) {c c' : K}
    (h : φ (SpecialLinearGroup.transvection hkl c) = φ (SpecialLinearGroup.transvection hkl c')) :
    c = c' := by
  have h1 : SpecialLinearGroup.transvection hkl (c' - c) =
      (SpecialLinearGroup.transvection hkl c)⁻¹ * SpecialLinearGroup.transvection hkl c' := by
    rw [eq_inv_mul_iff_mul_eq, ← Matrix.SpecialLinearGroup.transvection_add, add_sub_cancel]
  have h2 : φ (SpecialLinearGroup.transvection hkl (c' - c)) = 1 := by
    rw [h1, map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨e, -, he⟩ := mem_scalars.mp (hφker _ h2)
  have h3 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M k l) he
  simp [CFSG.LinearGroups.coe_transvection, hkl] at h3
  rw [sub_eq_zero] at h3
  exact h3.symm

theorem ratio_eq_of_act (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) {D D' : GL (Fin d) K}
    {t t' : Fin d → K} (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (hD' : (D' : Matrix (Fin d) (Fin d) K) = diagonal t')
    (h : ∀ s, φ (CatalogueBHigherLinearAction.slConjugation d K D s) =
      φ (CatalogueBHigherLinearAction.slConjugation d K D' s)) {k l : Fin d} (hkl : k ≠ l) :
    t k * (t l)⁻¹ = t' k * (t' l)⁻¹ := by
  have h1 := h (SpecialLinearGroup.transvection hkl 1)
  rw [slConjugation_transvection_of_diagonal hD, slConjugation_transvection_of_diagonal hD',
    mul_one, mul_one] at h1
  exact transvection_eq_of_map_eq hφker hkl h1

theorem diag_ne_zero {D : GL (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) (k : Fin d) : t k ≠ 0 := by
  intro hk
  have h1 := D.isUnit.map (Matrix.detMonoidHom (n := Fin d) (R := K))
  rw [Matrix.coe_detMonoidHom, hD, det_diagonal, Finset.prod_eq_zero (Finset.mem_univ k) hk] at h1
  exact not_isUnit_zero h1

theorem act_of_lift_GL (hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤)
    {ψ : L' →* projectiveSL d K} (hker : ψ.ker ≤ Subgroup.center L')
    (hφ : ∀ g, ψ (φ g) = proj d K g) {a : MulAut L'} {B : GL (Fin d) K}
    (hind : ∀ l, conjAut d K B (ψ l) = ψ (a l)) :
    ∀ s, a (φ s) = φ (CatalogueBHigherLinearAction.slConjugation d K B s) :=
  act_of_lift_of_mulAut hperfSL hker hφ
    (ψA := conjAut d K B) (γ := CatalogueBHigherLinearAction.slConjugation d K B)
    (fun s => conjAut_proj B s) hind

theorem act_mul {a b : MulAut L'} {D E : GL (Fin d) K}
    (ha : ∀ s, a (φ s) = φ (CatalogueBHigherLinearAction.slConjugation d K D s))
    (hb : ∀ s, b (φ s) = φ (CatalogueBHigherLinearAction.slConjugation d K E s)) :
    ∀ s, (a * b) (φ s) = φ (CatalogueBHigherLinearAction.slConjugation d K (D * E) s) := by
  intro s
  rw [MulAut.mul_apply, hb, ha, map_mul, MulAut.mul_apply]

theorem act_pow {a : MulAut L'} {D : GL (Fin d) K}
    (ha : ∀ s, a (φ s) = φ (CatalogueBHigherLinearAction.slConjugation d K D s)) (n : ℕ) :
    ∀ s, (a ^ n) (φ s) = φ (CatalogueBHigherLinearAction.slConjugation d K (D ^ n) s) := by
  induction n with
  | zero => intro s; simp
  | succ n ih =>
    intro s
    rw [pow_succ, pow_succ]
    exact act_mul ih ha s

end Act

theorem slConjugation_eq_self_of_const {D : GL (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) {c : K} (hc : ∀ k, t k = c) (hc0 : c ≠ 0)
    (s : SpecialLinearGroup (Fin d) K) :
    CatalogueBHigherLinearAction.slConjugation d K D s = s := by
  have hDs : D = Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc0) := by
    apply Units.ext
    rw [hD, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply]
    congr 1
    funext k
    exact hc k
  rw [hDs, CatalogueBHigherLinearAction.slConjugation_scalar, MulAut.one_apply]

theorem ggEndNode_of_torality [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hd : 5 ≤ d) (h4 : 4 ≤ Nat.card K) (hsec : SLHasSections d K)
    (htor : GGPGLTorality p d K) :
    GGEndNode p (d - 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3
  have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  obtain ⟨φ, hφs, hφ⟩ := exists_sl_cover hsec ψ hψ hker hperf
  set X := inducedSub ψ A with hX
  have hXA : IsElemAbelian p X := isElemAbelian_inducedSub hψ hA
  have hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hcardX : Nat.card X = Nat.card A := card_inducedSub hψ hker hperf (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  obtain ⟨A₀, hA₀⟩ := htor X hXA hXI (hcardX ▸ hr) (hcardX ▸ h3)
  set c₀ := CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹ with hc₀
  set φ' := φ.comp c₀.toMonoidHom with hφ'
  have hφ's : Function.Surjective φ' := hφs.comp c₀.surjective
  have hφ'ker : ∀ g, φ' g = 1 → g ∈ scalars d K := by
    intro g hg
    have h1 : proj d K (c₀ g) = 1 := by
      rw [← hφ]
      change ψ (φ' g) = 1
      rw [hg, map_one]
    exact mem_scalars_of_slConjugation_mem A₀⁻¹ (proj_eq_one_iff.mp h1)
  have hmodel : ∀ a ∈ A, ∃ D : GL (Fin d) K,
      (∃ t : Fin d → K, (D : Matrix (Fin d) (Fin d) K) = diagonal t) ∧
      ∀ s, a (φ' s) = φ' (CatalogueBHigherLinearAction.slConjugation d K D s) := by
    intro a ha
    obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a ha
    have hBX : conjAut d K B ∈ X := ⟨a, ha, hφa⟩
    set D := A₀ * B * A₀⁻¹ with hD
    refine ⟨D, ⟨fun i => (D : Matrix (Fin d) (Fin d) K) i i,
      CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag fun i j hij => by
        rw [hD, Units.val_mul, Units.val_mul]
        exact hA₀ B hBX i j hij⟩, fun s => ?_⟩
    have h1 := act_of_lift_GL hperfSL hker hφ hφa (c₀ s)
    change a (φ (c₀ s)) = φ (c₀ (CatalogueBHigherLinearAction.slConjugation d K D s))
    rw [h1, hc₀, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, hD]
    congr 2
    group
  choose Dr hDr using fun a : A => hmodel a a.2
  choose tr htr using fun a : A => (hDr a).1
  have hact : ∀ (a : A) s, (a : MulAut L') (φ' s) =
      φ' (CatalogueBHigherLinearAction.slConjugation d K (Dr a) s) := fun a => (hDr a).2
  have htr0 : ∀ a k, tr a k ≠ 0 := fun a k => diag_ne_zero (htr a) k
  set k₀ : Fin d := ⟨3, by omega⟩ with hk₀
  have hrat : ∀ {D D' : GL (Fin d) K} {t t' : Fin d → K},
      (D : Matrix (Fin d) (Fin d) K) = diagonal t →
      (D' : Matrix (Fin d) (Fin d) K) = diagonal t' →
      (∀ s, φ' (CatalogueBHigherLinearAction.slConjugation d K D s) =
        φ' (CatalogueBHigherLinearAction.slConjugation d K D' s)) →
      ∀ k, t k * (t k₀)⁻¹ = t' k * (t' k₀)⁻¹ := by
    intro D D' t t' hD hD' h k
    by_cases hk : k = k₀
    · rw [hk, mul_inv_cancel₀ (diag_ne_zero hD k₀), mul_inv_cancel₀ (diag_ne_zero hD' k₀)]
    · exact ratio_eq_of_act hφ'ker hD hD' h hk
  let ν : A →* (Fin d → Kˣ) :=
    { toFun := fun a k => Units.mk0 (tr a k * (tr a k₀)⁻¹)
        (mul_ne_zero (htr0 a k) (inv_ne_zero (htr0 a k₀)))
      map_one' := by
        funext k
        apply Units.ext
        have h1 := hrat (htr 1) (show ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          diagonal (fun _ => (1 : K)) by rw [Units.val_one, diagonal_one])
          (fun s => by rw [← hact 1 s, map_one]; rfl) k
        rw [Units.val_mk0, h1, inv_one, mul_one]
        rfl
      map_mul' := fun a b => by
        funext k
        apply Units.ext
        have hab : ((Dr a * Dr b : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
            diagonal (fun i => tr a i * tr b i) := by
          rw [Units.val_mul, htr a, htr b, diagonal_mul_diagonal]
        have h1 := hrat (htr (a * b)) hab (fun s => by
          rw [← hact (a * b) s, Subgroup.coe_mul]
          exact act_mul (hact a) (hact b) s) k
        simp only [Pi.mul_apply, Units.val_mul, Units.val_mk0]
        rw [h1]
        field_simp }
  have hν : ∀ a k, ((ν a k : Kˣ) : K) = tr a k * (tr a k₀)⁻¹ := fun _ _ => rfl
  have hνinj : Function.Injective ν := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hc : ∀ k, tr a k = tr a k₀ := fun k => by
      have h1 := congrArg (fun f : Fin d → Kˣ => ((f k : Kˣ) : K)) ha
      simp only [hν, Pi.one_apply, Units.val_one] at h1
      exact (mul_inv_eq_one₀ (htr0 a k₀)).mp h1
    apply Subtype.ext
    ext l
    obtain ⟨s, rfl⟩ := hφ's l
    rw [hact a s, slConjugation_eq_self_of_const (htr a) hc (htr0 a k₀)]
    rfl
  set Y := ν.range with hY
  have hYcard : Nat.card Y = Nat.card A := Nat.card_range_of_injective hνinj
  have hY0 : ∀ y ∈ Y, y ⟨3, by omega⟩ = 1 := by
    rintro _ ⟨a, rfl⟩
    apply Units.ext
    rw [hν, mul_inv_cancel₀ (htr0 a k₀)]
    rfl
  have hYp : ∀ y ∈ Y, ∀ k, y k ∈ rootsOfUnity p K := by
    rintro _ ⟨a, rfl⟩ k
    rw [mem_rootsOfUnity]
    apply Units.ext
    have hDp : (((Dr a) ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal (fun i => tr a i ^ p) := by
      rw [Units.val_pow_eq_pow_val, htr a, diagonal_pow]
      rfl
    have hap : (a : MulAut L') ^ p = 1 := hA.2 _ a.2
    have h1 := hrat hDp (show ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (fun _ => (1 : K)) by rw [Units.val_one, diagonal_one]) (fun s => by
        rw [← act_pow (hact a) p s, hap, map_one]
        rfl) k
    rw [Units.val_pow_eq_pow_val, hν, mul_pow, inv_pow, h1, inv_one, mul_one, Units.val_one]
  obtain ⟨y, ⟨a₁, rfl⟩, hy1, T, hTne, hT2, hyT, hyc, hyz⟩ :=
    exists_node hp hp2 hpK hd hY0 hYp (hYcard ▸ hr)
  have htT : ∀ i ∈ T, ∀ j, j ≠ i → tr a₁ j ≠ tr a₁ i := by
    intro i hi j hj h
    apply hyT i hi j hj
    apply Units.ext
    rw [hν, hν, h]
  have htc : ∀ k l, k ∉ T → l ∉ T → tr a₁ k = tr a₁ l := by
    intro k l hk hl
    have h1 := congrArg (fun u : Kˣ => (u : K)) (hyc k l hk hl)
    simp only [hν] at h1
    exact mul_right_cancel₀ (inv_ne_zero (htr0 a₁ k₀)) h1
  have hTc : T.card < Tᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hS : 2 ≤ Tᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨i₀, hi₀⟩ := hTne
  obtain ⟨hL, hJcomp⟩ :=
    layer_ggFix_eq_of_set h4 hφ'ker hφ's (htr a₁) htT htc hTc hi₀ hS (hact a₁)
  refine ⟨a₁, a₁.2, ?_, hL ▸ hJcomp, ?_⟩
  · intro h1
    apply hy1
    have : a₁ = 1 := Subtype.ext h1
    rw [this, map_one]
  · intro a' ha'
    rw [hL]
    constructor
    · intro hfix
      set b : A := ⟨a', ha'⟩ with hb
      have hconst : ∀ k l, k ∉ T → l ∉ T → ν b k = ν b l := by
        intro k l hk hl
        by_cases hkl : k = l
        · rw [hkl]
        · have hmem : SpecialLinearGroup.transvection hkl (1 : K) ∈ coordBlockSL K Tᶜ := by
            rw [mem_coordBlockSL_iff]
            intro a c hac
            simp only [Finset.mem_compl, not_not] at hac
            rw [CFSG.LinearGroups.coe_transvection]
            rcases hac with ha | hc
            · have hak : a ≠ k := fun h => hk (h ▸ ha)
              simp [Matrix.one_apply, Ne.symm hak]
            · have hcl : c ≠ l := fun h => hl (h ▸ hc)
              simp [Matrix.one_apply, Ne.symm hcl]
          have h1 : a' (φ' (SpecialLinearGroup.transvection hkl 1)) =
              φ' (SpecialLinearGroup.transvection hkl 1) := hfix _ ⟨_, hmem, rfl⟩
          have h1' : (b : MulAut L') (φ' (SpecialLinearGroup.transvection hkl 1)) =
              φ' (SpecialLinearGroup.transvection hkl 1) := h1
          rw [hact b, slConjugation_transvection_of_diagonal (htr b) hkl, mul_one] at h1'
          have h2 := transvection_eq_of_map_eq hφ'ker hkl h1'
          apply Units.ext
          rw [hν, hν, (mul_inv_eq_one₀ (htr0 b l)).mp h2]
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hyz (ν b) ⟨b, rfl⟩ hconst)
      have h3 : a₁ ^ m = b := hνinj (by rw [map_zpow, hm])
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨m, by rw [← Subgroup.coe_zpow, h3]⟩
    · intro hmem j hj
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hj1 : (a₁ : MulAut L') j = j := hJcomp.1 hj
      have hstab : (a₁ : MulAut L') ∈ MulAction.stabilizer (MulAut L') j :=
        MulAction.mem_stabilizer_iff.mpr (by rw [MulAut.smul_def]; exact hj1)
      have h1 := MulAction.mem_stabilizer_iff.mp
        ((Subgroup.zpowers_le.mpr hstab) (Subgroup.zpow_mem_zpowers _ m))
      rwa [MulAut.smul_def] at h1

end CFSG.StandardType.TypeA
