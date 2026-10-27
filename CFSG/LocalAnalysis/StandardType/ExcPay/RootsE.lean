module

public import CFSG.LocalAnalysis.StandardType.ExcPay.Defs
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F Matrix
  CFSG.LieType.Steinberg.Adjoint

private lemma excPayR_symmetrizedCartan_eq_cartan {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : τ.symmetrizedCartan = τ.cartan := by
  rcases hτ with rfl | rfl | rfl <;>
    simp [Tag.symmetrizedCartan, Tag.symmetrizer]

private lemma excPayR_posDef_cartan {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef := by
  rcases hτ with rfl | rfl | rfl
  · change ((Tag.cartanE 6).map (Int.cast : ℤ → ℚ)).PosDef
    rw [cartanE_eq]
    exact TauCeti.posDef_map_intCast_cartanMatrix_E6
  · change ((Tag.cartanE 7).map (Int.cast : ℤ → ℚ)).PosDef
    rw [cartanE_eq]
    exact TauCeti.posDef_map_intCast_cartanMatrix_E7
  · change ((Tag.cartanE 8).map (Int.cast : ℤ → ℚ)).PosDef
    rw [cartanE_eq]
    exact TauCeti.posDef_map_intCast_cartanMatrix_E8

private def excPayR_form (τ : Tag) (x y : Fin τ.rank → ℤ) : ℤ :=
  ∑ i, x i * ∑ j, τ.cartan i j * y j

private lemma excPayR_form_comm {τ : Tag}
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) (x y : Fin τ.rank → ℤ) :
    excPayR_form τ x y = excPayR_form τ y x := by
  have hsymm : ∀ i j, τ.cartan i j = τ.cartan j i := by
    intro i j
    have h := congrFun (congrFun hpd.isHermitian i) j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial] at h
    exact_mod_cast h.symm
  simp only [excPayR_form, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsymm j i]
  ring_nf

private lemma excPayR_form_add_left (τ : Tag) (x x' y : Fin τ.rank → ℤ) :
    excPayR_form τ (x + x') y = excPayR_form τ x y + excPayR_form τ x' y := by
  simp only [excPayR_form, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma excPayR_form_sub_left (τ : Tag) (x x' y : Fin τ.rank → ℤ) :
    excPayR_form τ (x - x') y = excPayR_form τ x y - excPayR_form τ x' y := by
  simp only [excPayR_form, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma excPayR_form_smul_left (τ : Tag) (a : ℤ) (x y : Fin τ.rank → ℤ) :
    excPayR_form τ (a • x) y = a * excPayR_form τ x y := by
  simp only [excPayR_form, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring_nf

private lemma excPayR_form_add_right (τ : Tag) (x y y' : Fin τ.rank → ℤ) :
    excPayR_form τ x (y + y') = excPayR_form τ x y + excPayR_form τ x y' := by
  simp only [excPayR_form, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma excPayR_form_sub_right (τ : Tag) (x y y' : Fin τ.rank → ℤ) :
    excPayR_form τ x (y - y') = excPayR_form τ x y - excPayR_form τ x y' := by
  simp only [excPayR_form, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma excPayR_form_smul_right {τ : Tag}
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) (a : ℤ) (x y : Fin τ.rank → ℤ) :
    excPayR_form τ x (a • y) = a * excPayR_form τ x y := by
  rw [excPayR_form_comm hpd, excPayR_form_smul_left, excPayR_form_comm hpd]

private lemma excPayR_form_single_left (τ : Tag) (i : Fin τ.rank) (y : Fin τ.rank → ℤ) :
    excPayR_form τ (Pi.single i 1) y = ∑ j, τ.cartan i j * y j := by
  simp only [excPayR_form, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

private lemma excPayR_form_single_right {τ : Tag}
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) (x : Fin τ.rank → ℤ)
    (i : Fin τ.rank) :
    excPayR_form τ x (Pi.single i 1) = ∑ j, τ.cartan i j * x j := by
  rw [excPayR_form_comm hpd, excPayR_form_single_left]

private lemma excPayR_form_single_single (τ : Tag) (i : Fin τ.rank) :
    excPayR_form τ (Pi.single i 1) (Pi.single i 1) = 2 := by
  rw [excPayR_form_single_left, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_one, Tag.cartan_self]
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

private lemma excPayR_form_reflect {τ : Tag}
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (i : Fin τ.rank) (x y : Fin τ.rank → ℤ) :
    excPayR_form τ (reflect τ i x) (reflect τ i y) = excPayR_form τ x y := by
  set a : ℤ := ∑ j, τ.cartan i j * x j with ha
  set b : ℤ := ∑ j, τ.cartan i j * y j with hb
  have hx : reflect τ i x = x - a • Pi.single i 1 := by rw [reflect, ← ha]
  have hy : reflect τ i y = y - b • Pi.single i 1 := by rw [reflect, ← hb]
  rw [hx, hy]
  calc
    excPayR_form τ (x - a • Pi.single i 1) (y - b • Pi.single i 1)
        = excPayR_form τ x (y - b • Pi.single i 1) -
            a * excPayR_form τ (Pi.single i 1) (y - b • Pi.single i 1) := by
          rw [excPayR_form_sub_left, excPayR_form_smul_left]
    _ = (excPayR_form τ x y - b * excPayR_form τ x (Pi.single i 1)) -
          a * (excPayR_form τ (Pi.single i 1) y -
            b * excPayR_form τ (Pi.single i 1) (Pi.single i 1)) := by
          rw [excPayR_form_sub_right, excPayR_form_smul_right hpd, excPayR_form_sub_right,
            excPayR_form_smul_right hpd]
    _ = (excPayR_form τ x y - b * a) - a * (b - b * 2) := by
          rw [excPayR_form_single_right hpd, excPayR_form_single_left,
            excPayR_form_single_single, ← ha, ← hb]
    _ = excPayR_form τ x y := by ring

private lemma excPayR_form_self_root {τ : Tag}
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : excPayR_form τ γ γ = 2 := by
  induction hγ with
  | basis j => exact excPayR_form_single_single τ j
  | reflect i _ ih => rw [excPayR_form_reflect hpd, ih]

private lemma excPayR_form_pos {τ : Tag}
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {x : Fin τ.rank → ℤ}
    (hx : x ≠ 0) : 0 < excPayR_form τ x x := by
  have hx' : (fun k => (x k : ℚ)) ≠ 0 := fun h =>
    hx (funext fun k => by have := congrFun h k; simpa using this)
  have h := hpd.dotProduct_mulVec_pos hx'
  have e : star (fun k => (x k : ℚ)) ⬝ᵥ Matrix.mulVec (τ.cartan.map (Int.cast : ℤ → ℚ))
      (fun k => (x k : ℚ)) = ((excPayR_form τ x x : ℤ) : ℚ) := by
    simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.map_apply, excPayR_form,
      Int.cast_sum, Int.cast_mul]
  rw [e] at h
  exact_mod_cast h

private lemma excPayR_form_sub_self {τ : Tag}
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) (x y : Fin τ.rank → ℤ) :
    excPayR_form τ (x - y) (x - y) =
      excPayR_form τ x x - 2 * excPayR_form τ x y + excPayR_form τ y y := by
  rw [excPayR_form_sub_left, excPayR_form_sub_right, excPayR_form_sub_right,
    excPayR_form_comm hpd y x]
  ring

private lemma excPayR_form_add_self {τ : Tag}
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) (x y : Fin τ.rank → ℤ) :
    excPayR_form τ (x + y) (x + y) =
      excPayR_form τ x x + 2 * excPayR_form τ x y + excPayR_form τ y y := by
  rw [excPayR_form_add_left, excPayR_form_add_right, excPayR_form_add_right,
    excPayR_form_comm hpd y x]
  ring

private lemma excPayR_rootChar_mulSingle {τ : Tag} {K : Type} [Field K]
    (j : Fin τ.rank) (ζ : Kˣ) (v : Fin τ.rank → ℤ) :
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar (Pi.mulSingle j ζ) v =
      ζ ^ v j := by
  rw [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar, Finset.prod_eq_single j]
  · simp
  · intro i _ hi
    rw [Pi.mulSingle_eq_of_ne hi, _root_.one_zpow]
  · intro h
    exact absurd (Finset.mem_univ j) h

private lemma excPayR_exists_abs_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℤ) :
    ∃ c : ℤ, (p : ℤ) ∣ n - c ∧ 2 * |c| ≤ (p : ℤ) - 1 := by
  have hp_pos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  set r : ℤ := n % (p : ℤ) with hr
  have hr_nonneg : 0 ≤ r := Int.emod_nonneg n (ne_of_gt hp_pos)
  have hr_lt : r < (p : ℤ) := Int.emod_lt_of_pos n hp_pos
  have hdvd : (p : ℤ) ∣ n - r := by
    have h := Int.emod_add_mul_ediv n (p : ℤ)
    exact ⟨n / (p : ℤ), by linarith⟩
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  rcases hp_odd with ⟨m, hm⟩
  have hp_eq : (p : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast hm
  by_cases hle : 2 * r ≤ (p : ℤ) - 1
  · exact ⟨r, by simpa using hdvd, by rw [abs_of_nonneg hr_nonneg]; linarith⟩
  · have hgt : (p : ℤ) - 1 < 2 * r := by linarith
    refine ⟨r - (p : ℤ), ?_, ?_⟩
    · convert dvd_add hdvd (dvd_refl (p : ℤ)) using 1
      ring
    · have hrp : r - (p : ℤ) < 0 := by linarith
      rw [abs_of_neg hrp]
      have hne : 2 * r ≠ (p : ℤ) := by
        intro h
        rw [hp_eq] at h
        omega
      have h2r : (p : ℤ) + 1 ≤ 2 * r := by omega
      linarith

private lemma excPayR_dvd_of_rootChar_eq_one {τ : Tag} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (k : Fin τ.rank) {α : Fin τ.rank → ℤ}
    (hker : ∀ a ∈ (Set.range fun a : rootKerFam τ p k => a.1),
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a α = 1) :
    ∀ j, j ≠ k → (p : ℤ) ∣ α j := by
  classical
  have hpG : (p : GGL) ≠ 0 := fun h => by
    have h2 := (CharP.cast_eq_zero_iff GGL 2 p).1 h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2
    omega
  haveI : NeZero (p : GGL) := ⟨hpG⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot GGL p
  lift ζ₀ to GGLˣ using hζ₀.isUnit hp.ne_zero
  rw [IsPrimitiveRoot.coe_units_iff] at hζ₀
  have hζp : ζ₀ ^ p = 1 := hζ₀.pow_eq_one
  intro j hjk
  have hζprim : IsPrimitiveRoot ζ₀ p := hζ₀
  let a : Fin τ.rank → GGLˣ := Pi.mulSingle j ζ₀
  have ha_mem : a ∈ (Set.range fun a : rootKerFam τ p k => a.1) := by
    refine ⟨⟨a, ?_, ?_⟩, rfl⟩
    · intro i
      by_cases hi : i = j
      · subst hi
        simpa [a] using hζp
      · simp [a, Pi.mulSingle_eq_of_ne hi]
    · exact Pi.mulSingle_eq_of_ne (M := fun _ => GGLˣ) (i := j) (i' := k) hjk.symm ζ₀
  have h1 := hker a ha_mem
  have h2 : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a α =
      ζ₀ ^ α j := excPayR_rootChar_mulSingle j ζ₀ α
  rw [h2] at h1
  exact (IsPrimitiveRoot.zpow_eq_one_iff_dvd hζprim (α j)).mp h1

private lemma excPayR_eq_pm_single_of_eq_smul {τ : Tag}
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) (k : Fin τ.rank)
    {α : Fin τ.rank → ℤ} (hroot : IsRoot τ α) {c : ℤ}
    (hc : α = c • (Pi.single k 1 : Fin τ.rank → ℤ)) :
    α = Pi.single k 1 ∨ α = -Pi.single k 1 := by
  have hBα : excPayR_form τ α α = 2 := excPayR_form_self_root hpd hroot
  rw [hc] at hBα
  rw [excPayR_form_smul_left, excPayR_form_smul_right hpd,
    excPayR_form_single_single] at hBα
  have hfac : (c - 1) * (c + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · left
    rw [hc]
    have : c = 1 := by omega
    rw [this]
    simp
  · right
    rw [hc]
    have : c = -1 := by omega
    rw [this]
    simp

private lemma excPayR_abs_form_single_le {τ : Tag}
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) (k : Fin τ.rank)
    {α : Fin τ.rank → ℤ} (hroot : IsRoot τ α)
    (hprop : ∀ c : ℤ, α ≠ c • (Pi.single k 1 : Fin τ.rank → ℤ)) :
    |excPayR_form τ α (Pi.single k 1)| ≤ 1 := by
  have hs_upper : excPayR_form τ α (Pi.single k 1) ≤ 1 := by
    have hone : 0 < excPayR_form τ (α - Pi.single k 1) (α - Pi.single k 1) := by
      apply excPayR_form_pos hpd
      intro h0
      exact hprop 1 (by simpa using sub_eq_zero.mp h0)
    rw [excPayR_form_sub_self hpd, excPayR_form_self_root hpd hroot,
      excPayR_form_single_single] at hone
    linarith
  have hs_lower : -1 ≤ excPayR_form τ α (Pi.single k 1) := by
    have hone : 0 < excPayR_form τ (α + Pi.single k 1) (α + Pi.single k 1) := by
      apply excPayR_form_pos hpd
      intro h0
      exact hprop (-1) (by simpa using add_eq_zero_iff_eq_neg.mp h0)
    rw [excPayR_form_add_self hpd, excPayR_form_self_root hpd hroot,
      excPayR_form_single_single] at hone
    linarith
  exact abs_le.mpr ⟨hs_lower, hs_upper⟩

private lemma excPayR_exists_beta {τ : Tag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (k : Fin τ.rank) {α : Fin τ.rank → ℤ}
    (hdvdj : ∀ j, j ≠ k → (p : ℤ) ∣ α j) :
    ∃ (c : ℤ) (β : Fin τ.rank → ℤ), 2 * |c| ≤ (p : ℤ) - 1 ∧
      β = α - c • (Pi.single k 1 : Fin τ.rank → ℤ) ∧
      (∀ j, (p : ℤ) ∣ β j) := by
  obtain ⟨c, hc_dvd, hc_bound⟩ := excPayR_exists_abs_le hp hp2 (α k)
  refine ⟨c, α - c • (Pi.single k 1 : Fin τ.rank → ℤ), hc_bound, rfl, ?_⟩
  intro j
  by_cases hj : j = k
  · subst j
    have hβk : (α - c • (Pi.single k 1 : Fin τ.rank → ℤ)) k = α k - c := by
      simp
    rw [hβk]
    exact hc_dvd
  · have hβj : (α - c • (Pi.single k 1 : Fin τ.rank → ℤ)) j = α j := by
      simp [Pi.single_eq_of_ne hj]
    rw [hβj]
    exact hdvdj j hj

private lemma excPayR_form_beta_eq {τ : Tag}
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) (k : Fin τ.rank)
    {α β : Fin τ.rank → ℤ} (hroot : IsRoot τ α) {c : ℤ}
    (hβ : β = α - c • (Pi.single k 1 : Fin τ.rank → ℤ)) :
    excPayR_form τ β β =
      2 - 2 * c * excPayR_form τ α (Pi.single k 1) + 2 * c ^ 2 := by
  rw [hβ, excPayR_form_sub_self hpd, excPayR_form_smul_right hpd,
    excPayR_form_smul_left, excPayR_form_smul_right hpd,
    excPayR_form_single_single, excPayR_form_self_root hpd hroot]
  ring

private lemma excPayR_form_beta_le {τ : Tag}
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) (k : Fin τ.rank)
    {α β : Fin τ.rank → ℤ} (hroot : IsRoot τ α) {c : ℤ}
    (hc_abs : |excPayR_form τ α (Pi.single k 1)| ≤ 1)
    (hβ : β = α - c • (Pi.single k 1 : Fin τ.rank → ℤ)) :
    excPayR_form τ β β ≤ 2 + 2 * |c| + 2 * c ^ 2 := by
  rw [excPayR_form_beta_eq hpd k hroot hβ]
  have hcs : -(c * excPayR_form τ α (Pi.single k 1)) ≤ |c| := by
    have h1 : -(c * excPayR_form τ α (Pi.single k 1)) ≤
        |c * excPayR_form τ α (Pi.single k 1)| := neg_le_abs _
    rw [abs_mul] at h1
    nlinarith [abs_nonneg c]
  nlinarith

private lemma excPayR_form_beta_lt {τ : Tag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β : Fin τ.rank → ℤ} {c : ℤ} (hc_bound : 2 * |c| ≤ (p : ℤ) - 1)
    (hBβ_ub : excPayR_form τ β β ≤ 2 + 2 * |c| + 2 * c ^ 2) :
    excPayR_form τ β β < (p : ℤ) ^ 2 := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hp3z : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  have hbound : 2 + 2 * |c| + 2 * c ^ 2 < (p : ℤ) ^ 2 := by
    have hsq_abs : c ^ 2 = |c| ^ 2 := by rw [sq_abs]
    have h1 : 0 ≤ (p : ℤ) - 1 - 2 * |c| := by linarith
    have h2 : 0 ≤ (p : ℤ) - 1 + 2 * |c| := by linarith [abs_nonneg c]
    have hprod : 0 ≤ ((p : ℤ) - 1 - 2 * |c|) * ((p : ℤ) - 1 + 2 * |c|) :=
      mul_nonneg h1 h2
    nlinarith [hprod, hsq_abs, hp3z]
  linarith

private lemma excPayR_false_of_not_smul {τ : Tag}
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {k : Fin τ.rank} {α : Fin τ.rank → ℤ} (hroot : IsRoot τ α)
    (hprop : ∀ c : ℤ, α ≠ c • (Pi.single k 1 : Fin τ.rank → ℤ))
    (hdvdj : ∀ j, j ≠ k → (p : ℤ) ∣ α j) : False := by
  obtain ⟨c, β, hc_bound, hβ, hβdvd⟩ := excPayR_exists_beta hp hp2 k hdvdj
  choose γ hγ using hβdvd
  have hβeq : β = (p : ℤ) • γ := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
    exact hγ j
  have hc_abs : |excPayR_form τ α (Pi.single k 1)| ≤ 1 :=
    excPayR_abs_form_single_le hpd k hroot hprop
  have hBβ_ub : excPayR_form τ β β ≤ 2 + 2 * |c| + 2 * c ^ 2 :=
    excPayR_form_beta_le hpd k hroot hc_abs hβ
  have hBβ_lt : excPayR_form τ β β < (p : ℤ) ^ 2 :=
    excPayR_form_beta_lt hp hp2 hc_bound hBβ_ub
  by_cases hβ0 : β = 0
  · have hαc : α = c • (Pi.single k 1 : Fin τ.rank → ℤ) := by
      rw [hβ] at hβ0
      simpa using sub_eq_zero.mp hβ0
    exact hprop c hαc
  · have hγ0 : γ ≠ 0 := by
      intro h0
      apply hβ0
      rw [hβeq, h0, smul_zero]
    have hBγ_pos : 0 < excPayR_form τ γ γ := excPayR_form_pos hpd hγ0
    have hBγ_ge : 1 ≤ excPayR_form τ γ γ := by omega
    have hβge : (p : ℤ) ^ 2 ≤ excPayR_form τ β β := by
      rw [hβeq, excPayR_form_smul_left, excPayR_form_smul_right hpd]
      nlinarith
    linarith

private lemma excPayR_famKernel_subset {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (k : Fin τ.rank) {α : Fin τ.rank → ℤ}
    (hα : α ∈ famKernel (τ := τ) (L := GGL)
      (Set.range fun a : rootKerFam τ p k => a.1)) :
    α = Pi.single k 1 ∨ α = -Pi.single k 1 := by
  classical
  have hroot : IsRoot τ α := hα.1
  have hker : ∀ a ∈ (Set.range fun a : rootKerFam τ p k => a.1),
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a α = 1 := hα.2
  have hpd := excPayR_posDef_cartan hτ
  have hdvdj : ∀ j, j ≠ k → (p : ℤ) ∣ α j :=
    excPayR_dvd_of_rootChar_eq_one hp hp2 k hker
  by_cases hprop : ∃ c0 : ℤ, α = c0 • (Pi.single k 1 : Fin τ.rank → ℤ)
  · obtain ⟨c0, hc0⟩ := hprop
    exact excPayR_eq_pm_single_of_eq_smul hpd k hroot hc0
  · push Not at hprop
    exact (excPayR_false_of_not_smul hpd hp hp2 hroot hprop hdvdj).elim

private lemma excPayR_famKernel_supset {τ : Tag} {p : ℕ} (k : Fin τ.rank)
    {α : Fin τ.rank → ℤ} (hα : α = Pi.single k 1 ∨ α = -Pi.single k 1) :
    α ∈ famKernel (τ := τ) (L := GGL)
      (Set.range fun a : rootKerFam τ p k => a.1) := by
  rcases hα with rfl | rfl
  · refine ⟨IsRoot.basis k, ?_⟩
    intro a ha
    rcases ha with ⟨x, rfl⟩
    have hk : x.1 k = 1 := x.2.2
    have h := rootChar_nsmul_single x.1 k 1
    simp only [one_smul, pow_one, hk] at h
    exact h
  · refine ⟨IsRoot.neg (IsRoot.basis k), ?_⟩
    intro a ha
    rcases ha with ⟨x, rfl⟩
    have hk : x.1 k = 1 := x.2.2
    have hpos := rootChar_nsmul_single x.1 k 1
    simp only [one_smul, pow_one, hk] at hpos
    have h := rootChar_sub x.1 0 (Pi.single k 1)
    rw [zero_sub, rootChar_zero, one_mul, hpos, inv_one] at h
    exact h

theorem famKernel_rootKerFam {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (k : Fin τ.rank) :
    famKernel (τ := τ) (L := GGL) (Set.range fun a : rootKerFam τ p k => a.1) =
      {Pi.single k 1, -Pi.single k 1} := by
  ext α
  constructor
  · intro hα
    have h := excPayR_famKernel_subset hτ hp hp2 k hα
    rwa [Set.mem_insert_iff, Set.mem_singleton_iff]
  · intro hα
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
    exact excPayR_famKernel_supset k hα

private def excPayR_coxeter : (τ : Tag) → CoxeterMatrix (Fin τ.rank)
  | .E6 => CoxeterMatrix.E₆
  | .E7 => CoxeterMatrix.E₇
  | .E8 => CoxeterMatrix.E₈
  | .G2 => CoxeterMatrix.A 2
  | .F4 => CoxeterMatrix.A 4
  | .D4 => CoxeterMatrix.A 4

private lemma excPayR_cartan_eq_neg_one_of_coxeter {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∀ i j : Fin τ.rank, excPayR_coxeter τ i j = 3 → τ.cartan i j = -1 := by
  rcases hτ with rfl | rfl | rfl
  · change ∀ i j : Fin 6, CoxeterMatrix.E₆ i j = 3 → Tag.cartanE 6 i j = -1
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.E₆, Tag.cartanE] at h ⊢
  · change ∀ i j : Fin 7, CoxeterMatrix.E₇ i j = 3 → Tag.cartanE 7 i j = -1
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.E₇, Tag.cartanE] at h ⊢
  · change ∀ i j : Fin 8, CoxeterMatrix.E₈ i j = 3 → Tag.cartanE 8 i j = -1
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.E₈, Tag.cartanE] at h ⊢

private lemma excPayR_cartan_eq_zero_of_coxeter {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∀ i j : Fin τ.rank, i ≠ j → excPayR_coxeter τ i j = 2 → τ.cartan i j = 0 := by
  rcases hτ with rfl | rfl | rfl
  · change ∀ i j : Fin 6, i ≠ j → CoxeterMatrix.E₆ i j = 2 → Tag.cartanE 6 i j = 0
    intro i j hij h
    fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.E₆, Tag.cartanE] at h hij ⊢
  · change ∀ i j : Fin 7, i ≠ j → CoxeterMatrix.E₇ i j = 2 → Tag.cartanE 7 i j = 0
    intro i j hij h
    fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.E₇, Tag.cartanE] at h hij ⊢
  · change ∀ i j : Fin 8, i ≠ j → CoxeterMatrix.E₈ i j = 2 → Tag.cartanE 8 i j = 0
    intro i j hij h
    fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.E₈, Tag.cartanE] at h hij ⊢

private lemma excPayR_iform_eq_form {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (x y : Fin τ.rank → ℤ) : @iform τ x y = excPayR_form τ x y := by
  rcases hτ with rfl | rfl | rfl <;>
    · simp only [iform, excPayR_form, Tag.symmetrizedCartan, Tag.symmetrizer, Matrix.one_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring

private lemma excPayR_iform_single_self {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (i : Fin τ.rank) : @iform τ (Pi.single i 1) (Pi.single i 1) = 2 := by
  rw [excPayR_iform_eq_form hτ, excPayR_form_single_single]

private lemma excPayR_iform_single_pair {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (i j : Fin τ.rank) : @iform τ (Pi.single i 1) (Pi.single j 1) = τ.cartan i j := by
  rw [excPayR_iform_eq_form hτ, excPayR_form_single_left τ i (Pi.single j 1)]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl
    simp [hl]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem excPayR_isA2Pair_simple {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {i j : Fin τ.rank} (h : excPayR_coxeter τ i j = 3) :
    CFSG.HardMathSupport.Timmesfeld.CrossChar.IsA2Pair (τ := τ)
      (Pi.single i 1) (Pi.single j 1) := by
  have hcart : τ.cartan i j = -1 := excPayR_cartan_eq_neg_one_of_coxeter hτ i j h
  have hroot_add : IsRoot τ (Pi.single i 1 + Pi.single j 1) := by
    have h1 : IsRoot τ (reflect τ i (Pi.single j 1)) :=
      IsRoot.reflect (τ := τ) i (IsRoot.basis (τ := τ) j)
    have h2 : reflect τ i (Pi.single j 1) = Pi.single i 1 + Pi.single j 1 := by
      simp only [reflect]
      rw [Finset.sum_eq_single j]
      · simp [hcart]
        abel
      · intro l _ hl
        simp [hl]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rwa [h2] at h1
  exact ⟨IsRoot.basis (τ := τ) i, IsRoot.basis (τ := τ) j, hroot_add,
    by rw [excPayR_iform_single_self hτ j, excPayR_iform_single_self hτ i],
    by rw [excPayR_iform_single_pair hτ i j, hcart, excPayR_iform_single_self hτ i]
       norm_num⟩

private theorem excPayR_orth_simple {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {i j : Fin τ.rank} (hij : i ≠ j) (h : excPayR_coxeter τ i j = 2) :
    ∀ α ∈ ({Pi.single i 1, -Pi.single i 1} : Set (Fin τ.rank → ℤ)),
      ∀ β ∈ ({Pi.single j 1, -Pi.single j 1} : Set (Fin τ.rank → ℤ)),
        α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β) = 0 := by
  have hzero : τ.cartan i j = 0 := excPayR_cartan_eq_zero_of_coxeter hτ i j hij h
  have hpd := excPayR_posDef_cartan hτ
  have hsymm : τ.symmetrizedCartan = τ.cartan := excPayR_symmetrizedCartan_eq_cartan hτ
  have hdot : ∀ x y : Fin τ.rank → ℤ,
      x ⬝ᵥ (τ.symmetrizedCartan *ᵥ y) = excPayR_form τ x y := by
    intro x y
    rw [hsymm]
    rfl
  have hpair : excPayR_form τ (Pi.single i 1) (Pi.single j 1) = 0 := by
    rw [excPayR_form_single_left τ i (Pi.single j 1), Finset.sum_eq_single j]
    · simp [hzero]
    · intro l _ hl
      simp [hl]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hnegi : (-Pi.single i 1 : Fin τ.rank → ℤ) = (-1 : ℤ) • Pi.single i 1 := by simp
  have hnegj : (-Pi.single j 1 : Fin τ.rank → ℤ) = (-1 : ℤ) • Pi.single j 1 := by simp
  rintro α (rfl | rfl) β (rfl | rfl)
  · rw [hdot, hpair]
  · rw [hdot, hnegj, excPayR_form_smul_right hpd, hpair]
    ring
  · rw [hdot, hnegi, excPayR_form_smul_left, hpair]
    ring
  · rw [hdot, hnegi, hnegj, excPayR_form_smul_left, excPayR_form_smul_right hpd, hpair]
    ring

theorem isA2Pair_simple_E7 {i j : Fin 7} (h : CoxeterMatrix.E₇ i j = 3) :
    CFSG.HardMathSupport.Timmesfeld.CrossChar.IsA2Pair (τ := .E7)
      (Pi.single i 1) (Pi.single j 1) :=
  excPayR_isA2Pair_simple (Or.inr (Or.inl rfl)) h

theorem orth_simple_E7 {i j : Fin 7} (hij : i ≠ j) (h : CoxeterMatrix.E₇ i j = 2) :
    ∀ α ∈ ({Pi.single i 1, -Pi.single i 1} : Set (Fin Tag.E7.rank → ℤ)),
      ∀ β ∈ ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.E7.rank → ℤ)),
        α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 :=
  excPayR_orth_simple (Or.inr (Or.inl rfl)) hij h

theorem exists_edge_E7 (i : Fin 7) : ∃ j, CoxeterMatrix.E₇ i j = 3 := by
  fin_cases i
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨5, by decide⟩

theorem isA2Pair_simple_E6 {i j : Fin 6} (h : CoxeterMatrix.E₆ i j = 3) :
    CFSG.HardMathSupport.Timmesfeld.CrossChar.IsA2Pair (τ := .E6)
      (Pi.single i 1) (Pi.single j 1) :=
  excPayR_isA2Pair_simple (Or.inl rfl) h

theorem orth_simple_E6 {i j : Fin 6} (hij : i ≠ j) (h : CoxeterMatrix.E₆ i j = 2) :
    ∀ α ∈ ({Pi.single i 1, -Pi.single i 1} : Set (Fin Tag.E6.rank → ℤ)),
      ∀ β ∈ ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.E6.rank → ℤ)),
        α ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ β) = 0 :=
  excPayR_orth_simple (Or.inl rfl) hij h

theorem exists_edge_E6 (i : Fin 6) : ∃ j, CoxeterMatrix.E₆ i j = 3 := by
  fin_cases i
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨4, by decide⟩

end CFSG.StandardType.ExcPay
