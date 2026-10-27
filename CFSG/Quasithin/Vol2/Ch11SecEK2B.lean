module

public import CFSG.Quasithin.Vol2.Ch11SecEFacts2
public import CFSG.Quasithin.Vol2.Ch11G2Q8RootLine
public import CFSG.Quasithin.Vol2.Ch11G2Q8OffLines

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8

namespace EK2

variable {K : Type} [Field K] [CharP K 2]

theorem fix_iff_polarQ_comm (γ : ↥(cayleyGroup K)) (w : Ix3 → K) :
    g2Act γ w = w ↔ ∀ z, polarQ w (g2Act γ z - z) = 0 := by
  constructor
  · intro h z
    rw [polarQ_sub_right, ← polarQ_g2Act γ w z, h, sub_self]
  · intro h
    have h1 : g2Act γ⁻¹ w - w = 0 := eq_zero_of_polarQ fun y => by
      rw [polarQ_sub_left, ← polarQ_g2Act γ (g2Act γ⁻¹ w) y, g2Act_apply_inv,
        ← polarQ_sub_right]
      exact h y
    have h2 := congrArg (g2Act γ) (sub_eq_zero.mp h1)
    rwa [g2Act_apply_inv, eq_comm] at h2

end EK2

open EK2 in
theorem factG2LongRoot_holds : FactG2LongRoot := by
  intro K _ _ n hn hK W _ _ hW H π hπ E hEab hEH hcard
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have := finite_cayleyGroup (F := K)
  have hq : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  have hfinj : Function.Injective f := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  have hcardW : Nat.card W = Nat.card K ^ 6 := by
    rw [← card_Q]
    exact Nat.card_eq_of_bijective f ⟨hfinj, hf.surj⟩
  have hq2 : 2 ^ (2 * n) = Nat.card K ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  have hcard' : Nat.card (commSpace E) ≤ Nat.card K ^ 2 := hq2 ▸ hcard
  have key : ∀ e ∈ E, ∃ γ : ↥(cayleyGroup K), γ * γ = 1 ∧
      (∀ w, f (e w) = g2Act γ (f w)) ∧ Nat.card K ^ 4 ≤ Nat.card (fixQ γ) := by
    intro e he
    have heH' : ∀ h ∈ H, e⁻¹ * h * e ∈ H := fun h hh => by
      simpa using hEH e⁻¹ (E.inv_mem he) h hh
    obtain ⟨c, γ, σ, hc, hcγ⟩ := exists_smul_frob_of_normalizes hf hc0 hc1 hK hn e
      (bot_maps e) (bot_maps e⁻¹) (hEH e he) heH'
    let φ : W →* W :=
      { toFun := fun w => e w * w⁻¹
        map_one' := by rw [map_one, inv_one, mul_one]
        map_mul' := fun a b => by rw [map_mul, mul_inv, mul_mul_mul_comm] }
    have hmemker : ∀ w, w ∈ φ.ker ↔ e w = w := fun w => by
      rw [MonoidHom.mem_ker]
      exact mul_inv_eq_one
    have hφr : φ.range ≤ commSpace E := by
      rintro _ ⟨w, rfl⟩
      exact Subgroup.subset_closure ⟨e, he, w, rfl⟩
    have hker : Nat.card K ^ 4 ≤ Nat.card φ.ker := by
      have h1 := φ.ker.card_mul_index
      rw [Subgroup.index_ker, hcardW] at h1
      have h2 : Nat.card φ.range ≤ Nat.card K ^ 2 := (Subgroup.card_le_of_le hφr).trans hcard'
      by_contra h3
      push Not at h3
      have h4 : Nat.card φ.ker * Nat.card φ.range < Nat.card K ^ 4 * Nat.card K ^ 2 :=
        Nat.mul_lt_mul_of_lt_of_le h3 h2 (by positivity)
      rw [h1, ← pow_add] at h4
      exact lt_irrefl _ h4
    have hσ : ∀ θ, σ θ = θ := by
      by_contra hσ
      obtain ⟨θ, hθ⟩ := not_forall.mp hσ
      let Te : (Ix3 → K) →+ (Ix3 → K) :=
        { toFun := fun x => c • g2Act γ (frobQ σ x)
          map_zero' := by
            rw [show frobQ (σ : K →+* K) 0 = 0 from funext fun j => map_zero σ, map_zero,
              smul_zero]
          map_add' := fun x y => by
            rw [show frobQ (σ : K →+* K) (x + y) = frobQ σ x + frobQ σ y from
              funext fun j => map_add σ (x j) (y j), map_add, smul_add] }
      have hTe : ∀ (a : K) (x : Ix3 → K), Te (a • x) = (σ : K →+* K) a • Te x := by
        intro a x
        show c • g2Act γ (frobQ σ (a • x)) = (σ : K →+* K) a • (c • g2Act γ (frobQ σ x))
        rw [frobQ_smul, G2Q8.g2Act_smul, smul_comm]
      have h1 := card_fix_sq_le Te (σ : K →+* K) hθ hTe
      have h3 : Nat.card φ.ker ≤ Nat.card {x : Ix3 → K // Te x = x} := by
        refine Nat.card_le_card_of_injective (fun w => ⟨f w.1, ?_⟩) ?_
        · show c • g2Act γ (frobQ σ (f w.1)) = f w.1
          rw [← hcγ, (hmemker w.1).mp w.2]
        · intro w w' h
          exact Subtype.ext (hfinj (congrArg Subtype.val h))
      rw [card_Q] at h1
      have h4 : Nat.card K ^ 4 * Nat.card K ^ 4 ≤ Nat.card K ^ 6 :=
        le_trans (Nat.mul_le_mul (hker.trans h3) (hker.trans h3)) (by rw [← sq]; exact h1)
      rw [← pow_add] at h4
      have h5 : Nat.card K ^ 6 < Nat.card K ^ (4 + 4) := Nat.pow_lt_pow_right hq (by norm_num)
      omega
    have hfrob : ∀ x, frobQ (σ : K →+* K) x = x := fun x => funext fun j => hσ (x j)
    have hcγ' : ∀ w, f (e w) = c • g2Act γ (f w) := fun w => by rw [hcγ, hfrob]
    have he2 : e * e = 1 := by
      have := hEab.2 e he
      rwa [sq] at this
    have hsq : ∀ x, g2Act (γ * γ) x = (c * c)⁻¹ • x := by
      intro x
      obtain ⟨w, rfl⟩ := hf.surj x
      have h1 := congrArg f (show e (e w) = w by
        rw [← MulAut.mul_apply, he2, MulAut.one_apply])
      rw [hcγ', hcγ', G2Q8.g2Act_smul, smul_smul] at h1
      rw [g2Act_mul_apply]
      conv_rhs => rw [← h1]
      rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc hc), one_smul]
    have hcc : (c * c)⁻¹ = 1 := scalar_eq_one hsq
    have hc1' : c = 1 := by
      have h3 : c * c = 1 := by rw [← inv_inv (c * c), hcc, inv_one]
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      have h4 : (c - 1) ^ 2 = 0 := by linear_combination h3 + (1 - c) * h2
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)
    have hγf : ∀ w, f (e w) = g2Act γ (f w) := fun w => by rw [hcγ', hc1', one_smul]
    refine ⟨γ, cayley_eq_one fun x => by rw [hsq, hcc, one_smul], hγf, ?_⟩
    refine hker.trans (Nat.card_le_card_of_injective
      (fun w => ⟨f w.1, mem_fixQ.mpr (by rw [← hγf, (hmemker w.1).mp w.2])⟩) ?_)
    intro w w' h
    exact Subtype.ext (hfinj (congrArg Subtype.val h))
  choose γe hγe1 hγe hγefix using key
  have hcommP : ∀ e (he : e ∈ E), ∀ y ∈ commQ (γe e he), ∃ w ∈ commSpace E, f w = y := by
    intro e he y hy
    obtain ⟨z, rfl⟩ := mem_commQ.mp hy
    obtain ⟨w, rfl⟩ := hf.surj z
    exact ⟨e w * w⁻¹, Subgroup.subset_closure ⟨e, he, w, rfl⟩,
      by rw [hf.map_mul_inv, hγe e he]⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ↥(cayleyGroup K), ∀ e (he : e ∈ E),
      x₀⁻¹ * γe e he * x₀ ∈ rootD (none : Option K) := by
    by_cases hall : ∀ e (he : e ∈ E), γe e he = 1
    · refine ⟨1, fun e he => ?_⟩
      rw [hall e he, inv_one, one_mul, one_mul]
      exact (rootD none).one_mem
    push Not at hall
    obtain ⟨e₀, he₀, hne₀⟩ := hall
    obtain ⟨x₀, hx₀⟩ := eq_conj_tL_of_fix (hγe1 e₀ he₀) hne₀ (hγefix e₀ he₀)
    refine ⟨x₀, fun e he => ?_⟩
    have hPle : ∀ w ∈ commSpace E, f w ∈ commQ (γe e₀ he₀) := by
      have hι : ∀ y : ↥(commQ (γe e₀ he₀)), ∃ w : ↥(commSpace E), f w = y := fun y => by
        obtain ⟨w, hw, hwy⟩ := hcommP e₀ he₀ y y.2
        exact ⟨⟨w, hw⟩, hwy⟩
      choose ι hι using hι
      have hιinj : Function.Injective ι := fun y y' h =>
        Subtype.ext (by rw [← hι y, ← hι y', h])
      have hcQ : Nat.card K ^ 2 ≤ Nat.card (commQ (γe e₀ he₀)) := by
        have h1 := card_commQ_mul_card_fixQ (γe e₀ he₀)
        have h2 : Nat.card (fixQ (γe e₀ he₀)) ≤ Nat.card K ^ 4 := by
          refine le_trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)))
            (card_inC_le x₀)
          rw [hx₀]
          exact mem_fixQ_conj_tL x₀ w
        rw [card_Q] at h1
        by_contra h3
        push Not at h3
        have h4 : Nat.card (commQ (γe e₀ he₀)) * Nat.card (fixQ (γe e₀ he₀)) <
            Nat.card K ^ 2 * Nat.card K ^ 4 := Nat.mul_lt_mul_of_lt_of_le h3 h2 (by positivity)
        rw [h1, ← pow_add] at h4
        exact lt_irrefl _ h4
      have hbij := (Nat.bijective_iff_injective_and_card ι).mpr ⟨hιinj,
        le_antisymm (Nat.card_le_card_of_injective ι hιinj) (hcard'.trans hcQ)⟩
      intro w hw
      obtain ⟨y, hy⟩ := hbij.2 ⟨w, hw⟩
      have h1 : f w = y := by
        rw [← hι y, hy]
      rw [h1]
      exact y.2
    have hfixC : ∀ v, InC v → g2Act (x₀⁻¹ * γe e he * x₀) v = v := by
      intro v hv
      rw [g2Act_mul_apply, g2Act_mul_apply]
      have h0 : g2Act (γe e₀ he₀) (g2Act x₀ v) = g2Act x₀ v := by
        rw [← mem_fixQ, hx₀, mem_fixQ_conj_tL, g2Act_inv_apply]
        exact hv
      have hw : g2Act (γe e he) (g2Act x₀ v) = g2Act x₀ v := by
        rw [fix_iff_polarQ_comm]
        intro z
        obtain ⟨u, hu, huz⟩ := hcommP e he _ (mem_commQ.mpr ⟨z, rfl⟩)
        obtain ⟨z', hz'⟩ := mem_commQ.mp (hPle u hu)
        rw [← huz, ← hz']
        exact (fix_iff_polarQ_comm _ _).mp h0 z'
      rw [hw, g2Act_inv_apply]
    refine mem_rootD_of_fixD (mem_A1.mpr fun w hw => hfixC w ?_) fun w hw => hfixC w ?_
    · obtain ⟨-, h2, h3⟩ := mem_stdF_three.mp hw
      exact ⟨h2, h3⟩
    · obtain ⟨h1, h2⟩ := (fixD_iff none w).mp hw
      exact ⟨h2, h1⟩
  let Φ : ↥E → ↥(rootD (none : Option K)) := fun e => ⟨x₀⁻¹ * γe e e.2 * x₀, hx₀ e e.2⟩
  have hΦ : Function.Injective Φ := by
    intro e e' h
    have h1 : γe e e.2 = γe e' e'.2 := mul_left_cancel (mul_right_cancel (congrArg Subtype.val h))
    exact Subtype.ext (MulEquiv.ext fun w => hfinj (by rw [hγe e e.2, hγe e' e'.2, h1]))
  have h1 := Nat.card_le_card_of_injective Φ hΦ
  rwa [card_rootD, hK] at h1

end CFSG.Quasithin.Vol2.Ch11.SecE
