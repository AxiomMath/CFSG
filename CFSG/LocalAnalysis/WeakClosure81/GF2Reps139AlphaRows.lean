module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139AlphaS
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139AlphaCtx
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139AlphaU43
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139FormsA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139FormsB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139FormsC

import CFSG.Quasithin.Vol2.Ch12Sec4L5B42

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

theorem Std139.alpha_row_SL (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n) (hn : 3 ≤ n)
    {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (hirr : IsIrrOn K ⊤ ⊥) {k a : ℕ}
    (ha : a ≤ 2) (hSL : IsSLn ↥K k a) (hNat : BinaryNaturalSL K ⊤ ⊥ k a) : ShapeNat4 K X n := by
  obtain ⟨E, hEfield, hEfin, hEcard, π, hπ⟩ := hNat
  letI : Field E := hEfield
  letI : Finite E := hEfin
  obtain ⟨f, hfadd, hfker, hfsurj, hfe⟩ :=
    CFSG.Quasithin.Vol2.KGNat.exists_coord
      (CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL k E)) hπ
  have hf1 : f 1 = 0 := by
    have h := hfadd 1 trivial 1 trivial
    rw [mul_one] at h
    exact (add_left_cancel (show f 1 + 0 = f 1 + f 1 by rw [add_zero]; exact h)).symm
  have hfinv : ∀ u : W, f u⁻¹ = - f u := by
    intro u
    have h := hfadd u trivial u⁻¹ trivial
    rw [mul_inv_cancel, hf1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hinj : Function.Injective f := by
    intro u v huv
    have h1 : f (u * v⁻¹) = 0 := by
      rw [hfadd u trivial v⁻¹ trivial, huv, hfinv v, add_neg_cancel]
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hfker (u * v⁻¹) trivial).mp h1))
  have hsurj : Function.Surjective f := fun m => by
    obtain ⟨u, -, hu⟩ := hfsurj m
    exact ⟨u, hu⟩
  let Ψm : W →* Multiplicative (Fin k → E) :=
    { toFun := fun w => Multiplicative.ofAdd (f w)
      map_one' := by rw [hf1]; rfl
      map_mul' := by
        intro u v
        show Multiplicative.ofAdd (f (u * v)) = _
        rw [hfadd u trivial v trivial]; rfl }
  have hΨinj : Function.Injective Ψm := fun u v huv =>
    hinj (congrArg Multiplicative.toAdd huv)
  have hΨsurj : Function.Surjective Ψm := by
    intro y
    obtain ⟨u, hu⟩ := hsurj (Multiplicative.toAdd y)
    refine ⟨u, ?_⟩
    show Multiplicative.ofAdd (f u) = y
    rw [hu]
    rfl
  let Ψ : W ≃* Multiplicative (Fin k → E) := MulEquiv.ofBijective Ψm ⟨hΨinj, hΨsurj⟩
  have hcardW : Nat.card W = Nat.card E ^ k := by
    calc Nat.card W = Nat.card (Multiplicative (Fin k → E)) := Nat.card_congr Ψ.toEquiv
      _ = Nat.card (Fin k → E) := rfl
      _ = Nat.card E ^ k := by rw [Nat.card_fun, Nat.card_fin]
  have hak : a * k = 2 * n := by
    apply CFSG.Quasithin.H13.eq_of_two_pow_eq
    calc 2 ^ (a * k) = (2 ^ a) ^ k := by rw [pow_mul]
      _ = Nat.card E ^ k := by rw [hEcard]
      _ = Nat.card W := hcardW.symm
      _ = 4 ^ n := S.card
      _ = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have ha1 : 1 ≤ a := by
    by_contra h
    have h0 : a = 0 := by omega
    haveI : Fintype E := Fintype.ofFinite E
    have h2 : 1 < Nat.card E := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    rw [h0, pow_zero] at hEcard
    omega
  have hk2 : 2 ≤ k := by
    interval_cases a <;> omega
  have hscalar : ∀ x ∈ X, ∃ c : E, c ≠ 0 ∧ ∀ y : Fin k → E,
      f (x (Ψ.symm (Multiplicative.ofAdd y))) = c • y := by
    intro x hx
    let Tx : (Fin k → E) →+ (Fin k → E) :=
      { toFun := fun y => f (x (Ψ.symm (Multiplicative.ofAdd y)))
        map_zero' := by
          show f (x (Ψ.symm (Multiplicative.ofAdd 0))) = 0
          rw [show (Multiplicative.ofAdd (0 : Fin k → E)) = 1 from rfl, map_one, map_one, hf1]
        map_add' := by
          intro y y'
          have h1 : Ψ.symm (Multiplicative.ofAdd (y + y')) =
              Ψ.symm (Multiplicative.ofAdd y) * Ψ.symm (Multiplicative.ofAdd y') := by
            rw [show Multiplicative.ofAdd (y + y') =
              Multiplicative.ofAdd y * Multiplicative.ofAdd y' from rfl, map_mul]
          show f (x (Ψ.symm (Multiplicative.ofAdd (y + y')))) =
            f (x (Ψ.symm (Multiplicative.ofAdd y))) + f (x (Ψ.symm (Multiplicative.ofAdd y')))
          rw [h1, map_mul, hfadd _ trivial _ trivial] }
    have hTinj : Function.Injective Tx := by
      intro y y' hyy
      have h1 : x (Ψ.symm (Multiplicative.ofAdd y)) =
          x (Ψ.symm (Multiplicative.ofAdd y')) := hinj hyy
      have h2 : Ψ.symm (Multiplicative.ofAdd y) = Ψ.symm (Multiplicative.ofAdd y') :=
        x.injective h1
      exact Multiplicative.ofAdd.injective (Ψ.symm.injective h2)
    have hTcomm : ∀ (γ : ↥(StatedSL k E)) (y : Fin k → E),
        Tx ((CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL k E)).lin γ y) =
          (CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL k E)).lin γ (Tx y) := by
      intro γ y
      let g : MulAut W := π γ
      set u : W := Ψ.symm (Multiplicative.ofAdd y) with hu
      have hfu : f u = y := by
        rw [hu]
        exact congrArg Multiplicative.toAdd (Ψ.apply_symm_apply (Multiplicative.ofAdd y))
      have hxcent : x ∈ Subgroup.centralizer (K : Set (MulAut W)) := by
        rw [Std139.alpha_centralizer hw2 S hn hK hirr]; exact hx
      have hcomm : x (g u) = g (x u) := by
        have hc := Subgroup.mem_centralizer_iff.mp hxcent g (π γ).2
        exact (congrArg (fun h : MulAut W => h u) hc).symm
      have hkey : Ψ.symm (Multiplicative.ofAdd
          ((CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL k E)).lin γ y)) = g u := by
        apply Ψ.injective
        rw [Ψ.apply_symm_apply]
        apply Multiplicative.ofAdd.injective
        show (CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL k E)).lin γ y = f (g u)
        rw [← hfu]
        exact (hfe γ u trivial).symm
      show f (x (Ψ.symm (Multiplicative.ofAdd
          ((CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL k E)).lin γ y)))) =
        (CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL k E)).lin γ
          (f (x (Ψ.symm (Multiplicative.ofAdd y))))
      rw [hkey]
      show f (x (g u)) =
        (CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL k E)).lin γ (f (x u))
      rw [hcomm, hfe γ (x u) trivial]
    obtain ⟨c, hc⟩ := CFSG.Quasithin.Vol2.KGNat.commutant_statedSL hk2 Tx hTcomm
    have hcne : c ≠ 0 := by
      intro hc0
      have hk0 : 0 < k := by omega
      let y0 : Fin k → E := Pi.single ⟨0, hk0⟩ 1
      have hy0 : y0 ≠ 0 := by
        intro h
        have h1 := congrFun h ⟨0, hk0⟩
        simp [y0] at h1
      have h1 : Tx y0 = Tx 0 := by rw [hc y0, hc 0, hc0, zero_smul, zero_smul]
      exact hy0 (hTinj h1)
    exact ⟨c, hcne, fun y => hc y⟩
  have ha2 : a = 2 := by
    let χ : ↥X → Eˣ := fun x =>
      Units.mk0 (hscalar x x.2).choose (hscalar x x.2).choose_spec.1
    have hχinj : Function.Injective χ := by
      intro x x' hxx
      have hc : (hscalar x x.2).choose = (hscalar x' x'.2).choose := by
        simpa [χ] using congrArg (fun u : Eˣ => (u : E)) hxx
      apply Subtype.ext
      ext w
      apply hinj
      have h1 := (hscalar x x.2).choose_spec.2 (f w)
      have h2 := (hscalar x' x'.2).choose_spec.2 (f w)
      rw [hc] at h1
      rw [← h1] at h2
      rw [show Ψ.symm (Multiplicative.ofAdd (f w)) = w from
        Ψ.symm_apply_apply w] at h2
      exact h2.symm
    have hle : Nat.card X ≤ Nat.card Eˣ := Nat.card_le_card_of_injective χ hχinj
    have hEunits : Nat.card Eˣ = 2 ^ a - 1 := by rw [Nat.card_units, hEcard]
    have h3 : 3 ≤ 2 ^ a - 1 := by
      rw [← S.Xcard, ← hEunits]; exact hle
    have h4 : 4 ≤ 2 ^ a := by omega
    interval_cases a <;> omega
  have hk : k = n := by
    rw [ha2] at hak
    omega
  have hkE4 : Nat.card E = 4 := by rw [hEcard, ha2]; norm_num
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite (GaloisField 2 2)
  have hGF4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  have hρcard : Fintype.card E = Fintype.card (GaloisField 2 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hkE4, hGF4]
  let ρ : E ≃+* GaloisField 2 2 := FiniteField.ringEquivOfCardEq hρcard
  have hρSL : Function.Bijective (Matrix.SpecialLinearGroup.map (n := Fin k) ρ.toRingHom) := by
    constructor
    · intro A B hAB
      apply Subtype.ext
      apply Matrix.map_injective ρ.injective
      simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using
        congrArg (fun x : Matrix.SpecialLinearGroup (Fin k) (GaloisField 2 2) =>
          (x : Matrix (Fin k) (Fin k) (GaloisField 2 2))) hAB
    · intro C
      refine ⟨⟨(C : Matrix (Fin k) (Fin k) (GaloisField 2 2)).map
        (ρ.symm : GaloisField 2 2 → E), ?_⟩, ?_⟩
      · have h := RingHom.map_det ρ.symm.toRingHom (C : Matrix (Fin k) (Fin k) (GaloisField 2 2))
        rw [C.prop, map_one] at h
        exact h.symm
      · apply Subtype.ext
        show (((C : Matrix (Fin k) (Fin k) (GaloisField 2 2)).map
          (ρ.symm : GaloisField 2 2 → E)).map (ρ : E → GaloisField 2 2)) =
          (C : Matrix (Fin k) (Fin k) (GaloisField 2 2))
        rw [Matrix.map_map]
        rw [show (((ρ : E → GaloisField 2 2)) ∘ (ρ.symm : GaloisField 2 2 → E)) = id from
          funext fun x => ρ.apply_symm_apply x]
        rw [Matrix.map_id]
  let ρSL : Matrix.SpecialLinearGroup (Fin k) E ≃*
      Matrix.SpecialLinearGroup (Fin k) (GaloisField 2 2) :=
    MulEquiv.ofBijective (Matrix.SpecialLinearGroup.map (n := Fin k) ρ.toRingHom) hρSL
  let πEquiv : ↥(StatedSL k E) ≃* ↥K :=
    MulEquiv.ofBijective π ⟨hπ.injective_of_faithful (FFModel.nat_faithful _), hπ.1⟩
  let φ : ↥K ≃* Matrix.SpecialLinearGroup (Fin k) (GaloisField 2 2) :=
    πEquiv.symm.trans ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL k E).symm.trans
      ρSL)
  let ψM : W →* Multiplicative (Fin k → GaloisField 2 2) :=
    { toFun := fun w => Multiplicative.ofAdd (fun i => ρ (f w i))
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext i
        simp [hf1]
      map_mul' := by
        intro u v
        apply Multiplicative.toAdd.injective
        funext i
        simp [Pi.add_apply, hfadd u trivial v trivial, map_add] }
  have hψinj : Function.Injective ψM := by
    intro u v huv
    apply hinj
    funext i
    exact ρ.injective (congrFun (congrArg Multiplicative.toAdd huv) i)
  have hψsurj : Function.Surjective ψM := by
    intro y
    obtain ⟨u, hu⟩ := hsurj (fun i => ρ.symm (Multiplicative.toAdd y i))
    refine ⟨u, ?_⟩
    apply Multiplicative.toAdd.injective
    show (fun i => ρ (f u i)) = Multiplicative.toAdd y
    funext i
    have hui : f u i = ρ.symm (Multiplicative.toAdd y i) := congrFun hu i
    rw [hui]
    simp
  let ψ : W ≃* Multiplicative (Fin k → GaloisField 2 2) :=
    MulEquiv.ofBijective ψM ⟨hψinj, hψsurj⟩
  have hcond1 : ∀ (b : ↥K) (w : W), ψ ((b : MulAut W) w) =
      Multiplicative.ofAdd (((φ b : Matrix.SpecialLinearGroup (Fin k) (GaloisField 2 2)) :
        Matrix (Fin k) (Fin k) (GaloisField 2 2)).mulVec (Multiplicative.toAdd (ψ w))) := by
    intro b w
    obtain ⟨γ, rfl⟩ := hπ.1 b
    set M : Matrix (Fin k) (Fin k) E :=
      (((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL k E).symm γ :
        Matrix.SpecialLinearGroup (Fin k) E) : Matrix (Fin k) (Fin k) E) with hM
    have hπγ : πEquiv.symm (π γ) = γ := by
      change πEquiv.symm (πEquiv γ) = γ
      exact MulEquiv.symm_apply_apply πEquiv γ
    let γ' : ↥(StatedSL k E) := γ
    let g : Matrix.GeneralLinearGroup (Fin k) E := γ'
    have hφ : (φ (π γ) : Matrix (Fin k) (Fin k) (GaloisField 2 2)) =
        M.map (ρ : E → GaloisField 2 2) := by
      simp only [φ, MulEquiv.trans_apply]
      rw [hπγ]
      simp only [ρSL, MulEquiv.ofBijective_apply,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      rw [hM]
      rfl
    have hcoe : M = (g : Matrix (Fin k) (Fin k) E) := by
      have h := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe k E
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL k E).symm γ)
      rw [show (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL k E)
          ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL k E).symm γ) = γ from
        MulEquiv.apply_symm_apply _ γ] at h
      rw [hM]
      exact h.symm
    rw [hφ]
    have hfw : f ((π γ : MulAut W) w) = M.mulVec (f w) := by
      rw [hfe γ w trivial]
      rw [show ((CFSG.Quasithin.Vol2.KGNat.linModelNat (StatedSL k E)).lin γ) (f w) =
        (g : Matrix (Fin k) (Fin k) E).mulVec (f w) from
        CFSG.Quasithin.Vol2.KGNat.linModelNat_lin (StatedSL k E) γ (f w)]
      rw [hcoe]
    show Multiplicative.ofAdd (fun i => ρ (f ((π γ : MulAut W) w) i)) =
      Multiplicative.ofAdd ((M.map (ρ : E → GaloisField 2 2)).mulVec (fun i => ρ (f w i)))
    congr 1
    funext i
    rw [hfw]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have hcond2 : ∀ x ∈ X, ∃ c : GaloisField 2 2, ∀ w : W,
      ψ (x w) = Multiplicative.ofAdd (c • Multiplicative.toAdd (ψ w)) := by
    intro x hx
    obtain ⟨c, hcne, hc⟩ := hscalar x hx
    refine ⟨ρ c, fun w => ?_⟩
    have hfw : f (x w) = c • f w := by
      have h := hc (f w)
      rwa [show Ψ.symm (Multiplicative.ofAdd (f w)) = w from
        Ψ.symm_apply_apply w] at h
    show Multiplicative.ofAdd (fun i => ρ (f (x w) i)) =
      Multiplicative.ofAdd ((ρ c) • (fun i => ρ (f w i)))
    congr 1
    funext i
    rw [hfw]
    simp [Pi.smul_apply, map_mul]
  exact hk ▸ ⟨φ, ψ, hcond1, hcond2⟩

theorem Std139.alpha_row_cover (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    (hn : 3 ≤ n) {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (hirr : IsIrrOn K ⊤ ⊥)
    (hHat : IsHat ↥K ↥(alternatingGroup (Fin 6))) (hcard : Nat.card W = 2 ^ 6) :
    ShapeCover K X n := by
  have hZcard : Nat.card (Subgroup.center ↥K) = 3 := hHat.2.1
  have hn3 : n = 3 := by
    have h46 : 4 ^ n = 2 ^ 6 := S.card.symm.trans hcard
    have h2 : 2 ^ (2 * n) = 2 ^ 6 := by
      calc 2 ^ (2 * n) = (2 ^ 2) ^ n := by rw [pow_mul]
        _ = 4 ^ n := by norm_num
        _ = 2 ^ 6 := h46
    have h2n : 2 * n = 6 := Nat.pow_right_injective (le_refl 2) h2
    omega
  refine ⟨hn3, hHat, ?_, hcard⟩
  have hmap : Nat.card ↥((Subgroup.center ↥K).map K.subtype) = 3 := by
    rw [Subgroup.card_subtype, hZcard]
  have hle : (Subgroup.center ↥K).map K.subtype ≤ X := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← Std139.alpha_centralizer hw2 S hn hK hirr]
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hb (⟨k, hk⟩ : ↥K))
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hmap, S.Xcard])

theorem Std139.alpha_row_centralizer (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    (hn : 3 ≤ n) {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (hirr : IsIrrOn K ⊤ ⊥)
    (hbot : Subgroup.centralizer (K : Set (MulAut W)) = ⊥) : False := by
  have h := Std139.alpha_centralizer hw2 S hn hK hirr
  rw [hbot] at h
  have h3 := S.Xcard
  rw [← h, Subgroup.card_bot] at h3
  omega

theorem natCard_of_g2NaturalDerived {K : Subgroup (MulAut W)} (hw2 : ∀ w : W, w ^ 2 = 1)
    (h : G2NaturalDerived K ⊤ ⊥ 1) : Nat.card W = 2 ^ 6 := by
  obtain ⟨K', hField, hFin, hcard, π, hπ⟩ := h
  obtain ⟨-, -, -, -, -, -, -, β, hβsurj, hβker, -⟩ := hπ
  letI : Fintype K' := Fintype.ofFinite K'
  have hchar : CharP K' 2 := by
    refine charP_of_card_eq_prime ?_
    rw [← Nat.card_eq_fintype_card, hcard]
    norm_num
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : (u : W) ∈ (⊥ : Subgroup W) := (hβker u).mp hu
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  let e : ↥(⊤ : Subgroup W) ≃* (FFModel.zornQ ⁅quasithinG2 K', quasithinG2 K'⁆).Mod :=
    MulEquiv.ofBijective β ⟨hinj, hβsurj⟩
  calc Nat.card W = Nat.card (⊤ : Subgroup W) := Subgroup.card_top.symm
    _ = Nat.card (FFModel.zornQ ⁅quasithinG2 K', quasithinG2 K'⁆).Mod :=
        Nat.card_congr e.toEquiv
    _ = Nat.card K' ^ 6 := CFSG.Quasithin.H13.card_mod_zornQ _
    _ = 2 ^ 6 := by rw [hcard]; norm_num

theorem Std139.alpha_shape (h135 : W4Lem13_5) (hgen : U43TripleGen) (gU33 : GapEndU33)
    (gSp62 : GapEndSp62) (gL52 : GapEndL52) (gM22 : GapEndM22) (gL32 : GapEndL32)
    (gOut : GapOutU43) (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n) (hn : 3 ≤ n)
    {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (hirr : IsIrrOn K ⊤ ⊥) :
    ShapeNat4 K X n ∨ ShapeCover K X n := by
  have hDgt : 1 < Nat.card D := by
    rw [S.Dcard]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hDne : D ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot (H := D)).mp hDgt
  obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hctx : Is135Context (K ⊔ Subgroup.zpowers d) K :=
    Std139.alpha_context hw2 S hn hK hirr hd hd1'
  have hdmem : d ∈ K ⊔ Subgroup.zpowers d :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  have hdord : orderOf d = 2 := orderOf_eq_prime (S.elem.2 d hd) hd1'
  have hfix : fixV (Subgroup.zpowers d) = Y := Std139.fixV_eq_axis hw2 S hd hd1'
  have hmq : E3.mQuot ⊤ (fixV (Subgroup.zpowers d)) = 2 := by
    have h1 : E3.mQuot ⊤ Y = rkIdx Y := by
      rw [E3.mQuot, rkIdx, Subgroup.relIndex_top_right]
    rw [hfix, h1, S.Yrk]
  have hcost : E3.mQuot ⊤ (fixV (Subgroup.zpowers d)) ≤ 3 := by omega
  have hfour : ∀ {k : ℕ}, 4 ^ n = 2 ^ k → 2 * n = k := by
    intro k hk
    apply CFSG.Quasithin.H13.eq_of_two_pow_eq
    calc 2 ^ (2 * n) = (2 ^ 2) ^ n := by rw [pow_mul]
      _ = 4 ^ n := by norm_num
      _ = 2 ^ k := hk
  rcases h135 W hw2 (K ⊔ Subgroup.zpowers d) K d hctx hdmem hdord hcost with
    ⟨m, b, hb, hrow⟩ | ⟨m, hrow⟩ | ⟨hHat, hcard⟩ | ⟨S', hgrp, hLie, hHat, hcard⟩ |
    ⟨m, hAlt, hNat⟩ | ⟨hAlt7, hcard⟩ | ⟨hSp6, hcard⟩ | ⟨hSL5, hcard⟩ | ⟨hM22, hcard⟩ |
    ⟨hL34, hcard⟩ | ⟨hL32, hcard⟩
  · rcases hrow with ⟨hSL, hNat⟩ | ⟨hSp, hNat⟩ | ⟨hOm, hNat⟩ | ⟨hOm, hNat⟩
    · exact Or.inl (Std139.alpha_row_SL hw2 S hn hK hirr (by rw [hmq] at hb; omega) hSL hNat)
    · exact False.elim (Std139.alpha_not_symplectic hw2 S hn hK hirr (hasSympForm_of_natSpn hNat))
    · exact False.elim
        (Std139.alpha_not_symplectic hw2 S hn hK hirr (hasSympForm_of_natOmegaPlus hNat))
    · exact False.elim
        (Std139.alpha_not_symplectic hw2 S hn hK hirr (hasSympForm_of_natOmegaMinus hNat))
  · rcases hrow with ⟨hSL, hNat⟩ | ⟨hSp, hNat⟩ | ⟨hOm, hNat⟩ | ⟨hOm, hNat⟩ | ⟨hSU, hNat⟩ |
      ⟨hLie, hG2⟩
    · exact Or.inl (Std139.alpha_row_SL hw2 S hn hK hirr (by norm_num) hSL hNat)
    · exact False.elim (Std139.alpha_not_symplectic hw2 S hn hK hirr (hasSympForm_of_natSpn hNat))
    · exact False.elim
        (Std139.alpha_not_symplectic hw2 S hn hK hirr (hasSympForm_of_natOmegaPlus hNat))
    · exact False.elim
        (Std139.alpha_not_symplectic hw2 S hn hK hirr (hasSympForm_of_natOmegaMinus hNat))
    · exact False.elim (Std139.alpha_not_symplectic hw2 S hn hK hirr (hasSympForm_of_natSUn hNat))
    · refine False.elim (Std139.alpha_row_centralizer hw2 S hn hK hirr ?_)
      exact gU33 W hw2 K hLie hirr (natCard_of_g2NaturalDerived hw2 hG2)
  · exact Or.inr (Std139.alpha_row_cover hw2 S hn hK hirr hHat hcard)
  · exact False.elim
      (Std139.alpha_row_U43 hgen gOut hw2 S hn hK hirr ⟨S', hgrp, hLie, hHat⟩ hcard)
  · exact False.elim
      (Std139.alpha_not_symplectic hw2 S hn hK hirr (hasSympForm_of_alternatingNatural hNat))
  · exact absurd (hfour (S.card.symm.trans hcard)) (by omega)
  · refine False.elim (Std139.alpha_row_centralizer hw2 S hn hK hirr ?_)
    exact gSp62 W hw2 K hSp6 hirr hcard
  · refine False.elim (Std139.alpha_row_centralizer hw2 S hn hK hirr ?_)
    exact gL52 W hw2 K hSL5 hirr hcard
  · refine False.elim (Std139.alpha_row_centralizer hw2 S hn hK hirr ?_)
    exact gM22 W hw2 K hM22 hirr hcard
  · exact absurd (hfour (S.card.symm.trans hcard)) (by omega)
  · refine False.elim (Std139.alpha_row_centralizer hw2 S hn hK hirr ?_)
    exact gL32 W hw2 K hL32 hirr hcard

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
