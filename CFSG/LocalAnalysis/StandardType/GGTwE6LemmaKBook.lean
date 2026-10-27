module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKCop
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Defs
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Lang.E6Descent.RankTwistedE6
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public noncomputable section

namespace CFSG.StandardType.TwE6LemmaK

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Lang.E6Descent CFSG.Open CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.RankThree.E6 CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.StandardType.TableBExc.E6Three
  (zetaVec zetaVec_apply exists_zetaVec_eq zetaVec_injective)
open scoped Matrix

private theorem cubeTuple_add {K : Type} [Field K] {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (v w : Fin 6 → ZMod 3) : cubeTuple ζ (v + w) = cubeTuple ζ v * cubeTuple ζ w := by
  funext i
  show ζ ^ ((v + w) (e6Idx.symm i)).val =
    ζ ^ (v (e6Idx.symm i)).val * ζ ^ (w (e6Idx.symm i)).val
  rw [Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add]

section Book


theorem exists_family_of_toral_data (hK : LemmaKCheck) {q : ℕ} (h3 : 3 ∣ q + 1)
    {Ω : Type} [Field Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ q) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {X : Subgroup (ModGL Tag.E6 Ω)} (hX3 : IsElemAbelian 3 X)
    (hcard : 3 ^ 4 ≤ Nat.card X) {g₀ : ModGL Tag.E6 Ω} {v₀ : WeylGroup Tag.E6}
    (hA : ∀ x ∈ X, g₀⁻¹ * x * g₀ ∈ torusGroup Tag.E6 Ω ∧
      canonicalRep (coxeterSystem Tag.E6) Ω v₀ * twistE6 Ω Fr (g₀⁻¹ * x * g₀) *
        (canonicalRep (coxeterSystem Tag.E6) Ω v₀)⁻¹ = g₀⁻¹ * x * g₀) :
    ∃ a : X → Fin Tag.E6.rank → Ωˣ,
      (∀ x : X, rootDiagUnit Tag.E6 (a x) = g₀⁻¹ * (x : ModGL Tag.E6 Ω) * g₀) ∧
      (∀ x : X, ∃ v, a x = zetaVec ζ hζ v) ∧
      twE6W0 * v₀⁻¹ ∈ Subgroup.closure {s | ∃ α ∈ familyKernel a, s = rootReflection α} := by
  classical
  have hconj_apply : ∀ z : ModGL Tag.E6 Ω, g₀⁻¹ * z * g₀ = MulAut.conj g₀⁻¹ z := by
    intro z
    rw [MulAut.conj_apply, inv_inv]
  have hex : ∀ x : X, ∃ v : Fin Tag.E6.rank → ZMod 3,
      rootDiagUnit Tag.E6 (zetaVec ζ hζ v) =
        g₀⁻¹ * (x : ModGL Tag.E6 Ω) * g₀ := by
    intro x
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hA x x.2).1
    have hx3 : (x : ModGL Tag.E6 Ω) ^ 3 = 1 := hX3.2 x x.2
    have ht3 : (g₀⁻¹ * (x : ModGL Tag.E6 Ω) * g₀) ^ 3 = 1 := by
      rw [hconj_apply (x : ModGL Tag.E6 Ω), ← map_pow, hx3, map_one]
    have hb3 : b ^ 3 = 1 := by
      apply rootDiagUnit_injective (K := Ω)
      rw [← rootDiagUnit_pow, ← hb, ht3, rootDiagUnit_one]
    obtain ⟨v, hv⟩ := exists_zetaVec_eq (τ := Tag.E6) (p := 3) hζo hζ hb3
    exact ⟨v, by rw [hv]; exact hb.symm⟩
  choose e he using hex
  let y : X → Fin 6 → ZMod 3 := fun x k => e x (e6Idx k)
  let a : X → Fin Tag.E6.rank → Ωˣ := fun x => zetaVec ζ hζ (e x)
  have he' : ∀ x : X, rootDiagUnit Tag.E6 (a x) =
      g₀⁻¹ * (x : ModGL Tag.E6 Ω) * g₀ := fun x => he x
  have ha_eq_cube : ∀ x : X, a x = cubeTuple ζ (y x) := by
    intro x
    funext i
    simp [a, y, cubeTuple, zetaVec_apply]
  have ha3 : ∀ x : X, ∀ i, (a x i) ^ 3 = 1 := by
    intro x i
    rw [ha_eq_cube x]
    simp only [cubeTuple]
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  let u : WeylGroup Tag.E6 := twE6W0 * v₀⁻¹
  have hfix_y : ∀ x : X, e6WeylMat u *ᵥ y x = y x := by
    intro x
    have hA' : canonicalRep (coxeterSystem Tag.E6) Ω v₀ *
        twistE6 Ω Fr (rootDiagUnit Tag.E6 (a x)) *
        (canonicalRep (coxeterSystem Tag.E6) Ω v₀)⁻¹ = rootDiagUnit Tag.E6 (a x) := by
      have h := (hA x x.2).2
      rw [← he' x] at h
      exact h
    have htw : twistE6 Ω Fr (rootDiagUnit Tag.E6 (a x)) =
        rootDiagUnit Tag.E6
          (fun i => Units.map Fr.toMonoidHom ((a x) (e6Rho.symm i))) :=
      twistE6_rootDiagUnit (a x)
    have hconj_v0 : ∀ v : Fin Tag.E6.rank → ℤ,
        rootChar (a x) (v₀ • v) =
          rootChar (fun i => Units.map Fr.toMonoidHom ((a x) (e6Rho.symm i))) v := by
      refine (rootDiagUnit_eq_conj_canonicalRep_iff (a x)
        (fun i => Units.map Fr.toMonoidHom ((a x) (e6Rho.symm i))) v₀).1 ?_
      rw [htw] at hA'
      exact hA'.symm
    have hconj_w0 : ∀ v : Fin Tag.E6.rank → ℤ,
        rootChar (a x) (twE6W0 • v) =
          rootChar (fun i => Units.map Fr.toMonoidHom ((a x) (e6Rho.symm i))) v := by
      refine (rootDiagUnit_eq_conj_canonicalRep_iff (a x)
        (fun i => Units.map Fr.toMonoidHom ((a x) (e6Rho.symm i))) twE6W0).1 ?_
      have h := conj_twistE6_rootDiagUnit_of_cube hFr h3 (a x) (ha3 x)
      rw [htw] at h
      exact h.symm
    have hchar : ∀ v : Fin Tag.E6.rank → ℤ,
        rootChar (a x) (u⁻¹ • v) = rootChar (a x) v := by
      intro v
      have h1 := hconj_v0 (twE6W0⁻¹ • v)
      have h2 := hconj_w0 (twE6W0⁻¹ • v)
      have hu : u⁻¹ • v = v₀ • (twE6W0⁻¹ • v) := by
        have h : u⁻¹ = v₀ * twE6W0⁻¹ := by
          rw [show u = twE6W0 * v₀⁻¹ from rfl, mul_inv_rev, inv_inv]
        rw [h, mul_smul]
      rw [hu, h1, ← h2, smul_inv_smul]
    have hweyl : weylAct u (a x) = a x := by
      apply eq_of_rootChar_eq
      intro v
      rw [rootChar_weylAct]
      exact hchar v
    have h1 : weylAct u (cubeTuple ζ (y x)) = cubeTuple ζ (y x) := by
      rw [← ha_eq_cube x]
      exact hweyl
    rw [weylAct_cubeTuple hζo u (y x)] at h1
    exact cubeTuple_injective hζo h1
  have hy_add : ∀ x₁ x₂ : X, y (x₁ * x₂) = y x₁ + y x₂ := by
    intro x₁ x₂
    apply cubeTuple_injective hζo
    rw [cubeTuple_add hζ (y x₁) (y x₂), ← ha_eq_cube (x₁ * x₂), ← ha_eq_cube x₁,
      ← ha_eq_cube x₂]
    apply rootDiagUnit_injective (K := Ω)
    rw [rootDiagUnit_mul, he' (x₁ * x₂), he' x₁, he' x₂, Subgroup.coe_mul,
      hconj_apply ((x₁ : ModGL Tag.E6 Ω) * (x₂ : ModGL Tag.E6 Ω)),
      hconj_apply (x₁ : ModGL Tag.E6 Ω), hconj_apply (x₂ : ModGL Tag.E6 Ω), ← map_mul]
  have hy_one : y 1 = 0 := by
    apply cubeTuple_injective hζo
    rw [← ha_eq_cube 1]
    have h0 : cubeTuple ζ (0 : Fin 6 → ZMod 3) = 1 := by
      funext i
      simp [cubeTuple]
    rw [h0]
    apply rootDiagUnit_injective (K := Ω)
    rw [he' 1, rootDiagUnit_one, Subgroup.coe_one, mul_one, inv_mul_cancel]
  have hy_neg : ∀ x : X, y x⁻¹ = - y x := by
    intro x
    have h : y x + y x⁻¹ = 0 := by
      have h1 := hy_add x x⁻¹
      rw [mul_inv_cancel, hy_one] at h1
      exact h1.symm
    refine (add_eq_zero_iff_eq_neg (a := y x⁻¹) (b := y x)).1 ?_
    rwa [add_comm]
  let Y : AddSubgroup (Fin 6 → ZMod 3) :=
    { carrier := Set.range y
      add_mem' := by
        rintro _ _ ⟨x₁, rfl⟩ ⟨x₂, rfl⟩
        exact ⟨x₁ * x₂, hy_add x₁ x₂⟩
      zero_mem' := ⟨1, hy_one⟩
      neg_mem' := by
        rintro _ ⟨x, rfl⟩
        exact ⟨x⁻¹, hy_neg x⟩ }
  have hy_inj : Function.Injective y := by
    intro x₁ x₂ h
    have hee : e x₁ = e x₂ := by
      funext i
      have hh := congrFun h (e6Idx.symm i)
      simpa [y] using hh
    have haa : a x₁ = a x₂ := by
      show zetaVec ζ hζ (e x₁) = zetaVec ζ hζ (e x₂)
      rw [hee]
    have ht : g₀⁻¹ * (x₁ : ModGL Tag.E6 Ω) * g₀ =
        g₀⁻¹ * (x₂ : ModGL Tag.E6 Ω) * g₀ := by
      rw [← he' x₁, ← he' x₂, haa]
    have hx : (x₁ : ModGL Tag.E6 Ω) = x₂ := by
      have h1 : g₀⁻¹ * (x₁ : ModGL Tag.E6 Ω) = g₀⁻¹ * (x₂ : ModGL Tag.E6 Ω) :=
        mul_right_cancel ht
      exact mul_left_cancel h1
    exact Subtype.ext hx
  have hYrange : (Y : Set (Fin 6 → ZMod 3)) = Set.range y := rfl
  have hy_bij : Function.Bijective (fun x : X => (⟨y x, ⟨x, rfl⟩⟩ : Y)) := by
    constructor
    · intro x₁ x₂ h
      exact hy_inj (congrArg Subtype.val h)
    · rintro ⟨z, hz⟩
      obtain ⟨x, hx⟩ := Set.mem_range.mp hz
      exact ⟨x, Subtype.ext hx⟩
  let eYX : X ≃ Y := Equiv.ofBijective (fun x : X => (⟨y x, ⟨x, rfl⟩⟩ : Y)) hy_bij
  have hcardY' : 3 ^ 4 ≤ Nat.card Y := by
    rw [← Nat.card_congr eYX]
    exact hcard
  have hfix : ∀ z ∈ Y, e6WeylMat u *ᵥ z = z := by
    intro z hz
    obtain ⟨x, rfl⟩ := Set.mem_range.mp hz
    exact hfix_y x
  have hkernel : familyKernel a = sigmaZ3 (Y : Set (Fin 6 → ZMod 3)) := by
    ext α
    simp only [familyKernel, sigmaZ3, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hα, h⟩
      refine ⟨hα, fun z hz => ?_⟩
      obtain ⟨x, rfl⟩ := Set.mem_range.mp hz
      rw [← rootChar_cubeTuple_eq_one_iff hζo (y x) α, ← ha_eq_cube x]
      exact h x
    · rintro ⟨hα, h⟩
      refine ⟨hα, fun x => ?_⟩
      rw [ha_eq_cube x, rootChar_cubeTuple_eq_one_iff hζo]
      exact h (y x) ⟨x, rfl⟩
  refine ⟨a, ?_, ?_, ?_⟩
  · intro x
    exact he' x
  · intro x
    exact ⟨e x, rfl⟩
  · rw [hkernel]
    exact hK Y hcardY' u hfix

end Book

end CFSG.StandardType.TwE6LemmaK
