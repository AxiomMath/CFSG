module

public import CFSG.RankThree.GF2n.Smith81.TiD3KForm
public import CFSG.Quasithin.Background.Harris.L2.Numerics

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.D3
open scoped MatrixGroups

theorem d_eq_of_mul_two_pow {f d : ℕ} (hf : 1 ≤ f) (hd : 1 ≤ d) {J : Finset ℕ}
    (hJne : J.Nonempty) (hJn : ∀ i ∈ J, i < 3 * f)
    (hshift : J.image (fun i => (i + d) % (3 * f)) = J)
    (h : d * 2 ^ J.card = 8 * f) : d = f := by
  classical
  have hnpos : 0 < 3 * f := by omega
  set g := Nat.gcd (3 * f) d with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left d hnpos
  have hgn : g ∣ 3 * f := Nat.gcd_dvd_left _ _
  have hgd : g ∣ d := Nat.gcd_dvd_right _ _
  have hgle : g ≤ d := Nat.le_of_dvd hd hgd
  obtain ⟨e, he⟩ := hgd
  set m := (3 * f) / g with hm
  have hmul : m * g = 3 * f := Nat.div_mul_cancel hgn
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, zero_mul] at hmul
      omega
    · exact h0
  have hle := CFSG.Quasithin.G11.Harris.L2.le_card_mul_gcd hnpos hJne hJn hshift
  have hgm : m ≤ J.card := by
    have h' : m * g ≤ J.card * g := by rw [hmul]; exact hle
    exact Nat.le_of_mul_le_mul_right h' hg0
  have hpow : 2 ^ m ≤ 2 ^ J.card := Nat.pow_le_pow_right (by norm_num) hgm
  have h1 : g * 2 ^ m ≤ 8 * f := by
    calc g * 2 ^ m ≤ g * 2 ^ J.card := Nat.mul_le_mul_left g hpow
      _ ≤ d * 2 ^ J.card := Nat.mul_le_mul_right _ hgle
      _ = 8 * f := h
  have h2 : 3 * f * 2 ^ m ≤ 8 * f * m := by
    calc 3 * f * 2 ^ m = (m * g) * 2 ^ m := by rw [hmul]
      _ = (g * 2 ^ m) * m := by ring
      _ ≤ (8 * f) * m := Nat.mul_le_mul_right m h1
      _ = 8 * f * m := by ring
  have h3 : 3 * 2 ^ m ≤ 8 * m := by
    have h2' : f * (3 * 2 ^ m) ≤ f * (8 * m) := by
      calc f * (3 * 2 ^ m) = 3 * f * 2 ^ m := by ring
        _ ≤ 8 * f * m := h2
        _ = f * (8 * m) := by ring
    exact Nat.le_of_mul_le_mul_left h2' (by omega : 0 < f)
  have hm3 : m ≤ 3 := by
    by_contra hcon
    have h4le : 4 ≤ m := by omega
    have h4 := CFSG.Quasithin.G11.Harris.L2.four_mul_le_two_pow h4le
    nlinarith
  have hkey : 3 * e * 2 ^ J.card = 8 * m := by
    have h1' : 3 * (d * 2 ^ J.card) = 3 * (8 * f) := by rw [h]
    have h1'' : 3 * d * 2 ^ J.card = 8 * (3 * f) := by
      calc 3 * d * 2 ^ J.card = 3 * (d * 2 ^ J.card) := by ring
        _ = 3 * (8 * f) := h1'
        _ = 8 * (3 * f) := by ring
    have h2' : 3 * (g * e) * 2 ^ J.card = 8 * (m * g) := by
      rw [he, ← hmul] at h1''
      exact h1''
    have h3' : (3 * e * 2 ^ J.card) * g = (8 * m) * g := by
      calc (3 * e * 2 ^ J.card) * g = 3 * (g * e) * 2 ^ J.card := by ring
        _ = 8 * (m * g) := h2'
        _ = (8 * m) * g := by ring
    exact Nat.eq_of_mul_eq_mul_right hg0 h3'
  have hdvd : 3 ∣ 8 * m := ⟨e * 2 ^ J.card, by rw [← mul_assoc, hkey]⟩
  have hm_cases : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm_cases with hm1 | hm2 | hm3'
  · exfalso
    rw [hm1] at hdvd
    exact (by norm_num : ¬ (3 ∣ 8 * 1)) hdvd
  · exfalso
    rw [hm2] at hdvd
    exact (by norm_num : ¬ (3 ∣ 8 * 2)) hdvd
  · have heq : e * 2 ^ J.card = 8 := by
      have h3' : 3 * (e * 2 ^ J.card) = 3 * 8 := by
        rw [← mul_assoc, hkey, hm3']
      exact Nat.mul_left_cancel (by norm_num : 0 < 3) h3'
    have hg3 : 3 ≤ J.card := by rw [← hm3']; exact hgm
    have hpow8 : 8 ≤ 2 ^ J.card := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ J.card := Nat.pow_le_pow_right (by norm_num) hg3
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · rw [h0, mul_zero] at he
        omega
      · exact h0
    have he_le : e ≤ 1 := by
      have hle' : e * 2 ^ J.card ≤ 1 * 2 ^ J.card := by
        rw [one_mul]
        calc e * 2 ^ J.card = 8 := heq
          _ ≤ 2 ^ J.card := hpow8
      exact Nat.le_of_mul_le_mul_right hle' (pow_pos (by norm_num) _)
    have he1' : e = 1 := by omega
    have hg_eq : g = f := by
      have hg3' : 3 * g = 3 * f := by
        have h := hmul
        rw [hm3'] at h
        exact h
      exact Nat.mul_left_cancel (by norm_num : 0 < 3) hg3'
    rw [he, he1', mul_one, hg_eq]

private noncomputable def repDField {F W : Type*} [Field F] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) SL(2, F) W)
    [Field (EndRing ρ)] : Representation (EndRing ρ) SL(2, F) W :=
  repD ρ

private theorem repD_isIrreducible {F W : Type*} [Field F] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible] :
    (repDField ρ).IsIrreducible := by
  rw [isIrreducible_iff]
  obtain ⟨hnt, hirr⟩ := (isIrreducible_iff ρ).mp Fact.out
  refine ⟨hnt, fun U hU => ?_⟩
  let N : Submodule (ZMod 2) W := U.restrictScalars (ZMod 2)
  have hN : ∀ g, ∀ u ∈ N, ρ g u ∈ N := by
    intro g u hu
    show ρ g u ∈ U
    simpa [repDField, repD_apply] using hU g u hu
  rcases hirr N hN with h | h
  · left
    exact (Submodule.restrictScalars_eq_bot_iff (ZMod 2) (EndRing ρ) W).mp h
  · right
    exact (Submodule.restrictScalars_eq_top_iff (ZMod 2) (EndRing ρ) W).mp h

private theorem repD_nontrivial {F W : Type*} [Field F] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) SL(2, F) W) (hnt : ∃ g, ρ g ≠ 1) :
    ∃ g, repD ρ g ≠ 1 := by
  obtain ⟨g, hg⟩ := hnt
  refine ⟨g, fun h => hg ?_⟩
  apply LinearMap.ext
  intro w
  have h1 := congrArg (fun f : Module.End (EndRing ρ) W => f w) h
  simpa [repD_apply] using h1

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

@[expose] def hypMap (ψ : F ≃+* F) (x : Hyp F) : Hyp F := fun i j k => ψ (x i j k)

theorem hypMap_add (ψ : F ≃+* F) (x y : Hyp F) :
    hypMap ψ (x + y) = hypMap ψ x + hypMap ψ y := by
  funext i j k
  simp [hypMap]

theorem hypMap_mem_kForm {K K' : Type} [Field K] [Field K'] [Algebra K F] [Algebra K' F]
    (τ : F →ₐ[K] F) (τ' : F →ₐ[K'] F) (ψ : F ≃+* F)
    (hψ : ∀ a, ψ (τ a) = τ' (ψ a)) {x : Hyp F} (hx : x ∈ kForm τ) :
    hypMap ψ x ∈ kForm τ' := by
  intro i j k
  show ψ (x k i j) = τ' (ψ (x i j k))
  rw [hx i j k]
  exact hψ (x i j k)

theorem hypMap_mem_kForm_symm {K K' : Type} [Field K] [Field K'] [Algebra K F] [Algebra K' F]
    (τ : F →ₐ[K] F) (τ' : F →ₐ[K'] F) (ψ : F ≃+* F)
    (hψ : ∀ a, ψ (τ a) = τ' (ψ a)) {y : Hyp F} (hy : y ∈ kForm τ') :
    hypMap ψ.symm y ∈ kForm τ := by
  have hsymm : ∀ a, ψ.symm (τ' a) = τ (ψ.symm a) := by
    intro a
    apply ψ.injective
    rw [RingEquiv.apply_symm_apply, hψ, RingEquiv.apply_symm_apply]
  intro i j k
  show ψ.symm (y k i j) = τ (ψ.symm (y i j k))
  rw [hy i j k]
  exact hsymm (y i j k)

@[expose] noncomputable def kFormEquiv {K K' : Type} [Field K] [Field K'] [Algebra K F]
    [Algebra K' F] (τ : F →ₐ[K] F) (τ' : F →ₐ[K'] F) (ψ : F ≃+* F)
    (hψ : ∀ a, ψ (τ a) = τ' (ψ a)) : ↥(kForm τ) ≃+ ↥(kForm τ') where
  toFun x := ⟨hypMap ψ x.1, hypMap_mem_kForm τ τ' ψ hψ x.2⟩
  invFun y := ⟨hypMap ψ.symm y.1, hypMap_mem_kForm_symm τ τ' ψ hψ y.2⟩
  left_inv x := by
    apply Subtype.ext
    show hypMap ψ.symm (hypMap ψ x.1) = x.1
    funext i j k
    simp [hypMap]
  right_inv y := by
    apply Subtype.ext
    show hypMap ψ (hypMap ψ.symm y.1) = y.1
    funext i j k
    simp [hypMap]
  map_add' x y := by
    apply Subtype.ext
    exact hypMap_add ψ x.1 y.1

theorem hypMap_act {K K' : Type} [Field K] [Field K'] [Algebra K F] [Algebra K' F]
    (τ : F →ₐ[K] F) (τ' : F →ₐ[K'] F) (ψ : F ≃+* F)
    (hψτ : ∀ a, ψ ((τ : F →+* F) a) = (τ' : F →+* F) (ψ a))
    (σ σ' : F ≃+* F) (hψσ : ∀ a, ψ (σ a) = σ' a)
    (g : SL(2, F)) (x : Hyp F) :
    hypMap ψ (act (τ : F →+* F) ((D2.slMap σ g : SL(2, F)) : Mat2 F) x) =
      act (τ' : F →+* F) ((D2.slMap σ' g : SL(2, F)) : Mat2 F) (hypMap ψ x) := by
  funext i j k
  simp only [act, hypMap, map_sum, map_mul, D2.coe_slMap]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ =>
    Finset.sum_congr rfl fun k' _ => ?_
  rw [hψτ ((τ : F →+* F) (σ ((g : Mat2 F) k k'))), hψτ (σ ((g : Mat2 F) k k')),
    hψτ (σ ((g : Mat2 F) j j'))]
  simp only [hψσ]

theorem card_endRing_eq_of_card_eq_two_pow_eight_mul {F : Type} [Field F] [Fintype F] [CharP F 2]
    {f : ℕ} (hf : 1 ≤ f) (hF : Fintype.card F = 2 ^ (3 * f)) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) SL(2, F) W)
    [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1) (hW : Nat.card W = 2 ^ (8 * f)) :
    Nat.card (EndRing ρ) = 2 ^ f := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ :=
    binary_SL2_irreducible_Frobenius_descent (n := 3 * f) (by omega) hF ρ hnt
  have hfinW : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  let b := Module.finBasis (EndRing ρ) W
  obtain ⟨K, hKF, hKfin, hKchar, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ := hdesc b
  have hWcard : Nat.card W = 2 ^ (d * 2 ^ J.card) := by
    have h1 := natCard_eq_pow_finrank (ρ := ρ)
    rw [hDcard, hdim, ← pow_mul] at h1
    exact h1
  have hexp : d * 2 ^ J.card = 8 * f :=
    Nat.pow_right_injective (a := 2) (by norm_num) (by
      change 2 ^ (d * 2 ^ J.card) = 2 ^ (8 * f)
      rw [← hWcard, hW])
  have hd : d = f := d_eq_of_mul_two_pow hf hd1 hJne hJn hshift hexp
  rw [hDcard, hd]

theorem exists_kForm_model {F : Type} [Field F] [Fintype F] [CharP F 2] {f : ℕ} (hf : 2 ≤ f)
    (hF : Fintype.card F = 2 ^ (3 * f)) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1)
    (hW : Nat.card W = 2 ^ (8 * f)) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra K F),
      Fintype.card K = 2 ^ f ∧
      ∃ (σ : F ≃+* F) (β : W ≃+ ↥(kForm (FiniteField.frobeniusAlgHom K F))),
        ∀ g w, ((β (ρ g w) : ↥(kForm (FiniteField.frobeniusAlgHom K F))) : Hyp F) =
          act (FiniteField.frobeniusAlgHom K F : F →+* F)
            ((D2.slMap σ g : SL(2, F)) : Mat2 F) (β w : Hyp F) := by
  classical
  have hf1 : 1 ≤ f := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (GaloisField 2 f) := inferInstanceAs (Finite (GaloisField 2 f))
  haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite (GaloisField 2 f)
  have hKcard : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 f (by omega)
  have hKnat : Nat.card (GaloisField 2 f) = 2 ^ f := by
    rw [Nat.card_eq_fintype_card]
    exact hKcard
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  haveI : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  letI : Algebra (ZMod 2) (GaloisField 2 f) := instAlgebraZModGaloisField 2 f
  have hfrK : Module.finrank (ZMod 2) (GaloisField 2 f) = f :=
    GaloisField.finrank 2 (n := f) (by omega)
  have hfrF : Module.finrank (ZMod 2) F = 3 * f := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [Nat.card_eq_fintype_card, hF, Nat.card_zmod] at h1
    exact (Nat.pow_right_injective (a := 2) (by norm_num) h1).symm
  obtain ⟨ιGF⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2)
    (K := GaloisField 2 f) (L := F)
    (by rw [hfrK, hfrF]; exact Dvd.intro_left 3 rfl)
  let algK : Algebra (GaloisField 2 f) F := ιGF.toRingHom.toAlgebra
  letI : Algebra (GaloisField 2 f) F := algK
  have hcardFK : Fintype.card F = Fintype.card (GaloisField 2 f) ^ 3 := by
    rw [hF, hKcard, ← pow_mul]
    congr 1
    ring
  have hKE : Nat.card (EndRing ρ) = 2 ^ f :=
    card_endRing_eq_of_card_eq_two_pow_eight_mul hf1 hF ρ hnt hW
  letI : Field (EndRing ρ) :=
    { endRingField ρ with toSemiring := Module.End.instSemiring }
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  haveI : Fintype (EndRing ρ) := Fintype.ofFinite _
  have hKEfc : Fintype.card (EndRing ρ) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact hKE
  have hcardE : Fintype.card (EndRing ρ) = Fintype.card (GaloisField 2 f) := by
    rw [hKEfc, hKcard]
  let eρ := FiniteField.ringEquivOfCardEq hcardE
  letI : Module (GaloisField 2 f) W := Module.compHom W eρ.symm.toRingHom
  let ρK : Representation (GaloisField 2 f) SL(2, F) W :=
    { toFun := fun g =>
        { toFun := fun w => repD ρ g w
          map_add' := fun x y => map_add (repD ρ g) x y
          map_smul' := fun k w => by
            change repD ρ g (eρ.symm k • w) = eρ.symm k • repD ρ g w
            exact (repD ρ g).map_smul (eρ.symm k) w }
      map_one' := by
        apply LinearMap.ext
        intro w
        simp
      map_mul' g h := by
        apply LinearMap.ext
        intro w
        simp [map_mul] }
  have hρK_irr : ρK.IsIrreducible := by
    rw [isIrreducible_iff]
    obtain ⟨hntD, hirrD⟩ := (isIrreducible_iff (repDField ρ)).mp (repD_isIrreducible ρ)
    refine ⟨hntD, fun U hU => ?_⟩
    let U' : Submodule (EndRing ρ) W :=
      { carrier := U
        add_mem' := U.add_mem
        zero_mem' := U.zero_mem
        smul_mem' := fun a w hw => by
          have h : (eρ a) • w ∈ U := U.smul_mem (eρ a) hw
          have h' : (eρ a) • w = a • w := by
            show eρ.symm (eρ a) • w = a • w
            simp
          rwa [h'] at h }
    have hU' : ∀ g, ∀ u ∈ U', repDField ρ g u ∈ U' := fun g u hu => hU g u hu
    rcases hirrD U' hU' with h | h
    · left
      apply Submodule.ext
      intro w
      change w ∈ U' ↔ w ∈ (⊥ : Submodule (EndRing ρ) W)
      rw [h]
    · right
      apply Submodule.ext
      intro w
      change w ∈ U' ↔ w ∈ (⊤ : Submodule (EndRing ρ) W)
      rw [h]
  have hntK : ∃ g, ρK g ≠ 1 := by
    obtain ⟨g, hg⟩ := repD_nontrivial ρ hnt
    refine ⟨g, fun h => hg ?_⟩
    apply LinearMap.ext
    intro w
    have h1 : (ρK g) w = w := congrArg (fun f : Module.End (GaloisField 2 f) W => f w) h
    change ρ g w = w
    exact h1
  haveI : Module.Finite (GaloisField 2 f) W := Module.Finite.of_finite
  have hdimK : Module.finrank (GaloisField 2 f) W = 8 := by
    have h1 := Module.natCard_eq_pow_finrank (K := GaloisField 2 f) (V := W)
    rw [hW, hKnat, ← pow_mul] at h1
    have h2 : 8 * f = f * Module.finrank (GaloisField 2 f) W :=
      Nat.pow_right_injective (a := 2) (by norm_num) h1
    have h3 : f * Module.finrank (GaloisField 2 f) W = f * 8 := by rw [← h2]; ring
    exact Nat.mul_left_cancel (by omega : 0 < f) h3
  haveI : Fact ρK.IsIrreducible := ⟨hρK_irr⟩
  obtain ⟨σ, θ, hθ⟩ :=
    CFSG.RankThree.GF2n.Stroth80.SL2Descent.exists_kForm_equiv (K := GaloisField 2 f) (F := F)
      (k := f) hKcard hf hcardFK hdimK ρK hntK
  refine ⟨GaloisField 2 f, inferInstance, inferInstance, algK, hKcard, σ, θ.toAddEquiv, ?_⟩
  intro g w
  exact hθ g w

theorem exists_equiv_of_card_eq_two_pow_eight_mul {F : Type} [Field F] [Fintype F] [CharP F 2]
    {f : ℕ} (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ (3 * f))
    {W W' : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [AddCommGroup W'] [Module (ZMod 2) W'] [Finite W']
    (ρ : Representation (ZMod 2) SL(2, F) W) (ρ' : Representation (ZMod 2) SL(2, F) W')
    [Fact ρ.IsIrreducible] [Fact ρ'.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1) (hnt' : ∃ g, ρ' g ≠ 1)
    (hW : Nat.card W = 2 ^ (8 * f)) (hW' : Nat.card W' = 2 ^ (8 * f)) :
    ∃ e : W ≃ₗ[ZMod 2] W', ∀ g w, e (ρ g w) = ρ' g (e w) := by
  classical
  obtain ⟨K, hKfield, hKfin, hKalg, hKcard, σ, β, hβ⟩ :=
    exists_kForm_model hf hF ρ hnt hW
  obtain ⟨K', hK'field, hK'fin, hK'alg, hK'card, σ', β', hβ'⟩ :=
    exists_kForm_model hf hF ρ' hnt' hW'
  letI : Field K := hKfield
  letI : Fintype K := hKfin
  letI : Algebra K F := hKalg
  letI : Field K' := hK'field
  letI : Fintype K' := hK'fin
  letI : Algebra K' F := hK'alg
  let τ : F →ₐ[K] F := FiniteField.frobeniusAlgHom K F
  let τ' : F →ₐ[K'] F := FiniteField.frobeniusAlgHom K' F
  have hτfun : ∀ a : F, τ a = a ^ (2 ^ f) := by
    intro a
    rw [show τ a = (FiniteField.frobeniusAlgHom K F) a from rfl,
      FiniteField.frobeniusAlgHom_apply, hKcard]
  have hτ'fun : ∀ a : F, τ' a = a ^ (2 ^ f) := by
    intro a
    rw [show τ' a = (FiniteField.frobeniusAlgHom K' F) a from rfl,
      FiniteField.frobeniusAlgHom_apply, hK'card]
  let ψ : F ≃+* F := σ.symm.trans σ'
  have hψσ : ∀ a : F, ψ (σ a) = σ' a := by
    intro a
    rw [show ψ (σ a) = (σ.symm.trans σ') (σ a) from rfl, RingEquiv.trans_apply]
    simp
  have hψτ : ∀ a : F, ψ (τ a) = τ' (ψ a) := by
    intro a
    rw [hτfun a, hτ'fun (ψ a), map_pow]
  let eTwist : ↥(kForm τ) ≃+ ↥(kForm τ') := kFormEquiv τ τ' ψ hψτ
  let eAdd : W ≃+ W' := (β.trans eTwist).trans β'.symm
  refine ⟨eAdd.toLinearEquiv (fun c x => ZMod.map_smul eAdd c x), ?_⟩
  intro g w
  have heAdd_apply : ∀ w, eAdd w = β'.symm (eTwist (β w)) := fun w => rfl
  have h2 : (β' (eAdd w)).1 = hypMap ψ ((β w).1) := by
    rw [heAdd_apply, AddEquiv.apply_symm_apply]
    show (eTwist (β w)).1 = hypMap ψ ((β w).1)
    rfl
  have hL : (β' (eAdd (ρ g w))).1 =
      act (τ' : F →+* F) ((D2.slMap σ' g : SL(2, F)) : Mat2 F) (hypMap ψ ((β w).1)) := by
    have h1 : β' (eAdd (ρ g w)) = eTwist (β (ρ g w)) := by
      rw [heAdd_apply, AddEquiv.apply_symm_apply]
    rw [h1]
    show hypMap ψ ((β (ρ g w)).1) =
      act (τ' : F →+* F) ((D2.slMap σ' g : SL(2, F)) : Mat2 F) (hypMap ψ ((β w).1))
    rw [hβ g w]
    exact hypMap_act τ τ' ψ (fun a => hψτ a) σ σ' hψσ g ((β w).1)
  have hR : (β' (ρ' g (eAdd w))).1 =
      act (τ' : F →+* F) ((D2.slMap σ' g : SL(2, F)) : Mat2 F) (hypMap ψ ((β w).1)) := by
    rw [hβ' g (eAdd w), h2]
  have hEq : β' (eAdd (ρ g w)) = β' (ρ' g (eAdd w)) := Subtype.ext (hL.trans hR.symm)
  exact β'.injective hEq

end CFSG.Quasithin.F112R.St84
