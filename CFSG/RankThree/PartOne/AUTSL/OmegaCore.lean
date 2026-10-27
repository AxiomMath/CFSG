module

public import CFSG.RankThree.PartOne.AUTSL.OmegaGeom
public import CFSG.RankThree.PartOne.AUTSL.OmegaForm
public import CFSG.RankThree.PartOne.AUTSL.SemilinearGen
public import CFSG.RankThree.PartOne.AUTSL.DiagGen
public import CFSG.RankThree.PartOne.AUTSL.SylowTrick
public import CFSG.RankThree.PartOne.AUTSL.OmegaDiag

public section

namespace CFSG.RankThree.PartOne.AUTSL

open Matrix

section Main

theorem exists_primitive_root_five_of_pow_mod {K : Type} [Field K] [Finite K] {s : ℕ}
    (hs : Nat.card K = 2 ^ s) (h : 2 ^ s % 5 = 1) : ∃ ζ : K, IsPrimitiveRoot ζ 5 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h5 : 5 ∣ Fintype.card Kˣ := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hs]
    have : 2 ^ s ≥ 1 := Nat.one_le_two_pow
    omega
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 5 h5
  refine ⟨(x : K), ?_⟩
  have := IsPrimitiveRoot.orderOf (x : K)
  have hord : orderOf (x : K) = 5 := by
    rw [← hx]
    exact orderOf_units
  rwa [hord] at this

theorem exists_frobenius_inverting {K K' : Type} [Field K] [Finite K] [CharP K 2] [Field K']
    [Algebra K K'] [CharP K' 2] (hK5 : ¬ ∃ ζ : K, IsPrimitiveRoot ζ 5) :
    ∃ σ : K' →+* K', (∀ x : K, σ (algebraMap K K' x) = algebraMap K K' x) ∧
      ∀ y : K', y ^ 5 = 1 → σ y = y⁻¹ := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  set s : ℕ := (n : ℕ) with hsdef
  have hs : Nat.card K = 2 ^ s := by rw [Nat.card_eq_fintype_card, hn]
  have h1 : 2 ^ s % 5 ≠ 1 := fun h => hK5 (exists_primitive_root_five_of_pow_mod hs h)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (2 ^ s) ^ t % 5 = 4 := by
    have h2 : 2 ^ s % 5 = 2 ∨ 2 ^ s % 5 = 3 ∨ 2 ^ s % 5 = 4 := by
      have h0 : 2 ^ s % 5 ≠ 0 := by
        intro h
        have : 5 ∣ 2 ^ s := Nat.dvd_of_mod_eq_zero h
        have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) this)
        omega
      omega
    rcases h2 with h | h | h
    · exact ⟨2, by rw [sq, Nat.mul_mod, h]⟩
    · exact ⟨2, by rw [sq, Nat.mul_mod, h]⟩
    · exact ⟨1, by rw [pow_one, h]⟩
  have : ExpChar K' 2 := ExpChar.prime Nat.prime_two
  refine ⟨iterateFrobenius K' 2 (s * t), fun x => ?_, fun y hy => ?_⟩
  · rw [iterateFrobenius_def, ← map_pow, pow_mul]
    congr 1
    have hcard : Fintype.card K = 2 ^ s := hn
    rw [← hcard]
    exact FiniteField.pow_card_pow t x
  · rw [iterateFrobenius_def, pow_mul, pow_eq_pow_mod _ hy, ht]
    have h4 : y * y ^ 4 = 1 := by
      rw [← pow_succ']
      exact hy
    exact eq_inv_of_mul_eq_one_right h4


theorem exists_mul_ne_one_of_ne_inv {B X : Type*} [Group B] [CommGroup X] {a b : B →* X}
    (h : a ≠ b⁻¹) : ∃ x : B, a x * b x ≠ 1 := by
  by_contra hall
  push Not at hall
  apply h
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.inv_apply]
  exact eq_inv_of_mul_eq_one_left (hall x)

theorem omega_core {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι]
    [DecidableEq ι] (hcard : Fintype.card ι = 8) (Qf : QuadraticForm K (ι → K))
    (hQnd : (QuadraticMap.polarBilin Qf).Nondegenerate)
    (hWitt : ∀ T : Submodule K (ι → K), (∀ x ∈ T, Qf x = 0) → Module.finrank K T ≤ 3)
    {Γ : Subgroup (GL ι K)}
    (hΓQ : ∀ g ∈ Γ, ∀ v : ι → K, Qf (((g : GL ι K) : Matrix ι ι K) *ᵥ v) = Qf v)
    (hAut : ∀ α : MulAut Γ, ∃ (A : GL ι K) (σ : K ≃+* K), ∀ g : Γ,
      (((α g : Γ) : GL ι K) : Matrix ι ι K) = (A : Matrix ι ι K) *
        (((g : Γ) : GL ι K) : Matrix ι ι K).map σ * ((A⁻¹ : GL ι K) : Matrix ι ι K))
    {S : Subgroup Γ} (hS : IsPGroup 2 S)
    (𝒲 : Set (Submodule K (ι → K))) (h𝒲 : 𝒲.Nonempty)
    (h𝒲0 : ∀ W ∈ 𝒲, W ≠ ⊥) (h𝒲Q : ∀ W ∈ 𝒲, ∀ x ∈ W, Qf x = 0)
    (hJ : ∀ y : Γ, y ∈ Subgroup.normalizer (S : Set Γ) ↔
      ∀ W ∈ 𝒲, ∀ w ∈ W, (((y : Γ) : GL ι K) : Matrix ι ι K) *ᵥ w ∈ W)
    {E B : Subgroup Γ} (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE5 : ∀ x ∈ E, x ^ 5 = 1)
    (hBE : B ≤ E) (hBJ : B ≤ Subgroup.normalizer (S : Set Γ)) (hB : Nat.card B = 25)
    (α : MulAut Γ) (hαB : B.map α.toMonoidHom = B) (hα3 : ∀ b ∈ B, (α ^ 3) b = b)
    (hα1 : ∃ b ∈ B, α b ≠ b) (x : MulAut Γ) (hxB : ∀ b ∈ B, b⁻¹ * x b ∈ S) :
    E ≤ Subgroup.normalizer (S : Set Γ) ∧ ∀ e ∈ E, e⁻¹ * x e ∈ S := by
  classical
  let _ : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun a b => Subtype.ext (hEc a a.2 b b.2) }
  let _ : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b => Subtype.ext (hEc a (hBE a.2) b (hBE b.2)) }
  have hE5' : ∀ e : E, e ^ 5 = 1 := fun e => Subtype.ext (by simpa using hE5 e e.2)
  have hB5' : ∀ b : B, b ^ 5 = 1 := fun b => Subtype.ext (by simpa using hE5 b (hBE b.2))
  obtain ⟨J, hpolJ, hJs, hJu⟩ := exists_polar_matrix Qf hQnd
  obtain ⟨K', hF', hAlg, hFin, hChar, ζ, hζ, hflag⟩ : ∃ (K' : Type) (_ : Field K')
      (_ : Algebra K K') (_ : Finite K') (_ : CharP K' 2) (ζ : K'), IsPrimitiveRoot ζ 5 ∧
      (Function.Surjective (algebraMap K K') ∨ ¬ ∃ ζ₀ : K, IsPrimitiveRoot ζ₀ 5) := by
    by_cases h : ∃ ζ₀ : K, IsPrimitiveRoot ζ₀ 5
    · obtain ⟨ζ₀, hζ₀⟩ := h
      exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, ζ₀, hζ₀,
        Or.inl fun y => ⟨y, by simp⟩⟩
    · obtain ⟨K', hF', hAlg, hFin, hChar, ζ, hζ⟩ := exists_finite_extension_five K
      exact ⟨K', hF', hAlg, hFin, hChar, ζ, hζ, Or.inr h⟩
  let ρG : Γ →* Matrix ι ι K := (Units.coeHom _).comp Γ.subtype
  have hρG : ∀ g : Γ, ρG g = (((g : Γ) : GL ι K) : Matrix ι ι K) := fun g => rfl
  let ρ' : E →* Matrix ι ι K' :=
    (RingHom.mapMatrix (algebraMap K K')).toMonoidHom.comp (ρG.comp E.subtype)
  obtain ⟨P, f, hD'⟩ := exists_characters_gen hζ hE5' ρ'
  have hD : ∀ g : E, (P : Matrix ι ι K') * (ρG (g : Γ)).map (algebraMap K K') *
      ((P⁻¹ : GL ι K') : Matrix ι ι K') = Matrix.diagonal fun i => ((f i g : K'ˣ) : K') :=
    fun g => hD' g
  have hPPi : (P : Matrix ι ι K') * ((P⁻¹ : GL ι K') : Matrix ι ι K') = 1 := Units.mul_inv P
  have hPiP : ((P⁻¹ : GL ι K') : Matrix ι ι K') * (P : Matrix ι ι K') = 1 := Units.inv_mul P
  have hconjinj : ∀ X Y : Matrix ι ι K',
      (P : Matrix ι ι K') * X * ((P⁻¹ : GL ι K') : Matrix ι ι K') =
      (P : Matrix ι ι K') * Y * ((P⁻¹ : GL ι K') : Matrix ι ι K') → X = Y := fun X Y h => by
    calc X = (((P⁻¹ : GL ι K') : Matrix ι ι K') * (P : Matrix ι ι K')) * X *
          (((P⁻¹ : GL ι K') : Matrix ι ι K') * (P : Matrix ι ι K')) := by
          rw [hPiP, one_mul, mul_one]
      _ = ((P⁻¹ : GL ι K') : Matrix ι ι K') *
          ((P : Matrix ι ι K') * X * ((P⁻¹ : GL ι K') : Matrix ι ι K')) *
          (P : Matrix ι ι K') := by noncomm_ring
      _ = ((P⁻¹ : GL ι K') : Matrix ι ι K') *
          ((P : Matrix ι ι K') * Y * ((P⁻¹ : GL ι K') : Matrix ι ι K')) *
          (P : Matrix ι ι K') := by rw [h]
      _ = Y := by
        calc _ = (((P⁻¹ : GL ι K') : Matrix ι ι K') * (P : Matrix ι ι K')) * Y *
              (((P⁻¹ : GL ι K') : Matrix ι ι K') * (P : Matrix ι ι K')) := by noncomm_ring
          _ = Y := by rw [hPiP, one_mul, mul_one]
  have hmapinj : ∀ X Y : Γ,
      (ρG X).map (algebraMap K K') = (ρG Y).map (algebraMap K K') → X = Y := fun X Y h =>
    Subtype.ext (Units.ext (Matrix.map_injective (algebraMap K K').injective h))
  have hfaithE : ∀ g : E, (∀ i, f i g = 1) → g = 1 := fun g hg => by
    have h1 := hD g
    have h2 : (Matrix.diagonal fun i => ((f i g : K'ˣ) : K')) = 1 := by
      have : (fun i => ((f i g : K'ˣ) : K')) = fun _ => 1 := funext fun i => by rw [hg i]; rfl
      rw [this]
      exact Matrix.diagonal_one
    rw [h2] at h1
    have h3 := hconjinj _ 1 (by rw [h1, mul_one, hPPi])
    have h5 : (ρG (g : Γ)).map (algebraMap K K') = (ρG 1).map (algebraMap K K') := by
      rw [h3, map_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Subtype.ext (hmapinj _ _ h5)
  let ιB : B →* E := Subgroup.inclusion hBE
  have hfaithB : ∀ b : B, (∀ i, f i (ιB b) = 1) → b = 1 := fun b hb =>
    Subgroup.inclusion_injective hBE (by rw [hfaithE (ιB b) hb, map_one])
  have hαB' : ∀ b : B, α b ∈ B := fun b => by
    have : α b ∈ B.map α.toMonoidHom := ⟨b, b.2, rfl⟩
    rwa [hαB] at this
  have hαBinv : ∀ b : B, α⁻¹ b ∈ B := fun b => by
    have hb : (b : Γ) ∈ B.map α.toMonoidHom := by
      rw [hαB]
      exact b.2
    obtain ⟨c, hc, hcb⟩ := hb
    have : α⁻¹ b = c := by
      rw [← hcb]
      simp
    rw [this]
    exact hc
  let θ : MulAut B :=
    { toFun := fun b => ⟨α b, hαB' b⟩
      invFun := fun b => ⟨α⁻¹ b, hαBinv b⟩
      left_inv := fun b => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hθval : ∀ b : B, ((θ b : B) : Γ) = α b := fun b => rfl
  have hθ3 : θ ^ 3 = 1 := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    have h1 := hα3 b b.2
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h1 ⊢
    simpa [hθval] using h1
  have hθ1 : θ ≠ 1 := by
    intro h
    obtain ⟨b, hb, hne⟩ := hα1
    apply hne
    have := congrArg (fun φ : MulAut B => ((φ ⟨b, hb⟩ : B) : Γ)) h
    simpa [hθval] using this
  have hnorm : ∀ b, b * θ b * θ (θ b) = 1 := norm_eq_one_of_order_three hB θ hθ3 hθ1
  let J' : Matrix ι ι K' := J.map (algebraMap K K')
  let Pinv : Matrix ι ι K' := ((P⁻¹ : GL ι K') : Matrix ι ι K')
  let Qm : Matrix ι ι K' := Pinvᵀ * J' * Pinv
  have hJ'u : IsUnit J' := hJu.map (RingHom.mapMatrix (algebraMap K K')).toMonoidHom
  have hPinvu : IsUnit Pinv := (P⁻¹).isUnit
  have hPinvTu : IsUnit Pinvᵀ := by
    have h1 : Pinvᵀ * (P : Matrix ι ι K')ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hPPi, Matrix.transpose_one]
    have h2 : (P : Matrix ι ι K')ᵀ * Pinvᵀ = 1 := by
      rw [← Matrix.transpose_mul, hPiP, Matrix.transpose_one]
    exact ⟨⟨Pinvᵀ, (P : Matrix ι ι K')ᵀ, h1, h2⟩, rfl⟩
  have hQm : IsUnit Qm := (hPinvTu.mul hJ'u).mul hPinvu
  have hQs : Qmᵀ = Qm := by
    have hJ's : J'ᵀ = J' := by
      simp only [J']
      rw [← Matrix.transpose_map, hJs]
    simp only [Qm, Matrix.transpose_mul, Matrix.transpose_transpose, hJ's, Matrix.mul_assoc]
  have hQE : ∀ g : E, Qm * diagOf f g =
      Matrix.diagonal (fun i => (((f i g : K'ˣ) : K'))⁻¹) * Qm := fun g => by
    have hG := gram_of_isometry Qf J hpolJ (ρG (g : Γ)) (hΓQ _ (g : Γ).2)
    have hG' : ((ρG (g : Γ)).map (algebraMap K K'))ᵀ * J' * (ρG (g : Γ)).map (algebraMap K K') =
        J' := by
      rw [← Matrix.transpose_map]
      have := congrArg (fun M : Matrix ι ι K => M.map (algebraMap K K')) hG
      simpa only [Matrix.map_mul] using this
    have h1 := gram_rel J' ((ρG (g : Γ)).map (algebraMap K K')) (P : Matrix ι ι K') Pinv hPPi hPiP
      hG' (fun i => ((f i g : K'ˣ) : K')) (hD g)
    exact gram_rel_inv Qm (fun i => f i g) h1
  have hpolQ : ∀ v w : ι → K, algebraMap K K' (QuadraticMap.polar Qf v w) =
      ((P : Matrix ι ι K') *ᵥ (algebraMap K K' ∘ v)) ⬝ᵥ
        Qm *ᵥ ((P : Matrix ι ι K') *ᵥ (algebraMap K K' ∘ w)) := fun v w => by
    rw [hpolJ]
    exact polar_coord J P v w
  have hQrel : ∀ b : B, Qm * diagOf f (ιB b) =
      Matrix.diagonal (fun i => (((f i (ιB b) : K'ˣ) : K'))⁻¹) * Qm := fun b => hQE (ιB b)
  obtain ⟨A, σ, hform⟩ := hAut α
  obtain ⟨j₀, e₀, A₀, hA₀, he₀, hrel₀⟩ :=
    exists_E_relation_gen ρG E.subtype α A σ hform P f hD
  have hrelB : ∀ b : B, A₀ * Matrix.diagonal (fun i => (((f i (ιB b) : K'ˣ) : K') ^ e₀) ^ 2 ^ j₀) =
      diagOf f (ιB (θ b)) * A₀ := fun b => by
    refine (hrel₀ (ιB b)).symm.trans ?_
    show _ = (Matrix.diagonal fun i => ((f i (ιB (θ b)) : K'ˣ) : K')) * A₀
    rw [← hD (ιB (θ b))]
    rfl
  obtain ⟨χ₀, hχ₀, h0, hT1, hT2, hall, hinj0, hzcard⟩ := weights_of_relation_omega f ιB hcard hB
    hB5' hfaithB θ hθ3 hθ1 j₀ e₀ he₀ A₀ hA₀ hrelB Qm hQm hQrel
  have hm : ¬ 5 ∣ e₀ * 2 ^ j₀ := not_dvd_five_mul j₀ e₀ he₀
  obtain ⟨i₀, k₀, hik, hzset⟩ := Finset.card_eq_two.1 hzcard
  have hzero : ∀ i, (f i).comp ιB = 1 → i = i₀ ∨ i = k₀ := fun i hi => by
    have : i ∈ (Finset.univ.filter fun i => (f i).comp ιB = 1) := by simpa using hi
    rw [hzset] at this
    simpa using this
  have hi₀ : (f i₀).comp ιB = 1 := by
    have : i₀ ∈ (Finset.univ.filter fun i => (f i).comp ιB = 1) := by rw [hzset]; simp
    simpa using this
  have hk₀ : (f k₀).comp ιB = 1 := by
    have : k₀ ∈ (Finset.univ.filter fun i => (f i).comp ιB = 1) := by rw [hzset]; simp
    simpa using this
  have hz : ∀ i, (f i).comp ιB = 1 → f i = 1 := by
    intro i hi
    by_contra hne
    rcases hflag with hsurj | hK5
    ·
      obtain ⟨ia, hia⟩ := h0
      obtain ⟨ib, hib⟩ := hT1
      obtain ⟨ic, hic⟩ := hT2
      obtain ⟨hb1, hc1, hab, hac, hbc, hab', hac', hbc'⟩ :=
        six_orbit_facts hB5' θ hnorm (e₀ * 2 ^ j₀) hm hχ₀
      exact zero_class_false_R hsurj hE5' ιB (ρG.comp E.subtype) Qf
        (fun g v => hΓQ _ (g : Γ).2 v) hWitt P f hD hia hib hic hi hne hχ₀ hb1 hc1 hab hac
        hbc (exists_mul_ne_one_of_ne_inv hab') (exists_mul_ne_one_of_ne_inv hac')
        (exists_mul_ne_one_of_ne_inv hbc')
    ·
      have hK5' : ∀ y : K, y ^ 5 = 1 → y = 1 := by
        intro y hy
        by_contra hy1
        have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        exact hK5 ⟨y, by simpa [orderOf_eq_prime hy hy1] using IsPrimitiveRoot.orderOf y⟩
      obtain ⟨σ₁, hσK, hσ5⟩ := exists_frobenius_inverting (K := K) (K' := K') hK5
      obtain ⟨W, hW⟩ := h𝒲
      have : Fintype B := Fintype.ofFinite B
      have hB25 : Fintype.card B = 25 := by
        rw [← Nat.card_eq_fintype_card]
        exact hB
      have hWB : ∀ b : B, ∀ w ∈ W, (ρG.comp E.subtype) (ιB b) *ᵥ w ∈ W := fun b w hw =>
        (hJ (b : Γ)).1 (hBJ b.2) W hW w hw
      rcases hzero i hi with h | h
      · rw [h] at hne
        exact zero_class_false_N hE5' hB25 ιB (ρG.comp E.subtype) Qf
          (fun g v => hΓQ _ (g : Γ).2 v) hK5' σ₁ hσK hσ5 P f hD Qm hQs hQm hQE hpolQ hinj0 hik
          hi₀ hzero W (h𝒲0 W hW) (h𝒲Q W hW) hWB hne
      · rw [h] at hne
        exact zero_class_false_N hE5' hB25 ιB (ρG.comp E.subtype) Qf
          (fun g v => hΓQ _ (g : Γ).2 v) hK5' σ₁ hσK hσ5 P f hD Qm hQs hQm hQE hpolQ hinj0
          hik.symm hk₀ (fun i hi => (hzero i hi).symm) W (h𝒲0 W hW) (h𝒲Q W hW) hWB hne
  have hcls : ∀ g : E, ∀ i k, (f i).comp ιB = (f k).comp ιB → f i g = f k g := by
    intro g i k hik'
    by_cases h1 : (f i).comp ιB = 1
    · have hk1 : (f k).comp ιB = 1 := by rw [← hik']; exact h1
      rw [hz i h1, hz k hk1]
    · rw [hinj0 i k hik' h1]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hBp : IsPGroup 5 B := IsPGroup.of_card (n := 2) (by rw [hB]; norm_num)
  obtain ⟨sT, hsS, hs⟩ := exists_conj_eq_of_sylow_trick (p := 5) (q := 2) Nat.prime_two
    (by norm_num) hS hBp hBJ x hxB
  let x' : MulAut Γ := MulAut.conj sT⁻¹ * x
  have hx'B : ∀ b ∈ B, x' b = b := fun b hb => by
    simp only [x', MulAut.mul_apply, MulAut.conj_apply, hs b hb]
    group
  obtain ⟨A', σ', hform'⟩ := hAut x'
  obtain ⟨l, e', A₁, hA₁, he', hrel₁⟩ :=
    exists_E_relation_gen ρG E.subtype x' A' σ' hform' P f hD
  have hrelB' : ∀ b : B, A₁ * Matrix.diagonal (fun i => (((f i (ιB b) : K'ˣ) : K') ^ e') ^ 2 ^ l) =
      diagOf f (ιB b) * A₁ := fun b => by
    refine (hrel₁ (ιB b)).symm.trans ?_
    show _ = (Matrix.diagonal fun i => ((f i (ιB b) : K'ˣ) : K')) * A₁
    rw [← hD (ιB b)]
    have h2 : x' (E.subtype (ιB b)) = E.subtype (ιB b) := hx'B _ b.2
    rw [h2]
    rfl
  have hall' := fun e₁ : E => fixes_of_relation_omega f ιB hB5' hE5' θ hnorm (e₀ * 2 ^ j₀) hm
    hχ₀ h0 hall Qm hQm hQE l e' he' A₁ hA₁ hrelB' e₁ (hcls e₁)
  have hfix : ∀ g : E, x' (g : Γ) = g := fun g => by
    have h3 := hrel₁ g
    have h4 := hall' g
    have h5 := hD g
    have h6 : (P : Matrix ι ι K') * (ρG (x' (g : Γ))).map (algebraMap K K') *
        ((P⁻¹ : GL ι K') : Matrix ι ι K') * A₁ =
        ((P : Matrix ι ι K') * (ρG (g : Γ)).map (algebraMap K K') *
          ((P⁻¹ : GL ι K') : Matrix ι ι K')) * A₁ := by
      refine h3.trans (h4.trans ?_)
      rw [h5]
      rfl
    exact hmapinj _ _ (hconjinj _ _ ((hA₁.mul_left_inj).1 h6))
  have hEJ : ∀ g : E, (g : Γ) ∈ Subgroup.normalizer (S : Set Γ) := fun g => by
    rw [hJ]
    intro W hW
    have hdesc := rho_mem_span_cls (ρG.comp E.subtype) ιB P f hD g (hcls g)
    let St : Submodule K (Matrix ι ι K) :=
      { carrier := {M | ∀ w ∈ W, M *ᵥ w ∈ W}
        add_mem' := fun {M N} hM hN w hw => by
          rw [Matrix.add_mulVec]
          exact W.add_mem (hM w hw) (hN w hw)
        zero_mem' := fun w hw => by simp
        smul_mem' := fun c M hM w hw => by
          rw [Matrix.smul_mulVec]
          exact W.smul_mem c (hM w hw) }
    have hle : Submodule.span K (Set.range fun b : B => (ρG.comp E.subtype) (ιB b)) ≤ St := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      exact (hJ _).1 (hBJ b.2) W hW
    exact hle hdesc
  refine ⟨fun g hg => hEJ ⟨g, hg⟩, fun e he => ?_⟩
  have hx'e : x' e = e := hfix ⟨e, he⟩
  have hxe : x e = sT * e * sT⁻¹ := by
    simp only [x', MulAut.mul_apply, MulAut.conj_apply] at hx'e
    calc x e = sT * (sT⁻¹ * x e * sT⁻¹⁻¹) * sT⁻¹ := by group
      _ = sT * e * sT⁻¹ := by rw [hx'e]
  rw [hxe]
  have hsconj : e⁻¹ * sT * e ∈ S := by
    have := (Subgroup.mem_normalizer_iff.1
      ((Subgroup.normalizer (S : Set Γ)).inv_mem (hEJ ⟨e, he⟩)) sT).1 hsS
    simpa using this
  have hrw : e⁻¹ * (sT * e * sT⁻¹) = (e⁻¹ * sT * e) * sT⁻¹ := by group
  rw [hrw]
  exact S.mul_mem hsconj (S.inv_mem hsS)

end Main

end CFSG.RankThree.PartOne.AUTSL
