module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutSL
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5
import CFSG.RankThree.PartOne.U5K.Kf.Assist
import CFSG.RankThree.PartOne.U5K.Kf.Std
import CFSG.RankThree.PartOne.U5K.Kf.Atil
import CFSG.RankThree.PartOne.U5K.Kf.Diagz

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.PartOne.U5K.Kf CFSG.RankThree.PartOne.KCEvenUnitaryFiveBridge

section Model

variable {n : ℕ} {K : Type} [Field K]

private theorem u5_frame (h : UnitaryFieldData 2 n K) (h5 : 5 ∣ 2 ^ n + 1) [Fact (Nat.Prime 5)]
    (V : Subgroup (MulAut (primeFormP h (idGram K 5)))) (hV : IsElementaryAbelian 5 ↥V)
    (hVc : Nat.card V = 5 ^ 4) (hD : V ≤ primeFormD h (idGram K 5)) :
    ∃ (Z : ZetaData h 5) (P : primeFormUnitary h (idGram K 5)),
      ∀ a : Fin 5 → ZMod 5, Z.par P a ∈ V := by
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot h (by norm_num) h5
  let Z : ZetaData h 5 := ⟨ζ, hζ, h5, le_rfl⟩
  have hcard : 5 ^ 3 ≤ Nat.card V := by rw [hVc]; norm_num
  obtain ⟨P, hP⟩ := Z.exists_diagonalizing hV hcard hD
  refine ⟨Z, P, fun a => ?_⟩
  have h1 := Z.card_Atil P hV hD hP
  have h2 : Nat.card (Z.Atil P V) = Nat.card (VM 5) := by
    rw [h1, hVc]
    simp [VM]
  have h3 : Z.Atil P V = ⊤ := Subgroup.eq_top_of_card_eq _ h2
  have h4 : Multiplicative.ofAdd a ∈ Z.Atil P V := by rw [h3]; exact Subgroup.mem_top _
  exact (Z.mem_Atil P V a).1 h4

private theorem u5_le_D (h : UnitaryFieldData 2 n K) (h5n : ¬ 5 ∣ n)
    (V : Subgroup (MulAut (primeFormP h (idGram K 5)))) (hV : ∀ x ∈ V, x ^ 5 = 1) :
    V ≤ primeFormD h (idGram K 5) := by
  have := h.finite
  have hG := CFSG.RankThree.PartTwo.Sec4.isPrimeFormGram_one_GL (n := 5) (K := K)
  intro α hα
  rw [← ker_primeFormFieldFactor h hG (by norm_num) (by omega), MonoidHom.mem_ker]
  have h1 : primeFormFieldFactor h hG (by norm_num) (by omega) α ^ 5 = 1 := by
    rw [← map_pow, hV α hα, map_one]
  have h2 : primeFormFieldFactor h hG (by norm_num) (by omega) α ^ (2 * n) = 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.ringEquiv_pow_eq_one h.prime (by rw [h.card]) _
  have hcop : Nat.Coprime 5 (2 * n) :=
    Nat.Coprime.mul_right (by norm_num) ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5n)
  have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rwa [hcop.gcd_eq_one, pow_one] at h3

private theorem u5_commute_transport (h : UnitaryFieldData 2 n K)
    (P X : primeFormUnitary h (idGram K 5)) (μ : Fin 5 → K)
    (hd : (((P⁻¹ * X * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = diagonal μ)
    (ι : HypIndex 2 1 ≃ Fin 5) {u c : K}
    (h0 : μ (ι (.inl 0)) = μ (ι (.inr (.inr 0)))) (h1 : μ (ι (.inl 1)) = μ (ι (.inr (.inr 1))))
    (R : Matrix (Fin (2 * 2 + 1)) (HypIndex 2 1) K) (hR : IsHypTransport (r := 2) (ε := 1) h R)
    (hRdef : R = ((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * wmat ι u c)
    {g : GL (HypIndex 2 1) K} {q : HypIndex 2 1 → K}
    (hg : (g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = diagonal q) :
    ((X : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((transportGL hR g : GL (Fin (2 * 2 + 1)) K) : Matrix (Fin 5) (Fin 5) K) =
      ((transportGL hR g : GL (Fin (2 * 2 + 1)) K) : Matrix (Fin 5) (Fin 5) K) *
        ((X : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
  classical
  let s : HypIndex 2 1 → K := fun y => match y with
    | .inl a => μ (ι (.inl a))
    | .inr (.inl k) => μ (ι (.inr (.inl k)))
    | .inr (.inr a) => μ (ι (.inl a))
  have hs : ∀ y, ((X : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ (R *ᵥ Pi.single y 1) =
      s y • (R *ᵥ Pi.single y 1) := by
    intro y
    rw [hRdef, col_eq_mul_wvec]
    rcases y with a | k | a
    · fin_cases a
      · exact eigen_of_diag h hd _ _ (diag_mulVec_wvec_inl ι u c μ 0 h0)
      · exact eigen_of_diag h hd _ _ (diag_mulVec_wvec_inl ι u c μ 1 h1)
    · exact eigen_of_diag h hd _ _ (diag_mulVec_wvec_inr_inl ι u c μ k)
    · fin_cases a
      · exact eigen_of_diag h hd _ _ (diag_mulVec_wvec_inr_inr ι u c μ 0 h0)
      · exact eigen_of_diag h hd _ _ (diag_mulVec_wvec_inr_inr ι u c μ 1 h1)
  have hdiag := transport_eq_diagonal h hR s hs
  have hX : ((X : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      R * diagonal s * transportInv h R := by
    rw [← hdiag, transport_transportInv hR]
  rw [coe_transportGL, hg, hX]
  have hRR' : transportInv h R * R = 1 := transportInv_mul hR
  calc R * diagonal s * transportInv h R * (R * diagonal q * transportInv h R)
      = R * (diagonal s * diagonal q) * transportInv h R := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (transportInv h R) R, hRR', Matrix.one_mul]
    _ = R * (diagonal q * diagonal s) * transportInv h R := by
        rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 3
        funext x
        exact mul_comm _ _
    _ = R * diagonal q * transportInv h R * (R * diagonal s * transportInv h R) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (transportInv h R) R, hRR', Matrix.one_mul]

private theorem u5_outer_pair_model (h : UnitaryFieldData 2 n K) (h5 : 5 ∣ 2 ^ n + 1)
    (h5n : ¬ 5 ∣ n) {r : ℕ} (hr : r.Prime) (hr5 : r ≠ 5) (hrn : r ∣ 2 ^ n - 1)
    (V : Subgroup (MulAut (primeFormP h (idGram K 5)))) (hV : IsElemAbelian 5 V)
    (hVc : Nat.card V = 5 ^ 4) :
    ∃ (E : Subgroup (primeFormP h (idGram K 5)))
      (Q : Subgroup (MulAut (primeFormP h (idGram K 5)))),
      IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ V ∧ IsElemAbelian 5 Q ∧
        Nat.card Q = 5 ^ 2 ∧ ∀ α ∈ Q, ∀ e ∈ E, α e = e := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hD := u5_le_D h h5n V (fun x hx => hV.2 x hx)
  obtain ⟨Z, P, hZ⟩ := u5_frame h h5 V hV.isElementaryAbelian hVc hD
  obtain ⟨u, hu⟩ := exists_bar_mul_eq_neg_one h
  obtain ⟨c, hc⟩ := exists_add_bar_eq_neg_one h
  have hR : IsHypTransport (r := 2) (ε := 1) h
      (((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * wmat stdIdx u c) :=
    isHypTransport_mul_unitary h (isHypTransport_wmat h stdIdx hu hc) P
  have hrK : r ∣ 2 ^ (2 * n) - 1 :=
    hrn.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Dvd.intro_left 2 rfl))
  have hcop : Nat.Coprime r (Nat.gcd 5 (2 ^ n + 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 5 _)
      ((Nat.coprime_primes hr (by norm_num)).2 hr5)
  obtain ⟨A, hAT, hAel, hAc⟩ := uc22s218_u5_model_elemAbelian h hr hrK hcop
  set θ := hypToPrimeForm h hR with hθ
  let g : Multiplicative (ZMod 5) × Multiplicative (ZMod 5) →* VM 5 :=
    { toFun := fun x => Multiplicative.ofAdd
        ![Multiplicative.toAdd x.1, Multiplicative.toAdd x.1, Multiplicative.toAdd x.2,
          Multiplicative.toAdd x.2, 0]
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i <;> rfl
      map_mul' := fun x y => by
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i <;> simp }
  let f : Multiplicative (ZMod 5) × Multiplicative (ZMod 5) →*
      MulAut (primeFormP h (idGram K 5)) := (Z.parHom P).comp g
  have hf : ∀ x, f x = Z.par P ![Multiplicative.toAdd x.1, Multiplicative.toAdd x.1,
      Multiplicative.toAdd x.2, Multiplicative.toAdd x.2, 0] := fun x => rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hf, Z.par_eq_one_iff] at hx
    have h0 := hx 0 4
    have h2 := hx 2 4
    simp at h0 h2
    exact Prod.ext (Multiplicative.toAdd.injective h0) (Multiplicative.toAdd.injective h2)
  have hpow5 : ∀ x : Multiplicative (ZMod 5), x ^ 5 = 1 := fun x => by
    have := pow_card_eq_one' (G := Multiplicative (ZMod 5)) (x := x)
    simpa using this
  refine ⟨A.map θ.toMonoidHom, f.range, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hAel.map θ.toMonoidHom
  · rw [Subgroup.card_map_of_injective θ.injective, hAc]
  · rintro _ ⟨x, rfl⟩
    rw [hf]
    exact hZ _
  · have hP : IsElemAbelian 5
        (⊤ : Subgroup (Multiplicative (ZMod 5) × Multiplicative (ZMod 5))) :=
      ⟨inferInstance, fun x _ => Prod.ext (hpow5 x.1) (hpow5 x.2)⟩
    rw [MonoidHom.range_eq_map]
    exact hP.map f
  · rw [Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv.symm, Nat.card_prod]
    simp [sq]
  · rintro α ⟨x, rfl⟩ e ⟨a₀, ha₀, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hAT ha₀
    show f x (θ (hypProj h 2 1 t)) = θ (hypProj h 2 1 t)
    obtain ⟨a', d', -, -, hm⟩ := ht
    rw [hf, ZetaData.par, hθ, hypToPrimeForm_hypProj h hR t, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    show (Z.Y P _ : GL (Fin 5) K) * transportGL hR (t : GL (HypIndex 2 1) K) *
      (Z.Y P _ : GL (Fin 5) K)⁻¹ = transportGL hR (t : GL (HypIndex 2 1) K)
    rw [mul_inv_eq_iff_eq_mul]
    apply Units.ext
    have e1 : P⁻¹ * Z.Y P ![Multiplicative.toAdd x.1, Multiplicative.toAdd x.1,
        Multiplicative.toAdd x.2, Multiplicative.toAdd x.2, 0] * P =
        Z.dgU ![Multiplicative.toAdd x.1, Multiplicative.toAdd x.1,
        Multiplicative.toAdd x.2, Multiplicative.toAdd x.2, 0] := by
      unfold ZetaData.Y
      group
    exact u5_commute_transport h P (Z.Y P _) (fun s => zp Z.ζ (![Multiplicative.toAdd x.1,
      Multiplicative.toAdd x.1, Multiplicative.toAdd x.2, Multiplicative.toAdd x.2, 0] s))
      (by rw [e1]; exact Z.dgU_val _) stdIdx rfl rfl _ hR rfl hm

end Model

theorem uc22s218_u5_outer_pair {Y : Type} [Group Y] {n : ℕ} (hY : IsU5 Y n)
    (h5 : 5 ∣ 2 ^ n + 1) (h5n : ¬ 5 ∣ n) {r : ℕ} (hr : r.Prime) (hr5 : r ≠ 5)
    (hrn : r ∣ 2 ^ n - 1) (V : Subgroup (MulAut Y)) (hV : IsElemAbelian 5 V)
    (hVc : Nat.card V = 5 ^ 4) :
    ∃ (E : Subgroup Y) (Q : Subgroup (MulAut Y)), IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      Q ≤ V ∧ IsElemAbelian 5 Q ∧ Nat.card Q = 5 ^ 2 ∧ ∀ α ∈ Q, ∀ e ∈ E, α e = e := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := uc22s218_u5_exists_model hY
  obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := 2) (ε := 1) h
  let ε : Y ≃* primeFormP h (idGram K 5) := e.symm.trans (hypToPrimeForm h hR₀)
  let θ : MulAut Y ≃* MulAut (primeFormP h (idGram K 5)) := MulAut.congr ε
  obtain ⟨E', Q', hE', hE'c, hQ'V, hQ', hQ'c, hact⟩ := u5_outer_pair_model h h5 h5n hr hr5 hrn
    (V.map θ.toMonoidHom) (hV.map θ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective θ.injective, hVc])
  refine ⟨E'.map ε.symm.toMonoidHom, Q'.map θ.symm.toMonoidHom, hE'.map _, ?_, ?_, hQ'.map _,
    ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective ε.symm.injective, hE'c]
  · rintro _ ⟨α', hα', rfl⟩
    obtain ⟨β, hβ, rfl⟩ := hQ'V hα'
    simpa using hβ
  · rw [Subgroup.card_map_of_injective θ.symm.injective, hQ'c]
  · rintro _ ⟨α', hα', rfl⟩ _ ⟨e', he', rfl⟩
    have h1 := hact α' hα' e' he'
    show (ε.trans (α'.trans ε.symm)) (ε.symm e') = ε.symm e'
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, h1]

end CFSG.LocalAnalysis.UniquenessCase.UC22
