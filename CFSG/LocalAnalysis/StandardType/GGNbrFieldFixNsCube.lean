module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylPlusLiftSL2

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBSymp

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem cube_pow_card_eq_one_zmod {p : ℕ} (f : Fin 3 → Multiplicative (ZMod p)) :
    f ^ p = 1 := by
  funext i
  rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (f i), ← ofAdd_nsmul, nsmul_eq_mul,
    ZMod.natCast_self, zero_mul, ofAdd_zero]

private theorem map_conj {G H : Type*} [Group G] [Group H] (f : G →* H) (x y : G) :
    f x * f y * (f x)⁻¹ = f (x * y * x⁻¹) := by
  simp only [map_mul, map_inv]

theorem exists_matrixTorus_of_sl2Cube [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {H : Subgroup (GL ι K)}
    (Φ : (Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) →* GL ι K)
    (Y : Multiplicative K →* GL ι K)
    (hΦinj : Function.Injective Φ) (hΦH : ∀ a, Φ a ∈ H) (hYH : ∀ c, Y c ∈ H)
    (hY1 : Y (Multiplicative.ofAdd 1) ∉ LargeEvenScalars ι K) (hY2 : ∀ c, Y c ^ 2 = 1)
    (hΦY : ∀ a c, Φ a * Y c = Y c * Φ a) :
    ∃ (τ : (Fin 3 → Multiplicative (ZMod p)) →* GL ι K) (X : Multiplicative K →* GL ι K),
      (∀ f, τ f ∈ H) ∧ (∀ f, τ f ∈ LargeEvenScalars ι K → f = 1) ∧
      (∀ i j : Fin 3, ∃ w ∈ H, w * torusBasis τ i * w⁻¹ = (torusBasis τ i)⁻¹ ∧
        (j ≠ i → w * torusBasis τ j * w⁻¹ = torusBasis τ j)) ∧
      (∀ c, X c ∈ H) ∧ X (Multiplicative.ofAdd 1) ∉ LargeEvenScalars ι K ∧
      (∀ c, X c ^ 2 = 1) ∧ (∀ f c, ∃ c', τ f * X c * (τ f)⁻¹ = X c') := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨s, n, hso, hn⟩ :=
    CFSG.StandardType.GGPlusLiftSL2.exists_order_p_inverting_sl2 hp hp2 hpq
  have hsp : s ^ p = 1 := by rw [← hso]; exact pow_orderOf_eq_one s
  let ρ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K := zmodPowHom hsp
  let τ : (Fin 3 → Multiplicative (ZMod p)) →* GL ι K :=
    Φ.comp (MonoidHom.pi fun i =>
      ρ.comp (Pi.evalMonoidHom (fun _ : Fin 3 => Multiplicative (ZMod p)) i))
  have hτ_apply : ∀ f, τ f = Φ (fun i => ρ (f i)) := fun _ => rfl
  have hbasis : ∀ i : Fin 3, torusBasis τ i = Φ (Pi.mulSingle i s) := by
    intro i
    rw [torusBasis, hτ_apply]
    congr 1
    funext j
    by_cases hji : j = i
    · subst hji
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      have h1 : ρ (Multiplicative.ofAdd (1 : ZMod p)) = s := by
        have := zmodPowHom_natCast hsp 1
        simpa [ρ] using this
      exact h1
    · rw [Pi.mulSingle_eq_of_ne hji, Pi.mulSingle_eq_of_ne hji]
      exact map_one ρ
  have hτs : ∀ f, τ f ∈ LargeEvenScalars ι K → f = 1 := by
    intro f hsc
    have hι : Nonempty ι := by
      rcases isEmpty_or_nonempty ι with h | h
      · exfalso
        refine hY1 ?_
        rw [largeEvenScalars_def]
        exact ⟨1, by
          rw [map_one]
          apply Units.ext
          ext i j
          exact (IsEmpty.false i).elim⟩
      · exact h
    obtain ⟨i⟩ := hι
    rw [largeEvenScalars_def] at hsc
    obtain ⟨c, hc⟩ := hsc
    have hτpow : (τ f) ^ p = 1 := by
      rw [← map_pow, cube_pow_card_eq_one_zmod, map_one]
    have hcpow : c ^ p = 1 := by
      have hmat : Matrix.GeneralLinearGroup.scalar ι (c ^ p) = 1 := by
        rw [map_pow, hc, hτpow]
      have hentry : ((c ^ p : Kˣ) : K) = 1 := by
        have h := congrArg (fun g : GL ι K => (g : Matrix ι ι K) i i) hmat
        rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          Matrix.diagonal_apply_eq] at h
        simpa using h
      exact Units.ext hentry
    have hord : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcpow
    have hordK : orderOf c ∣ Nat.card K - 1 := by
      rw [← Nat.card_units (α := K)]
      exact orderOf_dvd_natCard c
    have hpK : ¬ p ∣ Nat.card K - 1 := by
      intro hpdvd
      have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by
        have h1 : p ≤ Nat.card K + 1 := Nat.le_of_dvd (Nat.succ_pos _) hpq
        have h2 : 2 ≤ p := hp.two_le
        omega
      have h2d : p ∣ 2 := by
        rw [← hsub]
        exact Nat.dvd_sub hpq hpdvd
      exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) h2d) hp.two_le)
    have hc1 : c = 1 := by
      rcases hp.eq_one_or_self_of_dvd (orderOf c) hord with h1 | hp'
      · rw [← orderOf_eq_one_iff]; exact h1
      · exact absurd (hp' ▸ hordK) hpK
    have hτ1 : τ f = 1 := by rw [← hc, hc1, map_one]
    have hfun : (fun i => ρ (f i)) = 1 :=
      hΦinj (by rw [hτ_apply] at hτ1; rw [hτ1, map_one])
    funext i
    have hfi : ρ (f i) = 1 := congrFun hfun i
    exact (zmodPowHom_eq_one_iff hsp hso).mp hfi
  have hinv : ∀ i j : Fin 3, ∃ w ∈ H, w * torusBasis τ i * w⁻¹ = (torusBasis τ i)⁻¹ ∧
      (j ≠ i → w * torusBasis τ j * w⁻¹ = torusBasis τ j) := by
    intro i j
    refine ⟨Φ (Pi.mulSingle i n), hΦH _, ?_, ?_⟩
    · calc Φ (Pi.mulSingle i n) * torusBasis τ i * (Φ (Pi.mulSingle i n))⁻¹
          = Φ (Pi.mulSingle i n) * Φ (Pi.mulSingle i s) * (Φ (Pi.mulSingle i n))⁻¹ := by
            rw [hbasis i]
        _ = Φ (Pi.mulSingle i n * Pi.mulSingle i s * (Pi.mulSingle i n)⁻¹) :=
            map_conj Φ _ _
        _ = Φ (Pi.mulSingle i s⁻¹) := by
            congr 1
            rw [← Pi.mulSingle_inv, ← Pi.mulSingle_mul, ← Pi.mulSingle_mul, hn]
        _ = (torusBasis τ i)⁻¹ := by rw [hbasis i, ← map_inv, Pi.mulSingle_inv]
    · intro hji
      rw [hbasis j]
      let G : Fin 3 → Type := fun _ => Matrix.SpecialLinearGroup (Fin 2) K
      have hcomm : Commute (Pi.mulSingle (M := G) i n) (Pi.mulSingle (M := G) j s) :=
        Pi.mulSingle_commute (f := G) hji.symm n s
      have hcomm' : Commute (Φ (Pi.mulSingle i n)) (Φ (Pi.mulSingle j s)) := hcomm.map Φ
      rw [hcomm'.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hτX : ∀ f c, ∃ c', τ f * Y c * (τ f)⁻¹ = Y c' := by
    intro f c
    refine ⟨c, ?_⟩
    have hcomm : τ f * Y c = Y c * τ f := by
      rw [hτ_apply]
      exact hΦY _ c
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨τ, Y, fun f => hΦH _, hτs, hinv, hYH, hY1, hY2, hτX⟩

end TableBSymp

end CFSG.StandardType

end
