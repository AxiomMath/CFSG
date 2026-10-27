module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.EmptyFaithful.S153G93DCovLinA
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Bridge

variable {W : Type} [CommGroup W]

theorem cNatModStructSU3Sub_of_natSUn {X : Subgroup (MulAut W)} {U Z : Subgroup W} {n : ℕ}
    (h : NatSUn X U Z 3 n) (hZ : Z = ⊥) : CNatModSU3Sub W U X n := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, hReal⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨π, hπ⟩ := hReal
  have hπs : Function.Surjective π := hπ.1
  have hUinv : ∀ h : ↥X, ∀ u ∈ U, (h : MulAut W) u ∈ U := hπ.2.2.2.1
  obtain ⟨β, hβs, hβk, hβe⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.nat (StatedSU 3 (2 ^ n) K)) rfl rfl hπ
  have hker : ∀ u : ↥U, β u = 1 ↔ u = 1 := by
    intro u
    rw [hβk u, hZ, Subgroup.mem_bot]
    exact ⟨fun h1 => Subtype.ext h1, fun h1 => by rw [h1]; rfl⟩
  have hβ_inj : Function.Injective β := by
    intro u v huv
    have h1 : β (u * v⁻¹) = 1 := by rw [map_mul, map_inv, huv, mul_inv_cancel]
    have h2 := (hker (u * v⁻¹)).1 h1
    rwa [mul_inv_eq_one] at h2
  let e : ↥U ≃* Multiplicative (Fin 3 → K) := MulEquiv.ofBijective β ⟨hβ_inj, hβs⟩
  have he_apply : ∀ u : ↥U, e u = β u := fun u => rfl
  have hact : ∀ (γ : ↥(StatedSU 3 (2 ^ n) K)) (u : ↥U)
      (hu : (((π γ : ↥X)) : MulAut W) (u : W) ∈ U),
      (β ⟨(((π γ : ↥X)) : MulAut W) (u : W), hu⟩ : Multiplicative (Fin 3 → K)) =
        Multiplicative.ofAdd ((((γ : Matrix.GeneralLinearGroup (Fin 3) K)) :
          Matrix (Fin 3) (Fin 3) K).mulVec
            (Multiplicative.toAdd (show Multiplicative (Fin 3 → K) from β u))) := by
    intro γ u hu
    have h1 := hβe γ u hu
    rw [show (FFModel.nat (StatedSU 3 (2 ^ n) K)).act γ (β u) =
      natAct (StatedSU 3 (2 ^ n) K) γ (β u) from rfl] at h1
    simpa [natAct] using h1
  refine ⟨⟨K, hKcard, e, ?_, ?_, ?_, ?_⟩⟩
  · intro x hx w hw
    exact hUinv ⟨x, hx⟩ w hw
  · intro x hx
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    let γ' : ↥(StatedSU 3 (2 ^ n) K) := γ
    have hxeq : (((π γ : ↥X)) : MulAut W) = x := by rw [hγ]
    refine ⟨(γ' : Matrix.GeneralLinearGroup (Fin 3) K), γ'.2, fun w hw hxw => ?_⟩
    have hxw' : (((π γ : ↥X)) : MulAut W) w ∈ U := by rw [hxeq]; exact hxw
    have hsub : (⟨x w, hxw⟩ : ↥U) = ⟨(((π γ : ↥X)) : MulAut W) w, hxw'⟩ :=
      Subtype.ext (congrArg (fun f : MulAut W => f w) hxeq.symm)
    rw [hsub, he_apply, he_apply]
    exact hact γ' ⟨w, hw⟩ hxw'
  · intro A hA
    refine ⟨π ⟨A, hA⟩, (π ⟨A, hA⟩).2, fun w hw hxw => ?_⟩
    rw [he_apply, he_apply]
    exact hact ⟨A, hA⟩ ⟨w, hw⟩ hxw
  · intro x hx hfix
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    let γ' : ↥(StatedSU 3 (2 ^ n) K) := γ
    have hxeq : (((π γ : ↥X)) : MulAut W) = x := by rw [hγ]
    have hmatvec : ∀ v : Fin 3 → K,
        (((γ' : Matrix.GeneralLinearGroup (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K).mulVec v = v := by
      intro v
      obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd v)
      have hu' : (show Multiplicative (Fin 3 → K) from β u) = Multiplicative.ofAdd v := hu
      have hxu : (((π γ : ↥X)) : MulAut W) (u : W) = (u : W) := by
        rw [hxeq]; exact hfix (u : W) u.2
      have hsub : (⟨(((π γ : ↥X)) : MulAut W) (u : W),
          hUinv (π γ) (u : W) u.2⟩ : ↥U) = ⟨(u : W), u.2⟩ := Subtype.ext hxu
      have hv : β ⟨(((π γ : ↥X)) : MulAut W) (u : W),
          hUinv (π γ) (u : W) u.2⟩ = β u := by rw [hsub]
      have key := hact γ' u (hUinv (π γ) (u : W) u.2)
      have e1 : Multiplicative.ofAdd ((((γ' : Matrix.GeneralLinearGroup (Fin 3) K)) :
          Matrix (Fin 3) (Fin 3) K).mulVec
            (Multiplicative.toAdd (show Multiplicative (Fin 3 → K) from β u))) =
          Multiplicative.ofAdd v := key.symm.trans (hv.trans hu')
      have e2 := Multiplicative.ofAdd.injective e1
      have e3 : Multiplicative.toAdd (show Multiplicative (Fin 3 → K) from β u) = v := by
        rw [hu']; rfl
      rwa [e3] at e2
    have hγ1 : (γ' : Matrix.GeneralLinearGroup (Fin 3) K) = 1 := by
      refine Units.ext ?_
      exact S153G93D.CovLin.matrix_eq_one_of_mulVec_eq (M := ((γ' : Matrix.GeneralLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) hmatvec
    have hγ' : γ' = 1 := Subtype.ext hγ1
    have hπγ : π γ = 1 := by
      rw [show γ = (1 : ↥(StatedSU 3 (2 ^ n) K)) from hγ']
      exact map_one π
    have h1 : (((π γ : ↥X)) : MulAut W) = 1 := by rw [hπγ]; rfl
    rw [← hxeq]
    exact h1

end Bridge

theorem K_U3NotThin (hSyl : UCK.U3Syl) :
    ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsSU3 X n →
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  intro X _ _ n hX
  by_cases hn : Odd n
  · exact ⟨3, Nat.prime_three, by norm_num, two_le_pRank_three_of_isSU3 hX hn⟩
  · have hEven : Even n := Nat.not_odd_iff_even.mp hn
    have hn1 : 1 ≤ n := (hX.2.admissible).2.1
    have h2n : 2 ^ n % 3 = 1 := by
      obtain ⟨m, rfl⟩ := hEven
      have h4 : (2 : ℕ) ^ (m + m) = 4 ^ m := by
        rw [pow_add, ← mul_pow]
        norm_num
      rw [h4]
      have hb : (4 : ℕ) ≡ 1 [MOD 3] := by decide
      simpa [Nat.ModEq] using hb.pow m
    have h3 : ¬ 3 ∣ 2 ^ n + 1 := by
      intro hd
      have hd' := Nat.dvd_iff_mod_eq_zero.1 hd
      have h : (2 ^ n + 1) % 3 = 2 := by rw [Nat.add_mod, h2n]
      omega
    have hge : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn1
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (by omega : 2 ^ n + 1 ≠ 1)
    have hq2 : q ≠ 2 := by
      rintro rfl
      have h2dvd : 2 ∣ 2 ^ n := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        exact ⟨2 ^ k, by rw [pow_succ, mul_comm]⟩
      have hone : 2 ∣ 1 := by
        have h := Nat.dvd_sub hqdvd h2dvd
        simpa using h
      norm_num at hone
    have hq3 : 3 < q := by
      have h3le : 3 ≤ q := by
        rcases hq.eq_two_or_odd with h | h
        · exact absurd h hq2
        · have := hq.two_le; omega
      rcases lt_or_eq_of_le h3le with h | h
      · exact h
      · rw [← h] at hqdvd
        exact absurd hqdvd h3
    haveI : Fact q.Prime := ⟨hq⟩
    let S : Sylow q X := Classical.choice Sylow.nonempty
    obtain ⟨E, -, hEab, hEcard⟩ :=
      (hSyl X n hX q hq hq3 hqdvd (S : Subgroup X) S.isPGroup' S.not_dvd_index).1
    exact ⟨q, hq, hq2,
      CFSG.SectionRank.le_pRank hq.one_lt le_top hEab (by simpa using hEcard)⟩

theorem not_thin_of_isSU3 (hSyl : UCK.U3Syl) {L : Subgroup G} {n : ℕ}
    (hshape : IsSU3 (Bar2 L) n) : ¬ F08.Thin8 L := by
  obtain ⟨p, hp, hp2, hpr⟩ := K_U3NotThin hSyl (Bar2 L) n hshape
  have hEq := pRank_bar2_eq_of_odd (G := G) (Y := L) hp hp2
  rw [hEq] at hpr
  intro hthin
  exact absurd (hthin p hp hp2) (not_le.2 hpr)

theorem barSub_ne_bot_of_v0_bot (D : Data G) (h869 : F08.R869 D) (h127 : R127 D)
    (hSyl : UCK.U3Syl) {V L : Subgroup G} {n : ℕ} (hV : Hyp125 D ⊥ V)
    (hL : L ∈ calC D.M) (hshape : IsSU3 (Bar2 L) n) :
    barSub ⊥ V hV.isElemAbelian L ≠ ⊥ :=
  barSub_ne_bot_of_not_thin_bot h869 h127 hV hL (not_thin_of_isSU3 hSyl hshape)

theorem card_of_cNatModSU3Sub {W : Type} [CommGroup W] [Finite W] {W' : Subgroup W}
    {X : Subgroup (MulAut W)} {n : ℕ} (h : CNatModSU3Sub W W' X n) :
    Nat.card W' = 2 ^ (6 * n) := by
  obtain ⟨S⟩ := h
  letI : Field S.K := S.fieldK
  letI : Finite S.K := S.finiteK
  have hcard : Nat.card ↥W' = (Nat.card S.K) ^ 3 := by
    rw [Nat.card_congr S.e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_fin]
  rw [hcard, S.cardK, ← pow_mul, ← pow_mul]
  congr 1
  ring

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
