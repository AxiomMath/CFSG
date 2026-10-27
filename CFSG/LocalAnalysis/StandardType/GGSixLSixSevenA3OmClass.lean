module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmHyp
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmBlock
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmNumerics
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResHopf

public section

namespace CFSG.StandardType

namespace CoordOm

open Polynomial Module Multiplicative CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)

section Class

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
  {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

lemma exists_three_ne {r : ℕ} (a : Fin r) (hr : 4 ≤ r) :
    ∃ i₁ i₂ i₃ : Fin r, i₁ ≠ a ∧ i₂ ≠ a ∧ i₃ ≠ a ∧
      i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ := by
  classical
  have h3 : 3 ≤ (Finset.univ.erase a).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨s, hs, hsc⟩ := Finset.exists_subset_card_eq h3
  obtain ⟨x, y, z, hxy, hxz, hyz, hsxyz⟩ := Finset.card_eq_three.mp hsc
  rw [hsxyz] at hs
  exact ⟨x, y, z, (Finset.mem_erase.mp (hs (by simp))).1,
    (Finset.mem_erase.mp (hs (by simp))).1, (Finset.mem_erase.mp (hs (by simp))).1,
    hxy, hxz, hyz⟩

lemma exists_four_ne {r : ℕ} (a : Fin r) (hr : 5 ≤ r) :
    ∃ i₁ i₂ i₃ i₄ : Fin r, i₁ ≠ a ∧ i₂ ≠ a ∧ i₃ ≠ a ∧ i₄ ≠ a ∧
      i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₁ ≠ i₄ ∧ i₂ ≠ i₃ ∧ i₂ ≠ i₄ ∧ i₃ ≠ i₄ := by
  classical
  have h4 : 4 ≤ (Finset.univ.erase a).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨s, hs, hsc⟩ := Finset.exists_subset_card_eq h4
  obtain ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, hsxyzw⟩ := Finset.card_eq_four.mp hsc
  rw [hsxyzw] at hs
  exact ⟨x, y, z, w, (Finset.mem_erase.mp (hs (by simp))).1,
    (Finset.mem_erase.mp (hs (by simp))).1, (Finset.mem_erase.mp (hs (by simp))).1,
    (Finset.mem_erase.mp (hs (by simp))).1, hxy, hxz, hxw, hyz, hyw, hzw⟩

lemma sum_inv_mul_single_sub (ε : Fin r → (ZMod p)ˣ) (k l : Fin r) :
    ∑ i, (↑(ε i)⁻¹ : ZMod p) *
      (((Pi.single k (↑(ε k) : ZMod p) : Fin r → ZMod p) -
        (Pi.single l (↑(ε l) : ZMod p) : Fin r → ZMod p)) i) = 0 := by
  classical
  have hsingle : ∀ (k : Fin r) (c : ZMod p),
      ∑ i, (↑(ε i)⁻¹ : ZMod p) * ((Pi.single k c : Fin r → ZMod p) i) =
        (↑(ε k)⁻¹ : ZMod p) * c := by
    intro k c
    rw [Finset.sum_eq_single k]
    · rw [Pi.single_eq_same]
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  simp only [Pi.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib, hsingle, hsingle, Units.inv_mul, Units.inv_mul, sub_self]

theorem torus_card_ge_two (F : SevOm.Frame Q p A r) (hr : 4 ≤ r) (a : Fin r)
    (ε : Fin r → (ZMod p)ˣ) {J : Subgroup (V ≃ₗ[K] V)}
    (hT : ∀ s : Fin r → ZMod p, s a = 0 → ∑ i, (↑(ε i)⁻¹ : ZMod p) * s i = 0 →
      F.ι (ofAdd s) ∈ J) :
    p ^ 2 ≤ Nat.card ↥(A ⊓ J) := by
  classical
  obtain ⟨i₁, i₂, i₃, h1a, h2a, h3a, h12, h13, h23⟩ := exists_three_ne a hr
  haveI : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun _ _ he => LinearEquiv.ext (congrFun he)
  haveI : Finite ↥(A ⊓ J) := inferInstance
  set v₁ : Fin r → ZMod p :=
    Pi.single i₁ (↑(ε i₁) : ZMod p) - Pi.single i₃ (↑(ε i₃) : ZMod p) with hv₁def
  set v₂ : Fin r → ZMod p :=
    Pi.single i₂ (↑(ε i₂) : ZMod p) - Pi.single i₃ (↑(ε i₃) : ZMod p) with hv₂def
  have hv₁a : v₁ a = 0 := by
    rw [hv₁def, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm h1a), Pi.single_eq_of_ne (Ne.symm h3a),
      sub_zero]
  have hv₂a : v₂ a = 0 := by
    rw [hv₂def, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm h2a), Pi.single_eq_of_ne (Ne.symm h3a),
      sub_zero]
  have hv₁sum : ∑ i, (↑(ε i)⁻¹ : ZMod p) * v₁ i = 0 := by
    rw [hv₁def]; exact sum_inv_mul_single_sub ε i₁ i₃
  have hv₂sum : ∑ i, (↑(ε i)⁻¹ : ZMod p) * v₂ i = 0 := by
    rw [hv₂def]; exact sum_inv_mul_single_sub ε i₂ i₃
  have h₁ : F.ι (ofAdd v₁) ∈ A ⊓ J := Subgroup.mem_inf.mpr ⟨F.mem _, hT v₁ hv₁a hv₁sum⟩
  have h₂ : F.ι (ofAdd v₂) ∈ A ⊓ J := Subgroup.mem_inf.mpr ⟨F.mem _, hT v₂ hv₂a hv₂sum⟩
  have hv₁k₁ : v₁ i₁ ≠ 0 := by
    rw [hv₁def, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne h13, sub_zero]
    exact Units.ne_zero _
  have hv₂k₂ : v₂ i₂ ≠ 0 := by
    rw [hv₂def, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne h23, sub_zero]
    exact Units.ne_zero _
  have hv₁k₂ : v₁ i₂ = 0 := by
    rw [hv₁def, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm h12), Pi.single_eq_of_ne h23,
      sub_zero]
  exact card_ge_of_two F h₁ h₂ hv₁k₁ hv₂k₂ hv₁k₂

theorem torus_card_ge_three (F : SevOm.Frame Q p A r) (hr : 5 ≤ r) (a : Fin r)
    (ε : Fin r → (ZMod p)ˣ) {J : Subgroup (V ≃ₗ[K] V)}
    (hT : ∀ s : Fin r → ZMod p, s a = 0 → ∑ i, (↑(ε i)⁻¹ : ZMod p) * s i = 0 →
      F.ι (ofAdd s) ∈ J) :
    p ^ 3 ≤ Nat.card ↥(A ⊓ J) := by
  classical
  obtain ⟨i₁, i₂, i₃, i₄, h1a, h2a, h3a, h4a, h12, h13, h14, h23, h24, h34⟩ :=
    exists_four_ne a hr
  haveI : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun _ _ he => LinearEquiv.ext (congrFun he)
  haveI : Finite ↥(A ⊓ J) := inferInstance
  set v₁ : Fin r → ZMod p :=
    Pi.single i₁ (↑(ε i₁) : ZMod p) - Pi.single i₄ (↑(ε i₄) : ZMod p) with hv₁def
  set v₂ : Fin r → ZMod p :=
    Pi.single i₂ (↑(ε i₂) : ZMod p) - Pi.single i₄ (↑(ε i₄) : ZMod p) with hv₂def
  set v₃ : Fin r → ZMod p :=
    Pi.single i₃ (↑(ε i₃) : ZMod p) - Pi.single i₄ (↑(ε i₄) : ZMod p) with hv₃def
  have hv₁a : v₁ a = 0 := by
    rw [hv₁def, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm h1a), Pi.single_eq_of_ne (Ne.symm h4a),
      sub_zero]
  have hv₂a : v₂ a = 0 := by
    rw [hv₂def, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm h2a), Pi.single_eq_of_ne (Ne.symm h4a),
      sub_zero]
  have hv₃a : v₃ a = 0 := by
    rw [hv₃def, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm h3a), Pi.single_eq_of_ne (Ne.symm h4a),
      sub_zero]
  have hv₁sum : ∑ i, (↑(ε i)⁻¹ : ZMod p) * v₁ i = 0 := by
    rw [hv₁def]; exact sum_inv_mul_single_sub ε i₁ i₄
  have hv₂sum : ∑ i, (↑(ε i)⁻¹ : ZMod p) * v₂ i = 0 := by
    rw [hv₂def]; exact sum_inv_mul_single_sub ε i₂ i₄
  have hv₃sum : ∑ i, (↑(ε i)⁻¹ : ZMod p) * v₃ i = 0 := by
    rw [hv₃def]; exact sum_inv_mul_single_sub ε i₃ i₄
  have h₁ : F.ι (ofAdd v₁) ∈ A ⊓ J := Subgroup.mem_inf.mpr ⟨F.mem _, hT v₁ hv₁a hv₁sum⟩
  have h₂ : F.ι (ofAdd v₂) ∈ A ⊓ J := Subgroup.mem_inf.mpr ⟨F.mem _, hT v₂ hv₂a hv₂sum⟩
  have h₃ : F.ι (ofAdd v₃) ∈ A ⊓ J := Subgroup.mem_inf.mpr ⟨F.mem _, hT v₃ hv₃a hv₃sum⟩
  have hv₁k₁ : v₁ i₁ ≠ 0 := by
    rw [hv₁def, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne h14, sub_zero]
    exact Units.ne_zero _
  have hv₂k₂ : v₂ i₂ ≠ 0 := by
    rw [hv₂def, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne h24, sub_zero]
    exact Units.ne_zero _
  have hv₃k₃ : v₃ i₃ ≠ 0 := by
    rw [hv₃def, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne h34, sub_zero]
    exact Units.ne_zero _
  have hv₁k₂ : v₁ i₂ = 0 := by
    rw [hv₁def, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm h12), Pi.single_eq_of_ne h24, sub_zero]
  have hv₁k₃ : v₁ i₃ = 0 := by
    rw [hv₁def, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm h13), Pi.single_eq_of_ne h34, sub_zero]
  have hv₂k₃ : v₂ i₃ = 0 := by
    rw [hv₂def, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm h23), Pi.single_eq_of_ne h34, sub_zero]
  exact card_ge_of_three F h₁ h₂ h₃ hv₁k₁ hv₂k₂ hv₃k₃ hv₁k₂ hv₁k₃ hv₂k₃

variable {F : SevOm.Frame Q p A r} {E J : Subgroup (V ≃ₗ[K] V)}

theorem GGOmA3Hyp.false_of_class (H : GGOmA3Hyp F E J) {a : Fin r} {t : Fin r → ZMod p}
    (ht : F.ι (ofAdd t) ∈ E) (hta : t a = 0) (hfull : ∀ m, m ≠ a → t m ≠ 0)
    (hJc : IsComponentOf J (orthDerived Q ⊓
      Subgroup.centralizer ({F.ι (ofAdd t)} : Set (V ≃ₗ[K] V)))) : False := by
  classical
  haveI : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun _ _ he => LinearEquiv.ext (congrFun he)
  obtain ⟨i₁, i₂, i₃, h1a, h2a, h3a, h12, h13, h23⟩ := exists_three_ne a H.four_le
  have ht0 : t ≠ 0 := fun h0 => hfull i₁ h1a (by simp [h0])
  have hAexp : ∀ y ∈ A, y ^ p = 1 := by
    intro y hy
    obtain ⟨s, hs⟩ := F.exists_eq hy
    rw [← hs, F.pow_p]
  have hcard : Nat.card ↥(A ⊓ Subgroup.centralizer (J : Set (V ≃ₗ[K] V))) ≤ p ^ 2 := by
    rw [← H.card_E]
    exact Nat.card_mono (Set.toFinite _) H.centralizer_le
  rcases ggOmFrameCompInput_holds K V p H.ne_two Q H.nondeg H.tsub A H.le_orthDerived H.max r F
      H.four_le H.moves J t ht0 hJc hcard with hzero | hclass
  ·
    obtain ⟨j, j', hz, -⟩ := hzero
    have hlt : ({a, j, j'} : Finset (Fin r)).card < (Finset.univ : Finset (Fin r)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      have h3 := Finset.card_le_three (a := a) (b := j) (c := j')
      omega
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hia : i ≠ a := fun h => hi (by rw [h]; simp)
    have hij : i ≠ j := fun h => hi (by rw [h]; simp)
    have hij' : i ≠ j' := fun h => hi (by rw [h]; simp)
    exact hfull i hia (hz i hij hij')
  ·
    obtain ⟨k, c, ε, hc, hε, htk, hJtor⟩ := hclass
    have hka : k = a := by
      by_contra hne
      have h0 : (↑(ε a) : ZMod p) * c = 0 := by
        have := htk a (Ne.symm hne)
        rw [hta] at this
        exact this.symm
      rcases mul_eq_zero.mp h0 with hε0 | hc0
      · exact Units.ne_zero (ε a) hε0
      · exact hc hc0
    have htk' : ∀ i, i ≠ a → t i = (↑(ε i) : ZMod p) * c :=
      fun i hi => htk i fun h => hi (h.trans hka)
    have hJtor' : ∀ s : Fin r → ZMod p, s a = 0 →
        ∑ i, (↑(ε i)⁻¹ : ZMod p) * s i = 0 → F.ι (ofAdd s) ∈ J :=
      fun s hs hsum => hJtor s (by rw [hka]; exact hs) hsum
    by_cases hr5 : 5 ≤ r
    ·
      have hle3 := torus_card_ge_three F hr5 a ε hJtor'
      have hdvd : p ^ 3 ∣ Nat.card J :=
        pow_dvd_card_of_pow_le_card_inf (Fact.out : p.Prime) hAexp hle3
      exact not_prime_pow_three_dvd_forty_thousand (Fact.out : p.Prime) H.ne_two
        (hdvd.trans H.card_dvd)
    ·
      have hr4 : r = 4 := by omega
      have hle2 := torus_card_ge_two F H.four_le a ε hJtor'
      have hdvd2 : p ^ 2 ∣ Nat.card J :=
        pow_dvd_card_of_pow_le_card_inf (Fact.out : p.Prime) hAexp hle2
      have hp3 : p = 3 :=
        eq_three_of_sq_dvd_forty_thousand (Fact.out : p.Prime) H.ne_two
          (hdvd2.trans H.card_dvd)
      have hsum_t : ∑ i, (↑(ε i)⁻¹ : ZMod p) * t i = 0 := by
        have hterm : ∀ i, (↑(ε i)⁻¹ : ZMod p) * t i = if i = a then 0 else c := by
          intro i
          by_cases hi : i = a
          · rw [hi, hta, mul_zero, if_pos rfl]
          · rw [htk' i hi, if_neg hi, ← mul_assoc, Units.inv_mul, one_mul]
        calc ∑ i, (↑(ε i)⁻¹ : ZMod p) * t i
            = ∑ i, (if i = a then 0 else c) := Finset.sum_congr rfl fun i _ => hterm i
          _ = (Finset.univ.erase a).card • c := by
              rw [Finset.sum_ite]
              simp only [Finset.sum_const_zero, zero_add, Finset.sum_const]
              rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a)]
          _ = 0 := by
              have h3 : ((3 : ℕ) : ZMod p) = 0 := by
                rw [ZMod.natCast_eq_zero_iff, hp3]
              have hcard4 : (Finset.univ.erase a).card = 3 := by
                rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
                  Fintype.card_fin]
                omega
              rw [hcard4, nsmul_eq_mul, h3, zero_mul]
      have htJ : F.ι (ofAdd t) ∈ J := hJtor' t hta hsum_t
      have htcent : F.ι (ofAdd t) ∈ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) :=
        H.le_centralizer ht
      have hcentral : ∀ g ∈ J, F.ι (ofAdd t) * g = g * F.ι (ofAdd t) :=
        fun g hg => (Subgroup.mem_centralizer_iff.mp htcent g hg).symm
      have hz1 : F.ι (ofAdd t) = 1 := H.central_pow _ htJ hcentral (F.pow_p (ofAdd t))
      have ht_eq : t = 0 := by
        have hof : ofAdd t = ofAdd 0 := by
          rw [ofAdd_zero]
          exact F.inj (hz1.trans (map_one F.ι).symm)
        exact ofAdd.injective hof
      exact hfull i₁ h1a (by simp [ht_eq])

end Class

end CoordOm

end CFSG.StandardType
