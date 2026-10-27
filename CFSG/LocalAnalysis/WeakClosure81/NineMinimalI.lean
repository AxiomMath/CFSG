module

public import CFSG.LocalAnalysis.WeakClosure81.NineMinimal
public import CFSG.LocalAnalysis.WeakClosure81.NineMinB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V K S T X : Subgroup G} {p : ℕ}

theorem TwoPTwo.sup_inf_eq_of_invariant (h : TwoPTwo K S X p) {Y : Subgroup G} (hYX : Y ≤ X)
    (hY : ∀ s ∈ S ⊓ normalizer (X : Set G), ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) :
    (S ⊔ Y) ⊓ X = Y := by
  let R := pCoreOf 2 K
  let L := R ⊔ Y
  have hRS : R ≤ S := h.pCoreOf_le_sylowTwo
  have hKR : K ≤ normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hSK : S ≤ K := h.sylowTwo.le
  have hXK : X ≤ K := h.sylowP.le
  have hYR : Y ≤ normalizer (R : Set G) := hYX.trans (hXK.trans hKR)
  have hRY : (L : Set G) = (R : Set G) * (Y : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left R Y hYR
  have hSL : S ≤ normalizer (L : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs l hl
    have hl' : l ∈ (R : Set G) * (Y : Set G) := by
      rw [← hRY]
      exact hl
    rw [Set.mem_mul] at hl'
    obtain ⟨r, hr, y, hy, rfl⟩ := hl'
    obtain ⟨r₀, hr₀, n, hn, hs_eq⟩ := h.exists_mul_pCoreOf_inf_normalizer hs
    have hsr : s * r * s⁻¹ ∈ R := by
      have hsN : s ∈ normalizer (R : Set G) := hKR (hSK hs)
      exact (Subgroup.mem_normalizer_iff.mp hsN r).mp hr
    have hsy : s * y * s⁻¹ ∈ L := by
      rw [hs_eq]
      have hny : n * y * n⁻¹ ∈ Y := hY n hn y hy
      have hconj : (r₀ * n) * y * (r₀ * n)⁻¹ = r₀ * (n * y * n⁻¹) * r₀⁻¹ := by
        group
      rw [hconj]
      exact L.mul_mem (L.mul_mem (Subgroup.mem_sup_left hr₀) (Subgroup.mem_sup_right hny))
        (Subgroup.mem_sup_left (R.inv_mem hr₀))
    have hmul : s * (r * y) * s⁻¹ = (s * r * s⁻¹) * (s * y * s⁻¹) := by group
    rw [hmul]
    exact L.mul_mem (Subgroup.mem_sup_left hsr) hsy
  have hSX : S ⊓ X = ⊥ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (Nat.Prime p) := ⟨h.prime⟩
    exact disjoint_iff.mp
      (IsPGroup.disjoint_of_ne 2 p (Ne.symm h.odd) S X h.sylowTwo.isPGroup h.sylowP.isPGroup)
  apply le_antisymm
  · intro x hx
    have hxSY : x ∈ S ⊔ Y := hx.1
    have hxX : x ∈ X := hx.2
    have hxSL : x ∈ S ⊔ L := (sup_le_sup_left le_sup_right S) hxSY
    have hSLeq : (↑(S ⊔ L) : Set G) = (S : Set G) * (L : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right S L hSL
    have hx' : x ∈ (S : Set G) * (L : Set G) := by
      rw [← hSLeq]
      exact hxSL
    rw [Set.mem_mul] at hx'
    obtain ⟨s, hs, l, hl, hsl⟩ := hx'
    have hl' : l ∈ (R : Set G) * (Y : Set G) := by
      rw [← hRY]
      exact hl
    rw [Set.mem_mul] at hl'
    obtain ⟨r, hr, y, hy, rfl⟩ := hl'
    have hx_eq : x = s * (r * y) := hsl.symm
    have hsrS : s * r ∈ S := S.mul_mem hs (hRS hr)
    have hsrX : s * r ∈ X := by
      have h1 : x * y⁻¹ = s * r := by rw [hx_eq]; group
      rw [← h1]
      exact X.mul_mem hxX (X.inv_mem (hYX hy))
    have hmem : s * r ∈ S ⊓ X := ⟨hsrS, hsrX⟩
    rw [hSX, Subgroup.mem_bot] at hmem
    have hxy : x = y := by
      rw [hx_eq, ← mul_assoc, hmem, one_mul]
    rw [hxy]
    exact hy
  · exact le_inf le_sup_right hYX

theorem TwoPTwo.le_normalizer_of_invariant_lt {W : Subgroup G} (h : TwoPTwo K S X p)
    (hmin : ∀ K₀ : Subgroup G, S ≤ K₀ → K₀ < K → K₀ ≤ normalizer (W : Set G))
    {Y : Subgroup G} (hYX : Y ≤ X) (hYne : Y ≠ X)
    (hY : ∀ s ∈ S ⊓ normalizer (X : Set G), ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) :
    Y ≤ normalizer (W : Set G) := by
  have hle : S ⊔ Y ≤ K := sup_le h.sylowTwo.le (hYX.trans h.sylowP.le)
  have hne : S ⊔ Y ≠ K := by
    intro heq
    have hXle : X ≤ S ⊔ Y := by
      rw [heq]
      exact h.sylowP.le
    have hinf : (S ⊔ Y) ⊓ X = X := by
      apply le_antisymm inf_le_right
      exact le_inf hXle le_rfl
    have hXeq : X = Y := hinf.symm.trans (h.sup_inf_eq_of_invariant hYX hY)
    exact hYne hXeq.symm
  have hlt : S ⊔ Y < K := lt_of_le_of_ne hle hne
  have hmin' : S ⊔ Y ≤ normalizer (W : Set G) := hmin (S ⊔ Y) le_sup_left hlt
  exact le_sup_right.trans hmin'

theorem nine1Hyp_of_minimal {W : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : IsPGroup p X) (hXV : X ≤ normalizer (V : Set G)) (hT : IsPGroup 2 T)
    (hTV : T ≤ normalizer (V : Set G)) (hXT : (X : Set G) * T = T * X)
    (hTW : T ≤ normalizer (W : Set G)) (hKW : ¬ X ⊔ T ≤ normalizer (W : Set G))
    (hmin : ∀ K₀ : Subgroup G, T ≤ K₀ → K₀ < X ⊔ T → K₀ ≤ normalizer (W : Set G)) :
    Nine1Hyp V (X ⊔ T) T X p := by
  have hK : TwoPTwo (X ⊔ T) T X p := twoPTwo_of_minimal hp hp2 hX hT hXT hTW hKW hmin
  have hX1 : X ≠ ⊥ := by
    intro hbot
    apply hKW
    rw [hbot, bot_sup_eq]
    exact hTW
  have hS : ¬ p ∣ Nat.card ↥(T ⊓ normalizer (X : Set G)) := by
    intro hdvd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : IsPGroup 2 ↥(T ⊓ normalizer (X : Set G)) := hT.to_le inf_le_left
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    rw [hn] at hdvd
    have hp_dvd_two : p ∣ 2 := hp.dvd_of_dvd_pow hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp_dvd_two)
  have hirred : IrredOnFrattiniQuot T X := by
    refine irredOnFrattiniQuot_of_sup_ne hp hX hX1 hS ?_
    intro Y₁ Y₂ hΦY₁ hY₁X hY₁ne hinv₁ hΦY₂ hY₂X hY₂ne hinv₂ hsupXY
    have hY₁W : Y₁ ≤ normalizer (W : Set G) :=
      hK.le_normalizer_of_invariant_lt hmin hY₁X hY₁ne hinv₁
    have hY₂W : Y₂ ≤ normalizer (W : Set G) :=
      hK.le_normalizer_of_invariant_lt hmin hY₂X hY₂ne hinv₂
    apply hKW
    have hXW : X ≤ normalizer (W : Set G) := by
      rw [← hsupXY]
      exact sup_le hY₁W hY₂W
    exact sup_le hXW hTW
  exact ⟨⟨hK, hirred⟩, sup_le hXV hTV⟩

end CFSG.LocalAnalysis.WeakClosure81
