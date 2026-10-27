module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShape
public import CFSG.LocalAnalysis.WeakClosure81.EightEighteen
public import CFSG.LocalAnalysis.WeakClosure81.EightNineteenAux
public import CFSG.LocalAnalysis.WeakClosure81.EightSeventeen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem wc819p_exists_involution_of_isPGroup_ne_bot {P : Subgroup G} (hP : IsPGroup 2 P)
    (hne : P ≠ ⊥) : ∃ r ∈ P, r ≠ 1 ∧ r ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.card_eq_one.mp (by simpa using hk))
  have hdvd : 2 ∣ Nat.card P := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hy' : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
  refine ⟨y, y.2, ?_, orderOf_dvd_iff_pow_eq_one.mp (by rw [hy'])⟩
  intro h1
  rw [h1, orderOf_one] at hy'
  omega

@[expose] def W3Claim819' (G : Type) [Group G] [Finite G] : Prop :=
  ∀ {V H T A L K : Subgroup G} {i : ℕ}, Sit813 V H T i A L K →
    Case813AB (cGrp H T) L K →
    ∃ X Y : Subgroup G, IsSylowIn 3 X (K ⊓ normalizer (V : Set G)) ∧
      IsSylowIn 3 Y (conjClosure L H ⊓ normalizer (V : Set G)) ∧ X ≤ Y ∧
      Y ≤ normalizer (K : Set G) ∧
      ∀ t ∈ T, ∃ n ∈ T ⊓ normalizer (Y : Set G), ∃ k ∈ T ⊓ normalizer (K : Set G), t = n * k

theorem Sit813.conjClosure_uGrp_inf_le_centralizer (hin : W3In814 G) {V H T A L K : Subgroup G}
    {i : ℕ} (h : Sit813 V H T i A L K) {X Y : Subgroup G}
    (hX : IsSylowIn 3 X (K ⊓ normalizer (V : Set G)))
    (hY : IsSylowIn 3 Y (conjClosure L H ⊓ normalizer (V : Set G))) (hXY : X ≤ Y)
    (hYK : Y ≤ normalizer (K : Set G))
    (hT : ∀ t ∈ T, ∃ n ∈ T ⊓ normalizer (Y : Set G), ∃ k ∈ T ⊓ normalizer (K : Set G),
      t = n * k) :
    conjClosure (uGrp V K ⊓ centralizer (K : Set G)) T ≤ centralizer (Y : Set G) := by
  set D : Subgroup G := uGrp V K ⊓ centralizer (K : Set G) with hD
  have hYC : Y ≤ centralizer (D : Set G) := h.eight_seventeen_of_in hin hX hY hXY hYK
  have hCD : D ≤ centralizer (Y : Set G) := fun d hd =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hYC hy) d hd).symm
  have hkD : ∀ k ∈ T ⊓ normalizer (K : Set G), k ∈ normalizer (D : Set G) := by
    intro k hk
    obtain ⟨hkT, hkK⟩ := Subgroup.mem_inf.mp hk
    have h1 : k ∈ normalizer (uGrp V K : Set G) :=
      mem_normalizer_conjClosure_of_mem_normalizers (V := V) (K := K)
        (h.le_normalizer_T hkT) hkK
    have h2 : k ∈ normalizer (centralizer (K : Set G) : Set G) :=
      mem_normalizer_centralizer_of_mem_normalizer_set (K := K) hkK
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro x
    constructor
    · intro hx
      obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨(h1 x).1 hxU, (h2 x).1 hxC⟩
    · intro hx
      obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨(h1 x).2 hxU, (h2 x).2 hxC⟩
  refine conjClosure_le fun t ht d hd => ?_
  obtain ⟨n, hn, k, hk, rfl⟩ := hT t ht
  have hkd : k * d * k⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hkD k hk) d).1 hd
  have hnC : n ∈ normalizer (centralizer (Y : Set G) : Set G) :=
    mem_normalizer_centralizer_of_mem_normalizer_set (K := Y) (Subgroup.mem_inf.mp hn).2
  have hmem : n * (k * d * k⁻¹) * n⁻¹ ∈ centralizer (Y : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hnC (k * d * k⁻¹)).1 (hCD hkd)
  have heq : (n * k) * d * (n * k)⁻¹ = n * (k * d * k⁻¹) * n⁻¹ := by group
  rwa [heq]

theorem Sit813.exists_central_of_claim819' (hin : W3In814 G) {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) {X Y : Subgroup G}
    (hX : IsSylowIn 3 X (K ⊓ normalizer (V : Set G)))
    (hY : IsSylowIn 3 Y (conjClosure L H ⊓ normalizer (V : Set G))) (hXY : X ≤ Y)
    (hYK : Y ≤ normalizer (K : Set G))
    (hT : ∀ t ∈ T, ∃ n ∈ T ⊓ normalizer (Y : Set G), ∃ k ∈ T ⊓ normalizer (K : Set G),
      t = n * k) :
    ∃ w ∈ T, w ≠ 1 ∧ w * w = 1 ∧ (∀ t ∈ T, t * w = w * t) ∧ ∀ y ∈ Y, y * w = w * y := by
  set D : Subgroup G := uGrp V K ⊓ centralizer (K : Set G) with hD
  set W : Subgroup G := conjClosure D T with hW
  have hWY : W ≤ centralizer (Y : Set G) :=
    h.conjClosure_uGrp_inf_le_centralizer hin hX hY hXY hYK hT
  have hDp : D ≤ pCoreOf 2 H := inf_le_left.trans h.uGrp_le_pCoreOf
  have hWp : W ≤ pCoreOf 2 H := by
    rw [hW]
    refine conjClosure_le fun t ht d hd => ?_
    exact (Subgroup.mem_normalizer_iff.mp
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H) (h.T_le_H ht)) d).1 (hDp hd)
  have hWT : W ≤ T := hWp.trans (pCoreOf_le_of_isCalH h.minCex.hyp.calH h.minCex.hyp.sylow)
  have hT2 : IsPGroup 2 T := h.minCex.hyp.sylow.isPGroup
  have hW2 : IsPGroup 2 W := hT2.to_le hWT
  have hDW : D ≤ W := by rw [hW]; exact le_conjClosure D T
  have hWne : W ≠ ⊥ := by
    intro hbot
    exact h.eight_eighteen hin (le_bot_iff.mp (hDW.trans (le_of_eq hbot)))
  have hfix : W ⊓ centralizer (T : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot_of_two_groups hT2 hW2 (by rw [hW]; exact le_normalizer_conjClosure D T)
      hWne
  have hP2 : IsPGroup 2 ↥(W ⊓ centralizer (T : Set G)) :=
    hW2.to_le (inf_le_left : W ⊓ centralizer (T : Set G) ≤ W)
  obtain ⟨w, hwP, hw1, hw2'⟩ :=
    wc819p_exists_involution_of_isPGroup_ne_bot hP2 hfix
  obtain ⟨hwW, hwT⟩ := Subgroup.mem_inf.mp hwP
  exact ⟨w, hWT hwW, hw1, by rwa [pow_two] at hw2',
    fun t ht => Subgroup.mem_centralizer_iff.mp hwT t ht,
    fun y hy => Subgroup.mem_centralizer_iff.mp (hWY hwW) y hy⟩

end CFSG.LocalAnalysis.WeakClosure81

end
