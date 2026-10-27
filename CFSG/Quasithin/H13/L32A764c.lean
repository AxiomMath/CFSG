module

public import CFSG.Quasithin.H13.L32A764b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups commutatorElement

theorem sl24_prod : ∀ A : SL(2, F4), ∃ a b c d : F4,
    (A : Matrix (Fin 2) (Fin 2) F4) =
      !![1, a; 0, 1] * !![1, 0; b, 1] * !![1, c; 0, 1] * !![1, 0; d, 1] := by
  decide +kernel

theorem sl24_card_fix_vec : ∀ p : Fin 2 → F4, p ≠ 0 →
    (Finset.univ.filter fun A : SL(2, F4) => (A : Matrix (Fin 2) (Fin 2) F4).mulVec p = p).card =
      4 := by
  decide +kernel

theorem sl24_fix_both : ∀ v : Fin 2 → F4,
    (∀ a : F4, (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) F4).mulVec v = v) →
    (∀ a : F4, (!![1, 0; a, 1] : Matrix (Fin 2) (Fin 2) F4).mulVec v = v) → v = 0 := by
  decide +kernel

theorem f4_eq_of_add : ∀ x y : Fin 2 → F4, x + y = 0 → x = y := by
  decide

theorem f4_swap_upper : ∀ b : F4, (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F4) * !![1, b; 0, 1] *
    !![0, 1; 1, 0] = !![1, 0; b, 1] := by
  decide

theorem f4_upper_fix : ∀ a : F4,
    (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) F4).mulVec ![1, 0] = ![1, 0] := by
  decide

theorem f4_swap_sq : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F4) * !![0, 1; 1, 0] = 1 := by
  decide

theorem f4_e1_ne : (![1, 0] : Fin 2 → F4) ≠ 0 := by
  decide

@[expose] def upper24 (a : F4) : SL(2, F4) :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def swap24 : SL(2, F4) :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two]; decide⟩

theorem coe_upper24 (a : F4) :
    ((upper24 a : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4) = !![1, a; 0, 1] := rfl

theorem coe_swap24 : ((swap24 : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4) = !![0, 1; 1, 0] := rfl

theorem swap24_inv : swap24⁻¹ = swap24 := by
  have hJJ : swap24 * swap24 = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_swap24, f4_swap_sq]
    rfl
  exact inv_eq_of_mul_eq_one_right hJJ

theorem sl24_conj_mulVec (h₀ X : SL(2, F4)) (v : Fin 2 → F4) :
    ((h₀ * X * h₀⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
        ((h₀ : Matrix (Fin 2) (Fin 2) F4).mulVec v) =
      (h₀ : Matrix (Fin 2) (Fin 2) F4).mulVec ((X : Matrix (Fin 2) (Fin 2) F4).mulVec v) := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
    show h₀ * X * h₀⁻¹ * h₀ = h₀ * X by group, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec]

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Ctx764

variable (C : Ctx764 G T L V)
include C

theorem fix_of_mem_sup (π : ↥(kz T V) →* SL(2, F4))
    (β : ↥(fsuU T V) →* Multiplicative (Fin 2 → F4)) (hβk : β.ker = (u0 T V).subgroupOf (fsuU T V))
    (hβe : ∀ (k : ↥(kz T V)) (x x' : ↥(fsuU T V)), (x' : G) = k * x * (k : G)⁻¹ →
      β x' = Multiplicative.ofAdd (((π k : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
        (Multiplicative.toAdd (β x))))
    (k : ↥(kz T V)) (hkR : (k : G) ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) {w : G}
    (hwU : w ∈ fsuU T V) (hw : w ∈ V ⊔ u0 T V) :
    ((π k : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec (Multiplicative.toAdd (β ⟨w, hwU⟩)) =
      Multiplicative.toAdd (β ⟨w, hwU⟩) := by
  have hc := comm_mem_of_R1_sup C.hyp C.hMod C.h63 C.hF C.h1222 C.h1332 C.h1334 hkR hw
  have hkw : (k : G) * w * (k : G)⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp (C.H_le_normalizer_U (oTwoUpper_le _ k.2)) w).mp hwU
  have e1 := hβe k ⟨w, hwU⟩ ⟨_, hkw⟩ rfl
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hc0 : (k : G) * w * (k : G)⁻¹ * w⁻¹ ∈ u0 T V := fsuV1_le_u0 C.hyp C.hMod hc
  have hcm : (⟨(k : G) * w * (k : G)⁻¹, hkw⟩ : ↥(fsuU T V)) =
      ⟨(k : G) * w * (k : G)⁻¹ * w⁻¹, hU0U hc0⟩ * ⟨w, hwU⟩ := Subtype.ext (by simp)
  have hc1 : β ⟨(k : G) * w * (k : G)⁻¹ * w⁻¹, hU0U hc0⟩ = 1 := (l24_ker_iff hβk _).mpr hc0
  rw [hcm, map_mul, hc1, one_mul] at e1
  have := congrArg Multiplicative.toAdd e1
  rw [toAdd_ofAdd] at this
  exact this.symm

theorem exists_two : ∃ s₁ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T), s₁ ∉ pCoreOf 2 (hz T V) ∧
    ∃ s₂ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T), s₂ ∉ pCoreOf 2 (hz T V) ∧
      s₁⁻¹ * s₂ ∉ pCoreOf 2 (hz T V) := by
  have S0 : Setting147 G T L V (hz T V) := ⟨C.hyp, C.hyp.isHzOne_hz C.h63⟩
  obtain ⟨-, hR4⟩ := R1_le_kz_sup S0 C.hF C.h63 C.h1222 C.h1332 C.h1334
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hR
  set Q := pCoreOf 2 (hz T V) with hQ
  have hQR : Q ≤ R := pCoreOf_hz_le_R1 C.hyp C.hF
  have hRN : R ≤ Subgroup.normalizer (Q : Set G) := C.R1_le_H.trans (le_normalizer_pCoreOf 2 _)
  have hQn : (Q.subgroupOf R).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hRN
  have hcard : Nat.card (↥R ⧸ Q.subgroupOf R) = 4 := by
    rw [← Subgroup.index_eq_card]
    exact hR4
  obtain ⟨s₁, hs₁R, hs₁Q⟩ : ∃ s ∈ R, s ∉ Q := by
    by_contra hno
    push Not at hno
    rw [Subgroup.relIndex_eq_one.mpr hno] at hR4
    omega
  refine ⟨s₁, hs₁R, hs₁Q, ?_⟩
  by_contra hno
  push Not at hno
  let f : Bool → ↥R ⧸ Q.subgroupOf R := fun b =>
    if b then QuotientGroup.mk ⟨s₁, hs₁R⟩ else 1
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective x
    by_cases hr : (r : G) ∈ Q
    · refine ⟨false, ?_⟩
      show (1 : ↥R ⧸ Q.subgroupOf R) = QuotientGroup.mk r
      rw [eq_comm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hr
    · refine ⟨true, ?_⟩
      show QuotientGroup.mk ⟨s₁, hs₁R⟩ = (QuotientGroup.mk r : ↥R ⧸ Q.subgroupOf R)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hno r r.2 hr
  have hle := Nat.card_le_card_of_surjective f hf
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_bool] at hle
  omega

theorem exists_fix (π : ↥(kz T V) →* SL(2, F4))
    (hπk : π.ker = (pCoreOf 2 (kz T V)).subgroupOf (kz T V))
    (β : ↥(fsuU T V) →* Multiplicative (Fin 2 → F4)) (hβk : β.ker = (u0 T V).subgroupOf (fsuU T V))
    (hβe : ∀ (k : ↥(kz T V)) (x x' : ↥(fsuU T V)), (x' : G) = k * x * (k : G)⁻¹ →
      β x' = Multiplicative.ofAdd (((π k : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
        (Multiplicative.toAdd (β x))))
    {v₀ : G} (hv₀U : v₀ ∈ fsuU T V) (hv₀V : v₀ ∈ V) (hv₀1 : v₀ ∉ fsuV1 T V) (A : SL(2, F4))
    (hA : (A : Matrix (Fin 2) (Fin 2) F4).mulVec (Multiplicative.toAdd (β ⟨v₀, hv₀U⟩)) =
      Multiplicative.toAdd (β ⟨v₀, hv₀U⟩)) :
    ∃ r : ↥(kz T V), (r : G) ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ∧ π r = A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set p := Multiplicative.toAdd (β ⟨v₀, hv₀U⟩) with hp
  have hp0 : p ≠ 0 := by
    intro h0
    apply hv₀1
    have h1 : β ⟨v₀, hv₀U⟩ = 1 := by
      rw [← ofAdd_toAdd (β ⟨v₀, hv₀U⟩), ← hp, h0]
      rfl
    have hu0 : v₀ ∈ u0 T V := (l24_ker_iff hβk _).mp h1
    rw [← inf_u0_eq C.hyp C.hMod C.h63 C.hF]
    exact ⟨hv₀V, hu0⟩
  have hv₀VU : v₀ ∈ V ⊔ u0 T V := Subgroup.mem_sup_left hv₀V
  obtain ⟨s₁, hs₁R, hs₁Q, s₂, hs₂R, hs₂Q, hs₁₂⟩ := C.exists_two
  obtain ⟨k₁, hk₁K, hk₁R, q₁, hq₁, rfl⟩ := C.exists_kq hs₁R
  obtain ⟨k₂, hk₂K, hk₂R, q₂, hq₂, rfl⟩ := C.exists_kq hs₂R
  have hkQ : ∀ (k : G) (hk : k ∈ kz T V), π ⟨k, hk⟩ = 1 → k ∈ pCoreOf 2 (hz T V) := by
    intro k hk h1
    have h2 : (⟨k, hk⟩ : ↥(kz T V)) ∈ π.ker := h1
    rw [hπk, Subgroup.mem_subgroupOf] at h2
    exact pCoreOf_kz_le (T := T) (V := V) h2
  have hQn : ∀ g ∈ hz T V, ∀ q ∈ pCoreOf 2 (hz T V), g * q * g⁻¹ ∈ pCoreOf 2 (hz T V) :=
    fun g hg q hq => (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hg) q).mp hq
  have hπ₁ : π ⟨k₁, hk₁K⟩ ≠ 1 := fun h1 => hs₁Q (mul_mem (hkQ _ _ h1) hq₁)
  have hπ₂ : π ⟨k₂, hk₂K⟩ ≠ 1 := fun h1 => hs₂Q (mul_mem (hkQ _ _ h1) hq₂)
  have hπ₁₂ : π ⟨k₁, hk₁K⟩ ≠ π ⟨k₂, hk₂K⟩ := by
    intro e
    have h1 : π ⟨k₁⁻¹ * k₂, mul_mem (inv_mem hk₁K) hk₂K⟩ = 1 := by
      have : (⟨k₁⁻¹ * k₂, mul_mem (inv_mem hk₁K) hk₂K⟩ : ↥(kz T V)) =
          (⟨k₁, hk₁K⟩)⁻¹ * ⟨k₂, hk₂K⟩ := rfl
      rw [this, map_mul, map_inv, e, inv_mul_cancel]
    have h2 := hkQ _ _ h1
    apply hs₁₂
    have hk₁H : k₁ ∈ hz T V := oTwoUpper_le _ hk₁K
    rw [show (k₁ * q₁)⁻¹ * (k₂ * q₂) = q₁⁻¹ * (k₁⁻¹ * k₂) * q₂ by group]
    exact mul_mem (mul_mem (inv_mem hq₁) h2) hq₂
  have hsq : ∀ (k : G) (hk : k ∈ kz T V), k ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) →
      π ⟨k, hk⟩ * π ⟨k, hk⟩ = 1 := by
    intro k hk hkR
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (L₁Of L (fsuV1 T V) ⊔ T)) ⟨k, hkR⟩
    have hk2 : k ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have := sl24_sq_of_two_pow (π ⟨k, hk⟩) n (by
      rw [← map_pow]
      have : (⟨k, hk⟩ : ↥(kz T V)) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hk2)
      rw [this, map_one])
    rwa [sq] at this
  have hfix₁ := C.fix_of_mem_sup π β hβk hβe ⟨k₁, hk₁K⟩ hk₁R hv₀U hv₀VU
  have hfix₂ := C.fix_of_mem_sup π β hβk hβe ⟨k₂, hk₂K⟩ hk₂R hv₀U hv₀VU
  have hk₁₂R : k₁ * k₂ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := mul_mem hk₁R hk₂R
  have hfix₁₂ := C.fix_of_mem_sup π β hβk hβe ⟨k₁ * k₂, mul_mem hk₁K hk₂K⟩ hk₁₂R hv₀U hv₀VU
  have hm₁₂ : π ⟨k₁ * k₂, mul_mem hk₁K hk₂K⟩ = π ⟨k₁, hk₁K⟩ * π ⟨k₂, hk₂K⟩ := by
    rw [← map_mul]
    rfl
  set F := Finset.univ.filter fun B : SL(2, F4) => (B : Matrix (Fin 2) (Fin 2) F4).mulVec p = p
    with hF
  have hF4 : F.card = 4 := sl24_card_fix_vec p hp0
  set S : Finset (SL(2, F4)) :=
    {1, π ⟨k₁, hk₁K⟩, π ⟨k₂, hk₂K⟩, π ⟨k₁, hk₁K⟩ * π ⟨k₂, hk₂K⟩} with hS
  have hSF : S ⊆ F := by
    intro B hB
    simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hB
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hB with rfl | rfl | rfl | rfl
    · simp
    · exact hfix₁
    · exact hfix₂
    · rw [← hm₁₂]
      exact hfix₁₂
  have hS4 : S.card = 4 := by
    have h1 := hsq k₁ hk₁K hk₁R
    have h2 := hsq k₂ hk₂K hk₂R
    have hne1 : π ⟨k₁, hk₁K⟩ * π ⟨k₂, hk₂K⟩ ≠ 1 := by
      intro e
      apply hπ₁₂
      calc π ⟨k₁, hk₁K⟩ = π ⟨k₁, hk₁K⟩ * (π ⟨k₂, hk₂K⟩ * π ⟨k₂, hk₂K⟩) := by rw [h2, mul_one]
        _ = (π ⟨k₁, hk₁K⟩ * π ⟨k₂, hk₂K⟩) * π ⟨k₂, hk₂K⟩ := by rw [mul_assoc]
        _ = π ⟨k₂, hk₂K⟩ := by rw [e, one_mul]
    have hne2 : π ⟨k₁, hk₁K⟩ * π ⟨k₂, hk₂K⟩ ≠ π ⟨k₁, hk₁K⟩ := by
      intro e
      apply hπ₂
      have := congrArg (π ⟨k₁, hk₁K⟩ * ·) e
      simp only [← mul_assoc, h1, one_mul] at this
      exact this
    have hne3 : π ⟨k₁, hk₁K⟩ * π ⟨k₂, hk₂K⟩ ≠ π ⟨k₂, hk₂K⟩ := by
      intro e
      apply hπ₁
      have := congrArg (· * π ⟨k₂, hk₂K⟩) e
      simp only [mul_assoc, h2, mul_one] at this
      exact this
    rw [hS, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hne3.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hπ₁₂, fun e => hne2 e.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun e => hπ₁ e.symm, fun e => hπ₂ e.symm, fun e => hne1 e.symm⟩
  have hSeq : S = F := Finset.eq_of_subset_of_card_le hSF (by rw [hF4, hS4])
  have hAF : A ∈ F := by
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hA
  rw [← hSeq] at hAF
  simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hAF
  rcases hAF with rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, map_one π⟩
  · exact ⟨⟨k₁, hk₁K⟩, hk₁R, rfl⟩
  · exact ⟨⟨k₂, hk₂K⟩, hk₂R, rfl⟩
  · exact ⟨⟨k₁ * k₂, mul_mem hk₁K hk₂K⟩, hk₁₂R, hm₁₂⟩

omit [Finite G] C in
theorem exists_decomp (π : ↥(kz T V) →* SL(2, F4))
    (hπk : π.ker = (pCoreOf 2 (kz T V)).subgroupOf (kz T V)) (h₀ : SL(2, F4))
    (hfix : ∀ A : SL(2, F4), (A : Matrix (Fin 2) (Fin 2) F4).mulVec
        ((h₀ : Matrix (Fin 2) (Fin 2) F4).mulVec ![1, 0]) =
        (h₀ : Matrix (Fin 2) (Fin 2) F4).mulVec ![1, 0] →
      ∃ r : ↥(kz T V), (r : G) ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ∧ π r = A)
    (w : ↥(kz T V)) (hw : π w = h₀ * swap24 * h₀⁻¹) (k : ↥(kz T V)) :
    ∃ r₁ r₂ r₃ r₄ : ↥(kz T V), (r₁ : G) ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ∧
      (r₂ : G) ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ∧
      (r₃ : G) ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ∧
      (r₄ : G) ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ∧
      ∃ o ∈ pCoreOf 2 (kz T V),
        (k : G) = r₁ * (w * r₂ * w⁻¹) * r₃ * (w * r₄ * w⁻¹) * o := by
  have hup : ∀ a : F4, ∃ r : ↥(kz T V), (r : G) ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ∧
      π r = h₀ * upper24 a * h₀⁻¹ := by
    intro a
    refine hfix _ ?_
    rw [sl24_conj_mulVec, coe_upper24, f4_upper_fix]
  obtain ⟨a, b, c, d, habcd⟩ := sl24_prod (h₀⁻¹ * π k * h₀)
  have hdec : h₀⁻¹ * π k * h₀ = upper24 a * (swap24 * upper24 b * swap24⁻¹) * upper24 c *
      (swap24 * upper24 d * swap24⁻¹) := by
    rw [swap24_inv]
    ext i j
    rw [habcd]
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_upper24, coe_swap24]
    rw [f4_swap_upper, f4_swap_upper]
  obtain ⟨r₁, hr₁, e₁⟩ := hup a
  obtain ⟨r₂, hr₂, e₂⟩ := hup b
  obtain ⟨r₃, hr₃, e₃⟩ := hup c
  obtain ⟨r₄, hr₄, e₄⟩ := hup d
  have hπk' : π k = π (r₁ * (w * r₂ * w⁻¹) * r₃ * (w * r₄ * w⁻¹)) := by
    simp only [map_mul, map_inv]
    rw [e₁, e₂, e₃, e₄, hw]
    calc π k = h₀ * (h₀⁻¹ * π k * h₀) * h₀⁻¹ := by group
      _ = h₀ * (upper24 a * (swap24 * upper24 b * swap24⁻¹) * upper24 c *
          (swap24 * upper24 d * swap24⁻¹)) * h₀⁻¹ := by rw [hdec]
      _ = _ := by group
  refine ⟨r₁, r₂, r₃, r₄, hr₁, hr₂, hr₃, hr₄, ((r₁ * (w * r₂ * w⁻¹) * r₃ * (w * r₄ * w⁻¹))⁻¹ *
    k : ↥(kz T V)), ?_, ?_⟩
  · have hker : (r₁ * (w * r₂ * w⁻¹) * r₃ * (w * r₄ * w⁻¹))⁻¹ * k ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hπk', inv_mul_cancel]
    rw [hπk, Subgroup.mem_subgroupOf] at hker
    exact hker
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

end Ctx764

end CFSG.Quasithin.H13.L32A
