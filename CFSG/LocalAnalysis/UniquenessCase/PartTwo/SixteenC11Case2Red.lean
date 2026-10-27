module

public import CFSG.GroupTheory.SupCommute
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11RouteF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbSyl
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.WreathSylow
import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

section Model

variable {W : Type} [CommGroup W]

@[expose] def S16C11Model (X K : Subgroup (MulAut W)) (J₀ : Subgroup W) : Prop :=
  ∃ (s : ↥K ≃* Equiv.Perm (Fin 3)) (ψ : W ≃* ↥(s16c2m_Triples ↥J₀)),
    (∀ (κ : ↥K) (w : W) (i : Fin 3), (ψ ((κ : MulAut W) w)).1 i = (ψ w).1 ((s κ)⁻¹ i)) ∧
      ∀ g ∈ X, (∀ k ∈ K, g * k = k * g) → ∀ (w : W) (i : Fin 3),
        (((ψ (g w)).1 i : ↥J₀) : W) = g (((ψ w).1 i : ↥J₀) : W)

theorem s16c11_model_of_cfg2 [Finite W] {X L K : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (F : Cfg2Setting X L J₀ J₁) (hKX : K ≤ X) (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k)
    (hK : IsSym ↥K 3) (hE₀ : Z391.EndUnitsTrivial L J₀) (hE₁ : Z391.EndUnitsTrivial L J₁) :
    S16C11Model X K J₀ := by
  obtain ⟨s, ψ, -, -, h3, h4⟩ := s16c2m_model F hKX hKL hK hE₀ hE₁
  exact ⟨s, ψ, h3, h4⟩

theorem s16c11_exists_fixed_of_isPGroup_two {P : Subgroup (Equiv.Perm (Fin 3))}
    (hP : IsPGroup 2 ↥P) : ∃ k : Fin 3, ∀ a ∈ P, a k = k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Fin 3)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; decide)
  exact ⟨k, fun a ha => by simpa using hk ⟨a, ha⟩⟩

theorem s16c11_exists_vec {J₀ : Subgroup W} (hsq : ∀ w : W, w ^ 2 = 1)
    (ψ : W ≃* ↥(s16c2m_Triples ↥J₀)) {y : W} (hy : y ∈ J₀) (k : Fin 3) :
    ∃ w : W, ∀ i : Fin 3, (((ψ w).1 i : ↥J₀) : W) = if i = k then 1 else y := by
  have hyy : (⟨y, hy⟩ : ↥J₀) * ⟨y, hy⟩ = 1 :=
    Subtype.ext (by simpa [pow_two] using hsq y)
  have ht : (fun i : Fin 3 => if i = k then (1 : ↥J₀) else ⟨y, hy⟩) ∈ s16c2m_Triples ↥J₀ := by
    rw [s16c2m_mem_Triples_iff]
    fin_cases k <;> simp [hyy]
  refine ⟨ψ.symm ⟨_, ht⟩, fun i => ?_⟩
  rw [MulEquiv.apply_symm_apply]
  by_cases hik : i = k <;> simp [hik]

theorem s16c11_smul_vec_of_fix {K : Subgroup (MulAut W)} {J₀ : Subgroup W}
    (s : ↥K ≃* Equiv.Perm (Fin 3)) (ψ : W ≃* ↥(s16c2m_Triples ↥J₀))
    (hs : ∀ (κ : ↥K) (w : W) (i : Fin 3), (ψ ((κ : MulAut W) w)).1 i = (ψ w).1 ((s κ)⁻¹ i))
    {y : W} {k : Fin 3} {w : W}
    (hw : ∀ i : Fin 3, (((ψ w).1 i : ↥J₀) : W) = if i = k then 1 else y)
    {κ : ↥K} (hκ : s κ k = k) : (κ : MulAut W) w = w := by
  have hiff : ∀ i : Fin 3, (s κ)⁻¹ i = k ↔ i = k := by
    intro i
    rw [Equiv.Perm.inv_eq_iff_eq, hκ]
  apply ψ.injective
  apply Subtype.ext
  funext i
  rw [hs κ w i]
  apply Subtype.ext
  rw [hw ((s κ)⁻¹ i), hw i]
  simp only [hiff]

theorem s16c11_exists_fixV_vec [Finite W] {X K L₀ T : Subgroup (MulAut W)} {J₀ : Subgroup W}
    (hsq : ∀ w : W, w ^ 2 = 1)
    (s : ↥K ≃* Equiv.Perm (Fin 3)) (ψ : W ≃* ↥(s16c2m_Triples ↥J₀))
    (hs : ∀ (κ : ↥K) (w : W) (i : Fin 3), (ψ ((κ : MulAut W) w)).1 i = (ψ w).1 ((s κ)⁻¹ i))
    (hg : ∀ g ∈ X, (∀ k ∈ K, g * k = k * g) → ∀ (w : W) (i : Fin 3),
      (((ψ (g w)).1 i : ↥J₀) : W) = g (((ψ w).1 i : ↥J₀) : W))
    (hKL : ∀ k ∈ K, ∀ l ∈ L₀, k * l = l * k) (hL₀X : L₀ ≤ X) (hTp : IsPGroup 2 ↥T)
    (hTdec : ∀ t ∈ T, ∃ a ∈ T ⊓ K, ∃ b ∈ T ⊓ L₀, t = a * b)
    {y : W} (hy : y ∈ J₀) (hfix : ∀ t ∈ T ⊓ L₀, t y = y) :
    ∃ (k : Fin 3) (w : W), w ∈ fixV T ∧
      ∀ i : Fin 3, (((ψ w).1 i : ↥J₀) : W) = if i = k then 1 else y := by
  have hP : IsPGroup 2 ↥(((T ⊓ K).subgroupOf K).map s.toMonoidHom) :=
    (hTp.to_inf_left.comap_subtype (K := K)).map s.toMonoidHom
  obtain ⟨k, hk⟩ := s16c11_exists_fixed_of_isPGroup_two hP
  have hk' : ∀ a (ha : a ∈ T ⊓ K), s ⟨a, (Subgroup.mem_inf.1 ha).2⟩ k = k := by
    intro a ha
    exact hk (s.toMonoidHom ⟨a, (Subgroup.mem_inf.1 ha).2⟩)
      (Subgroup.mem_map_of_mem s.toMonoidHom (Subgroup.mem_subgroupOf.mpr ha))
  obtain ⟨w, hw⟩ := s16c11_exists_vec hsq ψ hy k
  have hbw : ∀ b ∈ T ⊓ L₀, b w = w := by
    intro b hb
    have hbL : b ∈ L₀ := (Subgroup.mem_inf.1 hb).2
    apply ψ.injective
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rw [hg b (hL₀X hbL) (fun k' hk' => (hKL k' hk' b hbL).symm) w i, hw i]
    by_cases hik : i = k
    · simp [hik]
    · simp [hik, hfix b hb]
  have haw : ∀ a ∈ T ⊓ K, a w = w := by
    intro a ha
    exact s16c11_smul_vec_of_fix s ψ hs hw (κ := ⟨a, (Subgroup.mem_inf.1 ha).2⟩) (hk' a ha)
  refine ⟨k, w, ?_, hw⟩
  rw [mem_fixV]
  intro t ht
  obtain ⟨a, ha, b, hb, rfl⟩ := hTdec t ht
  rw [MulAut.mul_apply, hbw b hb, haw a ha]

theorem s16c11_fix_of_smul_vec {X K L₀ : Subgroup (MulAut W)} {J₀ : Subgroup W}
    (s : ↥K ≃* Equiv.Perm (Fin 3)) (ψ : W ≃* ↥(s16c2m_Triples ↥J₀))
    (hs : ∀ (κ : ↥K) (w : W) (i : Fin 3), (ψ ((κ : MulAut W) w)).1 i = (ψ w).1 ((s κ)⁻¹ i))
    (hg : ∀ g ∈ X, (∀ k ∈ K, g * k = k * g) → ∀ (w : W) (i : Fin 3),
      (((ψ (g w)).1 i : ↥J₀) : W) = g (((ψ w).1 i : ↥J₀) : W))
    (hKL : ∀ k ∈ K, ∀ l ∈ L₀, k * l = l * k) (hL₀X : L₀ ≤ X)
    {y : W} (hy1 : y ≠ 1) {k : Fin 3} {w : W}
    (hw : ∀ i : Fin 3, (((ψ w).1 i : ↥J₀) : W) = if i = k then 1 else y)
    {κ : ↥K} {ξ : MulAut W} (hξ : ξ ∈ L₀) (hc : ((κ : MulAut W) * ξ) w = w) :
    s κ k = k ∧ ξ y = y := by
  have hcomm : ∀ k' ∈ K, ξ * k' = k' * ξ := fun k' hk' => (hKL k' hk' ξ hξ).symm
  have hcoord : ∀ i : Fin 3,
      (((ψ w).1 i : ↥J₀) : W) = ξ (((ψ w).1 ((s κ)⁻¹ i) : ↥J₀) : W) := by
    intro i
    calc (((ψ w).1 i : ↥J₀) : W)
        = (((ψ (((κ : MulAut W) * ξ) w)).1 i : ↥J₀) : W) :=
          congrArg (fun u : W => (((ψ u).1 i : ↥J₀) : W)) hc.symm
      _ = (((ψ ((κ : MulAut W) (ξ w))).1 i : ↥J₀) : W) := by rw [MulAut.mul_apply]
      _ = (((ψ (ξ w)).1 ((s κ)⁻¹ i) : ↥J₀) : W) := by rw [hs κ (ξ w) i]
      _ = ξ (((ψ w).1 ((s κ)⁻¹ i) : ↥J₀) : W) := hg ξ (hL₀X hξ) hcomm w ((s κ)⁻¹ i)
  have key : ∀ i : Fin 3,
      (if i = k then 1 else y) = ξ (if (s κ)⁻¹ i = k then 1 else y) := by
    intro i
    rw [← hw i, hcoord i, hw ((s κ)⁻¹ i)]
  have hA : (s κ)⁻¹ k = k := by
    by_contra hne
    have h1 := key k
    rw [if_pos rfl, if_neg hne] at h1
    exact hy1 (ξ.injective (by rw [map_one, h1])).symm
  have hsk : s κ k = k := ((Equiv.Perm.inv_eq_iff_eq (f := s κ)).1 hA).symm
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin 3, i ≠ k := by fin_cases k <;> decide
  have hne' : (s κ)⁻¹ i₀ ≠ k := by
    intro h
    refine hi₀ ?_
    have hEq : (s κ)⁻¹ i₀ = (s κ)⁻¹ k := h.trans hA.symm
    simpa using congrArg (s κ) hEq
  have hξy : ξ y = y := by
    have h1 := key i₀
    rw [if_neg hi₀, if_neg hne'] at h1
    exact h1.symm
  exact ⟨hsk, hξy⟩

private theorem s16c11_case2red_perm_sq_of_fix (σ : Equiv.Perm (Fin 3)) (k : Fin 3)
    (h : σ k = k) : σ ^ 2 = 1 := by
  revert h
  revert σ
  revert k
  decide

theorem s16c11_isPGroup_inf_centSub_fixV [Finite W] {X K L₀ X₀ T : Subgroup (MulAut W)}
    {J₀ : Subgroup W} (hsq : ∀ w : W, w ^ 2 = 1)
    (s : ↥K ≃* Equiv.Perm (Fin 3)) (ψ : W ≃* ↥(s16c2m_Triples ↥J₀))
    (hs : ∀ (κ : ↥K) (w : W) (i : Fin 3), (ψ ((κ : MulAut W) w)).1 i = (ψ w).1 ((s κ)⁻¹ i))
    (hg : ∀ g ∈ X, (∀ k ∈ K, g * k = k * g) → ∀ (w : W) (i : Fin 3),
      (((ψ (g w)).1 i : ↥J₀) : W) = g (((ψ w).1 i : ↥J₀) : W))
    (hKL : ∀ k ∈ K, ∀ l ∈ L₀, k * l = l * k) (hL₀X : L₀ ≤ X) (hX₀L : X₀ ≤ L₀)
    (hTp : IsPGroup 2 ↥T)
    (hTdec : ∀ t ∈ T, ∃ a ∈ T ⊓ K, ∃ b ∈ T ⊓ L₀, t = a * b)
    (hT₀X₀ : T ⊓ L₀ ≤ X₀) (h3 : (T ⊓ L₀).relIndex X₀ = 3)
    {y : W} (hy : y ∈ J₀) (hfix : ∀ t ∈ T ⊓ L₀, t y = y) (hmov : ∃ g ∈ X₀, g y ≠ y) :
    IsPGroup 2 ↥((K ⊔ X₀) ⊓ centSub (fixV T)) := by
  obtain ⟨k, w, hwT, hw⟩ :=
    s16c11_exists_fixV_vec hsq s ψ hs hg hKL hL₀X hTp hTdec hy hfix
  have hy1 : y ≠ 1 := by
    intro hy1
    obtain ⟨g, -, hgy⟩ := hmov
    exact hgy (by rw [hy1, map_one])
  intro c
  obtain ⟨hc1, hc2⟩ := Subgroup.mem_inf.1 c.2
  obtain ⟨κ, hκK, ξ, hξX₀, hc_eq⟩ :=
    (CFSG.mem_sup_of_commute (fun a ha b hb => hKL a ha b (hX₀L hb))).1 hc1
  have hcw : (κ * ξ) w = w := by
    rw [hc_eq]
    exact (mem_centSub.1 hc2) w hwT
  obtain ⟨hκk, hξy⟩ := s16c11_fix_of_smul_vec s ψ hs hg hKL hL₀X hy1 hw
    (κ := ⟨κ, hκK⟩) (hX₀L hξX₀) hcw
  have hξT₀ : ξ ∈ T ⊓ L₀ :=
    s16c11_mem_of_fix_of_relIndex_three hT₀X₀ h3 hfix hmov hξX₀ hξy
  obtain ⟨m, hm⟩ := hTp ⟨ξ, hξT₀.1⟩
  have hξ2 : ξ ^ 2 ^ m = 1 := by
    simpa using congrArg (Subtype.val) hm
  have hperm : (s ⟨κ, hκK⟩) ^ 2 = 1 := s16c11_case2red_perm_sq_of_fix _ k hκk
  have hκ2 : κ ^ 2 = 1 := by
    have h1 : (⟨κ, hκK⟩ : ↥K) ^ 2 = 1 := by
      apply s.injective
      rw [map_pow, map_one, hperm]
    simpa using congrArg (Subtype.val) h1
  have hcm : Commute κ ξ := hKL κ hκK ξ (hX₀L hξX₀)
  have hκ1 : κ ^ 2 ^ (m + 1) = 1 := by
    rw [pow_succ', pow_mul, hκ2, one_pow]
  have hξ1 : ξ ^ 2 ^ (m + 1) = 1 := by
    rw [pow_succ, pow_mul, hξ2, one_pow]
  refine ⟨m + 1, ?_⟩
  apply Subtype.ext
  change c.1 ^ 2 ^ (m + 1) = 1
  rw [hc_eq.symm, hcm.mul_pow, hκ1, hξ1, mul_one]

private theorem s16c11_card_isSym_three {X : Type} [Group X] (h : IsSym X 3) :
    Nat.card X = 6 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  norm_num

private theorem s16c11_pow_three_of_mem {A : Type*} [Group A] [Finite A] {P : Subgroup A}
    {m n : ℕ} (hm : ¬ 3 ∣ m) (hP : Nat.card ↥P ∣ 3 * m) {x : A} (hx : x ∈ P)
    (hxn : x ^ 3 ^ n = 1) : x ^ 3 = 1 := by
  have h1 : orderOf x ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hxn
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
  have h2 : orderOf x ∣ 3 * m := (Subgroup.orderOf_dvd_natCard P hx).trans hP
  have hj1 : j ≤ 1 := by
    by_contra hlt
    have h9 : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 (by omega)
    rw [← hj] at h9
    have h3m : 3 ^ 2 ∣ 3 * m := h9.trans h2
    exact hm (by omega)
  refine orderOf_dvd_iff_pow_eq_one.1 ?_
  rw [hj]
  exact (pow_dvd_pow 3 hj1)

theorem s16c11_exponent_three {A : Type} [Group A] [Finite A] {K X₀ : Subgroup A} {a : ℕ}
    (hK : IsSym ↥K 3) (hcomm : ∀ k ∈ K, ∀ l ∈ X₀, k * l = l * k) (hinf : K ⊓ X₀ = ⊥)
    (hX₀ : Nat.card ↥X₀ = 3 * 2 ^ a) : ∀ x ∈ K ⊔ X₀, (∃ n : ℕ, x ^ 3 ^ n = 1) → x ^ 3 = 1 := by
  intro x hx ⟨n, hn⟩
  obtain ⟨κ, hκ, ξ, hξ, rfl⟩ :=
    (CFSG.mem_sup_of_commute (fun a ha b hb => hcomm a ha b hb) (x := x)).1 hx
  have hcm : Commute κ ξ := hcomm κ hκ ξ hξ
  rw [hcm.mul_pow] at hn
  have h1 : κ ^ 3 ^ n = (ξ ^ 3 ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hn
  have h2 : κ ^ 3 ^ n ∈ K ⊓ X₀ :=
    ⟨K.pow_mem hκ _, by rw [h1]; exact X₀.inv_mem (X₀.pow_mem hξ _)⟩
  rw [hinf, Subgroup.mem_bot] at h2
  have h3 : ξ ^ 3 ^ n = 1 := by
    rw [h2, one_mul] at hn
    exact hn
  have hκ3 : κ ^ 3 = 1 :=
    s16c11_pow_three_of_mem (P := K) (m := 2) (by omega)
      (dvd_of_eq (by rw [s16c11_card_isSym_three hK])) hκ h2
  have hξ3 : ξ ^ 3 = 1 :=
    s16c11_pow_three_of_mem (P := X₀) (m := 2 ^ a)
      (fun h => by have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h; omega)
      (dvd_of_eq hX₀) hξ h3
  rw [hcm.mul_pow, hκ3, hξ3, one_mul]

theorem s16c11_nine_dvd_card_sup {A : Type} [Group A] [Finite A] {K X₀ : Subgroup A} {a : ℕ}
    (hK : IsSym ↥K 3) (hcomm : ∀ k ∈ K, ∀ l ∈ X₀, k * l = l * k) (hinf : K ⊓ X₀ = ⊥)
    (hX₀ : Nat.card ↥X₀ = 3 * 2 ^ a) : 3 ^ 2 ∣ Nat.card ↥(K ⊔ X₀) := by
  rw [CFSG.card_sup_eq_mul_of_commute K X₀ (fun a ha b hb => hcomm a ha b hb) hinf,
    s16c11_card_isSym_three hK, hX₀]
  exact ⟨2 ^ (a + 1), by ring⟩

theorem s16c11_padicValNat_three_of_isPGroup_two {A : Type*} [Group A] {P : Subgroup A}
    [Finite P] (hP : IsPGroup 2 ↥P) : padicValNat 3 (Nat.card ↥P) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  refine padicValNat.eq_zero_of_not_dvd ?_
  rw [hm]
  intro h
  have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

theorem s16c11_comm_of_isInternalDirect {A : Type*} [Group A] {K L₀ X : Subgroup A}
    (hI : IsInternalDirect K L₀ X) : ∀ k ∈ K, ∀ l ∈ L₀, k * l = l * k := by
  intro k hk l hl
  have h1 : ⁅k, l⁆ ∈ ⁅K, L₀⁆ := Subgroup.commutator_mem_commutator hk hl
  rw [hI.1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem s16c11_card_of_relIndex_three {H : Type*} [Group H] [Finite H] {T X : Subgroup H}
    (hT : IsPGroup 2 ↥T) (hTX : T ≤ X) (h3 : T.relIndex X = 3) :
    ∃ a : ℕ, Nat.card ↥X = 3 * 2 ^ a := by
  obtain ⟨a, ha⟩ := hT.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card T X
  rw [inf_eq_left.mpr hTX, h3, ha] at h1
  exact ⟨a, h1.symm⟩

theorem s16c11_mem_of_model {X K : Subgroup (MulAut W)} {J₀ : Subgroup W}
    (hsq : ∀ w : W, w ^ 2 = 1) (hM : S16C11Model X K J₀) {x : MulAut W} (hx : x ∈ X)
    (hxK : ∀ k ∈ K, x * k = k * x) {y : W} (hy : y ∈ J₀) : x y ∈ J₀ := by
  obtain ⟨s, ψ, hs, hg⟩ := hM
  obtain ⟨w, hw⟩ := s16c11_exists_vec hsq ψ hy 0
  have h1 := hg x hx hxK w 1
  rw [hw 1] at h1
  simp at h1
  rw [← h1]
  exact ((ψ (x w)).1 1).2

theorem s16c11_routeF_data_of_rf3 [Finite W] {X K L₀ T : Subgroup (MulAut W)} {J₀ : Subgroup W}
    (hsq : ∀ w : W, w ^ 2 = 1) (hM : S16C11Model X K J₀) (hK : IsSym ↥K 3)
    (hI : IsInternalDirect K L₀ X) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X)
    (hrf : S16C11RF3 L₀ J₀) :
    ∃ Xbar : Subgroup (MulAut W), Xbar ≤ X ∧ T ≤ Xbar ∧ Group.IsSolvable ↥Xbar ∧
      (∀ x ∈ Xbar, (∃ n : ℕ, x ^ 3 ^ n = 1) → x ^ 3 = 1) ∧
      padicValNat 3 (Nat.card ↥(Xbar ⊓ centSub (fixV T))) + 2 ≤
        padicValNat 3 (Nat.card ↥Xbar) := by
  have hKL := s16c11_comm_of_isInternalDirect hI
  obtain ⟨-, hinf, hsup⟩ := hI
  subst hsup
  obtain ⟨s, ψ, hs, hg⟩ := hM
  have hdisj : Disjoint K L₀ := disjoint_iff.2 hinf
  have hL₀X : L₀ ≤ K ⊔ L₀ := le_sup_right
  have hKc : K ≤ Subgroup.centralizer (L₀ : Set (MulAut W)) := fun k hk =>
    Subgroup.mem_centralizer_iff.2 fun l hl => (hKL k hk l hl).symm
  have hnorm : K ⊔ L₀ ≤ normalizer (L₀ : Set (MulAut W)) :=
    sup_le (hKc.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hT₀ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L₀) L₀ := hT.inf_of_le_normalizer hL₀X hnorm
  obtain ⟨hT₀L, hT₀p, hT₀i⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hT₀
  obtain ⟨X₀, hX₀L, hT₀X₀, h3, y, hy, hfix, hmov⟩ := hrf (T ⊓ L₀) hT₀L hT₀p hT₀i
  have hTp : IsPGroup 2 ↥T := (CFSG.ABGLocalTools.isSylowOf_iff.1 hT).2.1
  have hTdec : ∀ t ∈ T, ∃ a ∈ T ⊓ K, ∃ b ∈ T ⊓ L₀, t = a * b := fun t ht =>
    CFSG.EvenSporadicStandard.M23Std.exists_mul_mem_of_isSylowOf_sup hKL hdisj hT ht
  obtain ⟨a, ha⟩ := s16c11_card_of_relIndex_three hT₀p hT₀X₀ h3
  have hKX₀ : ∀ k ∈ K, ∀ l ∈ X₀, k * l = l * k := fun k hk l hl => hKL k hk l (hX₀L hl)
  have hinf' : K ⊓ X₀ = ⊥ :=
    eq_bot_iff.2 (hinf ▸ inf_le_inf_left K hX₀L)
  have hcard : Nat.card ↥(K ⊔ X₀) = 6 * (3 * 2 ^ a) := by
    rw [CFSG.card_sup_eq_mul_of_commute K X₀ (fun a ha b hb => hKX₀ a ha b hb) hinf',
      s16c11_card_isSym_three hK, ha]
  refine ⟨K ⊔ X₀, sup_le_sup_left hX₀L K, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨a', ha', b, hb, rfl⟩ := hTdec t ht
    exact mul_mem (mem_sup_left ha'.2) (mem_sup_right (hT₀X₀ hb))
  · refine TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three
      (a := a + 1) (b := 2) ?_
    rw [hcard]
    exact ⟨1, by ring⟩
  · exact s16c11_exponent_three hK hKX₀ hinf' ha
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h2 : IsPGroup 2 ↥((K ⊔ X₀) ⊓ centSub (fixV T)) :=
      s16c11_isPGroup_inf_centSub_fixV hsq s ψ hs hg hKL hL₀X hX₀L hTp hTdec hT₀X₀ h3 hy hfix hmov
    rw [s16c11_padicValNat_three_of_isPGroup_two h2]
    have h9 : 3 ^ 2 ∣ Nat.card ↥(K ⊔ X₀) := s16c11_nine_dvd_card_sup hK hKX₀ hinf' ha
    have hpos : Nat.card ↥(K ⊔ X₀) ≠ 0 := Nat.card_pos.ne'
    simpa using (padicValNat_dvd_iff_le (p := 3) hpos).1 h9

theorem s16c11_normalizer_le_of_case2_rf3 {G : Type} [Group G] [Finite G] (D : Data G)
    (h61 : UC6.R6_1 D) (h1610 : R16_10_2 D) (h169 : R16_9 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (hsig : D.sig = {3})
    {L₀ : Subgroup (MulAut (Vtil V₀ V hV))} {J₀ J₁ : Subgroup (Vtil V₀ V hV)}
    (hF : Cfg2Setting (Mbar D.M V₀ V hV) (lBar V₀ V hV L) J₀ J₁)
    (hKX : kBar D.M V₀ V hV L ≤ Mbar D.M V₀ V hV)
    (hKL : ∀ k ∈ kBar D.M V₀ V hV L, ∀ l ∈ lBar V₀ V hV L, k * l = l * k)
    (hK : IsSym ↥(kBar D.M V₀ V hV L) 3)
    (hE₀ : Z391.EndUnitsTrivial (lBar V₀ V hV L) J₀)
    (hE₁ : Z391.EndUnitsTrivial (lBar V₀ V hV L) J₁)
    (hI : IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV))
    (hrf : S16C11RF3 L₀ J₀) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hP := hc.setting.hyp16.hyp125.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 (barSub V₀ V hV D.T) (Mbar D.M V₀ V hV) :=
    CFSG.ABGLocalTools.isSylowOf_iff.2
      (s16c1_barSub_sylow hMst (TwelveShort.isSylowIn_of_le D D.sylowM.le))
  obtain ⟨Xbar, hXM, hTX, hsolv, hexp, hcount⟩ :=
    s16c11_routeF_data_of_rf3 hF.sq (s16c11_model_of_cfg2 hF hKX hKL hK hE₀ hE₁) hK hI hT hrf
  exact s16c11_normalizer_le_of_routeF D h61 h1610 h169 hV hc
    (by rw [hsig]; exact Set.mem_singleton 3) hXM hTX hsolv hexp hcount

end Model

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
