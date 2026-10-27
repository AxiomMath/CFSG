module

public import CFSG.Quasithin.EmptyFaithful.S1565L15
public import CFSG.Quasithin.EmptyFaithful.F918C19

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open Matrix
open scoped commutatorElement

theorem isSimpleGroup_statedSL2 {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    IsSimpleGroup ↥(StatedSL 2 K) := by
  have : Fintype K := Fintype.ofFinite K
  have h4 : ∃ s : Finset K, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hK)
    exact ⟨s, hs⟩
  have hsimple : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) K) :=
    (CFSG.LinearGroups.linear_projective_simple (n := 2) le_rfl (Or.inr h4)).2.1
  have hcenter : Subgroup.center (SpecialLinearGroup (Fin 2) K) = ⊥ := by
    ext A
    rw [Subgroup.mem_bot]
    constructor
    · intro hA
      obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
      have hr1 : r = 1 := by
        rw [Fintype.card_fin] at hr
        have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
        have h3 : (r + 1) ^ 2 = 0 := by linear_combination hr + (r + 1) * h2
        have h5 : r + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h3
        have h6 : r = -1 := eq_neg_of_add_eq_zero_left h5
        rw [h6]
        exact (CharTwo.neg_eq (1 : K))
      apply Subtype.ext
      rw [← hrA, hr1]
      simp
    · rintro rfl
      exact Subgroup.one_mem _
  let e1 : ProjectiveSpecialLinearGroup (Fin 2) K ≃* SpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  have h1 : IsSimpleGroup (SpecialLinearGroup (Fin 2) K) := MulEquiv.isSimpleGroup e1.symm
  exact MulEquiv.isSimpleGroup (specialLinearGroupEquivStatedSL 2 K).symm

theorem eq_one_of_mul_fixed {K : Type} [Field K] [CharP K 2] {A X : Matrix (Fin 2) (Fin 2) K}
    (hdet : A.det = 1) {r : ℕ} (hr : Odd r) (hAr : A ^ r = 1) (hAX : A * X = X) (hX : X ≠ 0) :
    A = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨i, j, hij⟩ : ∃ i j, X i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hX (Matrix.ext fun i j => hcon i j)
  set v : Fin 2 → K := fun k => X k j with hv
  have hv0 : v ≠ 0 := fun h => hij (congrFun h i)
  have hk : ∀ k, A.mulVec v k = v k := by
    intro k
    have := congrFun (congrFun hAX k) j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, hv] using this
  have hAv : (A - 1).mulVec v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    funext k
    rw [Pi.sub_apply, hk k, sub_self]
    rfl
  have hdet0 : (A - 1).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hAv⟩
  have hA : A = !![A 0 0, A 0 1; A 1 0, A 1 1] := Matrix.eta_fin_two A
  rw [Matrix.det_fin_two] at hdet hdet0
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at hdet0
  have htr : A 1 1 = A 0 0 := by
    have : A 1 1 + A 0 0 = 0 := by linear_combination -hdet0 + hdet + h2
    have h6 : A 1 1 = - A 0 0 := eq_neg_of_add_eq_zero_left this
    rw [h6]
    exact (CharTwo.neg_eq (A 0 0))
  rw [htr] at hdet
  have e00 : (A * A) 0 0 = 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination hdet + (A 0 1 * A 1 0) * h2
  have e11 : (A * A) 1 1 = 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, htr]
    linear_combination hdet + (A 0 1 * A 1 0) * h2
  have e01 : (A * A) 0 1 = 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, htr]
    linear_combination (A 0 0 * A 0 1) * h2
  have e10 : (A * A) 1 0 = 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, htr]
    linear_combination (A 0 0 * A 1 0) * h2
  have hsq : A * A = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [e00, e11, e01, e10]
  obtain ⟨k, rfl⟩ := hr
  have : A ^ (2 * k + 1) = A := by
    rw [pow_succ, pow_mul, sq, hsq, one_pow, one_mul]
  exact this.symm.trans hAr

theorem two_dvd_card_of_psl2_or_sz {X : Type} [Group X] {n : ℕ}
    (hn : 3 ≤ n) (h : IsPSL 2 2 n X ∨ IsSz n X) : 2 ∣ Nat.card X := by
  rcases h with h | h
  · obtain ⟨-, hc⟩ := Vol2.Ch11.SecA.card_of_isPSL_two_two h
    rw [hc]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  · obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
    subst hf
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero) _) _

theorem isQuasisimple_of_psl2_or_sz {X : Type} [Group X] {n : ℕ}
    (hn : 3 ≤ n) (h : IsPSL 2 2 n X ∨ IsSz n X) : CFSG.IsQuasisimple X := by
  have hs : IsSimpleGroup X := isSimpleGroup_of_psl2_or_sz h
  have h504 := le_card_of_psl2_or_sz hn h
  have h2 := two_dvd_card_of_psl2_or_sz hn h
  have hnc : ∃ a b : X, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hfin : Finite X := Nat.finite_of_card_ne_zero (by omega)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 h2
    have hnorm : (Subgroup.zpowers x).Normal := ⟨fun n hn g => by
      rw [hcon g n, mul_assoc, mul_inv_cancel, mul_one]
      exact hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h0 | h1
    · have hx1 : x = 1 := Subgroup.mem_bot.mp (h0 ▸ Subgroup.mem_zpowers x)
      rw [hx1, orderOf_one] at hx
      omega
    · have h3 : Nat.card (Subgroup.zpowers x) = Nat.card X := by rw [h1]; exact Subgroup.card_top
      rw [Nat.card_zpowers, hx] at h3
      omega
  exact isQuasisimple_of_perfect_of_isSimpleGroup (by
    have hc : (commutator X).Normal := inferInstance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h0 | h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have : ⁅a, b⁆ ∈ commutator X :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h0, Subgroup.mem_bot, commutatorElement_def] at this
      exact hab (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp this))
    · exact ⟨h1⟩) hs

section Tensor

variable {W : Type} [CommGroup W]

abbrev TensorE2 (K : Type) [Field K] : Type := Multiplicative (Matrix (Fin 2) (Fin 2) K)

abbrev TensorG2 (K : Type) [Field K] : Type := ↥(StatedSL 2 K) × ↥(StatedSL 2 K)

@[expose] def IsTensorData2 {K : Type} [Field K] (Mp : Subgroup (MulAut W))
    (π : TensorG2 K →* ↥Mp) (β : W ≃* TensorE2 K) : Prop :=
  ∀ (γ : TensorG2 K) (w : W), β ((π γ : MulAut W) w) = tensorAct 2 K γ (β w)

theorem exists_tensorData2 {Mp : Subgroup (MulAut W)} {n' : ℕ}
    (h : Omega4PlusModule (autSub Mp (⊤ : Subgroup W)) n') :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n' ∧
      ∃ (π : TensorG2 K →* ↥Mp) (β : W ≃* TensorE2 K),
        Function.Surjective π ∧ IsTensorData2 Mp π β := by
  obtain ⟨K, fK, finK, hK, π', hπ'⟩ := h
  refine ⟨K, fK, finK, hK, ?_⟩
  obtain ⟨hs, -, -, -, -, -, -, β₀, hβs₀, hβk₀, hβe₀⟩ := hπ'
  let β' : ↥(⊤ : Subgroup ↥(⊤ : Subgroup W)) →* (↥(⊤ : Subgroup (TensorE2 K)) ⧸
      (⊥ : Subgroup (TensorE2 K)).subgroupOf ⊤) := β₀
  have hβs : Function.Surjective β' := hβs₀
  have hβk : ∀ u, β' u = 1 ↔ (u : ↥(⊤ : Subgroup W)) ∈ (⊥ : Subgroup ↥(⊤ : Subgroup W)) := hβk₀
  have hβe : ∀ (γ : TensorG2 K) (u : ↥(⊤ : Subgroup ↥(⊤ : Subgroup W)))
      (m : ↥(⊤ : Subgroup (TensorE2 K)))
      (hu : (((π' γ : ↥(autSub Mp (⊤ : Subgroup W))) : MulAut ↥(⊤ : Subgroup W))
        (u : ↥(⊤ : Subgroup W))) ∈ (⊤ : Subgroup ↥(⊤ : Subgroup W)))
      (hm : tensorAct 2 K γ (m : TensorE2 K) ∈ (⊤ : Subgroup (TensorE2 K))),
      β' u = QuotientGroup.mk m →
        β' ⟨(((π' γ : ↥(autSub Mp (⊤ : Subgroup W))) : MulAut ↥(⊤ : Subgroup W))
          (u : ↥(⊤ : Subgroup W))), hu⟩ =
            QuotientGroup.mk ⟨tensorAct 2 K γ (m : TensorE2 K), hm⟩ :=
    hβe₀
  let eq : ↥Mp ≃* ↥(autSub Mp (⊤ : Subgroup W)) :=
    MulEquiv.ofBijective (restrTop Mp) (restrTop_bijective Mp)
  let π : TensorG2 K →* ↥Mp := eq.symm.toMonoidHom.comp π'
  have hπs : Function.Surjective π := eq.symm.surjective.comp hs
  have hinj : Function.Injective β' := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let e3 : ↥(⊤ : Subgroup ↥(⊤ : Subgroup W)) ≃*
      (↥(⊤ : Subgroup (TensorE2 K)) ⧸ (⊥ : Subgroup (TensorE2 K)).subgroupOf ⊤) :=
    MulEquiv.ofBijective β' ⟨hinj, hβs⟩
  let β : W ≃* TensorE2 K :=
    ((Subgroup.topEquiv (G := W)).symm.trans
      (Subgroup.topEquiv (G := ↥(⊤ : Subgroup W))).symm).trans
        (e3.trans (B5.natQuotEquiv (TensorE2 K)))
  refine ⟨π, β, hπs, fun γ w => ?_⟩
  have hrestr : restrTop Mp (π γ) = π' γ := eq.apply_symm_apply (π' γ)
  have hact : ∀ u : ↥(⊤ : Subgroup W),
      (((π' γ : ↥(autSub Mp (⊤ : Subgroup W))) : MulAut ↥(⊤ : Subgroup W)) u : W) =
        ((π γ : ↥Mp) : MulAut W) (u : W) := by
    intro u
    rw [← hrestr]
    rfl
  let uw : ↥(⊤ : Subgroup W) := ⟨w, trivial⟩
  let u₀ : ↥(⊤ : Subgroup ↥(⊤ : Subgroup W)) := ⟨uw, trivial⟩
  let m : ↥(⊤ : Subgroup (TensorE2 K)) := ⟨β w, trivial⟩
  have hm : β' u₀ = QuotientGroup.mk m := by
    apply (B5.natQuotEquiv (TensorE2 K)).injective
    exact (B5.natQuotEquiv_mk (TensorE2 K) (β w)).symm
  have hu : (((π' γ : ↥(autSub Mp (⊤ : Subgroup W))) : MulAut ↥(⊤ : Subgroup W))
      (u₀ : ↥(⊤ : Subgroup W))) ∈ (⊤ : Subgroup ↥(⊤ : Subgroup W)) := trivial
  have hm' : tensorAct 2 K γ (m : TensorE2 K) ∈ (⊤ : Subgroup (TensorE2 K)) := trivial
  have h1 := hβe γ u₀ m hu hm' hm
  have h2 : (⟨((π' γ : ↥(autSub Mp (⊤ : Subgroup W))) : MulAut ↥(⊤ : Subgroup W))
      (u₀ : ↥(⊤ : Subgroup W)), hu⟩ : ↥(⊤ : Subgroup ↥(⊤ : Subgroup W))) =
      ⟨⟨((π γ : ↥Mp) : MulAut W) w, trivial⟩, trivial⟩ := Subtype.ext (Subtype.ext (hact uw))
  rw [h2] at h1
  have h3 : β ((π γ : MulAut W) w) = B5.natQuotEquiv (TensorE2 K)
      (β' ⟨⟨((π γ : ↥Mp) : MulAut W) w, trivial⟩, trivial⟩) := rfl
  rw [h3, h1]
  exact B5.natQuotEquiv_mk (TensorE2 K) _

theorem scalar_statedSL_two_charTwo {K : Type} [Field K] [CharP K 2] :
    ∀ g ∈ StatedSL 2 K, ∀ c : K, (g : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) c → c = 1 :=
  CFSG.Quasithin.Vol2.Ch10.SecA.scalar_statedSL_two

theorem tensor_faithful2 {K : Type} [Field K] [CharP K 2] (γ : TensorG2 K)
    (h : ∀ X : TensorE2 K, tensorAct 2 K γ X = X) : γ = 1 := by
  have hf := CFSG.Quasithin.Vol2.Ch10.SecA.tensorPair_faithful (StatedSL 2 K) (StatedSL 2 K)
    scalar_statedSL_two_charTwo
  exact hf γ fun m _ => Subgroup.mem_bot.mpr (by
    rw [show (CFSG.Quasithin.H13.tensorPairModel (StatedSL 2 K) (StatedSL 2 K)).act γ m = m from
      h m]
    exact mul_inv_cancel m)

theorem IsTensorData2.injective {K : Type} [Field K] [CharP K 2] {Mp : Subgroup (MulAut W)}
    {π : TensorG2 K →* ↥Mp} {β : W ≃* TensorE2 K} (hd : IsTensorData2 Mp π β) :
    Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  refine tensor_faithful2 γ fun X => ?_
  obtain ⟨w, rfl⟩ := β.surjective X
  rw [← hd γ w, hγ]
  rfl

end Tensor

section Ident2

variable {W : Type} [CommGroup W]

@[expose] def factorL2 {K : Type} [Field K] (Mp : Subgroup (MulAut W)) (π : TensorG2 K →* ↥Mp) :
    Subgroup (MulAut W) :=
  (Mp.subtype.comp (π.comp (MonoidHom.inl _ _))).range

@[expose] def factorR2 {K : Type} [Field K] (Mp : Subgroup (MulAut W)) (π : TensorG2 K →* ↥Mp) :
    Subgroup (MulAut W) :=
  (Mp.subtype.comp (π.comp (MonoidHom.inr _ _))).range

theorem mem_factorL2 {K : Type} [Field K] {Mp : Subgroup (MulAut W)} {π : TensorG2 K →* ↥Mp}
    {x : MulAut W} :
    x ∈ factorL2 Mp π ↔ ∃ g : ↥(StatedSL 2 K), ((π (g, 1) : ↥Mp) : MulAut W) = x := by
  simp [factorL2, MonoidHom.mem_range]

theorem mem_factorR2 {K : Type} [Field K] {Mp : Subgroup (MulAut W)} {π : TensorG2 K →* ↥Mp}
    {x : MulAut W} :
    x ∈ factorR2 Mp π ↔ ∃ g : ↥(StatedSL 2 K), ((π (1, g) : ↥Mp) : MulAut W) = x := by
  simp [factorR2, MonoidHom.mem_range]

theorem eq_factor_or2 {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    {Mp L L' : Subgroup (MulAut W)} {π : TensorG2 K →* ↥Mp} {β : W ≃* TensorE2 K}
    (hd : IsTensorData2 Mp π β) (hπs : Function.Surjective π) (hMp : Mp = L ⊔ L')
    (hLL' : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) (hLq : CFSG.IsQuasisimple ↥L) (hL1 : L ≠ ⊥) :
    L = factorL2 Mp π ∨ L = factorR2 Mp π := by
  have hinj := hd.injective
  have hLMp : L ≤ Mp := hMp ▸ le_sup_left
  have hAMp : factorL2 Mp π ≤ Mp := by
    rintro _ ⟨g, rfl⟩
    exact (π (g, 1)).2
  have hBMp : factorR2 Mp π ≤ Mp := by
    rintro _ ⟨g, rfl⟩
    exact (π (1, g)).2
  have hsup : factorL2 Mp π ⊔ factorR2 Mp π = Mp := by
    refine le_antisymm (sup_le hAMp hBMp) fun x hx => ?_
    obtain ⟨⟨g, h⟩, hγ⟩ := hπs ⟨x, hx⟩
    have e : ((π (g, h) : ↥Mp) : MulAut W) =
        ((π (g, 1) : ↥Mp) : MulAut W) * ((π (1, h) : ↥Mp) : MulAut W) := by
      rw [← Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    have hx' : x = ((π (g, h) : ↥Mp) : MulAut W) := by rw [hγ]
    rw [hx', e]
    exact Subgroup.mul_mem_sup (mem_factorL2.mpr ⟨g, rfl⟩) (mem_factorR2.mpr ⟨h, rfl⟩)
  have hcomm : ∀ a ∈ factorL2 Mp π, ∀ b ∈ factorR2 Mp π, a * b = b * a := by
    rintro _ ha _ hb
    obtain ⟨g, rfl⟩ := mem_factorL2.mp ha
    obtain ⟨h, rfl⟩ := mem_factorR2.mp hb
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
    simp
  have hLn : ∀ x ∈ Mp, ∀ k ∈ L, x * k * x⁻¹ ∈ L := fun x hx k hk =>
    InternalSec.conj_mem_of_mem_sup_of_commute hLL' x (hMp ▸ hx) k hk
  have hLnorm : Mp ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun x hx =>
    Subgroup.mem_normalizer_iff.mpr fun k =>
      ⟨fun hk => hLn x hx k hk, fun hk => by
        have := hLn x⁻¹ (Mp.inv_mem hx) _ hk
        simpa [mul_assoc] using this⟩
  have hSL := isSimpleGroup_statedSL2 hK4
  have hAs : IsSimpleGroup ↥(factorL2 Mp π) :=
    MulEquiv.isSimpleGroup (MonoidHom.ofInjective (f := Mp.subtype.comp (π.comp (MonoidHom.inl _ _)))
      (fun a b hab => (Prod.mk.inj (hinj (Subtype.ext hab))).1)).symm
  have hBs : IsSimpleGroup ↥(factorR2 Mp π) :=
    MulEquiv.isSimpleGroup (MonoidHom.ofInjective (f := Mp.subtype.comp (π.comp (MonoidHom.inr _ _)))
      (fun a b hab => (Prod.mk.inj (hinj (Subtype.ext hab))).2)).symm
  rcases InternalSec.le_or_le_of_sup_eq hsup hcomm hLMp hLn hLq with h | h
  · exact Or.inl (eq_of_le_of_simple h (hAMp.trans hLnorm) hL1)
  · exact Or.inr (eq_of_le_of_simple h (hBMp.trans hLnorm) hL1)

end Ident2

theorem omegaGood_of : OmegaGood := by
  intro W _ _ M Mp L V t Q n hn3 hshape hMp hcomm hb₀ hΩ
  obtain ⟨hV, -, n', hpsl, hom⟩ := hΩ
  subst hV
  obtain ⟨b₀, hb₀L, hb₀Q, hb₀1, hb₀odd⟩ := hb₀
  have hLMp : L ≤ Mp := by rw [hMp]; exact le_sup_left
  have h504 := le_card_of_psl2_or_sz hn3 hshape
  have hLq := isQuasisimple_of_psl2_or_sz hn3 hshape
  have hL1 : L ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at h504
    omega
  obtain ⟨K, fK, finK, hK, π, β, hπs, hd⟩ := exists_tensorData2 hom
  have hn'3 : 3 ≤ n' := by
    obtain ⟨h1, hc⟩ := Vol2.Ch11.SecA.card_of_isPSL_two_two hpsl
    have h2 : Nat.card ↥(autSub L (⊤ : Subgroup W)) = Nat.card ↥L :=
      Nat.card_congr (autSubTopEquiv L).toEquiv
    by_contra hlt
    have h3 : n' ≤ 2 := by omega
    rw [h2] at hc
    rw [hc] at h504
    interval_cases n' <;> simp [Vol2.Ch11.SecA.oSL2] at h504
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n') (by rw [← Nat.card_eq_fintype_card, hK])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n' := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfact := eq_factor_or2 hK4 hd hπs hMp hcomm hLq hL1
  have hb₀Mp : b₀ ∈ Mp := hLMp hb₀L
  have hbr : b₀ ^ (orderOf b₀) = 1 := pow_orderOf_eq_one b₀
  have key : ∀ w : W, b₀ w = w → w = 1 := by
    intro w hw
    have hinj := hd.injective
    rcases hfact with hL | hL
    · rw [hL] at hb₀L
      obtain ⟨g, hg⟩ := mem_factorL2.mp hb₀L
      have hdet := CFSG.Quasithin.Vol2.Ch10.SecA.det_eq_one_of_mem_statedSL g.2
      have hg1 : g ≠ 1 := by
        intro h1
        apply hb₀1
        rw [← hg, h1, Prod.mk_one_one, map_one]
        rfl
      have hgr : (g, (1 : ↥(StatedSL 2 K))) ^ (orderOf b₀) = 1 := by
        apply hinj
        rw [map_pow, map_one]
        apply Subtype.ext
        rw [Subgroup.coe_pow, hg]
        exact hbr
      have hgr' : g ^ (orderOf b₀) = 1 := by
        have := congrArg Prod.fst hgr
        simpa using this
      have hGr : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ (orderOf b₀) = 1 := by
        have := congrArg (fun x : ↥(StatedSL 2 K) => ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hgr'
        simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using this
      have h1 := hd (g, 1) w
      rw [hg, hw] at h1
      have h2 := congrArg Multiplicative.toAdd h1
      simp only [tensorAct, toAdd_ofAdd, Subgroup.coe_one, Units.val_one, Matrix.transpose_one,
        mul_one] at h2
      by_contra hw1
      have hX : Multiplicative.toAdd (β w) ≠ 0 := by
        intro h0
        apply hw1
        have hbw1 : β w = 1 := by
          apply Multiplicative.toAdd.injective
          rw [h0]
          rfl
        exact β.injective (hbw1.trans (map_one β).symm)
      have := eq_one_of_mul_fixed hdet hb₀odd hGr h2.symm hX
      exact hg1 (Subtype.ext (Units.ext this))
    · rw [hL] at hb₀L
      obtain ⟨g, hg⟩ := mem_factorR2.mp hb₀L
      have hdet := CFSG.Quasithin.Vol2.Ch10.SecA.det_eq_one_of_mem_statedSL g.2
      have hg1 : g ≠ 1 := by
        intro h1
        apply hb₀1
        rw [← hg, h1, Prod.mk_one_one, map_one]
        rfl
      have hgr : ((1 : ↥(StatedSL 2 K)), g) ^ (orderOf b₀) = 1 := by
        apply hinj
        rw [map_pow, map_one]
        apply Subtype.ext
        rw [Subgroup.coe_pow, hg]
        exact hbr
      have hgr' : g ^ (orderOf b₀) = 1 := by
        have := congrArg Prod.snd hgr
        simpa using this
      have hGr : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ (orderOf b₀) = 1 := by
        have := congrArg (fun x : ↥(StatedSL 2 K) => ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hgr'
        simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using this
      have h1 := hd (1, g) w
      rw [hg, hw] at h1
      have h2 := congrArg Multiplicative.toAdd h1
      simp only [tensorAct, toAdd_ofAdd, Subgroup.coe_one, Units.val_one, Matrix.one_mul] at h2
      by_contra hw1
      have hX : (Multiplicative.toAdd (β w))ᵀ ≠ 0 := by
        intro h0
        apply hw1
        have h00 : Multiplicative.toAdd (β w) = 0 := Matrix.transpose_eq_zero.mp h0
        have hbw1 : β w = 1 := by
          apply Multiplicative.toAdd.injective
          rw [h00]
          rfl
        exact β.injective (hbw1.trans (map_one β).symm)
      have h3 : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          (Multiplicative.toAdd (β w))ᵀ = (Multiplicative.toAdd (β w))ᵀ := by
        have := congrArg Matrix.transpose h2
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at this
        exact this.symm
      have := eq_one_of_mul_fixed hdet hb₀odd hGr h3 hX
      exact hg1 (Subtype.ext (Units.ext this))
  refine ⟨b₀, hb₀Q, orderOf b₀, hb₀odd, hbr, ?_⟩
  intro w hw
  have hc : b₀ (b₀ w * w⁻¹) = b₀ w * w⁻¹ := hw b₀ hb₀Mp
  have hbw : b₀ w = w := mul_inv_eq_one.mp (key _ hc)
  rw [key w hbw]
  exact (fixV Mp).one_mem

end CFSG.Quasithin
