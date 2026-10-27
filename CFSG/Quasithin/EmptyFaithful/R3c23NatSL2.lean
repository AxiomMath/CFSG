module

public import CFSG.Quasithin.EmptyFaithful.R3c23Def
import CFSG.Quasithin.EmptyFaithful.SzN15Nat
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.Open.MatrixFixedVectors

public section

namespace CFSG.Quasithin

namespace R3c23

open CFSG.Assembly.LowTwoRank

section Natural

private theorem card_fixed_le_field {K : Type} [Field K] [Finite K] (g : ↥(StatedSL 2 K))
    (hg : g ≠ 1) :
    Nat.card {x : Multiplicative (Fin 2 → K) // natAct (StatedSL 2 K) g x = x} ≤ Nat.card K :=
  (Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun _ => Iff.rfl)).le.trans
    (CFSG.Open.StatedAPI.card_mulVec_fixed_le fun h => hg (Subtype.ext (Units.ext h)))

private theorem exists_natAct_upper (K : Type) [Field K] :
    ∃ g : ↥(StatedSL 2 K), ∀ v : Fin 2 → K,
      natAct (StatedSL 2 K) g (Multiplicative.ofAdd v) =
        Multiplicative.ofAdd (![v 0 + v 1, v 1] : Fin 2 → K) := by
  obtain ⟨A, hA⟩ : ∃ A : Matrix.SpecialLinearGroup (Fin 2) K,
      (A : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] :=
    ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, rfl⟩
  refine ⟨specialLinearGroupEquivStatedSL 2 K A, fun v => ?_⟩
  simp only [natAct, specialLinearGroupEquivStatedSL_coe, hA, toAdd_ofAdd]
  refine congrArg Multiplicative.ofAdd ?_
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem exists_natAct_lower (K : Type) [Field K] :
    ∃ g : ↥(StatedSL 2 K), ∀ v : Fin 2 → K,
      natAct (StatedSL 2 K) g (Multiplicative.ofAdd v) =
        Multiplicative.ofAdd (![v 0, v 0 + v 1] : Fin 2 → K) := by
  obtain ⟨A, hA⟩ : ∃ A : Matrix.SpecialLinearGroup (Fin 2) K,
      (A : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1] :=
    ⟨⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩, rfl⟩
  refine ⟨specialLinearGroupEquivStatedSL 2 K A, fun v => ?_⟩
  simp only [natAct, specialLinearGroupEquivStatedSL_coe, hA, toAdd_ofAdd]
  refine congrArg Multiplicative.ofAdd ?_
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem odd_two_pow_sub_one {k : ℕ} (hk : 0 < k) : Odd (2 ^ k - 1) := by
  have h : Even (2 ^ k) := (Nat.even_pow' hk.ne').mpr even_two
  exact Nat.Even.sub_odd Nat.one_le_two_pow h odd_one

private theorem card_elemAbelian_le_field {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m)
    {π : ↥(StatedSL 2 K) →* ↥L} (hπ : Function.Surjective π) {B : Subgroup (MulAut V)}
    (hBL : B ≤ L) (hB2 : IsElemAbelian2 B) : Nat.card ↥B ≤ Nat.card K := by
  have hdvd : Nat.card ↥B ∣ Nat.card ↥(StatedSL 2 K) :=
    (Subgroup.card_dvd_of_le hBL).trans (Subgroup.card_dvd_of_surjective hπ)
  have hcard : Nat.card ↥(StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num)]
    simp
  have hp : IsPGroup 2 ↥B := fun g => ⟨1, Subtype.ext (by simpa using hB2.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hm1 : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    have h1 := Finite.one_lt_card (α := K)
    rw [hm0, pow_zero] at hK
    omega
  have hodd : Odd (Nat.card K ^ 2 - 1) := by
    rw [hK, ← pow_mul]
    exact odd_two_pow_sub_one (by omega)
  have hcop : Nat.Coprime (2 ^ k) (Nat.card K ^ 2 - 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  rw [hk, hcard] at hdvd
  have h2 : 2 ^ k ∣ Nat.card K := hcop.dvd_of_dvd_mul_right hdvd
  rw [hk]
  exact Nat.le_of_dvd Nat.card_pos h2

private theorem beta_comm {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {W : Subgroup V}
    {K : Type} [Field K] {π : ↥(StatedSL 2 K) →* ↥L}
    (hWinv : ∀ x : ↥L, ∀ u ∈ W, (x : MulAut V) u ∈ W)
    {β : ↥W →* Multiplicative (Fin 2 → K)}
    (hβe : ∀ (γ : ↥(StatedSL 2 K)) (u : ↥W) (hu : ((π γ : ↥L) : MulAut V) u ∈ W),
      β ⟨((π γ : ↥L) : MulAut V) u, hu⟩ = natAct (StatedSL 2 K) γ (β u))
    (g : ↥(StatedSL 2 K)) (y : ↥W) :
    β ⟨((π g : ↥L) : MulAut V) y * (y : V)⁻¹, W.mul_mem (hWinv (π g) y y.2) (W.inv_mem y.2)⟩ =
      natAct (StatedSL 2 K) g (β y) * (β y)⁻¹ := by
  have hsu := hWinv (π g) y y.2
  have e : (⟨((π g : ↥L) : MulAut V) y * (y : V)⁻¹,
      W.mul_mem (hWinv (π g) y y.2) (W.inv_mem y.2)⟩ : ↥W) =
      ⟨((π g : ↥L) : MulAut V) y, hsu⟩ * y⁻¹ := rfl
  rw [e, map_mul, map_inv, hβe g y hsu]

private theorem natCount_of_natReal {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)}
    {W C : Subgroup V} {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m)
    {π : ↥(StatedSL 2 K) →* ↥L} (R : SzN15.NatReal L W C (StatedSL 2 K) π) (hCW : C ≤ W) :
    NatCount L W C := by
  intro B hBL hB2
  obtain ⟨β, hβs, hβk, hβe⟩ := R.exists_β
  have hWcard : Nat.card ↥W = Nat.card ↥C * Nat.card K ^ 2 := by
    have h2 : β.range = ⊤ := MonoidHom.range_eq_top.mpr hβs
    have h3 : Nat.card ↥β.range = Nat.card K ^ 2 := by
      rw [h2, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
      simp
    have h4 : Nat.card ↥β.ker = Nat.card ↥C := by
      have hker : β.ker = C.subgroupOf W := by
        ext u
        rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCW).toEquiv
    rw [← Subgroup.card_ker_mul_card_range β, h3, h4]
  have hfixW : fixMod B W C ≤ W := fun w hw => hw.1
  by_cases hbot : B = ⊥
  · subst hbot
    rw [Subgroup.card_bot, one_mul]
    exact Subgroup.card_le_of_le hfixW
  ·
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    obtain ⟨g, hg⟩ := R.surj ⟨(a : MulAut V), hBL a.2⟩
    have hg1 : g ≠ 1 := by
      rintro rfl
      apply ha1
      have h1 : (⟨(a : MulAut V), hBL a.2⟩ : ↥L) = 1 := by rw [← hg, map_one]
      exact Subtype.ext (congrArg (fun x : ↥L => (x : MulAut V)) h1)
    obtain ⟨φ, hφ⟩ : ∃ φ : ↥(fixMod B W C) →* Multiplicative (Fin 2 → K),
        ∀ c, φ c = β (Subgroup.inclusion hfixW c) :=
      ⟨β.comp (Subgroup.inclusion hfixW), fun c => rfl⟩
    have hφker : Nat.card ↥φ.ker ≤ Nat.card ↥C := by
      have hmemC : ∀ c : ↥φ.ker, ((c : ↥(fixMod B W C)) : V) ∈ C := fun c =>
        (hβk (Subgroup.inclusion hfixW c)).mp (by rw [← hφ]; exact c.2)
      refine Nat.card_le_card_of_injective
        (fun c => (⟨((c : ↥(fixMod B W C)) : V), hmemC c⟩ : ↥C)) ?_
      intro c d h
      have h1 : ((c : ↥(fixMod B W C)) : V) = ((d : ↥(fixMod B W C)) : V) :=
        congrArg (fun z : ↥C => (z : V)) h
      exact Subtype.ext (Subtype.ext h1)
    have hφrange : Nat.card ↥φ.range ≤ Nat.card K := by
      have hπa : ((π g : ↥L) : MulAut V) = (a : MulAut V) :=
        congrArg (fun x : ↥L => (x : MulAut V)) hg
      have hfix : ∀ c : ↥(fixMod B W C), natAct (StatedSL 2 K) g (φ c) = φ c := by
        intro c
        have hcW : (c : V) ∈ W := c.2.1
        have hcomm : ((π g : ↥L) : MulAut V) (c : V) * (c : V)⁻¹ ∈ C := by
          rw [hπa]
          exact c.2.2 (a : MulAut V) a.2
        have h1 := beta_comm R.U_inv hβe g ⟨(c : V), hcW⟩
        have h2 := (hβk ⟨((π g : ↥L) : MulAut V) (c : V) * (c : V)⁻¹,
          W.mul_mem (R.U_inv (π g) (c : V) hcW) (W.inv_mem hcW)⟩).mpr hcomm
        rw [hφ]
        exact mul_inv_eq_one.mp (h1.symm.trans h2)
      have hmem : ∀ x : ↥φ.range, natAct (StatedSL 2 K) g x.1 = x.1 := by
        rintro ⟨x, c, rfl⟩
        exact hfix c
      refine le_trans (Nat.card_le_card_of_injective
        (fun x : ↥φ.range => (⟨x.1, hmem x⟩ :
          {x : Multiplicative (Fin 2 → K) // natAct (StatedSL 2 K) g x = x})) ?_)
        (card_fixed_le_field g hg1)
      intro x y h
      have h1 : x.1 = y.1 := congrArg (fun z : {x : Multiplicative (Fin 2 → K) //
        natAct (StatedSL 2 K) g x = x} => z.1) h
      exact Subtype.ext h1
    have hfixcard : Nat.card ↥(fixMod B W C) ≤ Nat.card ↥C * Nat.card K := by
      rw [← Subgroup.card_ker_mul_card_range φ]
      exact Nat.mul_le_mul hφker hφrange
    have hBcard : Nat.card ↥B ≤ Nat.card K := card_elemAbelian_le_field hK R.surj hBL hB2
    calc Nat.card ↥B * Nat.card ↥(fixMod B W C)
        ≤ Nat.card K * (Nat.card ↥C * Nat.card K) := Nat.mul_le_mul hBcard hfixcard
      _ = Nat.card ↥C * Nat.card K ^ 2 := by ring
      _ = Nat.card ↥W := hWcard.symm

private theorem exists_not_mem_of_natReal {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {W C : Subgroup V} {K : Type} [Field K] {π : ↥(StatedSL 2 K) →* ↥L}
    (R : SzN15.NatReal L W C (StatedSL 2 K) π) : ∃ w ∈ W, w ∉ C := by
  obtain ⟨β, hβs, hβk, -⟩ := R.exists_β
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (![1, 0] : Fin 2 → K))
  refine ⟨(u : V), u.2, fun hC => ?_⟩
  have h1 : β u = 1 := (hβk u).mpr hC
  rw [hu] at h1
  have h2 : (![1, 0] : Fin 2 → K) = 0 := ofAdd_eq_one.mp h1
  have h3 : (1 : K) = 0 := by simpa using congrFun h2 0
  exact one_ne_zero h3

private theorem fixed_mem_of_natReal {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {W C : Subgroup V} {K : Type} [Field K] {π : ↥(StatedSL 2 K) →* ↥L}
    (R : SzN15.NatReal L W C (StatedSL 2 K) π) :
    ∀ w ∈ W, (∀ l ∈ L, l w * w⁻¹ ∈ C) → w ∈ C := by
  intro w hw hfix
  obtain ⟨y, rfl⟩ : ∃ y : ↥W, (y : V) = w := ⟨⟨w, hw⟩, rfl⟩
  obtain ⟨β, hβs, hβk, hβe⟩ := R.exists_β
  have hall : ∀ g : ↥(StatedSL 2 K), natAct (StatedSL 2 K) g (β y) = β y := by
    intro g
    have h1 : ((π g : ↥L) : MulAut V) (y : V) * (y : V)⁻¹ ∈ C := hfix _ (π g).2
    have h2 := beta_comm R.U_inv hβe g y
    have h3 := (hβk ⟨((π g : ↥L) : MulAut V) (y : V) * (y : V)⁻¹,
      W.mul_mem (R.U_inv (π g) (y : V) y.2) (W.inv_mem y.2)⟩).mpr h1
    exact mul_inv_eq_one.mp (h2.symm.trans h3)
  obtain ⟨g₁, hg₁⟩ := exists_natAct_upper K
  obtain ⟨g₂, hg₂⟩ := exists_natAct_lower K
  obtain ⟨v, hv⟩ : ∃ v : Fin 2 → K, β y = Multiplicative.ofAdd v :=
    ⟨Multiplicative.toAdd (β y), rfl⟩
  have h1 := hall g₁
  have h2 := hall g₂
  rw [hv, hg₁] at h1
  rw [hv, hg₂] at h2
  have h1' : (![v 0 + v 1, v 1] : Fin 2 → K) = v := Multiplicative.ofAdd.injective h1
  have h2' : (![v 0, v 0 + v 1] : Fin 2 → K) = v := Multiplicative.ofAdd.injective h2
  have e1 : v 1 = 0 := by simpa using congrFun h1' 0
  have e0 : v 0 = 0 := by simpa using congrFun h2' 1
  have hv0 : v = 0 := by
    funext i
    fin_cases i <;> simp [e0, e1]
  refine (hβk y).mp ?_
  rw [hv, hv0]
  exact ofAdd_zero

private theorem le_commMod_sup_of_natReal {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {W C : Subgroup V} {K : Type} [Field K] {π : ↥(StatedSL 2 K) →* ↥L}
    (R : SzN15.NatReal L W C (StatedSL 2 K) π) : W ≤ commMod L W ⊔ C := by
  intro w hw
  obtain ⟨y, rfl⟩ : ∃ y : ↥W, (y : V) = w := ⟨⟨w, hw⟩, rfl⟩
  obtain ⟨β, hβs, hβk, hβe⟩ := R.exists_β
  obtain ⟨g₁, hg₁⟩ := exists_natAct_upper K
  obtain ⟨g₂, hg₂⟩ := exists_natAct_lower K
  obtain ⟨x, hx⟩ : ∃ x : Fin 2 → K, β y = Multiplicative.ofAdd x :=
    ⟨Multiplicative.toAdd (β y), rfl⟩
  obtain ⟨y₁, hy₁⟩ := hβs (Multiplicative.ofAdd (![0, x 0] : Fin 2 → K))
  obtain ⟨y₂, hy₂⟩ := hβs (Multiplicative.ofAdd (![x 1, 0] : Fin 2 → K))
  have hc₁W : ((π g₁ : ↥L) : MulAut V) (y₁ : V) * (y₁ : V)⁻¹ ∈ W :=
    W.mul_mem (R.U_inv (π g₁) (y₁ : V) y₁.2) (W.inv_mem y₁.2)
  have hc₂W : ((π g₂ : ↥L) : MulAut V) (y₂ : V) * (y₂ : V)⁻¹ ∈ W :=
    W.mul_mem (R.U_inv (π g₂) (y₂ : V) y₂.2) (W.inv_mem y₂.2)
  have hc₁ : ((π g₁ : ↥L) : MulAut V) (y₁ : V) * (y₁ : V)⁻¹ ∈ commMod L W :=
    Subgroup.subset_closure ⟨_, (π g₁).2, (y₁ : V), y₁.2, rfl⟩
  have hc₂ : ((π g₂ : ↥L) : MulAut V) (y₂ : V) * (y₂ : V)⁻¹ ∈ commMod L W :=
    Subgroup.subset_closure ⟨_, (π g₂).2, (y₂ : V), y₂.2, rfl⟩
  have hβc₁ : β ⟨((π g₁ : ↥L) : MulAut V) (y₁ : V) * (y₁ : V)⁻¹, hc₁W⟩ =
      Multiplicative.ofAdd (![x 0, 0] : Fin 2 → K) := by
    rw [beta_comm R.U_inv hβe g₁ y₁, hy₁, hg₁, ← div_eq_mul_inv, ← ofAdd_sub]
    refine congrArg Multiplicative.ofAdd ?_
    ext i
    fin_cases i <;> simp
  have hβc₂ : β ⟨((π g₂ : ↥L) : MulAut V) (y₂ : V) * (y₂ : V)⁻¹, hc₂W⟩ =
      Multiplicative.ofAdd (![0, x 1] : Fin 2 → K) := by
    rw [beta_comm R.U_inv hβe g₂ y₂, hy₂, hg₂, ← div_eq_mul_inv, ← ofAdd_sub]
    refine congrArg Multiplicative.ofAdd ?_
    ext i
    fin_cases i <;> simp
  have hc₁₂ : ((π g₁ : ↥L) : MulAut V) (y₁ : V) * (y₁ : V)⁻¹ *
      (((π g₂ : ↥L) : MulAut V) (y₂ : V) * (y₂ : V)⁻¹) ∈ W := W.mul_mem hc₁W hc₂W
  have hmemW : (y : V) * (((π g₁ : ↥L) : MulAut V) (y₁ : V) * (y₁ : V)⁻¹ *
      (((π g₂ : ↥L) : MulAut V) (y₂ : V) * (y₂ : V)⁻¹))⁻¹ ∈ W :=
    W.mul_mem y.2 (W.inv_mem hc₁₂)
  have hβ1 : β ⟨(y : V) * (((π g₁ : ↥L) : MulAut V) (y₁ : V) * (y₁ : V)⁻¹ *
      (((π g₂ : ↥L) : MulAut V) (y₂ : V) * (y₂ : V)⁻¹))⁻¹, hmemW⟩ = 1 := by
    have e : (⟨(y : V) * (((π g₁ : ↥L) : MulAut V) (y₁ : V) * (y₁ : V)⁻¹ *
        (((π g₂ : ↥L) : MulAut V) (y₂ : V) * (y₂ : V)⁻¹))⁻¹, hmemW⟩ : ↥W) =
        y * (⟨_, hc₁W⟩ * ⟨_, hc₂W⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, map_mul, hx, hβc₁, hβc₂, ← ofAdd_add, ← ofAdd_neg, ← ofAdd_add]
    refine (congrArg Multiplicative.ofAdd (?_ : x + -(![x 0, 0] + ![0, x 1]) = 0)).trans ofAdd_zero
    ext i
    fin_cases i <;> simp
  have hmem := (hβk ⟨_, hmemW⟩).mp hβ1
  have hsplit : (y : V) = (((π g₁ : ↥L) : MulAut V) (y₁ : V) * (y₁ : V)⁻¹ *
      (((π g₂ : ↥L) : MulAut V) (y₂ : V) * (y₂ : V)⁻¹)) * ((y : V) * (((π g₁ : ↥L) : MulAut V)
        (y₁ : V) * (y₁ : V)⁻¹ * (((π g₂ : ↥L) : MulAut V) (y₂ : V) * (y₂ : V)⁻¹))⁻¹) := by
    rw [mul_comm (y : V), mul_inv_cancel_left]
  rw [hsplit]
  exact Subgroup.mul_mem_sup (mul_mem hc₁ hc₂) hmem

end Natural

theorem sl2PieceFacts : SL2PieceFacts := by
  intro V _ _ L W C m hnat
  obtain ⟨K, _, _, hK, π₀, hπ₀⟩ := hnat
  obtain ⟨π, hπ⟩ : ∃ π : ↥(StatedSL 2 K) →* ↥L,
      (FFModel.nat (StatedSL 2 K)).RealizesVia L W C π := ⟨π₀, hπ₀⟩
  have R := SzN15.NatReal.of_realizesVia hπ
  exact ⟨natCount_of_natReal hK R hπ.2.1, hπ.2.1, exists_not_mem_of_natReal R,
    fixed_mem_of_natReal R, le_commMod_sup_of_natReal R⟩

end R3c23

end CFSG.Quasithin
