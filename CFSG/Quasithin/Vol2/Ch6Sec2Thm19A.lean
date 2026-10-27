module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneModel
public import CFSG.Quasithin.Vol2.Ch6StatementsSec2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G]

theorem comm_mul_mul_eq_ch619 {a b z z' : G}
    (hzb : z * b = b * z) (hz'a : z' * a = a * z') (hzz' : z * z' = z' * z) :
    ⁅a * z, b * z'⁆ = ⁅a, b⁆ := by
  have e1 : z * (b * z') * z⁻¹ = b * z' := by
    have : z * (b * z') = (b * z') * z := by
      rw [← mul_assoc, hzb, mul_assoc, hzz', ← mul_assoc]
    rw [this]
    group
  have e2 : z' * a⁻¹ * z'⁻¹ = a⁻¹ := by
    have : z' * a⁻¹ = a⁻¹ * z' := by
      have h1 : a * z' = z' * a := hz'a.symm
      calc z' * a⁻¹ = a⁻¹ * (a * z') * a⁻¹ := by group
        _ = a⁻¹ * (z' * a) * a⁻¹ := by rw [h1]
        _ = a⁻¹ * z' := by group
    rw [this]
    group
  calc ⁅a * z, b * z'⁆ = a * (z * (b * z') * z⁻¹) * a⁻¹ * z'⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = a * (b * z') * a⁻¹ * z'⁻¹ * b⁻¹ := by rw [e1]
    _ = a * b * (z' * a⁻¹ * z'⁻¹) * b⁻¹ := by group
    _ = ⁅a, b⁆ := by
        rw [e2]
        simp only [commutatorElement_def]

variable [Finite G]

theorem exists_hatModelU_ch619 {U Zc : Subgroup G} (hV₁Z : Zc ≤ centerOf U)
    (hV₁2 : Nat.card Zc = 2) (hsq2 : ∀ w ∈ Zc, w * w = 1)
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Zc) (hsqU : ∀ a ∈ U, a * a ∈ Zc) :
    Nonempty (HatModelU U) := by
  classical
  have hZuU : centerOf U ≤ U := inf_le_left
  have hZc : ∀ z ∈ centerOf U, ∀ u ∈ U, u * z = z * u := fun z hz u hu =>
    Subgroup.mem_centralizer_iff.mp hz.2 u hu
  have hQS : QuotSetting (Subgroup.normalizer (U : Set G)) U (centerOf U) :=
    { S₂_le := hZuU
      Sx_le := Subgroup.le_normalizer
      nS := fun x hx y hy => (Subgroup.mem_normalizer_iff.mp hx y).mp hy
      nS₂ := fun x hx y hy => (Subgroup.mem_normalizer_iff.mp
        (normalizer_le_normalizer_centerOf U hx) y).mp hy
      abel := fun a ha b hb => hV₁Z (hcomm a ha b hb)
      sq := fun a ha => hV₁Z (hsqU a ha) }
  have hN : ((centerOf U).subgroupOf U).Normal := hQS.normal
  let _ : CommGroup (SecQuot U (centerOf U)) := hQS.quotCommGroup
  let _ : Module (ZMod 2) (Additive (SecQuot U (centerOf U))) :=
    AddCommGroup.zmodModule (n := 2) (fun x => by
      show (2 : ℕ) • x = 0
      rw [two_nsmul]
      exact Additive.toMul.injective (by simpa using hQS.quot_sq (Additive.toMul x)))
  have hmulL : ∀ a ∈ U, ∀ a' ∈ U, ∀ b ∈ U, ⁅a * a', b⁆ = ⁅a', b⁆ * ⁅a, b⁆ := by
    intro a ha a' ha' b hb
    have e : ⁅a * a', b⁆ = (a * ⁅a', b⁆ * a⁻¹) * ⁅a, b⁆ := by
      simp only [commutatorElement_def]
      group
    have hc : ⁅a', b⁆ ∈ centerOf U := hV₁Z (by
      have := hcomm a' ha' b hb
      simpa [commutatorElement_def] using this)
    have h2 : a * ⁅a', b⁆ * a⁻¹ = ⁅a', b⁆ := by
      have := hZc _ hc a ha
      calc a * ⁅a', b⁆ * a⁻¹ = (⁅a', b⁆ * a) * a⁻¹ := by rw [this]
        _ = ⁅a', b⁆ := by group
    rw [e, h2]
  have hmulR : ∀ a ∈ U, ∀ b ∈ U, ∀ b' ∈ U, ⁅a, b * b'⁆ = ⁅a, b⁆ * ⁅a, b'⁆ := by
    intro a ha b hb b' hb'
    have e : ⁅a, b * b'⁆ = ⁅a, b⁆ * (b * ⁅a, b'⁆ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    have hc : ⁅a, b'⁆ ∈ centerOf U := hV₁Z (by
      have := hcomm a ha b' hb'
      simpa [commutatorElement_def] using this)
    have h2 : b * ⁅a, b'⁆ * b⁻¹ = ⁅a, b'⁆ := by
      have := hZc _ hc b hb
      calc b * ⁅a, b'⁆ * b⁻¹ = (⁅a, b'⁆ * b) * b⁻¹ := by rw [this]
        _ = ⁅a, b'⁆ := by group
    rw [e, h2]
  have hmemV₁ : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ Zc := fun a ha b hb => by
    simpa [commutatorElement_def] using hcomm a ha b hb
  have hind : ∀ x ∈ Zc, ∀ y ∈ Zc, neOneInd (x * y) = neOneInd x + neOneInd y := by
    intro x hx y hy
    by_cases hx1 : x = 1
    · rw [hx1, one_mul, neOneInd_one, zero_add]
    by_cases hy1 : y = 1
    · rw [hy1, mul_one, neOneInd_one, add_zero]
    have e : x = y := SteinbergBS.eq_of_card_le_two hV₁2.le hx hy hx1 hy1
    have hy' : neOneInd y = 1 := by simp [neOneInd, hy1]
    rw [e, hsq2 y hy, neOneInd_one, hy']
    decide
  let rep : SecQuot U (centerOf U) → ↥U :=
    Function.surjInv (secMk_surjective (A := U) (B := centerOf U))
  have hrep : ∀ q : SecQuot U (centerOf U), secMk U (centerOf U) (rep q) = q :=
    Function.surjInv_eq (secMk_surjective (A := U) (B := centerOf U))
  let f : Additive (SecQuot U (centerOf U)) → Additive (SecQuot U (centerOf U)) → ZMod 2 :=
    fun x y => neOneInd ⁅((rep (Additive.toMul x) : ↥U) : G), ((rep (Additive.toMul y) : ↥U) : G)⁆
  have key : ∀ (a' b' a b : ↥U), secMk U (centerOf U) a' = secMk _ _ a →
      secMk U (centerOf U) b' = secMk _ _ b → ⁅(a' : G), (b' : G)⁆ = ⁅(a : G), (b : G)⁆ := by
    intro a' b' a b ha hb
    have ha1 := secMk_eq_secMk_iff.mp ha
    have hb1 := secMk_eq_secMk_iff.mp hb
    have := comm_mul_mul_eq_ch619 (a := (a' : G)) (b := (b' : G))
      (z := (a' : G)⁻¹ * a) (z' := (b' : G)⁻¹ * b)
      (hZc _ ha1 b' b'.2).symm (hZc _ hb1 a' a'.2).symm (hZc _ ha1 _ (hZuU hb1)).symm
    simpa using this.symm
  have hf : ∀ a b : ↥U, f (Additive.ofMul (secMk _ _ a)) (Additive.ofMul (secMk _ _ b)) =
      neOneInd ⁅(a : G), (b : G)⁆ := fun a b =>
    congrArg neOneInd (key _ _ a b (hrep _) (hrep _))
  have hsurj : ∀ x : Additive (SecQuot U (centerOf U)),
      ∃ a : ↥U, x = Additive.ofMul (secMk _ _ a) := fun x => by
    obtain ⟨a, ha⟩ := secMk_surjective (A := U) (B := centerOf U) (Additive.toMul x)
    exact ⟨a, (congrArg Additive.ofMul ha).symm⟩
  have hadd : ∀ a a' : ↥U, Additive.ofMul (secMk U (centerOf U) a) +
      Additive.ofMul (secMk U (centerOf U) a') =
        Additive.ofMul (secMk U (centerOf U) (a * a')) := by
    intro a a'
    rw [map_mul, ofMul_mul]
  have hzero : (0 : Additive (SecQuot U (centerOf U))) =
      Additive.ofMul (secMk U (centerOf U) 1) := by
    rw [map_one, ofMul_one]
  have hc01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have H1 : ∀ x x' y, f (x + x') y = f x y + f x' y := by
    intro x x' y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨a', rfl⟩ := hsurj x'
    obtain ⟨b, rfl⟩ := hsurj y
    rw [hadd, hf, hf, hf]
    show neOneInd ⁅((a : G) * a'), (b : G)⁆ = _
    rw [hmulL a a.2 a' a'.2 b b.2, hind _ (hmemV₁ _ a'.2 _ b.2) _ (hmemV₁ _ a.2 _ b.2), add_comm]
  have H3 : ∀ x y y', f x (y + y') = f x y + f x y' := by
    intro x y y'
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    obtain ⟨b', rfl⟩ := hsurj y'
    rw [hadd, hf, hf, hf]
    show neOneInd ⁅(a : G), ((b : G) * b')⁆ = _
    rw [hmulR a a.2 b b.2 b' b'.2, hind _ (hmemV₁ _ a.2 _ b.2) _ (hmemV₁ _ a.2 _ b'.2)]
  have H2 : ∀ (c : ZMod 2) x y, f (c • x) y = c • f x y := by
    intro c x y
    rcases hc01 c with rfl | rfl
    · obtain ⟨b, rfl⟩ := hsurj y
      rw [zero_smul, zero_smul, hzero, hf]
      simp [neOneInd_one]
    · rw [one_smul, one_smul]
  have H4 : ∀ (c : ZMod 2) x y, f x (c • y) = c • f x y := by
    intro c x y
    rcases hc01 c with rfl | rfl
    · obtain ⟨a, rfl⟩ := hsurj x
      rw [zero_smul, zero_smul, hzero, hf]
      simp [neOneInd_one]
    · rw [one_smul, one_smul]
  let toLin : MulAut (SecQuot U (centerOf U)) →*
      (Additive (SecQuot U (centerOf U)) ≃ₗ[ZMod 2] Additive (SecQuot U (centerOf U))) :=
    { toFun := fun e =>
        { MulEquiv.toAdditive e with
          map_smul' := fun c x => by
            rcases hc01 c with rfl | rfl
            · simp
            · simp }
      map_one' := LinearEquiv.ext fun x => rfl
      map_mul' := fun e e' => LinearEquiv.ext fun x => rfl }
  let ρ := toLin.comp hQS.convAct
  have hρ : ∀ (x : ↥(Subgroup.normalizer (U : Set G))) (u : ↥U),
      ρ x (Additive.ofMul (secMk U (centerOf U) u)) =
        Additive.ofMul (secMk U (centerOf U)
          ⟨(x : G) * u * (x : G)⁻¹, hQS.nS x x.2 u u.2⟩) := by
    intro x u
    show Additive.ofMul (hQS.convAct x (secMk U (centerOf U) u)) = _
    rw [QuotSetting.convAct_mk]
  refine ⟨{ V := Additive (SecQuot U (centerOf U))
            addCommGroup := inferInstance
            module := inferInstance
            finite := inferInstance
            π := fun x => if hx : x ∈ U then Additive.ofMul (secMk _ _ ⟨x, hx⟩) else 0
            B := LinearMap.mk₂ (ZMod 2) f H1 H2 H3 H4
            ρ := ρ
            π_mul := ?_
            π_surj := ?_
            π_eq_iff := ?_
            B_spec := ?_
            ρ_π := ?_ }⟩
  · intro a ha b hb
    have hab := U.mul_mem ha hb
    simp only [ha, hb, hab, ↓reduceDIte]
    exact (hadd ⟨a, ha⟩ ⟨b, hb⟩).symm
  · intro v
    obtain ⟨u, rfl⟩ := hsurj v
    exact ⟨u, u.2, by simp only [u.2, ↓reduceDIte]⟩
  · intro a ha b hb
    simp only [ha, hb, ↓reduceDIte]
    rw [Equiv.apply_eq_iff_eq, secMk_eq_secMk_iff]
  · intro a ha b hb
    simp only [ha, hb, ↓reduceDIte]
    rw [LinearMap.mk₂_apply, hf, neOneInd_eq_zero_iff]
    simp only [commutatorElement_def]
  · intro x u hu
    have hxu : (x : G) * u * (x : G)⁻¹ ∈ U := hQS.nS x x.2 u hu
    simp only [hu, hxu, ↓reduceDIte]
    exact hρ x ⟨u, hu⟩

omit [Finite G] in
theorem realization_of_hat_ch619 {H U : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (U : Set G)) (D : HatModelU U) :
    ∃ (β : ↥U →* Multiplicative D.V) (ρ : ↥H →* (D.V ≃ₗ[ZMod 2] D.V)),
      IsSymplecticRealization H U (centerOf U) D.V D.B β ρ := by
  have hπ1 : D.π 1 = 0 := by
    have := D.π_mul 1 U.one_mem 1 U.one_mem
    simpa using this
  let β : ↥U →* Multiplicative D.V :=
    { toFun := fun u => Multiplicative.ofAdd (D.π u)
      map_one' := by
        show Multiplicative.ofAdd (D.π 1) = 1
        rw [hπ1, ofAdd_zero]
      map_mul' := fun u u' => by
        show Multiplicative.ofAdd (D.π ((u : G) * u')) = _
        rw [D.π_mul u u.2 u' u'.2, ofAdd_add] }
  refine ⟨β, D.ρ.comp (Subgroup.inclusion hHN), fun x => ?_, fun u => ?_, fun h u v huv => ?_,
    fun u v => ?_⟩
  · obtain ⟨u, hu, hux⟩ := D.π_surj (Multiplicative.toAdd x)
    exact ⟨⟨u, hu⟩, by
      show Multiplicative.ofAdd (D.π u) = x
      rw [hux, ofAdd_toAdd]⟩
  · show Multiplicative.ofAdd (D.π u) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, ← hπ1,
      D.π_eq_iff u u.2 1 U.one_mem]
    constructor
    · intro hc
      have := (centerOf U).inv_mem hc
      simpa using this
    · intro hc
      have := (centerOf U).inv_mem hc
      simpa using this
  · show D.π v = D.ρ ⟨h, hHN h.2⟩ (D.π u)
    rw [D.ρ_π ⟨h, hHN h.2⟩ u u.2, huv]
  · show D.B (D.π u) (D.π v) ≠ 0 ↔ _
    exact not_congr (D.B_spec u u.2 v v.2)

theorem exists_realization_ch619 {H U Zc : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (U : Set G)) (hV₁Z : Zc ≤ centerOf U)
    (hV₁2 : Nat.card Zc = 2) (hsq2 : ∀ w ∈ Zc, w * w = 1)
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Zc) (hsqU : ∀ a ∈ U, a * a ∈ Zc) :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module (ZMod 2) A) (_ : Finite A)
      (B : LinearMap.BilinForm (ZMod 2) A) (β : ↥U →* Multiplicative A)
      (ρ : ↥H →* (A ≃ₗ[ZMod 2] A)), IsSymplecticRealization H U (centerOf U) A B β ρ := by
  obtain ⟨D⟩ := exists_hatModelU_ch619 hV₁Z hV₁2 hsq2 hcomm hsqU
  obtain ⟨β, ρ, hR⟩ := realization_of_hat_ch619 hHN D
  exact ⟨D.V, inferInstance, inferInstance, inferInstance, D.B, β, ρ, hR⟩

end CFSG.Quasithin.H13
