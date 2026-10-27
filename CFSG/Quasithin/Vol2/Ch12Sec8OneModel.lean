module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneHat
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma8
public import CFSG.Quasithin.Background.G2Omega4PlusQuot

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G]

open scoped Classical in
@[expose] noncomputable def neOneInd (x : G) : ZMod 2 := if x = 1 then 0 else 1

theorem neOneInd_one : neOneInd (1 : G) = 0 := by simp [neOneInd]

theorem neOneInd_eq_zero_iff {x : G} : neOneInd x = 0 ↔ x = 1 := by
  by_cases hx : x = 1
  · simp [neOneInd, hx]
  · simp [neOneInd, hx]

private theorem commutator_mul_mul_eq {a b z z' : G}
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

theorem Setting1282One.exists_hatModelU (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    Nonempty (HatModelU (u128 V V₁)) := by
  classical
  set U := u128 V V₁ with hUdef
  have hA := hs.almostSpecial h1222 h12213
  have hV₁Z : V₁ ≤ centerOf U := hs.le_centerOf h1222 h12213
  have hZuU : centerOf U ≤ U := inf_le_left
  have hZc : ∀ z ∈ centerOf U, ∀ u ∈ U, u * z = z * u := fun z hz u hu =>
    Subgroup.mem_centralizer_iff.mp hz.2 u hu
  have hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ V₁ := fun a ha b hb =>
    hA.G22_commutator_mem ha hb
  have hQS : QuotSetting (Subgroup.normalizer (U : Set G)) U (centerOf U) :=
    { S₂_le := hZuU
      Sx_le := Subgroup.le_normalizer
      nS := fun x hx y hy => (Subgroup.mem_normalizer_iff.mp hx y).mp hy
      nS₂ := fun x hx y hy => (Subgroup.mem_normalizer_iff.mp
        (normalizer_le_normalizer_centerOf U hx) y).mp hy
      abel := fun a ha b hb => hV₁Z (hcomm a ha b hb)
      sq := fun a ha => hV₁Z (by
        have := hA.G22_sq_mem ha
        rwa [pow_two] at this) }
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
  have hmemV₁ : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ V₁ := fun a ha b hb => by
    simpa [commutatorElement_def] using hcomm a ha b hb
  have hind : ∀ x ∈ V₁, ∀ y ∈ V₁, neOneInd (x * y) = neOneInd x + neOneInd y := by
    intro x hx y hy
    have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
    have hsq : ∀ w ∈ V₁, w * w = 1 := fun w hw => by
      have := hs.hyp.card_sq.2.1 w (hs.v1.1 hw)
      rwa [pow_two] at this
    by_cases hx1 : x = 1
    · rw [hx1, one_mul, neOneInd_one, zero_add]
    by_cases hy1 : y = 1
    · rw [hy1, mul_one, neOneInd_one, add_zero]
    have e : x = y := SteinbergBS.eq_of_card_le_two hV₁2.le hx hy hx1 hy1
    have hy' : neOneInd y = 1 := by simp [neOneInd, hy1]
    rw [e, hsq y hy, neOneInd_one, hy']
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
    have := commutator_mul_mul_eq (a := (a' : G)) (b := (b' : G))
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

end CFSG.Quasithin.H13
