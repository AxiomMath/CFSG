module

public import CFSG.Quasithin.EmptyFaithful.SBd7Mod
public import CFSG.Quasithin.EmptyFaithful.S153F19
public import CFSG.Quasithin.EmptyFaithful.SBd2L3Branch2
public import CFSG.Quasithin.EmptyFaithful.SBd7Gen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

namespace SBd7

section Case3

variable {G : Type} [Group G]

theorem commutator_eq_bot_of_centralizes {V Vc Vn Y : Subgroup G}
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hsup : Vc ⊔ Vn = V)
    (h1 : Y ≤ Subgroup.centralizer (Vc : Set G)) (h2 : Y ≤ Subgroup.centralizer (Vn : Set G)) :
    ⁅V, Y⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro v hv y hy
  have hVc : Vc ≤ V := hsup ▸ le_sup_left
  have hVn : Vn ≤ V := hsup ▸ le_sup_right
  obtain ⟨a, ha, b, hb, rfl⟩ := SBd2.exists_mul_of_mem_sup'
    (fun a ha b hb => hVab a (hVc ha) b (hVn hb)) (hsup ▸ hv)
  have hya : a * y = y * a := Subgroup.mem_centralizer_iff.mp (h1 hy) a ha
  have hyb : b * y = y * b := Subgroup.mem_centralizer_iff.mp (h2 hy) b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  calc a * b * y = a * (b * y) := by rw [mul_assoc]
    _ = a * (y * b) := by rw [hyb]
    _ = (a * y) * b := by rw [mul_assoc]
    _ = (y * a) * b := by rw [hya]
    _ = y * (a * b) := by rw [mul_assoc]

theorem fixed_in_V_false {V Vc Vn YL YC : Subgroup G}
    (hsup : Vc ⊔ Vn = V) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hc4 : Nat.card Vc = 4) (hn4 : Nat.card Vn = 4) (hsq : ∀ a ∈ V, a * a = 1)
    (hYLc : YL ≤ Subgroup.centralizer (Vc : Set G)) (hYLn : YL ≤ Subgroup.normalizer (Vn : Set G))
    (hYCn : YC ≤ Subgroup.centralizer (Vn : Set G)) (hYCc : YC ≤ Subgroup.normalizer (Vc : Set G))
    (hYLgen : ∀ K : Subgroup G, (∀ y ∈ YL, Odd (orderOf y) → y ∈ K) → YL ≤ K)
    (hYCgen : ∀ K : Subgroup G, (∀ y ∈ YC, Odd (orderOf y) → y ∈ K) → YC ≤ K)
    (hLnt : ⁅V, YL⁆ ≠ ⊥) (hCnt : ⁅V, YC⁆ ≠ ⊥) :
    ∀ n ∈ V, (∀ y ∈ YL, y * n * y⁻¹ = n) → (∀ y ∈ YC, y * n * y⁻¹ = n) → n = 1 := by
  intro n hn hL hC
  have hVc : Vc ≤ V := hsup ▸ le_sup_left
  have hVn : Vn ≤ V := hsup ▸ le_sup_right
  obtain ⟨a, ha, b, hb, rfl⟩ := SBd2.exists_mul_of_mem_sup'
    (fun a ha b hb => hVab a (hVc ha) b (hVn hb)) (hsup ▸ hn)
  have hbL : ∀ y ∈ YL, y * b * y⁻¹ = b := by
    intro y hy
    have hya : y * a * y⁻¹ = a := by
      have := Subgroup.mem_centralizer_iff.mp (hYLc hy) a ha
      calc y * a * y⁻¹ = a * y * y⁻¹ := by rw [← this]
        _ = a := by group
    have h1 := hL y hy
    have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [e, hya] at h1
    exact mul_left_cancel h1
  have hb1 : b = 1 := by
    by_contra hb1
    apply hLnt
    have hYLC : YL ≤ Subgroup.centralizer (Vn : Set G) := by
      refine hYLgen _ fun y hy hodd => ?_
      refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
      have := SBd7.odd_fixes_of_card_four hn4 (fun x hx => hsq x (hVn hx)) (hYLn hy) hodd hb hb1
        (hbL y hy) c hc
      calc c * y = (y * c * y⁻¹) * y := by rw [this]
        _ = y * c := by group
    exact commutator_eq_bot_of_centralizes hVab hsup hYLc hYLC
  subst hb1
  have haC : ∀ y ∈ YC, y * a * y⁻¹ = a := by
    intro y hy
    simpa using hC y hy
  have ha1 : a = 1 := by
    by_contra ha1
    apply hCnt
    have hYCC : YC ≤ Subgroup.centralizer (Vc : Set G) := by
      refine hYCgen _ fun y hy hodd => ?_
      refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
      have := SBd7.odd_fixes_of_card_four hc4 (fun x hx => hsq x (hVc hx)) (hYCc hy) hodd ha ha1
        (haC y hy) c hc
      calc c * y = (y * c * y⁻¹) * y := by rw [this]
        _ = y * c := by group
    exact commutator_eq_bot_of_centralizes hVab hsup hYCC hYCn
  subst ha1
  simp

theorem add_self_eq_zero_of_card_two {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2) (x : F) :
    x + x = 0 := by
  rcases SBd5.eq_zero_or_one_of_card_two hF x with rfl | rfl
  · simp
  · rcases SBd5.eq_zero_or_one_of_card_two hF (1 + 1) with h | h
    · exact h
    · exfalso
      have : (1 : F) = 0 := by
        have h1 : (1 : F) + 1 = 1 + 0 := by rw [h, add_zero]
        exact add_left_cancel h1
      exact one_ne_zero this

theorem case3_Q_le_of_fixed [Finite G] {L Q S V YL YC : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    (hα : IsModO2Surj L α)
    (hZ1 : IsSumOfNaturalModulesVia L (centerOf Q) ⊥ α false 1)
    (hZ2 : IsSumOfNaturalModulesVia L Q (centerOf Q) α true 2)
    (hS2 : IsPGroup 2 ↥S) (hQS : Q ≤ S) (hSQ : S ≤ Subgroup.normalizer (Q : Set G))
    (hSYL : S ≤ Subgroup.normalizer (YL : Set G)) (hYLL : YL ≤ L)
    (hYLQ : YL ≤ Subgroup.normalizer (Q : Set G)) (hQYL : Q ≤ Subgroup.normalizer (YL : Set G))
    (hΩ : ∀ n ∈ S, (∀ s ∈ S, s * n * s⁻¹ = n) → n * n = 1 → n ∈ V)
    (hVfix : ∀ n ∈ V, (∀ y ∈ YL, y * n * y⁻¹ = n) → (∀ y ∈ YC, y * n * y⁻¹ = n) → n = 1)
    (hYCZ : ∀ y ∈ YC, ∀ z ∈ centerOf Q, y * z * y⁻¹ = z) :
    Q ≤ YL := by
  classical
  have hZQ : centerOf Q ≤ Q := inf_le_left
  have hZc : ∀ z ∈ centerOf Q, ∀ q ∈ Q, z * q = q * z := fun z hz q hq =>
    (Subgroup.mem_centralizer_iff.mp hz.2 q hq).symm
  have hZcomm : centerOf Q ≤ ⁅Q, Q⁆ := le_commutator_of_case3 hF hα hZ1 hZ2
  obtain ⟨hLZ, -, β₁, hβ₁s, hβ₁k, hβ₁e⟩ := hZ1
  have hβ₁i : Function.Injective β₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ₁k, Subgroup.bot_subgroupOf]
  have hZsq : ∀ z ∈ centerOf Q, z * z = 1 := by
    intro z hz
    have : (⟨z * z, (centerOf Q).mul_mem hz hz⟩ : ↥(centerOf Q)) = 1 := by
      apply hβ₁i
      rw [show (⟨z * z, (centerOf Q).mul_mem hz hz⟩ : ↥(centerOf Q)) = ⟨z, hz⟩ * ⟨z, hz⟩ from rfl,
        map_mul, map_one]
      apply Multiplicative.toAdd.injective
      funext i j
      simp only [toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply]
      exact add_self_eq_zero_of_card_two hF _
    exact congrArg Subtype.val this
  have hSZ : ∀ s ∈ S, s ∈ Subgroup.normalizer ((centerOf Q : Subgroup G) : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hSQ hs,
      S153F.mem_normalizer_centralizer_of_mem_normalizer (hSQ hs)⟩
  have hCZ : ∀ n ∈ centerOf Q, (∀ y ∈ YL, y * n * y⁻¹ = n) → n = 1 := by
    intro n₀ hn₀ hfix₀
    by_contra hn₀1
    set X : Subgroup G := centerOf Q ⊓ Subgroup.centralizer (YL : Set G) with hX
    have hXS : X ≤ S := inf_le_left.trans (hZQ.trans hQS)
    have hXN : S ≤ Subgroup.normalizer (X : Set G) := fun s hs =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hSZ s hs,
        S153F.mem_normalizer_centralizer_of_mem_normalizer (hSYL hs)⟩
    have hn₀X : n₀ ∈ X := ⟨hn₀, Subgroup.mem_centralizer_iff.mpr fun y hy => by
      have := hfix₀ y hy
      exact mul_inv_eq_iff_eq_mul.mp this⟩
    have hX1 : X ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.mem_bot] at hn₀X
      exact hn₀1 hn₀X
    obtain ⟨n, hnX, hn1, hnS⟩ := exists_central_of_normal hS2 hXS hXN hX1
    have hnZ : n ∈ centerOf Q := hnX.1
    have hnV : n ∈ V := hΩ n (hXS hnX) hnS (hZsq n hnZ)
    refine hn1 (hVfix n hnV (fun y hy => ?_) (fun y hy => hYCZ y hy n hnZ))
    have := Subgroup.mem_centralizer_iff.mp hnX.2 y hy
    exact mul_inv_eq_iff_eq_mul.mpr this
  have hfix : ∀ x : Fin 3 → F, (∀ (y : G) (hy : y ∈ YL),
      ((α ⟨y, hYLL hy⟩ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x = x) →
        x = 0 := by
    intro x hx
    obtain ⟨z, hz⟩ := hβ₁s (Multiplicative.ofAdd (fun _ => x))
    have hzfix : ∀ y ∈ YL, y * (z : G) * y⁻¹ = z := by
      intro y hy
      have hyz : y * (z : G) * y⁻¹ ∈ centerOf Q :=
        (Subgroup.mem_normalizer_iff.mp (hLZ (hYLL hy)) _).mp z.2
      have hact := hβ₁e ⟨y, hYLL hy⟩ z ⟨_, hyz⟩ rfl 0
      have hzx : Multiplicative.toAdd (β₁ z) 0 = x := by rw [hz]; rfl
      have h' : moduleAct false (α ⟨y, hYLL hy⟩ : Matrix.GeneralLinearGroup (Fin 3) F) =
          ((α ⟨y, hYLL hy⟩ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        simp [moduleAct]
      rw [h', hzx, hx y hy] at hact
      have : (⟨y * (z : G) * y⁻¹, hyz⟩ : ↥(centerOf Q)) = z := by
        apply hβ₁i
        apply Multiplicative.toAdd.injective
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        rw [hact, hzx]
      exact congrArg Subtype.val this
    have hz1 : (z : G) = 1 := hCZ z z.2 hzfix
    have : z = 1 := Subtype.ext hz1
    rw [this, map_one] at hz
    have h2 := congrArg (fun w : Multiplicative (Fin 1 → Fin 3 → F) =>
      Multiplicative.toAdd w (0 : Fin 1)) hz
    simpa using h2.symm
  have hprod := exists_mul_of_dual hF hZ2 hYLL hYLQ le_rfl hfix
  have hHQ : ⁅Q, YL⁆ ≤ Q := by
    refine Subgroup.commutator_le.mpr fun q hq y hy => ?_
    have h1 : y * q⁻¹ * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hYLQ hy) _).mp (Q.inv_mem hq)
    have e : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
    rw [commutatorElement_def, e]
    exact Q.mul_mem hq h1
  have hQH : Q ≤ ⁅Q, YL⁆ := le_of_central_mul hHQ hZQ hZc hprod hZcomm
  have hHY : ⁅Q, YL⁆ ≤ YL := by
    refine Subgroup.commutator_le.mpr fun q hq y hy => ?_
    have h1 : q * y * q⁻¹ ∈ YL := (Subgroup.mem_normalizer_iff.mp (hQYL hq) _).mp hy
    rw [commutatorElement_def]
    exact YL.mul_mem h1 (YL.inv_mem hy)
  exact hQH.trans hHY

theorem isE2_card_sq {m : ℕ} {X : Type} [Group X] (h : IsE2 m X) :
    Nat.card X = 2 ^ m ∧ ∀ x : X, x * x = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨?_, fun x => ?_⟩
  · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_pi]
  · apply e.injective
    rw [map_mul, map_one]
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply]
    generalize Multiplicative.toAdd (e x) i = a
    revert a
    decide

end Case3

end SBd7

end CFSG.Quasithin
