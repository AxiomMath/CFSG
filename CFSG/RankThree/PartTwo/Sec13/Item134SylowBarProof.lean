module

public import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarNorm
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarCoords
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace Item134SylowBarProof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_inv_subgroup {A : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (x : G) :
    ∃ Am : Subgroup G, ∀ a, a ∈ Am ↔ a ∈ A ∧ x * a * x⁻¹ = a⁻¹ := by
  refine ⟨{ carrier := {a | a ∈ A ∧ x * a * x⁻¹ = a⁻¹}
            one_mem' := ⟨one_mem A, by group⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun a => Iff.rfl⟩
  · rintro a b ⟨ha, hax⟩ ⟨hb, hbx⟩
    refine ⟨mul_mem ha hb, ?_⟩
    calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      _ = a⁻¹ * b⁻¹ := by rw [hax, hbx]
      _ = (a * b)⁻¹ := by rw [mul_inv_rev, (hA _ (inv_mem hb) _ (inv_mem ha)).symm]
  · rintro a ⟨ha, hax⟩
    refine ⟨inv_mem ha, ?_⟩
    calc x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
      _ = a⁻¹⁻¹ := by rw [hax]

theorem eigen_decomp {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A) {x : G}
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hx2 : ∀ a ∈ A, x * x * a * (x * x)⁻¹ = a) :
    ∃ Ap Am : Subgroup G, (∀ a, a ∈ Ap ↔ a ∈ A ∧ x * a * x⁻¹ = a) ∧
      (∀ a, a ∈ Am ↔ a ∈ A ∧ x * a * x⁻¹ = a⁻¹) ∧ Nat.card Ap * Nat.card Am = Nat.card A := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨Am, hAm⟩ := exists_inv_subgroup hcomm x
  set Ap := A ⊓ Subgroup.centralizer ({x} : Set G) with hApdef
  have hAp : ∀ a, a ∈ Ap ↔ a ∈ A ∧ x * a * x⁻¹ = a := by
    intro a
    rw [hApdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨ha, hxa⟩
      exact ⟨ha, by rw [← hxa, mul_inv_cancel_right]⟩
    · rintro ⟨ha, hxa⟩
      refine ⟨ha, ?_⟩
      calc a * x = x * a * x⁻¹ * x := by rw [hxa]
        _ = x * a := by group
  refine ⟨Ap, Am, hAp, hAm, ?_⟩
  have hxa : ∀ a ∈ A, x * a * x⁻¹ ∈ A := fun a ha => (Subgroup.mem_normalizer_iff.mp hxA a).mp ha
  have hxx : ∀ a ∈ A, x * (x * a * x⁻¹) * x⁻¹ = a := fun a ha => by
    have := hx2 a ha
    calc x * (x * a * x⁻¹) * x⁻¹ = x * x * a * (x * x)⁻¹ := by group
      _ = a := this
  have hc : ∀ y ∈ Ap, ∀ z ∈ Am, y * z = z * y := fun y hy z hz =>
    hcomm y ((hAp y).mp hy).1 z ((hAm z).mp hz).1
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Ap Am hc
  have hinf : Ap ⊓ Am = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨haA, hp⟩ := (hAp a).mp ha1
    obtain ⟨-, hm⟩ := (hAm a).mp ha2
    have h1 : a = a⁻¹ := hp.symm.trans hm
    have h2 : a * a = 1 := mul_eq_one_iff_eq_inv.mpr h1
    have h3 : a ^ 3 = 1 := hA.2 a haA
    rw [Subgroup.mem_bot]
    calc a = a ^ 3 * (a * a)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  have hsup : Ap ⊔ Am = A := by
    apply le_antisymm (sup_le (fun a ha => ((hAp a).mp ha).1) (fun a ha => ((hAm a).mp ha).1))
    intro a ha
    set b := x * a * x⁻¹ with hb
    have hbA : b ∈ A := hxa a ha
    have hab : a * b = b * a := hcomm a ha b hbA
    have hp : (a * b) ^ 2 ∈ Ap := by
      refine (hAp _).mpr ⟨pow_mem (mul_mem ha hbA) 2, ?_⟩
      rw [← conj_pow]
      congr 1
      calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
        _ = b * a := by rw [← hb, hxx a ha]
        _ = a * b := hab.symm
    have hm : (a * b⁻¹) ^ 2 ∈ Am := by
      refine (hAm _).mpr ⟨pow_mem (mul_mem ha (inv_mem hbA)) 2, ?_⟩
      rw [← conj_pow, ← inv_pow]
      congr 1
      calc x * (a * b⁻¹) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹)⁻¹ := by group
        _ = b * a⁻¹ := by rw [← hb, hxx a ha]
        _ = (a * b⁻¹)⁻¹ := by group
    have h3 : a ^ 3 = 1 := hA.2 a ha
    have heq : (a * b) ^ 2 * (a * b⁻¹) ^ 2 = a := by
      have hc' : Commute a b := hab
      have h22 : a ^ 2 * b ^ 2 = b ^ 2 * a ^ 2 := (hc'.pow_pow 2 2).eq
      calc (a * b) ^ 2 * (a * b⁻¹) ^ 2 = (a ^ 2 * b ^ 2) * (a ^ 2 * b⁻¹ ^ 2) := by
            rw [hc'.mul_pow, (hc'.inv_right).mul_pow]
        _ = a ^ 2 * (b ^ 2 * a ^ 2) * b⁻¹ ^ 2 := by group
        _ = a ^ 2 * (a ^ 2 * b ^ 2) * b⁻¹ ^ 2 := by rw [h22]
        _ = a ^ 3 * a := by group
        _ = a := by rw [h3, one_mul]
    rw [← heq]
    exact Subgroup.mul_mem_sup hp hm
  rw [hinf, Subgroup.card_bot, mul_one, hsup] at hcard
  exact hcard.symm

omit [Finite G] in
theorem conj_eq_or_eq_inv {x y : G} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hx : x * y * x⁻¹ ∈ Subgroup.zpowers y) : x * y * x⁻¹ = y ∨ x * y * x⁻¹ = y⁻¹ := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hj' : y ^ (j % 3) = x * y * x⁻¹ := by
    rw [← hj]
    conv_rhs => rw [← Int.mul_ediv_add_emod j 3]
    rw [zpow_add, zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hy3, one_zpow,
      one_mul]
  rcases (show j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 by omega) with h | h | h
  · exfalso
    apply hy1
    rw [h, zpow_zero] at hj'
    calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
      _ = 1 := by rw [← hj']; group
  · left
    rw [h, zpow_one] at hj'
    exact hj'.symm
  · right
    rw [h] at hj'
    rw [← hj']
    calc y ^ (2 : ℤ) = y ^ 3 * y⁻¹ := by group
      _ = y⁻¹ := by rw [hy3, one_mul]

namespace Base

variable {A L K : Subgroup G} {c d : G}

theorem mem_normalizer_c_of_central
    (H : Base A c L d K) {S T : Subgroup G}
    (hSD : SylowData A L d K S) (hTD : TData A c L d S T) {x₀ : G}
    (hx₀W : x₀ ∈ Subgroup.normalizer (A : Set G))
    (hx₀d : x₀ ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hcent : ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ a ∈ A,
      (w * x₀ * w⁻¹) * a * (w * x₀ * w⁻¹)⁻¹ = x₀ * a * x₀⁻¹) :
    x₀ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set CA := Subgroup.centralizer (A : Set G) with hCA
  have hCAW : CA ≤ Subgroup.normalizer (A : Set G) := fun g hg =>
    Subgroup.mem_normalizer_fintype fun a ha => by
      rw [SetLike.mem_coe, (Subgroup.mem_centralizer_iff.mp hg a ha).symm, mul_inv_cancel_right]
      exact ha
  have hCAc : CA ≤ Subgroup.centralizer ({c} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hg c H.data.mem_A).symm
  have hCAd : CA ≤ Subgroup.centralizer ({d} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hg d H.mem_A).symm
  set R₀ := T ⊔ CA with hR₀
  have hR₀le : R₀ ≤ Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    sup_le hTD.isSylowOf.le (le_inf hCAW
      (fun g hg => mem_normalizer_zpowers_of_mem_centralizer (hCAd hg)))
  have hR₀c : R₀ ≤ Subgroup.centralizer ({c} : Set G) := sup_le hTD.le_c hCAc
  have hTR₀ : IsSylowOf 3 T R₀ := hTD.isSylowOf.of_le le_sup_left hR₀le
  set T' := T.map (MulAut.conj x₀).toMonoidHom with hT'
  have hT'R₀ : T' ≤ R₀ := by
    rintro _ ⟨τ, hτ, rfl⟩
    have hτW : τ⁻¹ ∈ Subgroup.normalizer (A : Set G) := inv_mem (hTD.isSylowOf.le hτ).1
    set γ := τ⁻¹ * x₀ * τ * x₀⁻¹ with hγdef
    have hγ : γ ∈ CA := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hb : x₀⁻¹ * a * x₀ ∈ A := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hx₀W) a).mp ha
        simpa using this
      have h1 := hcent τ⁻¹ hτW _ hb
      simp only [inv_inv] at h1
      have h2 : x₀ * (x₀⁻¹ * a * x₀) * x₀⁻¹ = a := by group
      rw [h2] at h1
      calc a * γ = (τ⁻¹ * x₀ * τ) * (x₀⁻¹ * a * x₀) * (τ⁻¹ * x₀ * τ)⁻¹ * γ := by rw [h1]
        _ = γ * a := by rw [hγdef]; group
    have h1 : (MulAut.conj x₀).toMonoidHom τ = τ * γ := by
      change x₀ * τ * x₀⁻¹ = τ * γ
      rw [hγdef]
      group
    rw [h1]
    exact Subgroup.mul_mem_sup hτ hγ
  have hT'syl : IsSylowOf 3 T' R₀ := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hT'R₀ ?_
    rw [hT', Subgroup.card_map_of_injective (MulAut.conj x₀).injective]
    exact hTR₀.card_eq
  obtain ⟨m, hmR₀, hm⟩ := exists_conj_of_isSylowOf hTR₀ hT'syl
  have hx₁T : m⁻¹ * x₀ ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show T.map (MulAut.conj (m⁻¹ * x₀)).toMonoidHom = T
    have h1 : T.map (MulAut.conj (m⁻¹ * x₀)).toMonoidHom =
        (T.map (MulAut.conj x₀).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [h1, ← hT', hm, Subgroup.map_map]
    convert Subgroup.map_id T using 2
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hmd : m ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := (hR₀le hmR₀).2
  have hx₁d : m⁻¹ * x₀ ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    mul_mem (inv_mem hmd) hx₀d
  have hx₁c := H.mem_normalizer_zpowers_c hSD hTD hx₁T hx₁d
  have hmc : m ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    mem_normalizer_zpowers_of_mem_centralizer (hR₀c hmR₀)
  have : x₀ = m * (m⁻¹ * x₀) := by group
  rw [this]
  exact mul_mem hmc hx₁c

end Base

namespace Hyp

variable {A L K : Subgroup G} {c d : G}

theorem normalizer_le_of_line (H : Hyp A c L d K) {S : Subgroup G} (hSD : SylowData A L d K S)
    {X Y : Subgroup G} (hXA : X ≤ A) (hX3 : Nat.card X = 3) (hY9 : Nat.card Y = 9)
    (hXY : X ⊓ Y = ⊥)
    (hXW : ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ a ∈ X, w * a * w⁻¹ ∈ X)
    (hc : c ∈ X ∨ c ∈ Y) (hd : d ∈ X ∨ d ∈ Y) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have hzc : Nat.card (Subgroup.zpowers c) = 3 := H.data.card_zpowers
  have hzd : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, H.orderOf_d]
  rcases hc with hcX | hcY
  ·
    have hXc : Subgroup.zpowers c = X :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcX) (by rw [hX3, hzc])
    intro w hw
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [SetLike.mem_coe, hXc] at hy ⊢
    exact hXW w hw y hy
  rcases hd with hdX | hdY
  · exfalso
    have hXd : Subgroup.zpowers d = X :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdX) (by rw [hX3, hzd])
    apply H.not_le
    intro w hw
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [SetLike.mem_coe, hXd] at hy ⊢
    exact hXW w hw y hy
  · exfalso
    have hBY : Subgroup.zpowers c ⊔ Subgroup.zpowers d = Y :=
      Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hcY)
        (Subgroup.zpowers_le.mpr hdY)) (by rw [hY9, H.card_B])
    obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp (fun h : X = ⊥ => by
      rw [h, Subgroup.card_bot] at hX3; norm_num at hX3))
    have hvB : (v : G) ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
      intro hv
      apply hv1
      have : (v : G) ∈ X ⊓ Y := ⟨v.2, hBY ▸ hv⟩
      rw [hXY, Subgroup.mem_bot] at this
      exact Subtype.ext this
    obtain ⟨s₀, hs₀S, a₀, ha₀A, hmove⟩ := H.exists_moved hSD
    have hs₀W := H.S_le_normalizer hSD hs₀S
    have hcomm : s₀ * v * s₀⁻¹ * (v : G)⁻¹ ∈ X ⊓ Y := by
      refine Subgroup.mem_inf.mpr ⟨X.mul_mem (hXW s₀ hs₀W v v.2) (X.inv_mem v.2), ?_⟩
      rw [← hBY]
      exact Subgroup.mem_sup_right (H.conj_mem_of_mem_S hSD hs₀S (hXA v.2))
    rw [hXY, Subgroup.mem_bot, mul_inv_eq_one] at hcomm
    have hs₀L := hSD.isSylowOf.le hs₀S
    have hAs : A ≤ Subgroup.centralizer ({s₀} : Set G) := by
      rw [← H.sup_zpowers_eq (hXA v.2) hvB]
      refine sup_le (sup_le ?_ ?_) ?_ <;>
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      · exact (H.comm_L hs₀L).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp (hSD.le_centralizer hs₀S)).symm
      · calc (v : G) * s₀ = s₀ * v * s₀⁻¹ * s₀ := by rw [hcomm]
          _ = s₀ * v := by group
    apply hmove
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hAs ha₀A)).symm, mul_inv_cancel_right]

theorem normalizer_le
    (H : Hyp A c L d K) {S T : Subgroup G} (hSD : SylowData A L d K S)
    (hTD : TData A c L d S T) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  obtain ⟨x₀, hx₀W, hx₀d, hx₀2, ⟨a₁, ha₁, ha₁x⟩, ⟨a₂, ha₂, ha₂x⟩, hcent⟩ :=
    H.exists_central_involution hSD hTD
  have hx₀c := H.mem_normalizer_c_of_central hSD hTD hx₀W hx₀d hcent
  obtain ⟨Ap, Am, hAp, hAm, hcard⟩ := eigen_decomp H.data.isElemAbelian hx₀W hx₀2
  have hApA : Ap ≤ A := fun a ha => ((hAp a).mp ha).1
  have hAmA : Am ≤ A := fun a ha => ((hAm a).mp ha).1
  have hconj : ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ a ∈ A,
      x₀ * (w * a * w⁻¹) * x₀⁻¹ = w * (x₀ * a * x₀⁻¹) * w⁻¹ := by
    intro w hw a ha
    have h1 := hcent w⁻¹ (inv_mem hw) a ha
    simp only [inv_inv] at h1
    calc x₀ * (w * a * w⁻¹) * x₀⁻¹ = w * ((w⁻¹ * x₀ * w) * a * (w⁻¹ * x₀ * w)⁻¹) * w⁻¹ := by
          group
      _ = w * (x₀ * a * x₀⁻¹) * w⁻¹ := by rw [h1]
  have hwA : ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ a ∈ A, w * a * w⁻¹ ∈ A := fun w hw a ha =>
    (Subgroup.mem_normalizer_iff.mp hw a).mp ha
  have hApW : ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ a ∈ Ap, w * a * w⁻¹ ∈ Ap := by
    intro w hw a ha
    obtain ⟨haA, hax⟩ := (hAp a).mp ha
    exact (hAp _).mpr ⟨hwA w hw a haA, by rw [hconj w hw a haA, hax]⟩
  have hAmW : ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ a ∈ Am, w * a * w⁻¹ ∈ Am := by
    intro w hw a ha
    obtain ⟨haA, hax⟩ := (hAm a).mp ha
    exact (hAm _).mpr ⟨hwA w hw a haA, by rw [hconj w hw a haA, hax]; group⟩
  have hinf : Ap ⊓ Am = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨haA, hp⟩ := (hAp a).mp ha.1
    obtain ⟨-, hm⟩ := (hAm a).mp ha.2
    have h1 : a = a⁻¹ := hp.symm.trans hm
    have h2 : a * a = 1 := mul_eq_one_iff_eq_inv.mpr h1
    have h3 : a ^ 3 = 1 := H.data.isElemAbelian.2 a haA
    rw [Subgroup.mem_bot]
    calc a = a ^ 3 * (a * a)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  have hmem : ∀ y ∈ A, y ≠ 1 → x₀ * y * x₀⁻¹ ∈ Subgroup.zpowers y → y ∈ Ap ∨ y ∈ Am := by
    intro y hyA hy1 hy
    rcases conj_eq_or_eq_inv (H.data.isElemAbelian.2 y hyA) hy1 hy with h | h
    · exact Or.inl ((hAp y).mpr ⟨hyA, h⟩)
    · exact Or.inr ((hAm y).mpr ⟨hyA, h⟩)
  have hc := hmem c H.data.mem_A H.data.ne_one
    ((Subgroup.mem_normalizer_iff.mp hx₀c c).mp (Subgroup.mem_zpowers c))
  have hd := hmem d H.mem_A H.ne_one
    ((Subgroup.mem_normalizer_iff.mp hx₀d d).mp (Subgroup.mem_zpowers d))
  have hApne : Nat.card Ap ≠ 1 := by
    intro h1
    rw [h1, one_mul, H.data.card_eq] at hcard
    have hAmeq : Am = A := Subgroup.eq_of_le_of_card_ge hAmA (by rw [hcard, H.data.card_eq])
    exact ha₂x ((hAm a₂).mp (hAmeq ▸ ha₂)).2
  have hAmne : Nat.card Am ≠ 1 := by
    intro h1
    rw [h1, mul_one, H.data.card_eq] at hcard
    have hApeq : Ap = A := Subgroup.eq_of_le_of_card_ge hApA (by rw [hcard, H.data.card_eq])
    exact ha₁x ((hAp a₁).mp (hApeq ▸ ha₁)).2
  have hdvdp : Nat.card Ap ∣ 27 := H.data.card_eq ▸ Subgroup.card_dvd_of_le hApA
  have hdvdm : Nat.card Am ∣ 27 := H.data.card_eq ▸ Subgroup.card_dvd_of_le hAmA
  rw [H.data.card_eq] at hcard
  have hdiv27 : Nat.divisors 27 = {1, 3, 9, 27} := by decide
  have hp' : Nat.card Ap ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdvdp, by norm_num⟩
  have hm' : Nat.card Am ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdvdm, by norm_num⟩
  rw [hdiv27] at hp' hm'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp' hm'
  have hcases : (Nat.card Ap = 3 ∧ Nat.card Am = 9) ∨ (Nat.card Ap = 9 ∧ Nat.card Am = 3) := by
    rcases hp' with hp | hp | hp | hp <;> rcases hm' with hm | hm | hm | hm <;>
      rw [hp, hm] at hcard <;> omega
  rcases hcases with ⟨hp, hm⟩ | ⟨hp, hm⟩
  ·
    exact H.normalizer_le_of_line hSD hApA hp hm hinf hApW hc hd
  ·
    rw [inf_comm] at hinf
    exact H.normalizer_le_of_line hSD hAmA hm hp hinf hAmW hc.symm hd.symm

theorem inconsistent
    (H : Hyp A c L d K) : False := by
  obtain ⟨S, hSD⟩ := H.exists_sylowData
  obtain ⟨T, hTD⟩ := H.exists_tData hSD
  have hWH := H.normalizer_le hSD hTD
  have hdL := H.d_mem_L
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hd
    apply H.ne_one
    have hd' : d ∈ Subgroup.zpowers c ⊓ L := ⟨hd, hdL⟩
    rwa [zpowers_inf_eq_bot H.c_pow H.not_mem_L, Subgroup.mem_bot] at hd'
  have hWL : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    normalizer_inf_le_of_mem H.data.mem_thetaComponentsAt H.data.le_normalizer
      H.data.sectionCentralizer_eq H.mem_A hdL hdc
  apply H.not_le
  intro w hw
  have hwL : w ∈ Subgroup.normalizer (L : Set G) := hWL ⟨hWH hw, hw⟩
  have hwdA : w * d * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw d).mp H.mem_A
  have hwdL : w * d * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hwL d).mp hdL
  have hwd1 : w * d * w⁻¹ ≠ 1 := by
    intro h
    apply H.ne_one
    calc d = w⁻¹ * (w * d * w⁻¹) * w := by group
      _ = 1 := by rw [h]; group
  obtain ⟨hdL', S₀, hdS₀, hS₀d⟩ := H.exists_d_mem_L
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [H.data.card_eq]; norm_num)
  have hzz := zpowers_eq_of_central_of_quot_j2 H.h415 H.quot hAp H.mem_A hwdA hdL hwdL H.ne_one
    hwd1 ⟨S₀, hdS₀, hS₀d⟩ (central_conj hwL hdL ⟨S₀, hdS₀, hS₀d⟩ hwdL)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show (Subgroup.zpowers d).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers d
  rw [MonoidHom.map_zpowers]
  exact hzz.symm

end Hyp

end Item134SylowBarProof

theorem item134SylowBar_of
    (h45 : Sec4.Item4_5) (h131 : Item131) (hspor : SporadicModels131) (h415 : Sec4.Item4_15) :
    Item134SylowBar := by
  intro G _ _ A c L h hJ d hdA hd1 hS K hK hLK _ hA6 hW hZ
  exact (Item134SylowBarProof.Hyp.inconsistent
    ⟨⟨h45, h131, hspor, h415, h, hJ, hdA, hd1, hS, hK, hLK, hA6, hZ⟩, hW⟩).elim

end CFSG.RankThree.PartTwo.Sec13
