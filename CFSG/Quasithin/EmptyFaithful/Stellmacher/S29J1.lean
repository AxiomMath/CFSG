module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S29Base
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

open scoped commutatorElement

namespace F53.Stellmacher.S29

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α a₂ a₃ β : Geo H M}

namespace S29Step6

omit [Finite G] in
theorem commute_of_mem {E : Subgroup G} (hE : IsElemAbelian 2 E) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : Commute x y :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

omit [Finite G] in
theorem elemAbelian_of_le {E F : Subgroup G} (hE : IsElemAbelian 2 E) (hFE : F ≤ E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

omit [Finite G] in
theorem exists_mul_of_mem_sup {B C : Subgroup G} (h : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) {w : G}
    (hw : w ∈ B ⊔ C) : ∃ x ∈ B, ∃ y ∈ C, w = x * y := by
  have hBC : B ≤ Subgroup.normalizer (C : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun c hc => (h b hb c hc).symm)
  have hw' : w ∈ ((B ⊔ C : Subgroup G) : Set G) := hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right B C hBC] at hw'
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hw'
  exact ⟨x, hx, y, hy, rfl⟩

omit [Finite G] in
theorem elemAbelian_sup {B C : Subgroup G} (hB : IsElemAbelian 2 B) (hC : IsElemAbelian 2 C)
    (h : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) : IsElemAbelian 2 (B ⊔ C) :=
  CFSG.Open.IsElemAbelian.sup_of_commute hB hC h

omit [Finite G] in
theorem card_sup_mul_card_inf {B C : Subgroup G} (hP : IsMulCommutative ↥(B ⊔ C)) :
    Nat.card ↥(B ⊔ C) * Nat.card ↥(B ⊓ C) = Nat.card B * Nat.card C := by
  have hBP : B ≤ B ⊔ C := le_sup_left
  have hCP : C ≤ B ⊔ C := le_sup_right
  have : (C.subgroupOf (B ⊔ C)).Normal :=
    ⟨fun n hn g => by rwa [mul_comm' g n, mul_inv_cancel_right]⟩
  have key := Subgroup.relIndex_sup_right (H := B.subgroupOf (B ⊔ C)) (K := C.subgroupOf (B ⊔ C))
  rw [← Subgroup.subgroupOf_sup hBP hCP, Subgroup.subgroupOf_self,
    Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hBP] at key
  have h1 := Subgroup.relIndex_mul_card (H := C) (K := B ⊔ C)
  have h2 := Subgroup.relIndex_mul_card (H := C) (K := B)
  rw [inf_eq_left.mpr hCP] at h1
  rw [inf_comm] at h2
  have h3 : C.relIndex (B ⊔ C) = C.relIndex B := key
  rw [h3] at h1
  rw [← h1, ← h2]
  ring

theorem mem_Zv_of_commute (hs : Sit29 H M S α a₂ a₃ β) (hR : Zv α ⊓ Zv a₂ = Zv β) {a : G}
    (haα : a ∈ stab α) (haβ : a ∈ stab β) (haQ : a ∉ Qv β) {z : G} (hz : z ∈ Zv a₂)
    (hc : a * z = z * a) : z ∈ Zv β := by
  obtain ⟨q, hqQ, hqn⟩ := hs.swap₁₂.exists_q
  have hq : q ∈ stab a₂ ⊓ stab β := by
    rw [← hs.swap₁₂.sup_Qv]; exact Subgroup.mem_sup_left hqQ
  have h1 : z ∈ Zv a₃ := by
    rw [← (hs.Zv_conj_swap haα haβ haQ).1, mem_conjSub]
    have : a⁻¹ * z * a = z := by rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    rwa [this]
  have h2 : z ∈ Zv α := by
    rw [← (hs.swap₁₂.Zv_conj_swap hq.1 hq.2 hqn).2, mem_conjSub]
    have hzc := (Zv_le_centerOf_Qv hs.amalg a₂ hz).2
    have : q⁻¹ * z * q = z := by
      rw [mul_assoc, ← (Subgroup.mem_centralizer_iff.mp hzc q hqQ), ← mul_assoc, inv_mul_cancel,
        one_mul]
    rwa [this]
  have : z ∈ Zv α ⊓ Zv a₂ := ⟨h2, hz⟩
  rwa [hR] at this

theorem relIndex_ne_zero' (K L : Subgroup G) : K.relIndex L ≠ 0 := fun h => by
  have := Subgroup.relIndex_mul_card (H := K) (K := L)
  rw [h, zero_mul] at this
  exact Nat.card_pos.ne this

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {a g : G} (ha : a ^ 2 = 1) (hg : g ∈ Subgroup.zpowers a) :
    g = 1 ∨ g = a := by
  obtain ⟨k, rfl⟩ := hg
  show a ^ k = 1 ∨ a ^ k = a
  have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
  have h2 : a ^ (2 : ℤ) = 1 := by exact_mod_cast ha
  have hk2 : a ^ k = a ^ (k % 2) := by
    conv_lhs => rw [hk]
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk2, h, zpow_zero]
  · right
    rw [hk2, h, zpow_one]

theorem core (hs : Sit29 H M S α a₂ a₃ β) (hb : 2 < bMin H M) (hR : Zv α ⊓ Zv a₂ = Zv β)
    {A : Subgroup G} (hA : IsMaxElemAbelian (stab α ⊓ stab β) A) (hAQ : ¬ A ≤ Qv β) : False := by
  obtain ⟨hAS, hAel, hAmax⟩ := hA
  obtain ⟨a, haA, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
  have haS := hAS haA
  have ha2 : a ^ 2 = 1 := hAel.2 a haA
  have haa : a * a = 1 := by rw [← sq]; exact ha2
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, Commute x y := fun x hx y hy => commute_of_mem hAel hx hy
  have hs2 := hs.swap₁₂
  have hs3 := hs.swap₂₃.swap₁₂.swap₂₃
  have hQbS : Qv β ≤ stab α ⊓ stab β := by rw [← hs.sup_Qv]; exact le_sup_right
  have hQbS2 : Qv β ≤ stab a₂ ⊓ stab β := by rw [← hs2.sup_Qv]; exact le_sup_right
  have hZlQb : Zv a₂ ≤ Qv β := hs2.Zv_le_Qv_right
  have hZl'Qb : Zv a₃ ≤ Qv β := hs3.Zv_le_Qv_right
  have hZl'Ql : Zv a₃ ≤ Qv a₂ := hs3.Zv_le_Qv_other hb
  have hZβZl : Zv β ≤ Zv a₂ := hR ▸ inf_le_right
  have hZβQb : Zv β ≤ Qv β := Zv_le_Qv hs.amalg β
  have hZβQl : Zv β ≤ Qv a₂ := hZβZl.trans (Zv_le_Qv hs.amalg a₂)
  have hZβS : Zv β ≤ stab α ⊓ stab β :=
    le_inf ((hs.Zv_right_le.trans (Zv_le_Qv hs.amalg α)).trans (pCoreOf_le 2 _))
      (hZβQb.trans (pCoreOf_le 2 _))
  have hZβA : Zv β ≤ A := by
    have hc : ∀ x ∈ A, ∀ z ∈ Zv β, x * z = z * x := fun x hx z hz =>
      Subgroup.mem_centralizer_iff.mp (hs.hz hz).2 x (hAS hx).2
    have hel := elemAbelian_sup hAel (isElemAbelian_Zv hs.amalg β) hc
    have hle : A ⊔ Zv β ≤ stab α ⊓ stab β := sup_le hAS hZβS
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : A ≤ A ⊔ Zv β)
      (hAmax _ hle hel)
    exact heq ▸ le_sup_right
  have hCa : ∀ z ∈ Zv a₂, a * z = z * a → z ∈ Zv β := fun z hz hc =>
    mem_Zv_of_commute hs hR haS.1 haS.2 haQ hz hc
  have hZβA₁ : Zv β ≤ Qv a₂ ⊓ (Qv β ⊓ A) := le_inf hZβQl (le_inf hZβQb hZβA)
  have hA₁A : Qv a₂ ⊓ (Qv β ⊓ A) ≤ A := inf_le_right.trans inf_le_right
  have hinfA : (Qv a₂ ⊓ (Qv β ⊓ A)) ⊓ Zv a₂ = Zv β :=
    le_antisymm (fun x hx => hCa x hx.2 (hAcomm a haA x (hA₁A hx.1)).eq)
      (le_inf hZβA₁ hZβZl)
  have hZlcent : ∀ x ∈ Qv a₂, ∀ y ∈ Zv a₂, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hs.amalg a₂ hy).2 x hx
  have hCel : IsElemAbelian 2 (Qv a₂ ⊓ (Qv β ⊓ A) ⊔ Zv a₂) :=
    elemAbelian_sup (elemAbelian_of_le hAel hA₁A) (isElemAbelian_Zv hs.amalg a₂)
      fun x hx y hy => hZlcent x hx.1 y hy
  have hCS : Qv a₂ ⊓ (Qv β ⊓ A) ⊔ Zv a₂ ≤ stab α ⊓ stab β :=
    sup_le (hA₁A.trans hAS) (hZlQb.trans hQbS)
  have hcardC : Nat.card ↥(Qv a₂ ⊓ (Qv β ⊓ A) ⊔ Zv a₂) * 2 =
      Nat.card ↥(Qv a₂ ⊓ (Qv β ⊓ A)) * 16 := by
    have h := card_sup_mul_card_inf (B := Qv a₂ ⊓ (Qv β ⊓ A)) (C := Zv a₂) hCel.1
    rwa [hinfA, hs.card_Zv_right, hs2.card_Zv] at h
  have hrel : (Qv β).relIndex A = 2 := by
    have h1 : (Qv β).relIndex A ≤ 2 := by
      have := Subgroup.relIndex_le_of_le_right hAS (relIndex_ne_zero' (Qv β) _)
      rwa [hs.relIndex_Qv_right] at this
    have h2 : (Qv β).relIndex A ≠ 1 := fun h => hAQ (Subgroup.relIndex_eq_one.mp h)
    have h3 : (Qv β).relIndex A ≠ 0 := relIndex_ne_zero' _ _
    omega
  have hAcard : 2 * Nat.card ↥(Qv β ⊓ A) = Nat.card A := by
    have := Subgroup.relIndex_mul_card (H := Qv β) (K := A)
    rwa [hrel] at this
  have hA₀S : Qv β ⊓ A ≤ stab a₂ ⊓ stab β := inf_le_left.trans hQbS2
  have hmod := hs.mod₂.elem_abelian (Qv β ⊓ A) hA₀S (elemAbelian_of_le hAel inf_le_right)
  have hr := Subgroup.relIndex_mul_card (H := Qv a₂) (K := Qv β ⊓ A)
  rw [← Subgroup.inf_relIndex_right] at hr
  have hpos : 0 < Nat.card ↥(Qv a₂ ⊓ (Qv β ⊓ A)) := Nat.card_pos
  have hCle : Nat.card ↥(Qv a₂ ⊓ (Qv β ⊓ A) ⊔ Zv a₂) ≤ Nat.card A :=
    hAmax _ hCS hCel
  have hr4 : (Qv a₂ ⊓ (Qv β ⊓ A)).relIndex (Qv β ⊓ A) = 4 := by
    have hle4 : (Qv a₂ ⊓ (Qv β ⊓ A)).relIndex (Qv β ⊓ A) ≤ 4 := hmod.1
    set r := (Qv a₂ ⊓ (Qv β ⊓ A)).relIndex (Qv β ⊓ A)
    set c1 := Nat.card ↥(Qv a₂ ⊓ (Qv β ⊓ A))
    have h1 : 4 * c1 ≤ r * c1 := by nlinarith
    have h2 : 4 ≤ r := Nat.le_of_mul_le_mul_right h1 hpos
    omega
  set A₀ := Qv β ⊓ A with hA₀
  set A₁ := Qv a₂ ⊓ A₀ with hA₁
  have hA₀A : A₀ ≤ A := inf_le_right
  set C := A₁ ⊔ Zv a₂ with hC
  rw [hr4] at hr
  have hAC : Nat.card A = Nat.card C := by omega
  have hmaxC : ∀ B ≤ stab α ⊓ stab β, IsElemAbelian 2 B → Nat.card B ≤ Nat.card C :=
    fun B hB hBel => hAC ▸ hAmax B hB hBel
  have hconj : ∀ z ∈ Zv a₂, a * z * a⁻¹ ∈ Zv a₃ := by
    intro z hz
    rw [← (hs.Zv_conj_swap haS.1 haS.2 haQ).1, mem_conjSub]
    have : a⁻¹ * (a * z * a⁻¹) * a = z := by group
    rwa [this]
  have hconj' : ∀ u ∈ Zv a₃, a⁻¹ * u * a ∈ Zv a₂ := by
    intro u hu
    rw [← (hs.Zv_conj_swap haS.1 haS.2 haQ).1, mem_conjSub] at hu
    exact hu
  have hZl'comm : ∀ u ∈ Zv a₃, ∀ c ∈ C, u * c = c * u := by
    intro u hu c hc
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup (B := A₁) (C := Zv a₂)
      (fun x hx y hy => hZlcent x hx.1 y hy) hc
    have hz := hconj' u hu
    have hxz : Commute x (a⁻¹ * u * a) := hZlcent x hx.1 _ hz
    have hxa : Commute x a := hAcomm x (hA₁A hx) a haA
    have hxu : Commute x u := by
      have h := (hxa.mul_right hxz).mul_right hxa.inv_right
      rwa [show a * (a⁻¹ * u * a) * a⁻¹ = u by group] at h
    have huy : Commute u y := hZlcent u (hZl'Ql hu) y hy
    exact ((hxu.symm.mul_right huy)).eq
  have hel' : IsElemAbelian 2 (Zv a₃ ⊔ C) :=
    elemAbelian_sup (isElemAbelian_Zv hs.amalg a₃) hCel hZl'comm
  have hle' : Zv a₃ ⊔ C ≤ stab α ⊓ stab β := sup_le (hZl'Qb.trans hQbS) hCS
  have hZl'C : Zv a₃ ≤ C := by
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_right : C ≤ Zv a₃ ⊔ C)
      (hmaxC _ hle' hel')
    calc Zv a₃ ≤ Zv a₃ ⊔ C := le_sup_left
      _ = C := heq.symm
  have hZlC : Zv a₂ ≤ C := le_sup_right
  have hcom6e : ∀ z ∈ Zv a₂, z * (a * z * a⁻¹) ∈ A₁ := by
    intro z hz
    have hu : a * z * a⁻¹ ∈ Zv a₃ := hconj z hz
    have hwC : z * (a * z * a⁻¹) ∈ C := C.mul_mem (hZlC hz) (hZl'C hu)
    have hcomm : z * (a * z * a⁻¹) = (a * z * a⁻¹) * z :=
      (commute_of_mem hCel (hZlC hz) (hZl'C hu)).eq
    rw [hainv] at hcomm hwC ⊢
    have hfix : a * (z * (a * z * a)) = z * (a * z * a) * a := by
      have e1 : a * ((a * z * a) * z) = z * a * z := by
        calc a * ((a * z * a) * z) = (a * a) * (z * a * z) := by simp only [mul_assoc]
          _ = z * a * z := by rw [haa, one_mul]
      have e2 : z * (a * z * a) * a = z * a * z := by
        calc z * (a * z * a) * a = z * a * z * (a * a) := by simp only [mul_assoc]
          _ = z * a * z := by rw [haa, mul_one]
      calc a * (z * (a * z * a)) = a * ((a * z * a) * z) := by rw [hcomm]
        _ = z * a * z := e1
        _ = z * (a * z * a) * a := e2.symm
    obtain ⟨x, hx, y, hy, hw⟩ :=
      exists_mul_of_mem_sup (B := A₁) (C := Zv a₂)
        (fun x hx y hy => hZlcent x hx.1 y hy) hwC
    have hxa : x * a = a * x := (hAcomm x (hA₁A hx) a haA).eq
    have hay : a * y = y * a := by
      rw [hw] at hfix
      have : x * (a * y) = x * (y * a) := by
        calc x * (a * y) = (x * a) * y := by rw [mul_assoc]
          _ = (a * x) * y := by rw [hxa]
          _ = a * (x * y) := by rw [mul_assoc]
          _ = x * y * a := hfix
          _ = x * (y * a) := by rw [mul_assoc]
      exact mul_left_cancel this
    rw [hw]
    exact A₁.mul_mem hx (hZβA₁ (hCa y hy hay))
  have hcomm_le : ⁅Zv a₂, Subgroup.zpowers a⁆ ≤ A₁ := by
    rw [Subgroup.commutator_le]
    intro z hz g hg
    rcases eq_one_or_eq_of_mem_zpowers ha2 hg with h | h
    · rw [h, commutatorElement_one_right]; exact A₁.one_mem
    · rw [h]
      have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right
        (by rw [← sq]; exact (isElemAbelian_Zv hs.amalg a₂).2 z hz)
      have := hcom6e z hz
      rw [commutatorElement_def, hzinv, hainv]
      simpa [hainv, mul_assoc] using this
  have h1 : ⁅⁅Zv a₂, Subgroup.zpowers a⁆, A₀⁆ = ⊥ := by
    have hbot : ⁅A₁, A₀⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (hAcomm y (hA₀A hy) x (hA₁A hx)).eq
    exact le_bot_iff.mp ((Subgroup.commutator_mono hcomm_le le_rfl).trans hbot.le)
  have h2 : ⁅⁅Subgroup.zpowers a, A₀⁆, Zv a₂⁆ = ⊥ := by
    have hbot : ⁅Subgroup.zpowers a, A₀⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (hAcomm y (hA₀A hy) a haA).eq))
    rw [hbot, Subgroup.commutator_bot_left]
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := A₀) (H₂ := Zv a₂) (H₃ := Subgroup.zpowers a) h1 h2
  have h4 : ⁅A₀, Zv a₂⁆ ≤ Zv β := by
    intro u hu
    have huZ : u ∈ Zv a₂ := by
      refine (Subgroup.commutator_le.mpr (fun x hx z hz => ?_)) hu
      have hxs : x ∈ stab a₂ := (hA₀S hx).1
      have hxz := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hs.amalg a₂ hxs) z).mp hz
      rw [commutatorElement_def]
      exact (Zv a₂).mul_mem hxz ((Zv a₂).inv_mem hz)
    have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3 hu
    exact hCa u huZ (Subgroup.mem_centralizer_iff.mp hcent a (Subgroup.mem_zpowers a))
  have h5 : Nat.card ↥⁅Zv a₂, A₀⁆ ≤ 2 := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.card_le_of_le h4).trans (hs.card_Zv_right ▸ le_rfl)
  have h6 := hmod.2.2 hr4
  omega

end S29Step6

theorem step6 (hs : Sit29 H M S α a₂ a₃ β) (hb : 2 < bMin H M)
    (hR : Zv α ⊓ Zv a₂ = Zv β) (hJ : ¬ thompsonJ (stab α ⊓ stab β) ≤ Qv β) : False := by
  have h : ∃ A : Subgroup G, IsMaxElemAbelian (stab α ⊓ stab β) A ∧ ¬ A ≤ Qv β := by
    by_contra hne
    exact hJ (iSup₂_le fun A hA => not_not.mp fun hAQ => hne ⟨A, hA, hAQ⟩)
  obtain ⟨A, hA, hAQ⟩ := h
  exact S29Step6.core hs hb hR hA hAQ

end F53.Stellmacher.S29

end CFSG.Quasithin
