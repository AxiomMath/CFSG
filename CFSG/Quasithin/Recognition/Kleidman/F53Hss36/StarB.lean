module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.NatAPI

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher Equiv
open scoped commutatorElement

set_option linter.unusedSectionVars false

private theorem fact_sq' : ∀ t : Perm (Fin 5), t * t = 1 → ∀ c : Fin 4 → ZMod 2,
    CFSG.Quasithin.F53Mod.natAct t (CFSG.Quasithin.F53Mod.natAct t c - c) = CFSG.Quasithin.F53Mod.natAct t c - c := by
  decide +kernel

private theorem toAdd_act' (g : Perm (Fin 5)) (w : nat.W) :
    Multiplicative.toAdd (nat.act g w) = CFSG.Quasithin.F53Mod.natAct g (Multiplicative.toAdd w) := rfl

private theorem mem_zpowers_invol {t b : Perm (Fin 5)} (ht : t * t = 1)
    (hb : b ∈ Subgroup.zpowers t) : b = 1 ∨ b = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, ht, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, ht, one_zpow, one_mul, zpow_one]

theorem quad_nat_of_sq {t : Perm (Fin 5)} (ht : t * t = 1) :
    commW nat (Subgroup.zpowers t) (commW nat (Subgroup.zpowers t) ⊤) = ⊥ := by
  have hz := fun {b} (hb : b ∈ Subgroup.zpowers t) => mem_zpowers_invol ht hb
  have e2 : ∀ (g : Perm (Fin 5)) (w : nat.W),
      (Multiplicative.toAdd (nat.act g w * w⁻¹) : Fin 4 → ZMod 2) =
        CFSG.Quasithin.F53Mod.natAct g (Multiplicative.toAdd w : Fin 4 → ZMod 2) -
          (Multiplicative.toAdd w : Fin 4 → ZMod 2) := fun g w =>
    (show (Multiplicative.toAdd (nat.act g w * w⁻¹) : Fin 4 → ZMod 2) =
        CFSG.Quasithin.F53Mod.natAct g (Multiplicative.toAdd w : Fin 4 → ZMod 2) +
          -(Multiplicative.toAdd w : Fin 4 → ZMod 2) from rfl).trans
      (sub_eq_add_neg _ _).symm
  have hfixgen : ∀ (b b' : Perm (Fin 5)), b ∈ Subgroup.zpowers t → b' ∈ Subgroup.zpowers t →
      ∀ w : nat.W, nat.act b' (nat.act b w * w⁻¹) = nat.act b w * w⁻¹ := by
    intro b b' hb hb' w
    apply Multiplicative.toAdd.injective
    rcases hz hb with rfl | rfl <;> rcases hz hb' with rfl | rfl
    · simp
    · simp
    · simp
    · exact ((toAdd_act' _ _).trans (congrArg (CFSG.Quasithin.F53Mod.natAct _) (e2 _ _))).trans
        ((fact_sq' _ ht _).trans (e2 _ _).symm)
  have h1 : commW nat (Subgroup.zpowers t) ⊤ ≤ fixW nat (Subgroup.zpowers t) := by
    unfold commW
    rw [Subgroup.closure_le]
    rintro _ ⟨b, hb, u, -, rfl⟩ b' hb'
    exact hfixgen b b' hb hb' u
  unfold commW
  rw [Subgroup.closure_eq_bot_iff]
  rintro _ ⟨b, hb, u, hu, rfl⟩
  have := h1 hu b hb
  rw [Set.mem_singleton_iff, this, mul_inv_cancel]

theorem idx_nat_invol {t : Perm (Fin 5)} (ht : t * t = 1) (ht1 : t ≠ 1) : idx nat t = 4 := by
  rw [idx_nat]
  simp [ht1, pow_two, ht]

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem fixSecIn_eq_commSec {δ : Geo H M} (hδ : vtype δ = false) {x : G} (hx : x ∈ stab δ)
    (hxQ : x ∉ Qv δ) (hx2 : x * x ∈ Qv δ) :
    fixSecIn (Subgroup.zpowers x) (F53B3.Cv δ) (Vn δ) =
      commSec (Subgroup.zpowers x) (F53B3.Cv δ) (Vn δ) := by
  obtain ⟨hN, θ, βm, -, hθk, hsd⟩ := C.exists_secData hδ
  have hLX : F53B3.Cv δ ≤ Vn δ := inf_le_left
  have hAK : Subgroup.zpowers x ≤ stab δ := Subgroup.zpowers_le.mpr hx
  have hmap := map_zpowers_subgroupOf hx θ
  have ht1 : θ ⟨x, hx⟩ ≠ 1 := by
    intro h1
    have : (⟨x, hx⟩ : ↥(stab δ)) ∈ θ.ker := h1
    rw [hθk, Subgroup.mem_subgroupOf] at this
    exact hxQ this
  have htt : θ ⟨x, hx⟩ * θ ⟨x, hx⟩ = 1 := by
    rw [← map_mul]
    have : (⟨x, hx⟩ * ⟨x, hx⟩ : ↥(stab δ)) ∈ θ.ker := by
      rw [hθk, Subgroup.mem_subgroupOf]; exact hx2
    exact this
  have hq := quad_nat_of_sq htt
  have hCX : commSec (Subgroup.zpowers x) (F53B3.Cv δ) (Vn δ) ≤ Vn δ :=
    sup_le (hsd.commutator_le hAK) hLX
  have hFX : fixSecIn (Subgroup.zpowers x) (F53B3.Cv δ) (Vn δ) ≤ Vn δ := by
    unfold fixSecIn
    rw [Subgroup.closure_le]
    exact fun y hy => hy.1
  have hle : commSec (Subgroup.zpowers x) (F53B3.Cv δ) (Vn δ) ≤
      fixSecIn (Subgroup.zpowers x) (F53B3.Cv δ) (Vn δ) := by
    have hquad := (hsd.quadratic_iff hLX hAK).mpr (by rw [hmap]; exact hq)
    intro c hc
    refine Subgroup.subset_closure ⟨hCX hc, fun a ha => ?_⟩
    have h1 := hquad (Subgroup.commutator_mem_commutator hc ha)
    have e : a * c * a⁻¹ * c⁻¹ = (⁅c, a⁆)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact (F53B3.Cv δ).inv_mem h1
  have h1 : (fixSecIn (Subgroup.zpowers x) (F53B3.Cv δ) (Vn δ)).relIndex (Vn δ) = 4 := by
    rw [hsd.relIndex_fixSecIn hLX hAK, hmap]
    exact idx_nat_invol htt ht1
  have h2 : (F53B3.Cv δ).relIndex (commSec (Subgroup.zpowers x) (F53B3.Cv δ) (Vn δ)) = 4 := by
    rw [hsd.card_commSec hLX hAK, hmap,
      card_commW_zpowers_eq_relIndex (isInvSub_zpowers_top nat _), Subgroup.relIndex_top_right]
    exact idx_nat_invol htt ht1
  have h3 : (F53B3.Cv δ).relIndex (Vn δ) = 16 := by
    rw [hsd.relIndex_eq, card_nat]
  have hm1 := Subgroup.relIndex_mul_relIndex (F53B3.Cv δ)
    (commSec (Subgroup.zpowers x) (F53B3.Cv δ) (Vn δ)) (Vn δ) le_sup_right hCX
  rw [h2, h3] at hm1
  have hm2 := Subgroup.relIndex_mul_relIndex
    (commSec (Subgroup.zpowers x) (F53B3.Cv δ) (Vn δ))
    (fixSecIn (Subgroup.zpowers x) (F53B3.Cv δ) (Vn δ)) (Vn δ) hle hFX
  rw [h1, show (commSec (Subgroup.zpowers x) (F53B3.Cv δ) (Vn δ)).relIndex (Vn δ) = 4 by omega]
    at hm2
  have h4 : (commSec (Subgroup.zpowers x) (F53B3.Cv δ) (Vn δ)).relIndex
      (fixSecIn (Subgroup.zpowers x) (F53B3.Cv δ) (Vn δ)) = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h4) hle

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
