module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6FourFacts
public import CFSG.GH74.Uniqueness.Bender.AutFixed
import CFSG.GroupTheory.CommuteOfSqEqOne
import CFSG.GroupTheory.ConjKerCenter
import CFSG.GroupTheory.MulAutCongr
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.GH74.Uniqueness.Bender

variable {X X' : Type*} [Group X] [Group X']

private lemma mul_conj_eq (β : MulAut X) (y : X) :
    β * MulAut.conj y = MulAut.conj (β y) * β := by
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem FourGenWith.fourGen {H : Subgroup X} {B : Subgroup (MulAut X)} {β : MulAut X} {x : X}
    (hH : H ≤ commY B β) (h : FourGenWith H β x) : FourGen B β x := by
  obtain ⟨k, hk, hsup⟩ := h
  refine ⟨k, hk, ?_⟩
  rw [eq_top_iff, ← hsup]
  exact sup_le_sup hH (Subgroup.map_mono hH)

theorem orderOf_congr_mul_conj (e : X ≃* X') (β : MulAut X) (x : X) :
    orderOf (MulAut.congr e β *
        (MulAut.conj (e x) * MulAut.congr e β * (MulAut.conj (e x))⁻¹)) =
      orderOf (β * (MulAut.conj x * β * (MulAut.conj x)⁻¹)) := by
  have h : MulAut.congr e (β * (MulAut.conj x * β * (MulAut.conj x)⁻¹)) =
      MulAut.congr e β * (MulAut.conj (e x) * MulAut.congr e β *
        (MulAut.conj (e x))⁻¹) := by
    simp [map_mul, map_inv, CFSG.mulAut_congr_conj e x]
  rw [← h, MulEquiv.orderOf_eq]

theorem mul_conj_mul_conj_inv {β : MulAut X} (hβ : β * β = 1) (x : X) :
    β * (MulAut.conj x * β * (MulAut.conj x)⁻¹) = MulAut.conj (β x * x⁻¹) := by
  ext y
  have hβ' : ∀ z : X, β (β z) = z := by
    intro z
    have h := congrArg (fun f : MulAut X => f z) hβ
    simpa using h
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply,
    MulAut.conj_symm_apply, map_mul, map_inv, mul_inv_rev, inv_inv, hβ']

theorem conj_mul_mul_conj_inv (β : MulAut X) (k : X) :
    MulAut.conj k * β * (MulAut.conj k)⁻¹ = MulAut.conj (k * (β k)⁻¹) * β := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply,
    MulAut.conj_symm_apply, map_mul, map_inv, mul_inv_rev, inv_inv]

theorem fourGenWith_of (hZ : Subgroup.center X = ⊥) {β : MulAut X} (hβ : β * β = 1)
    {H : Subgroup X} {x k : X}
    (hk : k * (β k)⁻¹ = β ((β x * x⁻¹) ^ (orderOf (β x * x⁻¹) / 2)))
    (hgen : H ⊔ H.map (MulAut.conj k).toMonoidHom = ⊤) : FourGenWith H β x := by
  let w : X := β x * x⁻¹
  let β' : MulAut X := MulAut.conj x * β * (MulAut.conj x)⁻¹
  have hw : β * β' = MulAut.conj w := mul_conj_mul_conj_inv hβ x
  have hconj_inj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, hZ]
  have hord : orderOf (β * β') = orderOf w := by
    rw [hw]
    exact orderOf_injective (MulAut.conj : X →* MulAut X) hconj_inj w
  have hkw : k * (β k)⁻¹ = β (w ^ (orderOf w / 2)) := hk
  refine ⟨k, ?_, hgen⟩
  change MulAut.conj k * β * (MulAut.conj k)⁻¹ =
    β * (β * β') ^ (orderOf (β * β') / 2)
  calc MulAut.conj k * β * (MulAut.conj k)⁻¹
      = MulAut.conj (k * (β k)⁻¹) * β := conj_mul_mul_conj_inv β k
    _ = MulAut.conj (β (w ^ (orderOf w / 2))) * β := by rw [hkw]
    _ = β * MulAut.conj (w ^ (orderOf w / 2)) :=
          (mul_conj_eq β (w ^ (orderOf w / 2))).symm
    _ = β * (MulAut.conj w) ^ (orderOf w / 2) := by
          rw [← map_pow (MulAut.conj : X →* MulAut X) w (orderOf w / 2)]
    _ = β * (β * β') ^ (orderOf (β * β') / 2) := by rw [hord, hw]

theorem autFixed_congr (e : X ≃* X') (β : MulAut X) :
    autFixed (MulAut.congr e β) = (autFixed β).map e.toMonoidHom := by
  ext y
  rw [mem_autFixed_iff, Subgroup.mem_map]
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_autFixed_iff]
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨x, hx, rfl⟩
    rw [mem_autFixed_iff] at hx
    change e (β (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hx]

theorem commY_le_autFixed {B : Subgroup (MulAut X)} {β : MulAut X} (hB2 : ∀ b ∈ B, b * b = 1)
    (hβ : β ∈ B) : commY B β ≤ autFixed β := by
  rw [commY, Subgroup.closure_le]
  rintro w ⟨y, hy, b, hb, rfl⟩
  change β (y * (b y)⁻¹) = y * (b y)⁻¹
  have hcomm : β * b = b * β := CFSG.commute_of_sq_eq_one (by rw [pow_two]; exact hB2 β hβ)
    (by rw [pow_two]; exact hB2 b hb) (by rw [pow_two]; exact hB2 (β * b) (mul_mem hβ hb))
  have hbfix : β (b y) = b y := by
    have h := congrArg (fun f : MulAut X => f y) hcomm
    simpa [MulAut.mul_apply, hy] using h
  rw [map_mul, map_inv, hy, hbfix]

theorem autFixed_le_commY {B : Subgroup (MulAut X)} {β : MulAut X} (hB4 : Nat.card B = 4)
    (hB2 : ∀ b ∈ B, b * b = 1) (hβ : β ∈ B) (hs : IsSimpleGroup (autFixed β))
    (hc : ∀ b ∈ B, (∀ y ∈ autFixed β, b y = y) → b = 1 ∨ b = β) :
    autFixed β ≤ commY B β := by
  have hH : commY B β ≤ autFixed β := commY_le_autFixed hB2 hβ
  have hconj_le : ∀ d ∈ autFixed β,
      (commY B β).map (MulAut.conj d).toMonoidHom ≤ commY B β := by
    intro d hd
    rw [commY, MonoidHom.map_closure, Subgroup.closure_le]
    rintro w ⟨g, ⟨y, hy, b, hb, rfl⟩, rfl⟩
    have hdy : β (d * y) = d * y := by rw [map_mul, hd, hy]
    have hgen1 : d * y * (b (d * y))⁻¹ ∈ commY B β :=
      Subgroup.subset_closure ⟨d * y, hdy, b, hb, rfl⟩
    have hgen2 : d * (b d)⁻¹ ∈ commY B β :=
      Subgroup.subset_closure ⟨d, hd, b, hb, rfl⟩
    have hid : MulAut.conj d (y * (b y)⁻¹) =
        (d * y * (b (d * y))⁻¹) * (d * (b d)⁻¹)⁻¹ := by
      rw [MulAut.conj_apply]
      simp only [map_mul, mul_inv_rev, inv_inv]
      group
    change MulAut.conj d (y * (b y)⁻¹) ∈ commY B β
    rw [hid]
    exact mul_mem hgen1 (inv_mem hgen2)
  have hN : ((commY B β).subgroupOf (autFixed β)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hH]
    intro h k hh hk
    have hm : MulAut.conj k h ∈ (commY B β).map (MulAut.conj k).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hh
    have hle := hconj_le k hk hm
    rwa [MulAut.conj_apply] at hle
  haveI := hN
  rcases hs.eq_bot_or_eq_top_of_normal ((commY B β).subgroupOf (autFixed β)) with hbot | htop
  · exfalso
    have htriv : ∀ b ∈ B, ∀ y ∈ autFixed β, b y = y := by
      intro b hb y hy
      have hg : y * (b y)⁻¹ ∈ commY B β :=
        Subgroup.subset_closure ⟨y, hy, b, hb, rfl⟩
      have hgfix : y * (b y)⁻¹ ∈ autFixed β := hH hg
      have hmem : (⟨y * (b y)⁻¹, hgfix⟩ : autFixed β) ∈
          (commY B β).subgroupOf (autFixed β) := hg
      rw [hbot] at hmem
      have hone : y * (b y)⁻¹ = 1 := by
        have h := Subgroup.mem_bot.mp hmem
        simpa using congrArg Subtype.val h
      exact (mul_inv_eq_one.mp hone).symm
    have hsub : (B : Set (MulAut X)) ⊆ ({1, β} : Set (MulAut X)) := by
      intro b hb
      rcases hc b hb (htriv b hb) with h1 | hβb
      · rw [h1]
        exact Set.mem_insert _ _
      · rw [hβb]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    have hle2 : Nat.card B ≤ 2 := by
      have h1 : Nat.card B = (B : Set (MulAut X)).ncard :=
        Nat.card_coe_set_eq (B : Set (MulAut X))
      rw [h1]
      refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
      have h2 := Set.ncard_insert_le (1 : MulAut X) ({β} : Set (MulAut X))
      simpa using h2
    omega
  · exact (Subgroup.subgroupOf_eq_top).mp htop

theorem sq_mem_commY {B : Subgroup (MulAut X)} {β : MulAut X} {y t : X} (hy : β y = y)
    (ht : MulAut.conj t ∈ B) (hinv : t * y * t⁻¹ = y⁻¹) : y ^ 2 ∈ commY B β := by
  have hgen : y * ((MulAut.conj t) y)⁻¹ ∈ commY B β :=
    Subgroup.subset_closure ⟨y, hy, MulAut.conj t, ht, rfl⟩
  have hone : y * ((MulAut.conj t) y)⁻¹ = y ^ 2 := by
    rw [MulAut.conj_apply, hinv, inv_inv, pow_two]
  rwa [hone] at hgen

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
