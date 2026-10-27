module

public import CFSG.Quasithin.EmptyFaithful.S146C2
public import CFSG.LieType.Simplicity.Classical
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

section Sec4

variable {W : Type} [CommGroup W]

theorem mulAut_apply_inv_apply (z : MulAut W) (w : W) : z (z⁻¹ w) = w := by simp

theorem mulAut_inv_apply_apply (z : MulAut W) (w : W) : z⁻¹ (z w) = w := by simp

theorem le_stabSub_of_inv {L : Subgroup (MulAut W)} {U : Subgroup W} (hU : ∀ x ∈ L, ∀ a ∈ U, x a ∈ U) :
    L ≤ stabSub U := fun x hx u => by
  constructor
  · intro h
    have := hU x⁻¹ (L.inv_mem hx) _ h
    simpa using this
  · exact hU x hx u

theorem card_mulAut_le_factorial (Q : Type*) [Group Q] [Finite Q] :
    Nat.card (MulAut Q) ≤ (Nat.card Q).factorial := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have : Fintype (MulAut Q) := Fintype.ofFinite _
  have hinj : Function.Injective (MulAut.toPerm Q) := fun a b h => by
    ext x
    exact congrArg (fun p : Equiv.Perm Q => p x) h
  calc Nat.card (MulAut Q) ≤ Nat.card (Equiv.Perm Q) := Nat.card_le_card_of_injective _ hinj
    _ = (Nat.card Q).factorial := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := Q), Fintype.card_perm]

theorem normal_inf_centSec {L : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : ∀ x ∈ L, ∀ a ∈ A, x a ∈ A) (hB : ∀ x ∈ L, ∀ b ∈ B, x b ∈ B) :
    ((L ⊓ centSec A B).subgroupOf L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnL, hnc⟩ := hn
  have hgL : (g : MulAut W) ∈ L := g.2
  refine ⟨L.mul_mem (L.mul_mem hgL hnL) (L.inv_mem hgL),
    le_stabSub_of_inv hA (L.mul_mem (L.mul_mem hgL hnL) (L.inv_mem hgL)), fun a ha => ?_⟩
  have hg' : (g : MulAut W)⁻¹ a ∈ A := hA _ (L.inv_mem hgL) a ha
  have h1 := hnc.2 _ hg'
  have h2 : (↑(g * n * g⁻¹) : MulAut W) a * a⁻¹ = (g : MulAut W) ((n : MulAut W) ((g : MulAut W)⁻¹ a) *
      ((g : MulAut W)⁻¹ a)⁻¹) := by
    simp [MulAut.mul_apply, map_mul, map_inv]
  rw [h2]
  exact hB _ hgL _ h1

variable [Finite W]

theorem commutator_mem_of_sec_small {L : Subgroup (MulAut W)} [IsSimpleGroup ↥L]
    (hL : 24 < Nat.card ↥L) {A B : Subgroup W} (hA : ∀ x ∈ L, ∀ a ∈ A, x a ∈ A)
    (hB : ∀ x ∈ L, ∀ b ∈ B, x b ∈ B) (hs : Nat.card (↥A ⧸ B.subgroupOf A) ≤ 4) :
    ∀ x ∈ L, ∀ a ∈ A, x a * a⁻¹ ∈ B := by
  have hmul := card_autSec_mul (le_stabSub_of_inv hA) (le_stabSub_of_inv hB)
  have hnorm := normal_inf_centSec hA hB
  have hbound : Nat.card (autSec L A B) ≤ 24 := by
    have h1 : Nat.card (autSec L A B) ≤ Nat.card (MulAut (↥A ⧸ B.subgroupOf A)) :=
      Subgroup.card_le_card_group _
    have h2 := card_mulAut_le_factorial (↥A ⧸ B.subgroupOf A)
    have h3 : (Nat.card (↥A ⧸ B.subgroupOf A)).factorial ≤ (4 : ℕ).factorial :=
      Nat.factorial_le hs
    have h4 : (4 : ℕ).factorial = 24 := by decide
    omega
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ centSec A B).subgroupOf L) with hbot | htop
  · exfalso
    have hK : L ⊓ centSec A B = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have : (⟨g, hg.1⟩ : ↥L) ∈ (L ⊓ centSec A B).subgroupOf L := hg
      rw [hbot, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    rw [hK, Subgroup.card_bot, mul_one] at hmul
    omega
  · intro x hx a ha
    have : (⟨x, hx⟩ : ↥L) ∈ (L ⊓ centSec A B).subgroupOf L := by rw [htop]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).2.2 a ha

end Sec4

section Rank3

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem rank3_inj {L : Subgroup (MulAut W)} (hL : IsPSL 3 2 1 ↥L) {V : Subgroup W}
    (hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V) (hnt : ∃ x ∈ L, ∃ v ∈ V, x v ≠ v) :
    ∀ a ∈ L, (∀ v ∈ V, a v = v) → a = 1 := by
  have : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hL).2
  have hnorm : ((L ⊓ centSub V).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnL, hnc⟩ := hn
    have hgL : (g : MulAut W) ∈ L := g.2
    refine ⟨L.mul_mem (L.mul_mem hgL hnL) (L.inv_mem hgL), fun v hv => ?_⟩
    have hg' : (g : MulAut W)⁻¹ v ∈ V := hinv _ (L.inv_mem hgL) v hv
    have h1 : (n : MulAut W) ((g : MulAut W)⁻¹ v) = (g : MulAut W)⁻¹ v := hnc _ hg'
    show (g : MulAut W) ((n : MulAut W) ((g : MulAut W)⁻¹ v)) = v
    rw [h1]
    exact mulAut_apply_inv_apply _ _
  intro a ha hav
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ centSub V).subgroupOf L) with hbot | htop
  · have : (⟨a, ha⟩ : ↥L) ∈ (L ⊓ centSub V).subgroupOf L := Subgroup.mem_subgroupOf.mpr ⟨ha, hav⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · exfalso
    obtain ⟨x, hx, v, hv, hxv⟩ := hnt
    have : (⟨x, hx⟩ : ↥L) ∈ (L ⊓ centSub V).subgroupOf L := by rw [htop]; exact Subgroup.mem_top _
    exact hxv ((Subgroup.mem_subgroupOf.mp this).2 v hv)

theorem card_eq_168_of_isPSL_three_two {L : Type} [Group L] (hL : IsPSL 3 2 1 L) : Nat.card L = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two hL

theorem rank3_surj (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hL : IsPSL 3 2 1 ↥L)
    {V : Subgroup W} (hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V) (hcard : Nat.card ↥V = 8)
    (hnt : ∃ x ∈ L, ∃ v ∈ V, x v ≠ v) : autSub L V = ⊤ := by
  have hLs : L ≤ stabSub V := le_stabSub_of_inv hinv
  have hinj := rank3_inj hL hinv hnt
  have h1 := card_autSub_mul hLs
  have hK : L ⊓ centSub V = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    exact Subgroup.mem_bot.2 (hinj a ha.1 ha.2)
  rw [hK, Subgroup.card_bot, mul_one] at h1
  have hL168 := card_eq_168_of_isPSL_three_two hL
  have hAut : Nat.card (MulAut ↥V) = 168 :=
    card_mulAut_of_card_eight (fun a b => mul_comm a b)
      (fun a => Subtype.ext (by simpa using hW2 (a : W))) hcard
  exact Subgroup.eq_top_of_card_eq _ (by rw [h1, hL168, hAut])

theorem inner_of_stable_card_eight (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL : IsPSL 3 2 1 ↥L) {V : Subgroup W} (hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V)
    (hcard : Nat.card ↥V = 8) (hnt : ∃ x ∈ L, ∃ v ∈ V, x v ≠ v) {σ : MulAut W}
    (hσL : ∀ x ∈ L, σ * x * σ⁻¹ ∈ L) (hσV : σ ∈ stabSub V) :
    ∃ l₀ ∈ L, ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹) := by
  have htop := rank3_surj hW2 hL hinv hcard hnt
  have hinj := rank3_inj hL hinv hnt
  have hmem : resHom V ⟨σ, hσV⟩ ∈ autSub L V := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨g, hgL, hg⟩ := mem_autSub.mp hmem
  have hl : ∀ v ∈ V, (g : MulAut W) v = σ v := fun v hv => by
    have := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : W)) hg
    exact this
  have hσinv : ∀ v ∈ V, σ⁻¹ v ∈ V := fun v hv => ((stabSub V).inv_mem hσV v).2 hv
  have hkey : ∀ y ∈ L, σ * y * σ⁻¹ = (g : MulAut W) * y * (g : MulAut W)⁻¹ := by
    intro y hy
    have h1 : σ * y * σ⁻¹ ∈ L := hσL y hy
    have h2 : (g : MulAut W) * y * (g : MulAut W)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem hgL hy) (L.inv_mem hgL)
    have hagree : ∀ v ∈ V, (σ * y * σ⁻¹) v = ((g : MulAut W) * y * (g : MulAut W)⁻¹) v := by
      intro v hv
      have hu : σ⁻¹ v ∈ V := hσinv v hv
      have hgu : (g : MulAut W) (σ⁻¹ v) = v := by
        rw [hl _ hu]
        exact mulAut_apply_inv_apply _ _
      have hgv : (g : MulAut W)⁻¹ v = σ⁻¹ v := by
        calc (g : MulAut W)⁻¹ v = (g : MulAut W)⁻¹ ((g : MulAut W) (σ⁻¹ v)) := by rw [hgu]
          _ = σ⁻¹ v := mulAut_inv_apply_apply _ _
      have hyu : y (σ⁻¹ v) ∈ V := hinv y hy _ hu
      have : σ (y (σ⁻¹ v)) = (g : MulAut W) (y (σ⁻¹ v)) := (hl _ hyu).symm
      show σ (y (σ⁻¹ v)) = (g : MulAut W) (y ((g : MulAut W)⁻¹ v))
      rw [hgv]
      exact this
    have h3 : (σ * y * σ⁻¹) * ((g : MulAut W) * y * (g : MulAut W)⁻¹)⁻¹ ∈ L :=
      L.mul_mem h1 (L.inv_mem h2)
    have h4 := hinj _ h3 (fun v hv => by
      have hv' : ((g : MulAut W) * y * (g : MulAut W)⁻¹)⁻¹ v ∈ V :=
        hinv _ (L.inv_mem h2) v hv
      show (σ * y * σ⁻¹) (((g : MulAut W) * y * (g : MulAut W)⁻¹)⁻¹ v) = v
      rw [hagree _ hv']
      exact mulAut_apply_inv_apply ((g : MulAut W) * y * (g : MulAut W)⁻¹) v)
    exact mul_inv_eq_one.mp h4
  refine ⟨g, hgL, fun x hx => ?_⟩
  have hy : (g : MulAut W)⁻¹ * x * (g : MulAut W) ∈ L :=
    L.mul_mem (L.mul_mem (L.inv_mem hgL) hx) hgL
  have h := hkey _ hy
  have e1 : (g : MulAut W) * ((g : MulAut W)⁻¹ * x * (g : MulAut W)) * (g : MulAut W)⁻¹ = x := by
    group
  rw [e1] at h
  calc (σ * (g : MulAut W)⁻¹) * x
      = σ * ((g : MulAut W)⁻¹ * x * (g : MulAut W)) * (g : MulAut W)⁻¹ := by group
    _ = (σ * ((g : MulAut W)⁻¹ * x * (g : MulAut W)) * σ⁻¹) * (σ * (g : MulAut W)⁻¹) := by group
    _ = x * (σ * (g : MulAut W)⁻¹) := by rw [h]

theorem rank3_irr {L : Subgroup (MulAut W)} (hL : IsPSL 3 2 1 ↥L) {V : Subgroup W}
    (hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V) (hcard : Nat.card ↥V = 8)
    (hcomm : XMod.commOf ↥L V = V) :
    ∀ J : Subgroup W, J ≤ V → (∀ x ∈ L, ∀ j ∈ J, x j ∈ J) → J = ⊥ ∨ J = V := by
  have : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hL).2
  have hL24 : 24 < Nat.card ↥L := by have := card_eq_168_of_isPSL_three_two hL; omega
  intro J hJV hJinv
  by_contra hcon
  push Not at hcon
  obtain ⟨hJ1, hJ2⟩ := hcon
  have hdvd : Nat.card ↥J ∣ 8 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hJV
  have hJpos : 0 < Nat.card ↥J := Nat.card_pos
  have hcJ : Nat.card ↥J = 2 ∨ Nat.card ↥J = 4 := by
    have hle : Nat.card ↥J ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    have h1 : Nat.card ↥J ≠ 1 := fun h => hJ1 (Subgroup.card_eq_one.mp h)
    have h8 : Nat.card ↥J ≠ 8 := fun h =>
      hJ2 (Subgroup.eq_of_le_of_card_ge hJV (by rw [h, hcard]))
    interval_cases hc : Nat.card ↥J <;> simp_all
  have hsec : Nat.card (↥V ⧸ J.subgroupOf V) ≤ 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (J.subgroupOf V)
    have h2 : Nat.card ↥(J.subgroupOf V) = Nat.card ↥J :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJV).toEquiv
    rw [h2, hcard] at h1
    rcases hcJ with h | h <;> rw [h] at h1 <;> omega
  have hcomm' := commutator_mem_of_sec_small hL24 hinv hJinv hsec
  have hle : XMod.commOf ↥L V ≤ J := by
    rw [XMod.commOf_le_iff]
    intro a l hl
    exact hcomm' a a.2 l hl
  rw [hcomm] at hle
  exact hJ2 (le_antisymm hJV hle)

end Rank3

end CFSG.Quasithin
