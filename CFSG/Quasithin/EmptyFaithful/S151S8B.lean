module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.Quasithin.EmptyFaithful.S151S5A
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.S151S8

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.GammaExtra

variable {G : Type} [Group G] {X Y : Subgroup G}

theorem mem_sup_comm (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {g : G} (hg : g ∈ X ⊔ Y) :
    ∃ x ∈ X, ∃ y ∈ Y, g = x * y := by
  have hY : Y ≤ Subgroup.centralizer (X : Set G) := fun y hy =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx y hy
  exact S151S5.mem_mul_of_le_normalizer (A := X) (B := Y)
    (hY.trans (Subgroup.centralizer_le_normalizer _)) hg

theorem card_sup_of_comm [Finite G] {E F : Subgroup G} (hc : ∀ x ∈ E, ∀ y ∈ F, x * y = y * x)
    (hEF : E ⊓ F = ⊥) : Nat.card ↥(E ⊔ F) = Nat.card ↥E * Nat.card ↥F := by
  have hbij : Function.Bijective (fun p : ↥E × ↥F =>
      (⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(E ⊔ F))) := by
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
      have h1 : a * b = a' * b' := congrArg Subtype.val h
      have h2 : a'⁻¹ * a = b' * b⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
          _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h1]
          _ = b' * b⁻¹ := by group
      have hmemE : a'⁻¹ * a ∈ E := E.mul_mem (E.inv_mem ha') ha
      have hmemF : b' * b⁻¹ ∈ F := F.mul_mem hb' (F.inv_mem hb)
      have hbot : a'⁻¹ * a ∈ E ⊓ F := ⟨hmemE, h2 ▸ hmemF⟩
      rw [hEF, Subgroup.mem_bot, inv_mul_eq_one] at hbot
      have hbb : b = b' := by
        rw [← hbot] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext hbot.symm) (Subtype.ext hbb)
    · rintro ⟨g, hg⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup_comm hc hg
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij).symm, Nat.card_prod]

theorem isElemAbelian_sup_of_comm {E F : Subgroup G} (hE : IsElemAbelian 2 E)
    (hF : IsElemAbelian 2 F) (hc : ∀ x ∈ E, ∀ y ∈ F, x * y = y * x) : IsElemAbelian 2 (E ⊔ F) :=
  CFSG.Open.IsElemAbelian.sup_of_commute hE hF hc

@[expose] def part (X Y A : Subgroup G) : Subgroup G := X ⊓ (A ⊔ Y)

theorem mem_part_iff (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {A : Subgroup G} (hA : A ≤ X ⊔ Y)
    {x : G} : x ∈ part X Y A ↔ x ∈ X ∧ ∃ y ∈ Y, x * y ∈ A := by
  constructor
  · rintro ⟨hxX, hxAY⟩
    refine ⟨hxX, ?_⟩
    have hXY : X ≤ Subgroup.normalizer (Y : Set G) := fun x' hx' =>
      Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun y hy => (hc x' hx' y hy).symm)
    have hAN : A ≤ Subgroup.normalizer (Y : Set G) :=
      hA.trans (sup_le hXY (fun y hy => Subgroup.le_normalizer hy))
    obtain ⟨y, hy, a, ha, hxya⟩ := S151S5.mem_mul_of_le_normalizer (A := Y) (B := A) hAN
      (by rwa [sup_comm] at hxAY)
    refine ⟨y⁻¹, Y.inv_mem hy, ?_⟩
    have h1 : x * y⁻¹ = y⁻¹ * x := hc x hxX y⁻¹ (Y.inv_mem hy)
    have h2 : y⁻¹ * x = a := by rw [hxya]; group
    rw [h1, h2]
    exact ha
  · rintro ⟨hxX, y, hy, hxy⟩
    refine ⟨hxX, ?_⟩
    have := Subgroup.mul_mem_sup hxy (Y.inv_mem hy)
    simpa using this

theorem part_le_left (A : Subgroup G) : part X Y A ≤ X := inf_le_left

theorem isElemAbelian_part (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hbot : X ⊓ Y = ⊥)
    {A : Subgroup G} (hA : A ≤ X ⊔ Y) (hAe : IsElemAbelian 2 A) :
    IsElemAbelian 2 (part X Y A) := by
  have hAc := isMulCommutative_iff_forall.mp hAe.1
  refine ⟨isMulCommutative_iff_forall.mpr ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨haX, y, hy, hay⟩ := (mem_part_iff hc hA).mp ha
    obtain ⟨hbX, y', hy', hby⟩ := (mem_part_iff hc hA).mp hb
    have h1 := hAc _ hay _ hby
    have e1 : a * y * (b * y') = a * b * (y * y') := by
      calc a * y * (b * y') = a * (y * b) * y' := by group
        _ = a * (b * y) * y' := by rw [← hc b hbX y hy]
        _ = a * b * (y * y') := by group
    have e2 : b * y' * (a * y) = b * a * (y' * y) := by
      calc b * y' * (a * y) = b * (y' * a) * y := by group
        _ = b * (a * y') * y := by rw [← hc a haX y' hy']
        _ = b * a * (y' * y) := by group
    have h2 : a * b * (y * y') = b * a * (y' * y) := by rw [← e1, ← e2]; exact h1
    have h3 : (b * a)⁻¹ * (a * b) = (y' * y) * (y * y')⁻¹ := by
      calc (b * a)⁻¹ * (a * b) = (b * a)⁻¹ * (a * b * (y * y')) * (y * y')⁻¹ := by group
        _ = (b * a)⁻¹ * (b * a * (y' * y)) * (y * y')⁻¹ := by rw [h2]
        _ = (y' * y) * (y * y')⁻¹ := by group
    have hX : (b * a)⁻¹ * (a * b) ∈ X := X.mul_mem (X.inv_mem (X.mul_mem hbX haX)) (X.mul_mem haX hbX)
    have hY : (y' * y) * (y * y')⁻¹ ∈ Y :=
      Y.mul_mem (Y.mul_mem hy' hy) (Y.inv_mem (Y.mul_mem hy hy'))
    have hmem : (b * a)⁻¹ * (a * b) ∈ X ⊓ Y := ⟨hX, h3 ▸ hY⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm
  · intro a ha
    obtain ⟨haX, y, hy, hay⟩ := (mem_part_iff hc hA).mp ha
    have h1 : (a * y) ^ 2 = 1 := hAe.2 _ hay
    rw [Commute.mul_pow (hc a haX y hy)] at h1
    have h2 : a ^ 2 = (y ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hmem : a ^ 2 ∈ X ⊓ Y := ⟨X.pow_mem haX 2, h2 ▸ Y.inv_mem (Y.pow_mem hy 2)⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem

theorem le_part_sup (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {A : Subgroup G} (hA : A ≤ X ⊔ Y) :
    A ≤ part X Y A ⊔ part Y X A := by
  intro a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup_comm hc (hA ha)
  have hc' : ∀ y ∈ Y, ∀ x ∈ X, y * x = x * y := fun y hy x hx => (hc x hx y hy).symm
  have hA' : A ≤ Y ⊔ X := by rwa [sup_comm] at hA
  refine Subgroup.mul_mem_sup ((mem_part_iff hc hA).mpr ⟨hx, y, hy, ha⟩)
    ((mem_part_iff hc' hA').mpr ⟨hy, x, hx, ?_⟩)
  rw [hc' y hy x hx]
  exact ha

theorem part_le_of_split (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hbot : X ⊓ Y = ⊥)
    {S : Subgroup G} (hsplit : S ≤ (S ⊓ X) ⊔ (S ⊓ Y)) {A : Subgroup G} (hAS : A ≤ S) :
    part X Y A ≤ S ⊓ X := by
  have hSXY : S ≤ X ⊔ Y := hsplit.trans (sup_le_sup inf_le_right inf_le_right)
  intro x hx
  obtain ⟨hxX, y, hy, hxyA⟩ := (mem_part_iff hc (hAS.trans hSXY)).mp hx
  have hc2 : ∀ u ∈ S ⊓ X, ∀ v ∈ S ⊓ Y, u * v = v * u := fun u hu v hv => hc u hu.2 v hv.2
  obtain ⟨s₁, hs₁, s₂, hs₂, hxy⟩ := mem_sup_comm hc2 (hsplit (hAS hxyA))
  have h1 : s₁⁻¹ * x = s₂ * y⁻¹ := by
    calc s₁⁻¹ * x = s₁⁻¹ * (x * y) * y⁻¹ := by group
      _ = s₁⁻¹ * (s₁ * s₂) * y⁻¹ := by rw [hxy]
      _ = s₂ * y⁻¹ := by group
  have hX : s₁⁻¹ * x ∈ X := X.mul_mem (X.inv_mem hs₁.2) hxX
  have hY : s₂ * y⁻¹ ∈ Y := Y.mul_mem hs₂.2 (Y.inv_mem hy)
  have hmem : s₁⁻¹ * x ∈ X ⊓ Y := ⟨hX, h1 ▸ hY⟩
  rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  rw [← hmem]
  exact hs₁

section Thompson

variable [Finite G]

theorem isMaxElemAbelian_part (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hbot : X ⊓ Y = ⊥)
    {S : Subgroup G} (hsplit : S ≤ (S ⊓ X) ⊔ (S ⊓ Y)) {A : Subgroup G}
    (hA : IsMaxElemAbelian S A) :
    A = part X Y A ⊔ part Y X A ∧ IsMaxElemAbelian (S ⊓ X) (part X Y A) := by
  have hSXY : S ≤ X ⊔ Y := hsplit.trans (sup_le_sup inf_le_right inf_le_right)
  have hAXY : A ≤ X ⊔ Y := hA.1.trans hSXY
  have hc' : ∀ y ∈ Y, ∀ x ∈ X, y * x = x * y := fun y hy x hx => (hc x hx y hy).symm
  have hbot' : Y ⊓ X = ⊥ := by rw [inf_comm]; exact hbot
  have hsplit' : S ≤ (S ⊓ Y) ⊔ (S ⊓ X) := by rwa [sup_comm] at hsplit
  have hAYX : A ≤ Y ⊔ X := by rwa [sup_comm] at hAXY
  have hPXS : part X Y A ≤ S ⊓ X := part_le_of_split hc hbot hsplit hA.1
  have hPYS : part Y X A ≤ S ⊓ Y := part_le_of_split hc' hbot' hsplit' hA.1
  have hPXe : IsElemAbelian 2 (part X Y A) := isElemAbelian_part hc hbot hAXY hA.2.1
  have hPYe : IsElemAbelian 2 (part Y X A) := isElemAbelian_part hc' hbot' hAYX hA.2.1
  have hcP : ∀ x ∈ part X Y A, ∀ y ∈ part Y X A, x * y = y * x := fun x hx y hy =>
    hc x (part_le_left _ hx) y (part_le_left _ hy)
  have hPbot : part X Y A ⊓ part Y X A = ⊥ := by
    rw [eq_bot_iff, ← hbot]
    exact inf_le_inf (part_le_left _) (part_le_left _)
  have hAle : A ≤ part X Y A ⊔ part Y X A := le_part_sup hc hAXY
  have hBe : IsElemAbelian 2 (part X Y A ⊔ part Y X A) := isElemAbelian_sup_of_comm hPXe hPYe hcP
  have hBS : part X Y A ⊔ part Y X A ≤ S :=
    sup_le (hPXS.trans inf_le_left) (hPYS.trans inf_le_left)
  have hBcard : Nat.card ↥(part X Y A ⊔ part Y X A) ≤ Nat.card ↥A := hA.2.2 _ hBS hBe
  have hAB : A = part X Y A ⊔ part Y X A := Subgroup.eq_of_le_of_card_ge hAle hBcard
  have hAcard : Nat.card ↥A = Nat.card ↥(part X Y A) * Nat.card ↥(part Y X A) := by
    have h := card_sup_of_comm hcP hPbot
    rw [← hAB] at h
    exact h
  refine ⟨hAB, hPXS, hPXe, fun E hES hE => ?_⟩
  by_contra hlt
  have hlt' : Nat.card ↥(part X Y A) < Nat.card ↥E := not_le.mp hlt
  have hEX : E ≤ X := hES.trans inf_le_right
  have hcEF : ∀ x ∈ E, ∀ y ∈ part Y X A, x * y = y * x := fun x hx y hy =>
    hc x (hEX hx) y (part_le_left _ hy)
  have hEPbot : E ⊓ part Y X A = ⊥ := by
    rw [eq_bot_iff, ← hbot]
    exact inf_le_inf hEX (part_le_left _)
  have hFe : IsElemAbelian 2 (E ⊔ part Y X A) := isElemAbelian_sup_of_comm hE hPYe hcEF
  have hFS : E ⊔ part Y X A ≤ S := sup_le (hES.trans inf_le_left) (hPYS.trans inf_le_left)
  have hFcard : Nat.card ↥(E ⊔ part Y X A) ≤ Nat.card ↥A := hA.2.2 _ hFS hFe
  rw [card_sup_of_comm hcEF hEPbot] at hFcard
  have hpos : 0 < Nat.card ↥(part Y X A) := Nat.card_pos
  have hmul : Nat.card ↥(part X Y A) * Nat.card ↥(part Y X A) <
      Nat.card ↥E * Nat.card ↥(part Y X A) := Nat.mul_lt_mul_of_pos_right hlt' hpos
  exact absurd (hFcard.trans_eq hAcard) (not_le.mpr hmul)

theorem thompsonJ_le_of_split (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hbot : X ⊓ Y = ⊥)
    {S : Subgroup G} (hsplit : S ≤ (S ⊓ X) ⊔ (S ⊓ Y)) : thompsonJ (S ⊓ X) ≤ thompsonJ S := by
  have hSXY : S ≤ X ⊔ Y := hsplit.trans (sup_le_sup inf_le_right inf_le_right)
  have hc' : ∀ y ∈ Y, ∀ x ∈ X, y * x = x * y := fun y hy x hx => (hc x hx y hy).symm
  have hbot' : Y ⊓ X = ⊥ := by rw [inf_comm]; exact hbot
  have hsplit' : S ≤ (S ⊓ Y) ⊔ (S ⊓ X) := by rwa [sup_comm] at hsplit
  refine thompsonJ_le fun E hE => ?_
  obtain ⟨F, hF⟩ := exists_isMaxElemAbelian (S ⊓ Y)
  have hEX : E ≤ X := hE.1.trans inf_le_right
  have hFY : F ≤ Y := hF.1.trans inf_le_right
  have hcEF : ∀ x ∈ E, ∀ y ∈ F, x * y = y * x := fun x hx y hy => hc x (hEX hx) y (hFY hy)
  have hEFbot : E ⊓ F = ⊥ := by
    rw [eq_bot_iff, ← hbot]
    exact inf_le_inf hEX hFY
  have hAmax : IsMaxElemAbelian S (E ⊔ F) := by
    refine ⟨sup_le (hE.1.trans inf_le_left) (hF.1.trans inf_le_left),
      isElemAbelian_sup_of_comm hE.2.1 hF.2.1 hcEF, fun B hBS hBe => ?_⟩
    have hBXY : B ≤ X ⊔ Y := hBS.trans hSXY
    have hBYX : B ≤ Y ⊔ X := by rwa [sup_comm] at hBXY
    have hPX := part_le_of_split hc hbot hsplit hBS
    have hPY := part_le_of_split hc' hbot' hsplit' hBS
    have hPXe := isElemAbelian_part hc hbot hBXY hBe
    have hPYe := isElemAbelian_part hc' hbot' hBYX hBe
    have h1 : Nat.card ↥(part X Y B) ≤ Nat.card ↥E := hE.2.2 _ hPX hPXe
    have h2 : Nat.card ↥(part Y X B) ≤ Nat.card ↥F := hF.2.2 _ hPY hPYe
    have hcP : ∀ x ∈ part X Y B, ∀ y ∈ part Y X B, x * y = y * x := fun x hx y hy =>
      hc x (part_le_left _ hx) y (part_le_left _ hy)
    have hPbot : part X Y B ⊓ part Y X B = ⊥ := by
      rw [eq_bot_iff, ← hbot]
      exact inf_le_inf (part_le_left _) (part_le_left _)
    calc Nat.card ↥B ≤ Nat.card ↥(part X Y B ⊔ part Y X B) :=
          Subgroup.card_le_of_le (le_part_sup hc hBXY)
      _ = Nat.card ↥(part X Y B) * Nat.card ↥(part Y X B) := card_sup_of_comm hcP hPbot
      _ ≤ Nat.card ↥E * Nat.card ↥F := Nat.mul_le_mul h1 h2
      _ = Nat.card ↥(E ⊔ F) := (card_sup_of_comm hcEF hEFbot).symm
  exact (le_sup_left : E ≤ E ⊔ F).trans (le_thompsonJ hAmax)

theorem thompsonJ_inf_le (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hbot : X ⊓ Y = ⊥)
    {S : Subgroup G} (hsplit : S ≤ (S ⊓ X) ⊔ (S ⊓ Y)) :
    thompsonJ S ⊓ X ≤ thompsonJ (S ⊓ X) := by
  have hJ : thompsonJ S ≤ thompsonJ (S ⊓ X) ⊔ Y := by
    refine thompsonJ_le fun A hA => ?_
    obtain ⟨hAB, hAmax⟩ := isMaxElemAbelian_part hc hbot hsplit hA
    calc A = part X Y A ⊔ part Y X A := hAB
      _ ≤ thompsonJ (S ⊓ X) ⊔ Y := sup_le_sup (le_thompsonJ hAmax) (part_le_left _)
  rintro x ⟨hxJ, hxX⟩
  have hJX : thompsonJ (S ⊓ X) ≤ X := (thompsonJ_le_self (S ⊓ X)).trans inf_le_right
  obtain ⟨u, hu, y, hy, rfl⟩ := mem_sup_comm (X := thompsonJ (S ⊓ X)) (Y := Y)
    (fun u hu y hy => hc u (hJX hu) y hy) (hJ hxJ)
  have hyX : y ∈ X := by
    have := X.mul_mem (X.inv_mem (hJX hu)) hxX
    simpa using this
  have hy1 : y ∈ X ⊓ Y := ⟨hyX, hy⟩
  rw [hbot, Subgroup.mem_bot] at hy1
  rw [hy1, mul_one]
  exact hu

theorem thompsonJ_inf_eq (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hbot : X ⊓ Y = ⊥)
    {S : Subgroup G} (hsplit : S ≤ (S ⊓ X) ⊔ (S ⊓ Y)) :
    thompsonJ S ⊓ X = thompsonJ (S ⊓ X) :=
  le_antisymm (thompsonJ_inf_le hc hbot hsplit)
    (le_inf (thompsonJ_le_of_split hc hbot hsplit)
      ((thompsonJ_le_self (S ⊓ X)).trans inf_le_right))

end Thompson

end CFSG.Quasithin.S151S8
