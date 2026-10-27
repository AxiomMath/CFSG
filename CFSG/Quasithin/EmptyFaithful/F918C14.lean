module

public import CFSG.Quasithin.EmptyFaithful.F918C13
public import CFSG.Quasithin.Background.F918P2
public import CFSG.Quasithin.Background.F918C2

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

section Conj

variable {W : Type} [CommGroup W]

theorem exists_act_eq_of_mem_sup {L L' : Subgroup (MulAut W)} {V : Subgroup W}
    (hV : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V) (hL' : ∀ y ∈ L', ∀ v ∈ V, y v = v) :
    ∀ a ∈ L ⊔ L', ∃ b ∈ L, ∀ v ∈ V, a v = b v := by
  intro a ha
  rw [Subgroup.sup_eq_closure] at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, fun v _ => rfl⟩
    · exact ⟨1, L.one_mem, fun v hv => by simpa using hL' x hx v hv⟩
  | one => exact ⟨1, L.one_mem, fun v _ => rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨b₁, hb₁, h₁⟩ := hx
    obtain ⟨b₂, hb₂, h₂⟩ := hy
    refine ⟨b₁ * b₂, L.mul_mem hb₁ hb₂, fun v hv => ?_⟩
    show x (y v) = b₁ (b₂ v)
    rw [h₂ v hv, h₁ _ (hV b₂ hb₂ v hv)]
  | inv x _ hx =>
    obtain ⟨b, hb, h⟩ := hx
    refine ⟨b⁻¹, L.inv_mem hb, fun v hv => ?_⟩
    have hv' : b⁻¹ v ∈ V := hV b⁻¹ (L.inv_mem hb) v hv
    have h2 : x (b⁻¹ v) = v := by
      rw [h _ hv']
      exact mulAut_apply_inv_apply b v
    calc x⁻¹ v = x⁻¹ (x (b⁻¹ v)) := by rw [h2]
      _ = b⁻¹ v := mulAut_inv_apply_apply x _

theorem commOf_eq_of_trivial {L L' : Subgroup (MulAut W)} {V : Subgroup W}
    (hV : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V) (hL' : ∀ y ∈ L', ∀ v ∈ V, y v = v)
    (hcomm : XMod.commOf ↥(L ⊔ L') V = V) : XMod.commOf ↥L V = V := by
  refine le_antisymm (XMod.commOf_le_of_isInv (fun a v hv => hV a a.2 v hv)) ?_
  calc V = XMod.commOf ↥(L ⊔ L') V := hcomm.symm
    _ ≤ XMod.commOf ↥L V := by
      rw [XMod.commOf_le_iff]
      intro a l hl
      obtain ⟨b, hb, h⟩ := exists_act_eq_of_mem_sup hV hL' a a.2
      have h1 : (a • l) * l⁻¹ = ((⟨b, hb⟩ : ↥L) • l) * l⁻¹ := by
        show (a : MulAut W) l * l⁻¹ = b l * l⁻¹
        rw [h l hl]
      rw [h1]
      exact XMod.mem_commOf_of_mem _ hl

theorem map_commV_conj (c : MulAut W) (L : Subgroup (MulAut W)) :
    (commV L).map c.toMonoidHom = commV (conjAutSub c L) :=
  (CFSG.Quasithin.commV_map_conj_eq L c).symm

theorem map_fixV_conj (c : MulAut W) (L : Subgroup (MulAut W)) :
    (fixV L).map c.toMonoidHom = fixV (conjAutSub c L) :=
  (CFSG.Quasithin.fixV_map_conj_eq L c).symm

theorem map_inv_map (c : MulAut W) (J : Subgroup W) :
    (J.map c⁻¹.toMonoidHom).map c.toMonoidHom = J := by
  ext x
  constructor
  · rintro ⟨y, ⟨j, hj, rfl⟩, rfl⟩
    show c (c⁻¹ j) ∈ J
    rw [mulAut_apply_inv_apply]
    exact hj
  · intro hx
    exact ⟨c⁻¹ x, ⟨x, hx, rfl⟩, mulAut_apply_inv_apply c x⟩

theorem isIrr_map_conj (c : MulAut W) {L : Subgroup (MulAut W)} {J : Subgroup W}
    (h : XMod.IsIrr ↥L J) : XMod.IsIrr ↥(conjAutSub c L) (J.map c.toMonoidHom) := by
  obtain ⟨hinv, hlt, hirr⟩ := h
  have hback : ∀ x ∈ L, ∀ y : MulAut W, y = c * x * c⁻¹ → y ∈ conjAutSub c L := by
    rintro x hx y rfl
    rw [mem_conjAutSub_iff]
    simpa [mul_assoc] using hx
  refine ⟨?_, ?_, ?_⟩
  · intro a w hw
    obtain ⟨j, hj, rfl⟩ := hw
    have ha : c⁻¹ * (a : MulAut W) * c ∈ L := mem_conjAutSub_iff.mp a.2
    refine ⟨((⟨c⁻¹ * (a : MulAut W) * c, ha⟩ : ↥L) • j), hinv _ j hj, ?_⟩
    show c ((c⁻¹ * (a : MulAut W) * c) j) = (a : MulAut W) (c j)
    show c (c⁻¹ ((a : MulAut W) (c j))) = (a : MulAut W) (c j)
    exact mulAut_apply_inv_apply c _
  · have hne : J ≠ ⊥ := bot_lt_iff_ne_bot.mp hlt
    refine bot_lt_iff_ne_bot.mpr fun hb => hne ?_
    rw [Subgroup.map_eq_bot_iff] at hb
    rw [eq_bot_iff]
    intro x hx
    have := hb hx
    rw [MonoidHom.mem_ker] at this
    exact Subgroup.mem_bot.2 (c.injective (by simpa using this))
  · intro J' hJ'inv hbot hJ'le
    have hle : J'.map c⁻¹.toMonoidHom ≤ J := by
      intro y hy
      obtain ⟨j', hj', rfl⟩ := hy
      obtain ⟨j, hj, hjj⟩ := hJ'le hj'
      have : c⁻¹ j' = j := by
        rw [← hjj]
        exact mulAut_inv_apply_apply c j
      show c⁻¹ j' ∈ J
      rw [this]
      exact hj
    have hinv' : XMod.IsInv ↥L (J'.map c⁻¹.toMonoidHom) := by
      intro a y hy
      obtain ⟨j', hj', rfl⟩ := hy
      refine ⟨(c * (a : MulAut W) * c⁻¹) j', hJ'inv ⟨c * (a : MulAut W) * c⁻¹, hback _ a.2 _ rfl⟩ j' hj', ?_⟩
      show c⁻¹ (c ((a : MulAut W) (c⁻¹ j'))) = (a : MulAut W) (c⁻¹ j')
      exact mulAut_inv_apply_apply c _
    rcases hirr _ hinv' bot_le hle with h1 | h1
    · left
      rw [← map_inv_map c J', h1, Subgroup.map_bot]
    · right
      rw [← map_inv_map c J', h1]

theorem isIrr_map {L : Subgroup (MulAut W)} {σ : MulAut W}
    (hσ : σ ∈ Subgroup.normalizer (L : Set (MulAut W))) {J : Subgroup W} (h : XMod.IsIrr ↥L J) :
    XMod.IsIrr ↥L (J.map σ.toMonoidHom) := by
  have h1 : conjAutSub σ L = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hσ
  have := isIrr_map_conj σ h
  rw [h1] at this
  exact this

theorem map_commV_eq_of_normalizes {L : Subgroup (MulAut W)} {σ : MulAut W}
    (hσ : σ ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    (commV L).map σ.toMonoidHom = commV L := by
  have h1 : conjAutSub σ L = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hσ
  rw [map_commV_conj, h1]

end Conj

section Isotypic

variable {W : Type} [CommGroup W]

theorem inner_of_stable_isotypic {F : Type} [Field F] (hF : Nat.card F = 2) {ι : Type} [Nonempty ι]
    (hW : ∀ v : W, v ^ 2 = 1) {L : Subgroup (MulAut W)} {π : ↥(StatedSL 3 F) →* ↥L}
    (I : ι → Subgroup W) (hreal : ∀ i, (FFModel.nat (StatedSL 3 F)).RealizesVia L (I i) ⊥ π)
    {σ : MulAut W} (hσ : σ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hσX : (⨆ i, I i).map σ.toMonoidHom = ⨆ i, I i) :
    ∃ l₀ ∈ L, ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hhom := (B5.homogeneous_of_nat_copies (by norm_num : 2 ≤ 3) hW I hreal).2
  have hirr : ∀ i, XMod.IsIrr ↥L (I i) := fun i => B5.isIrr_of_realizes (by norm_num) (hreal i)
  have hJ : XMod.IsIrr ↥L ((I i₀).map σ.toMonoidHom) := isIrr_map hσ (hirr i₀)
  have hJX : (I i₀).map σ.toMonoidHom ≤ ⨆ i, I i := by
    rw [← hσX]
    exact Subgroup.map_mono (le_iSup I i₀)
  have hiso := hhom.2 ((I i₀).map σ.toMonoidHom) (I i₀)
    ⟨bot_le, hJX, hJ.1, hJ.2⟩ ⟨bot_le, le_iSup I i₀, (hirr i₀).1, (hirr i₀).2⟩
  have hσL : ∀ x ∈ L, σ * x * σ⁻¹ ∈ L := fun x hx => (Subgroup.mem_normalizer_iff.1 hσ x).1 hx
  exact exists_inner_of_twist_sl3 hF (hreal i₀) hσL rfl (Subgroup.map_bot _).symm hiso

end Isotypic

end CFSG.Quasithin
