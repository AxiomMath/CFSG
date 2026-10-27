module

public import CFSG.Quasithin.Background.B3Sec
public import CFSG.Quasithin.MS93.S38ECount

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Quasithin.B3

variable {G : Type*} [Group G] {Y : Type*} [CommGroup Y] {ρ : G →* MulAut Y}
  {W N : Subgroup Y} (hW : IsInv ρ W) (hN : IsInv ρ N)

theorem secAct_mk (g : G) (w : ↥W) :
    secAct ρ hW hN g (QuotientGroup.mk w) =
      QuotientGroup.mk (⟨ρ g w, hW g w w.2⟩ : ↥W) := rfl

@[expose] def secPre (J : Subgroup (Sec W N)) : Subgroup Y :=
  (J.comap (QuotientGroup.mk' (N.subgroupOf W))).map W.subtype

theorem mem_secPre {J : Subgroup (Sec W N)} {y : Y} :
    y ∈ secPre J ↔ ∃ h : y ∈ W, (QuotientGroup.mk ⟨y, h⟩ : Sec W N) ∈ J := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨h, hy⟩
    exact ⟨⟨y, h⟩, hy, rfl⟩

theorem secPre_le (J : Subgroup (Sec W N)) : secPre J ≤ W := Subgroup.map_subtype_le _

include hW hN in
theorem sec_irr (hNW : N ≤ W)
    (hirr : ∀ J : Subgroup Y, IsInv ρ J → N ≤ J → J ≤ W → J = N ∨ J = W)
    (J : Subgroup (Sec W N)) (hJ : ∀ g : G, ∀ s ∈ J, secAct ρ hW hN g s ∈ J) :
    J = ⊥ ∨ J = ⊤ := by
  have hNJ : N ≤ secPre J := by
    intro n hn
    rw [mem_secPre]
    refine ⟨hNW hn, ?_⟩
    have : (QuotientGroup.mk (⟨n, hNW hn⟩ : ↥W) : Sec W N) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hn)
    rw [this]
    exact J.one_mem
  have hinv : IsInv ρ (secPre J) := by
    intro g y hy
    rw [mem_secPre] at hy ⊢
    obtain ⟨hyW, hyJ⟩ := hy
    refine ⟨hW g y hyW, ?_⟩
    have := hJ g _ hyJ
    rwa [secAct_mk] at this
  rcases hirr _ hinv hNJ (secPre_le J) with h | h
  · left
    rw [eq_bot_iff]
    intro s hs
    induction s using QuotientGroup.induction_on with
    | H w =>
      have hw : (w : Y) ∈ secPre J := (mem_secPre).mpr ⟨w.2, hs⟩
      rw [h] at hw
      rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hw
  · right
    rw [eq_top_iff]
    intro s _
    induction s using QuotientGroup.induction_on with
    | H w =>
      have hw : (w : Y) ∈ secPre J := by rw [h]; exact w.2
      obtain ⟨_, hwJ⟩ := (mem_secPre).mp hw
      exact hwJ

theorem sec_sq (hY : ∀ y : Y, y ^ 2 = 1) (s : Sec W N) : s ^ 2 = 1 := by
  induction s using QuotientGroup.induction_on with
  | H w =>
    rw [← QuotientGroup.mk_pow]
    have : w ^ 2 = 1 := Subtype.ext (by simpa using hY (w : Y))
    rw [this, QuotientGroup.mk_one]

include hW hN in
theorem secAct_eq_one_iff (g : G) :
    secAct ρ hW hN g = 1 ↔ ∀ w ∈ W, ρ g w * w⁻¹ ∈ N := by
  constructor
  · intro h w hw
    have h1 := congrArg (fun φ : MulAut (Sec W N) => φ (QuotientGroup.mk (⟨w, hw⟩ : ↥W))) h
    simp only [secAct_mk, MulAut.one_apply] at h1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    have h2 := N.inv_mem h1
    simpa [mul_comm] using h2
  · intro h
    ext s
    induction s using QuotientGroup.induction_on with
    | H w =>
      rw [secAct_mk, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h2 := N.inv_mem (h w w.2)
      simpa [mul_comm] using h2

include hW hN in
theorem index_fixV_sec [Finite Y] (hNW : N ≤ W) (B : Subgroup G) :
    (fixV (B.map (secAct ρ hW hN))).index = aI (B.map ρ) W N := by
  have h1 := card_fixV_sec ρ hW hN B
  have hfix : Nat.card {w : Y // w ∈ W ∧ ∀ b ∈ B, ρ b w * w⁻¹ ∈ N} =
      Nat.card (fixRel (B.map ρ) W N) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    simp only [mem_fixRel, Subgroup.mem_map]
    constructor
    · rintro ⟨hw, h⟩
      refine ⟨hw, ?_⟩
      rintro _ ⟨b, hb, rfl⟩
      exact h b hb
    · rintro ⟨hw, h⟩
      exact ⟨hw, fun b hb => h _ ⟨b, hb, rfl⟩⟩
  rw [hfix, inf_eq_left.mpr hNW] at h1
  have h2 := (fixV (B.map (secAct ρ hW hN))).index_mul_card
  have h3 : Nat.card (Sec W N) * Nat.card N = Nat.card W := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf W)
    rw [this, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNW).toEquiv]
  have h4 := (fixRel (B.map ρ) W N).relIndex_mul_card (K := W)
  rw [inf_eq_left.mpr (fixRel_le _ _ _)] at h4
  unfold aI
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hFpos : 0 < Nat.card (fixV (B.map (secAct ρ hW hN))) := Nat.card_pos
  have key : (fixV (B.map (secAct ρ hW hN))).index *
      (Nat.card (fixV (B.map (secAct ρ hW hN))) * Nat.card N) =
      (fixRel (B.map ρ) W N).relIndex W * (Nat.card (fixV (B.map (secAct ρ hW hN))) *
        Nat.card N) := by
    calc _ = (fixV (B.map (secAct ρ hW hN))).index *
          Nat.card (fixV (B.map (secAct ρ hW hN))) * Nat.card N := (mul_assoc _ _ _).symm
      _ = Nat.card W := by rw [h2, h3]
      _ = _ := by rw [h1, h4]
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hFpos hNpos) key

end CFSG.Quasithin.MS93.S38E
