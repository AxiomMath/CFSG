module

public import CFSG.Quasithin.Vol2.Ch10SecE9ZL
public import CFSG.Quasithin.Background.InternalSecB56M
public import CFSG.Quasithin.Vol2.Ch10SecE9ZJ

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.EmptyFaithfulMultiple CFSG.Quasithin.B5

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem isSimpleGroup_of_centerless {L : Subgroup (MulAut V)} (hq : CFSG.IsQuasisimple ↥L)
    (hz : LRed5.Centerless L) : IsSimpleGroup ↥L := by
  have hc : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hz x x.2 fun y hy =>
      congrArg Subtype.val ((Subgroup.mem_center_iff.mp hx) ⟨y, hy⟩).symm)
  have e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have := hq.2.1
  exact e.symm.isSimpleGroup

omit [Finite V] in
theorem exists_mul_ne_of_centerless {L : Subgroup (MulAut V)} (hz : LRed5.Centerless L)
    (hc : Nat.card ↥L = 168) : ∃ a b : ↥L, a * b ≠ b * a := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hbot : L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.mpr (hz x hx fun y hy => congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩))
  rw [hbot, Subgroup.card_bot] at hc
  omega

omit [Finite V] in
theorem mem_normalizer_sup {L₁ L₂ : Subgroup (MulAut V)} {s : MulAut V}
    (h₁ : s ∈ Subgroup.normalizer (L₁ : Set (MulAut V)))
    (h₂ : s ∈ Subgroup.normalizer (L₂ : Set (MulAut V))) :
    s ∈ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup (MulAut V)) : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h₁ h₂ ⊢
  rw [Subgroup.map_sup, h₁, h₂]

theorem pair_fixSec (h56 : AsB56) (hB48 : AsB4_8Three) (hV2 : ∀ v : V, v ^ 2 = 1)
    {Γ L₁ L₂ : Subgroup (MulAut V)} {t : MulAut V} (P : LRed5.PairData Γ L₁ L₂ t)
    {S X : Subgroup (MulAut V)} (hS2 : IsPGroup 2 ↥S)
    (hSn₁ : ∀ s ∈ S, s ∈ Subgroup.normalizer (L₁ : Set (MulAut V)))
    (hSn₂ : ∀ s ∈ S, s ∈ Subgroup.normalizer (L₂ : Set (MulAut V)))
    (hXJ : X ≤ L₁ ⊔ L₂) {U₁ U₂ : Subgroup V} (hU₁ : U₁ ≤ commV L₁) (hU₂ : U₂ ≤ commV L₂)
    (hU₁8 : Nat.card ↥(U₁ ⊔ fixV (L₁ ⊔ L₂)) = 8 * Nat.card ↥(fixV (L₁ ⊔ L₂)))
    (hU₂8 : Nat.card ↥(U₂ ⊔ fixV (L₁ ⊔ L₂)) = 8 * Nat.card ↥(fixV (L₁ ⊔ L₂)))
    (hSU₁ : ∀ s ∈ S, ∀ u ∈ U₁, s u ∈ U₁) (hSU₂ : ∀ s ∈ S, ∀ u ∈ U₂, s u ∈ U₂)
    (hpt₁ : fixSec S (U₁ ⊔ fixV (L₁ ⊔ L₂)) (fixV (L₁ ⊔ L₂)) ≤
      fixSec X (U₁ ⊔ fixV (L₁ ⊔ L₂)) (fixV (L₁ ⊔ L₂)))
    (hpt₂ : fixSec S (U₂ ⊔ fixV (L₁ ⊔ L₂)) (fixV (L₁ ⊔ L₂)) ≤
      fixSec X (U₂ ⊔ fixV (L₁ ⊔ L₂)) (fixV (L₁ ⊔ L₂)))
    {g₁ g₂ : MulAut V} (hg₁L : g₁ ∈ L₁) (hg₁S : g₁ ∈ S) (hg₁4 : orderOf g₁ = 4)
    (hg₂L : g₂ ∈ L₂) (hg₂S : g₂ ∈ S) (hg₂4 : orderOf g₂ = 4) :
    fixSec S ⊤ (fixV (L₁ ⊔ L₂)) ≤ fixSec X ⊤ (fixV (L₁ ⊔ L₂)) := by
  have hV : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV2 v
  obtain ⟨hJeq, hcase⟩ := b56_of_pairData h56 hV P
  rw [hJeq] at hcase
  set C := fixV (L₁ ⊔ L₂) with hC
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (P.comm b hb a ha).symm
  have hs₁ := isSimpleGroup_of_centerless P.q₁ P.z₁
  have hs₂ := isSimpleGroup_of_centerless P.q₂ P.z₂
  have hSC : ∀ s ∈ S, ∀ c ∈ C, s c ∈ C := fun s hs c hc =>
    LRed5.fixV_invariant_of_normalizer (mem_normalizer_sup (hSn₁ s hs) (hSn₂ s hs)) hc
  have hSUC : ∀ {U : Subgroup V}, (∀ s ∈ S, ∀ u ∈ U, s u ∈ U) → ∀ s ∈ S, ∀ u ∈ U ⊔ C,
      s u ∈ U ⊔ C := fun hU s hs u hu => by
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul]
    exact Subgroup.mul_mem_sup (hU s hs a ha) (hSC s hs c hc)
  rcases hcase with ⟨W₁, W₂, hW₁, hW₂, hinv₁, hinv₂, hWsup, hWinf, hp₁, hp₂⟩ |
    ⟨G₁, G₂, hG, ⟨e₁⟩, hdir, hc8, hidx, -⟩
  ·
    have hiW₁ : ∀ g ∈ L₁ ⊔ L₂, ∀ w ∈ W₁, g w ∈ W₁ := fun g hg w hw => hinv₁ ⟨g, hg⟩ w hw
    have hiW₂ : ∀ g ∈ L₁ ⊔ L₂, ∀ w ∈ W₂, g w ∈ W₂ := fun g hg w hw => hinv₂ ⟨g, hg⟩ w hw
    have hcW₁ : commV L₁ ≤ W₁ := InternalSec.commV_le_of_b56Piece hp₁
    have hcW₂ : commV L₂ ≤ W₂ := InternalSec.commV_le_of_b56Piece hp₂
    have hfix₁ := fixSec_le_of_piece hB48 hV2 rfl P.comm hs₁ P.c₁ hp₁ hW₁ hWsup hWinf hiW₁
      hiW₂ hcW₂ hS2 hXJ hU₁ hU₁8 (hSUC hSU₁) hSC hpt₁ hg₁L hg₁S hg₁4
    have hfix₂ := fixSec_le_of_piece hB48 hV2 (sup_comm L₂ L₁) hc' hs₂ P.c₂ hp₂ hW₂
      (by rw [sup_comm]; exact hWsup) (by rw [inf_comm]; exact hWinf) hiW₂ hiW₁ hcW₁ hS2 hXJ
      hU₂ hU₂8 (hSUC hSU₂) hSC hpt₂ hg₂L hg₂S hg₂4
    have hW12 : W₁ ⊓ (C ⊔ W₂) = C := by rw [sup_eq_right.mpr hW₂, hWinf]
    have hW21 : W₂ ⊓ (C ⊔ W₁) = C := by rw [sup_eq_right.mpr hW₁, inf_comm, hWinf]
    have hY12 : (commV L₁ ⊔ C) ⊓ (C ⊔ (commV L₂ ⊔ C)) = C := by
      refine le_antisymm ?_ (le_inf le_sup_right le_sup_left)
      calc (commV L₁ ⊔ C) ⊓ (C ⊔ (commV L₂ ⊔ C)) ≤ W₁ ⊓ (C ⊔ W₂) :=
            inf_le_inf (sup_le hcW₁ hW₁) (sup_le_sup_left (sup_le hcW₂ hW₂) C)
        _ = C := hW12
    have hY21 : (commV L₂ ⊔ C) ⊓ (C ⊔ (commV L₁ ⊔ C)) = C := by
      refine le_antisymm ?_ (le_inf le_sup_right le_sup_left)
      calc (commV L₂ ⊔ C) ⊓ (C ⊔ (commV L₁ ⊔ C)) ≤ W₂ ⊓ (C ⊔ W₁) :=
            inf_le_inf (sup_le hcW₂ hW₂) (sup_le_sup_left (sup_le hcW₁ hW₁) C)
        _ = C := hW21
    have hinvY : ∀ s ∈ S, (∀ v ∈ commV L₁ ⊔ C, s v ∈ commV L₁ ⊔ C) ∧
        ∀ v ∈ commV L₂ ⊔ C, s v ∈ commV L₂ ⊔ C := fun s hs =>
      ⟨hSUC (fun s' hs' u hu => LRed4.commV_invariant_of_normalizer (hSn₁ s' hs') hu) s hs,
        hSUC (fun s' hs' u hu => LRed4.commV_invariant_of_normalizer (hSn₂ s' hs') hu) s hs⟩
    have hfC : ∀ l ∈ L₁ ⊔ L₂, ∀ c ∈ C, l c = c := fun l hl c hc => mem_fixV.mp hc l hl
    rintro w ⟨-, hwS⟩
    refine ⟨trivial, fun x hx => ?_⟩
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.mp (hWsup ▸ Subgroup.mem_top w)
    have ha₁ : orderOf (g₁ ^ 2) = 2 := by rw [orderOf_pow' g₁ two_ne_zero, hg₁4]; norm_num
    have ha₂ : orderOf (g₂ ^ 2) = 2 := by rw [orderOf_pow' g₂ two_ne_zero, hg₂4]; norm_num
    have hJ₁ : g₁ ^ 2 ∈ L₁ ⊔ L₂ := Subgroup.mem_sup_left (L₁.pow_mem hg₁L 2)
    have hJ₂ : g₂ ^ 2 ∈ L₁ ⊔ L₂ := Subgroup.mem_sup_right (L₂.pow_mem hg₂L 2)
    have hw₁Y : w₁ ∈ commV L₁ ⊔ C :=
      mem_commV_sup_of_piece hB48 hV2 hs₁ hp₁ hW₁ hWsup hWinf
        (fun l hl => hiW₁ l (Subgroup.mem_sup_left hl))
        (fun l hl => hiW₂ l (Subgroup.mem_sup_left hl))
        (fun l hl => hfC l (Subgroup.mem_sup_left hl)) (L₁.pow_mem hg₁L 2) ha₁ hw₁
        (mul_inv_mem_of_independent hW12 (hiW₁ _ hJ₁) (hiW₂ _ hJ₁) hw₁ hw₂
          (hwS _ (S.pow_mem hg₁S 2)))
    have hw₂Y : w₂ ∈ commV L₂ ⊔ C :=
      mem_commV_sup_of_piece hB48 hV2 hs₂ hp₂ hW₂ (by rw [sup_comm]; exact hWsup)
        (by rw [inf_comm]; exact hWinf)
        (fun l hl => hiW₂ l (Subgroup.mem_sup_right hl))
        (fun l hl => hiW₁ l (Subgroup.mem_sup_right hl))
        (fun l hl => hfC l (Subgroup.mem_sup_right hl)) (L₂.pow_mem hg₂L 2) ha₂ hw₂
        (mul_inv_mem_of_independent hW21 (hiW₂ _ hJ₂) (hiW₁ _ hJ₂) hw₂ hw₁
          (by rw [mul_comm w₂ w₁]; exact hwS _ (S.pow_mem hg₂S 2)))
    have hS₁ : w₁ ∈ fixSec S W₁ C := ⟨hw₁, fun s hs =>
      mul_inv_mem_of_independent hY12 (hinvY s hs).1 (hinvY s hs).2 hw₁Y hw₂Y (hwS s hs)⟩
    have hS₂ : w₂ ∈ fixSec S W₂ C := ⟨hw₂, fun s hs =>
      mul_inv_mem_of_independent hY21 (hinvY s hs).2 (hinvY s hs).1 hw₂Y hw₁Y
        (by rw [mul_comm w₂ w₁]; exact hwS s hs)⟩
    have hX₁ := (hfix₁ hS₁).2 x hx
    have hX₂ := (hfix₂ hS₂).2 x hx
    have e : x (w₁ * w₂) * (w₁ * w₂)⁻¹ = (x w₁ * w₁⁻¹) * (x w₂ * w₂⁻¹) := by
      rw [map_mul, mul_inv_rev]
      ac_rfl
    rw [e]
    exact C.mul_mem hX₁ hX₂
  ·
    have htJ := P.le_normalizer P.tΓ
    rcases hG with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fixSec_top_le_of_case5 hB48 hV2 rfl P.comm hs₁ (exists_mul_ne_of_centerless P.z₁ P.c₁)
        P.c₁ e₁ hdir hc8 hidx P.swap₂ htJ hSn₁ hSn₂ hSC hXJ hU₁ hU₂ hU₁8 hU₂8 hpt₁ hpt₂ hg₁L hg₁S
        hg₁4
    · have hs₂₁ : ∀ y ∈ G₂, t⁻¹⁻¹ * y * t⁻¹ ∈ G₁ := fun y hy => by
        simpa using P.swap₁ y hy
      exact fixSec_top_le_of_case5 hB48 hV2 (sup_comm G₁ G₂) hc' hs₂
        (exists_mul_ne_of_centerless P.z₂ P.c₂) P.c₂ e₁ hdir hc8 hidx hs₂₁
        (Subgroup.inv_mem _ htJ) hSn₂ hSn₁ hSC hXJ hU₂ hU₁ hU₂8 hU₁8 hpt₂ hpt₁ hg₂L hg₂S hg₂4

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
