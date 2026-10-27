module

public import CFSG.Quasithin.H13.VolII16Restrict
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123CentralZeroAbs

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin Subgroup

theorem card_f2_four : Nat.card (Multiplicative (Fin 4 → ZMod 2)) = 16 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem a7Four_cover
    {α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
    {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {Z : Subgroup W} (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (h : (FFModel.a7Four α).Realizes H ⊤ Z) : Z = ⊥ := by
  obtain ⟨π₀, hπs, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  let π : ↥(alternatingGroup (Fin 7)) →* ↥H := π₀
  let act : ↥(alternatingGroup (Fin 7)) →* MulAut W := H.subtype.comp π
  refine CFSG.QuasithinUnique.L246.C123.central_zero_abstract hW2 act (MonoidHom.id _)
    (fun x => ⟨x, rfl⟩) (fun q hq => by rw [show q = 1 from hq, map_one]) Z
    (fun g z hz => hZ hz _ (π g).2) ?_ ?_
  ·
    have hk : β.ker = Z.subgroupOf ⊤ := by
      ext u
      rw [MonoidHom.mem_ker, hβk, mem_subgroupOf]
    have hr : β.range = ⊤ := MonoidHom.range_eq_top.2 hβs
    have h1 := card_ker_mul_card_range β
    rw [hk, hr, card_top, card_top,
      Nat.card_congr (subgroupOfEquivOfLe (le_top : Z ≤ ⊤)).toEquiv] at h1
    have hQ : Nat.card (↥(FFModel.a7Four α).sec ⧸
        (FFModel.a7Four α).ker.subgroupOf (FFModel.a7Four α).sec) = 16 := by
      show Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 2))) ⧸
        (⊥ : Subgroup (Multiplicative (Fin 4 → ZMod 2))).subgroupOf ⊤) = 16
      rw [bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv, card_top,
        card_f2_four]
    rw [hQ] at h1
    rw [← h1, mul_comm]
  ·
    rw [← hcomm]
    congr 1
    ext x
    constructor
    · rintro ⟨g, v, rfl⟩
      exact ⟨_, (π g).2, v, rfl⟩
    · rintro ⟨y, hy, v, rfl⟩
      obtain ⟨g, hg⟩ := hπs ⟨y, hy⟩
      refine ⟨g, v, ?_⟩
      have hg' : act g = y := congrArg Subtype.val hg
      rw [hg']

theorem a7Four_eq_bot
    {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} (hI : commV L ∈ IrrPlus L ⊤)
    (h : A7Four L (commV L) (fixV L ⊓ commV L)) : fixV L ⊓ commV L = ⊥ := by
  obtain ⟨α, hα⟩ := h
  exact eq_bot_of_restrict _ (fun W _ _ hW2 H Z hZ hcomm hR => a7Four_cover hW2 hZ hcomm hR)
    hV2 hI hα

end CFSG.Quasithin.H13.VolI
