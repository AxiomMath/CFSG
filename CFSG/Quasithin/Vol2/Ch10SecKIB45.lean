module

public import CFSG.Quasithin.Vol2.Ch10SecKIf
public import CFSG.Quasithin.Vol2.Ch10SecKIg
public import CFSG.Quasithin.Background.B5NonB
public import CFSG.Quasithin.Background.G64ProofBasic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace C10KH

theorem false_of_action (h45 : AsB45) {Y : Type} [Group Y] [Finite Y]
    (hS : CFSG.SectionRank.IsSQTKCat Y) (hq : CFSG.IsQuasisimple Y)
    (hT : TargetCard (Nat.card Y)) (hZ : Nat.card (Subgroup.center Y) ≤ 3) {W : Type}
    [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (ρ : Y →* MulAut W)
    (hinj : Function.Injective ρ) (N : Subgroup Y)
    (hQ : ∀ K : Subgroup Y, K.Normal → (∀ n ∈ N, n * n ∈ K) → N ≤ K)
    (hF : ∀ K : Subgroup Y, K.Normal → ¬ N ≤ K → K = ⊥) (hN : N ≠ ⊥) {b : Y}
    (hb : orderOf b = 2) (hc : Nat.card ↥(commV (Subgroup.zpowers (ρ b))) ≤ 4) : False := by
  have hNk : ¬ N ≤ ρ.ker := by
    rw [(MonoidHom.ker_eq_bot_iff ρ).2 hinj]
    exact fun h => hN (eq_bot_iff.2 h)
  obtain ⟨W', U', hUW, hXW, hXU, hirr, hNWU⟩ := exists_irr_section hW ρ N hQ hNk
  have hK := hF _ (comap_centSec_normal ρ hXW hXU) hNWU
  have hfaith : ρ.range ⊓ centSec W' U' = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨y, rfl⟩, hy⟩
    have hy' : y ∈ (centSec W' U').comap ρ := hy
    rw [hK, Subgroup.mem_bot] at hy'
    rw [hy', map_one]
    exact Subgroup.one_mem _
  let f : Y ≃* ↥ρ.range := MonoidHom.ofInjective hinj
  have hSX : SQTKGroup ↥ρ.range := B5.sqtk_of_mulEquiv f.symm (G64.sqtkGroup_of_isSQTKCat hS)
  have hqX : CFSG.IsQuasisimple ↥ρ.range := CFSG.LocalCores.isQuasisimple_of_mulEquiv f hq
  have hB4 := b4Hyp_autSec hUW hXW hXU hirr hfaith hSX hqX
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  have hb1 : ρ b ≠ 1 := by
    intro h
    have h1 : b = 1 := hinj (h.trans (map_one ρ).symm)
    rw [h1, orderOf_one] at hb
    omega
  have hqh := qhatOf_autSec_le hW hXW hXU hfaith hb2 hb1 hc
  let e : ↥(autSec ρ.range W' U') ≃* Y :=
    (B5.secEquiv ρ.range hXW hXU hfaith).symm.trans f.symm
  have hTG : TargetCard (Nat.card ↥(autSec ρ.range W' U')) := by
    rw [Nat.card_congr e.toEquiv]
    exact hT
  have hZG : Nat.card (Subgroup.center ↥(autSec ρ.range W' U')) ≤ 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hZ
  have hV' := sec_sq hW W' U'
  rcases h45 (Sec W' U') hV' _ _ hB4 hqh with ⟨-, ⟨A, hA⟩, hall⟩ | ⟨-, ht⟩ | h3
  · exact false_of_b42 hV' hB4 rfl hA (hall A hA) hTG
  · exact false_of_table ht hTG hZG
  · exact false_of_part3 h3 hTG

end C10KH

end CFSG.Quasithin.Vol2.Ch10.SecF
