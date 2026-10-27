module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Out
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Z12
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2NoDih
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Res
public import CFSG.Sporadic.Schreier.M12OrderTwelve
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2DihB

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

namespace S143

namespace InspW2

theorem resW_m12 :
    ResW fun L _ => Nonempty (L ≃* NativeSporadic.Carrier .M12) := by
  intro L _ _ _ ⟨e⟩ Gc _ _ ρ ž Ŝ Kh hin _
  have hZ : Subgroup.center L = ⊥ :=
    center_eq_bot_of_mulEquiv e CFSG.Sporadic.Schreier.m12_center_eq_bot'
  have hcard : Nat.card L = 95040 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.m12_card
  have h6 : 2 ^ 6 ∣ Nat.card L := ⟨1485, by rw [hcard]; norm_num⟩
  have hodd := odd_index_comap_conj hZ h6 hin
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) ≤ 2 := by
    refine card_outer_le_of_card_aut hZ ?_
    have h1 : Nat.card (MulAut L) = Nat.card (MulAut (NativeSporadic.Carrier .M12)) :=
      Nat.card_congr (MulAut.congr e).toEquiv
    have h2 : Nat.card L = Nat.card (NativeSporadic.Carrier .M12) := Nat.card_congr e.toEquiv
    rw [h1, h2]
    exact CFSG.Sporadic.Schreier.m12_mulAut_card
  have hinner := mem_conj_range_of_odd_index ρ hOut hodd
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [← MonoidHom.ker_eq_bot_iff, Insp7.ker_conj_eq_center, hZ]
  obtain ⟨g, hg⟩ := exists_orderOf_twelve_of_z4StarSL23 hin.K_shape
  obtain ⟨l, hl⟩ := hinner (g : Gc)
  have hg' : orderOf (g : Gc) = 12 := by rw [Subgroup.orderOf_coe, hg]
  have hl12 : orderOf l = 12 := by
    rw [← orderOf_injective _ hinj l, hl, orderOf_injective _ hin.inj, hg']
  have h12 : orderOf (e l) = 12 := by
    rw [← hl12]
    exact orderOf_injective e.toMonoidHom e.injective l
  exact CFSG.Sporadic.Schreier.m12_no_order_twelve (e l) h12

end InspW2

end S143

end CFSG.Quasithin
