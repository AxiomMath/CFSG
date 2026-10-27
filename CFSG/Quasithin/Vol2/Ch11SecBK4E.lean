module

public import CFSG.Quasithin.Vol2.Ch11SecBK4D
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall
open CFSG.Open (quasithinG2 IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped IsMulCommutative

namespace BK4

variable {G : Type} [Group G] {L V : Subgroup G}

omit [Group G] in
theorem conjV_eq_one_of_mem {G : Type} [Group G] {V : Subgroup G} {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hx : x ∈ Subgroup.centralizer (V : Set G)) :
    SecA.conjV V x hxV = 1 := by
  ext v
  rw [SecA.conjV_apply_coe, MulAut.one_apply, ← (Subgroup.mem_centralizer_iff.mp hx v v.2),
    mul_inv_cancel_right]

variable [IsMulCommutative ↥V]

theorem mParam_eq_of [Finite G] (hV : IsElemAbelian 2 V) {X : Subgroup G} (hLX : L ≤ X)
    {m : ℕ}
    (hlow : ∀ (x : G) (_ : x ∈ X) (hxV : x ∈ Subgroup.normalizer (V : Set G)),
      x ∉ Subgroup.centralizer (V : Set G) → SecA.conjV V x hxV * SecA.conjV V x hxV = 1 →
        m ≤ rkIdx (fixV (Subgroup.zpowers (SecA.conjV V x hxV))))
    (hup : ∃ t ∈ autOn L V, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) ≤ m) :
    E3.mParam (autI hV X) = m := by
  have hlow' : ∀ t ∈ autI hV X, orderOf t = 2 → m ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
    intro t ht ht2
    obtain ⟨⟨x, hxV⟩, hxX, rfl⟩ := (mem_autI hV).mp ht
    have hx1 : x ∉ Subgroup.centralizer (V : Set G) := fun hx => by
      have h1 : SecA.conjV V x hxV = 1 := conjV_eq_one_of_mem hxV hx
      have h2 : orderOf (SecA.conjV V x hxV) = 1 := by rw [h1, orderOf_one]
      exact absurd (h2.symm.trans ht2) (by norm_num)
    have hsq : SecA.conjV V x hxV * SecA.conjV V x hxV = 1 := by
      rw [← sq]
      exact (orderOf_eq_iff (by norm_num)).mp ht2 |>.1
    exact hlow x hxX hxV hx1 hsq
  obtain ⟨t, ht, ht2, htm⟩ := hup
  have htX : t ∈ autI hV X := by
    obtain ⟨l, hl, hlV, rfl⟩ := SecA.mem_autOn_iff.mp ht
    exact SecA.conjV_mem_autOn (hLX hl) hlV
  exact mParam_eq hV hlow' ⟨t, htX, ht2, le_antisymm htm (hlow' t htX ht2)⟩

theorem le_mQuot_bot [Finite G] (hV : IsElemAbelian 2 V) {D : FFModel} {K M : Type} [Field K]
    [AddCommGroup M] [Module K M] {LM : KGNat.LinModel D K M} {H : Subgroup (MulAut ↥V)}
    {Z : Subgroup ↥V} {π : D.Gam →* ↥H} {f : ↥V → M} (hf : KGNat.IsCoord LM H Z π f) {a : ℕ}
    (hM : Nat.card M = 2 ^ a) : a ≤ E3.mQuot V ⊥ := by
  rw [E3.mQuot_eq_rkIdx, Subgroup.bot_subgroupOf]
  have h1 := index_eq_two_pow hV (⊥ : Subgroup ↥V)
  rw [Subgroup.index_bot, card_eq_mul hf, hM] at h1
  have h2 : 2 ^ a ≤ 2 ^ rkIdx (⊥ : Subgroup ↥V) := by
    rw [← h1]
    exact Nat.le_mul_of_pos_left _ Nat.card_pos
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

end BK4

theorem factMParam_holds : FactMParam := by
  intro G _ _ L V X n m hV hn hLV hVL hnat hm hLX hXN
  obtain ⟨hc, hnat'⟩ := hnat
  have hG2 : SecA.FactG2DerivedOrder := KGNat.factG2DerivedOrder_holds
  rcases hnat' with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
    have hmn : m = n := by
      rcases hm with ⟨hk, -⟩ | ⟨-, hmn⟩
      · exact (SecA.kind_not_SL3_G2 hG2 hn (BK4.kindSL3_of_isCoord hK hf) hk).elim
      · exact hmn
    subst hmn
    refine ⟨BK4.mParam_eq_of hV hLX (fun x hxX hxV hx1 _ =>
      BK4.le_rkIdx_sl3 hV hLV hVL hK hf hxV (hXN ⟨hxX, hxV⟩) hx1)
      (BK4.exists_rkIdx_le_sl3 hV hn hK hf), ?_⟩
    have := BK4.le_mQuot_bot hV hf (BK4.card_fun_three hK)
    omega
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
    have hmn : m = n := by
      rcases hm with ⟨hk, -⟩ | ⟨-, hmn⟩
      · exact (SecA.kind_not_Sp4_G2 hG2 hn (BK4.kindSp4_of_isCoord hK hf) hk).elim
      · exact hmn
    subst hmn
    refine ⟨BK4.mParam_eq_of hV hLX (fun x hxX hxV hx1 _ =>
      BK4.le_rkIdx_sp4 hV hLV hVL hK hf hxV (hXN ⟨hxX, hxV⟩) hx1)
      (BK4.exists_rkIdx_le_sp4 hV hK hf), ?_⟩
    have := BK4.le_mQuot_bot hV hf (BK4.card_fun_four hK)
    omega
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (G2Q8.lmG K) hπ
    have hmn : m = 2 * n := by
      rcases hm with ⟨-, hmn⟩ | ⟨hk, -⟩
      · exact hmn
      · exact (hk (BK4.kindG2_of_isCoord hn hK hf)).elim
    subst hmn
    refine ⟨BK4.mParam_eq_of hV hLX (fun x hxX hxV hx1 hsq =>
      BK4.le_rkIdx_g2 hV hLV hVL hn hK hf hxV (hXN ⟨hxX, hxV⟩) hx1 hsq)
      (BK4.exists_rkIdx_le_g2 hV hn hK hf), ?_⟩
    have := BK4.le_mQuot_bot hV hf (BK4.card_fun_six hK)
    omega

end CFSG.Quasithin.Vol2.Ch11.SecB
