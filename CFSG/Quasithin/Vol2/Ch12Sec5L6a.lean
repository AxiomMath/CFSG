module

public import CFSG.Quasithin.Background.FixVZPowers
public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Vol2.Ch12Sec5L5a
public import CFSG.Quasithin.Vol2.Ch12Sec4E61
public import CFSG.Quasithin.Vol2.Ch12Sec4L5Mbar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 Matrix
open scoped IsMulCommutative

namespace S125L6a

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem hypE61_of_hyp (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (hyp : Hyp1223 G T L V) (hVe : IsElemAbelian 2 V) (hV1 : V ≠ ⊥)
    (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    E6.HypE61 T (Subgroup.normalizer (L : Set G)) V := by
  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨hmax, -, huniq⟩, -, -, -, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at hmax huniq
  have hLT : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hyp.normalizes
  have hQ : L ⊔ T ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    rw [← pCoreOf_sup_eq_of_hyp1223 h1222 h3228 hyp]
    exact LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hLTX : L ⊔ T ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ⊓
        (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) :=
    le_inf hQ (le_inf hLT (sup_le hLV hTV))
  refine
    { simple := hyp.simple
      nonabelian := hyp.nonabelian
      qtke := hyp.qtke
      sylow := hyp.sylow
      inM := ⟨hmax, hyp.normalizes⟩
      ne_bot := hV1
      isElemAbelian := hVe
      le := hVT
      normal := hTV
      tiSet := ⟨hVT.trans hyp.normalizes, fun g hg hgN => ?_⟩
      unique := ⟨⟨hmax, inf_le_right.trans inf_le_left⟩, fun M' hM' =>
        huniq M' hM'.1 (hLTX.trans hM'.2)⟩ }
  rcases (stmt12_2_6_of h1222 h323 G T L V hyp).1 g hg with h | h
  · exact absurd (mem_normalizer_of_conjugate_eq h) hgN
  · exact h

theorem autOn_normalizer_eq (h12210 : Stmt12_2_10) (hyp : Hyp1223 G T L V)
    (F : Frame125 T L V) : autOn (Subgroup.normalizer (L : Set G)) V = autOn L V := by
  have h1 : autOn (Subgroup.normalizer (L : Set G)) V = hyp.MVbar := by
    show autOn (Subgroup.normalizer (L : Set G)) V =
      autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V
    unfold autOn
    rw [Subgroup.inf_subgroupOf_right]
  rw [h1, (h12210 G T L V hyp).2.2, sup_eq_left.2 (S125St.autOn_T_le F)]

omit [Finite G] in
theorem mem_fixV_zpowers_iff {W : Type*} [CommGroup W] {a : MulAut W} {v : W} :
    v ∈ fixV (Subgroup.zpowers a) ↔ a v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

omit [Finite G] in
theorem fixV_conj {W : Type*} [CommGroup W] (a c : MulAut W) :
    fixV (Subgroup.zpowers (c * a * c⁻¹)) = (fixV (Subgroup.zpowers a)).map c.toMonoidHom :=
  CFSG.Quasithin.fixV_zpowers_conj c a

omit [Finite G] in
theorem card_fixV_conj {W : Type*} [CommGroup W] (a c : MulAut W) :
    Nat.card (fixV (Subgroup.zpowers (c * a * c⁻¹))) = Nat.card (fixV (Subgroup.zpowers a)) :=
  CFSG.Quasithin.card_fixV_zpowers_conj c a

omit [Finite G] in
theorem card_fixV_j1 (F : Frame125 T L V) [IsMulCommutative ↥V] :
    Nat.card (fixV (V := ↥V) (Subgroup.zpowers ((S125L5a.j1 F : ↥(autOn L V)) : MulAut ↥V))) =
      128 := by
  rw [S125L5a.card_of_coords F
    (p := fun x => JonesParshall.wedgeMat S125Inv.t1 *ᵥ x = x) fun v => ?_]
  · exact S125L5a.card_fix_t1
  · rw [mem_fixV_zpowers_iff, S125L5a.j1]
    exact S125L5a.fix_iff F S125L5a.T1 v

omit [Finite G] in
theorem card_fixV_j2 (F : Frame125 T L V) [IsMulCommutative ↥V] :
    Nat.card (fixV (V := ↥V) (Subgroup.zpowers ((S125L5a.j2 F : ↥(autOn L V)) : MulAut ↥V))) =
      64 := by
  rw [S125L5a.card_of_coords F
    (p := fun x => JonesParshall.wedgeMat S125Inv.t2 *ᵥ x = x) fun v => ?_]
  · exact S125L5a.card_fix_t2
  · rw [mem_fixV_zpowers_iff, S125L5a.j2]
    exact S125L5a.fix_iff F S125L5a.T2 v

omit [Finite G] in
theorem card_fixV_invol (F : Frame125 T L V) [IsMulCommutative ↥V] (a : ↥(autOn L V))
    (ha : orderOf a = 2) :
    ((∃ c : ↥(autOn L V), c * a * c⁻¹ = S125L5a.j1 F) ∧
        Nat.card (fixV (V := ↥V) (Subgroup.zpowers (a : MulAut ↥V))) = 128) ∨
      Nat.card (fixV (V := ↥V) (Subgroup.zpowers (a : MulAut ↥V))) = 64 := by
  have key : ∀ c : ↥(autOn L V), Nat.card (fixV (V := ↥V) (Subgroup.zpowers
      ((c * a * c⁻¹ : ↥(autOn L V)) : MulAut ↥V))) =
        Nat.card (fixV (V := ↥V) (Subgroup.zpowers (a : MulAut ↥V))) := fun c => by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact card_fixV_conj _ _
  rcases S125L5a.conj_j F a ha with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine Or.inl ⟨⟨c, hc⟩, ?_⟩
    rw [← key c, hc]
    exact card_fixV_j1 F
  · refine Or.inr ?_
    rw [← key c, hc]
    exact card_fixV_j2 F

theorem mParam_eq (h12210 : Stmt12_2_10) (hyp : Hyp1223 G T L V) (F : Frame125 T L V)
    (hV : IsElemAbelian 2 V) [IsMulCommutative ↥V] (hcard : Nat.card V = 2 ^ 10) :
    E3.mParam (autI hV (Subgroup.normalizer (L : Set G))) = 3 := by
  have hMV : autI hV (Subgroup.normalizer (L : Set G)) = autI hV L :=
    autOn_normalizer_eq h12210 hyp F
  have hcardL : Nat.card ↥(autI hV L) = 9999360 := by
    rw [← card_sl_five_zmod_two]
    exact Nat.card_congr F.γ.toEquiv
  have hev : Even (Nat.card ↥(autI hV L)) := by
    rw [hcardL]
    exact ⟨4999680, by norm_num⟩
  have hcardI : Nat.card (IntMod V hV) = 2 ^ 10 := hcard
  have hj1 : orderOf ((S125L5a.j1 F).val : MulAut (IntMod V hV)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact S125L5a.orderOf_j1 F
  unfold E3.mParam
  rw [hMV, ite_eq_left hev]
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _)
      ⟨(S125L5a.j1 F).val, (S125L5a.j1 F).2, hj1, (S125L5a.rkIdx_fixV_j1 F hcard).symm⟩
  · refine le_csInf ⟨_, (S125L5a.j1 F).val, (S125L5a.j1 F).2, hj1, rfl⟩ ?_
    rintro _ ⟨t, ht, hto, rfl⟩
    set a : ↥(autOn L V) := ⟨t, ht⟩
    have ha : orderOf a = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hto
    have hle : Nat.card (fixV (V := IntMod V hV) (Subgroup.zpowers t)) ≤ 2 ^ 7 := by
      rcases card_fixV_invol F a ha with ⟨-, h⟩ | h
      · exact h.le
      · exact h.le.trans (by norm_num)
    exact three_le_rkIdx hcardI hle

end S125L6a

end CFSG.Quasithin.H13
