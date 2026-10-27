module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aJ4D
public import CFSG.Sporadic.J4.QT2LocUniq
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.Quasithin.Vol2.Ch11SecQ9aJ4C

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.J4U

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs CFSG.QuasithinUnique.Ch1.SporLat.M24

theorem finite_J : Finite J :=
  Nat.finite_of_card_ne_zero (by rw [card_J j4Facts]; norm_num)

theorem isSylowTwoOf_P0 :
    QuasithinUnique.IsSylowTwoOf P0 ⊤ := by
  have hF := j4Facts
  have hM := hF.mat
  have := finite_J
  refine QuasithinUnique.K1.isSylowTwoOf_top_iff.mpr
    ⟨IsPGroup.of_card (card_P0 hM hF), fun h => ?_⟩
  have h1 := Subgroup.card_mul_index P0
  rw [card_P0 hM hF, card_J hF] at h1
  norm_num at h1
  have h2 : P0.index = 41377816699065 := by omega
  rw [h2] at h
  norm_num at h

theorem le_P0_of_isPGroup
    {P : Subgroup J} (hP : IsPGroup 2 P)
    (hSP : P0 ≤ Subgroup.normalizer (P : Set J)) : P ≤ P0 := by
  have := finite_J
  exact OE5.le_of_isPGroup isSylowTwoOf_P0 hP hSP

theorem nonempty_quot_equiv_m24 :
    Nonempty (↥Hj ⧸ (Eg uJ 11).subgroupOf Hj ≃* CFSG.Blueprint.NativeSporadic.Carrier .M24) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq ker_starHom.symm).trans
      (QuotientGroup.quotientKerEquivRange starHom)).trans
    (MulEquiv.subgroupCongr range_starHom_eq)⟩

theorem card_map_quot
    {Y : Subgroup J} (hYH : Y ≤ Hj) (hEY : Eg uJ 11 ≤ Y) {a : ℕ}
    (hY : Nat.card Y = a * 2 ^ 11) :
    Nat.card ((Y.subgroupOf Hj).map (QuotientGroup.mk' ((Eg uJ 11).subgroupOf Hj))) = a := by
  have hF := j4Facts
  have hM := hF.mat
  have : ((Eg uJ 11).subgroupOf Hj).Normal :=
    (Subgroup.normal_subgroupOf_iff Eg_le_Hj).2 fun h g hh hg => Hj_normalizes_Eg hM g hg h hh
  have hker : (QuotientGroup.mk' ((Eg uJ 11).subgroupOf Hj)).ker ≤ Y.subgroupOf Hj := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hEY (Subgroup.mem_subgroupOf.mp hx))
  have hidx := Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker
  have h1 := Subgroup.card_mul_index
    ((Y.subgroupOf Hj).map (QuotientGroup.mk' ((Eg uJ 11).subgroupOf Hj)))
  have h2 := Subgroup.card_mul_index (Y.subgroupOf Hj)
  rw [hidx, card_Hj_quotient] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv, hY, card_Hj hF] at h2
  have h3 : a * (Y.subgroupOf Hj).index = 244823040 := by
    have h4 : 2 ^ 11 * (a * (Y.subgroupOf Hj).index) = 2 ^ 11 * 244823040 := by
      rw [show (2 : ℕ) ^ 11 * 244823040 = 501397585920 by norm_num, ← h2]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h4
  have hpos : 0 < (Y.subgroupOf Hj).index :=
    Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at h3; norm_num at h3
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h3.symm)

theorem not_le_Hj
    {B : Subgroup J}
    (hB : IsL24Sub P0 B) (hBH : B ≤ Hj) : False := by
  have hF := j4Facts
  have hM := hF.mat
  have := finite_J
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP0 : IsPGroup 2 P0 := IsPGroup.of_card (card_P0 hM hF)
  have hYH : B ⊔ P0 ≤ Hj := sup_le hBH P0_le_Hj
  obtain ⟨m, hm⟩ := O11.card_sup hP0 hB
  have hm21 : m = 21 := by
    have h1 : 2 ^ 21 ∣ 15 * 2 ^ m := by
      rw [← hm, ← card_P0 hM hF]
      exact Subgroup.card_dvd_of_le le_sup_right
    have h2 : 15 * 2 ^ m ∣ 86775571046077562880 := by
      rw [← hm, ← card_J hF]
      exact Subgroup.card_subgroup_dvd_card _
    have h1' : 2 ^ 21 ∣ 2 ^ m :=
      (Nat.Coprime.pow_left 21 (by norm_num : Nat.Coprime 2 15)).dvd_of_dvd_mul_left h1
    have hle : 21 ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1'
    by_contra hne
    have h3 : 2 ^ 22 ∣ 86775571046077562880 :=
      (Nat.pow_dvd_pow 2 (by omega : 22 ≤ m)).trans ((dvd_mul_left _ _).trans h2)
    norm_num at h3
  subst hm21
  have hEP : Eg uJ 11 ≤ P0 := Eg_le_P0
  have hYc := card_map_quot hYH (hEP.trans le_sup_right) (a := 15 * 2 ^ 10)
    (by rw [hm]; ring)
  have hTc := card_map_quot P0_le_Hj hEP (a := 2 ^ 10) (by rw [card_P0 hM hF]; ring)
  have hT : QuasithinUnique.IsSylowTwoOf
      ((P0.subgroupOf Hj).map (QuotientGroup.mk' ((Eg uJ 11).subgroupOf Hj))) ⊤ := by
    refine QuasithinUnique.K1.isSylowTwoOf_top_iff.mpr ⟨IsPGroup.of_card hTc, fun h => ?_⟩
    have h1 := Subgroup.card_mul_index
      ((P0.subgroupOf Hj).map (QuotientGroup.mk' ((Eg uJ 11).subgroupOf Hj)))
    rw [hTc, card_Hj_quotient] at h1
    norm_num at h1
    have h2 : ((P0.subgroupOf Hj).map
        (QuotientGroup.mk' ((Eg uJ 11).subgroupOf Hj))).index = 239085 := by omega
    rw [h2] at h
    norm_num at h
  have hTY : (P0.subgroupOf Hj).map (QuotientGroup.mk' ((Eg uJ 11).subgroupOf Hj)) ≤
      ((B ⊔ P0).subgroupOf Hj).map (QuotientGroup.mk' ((Eg uJ 11).subgroupOf Hj)) :=
    Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr ((le_sup_right : P0 ≤ B ⊔ P0) (Subgroup.mem_subgroupOf.mp hx))
  have hall : ∀ r ∈ m24Mems, r.order ≠ 15360 := by decide
  rcases m24_overgroups nonempty_quot_equiv_m24 hT hTY with h | ⟨r, hr, hrc, -⟩
  · rw [h, Subgroup.card_top, card_Hj_quotient] at hYc
    norm_num at hYc
  · rw [hYc] at hrc
    exact hall r hr (by rw [← hrc]; norm_num)

theorem le_centralizer_z0
    {B : Subgroup J}
    (hB : IsL24Sub P0 B) : B ≤ Subgroup.centralizer ({z0} : Set J) := by
  have hF := j4Facts
  have hM := hF.mat
  have := finite_J
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP0 : IsPGroup 2 P0 := IsPGroup.of_card (card_P0 hM hF)
  have hSB := hB.2.2.1
  have hO : pCoreOf 2 B ≤ P0 := by
    refine le_P0_of_isPGroup ?_
      (hSB.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B))
    have h : pCoreOf 2 B = (CFSG.pCore 2 ↥B).map B.subtype := by
      rw [pCoreOf]
    rw [h]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).map _
  have hS₁ : actKer hSB ≤ P0 := actKer_le hSB
  have hidx : (actKer hSB).relIndex P0 ≤ 8 := relIndex_actKer_le hP0 hB
  have hBS₁ : B ≤ Subgroup.normalizer (actKer hSB : Set J) := le_normalizer_actKer hSB hO
  have hPS₁ : P0 ≤ Subgroup.normalizer (actKer hSB : Set J) := le_normalizer_actKer' hSB
  have hS₁ne : actKer hSB ≠ ⊥ := by
    intro h
    rw [h, Subgroup.relIndex_bot_left, card_P0 hM hF] at hidx
    norm_num at hidx
  have hz0 : z0 ∈ actKer hSB :=
    OE5.mem_of_normal hP0 (fun y hy hc => eq_z0_of_central hM hF hy hc) hS₁ hPS₁ hS₁ne
  set V := (Subgroup.center (actKer hSB)).map (actKer hSB).subtype with hV
  have hVE : V ≤ Eg uJ 11 := center_le_Eg hM hF hS₁ hidx
  have hz0V : z0 ∈ V := by
    refine ⟨⟨z0, hz0⟩, Subgroup.mem_center_iff.mpr fun s => Subtype.ext ?_, rfl⟩
    exact (z0_central hM hF).2 s (hS₁ s.2)
  have hBV : B ≤ Subgroup.normalizer (V : Set J) := fun b hb =>
    normalizer_le_normalizer_center (hBS₁ hb)
  by_cases h8 : Nat.card V ≤ 8
  · have hV2 : IsPGroup 2 V := hP0.to_le ((Subgroup.map_subtype_le _).trans hS₁)
    have hc := le_centralizer_of_card_le hB hV2 h8 hBV
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_iff.mp (hc hb) _ hz0V
  · exfalso
    push Not at h8
    refine not_le_Hj hB fun b hb => QT2.mem_Hj_of_big_inter hF hVE (fun v hv => hVE ?_) h8
    have := (Subgroup.mem_normalizer_iff.mp (hBV (inv_mem hb)) v).mp hv
    rwa [inv_inv] at this

end CFSG.Quasithin.Vol2.Ch11.SecS.J4U
