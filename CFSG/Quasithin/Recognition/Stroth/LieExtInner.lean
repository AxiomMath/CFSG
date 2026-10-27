module

public import CFSG.Quasithin.Recognition.F112WSetup
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Am
public import CFSG.Quasithin.Vol2.Ch5Sec3L532Rig
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Data
public import CFSG.CGT.Timmesfeld75.Sec4TwoBender
public import CFSG.GH74.Uniqueness.SU.KI8Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveDefs
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Quasithin.EmptyFaithful.F112HypW
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.Quasithin.H13 CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.L532
  CFSG.RankThree.LargeReeOrder

private theorem eq_top_of_normal_odd_index_of_simple_quotient
    {L : Type} [Group L] [Finite L] {H : Subgroup L} [H.Normal]
    (hH2 : IsPGroup 2 H) (hsimple : IsSimpleGroup (L ⧸ H))
    (heven : Even (Nat.card (L ⧸ H)))
    {N : Subgroup L} (hN : N.Normal) (hodd : Odd N.index) : N = ⊤ := by
  have hHN : H ≤ N := CFSG.GH74.Uniqueness.SU.K.KI8.le_of_isPGroup_of_odd_index hodd hH2
  have hNbar : (N.map (QuotientGroup.mk' H)).Normal :=
    hN.map (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  have hker : (QuotientGroup.mk' H).ker ≤ N := by
    rw [QuotientGroup.ker_mk']
    exact hHN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' H)) with hbot | htop
  · have hNH : N ≤ H := by
      have := (Subgroup.map_eq_bot_iff N).mp hbot
      rwa [QuotientGroup.ker_mk'] at this
    have hNeq : N = H := le_antisymm hNH hHN
    have hodd' : Odd (Nat.card (L ⧸ H)) := by
      rw [hNeq, Subgroup.index_eq_card] at hodd
      exact hodd
    exact absurd heven (Nat.not_even_iff_odd.mpr hodd')
  · calc N = (N.map (QuotientGroup.mk' H)).comap (QuotientGroup.mk' H) :=
        (Subgroup.comap_map_eq_self hker).symm
      _ = ⊤ := by rw [htop, Subgroup.comap_top]

theorem eq_top_of_normal_odd_index_of_sz
    {L : Type} [Group L] [Finite L] {a : ℕ}
    (ha : 1 ≤ a) (h : Nonempty (oTwoQuot L ≃* Sz a)) :
    ∀ N : Subgroup L, N.Normal → Odd N.index → N = ⊤ := by
  obtain ⟨e⟩ := h
  haveI hsimple : IsSimpleGroup (oTwoQuot L) :=
    e.isSimpleGroup_congr.mpr
      (CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_isSimpleGroup ha)
  have heven : Even (Nat.card (oTwoQuot L)) := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz a]
    have hq : Even ((2 ^ (2 * a + 1)) ^ 2) :=
      (Even.pow_of_ne_zero (by norm_num : Even 2) (by omega)).pow_of_ne_zero (by norm_num)
    exact (hq.mul_right (((2 ^ (2 * a + 1)) ^ 2 + 1))).mul_right (2 ^ (2 * a + 1) - 1)
  intro N hN hodd
  exact eq_top_of_normal_odd_index_of_simple_quotient (pCore_isPGroup (G := L) (p := 2))
    hsimple heven hN hodd

theorem eq_top_of_normal_odd_index_of_isL2Quot {L : Type} [Group L] [Finite L] {f : ℕ}
    (hf : 2 ≤ f) (h : IsL2Quot f (oTwoQuot L)) :
    ∀ N : Subgroup L, N.Normal → Odd N.index → N = ⊤ := by
  obtain ⟨e⟩ := h
  haveI hsimple : IsSimpleGroup (oTwoQuot L) :=
    CFSG.CGT.Timmesfeld75.isSimpleGroup_of_psl2 hf e
  have heven : Even (Nat.card (oTwoQuot L)) := by
    rw [Nat.card_congr e.toEquiv, CFSG.Walter.psl2_even_card (by omega : f ≠ 0)]
    exact (Even.pow_of_ne_zero (by norm_num : Even 2) (by omega)).mul_right _
  intro N hN hodd
  exact eq_top_of_normal_odd_index_of_simple_quotient (pCore_isPGroup (G := L) (p := 2))
    hsimple heven hN hodd

private theorem inf_autStab_inf_eq {D : Type} [Group D] [Finite D]
    {TD P1 P2 : Subgroup D} (hY : IsYAmalgamPair TD P1 P2) :
    ((MulAut.conj : D →* MulAut D).range ⊓ autStab (P1 ⊓ P2)) =
      ((MulAut.conj : D →* MulAut D).range ⊓ autStab P1) ⊓
        ((MulAut.conj : D →* MulAut D).range ⊓ autStab P2) := by
  ext φ
  constructor
  · rintro ⟨hinn, hstab⟩
    obtain ⟨d, rfl⟩ := hinn
    have hd : d ∈ P1 ⊓ P2 := by
      rw [← S1421QA18.normalizer_inf_eq hY]
      exact S1421QA18.conj_mem_autStab_iff.mp hstab
    exact ⟨⟨⟨d, rfl⟩, S1421QA18.conj_mem_autStab_iff.mpr (Subgroup.le_normalizer hd.1)⟩,
      ⟨⟨d, rfl⟩, S1421QA18.conj_mem_autStab_iff.mpr (Subgroup.le_normalizer hd.2)⟩⟩
  · rintro ⟨⟨hinn, hstab1⟩, ⟨-, hstab2⟩⟩
    refine ⟨hinn, fun x => ⟨?_, ?_⟩⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨(hstab1 x).mp hx1, (hstab2 x).mp hx2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨(hstab1 x).mpr hx1, (hstab2 x).mpr hx2⟩

private theorem odd_index_comap {D : Type} [Group D] [Finite D]
    {G : Type} [Group G] [Finite G]
    {M S : Subgroup G} (hSyl : IsSylowTwoOf S M)
    (hZ : Subgroup.center D = ⊥)
    {Mbar : Subgroup (MulAut D)} (hinn : (MulAut.conj : D →* MulAut D).range ≤ Mbar)
    {P TD : Subgroup D}
    (hP : Subgroup.normalizer (P : Set D) = P)
    (hTD : IsSylowTwoOf TD ⊤) (hTDle : TD ≤ P)
    (hcard : ∀ T : Subgroup D, IsSylowTwoOf T ⊤ → Nat.card S = Nat.card T)
    (φ : ↥M ≃* ↥(Mbar ⊓ autStab P))
    (I : Subgroup (MulAut D)) (hI : I = (MulAut.conj : D →* MulAut D).range ⊓ autStab P)
    (K : Subgroup ↥M) (hK : K = (I.subgroupOf (Mbar ⊓ autStab P)).comap φ.toMonoidHom) :
    Odd K.index := by
  classical
  haveI : Finite (MulAut D) := CFSG.Quasithin.H13.F431.finite_mulAut_of_finite
  have hIle : I ≤ Mbar ⊓ autStab P := by
    rw [hI]
    exact inf_le_inf hinn le_rfl
  have hKindex : K.index = (I.subgroupOf (Mbar ⊓ autStab P)).index := by
    rw [hK]
    exact Subgroup.index_comap_of_surjective _ φ.surjective
  have hcardN : Nat.card ↥(Mbar ⊓ autStab P) = Nat.card ↥I * K.index := by
    have h1 := Subgroup.card_mul_index (I.subgroupOf (Mbar ⊓ autStab P))
    have h2 : Nat.card ↥(I.subgroupOf (Mbar ⊓ autStab P)) = Nat.card ↥I :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIle).toEquiv
    rw [h2, ← hKindex] at h1
    exact h1.symm
  have hcardI : Nat.card ↥I = Nat.card ↥P := by
    rw [hI]
    exact (Nat.card_congr (innEquiv hZ hP).toEquiv).symm
  have hcardP : Nat.card ↥P = Nat.card ↥TD * (TD.subgroupOf P).index := by
    have h1 := Subgroup.card_mul_index (TD.subgroupOf P)
    have h2 : Nat.card ↥(TD.subgroupOf P) = Nat.card ↥TD :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTDle).toEquiv
    rw [h2] at h1
    exact h1.symm
  have hcardMS : Nat.card ↥M = Nat.card ↥S * (S.subgroupOf M).index := by
    have h1 := Subgroup.card_mul_index (S.subgroupOf M)
    have h2 : Nat.card ↥(S.subgroupOf M) = Nat.card ↥S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSyl.1).toEquiv
    rw [h2] at h1
    exact h1.symm
  have hoddS : Odd (S.subgroupOf M).index :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSyl.2.2)
  have hrelTD : (TD.subgroupOf P).index * P.index = (TD.subgroupOf ⊤).index := by
    rw [show (TD.subgroupOf P).index = TD.relIndex P from rfl,
      show (TD.subgroupOf ⊤).index = TD.index from Subgroup.relIndex_top_right TD]
    exact Subgroup.relIndex_mul_index hTDle
  have hoddTD : Odd (TD.subgroupOf P).index := by
    refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 => hTD.2.2 ?_)
    exact hrelTD ▸ Dvd.dvd.mul_right h2 P.index
  have hcardSTD : Nat.card ↥S = Nat.card ↥TD := hcard TD hTD
  have hEq : Nat.card ↥S * (S.subgroupOf M).index =
      Nat.card ↥S * ((TD.subgroupOf P).index * K.index) := by
    calc Nat.card ↥S * (S.subgroupOf M).index = Nat.card ↥M := hcardMS.symm
      _ = Nat.card ↥(Mbar ⊓ autStab P) := Nat.card_congr φ.toEquiv
      _ = Nat.card ↥I * K.index := hcardN
      _ = Nat.card ↥P * K.index := by rw [hcardI]
      _ = (Nat.card ↥TD * (TD.subgroupOf P).index) * K.index := by rw [hcardP]
      _ = Nat.card ↥S * ((TD.subgroupOf P).index * K.index) := by
        rw [hcardSTD]
        ring
  have hcancel := Nat.mul_left_cancel (Nat.card_pos (α := ↥S)) hEq
  have hprod : Odd ((TD.subgroupOf P).index * K.index) := hcancel ▸ hoddS
  exact Nat.Odd.of_mul_right hprod

private theorem no_proper_odd_index_of_mulEquiv {X Y : Type} [Group X] [Finite X]
    [Group Y] [Finite Y]
    (e : X ≃* Y) (hX : ∀ N : Subgroup X, N.Normal → Odd N.index → N = ⊤) :
    ∀ N : Subgroup Y, N.Normal → Odd N.index → N = ⊤ := by
  intro N hN hodd
  have hN' : (N.map e.symm.toMonoidHom).Normal := hN.map _ e.symm.surjective
  have hodd' : Odd (N.map e.symm.toMonoidHom).index :=
    (Subgroup.index_map_equiv N e.symm) ▸ hodd
  have htop := hX _ hN' hodd'
  rw [eq_top_iff]
  intro y _
  have hy : e.symm y ∈ N.map e.symm.toMonoidHom := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, hny⟩ := hy
  have hny' : n = y := e.symm.injective hny
  rwa [hny'] at hn

private theorem le_of_odd_index_of_no_proper {M : Type} [Group M] [Finite M]
    {L K : Subgroup M} [K.Normal] (hKodd : Odd K.index)
    (hL : ∀ N : Subgroup ↥L, N.Normal → Odd N.index → N = ⊤) :
    L ≤ K := by
  classical
  let f : ↥L →* M ⧸ K := (QuotientGroup.mk' K).comp L.subtype
  have hfker : f.ker = ⊤ := by
    refine hL f.ker (MonoidHom.normal_ker f) ?_
    rw [Subgroup.index_ker]
    exact hKodd.of_dvd_nat (by
      rw [Subgroup.index_eq_card (H := K)]
      exact Subgroup.card_subgroup_dvd_card f.range)
  intro x hx
  let x' : ↥L := ⟨x, hx⟩
  have hx1 : x' ∈ f.ker := by rw [hfker]; exact Subgroup.mem_top x'
  have hx2 : (QuotientGroup.mk' K) (x : M) = 1 := hx1
  rw [QuotientGroup.mk'_apply] at hx2
  exact (QuotientGroup.eq_one_iff (x : M)).mp hx2

private theorem eq_inf_autStab_left {D : Type} [Group D] [Finite D] {G : Type} [Group G]
    [Finite G] {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hL1 : ∀ N : Subgroup ↥L1, N.Normal → Odd N.index → N = ⊤)
    (hL2 : ∀ N : Subgroup ↥L2, N.Normal → Odd N.index → N = ⊤)
    (hZ : Subgroup.center D = ⊥)
    (hS : ∀ T : Subgroup D, IsSylowTwoOf T ⊤ → Nat.card S = Nat.card T)
    (E : LieExt D (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)) :
    E.Mbar ⊓ autStab E.P1 =
      (MulAut.conj : D →* MulAut D).range ⊓ autStab E.P1 := by
  classical
  let M1 : Subgroup G := L1 ⊔ bigB L1 L2 S
  let M2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hSyl1 : IsSylowTwoOf S M1 := F112W.isSylowTwoOf_parabolic hR
  have hSyl2 : IsSylowTwoOf S M2 := F112W.isSylowTwoOf_parabolic' hR
  have hP1 : Subgroup.normalizer (E.P1 : Set D) = E.P1 :=
    S1421QA18.normalizer_eq_of_isMaximalTwoLocal (S1421QA18.yamPair_left E.yam)
  have hP2 : Subgroup.normalizer (E.P2 : Set D) = E.P2 :=
    S1421QA18.normalizer_eq_of_isMaximalTwoLocal (S1421QA18.yamPair_right E.yam)
  have hTDle_inf : E.TD ≤ E.P1 ⊓ E.P2 :=
    Subgroup.le_normalizer.trans (S1421QA18.yamPair_normalizer_le E.yam)
  have hTDleP1 : E.TD ≤ E.P1 := hTDle_inf.trans inf_le_left
  have hTDleP2 : E.TD ≤ E.P2 := hTDle_inf.trans inf_le_right
  let I1 : Subgroup (MulAut D) := (MulAut.conj : D →* MulAut D).range ⊓ autStab E.P1
  let I2 : Subgroup (MulAut D) := (MulAut.conj : D →* MulAut D).range ⊓ autStab E.P2
  let K1 : Subgroup ↥M1 := (I1.subgroupOf E.N1).comap E.phi1.toMonoidHom
  let K2 : Subgroup ↥M2 := (I2.subgroupOf E.N2).comap E.phi2.toMonoidHom
  have hI1normal : (I1.subgroupOf E.N1).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨(S1421QA18.normal_conj_range).conj_mem n.1 hn.1 g.1,
      (autStab E.P1).mul_mem ((autStab E.P1).mul_mem g.2.2 hn.2) ((autStab E.P1).inv_mem g.2.2)⟩
  have hI2normal : (I2.subgroupOf E.N2).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨(S1421QA18.normal_conj_range).conj_mem n.1 hn.1 g.1,
      (autStab E.P2).mul_mem ((autStab E.P2).mul_mem g.2.2 hn.2) ((autStab E.P2).inv_mem g.2.2)⟩
  have hK1normal : K1.Normal := hI1normal.comap E.phi1.toMonoidHom
  have hK2normal : K2.Normal := hI2normal.comap E.phi2.toMonoidHom
  have hK1odd : Odd K1.index :=
    odd_index_comap hSyl1 hZ E.inn_le hP1 E.yam.1 hTDleP1 hS E.phi1 I1 rfl K1 rfl
  have hK2odd : Odd K2.index :=
    odd_index_comap hSyl2 hZ E.inn_le hP2 E.yam.1 hTDleP2 hS E.phi2 I2 rfl K2 rfl
  have hL1' : ∀ N : Subgroup ↥(L1.subgroupOf M1), N.Normal → Odd N.index → N = ⊤ :=
    no_proper_odd_index_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : L1 ≤ M1)).symm hL1
  have hL2' : ∀ N : Subgroup ↥(L2.subgroupOf M2), N.Normal → Odd N.index → N = ⊤ :=
    no_proper_odd_index_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : L2 ≤ M2)).symm hL2
  have hL1K1 : L1.subgroupOf M1 ≤ K1 :=
    letI : K1.Normal := hK1normal
    le_of_odd_index_of_no_proper hK1odd hL1'
  have hL2K2 : L2.subgroupOf M2 ≤ K2 :=
    letI : K2.Normal := hK2normal
    le_of_odd_index_of_no_proper hK2odd hL2'
  have hSleM1 : S ≤ M1 :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans (le_sup_right : bigB L1 L2 S ≤ M1)
  have hSK1 : S.subgroupOf M1 ≤ K1 :=
    letI : K1.Normal := hK1normal
    CFSG.GH74.Uniqueness.SU.K.KI8.le_of_isPGroup_of_odd_index hK1odd
      (hSyl1.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSleM1).symm)
  have hB1K1 : (borelOf L1 S).subgroupOf M1 ≤ K1 := by
    intro x hx
    exact hL1K1 (Subgroup.mem_subgroupOf.mpr
      ((CFSG.Quasithin.F1.borelOf_le L1 S) (Subgroup.mem_subgroupOf.mp hx)))
  have hB2M1 : borelOf L2 S ≤ M1 :=
    ((le_sup_right : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans
      (le_sup_left : (borelOf L1 S ⊔ borelOf L2 S) ≤
        (borelOf L1 S ⊔ borelOf L2 S) ⊔ S)).trans
      (le_sup_right : ((borelOf L1 S ⊔ borelOf L2 S) ⊔ S) ≤
        L1 ⊔ ((borelOf L1 S ⊔ borelOf L2 S) ⊔ S))
  have hB2M2 : borelOf L2 S ≤ M2 :=
    ((le_sup_right : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans
      (le_sup_left : (borelOf L1 S ⊔ borelOf L2 S) ≤
        (borelOf L1 S ⊔ borelOf L2 S) ⊔ S)).trans
      (le_sup_right : ((borelOf L1 S ⊔ borelOf L2 S) ⊔ S) ≤
        L2 ⊔ ((borelOf L1 S ⊔ borelOf L2 S) ⊔ S))
  have hB2K1 : (borelOf L2 S).subgroupOf M1 ≤ K1 := by
    intro x hx
    have hxL2 : (x : G) ∈ L2 := (CFSG.Quasithin.F1.borelOf_le L2 S) (Subgroup.mem_subgroupOf.mp hx)
    have hxM1 : (x : G) ∈ M1 := hB2M1 (Subgroup.mem_subgroupOf.mp hx)
    have hxM2 : (x : G) ∈ M2 := hB2M2 (Subgroup.mem_subgroupOf.mp hx)
    have hxK2 : (⟨(x : G), hxM2⟩ : ↥M2) ∈ K2 :=
      hL2K2 (Subgroup.mem_subgroupOf.mpr hxL2)
    have hphi2 : (E.phi2 ⟨(x : G), hxM2⟩ : ↥E.N2) ∈ I2.subgroupOf E.N2 := by
      have := hxK2
      change E.phi2 ⟨(x : G), hxM2⟩ ∈ I2.subgroupOf E.N2 at this
      exact Subgroup.mem_comap.mp this
    have hphi2' : ((E.phi2 ⟨(x : G), hxM2⟩ : ↥E.N2) : MulAut D) ∈
        (MulAut.conj : D →* MulAut D).range :=
      (Subgroup.mem_subgroupOf.mp hphi2).1
    have hagree : ((E.phi1 x : ↥E.N1) : MulAut D) =
        ((E.phi2 ⟨(x : G), hxM2⟩ : ↥E.N2) : MulAut D) := by
      let g : ↥(M1 ⊓ M2) := ⟨x.1, hxM1, hxM2⟩
      rw [E.phi1_phi12 g, E.phi2_phi12 g]
    have hphi1 : (E.phi1 x : ↥E.N1) ∈ I1.subgroupOf E.N1 := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hagree ▸ hphi2', (E.phi1 x).2.2⟩
    have hxK1 : x ∈ K1 := by
      change E.phi1 x ∈ I1.subgroupOf E.N1
      exact hphi1
    exact hxK1
  have hB12M1 : borelOf L1 S ⊔ borelOf L2 S ≤ M1 := by
    refine sup_le ?_ ?_
    · exact (CFSG.Quasithin.F1.borelOf_le L1 S).trans (le_sup_left : L1 ≤ M1)
    · exact hB2M1
  have hB12K1 : (borelOf L1 S ⊔ borelOf L2 S).subgroupOf M1 ≤ K1 := by
    rw [Subgroup.subgroupOf_sup
      ((CFSG.Quasithin.F1.borelOf_le L1 S).trans (le_sup_left : L1 ≤ M1)) hB2M1]
    exact sup_le hB1K1 hB2K1
  have hbigBK1 : (bigB L1 L2 S).subgroupOf M1 ≤ K1 := by
    show ((borelOf L1 S ⊔ borelOf L2 S) ⊔ S).subgroupOf M1 ≤ K1
    rw [Subgroup.subgroupOf_sup hB12M1 hSleM1]
    exact sup_le hB12K1 hSK1
  have hM1K1 : L1.subgroupOf M1 ⊔ (bigB L1 L2 S).subgroupOf M1 ≤ K1 :=
    sup_le hL1K1 hbigBK1
  have htop : L1.subgroupOf M1 ⊔ (bigB L1 L2 S).subgroupOf M1 = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : L1 ≤ M1) (le_sup_right : bigB L1 L2 S ≤ M1)]
    exact Subgroup.subgroupOf_self M1
  have hK1top : K1 = ⊤ := eq_top_iff.mpr (htop ▸ hM1K1)
  have hN1le : E.N1 ≤ I1 := by
    intro x hx
    let m : ↥M1 := E.phi1.symm ⟨x, hx⟩
    have hm : m ∈ K1 := by rw [hK1top]; exact Subgroup.mem_top m
    have hx' : E.phi1 m ∈ I1.subgroupOf E.N1 := by
      have := hm
      change E.phi1 m ∈ I1.subgroupOf E.N1 at this
      exact Subgroup.mem_comap.mp this
    rw [Subgroup.mem_subgroupOf] at hx'
    have hmx : E.phi1 m = ⟨x, hx⟩ := E.phi1.apply_symm_apply _
    rw [hmx] at hx'
    exact hx'
  exact le_antisymm hN1le (inf_le_inf E.inn_le le_rfl)

private theorem eq_inf_autStab_right {D : Type} [Group D] [Finite D] {G : Type} [Group G]
    [Finite G] {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hL1 : ∀ N : Subgroup ↥L1, N.Normal → Odd N.index → N = ⊤)
    (hL2 : ∀ N : Subgroup ↥L2, N.Normal → Odd N.index → N = ⊤)
    (hZ : Subgroup.center D = ⊥)
    (hS : ∀ T : Subgroup D, IsSylowTwoOf T ⊤ → Nat.card S = Nat.card T)
    (E : LieExt D (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)) :
    E.Mbar ⊓ autStab E.P2 =
      (MulAut.conj : D →* MulAut D).range ⊓ autStab E.P2 := by
  classical
  let M1 : Subgroup G := L1 ⊔ bigB L1 L2 S
  let M2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hSyl1 : IsSylowTwoOf S M1 := F112W.isSylowTwoOf_parabolic hR
  have hSyl2 : IsSylowTwoOf S M2 := F112W.isSylowTwoOf_parabolic' hR
  have hP1 : Subgroup.normalizer (E.P1 : Set D) = E.P1 :=
    S1421QA18.normalizer_eq_of_isMaximalTwoLocal (S1421QA18.yamPair_left E.yam)
  have hP2 : Subgroup.normalizer (E.P2 : Set D) = E.P2 :=
    S1421QA18.normalizer_eq_of_isMaximalTwoLocal (S1421QA18.yamPair_right E.yam)
  have hTDle_inf : E.TD ≤ E.P1 ⊓ E.P2 :=
    Subgroup.le_normalizer.trans (S1421QA18.yamPair_normalizer_le E.yam)
  have hTDleP1 : E.TD ≤ E.P1 := hTDle_inf.trans inf_le_left
  have hTDleP2 : E.TD ≤ E.P2 := hTDle_inf.trans inf_le_right
  let I1 : Subgroup (MulAut D) := (MulAut.conj : D →* MulAut D).range ⊓ autStab E.P1
  let I2 : Subgroup (MulAut D) := (MulAut.conj : D →* MulAut D).range ⊓ autStab E.P2
  let K1 : Subgroup ↥M1 := (I1.subgroupOf E.N1).comap E.phi1.toMonoidHom
  let K2 : Subgroup ↥M2 := (I2.subgroupOf E.N2).comap E.phi2.toMonoidHom
  have hI1normal : (I1.subgroupOf E.N1).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨(S1421QA18.normal_conj_range).conj_mem n.1 hn.1 g.1,
      (autStab E.P1).mul_mem ((autStab E.P1).mul_mem g.2.2 hn.2) ((autStab E.P1).inv_mem g.2.2)⟩
  have hI2normal : (I2.subgroupOf E.N2).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨(S1421QA18.normal_conj_range).conj_mem n.1 hn.1 g.1,
      (autStab E.P2).mul_mem ((autStab E.P2).mul_mem g.2.2 hn.2) ((autStab E.P2).inv_mem g.2.2)⟩
  have hK1normal : K1.Normal := hI1normal.comap E.phi1.toMonoidHom
  have hK2normal : K2.Normal := hI2normal.comap E.phi2.toMonoidHom
  have hK1odd : Odd K1.index :=
    odd_index_comap hSyl1 hZ E.inn_le hP1 E.yam.1 hTDleP1 hS E.phi1 I1 rfl K1 rfl
  have hK2odd : Odd K2.index :=
    odd_index_comap hSyl2 hZ E.inn_le hP2 E.yam.1 hTDleP2 hS E.phi2 I2 rfl K2 rfl
  have hL1' : ∀ N : Subgroup ↥(L1.subgroupOf M1), N.Normal → Odd N.index → N = ⊤ :=
    no_proper_odd_index_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : L1 ≤ M1)).symm hL1
  have hL2' : ∀ N : Subgroup ↥(L2.subgroupOf M2), N.Normal → Odd N.index → N = ⊤ :=
    no_proper_odd_index_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : L2 ≤ M2)).symm hL2
  have hL1K1 : L1.subgroupOf M1 ≤ K1 :=
    letI : K1.Normal := hK1normal
    le_of_odd_index_of_no_proper hK1odd hL1'
  have hL2K2 : L2.subgroupOf M2 ≤ K2 :=
    letI : K2.Normal := hK2normal
    le_of_odd_index_of_no_proper hK2odd hL2'
  have hSleM2 : S ≤ M2 :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans (le_sup_right : bigB L1 L2 S ≤ M2)
  have hSK2 : S.subgroupOf M2 ≤ K2 :=
    letI : K2.Normal := hK2normal
    CFSG.GH74.Uniqueness.SU.K.KI8.le_of_isPGroup_of_odd_index hK2odd
      (hSyl2.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSleM2).symm)
  have hB2K2 : (borelOf L2 S).subgroupOf M2 ≤ K2 := by
    intro x hx
    exact hL2K2 (Subgroup.mem_subgroupOf.mpr
      ((CFSG.Quasithin.F1.borelOf_le L2 S) (Subgroup.mem_subgroupOf.mp hx)))
  have hB1M2 : borelOf L1 S ≤ M2 :=
    ((le_sup_left : borelOf L1 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans
      (le_sup_left : (borelOf L1 S ⊔ borelOf L2 S) ≤
        (borelOf L1 S ⊔ borelOf L2 S) ⊔ S)).trans
      (le_sup_right : ((borelOf L1 S ⊔ borelOf L2 S) ⊔ S) ≤
        L2 ⊔ ((borelOf L1 S ⊔ borelOf L2 S) ⊔ S))
  have hB1M1 : borelOf L1 S ≤ M1 :=
    ((le_sup_left : borelOf L1 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans
      (le_sup_left : (borelOf L1 S ⊔ borelOf L2 S) ≤
        (borelOf L1 S ⊔ borelOf L2 S) ⊔ S)).trans
      (le_sup_right : ((borelOf L1 S ⊔ borelOf L2 S) ⊔ S) ≤
        L1 ⊔ ((borelOf L1 S ⊔ borelOf L2 S) ⊔ S))
  have hB1K2 : (borelOf L1 S).subgroupOf M2 ≤ K2 := by
    intro x hx
    have hxL1 : (x : G) ∈ L1 := (CFSG.Quasithin.F1.borelOf_le L1 S) (Subgroup.mem_subgroupOf.mp hx)
    have hxM1 : (x : G) ∈ M1 := hB1M1 (Subgroup.mem_subgroupOf.mp hx)
    have hxM2 : (x : G) ∈ M2 := hB1M2 (Subgroup.mem_subgroupOf.mp hx)
    have hxK1 : (⟨(x : G), hxM1⟩ : ↥M1) ∈ K1 :=
      hL1K1 (Subgroup.mem_subgroupOf.mpr hxL1)
    have hphi1 : (E.phi1 ⟨(x : G), hxM1⟩ : ↥E.N1) ∈ I1.subgroupOf E.N1 := by
      have := hxK1
      change E.phi1 ⟨(x : G), hxM1⟩ ∈ I1.subgroupOf E.N1 at this
      exact Subgroup.mem_comap.mp this
    have hphi1' : ((E.phi1 ⟨(x : G), hxM1⟩ : ↥E.N1) : MulAut D) ∈
        (MulAut.conj : D →* MulAut D).range :=
      (Subgroup.mem_subgroupOf.mp hphi1).1
    have hagree : ((E.phi1 ⟨(x : G), hxM1⟩ : ↥E.N1) : MulAut D) =
        ((E.phi2 x : ↥E.N2) : MulAut D) := by
      let g : ↥(M1 ⊓ M2) := ⟨x.1, hxM1, hxM2⟩
      rw [E.phi1_phi12 g, E.phi2_phi12 g]
    have hphi2 : (E.phi2 x : ↥E.N2) ∈ I2.subgroupOf E.N2 := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hagree ▸ hphi1', (E.phi2 x).2.2⟩
    have hxK2 : x ∈ K2 := by
      change E.phi2 x ∈ I2.subgroupOf E.N2
      exact hphi2
    exact hxK2
  have hB12M2 : borelOf L1 S ⊔ borelOf L2 S ≤ M2 := by
    refine sup_le ?_ ?_
    · exact hB1M2
    · exact (CFSG.Quasithin.F1.borelOf_le L2 S).trans (le_sup_left : L2 ≤ M2)
  have hB12K2 : (borelOf L1 S ⊔ borelOf L2 S).subgroupOf M2 ≤ K2 := by
    rw [Subgroup.subgroupOf_sup hB1M2
      ((CFSG.Quasithin.F1.borelOf_le L2 S).trans (le_sup_left : L2 ≤ M2))]
    exact sup_le hB1K2 hB2K2
  have hbigBK2 : (bigB L1 L2 S).subgroupOf M2 ≤ K2 := by
    show ((borelOf L1 S ⊔ borelOf L2 S) ⊔ S).subgroupOf M2 ≤ K2
    rw [Subgroup.subgroupOf_sup hB12M2 hSleM2]
    exact sup_le hB12K2 hSK2
  have hM2K2 : L2.subgroupOf M2 ⊔ (bigB L1 L2 S).subgroupOf M2 ≤ K2 :=
    sup_le hL2K2 hbigBK2
  have htop : L2.subgroupOf M2 ⊔ (bigB L1 L2 S).subgroupOf M2 = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : L2 ≤ M2) (le_sup_right : bigB L1 L2 S ≤ M2)]
    exact Subgroup.subgroupOf_self M2
  have hK2top : K2 = ⊤ := eq_top_iff.mpr (htop ▸ hM2K2)
  have hN2le : E.N2 ≤ I2 := by
    intro x hx
    let m : ↥M2 := E.phi2.symm ⟨x, hx⟩
    have hm : m ∈ K2 := by rw [hK2top]; exact Subgroup.mem_top m
    have hx' : E.phi2 m ∈ I2.subgroupOf E.N2 := by
      have := hm
      change E.phi2 m ∈ I2.subgroupOf E.N2 at this
      exact Subgroup.mem_comap.mp this
    rw [Subgroup.mem_subgroupOf] at hx'
    have hmx : E.phi2 m = ⟨x, hx⟩ := E.phi2.apply_symm_apply _
    rw [hmx] at hx'
    exact hx'
  exact le_antisymm hN2le (inf_le_inf E.inn_le le_rfl)

theorem isYAmalgam_of_isExtensionOfLieAmalgam {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hL1 : ∀ N : Subgroup ↥L1, N.Normal → Odd N.index → N = ⊤)
    (hL2 : ∀ N : Subgroup ↥L2, N.Normal → Odd N.index → N = ⊤)
    {D : Type} [Group D] [Finite D] (hZ : Subgroup.center D = ⊥)
    (hS : ∀ T : Subgroup D, IsSylowTwoOf T ⊤ → Nat.card S = Nat.card T)
    (hE : IsExtensionOfLieAmalgam D (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)) :
    ∃ T : Subgroup D, IsYAmalgam (f112Amalgam L1 L2 S) T := by
  classical
  obtain ⟨E⟩ := isExtensionOfLieAmalgam_iff.mp hE
  have hN1 := eq_inf_autStab_left hF hL1 hL2 hZ hS E
  have hN2 := eq_inf_autStab_right hF hL1 hL2 hZ hS E
  have hP1 : Subgroup.normalizer (E.P1 : Set D) = E.P1 :=
    S1421QA18.normalizer_eq_of_isMaximalTwoLocal (S1421QA18.yamPair_left E.yam)
  have hJ : ((MulAut.conj : D →* MulAut D).range ⊓ autStab (E.P1 ⊓ E.P2)) =
      E.N1 ⊓ E.N2 := by
    change ((MulAut.conj : D →* MulAut D).range ⊓ autStab (E.P1 ⊓ E.P2)) =
      (E.Mbar ⊓ autStab E.P1) ⊓ (E.Mbar ⊓ autStab E.P2)
    rw [hN1, hN2]
    exact inf_autStab_inf_eq E.yam
  let e1 : ↥E.P1 ≃* ↥E.N1 :=
    (innEquiv hZ hP1).trans (MulEquiv.subgroupCongr hN1.symm)
  let e2 : ↥E.P2 ≃* ↥E.N2 :=
    (innEquiv hZ (S1421QA18.normalizer_eq_of_isMaximalTwoLocal
      (S1421QA18.yamPair_right E.yam))).trans (MulEquiv.subgroupCongr hN2.symm)
  let e12 : ↥(E.P1 ⊓ E.P2) ≃* ↥(E.N1 ⊓ E.N2) :=
    (innEquiv hZ (S1421QA18.normalizer_inf_eq E.yam)).trans (MulEquiv.subgroupCongr hJ)
  let hL : (RankTwoAmalgam.ofSubgroups E.P1 E.P2).Iso
      (RankTwoAmalgam.ofSubgroups E.N1 E.N2) :=
    { φ1 := e1
      φ12 := e12
      φ2 := e2
      comm1 := by
        intro g
        apply Subtype.ext
        rfl
      comm2 := by
        intro g
        apply Subtype.ext
        rfl }
  refine ⟨E.TD, E.P1, E.P2, E.yam, ?_⟩
  exact ⟨U42.Am.isoTrans E.iso (U42.Am.isoSymm hL)⟩

section TwistedF4Model


theorem isAmalgamOfGroup_twistedF4_of_ext {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : F112HypW L1 L2 S) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hS : Nat.card S = (2 ^ (2 * a + 1)) ^ 12)
    {D : Type} [Group D] (hD : IsTwistedF4Over (2 * a + 1) D)
    (hE : IsExtensionOfLieAmalgam D (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsTwistedF4Over (2 * a + 1)) := by
  classical
  have hD' : IsLieOverTwo .twistedF4 0 (2 * a + 1) D := by
    rcases hD with ⟨h1, -⟩ | ⟨-, -, hmodel⟩
    · omega
    · exact hmodel
  obtain ⟨a0, K, hKfield, hKfinite, hKchar, ha0, hfa0, hKcard, ⟨eΓ⟩⟩ :=
    CFSG.Quasithin.H13.F431.TwoF4.f4_model_data hD'
  letI : Field K := hKfield
  haveI : Finite K := hKfinite
  have ha0 : a0 = a := by omega
  subst a0
  haveI : Finite D := Finite.of_equiv _ eΓ.symm.toEquiv
  have hZ : Subgroup.center D = ⊥ := by
    have h := Subgroup.map_center_eq eΓ
    rw [CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial a K hKcard] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ eΓ.injective).mp h
  have hord : Nat.card D = ordTwistedF4 (2 ^ (2 * a + 1)) := by
    have hΓ := (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hKcard).1
    rw [Nat.card_congr eΓ.toEquiv, hΓ, ordTwistedF4]
    set q := 2 ^ (2 * a + 1) with hq
    have h1 : 1 ≤ q := Nat.one_le_two_pow
    have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    have h3 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2, h3, h4]
    ring
  have hprof := CFSG.Timmesfeld.Orders.profile_ordTwistedF4 (f := 2 * a + 1) (by omega)
  obtain ⟨r, hr, hfac⟩ := hprof.two
  have hTcard : ∀ T : Subgroup D, IsSylowTwoOf T ⊤ → Nat.card T = (2 ^ (2 * a + 1)) ^ 12 := by
    intro T hT
    have hDfac : Nat.card D = 2 ^ ((2 * a + 1) * 12) * r := by
      rw [hord, hfac]
    have := CFSG.Quasithin.H13.FiveNorm.card_eq_of_isSylowTwoOf_top (W := D) hT hDfac
      hr.not_two_dvd_nat
    rwa [pow_mul] at this
  have hL1' := eq_top_of_normal_odd_index_of_sz ha hSz
  have hL2' := eq_top_of_normal_odd_index_of_isL2Quot (by omega : 2 ≤ 2 * a + 1) hL2
  have hS' : ∀ T : Subgroup D, IsSylowTwoOf T ⊤ → Nat.card S = Nat.card T :=
    fun T hT => hS.trans (hTcard T hT).symm
  obtain ⟨T, hT⟩ := isYAmalgam_of_isExtensionOfLieAmalgam hF hL1' hL2' hZ hS' hE
  exact ⟨D, inferInstance, hD, T, hT⟩

end TwistedF4Model

end CFSG.Quasithin.Stroth
