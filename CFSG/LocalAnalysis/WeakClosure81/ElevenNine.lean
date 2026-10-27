module

public import CFSG.LocalAnalysis.WeakClosure81.Eleven
public import CFSG.CGT.PushingUpLit.ThmOne.Basic
public import CFSG.CGT.PushingUpLit.CGT6.EmbEightFive
public import CFSG.CGT.PushingUpLit.Glue.SixSixteenRel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourRank1
public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightSLNat
public import CFSG.LocalAnalysis.WeakClosure81.ElevenNineSL2
public import CFSG.CGT.PushingUpLit.Glue.NineContentGlue
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Gen
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.Quasithin.Background.A1GaschutzNorm
public import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open Matrix
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)
open CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.SL2Modules

variable {G : Type} [Group G] [Finite G]

@[expose] def IsLTwoBlockType (L : Subgroup G) (n : ℕ) : Prop :=
  1 < n ∧ IsNaturalSLTwoModule ↥L n ∧ ¬ ∃ m : ℕ, 1 ≤ m ∧ IsNaturalAltModule ↥L m

private theorem eleven_nine_sylowQ_centralizer {M V Q U : Subgroup G} (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V) :
    CFSG.RankThree.PartOne.IsSylowOf 2 Q (Subgroup.centralizer (U : Set G)) :=
  eleven_two_sylow hset.isElemAbelian hset.V_le_M hset.uniqueMax hset.sylowQ hU

theorem eleven_nine_oTwoIn_le_Q {M V Q U L : Subgroup G} (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) :
    oTwoIn L ≤ Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := Subgroup.centralizer (U : Set G) with hH
  have hQH : Q ≤ H := (hset.sylowQ.1.trans inf_le_right).trans (Subgroup.centralizer_le hU.1)
  have hQsyl : CFSG.RankThree.PartOne.IsSylowOf 2 Q H :=
    eleven_nine_sylowQ_centralizer hset hU
  obtain ⟨T', hT'⟩ := sylow_of_isSylowOf hQsyl
  have hpc : (pCore 2 ↥H) ≤ (T' : Subgroup ↥H) := by
    haveI : (pCore 2 ↥H).Normal := pCore_normal
    exact IsPGroup.le_sylow_of_normal pCore_isPGroup T'
  have hoTwoH : oTwoIn H ≤ Q := by
    calc oTwoIn H = (pCore 2 ↥H).map H.subtype := oTwoIn_eq_map H
      _ ≤ (T' : Subgroup ↥H).map H.subtype := Subgroup.map_mono hpc
      _ = Q := by rw [hT', Subgroup.map_subgroupOf_eq_of_le hQH]
  exact (CGT6.oTwoIn_le_of_isSubnormal hL.1 hL.2.1).trans hoTwoH

private theorem eleven_nine_V_le_centralizer {M V Q U : Subgroup G} (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V) :
    V ≤ Subgroup.centralizer (U : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (B2F.isElemAbelian_comm hset.isElemAbelian hv (hU.1 hu)).symm

private theorem eleven_nine_oTwoIn_centralizer_le_Q {M V Q U : Subgroup G}
    (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V) :
    oTwoIn (Subgroup.centralizer (U : Set G)) ≤ Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := Subgroup.centralizer (U : Set G) with hH
  have hQH : Q ≤ H := (hset.sylowQ.1.trans inf_le_right).trans (Subgroup.centralizer_le hU.1)
  obtain ⟨T', hT'⟩ := sylow_of_isSylowOf (eleven_nine_sylowQ_centralizer hset hU)
  have hpc : (pCore 2 ↥H) ≤ (T' : Subgroup ↥H) := by
    haveI : (pCore 2 ↥H).Normal := pCore_normal
    exact IsPGroup.le_sylow_of_normal pCore_isPGroup T'
  calc oTwoIn H = (pCore 2 ↥H).map H.subtype := oTwoIn_eq_map H
    _ ≤ (T' : Subgroup ↥H).map H.subtype := Subgroup.map_mono hpc
    _ = Q := by rw [hT', Subgroup.map_subgroupOf_eq_of_le hQH]

theorem eleven_nine_V_le_Q {M V Q U : Subgroup G} (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V) :
    V ≤ Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hset.isElemAbelian
  have hQ2 : IsPGroup 2 Q := hset.sylowQ.2.1
  have hQCV : Q ≤ Subgroup.centralizer (V : Set G) := hset.sylowQ.1.trans inf_le_right
  have hVcQ : V ≤ Subgroup.centralizer (Q : Set G) := eleven_a hQCV
  have hVcV : V ≤ Subgroup.centralizer (V : Set G) := fun v hv => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (B2F.isElemAbelian_comm hset.isElemAbelian hv hw).symm
  have hP2 : IsPGroup 2 ↥(Q ⊔ V) :=
    hQ2.to_sup_of_normal_left' hV2 (hVcQ.trans (Subgroup.centralizer_le_normalizer _))
  have hPK : Q ⊔ V ≤ M ⊓ Subgroup.centralizer (V : Set G) :=
    sup_le (le_inf (hset.sylowQ.1.trans inf_le_left) hQCV)
      (le_inf hset.V_le_M hVcV)
  have heq := eq_of_isSylowOf_of_isPGroup_le hset.sylowQ le_sup_left hPK hP2
  exact le_sup_right.trans_eq heq

private theorem eleven_nine_conjugate_iSup {ι : Sort*} (A : ι → Subgroup G) (g : G) :
    conjugate (⨆ i, A i) g = ⨆ i, conjugate (A i) g := by
  simp only [conjugate]
  rw [Subgroup.map_iSup]

theorem eleven_nine_mem_normalizer_of_conjugate_eq {H : Subgroup G} {g : G}
    (h : conjugate H g = H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [← ThreeFromEight.mem_conjugate_iff, h]

private def eleven_nineX (Q L : Subgroup G) : Subgroup G := ⨆ q : Q, conjugate L (q : G)

private def eleven_nineK (Q L : Subgroup G) : Subgroup G := eleven_nineX Q L ⊔ Q

private theorem eleven_nine_L_le_X (Q L : Subgroup G) : L ≤ eleven_nineX Q L := by
  have h1 : conjugate L (1 : G) = L := by
    ext x
    simp [conjugate, MulAut.conj_apply]
  rw [eleven_nineX]
  have h := le_iSup (fun q : Q => conjugate L (q : G)) (⟨1, one_mem Q⟩ : Q)
  rwa [h1] at h

private theorem eleven_nine_X_le {H Q L : Subgroup G}
    (h : ∀ q : Q, conjugate L (q : G) ≤ H) : eleven_nineX Q L ≤ H := by
  rw [eleven_nineX]
  exact iSup_le h

private theorem eleven_nine_conjugate_X (Q L : Subgroup G) {g : G} (hg : g ∈ Q) :
    conjugate (eleven_nineX Q L) g = eleven_nineX Q L := by
  rw [eleven_nineX, eleven_nine_conjugate_iSup]
  apply le_antisymm
  · refine iSup_le fun q => ?_
    rw [CFSG.GroupTheory.conjugate_conjugate]
    exact le_iSup (fun q : Q => conjugate L (q : G)) ⟨(q : G) * g, Q.mul_mem q.2 hg⟩
  · refine iSup_le fun q => ?_
    have h := le_iSup (fun q' : Q => conjugate (conjugate L (q' : G)) g)
      (⟨(q : G) * g⁻¹, Q.mul_mem q.2 (Q.inv_mem hg)⟩ : Q)
    rw [CFSG.GroupTheory.conjugate_conjugate] at h
    simpa [mul_assoc] using h

private theorem eleven_nine_Q_le_normalizer_X (Q L : Subgroup G) :
    Q ≤ Subgroup.normalizer (eleven_nineX Q L : Set G) :=
  fun g hg => eleven_nine_mem_normalizer_of_conjugate_eq (eleven_nine_conjugate_X Q L hg)

private theorem eleven_nine_X_normal_K (Q L : Subgroup G) :
    ((eleven_nineX Q L).subgroupOf (eleven_nineX Q L ⊔ Q)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  exact sup_le Subgroup.le_normalizer (eleven_nine_Q_le_normalizer_X Q L)

private theorem eleven_nine_isSylowOf_of_le {Q H K : Subgroup G}
    (hQ : CFSG.RankThree.PartOne.IsSylowOf 2 Q H) (hQK : Q ≤ K) (hKH : K ≤ H) :
    CFSG.RankThree.PartOne.IsSylowOf 2 Q K := by
  refine ⟨hQK, hQ.2.1, ?_⟩
  intro h2
  have hd : 2 ∣ Q.relIndex K * K.relIndex H := dvd_mul_of_dvd_left h2 _
  exact hQ.2.2 (Subgroup.relIndex_mul_relIndex Q K H hQK hKH ▸ hd)

private theorem eleven_nine_isCharacteristicP_of_le {H K : Subgroup G} (hKH : K ≤ H)
    (hHchar : IsCharacteristicP 2 ↥H) (hO : oTwoIn H ≤ K) :
    IsCharacteristicP 2 ↥K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K' : Subgroup ↥H := K.subgroupOf H
  have hK'char : IsCharacteristicP 2 ↥K' := by
    change Subgroup.centralizer (pCore 2 ↥K' : Set ↥K') ≤ pCore 2 ↥K'
    have hP : ((pCore 2 ↥H).subgroupOf K') ≤ pCore 2 ↥K' := by
      refine le_sSup ⟨inferInstance, ?_⟩
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).comap_of_injective K'.subtype
        K'.subtype_injective
    intro x hx
    apply hP
    rw [Subgroup.mem_subgroupOf]
    refine hHchar ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyK : H.subtype y ∈ K := hO (Subgroup.mem_map_of_mem H.subtype hy)
    have hy' : (⟨y, hyK⟩ : ↥K') ∈ (pCore 2 ↥H).subgroupOf K' :=
      Subgroup.mem_subgroupOf.mpr hy
    have hc := Subgroup.mem_centralizer_iff.mp hx ⟨y, hyK⟩ (hP hy')
    simpa using congrArg (fun z : ↥K' => (z : ↥H)) hc
  exact T2K.isCharacteristicP_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hKH) hK'char

private theorem eleven_nine_conjSub_eq_conjugate {X : Type*} [Group X] (H : Subgroup X) (g : X) :
    A1b.conjSub g H = conjugate H g⁻¹ := by
  ext x
  simp [A1b.conjSub, conjugate, MulAut.conj_apply]

private theorem eleven_nine_conjugate_one (L : Subgroup G) : conjugate L (1 : G) = L := by
  ext x
  simp [conjugate, MulAut.conj_apply]

private theorem eleven_nine_K_pow_mem_X (Q L : Subgroup G) (hQ2 : IsPGroup 2 Q) :
    ∀ g ∈ eleven_nineK Q L, ∃ k : ℕ, g ^ 2 ^ k ∈ eleven_nineX Q L := by
  intro g hg
  refine SubTwo.exists_pow_mem_of_decomp (Y := eleven_nineX Q L)
    (B := eleven_nineK Q L) (P := Q) ?_ hQ2 ?_ g hg
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp
      (eleven_nine_X_normal_K Q L)
  · intro b hb
    have hb' : b ∈ Q ⊔ eleven_nineX Q L := by
      rw [sup_comm]; exact hb
    have hb'' : b ∈ (Q : Set G) * (eleven_nineX Q L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Q (eleven_nineX Q L)
        (eleven_nine_Q_le_normalizer_X Q L)]
      exact hb'
    obtain ⟨q, hq, x, hx, hqxb⟩ := hb''
    refine ⟨q * x * q⁻¹, ?_, q, hq, (le_sup_right : Q ≤ eleven_nineX Q L ⊔ Q) hq, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (eleven_nine_Q_le_normalizer_X Q L hq) x).1 hx
    · rw [← hqxb]; group

private theorem eleven_nine_K_core_bound {M V Q U L : Subgroup G} (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V) (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) :
    ∀ T : Sylow 2 ↥(eleven_nineK Q L),
      (T : Subgroup ↥(eleven_nineK Q L)) = Q.subgroupOf (eleven_nineK Q L) →
      characteristicCoreStar (T : Subgroup ↥(eleven_nineK Q L)) ≤
        M.subgroupOf (eleven_nineK Q L) := by
  intro T hT
  have hQ2 : IsPGroup 2 Q := hset.sylowQ.2.1
  have hQne : Q ≠ ⊥ := fun hbot =>
    hset.V_ne_bot (le_bot_iff.1 ((eleven_nine_V_le_Q hset hU).trans hbot.le))
  have hC : Subgroup.centralizer (omegaOneCenterIn Q : Set G) ⊓ (eleven_nineK Q L) ≤ M := by
    refine (inf_le_left.trans
      (Subgroup.centralizer_le_normalizer (omegaOneCenterIn Q : Set G))).trans ?_
    haveI : ((omegaOneCenterIn Q).subgroupOf Q).Characteristic :=
      characteristic_omegaOneCenterIn Q
    have hω0 : omegaOneCenterIn Q ≠ ⊥ := omegaOneCenterIn_ne_bot hQ2 hQne
    have hω2 : IsPGroup 2 (omegaOneCenterIn Q) := hQ2.to_le (omegaOneCenterIn_le Q)
    have hN : Subgroup.normalizer (Q : Set G) ⊓ M ≤
        Subgroup.normalizer (omegaOneCenterIn Q : Set G) := by
      refine inf_le_left.trans ?_
      have hmap : ((omegaOneCenterIn Q).subgroupOf Q).map Q.subtype = omegaOneCenterIn Q :=
        Subgroup.map_subgroupOf_eq_of_le (omegaOneCenterIn_le Q)
      have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        ((omegaOneCenterIn Q).subgroupOf Q)
      rwa [hmap] at h
    exact eleven_b hset.uniqueMax hω0 hω2 hN
  have hN : ∀ B : Subgroup G, B ≠ ⊥ → B ≤ pushingUpS Q →
      (B.subgroupOf (pushingUpS Q)).Characteristic →
      Subgroup.normalizer (B : Set G) ⊓ (eleven_nineK Q L) ≤ M := by
    intro B hB0 hBS hBc
    refine inf_le_left.trans ?_
    have hBQ : B ≤ Q := hBS.trans (inf_le_left : pushingUpS Q ≤ Q)
    have h1 : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (pushingUpS Q : Set G) := by
      haveI : ((pushingUpS Q).subgroupOf Q).Characteristic := characteristic_pushingUpS Q
      have hmap : ((pushingUpS Q).subgroupOf Q).map Q.subtype = pushingUpS Q :=
        Subgroup.map_subgroupOf_eq_of_le (inf_le_left : pushingUpS Q ≤ Q)
      have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        ((pushingUpS Q).subgroupOf Q)
      rwa [hmap] at h
    have h2 : Subgroup.normalizer (pushingUpS Q : Set G) ≤
        Subgroup.normalizer (B : Set G) := by
      haveI : (B.subgroupOf (pushingUpS Q)).Characteristic := hBc
      have hmap : (B.subgroupOf (pushingUpS Q)).map (pushingUpS Q).subtype = B :=
        Subgroup.map_subgroupOf_eq_of_le hBS
      have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (B.subgroupOf (pushingUpS Q))
      rwa [hmap] at h
    exact eleven_b hset.uniqueMax hB0 (hQ2.to_le hBQ) ((inf_le_left.trans h1).trans h2)
  exact Glue.characteristicCoreStar_subgroupOf_le T hT le_sup_right hC hN

theorem eleven_nine_V_le_centralizerModCore {M V Q U L : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (h78 : IsLTwoBlockType L n) :
    V ≤ centralizerModCore L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHchar : IsCharacteristicP 2 ↥(Subgroup.centralizer (U : Set G)) :=
    eleven_e hset.charTwo hU.2.1
      ((B2F.isPGroup_of_isElemAbelian hset.isElemAbelian).to_le hU.1)
  have hVcQ : V ≤ Subgroup.centralizer (Q : Set G) :=
    eleven_a (hset.sylowQ.1.trans inf_le_right)
  have hblockQ : blockU L ≤ Q :=
    (blockU_le_oTwoIn L).trans (eleven_nine_oTwoIn_le_Q hset hU hL)
  have hVcent : V ≤ Subgroup.centralizer (blockU L : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_iff.mp (hVcQ hv) u (hblockQ hu)
  have hVNL : V ≤ Subgroup.normalizer (L : Set G) := by
    have hVinf : V ≤ Subgroup.centralizer (U : Set G) ⊓
        Subgroup.normalizer (blockU L : Set G) :=
      le_inf (eleven_nine_V_le_centralizer hset hU)
        (hVcent.trans (Subgroup.centralizer_le_normalizer _))
    exact hVinf.trans (ThmOne.inf_normalizer_blockU_le_normalizer hHchar hL)
  intro v hv
  rw [mem_centralizerModCore_iff]
  refine ⟨hVNL hv, ?_⟩
  intro l hl
  set a : G := v * l * v⁻¹ with ha
  set y : G := a * l⁻¹ with hy
  have hvN := hVNL hv
  have hvl : v * l * v⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hvN l).1 hl
  have hyL : y ∈ L := by rw [hy, ha]; exact L.mul_mem hvl (L.inv_mem hl)
  have hact : ∀ w ∈ blockU L, a * w * a⁻¹ = l * w * l⁻¹ := by
    intro w hw
    have hvw : v⁻¹ * w * v = w := by
      have hc := Subgroup.mem_centralizer_iff.mp (hVcent hv) w hw
      calc v⁻¹ * w * v = v⁻¹ * (w * v) := by group
        _ = v⁻¹ * (v * w) := by rw [hc]
        _ = w := by group
    have hconj1 : v⁻¹ * w * v ∈ blockU L := by rw [hvw]; exact hw
    have hconj2 : l * (v⁻¹ * w * v) * l⁻¹ ∈ blockU L :=
      conj_mem_blockU (Subgroup.le_normalizer hl) hconj1
    calc a * w * a⁻¹ = v * (l * (v⁻¹ * w * v) * l⁻¹) * v⁻¹ := by rw [ha]; group
      _ = l * (v⁻¹ * w * v) * l⁻¹ := by
        have hc := Subgroup.mem_centralizer_iff.mp (hVcent hv) _ hconj2
        rw [← hc]; group
      _ = l * w * l⁻¹ := by rw [hvw]
  have hcent : y ∈ Subgroup.centralizer (blockU L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hlu : l⁻¹ * u * l ∈ blockU L := by
      simpa using conj_mem_blockU (Subgroup.le_normalizer (L.inv_mem hl)) hu
    have hyu : y * u * y⁻¹ = u := by
      calc y * u * y⁻¹ = a * (l⁻¹ * u * l) * a⁻¹ := by rw [hy, ha]; group
        _ = l * (l⁻¹ * u * l) * l⁻¹ := hact _ hlu
        _ = u := by group
    calc u * y = (y * u * y⁻¹) * y := by rw [hyu]
      _ = y * u := by group
  have hC := CGT6.inf_centralizer_blockU_eq_SL hL.2.2.1 h78.2.1
  rw [← hC]
  exact Subgroup.mem_inf.mpr ⟨hyL, hcent⟩

theorem eleven_nine_one {M V Q U L : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) :
    (CFSG.RankThree.PartOne.IsSylowOf 2 (L ⊓ Q) L ∧
      L ⊓ M = L ⊓ Subgroup.normalizer ((L ⊓ Q : Subgroup G) : Set G)) ∧
    ∃ S : Sylow 2 (↥L ⧸ CFSG.pCore 2 ↥L),
      ((L ⊓ M).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
        Subgroup.normalizer ((S : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
          Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := Subgroup.centralizer (U : Set G) with hH
  have hQH : Q ≤ H := (hset.sylowQ.1.trans inf_le_right).trans (Subgroup.centralizer_le hU.1)
  have hQH_syl : CFSG.RankThree.PartOne.IsSylowOf 2 Q H :=
    eleven_nine_sylowQ_centralizer hset hU
  have hSa : CFSG.RankThree.PartOne.IsSylowOf 2 (L ⊓ Q) L := by
    obtain ⟨TH, hTH⟩ := sylow_of_isSylowOf hQH_syl
    have hTs : CFSG.RankThree.PartOne.IsSylowOf 2 (Q.subgroupOf H) ⊤ := by
      rw [← hTH]; exact CFSG.CGT.PushingUpLit.Glue.isSylowOf_top TH
    have hinf := CFSG.CGT.PushingUpLit.Glue.isSylowOf_inf_of_isSubnormal hTs hL.2.1
    have hsub : (L ⊓ Q).subgroupOf H = (Q.subgroupOf H) ⊓ (L.subgroupOf H) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      tauto
    rw [← hsub] at hinf
    have hiff : CFSG.RankThree.PartOne.IsSylowOf 2 ((L ⊓ Q).subgroupOf H)
        (L.subgroupOf H) ↔ CFSG.RankThree.PartOne.IsSylowOf 2 (L ⊓ Q) L :=
      Glue.isSylowOf_subgroupOf_iff' (inf_le_right.trans hQH) hL.1
    exact hiff.mp hinf
  have hXH : eleven_nineX Q L ≤ H :=
    eleven_nine_X_le fun q => (isBlockOfInX_conjugate hL (hQH q.2)).1
  have hKH : eleven_nineK Q L ≤ H := sup_le hXH hQH
  have hHchar : IsCharacteristicP 2 ↥H :=
    eleven_e hset.charTwo hU.2.1
      ((B2F.isPGroup_of_isElemAbelian hset.isElemAbelian).to_le hU.1)
  have hQleK : Q ≤ eleven_nineK Q L := le_sup_right
  have hKchar : IsCharacteristicP 2 ↥(eleven_nineK Q L) :=
    eleven_nine_isCharacteristicP_of_le hKH hHchar
      ((eleven_nine_oTwoIn_centralizer_le_Q hset hU).trans hQleK)
  have hLsylK : CFSG.RankThree.PartOne.IsSylowOf 2 Q (eleven_nineK Q L) :=
    eleven_nine_isSylowOf_of_le hQH_syl hQleK hKH
  have hLK : L ≤ eleven_nineK Q L := (eleven_nine_L_le_X Q L).trans le_sup_left
  have hLBlockK : IsBlockOfInX (eleven_nineK Q L) L :=
    ⟨hLK, isSubnormal_subgroupOf_mono hLK hKH hL.2.1, hL.2.2⟩
  obtain ⟨TK, hTK⟩ := sylow_of_isSylowOf hLsylK
  have hcc : characteristicCoreStar (TK : Subgroup ↥(eleven_nineK Q L)) ≤
      M.subgroupOf (eleven_nineK Q L) :=
    eleven_nine_K_core_bound hset hU hL TK hTK
  have hch : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup ↥(eleven_nineK Q L)) :=
    CFSG.CGT.PushingUpLit.Glue.charTwo_top_of_isCharacteristicP hKchar
  have hTs : CFSG.RankThree.PartOne.IsSylowOf 2
      (TK : Subgroup ↥(eleven_nineK Q L)) ⊤ :=
    CFSG.CGT.PushingUpLit.Glue.isSylowOf_top TK
  have hCstar_ne : BHS.cStarIn (⊤ : Subgroup ↥(eleven_nineK Q L))
      (TK : Subgroup ↥(eleven_nineK Q L)) ≠ ⊤ := by
    intro htop
    have hcc' : characteristicCoreStar (TK : Subgroup ↥(eleven_nineK Q L)) = ⊤ := by
      rw [CFSG.CGT.PushingUpLit.Glue.characteristicCoreStar_eq_cStarIn]
      exact htop
    have hMK : M.subgroupOf (eleven_nineK Q L) = ⊤ := top_le_iff.mp (hcc' ▸ hcc)
    have hKM : eleven_nineK Q L ≤ M := fun x hx => by
      have hxM : (⟨x, hx⟩ : ↥(eleven_nineK Q L)) ∈ M.subgroupOf (eleven_nineK Q L) := by
        rw [hMK]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hxM
    exact hLM (hLK.trans hKM)
  obtain ⟨𝒢, hB, hinv, hcomm, hgen, hd, he, hlast⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved (↥(eleven_nineK Q L)) ⊤
      (TK : Subgroup ↥(eleven_nineK Q L)) hch hTs hCstar_ne
  have hinv' : ∀ E ∈ 𝒢, ∀ g : ↥(eleven_nineK Q L), A1b.conjSub g E ∈ 𝒢 :=
    fun E hE g => hinv E hE g (Subgroup.mem_top g)
  have h𝒢ne : 𝒢.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    refine hCstar_ne ?_
    have h := hgen
    rw [hemp] at h
    simpa using h
  obtain ⟨E, hE⟩ := h𝒢ne
  have hEsub : E.IsSubnormal :=
    CFSG.CGT.PushingUpLit.Glue.isSubnormal_of_mem_family hinv' hcomm hE
  have hEchar : CFSG.QuasithinUnique.CharTwo E :=
    CFSG.CGT.PushingUpLit.Glue.charTwo_of_isSubnormal_top hch hEsub
  have hEX : InClassX ↥E :=
    CFSG.CGT.PushingUpLit.Glue.inClassX_of_isBTBlock (hB E hE) hEchar
  have hEmapX : InClassX ↥(E.map (eleven_nineK Q L).subtype) :=
    InClassX.of_mulEquiv (E.equivMapOfInjective (eleven_nineK Q L).subtype
      (eleven_nineK Q L).subtype_injective) hEX
  have hEmap_le_K : E.map (eleven_nineK Q L).subtype ≤ eleven_nineK Q L :=
    Subgroup.map_subtype_le E
  have hEmapBlockK : IsBlockOfInX (eleven_nineK Q L) (E.map (eleven_nineK Q L).subtype) :=
    ⟨hEmap_le_K, by
      change (Subgroup.comap (eleven_nineK Q L).subtype
        (E.map (eleven_nineK Q L).subtype)).IsSubnormal
      rw [Subgroup.comap_map_eq_self_of_injective (eleven_nineK Q L).subtype_injective E]
      exact hEsub, hEmapX⟩
  have hKnormX : eleven_nineK Q L ≤
      Subgroup.normalizer (eleven_nineX Q L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp
      (eleven_nine_X_normal_K Q L)
  have hKpowX : ∀ g ∈ eleven_nineK Q L, ∃ k : ℕ, g ^ 2 ^ k ∈ eleven_nineX Q L :=
    eleven_nine_K_pow_mem_X Q L hset.sylowQ.2.1
  have hEmap_le_X : E.map (eleven_nineK Q L).subtype ≤ eleven_nineX Q L := by
    refine noTwoQuot_of_short hEmapX.1 (eleven_nineX Q L) (fun g hg n hn => ?_)
      (fun g hg => hKpowX g (hEmap_le_K hg))
    exact (Subgroup.mem_normalizer_iff.mp (hKnormX (hEmap_le_K hg)) n).1 hn
  have hex : ∃ q : Q, E.map (eleven_nineK Q L).subtype = conjugate L (q : G) := by
    by_contra hall
    push Not at hall
    have hXcent : eleven_nineX Q L ≤
        Subgroup.centralizer (E.map (eleven_nineK Q L).subtype : Set G) := by
      rw [eleven_nineX]
      refine iSup_le fun q => ?_
      have hcommq : ⁅E.map (eleven_nineK Q L).subtype, conjugate L (q : G)⁆ = ⊥ :=
        distinct_blocks_commute_of_isBlockOfInX hKchar hEmapBlockK
          (isBlockOfInX_conjugate hLBlockK (hQleK q.2)) (hall q)
      rw [Subgroup.commutator_comm] at hcommq
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommq
    have hb : ⁅E.map (eleven_nineK Q L).subtype,
        E.map (eleven_nineK Q L).subtype⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hEmap_le_X.trans hXcent
    exact InClassX.commutator_ne_bot hEmapX hb
  obtain ⟨q, hq⟩ := hex
  have hLsubK_mem : L.subgroupOf (eleven_nineK Q L) ∈ 𝒢 := by
    have hEq : E = (conjugate L (q : G)).subgroupOf (eleven_nineK Q L) := by
      rw [← hq]
      change E = Subgroup.comap (eleven_nineK Q L).subtype
        (E.map (eleven_nineK Q L).subtype)
      rw [Subgroup.comap_map_eq_self_of_injective (eleven_nineK Q L).subtype_injective E]
    have hconj_eq : A1b.conjSub (⟨q, hQleK q.2⟩ : ↥(eleven_nineK Q L)) E =
        L.subgroupOf (eleven_nineK Q L) := by
      rw [hEq, eleven_nine_conjSub_eq_conjugate]
      rw [CFSG.GroupTheory.conjugate_subgroupOf, CFSG.GroupTheory.conjugate_conjugate]
      simp [eleven_nine_conjugate_one]
    have hmem : A1b.conjSub (⟨q, hQleK q.2⟩ : ↥(eleven_nineK Q L)) E ∈ 𝒢 :=
      hinv E hE (⟨q, hQleK q.2⟩ : ↥(eleven_nineK Q L)) (Subgroup.mem_top _)
    rwa [hconj_eq] at hmem
  have hlin : L ⊓ Subgroup.normalizer ((L ⊓ Q : Subgroup G) : Set G) ≤ M := by
    rcases hlast (L.subgroupOf (eleven_nineK Q L)) hLsubK_mem with
      ⟨⟨n', -, -⟩, hceq⟩ | ⟨m, hm1, halt, -⟩
    · have hCstar_le : BHS.cStarIn (⊤ : Subgroup ↥(eleven_nineK Q L))
          (TK : Subgroup ↥(eleven_nineK Q L)) ≤ M.subgroupOf (eleven_nineK Q L) := by
        rw [← CFSG.CGT.PushingUpLit.Glue.characteristicCoreStar_eq_cStarIn]
        exact hcc
      have hnorm_le : Subgroup.normalizer
          ((TK : Subgroup ↥(eleven_nineK Q L)) ⊓
            L.subgroupOf (eleven_nineK Q L)) ⊓
          L.subgroupOf (eleven_nineK Q L) ≤ M.subgroupOf (eleven_nineK Q L) :=
        (le_of_eq hceq.symm).trans (inf_le_left.trans hCstar_le)
      intro x hx
      obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp hx
      have hxK : x ∈ eleven_nineK Q L := hLK hxL
      have hxE : (⟨x, hxK⟩ : ↥(eleven_nineK Q L)) ∈ L.subgroupOf (eleven_nineK Q L) :=
        Subgroup.mem_subgroupOf.mpr hxL
      have hxN'' : x ∈ Subgroup.normalizer ((Q ⊓ L : Subgroup G) : Set G) := by
        rw [inf_comm]; exact hxN
      have hxN' : (⟨x, hxK⟩ : ↥(eleven_nineK Q L)) ∈
          Subgroup.normalizer ((TK : Subgroup ↥(eleven_nineK Q L)) ⊓
            L.subgroupOf (eleven_nineK Q L)) := by
        have hsub : (TK : Subgroup ↥(eleven_nineK Q L)) ⊓
            L.subgroupOf (eleven_nineK Q L) = (Q ⊓ L).subgroupOf (eleven_nineK Q L) := by
          rw [hTK]
          ext y
          simp [Subgroup.mem_subgroupOf, and_comm]
        have hmem : (⟨x, hxK⟩ : ↥(eleven_nineK Q L)) ∈
            Subgroup.normalizer ((Q ⊓ L).subgroupOf (eleven_nineK Q L)) := by
          rw [← Subgroup.subgroupOf_normalizer_eq (H := Q ⊓ L) (N := eleven_nineK Q L)
            (inf_le_left.trans hQleK)]
          exact Subgroup.mem_subgroupOf.mpr hxN''
        rwa [← hsub] at hmem
      exact Subgroup.mem_subgroupOf.mp (hnorm_le (Subgroup.mem_inf.mpr ⟨hxN', hxE⟩))
    · exact absurd ⟨m, hm1, IsNaturalAltModule.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hLK) halt⟩ h78.2.2
  have hNb : L ⊓ M = L ⊓ Subgroup.normalizer ((L ⊓ Q : Subgroup G) : Set G) := by
    refine le_antisymm ?_ (le_inf inf_le_left hlin)
    refine le_inf inf_le_left ?_
    have hQleM : Q ≤ M := hset.sylowQ.1.trans inf_le_left
    have hSA : (L ⊓ Q) ≤ L ⊓ M := le_inf inf_le_left (inf_le_right.trans hQleM)
    ·
      have hmod : ∃ (F : Type) (_ : Field F) (_ : Fintype F) (m : ℕ),
          Fintype.card F = 2 ^ m ∧ 0 < m ∧
          ∃ α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective α ∧
            α.ker = CFSG.pCore 2 ↥L := by
        obtain ⟨φ, -, -⟩ := h78.2.1
        letI : Fintype (GaloisField 2 n) := Fintype.ofFinite (GaloisField 2 n)
        refine ⟨GaloisField 2 n, inferInstance, inferInstance, n, ?_,
          Nat.lt_trans Nat.zero_lt_one h78.1, ?_⟩
        · rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n
            (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one h78.1))]
        · refine ⟨(φ : (↥L ⧸ CFSG.pCore 2 ↥L) →* _).comp
            (QuotientGroup.mk' (CFSG.pCore 2 ↥L)),
            φ.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
          ext x
          rw [MonoidHom.mem_ker]
          show φ (QuotientGroup.mk x) = 1 ↔ x ∈ CFSG.pCore 2 ↥L
          rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
      rcases CFSG.QuasithinUnique.L238.dickson_block (L := L) (S₁ := L ⊓ Q) (A := L ⊓ M)
        hSa hSA inf_le_left hmod with hAeq | hAN
      · exact absurd (hAeq ▸ inf_le_right) hLM
      · exact hAN
  refine ⟨⟨hSa, hNb⟩, ?_⟩
  let π : ↥L →* (↥L ⧸ CFSG.pCore 2 ↥L) := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  obtain ⟨S₀, hS₀⟩ := sylow_of_isSylowOf hSa
  have hpc_le : CFSG.pCore 2 ↥L ≤ S₀ := by
    haveI : (CFSG.pCore 2 ↥L).Normal := pCore_normal
    exact IsPGroup.le_sylow_of_normal pCore_isPGroup S₀
  have hS'map : CFSG.RankThree.PartOne.IsSylowOf 2 ((S₀ : Subgroup ↥L).map π) ⊤ := by
    have hP := CFSG.CGT.PushingUpLit.Glue.isSylowOf_top S₀
    refine ⟨le_top, hP.2.1.map π, ?_⟩
    rw [Subgroup.relIndex_top_right]
    have hP' : ¬ 2 ∣ (S₀ : Subgroup ↥L).index := by
      simpa [Subgroup.relIndex_top_right] using hP.2.2
    intro hd
    exact hP' (hd.trans (Subgroup.index_map_dvd (H := (S₀ : Subgroup ↥L))
      (QuotientGroup.mk'_surjective _)))
  let S' : Sylow 2 (↥L ⧸ CFSG.pCore 2 ↥L) :=
    { (S₀ : Subgroup ↥L).map π with
      isPGroup' := hS'map.2.1
      is_maximal' := fun {Q} hQ hle => eq_of_isSylowOf_of_isPGroup_le hS'map hle le_top hQ }
  refine ⟨S', ?_⟩
  have hcomap : (Subgroup.normalizer (((S₀ : Subgroup ↥L).map π))).comap π =
      Subgroup.normalizer (S₀ : Subgroup ↥L) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _)]
    congr 1
    rw [QuotientGroup.comap_map_mk' (N := CFSG.pCore 2 ↥L) (H := (S₀ : Subgroup ↥L)),
      sup_eq_right.mpr hpc_le]
  have hnorm : Subgroup.normalizer (S' : Set (↥L ⧸ CFSG.pCore 2 ↥L)) =
      (Subgroup.normalizer (S₀ : Subgroup ↥L)).map π := by
    change Subgroup.normalizer ((S₀ : Subgroup ↥L).map π :
        Set (↥L ⧸ CFSG.pCore 2 ↥L)) = (Subgroup.normalizer (S₀ : Subgroup ↥L)).map π
    have hmap := congrArg (Subgroup.map π) hcomap
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _] at hmap
    exact hmap
  have hN : Subgroup.normalizer (S₀ : Subgroup ↥L) = (L ⊓ M).subgroupOf L := by
    rw [hS₀, ← Subgroup.subgroupOf_normalizer_eq (H := L ⊓ Q) (N := L)
      (inf_le_left : L ⊓ Q ≤ L)]
    have hsub_eq : (L ⊓ Subgroup.normalizer ((L ⊓ Q : Subgroup G) : Set G)).subgroupOf L =
        (Subgroup.normalizer ((L ⊓ Q : Subgroup G) : Set G)).subgroupOf L := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [← hsub_eq, hNb]
  calc ((L ⊓ M).subgroupOf L).map π
      = (Subgroup.normalizer (S₀ : Subgroup ↥L)).map π := by rw [hN]
    _ = Subgroup.normalizer (S' : Set (↥L ⧸ CFSG.pCore 2 ↥L)) := hnorm.symm

private theorem eleven_nine_map_normalizer_eq {G' : Type*} [Group G'] {f : G →* G'}
    (hf : Function.Surjective f) {H : Subgroup G} (hker : f.ker ≤ H) :
    (Subgroup.normalizer (H : Set G)).map f =
      Subgroup.normalizer ((H.map f : Subgroup G') : Set G') := by
  have hcomap : (Subgroup.normalizer ((H.map f : Subgroup G') : Set G')).comap f =
      Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective _ hf, Subgroup.comap_map_eq_self hker]
  have hmap := congrArg (Subgroup.map f) hcomap
  rw [Subgroup.map_comap_eq_self_of_surjective hf] at hmap
  exact hmap.symm

theorem eleven_nine_ker_eq {X : Subgroup G} {n : ℕ} (hshort : IsShortGroup ↥X)
    (hnat : IsNaturalSLTwoModule ↥X n)
    {α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    (hαker : α.ker = (X ⊓ Subgroup.centralizer (blockU X : Set G)).subgroupOf X) :
    α.ker = (oTwoIn X).subgroupOf X := by
  rw [hαker, CGT6.inf_centralizer_blockU_eq_SL hshort hnat]

private theorem eleven_nine_oTwoIn_inf_eq_bot {L D : Subgroup G} (hodd : Odd (Nat.card D)) :
    oTwoIn L ⊓ D = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyO, hyD⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨m, hm⟩ := (isPGroup_oTwoIn L) ⟨y, hyO⟩
  have hoddy : Odd (orderOf y) := hodd.of_dvd_nat (by
    simpa using orderOf_dvd_natCard (⟨y, hyD⟩ : ↥D))
  have hdvd : orderOf y ∣ 2 ^ m := orderOf_dvd_iff_pow_eq_one.mpr (by simpa using hm)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hi0 : i = 0 := by
    by_contra hin
    exact (Nat.not_even_iff_odd.mpr hoddy) (even_iff_two_dvd.mpr (hi ▸ dvd_pow_self 2 hin))
  rw [Subgroup.mem_bot, ← orderOf_eq_one_iff, hi, hi0, pow_zero]

theorem eleven_nine_root_point {M V Q U L : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n)
    {α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    (hαsurj : Function.Surjective α) (hαker : α.ker = (oTwoIn L).subgroupOf L) :
    ∃ p : Projectivization (GaloisField 2 n) (Fin 2 → GaloisField 2 n),
      ((L ⊓ Q).subgroupOf L).map α = rootGrp p := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := le_of_lt h78.1
  have hFcard : Nat.card (GaloisField 2 n) = 2 ^ n :=
    GaloisField.card 2 n (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one h78.1))
  obtain ⟨⟨hS, -⟩, -⟩ := eleven_nine_one hset hU hL hLM h78
  obtain ⟨PL, hPL⟩ := sylow_of_isSylowOf hS
  let PS : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    PL.mapSurjective hαsurj
  have hPScoe : (PS : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))) =
      ((L ⊓ Q).subgroupOf L).map α := by
    change (PL : Subgroup ↥L).map α = ((L ⊓ Q).subgroupOf L).map α
    rw [hPL]
  have hPScardF : Nat.card (PS : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))) =
      Nat.card (GaloisField 2 n) := by
    haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    rw [Sylow.card_eq_multiplicity]
    rw [factorization_card_sl2_prime (p := 2) hn1
      (by rw [← Nat.card_eq_fintype_card]; exact hFcard)]
    exact hFcard.symm
  obtain ⟨p, hpS⟩ := exists_point_eq_rootGrp (k := GaloisField 2 n) (p := 2) (f := n)
    Nat.prime_two hFcard
    (P := (PS : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)))) hPScardF
  exact ⟨p, by rw [← hPScoe, hpS]⟩

private theorem eleven_nine_borel_image
    {M V Q U L : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n)
    {α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    (hαsurj : Function.Surjective α) (hαker : α.ker = (oTwoIn L).subgroupOf L)
    {p : Projectivization (GaloisField 2 n) (Fin 2 → GaloisField 2 n)}
    (hαS : ((L ⊓ Q).subgroupOf L).map α = rootGrp p) :
    ((L ⊓ M).subgroupOf L).map α =
      Subgroup.normalizer (rootGrp p :
        Set (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))) := by
  obtain ⟨⟨hS, hBeq⟩, -⟩ := eleven_nine_one hset hU hL hLM h78
  have hO2LQ : oTwoIn L ≤ Q := eleven_nine_oTwoIn_le_Q hset hU hL
  have hkerS : α.ker ≤ (L ⊓ Q).subgroupOf L := by
    rw [hαker]
    intro x hx
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · exact oTwoIn_le L (Subgroup.mem_subgroupOf.mp hx)
    · exact hO2LQ (Subgroup.mem_subgroupOf.mp hx)
  have hBsub : (L ⊓ M).subgroupOf L =
      Subgroup.normalizer ((L ⊓ Q).subgroupOf L : Set ↥L) := by
    rw [hBeq]
    have h1 : (L ⊓ Subgroup.normalizer ((L ⊓ Q : Subgroup G) : Set G)).subgroupOf L =
        (Subgroup.normalizer ((L ⊓ Q : Subgroup G) : Set G)).subgroupOf L := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [h1, Subgroup.subgroupOf_normalizer_eq (H := L ⊓ Q) (N := L) hS.1]
  rw [hBsub, eleven_nine_map_normalizer_eq hαsurj hkerS, hαS]

theorem eleven_nine_card_hall
    {M V Q U L D : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) (hD : IsHallTwoPrimeOf D (L ⊓ M)) :
    Nat.card D = 2 ^ n - 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, -, hαsurj, hαker, -, -, -⟩ := CGT6.isNatSL_blockU hL.2.2.1 h78.2.1
  have hαker' : α.ker = (oTwoIn L).subgroupOf L := eleven_nine_ker_eq hL.2.2.1 h78.2.1 hαker
  obtain ⟨p, hαS⟩ := eleven_nine_root_point hset hU hL hLM h78 hαsurj hαker'
  have hBmap := eleven_nine_borel_image hset hU hL hLM h78 hαsurj hαker' hαS
  obtain ⟨⟨hS, hBeq⟩, -⟩ := eleven_nine_one hset hU hL hLM h78
  have hBL : L ⊓ M ≤ L := inf_le_left
  have hSB : L ⊓ Q ≤ L ⊓ M := by
    rw [hBeq]; exact le_inf hS.1 (Subgroup.le_normalizer)
  have hO2LQ : oTwoIn L ≤ Q := eleven_nine_oTwoIn_le_Q hset hU hL
  have hkerS : α.ker ≤ (L ⊓ Q).subgroupOf L := by
    rw [hαker']
    intro x hx
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · exact oTwoIn_le L (Subgroup.mem_subgroupOf.mp hx)
    · exact hO2LQ (Subgroup.mem_subgroupOf.mp hx)
  have hO2LB : oTwoIn L ≤ L ⊓ M := (le_inf (oTwoIn_le L) hO2LQ).trans hSB
  have hkerB : α.ker ≤ (L ⊓ M).subgroupOf L := by
    rw [hαker']
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hO2LB (Subgroup.mem_subgroupOf.mp hx))
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hSL2card : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) =
      Nat.card (GaloisField 2 n) * (Nat.card (GaloisField 2 n) ^ 2 - 1) :=
    CFSG.GorensteinWalter.sl2_card_formula (GaloisField 2 n)
  have hSrel : (L ⊓ Q).relIndex L = Nat.card (GaloisField 2 n) ^ 2 - 1 := by
    change ((L ⊓ Q).subgroupOf L).index = Nat.card (GaloisField 2 n) ^ 2 - 1
    rw [← Subgroup.index_map_eq (H := (L ⊓ Q).subgroupOf L) hαsurj hkerS, hαS]
    have h := Subgroup.card_mul_index (rootGrp p)
    rw [card_rootGrp, hSL2card] at h
    exact mul_left_cancel₀ (Nat.card_pos (α := GaloisField 2 n)).ne' h
  have hBrel : (L ⊓ M).relIndex L = Nat.card (GaloisField 2 n) + 1 := by
    change ((L ⊓ M).subgroupOf L).index = Nat.card (GaloisField 2 n) + 1
    rw [← Subgroup.index_map_eq (H := (L ⊓ M).subgroupOf L) hαsurj hkerB, hBmap]
    have hstab : Subgroup.normalizer (rootGrp p :
        Set (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))) =
        MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) p := by
      ext g
      rw [mem_normalizer_rootGrp_iff, MulAction.mem_stabilizer_iff]
    rw [hstab, index_stabilizer_projective, Nat.card_eq_fintype_card]
  have hSBsyl : CFSG.QuasithinUnique.IsSylowTwoOf (L ⊓ Q) (L ⊓ M) :=
    CFSG.CGT.PushingUpLit.Glue.isSylowOf_of_le hS hSB hBL
  have hDN : D ≤ Subgroup.normalizer ((L ⊓ Q : Subgroup G) : Set G) :=
    hD.1.trans (by rw [hBeq]; exact inf_le_right)
  obtain ⟨hDS, hSDB, -⟩ := CFSG.QuasithinUnique.Lin2.hall_sylow_decomp' hSBsyl hD hDN
  have hcardsup : Nat.card ↥(L ⊓ M) = Nat.card ↥(L ⊓ Q) * Nat.card ↥D := by
    have h := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq
      (A := L ⊓ Q) (B := D) hDN
    rw [hSDB] at h
    rw [show (L ⊓ Q) ⊓ D = D ⊓ (L ⊓ Q) from inf_comm _ _] at h
    rw [hDS, Subgroup.card_bot, mul_one] at h
    exact h
  have hDrel : Nat.card ↥D = (L ⊓ Q).relIndex (L ⊓ M) := by
    have h1 := Subgroup.card_mul_index ((L ⊓ Q).subgroupOf (L ⊓ M))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSB).toEquiv] at h1
    rw [hcardsup] at h1
    exact (mul_left_cancel₀ (Nat.card_pos (α := ↥(L ⊓ Q))).ne' h1).symm
  have hrelprod : (L ⊓ Q).relIndex (L ⊓ M) * (L ⊓ M).relIndex L = (L ⊓ Q).relIndex L :=
    Subgroup.relIndex_mul_relIndex (L ⊓ Q) (L ⊓ M) L hSB hBL
  have hq2 : Nat.card (GaloisField 2 n) ^ 2 - 1 =
      (Nat.card (GaloisField 2 n) + 1) * (Nat.card (GaloisField 2 n) - 1) := by
    simpa [sq] using mul_self_tsub_one (Nat.card (GaloisField 2 n))
  have h2 : Nat.card ↥D * (L ⊓ M).relIndex L = (L ⊓ Q).relIndex L := by
    rw [hDrel, hrelprod]
  rw [hBrel, hSrel, hq2, mul_comm (Nat.card ↥D)] at h2
  have hq1 : Nat.card (GaloisField 2 n) + 1 ≠ 0 := by positivity
  have := mul_left_cancel₀ hq1 h2
  rw [GaloisField.card 2 n (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one h78.1))] at this
  exact this

theorem eleven_nine_isCyclic_hall
    {M V Q U L D : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) (hD : IsHallTwoPrimeOf D (L ⊓ M)) :
    IsCyclic ↥D := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, -, hαsurj, hαker, -⟩ := CGT6.isNatSL_blockU hL.2.2.1 h78.2.1
  have hαker' : α.ker = (oTwoIn L).subgroupOf L := eleven_nine_ker_eq hL.2.2.1 h78.2.1 hαker
  obtain ⟨p, hαS⟩ := eleven_nine_root_point hset hU hL hLM h78 hαsurj hαker'
  have hBmap := eleven_nine_borel_image hset hU hL hLM h78 hαsurj hαker' hαS
  have hFcard : Nat.card (GaloisField 2 n) = 2 ^ n :=
    GaloisField.card 2 n (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one h78.1))
  have hDL : D ≤ L := hD.1.trans inf_le_left
  have hαD_le : (D.subgroupOf L).map α ≤
      Subgroup.normalizer (rootGrp p :
        Set (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))) := by
    have hmono : D.subgroupOf L ≤ (L ⊓ M).subgroupOf L := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hD.1 (Subgroup.mem_subgroupOf.mp hx))
    refine (Subgroup.map_mono hmono).trans ?_
    rw [hBmap]
  have hcardDL : Nat.card (D.subgroupOf L) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
  have hoddimg : Odd (Nat.card ((D.subgroupOf L).map α)) :=
    hD.2.1.of_dvd_nat (hcardDL ▸ Subgroup.card_map_dvd (H := D.subgroupOf L) α)
  have hbot : oTwoIn L ⊓ D = ⊥ := eleven_nine_oTwoIn_inf_eq_bot hD.2.1
  let φ : D →* (D.subgroupOf L).map α :=
    ((α.comp (D.subgroupOf L).subtype).codRestrict ((D.subgroupOf L).map α)
      (fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)).comp
        (Subgroup.subgroupOfEquivOfLe hDL).symm.toMonoidHom
  have hφinj : Function.Injective φ := by
    intro a b hab
    set e := Subgroup.subgroupOfEquivOfLe hDL with he
    set x := e.symm a with hx
    set y := e.symm b with hy
    have hαxy : α (x : ↥L) = α (y : ↥L) :=
      congrArg (fun z : ↥((D.subgroupOf L).map α) =>
        (z : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))) hab
    have hmem : (x : ↥L) * (y : ↥L)⁻¹ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hαxy, mul_inv_cancel]
    rw [hαker', Subgroup.mem_subgroupOf] at hmem
    have hinD : (x : ↥L) * (y : ↥L)⁻¹ ∈ D.subgroupOf L :=
      (D.subgroupOf L).mul_mem x.2 ((D.subgroupOf L).inv_mem y.2)
    have hmem2 : ((x : ↥L) * (y : ↥L)⁻¹ : G) ∈ oTwoIn L ⊓ D :=
      Subgroup.mem_inf.mpr ⟨hmem, Subgroup.mem_subgroupOf.mp hinD⟩
    rw [hbot, Subgroup.mem_bot] at hmem2
    have hxy : x = y := by
      apply Subtype.ext
      apply Subtype.ext
      exact mul_inv_eq_one.mp hmem2
    rw [← e.apply_symm_apply a, ← e.apply_symm_apply b, ← hx, ← hy, hxy]
  have hχinj : Function.Injective ((eleven_nine_sl2_scalarHom hαD_le).comp φ) := by
    intro a b hab
    exact hφinj (eleven_nine_sl2_scalarHom_injective hαD_le hFcard hoddimg hab)
  refine isCyclic_of_injective_ringHom
    ((Units.coeHom (GaloisField 2 n)).comp
      ((eleven_nine_sl2_scalarHom hαD_le).comp φ)) ?_
  intro a b hab
  refine hχinj (Units.ext ?_)
  have := congrArg (fun x : GaloisField 2 n => x) hab
  simpa using this

theorem eleven_nine_blockU_centralizer_eq_blockZ
    {M V Q U L D : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) (hD : IsHallTwoPrimeOf D (L ⊓ M)) :
    blockU L ⊓ Subgroup.centralizer (D : Set G) = blockZ L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, ψ, hαsurj, hαker, hψsurj, hψker, hψeq⟩ := CGT6.isNatSL_blockU hL.2.2.1 h78.2.1
  have hαker' : α.ker = (oTwoIn L).subgroupOf L := eleven_nine_ker_eq hL.2.2.1 h78.2.1 hαker
  have hψker' : ψ.ker = (blockZ L).subgroupOf (blockU L) := hψker
  obtain ⟨p, hαS⟩ := eleven_nine_root_point hset hU hL hLM h78 hαsurj hαker'
  have hBmap := eleven_nine_borel_image hset hU hL hLM h78 hαsurj hαker' hαS
  have hDL : D ≤ L := hD.1.trans inf_le_left
  have hαD_le : (D.subgroupOf L).map α ≤
      Subgroup.normalizer (rootGrp p :
        Set (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))) := by
    have hmono : D.subgroupOf L ≤ (L ⊓ M).subgroupOf L := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hD.1 (Subgroup.mem_subgroupOf.mp hx))
    refine (Subgroup.map_mono hmono).trans ?_
    rw [hBmap]
  have hbot : oTwoIn L ⊓ D = ⊥ := eleven_nine_oTwoIn_inf_eq_bot hD.2.1
  have h5 := eleven_nine_card_hall hset hU hL hLM h78 hD
  have hDne : D ≠ ⊥ := by
    have h2n : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h78.1
    exact (Subgroup.one_lt_card_iff_ne_bot (H := D)).mp (by rw [h5]; omega)
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨d, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
    have hdL : (d : G) ∈ L := hDL d.2
    have hxd : (d : G) * x * (d : G)⁻¹ ∈ blockU L :=
      conj_mem_blockU (Subgroup.le_normalizer hdL) hxU
    have hxfix : (d : G) * x * (d : G)⁻¹ = x := by
      have hc := Subgroup.mem_centralizer_iff.mp hxC (d : G) d.2
      rw [hc]; group
    have hsame : ψ ⟨(d : G) * x * (d : G)⁻¹, hxd⟩ = ψ ⟨x, hxU⟩ := by
      congr 1
      exact Subtype.ext hxfix
    have heq := hψeq (⟨(d : G), hdL⟩ : ↥L) (⟨x, hxU⟩ : ↥(blockU L)) hxd
    have h2 : Multiplicative.ofAdd
        (((α ⟨(d : G), hdL⟩ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
          (Multiplicative.toAdd (ψ (⟨x, hxU⟩ : ↥(blockU L))))) =
        ψ (⟨x, hxU⟩ : ↥(blockU L)) := heq.symm.trans hsame
    have hw : (α ⟨(d : G), hdL⟩) •
        (Multiplicative.toAdd (ψ (⟨x, hxU⟩ : ↥(blockU L)))) =
        Multiplicative.toAdd (ψ (⟨x, hxU⟩ : ↥(blockU L))) := by
      have h1 : ((α ⟨(d : G), hdL⟩ :
            Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
            Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
            (Multiplicative.toAdd (ψ (⟨x, hxU⟩ : ↥(blockU L)))) =
          Multiplicative.toAdd (ψ (⟨x, hxU⟩ : ↥(blockU L))) := by
        simpa using congrArg Multiplicative.toAdd h2
      simpa [Matrix.SpecialLinearGroup.smul_def] using h1
    have hgN : α ⟨(d : G), hdL⟩ ∈
        Subgroup.normalizer (rootGrp p :
          Set (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))) :=
      hαD_le ⟨⟨(d : G), hdL⟩, d.2, rfl⟩
    have hgrem : α ⟨(d : G), hdL⟩ ∉ rootGrp p := by
      intro hmem
      have hpg : IsPGroup 2 (rootGrp p) :=
        IsPGroup.of_card (n := n) (by
          rw [card_rootGrp, GaloisField.card 2 n
            (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one h78.1))])
      obtain ⟨k, hk⟩ := hpg ⟨_, hmem⟩
      have hdvd2 : orderOf (α ⟨(d : G), hdL⟩) ∣ 2 ^ k :=
        orderOf_dvd_iff_pow_eq_one.mpr (by simpa using hk)
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
      have hodd : Odd (orderOf (α ⟨(d : G), hdL⟩)) := by
        refine hD.2.1.of_dvd_nat ?_
        calc orderOf (α ⟨(d : G), hdL⟩) ∣ orderOf (⟨(d : G), hdL⟩ : ↥L) :=
              orderOf_map_dvd α _
          _ ∣ Nat.card D := by
              rw [Subgroup.orderOf_mk]
              have h := orderOf_dvd_natCard (G := ↥D) (⟨(d : G), d.2⟩ : ↥D)
              rwa [Subgroup.orderOf_mk] at h
      have hj0 : j = 0 := by
        by_contra hjn
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (hj ▸ dvd_pow_self 2 hjn))
      have h1 : α ⟨(d : G), hdL⟩ = 1 := by
        rw [← orderOf_eq_one_iff, hj, hj0, pow_zero]
      have hdker : (⟨(d : G), hdL⟩ : ↥L) ∈ α.ker := h1
      rw [hαker', Subgroup.mem_subgroupOf] at hdker
      have hmem2 : (d : G) ∈ oTwoIn L ⊓ D := Subgroup.mem_inf.mpr ⟨hdker, d.2⟩
      rw [hbot, Subgroup.mem_bot] at hmem2
      exact hd1 (Subtype.ext hmem2)
    have hzero := eleven_nine_sl2_fixes_eq_zero_of_mem_normalizer_of_not_mem_rootGrp hgN hgrem hw
    have hxker : x ∈ blockZ L := by
      have h1 : (⟨x, hxU⟩ : ↥(blockU L)) ∈ ψ.ker := by
        apply Multiplicative.toAdd.injective
        simpa using hzero
      rw [hψker', Subgroup.mem_subgroupOf] at h1
      exact h1
    exact hxker
  · exact le_inf (blockZ_le_blockU L)
      ((inf_le_right : blockZ L ≤ Subgroup.centralizer (L : Set G)).trans
        (Subgroup.centralizer_le (fun d hd => hDL hd)))

section Gaschutz

variable {M V Q U L : Subgroup G} {n : ℕ}

private theorem eleven_nine_gaschutz_hWc (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L)
    (h78 : IsLTwoBlockType L n) {v : G}
    (hvU : v ∈ Subgroup.centralizer (blockU L : Set G)) :
    ∀ a ∈ (blockU L ⊔ Subgroup.zpowers v : Subgroup G),
      ∀ b ∈ (blockU L ⊔ Subgroup.zpowers v : Subgroup G), a * b = b * a := by
  set W : Subgroup G := blockU L ⊔ Subgroup.zpowers v with hW
  have hUab : blockU L ≤ Subgroup.centralizer (blockU L : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (ThmOne.blockU_mul_comm hL.2.2.1 ha hb).symm
  have hUv : Subgroup.zpowers v ≤ Subgroup.centralizer (blockU L : Set G) :=
    Subgroup.zpowers_le.mpr hvU
  have hvU' : blockU L ≤ Subgroup.centralizer (Subgroup.zpowers v : Set G) :=
    Subgroup.le_centralizer_iff.mp hUv
  have hvz : Subgroup.zpowers v ≤ Subgroup.centralizer (Subgroup.zpowers v : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr (Subgroup.zpowers_isMulCommutative v)
  have hsup : Subgroup.centralizer (blockU L : Set G) ⊓
      Subgroup.centralizer (Subgroup.zpowers v : Set G) ≤
      Subgroup.centralizer (W : Set G) := by
    rw [hW, Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mpr inf_le_left)
      (Subgroup.le_centralizer_iff.mpr inf_le_right)
  have hWle : W ≤ Subgroup.centralizer (W : Set G) :=
    (sup_le (le_inf hUab hvU') (le_inf hUv hvz)).trans hsup
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.mp (hWle ha) b hb).symm

private theorem eleven_nine_gaschutz_hWe {L : Subgroup G} (v : G) :
    ∀ w ∈ (blockU L ⊔ Subgroup.zpowers v : Subgroup G),
      w ^ Nat.card (blockU L ⊔ Subgroup.zpowers v : Subgroup G) = 1 := by
  intro w hw
  exact congrArg Subtype.val
    (pow_card_eq_one' (x := (⟨w, hw⟩ : ↥(blockU L ⊔ Subgroup.zpowers v : Subgroup G))))

private theorem eleven_nine_gaschutz_hXW (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (h78 : IsLTwoBlockType L n)
    {v : G} (hvV : v ∈ V) :
    L ≤ Subgroup.normalizer ((blockU L ⊔ Subgroup.zpowers v : Subgroup G) : Set G) := by
  have hVcm : V ≤ centralizerModCore L := eleven_nine_V_le_centralizerModCore hset hU hL h78
  have hVcomm : ∀ v' ∈ V, ∀ l ∈ L, v' * l * v'⁻¹ * l⁻¹ ∈ blockU L := fun v' hv' l hl =>
    ((ThmOne.mem_centralizerModCore_iff_blockU hL.2.2.1.residual_eq).mp (hVcm hv')).2 l hl
  set W : Subgroup G := blockU L ⊔ Subgroup.zpowers v with hW
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [hW, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_blockU L hx)
      rw [h]; exact le_sup_left
    · rw [MonoidHom.map_zpowers]
      refine Subgroup.zpowers_le.mpr ?_
      change x * v * x⁻¹ ∈ W
      have hc := hVcomm v hvV x hx
      rw [show x * v * x⁻¹ = (v * x * v⁻¹ * x⁻¹)⁻¹ * v from by group]
      exact W.mul_mem (Subgroup.mem_sup_left ((blockU L).inv_mem hc))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

private theorem eleven_nine_gaschutz_hXU (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (h78 : IsLTwoBlockType L n)
    {v : G} (hvV : v ∈ V) :
    ∀ x ∈ L, ∀ w ∈ (blockU L ⊔ Subgroup.zpowers v : Subgroup G),
      x * w * x⁻¹ * w⁻¹ ∈ blockU L := by
  have hVcm : V ≤ centralizerModCore L := eleven_nine_V_le_centralizerModCore hset hU hL h78
  have hVcomm : ∀ v' ∈ V, ∀ l ∈ L, v' * l * v'⁻¹ * l⁻¹ ∈ blockU L := fun v' hv' l hl =>
    ((ThmOne.mem_centralizerModCore_iff_blockU hL.2.2.1.residual_eq).mp (hVcm hv')).2 l hl
  have hVcQ : V ≤ Subgroup.centralizer (Q : Set G) :=
    eleven_a (hset.sylowQ.1.trans inf_le_right)
  have hVcU : V ≤ Subgroup.centralizer (blockU L : Set G) := by
    intro v' hv'
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (hVcQ hv') y
      ((eleven_nine_oTwoIn_le_Q hset hU hL) (blockU_le_oTwoIn L hy))
  set W : Subgroup G := blockU L ⊔ Subgroup.zpowers v with hW
  have hvUL : ∀ u ∈ blockU L, v * u * v⁻¹ ∈ blockU L := by
    intro u hu
    have hc := hVcomm v hvV u (blockU_le L hu)
    rw [show v * u * v⁻¹ = (v * u * v⁻¹ * u⁻¹) * u from by group]
    exact (blockU L).mul_mem hc hu
  have hvNUL : v ∈ Subgroup.normalizer (blockU L : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro u hu
      simpa [MulAut.conj_apply] using hvUL u hu
    · rw [Subgroup.card_map_of_injective (MulAut.conj v).injective]
  have hWnormUL : W ≤ Subgroup.normalizer (blockU L : Set G) := by
    rw [hW]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hvNUL)
  intro x hx
  let H : Subgroup G :=
    { carrier := {y : G | y ∈ W ∧ ⁅x, y⁆ ∈ blockU L}
      one_mem' := ⟨W.one_mem, by simp⟩
      mul_mem' := by
        intro a b ha hb
        obtain ⟨haW, ha⟩ := ha
        obtain ⟨hbW, hb⟩ := hb
        refine ⟨W.mul_mem haW hbW, ?_⟩
        have h2 : a * ⁅x, b⁆ * a⁻¹ ∈ blockU L :=
          (Subgroup.mem_normalizer_iff.mp (hWnormUL haW) ⁅x, b⁆).mp hb
        have heq : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
          rw [commutatorElement_mul_right_eq_mul_conj]; group
        rw [heq]
        exact (blockU L).mul_mem ha h2
      inv_mem' := by
        intro a ha
        obtain ⟨haW, ha⟩ := ha
        refine ⟨W.inv_mem haW, ?_⟩
        have h2 : a⁻¹ * ⁅x, a⁆⁻¹ * a ∈ blockU L := by
          have hna : (a⁻¹ : G) ∈ Subgroup.normalizer (blockU L : Set G) :=
            (Subgroup.normalizer (blockU L : Set G)).inv_mem (hWnormUL haW)
          simpa [inv_inv] using (Subgroup.mem_normalizer_iff.mp hna ⁅x, a⁆⁻¹).mp
            ((blockU L).inv_mem ha)
        have heq : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a := by
          rw [commutatorElement_inv_right, ← commutatorElement_inv]
        rw [heq]; exact h2 }
  have hUL_le_H : blockU L ≤ H := by
    intro u hu
    refine ⟨Subgroup.mem_sup_left hu, ?_⟩
    have h1 : x * u * x⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_blockU L hx) u).mp hu
    rw [show ⁅x, u⁆ = (x * u * x⁻¹) * u⁻¹ from by group]
    exact (blockU L).mul_mem h1 ((blockU L).inv_mem hu)
  have hzp_le_H : Subgroup.zpowers v ≤ H :=
    Subgroup.zpowers_le.mpr
      ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers v), by
        have hc := hVcomm v hvV x hx
        rw [show ⁅x, v⁆ = (v * x * v⁻¹ * x⁻¹)⁻¹ from by group]
        exact (blockU L).inv_mem hc⟩
  have hW_le_H : W ≤ H := sup_le hUL_le_H hzp_le_H
  intro w hw
  have := (hW_le_H hw).2
  rwa [← commutatorElement_def]

end Gaschutz


theorem eleven_nine_inf_centralizer_hall
    {M V Q U L D : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) (hD : IsHallTwoPrimeOf D (L ⊓ M)) :
    V ⊓ Subgroup.centralizer (D : Set G) = V ⊓ Subgroup.centralizer (L : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ ?_
  · rintro v ⟨hvV, hvC⟩
    refine Subgroup.mem_inf.mpr ⟨hvV, ?_⟩
    have hV2 : ∀ x ∈ V, x ^ 2 = 1 := hset.isElemAbelian.2
    have hVcQ : V ≤ Subgroup.centralizer (Q : Set G) :=
      eleven_a (hset.sylowQ.1.trans inf_le_right)
    have hVcU : V ≤ Subgroup.centralizer (blockU L : Set G) := by
      intro v' hv'
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_iff.mp (hVcQ hv') y
        ((eleven_nine_oTwoIn_le_Q hset hU hL) (blockU_le_oTwoIn L hy))
    have hv2 : v ^ 2 = 1 := hV2 v hvV
    have hvUL : ∀ u ∈ blockU L, v * u * v⁻¹ ∈ blockU L := by
      have hVcm : V ≤ centralizerModCore L :=
        eleven_nine_V_le_centralizerModCore hset hU hL h78
      have hVcomm : ∀ v' ∈ V, ∀ l ∈ L, v' * l * v'⁻¹ * l⁻¹ ∈ blockU L := fun v' hv' l hl =>
        ((ThmOne.mem_centralizerModCore_iff_blockU hL.2.2.1.residual_eq).mp (hVcm hv')).2 l hl
      intro u hu
      have hc := hVcomm v hvV u (blockU_le L hu)
      rw [show v * u * v⁻¹ = (v * u * v⁻¹ * u⁻¹) * u from by group]
      exact (blockU L).mul_mem hc hu
    have hvNUL : v ∈ Subgroup.normalizer (blockU L : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [Subgroup.map_le_iff_le_comap]
        intro u hu
        simpa [MulAut.conj_apply] using hvUL u hu
      · rw [Subgroup.card_map_of_injective (MulAut.conj v).injective]
    set W : Subgroup G := blockU L ⊔ Subgroup.zpowers v with hW
    have hUL2 : IsPGroup 2 (blockU L) := (isPGroup_oTwoIn L).to_le (blockU_le_oTwoIn L)
    have hz2 : IsPGroup 2 (Subgroup.zpowers v) := by
      rw [IsPGroup.iff_card]
      have hdvd : orderOf v ∣ 2 ^ 1 := by
        simpa using orderOf_dvd_iff_pow_eq_one.mpr hv2
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact ⟨k, by rw [Nat.card_zpowers, hk]⟩
    have hW2 : IsPGroup 2 W := by
      rw [hW]
      exact hUL2.to_sup_of_normal_left' hz2 (Subgroup.zpowers_le.mpr hvNUL)
    obtain ⟨⟨hS, hBeq⟩, -⟩ := eleven_nine_one hset hU hL hLM h78
    have hBL : L ⊓ M ≤ L := inf_le_left
    have hSB : L ⊓ Q ≤ L ⊓ M := by
      rw [hBeq]; exact le_inf hS.1 (Subgroup.le_normalizer)
    have hBodd : Odd ((L ⊓ M).relIndex L) := by
      have hrel := Subgroup.relIndex_mul_relIndex (L ⊓ Q) (L ⊓ M) L hSB hBL
      have hodd : Odd ((L ⊓ Q).relIndex L) :=
        Nat.not_even_iff_odd.mp fun he => hS.2.2 (even_iff_two_dvd.mp he)
      exact hodd.of_dvd_nat ⟨(L ⊓ Q).relIndex (L ⊓ M), by rw [← hrel, mul_comm]⟩
    have hcop : Nat.Coprime (Nat.card W) ((L ⊓ M).relIndex L) := by
      obtain ⟨k, hk⟩ := hW2.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_left k
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hBodd.not_two_dvd_nat)
    have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a :=
      eleven_nine_gaschutz_hWc hL h78 (hVcU hvV)
    have hWe : ∀ w ∈ W, w ^ Nat.card W = 1 := eleven_nine_gaschutz_hWe v
    have hUW : blockU L ≤ W := by rw [hW]; exact le_sup_left
    have hXW : L ≤ Subgroup.normalizer (W : Set G) :=
      eleven_nine_gaschutz_hXW hset hU hL h78 hvV
    have hXU : ∀ x ∈ L, ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ∈ blockU L :=
      eleven_nine_gaschutz_hXU hset hU hL h78 hvV
    have hvCB : v ∈ Subgroup.centralizer ((L ⊓ M : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hB_le_Cv : L ⊓ M ≤ Subgroup.centralizer ({v} : Set G) := by
        have hS_le : L ⊓ Q ≤ Subgroup.centralizer ({v} : Set G) := by
          intro s hs
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp (hVcQ hvV) s hs.2
        have hD_le : D ≤ Subgroup.centralizer ({v} : Set G) := by
          intro d hd
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp hvC d hd
        have hSD : L ⊓ Q ⊔ D = L ⊓ M := by
          have hDN : D ≤ Subgroup.normalizer ((L ⊓ Q : Subgroup G) : Set G) :=
            hD.1.trans (by rw [hBeq]; exact inf_le_right)
          have hSBsyl : CFSG.QuasithinUnique.IsSylowTwoOf (L ⊓ Q) (L ⊓ M) :=
            CFSG.CGT.PushingUpLit.Glue.isSylowOf_of_le hS hSB hBL
          exact (CFSG.QuasithinUnique.Lin2.hall_sylow_decomp' hSBsyl hD hDN).2.1
        rw [← hSD]
        exact sup_le hS_le hD_le
      exact Subgroup.mem_centralizer_singleton_iff.mp (hB_le_Cv hb)
    have hWT : W ≤ blockU L ⊔ W ⊓ Subgroup.centralizer ((L ⊓ M : Subgroup G) : Set G) := by
      rw [hW]
      refine sup_le le_sup_left ?_
      refine Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers v), hvCB⟩))
    have hG := CFSG.Quasithin.GaschutzNorm.sup_fixed_eq_of_coprime_index
      (X := L) (T := L ⊓ M) (W := W) (U := blockU L) (e := Nat.card W)
      hcop hWc hWe hUW hXW hXU hWT
    have hvW : v ∈ W := by rw [hW]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
    have hv_in : v ∈ blockU L ⊔ W ⊓ Subgroup.centralizer (L : Set G) := by
      rw [hG]; exact hvW
    have hUL_N : blockU L ≤ Subgroup.normalizer
        ((W ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
      have hWleC : W ≤ Subgroup.centralizer (W : Set G) := fun a ha =>
        Subgroup.mem_centralizer_iff.mpr fun b hb => (hWc a ha b hb).symm
      exact (le_sup_left : blockU L ≤ W).trans (hWleC.trans
        ((Subgroup.centralizer_le inf_le_left).trans (Subgroup.centralizer_le_normalizer _)))
    have hv_in' : v ∈ (blockU L : Set G) *
        ((W ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (blockU L)
        (W ⊓ Subgroup.centralizer (L : Set G)) hUL_N]
      exact hv_in
    obtain ⟨u, hu, z, hz, huz⟩ := hv_in'
    have huCD : u ∈ Subgroup.centralizer (D : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hdL : d ∈ L := hD.1.trans inf_le_left hd
      have hu_eq : u = v * z⁻¹ := by rw [← huz]; group
      rw [hu_eq]
      have hv_comm : Commute d v := Subgroup.mem_centralizer_iff.mp hvC d hd
      have hz_comm : Commute d z := Subgroup.mem_centralizer_iff.mp hz.2 d hdL
      exact (hv_comm.mul_right hz_comm.inv_right).eq
    have huZ : u ∈ blockZ L := by
      have hCU := eleven_nine_blockU_centralizer_eq_blockZ hset hU hL hLM h78 hD
      rw [← hCU]
      exact Subgroup.mem_inf.mpr ⟨hu, huCD⟩
    have huL : u ∈ Subgroup.centralizer (L : Set G) := (inf_le_right : blockZ L ≤ _) huZ
    have hfinal : u * z ∈ Subgroup.centralizer (L : Set G) :=
      (Subgroup.centralizer (L : Set G)).mul_mem huL hz.2
    rw [← huz]
    exact hfinal
  · intro v hv
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hv).1,
      (Subgroup.centralizer_le (fun d hd => hD.1.trans inf_le_left hd)) (Subgroup.mem_inf.mp hv).2⟩

theorem eleven_nine_eq_sup_inf_blockU
    {M V Q U L D : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) (hD : IsHallTwoPrimeOf D (L ⊓ M)) :
    V = (V ⊓ Subgroup.centralizer (L : Set G)) ⊔ (V ⊓ blockU L) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVcm : V ≤ centralizerModCore L := eleven_nine_V_le_centralizerModCore hset hU hL h78
  have hVcomm : ∀ v' ∈ V, ∀ l ∈ L, v' * l * v'⁻¹ * l⁻¹ ∈ blockU L := fun v' hv' l hl =>
    ((ThmOne.mem_centralizerModCore_iff_blockU hL.2.2.1.residual_eq).mp (hVcm hv')).2 l hl
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  have hVpg : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hset.isElemAbelian
  have hcop : Nat.Coprime (Nat.card D) (Nat.card V) := by
    obtain ⟨k, hk⟩ := hVpg.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hD.2.1.not_two_dvd_nat).symm
  have hAR : D ≤ Subgroup.normalizer (V : Set G) :=
    hD.1.trans (inf_le_right.trans hset.normal)
  have hsolv : Group.IsSolvable ↥V := isSolvable_of_comm (fun a b =>
    Subtype.ext (B2F.isElemAbelian_comm hset.isElemAbelian a.2 b.2))
  have hcomm_le : ⁅V, D⁆ ≤ V ⊓ blockU L := by
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_le]
      intro v hv d hd
      have hdM : d ∈ M := (hD.1 hd).2
      have hdv : d * v * d⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hset.normal hdM) v).mp hv
      rw [show ⁅v, d⁆ = v * (d * v * d⁻¹)⁻¹ from by group]
      exact V.mul_mem hv (V.inv_mem hdv)
    · rw [Subgroup.commutator_le]
      intro v hv d hd
      have := hVcomm v hv d (hD.1 hd).1
      rwa [commutatorElement_def]
  calc V ≤ ⁅V, D⁆ ⊔ V ⊓ Subgroup.centralizer (D : Set G) :=
        CFSG.AGLEmbedding.le_commutator_sup_inf_centralizer_of_coprime hAR hcop hsolv
    _ ≤ (V ⊓ blockU L) ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) :=
        sup_le_sup hcomm_le
          (le_of_eq (eleven_nine_inf_centralizer_hall hset hU hL hLM h78 hD))
    _ = (V ⊓ Subgroup.centralizer (L : Set G)) ⊔ (V ⊓ blockU L) := sup_comm _ _

theorem eleven_nine_fixed_line
    {M V Q U L D : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) (hD : IsHallTwoPrimeOf D (L ⊓ M))
    {α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    (hαsurj : Function.Surjective α)
    (hαker : α.ker = (L ⊓ Subgroup.centralizer (blockU L : Set G)).subgroupOf L)
    {p : Projectivization (GaloisField 2 n) (Fin 2 → GaloisField 2 n)}
    (hαS : ((L ⊓ Q).subgroupOf L).map α = rootGrp p)
    {ψ : ↥(blockU L) →* Multiplicative (Fin 2 → GaloisField 2 n)}
    (hψker : ψ.ker = (blockZ L).subgroupOf (blockU L))
    (hψeq : ∀ (e : ↥L) (w : ↥(blockU L)) (hw : (e : G) * w * (e : G)⁻¹ ∈ blockU L),
      ψ ⟨(e : G) * w * (e : G)⁻¹, hw⟩ =
        Multiplicative.ofAdd (((α e : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd (ψ w)))) :
    (∀ u : ↥(blockU L), (∀ z : G, z ∈ L ⊓ Q → z * (u : G) * z⁻¹ = (u : G)) →
        Multiplicative.toAdd (ψ u) ∈ p.submodule) ∧
    (∀ w : Fin 2 → GaloisField 2 n,
        (∃ u : ↥(blockU L), (u : G) ∈ V ∧ Multiplicative.toAdd (ψ u) = w) ↔
          w ∈ p.submodule) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hαker' : α.ker = (oTwoIn L).subgroupOf L := eleven_nine_ker_eq hL.2.2.1 h78.2.1 hαker
  have hψker' : ψ.ker = (blockZ L).subgroupOf (blockU L) := hψker
  have hBmap := eleven_nine_borel_image hset hU hL hLM h78 hαsurj hαker' hαS
  have hDL : D ≤ L := hD.1.trans inf_le_left
  have hαD_le : (D.subgroupOf L).map α ≤
      Subgroup.normalizer (rootGrp p :
        Set (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))) := by
    have hmono : D.subgroupOf L ≤ (L ⊓ M).subgroupOf L := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hD.1 (Subgroup.mem_subgroupOf.mp hx))
    refine (Subgroup.map_mono hmono).trans ?_
    rw [hBmap]
  have hbot : oTwoIn L ⊓ D = ⊥ := eleven_nine_oTwoIn_inf_eq_bot hD.2.1
  have hFcard : Nat.card (GaloisField 2 n) = 2 ^ n :=
    GaloisField.card 2 n (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one h78.1))
  have hcardD : Nat.card D = 2 ^ n - 1 := eleven_nine_card_hall hset hU hL hLM h78 hD
  have hcardDL : Nat.card (D.subgroupOf L) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
  let D' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    (D.subgroupOf L).map α
  have hkerD : (α.comp (D.subgroupOf L).subtype).ker = ⊥ := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_bot]
    constructor
    · intro hx
      have hx' : (x : ↥L) ∈ α.ker := hx
      rw [hαker', Subgroup.mem_subgroupOf] at hx'
      have hxD : ((x : ↥L) : G) ∈ D := Subgroup.mem_subgroupOf.mp x.2
      have hmem : ((x : ↥L) : G) ∈ oTwoIn L ⊓ D := Subgroup.mem_inf.mpr ⟨hx', hxD⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact Subtype.ext (Subtype.ext hmem)
    · intro hx
      rw [hx]; simp
  have hrangeD : (α.comp (D.subgroupOf L).subtype).range = D' := by
    ext y
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    exact ⟨fun ⟨x, hx⟩ => ⟨x, x.2, hx⟩, fun ⟨x, hx, hxy⟩ => ⟨⟨x, hx⟩, hxy⟩⟩
  have hcardD' : Nat.card D' = Nat.card D := by
    have h := Subgroup.card_ker_mul_card_range (α.comp (D.subgroupOf L).subtype)
    rw [hkerD, hrangeD, Subgroup.card_bot, one_mul, hcardDL] at h
    exact h
  have hoddimg : Odd (Nat.card D') := by rw [hcardD']; exact hD.2.1
  have hχinj : Function.Injective (eleven_nine_sl2_scalarHom hαD_le) :=
    eleven_nine_sl2_scalarHom_injective hαD_le hFcard hoddimg
  have hcardU : Nat.card (GaloisField 2 n)ˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, hFcard]
  have hχsurj : Function.Surjective (eleven_nine_sl2_scalarHom hαD_le) := by
    haveI : Fintype D' := Fintype.ofFinite _
    haveI : Fintype (GaloisField 2 n)ˣ := Fintype.ofFinite _
    have hcard : Fintype.card D' = Fintype.card (GaloisField 2 n)ˣ := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardD', hcardD, hcardU]
    exact (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard)).mp hχinj
  have hVpg : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hset.isElemAbelian
  have hVcQ : V ≤ Subgroup.centralizer (Q : Set G) :=
    eleven_a (hset.sylowQ.1.trans inf_le_right)
  have hroot_ne : rootGrp p ≠ ⊥ := by
    intro hb
    have : Nat.card (rootGrp p) = 1 := by rw [hb, Subgroup.card_bot]
    rw [card_rootGrp, hFcard] at this
    have h2n : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h78.1
    omega
  obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hroot_ne
  have ht_ne : (t : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) ≠ 1 :=
    fun h => ht1 (Subtype.ext h)
  have htX : (t : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) ∈
      ((L ⊓ Q).subgroupOf L).map α := by rw [hαS]; exact t.2
  obtain ⟨s, hs, hsα⟩ := Subgroup.mem_map.mp htX
  have hsS : (s : G) ∈ L ⊓ Q := Subgroup.mem_subgroupOf.mp hs
  have hfixed : ∀ u : ↥(blockU L),
      (∀ z : G, z ∈ L ⊓ Q → z * (u : G) * z⁻¹ = (u : G)) →
      Multiplicative.toAdd (ψ u) ∈ p.submodule := by
    intro u hcen
    have hw : (s : G) * (u : G) * (s : G)⁻¹ ∈ blockU L := by
      rw [hcen (s : G) hsS]; exact u.2
    have heq := hψeq s u hw
    have hsame : ψ ⟨(s : G) * (u : G) * (s : G)⁻¹, hw⟩ = ψ u := by
      congr 1; exact Subtype.ext (hcen (s : G) hsS)
    have h2 : Multiplicative.ofAdd (((α s : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
        (Multiplicative.toAdd (ψ u))) = ψ u := heq.symm.trans hsame
    have h3 : (α s) • (Multiplicative.toAdd (ψ u)) = Multiplicative.toAdd (ψ u) := by
      have := congrArg Multiplicative.toAdd h2
      simpa [Matrix.SpecialLinearGroup.smul_def] using this
    rw [hsα] at h3
    exact (smul_eq_self_iff_mem_of_mem_rootGrp t.2 ht_ne _).mp h3
  let S_line : AddSubgroup (Fin 2 → GaloisField 2 n) :=
    { carrier := {w | ∃ u : ↥(blockU L), (u : G) ∈ V ∧ Multiplicative.toAdd (ψ u) = w}
      zero_mem' := ⟨1, by simpa using Subgroup.one_mem V, by simp⟩
      add_mem' := by
        rintro a b ⟨u, huV, rfl⟩ ⟨v, hvV, rfl⟩
        exact ⟨u * v, V.mul_mem huV hvV, by rw [map_mul, toAdd_mul]⟩
      neg_mem' := by
        rintro a ⟨u, huV, rfl⟩
        exact ⟨u⁻¹, V.inv_mem huV, by rw [map_inv, toAdd_inv]⟩ }
  have hSp : (S_line : Set (Fin 2 → GaloisField 2 n)) ⊆ p.submodule := by
    rintro w ⟨u, huV, rfl⟩
    exact hfixed u fun z hz => by
      have hc := Subgroup.mem_centralizer_iff.mp (hVcQ huV) z hz.2
      rw [hc]; group
  have hSne : S_line ≠ ⊥ := by
    intro hb
    have hle : V ⊓ blockU L ≤ blockZ L := by
      rintro x ⟨hxV, hxU⟩
      have hmem : Multiplicative.toAdd (ψ ⟨x, hxU⟩) = 0 := by
        have h : Multiplicative.toAdd (ψ ⟨x, hxU⟩) ∈ (S_line : Set (Fin 2 → GaloisField 2 n)) :=
          ⟨⟨x, hxU⟩, hxV, rfl⟩
        simpa [hb] using h
      have hxker : (⟨x, hxU⟩ : ↥(blockU L)) ∈ ψ.ker := by
        apply Multiplicative.toAdd.injective
        simpa using hmem
      rwa [hψker', Subgroup.mem_subgroupOf] at hxker
    have hVleC : V ≤ Subgroup.centralizer (L : Set G) := by
      rw [eleven_nine_eq_sup_inf_blockU hset hU hL hLM h78 hD]
      exact sup_le inf_le_right (hle.trans inf_le_right)
    have hCV : Subgroup.centralizer (V : Set G) ≤ M := by
      refine (Subgroup.centralizer_le_normalizer (V : Set G)).trans ?_
      rw [eleven_c_normalizer hset.maxLocal hset.V_ne_bot hVpg hset.normal]
    exact hLM ((Subgroup.le_centralizer_iff.mp hVleC).trans hCV)
  have hsmul : ∀ a : GaloisField 2 n, a ≠ 0 → ∀ w ∈ S_line, a • w ∈ S_line := by
    intro a ha w hw
    rcases hw with ⟨u, huV, rfl⟩
    obtain ⟨d', hd'⟩ := hχsurj (Units.mk0 a ha)
    obtain ⟨dl, hdl, hdlα⟩ := Subgroup.mem_map.mp d'.2
    have hdlD : (dl : G) ∈ D := Subgroup.mem_subgroupOf.mp hdl
    have hdlL : (dl : G) ∈ L := (hD.1 hdlD).1
    have hduU : (dl : G) * (u : G) * (dl : G)⁻¹ ∈ blockU L :=
      conj_mem_blockU (Subgroup.le_normalizer hdlL) u.2
    have hduV : (dl : G) * (u : G) * (dl : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hset.normal (hD.1 hdlD).2) (u : G)).mp huV
    refine ⟨⟨(dl : G) * (u : G) * (dl : G)⁻¹, hduU⟩, hduV, ?_⟩
    have hwmem : Multiplicative.toAdd (ψ u) ∈ p.submodule := hSp ⟨u, huV, rfl⟩
    have hscalar : eleven_nine_sl2_scalar (α dl) (hαD_le ⟨dl, hdl, rfl⟩) = a := by
      have hd'' : (⟨α dl, Subgroup.mem_map.mpr ⟨dl, hdl, rfl⟩⟩ : ↥D') = d' :=
        Subtype.ext hdlα
      have h2 : (eleven_nine_sl2_scalarHom hαD_le)
          (⟨α dl, Subgroup.mem_map.mpr ⟨dl, hdl, rfl⟩⟩ : ↥D') = Units.mk0 a ha := by
        rw [hd'']; exact hd'
      have h3 := congrArg (fun x : (GaloisField 2 n)ˣ => (x : GaloisField 2 n)) h2
      rw [eleven_nine_sl2_scalarHom_apply] at h3
      exact h3
    have hsc := eleven_nine_sl2_scalar_smul (α dl) (hαD_le ⟨dl, hdl, rfl⟩) hwmem
    have hlast : Multiplicative.toAdd (ψ ⟨(dl : G) * (u : G) * (dl : G)⁻¹, hduU⟩) =
        (α dl) • Multiplicative.toAdd (ψ u) := by
      have := congrArg Multiplicative.toAdd (hψeq dl u hduU)
      simpa [Matrix.SpecialLinearGroup.smul_def] using this
    rw [hlast, hsc, hscalar]
  have hS_eq : (S_line : Set (Fin 2 → GaloisField 2 n)) = p.submodule :=
    eleven_nine_sl2_addSubgroup_eq_of_ne_bot_of_smul hSp hSne hsmul
  have hfix : ∀ w : Fin 2 → GaloisField 2 n,
      (∃ u : ↥(blockU L), (u : G) ∈ V ∧ Multiplicative.toAdd (ψ u) = w) ↔
        w ∈ p.submodule := by
    intro w
    constructor
    · rintro ⟨u, huV, huψ⟩
      change w ∈ (p.submodule : Set (Fin 2 → GaloisField 2 n))
      rw [← hS_eq]
      exact ⟨u, huV, huψ⟩
    · intro hw
      have hw' : w ∈ (p.submodule : Set (Fin 2 → GaloisField 2 n)) := hw
      rw [← hS_eq] at hw'
      exact hw'
  exact ⟨hfixed, hfix⟩


theorem eleven_nine_blockU_inf_centralizer_sylow
    {M V Q U L D : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) (hD : IsHallTwoPrimeOf D (L ⊓ M)) :
    blockU L ⊓ Subgroup.centralizer ((L ⊓ Q : Subgroup G) : Set G) =
      (V ⊓ blockU L) ⊔ blockZ L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, ψ, hαsurj, hαker, hψsurj, hψker, hψeq⟩ := CGT6.isNatSL_blockU hL.2.2.1 h78.2.1
  have hαker' : α.ker = (oTwoIn L).subgroupOf L := eleven_nine_ker_eq hL.2.2.1 h78.2.1 hαker
  obtain ⟨p, hαS⟩ := eleven_nine_root_point hset hU hL hLM h78 hαsurj hαker'
  have hψker' : ψ.ker = (blockZ L).subgroupOf (blockU L) := hψker
  have hVcQ : V ≤ Subgroup.centralizer (Q : Set G) :=
    eleven_a (hset.sylowQ.1.trans inf_le_right)
  obtain ⟨hfixed, hfix⟩ :=
    eleven_nine_fixed_line hset hU hL hLM h78 hD hαsurj hαker hαS hψker hψeq
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxp : Multiplicative.toAdd (ψ ⟨x, hxU⟩) ∈ p.submodule :=
      hfixed ⟨x, hxU⟩ fun z hz => by
        have hc := Subgroup.mem_centralizer_iff.mp hxC z hz
        rw [hc]; group
    obtain ⟨u, huV, huψ⟩ := (hfix _).mpr hxp
    have hxu : (⟨x, hxU⟩ : ↥(blockU L)) * u⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      rw [map_mul, toAdd_mul, map_inv, toAdd_inv, huψ]
      simp
    rw [hψker', Subgroup.mem_subgroupOf] at hxu
    have hxZ : x * (u : G)⁻¹ ∈ blockZ L := by simpa using hxu
    rw [show x = (x * (u : G)⁻¹) * (u : G) from by group]
    exact ((V ⊓ blockU L) ⊔ blockZ L).mul_mem (Subgroup.mem_sup_right hxZ)
      (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨huV, u.2⟩))
  · refine le_inf ?_ ?_
    · exact sup_le (fun y hy => hy.2) (blockZ_le_blockU L)
    · refine sup_le ?_ ?_
      · intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (Subgroup.mem_centralizer_iff.mp (hVcQ hy.1) z hz.2)
      · exact ((inf_le_right : blockZ L ≤ Subgroup.centralizer (L : Set G)).trans
          (Subgroup.centralizer_le (fun z hz => hz.1)))

theorem eleven_nine_card_commutator_hall
    {M V Q U L D : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) (hD : IsHallTwoPrimeOf D (L ⊓ M)) :
    Nat.card (⁅V, D⁆ : Subgroup G) = 2 ^ n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, ψ, hαsurj, hαker, hψsurj, hψker, hψeq⟩ := CGT6.isNatSL_blockU hL.2.2.1 h78.2.1
  have hαker' : α.ker = (oTwoIn L).subgroupOf L := eleven_nine_ker_eq hL.2.2.1 h78.2.1 hαker
  have hψker' : ψ.ker = (blockZ L).subgroupOf (blockU L) := hψker
  obtain ⟨p, hαS⟩ := eleven_nine_root_point hset hU hL hLM h78 hαsurj hαker'
  obtain ⟨hfixed, hfix⟩ :=
    eleven_nine_fixed_line hset hU hL hLM h78 hD hαsurj hαker hαS hψker hψeq
  have hFcard : Nat.card (GaloisField 2 n) = 2 ^ n :=
    GaloisField.card 2 n (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one h78.1))
  have hVpg : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hset.isElemAbelian
  set N : Subgroup G := V ⊓ blockU L with hN
  have hNleV : N ≤ V := by rw [hN]; exact inf_le_left
  have hNleU : N ≤ blockU L := by rw [hN]; exact inf_le_right
  have hAN : D ≤ Subgroup.normalizer (N : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hdM : d ∈ M := (hD.1 hd).2
    have hdL : d ∈ L := (hD.1 hd).1
    constructor
    · intro hx
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hset.normal hdM) x).mp hx.1,
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_blockU L hdL) x).mp hx.2⟩
    · intro hx
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hset.normal hdM) x).mpr hx.1,
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_blockU L hdL) x).mpr hx.2⟩
  have hNab : ∀ x y : ↥N, x * y = y * x := fun x y =>
    Subtype.ext (B2F.isElemAbelian_comm hset.isElemAbelian (hNleV x.2) (hNleV y.2))
  have hNpg : IsPGroup 2 N := hVpg.to_le hNleV
  have hcop : Nat.Coprime (Nat.card D) (Nat.card N) := by
    obtain ⟨k, hk⟩ := hNpg.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hD.2.1.not_two_dvd_nat).symm
  obtain ⟨hsup, hdisj⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp N D hAN hNab hcop
  have hNab' : N ≤ Subgroup.centralizer (N : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => congrArg Subtype.val (hNab ⟨y, hy⟩ ⟨x, hx⟩)
  have hcommN : ⁅N, D⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro x hx d hd
    have hdV : d * x * d⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hAN hd) x).mp hx
    rw [show ⁅x, d⁆ = x * (d * x * d⁻¹)⁻¹ from by group]
    exact N.mul_mem hx (N.inv_mem hdV)
  have hcard1 : Nat.card ↥N = Nat.card ↥(N ⊓ Subgroup.centralizer (D : Set G)) *
      Nat.card ↥(⁅N, D⁆) := by
    have hB : ⁅N, D⁆ ≤ Subgroup.normalizer
        ((N ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
      hcommN.trans (hNab'.trans ((Subgroup.centralizer_le inf_le_left).trans
        (Subgroup.centralizer_le_normalizer _)))
    have h := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq
      (A := N ⊓ Subgroup.centralizer (D : Set G)) (B := ⁅N, D⁆) hB
    rw [hsup, hdisj.eq_bot, Subgroup.card_bot, mul_one] at h
    exact h
  have hcard2 : Nat.card ↥N = Nat.card ↥(N ⊓ blockZ L) * 2 ^ n := by
    let incl : ↥N →* ↥(blockU L) := Subgroup.inclusion hNleU
    let g : ↥N →* Multiplicative (Fin 2 → GaloisField 2 n) := ψ.comp incl
    have hker : g.ker = (N ⊓ blockZ L).subgroupOf N := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro hx
        have hx' : incl x ∈ ψ.ker := hx
        rw [hψker', Subgroup.mem_subgroupOf] at hx'
        exact ⟨x.2, hx'⟩
      · rintro ⟨-, hxZ⟩
        have hx' : incl x ∈ ψ.ker := by
          rw [hψker', Subgroup.mem_subgroupOf]; exact hxZ
        exact hx'
    have hker_card : Nat.card g.ker = Nat.card ↥(N ⊓ blockZ L) := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hrange_card : Nat.card g.range = 2 ^ n := by
      have hrange_eq : g.range = (p.submodule.toAddSubgroup).toSubgroup := by
        ext y
        rw [MonoidHom.mem_range, Multiplicative.mem_toSubgroup]
        constructor
        · rintro ⟨x, rfl⟩
          exact (hfix _).mp ⟨incl x, hNleV x.2, rfl⟩
        · intro hy
          obtain ⟨u, huV, huψ⟩ := (hfix y.toAdd).mpr hy
          refine ⟨⟨(u : G), ⟨huV, u.2⟩⟩, ?_⟩
          show ψ (incl ⟨(u : G), ⟨huV, u.2⟩⟩) = y
          rw [show incl ⟨(u : G), ⟨huV, u.2⟩⟩ = u from Subtype.ext rfl]
          exact Multiplicative.toAdd.injective huψ
      rw [hrange_eq]
      rw [show Nat.card ↥((p.submodule.toAddSubgroup).toSubgroup) = Nat.card (p.submodule) from
        Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd (fun _ => Iff.rfl))]
      rw [card_submodule_line p, hFcard]
    have h := Subgroup.card_ker_mul_card_range g
    rw [hker_card, hrange_card] at h
    exact h.symm
  have hNZD : N ⊓ Subgroup.centralizer (D : Set G) = N ⊓ blockZ L := by
    rw [hN]
    rw [inf_assoc, eleven_nine_blockU_centralizer_eq_blockZ hset hU hL hLM h78 hD,
      inf_assoc, inf_eq_right.mpr (blockZ_le_blockU L)]
  have hcardN : Nat.card ↥N = Nat.card ↥(N ⊓ blockZ L) * Nat.card ↥(⁅N, D⁆) := by
    rw [← hNZD]; exact hcard1
  have hcancel : Nat.card ↥(N ⊓ blockZ L) * Nat.card ↥(⁅N, D⁆) =
      Nat.card ↥(N ⊓ blockZ L) * 2 ^ n := hcardN.symm.trans hcard2
  have hNcard : Nat.card ↥(⁅N, D⁆) = 2 ^ n :=
    mul_left_cancel₀ (Nat.card_pos (α := ↥(N ⊓ blockZ L))).ne' hcancel
  have hcomm_eq : ⁅V, D⁆ = ⁅N, D⁆ := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro v hv d hd
      have hVleC : V ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
        Subgroup.mem_centralizer_iff.mpr fun y hy =>
          B2F.isElemAbelian_comm hset.isElemAbelian hy hx
      have hCN : V ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (N : Set G) :=
        (inf_le_left : V ⊓ Subgroup.centralizer (L : Set G) ≤ V).trans
          (hVleC.trans ((Subgroup.centralizer_le hNleV).trans
            (Subgroup.centralizer_le_normalizer _)))
      have hprod : ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) *
          (N : Set G) = V := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right
          (V ⊓ Subgroup.centralizer (L : Set G)) N hCN, hN,
          ← eleven_nine_eq_sup_inf_blockU hset hU hL hLM h78 hD]
      have hv' : v ∈ ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) *
          (N : Set G) := by
        rw [hprod]; exact hv
      obtain ⟨c, hc, n, hn, hcn⟩ := hv'
      have hcd : ⁅c, d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp hc.2 d (hD.1 hd).1).symm
      have hnV : ⁅n, d⁆ ∈ V := by
        have hdnV : d * n * d⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp (hset.normal (hD.1 hd).2) n).mp (hNleV hn)
        rw [show ⁅n, d⁆ = n * (d * n * d⁻¹)⁻¹ from by group]
        exact V.mul_mem (hNleV hn) (V.inv_mem hdnV)
      have hcalc : ⁅v, d⁆ = ⁅n, d⁆ := by
        rw [← hcn, commutatorElement_mul_left_eq_conj_mul, hcd, mul_one]
        rw [B2F.isElemAbelian_comm hset.isElemAbelian hc.1 hnV, mul_assoc, mul_inv_cancel, mul_one]
      rw [hcalc]
      exact Subgroup.commutator_mem_commutator hn hd
    · exact Subgroup.commutator_mono inf_le_left le_rfl
  rw [hcomm_eq]
  exact hNcard

theorem eleven_nine_commutator_inf_blockZ_eq_bot
    {M V Q U L D : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) (hD : IsHallTwoPrimeOf D (L ⊓ M)) :
    ⁅V, D⁆ ⊓ blockZ L = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVpg : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hset.isElemAbelian
  set N : Subgroup G := V ⊓ blockU L with hN
  have hNleV : N ≤ V := by rw [hN]; exact inf_le_left
  have hNleU : N ≤ blockU L := by rw [hN]; exact inf_le_right
  have hAN : D ≤ Subgroup.normalizer (N : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hdM : d ∈ M := (hD.1 hd).2
    have hdL : d ∈ L := (hD.1 hd).1
    constructor
    · intro hx
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hset.normal hdM) x).mp hx.1,
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_blockU L hdL) x).mp hx.2⟩
    · intro hx
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hset.normal hdM) x).mpr hx.1,
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_blockU L hdL) x).mpr hx.2⟩
  have hNab : ∀ x y : ↥N, x * y = y * x := fun x y =>
    Subtype.ext (B2F.isElemAbelian_comm hset.isElemAbelian (hNleV x.2) (hNleV y.2))
  have hNpg : IsPGroup 2 N := hVpg.to_le hNleV
  have hcop : Nat.Coprime (Nat.card D) (Nat.card N) := by
    obtain ⟨k, hk⟩ := hNpg.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hD.2.1.not_two_dvd_nat).symm
  obtain ⟨hsup, hdisj⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp N D hAN hNab hcop
  have hcomm_eq : ⁅V, D⁆ = ⁅N, D⁆ := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro v hv d hd
      have hVleC : V ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
        Subgroup.mem_centralizer_iff.mpr fun y hy =>
          B2F.isElemAbelian_comm hset.isElemAbelian hy hx
      have hCN : V ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (N : Set G) :=
        (inf_le_left : V ⊓ Subgroup.centralizer (L : Set G) ≤ V).trans
          (hVleC.trans ((Subgroup.centralizer_le hNleV).trans
            (Subgroup.centralizer_le_normalizer _)))
      have hprod : ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) *
          (N : Set G) = V := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right
          (V ⊓ Subgroup.centralizer (L : Set G)) N hCN, hN,
          ← eleven_nine_eq_sup_inf_blockU hset hU hL hLM h78 hD]
      have hv' : v ∈ ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) *
          (N : Set G) := by
        rw [hprod]; exact hv
      obtain ⟨c, hc, nn, hn, hcn⟩ := hv'
      have hcd : ⁅c, d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp hc.2 d (hD.1 hd).1).symm
      have hnV : ⁅nn, d⁆ ∈ V := by
        have hdnV : d * nn * d⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp (hset.normal (hD.1 hd).2) nn).mp (hNleV hn)
        rw [show ⁅nn, d⁆ = nn * (d * nn * d⁻¹)⁻¹ from by group]
        exact V.mul_mem (hNleV hn) (V.inv_mem hdnV)
      have hcalc : ⁅v, d⁆ = ⁅nn, d⁆ := by
        rw [← hcn, commutatorElement_mul_left_eq_conj_mul, hcd, mul_one]
        rw [B2F.isElemAbelian_comm hset.isElemAbelian hc.1 hnV, mul_assoc, mul_inv_cancel,
          mul_one]
      rw [hcalc]
      exact Subgroup.commutator_mem_commutator hn hd
    · exact Subgroup.commutator_mono inf_le_left le_rfl
  have hcomm_le_N : ⁅V, D⁆ ≤ N := by
    rw [hcomm_eq]
    rw [Subgroup.commutator_le]
    intro x hx d hd
    have hdV : d * x * d⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hAN hd) x).mp hx
    rw [show ⁅x, d⁆ = x * (d * x * d⁻¹)⁻¹ from by group]
    exact N.mul_mem hx (N.inv_mem hdV)
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxD, hxZ⟩ := Subgroup.mem_inf.mp hx
  have hxN : x ∈ N := hcomm_le_N hxD
  have hxC : x ∈ Subgroup.centralizer (D : Set G) :=
    (Subgroup.centralizer_le (fun z hz => (hD.1 hz).1))
      ((inf_le_right : blockZ L ≤ Subgroup.centralizer (L : Set G)) hxZ)
  have hxND : x ∈ ⁅N, D⁆ := hcomm_eq ▸ hxD
  have : x ∈ (N ⊓ Subgroup.centralizer (D : Set G)) ⊓ ⁅N, D⁆ :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxN, hxC⟩, hxND⟩
  rw [hdisj.eq_bot, Subgroup.mem_bot] at this
  exact this

theorem eleven_nine_commutator_hall_inf_centralizer
    {M V Q U L D : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) (hD : IsHallTwoPrimeOf D (L ⊓ M)) :
    ∀ d ∈ D, d ≠ 1 → ⁅V, D⁆ ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, ψ, hαsurj, hαker, hψsurj, hψker, hψeq⟩ := CGT6.isNatSL_blockU hL.2.2.1 h78.2.1
  have hαker' : α.ker = (oTwoIn L).subgroupOf L := eleven_nine_ker_eq hL.2.2.1 h78.2.1 hαker
  have hψker' : ψ.ker = (blockZ L).subgroupOf (blockU L) := hψker
  obtain ⟨p, hαS⟩ := eleven_nine_root_point hset hU hL hLM h78 hαsurj hαker'
  have hFcard : Nat.card (GaloisField 2 n) = 2 ^ n :=
    GaloisField.card 2 n (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one h78.1))
  have hDL : D ≤ L := hD.1.trans inf_le_left
  have hbot : oTwoIn L ⊓ D = ⊥ := eleven_nine_oTwoIn_inf_eq_bot hD.2.1
  have hαD_le : (D.subgroupOf L).map α ≤
      Subgroup.normalizer (rootGrp p :
        Set (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))) := by
    have hmono : D.subgroupOf L ≤ (L ⊓ M).subgroupOf L := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hD.1 (Subgroup.mem_subgroupOf.mp hx))
    refine (Subgroup.map_mono hmono).trans ?_
    rw [eleven_nine_borel_image hset hU hL hLM h78 hαsurj hαker' hαS]
  let D' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    (D.subgroupOf L).map α
  have hcardDL : Nat.card (D.subgroupOf L) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
  have hcardD : Nat.card D = 2 ^ n - 1 := eleven_nine_card_hall hset hU hL hLM h78 hD
  have hcardD' : Nat.card D' = Nat.card D := by
    have hkerD : (α.comp (D.subgroupOf L).subtype).ker = ⊥ := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_bot]
      constructor
      · intro hx
        have hx' : (x : ↥L) ∈ α.ker := hx
        rw [hαker', Subgroup.mem_subgroupOf] at hx'
        have hxD : ((x : ↥L) : G) ∈ D := Subgroup.mem_subgroupOf.mp x.2
        have hmem : ((x : ↥L) : G) ∈ oTwoIn L ⊓ D := Subgroup.mem_inf.mpr ⟨hx', hxD⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact Subtype.ext (Subtype.ext hmem)
      · intro hx
        rw [hx]; simp
    have hrangeD : (α.comp (D.subgroupOf L).subtype).range = D' := by
      ext y
      rw [MonoidHom.mem_range, Subgroup.mem_map]
      exact ⟨fun ⟨x, hx⟩ => ⟨x, x.2, hx⟩, fun ⟨x, hx, hxy⟩ => ⟨⟨x, hx⟩, hxy⟩⟩
    have h := Subgroup.card_ker_mul_card_range (α.comp (D.subgroupOf L).subtype)
    rw [hkerD, hrangeD, Subgroup.card_bot, one_mul, hcardDL] at h
    exact h
  have hoddimg : Odd (Nat.card D') := by rw [hcardD']; exact hD.2.1
  have hχinj : Function.Injective (eleven_nine_sl2_scalarHom hαD_le) :=
    eleven_nine_sl2_scalarHom_injective hαD_le hFcard hoddimg
  have hcomm_le_V : ⁅V, D⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv d hd
    have hdV : d * v * d⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hset.normal (hD.1 hd).2) v).mp hv
    rw [show ⁅v, d⁆ = v * (d * v * d⁻¹)⁻¹ from by group]
    exact V.mul_mem hv (V.inv_mem hdV)
  have hcomm_le_U : ⁅V, D⁆ ≤ blockU L := by
    rw [Subgroup.commutator_le]
    intro v hv d hd
    exact ((ThmOne.mem_centralizerModCore_iff_blockU hL.2.2.1.residual_eq).mp
      (eleven_nine_V_le_centralizerModCore hset hU hL h78 hv)).2 d (hD.1 hd).1
  have hker_bot : ⁅V, D⁆ ⊓ blockZ L = ⊥ :=
    eleven_nine_commutator_inf_blockZ_eq_bot hset hU hL hLM h78 hD
  intro d hd hd1
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxcomm, hxcen⟩ := Subgroup.mem_inf.mp hx
  have hdL : (d : G) ∈ L := (hD.1 hd).1
  have hxV : x ∈ V := hcomm_le_V hxcomm
  have hxU : x ∈ blockU L := hcomm_le_U hxcomm
  have hxd : (d : G) * x * (d : G)⁻¹ = x := by
    have hc := Subgroup.mem_centralizer_iff.mp hxcen (d : G) (by simp)
    rw [hc]; group
  have hxdU : (d : G) * x * (d : G)⁻¹ ∈ blockU L := by rw [hxd]; exact hxU
  have heq := hψeq ⟨(d : G), hdL⟩ ⟨x, hxU⟩ hxdU
  have hsame : ψ ⟨(d : G) * x * (d : G)⁻¹, hxdU⟩ = ψ ⟨x, hxU⟩ := by
    congr 1; exact Subtype.ext hxd
  have h2 : Multiplicative.ofAdd (((α ⟨(d : G), hdL⟩ :
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
      (Multiplicative.toAdd (ψ ⟨x, hxU⟩))) = ψ ⟨x, hxU⟩ := heq.symm.trans hsame
  have hw : (α ⟨(d : G), hdL⟩) • (Multiplicative.toAdd (ψ ⟨x, hxU⟩)) =
      Multiplicative.toAdd (ψ ⟨x, hxU⟩) := by
    have h3 := congrArg Multiplicative.toAdd h2
    simpa [Matrix.SpecialLinearGroup.smul_def] using h3
  let dmap : ↥D' := ⟨α ⟨(d : G), hdL⟩,
    Subgroup.mem_map.mpr ⟨⟨(d : G), hdL⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩⟩
  let d' : ↥D' := dmap
  have hd'1 : d' ≠ 1 := by
    intro h
    have hαd1 : α ⟨(d : G), hdL⟩ = 1 := congrArg Subtype.val h
    have hdker : (⟨(d : G), hdL⟩ : ↥L) ∈ α.ker := hαd1
    rw [hαker', Subgroup.mem_subgroupOf] at hdker
    have hmem : (d : G) ∈ oTwoIn L ⊓ D := Subgroup.mem_inf.mpr ⟨hdker, hd⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hd1 hmem
  have hχne : (eleven_nine_sl2_scalarHom hαD_le) d' ≠ 1 := by
    intro h
    exact hd'1 (hχinj (by rw [h, map_one]))
  have hsc_ne : eleven_nine_sl2_scalar (α ⟨(d : G), hdL⟩) (hαD_le dmap.2) ≠ 1 := by
    intro hsc
    apply hχne
    apply Units.ext
    rw [eleven_nine_sl2_scalarHom_apply, hsc]
    rfl
  have hgrem : α ⟨(d : G), hdL⟩ ∉ rootGrp p := by
    intro hmem
    exact hsc_ne ((eleven_nine_sl2_scalar_eq_one_iff _ _).mpr hmem)
  have hzero := eleven_nine_sl2_fixes_eq_zero_of_mem_normalizer_of_not_mem_rootGrp
    (hαD_le dmap.2) hgrem hw
  have hxZ : x ∈ blockZ L := by
    have h1 : (⟨x, hxU⟩ : ↥(blockU L)) ∈ ψ.ker := by
      apply Multiplicative.toAdd.injective
      simpa using hzero
    rwa [hψker', Subgroup.mem_subgroupOf] at h1
  have : x ∈ ⁅V, D⁆ ⊓ blockZ L := Subgroup.mem_inf.mpr ⟨hxcomm, hxZ⟩
  rw [hker_bot, Subgroup.mem_bot] at this
  exact this


theorem eleven_nine_hall_structure
    {M V Q U L D : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) (hD : IsHallTwoPrimeOf D (L ⊓ M)) :
    V ⊓ Subgroup.centralizer (D : Set G) = V ⊓ Subgroup.centralizer (L : Set G) ∧
    V = (V ⊓ Subgroup.centralizer (L : Set G)) ⊔ (V ⊓ blockU L) ∧
    blockU L ⊓ Subgroup.centralizer ((L ⊓ Q : Subgroup G) : Set G) =
      (V ⊓ blockU L) ⊔ blockZ L ∧
    Nat.card (⁅V, D⁆ : Subgroup G) = 2 ^ n ∧ Nat.card D = 2 ^ n - 1 ∧
    (∀ d ∈ D, d ≠ 1 → ⁅V, D⁆ ⊓ Subgroup.centralizer ({d} : Set G) = ⊥) ∧ IsCyclic ↥D :=
  ⟨eleven_nine_inf_centralizer_hall hset hU hL hLM h78 hD,
   eleven_nine_eq_sup_inf_blockU hset hU hL hLM h78 hD,
   eleven_nine_blockU_inf_centralizer_sylow hset hU hL hLM h78 hD,
   eleven_nine_card_commutator_hall hset hU hL hLM h78 hD,
   eleven_nine_card_hall hset hU hL hLM h78 hD,
   eleven_nine_commutator_hall_inf_centralizer hset hU hL hLM h78 hD,
   eleven_nine_isCyclic_hall hset hU hL hLM h78 hD⟩

theorem eleven_nine_exists_hall
    {M V Q U L : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) :
    ∃ X : Subgroup G, IsHallTwoPrimeOf X (L ⊓ M) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hS, hBeq⟩, -⟩ := eleven_nine_one hset hU hL hLM h78
  have hSB : L ⊓ Q ≤ L ⊓ M :=
    le_inf inf_le_left (inf_le_right.trans (hset.sylowQ.1.trans inf_le_left))
  have hBM : L ⊓ M ≤ Subgroup.normalizer ((L ⊓ Q : Subgroup G) : Set G) :=
    hBeq.le.trans inf_le_right
  have hNnormal : ((L ⊓ Q).subgroupOf (L ⊓ M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr hBM
  haveI := hNnormal
  have hS2 : IsPGroup 2 ↥(L ⊓ Q) := hset.sylowQ.2.1.to_le inf_le_right
  have hodd : ¬ 2 ∣ ((L ⊓ Q).subgroupOf (L ⊓ M)).index := by
    intro hd
    have hrel := Subgroup.relIndex_mul_relIndex (L ⊓ Q) (L ⊓ M) L hSB inf_le_left
    have hd2 : 2 ∣ (L ⊓ Q).relIndex L := by
      rw [← hrel]
      exact dvd_mul_of_dvd_left hd _
    exact hS.2.2 hd2
  have hpN : IsPGroup 2 ↥((L ⊓ Q).subgroupOf (L ⊓ M)) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSB).symm
  obtain ⟨m, hm⟩ := hpN.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥((L ⊓ Q).subgroupOf (L ⊓ M)))
      ((L ⊓ Q).subgroupOf (L ⊓ M)).index := by
    rw [hm]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hsub : (K.map (L ⊓ M).subtype).subgroupOf (L ⊓ M) = K :=
    Subgroup.comap_map_eq_self_of_injective (L ⊓ M).subtype_injective K
  refine ⟨K.map (L ⊓ M).subtype, ?_⟩
  unfold IsHallTwoPrimeOf
  refine ⟨Subgroup.map_subtype_le K, ?_, m, ?_⟩
  · rw [Subgroup.card_map_of_injective (L ⊓ M).subtype_injective, ← hK.symm.index_eq_card]
    exact Nat.odd_iff.mpr (by omega)
  · rw [Subgroup.relIndex, hsub, hK.index_eq_card, hm]

end CFSG.LocalAnalysis.WeakClosure81
