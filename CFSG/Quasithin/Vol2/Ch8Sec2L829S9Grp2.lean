module

public import CFSG.Open.StatedZModTwo
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.Quasithin.H13.L829N

open scoped MatrixGroups

noncomputable def s9g2_sl32EquivGL : SL(3, ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
  (MonoidHom.ofInjective (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 3) (R := ZMod 2))).trans
    ((MulEquiv.subgroupCongr ((CFSG.Open.StatedAPI.statedSL_eq_range_toGL 3 (ZMod 2)).symm.trans
      (CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two (Nat.card_zmod 2) 3))).trans
      Subgroup.topEquiv)

theorem s9g2_card_sl32 : Nat.card SL(3, ZMod 2) = 168 := by
  have e1 : SL(3, ZMod 2) ≃* ↥(CFSG.Open.StatedSL 3 (ZMod 2)) :=
    (MonoidHom.ofInjective (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 3) (R := ZMod 2))).trans
      (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 3 (ZMod 2)).symm)
  rw [Nat.card_congr e1.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three_zmod_two]

noncomputable def s9g2_statedProjEquivGL (K : Type) [Field K] (hK : Nat.card K = 2) :
    CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K) ≃* GL (Fin 3) K :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK (Fin 3), Subgroup.bot_subgroupOf])
    |>.trans QuotientGroup.quotientBot).trans
  ((MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hK 3)).trans
    Subgroup.topEquiv)

noncomputable def s9g2_glEquivZModTwo (K : Type) [Field K] (hK : Nat.card K = 2) :
    GL (Fin 3) K ≃* GL (Fin 3) (ZMod 2) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  exact Units.mapEquiv (RingEquiv.mapMatrix (ZMod.ringEquivOfPrime K Nat.prime_two hcard).symm).toMulEquiv

theorem s9g2_iso_sl32 {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    Nonempty (X ≃* SL(3, ZMod 2)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  exact ⟨e.trans ((s9g2_statedProjEquivGL K hK2).trans
    ((s9g2_glEquivZModTwo K hK2).trans s9g2_sl32EquivGL.symm))⟩

theorem s9g2_isSylow_map {A B : Type} [Group A] [Group B] (e : A ≃* B) {S : Subgroup A}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    CFSG.QuasithinUnique.IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
  obtain ⟨-, hp, hodd⟩ := hS
  refine ⟨le_top, hp.map e.toMonoidHom, ?_⟩
  have hidx : (S.map e.toMonoidHom).index = S.index := Subgroup.index_map_equiv (H := S) e
  change ¬ 2 ∣ (S.map e.toMonoidHom).relIndex ⊤
  rw [Subgroup.relIndex_top_right, hidx]
  change ¬ 2 ∣ S.relIndex ⊤ at hodd
  rwa [Subgroup.relIndex_top_right] at hodd

theorem s9g2_isParabolic_map_top {A B : Type} [Group A] [Group B] (e : A ≃* B) {R : Subgroup A}
    (hR : CFSG.Quasithin.IsParabolic2 (⊤ : Subgroup A) R) :
    CFSG.Quasithin.IsParabolic2 (⊤ : Subgroup B) (R.map e.toMonoidHom) := by
  obtain ⟨-, S, hS, hN⟩ := hR
  refine ⟨le_top, S.map e.toMonoidHom, s9g2_isSylow_map e hS, ?_⟩
  intro b hb
  have hbN : b ∈ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup B) : Set B) :=
    (Subgroup.mem_inf.mp hb).2
  have hb' : e.symm b ∈ Subgroup.normalizer (S : Set A) := by
    rw [Subgroup.mem_normalizer_iff] at hbN ⊢
    intro a
    have h1 := hbN (e a)
    simp only [SetLike.mem_coe, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply,
      map_mul, map_inv] at h1
    simpa using h1
  have hR' : e.symm b ∈ R := hN (Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, hb'⟩)
  exact Subgroup.mem_map.mpr ⟨e.symm b, hR', by simp⟩

theorem s9g2_maxParabolic_map {A B : Type} [Group A] [Group B] (e : A ≃* B) {R : Subgroup A}
    (hR : CFSG.Quasithin.IsMaxParabolic2 (⊤ : Subgroup A) R) :
    CFSG.Quasithin.IsMaxParabolic2 (⊤ : Subgroup B) (R.map e.toMonoidHom) := by
  obtain ⟨hP, hne, hmax⟩ := hR
  refine ⟨s9g2_isParabolic_map_top e hP, ?_, ?_⟩
  · intro h
    apply hne
    ext a
    simp only [Subgroup.mem_top, iff_true]
    have hea : e a ∈ R.map e.toMonoidHom := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨r, hr, hra⟩ := Subgroup.mem_map.mp hea
    have hra' : r = a := e.injective hra
    rw [← hra']
    exact hr
  · intro Q hQ hQne hle
    have hQ' : CFSG.Quasithin.IsParabolic2 (⊤ : Subgroup A) (Q.map e.symm.toMonoidHom) :=
      s9g2_isParabolic_map_top e.symm hQ
    have hQ'ne : Q.map e.symm.toMonoidHom ≠ ⊤ := by
      intro h
      apply hQne
      ext b
      simp only [Subgroup.mem_top, iff_true]
      have hb : e.symm b ∈ Q.map e.symm.toMonoidHom := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨q, hq, hqb⟩ := Subgroup.mem_map.mp hb
      have hqb' : q = b := e.symm.injective hqb
      rw [← hqb']
      exact hq
    have hle' : R ≤ Q.map e.symm.toMonoidHom := by
      intro r hr
      have hre : e r ∈ Q := hle (Subgroup.mem_map.mpr ⟨r, hr, rfl⟩)
      exact Subgroup.mem_map.mpr ⟨e r, hre, by simp⟩
    have hQR := hmax _ hQ' hQ'ne hle'
    ext b
    constructor
    · intro hb
      have hb' : e.symm b ∈ Q.map e.symm.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
      rw [hQR] at hb'
      exact Subgroup.mem_map.mpr ⟨e.symm b, hb', by simp⟩
    · intro hb
      obtain ⟨r, hr, hrb⟩ := Subgroup.mem_map.mp hb
      have hrQ : r ∈ Q.map e.symm.toMonoidHom := by
        rw [hQR]
        exact hr
      obtain ⟨q, hq, hqr⟩ := Subgroup.mem_map.mp hrQ
      have hbq : b = q := by
        rw [← hrb, ← hqr]
        simp
      rw [hbq]
      exact hq

theorem s9g2_mem_map_subtype {Y : Type} [Group Y] {L : Subgroup Y} {R : Subgroup ↥L} (x : ↥L) :
    (x : Y) ∈ R.map L.subtype ↔ x ∈ R := by
  constructor
  · intro h
    obtain ⟨r, hr, hrx⟩ := Subgroup.mem_map.mp h
    have hrx' : r = x := Subtype.ext hrx
    rw [← hrx']
    exact hr
  · intro h
    exact Subgroup.mem_map_of_mem _ h

theorem s9g2_subgroupOf_map_subtype {Y : Type} [Group Y] {L : Subgroup Y} (S : Subgroup ↥L) :
    (S.map L.subtype).subgroupOf L = S := by
  ext x
  rw [Subgroup.mem_subgroupOf, s9g2_mem_map_subtype]

theorem s9g2_map_subgroupOf_eq {Y : Type} [Group Y] {L Q : Subgroup Y} (hQL : Q ≤ L) :
    (Q.subgroupOf L).map L.subtype = Q := by
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hQL]

theorem s9g2_isParabolic_subgroupOf {Y : Type} [Group Y] {L Q : Subgroup Y}
    (hQ : CFSG.Quasithin.IsParabolic2 L Q) :
    CFSG.Quasithin.IsParabolic2 (⊤ : Subgroup ↥L) (Q.subgroupOf L) := by
  obtain ⟨hQL, S, hS, hN⟩ := hQ
  refine ⟨le_top, S.subgroupOf L, ⟨le_top, ?_, ?_⟩, ?_⟩
  · exact hS.2.1.comap_of_injective L.subtype Subtype.val_injective
  · have h := hS.2.2
    change ¬ 2 ∣ (S.subgroupOf L).index at h
    change ¬ 2 ∣ (S.subgroupOf L).relIndex ⊤
    rwa [Subgroup.relIndex_top_right]
  · intro x hx
    have hxN : x ∈ Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      (Subgroup.mem_inf.mp hx).2
    rw [Subgroup.mem_normalizer_iff] at hxN
    have hxS : (x : Y) ∈ Subgroup.normalizer (S : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      by_cases hh : h ∈ L
      · have h1 := hxN ⟨h, hh⟩
        simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h1
        exact h1
      · constructor
        · intro hhS
          exact absurd (hS.1 hhS) hh
        · intro hxhS
          exfalso
          apply hh
          have hmem : (x : Y) * h * (x : Y)⁻¹ ∈ L := hS.1 hxhS
          have e : h = (x : Y)⁻¹ * ((x : Y) * h * (x : Y)⁻¹) * (x : Y) := by group
          rw [e]
          exact L.mul_mem (L.mul_mem (L.inv_mem x.2) hmem) x.2
    have hxQ : (x : Y) ∈ Q := hN (Subgroup.mem_inf.mpr ⟨x.2, hxS⟩)
    exact Subgroup.mem_subgroupOf.mpr hxQ

theorem s9g2_maxParabolic_subgroup {Y : Type} [Group Y] {L : Subgroup Y} {R : Subgroup ↥L}
    (hR : CFSG.Quasithin.IsMaxParabolic2 (⊤ : Subgroup ↥L) R) :
    CFSG.Quasithin.IsMaxParabolic2 L (R.map L.subtype) := by
  obtain ⟨hR1, hRne, hRmax⟩ := hR
  have hPL : R.map L.subtype ≤ L := Subgroup.map_subtype_le R
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨-, S_L, hS_L, hN_L⟩ := hR1
    refine ⟨hPL, S_L.map L.subtype, ⟨Subgroup.map_subtype_le S_L, hS_L.2.1.map L.subtype, ?_⟩, ?_⟩
    · rw [s9g2_subgroupOf_map_subtype]
      have h := hS_L.2.2
      change ¬ 2 ∣ S_L.relIndex ⊤ at h
      rwa [Subgroup.relIndex_top_right] at h
    · intro y hy
      obtain ⟨hyL, hyN⟩ := Subgroup.mem_inf.mp hy
      have hyN' : y ∈ Subgroup.normalizer ((S_L.map L.subtype : Subgroup Y) : Set Y) := hyN
      rw [Subgroup.mem_normalizer_iff] at hyN'
      have hxN : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.normalizer ((S_L : Subgroup ↥L) : Set ↥L) := by
        rw [Subgroup.mem_normalizer_iff]
        intro a
        have h1 := hyN' (a : Y)
        have e : y * (a : Y) * y⁻¹ = ((⟨y, hyL⟩ * a * (⟨y, hyL⟩ : ↥L)⁻¹ : ↥L) : Y) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [e] at h1
        simp only [SetLike.mem_coe, s9g2_mem_map_subtype] at h1
        exact h1
      have hxR := hN_L (Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, hxN⟩)
      exact (s9g2_mem_map_subtype _).mpr hxR
  ·
    intro h
    apply hRne
    ext x
    simp only [Subgroup.mem_top, iff_true]
    rw [← s9g2_mem_map_subtype, h]
    exact x.2
  ·
    intro Q hQ hQne hPQ
    have hQL : Q ≤ L := hQ.1
    have hQ_L := s9g2_isParabolic_subgroupOf hQ
    have hne_L : Q.subgroupOf L ≠ ⊤ := by
      intro h
      apply hQne
      apply le_antisymm hQL
      intro y hy
      have hmem : (⟨y, hy⟩ : ↥L) ∈ Q.subgroupOf L := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    have hRle : R ≤ Q.subgroupOf L := fun r hr =>
      Subgroup.mem_subgroupOf.mpr (hPQ ((s9g2_mem_map_subtype r).mpr hr))
    have hQR : Q.subgroupOf L = R := hRmax (Q.subgroupOf L) hQ_L hne_L hRle
    calc Q = (Q.subgroupOf L).map L.subtype := (s9g2_map_subgroupOf_eq hQL).symm
      _ = R.map L.subtype := by rw [hQR]

theorem s9g2_normalizer_map {A B : Type} [Group A] [Group B] (e : A ≃* B) {S : Subgroup A} {a : A}
    (ha : a ∈ Subgroup.normalizer (S : Set A)) :
    e a ∈ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup B) : Set B) := by
  rw [Subgroup.mem_normalizer_iff] at ha ⊢
  intro g
  obtain ⟨b, rfl⟩ := e.surjective g
  have h := ha b
  simp only [SetLike.mem_coe, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, map_mul,
    map_inv] at h ⊢
  exact h

theorem s9g2_center_sl32 (g : SL(3, ZMod 2)) (hg : ∀ h : SL(3, ZMod 2), g * h = h * g) :
    g = 1 := by
  have hc : g ∈ Subgroup.center (SL(3, ZMod 2)) :=
    Subgroup.mem_center_iff.mpr (fun h => (hg h).symm)
  obtain ⟨r, hr, hgr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hr1 : r = 1 := by
    have h01 : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
    rcases h01 r with h | h
    · exfalso
      rw [h, Fintype.card_fin, zero_pow (by norm_num)] at hr
      exact zero_ne_one hr
    · exact h
  apply Subtype.ext
  rw [← hgr, hr1]
  simp

end CFSG.Quasithin.H13.L829N
