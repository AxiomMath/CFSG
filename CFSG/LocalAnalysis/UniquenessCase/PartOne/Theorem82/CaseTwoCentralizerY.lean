module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoNormalForm
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixedRank
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem card_inf_centralizer_y :
    Nat.card (t.P ⊓ Subgroup.centralizer ({t.y} : Set G) : Subgroup G) =
      3 * Nat.card (t.d.H 0) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbase : CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y = t.d.S := t.base_eq
  have hyS_norm : t.y ∈ Subgroup.normalizer (t.d.S : Set G) := by
    rw [t.hdS]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer t.hyP, c.le_normalizer_L (t.hP.le t.hyP)⟩
  have hzS_norm : Subgroup.zpowers t.y ≤ Subgroup.normalizer (t.d.S : Set G) :=
    Subgroup.zpowers_le.mpr hyS_norm
  let D : Subgroup G := t.d.S ⊓ Subgroup.centralizer ({t.y} : Set G)
  have hDP : D ≤ t.P := fun x hx => by
    rw [← t.hPy]
    exact Subgroup.mem_sup_left hx.1
  have hDC : D ≤ Subgroup.centralizer ({t.y} : Set G) := inf_le_right
  have hZP : Subgroup.zpowers t.y ≤ t.P := by
    rw [← t.hPy]
    exact le_sup_right
  have hZC : Subgroup.zpowers t.y ≤ Subgroup.centralizer ({t.y} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hcardS : Nat.card (D : Subgroup G) = Nat.card (t.d.H 0) := by
    change Nat.card (t.d.S ⊓ Subgroup.centralizer ({t.y} : Set G) : Subgroup G) =
      Nat.card (t.d.H 0)
    rw [← hbase]
    refine CFSG.GroupTheory.WreathThree.card_base_inf_centralizer t.isWreathThree t.hy3 ?_ ?_
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t.y)
    · exact CFSG.GroupTheory.WreathThree.not_mem_base t.isWreathThree
  have hyS : t.y ∉ t.d.S := hbase ▸ CFSG.GroupTheory.WreathThree.not_mem_base t.isWreathThree
  have hdisjS : t.d.S ⊓ Subgroup.zpowers t.y = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzS, hzy⟩
    rw [Subgroup.mem_bot]
    by_contra hz1
    have hzord : orderOf z = 3 := by
      have hdvd : orderOf z ∣ 3 := by
        simpa [t.orderOf_y] using orderOf_dvd_of_mem_zpowers hzy
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hz1
      · exact h
    have hzle : Subgroup.zpowers z ≤ Subgroup.zpowers t.y :=
      Subgroup.zpowers_le.mpr hzy
    have heq : Subgroup.zpowers z = Subgroup.zpowers t.y := by
      refine Subgroup.eq_of_le_of_card_ge hzle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hzord, t.orderOf_y]
    have hyz : t.y ∈ Subgroup.zpowers z := heq.symm ▸ Subgroup.mem_zpowers t.y
    exact hyS (Subgroup.zpowers_le.mpr hzS hyz)
  have hPD : t.P ⊓ Subgroup.centralizer ({t.y} : Set G) = D ⊔ Subgroup.zpowers t.y := by
    apply le_antisymm
    · intro p hp
      have hpS : p ∈ ((t.d.S ⊔ Subgroup.zpowers t.y : Subgroup G) : Set G) := by
        have h := hp.1
        rwa [← t.hPy] at h
      rw [Subgroup.coe_mul_of_right_le_normalizer_left t.d.S (Subgroup.zpowers t.y)
        hzS_norm] at hpS
      obtain ⟨s, hs, z, hz, hsz⟩ := hpS
      have hzcent : z ∈ Subgroup.centralizer ({t.y} : Set G) := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Commute.refl t.y).zpow_left k).eq
      have hsp : s ∈ Subgroup.centralizer ({t.y} : Set G) := by
        have hpcent : Commute p t.y :=
          (commute_iff_eq _ _).mpr (Subgroup.mem_centralizer_singleton_iff.mp hp.2)
        have hzc : Commute z t.y :=
          (commute_iff_eq _ _).mpr (Subgroup.mem_centralizer_singleton_iff.mp hzcent)
        have hs_eq : s = p * z⁻¹ := by
          rw [← hsz, mul_assoc, mul_inv_cancel, mul_one]
        rw [Subgroup.mem_centralizer_singleton_iff, hs_eq]
        exact (hpcent.mul_left hzc.inv_left).eq
      have hmem : s * z ∈ D ⊔ Subgroup.zpowers t.y :=
        Subgroup.mul_mem_sup (S := D) (T := Subgroup.zpowers t.y) (x := s) (y := z)
          (show s ∈ D from ⟨hs, hsp⟩) hz
      simpa [hsz] using hmem
    · exact sup_le (le_inf hDP hDC) (le_inf hZP hZC)
  have hdisj : Disjoint D (Subgroup.zpowers t.y) := by
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    calc D ⊓ Subgroup.zpowers t.y
        ≤ t.d.S ⊓ Subgroup.zpowers t.y := inf_le_inf inf_le_left le_rfl
      _ = ⊥ := hdisjS
  have hyD : t.y ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subgroup.mem_centralizer_singleton_iff.mp hd.2
  have hnorm : Subgroup.zpowers t.y ≤
      Subgroup.normalizer (D : Set G) :=
    (Subgroup.zpowers_le.mpr hyD).trans (Subgroup.centralizer_le_normalizer _)
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    D (Subgroup.zpowers t.y) hnorm hdisj
  rw [hPD, hcard, hcardS, Nat.card_zpowers, t.orderOf_y]
  ring

theorem exists_conj_mem_AA {x : G} (hxL : x ∈ c.L) (hx3 : x ^ 3 = 1) :
    ∃ l ∈ c.L, l * x * l⁻¹ ∈ t.d.AA := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 3 t.d.S c.L := by
    simpa [t.hdL] using t.d.hS
  have hTp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_iff_pow_eq_one.mpr hx3)
  obtain ⟨Syl, hTSyl⟩ := (hTp.comap_subtype (K := c.L)).exists_le_sylow
  let S' : Subgroup G := (Syl : Subgroup c.L).map c.L.subtype
  have hS'syl : CFSG.ABGLocalTools.IsSylowOf 3 S' c.L := ⟨Syl, rfl⟩
  obtain ⟨h, hhL, hh⟩ := hSsyl.exists_mem_conj hS'syl
  have hxSyl : (⟨x, hxL⟩ : ↥c.L) ∈ (Syl : Subgroup ↥c.L) :=
    hTSyl (by change x ∈ Subgroup.zpowers x; exact Subgroup.mem_zpowers x)
  have hxS' : x ∈ S' := by
    change x ∈ (Syl : Subgroup ↥c.L).map c.L.subtype
    exact Subgroup.mem_map_of_mem _ hxSyl
  have hmem : h⁻¹ * x * h ∈ t.d.S := (hh x).mp hxS'
  have hcube : (h⁻¹ * x * h) ^ 3 = 1 := by
    have hconj : (h⁻¹ * x * h) ^ 3 = h⁻¹ * x ^ 3 * h := by
      simpa using conj_pow (a := h⁻¹) (b := x) (i := 3)
    rw [hconj, hx3, mul_one, inv_mul_cancel]
  refine ⟨h⁻¹, c.L.inv_mem hhL, ?_⟩
  simpa using t.d.mem_AA_of_pow_eq_one hmem hcube

theorem exists_conj_eq_y {x : G} (hxM : x ∈ c.S.M) (hx3 : x ^ 3 = 1) (hxL : x ∉ c.L) :
    ∃ m ∈ c.S.M, m * x * m⁻¹ = t.y ∨ m * x * m⁻¹ = t.y⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_iff_pow_eq_one.mpr hx3)
  obtain ⟨Syl, hTSyl⟩ := (hTp.comap_subtype (K := c.S.M)).exists_le_sylow
  let S' : Subgroup G := (Syl : Subgroup c.S.M).map c.S.M.subtype
  have hS'syl : CFSG.ABGLocalTools.IsSylowOf 3 S' c.S.M := ⟨Syl, rfl⟩
  obtain ⟨h, hhM, hh⟩ := t.hP.exists_mem_conj hS'syl
  set x' : G := h⁻¹ * x * h with hx'def
  have hxSyl : (⟨x, hxM⟩ : ↥c.S.M) ∈ (Syl : Subgroup ↥c.S.M) :=
    hTSyl (by change x ∈ Subgroup.zpowers x; exact Subgroup.mem_zpowers x)
  have hxS' : x ∈ S' := by
    change x ∈ (Syl : Subgroup ↥c.S.M).map c.S.M.subtype
    exact Subgroup.mem_map_of_mem _ hxSyl
  have hx'P : x' ∈ t.P := (hh x).mp hxS'
  have hx'3 : x' ^ 3 = 1 := by
    have hconj : x' ^ 3 = h⁻¹ * x ^ 3 * h := by
      rw [hx'def]
      simpa using conj_pow (a := h⁻¹) (b := x) (i := 3)
    rw [hconj, hx3, mul_one, inv_mul_cancel]
  have hx'L : x' ∉ c.L := by
    intro hxL'
    apply hxL
    have hx_eq : x = h * x' * h⁻¹ := by
      rw [hx'def]; group
    rw [hx_eq]
    exact (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_L hhM) x').mp hxL'
  have hx'S : x' ∉ t.d.S := by
    rw [t.hdS]
    exact fun hx => hx'L hx.2
  have hx'base : x' ∈ CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y ⊔
      Subgroup.zpowers t.y := by
    rw [t.base_eq, t.hPy]
    exact hx'P
  have hxbase : x' ∉ CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y := by
    rw [t.base_eq]
    exact hx'S
  obtain ⟨s, hs, hconj⟩ :=
    CFSG.GroupTheory.WreathThree.exists_conj_eq_of_pow_three t.isWreathThree t.hy3
      hx'base hxbase hx'3
  have hsS : s ∈ t.d.S := by rwa [t.base_eq] at hs
  have hsL : s ∈ c.L := by
    rw [← t.hdL]
    exact t.d.hS.le hsS
  have hsM : s ∈ c.S.M := (c.hyp81.1) hsL
  refine ⟨s * h⁻¹, c.S.M.mul_mem hsM (c.S.M.inv_mem hhM), ?_⟩
  have hxeq : (s * h⁻¹) * x * (s * h⁻¹)⁻¹ = s * x' * s⁻¹ := by
    rw [hx'def]
    group
  rw [hxeq]
  exact hconj

theorem isSylowOf_inf_centralizer_y :
    CFSG.ABGLocalTools.IsSylowOf 3 (t.P ⊓ Subgroup.centralizer ({t.y} : Set G))
      (c.S.M ⊓ Subgroup.centralizer ({t.y} : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let T : Subgroup G := t.P ⊓ Subgroup.centralizer ({t.y} : Set G)
  let K : Subgroup G := c.S.M ⊓ Subgroup.centralizer ({t.y} : Set G)
  have hTK : T ≤ K := inf_le_inf t.hP.le le_rfl
  have hTp : IsPGroup 3 T := t.hP.isPGroup.to_inf_left
  obtain ⟨SylK, hTSylK⟩ := (hTp.comap_subtype (K := K)).exists_le_sylow
  let T₁ : Subgroup G := (SylK : Subgroup K).map K.subtype
  have hT1syl : CFSG.ABGLocalTools.IsSylowOf 3 T₁ K := ⟨SylK, rfl⟩
  have hTleT1 : T ≤ T₁ := fun x hx =>
    Subgroup.mem_map_of_mem K.subtype
      (hTSylK (show (⟨x, hTK hx⟩ : ↥K) ∈ T.subgroupOf K from
        Subgroup.mem_subgroupOf.mpr hx))
  have hT1K : T₁ ≤ K := hT1syl.le
  have hT1M : T₁ ≤ c.S.M := hT1K.trans inf_le_left
  have hT1C : T₁ ≤ Subgroup.centralizer ({t.y} : Set G) := hT1K.trans inf_le_right
  have hT1p : IsPGroup 3 T₁ := hT1syl.isPGroup
  obtain ⟨SylM, hT1SylM⟩ := (hT1p.comap_subtype (K := c.S.M)).exists_le_sylow
  let S'M : Subgroup G := (SylM : Subgroup c.S.M).map c.S.M.subtype
  have hS'Msyl : CFSG.ABGLocalTools.IsSylowOf 3 S'M c.S.M := ⟨SylM, rfl⟩
  obtain ⟨m, hmM, hm⟩ := t.hP.exists_mem_conj hS'Msyl
  have hmP : ∀ x ∈ T₁, m⁻¹ * x * m ∈ t.P := fun x hx =>
    (hm x).mp (Subgroup.mem_map_of_mem c.S.M.subtype
      (hT1SylM (show (⟨x, hT1M hx⟩ : ↥c.S.M) ∈ T₁.subgroupOf c.S.M from
        Subgroup.mem_subgroupOf.mpr hx)))
  have hyT1 : t.y ∈ T₁ :=
    hTleT1 ⟨t.hyP, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  set x : G := m⁻¹ * t.y * m with hxdef
  have hxP : x ∈ t.P := hmP t.y hyT1
  have hxL : x ∉ c.L := by
    intro hxLmem
    apply t.y_not_mem_L
    have hy_eq : t.y = m * x * m⁻¹ := by rw [hxdef]; group
    rw [hy_eq]
    exact (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_L hmM) x).mp hxLmem
  have hxS : x ∉ t.d.S := by
    rw [t.hdS]
    exact fun hx => hxL hx.2
  have hxbase : x ∉ CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y := by
    rw [t.base_eq]
    exact hxS
  have hxmem : x ∈ CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y ⊔
      Subgroup.zpowers t.y := by
    rw [t.base_eq, t.hPy]
    exact hxP
  have hcardx : Nat.card (CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y ⊓
      Subgroup.centralizer ({x} : Set G) : Subgroup G) = Nat.card (t.d.H 0) :=
    CFSG.GroupTheory.WreathThree.card_base_inf_centralizer t.isWreathThree t.hy3 hxmem hxbase
  let f : G →* G := (MulAut.conj m⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj m⁻¹).injective
  let T₁' : Subgroup G := T₁.map f
  have hT1'P : T₁' ≤ t.P := by
    rintro _ ⟨z, hz, rfl⟩
    have hfz : f z = m⁻¹ * z * m := by simp [f, MulAut.conj_apply]
    rw [hfz]
    exact hmP z hz
  have hmap_eq : T₁' ⊓ c.L = (T₁ ⊓ c.L).map f := by
    rw [show T₁' = T₁.map f from rfl, Subgroup.map_inf_eq _ _ f hf]
    congr 1
    show c.L = c.L.map f
    simpa [f] using (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (c.le_normalizer_L (c.S.M.inv_mem hmM))).symm
  have hmap_le : T₁' ⊓ c.L ≤
      CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y ⊓
        Subgroup.centralizer ({x} : Set G) := by
    intro w hw
    rw [hmap_eq] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    have hzT1 : z ∈ T₁ := hz.1
    have hzL : z ∈ c.L := hz.2
    have hfz : f z = m⁻¹ * z * m := by simp [f, MulAut.conj_apply]
    rw [hfz]
    have hzP : m⁻¹ * z * m ∈ t.P := hmP z hzT1
    have hzL' : m⁻¹ * z * m ∈ c.L := by
      have h := (Subgroup.mem_normalizer_iff.mp
        (c.le_normalizer_L (c.S.M.inv_mem hmM)) z).mp hzL
      simpa using h
    refine ⟨?_, ?_⟩
    · rw [t.base_eq, t.hdS]
      exact ⟨hzP, hzL'⟩
    · change m⁻¹ * z * m ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hzy : z * t.y = t.y * z :=
        Subgroup.mem_centralizer_singleton_iff.mp (hT1C hzT1)
      rw [hxdef]
      calc (m⁻¹ * z * m) * (m⁻¹ * t.y * m)
          = m⁻¹ * (z * t.y) * m := by group
        _ = m⁻¹ * (t.y * z) * m := by rw [hzy]
        _ = (m⁻¹ * t.y * m) * (m⁻¹ * z * m) := by group
  have hcardT1'L : Nat.card (T₁' ⊓ c.L : Subgroup G) ≤ Nat.card (t.d.H 0) :=
    (Subgroup.card_le_of_le hmap_le).trans_eq hcardx
  have hSP : t.d.S ≤ t.P := by
    rw [← t.hPy]
    exact le_sup_left
  have hcardP : Nat.card t.P = 3 * Nat.card t.d.S := by
    rw [← t.hPy, ← t.base_eq]
    exact CFSG.GroupTheory.WreathThree.card_sup_zpowers t.isWreathThree t.hy3
  have hrelP : t.d.S.relIndex t.P = 3 := by
    have h := Subgroup.relIndex_mul_card t.d.S t.P
    rw [inf_eq_left.mpr hSP, hcardP] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) h
  have hT1'normL : T₁' ≤ Subgroup.normalizer (c.L : Set G) :=
    hT1'P.trans (t.hP.le.trans c.le_normalizer_L)
  have hPnormL : t.P ≤ Subgroup.normalizer (c.L : Set G) :=
    t.hP.le.trans c.le_normalizer_L
  have hrel_sup {H : Subgroup G}
      (hH : H ≤ Subgroup.normalizer (c.L : Set G)) :
      c.L.relIndex (H ⊔ c.L) = c.L.relIndex H := by
    letI : (c.L.subgroupOf H).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hH
    letI : (c.L.subgroupOf (H ⊔ c.L)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hH
    exact (Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient H c.L hH).toEquiv).symm
  have hidx_le : (T₁' ⊓ c.L).relIndex T₁' ≤ 3 := by
    have hinflT : (T₁' ⊓ c.L).relIndex T₁' = c.L.relIndex T₁' :=
      Subgroup.inf_relIndex_left T₁' c.L
    have hsupT : c.L.relIndex (T₁' ⊔ c.L) = c.L.relIndex T₁' :=
      hrel_sup hT1'normL
    have hinflP : (t.P ⊓ c.L).relIndex t.P = c.L.relIndex t.P :=
      Subgroup.inf_relIndex_left t.P c.L
    have hsupP : c.L.relIndex (t.P ⊔ c.L) = c.L.relIndex t.P :=
      hrel_sup hPnormL
    have hsup_le : T₁' ⊔ c.L ≤ t.P ⊔ c.L :=
      sup_le (hT1'P.trans le_sup_left) le_sup_right
    have hdvd : c.L.relIndex (T₁' ⊔ c.L) ∣ c.L.relIndex (t.P ⊔ c.L) := by
      have h := Subgroup.relIndex_mul_relIndex c.L (T₁' ⊔ c.L) (t.P ⊔ c.L)
        le_sup_right hsup_le
      exact ⟨_, h.symm⟩
    have hdvd' : c.L.relIndex (T₁' ⊔ c.L) ∣ (t.P ⊓ c.L).relIndex t.P := by
      have this := hdvd
      rw [hsupP, ← hinflP] at this
      exact this
    have hdvd'' : c.L.relIndex (T₁' ⊔ c.L) ∣ 3 := by
      have this := hdvd'
      rw [show (t.P ⊓ c.L).relIndex t.P = 3 from by rw [← t.hdS]; exact hrelP] at this
      exact this
    rw [hinflT, ← hsupT]
    exact Nat.le_of_dvd (by norm_num) hdvd''
  have hcardT1' : Nat.card T₁' ≤ 3 * Nat.card (t.d.H 0) := by
    have h := Subgroup.relIndex_mul_card (T₁' ⊓ c.L) T₁'
    have hinf : (T₁' ⊓ c.L) ⊓ T₁' = T₁' ⊓ c.L := by
      rw [inf_comm, ← inf_assoc, inf_idem]
    rw [hinf] at h
    rw [← h]
    exact Nat.mul_le_mul hidx_le hcardT1'L
  have hcardT1 : Nat.card T₁ ≤ 3 * Nat.card (t.d.H 0) := by
    have hmapcard : Nat.card T₁' = Nat.card T₁ :=
      Subgroup.card_map_of_injective (K := T₁) (f := f) hf
    rw [← hmapcard]
    exact hcardT1'
  have hcardT : Nat.card T = 3 * Nat.card (t.d.H 0) := t.card_inf_centralizer_y
  have hle : Nat.card T₁ ≤ Nat.card T := by
    rw [hcardT]
    exact hcardT1
  have hcard_eq : Nat.card T = Nat.card T₁ :=
    le_antisymm (Subgroup.card_le_of_le hTleT1) hle
  have hEq : T = T₁ := Subgroup.eq_of_le_of_card_ge hTleT1 (by omega)
  rw [← hEq] at hT1syl
  exact hT1syl

theorem two_le_pRank_inf_centralizer_AA_of_not_dvd {p : ℕ}
    (hp : p ∈ c.sig) (hpL : ¬ p ∣ Nat.card c.L) :
    2 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (t.d.AA : Set G)) := by
  classical
  have hpp : p.Prime := (c.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp5 : 5 ≤ p := c.five_le_of_mem_sigma hp
  have hp2 : p ≠ 2 := by omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLM : c.L ≤ c.S.M := c.hyp81.1
  have hML : c.S.M ≤ Subgroup.normalizer (c.L : Set G) := c.le_normalizer_L
  let Nbar : Subgroup ↥c.S.M := c.L.subgroupOf c.S.M
  have hNbarNorm : Nbar.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mpr hML
  letI : Nbar.Normal := hNbarNorm
  let Q : Sylow 3 ↥c.L := Classical.choice Sylow.nonempty
  let e : ↥Nbar ≃* ↥c.L := Subgroup.subgroupOfEquivOfLe hLM
  let Pbar : Sylow 3 ↥Nbar := Q.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let T : Subgroup G := (Q : Subgroup ↥c.L).map c.L.subtype
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T c.L := ⟨Q, rfl⟩
  have hTM : T ≤ c.S.M := (Subgroup.map_subtype_le _).trans hLM
  let D : Subgroup G := c.S.M ⊓ Subgroup.normalizer (T : Set G)
  have hNimg : (Pbar : Subgroup ↥Nbar).map Nbar.subtype = T.subgroupOf c.S.M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hPbar : (Pbar : Subgroup ↥Nbar) =
          (Q : Subgroup ↥c.L).map e.symm.toMonoidHom :=
        Sylow.coe_mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective Q
      change y ∈ (Pbar : Subgroup ↥Nbar) at hy
      rw [hPbar] at hy
      obtain ⟨q, hq, hqy⟩ := hy
      have heq : e y = q := by
        rw [← hqy]
        exact e.apply_symm_apply q
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨e y, ?_, ?_⟩)
      · rwa [heq]
      · simp only [Subgroup.coe_subtype]
        rfl
    · intro hx
      obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
      refine Subgroup.mem_map.mpr ⟨e.symm q, ?_, ?_⟩
      · have : e.symm q ∈ (Q : Subgroup ↥c.L).map e.symm.toMonoidHom :=
          Subgroup.mem_map_of_mem _ hq
        simpa [Pbar, Sylow.coe_mapSurjective] using this
      · apply Subtype.ext
        change ((e.symm q : ↥Nbar) : G) = (x : G)
        exact hqeq
  have hMD : c.S.M = D ⊔ c.L := by
    have hfr := Sylow.normalizer_sup_eq_top (p := 3) Pbar
    have h := congrArg (Subgroup.map c.S.M.subtype) hfr
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at h
    have hNmap : Nbar.map c.S.M.subtype = c.L := by
      rw [show Nbar = c.L.subgroupOf c.S.M from rfl, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hLM]
    rw [hNimg, ← Subgroup.subgroupOf_normalizer_eq hTM,
      Subgroup.subgroupOf_map_subtype, hNmap, inf_comm] at h
    exact h.symm
  obtain ⟨R, hRsylD⟩ := CFSG.ABGLocalTools.exists_isSylowOf p D
  have hRD : R ≤ D := hRsylD.le
  have hRM : R ≤ c.S.M := hRD.trans inf_le_left
  have hDnormL : D ≤ Subgroup.normalizer (c.L : Set G) := inf_le_left.trans hML
  have hcard_sup : Nat.card ↥(c.L ⊔ D) * Nat.card ↥(c.L ⊓ D) =
      Nat.card ↥c.L * Nat.card ↥D := by
    have h1 : c.L.relIndex (D ⊔ c.L) * Nat.card c.L = Nat.card ↥(D ⊔ c.L) := by
      have h := Subgroup.relIndex_mul_card (H := c.L) (K := D ⊔ c.L)
      rwa [inf_eq_left.mpr le_sup_right] at h
    have h2 : c.L.relIndex D * Nat.card ↥(c.L ⊓ D) = Nat.card D :=
      Subgroup.relIndex_mul_card (H := c.L) (K := D)
    have h3 : c.L.relIndex (D ⊔ c.L) = c.L.relIndex D := by
      letI : (c.L.subgroupOf D).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hDnormL
      letI : (c.L.subgroupOf (D ⊔ c.L)).Normal :=
        Subgroup.normal_subgroupOf_sup_of_le_normalizer hDnormL
      exact (Nat.card_congr
        (QuotientGroup.quotientInfEquivProdNormalizerQuotient D c.L hDnormL).toEquiv).symm
    calc
      Nat.card ↥(c.L ⊔ D) * Nat.card ↥(c.L ⊓ D)
          = Nat.card ↥(D ⊔ c.L) * Nat.card ↥(c.L ⊓ D) := by rw [sup_comm]
      _ = (c.L.relIndex (D ⊔ c.L) * Nat.card c.L) * Nat.card ↥(c.L ⊓ D) := by rw [h1]
      _ = (c.L.relIndex D * Nat.card c.L) * Nat.card ↥(c.L ⊓ D) := by rw [h3]
      _ = Nat.card c.L * (c.L.relIndex D * Nat.card ↥(c.L ⊓ D)) := by ac_rfl
      _ = Nat.card c.L * Nat.card D := by rw [h2]
  have hLD : c.L ⊔ D = c.S.M := by rw [sup_comm]; exact hMD.symm
  have hcardM : Nat.card c.S.M * Nat.card (c.L ⊓ D : Subgroup G) =
      Nat.card c.L * Nat.card D := by
    rw [← hLD]
    exact hcard_sup
  have hp_eq : (Nat.card c.S.M).factorization p = (Nat.card D).factorization p := by
    have hLp : (Nat.card c.L).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hpL
    have hLDp : (Nat.card (c.L ⊓ D : Subgroup G)).factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdvd
      exact hpL (hdvd.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hfac : (Nat.card c.S.M * Nat.card (c.L ⊓ D : Subgroup G)).factorization p =
        (Nat.card c.L * Nat.card D).factorization p := by rw [hcardM]
    rw [Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
      Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply,
      Finsupp.add_apply, hLp, hLDp, add_zero, zero_add] at hfac
    exact hfac
  have hRsylM : CFSG.ABGLocalTools.IsSylowOf p R c.S.M := by
    apply CFSG.ABGLocalTools.isSylowOf_of_card hRM
    rw [hRsylD.card_eq, hp_eq]
  have hRrank : c.k ≤ CFSG.Open.pRank p R := by
    have hRrank_eq : CFSG.Open.pRank p R = CFSG.Open.pRank p c.S.M := by
      obtain ⟨Q, hQ⟩ := hRsylM.exists_sylow_eq_subgroupOf
      have hRmap : (Q : Subgroup ↥c.S.M).map c.S.M.subtype = R := by
        rw [hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRM]
      calc
        CFSG.Open.pRank p R
            = CFSG.Open.pRank p ((Q : Subgroup ↥c.S.M).map c.S.M.subtype) := by
                rw [hRmap]
        _ = CFSG.pRank p ↥((Q : Subgroup ↥c.S.M).map c.S.M.subtype) :=
              (CFSG.SectionRank.pRank_coe_eq_openPRank p _).symm
        _ = CFSG.pRank p ↥(Q : Subgroup ↥c.S.M) :=
              (CFSG.pRank_congr_of_mulEquiv
                (Subgroup.equivMapOfInjective (Q : Subgroup ↥c.S.M) c.S.M.subtype
                  c.S.M.subtype_injective) p).symm
        _ = CFSG.Open.pRank p (Q : Subgroup ↥c.S.M) :=
              CFSG.SectionRank.pRank_coe_eq_openPRank p _
        _ = CFSG.Open.pRank p (⊤ : Subgroup ↥c.S.M) :=
              (CFSG.SectionRank.pRank_sylow Q).1
        _ = CFSG.Open.pRank p c.S.M := by
              rw [← CFSG.SectionRank.pRank_eq_open_pRank_top p ↥c.S.M,
                CFSG.SectionRank.pRank_coe_eq_openPRank p c.S.M]
    rw [hRrank_eq]
    exact c.rank_ge p hp
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 3 t.d.S c.L := by
    simpa [t.hdL] using t.d.hS
  obtain ⟨l, hlL, hl⟩ := hSsyl.exists_mem_conj hTsyl
  have hlL' : l⁻¹ ∈ c.L := c.L.inv_mem hlL
  have hlM : l ∈ c.S.M := c.hyp81.1 hlL
  have hlM' : l⁻¹ ∈ c.S.M := c.hyp81.1 hlL'
  have hTmap : T.map (MulAut.conj l⁻¹).toMonoidHom = t.d.S := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using (hl y).mp hy
    · intro hx
      refine ⟨l * x * l⁻¹, (hl (l * x * l⁻¹)).mpr ?_, ?_⟩
      · have hx' : l⁻¹ * (l * x * l⁻¹) * l = x := by group
        rwa [hx']
      · show (MulAut.conj l⁻¹) (l * x * l⁻¹) = x
        rw [MulAut.conj_apply]
        group
  let R' : Subgroup G := R.map (MulAut.conj l⁻¹).toMonoidHom
  have hR'cent : R' ≤ c.S.M ⊓ Subgroup.centralizer (t.d.AA : Set G) := by
    refine le_inf ?_ ?_
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := hx
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
        c.S.M.mul_mem (c.S.M.mul_mem hlM' (hRM hr)) hlM
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := hx
      rw [Subgroup.mem_centralizer_iff]
      have hrN : r ∈ Subgroup.normalizer (T : Set G) := (hRD hr).2
      have hnormmap : (Subgroup.normalizer (T : Set G)).map
          (MulAut.conj l⁻¹).toMonoidHom =
          Subgroup.normalizer (t.d.S : Set G) := by
        rw [Subgroup.map_normalizer_eq_of_bijective T (MulAut.conj l⁻¹).bijective, hTmap]
      have hxS : (MulAut.conj l⁻¹) r ∈ Subgroup.normalizer (t.d.S : Set G) :=
        hnormmap ▸ Subgroup.mem_map_of_mem _ hrN
      have hxM : (MulAut.conj l⁻¹) r ∈ c.S.M := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
          c.S.M.mul_mem (c.S.M.mul_mem hlM' (hRM hr)) hlM
      have hR'p : IsPGroup p R' := hRsylD.isPGroup.map _
      have hxpow : IsPGroup p (Subgroup.zpowers ((MulAut.conj l⁻¹) r)) :=
        hR'p.to_le (Subgroup.zpowers_le.mpr ⟨r, hr, rfl⟩)
      have hxLf : ∀ i, (MulAut.conj l⁻¹) r ∈
          Subgroup.normalizer ((t.d.Lf i : Subgroup G) : Set G) := by
        intro i
        exact t.d.le_normalizer_Lf_of_isPGroup hp5 t.hinj
          (fun m hm i => t.hperm m (t.hdM ▸ hm) i) (t.hdM.symm ▸ hxM) hxpow i
      have hcent := t.d.centralizes_AA_of_isPGroup hpp hp2 hxpow hxS hxLf
      intro a ha
      exact (hcent a ha).symm
  have hR'rank : c.k ≤ CFSG.Open.pRank p R' := by
    rw [show R' = R.map (MulAut.conj l⁻¹).toMonoidHom from rfl,
      ← CFSG.SectionRank.pRank_coe_eq_openPRank p
        (R.map (MulAut.conj l⁻¹).toMonoidHom),
      ← CFSG.pRank_congr_of_mulEquiv
        (Subgroup.equivMapOfInjective R (MulAut.conj l⁻¹).toMonoidHom
          (MulAut.conj l⁻¹).injective) p,
      CFSG.SectionRank.pRank_coe_eq_openPRank p R]
    exact hRrank
  have hmono : CFSG.Open.pRank p R' ≤
      CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (t.d.AA : Set G)) :=
    CFSG.SectionRank.pRank_mono hpp.one_lt hR'cent
  have hk3 := c.three_le_k
  omega

theorem normalizer_le_of_le_AA_of_not_dvd {p : ℕ}
    (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (hpL : ¬ p ∣ Nat.card c.L) {Y : Subgroup G} (hY : Y ≤ t.d.AA) (hY1 : Y ≠ ⊥) :
    Subgroup.normalizer (Y : Set G) ≤ c.S.M := by
  have hpp : p.Prime := (c.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAAL : t.d.AA ≤ c.L := t.hdL ▸ t.d.AA_le_L
  have hBM : t.d.AA ≤ c.S.M := hAAL.trans c.hyp81.1
  have hB : IsPGroup 3 t.d.AA := t.d.isElemAbelian_AA.isPGroup
  have hBr : 2 ≤ CFSG.Open.pRank 3 t.d.AA := by
    have hcard : Nat.card t.d.AA = 3 ^ 3 := by rw [t.d.card_AA]; norm_num
    have hle := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl
      t.d.isElemAbelian_AA hcard
    omega
  exact
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.normalizer_le_of_two_le_pRank_inf_centralizer
      (p := p) (r := 3) (M := c.S.M) (B := t.d.AA)
      (c.isStronglyPEmbedded_of_mem_sigma hp) h76 hBM hB hBr
      (t.two_le_pRank_inf_centralizer_AA_of_not_dvd hp hpL) Y hY hY1

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
