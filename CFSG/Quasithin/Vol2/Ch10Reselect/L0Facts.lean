module

public import CFSG.Quasithin.Vol2.Ch10Reselect.Basic
public import CFSG.Quasithin.Vol2.Ch10Reselect.GroupLemmas

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

private lemma eq_bot_of_two_power_normal {Q : Type*} [Group Q] [Finite Q] (hs : IsSimpleGroup Q)
    (hz : Subgroup.center Q = ⊥) (N : Subgroup Q) [N.Normal]
    (hN : ∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) = 1) : N = ⊥ := by
  haveI := hs
  rcases hs.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have hP : IsPGroup 2 Q := fun q => hN q (by rw [h]; exact Subgroup.mem_top q)
    have hnt : Nontrivial ↥(Subgroup.center Q) := IsPGroup.center_nontrivial hP
    exact ((Subgroup.nontrivial_iff_ne_bot _).mp hnt) hz

theorem isSimpleGroup_quot_of_fsu (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L) :
    IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hz := center_quot_eq_bot_of_fsu h37 h38 hfsu (not_le_normalizer_of_lt hlt)
  have hs := hfsu.quasisimple.2.1
  haveI := hs
  exact MulEquiv.isSimpleGroup
    (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm)

theorem mem_pCoreOf_of_commutators_mem
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hlt : L < fsuL0 T L) {k : G} (hk : k ∈ fsuL0 T L)
    (h : ∀ l ∈ fsuL0 T L, ⁅k, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) :
    k ∈ pCoreOf 2 (fsuL0 T L) := by
  have hnn := not_le_normalizer_of_lt hlt
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hnn
  obtain ⟨φ, -, hker, hL, hLt⟩ := exists_fsuL0_prod_of_fsu h37 h38 hfsu hnn ht htn
  have hz₁ := center_quot_eq_bot_of_fsu h37 h38 hfsu hnn
  have hz₂ := center_quot_conjugate_eq_bot_of_fsu h37 h38 hfsu hnn ht htn
  have hcomm : ∀ l : fsuL0 T L, φ ⁅(⟨k, hk⟩ : fsuL0 T L), l⁆ = 1 := by
    intro l
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    have hmem : ⁅k, (l : G)⁆ ∈ fsuL0 T L := by
      rw [commutatorElement_def]
      exact (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem hk l.2)
        ((fsuL0 T L).inv_mem hk)) ((fsuL0 T L).inv_mem l.2)
    have hc : ((⁅(⟨k, hk⟩ : fsuL0 T L), l⁆ : fsuL0 T L) : G) = ⁅k, (l : G)⁆ := by
      simp [commutatorElement_def]
    rw [hc]
    exact fsuL0_inf_centralizer_le_of_fsu h37 h38 hfsu hnn ⟨hmem, h _ l.2⟩
  have hA : ∀ g : ↥L ⧸ CFSG.pCore 2 ↥L, ⁅(φ ⟨k, hk⟩).1, g⁆ = 1 := by
    intro g
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 := hcomm ⟨l, le_fsuL0 T L hl⟩
    rw [map_commutatorElement, hL l hl] at h1
    have h2 := congrArg (MonoidHom.fst _ _) h1
    simpa [map_commutatorElement] using h2
  have ha : (φ ⟨k, hk⟩).1 = 1 := by
    have hc : (φ ⟨k, hk⟩).1 ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
      Subgroup.mem_center_iff.mpr fun g => (commutatorElement_eq_one_iff_mul_comm.mp (hA g)).symm
    rwa [hz₁, Subgroup.mem_bot] at hc
  have hB : ∀ g : ↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t),
      ⁅(φ ⟨k, hk⟩).2, g⁆ = 1 := by
    intro g
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 := hcomm ⟨l, conjugate_le_fsuL0 ht hl⟩
    rw [map_commutatorElement, hLt l hl] at h1
    have h2 := congrArg (MonoidHom.snd _ _) h1
    simpa [map_commutatorElement] using h2
  have hb : (φ ⟨k, hk⟩).2 = 1 := by
    have hc : (φ ⟨k, hk⟩).2 ∈
        Subgroup.center (↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t)) :=
      Subgroup.mem_center_iff.mpr fun g => (commutatorElement_eq_one_iff_mul_comm.mp (hB g)).symm
    rwa [hz₂, Subgroup.mem_bot] at hc
  have hφ : φ ⟨k, hk⟩ = 1 := Prod.ext ha hb
  have hmem : (⟨k, hk⟩ : fsuL0 T L) ∈ φ.ker := hφ
  rw [hker, Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem le_pCoreOf_fsuL0_of_two_power
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hlt : L < fsuL0 T L) {W : Subgroup G} (hW : W ≤ fsuL0 T L)
    (hWn : fsuL0 T L ≤ Subgroup.normalizer (W : Set G))
    (h2 : ∀ x ∈ W, ∃ k : ℕ, x ^ (2 ^ k) ∈ Subgroup.centralizer (fsuVM T L I : Set G)) :
    W ≤ pCoreOf 2 (fsuL0 T L) := by
  have hnn := not_le_normalizer_of_lt hlt
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hnn
  obtain ⟨φ, hsurj, hker, hL, hLt⟩ := exists_fsuL0_prod_of_fsu h37 h38 hfsu hnn ht htn
  have hz₁ := center_quot_eq_bot_of_fsu h37 h38 hfsu hnn
  have hz₂ := center_quot_conjugate_eq_bot_of_fsu h37 h38 hfsu hnn ht htn
  have hs₁ := isSimpleGroup_quot_of_fsu h37 h38 hfsu hlt
  have hs₂ := isSimpleGroup_conjugate_of_fsu h37 h38 hfsu hnn ht htn
  have hker' : ∀ u : fsuL0 T L,
      (u : G) ∈ fsuL0 T L ⊓ Subgroup.centralizer (fsuVM T L I : Set G) → φ u = 1 := by
    intro u hu
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    exact fsuL0_inf_centralizer_le_of_fsu h37 h38 hfsu hnn hu
  have hpow : ∀ w : fsuL0 T L, (w : G) ∈ W → ∃ k : ℕ, φ w ^ (2 ^ k) = 1 := by
    intro w hw
    obtain ⟨k, hk⟩ := h2 _ hw
    refine ⟨k, ?_⟩
    have h3 : φ (w ^ (2 ^ k)) = 1 := by
      apply hker'
      refine ⟨(w ^ (2 ^ k)).2, ?_⟩
      rw [Subgroup.coe_pow]
      exact hk
    rwa [map_pow] at h3
  have hNW : (W.subgroupOf (fsuL0 T L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hW).mpr hWn
  have hD : ((W.subgroupOf (fsuL0 T L)).map φ).Normal := hNW.map φ hsurj
  have hbot₁ : ((W.subgroupOf (fsuL0 T L)).map φ).map (MonoidHom.fst _ _) = ⊥ := by
    haveI : ((W.subgroupOf (fsuL0 T L)).map φ).Normal := hD
    haveI : (((W.subgroupOf (fsuL0 T L)).map φ).map (MonoidHom.fst _ _)).Normal :=
      hD.map (MonoidHom.fst _ _) (fun a => ⟨(a, 1), rfl⟩)
    apply eq_bot_of_two_power_normal hs₁ hz₁
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hd
    obtain ⟨k, hk⟩ := hpow w (Subgroup.mem_subgroupOf.mp hw)
    refine ⟨k, ?_⟩
    have h4 := congrArg (MonoidHom.fst _ _) hk
    simpa [map_pow] using h4
  have hbot₂ : ((W.subgroupOf (fsuL0 T L)).map φ).map (MonoidHom.snd _ _) = ⊥ := by
    haveI : ((W.subgroupOf (fsuL0 T L)).map φ).Normal := hD
    haveI : (((W.subgroupOf (fsuL0 T L)).map φ).map (MonoidHom.snd _ _)).Normal :=
      hD.map (MonoidHom.snd _ _) (fun a => ⟨(1, a), rfl⟩)
    apply eq_bot_of_two_power_normal hs₂ hz₂
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hd
    obtain ⟨k, hk⟩ := hpow w (Subgroup.mem_subgroupOf.mp hw)
    refine ⟨k, ?_⟩
    have h4 := congrArg (MonoidHom.snd _ _) hk
    simpa [map_pow] using h4
  intro w hw
  have hwL : w ∈ fsuL0 T L := hW hw
  have hmem : (⟨w, hwL⟩ : fsuL0 T L) ∈ W.subgroupOf (fsuL0 T L) := Subgroup.mem_subgroupOf.mpr hw
  have h1 : (φ ⟨w, hwL⟩).1 = 1 := by
    have hm : MonoidHom.fst _ _ (φ ⟨w, hwL⟩) ∈
        ((W.subgroupOf (fsuL0 T L)).map φ).map (MonoidHom.fst _ _) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem φ hmem)
    rw [hbot₁, Subgroup.mem_bot] at hm
    exact hm
  have h2' : (φ ⟨w, hwL⟩).2 = 1 := by
    have hm : MonoidHom.snd _ _ (φ ⟨w, hwL⟩) ∈
        ((W.subgroupOf (fsuL0 T L)).map φ).map (MonoidHom.snd _ _) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem φ hmem)
    rw [hbot₂, Subgroup.mem_bot] at hm
    exact hm
  have hφ : φ ⟨w, hwL⟩ = 1 := Prod.ext h1 h2'
  have hker_mem : (⟨w, hwL⟩ : fsuL0 T L) ∈ φ.ker := hφ
  rw [hker, Subgroup.mem_subgroupOf] at hker_mem
  exact hker_mem

theorem pCoreOf_fsuL0_le_centralizer_fsuVM (h322 : Ch10.TmpL6_3_2_2_two) (hfsu : FSU G T L I) :
    pCoreOf 2 (fsuL0 T L) ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
  obtain ⟨hAM, hA⟩ := h322 G T L I hfsu
  have hNM : pCoreOf 2 (fsuL0 T L) ≤ fsuM T L :=
    (Subgroup.map_subtype_le _).trans Subgroup.le_normalizer
  have hN : ((pCoreOf 2 (fsuL0 T L)).subgroupOf (fsuM T L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (fsuL0 T L))
  refine le_centralizer_of_normal_of_two_power hAM hA hNM hN fun x hx => ?_
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (fsuL0 T L) ⟨x, hx⟩
  refine ⟨k, ?_⟩
  have hx1 : x ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [hx1]
  exact Subgroup.one_mem _

theorem le_centralizer_of_two_power_of_le_fsuL0
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L) {W : Subgroup G}
    (hW : W ≤ fsuL0 T L) (hWn : fsuL0 T L ≤ Subgroup.normalizer (W : Set G))
    (h2 : ∀ x ∈ W, ∃ k : ℕ, x ^ (2 ^ k) ∈ Subgroup.centralizer (fsuVM T L I : Set G)) :
    W ≤ Subgroup.centralizer (fsuVM T L I : Set G) :=
  (le_pCoreOf_fsuL0_of_two_power h37 h38 hfsu hlt hW hWn h2).trans
    (pCoreOf_fsuL0_le_centralizer_fsuVM h322 hfsu)

theorem isElemAbelian_fsuVM_of_h322 (h322 : Ch10.TmpL6_3_2_2_two) (hfsu : FSU G T L I) :
    IsElemAbelian 2 (fsuVM T L I) := by
  obtain ⟨hAM, hA⟩ := h322 G T L I hfsu
  obtain ⟨-, hel, -⟩ := hA
  obtain ⟨hcomm, hsq⟩ := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mp hel
  refine ⟨?_, fun x hx => ?_⟩
  · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have h1 := congrArg Subtype.val (hcomm.is_comm.comm
      (⟨⟨(a : G), hAM a.2⟩, Subgroup.mem_subgroupOf.mpr a.2⟩ :
        ↥((fsuVM T L I).subgroupOf (fsuM T L)))
      (⟨⟨(b : G), hAM b.2⟩, Subgroup.mem_subgroupOf.mpr b.2⟩ :
        ↥((fsuVM T L I).subgroupOf (fsuM T L))))
    simpa using h1
  · have hxM : (⟨x, hAM hx⟩ : ↥(fsuM T L)) ∈ (fsuVM T L I).subgroupOf (fsuM T L) :=
      Subgroup.mem_subgroupOf.mpr hx
    have h1 := congrArg Subtype.val (hsq _ hxM)
    simpa using h1

theorem fsuVM_le_T_of_h322 (h322 : Ch10.TmpL6_3_2_2_two) (hfsu : FSU G T L I) :
    fsuVM T L I ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAM, hA⟩ := h322 G T L I hfsu
  obtain ⟨hn, -, -⟩ := hA
  haveI := hn
  have hPV : IsPGroup 2 (fsuVM T L I) := fun x => ⟨1, by
    simpa using Subtype.ext ((isElemAbelian_fsuVM_of_h322 h322 hfsu).2 x x.2)⟩
  have hp : IsPGroup 2 ((fsuVM T L I).subgroupOf (fsuM T L)) :=
    hPV.comap_of_injective _ (Subgroup.subtype_injective _)
  have hT : IsPGroup 2 (T.subgroupOf (fsuM T L)) :=
    hfsu.sylow.1.comap_of_injective _ (Subgroup.subtype_injective _)
  have hle := hp.le_sylow_of_normal (hT.toSylow (not_two_dvd_index_of_le hfsu.sylow
    (le_fsuM T L)))
  intro v hv
  have h1 := hle (show (⟨v, hAM hv⟩ : ↥(fsuM T L)) ∈
    (fsuVM T L I).subgroupOf (fsuM T L) from hv)
  rw [IsPGroup.toSylow_coe, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem fsuVM_le_sup_of_h322 (h322 : Ch10.TmpL6_3_2_2_two) (hfsu : FSU G T L I) :
    fsuVM T L I ≤ L ⊔ T :=
  (fsuVM_le_T_of_h322 h322 hfsu).trans le_sup_right

end CFSG.Quasithin.Vol2.Ch10Reselect
