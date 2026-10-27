module

public import CFSG.Quasithin.Vol2.Ch11SecOE1B
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Vol2.Ch3Sec3Comp
public import CFSG.Quasithin.Vol2.Ch4Sec4Rem442
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic


public section

namespace CFSG.Quasithin.Vol2.Ch11.OE1

open Subgroup CFSG.Quasithin
open CFSG.Open (pCoreOf)
open CFSG.LieType.BorelTits (normalizer_le_normalizer_pCoreOf le_pCoreOf_of_le_normalizer)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_commutator {H K : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, map_commutator]
  exact congrArg₂ (fun A B : Subgroup G => ⁅A, B⁆) (map_conj_eq_self hH) (map_conj_eq_self hK)

theorem thompsonJ_le (T : Subgroup G) : thompsonJ T ≤ T :=
  iSup_le fun _ => iSup_le fun hA => hA.1

theorem commutator_conjClosure_le {K L T N : Subgroup G} (hTK : T ≤ normalizer (K : Set G))
    (hTN : T ≤ normalizer (N : Set G)) (hL₀N : conjClosure L T ≤ normalizer (N : Set G))
    (hKL : ⁅K, L⁆ ≤ N) : ⁅K, conjClosure L T⁆ ≤ N := by
  have key : ∀ g ∈ conjClosure L T, ∀ k ∈ K, ⁅k, g⁆ ∈ N := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨t, ht, l, hl, rfl⟩ := hx
      intro k hk
      have hk' : t⁻¹ * k * t⁻¹⁻¹ ∈ K := (mem_normalizer_iff.mp (hTK (T.inv_mem ht)) k).mp hk
      rw [inv_inv] at hk'
      have e : ⁅k, t * l * t⁻¹⁆ = t * ⁅t⁻¹ * k * t, l⁆ * t⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (mem_normalizer_iff.mp (hTN ht) _).mp (hKL (commutator_mem_commutator hk' hl))
    | one =>
      intro k _
      rw [commutatorElement_one_right]
      exact N.one_mem
    | mul x y hx _ ihx ihy =>
      intro k hk
      have e : ⁅k, x * y⁆ = ⁅k, x⁆ * (x * ⁅k, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact N.mul_mem (ihx k hk) ((mem_normalizer_iff.mp (hL₀N hx) _).mp (ihy k hk))
    | inv x hx ih =>
      intro k hk
      have e : ⁅k, x⁻¹⁆ = x⁻¹ * ⁅k, x⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (mem_normalizer_iff.mp (hL₀N (inv_mem hx)) _).mp (N.inv_mem (ih k hk))
  exact commutator_le.mpr fun k hk g hg => key g hg k hk

theorem isPGroup_quotient_of_map_eq_top {K L : Subgroup G} [(K.subgroupOf L).Normal]
    (htop : (K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤) :
    IsPGroup 2 (↥L ⧸ K.subgroupOf L) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hy : QuotientGroup.mk' (CFSG.pCore 2 ↥L) y ∈
      (K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    rw [htop]
    exact mem_top _
  obtain ⟨k, hk, hky⟩ := hy
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hky
  obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (⟨_, hky⟩ : ↥(CFSG.pCore 2 ↥L))
  have hn' : (k⁻¹ * y) ^ 2 ^ n = 1 := congrArg Subtype.val hn
  refine ⟨n, ?_⟩
  have hk1 : ((k : ↥L) : ↥L ⧸ K.subgroupOf L) = 1 := (QuotientGroup.eq_one_iff k).mpr hk
  have e : ((y : ↥L) : ↥L ⧸ K.subgroupOf L) = ((k⁻¹ * y : ↥L) : ↥L ⧸ K.subgroupOf L) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hk1, inv_one, one_mul]
  rw [e, ← QuotientGroup.mk_pow, hn', QuotientGroup.mk_one]

theorem commutator_mem_of_map_le_center {K L : Subgroup G}
    (hc : (K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≤
      center (↥L ⧸ CFSG.pCore 2 ↥L))
    {k l : G} (hk : k ∈ K) (hkL : k ∈ L) (hl : l ∈ L) : ⁅k, l⁆ ∈ pCoreOf 2 L := by
  have hkc : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨k, hkL⟩ ∈ center (↥L ⧸ CFSG.pCore 2 ↥L) :=
    hc (mem_map_of_mem _ (mem_subgroupOf.mpr hk))
  have hcomm := Subgroup.mem_center_iff.mp hkc (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨l, hl⟩)
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⁅(⟨k, hkL⟩ : ↥L), ⟨l, hl⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hcomm]
  have h2 : ⁅(⟨k, hkL⟩ : ↥L), ⟨l, hl⟩⁆ ∈ CFSG.Open.pCore 2 ↥L := by
    have h := (MonoidHom.mem_ker (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L))).mpr h1
    rwa [QuotientGroup.ker_mk'] at h
  exact ⟨_, h2, rfl⟩

theorem le_or_commutator_le [Finite G] {K L T : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hL₀L : conjClosure L T ≤ normalizer (L : Set G)) (hKL₀ : K ≤ conjClosure L T)
    (hL₀K : conjClosure L T ≤ normalizer (K : Set G)) (hTK : T ≤ normalizer (K : Set G)) :
    conjClosure L T ≤ K ∨ ⁅K, conjClosure L T⁆ ≤ pCoreOf 2 (conjClosure L T) := by
  have hLL₀ : L ≤ conjClosure L T := le_conjClosure L T
  have hTL₀ : T ≤ normalizer (conjClosure L T : Set G) := le_normalizer_conjClosure L T
  have hLK : L ≤ normalizer (K : Set G) := hLL₀.trans hL₀K
  have hKn : (K.subgroupOf L).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.mp (hLK g.2) n).mp hn⟩
  have hmapn : ((K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
    hKn.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
    (B1Red.isQuasisimple_to_open hq)
    ((K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with hc | htop
  ·
    right
    have hKLK : ⁅K, L⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hLK
    have hKLL : ⁅K, L⁆ ≤ L :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp (hKL₀.trans hL₀L)
    have h1 : ⁅⁅K, L⁆, L⁆ ≤ pCoreOf 2 L := commutator_le.mpr fun x hx l hl =>
      commutator_mem_of_map_le_center hc (hKLK hx) (hKLL hx) hl
    have hNL : L ≤ normalizer (pCoreOf 2 L : Set G) :=
      le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 L)
    have hNK : K ≤ normalizer (pCoreOf 2 L : Set G) :=
      (hKL₀.trans hL₀L).trans (normalizer_le_normalizer_pCoreOf 2 L)
    have h3 : ⁅⁅L, L⁆, K⁆ ≤ pCoreOf 2 L :=
      H13.three_subgroups_le (X := L) (Y := K) (Z := L) hNL hNK hNL
        (by rw [Subgroup.commutator_comm L K]; exact h1) h1
    rw [hperf, Subgroup.commutator_comm] at h3
    have hOO : pCoreOf 2 L ≤ pCoreOf 2 (conjClosure L T) :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L _ hLL₀
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hLL₀).mpr hL₀L)
    exact commutator_conjClosure_le hTK
      (hTL₀.trans (normalizer_le_normalizer_pCoreOf 2 _))
      (le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 _)) (h3.trans hOO)
  ·
    left
    have hLK' : L ≤ K :=
      H13.Ch3Sec3.le_of_isPGroup_quotient hperf (isPGroup_quotient_of_map_eq_top htop)
    exact conjClosure_le fun t ht l hl => (mem_normalizer_iff.mp (hTK ht) l).mp (hLK' hl)

theorem le_pCoreOf_sup_of_commutator_le [Finite G] {L₀ T J : Subgroup G} (hT : IsPGroup 2 T)
    (hTL₀ : T ≤ normalizer (L₀ : Set G)) (hOT : pCoreOf 2 L₀ ≤ T) (hJT : J ≤ T)
    (hJ : ⁅L₀, J⁆ ≤ pCoreOf 2 L₀) : J ≤ pCoreOf 2 (L₀ ⊔ T) := by
  set N := pCoreOf 2 L₀ with hN
  have hTN : T ≤ normalizer (N : Set G) := hTL₀.trans (normalizer_le_normalizer_pCoreOf 2 L₀)
  have hL₀N : L₀ ≤ normalizer (N : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 L₀)
  let R : Subgroup G :=
    { carrier := {t | t ∈ T ∧ ∀ l ∈ L₀, ⁅t, l⁆ ∈ N}
      mul_mem' := by
        rintro a b ⟨ha, hal⟩ ⟨hb, hbl⟩
        refine ⟨T.mul_mem ha hb, fun l hl => ?_⟩
        have e : ⁅a * b, l⁆ = a * ⁅b, l⁆ * a⁻¹ * ⁅a, l⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem ((mem_normalizer_iff.mp (hTN ha) _).mp (hbl l hl)) (hal l hl)
      one_mem' := ⟨T.one_mem, fun l _ => by
        rw [commutatorElement_one_left]
        exact N.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, hal⟩
        refine ⟨T.inv_mem ha, fun l hl => ?_⟩
        have e : ⁅a⁻¹, l⁆ = a⁻¹ * ⁅a, l⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (mem_normalizer_iff.mp (hTN (T.inv_mem ha)) _).mp (N.inv_mem (hal l hl)) }
  have hmemR : ∀ t, t ∈ R ↔ t ∈ T ∧ ∀ l ∈ L₀, ⁅t, l⁆ ∈ N := fun t => Iff.rfl
  have hRT : R ≤ T := fun t ht => ((hmemR t).mp ht).1
  have hJR : J ≤ R := fun j hj => (hmemR j).mpr ⟨hJT hj, fun l hl => by
    rw [← commutatorElement_inv]
    exact N.inv_mem (hJ (commutator_mem_commutator hl hj))⟩
  have hTR : T ≤ normalizer (R : Set G) := Subgroup.le_normalizer_iff.mpr fun s hs t ht => by
    obtain ⟨htT, htl⟩ := (hmemR t).mp ht
    refine (hmemR _).mpr ⟨T.mul_mem (T.mul_mem hs htT) (T.inv_mem hs), fun l hl => ?_⟩
    have hl' : s⁻¹ * l * s⁻¹⁻¹ ∈ L₀ := (mem_normalizer_iff.mp (hTL₀ (T.inv_mem hs)) l).mp hl
    rw [inv_inv] at hl'
    have e : ⁅s * t * s⁻¹, l⁆ = s * ⁅t, s⁻¹ * l * s⁆ * s⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (mem_normalizer_iff.mp (hTN hs) _).mp (htl _ hl')
  have hL₀R : L₀ ≤ normalizer (R : Set G) := Subgroup.le_normalizer_iff.mpr fun g hg t ht => by
    obtain ⟨htT, htl⟩ := (hmemR t).mp ht
    have ho : ⁅g, t⁆ ∈ N := by
      rw [← commutatorElement_inv]
      exact N.inv_mem (htl g hg)
    have e : g * t * g⁻¹ = ⁅g, t⁆ * t := by simp only [commutatorElement_def]; group
    rw [e]
    refine (hmemR _).mpr ⟨T.mul_mem (hOT ho) htT, fun l hl => ?_⟩
    have e' : ⁅⁅g, t⁆ * t, l⁆ = ⁅g, t⁆ * ⁅t, l⁆ * ⁅g, t⁆⁻¹ * (⁅g, t⁆ * (l * ⁅g, t⁆⁻¹ * l⁻¹)) := by
      simp only [commutatorElement_def]; group
    rw [e']
    refine N.mul_mem ((mem_normalizer_iff.mp (le_normalizer ho) _).mp (htl l hl))
      (N.mul_mem ho ?_)
    exact (mem_normalizer_iff.mp (hL₀N hl) _).mp (N.inv_mem ho)
  have hR2 : IsPGroup 2 R := hT.to_le hRT
  exact hJR.trans (le_pCoreOf_of_le_normalizer 2 (hRT.trans le_sup_right) (sup_le hL₀R hTR) hR2)

theorem eq_commutator_thompsonJ [Finite G] {L T : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hT : IsPGroup 2 T)
    (hL₀L : conjClosure L T ≤ normalizer (L : Set G)) (hOT : pCoreOf 2 (conjClosure L T) ≤ T)
    (hJ : ¬ thompsonJ T ≤ pCoreOf 2 (conjClosure L T ⊔ T)) :
    conjClosure L T = ⁅conjClosure L T, thompsonJ T⁆ := by
  have hTL₀ : T ≤ normalizer (conjClosure L T : Set G) := le_normalizer_conjClosure L T
  have hJT : thompsonJ T ≤ T := thompsonJ_le T
  have hJL₀ : thompsonJ T ≤ normalizer (conjClosure L T : Set G) := hJT.trans hTL₀
  have hKL₀ : ⁅conjClosure L T, thompsonJ T⁆ ≤ conjClosure L T :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hJL₀
  have hL₀K := Subgroup.normalizer_commutator_ge_left (conjClosure L T) (thompsonJ T)
  have hTK : T ≤ normalizer ((⁅conjClosure L T, thompsonJ T⁆ : Subgroup G) : Set G) :=
    fun t ht => mem_normalizer_commutator (hTL₀ ht)
      (QuasithinUnique.GammaExtra.normalizer_le_normalizer_thompsonJ T (le_normalizer ht))
  rcases le_or_commutator_le hperf hq hL₀L hKL₀ hL₀K hTK with h | h
  · exact le_antisymm h hKL₀
  · refine absurd ?_ hJ
    have hN := normalizer_le_normalizer_pCoreOf 2 (conjClosure L T)
    have h3 : ⁅⁅conjClosure L T, conjClosure L T⁆, thompsonJ T⁆ ≤ pCoreOf 2 (conjClosure L T) :=
      H13.three_subgroups_le (le_normalizer.trans hN) (hJL₀.trans hN) (le_normalizer.trans hN) h
        (by rw [Subgroup.commutator_comm (thompsonJ T)]; exact h)
    rw [perfect_conjClosure hperf] at h3
    exact le_pCoreOf_sup_of_commutator_le hT hTL₀ hOT hJT h3

end CFSG.Quasithin.Vol2.Ch11.OE1
