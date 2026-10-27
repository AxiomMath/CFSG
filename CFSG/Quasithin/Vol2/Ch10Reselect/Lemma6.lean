module

public import CFSG.Quasithin.Vol2.Ch10Reselect.L0Facts
public import CFSG.Quasithin.Vol2.Ch10Reselect.GLemma

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem isPrimeReduced_fsuVM_sup (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two) (hfsu : FSU G T L I)
    (hlt : L < fsuL0 T L)
    (hL3 : ∀ k ∈ fsuM T L, (∀ l ∈ fsuL0 T L,
        ⁅k, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) →
      k ∈ Subgroup.centralizer (fsuVM T L I : Set G)) :
    IsPrimeReduced 2 ((fsuVM T L I).subgroupOf (L ⊔ T)) := by
  obtain ⟨hAcomm, hAsq⟩ := isElemAbelian_fsuVM_of_h322 h322 hfsu
  haveI := hAcomm
  have hAX : fsuVM T L I ≤ L ⊔ T := fsuVM_le_sup_of_h322 h322 hfsu
  have hXM : L ⊔ T ≤ fsuM T L := sup_le_fsuM T L
  have hL0X : fsuL0 T L ≤ L ⊔ T := by
    refine conjClosure_le fun h hh z hz => ?_
    exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left hz))
      ((L ⊔ T).inv_mem (Subgroup.mem_sup_right hh))
  have hVn : ((fsuVM T L I).subgroupOf (L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAX).mpr
      (hXM.trans (fsuM_le_normalizer_fsuVM T L I))
  haveI := hVn
  have hCx : ∀ y : ↥(L ⊔ T),
      y ∈ Subgroup.centralizer (((fsuVM T L I).subgroupOf (L ⊔ T) : Subgroup ↥(L ⊔ T)) :
        Set ↥(L ⊔ T)) ↔ (y : G) ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
    intro y
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h a ha
      have hv : (⟨a, hAX ha⟩ : ↥(L ⊔ T)) ∈ (fsuVM T L I).subgroupOf (L ⊔ T) :=
        Subgroup.mem_subgroupOf.mpr ha
      have := h _ (SetLike.mem_coe.mpr hv)
      simpa using congrArg Subtype.val this
    · intro h v hv
      apply Subtype.ext
      simpa using h _ (Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hv))
  have hcore : CFSG.pCore 2 (↥(L ⊔ T) ⧸ Subgroup.centralizer (((fsuVM T L I).subgroupOf (L ⊔ T) :
      Subgroup ↥(L ⊔ T)) : Set ↥(L ⊔ T))) = ⊥ := by
    apply pCore_quotient_eq_bot
    intro N hN hNx
    haveI := hN
    have hN'X : ∀ w ∈ N.map (L ⊔ T).subtype, ∀ g ∈ L ⊔ T,
        g * w * g⁻¹ ∈ N.map (L ⊔ T).subtype := by
      intro w hw g hg
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
      refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, Subgroup.Normal.conj_mem hN y hy _, ?_⟩
      simp
    have hWL : N.map (L ⊔ T).subtype ⊓ fsuL0 T L ≤ fsuL0 T L := inf_le_right
    have hconjW : ∀ g ∈ fsuL0 T L, ∀ w ∈ N.map (L ⊔ T).subtype ⊓ fsuL0 T L,
        g * w * g⁻¹ ∈ N.map (L ⊔ T).subtype ⊓ fsuL0 T L := by
      intro g hg w hw
      obtain ⟨hwN, hwL⟩ := Subgroup.mem_inf.mp hw
      exact Subgroup.mem_inf.mpr ⟨hN'X w hwN g (hL0X hg),
        (fsuL0 T L).mul_mem ((fsuL0 T L).mul_mem hg hwL) ((fsuL0 T L).inv_mem hg)⟩
    have hWn : fsuL0 T L ≤
        Subgroup.normalizer ((N.map (L ⊔ T).subtype ⊓ fsuL0 T L : Subgroup G) : Set G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · exact hconjW g hg w
      · intro hw
        have := hconjW g⁻¹ ((fsuL0 T L).inv_mem hg) _ hw
        simpa [mul_assoc] using this
    have h2 : ∀ w ∈ N.map (L ⊔ T).subtype ⊓ fsuL0 T L,
        ∃ k : ℕ, w ^ (2 ^ k) ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
      intro w hw
      obtain ⟨hwN, -⟩ := Subgroup.mem_inf.mp hw
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hwN
      obtain ⟨k, hk⟩ := hNx y hy
      refine ⟨k, ?_⟩
      have := (hCx _).mp hk
      simpa [Subgroup.coe_pow] using this
    have hWC := le_centralizer_of_two_power_of_le_fsuL0 h37 h38 h322 hfsu hlt hWL hWn h2
    intro x hx
    rw [hCx]
    have hxM : (x : G) ∈ fsuM T L := hXM x.2
    refine hL3 (x : G) hxM (fun l hl => ?_)
    have hnN : (x : G) ∈ N.map (L ⊔ T).subtype := Subgroup.mem_map_of_mem _ hx
    have hcN : ⁅(x : G), l⁆ ∈ N.map (L ⊔ T).subtype := by
      have hlN := hN'X ((x : G)⁻¹) ((N.map (L ⊔ T).subtype).inv_mem hnN) l (hL0X hl)
      have e : ⁅(x : G), l⁆ = (x : G) * (l * (x : G)⁻¹ * l⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (N.map (L ⊔ T).subtype).mul_mem hnN hlN
    have hcL : ⁅(x : G), l⁆ ∈ fsuL0 T L := by
      rw [commutatorElement_def]
      have hnl : (x : G) * l * (x : G)⁻¹ ∈ fsuL0 T L :=
        (Subgroup.mem_normalizer_iff.mp hxM l).mp hl
      exact (fsuL0 T L).mul_mem hnl ((fsuL0 T L).inv_mem hl)
    exact hWC (Subgroup.mem_inf.mpr ⟨hcN, hcL⟩)
  have hel : CFSG.IsElementaryAbelian 2 ↥((fsuVM T L I).subgroupOf (L ⊔ T)) := by
    have hcomm : ∀ x ∈ (fsuVM T L I).subgroupOf (L ⊔ T), ∀ y ∈ (fsuVM T L I).subgroupOf (L ⊔ T),
        x * y = y * x := by
      intro x hx y hy
      apply Subtype.ext
      have h := IsMulCommutative.is_comm.comm
        (⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩ : ↥(fsuVM T L I))
        ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
      exact congrArg (fun z : ↥(fsuVM T L I) => (z : G)) h
    have hel' : IsElemAbelian 2 ((fsuVM T L I).subgroupOf (L ⊔ T)) :=
      ⟨IsMulCommutative.of_setLike_mul_comm hcomm, fun x hx => Subtype.ext
        (by simpa using hAsq (x : G) (Subgroup.mem_subgroupOf.mp hx))⟩
    exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mpr hel'
  exact ⟨hVn, hel, hcore⟩

theorem fsuVM_le_reducedAggregate (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two) (hfsu : FSU G T L I)
    (hlt : L < fsuL0 T L)
    (hL3 : ∀ k ∈ fsuM T L, (∀ l ∈ fsuL0 T L,
        ⁅k, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) →
      k ∈ Subgroup.centralizer (fsuVM T L I : Set G)) :
    fsuVM T L I ≤ reducedAggregate (L ⊔ T) := by
  have hmem : (fsuVM T L I).subgroupOf (L ⊔ T) ∈ primeReducedFamily ↥(L ⊔ T) 2 :=
    isPrimeReduced_fsuVM_sup h37 h38 h322 hfsu hlt hL3
  have hle : (fsuVM T L I).subgroupOf (L ⊔ T) ≤ primeReducedAggregate ↥(L ⊔ T) 2 :=
    le_sSup hmem
  have hmap := Subgroup.map_mono (f := (L ⊔ T).subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le (fsuVM_le_sup_of_h322 h322 hfsu)] at hmap

end CFSG.Quasithin.Vol2.Ch10Reselect
