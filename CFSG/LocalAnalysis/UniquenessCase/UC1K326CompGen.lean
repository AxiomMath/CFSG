module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326CompDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326ZWrC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {n : ℕ} {P : Subgroup G}

theorem centralizer_inf_subgroupOf {a : G} (ha : a ∈ P) :
    (Subgroup.centralizer ({a} : Set G) ⊓ P).subgroupOf P =
      Subgroup.centralizer ({⟨a, ha⟩} : Set ↥P) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hx, -⟩
    exact Subtype.ext (by simpa using hx)
  · intro hx
    exact ⟨Subtype.ext_iff.mp hx, x.2⟩

theorem relIndex_eq_three_of_index_eq_three {H : Type*} [Group H] {D T : Subgroup H}
    (hDn : D.Normal) (hDi : D.index = 3) (hTD : ¬ T ≤ D) : D.relIndex T = 3 := by
  haveI : D.Normal := hDn
  have hprime : D.index.Prime := by rw [hDi]; exact Nat.prime_three
  have hlt : D < D ⊔ T :=
    lt_of_le_of_ne le_sup_left fun h => hTD (h.symm ▸ le_sup_right)
  have hsup : D ⊔ T = ⊤ := (Subgroup.isCoatom_of_index_prime hprime).lt_iff.mp hlt
  rw [← Subgroup.relIndex_sup_left (H := T) (K := D), hsup, Subgroup.relIndex_top_right, hDi]

theorem zwr_centralizer_inf_relIndex (h : Hyp326 G n P) {a : G} (ha : a ∈ jOf P)
    (ha2 : a ∉ z2Of P) :
    (Subgroup.centralizer ({a} : Set G) ⊓ P).relIndex P = 3 ∧
      IsMulCommutative ↥(Subgroup.centralizer ({a} : Set G) ⊓ P) := by
  obtain ⟨e⟩ := h.wr
  have haP : a ∈ P := (jOf_spec h).1 ha
  let a' : ↥P := ⟨a, haP⟩
  have ha' : a' ∈ CFSG.elemThompson ↥P 3 := by
    rw [jOf, CFSG.inSubgroup, Subgroup.mem_map] at ha
    obtain ⟨y, hy, hyeq⟩ := ha
    have hy_eq : y = a' := Subtype.ext (show (y : G) = (a' : G) from hyeq)
    exact hy_eq ▸ hy
  have ha2' : a' ∉ Subgroup.upperCentralSeries ↥P 2 := by
    intro hmem
    apply ha2
    rw [z2Of, Subgroup.mem_map]
    exact ⟨a', hmem, rfl⟩
  obtain ⟨hcomm, hidx, -⟩ := zwr_centralizer_of_mem_J h.one_le e ha' ha2'
  have hDC' : (Subgroup.centralizer ({a} : Set G) ⊓ P).subgroupOf P =
      Subgroup.centralizer ({a'} : Set ↥P) := centralizer_inf_subgroupOf haP
  haveI : IsMulCommutative (Subgroup.centralizer ({a'} : Set ↥P)) := hcomm
  have hmap : (Subgroup.centralizer ({a'} : Set ↥P)).map P.subtype =
      Subgroup.centralizer ({a} : Set G) ⊓ P := by
    rw [← hDC', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  refine ⟨?_, ?_⟩
  · rw [Subgroup.relIndex, hDC']; exact hidx
  · rw [← hmap]; infer_instance

theorem not_le_centralizer_of_isSylowOf {L : Subgroup G} (hS : IsSL3pi ↥L)
    (hTL : IsSylowOf 3 (P ⊓ L) L) {a : G}
    (hDcomm : IsMulCommutative ↥(Subgroup.centralizer ({a} : Set G) ⊓ P)) :
    ¬ (P ⊓ L) ≤ Subgroup.centralizer ({a} : Set G) := by
  intro hle
  have hTnab : ¬ IsMulCommutative ↥(P ⊓ L) :=
    not_isMulCommutative_of_isSylowOf hS.isQuasisimple hS.card_center hTL
  apply hTnab
  haveI := hDcomm
  exact isMulCommutative_anti (show P ⊓ L ≤ Subgroup.centralizer ({a} : Set G) ⊓ P from
    fun x hx => ⟨hle hx, hx.1⟩)

theorem exists_commutator_notMem_zOf (h : Hyp326 G n P) {L : Subgroup G} (hLn : L.Normal)
    (hS : IsSL3pi ↥L) (hTL : IsSylowOf 3 (P ⊓ L) L) {a : G} (ha : a ∈ jOf P)
    (ha2 : a ∉ z2Of P) : ∃ t ∈ P ⊓ L, ⁅t, a⁆ ∉ zOf L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h.wr
  have haP : a ∈ P := (jOf_spec h).1 ha
  let a' : ↥P := ⟨a, haP⟩
  have ha' : a' ∈ CFSG.elemThompson ↥P 3 := by
    rw [jOf, CFSG.inSubgroup, Subgroup.mem_map] at ha
    obtain ⟨y, hy, hyeq⟩ := ha
    have hy_eq : y = a' := Subtype.ext (show (y : G) = (a' : G) from hyeq)
    exact hy_eq ▸ hy
  have ha2' : a' ∉ Subgroup.upperCentralSeries ↥P 2 := by
    intro hmem
    apply ha2
    rw [z2Of, Subgroup.mem_map]
    exact ⟨a', hmem, rfl⟩
  obtain ⟨hC'comm, -, hC'commut⟩ := zwr_centralizer_of_mem_J h.one_le e ha' ha2'
  have hDC' : (Subgroup.centralizer ({a} : Set G) ⊓ P).subgroupOf P =
      Subgroup.centralizer ({a'} : Set ↥P) := centralizer_inf_subgroupOf haP
  have hDcomm : IsMulCommutative ↥(Subgroup.centralizer ({a} : Set G) ⊓ P) := by
    haveI : IsMulCommutative (Subgroup.centralizer ({a'} : Set ↥P)) := hC'comm
    have hmap : (Subgroup.centralizer ({a'} : Set ↥P)).map P.subtype =
        Subgroup.centralizer ({a} : Set G) ⊓ P := by
      rw [← hDC', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
    rw [← hmap]; infer_instance
  have hTnotC : ¬ (P ⊓ L) ≤ Subgroup.centralizer ({a} : Set G) :=
    not_le_centralizer_of_isSylowOf hS hTL hDcomm
  obtain ⟨t, htT, htC⟩ := SetLike.not_le_iff_exists.mp hTnotC
  refine ⟨t, htT, ?_⟩
  intro htz
  have htP : t ∈ P := htT.1
  have ht'notC' : (⟨t, htP⟩ : ↥P) ∉ Subgroup.centralizer ({a'} : Set ↥P) := by
    intro hmem
    apply htC
    have hmem' : (⟨t, htP⟩ : ↥P) ∈
        (Subgroup.centralizer ({a} : Set G) ⊓ P).subgroupOf P := by
      rwa [hDC']
    exact (Subgroup.mem_subgroupOf.mp hmem').1
  have hcommt := hC'commut (⟨t, htP⟩ : ↥P) ht'notC'
  have hzP : ⁅t, a⁆ ∈ P := (zOf_le_center h hLn hS.card_center).1 htz
  have hzcent : ⁅t, a⁆ ∈ Subgroup.centralizer (P : Set G) :=
    (zOf_le_center h hLn hS.card_center).2 htz
  have hu : (⟨⁅t, a⁆, hzP⟩ : ↥P) ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hyc := Subgroup.mem_centralizer_iff.mp hzcent y y.2
    simpa using hyc
  have heq : (⟨⁅t, a⁆, hzP⟩ : ↥P) = ⁅(⟨t, htP⟩ : ↥P), a'⁆ := by
    apply Subtype.ext
    change ⁅t, a⁆ = (P.subtype ⁅(⟨t, htP⟩ : ↥P), a'⁆ : G)
    rw [map_commutatorElement]
    rfl
  exact hcommt (heq ▸ hu)

theorem relIndex_centralizer_inf_eq_three (h : Hyp326 G n P) {L : Subgroup G}
    (hS : IsSL3pi ↥L) (hTL : IsSylowOf 3 (P ⊓ L) L) {a : G} (ha : a ∈ jOf P)
    (ha2 : a ∉ z2Of P) :
    (Subgroup.centralizer ({a} : Set G)).relIndex (P ⊓ L) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h.wr
  have hrelP : (Subgroup.centralizer ({a} : Set G) ⊓ P).relIndex P = 3 :=
    (zwr_centralizer_inf_relIndex h ha ha2).1
  have hTnotC : ¬ (P ⊓ L) ≤ Subgroup.centralizer ({a} : Set G) :=
    not_le_centralizer_of_isSylowOf hS hTL (zwr_centralizer_inf_relIndex h ha ha2).2
  set D' : Subgroup ↥P := (Subgroup.centralizer ({a} : Set G) ⊓ P).subgroupOf P with hD'def
  set T' : Subgroup ↥P := (P ⊓ L).subgroupOf P with hT'def
  have hD'index : D'.index = 3 := by rw [hD'def]; exact hrelP
  have hcardP : Nat.card ↥P = 3 ^ (3 * n + 1) := by
    rw [Nat.card_congr e.toEquiv, (zwr_card_center_Zwr h.one_le).1]
  have hminfac : (Nat.card ↥P).minFac = 3 := by
    rw [hcardP]; exact Nat.Prime.pow_minFac Nat.prime_three (by omega)
  have hD'normal : D'.Normal :=
    Subgroup.normal_of_index_eq_minFac_card (H := D') (by rw [hD'index, hminfac])
  have hT'notD' : ¬ T' ≤ D' := by
    intro hle
    apply hTnotC
    intro x hx
    have hxT : (⟨x, hx.1⟩ : ↥P) ∈ T' := by
      rw [hT'def, Subgroup.mem_subgroupOf]; exact hx
    have hxD : (⟨x, hx.1⟩ : ↥P) ∈ D' := hle hxT
    rw [hD'def, Subgroup.mem_subgroupOf] at hxD
    exact hxD.1
  have hD'relT' : D'.relIndex T' = 3 :=
    relIndex_eq_three_of_index_eq_three hD'normal hD'index hT'notD'
  have h1 : (Subgroup.centralizer ({a} : Set G)).relIndex (P ⊓ L) =
      (Subgroup.centralizer ({a} : Set G) ⊓ P).relIndex (P ⊓ L) := by
    rw [Subgroup.relIndex, Subgroup.relIndex]
    congr 1
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hh => ⟨hh, x.2.1⟩, fun hh => hh.1⟩
  have h2 : (Subgroup.centralizer ({a} : Set G) ⊓ P).relIndex (P ⊓ L) = D'.relIndex T' := by
    rw [hD'def, hT'def]
    exact (Subgroup.relIndex_subgroupOf (H := Subgroup.centralizer ({a} : Set G) ⊓ P)
      (K := P ⊓ L) (L := P) (show P ⊓ L ≤ P from inf_le_left)).symm
  rw [h1, h2]
  exact hD'relT'

theorem comp_L_le (hG : SL3Gen) (h : Hyp326 G n P) {L : Subgroup G} (hLn : L.Normal)
    (hS : IsSL3pi ↥L) {a : G} (ha : a ∈ jOf P) (ha2 : a ∉ z2Of P) {M : Subgroup G}
    (hPM : P ≤ M) (hCM : Subgroup.centralizer ({a} : Set G) ≤ M) : L ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTL : IsSylowOf 3 (P ⊓ L) L :=
    h.sylow.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have haP : a ∈ P := (jOf_spec h).1 ha
  have haNorm : a ∈ Subgroup.normalizer ((P ⊓ L : Subgroup G) : Set G) := by
    have h1 : a ∈ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer haP
    have h2 : a ∈ Subgroup.normalizer (L : Set G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hLn]; exact Subgroup.mem_top a
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := P) (K := L) ⟨h1, h2⟩
  have ha3 : a ^ 3 ∈ Subgroup.centralizer (L : Set G) := by
    have h1 : a ^ 3 = 1 := ((jOf_spec h).2.1).2 a ha
    rw [h1]; exact Subgroup.one_mem _
  have hex : ∃ t ∈ P ⊓ L, ⁅t, a⁆ ∉ zOf L :=
    exists_commutator_notMem_zOf h hLn hS hTL ha ha2
  have hrel : (Subgroup.centralizer ({a} : Set G)).relIndex (P ⊓ L) = 3 :=
    relIndex_centralizer_inf_eq_three h hS hTL ha ha2
  have hcomm : IsMulCommutative ↥((P ⊓ L) ⊓ Subgroup.centralizer ({a} : Set G)) := by
    haveI : IsMulCommutative ↥(Subgroup.centralizer ({a} : Set G) ⊓ P) :=
      (zwr_centralizer_inf_relIndex h ha ha2).2
    exact isMulCommutative_anti (show (P ⊓ L) ⊓ Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.centralizer ({a} : Set G) ⊓ P from fun x hx => ⟨hx.2, hx.1.1⟩)
  have hgen := hG G L (P ⊓ L) a hS hLn hTL haNorm ha3 hex hrel hcomm
  rw [← hgen]
  exact sup_le (fun x hx => hPM hx.1) (fun x hx => hCM hx.2)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
