module

public import CFSG.Quasithin.Vol2.Ch10SecABasicOrbit

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem conjugate_le_fsuL0 {T L : Subgroup G} {t : G} (ht : t ∈ T) :
    CFSG.conjugate L t ≤ fsuL0 T L := by
  intro x hx
  rw [mem_conjugate_iff] at hx
  simpa [mul_assoc] using mem_conjClosure (T.inv_mem ht) hx

variable [Finite G] {T L I : Subgroup G}

theorem fsuL0_eq_sup (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuL0 T L = L ⊔ CFSG.conjugate L t := by
  refine le_antisymm (conjClosure_le fun s hs l hl => ?_)
    (sup_le (le_fsuL0 T L) (conjugate_le_fsuL0 ht))
  have hmem : s * l * s⁻¹ ∈ CFSG.conjugate L s⁻¹ := by
    rw [mem_conjugate_iff]
    simpa [mul_assoc] using hl
  rcases conjugate_eq_or h37 h38 hyp ht htn (le_fsuM T L (T.inv_mem hs)) with h | h
  · rw [h] at hmem
    exact Subgroup.mem_sup_left hmem
  · rw [h] at hmem
    exact Subgroup.mem_sup_right hmem

theorem conjugate_le_normalizer (hloc : quasithinIsLocal T L) {s : G} (hs : s ∈ fsuM T L) :
    CFSG.conjugate L s ≤ Subgroup.normalizer (L : Set G) :=
  le_normalizer_of_mem_cComp (mem_cComp_fsuM hloc) (conjugate_mem_cComp_fsuM hloc hs)

theorem le_normalizer_conjugate (hloc : quasithinIsLocal T L) {s : G} (hs : s ∈ fsuM T L) :
    L ≤ Subgroup.normalizer (CFSG.conjugate L s : Set G) :=
  le_normalizer_of_mem_cComp (conjugate_mem_cComp_fsuM hloc hs) (mem_cComp_fsuM hloc)

theorem fsuL0_le_normalizer_conjugate (hloc : quasithinIsLocal T L) {s : G}
    (hs : s ∈ fsuM T L) : fsuL0 T L ≤ Subgroup.normalizer (CFSG.conjugate L s : Set G) := by
  refine conjClosure_le fun r hr l hl => ?_
  have hmem : r * l * r⁻¹ ∈ CFSG.conjugate L r⁻¹ := by
    rw [mem_conjugate_iff]
    simpa [mul_assoc] using hl
  exact le_normalizer_of_mem_cComp (conjugate_mem_cComp_fsuM hloc hs)
    (conjugate_mem_cComp_fsuM hloc (le_fsuM T L (T.inv_mem hr))) hmem

theorem fsuL0_le_normalizer (hloc : quasithinIsLocal T L) :
    fsuL0 T L ≤ Subgroup.normalizer (L : Set G) := by
  simpa [conjugate_one] using fsuL0_le_normalizer_conjugate hloc (fsuM T L).one_mem

theorem normal_fsuL0 (hloc : quasithinIsLocal T L) : (L.subgroupOf (fsuL0 T L)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (le_fsuL0 T L)).mpr (fsuL0_le_normalizer hloc)

theorem normal_fsuL0_conjugate (hloc : quasithinIsLocal T L) {t : G} (ht : t ∈ T) :
    ((CFSG.conjugate L t).subgroupOf (fsuL0 T L)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (conjugate_le_fsuL0 ht)).mpr
    (fsuL0_le_normalizer_conjugate hloc (le_fsuM T L ht))

theorem commutator_conjugate_le (h37 : Vol2Native.A37ForSQTKCat) (hyp : Hyp10 G T L I) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ⁅L, CFSG.conjugate L t⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 (CFSG.conjugate L t) := by
  have := hyp.fsu.simple
  exact (Vol2Native.lemma_1_2_1_two (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1 h37
    (pCoreOf_fsuM_ne_bot hyp.fsu.faithful) (mem_cComp_fsuM hyp.fsu.maximal.1)
    (conjugate_mem_cComp_fsuM hyp.fsu.maximal.1 (le_fsuM T L ht)) (ne_conjugate htn)).1

theorem T0_le_T1 (hloc : quasithinIsLocal T L) : T0 T L ≤ T1 T L :=
  inf_le_inf_left T (fsuL0_le_normalizer hloc)

omit [Finite G] in
theorem not_two_dvd_index_of_le (hT : quasithinIsSylowTwo T) {X : Subgroup G} (hTX : T ≤ X) :
    ¬ 2 ∣ (T.subgroupOf X).index := by
  rw [← Subgroup.relIndex]
  exact fun hd => hT.2 (hd.trans (Subgroup.relIndex_dvd_index_of_le hTX))

theorem pCoreOf_le_of_sylow (hT : quasithinIsSylowTwo T) {X : Subgroup G} (hTX : T ≤ X) :
    pCoreOf 2 X ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (pCoreOf_le_pCoreOf_of_sylow hTX hT.1 le_rfl (not_two_dvd_index_of_le hT hTX)).trans
    (Subgroup.map_subtype_le _)

theorem pCoreOf_fsuL0_le_T0 (hT : quasithinIsSylowTwo T) : pCoreOf 2 (fsuL0 T L) ≤ T0 T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_inf ((A4.pCoreOf_le_of_subnormal 2 (subnormal_fsuL0 T L)).trans
    (pCoreOf_le_of_sylow hT (le_fsuM T L))) (Subgroup.map_subtype_le _)

theorem inf_pCoreOf_eq_of_normal {K X : Subgroup G} (hKX : K ≤ X)
    (hn : X ≤ Subgroup.normalizer (K : Set G)) : K ⊓ pCoreOf 2 X = pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_inf (Subgroup.map_subtype_le _) ?_)
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (hKX hx)⟩)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le inf_le_right)
  · refine A4.pCoreOf_le_of_subnormal 2 (CFSG.Open.IsSubnormal.step hKX ?_
      (CFSG.Open.IsSubnormal.refl _))
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hn

theorem inf_pCoreOf_fsuL0 (hloc : quasithinIsLocal T L) :
    L ⊓ pCoreOf 2 (fsuL0 T L) = pCoreOf 2 L :=
  inf_pCoreOf_eq_of_normal (le_fsuL0 T L) (fsuL0_le_normalizer hloc)

theorem conjugate_inf_pCoreOf_fsuL0 (hloc : quasithinIsLocal T L) {t : G} (ht : t ∈ T) :
    CFSG.conjugate L t ⊓ pCoreOf 2 (fsuL0 T L) = pCoreOf 2 (CFSG.conjugate L t) :=
  inf_pCoreOf_eq_of_normal (conjugate_le_fsuL0 ht)
    (fsuL0_le_normalizer_conjugate hloc (le_fsuM T L ht))

theorem sup_pCoreOf_le (hloc : quasithinIsLocal T L) {t : G} (ht : t ∈ T) :
    pCoreOf 2 L ⊔ pCoreOf 2 (CFSG.conjugate L t) ≤ pCoreOf 2 (fsuL0 T L) := by
  rw [← inf_pCoreOf_fsuL0 hloc, ← conjugate_inf_pCoreOf_fsuL0 hloc ht]
  exact sup_le inf_le_right inf_le_right

theorem isSylowTwoOf_inf (hloc : quasithinIsLocal T L) : IsSylowTwoOf (T ⊓ L) L := by
  have hT : IsSylowTwoOf T (L ⊔ T) := ⟨le_sup_right, hloc.1, hloc.2.2.1⟩
  have hL0 : IsSylowTwoOf (T ⊓ fsuL0 T L) (fsuL0 T L) :=
    B6.isSylowTwoOf_inf_normal hT (fsuL0_le_sup T L)
      (sup_le ((le_fsuL0 T L).trans Subgroup.le_normalizer) (le_fsuM T L))
  have h := B6.isSylowTwoOf_inf_normal hL0 (le_fsuL0 T L) (fsuL0_le_normalizer hloc)
  rwa [inf_assoc, inf_eq_right.mpr (le_fsuL0 T L)] at h

omit [Finite G] in
theorem perfect_L (hloc : quasithinIsLocal T L) : ⁅L, L⁆ = L :=
  hloc.2.1.2.1

end CFSG.Quasithin.Vol2.Ch10.SecA
