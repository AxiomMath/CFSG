module

public import CFSG.Quasithin.Vol2.Ch10SecABasicOrbit
public import CFSG.Quasithin.Vol2.Ch10SecBSetup
public import CFSG.Quasithin.Vol2.Ch10StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem_of_lt {P Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hPQ : P < Q) : ∃ x ∈ Q, x ∉ P ∧ x ∈ Subgroup.normalizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : P.subgroupOf Q < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hPQ.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : Q) ∈ P.subgroupOf Q := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt)
  refine ⟨y, y.2, fun h => hyP (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (Subgroup.normalizer (P : Set G)).subgroupOf Q := by
    rw [Subgroup.subgroupOf_normalizer_eq hPQ.le]
    exact hyN
  exact Subgroup.mem_subgroupOf.mp hy

variable {T L I : Subgroup G}

theorem isSylowTwoOf_T1_of_inM (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1025 : Stmt10_2_5) (hyp : Hyp10 G T L I)
    {H : Subgroup G} (hH : InM (fsuL0 T L ⊔ T1 T L) H) (hHM : H ≠ fsuM T L) :
    IsSylowTwoOf (T1 T L) H := by
  have hT1H : T1 T L ≤ H := le_sup_right.trans hH.2
  have hT1p : IsPGroup 2 ↥(T1 T L) := hyp.fsu.sylow.1.to_le inf_le_left
  obtain ⟨S, hT1S, hS⟩ := exists_isSylowTwoOf_of_le hT1H hT1p
  by_contra hns
  have hlt : T1 T L < S := lt_of_le_of_ne hT1S fun h => hns (h ▸ hS)
  obtain ⟨x, hxS, hxT1, hxN⟩ := exists_mem_normalizer_not_mem_of_lt hS.isPGroup hlt
  have hPM : S ⊓ Subgroup.normalizer (T1 T L : Set G) ≤ fsuM T L :=
    inf_le_right.trans (h1025 G T L I hyp)
  have hPp : IsPGroup 2 ↥(S ⊓ Subgroup.normalizer (T1 T L : Set G)) :=
    hS.isPGroup.to_le inf_le_left
  have hT1P : T1 T L ≤ S ⊓ Subgroup.normalizer (T1 T L : Set G) :=
    le_inf hT1S Subgroup.le_normalizer
  have hT : IsSylowTwoOf T (fsuM T L) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow (le_fsuM T L)
  have hcT : Nat.card ↥(T1 T L) * 2 = Nat.card ↥T := by
    have h1 := Subgroup.card_mul_index ((T1 T L).subgroupOf T)
    rw [SecA.index_T1 h37 h38 hyp] at h1
    rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hcP : Nat.card ↥(T1 T L) * 2 ≤ Nat.card ↥(S ⊓ Subgroup.normalizer (T1 T L : Set G)) := by
    have h1 := Subgroup.relIndex_mul_card (T1 T L) (S ⊓ Subgroup.normalizer (T1 T L : Set G))
    rw [inf_eq_left.mpr hT1P] at h1
    have h2 : (T1 T L).relIndex (S ⊓ Subgroup.normalizer (T1 T L : Set G)) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact fun h => hxT1 (h ⟨hxS, hxN⟩)
    have h3 : (T1 T L).relIndex (S ⊓ Subgroup.normalizer (T1 T L : Set G)) ≠ 0 :=
      E3.relIndex_ne_zero' _ _
    have h4 : 2 ≤ (T1 T L).relIndex (S ⊓ Subgroup.normalizer (T1 T L : Set G)) := by omega
    rw [← h1]
    calc Nat.card ↥(T1 T L) * 2 ≤
        Nat.card ↥(T1 T L) * (T1 T L).relIndex (S ⊓ Subgroup.normalizer (T1 T L : Set G)) :=
          Nat.mul_le_mul_left _ h4
      _ = _ := mul_comm _ _
  have hcP' : Nat.card ↥(S ⊓ Subgroup.normalizer (T1 T L : Set G)) ≤ Nat.card ↥T := by
    rw [hT.card_eq]
    exact card_le_twoPart hPM hPp
  have hPsyl : IsSylowTwoOf (S ⊓ Subgroup.normalizer (T1 T L : Set G)) (fsuM T L) :=
    isSylowTwoOf_of_card_eq hPM hPp (by rw [← hT.card_eq]; omega)
  have hU := isUniqueM_L0_sylow h331 hyp hPsyl
  have hle : fsuL0 T L ⊔ S ⊓ Subgroup.normalizer (T1 T L : Set G) ≤ H :=
    sup_le (le_sup_left.trans hH.2) (inf_le_left.trans hS.1)
  exact hHM (hU.2 H ⟨hH.1, hle⟩)

theorem exists_cComp_of_inM (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) {H X : Subgroup G}
    (hH : InM (fsuL0 T L ⊔ T1 T L) H) (hS : IsSylowTwoOf (T1 T L) H) (hX : X ∈ cComp (fsuM T L))
    (hXH : X ≤ H) (hXT1 : T1 T L ≤ Subgroup.normalizer (X : Set G)) :
    ∃ K ∈ cComp H, X ≤ K ∧ (K.subgroupOf H).Normal := by
  have hH2 : pCoreOf 2 H ≠ ⊥ := (inH_of_inM hH).2
  have hXfam : X ∈ lFamily (T1 T L) :=
    cComp_subset_lFamily (inf_le_left.trans (le_fsuM T L)) hX
  obtain ⟨K, hK', hXK⟩ := Vol2Native.lemma_1_2_4_exists hK h37 h39 hH2 hS hXH hXfam
  exact ⟨K, hK', hXK, Vol2Native.lemma_1_2_4_normal hK h37 h38 hH2 hS hXfam hXK hK' hXT1⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
